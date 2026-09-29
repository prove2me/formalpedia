-- Prove2me | solution 1 for syracuse_descends_range_876568_880568
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:43.941926+00:00
-- url     : https://prove2.me/submissions/12996caf-01b8-48bf-b94f-d014d6e1aafe

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


theorem B2228269 : Blo 876568 2228269 := bbase (se 3 (by rfl) ⟨417800, by rfl⟩ : syracuseStep 2228269 = 835601) (by norm_num)
theorem B1114165 : Blo 876568 1114165 := bbase (se 5 (by rfl) ⟨52226, by rfl⟩ : syracuseStep 1114165 = 104453) (by norm_num)
theorem B1671293 : Blo 876568 1671293 := bbase (se 3 (by rfl) ⟨313367, by rfl⟩ : syracuseStep 1671293 = 626735) (by norm_num)
theorem B950401 : Blo 876568 950401 := bbase (se 2 (by rfl) ⟨356400, by rfl⟩ : syracuseStep 950401 = 712801) (by norm_num)
theorem B2228381 : Blo 876568 2228381 := bbase (se 3 (by rfl) ⟨417821, by rfl⟩ : syracuseStep 2228381 = 835643) (by norm_num)
theorem B1114337 : Blo 876568 1114337 := bbase (se 2 (by rfl) ⟨417876, by rfl⟩ : syracuseStep 1114337 = 835753) (by norm_num)
theorem B2818309 : Blo 876568 2818309 := bbase (se 4 (by rfl) ⟨264216, by rfl⟩ : syracuseStep 2818309 = 528433) (by norm_num)
theorem B1671445 : Blo 876568 1671445 := bbase (se 6 (by rfl) ⟨39174, by rfl⟩ : syracuseStep 1671445 = 78349) (by norm_num)
theorem B1114393 : Blo 876568 1114393 := bbase (se 2 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 1114393 = 835795) (by norm_num)
theorem B1409309 : Blo 876568 1409309 := bbase (se 3 (by rfl) ⟨264245, by rfl⟩ : syracuseStep 1409309 = 528491) (by norm_num)
theorem B2228573 : Blo 876568 2228573 := bbase (se 3 (by rfl) ⟨417857, by rfl⟩ : syracuseStep 2228573 = 835715) (by norm_num)
theorem B1409501 : Blo 876568 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B2818565 : Blo 876568 2818565 := bbase (se 4 (by rfl) ⟨264240, by rfl⟩ : syracuseStep 2818565 = 528481) (by norm_num)
theorem B2228917 : Blo 876568 2228917 := bbase (se 5 (by rfl) ⟨104480, by rfl⟩ : syracuseStep 2228917 = 208961) (by norm_num)
theorem B1999709 : Blo 876568 1999709 := bbase (se 3 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 1999709 = 749891) (by norm_num)
theorem B3343301 : Blo 876568 3343301 := bbase (se 4 (by rfl) ⟨313434, by rfl⟩ : syracuseStep 3343301 = 626869) (by norm_num)
theorem B4457429 : Blo 876568 4457429 := bbase (se 7 (by rfl) ⟨52235, by rfl⟩ : syracuseStep 4457429 = 104471) (by norm_num)
theorem B6325397 : Blo 876568 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B7505237 : Blo 876568 7505237 := bbase (se 12 (by rfl) ⟨2748, by rfl⟩ : syracuseStep 7505237 = 5497) (by norm_num)
theorem B5998549 : Blo 876568 5998549 := bbase (se 7 (by rfl) ⟨70295, by rfl⟩ : syracuseStep 5998549 = 140591) (by norm_num)
theorem B952393 : Blo 876568 952393 := bbase (se 2 (by rfl) ⟨357147, by rfl⟩ : syracuseStep 952393 = 714295) (by norm_num)
theorem B8456309 : Blo 876568 8456309 := bbase (se 5 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 8456309 = 792779) (by norm_num)
theorem B1608317 : Blo 876568 1608317 := bbase (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) (by norm_num)
theorem B2001541 : Blo 876568 2001541 := bbase (se 4 (by rfl) ⟨187644, by rfl⟩ : syracuseStep 2001541 = 375289) (by norm_num)
theorem B12028949 : Blo 876568 12028949 := bbase (se 6 (by rfl) ⟨281928, by rfl⟩ : syracuseStep 12028949 = 563857) (by norm_num)
theorem B986161 : Blo 876568 986161 := bbase (se 2 (by rfl) ⟨369810, by rfl⟩ : syracuseStep 986161 = 739621) (by norm_num)
theorem B986197 : Blo 876568 986197 := bbase (se 8 (by rfl) ⟨5778, by rfl⟩ : syracuseStep 986197 = 11557) (by norm_num)
theorem B986233 : Blo 876568 986233 := bbase (se 2 (by rfl) ⟨369837, by rfl⟩ : syracuseStep 986233 = 739675) (by norm_num)
theorem B986269 : Blo 876568 986269 := bbase (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) (by norm_num)
theorem B986305 : Blo 876568 986305 := bbase (se 2 (by rfl) ⟨369864, by rfl⟩ : syracuseStep 986305 = 739729) (by norm_num)
theorem B2002117 : Blo 876568 2002117 := bbase (se 4 (by rfl) ⟨187698, by rfl⟩ : syracuseStep 2002117 = 375397) (by norm_num)
theorem B986341 : Blo 876568 986341 := bbase (se 4 (by rfl) ⟨92469, by rfl⟩ : syracuseStep 986341 = 184939) (by norm_num)
theorem B986377 : Blo 876568 986377 := bbase (se 2 (by rfl) ⟨369891, by rfl⟩ : syracuseStep 986377 = 739783) (by norm_num)
theorem B986413 : Blo 876568 986413 := bbase (se 3 (by rfl) ⟨184952, by rfl⟩ : syracuseStep 986413 = 369905) (by norm_num)
theorem B986449 : Blo 876568 986449 := bbase (se 2 (by rfl) ⟨369918, by rfl⟩ : syracuseStep 986449 = 739837) (by norm_num)
theorem B986485 : Blo 876568 986485 := bbase (se 5 (by rfl) ⟨46241, by rfl⟩ : syracuseStep 986485 = 92483) (by norm_num)
theorem B986521 : Blo 876568 986521 := bbase (se 2 (by rfl) ⟨369945, by rfl⟩ : syracuseStep 986521 = 739891) (by norm_num)
theorem B986557 : Blo 876568 986557 := bbase (se 3 (by rfl) ⟨184979, by rfl⟩ : syracuseStep 986557 = 369959) (by norm_num)
theorem B1248709 : Blo 876568 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B986593 : Blo 876568 986593 := bbase (se 2 (by rfl) ⟨369972, by rfl⟩ : syracuseStep 986593 = 739945) (by norm_num)
theorem B7114229 : Blo 876568 7114229 := bbase (se 5 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 7114229 = 666959) (by norm_num)
theorem B986629 : Blo 876568 986629 := bbase (se 4 (by rfl) ⟨92496, by rfl⟩ : syracuseStep 986629 = 184993) (by norm_num)
theorem B986665 : Blo 876568 986665 := bbase (se 2 (by rfl) ⟨369999, by rfl⟩ : syracuseStep 986665 = 739999) (by norm_num)
theorem B986701 : Blo 876568 986701 := bbase (se 3 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 986701 = 370013) (by norm_num)
theorem B986737 : Blo 876568 986737 := bbase (se 2 (by rfl) ⟨370026, by rfl⟩ : syracuseStep 986737 = 740053) (by norm_num)
theorem B986773 : Blo 876568 986773 := bbase (se 6 (by rfl) ⟨23127, by rfl⟩ : syracuseStep 986773 = 46255) (by norm_num)
theorem B1805981 : Blo 876568 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B986809 : Blo 876568 986809 := bbase (se 2 (by rfl) ⟨370053, by rfl⟩ : syracuseStep 986809 = 740107) (by norm_num)
theorem B986845 : Blo 876568 986845 := bbase (se 3 (by rfl) ⟨185033, by rfl⟩ : syracuseStep 986845 = 370067) (by norm_num)
theorem B986881 : Blo 876568 986881 := bbase (se 2 (by rfl) ⟨370080, by rfl⟩ : syracuseStep 986881 = 740161) (by norm_num)
theorem B986917 : Blo 876568 986917 := bbase (se 4 (by rfl) ⟨92523, by rfl⟩ : syracuseStep 986917 = 185047) (by norm_num)
theorem B986953 : Blo 876568 986953 := bbase (se 2 (by rfl) ⟨370107, by rfl⟩ : syracuseStep 986953 = 740215) (by norm_num)
theorem B986989 : Blo 876568 986989 := bbase (se 3 (by rfl) ⟨185060, by rfl⟩ : syracuseStep 986989 = 370121) (by norm_num)
theorem B987025 : Blo 876568 987025 := bbase (se 2 (by rfl) ⟨370134, by rfl⟩ : syracuseStep 987025 = 740269) (by norm_num)
theorem B4231061 : Blo 876568 4231061 := bbase (se 6 (by rfl) ⟨99165, by rfl⟩ : syracuseStep 4231061 = 198331) (by norm_num)
theorem B987061 : Blo 876568 987061 := bbase (se 5 (by rfl) ⟨46268, by rfl⟩ : syracuseStep 987061 = 92537) (by norm_num)
theorem B987097 : Blo 876568 987097 := bbase (se 2 (by rfl) ⟨370161, by rfl⟩ : syracuseStep 987097 = 740323) (by norm_num)
theorem B987133 : Blo 876568 987133 := bbase (se 3 (by rfl) ⟨185087, by rfl⟩ : syracuseStep 987133 = 370175) (by norm_num)
theorem B1249301 : Blo 876568 1249301 := bbase (se 6 (by rfl) ⟨29280, by rfl⟩ : syracuseStep 1249301 = 58561) (by norm_num)
theorem B987169 : Blo 876568 987169 := bbase (se 2 (by rfl) ⟨370188, by rfl⟩ : syracuseStep 987169 = 740377) (by norm_num)
theorem B1314869 : Blo 876568 1314869 := bbase (se 5 (by rfl) ⟨61634, by rfl⟩ : syracuseStep 1314869 = 123269) (by norm_num)
theorem B987205 : Blo 876568 987205 := bbase (se 4 (by rfl) ⟨92550, by rfl⟩ : syracuseStep 987205 = 185101) (by norm_num)
theorem B1314893 : Blo 876568 1314893 := bbase (se 3 (by rfl) ⟨246542, by rfl⟩ : syracuseStep 1314893 = 493085) (by norm_num)
theorem B1314917 : Blo 876568 1314917 := bbase (se 4 (by rfl) ⟨123273, by rfl⟩ : syracuseStep 1314917 = 246547) (by norm_num)
theorem B1249381 : Blo 876568 1249381 := bbase (se 4 (by rfl) ⟨117129, by rfl⟩ : syracuseStep 1249381 = 234259) (by norm_num)
theorem B987241 : Blo 876568 987241 := bbase (se 2 (by rfl) ⟨370215, by rfl⟩ : syracuseStep 987241 = 740431) (by norm_num)
theorem B1314941 : Blo 876568 1314941 := bbase (se 3 (by rfl) ⟨246551, by rfl⟩ : syracuseStep 1314941 = 493103) (by norm_num)
theorem B987277 : Blo 876568 987277 := bbase (se 3 (by rfl) ⟨185114, by rfl⟩ : syracuseStep 987277 = 370229) (by norm_num)
theorem B1314965 : Blo 876568 1314965 := bbase (se 6 (by rfl) ⟨30819, by rfl⟩ : syracuseStep 1314965 = 61639) (by norm_num)
theorem B1314989 : Blo 876568 1314989 := bbase (se 3 (by rfl) ⟨246560, by rfl⟩ : syracuseStep 1314989 = 493121) (by norm_num)
theorem B987313 : Blo 876568 987313 := bbase (se 2 (by rfl) ⟨370242, by rfl⟩ : syracuseStep 987313 = 740485) (by norm_num)
theorem B1315013 : Blo 876568 1315013 := bbase (se 4 (by rfl) ⟨123282, by rfl⟩ : syracuseStep 1315013 = 246565) (by norm_num)
theorem B987349 : Blo 876568 987349 := bbase (se 7 (by rfl) ⟨11570, by rfl⟩ : syracuseStep 987349 = 23141) (by norm_num)
theorem B1315037 : Blo 876568 1315037 := bbase (se 3 (by rfl) ⟨246569, by rfl⟩ : syracuseStep 1315037 = 493139) (by norm_num)
theorem B1249501 : Blo 876568 1249501 := bbase (se 3 (by rfl) ⟨234281, by rfl⟩ : syracuseStep 1249501 = 468563) (by norm_num)
theorem B1315061 : Blo 876568 1315061 := bbase (se 5 (by rfl) ⟨61643, by rfl⟩ : syracuseStep 1315061 = 123287) (by norm_num)
theorem B7508213 : Blo 876568 7508213 := bbase (se 5 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 7508213 = 703895) (by norm_num)
theorem B987385 : Blo 876568 987385 := bbase (se 2 (by rfl) ⟨370269, by rfl⟩ : syracuseStep 987385 = 740539) (by norm_num)
theorem B1315085 : Blo 876568 1315085 := bbase (se 3 (by rfl) ⟨246578, by rfl⟩ : syracuseStep 1315085 = 493157) (by norm_num)
theorem B987421 : Blo 876568 987421 := bbase (se 3 (by rfl) ⟨185141, by rfl⟩ : syracuseStep 987421 = 370283) (by norm_num)
theorem B1315109 : Blo 876568 1315109 := bbase (se 4 (by rfl) ⟨123291, by rfl⟩ : syracuseStep 1315109 = 246583) (by norm_num)
theorem B1315133 : Blo 876568 1315133 := bbase (se 3 (by rfl) ⟨246587, by rfl⟩ : syracuseStep 1315133 = 493175) (by norm_num)
theorem B1249597 : Blo 876568 1249597 := bbase (se 3 (by rfl) ⟨234299, by rfl⟩ : syracuseStep 1249597 = 468599) (by norm_num)
theorem B987457 : Blo 876568 987457 := bbase (se 2 (by rfl) ⟨370296, by rfl⟩ : syracuseStep 987457 = 740593) (by norm_num)
theorem B1315157 : Blo 876568 1315157 := bbase (se 10 (by rfl) ⟨1926, by rfl⟩ : syracuseStep 1315157 = 3853) (by norm_num)
theorem B987493 : Blo 876568 987493 := bbase (se 4 (by rfl) ⟨92577, by rfl⟩ : syracuseStep 987493 = 185155) (by norm_num)
theorem B1315181 : Blo 876568 1315181 := bbase (se 3 (by rfl) ⟨246596, by rfl⟩ : syracuseStep 1315181 = 493193) (by norm_num)
theorem B1315205 : Blo 876568 1315205 := bbase (se 4 (by rfl) ⟨123300, by rfl⟩ : syracuseStep 1315205 = 246601) (by norm_num)
theorem B987529 : Blo 876568 987529 := bbase (se 2 (by rfl) ⟨370323, by rfl⟩ : syracuseStep 987529 = 740647) (by norm_num)
theorem B1315229 : Blo 876568 1315229 := bbase (se 3 (by rfl) ⟨246605, by rfl⟩ : syracuseStep 1315229 = 493211) (by norm_num)
theorem B987565 : Blo 876568 987565 := bbase (se 3 (by rfl) ⟨185168, by rfl⟩ : syracuseStep 987565 = 370337) (by norm_num)
theorem B1315253 : Blo 876568 1315253 := bbase (se 5 (by rfl) ⟨61652, by rfl⟩ : syracuseStep 1315253 = 123305) (by norm_num)
theorem B1315277 : Blo 876568 1315277 := bbase (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) (by norm_num)
theorem B987601 : Blo 876568 987601 := bbase (se 2 (by rfl) ⟨370350, by rfl⟩ : syracuseStep 987601 = 740701) (by norm_num)
theorem B1315301 : Blo 876568 1315301 := bbase (se 4 (by rfl) ⟨123309, by rfl⟩ : syracuseStep 1315301 = 246619) (by norm_num)
theorem B987637 : Blo 876568 987637 := bbase (se 5 (by rfl) ⟨46295, by rfl⟩ : syracuseStep 987637 = 92591) (by norm_num)
theorem B1315325 : Blo 876568 1315325 := bbase (se 3 (by rfl) ⟨246623, by rfl⟩ : syracuseStep 1315325 = 493247) (by norm_num)
theorem B1315349 : Blo 876568 1315349 := bbase (se 6 (by rfl) ⟨30828, by rfl⟩ : syracuseStep 1315349 = 61657) (by norm_num)
theorem B987673 : Blo 876568 987673 := bbase (se 2 (by rfl) ⟨370377, by rfl⟩ : syracuseStep 987673 = 740755) (by norm_num)
theorem B1053229 : Blo 876568 1053229 := bbase (se 3 (by rfl) ⟨197480, by rfl⟩ : syracuseStep 1053229 = 394961) (by norm_num)
theorem B1315373 : Blo 876568 1315373 := bbase (se 3 (by rfl) ⟨246632, by rfl⟩ : syracuseStep 1315373 = 493265) (by norm_num)
theorem B987709 : Blo 876568 987709 := bbase (se 3 (by rfl) ⟨185195, by rfl⟩ : syracuseStep 987709 = 370391) (by norm_num)
theorem B1315397 : Blo 876568 1315397 := bbase (se 4 (by rfl) ⟨123318, by rfl⟩ : syracuseStep 1315397 = 246637) (by norm_num)
theorem B1315421 : Blo 876568 1315421 := bbase (se 3 (by rfl) ⟨246641, by rfl⟩ : syracuseStep 1315421 = 493283) (by norm_num)
theorem B987745 : Blo 876568 987745 := bbase (se 2 (by rfl) ⟨370404, by rfl⟩ : syracuseStep 987745 = 740809) (by norm_num)
theorem B1479269 : Blo 876568 1479269 := bbase (se 4 (by rfl) ⟨138681, by rfl⟩ : syracuseStep 1479269 = 277363) (by norm_num)
theorem B1315445 : Blo 876568 1315445 := bbase (se 5 (by rfl) ⟨61661, by rfl⟩ : syracuseStep 1315445 = 123323) (by norm_num)
theorem B1872517 : Blo 876568 1872517 := bbase (se 4 (by rfl) ⟨175548, by rfl⟩ : syracuseStep 1872517 = 351097) (by norm_num)
theorem B987781 : Blo 876568 987781 := bbase (se 4 (by rfl) ⟨92604, by rfl⟩ : syracuseStep 987781 = 185209) (by norm_num)
theorem B1315469 : Blo 876568 1315469 := bbase (se 3 (by rfl) ⟨246650, by rfl⟩ : syracuseStep 1315469 = 493301) (by norm_num)
theorem B1053329 : Blo 876568 1053329 := bbase (se 2 (by rfl) ⟨394998, by rfl⟩ : syracuseStep 1053329 = 789997) (by norm_num)
theorem B1315493 : Blo 876568 1315493 := bbase (se 4 (by rfl) ⟨123327, by rfl⟩ : syracuseStep 1315493 = 246655) (by norm_num)
theorem B987817 : Blo 876568 987817 := bbase (se 2 (by rfl) ⟨370431, by rfl⟩ : syracuseStep 987817 = 740863) (by norm_num)
theorem B1315517 : Blo 876568 1315517 := bbase (se 3 (by rfl) ⟨246659, by rfl⟩ : syracuseStep 1315517 = 493319) (by norm_num)
theorem B987853 : Blo 876568 987853 := bbase (se 3 (by rfl) ⟨185222, by rfl⟩ : syracuseStep 987853 = 370445) (by norm_num)
theorem B1315541 : Blo 876568 1315541 := bbase (se 7 (by rfl) ⟨15416, by rfl⟩ : syracuseStep 1315541 = 30833) (by norm_num)
theorem B1479397 : Blo 876568 1479397 := bbase (se 4 (by rfl) ⟨138693, by rfl⟩ : syracuseStep 1479397 = 277387) (by norm_num)
theorem B1315565 : Blo 876568 1315565 := bbase (se 3 (by rfl) ⟨246668, by rfl⟩ : syracuseStep 1315565 = 493337) (by norm_num)
theorem B987889 : Blo 876568 987889 := bbase (se 2 (by rfl) ⟨370458, by rfl⟩ : syracuseStep 987889 = 740917) (by norm_num)
theorem B1315589 : Blo 876568 1315589 := bbase (se 4 (by rfl) ⟨123336, by rfl⟩ : syracuseStep 1315589 = 246673) (by norm_num)
theorem B987925 : Blo 876568 987925 := bbase (se 6 (by rfl) ⟨23154, by rfl⟩ : syracuseStep 987925 = 46309) (by norm_num)
theorem B1315613 : Blo 876568 1315613 := bbase (se 3 (by rfl) ⟨246677, by rfl⟩ : syracuseStep 1315613 = 493355) (by norm_num)
theorem B1250093 : Blo 876568 1250093 := bbase (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) (by norm_num)
theorem B1315637 : Blo 876568 1315637 := bbase (se 5 (by rfl) ⟨61670, by rfl⟩ : syracuseStep 1315637 = 123341) (by norm_num)
theorem B987961 : Blo 876568 987961 := bbase (se 2 (by rfl) ⟨370485, by rfl⟩ : syracuseStep 987961 = 740971) (by norm_num)
theorem B1479485 : Blo 876568 1479485 := bbase (se 3 (by rfl) ⟨277403, by rfl⟩ : syracuseStep 1479485 = 554807) (by norm_num)
theorem B1315661 : Blo 876568 1315661 := bbase (se 3 (by rfl) ⟨246686, by rfl⟩ : syracuseStep 1315661 = 493373) (by norm_num)
theorem B987997 : Blo 876568 987997 := bbase (se 3 (by rfl) ⟨185249, by rfl⟩ : syracuseStep 987997 = 370499) (by norm_num)
theorem B1315685 : Blo 876568 1315685 := bbase (se 4 (by rfl) ⟨123345, by rfl⟩ : syracuseStep 1315685 = 246691) (by norm_num)
theorem B1315709 : Blo 876568 1315709 := bbase (se 3 (by rfl) ⟨246695, by rfl⟩ : syracuseStep 1315709 = 493391) (by norm_num)
theorem B988033 : Blo 876568 988033 := bbase (se 2 (by rfl) ⟨370512, by rfl⟩ : syracuseStep 988033 = 741025) (by norm_num)
theorem B1315733 : Blo 876568 1315733 := bbase (se 6 (by rfl) ⟨30837, by rfl⟩ : syracuseStep 1315733 = 61675) (by norm_num)
theorem B988069 : Blo 876568 988069 := bbase (se 4 (by rfl) ⟨92631, by rfl⟩ : syracuseStep 988069 = 185263) (by norm_num)
theorem B1315757 : Blo 876568 1315757 := bbase (se 3 (by rfl) ⟨246704, by rfl⟩ : syracuseStep 1315757 = 493409) (by norm_num)
theorem B1479613 : Blo 876568 1479613 := bbase (se 3 (by rfl) ⟨277427, by rfl⟩ : syracuseStep 1479613 = 554855) (by norm_num)
theorem B1315781 : Blo 876568 1315781 := bbase (se 4 (by rfl) ⟨123354, by rfl⟩ : syracuseStep 1315781 = 246709) (by norm_num)
theorem B988105 : Blo 876568 988105 := bbase (se 2 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 988105 = 741079) (by norm_num)
theorem B1315805 : Blo 876568 1315805 := bbase (se 3 (by rfl) ⟨246713, by rfl⟩ : syracuseStep 1315805 = 493427) (by norm_num)
theorem B988141 : Blo 876568 988141 := bbase (se 3 (by rfl) ⟨185276, by rfl⟩ : syracuseStep 988141 = 370553) (by norm_num)
theorem B1315829 : Blo 876568 1315829 := bbase (se 5 (by rfl) ⟨61679, by rfl⟩ : syracuseStep 1315829 = 123359) (by norm_num)
theorem B1315853 : Blo 876568 1315853 := bbase (se 3 (by rfl) ⟨246722, by rfl⟩ : syracuseStep 1315853 = 493445) (by norm_num)
theorem B988177 : Blo 876568 988177 := bbase (se 2 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 988177 = 741133) (by norm_num)
theorem B1479701 : Blo 876568 1479701 := bbase (se 6 (by rfl) ⟨34680, by rfl⟩ : syracuseStep 1479701 = 69361) (by norm_num)
theorem B1315877 : Blo 876568 1315877 := bbase (se 4 (by rfl) ⟨123363, by rfl⟩ : syracuseStep 1315877 = 246727) (by norm_num)
theorem B988213 : Blo 876568 988213 := bbase (se 5 (by rfl) ⟨46322, by rfl⟩ : syracuseStep 988213 = 92645) (by norm_num)
theorem B1315901 : Blo 876568 1315901 := bbase (se 3 (by rfl) ⟨246731, by rfl⟩ : syracuseStep 1315901 = 493463) (by norm_num)
theorem B1315925 : Blo 876568 1315925 := bbase (se 8 (by rfl) ⟨7710, by rfl⟩ : syracuseStep 1315925 = 15421) (by norm_num)
theorem B988249 : Blo 876568 988249 := bbase (se 2 (by rfl) ⟨370593, by rfl⟩ : syracuseStep 988249 = 741187) (by norm_num)
theorem B1315949 : Blo 876568 1315949 := bbase (se 3 (by rfl) ⟨246740, by rfl⟩ : syracuseStep 1315949 = 493481) (by norm_num)
theorem B988285 : Blo 876568 988285 := bbase (se 3 (by rfl) ⟨185303, by rfl⟩ : syracuseStep 988285 = 370607) (by norm_num)
theorem B1315973 : Blo 876568 1315973 := bbase (se 4 (by rfl) ⟨123372, by rfl⟩ : syracuseStep 1315973 = 246745) (by norm_num)
theorem B1479829 : Blo 876568 1479829 := bbase (se 6 (by rfl) ⟨34683, by rfl⟩ : syracuseStep 1479829 = 69367) (by norm_num)
theorem B1315997 : Blo 876568 1315997 := bbase (se 3 (by rfl) ⟨246749, by rfl⟩ : syracuseStep 1315997 = 493499) (by norm_num)
theorem B988321 : Blo 876568 988321 := bbase (se 2 (by rfl) ⟨370620, by rfl⟩ : syracuseStep 988321 = 741241) (by norm_num)
theorem B1316021 : Blo 876568 1316021 := bbase (se 5 (by rfl) ⟨61688, by rfl⟩ : syracuseStep 1316021 = 123377) (by norm_num)
theorem B988357 : Blo 876568 988357 := bbase (se 4 (by rfl) ⟨92658, by rfl⟩ : syracuseStep 988357 = 185317) (by norm_num)
theorem B1316045 : Blo 876568 1316045 := bbase (se 3 (by rfl) ⟨246758, by rfl⟩ : syracuseStep 1316045 = 493517) (by norm_num)
theorem B1316069 : Blo 876568 1316069 := bbase (se 4 (by rfl) ⟨123381, by rfl⟩ : syracuseStep 1316069 = 246763) (by norm_num)
theorem B988393 : Blo 876568 988393 := bbase (se 2 (by rfl) ⟨370647, by rfl⟩ : syracuseStep 988393 = 741295) (by norm_num)
theorem B1479917 : Blo 876568 1479917 := bbase (se 3 (by rfl) ⟨277484, by rfl⟩ : syracuseStep 1479917 = 554969) (by norm_num)
theorem B1316093 : Blo 876568 1316093 := bbase (se 3 (by rfl) ⟨246767, by rfl⟩ : syracuseStep 1316093 = 493535) (by norm_num)
theorem B988429 : Blo 876568 988429 := bbase (se 3 (by rfl) ⟨185330, by rfl⟩ : syracuseStep 988429 = 370661) (by norm_num)
theorem B1316117 : Blo 876568 1316117 := bbase (se 6 (by rfl) ⟨30846, by rfl⟩ : syracuseStep 1316117 = 61693) (by norm_num)
theorem B1316141 : Blo 876568 1316141 := bbase (se 3 (by rfl) ⟨246776, by rfl⟩ : syracuseStep 1316141 = 493553) (by norm_num)
theorem B988465 : Blo 876568 988465 := bbase (se 2 (by rfl) ⟨370674, by rfl⟩ : syracuseStep 988465 = 741349) (by norm_num)
theorem B1316165 : Blo 876568 1316165 := bbase (se 4 (by rfl) ⟨123390, by rfl⟩ : syracuseStep 1316165 = 246781) (by norm_num)
theorem B1250645 : Blo 876568 1250645 := bbase (se 14 (by rfl) ⟨114, by rfl⟩ : syracuseStep 1250645 = 229) (by norm_num)
theorem B988501 : Blo 876568 988501 := bbase (se 14 (by rfl) ⟨90, by rfl⟩ : syracuseStep 988501 = 181) (by norm_num)
theorem B1316189 : Blo 876568 1316189 := bbase (se 3 (by rfl) ⟨246785, by rfl⟩ : syracuseStep 1316189 = 493571) (by norm_num)
theorem B1480045 : Blo 876568 1480045 := bbase (se 3 (by rfl) ⟨277508, by rfl⟩ : syracuseStep 1480045 = 555017) (by norm_num)
theorem B1316213 : Blo 876568 1316213 := bbase (se 5 (by rfl) ⟨61697, by rfl⟩ : syracuseStep 1316213 = 123395) (by norm_num)
theorem B988537 : Blo 876568 988537 := bbase (se 2 (by rfl) ⟨370701, by rfl⟩ : syracuseStep 988537 = 741403) (by norm_num)
theorem B1316237 : Blo 876568 1316237 := bbase (se 3 (by rfl) ⟨246794, by rfl⟩ : syracuseStep 1316237 = 493589) (by norm_num)
theorem B988573 : Blo 876568 988573 := bbase (se 3 (by rfl) ⟨185357, by rfl⟩ : syracuseStep 988573 = 370715) (by norm_num)
theorem B1054117 : Blo 876568 1054117 := bbase (se 4 (by rfl) ⟨98823, by rfl⟩ : syracuseStep 1054117 = 197647) (by norm_num)
theorem B1316261 : Blo 876568 1316261 := bbase (se 4 (by rfl) ⟨123399, by rfl⟩ : syracuseStep 1316261 = 246799) (by norm_num)
theorem B2004389 : Blo 876568 2004389 := bbase (se 4 (by rfl) ⟨187911, by rfl⟩ : syracuseStep 2004389 = 375823) (by norm_num)
theorem B1316285 : Blo 876568 1316285 := bbase (se 3 (by rfl) ⟨246803, by rfl⟩ : syracuseStep 1316285 = 493607) (by norm_num)
theorem B988609 : Blo 876568 988609 := bbase (se 2 (by rfl) ⟨370728, by rfl⟩ : syracuseStep 988609 = 741457) (by norm_num)
theorem B1480133 : Blo 876568 1480133 := bbase (se 4 (by rfl) ⟨138762, by rfl⟩ : syracuseStep 1480133 = 277525) (by norm_num)
theorem B1185229 : Blo 876568 1185229 := bbase (se 3 (by rfl) ⟨222230, by rfl⟩ : syracuseStep 1185229 = 444461) (by norm_num)
theorem B1316309 : Blo 876568 1316309 := bbase (se 7 (by rfl) ⟨15425, by rfl⟩ : syracuseStep 1316309 = 30851) (by norm_num)
theorem B988645 : Blo 876568 988645 := bbase (se 4 (by rfl) ⟨92685, by rfl⟩ : syracuseStep 988645 = 185371) (by norm_num)
theorem B1316333 : Blo 876568 1316333 := bbase (se 3 (by rfl) ⟨246812, by rfl⟩ : syracuseStep 1316333 = 493625) (by norm_num)
theorem B1873405 : Blo 876568 1873405 := bbase (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) (by norm_num)
theorem B1316357 : Blo 876568 1316357 := bbase (se 4 (by rfl) ⟨123408, by rfl⟩ : syracuseStep 1316357 = 246817) (by norm_num)
theorem B988681 : Blo 876568 988681 := bbase (se 2 (by rfl) ⟨370755, by rfl⟩ : syracuseStep 988681 = 741511) (by norm_num)
theorem B1316381 : Blo 876568 1316381 := bbase (se 3 (by rfl) ⟨246821, by rfl⟩ : syracuseStep 1316381 = 493643) (by norm_num)
theorem B988717 : Blo 876568 988717 := bbase (se 3 (by rfl) ⟨185384, by rfl⟩ : syracuseStep 988717 = 370769) (by norm_num)
theorem B1316405 : Blo 876568 1316405 := bbase (se 5 (by rfl) ⟨61706, by rfl⟩ : syracuseStep 1316405 = 123413) (by norm_num)
theorem B1480261 : Blo 876568 1480261 := bbase (se 4 (by rfl) ⟨138774, by rfl⟩ : syracuseStep 1480261 = 277549) (by norm_num)
theorem B1316429 : Blo 876568 1316429 := bbase (se 3 (by rfl) ⟨246830, by rfl⟩ : syracuseStep 1316429 = 493661) (by norm_num)
theorem B988753 : Blo 876568 988753 := bbase (se 2 (by rfl) ⟨370782, by rfl⟩ : syracuseStep 988753 = 741565) (by norm_num)
theorem B1316453 : Blo 876568 1316453 := bbase (se 4 (by rfl) ⟨123417, by rfl⟩ : syracuseStep 1316453 = 246835) (by norm_num)
theorem B1873525 : Blo 876568 1873525 := bbase (se 5 (by rfl) ⟨87821, by rfl⟩ : syracuseStep 1873525 = 175643) (by norm_num)
theorem B988789 : Blo 876568 988789 := bbase (se 5 (by rfl) ⟨46349, by rfl⟩ : syracuseStep 988789 = 92699) (by norm_num)
theorem B1316477 : Blo 876568 1316477 := bbase (se 3 (by rfl) ⟨246839, by rfl⟩ : syracuseStep 1316477 = 493679) (by norm_num)
theorem B1316501 : Blo 876568 1316501 := bbase (se 6 (by rfl) ⟨30855, by rfl⟩ : syracuseStep 1316501 = 61711) (by norm_num)
theorem B7214741 : Blo 876568 7214741 := bbase (se 6 (by rfl) ⟨169095, by rfl⟩ : syracuseStep 7214741 = 338191) (by norm_num)
theorem B988825 : Blo 876568 988825 := bbase (se 2 (by rfl) ⟨370809, by rfl⟩ : syracuseStep 988825 = 741619) (by norm_num)
theorem B1480349 : Blo 876568 1480349 := bbase (se 3 (by rfl) ⟨277565, by rfl⟩ : syracuseStep 1480349 = 555131) (by norm_num)
theorem B1316525 : Blo 876568 1316525 := bbase (se 3 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 1316525 = 493697) (by norm_num)
theorem B988861 : Blo 876568 988861 := bbase (se 3 (by rfl) ⟨185411, by rfl⟩ : syracuseStep 988861 = 370823) (by norm_num)
theorem B1316549 : Blo 876568 1316549 := bbase (se 4 (by rfl) ⟨123426, by rfl⟩ : syracuseStep 1316549 = 246853) (by norm_num)
theorem B1316573 : Blo 876568 1316573 := bbase (se 3 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 1316573 = 493715) (by norm_num)
theorem B988897 : Blo 876568 988897 := bbase (se 2 (by rfl) ⟨370836, by rfl⟩ : syracuseStep 988897 = 741673) (by norm_num)
theorem B1316597 : Blo 876568 1316597 := bbase (se 5 (by rfl) ⟨61715, by rfl⟩ : syracuseStep 1316597 = 123431) (by norm_num)
theorem B988933 : Blo 876568 988933 := bbase (se 4 (by rfl) ⟨92712, by rfl⟩ : syracuseStep 988933 = 185425) (by norm_num)
theorem B1316621 : Blo 876568 1316621 := bbase (se 3 (by rfl) ⟨246866, by rfl⟩ : syracuseStep 1316621 = 493733) (by norm_num)
theorem B1480477 : Blo 876568 1480477 := bbase (se 3 (by rfl) ⟨277589, by rfl⟩ : syracuseStep 1480477 = 555179) (by norm_num)
theorem B1316645 : Blo 876568 1316645 := bbase (se 4 (by rfl) ⟨123435, by rfl⟩ : syracuseStep 1316645 = 246871) (by norm_num)
theorem B988969 : Blo 876568 988969 := bbase (se 2 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 988969 = 741727) (by norm_num)
theorem B1316669 : Blo 876568 1316669 := bbase (se 3 (by rfl) ⟨246875, by rfl⟩ : syracuseStep 1316669 = 493751) (by norm_num)
theorem B989005 : Blo 876568 989005 := bbase (se 3 (by rfl) ⟨185438, by rfl⟩ : syracuseStep 989005 = 370877) (by norm_num)
theorem B14980949 : Blo 876568 14980949 := bbase (se 9 (by rfl) ⟨43889, by rfl⟩ : syracuseStep 14980949 = 87779) (by norm_num)
theorem B1316693 : Blo 876568 1316693 := bbase (se 9 (by rfl) ⟨3857, by rfl⟩ : syracuseStep 1316693 = 7715) (by norm_num)
theorem B1316717 : Blo 876568 1316717 := bbase (se 3 (by rfl) ⟨246884, by rfl⟩ : syracuseStep 1316717 = 493769) (by norm_num)
theorem B989041 : Blo 876568 989041 := bbase (se 2 (by rfl) ⟨370890, by rfl⟩ : syracuseStep 989041 = 741781) (by norm_num)
theorem B1873781 : Blo 876568 1873781 := bbase (se 5 (by rfl) ⟨87833, by rfl⟩ : syracuseStep 1873781 = 175667) (by norm_num)
theorem B1480565 : Blo 876568 1480565 := bbase (se 5 (by rfl) ⟨69401, by rfl⟩ : syracuseStep 1480565 = 138803) (by norm_num)
theorem B1316741 : Blo 876568 1316741 := bbase (se 4 (by rfl) ⟨123444, by rfl⟩ : syracuseStep 1316741 = 246889) (by norm_num)
theorem B989077 : Blo 876568 989077 := bbase (se 6 (by rfl) ⟨23181, by rfl⟩ : syracuseStep 989077 = 46363) (by norm_num)
theorem B1316765 : Blo 876568 1316765 := bbase (se 3 (by rfl) ⟨246893, by rfl⟩ : syracuseStep 1316765 = 493787) (by norm_num)
theorem B1316789 : Blo 876568 1316789 := bbase (se 5 (by rfl) ⟨61724, by rfl⟩ : syracuseStep 1316789 = 123449) (by norm_num)
theorem B989113 : Blo 876568 989113 := bbase (se 2 (by rfl) ⟨370917, by rfl⟩ : syracuseStep 989113 = 741835) (by norm_num)
theorem B1316813 : Blo 876568 1316813 := bbase (se 3 (by rfl) ⟨246902, by rfl⟩ : syracuseStep 1316813 = 493805) (by norm_num)
theorem B2856917 : Blo 876568 2856917 := bbase (se 7 (by rfl) ⟨33479, by rfl⟩ : syracuseStep 2856917 = 66959) (by norm_num)
theorem B989149 : Blo 876568 989149 := bbase (se 3 (by rfl) ⟨185465, by rfl⟩ : syracuseStep 989149 = 370931) (by norm_num)
theorem B1316837 : Blo 876568 1316837 := bbase (se 4 (by rfl) ⟨123453, by rfl⟩ : syracuseStep 1316837 = 246907) (by norm_num)
theorem B1480693 : Blo 876568 1480693 := bbase (se 5 (by rfl) ⟨69407, by rfl⟩ : syracuseStep 1480693 = 138815) (by norm_num)
theorem B1316861 : Blo 876568 1316861 := bbase (se 3 (by rfl) ⟨246911, by rfl⟩ : syracuseStep 1316861 = 493823) (by norm_num)
theorem B989185 : Blo 876568 989185 := bbase (se 2 (by rfl) ⟨370944, by rfl⟩ : syracuseStep 989185 = 741889) (by norm_num)
theorem B1316885 : Blo 876568 1316885 := bbase (se 6 (by rfl) ⟨30864, by rfl⟩ : syracuseStep 1316885 = 61729) (by norm_num)
theorem B989221 : Blo 876568 989221 := bbase (se 4 (by rfl) ⟨92739, by rfl⟩ : syracuseStep 989221 = 185479) (by norm_num)
theorem B1316909 : Blo 876568 1316909 := bbase (se 3 (by rfl) ⟨246920, by rfl⟩ : syracuseStep 1316909 = 493841) (by norm_num)
theorem B1316933 : Blo 876568 1316933 := bbase (se 4 (by rfl) ⟨123462, by rfl⟩ : syracuseStep 1316933 = 246925) (by norm_num)
theorem B1251397 : Blo 876568 1251397 := bbase (se 4 (by rfl) ⟨117318, by rfl⟩ : syracuseStep 1251397 = 234637) (by norm_num)
theorem B989257 : Blo 876568 989257 := bbase (se 2 (by rfl) ⟨370971, by rfl⟩ : syracuseStep 989257 = 741943) (by norm_num)
theorem B1480781 : Blo 876568 1480781 := bbase (se 3 (by rfl) ⟨277646, by rfl⟩ : syracuseStep 1480781 = 555293) (by norm_num)
theorem B1316957 : Blo 876568 1316957 := bbase (se 3 (by rfl) ⟨246929, by rfl⟩ : syracuseStep 1316957 = 493859) (by norm_num)
theorem B1054829 : Blo 876568 1054829 := bbase (se 3 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 1054829 = 395561) (by norm_num)
theorem B989293 : Blo 876568 989293 := bbase (se 3 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 989293 = 370985) (by norm_num)
theorem B2136181 : Blo 876568 2136181 := bbase (se 5 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 2136181 = 200267) (by norm_num)
theorem B1316981 : Blo 876568 1316981 := bbase (se 5 (by rfl) ⟨61733, by rfl⟩ : syracuseStep 1316981 = 123467) (by norm_num)
theorem B1972349 : Blo 876568 1972349 := bbase (se 3 (by rfl) ⟨369815, by rfl⟩ : syracuseStep 1972349 = 739631) (by norm_num)
theorem B1317005 : Blo 876568 1317005 := bbase (se 3 (by rfl) ⟨246938, by rfl⟩ : syracuseStep 1317005 = 493877) (by norm_num)
theorem B989329 : Blo 876568 989329 := bbase (se 2 (by rfl) ⟨370998, by rfl⟩ : syracuseStep 989329 = 741997) (by norm_num)
theorem B1317029 : Blo 876568 1317029 := bbase (se 4 (by rfl) ⟨123471, by rfl⟩ : syracuseStep 1317029 = 246943) (by norm_num)
theorem B989365 : Blo 876568 989365 := bbase (se 5 (by rfl) ⟨46376, by rfl⟩ : syracuseStep 989365 = 92753) (by norm_num)
theorem B1317053 : Blo 876568 1317053 := bbase (se 3 (by rfl) ⟨246947, by rfl⟩ : syracuseStep 1317053 = 493895) (by norm_num)
theorem B1972421 : Blo 876568 1972421 := bbase (se 4 (by rfl) ⟨184914, by rfl⟩ : syracuseStep 1972421 = 369829) (by norm_num)
theorem B1480909 : Blo 876568 1480909 := bbase (se 3 (by rfl) ⟨277670, by rfl⟩ : syracuseStep 1480909 = 555341) (by norm_num)
theorem B1317077 : Blo 876568 1317077 := bbase (se 7 (by rfl) ⟨15434, by rfl⟩ : syracuseStep 1317077 = 30869) (by norm_num)
theorem B989401 : Blo 876568 989401 := bbase (se 2 (by rfl) ⟨371025, by rfl⟩ : syracuseStep 989401 = 742051) (by norm_num)
theorem B1317101 : Blo 876568 1317101 := bbase (se 3 (by rfl) ⟨246956, by rfl⟩ : syracuseStep 1317101 = 493913) (by norm_num)
theorem B2005229 : Blo 876568 2005229 := bbase (se 3 (by rfl) ⟨375980, by rfl⟩ : syracuseStep 2005229 = 751961) (by norm_num)
theorem B2496757 : Blo 876568 2496757 := bbase (se 5 (by rfl) ⟨117035, by rfl⟩ : syracuseStep 2496757 = 234071) (by norm_num)
theorem B989437 : Blo 876568 989437 := bbase (se 3 (by rfl) ⟨185519, by rfl⟩ : syracuseStep 989437 = 371039) (by norm_num)
theorem B1317125 : Blo 876568 1317125 := bbase (se 4 (by rfl) ⟨123480, by rfl⟩ : syracuseStep 1317125 = 246961) (by norm_num)
theorem B1972493 : Blo 876568 1972493 := bbase (se 3 (by rfl) ⟨369842, by rfl⟩ : syracuseStep 1972493 = 739685) (by norm_num)
theorem B1317149 : Blo 876568 1317149 := bbase (se 3 (by rfl) ⟨246965, by rfl⟩ : syracuseStep 1317149 = 493931) (by norm_num)
theorem B989473 : Blo 876568 989473 := bbase (se 2 (by rfl) ⟨371052, by rfl⟩ : syracuseStep 989473 = 742105) (by norm_num)
theorem B1480997 : Blo 876568 1480997 := bbase (se 4 (by rfl) ⟨138843, by rfl⟩ : syracuseStep 1480997 = 277687) (by norm_num)
theorem B1317173 : Blo 876568 1317173 := bbase (se 5 (by rfl) ⟨61742, by rfl⟩ : syracuseStep 1317173 = 123485) (by norm_num)
theorem B989509 : Blo 876568 989509 := bbase (se 4 (by rfl) ⟨92766, by rfl⟩ : syracuseStep 989509 = 185533) (by norm_num)
theorem B1317197 : Blo 876568 1317197 := bbase (se 3 (by rfl) ⟨246974, by rfl⟩ : syracuseStep 1317197 = 493949) (by norm_num)
theorem B1972565 : Blo 876568 1972565 := bbase (se 10 (by rfl) ⟨2889, by rfl⟩ : syracuseStep 1972565 = 5779) (by norm_num)
theorem B1317221 : Blo 876568 1317221 := bbase (se 4 (by rfl) ⟨123489, by rfl⟩ : syracuseStep 1317221 = 246979) (by norm_num)
theorem B989545 : Blo 876568 989545 := bbase (se 2 (by rfl) ⟨371079, by rfl⟩ : syracuseStep 989545 = 742159) (by norm_num)
theorem B1317245 : Blo 876568 1317245 := bbase (se 3 (by rfl) ⟨246983, by rfl⟩ : syracuseStep 1317245 = 493967) (by norm_num)
theorem B989581 : Blo 876568 989581 := bbase (se 3 (by rfl) ⟨185546, by rfl⟩ : syracuseStep 989581 = 371093) (by norm_num)
theorem B1317269 : Blo 876568 1317269 := bbase (se 6 (by rfl) ⟨30873, by rfl⟩ : syracuseStep 1317269 = 61747) (by norm_num)
theorem B1972637 : Blo 876568 1972637 := bbase (se 3 (by rfl) ⟨369869, by rfl⟩ : syracuseStep 1972637 = 739739) (by norm_num)
theorem B1481125 : Blo 876568 1481125 := bbase (se 4 (by rfl) ⟨138855, by rfl⟩ : syracuseStep 1481125 = 277711) (by norm_num)
theorem B1317293 : Blo 876568 1317293 := bbase (se 3 (by rfl) ⟨246992, by rfl⟩ : syracuseStep 1317293 = 493985) (by norm_num)
theorem B989617 : Blo 876568 989617 := bbase (se 2 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 989617 = 742213) (by norm_num)
theorem B1055165 : Blo 876568 1055165 := bbase (se 3 (by rfl) ⟨197843, by rfl⟩ : syracuseStep 1055165 = 395687) (by norm_num)
theorem B1317317 : Blo 876568 1317317 := bbase (se 4 (by rfl) ⟨123498, by rfl⟩ : syracuseStep 1317317 = 246997) (by norm_num)
theorem B3807701 : Blo 876568 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B989653 : Blo 876568 989653 := bbase (se 7 (by rfl) ⟨11597, by rfl⟩ : syracuseStep 989653 = 23195) (by norm_num)
theorem B1317341 : Blo 876568 1317341 := bbase (se 3 (by rfl) ⟨247001, by rfl⟩ : syracuseStep 1317341 = 494003) (by norm_num)
theorem B1972709 : Blo 876568 1972709 := bbase (se 4 (by rfl) ⟨184941, by rfl⟩ : syracuseStep 1972709 = 369883) (by norm_num)
theorem B1317365 : Blo 876568 1317365 := bbase (se 5 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 1317365 = 123503) (by norm_num)
theorem B989689 : Blo 876568 989689 := bbase (se 2 (by rfl) ⟨371133, by rfl⟩ : syracuseStep 989689 = 742267) (by norm_num)
theorem B1481213 : Blo 876568 1481213 := bbase (se 3 (by rfl) ⟨277727, by rfl⟩ : syracuseStep 1481213 = 555455) (by norm_num)
theorem B2005501 : Blo 876568 2005501 := bbase (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) (by norm_num)
theorem B1317389 : Blo 876568 1317389 := bbase (se 3 (by rfl) ⟨247010, by rfl⟩ : syracuseStep 1317389 = 494021) (by norm_num)
theorem B989725 : Blo 876568 989725 := bbase (se 3 (by rfl) ⟨185573, by rfl⟩ : syracuseStep 989725 = 371147) (by norm_num)
theorem B1317413 : Blo 876568 1317413 := bbase (se 4 (by rfl) ⟨123507, by rfl⟩ : syracuseStep 1317413 = 247015) (by norm_num)
theorem B1972781 : Blo 876568 1972781 := bbase (se 3 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 1972781 = 739793) (by norm_num)
theorem B1055281 : Blo 876568 1055281 := bbase (se 2 (by rfl) ⟨395730, by rfl⟩ : syracuseStep 1055281 = 791461) (by norm_num)
theorem B1317437 : Blo 876568 1317437 := bbase (se 3 (by rfl) ⟨247019, by rfl⟩ : syracuseStep 1317437 = 494039) (by norm_num)
theorem B989761 : Blo 876568 989761 := bbase (se 2 (by rfl) ⟨371160, by rfl⟩ : syracuseStep 989761 = 742321) (by norm_num)
theorem B1055305 : Blo 876568 1055305 := bbase (se 2 (by rfl) ⟨395739, by rfl⟩ : syracuseStep 1055305 = 791479) (by norm_num)
theorem B1317461 : Blo 876568 1317461 := bbase (se 8 (by rfl) ⟨7719, by rfl⟩ : syracuseStep 1317461 = 15439) (by norm_num)
theorem B989797 : Blo 876568 989797 := bbase (se 4 (by rfl) ⟨92793, by rfl⟩ : syracuseStep 989797 = 185587) (by norm_num)
theorem B1317485 : Blo 876568 1317485 := bbase (se 3 (by rfl) ⟨247028, by rfl⟩ : syracuseStep 1317485 = 494057) (by norm_num)
theorem B1972853 : Blo 876568 1972853 := bbase (se 5 (by rfl) ⟨92477, by rfl⟩ : syracuseStep 1972853 = 184955) (by norm_num)
theorem B1481341 : Blo 876568 1481341 := bbase (se 3 (by rfl) ⟨277751, by rfl⟩ : syracuseStep 1481341 = 555503) (by norm_num)
theorem B1317509 : Blo 876568 1317509 := bbase (se 4 (by rfl) ⟨123516, by rfl⟩ : syracuseStep 1317509 = 247033) (by norm_num)
theorem B989833 : Blo 876568 989833 := bbase (se 2 (by rfl) ⟨371187, by rfl⟩ : syracuseStep 989833 = 742375) (by norm_num)
theorem B1317533 : Blo 876568 1317533 := bbase (se 3 (by rfl) ⟨247037, by rfl⟩ : syracuseStep 1317533 = 494075) (by norm_num)
theorem B989869 : Blo 876568 989869 := bbase (se 3 (by rfl) ⟨185600, by rfl⟩ : syracuseStep 989869 = 371201) (by norm_num)
theorem B1317557 : Blo 876568 1317557 := bbase (se 5 (by rfl) ⟨61760, by rfl⟩ : syracuseStep 1317557 = 123521) (by norm_num)
theorem B1972925 : Blo 876568 1972925 := bbase (se 3 (by rfl) ⟨369923, by rfl⟩ : syracuseStep 1972925 = 739847) (by norm_num)
theorem B1317581 : Blo 876568 1317581 := bbase (se 3 (by rfl) ⟨247046, by rfl⟩ : syracuseStep 1317581 = 494093) (by norm_num)
theorem B989905 : Blo 876568 989905 := bbase (se 2 (by rfl) ⟨371214, by rfl⟩ : syracuseStep 989905 = 742429) (by norm_num)
theorem B1481429 : Blo 876568 1481429 := bbase (se 7 (by rfl) ⟨17360, by rfl⟩ : syracuseStep 1481429 = 34721) (by norm_num)
theorem B1317605 : Blo 876568 1317605 := bbase (se 4 (by rfl) ⟨123525, by rfl⟩ : syracuseStep 1317605 = 247051) (by norm_num)
theorem B1874669 : Blo 876568 1874669 := bbase (se 3 (by rfl) ⟨351500, by rfl⟩ : syracuseStep 1874669 = 703001) (by norm_num)
theorem B989941 : Blo 876568 989941 := bbase (se 5 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 989941 = 92807) (by norm_num)
theorem B1317629 : Blo 876568 1317629 := bbase (se 3 (by rfl) ⟨247055, by rfl⟩ : syracuseStep 1317629 = 494111) (by norm_num)
theorem B1972997 : Blo 876568 1972997 := bbase (se 4 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 1972997 = 369937) (by norm_num)
theorem B1317653 : Blo 876568 1317653 := bbase (se 6 (by rfl) ⟨30882, by rfl⟩ : syracuseStep 1317653 = 61765) (by norm_num)
theorem B989977 : Blo 876568 989977 := bbase (se 2 (by rfl) ⟨371241, by rfl⟩ : syracuseStep 989977 = 742483) (by norm_num)
theorem B1317677 : Blo 876568 1317677 := bbase (se 3 (by rfl) ⟨247064, by rfl⟩ : syracuseStep 1317677 = 494129) (by norm_num)
theorem B2005813 : Blo 876568 2005813 := bbase (se 5 (by rfl) ⟨94022, by rfl⟩ : syracuseStep 2005813 = 188045) (by norm_num)
theorem B990013 : Blo 876568 990013 := bbase (se 3 (by rfl) ⟨185627, by rfl⟩ : syracuseStep 990013 = 371255) (by norm_num)
theorem B1317701 : Blo 876568 1317701 := bbase (se 4 (by rfl) ⟨123534, by rfl⟩ : syracuseStep 1317701 = 247069) (by norm_num)
theorem B1973069 : Blo 876568 1973069 := bbase (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) (by norm_num)
theorem B1481557 : Blo 876568 1481557 := bbase (se 9 (by rfl) ⟨4340, by rfl⟩ : syracuseStep 1481557 = 8681) (by norm_num)
theorem B1317725 : Blo 876568 1317725 := bbase (se 3 (by rfl) ⟨247073, by rfl⟩ : syracuseStep 1317725 = 494147) (by norm_num)
theorem B1252189 : Blo 876568 1252189 := bbase (se 3 (by rfl) ⟨234785, by rfl⟩ : syracuseStep 1252189 = 469571) (by norm_num)
theorem B990049 : Blo 876568 990049 := bbase (se 2 (by rfl) ⟨371268, by rfl⟩ : syracuseStep 990049 = 742537) (by norm_num)
theorem B1317749 : Blo 876568 1317749 := bbase (se 5 (by rfl) ⟨61769, by rfl⟩ : syracuseStep 1317749 = 123539) (by norm_num)
theorem B990085 : Blo 876568 990085 := bbase (se 4 (by rfl) ⟨92820, by rfl⟩ : syracuseStep 990085 = 185641) (by norm_num)
theorem B1317773 : Blo 876568 1317773 := bbase (se 3 (by rfl) ⟨247082, by rfl⟩ : syracuseStep 1317773 = 494165) (by norm_num)
theorem B1973141 : Blo 876568 1973141 := bbase (se 6 (by rfl) ⟨46245, by rfl⟩ : syracuseStep 1973141 = 92491) (by norm_num)
theorem B1317797 : Blo 876568 1317797 := bbase (se 4 (by rfl) ⟨123543, by rfl⟩ : syracuseStep 1317797 = 247087) (by norm_num)
theorem B990121 : Blo 876568 990121 := bbase (se 2 (by rfl) ⟨371295, by rfl⟩ : syracuseStep 990121 = 742591) (by norm_num)
theorem B1481645 : Blo 876568 1481645 := bbase (se 3 (by rfl) ⟨277808, by rfl⟩ : syracuseStep 1481645 = 555617) (by norm_num)
theorem B1317821 : Blo 876568 1317821 := bbase (se 3 (by rfl) ⟨247091, by rfl⟩ : syracuseStep 1317821 = 494183) (by norm_num)
theorem B990157 : Blo 876568 990157 := bbase (se 3 (by rfl) ⟨185654, by rfl⟩ : syracuseStep 990157 = 371309) (by norm_num)
theorem B1317845 : Blo 876568 1317845 := bbase (se 7 (by rfl) ⟨15443, by rfl⟩ : syracuseStep 1317845 = 30887) (by norm_num)
theorem B1973213 : Blo 876568 1973213 := bbase (se 3 (by rfl) ⟨369977, by rfl⟩ : syracuseStep 1973213 = 739955) (by norm_num)
theorem B1874909 : Blo 876568 1874909 := bbase (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) (by norm_num)
theorem B1317869 : Blo 876568 1317869 := bbase (se 3 (by rfl) ⟨247100, by rfl⟩ : syracuseStep 1317869 = 494201) (by norm_num)
theorem B990193 : Blo 876568 990193 := bbase (se 2 (by rfl) ⟨371322, by rfl⟩ : syracuseStep 990193 = 742645) (by norm_num)
theorem B1317893 : Blo 876568 1317893 := bbase (se 4 (by rfl) ⟨123552, by rfl⟩ : syracuseStep 1317893 = 247105) (by norm_num)
theorem B990229 : Blo 876568 990229 := bbase (se 6 (by rfl) ⟨23208, by rfl⟩ : syracuseStep 990229 = 46417) (by norm_num)
theorem B1317917 : Blo 876568 1317917 := bbase (se 3 (by rfl) ⟨247109, by rfl⟩ : syracuseStep 1317917 = 494219) (by norm_num)
theorem B1973285 : Blo 876568 1973285 := bbase (se 4 (by rfl) ⟨184995, by rfl⟩ : syracuseStep 1973285 = 369991) (by norm_num)
theorem B1481773 : Blo 876568 1481773 := bbase (se 3 (by rfl) ⟨277832, by rfl⟩ : syracuseStep 1481773 = 555665) (by norm_num)
theorem B1317941 : Blo 876568 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B990265 : Blo 876568 990265 := bbase (se 2 (by rfl) ⟨371349, by rfl⟩ : syracuseStep 990265 = 742699) (by norm_num)
theorem B1317965 : Blo 876568 1317965 := bbase (se 3 (by rfl) ⟨247118, by rfl⟩ : syracuseStep 1317965 = 494237) (by norm_num)
theorem B990301 : Blo 876568 990301 := bbase (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) (by norm_num)
theorem B1317989 : Blo 876568 1317989 := bbase (se 4 (by rfl) ⟨123561, by rfl⟩ : syracuseStep 1317989 = 247123) (by norm_num)
theorem B1973357 : Blo 876568 1973357 := bbase (se 3 (by rfl) ⟨370004, by rfl⟩ : syracuseStep 1973357 = 740009) (by norm_num)
theorem B1318013 : Blo 876568 1318013 := bbase (se 3 (by rfl) ⟨247127, by rfl⟩ : syracuseStep 1318013 = 494255) (by norm_num)
theorem B990337 : Blo 876568 990337 := bbase (se 2 (by rfl) ⟨371376, by rfl⟩ : syracuseStep 990337 = 742753) (by norm_num)
theorem B1481861 : Blo 876568 1481861 := bbase (se 4 (by rfl) ⟨138924, by rfl⟩ : syracuseStep 1481861 = 277849) (by norm_num)
theorem B1318037 : Blo 876568 1318037 := bbase (se 6 (by rfl) ⟨30891, by rfl⟩ : syracuseStep 1318037 = 61783) (by norm_num)
theorem B990373 : Blo 876568 990373 := bbase (se 4 (by rfl) ⟨92847, by rfl⟩ : syracuseStep 990373 = 185695) (by norm_num)
theorem B1318061 : Blo 876568 1318061 := bbase (se 3 (by rfl) ⟨247136, by rfl⟩ : syracuseStep 1318061 = 494273) (by norm_num)
theorem B1252525 : Blo 876568 1252525 := bbase (se 3 (by rfl) ⟨234848, by rfl⟩ : syracuseStep 1252525 = 469697) (by norm_num)
theorem B1973429 : Blo 876568 1973429 := bbase (se 5 (by rfl) ⟨92504, by rfl⟩ : syracuseStep 1973429 = 185009) (by norm_num)
theorem B1318085 : Blo 876568 1318085 := bbase (se 4 (by rfl) ⟨123570, by rfl⟩ : syracuseStep 1318085 = 247141) (by norm_num)
theorem B990409 : Blo 876568 990409 := bbase (se 2 (by rfl) ⟨371403, by rfl⟩ : syracuseStep 990409 = 742807) (by norm_num)
theorem B1318109 : Blo 876568 1318109 := bbase (se 3 (by rfl) ⟨247145, by rfl⟩ : syracuseStep 1318109 = 494291) (by norm_num)
theorem B990445 : Blo 876568 990445 := bbase (se 3 (by rfl) ⟨185708, by rfl⟩ : syracuseStep 990445 = 371417) (by norm_num)
theorem B1318133 : Blo 876568 1318133 := bbase (se 5 (by rfl) ⟨61787, by rfl⟩ : syracuseStep 1318133 = 123575) (by norm_num)
theorem B1973501 : Blo 876568 1973501 := bbase (se 3 (by rfl) ⟨370031, by rfl⟩ : syracuseStep 1973501 = 740063) (by norm_num)
theorem B1056001 : Blo 876568 1056001 := bbase (se 2 (by rfl) ⟨396000, by rfl⟩ : syracuseStep 1056001 = 792001) (by norm_num)
theorem B1481989 : Blo 876568 1481989 := bbase (se 4 (by rfl) ⟨138936, by rfl⟩ : syracuseStep 1481989 = 277873) (by norm_num)
theorem B1318157 : Blo 876568 1318157 := bbase (se 3 (by rfl) ⟨247154, by rfl⟩ : syracuseStep 1318157 = 494309) (by norm_num)
theorem B990481 : Blo 876568 990481 := bbase (se 2 (by rfl) ⟨371430, by rfl⟩ : syracuseStep 990481 = 742861) (by norm_num)
theorem B1318181 : Blo 876568 1318181 := bbase (se 4 (by rfl) ⟨123579, by rfl⟩ : syracuseStep 1318181 = 247159) (by norm_num)
theorem B990517 : Blo 876568 990517 := bbase (se 5 (by rfl) ⟨46430, by rfl⟩ : syracuseStep 990517 = 92861) (by norm_num)
theorem B1318205 : Blo 876568 1318205 := bbase (se 3 (by rfl) ⟨247163, by rfl⟩ : syracuseStep 1318205 = 494327) (by norm_num)
theorem B1973573 : Blo 876568 1973573 := bbase (se 4 (by rfl) ⟨185022, by rfl⟩ : syracuseStep 1973573 = 370045) (by norm_num)
theorem B1318229 : Blo 876568 1318229 := bbase (se 11 (by rfl) ⟨965, by rfl⟩ : syracuseStep 1318229 = 1931) (by norm_num)
theorem B990553 : Blo 876568 990553 := bbase (se 2 (by rfl) ⟨371457, by rfl⟩ : syracuseStep 990553 = 742915) (by norm_num)
theorem B1482077 : Blo 876568 1482077 := bbase (se 3 (by rfl) ⟨277889, by rfl⟩ : syracuseStep 1482077 = 555779) (by norm_num)
theorem B1056097 : Blo 876568 1056097 := bbase (se 2 (by rfl) ⟨396036, by rfl⟩ : syracuseStep 1056097 = 792073) (by norm_num)
theorem B1318253 : Blo 876568 1318253 := bbase (se 3 (by rfl) ⟨247172, by rfl⟩ : syracuseStep 1318253 = 494345) (by norm_num)
theorem B990589 : Blo 876568 990589 := bbase (se 3 (by rfl) ⟨185735, by rfl⟩ : syracuseStep 990589 = 371471) (by norm_num)
theorem B1318277 : Blo 876568 1318277 := bbase (se 4 (by rfl) ⟨123588, by rfl⟩ : syracuseStep 1318277 = 247177) (by norm_num)
theorem B1252741 : Blo 876568 1252741 := bbase (se 4 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 1252741 = 234889) (by norm_num)
theorem B1973645 : Blo 876568 1973645 := bbase (se 3 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 1973645 = 740117) (by norm_num)
theorem B16883093 : Blo 876568 16883093 := bbase (se 6 (by rfl) ⟨395697, by rfl⟩ : syracuseStep 16883093 = 791395) (by norm_num)
theorem B1318301 : Blo 876568 1318301 := bbase (se 3 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 1318301 = 494363) (by norm_num)
theorem B990625 : Blo 876568 990625 := bbase (se 2 (by rfl) ⟨371484, by rfl⟩ : syracuseStep 990625 = 742969) (by norm_num)
theorem B1187245 : Blo 876568 1187245 := bbase (se 3 (by rfl) ⟨222608, by rfl⟩ : syracuseStep 1187245 = 445217) (by norm_num)
theorem B1318325 : Blo 876568 1318325 := bbase (se 5 (by rfl) ⟨61796, by rfl⟩ : syracuseStep 1318325 = 123593) (by norm_num)
theorem B1318349 : Blo 876568 1318349 := bbase (se 3 (by rfl) ⟨247190, by rfl⟩ : syracuseStep 1318349 = 494381) (by norm_num)
theorem B1973717 : Blo 876568 1973717 := bbase (se 7 (by rfl) ⟨23129, by rfl⟩ : syracuseStep 1973717 = 46259) (by norm_num)
theorem B1875413 : Blo 876568 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B1875421 : Blo 876568 1875421 := bbase (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) (by norm_num)
theorem B1482205 : Blo 876568 1482205 := bbase (se 3 (by rfl) ⟨277913, by rfl⟩ : syracuseStep 1482205 = 555827) (by norm_num)
theorem B1318373 : Blo 876568 1318373 := bbase (se 4 (by rfl) ⟨123597, by rfl⟩ : syracuseStep 1318373 = 247195) (by norm_num)
theorem B1318397 : Blo 876568 1318397 := bbase (se 3 (by rfl) ⟨247199, by rfl⟩ : syracuseStep 1318397 = 494399) (by norm_num)
theorem B1318421 : Blo 876568 1318421 := bbase (se 6 (by rfl) ⟨30900, by rfl⟩ : syracuseStep 1318421 = 61801) (by norm_num)
theorem B1973789 : Blo 876568 1973789 := bbase (se 3 (by rfl) ⟨370085, by rfl⟩ : syracuseStep 1973789 = 740171) (by norm_num)
theorem B1318445 : Blo 876568 1318445 := bbase (se 3 (by rfl) ⟨247208, by rfl⟩ : syracuseStep 1318445 = 494417) (by norm_num)
theorem B1482293 : Blo 876568 1482293 := bbase (se 5 (by rfl) ⟨69482, by rfl⟩ : syracuseStep 1482293 = 138965) (by norm_num)
theorem B1318469 : Blo 876568 1318469 := bbase (se 4 (by rfl) ⟨123606, by rfl⟩ : syracuseStep 1318469 = 247213) (by norm_num)
theorem B1318493 : Blo 876568 1318493 := bbase (se 3 (by rfl) ⟨247217, by rfl⟩ : syracuseStep 1318493 = 494435) (by norm_num)
theorem B1973861 : Blo 876568 1973861 := bbase (se 4 (by rfl) ⟨185049, by rfl⟩ : syracuseStep 1973861 = 370099) (by norm_num)
theorem B1318517 : Blo 876568 1318517 := bbase (se 5 (by rfl) ⟨61805, by rfl⟩ : syracuseStep 1318517 = 123611) (by norm_num)
theorem B1318541 : Blo 876568 1318541 := bbase (se 3 (by rfl) ⟨247226, by rfl⟩ : syracuseStep 1318541 = 494453) (by norm_num)
theorem B1318565 : Blo 876568 1318565 := bbase (se 4 (by rfl) ⟨123615, by rfl⟩ : syracuseStep 1318565 = 247231) (by norm_num)
theorem B1973933 : Blo 876568 1973933 := bbase (se 3 (by rfl) ⟨370112, by rfl⟩ : syracuseStep 1973933 = 740225) (by norm_num)
theorem B1482421 : Blo 876568 1482421 := bbase (se 5 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 1482421 = 138977) (by norm_num)
theorem B1318589 : Blo 876568 1318589 := bbase (se 3 (by rfl) ⟨247235, by rfl⟩ : syracuseStep 1318589 = 494471) (by norm_num)
theorem B1318613 : Blo 876568 1318613 := bbase (se 7 (by rfl) ⟨15452, by rfl⟩ : syracuseStep 1318613 = 30905) (by norm_num)
theorem B1318637 : Blo 876568 1318637 := bbase (se 3 (by rfl) ⟨247244, by rfl⟩ : syracuseStep 1318637 = 494489) (by norm_num)
theorem B1974005 : Blo 876568 1974005 := bbase (se 5 (by rfl) ⟨92531, by rfl⟩ : syracuseStep 1974005 = 185063) (by norm_num)
theorem B1253117 : Blo 876568 1253117 := bbase (se 3 (by rfl) ⟨234959, by rfl⟩ : syracuseStep 1253117 = 469919) (by norm_num)
theorem B1318661 : Blo 876568 1318661 := bbase (se 4 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 1318661 = 247249) (by norm_num)
theorem B1482509 : Blo 876568 1482509 := bbase (se 3 (by rfl) ⟨277970, by rfl⟩ : syracuseStep 1482509 = 555941) (by norm_num)
theorem B1318685 : Blo 876568 1318685 := bbase (se 3 (by rfl) ⟨247253, by rfl⟩ : syracuseStep 1318685 = 494507) (by norm_num)
theorem B1318709 : Blo 876568 1318709 := bbase (se 5 (by rfl) ⟨61814, by rfl⟩ : syracuseStep 1318709 = 123629) (by norm_num)
theorem B1974077 : Blo 876568 1974077 := bbase (se 3 (by rfl) ⟨370139, by rfl⟩ : syracuseStep 1974077 = 740279) (by norm_num)
theorem B1318733 : Blo 876568 1318733 := bbase (se 3 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 1318733 = 494525) (by norm_num)
theorem B32481109 : Blo 876568 32481109 := bbase (se 9 (by rfl) ⟨95159, by rfl⟩ : syracuseStep 32481109 = 190319) (by norm_num)
theorem B16916309 : Blo 876568 16916309 := bbase (se 9 (by rfl) ⟨49559, by rfl⟩ : syracuseStep 16916309 = 99119) (by norm_num)
theorem B1318757 : Blo 876568 1318757 := bbase (se 4 (by rfl) ⟨123633, by rfl⟩ : syracuseStep 1318757 = 247267) (by norm_num)
theorem B6004597 : Blo 876568 6004597 := bbase (se 5 (by rfl) ⟨281465, by rfl⟩ : syracuseStep 6004597 = 562931) (by norm_num)
theorem B1318781 : Blo 876568 1318781 := bbase (se 3 (by rfl) ⟨247271, by rfl⟩ : syracuseStep 1318781 = 494543) (by norm_num)
theorem B1974149 : Blo 876568 1974149 := bbase (se 4 (by rfl) ⟨185076, by rfl⟩ : syracuseStep 1974149 = 370153) (by norm_num)
theorem B1482637 : Blo 876568 1482637 := bbase (se 3 (by rfl) ⟨277994, by rfl⟩ : syracuseStep 1482637 = 555989) (by norm_num)
theorem B1318805 : Blo 876568 1318805 := bbase (se 6 (by rfl) ⟨30909, by rfl⟩ : syracuseStep 1318805 = 61819) (by norm_num)
theorem B1318829 : Blo 876568 1318829 := bbase (se 3 (by rfl) ⟨247280, by rfl⟩ : syracuseStep 1318829 = 494561) (by norm_num)
theorem B1318853 : Blo 876568 1318853 := bbase (se 4 (by rfl) ⟨123642, by rfl⟩ : syracuseStep 1318853 = 247285) (by norm_num)
theorem B1974221 : Blo 876568 1974221 := bbase (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) (by norm_num)
theorem B1318877 : Blo 876568 1318877 := bbase (se 3 (by rfl) ⟨247289, by rfl⟩ : syracuseStep 1318877 = 494579) (by norm_num)
theorem B1482725 : Blo 876568 1482725 := bbase (se 4 (by rfl) ⟨139005, by rfl⟩ : syracuseStep 1482725 = 278011) (by norm_num)
theorem B1318901 : Blo 876568 1318901 := bbase (se 5 (by rfl) ⟨61823, by rfl⟩ : syracuseStep 1318901 = 123647) (by norm_num)
theorem B1581061 : Blo 876568 1581061 := bbase (se 4 (by rfl) ⟨148224, by rfl⟩ : syracuseStep 1581061 = 296449) (by norm_num)
theorem B1318925 : Blo 876568 1318925 := bbase (se 3 (by rfl) ⟨247298, by rfl⟩ : syracuseStep 1318925 = 494597) (by norm_num)
theorem B1974293 : Blo 876568 1974293 := bbase (se 6 (by rfl) ⟨46272, by rfl⟩ : syracuseStep 1974293 = 92545) (by norm_num)
theorem B1318949 : Blo 876568 1318949 := bbase (se 4 (by rfl) ⟨123651, by rfl⟩ : syracuseStep 1318949 = 247303) (by norm_num)
theorem B1318973 : Blo 876568 1318973 := bbase (se 3 (by rfl) ⟨247307, by rfl⟩ : syracuseStep 1318973 = 494615) (by norm_num)
theorem B1318997 : Blo 876568 1318997 := bbase (se 8 (by rfl) ⟨7728, by rfl⟩ : syracuseStep 1318997 = 15457) (by norm_num)
theorem B1974365 : Blo 876568 1974365 := bbase (se 3 (by rfl) ⟨370193, by rfl⟩ : syracuseStep 1974365 = 740387) (by norm_num)
theorem B1482853 : Blo 876568 1482853 := bbase (se 4 (by rfl) ⟨139017, by rfl⟩ : syracuseStep 1482853 = 278035) (by norm_num)
theorem B1319021 : Blo 876568 1319021 := bbase (se 3 (by rfl) ⟨247316, by rfl⟩ : syracuseStep 1319021 = 494633) (by norm_num)
theorem B1319045 : Blo 876568 1319045 := bbase (se 4 (by rfl) ⟨123660, by rfl⟩ : syracuseStep 1319045 = 247321) (by norm_num)
theorem B1319069 : Blo 876568 1319069 := bbase (se 3 (by rfl) ⟨247325, by rfl⟩ : syracuseStep 1319069 = 494651) (by norm_num)
theorem B1974437 : Blo 876568 1974437 := bbase (se 4 (by rfl) ⟨185103, by rfl⟩ : syracuseStep 1974437 = 370207) (by norm_num)
theorem B1319093 : Blo 876568 1319093 := bbase (se 5 (by rfl) ⟨61832, by rfl⟩ : syracuseStep 1319093 = 123665) (by norm_num)
theorem B1482941 : Blo 876568 1482941 := bbase (se 3 (by rfl) ⟨278051, by rfl⟩ : syracuseStep 1482941 = 556103) (by norm_num)
theorem B1319117 : Blo 876568 1319117 := bbase (se 3 (by rfl) ⟨247334, by rfl⟩ : syracuseStep 1319117 = 494669) (by norm_num)
theorem B1319141 : Blo 876568 1319141 := bbase (se 4 (by rfl) ⟨123669, by rfl⟩ : syracuseStep 1319141 = 247339) (by norm_num)
theorem B1974509 : Blo 876568 1974509 := bbase (se 3 (by rfl) ⟨370220, by rfl⟩ : syracuseStep 1974509 = 740441) (by norm_num)
theorem B1351925 : Blo 876568 1351925 := bbase (se 5 (by rfl) ⟨63371, by rfl⟩ : syracuseStep 1351925 = 126743) (by norm_num)
theorem B1319165 : Blo 876568 1319165 := bbase (se 3 (by rfl) ⟨247343, by rfl⟩ : syracuseStep 1319165 = 494687) (by norm_num)
theorem B1319189 : Blo 876568 1319189 := bbase (se 6 (by rfl) ⟨30918, by rfl⟩ : syracuseStep 1319189 = 61837) (by norm_num)
theorem B1319213 : Blo 876568 1319213 := bbase (se 3 (by rfl) ⟨247352, by rfl⟩ : syracuseStep 1319213 = 494705) (by norm_num)
theorem B1974581 : Blo 876568 1974581 := bbase (se 5 (by rfl) ⟨92558, by rfl⟩ : syracuseStep 1974581 = 185117) (by norm_num)
theorem B1483069 : Blo 876568 1483069 := bbase (se 3 (by rfl) ⟨278075, by rfl⟩ : syracuseStep 1483069 = 556151) (by norm_num)
theorem B1319237 : Blo 876568 1319237 := bbase (se 4 (by rfl) ⟨123678, by rfl⟩ : syracuseStep 1319237 = 247357) (by norm_num)
theorem B1057097 : Blo 876568 1057097 := bbase (se 2 (by rfl) ⟨396411, by rfl⟩ : syracuseStep 1057097 = 792823) (by norm_num)
theorem B1777997 : Blo 876568 1777997 := bbase (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) (by norm_num)
theorem B1319261 : Blo 876568 1319261 := bbase (se 3 (by rfl) ⟨247361, by rfl⟩ : syracuseStep 1319261 = 494723) (by norm_num)
theorem B1319285 : Blo 876568 1319285 := bbase (se 5 (by rfl) ⟨61841, by rfl⟩ : syracuseStep 1319285 = 123683) (by norm_num)
theorem B1974653 : Blo 876568 1974653 := bbase (se 3 (by rfl) ⟨370247, by rfl⟩ : syracuseStep 1974653 = 740495) (by norm_num)
theorem B1319309 : Blo 876568 1319309 := bbase (se 3 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 1319309 = 494741) (by norm_num)
theorem B1483157 : Blo 876568 1483157 := bbase (se 6 (by rfl) ⟨34761, by rfl⟩ : syracuseStep 1483157 = 69523) (by norm_num)
theorem B1319333 : Blo 876568 1319333 := bbase (se 4 (by rfl) ⟨123687, by rfl⟩ : syracuseStep 1319333 = 247375) (by norm_num)
theorem B1319357 : Blo 876568 1319357 := bbase (se 3 (by rfl) ⟨247379, by rfl⟩ : syracuseStep 1319357 = 494759) (by norm_num)
theorem B1974725 : Blo 876568 1974725 := bbase (se 4 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 1974725 = 370261) (by norm_num)
theorem B1319381 : Blo 876568 1319381 := bbase (se 7 (by rfl) ⟨15461, by rfl⟩ : syracuseStep 1319381 = 30923) (by norm_num)
theorem B1319405 : Blo 876568 1319405 := bbase (se 3 (by rfl) ⟨247388, by rfl⟩ : syracuseStep 1319405 = 494777) (by norm_num)
theorem B1319429 : Blo 876568 1319429 := bbase (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) (by norm_num)
theorem B1974797 : Blo 876568 1974797 := bbase (se 3 (by rfl) ⟨370274, by rfl⟩ : syracuseStep 1974797 = 740549) (by norm_num)
theorem B6660629 : Blo 876568 6660629 := bbase (se 6 (by rfl) ⟨156108, by rfl⟩ : syracuseStep 6660629 = 312217) (by norm_num)
theorem B1483285 : Blo 876568 1483285 := bbase (se 6 (by rfl) ⟨34764, by rfl⟩ : syracuseStep 1483285 = 69529) (by norm_num)
theorem B1319453 : Blo 876568 1319453 := bbase (se 3 (by rfl) ⟨247397, by rfl⟩ : syracuseStep 1319453 = 494795) (by norm_num)
theorem B1319477 : Blo 876568 1319477 := bbase (se 5 (by rfl) ⟨61850, by rfl⟩ : syracuseStep 1319477 = 123701) (by norm_num)
theorem B1581637 : Blo 876568 1581637 := bbase (se 4 (by rfl) ⟨148278, by rfl⟩ : syracuseStep 1581637 = 296557) (by norm_num)
theorem B1876549 : Blo 876568 1876549 := bbase (se 4 (by rfl) ⟨175926, by rfl⟩ : syracuseStep 1876549 = 351853) (by norm_num)
theorem B1319501 : Blo 876568 1319501 := bbase (se 3 (by rfl) ⟨247406, by rfl⟩ : syracuseStep 1319501 = 494813) (by norm_num)
theorem B1974869 : Blo 876568 1974869 := bbase (se 8 (by rfl) ⟨11571, by rfl⟩ : syracuseStep 1974869 = 23143) (by norm_num)
theorem B1319525 : Blo 876568 1319525 := bbase (se 4 (by rfl) ⟨123705, by rfl⟩ : syracuseStep 1319525 = 247411) (by norm_num)
theorem B1057385 : Blo 876568 1057385 := bbase (se 2 (by rfl) ⟨396519, by rfl⟩ : syracuseStep 1057385 = 793039) (by norm_num)
theorem B1483373 : Blo 876568 1483373 := bbase (se 3 (by rfl) ⟨278132, by rfl⟩ : syracuseStep 1483373 = 556265) (by norm_num)
theorem B1319549 : Blo 876568 1319549 := bbase (se 3 (by rfl) ⟨247415, by rfl⟩ : syracuseStep 1319549 = 494831) (by norm_num)
theorem B2171525 : Blo 876568 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B1319573 : Blo 876568 1319573 := bbase (se 6 (by rfl) ⟨30927, by rfl⟩ : syracuseStep 1319573 = 61855) (by norm_num)
theorem B1974941 : Blo 876568 1974941 := bbase (se 3 (by rfl) ⟨370301, by rfl⟩ : syracuseStep 1974941 = 740603) (by norm_num)
theorem B1319597 : Blo 876568 1319597 := bbase (se 3 (by rfl) ⟨247424, by rfl⟩ : syracuseStep 1319597 = 494849) (by norm_num)
theorem B1319621 : Blo 876568 1319621 := bbase (se 4 (by rfl) ⟨123714, by rfl⟩ : syracuseStep 1319621 = 247429) (by norm_num)
theorem B1319645 : Blo 876568 1319645 := bbase (se 3 (by rfl) ⟨247433, by rfl⟩ : syracuseStep 1319645 = 494867) (by norm_num)
theorem B1975013 : Blo 876568 1975013 := bbase (se 4 (by rfl) ⟨185157, by rfl⟩ : syracuseStep 1975013 = 370315) (by norm_num)
theorem B1483501 : Blo 876568 1483501 := bbase (se 3 (by rfl) ⟨278156, by rfl⟩ : syracuseStep 1483501 = 556313) (by norm_num)
theorem B1319669 : Blo 876568 1319669 := bbase (se 5 (by rfl) ⟨61859, by rfl⟩ : syracuseStep 1319669 = 123719) (by norm_num)
theorem B4760309 : Blo 876568 4760309 := bbase (se 5 (by rfl) ⟨223139, by rfl⟩ : syracuseStep 4760309 = 446279) (by norm_num)
theorem B1319693 : Blo 876568 1319693 := bbase (se 3 (by rfl) ⟨247442, by rfl⟩ : syracuseStep 1319693 = 494885) (by norm_num)
theorem B1057549 : Blo 876568 1057549 := bbase (se 3 (by rfl) ⟨198290, by rfl⟩ : syracuseStep 1057549 = 396581) (by norm_num)
theorem B1319717 : Blo 876568 1319717 := bbase (se 4 (by rfl) ⟨123723, by rfl⟩ : syracuseStep 1319717 = 247447) (by norm_num)
theorem B1057577 : Blo 876568 1057577 := bbase (se 2 (by rfl) ⟨396591, by rfl⟩ : syracuseStep 1057577 = 793183) (by norm_num)
theorem B1975085 : Blo 876568 1975085 := bbase (se 3 (by rfl) ⟨370328, by rfl⟩ : syracuseStep 1975085 = 740657) (by norm_num)
theorem B1319741 : Blo 876568 1319741 := bbase (se 3 (by rfl) ⟨247451, by rfl⟩ : syracuseStep 1319741 = 494903) (by norm_num)
theorem B1483589 : Blo 876568 1483589 := bbase (se 4 (by rfl) ⟨139086, by rfl⟩ : syracuseStep 1483589 = 278173) (by norm_num)
theorem B1319765 : Blo 876568 1319765 := bbase (se 9 (by rfl) ⟨3866, by rfl⟩ : syracuseStep 1319765 = 7733) (by norm_num)
theorem B1319789 : Blo 876568 1319789 := bbase (se 3 (by rfl) ⟨247460, by rfl⟩ : syracuseStep 1319789 = 494921) (by norm_num)
theorem B1975157 : Blo 876568 1975157 := bbase (se 5 (by rfl) ⟨92585, by rfl⟩ : syracuseStep 1975157 = 185171) (by norm_num)
theorem B1319813 : Blo 876568 1319813 := bbase (se 4 (by rfl) ⟨123732, by rfl⟩ : syracuseStep 1319813 = 247465) (by norm_num)
theorem B1319837 : Blo 876568 1319837 := bbase (se 3 (by rfl) ⟨247469, by rfl⟩ : syracuseStep 1319837 = 494939) (by norm_num)
theorem B1057693 : Blo 876568 1057693 := bbase (se 3 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 1057693 = 396635) (by norm_num)
theorem B1319861 : Blo 876568 1319861 := bbase (se 5 (by rfl) ⟨61868, by rfl⟩ : syracuseStep 1319861 = 123737) (by norm_num)
theorem B1975229 : Blo 876568 1975229 := bbase (se 3 (by rfl) ⟨370355, by rfl⟩ : syracuseStep 1975229 = 740711) (by norm_num)
theorem B1876925 : Blo 876568 1876925 := bbase (se 3 (by rfl) ⟨351923, by rfl⟩ : syracuseStep 1876925 = 703847) (by norm_num)
theorem B1483717 : Blo 876568 1483717 := bbase (se 4 (by rfl) ⟨139098, by rfl⟩ : syracuseStep 1483717 = 278197) (by norm_num)
theorem B1319885 : Blo 876568 1319885 := bbase (se 3 (by rfl) ⟨247478, by rfl⟩ : syracuseStep 1319885 = 494957) (by norm_num)
theorem B1319909 : Blo 876568 1319909 := bbase (se 4 (by rfl) ⟨123741, by rfl⟩ : syracuseStep 1319909 = 247483) (by norm_num)
theorem B1319933 : Blo 876568 1319933 := bbase (se 3 (by rfl) ⟨247487, by rfl⟩ : syracuseStep 1319933 = 494975) (by norm_num)
theorem B1057789 : Blo 876568 1057789 := bbase (se 3 (by rfl) ⟨198335, by rfl⟩ : syracuseStep 1057789 = 396671) (by norm_num)
theorem B1975301 : Blo 876568 1975301 := bbase (se 4 (by rfl) ⟨185184, by rfl⟩ : syracuseStep 1975301 = 370369) (by norm_num)
theorem B2106389 : Blo 876568 2106389 := bbase (se 6 (by rfl) ⟨49368, by rfl⟩ : syracuseStep 2106389 = 98737) (by norm_num)
theorem B2499605 : Blo 876568 2499605 := bbase (se 6 (by rfl) ⟨58584, by rfl⟩ : syracuseStep 2499605 = 117169) (by norm_num)
theorem B10298389 : Blo 876568 10298389 := bbase (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) (by norm_num)
theorem B1319957 : Blo 876568 1319957 := bbase (se 6 (by rfl) ⟨30936, by rfl⟩ : syracuseStep 1319957 = 61873) (by norm_num)
theorem B1483805 : Blo 876568 1483805 := bbase (se 3 (by rfl) ⟨278213, by rfl⟩ : syracuseStep 1483805 = 556427) (by norm_num)
theorem B1319981 : Blo 876568 1319981 := bbase (se 3 (by rfl) ⟨247496, by rfl⟩ : syracuseStep 1319981 = 494993) (by norm_num)
theorem B1320005 : Blo 876568 1320005 := bbase (se 4 (by rfl) ⟨123750, by rfl⟩ : syracuseStep 1320005 = 247501) (by norm_num)
theorem B1975373 : Blo 876568 1975373 := bbase (se 3 (by rfl) ⟨370382, by rfl⟩ : syracuseStep 1975373 = 740765) (by norm_num)
theorem B1320029 : Blo 876568 1320029 := bbase (se 3 (by rfl) ⟨247505, by rfl⟩ : syracuseStep 1320029 = 495011) (by norm_num)
theorem B1320053 : Blo 876568 1320053 := bbase (se 5 (by rfl) ⟨61877, by rfl⟩ : syracuseStep 1320053 = 123755) (by norm_num)
theorem B1320077 : Blo 876568 1320077 := bbase (se 3 (by rfl) ⟨247514, by rfl⟩ : syracuseStep 1320077 = 495029) (by norm_num)
theorem B1975445 : Blo 876568 1975445 := bbase (se 6 (by rfl) ⟨46299, by rfl⟩ : syracuseStep 1975445 = 92599) (by norm_num)
theorem B1483933 : Blo 876568 1483933 := bbase (se 3 (by rfl) ⟨278237, by rfl⟩ : syracuseStep 1483933 = 556475) (by norm_num)
theorem B1320101 : Blo 876568 1320101 := bbase (se 4 (by rfl) ⟨123759, by rfl⟩ : syracuseStep 1320101 = 247519) (by norm_num)
theorem B1320125 : Blo 876568 1320125 := bbase (se 3 (by rfl) ⟨247523, by rfl⟩ : syracuseStep 1320125 = 495047) (by norm_num)
theorem B1320149 : Blo 876568 1320149 := bbase (se 7 (by rfl) ⟨15470, by rfl⟩ : syracuseStep 1320149 = 30941) (by norm_num)
theorem B2008277 : Blo 876568 2008277 := bbase (se 7 (by rfl) ⟨23534, by rfl⟩ : syracuseStep 2008277 = 47069) (by norm_num)
theorem B1975517 : Blo 876568 1975517 := bbase (se 3 (by rfl) ⟨370409, by rfl⟩ : syracuseStep 1975517 = 740819) (by norm_num)
theorem B1582301 : Blo 876568 1582301 := bbase (se 3 (by rfl) ⟨296681, by rfl⟩ : syracuseStep 1582301 = 593363) (by norm_num)
theorem B1320173 : Blo 876568 1320173 := bbase (se 3 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 1320173 = 495065) (by norm_num)
theorem B1484021 : Blo 876568 1484021 := bbase (se 5 (by rfl) ⟨69563, by rfl⟩ : syracuseStep 1484021 = 139127) (by norm_num)
theorem B1320197 : Blo 876568 1320197 := bbase (se 4 (by rfl) ⟨123768, by rfl⟩ : syracuseStep 1320197 = 247537) (by norm_num)
theorem B1320221 : Blo 876568 1320221 := bbase (se 3 (by rfl) ⟨247541, by rfl⟩ : syracuseStep 1320221 = 495083) (by norm_num)
theorem B1975589 : Blo 876568 1975589 := bbase (se 4 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 1975589 = 370423) (by norm_num)
theorem B1320245 : Blo 876568 1320245 := bbase (se 5 (by rfl) ⟨61886, by rfl⟩ : syracuseStep 1320245 = 123773) (by norm_num)
theorem B1320269 : Blo 876568 1320269 := bbase (se 3 (by rfl) ⟨247550, by rfl⟩ : syracuseStep 1320269 = 495101) (by norm_num)
theorem B1320293 : Blo 876568 1320293 := bbase (se 4 (by rfl) ⟨123777, by rfl⟩ : syracuseStep 1320293 = 247555) (by norm_num)
theorem B1975661 : Blo 876568 1975661 := bbase (se 3 (by rfl) ⟨370436, by rfl⟩ : syracuseStep 1975661 = 740873) (by norm_num)
theorem B1484149 : Blo 876568 1484149 := bbase (se 5 (by rfl) ⟨69569, by rfl⟩ : syracuseStep 1484149 = 139139) (by norm_num)
theorem B1320317 : Blo 876568 1320317 := bbase (se 3 (by rfl) ⟨247559, by rfl⟩ : syracuseStep 1320317 = 495119) (by norm_num)
theorem B1320341 : Blo 876568 1320341 := bbase (se 6 (by rfl) ⟨30945, by rfl⟩ : syracuseStep 1320341 = 61891) (by norm_num)
theorem B1320365 : Blo 876568 1320365 := bbase (se 3 (by rfl) ⟨247568, by rfl⟩ : syracuseStep 1320365 = 495137) (by norm_num)
theorem B1975733 : Blo 876568 1975733 := bbase (se 5 (by rfl) ⟨92612, by rfl⟩ : syracuseStep 1975733 = 185225) (by norm_num)
theorem B1582517 : Blo 876568 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B1320389 : Blo 876568 1320389 := bbase (se 4 (by rfl) ⟨123786, by rfl⟩ : syracuseStep 1320389 = 247573) (by norm_num)
theorem B1484237 : Blo 876568 1484237 := bbase (se 3 (by rfl) ⟨278294, by rfl⟩ : syracuseStep 1484237 = 556589) (by norm_num)
theorem B1320413 : Blo 876568 1320413 := bbase (se 3 (by rfl) ⟨247577, by rfl⟩ : syracuseStep 1320413 = 495155) (by norm_num)
theorem B2958821 : Blo 876568 2958821 := bbase (se 4 (by rfl) ⟨277389, by rfl⟩ : syracuseStep 2958821 = 554779) (by norm_num)
theorem B1320437 : Blo 876568 1320437 := bbase (se 5 (by rfl) ⟨61895, by rfl⟩ : syracuseStep 1320437 = 123791) (by norm_num)
theorem B1975805 : Blo 876568 1975805 := bbase (se 3 (by rfl) ⟨370463, by rfl⟩ : syracuseStep 1975805 = 740927) (by norm_num)
theorem B1320461 : Blo 876568 1320461 := bbase (se 3 (by rfl) ⟨247586, by rfl⟩ : syracuseStep 1320461 = 495173) (by norm_num)
theorem B1320485 : Blo 876568 1320485 := bbase (se 4 (by rfl) ⟨123795, by rfl⟩ : syracuseStep 1320485 = 247591) (by norm_num)
theorem B1320509 : Blo 876568 1320509 := bbase (se 3 (by rfl) ⟨247595, by rfl⟩ : syracuseStep 1320509 = 495191) (by norm_num)
theorem B1975877 : Blo 876568 1975877 := bbase (se 4 (by rfl) ⟨185238, by rfl⟩ : syracuseStep 1975877 = 370477) (by norm_num)
theorem B1484365 : Blo 876568 1484365 := bbase (se 3 (by rfl) ⟨278318, by rfl⟩ : syracuseStep 1484365 = 556637) (by norm_num)
theorem B1320533 : Blo 876568 1320533 := bbase (se 8 (by rfl) ⟨7737, by rfl⟩ : syracuseStep 1320533 = 15475) (by norm_num)
theorem B1320557 : Blo 876568 1320557 := bbase (se 3 (by rfl) ⟨247604, by rfl⟩ : syracuseStep 1320557 = 495209) (by norm_num)
theorem B1320581 : Blo 876568 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B1975949 : Blo 876568 1975949 := bbase (se 3 (by rfl) ⟨370490, by rfl⟩ : syracuseStep 1975949 = 740981) (by norm_num)
theorem B1320605 : Blo 876568 1320605 := bbase (se 3 (by rfl) ⟨247613, by rfl⟩ : syracuseStep 1320605 = 495227) (by norm_num)
theorem B1484453 : Blo 876568 1484453 := bbase (se 4 (by rfl) ⟨139167, by rfl⟩ : syracuseStep 1484453 = 278335) (by norm_num)
theorem B1320629 : Blo 876568 1320629 := bbase (se 5 (by rfl) ⟨61904, by rfl⟩ : syracuseStep 1320629 = 123809) (by norm_num)
theorem B1320653 : Blo 876568 1320653 := bbase (se 3 (by rfl) ⟨247622, by rfl⟩ : syracuseStep 1320653 = 495245) (by norm_num)
theorem B1976021 : Blo 876568 1976021 := bbase (se 7 (by rfl) ⟨23156, by rfl⟩ : syracuseStep 1976021 = 46313) (by norm_num)
theorem B1320677 : Blo 876568 1320677 := bbase (se 4 (by rfl) ⟨123813, by rfl⟩ : syracuseStep 1320677 = 247627) (by norm_num)
theorem B1320701 : Blo 876568 1320701 := bbase (se 3 (by rfl) ⟨247631, by rfl⟩ : syracuseStep 1320701 = 495263) (by norm_num)
theorem B1320725 : Blo 876568 1320725 := bbase (se 6 (by rfl) ⟨30954, by rfl⟩ : syracuseStep 1320725 = 61909) (by norm_num)
theorem B1976093 : Blo 876568 1976093 := bbase (se 3 (by rfl) ⟨370517, by rfl⟩ : syracuseStep 1976093 = 741035) (by norm_num)
theorem B1484581 : Blo 876568 1484581 := bbase (se 4 (by rfl) ⟨139179, by rfl⟩ : syracuseStep 1484581 = 278359) (by norm_num)
theorem B1320749 : Blo 876568 1320749 := bbase (se 3 (by rfl) ⟨247640, by rfl⟩ : syracuseStep 1320749 = 495281) (by norm_num)
theorem B1320773 : Blo 876568 1320773 := bbase (se 4 (by rfl) ⟨123822, by rfl⟩ : syracuseStep 1320773 = 247645) (by norm_num)
theorem B1713997 : Blo 876568 1713997 := bbase (se 3 (by rfl) ⟨321374, by rfl⟩ : syracuseStep 1713997 = 642749) (by norm_num)
theorem B117253973 : Blo 876568 117253973 := bbase (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) (by norm_num)
theorem B1320797 : Blo 876568 1320797 := bbase (se 3 (by rfl) ⟨247649, by rfl⟩ : syracuseStep 1320797 = 495299) (by norm_num)
theorem B1976165 : Blo 876568 1976165 := bbase (se 4 (by rfl) ⟨185265, by rfl⟩ : syracuseStep 1976165 = 370531) (by norm_num)
theorem B1320821 : Blo 876568 1320821 := bbase (se 5 (by rfl) ⟨61913, by rfl⟩ : syracuseStep 1320821 = 123827) (by norm_num)
theorem B1484669 : Blo 876568 1484669 := bbase (se 3 (by rfl) ⟨278375, by rfl⟩ : syracuseStep 1484669 = 556751) (by norm_num)
theorem B1320845 : Blo 876568 1320845 := bbase (se 3 (by rfl) ⟨247658, by rfl⟩ : syracuseStep 1320845 = 495317) (by norm_num)
theorem B2369429 : Blo 876568 2369429 := bbase (se 6 (by rfl) ⟨55533, by rfl⟩ : syracuseStep 2369429 = 111067) (by norm_num)
theorem B2959253 : Blo 876568 2959253 := bbase (se 6 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 2959253 = 138715) (by norm_num)
theorem B1976237 : Blo 876568 1976237 := bbase (se 3 (by rfl) ⟨370544, by rfl⟩ : syracuseStep 1976237 = 741089) (by norm_num)
theorem B1583021 : Blo 876568 1583021 := bbase (se 3 (by rfl) ⟨296816, by rfl⟩ : syracuseStep 1583021 = 593633) (by norm_num)
theorem B1189829 : Blo 876568 1189829 := bbase (se 4 (by rfl) ⟨111546, by rfl⟩ : syracuseStep 1189829 = 223093) (by norm_num)
theorem B1976309 : Blo 876568 1976309 := bbase (se 5 (by rfl) ⟨92639, by rfl⟩ : syracuseStep 1976309 = 185279) (by norm_num)
theorem B1484797 : Blo 876568 1484797 := bbase (se 3 (by rfl) ⟨278399, by rfl⟩ : syracuseStep 1484797 = 556799) (by norm_num)
theorem B1779749 : Blo 876568 1779749 := bbase (se 4 (by rfl) ⟨166851, by rfl⟩ : syracuseStep 1779749 = 333703) (by norm_num)
theorem B4499509 : Blo 876568 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B1976381 : Blo 876568 1976381 := bbase (se 3 (by rfl) ⟨370571, by rfl⟩ : syracuseStep 1976381 = 741143) (by norm_num)
theorem B6006869 : Blo 876568 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B1484885 : Blo 876568 1484885 := bbase (se 8 (by rfl) ⟨8700, by rfl⟩ : syracuseStep 1484885 = 17401) (by norm_num)
theorem B1976453 : Blo 876568 1976453 := bbase (se 4 (by rfl) ⟨185292, by rfl⟩ : syracuseStep 1976453 = 370585) (by norm_num)
theorem B2500789 : Blo 876568 2500789 := bbase (se 5 (by rfl) ⟨117224, by rfl⟩ : syracuseStep 2500789 = 234449) (by norm_num)
theorem B1976525 : Blo 876568 1976525 := bbase (se 3 (by rfl) ⟨370598, by rfl⟩ : syracuseStep 1976525 = 741197) (by norm_num)
theorem B2140373 : Blo 876568 2140373 := bbase (se 7 (by rfl) ⟨25082, by rfl⟩ : syracuseStep 2140373 = 50165) (by norm_num)
theorem B1485013 : Blo 876568 1485013 := bbase (se 7 (by rfl) ⟨17402, by rfl⟩ : syracuseStep 1485013 = 34805) (by norm_num)
theorem B4696309 : Blo 876568 4696309 := bbase (se 5 (by rfl) ⟨220139, by rfl⟩ : syracuseStep 4696309 = 440279) (by norm_num)
theorem B1976597 : Blo 876568 1976597 := bbase (se 6 (by rfl) ⟨46326, by rfl⟩ : syracuseStep 1976597 = 92653) (by norm_num)
theorem B1485101 : Blo 876568 1485101 := bbase (se 3 (by rfl) ⟨278456, by rfl⟩ : syracuseStep 1485101 = 556913) (by norm_num)
theorem B2959685 : Blo 876568 2959685 := bbase (se 4 (by rfl) ⟨277470, by rfl⟩ : syracuseStep 2959685 = 554941) (by norm_num)
theorem B2500949 : Blo 876568 2500949 := bbase (se 10 (by rfl) ⟨3663, by rfl⟩ : syracuseStep 2500949 = 7327) (by norm_num)
theorem B7317845 : Blo 876568 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B1976669 : Blo 876568 1976669 := bbase (se 3 (by rfl) ⟨370625, by rfl⟩ : syracuseStep 1976669 = 741251) (by norm_num)
theorem B1976741 : Blo 876568 1976741 := bbase (se 4 (by rfl) ⟨185319, by rfl⟩ : syracuseStep 1976741 = 370639) (by norm_num)
theorem B1485229 : Blo 876568 1485229 := bbase (se 3 (by rfl) ⟨278480, by rfl⟩ : syracuseStep 1485229 = 556961) (by norm_num)
theorem B1976813 : Blo 876568 1976813 := bbase (se 3 (by rfl) ⟨370652, by rfl⟩ : syracuseStep 1976813 = 741305) (by norm_num)
theorem B1485317 : Blo 876568 1485317 := bbase (se 4 (by rfl) ⟨139248, by rfl⟩ : syracuseStep 1485317 = 278497) (by norm_num)
theorem B1878565 : Blo 876568 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B1976885 : Blo 876568 1976885 := bbase (se 5 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 1976885 = 185333) (by norm_num)
theorem B2501189 : Blo 876568 2501189 := bbase (se 4 (by rfl) ⟨234486, by rfl⟩ : syracuseStep 2501189 = 468973) (by norm_num)
theorem B1780309 : Blo 876568 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B1976957 : Blo 876568 1976957 := bbase (se 3 (by rfl) ⟨370679, by rfl⟩ : syracuseStep 1976957 = 741359) (by norm_num)
theorem B1485445 : Blo 876568 1485445 := bbase (se 4 (by rfl) ⟨139260, by rfl⟩ : syracuseStep 1485445 = 278521) (by norm_num)
theorem B2108101 : Blo 876568 2108101 := bbase (se 4 (by rfl) ⟨197634, by rfl⟩ : syracuseStep 2108101 = 395269) (by norm_num)
theorem B1977029 : Blo 876568 1977029 := bbase (se 4 (by rfl) ⟨185346, by rfl⟩ : syracuseStep 1977029 = 370693) (by norm_num)
theorem B1780445 : Blo 876568 1780445 := bbase (se 3 (by rfl) ⟨333833, by rfl⟩ : syracuseStep 1780445 = 667667) (by norm_num)
theorem B1485533 : Blo 876568 1485533 := bbase (se 3 (by rfl) ⟨278537, by rfl⟩ : syracuseStep 1485533 = 557075) (by norm_num)
theorem B2960117 : Blo 876568 2960117 := bbase (se 5 (by rfl) ⟨138755, by rfl⟩ : syracuseStep 2960117 = 277511) (by norm_num)
theorem B2501381 : Blo 876568 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B1977101 : Blo 876568 1977101 := bbase (se 3 (by rfl) ⟨370706, by rfl⟩ : syracuseStep 1977101 = 741413) (by norm_num)
theorem B1125149 : Blo 876568 1125149 := bbase (se 3 (by rfl) ⟨210965, by rfl⟩ : syracuseStep 1125149 = 421931) (by norm_num)
theorem B1977173 : Blo 876568 1977173 := bbase (se 9 (by rfl) ⟨5792, by rfl⟩ : syracuseStep 1977173 = 11585) (by norm_num)
theorem B1485661 : Blo 876568 1485661 := bbase (se 3 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 1485661 = 557123) (by norm_num)
theorem B1977245 : Blo 876568 1977245 := bbase (se 3 (by rfl) ⟨370733, by rfl⟩ : syracuseStep 1977245 = 741467) (by norm_num)
theorem B1125289 : Blo 876568 1125289 := bbase (se 2 (by rfl) ⟨421983, by rfl⟩ : syracuseStep 1125289 = 843967) (by norm_num)
theorem B1485749 : Blo 876568 1485749 := bbase (se 5 (by rfl) ⟨69644, by rfl⟩ : syracuseStep 1485749 = 139289) (by norm_num)
theorem B1977317 : Blo 876568 1977317 := bbase (se 4 (by rfl) ⟨185373, by rfl⟩ : syracuseStep 1977317 = 370747) (by norm_num)
theorem B1354733 : Blo 876568 1354733 := bbase (se 3 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 1354733 = 508025) (by norm_num)
theorem B1977389 : Blo 876568 1977389 := bbase (se 3 (by rfl) ⟨370760, by rfl⟩ : syracuseStep 1977389 = 741521) (by norm_num)
theorem B1485877 : Blo 876568 1485877 := bbase (se 5 (by rfl) ⟨69650, by rfl⟩ : syracuseStep 1485877 = 139301) (by norm_num)
theorem B1977461 : Blo 876568 1977461 := bbase (se 5 (by rfl) ⟨92693, by rfl⟩ : syracuseStep 1977461 = 185387) (by norm_num)
theorem B2960549 : Blo 876568 2960549 := bbase (se 4 (by rfl) ⟨277551, by rfl⟩ : syracuseStep 2960549 = 555103) (by norm_num)
theorem B1977533 : Blo 876568 1977533 := bbase (se 3 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 1977533 = 741575) (by norm_num)
theorem B1977605 : Blo 876568 1977605 := bbase (se 4 (by rfl) ⟨185400, by rfl⟩ : syracuseStep 1977605 = 370801) (by norm_num)
theorem B2108717 : Blo 876568 2108717 := bbase (se 3 (by rfl) ⟨395384, by rfl⟩ : syracuseStep 2108717 = 790769) (by norm_num)
theorem B1977677 : Blo 876568 1977677 := bbase (se 3 (by rfl) ⟨370814, by rfl⟩ : syracuseStep 1977677 = 741629) (by norm_num)
theorem B3747221 : Blo 876568 3747221 := bbase (se 6 (by rfl) ⟨87825, by rfl⟩ : syracuseStep 3747221 = 175651) (by norm_num)
theorem B1977749 : Blo 876568 1977749 := bbase (se 6 (by rfl) ⟨46353, by rfl⟩ : syracuseStep 1977749 = 92707) (by norm_num)
theorem B1879453 : Blo 876568 1879453 := bbase (se 3 (by rfl) ⟨352397, by rfl⟩ : syracuseStep 1879453 = 704795) (by norm_num)
theorem B1977821 : Blo 876568 1977821 := bbase (se 3 (by rfl) ⟨370841, by rfl⟩ : syracuseStep 1977821 = 741683) (by norm_num)
theorem B1977893 : Blo 876568 1977893 := bbase (se 4 (by rfl) ⟨185427, by rfl⟩ : syracuseStep 1977893 = 370855) (by norm_num)
theorem B2960981 : Blo 876568 2960981 := bbase (se 8 (by rfl) ⟨17349, by rfl⟩ : syracuseStep 2960981 = 34699) (by norm_num)
theorem B1977965 : Blo 876568 1977965 := bbase (se 3 (by rfl) ⟨370868, by rfl⟩ : syracuseStep 1977965 = 741737) (by norm_num)
theorem B1978037 : Blo 876568 1978037 := bbase (se 5 (by rfl) ⟨92720, by rfl⟩ : syracuseStep 1978037 = 185441) (by norm_num)
theorem B2109149 : Blo 876568 2109149 := bbase (se 3 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 2109149 = 790931) (by norm_num)
theorem B2502373 : Blo 876568 2502373 := bbase (se 4 (by rfl) ⟨234597, by rfl⟩ : syracuseStep 2502373 = 469195) (by norm_num)
theorem B1978109 : Blo 876568 1978109 := bbase (se 3 (by rfl) ⟨370895, by rfl⟩ : syracuseStep 1978109 = 741791) (by norm_num)
theorem B1978181 : Blo 876568 1978181 := bbase (se 4 (by rfl) ⟨185454, by rfl⟩ : syracuseStep 1978181 = 370909) (by norm_num)
theorem B28946261 : Blo 876568 28946261 := bbase (se 9 (by rfl) ⟨84803, by rfl⟩ : syracuseStep 28946261 = 169607) (by norm_num)
theorem B1978253 : Blo 876568 1978253 := bbase (se 3 (by rfl) ⟨370922, by rfl⟩ : syracuseStep 1978253 = 741845) (by norm_num)
theorem B1879949 : Blo 876568 1879949 := bbase (se 3 (by rfl) ⟨352490, by rfl⟩ : syracuseStep 1879949 = 704981) (by norm_num)
theorem B1978325 : Blo 876568 1978325 := bbase (se 7 (by rfl) ⟨23183, by rfl⟩ : syracuseStep 1978325 = 46367) (by norm_num)
theorem B2961413 : Blo 876568 2961413 := bbase (se 4 (by rfl) ⟨277632, by rfl⟩ : syracuseStep 2961413 = 555265) (by norm_num)
theorem B1978397 : Blo 876568 1978397 := bbase (se 3 (by rfl) ⟨370949, by rfl⟩ : syracuseStep 1978397 = 741899) (by norm_num)
theorem B1978469 : Blo 876568 1978469 := bbase (se 4 (by rfl) ⟨185481, by rfl⟩ : syracuseStep 1978469 = 370963) (by norm_num)
theorem B1978541 : Blo 876568 1978541 := bbase (se 3 (by rfl) ⟨370976, by rfl⟩ : syracuseStep 1978541 = 741953) (by norm_num)
theorem B1978613 : Blo 876568 1978613 := bbase (se 5 (by rfl) ⟨92747, by rfl⟩ : syracuseStep 1978613 = 185495) (by norm_num)
theorem B3256613 : Blo 876568 3256613 := bbase (se 4 (by rfl) ⟨305307, by rfl⟩ : syracuseStep 3256613 = 610615) (by norm_num)
theorem B1978685 : Blo 876568 1978685 := bbase (se 3 (by rfl) ⟨371003, by rfl⟩ : syracuseStep 1978685 = 742007) (by norm_num)
theorem B1782101 : Blo 876568 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B1978757 : Blo 876568 1978757 := bbase (se 4 (by rfl) ⟨185508, by rfl⟩ : syracuseStep 1978757 = 371017) (by norm_num)
theorem B2961845 : Blo 876568 2961845 := bbase (se 5 (by rfl) ⟨138836, by rfl⟩ : syracuseStep 2961845 = 277673) (by norm_num)
theorem B1978829 : Blo 876568 1978829 := bbase (se 3 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 1978829 = 742061) (by norm_num)
theorem B1978901 : Blo 876568 1978901 := bbase (se 6 (by rfl) ⟨46380, by rfl⟩ : syracuseStep 1978901 = 92761) (by norm_num)
theorem B1978973 : Blo 876568 1978973 := bbase (se 3 (by rfl) ⟨371057, by rfl⟩ : syracuseStep 1978973 = 742115) (by norm_num)
theorem B7713397 : Blo 876568 7713397 := bbase (se 5 (by rfl) ⟨361565, by rfl⟩ : syracuseStep 7713397 = 723131) (by norm_num)
theorem B1979045 : Blo 876568 1979045 := bbase (se 4 (by rfl) ⟨185535, by rfl⟩ : syracuseStep 1979045 = 371071) (by norm_num)
theorem B1979117 : Blo 876568 1979117 := bbase (se 3 (by rfl) ⟨371084, by rfl⟩ : syracuseStep 1979117 = 742169) (by norm_num)
theorem B2503477 : Blo 876568 2503477 := bbase (se 5 (by rfl) ⟨117350, by rfl⟩ : syracuseStep 2503477 = 234701) (by norm_num)
theorem B1979189 : Blo 876568 1979189 := bbase (se 5 (by rfl) ⟨92774, by rfl⟩ : syracuseStep 1979189 = 185549) (by norm_num)
theorem B2962277 : Blo 876568 2962277 := bbase (se 4 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 2962277 = 555427) (by norm_num)
theorem B1979261 : Blo 876568 1979261 := bbase (se 3 (by rfl) ⟨371111, by rfl⟩ : syracuseStep 1979261 = 742223) (by norm_num)
theorem B2110349 : Blo 876568 2110349 := bbase (se 3 (by rfl) ⟨395690, by rfl⟩ : syracuseStep 2110349 = 791381) (by norm_num)
theorem B1979333 : Blo 876568 1979333 := bbase (se 4 (by rfl) ⟨185562, by rfl⟩ : syracuseStep 1979333 = 371125) (by norm_num)
theorem B1782773 : Blo 876568 1782773 := bbase (se 5 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 1782773 = 167135) (by norm_num)
theorem B1979405 : Blo 876568 1979405 := bbase (se 3 (by rfl) ⟨371138, by rfl⟩ : syracuseStep 1979405 = 742277) (by norm_num)
theorem B1979477 : Blo 876568 1979477 := bbase (se 8 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 1979477 = 23197) (by norm_num)
theorem B3748997 : Blo 876568 3748997 := bbase (se 4 (by rfl) ⟨351468, by rfl⟩ : syracuseStep 3748997 = 702937) (by norm_num)
theorem B1127561 : Blo 876568 1127561 := bbase (se 2 (by rfl) ⟨422835, by rfl⟩ : syracuseStep 1127561 = 845671) (by norm_num)
theorem B1979549 : Blo 876568 1979549 := bbase (se 3 (by rfl) ⟨371165, by rfl⟩ : syracuseStep 1979549 = 742331) (by norm_num)
theorem B1979621 : Blo 876568 1979621 := bbase (se 4 (by rfl) ⟨185589, by rfl⟩ : syracuseStep 1979621 = 371179) (by norm_num)
theorem B2667797 : Blo 876568 2667797 := bbase (se 6 (by rfl) ⟨62526, by rfl⟩ : syracuseStep 2667797 = 125053) (by norm_num)
theorem B2962709 : Blo 876568 2962709 := bbase (se 6 (by rfl) ⟨69438, by rfl⟩ : syracuseStep 2962709 = 138877) (by norm_num)
theorem B1979693 : Blo 876568 1979693 := bbase (se 3 (by rfl) ⟨371192, by rfl⟩ : syracuseStep 1979693 = 742385) (by norm_num)
theorem B2667845 : Blo 876568 2667845 := bbase (se 4 (by rfl) ⟨250110, by rfl⟩ : syracuseStep 2667845 = 500221) (by norm_num)
theorem B3749237 : Blo 876568 3749237 := bbase (se 5 (by rfl) ⟨175745, by rfl⟩ : syracuseStep 3749237 = 351491) (by norm_num)
theorem B1979765 : Blo 876568 1979765 := bbase (se 5 (by rfl) ⟨92801, by rfl⟩ : syracuseStep 1979765 = 185603) (by norm_num)
theorem B1979837 : Blo 876568 1979837 := bbase (se 3 (by rfl) ⟨371219, by rfl⟩ : syracuseStep 1979837 = 742439) (by norm_num)
theorem B1979909 : Blo 876568 1979909 := bbase (se 4 (by rfl) ⟨185616, by rfl⟩ : syracuseStep 1979909 = 371233) (by norm_num)
theorem B1979981 : Blo 876568 1979981 := bbase (se 3 (by rfl) ⟨371246, by rfl⟩ : syracuseStep 1979981 = 742493) (by norm_num)
theorem B1980053 : Blo 876568 1980053 := bbase (se 6 (by rfl) ⟨46407, by rfl⟩ : syracuseStep 1980053 = 92815) (by norm_num)
theorem B1128125 : Blo 876568 1128125 := bbase (se 3 (by rfl) ⟨211523, by rfl⟩ : syracuseStep 1128125 = 423047) (by norm_num)
theorem B2963141 : Blo 876568 2963141 := bbase (se 4 (by rfl) ⟨277794, by rfl⟩ : syracuseStep 2963141 = 555589) (by norm_num)
theorem B1980125 : Blo 876568 1980125 := bbase (se 3 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 1980125 = 742547) (by norm_num)
theorem B1980197 : Blo 876568 1980197 := bbase (se 4 (by rfl) ⟨185643, by rfl⟩ : syracuseStep 1980197 = 371287) (by norm_num)
theorem B1980269 : Blo 876568 1980269 := bbase (se 3 (by rfl) ⟨371300, by rfl⟩ : syracuseStep 1980269 = 742601) (by norm_num)
theorem B1980341 : Blo 876568 1980341 := bbase (se 5 (by rfl) ⟨92828, by rfl⟩ : syracuseStep 1980341 = 185657) (by norm_num)
theorem B964561 : Blo 876568 964561 := bbase (se 2 (by rfl) ⟨361710, by rfl⟩ : syracuseStep 964561 = 723421) (by norm_num)
theorem B4437989 : Blo 876568 4437989 := bbase (se 4 (by rfl) ⟨416061, by rfl⟩ : syracuseStep 4437989 = 832123) (by norm_num)
theorem B1980413 : Blo 876568 1980413 := bbase (se 3 (by rfl) ⟨371327, by rfl⟩ : syracuseStep 1980413 = 742655) (by norm_num)
theorem B5716021 : Blo 876568 5716021 := bbase (se 5 (by rfl) ⟨267938, by rfl⟩ : syracuseStep 5716021 = 535877) (by norm_num)
theorem B1980485 : Blo 876568 1980485 := bbase (se 4 (by rfl) ⟨185670, by rfl⟩ : syracuseStep 1980485 = 371341) (by norm_num)
theorem B2963573 : Blo 876568 2963573 := bbase (se 5 (by rfl) ⟨138917, by rfl⟩ : syracuseStep 2963573 = 277835) (by norm_num)
theorem B4274309 : Blo 876568 4274309 := bbase (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) (by norm_num)
theorem B1980557 : Blo 876568 1980557 := bbase (se 3 (by rfl) ⟨371354, by rfl⟩ : syracuseStep 1980557 = 742709) (by norm_num)
theorem B1128617 : Blo 876568 1128617 := bbase (se 2 (by rfl) ⟨423231, by rfl⟩ : syracuseStep 1128617 = 846463) (by norm_num)
theorem B1980629 : Blo 876568 1980629 := bbase (se 7 (by rfl) ⟨23210, by rfl⟩ : syracuseStep 1980629 = 46421) (by norm_num)
theorem B2504981 : Blo 876568 2504981 := bbase (se 6 (by rfl) ⟨58710, by rfl⟩ : syracuseStep 2504981 = 117421) (by norm_num)
theorem B1980701 : Blo 876568 1980701 := bbase (se 3 (by rfl) ⟨371381, by rfl⟩ : syracuseStep 1980701 = 742763) (by norm_num)
theorem B3160421 : Blo 876568 3160421 := bbase (se 4 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 3160421 = 592579) (by norm_num)
theorem B1980773 : Blo 876568 1980773 := bbase (se 4 (by rfl) ⟨185697, by rfl⟩ : syracuseStep 1980773 = 371395) (by norm_num)
theorem B1980845 : Blo 876568 1980845 := bbase (se 3 (by rfl) ⟨371408, by rfl⟩ : syracuseStep 1980845 = 742817) (by norm_num)
theorem B1980917 : Blo 876568 1980917 := bbase (se 5 (by rfl) ⟨92855, by rfl⟩ : syracuseStep 1980917 = 185711) (by norm_num)
theorem B2964005 : Blo 876568 2964005 := bbase (se 4 (by rfl) ⟨277875, by rfl⟩ : syracuseStep 2964005 = 555751) (by norm_num)
theorem B1980989 : Blo 876568 1980989 := bbase (se 3 (by rfl) ⟨371435, by rfl⟩ : syracuseStep 1980989 = 742871) (by norm_num)
theorem B4995701 : Blo 876568 4995701 := bbase (se 5 (by rfl) ⟨234173, by rfl⟩ : syracuseStep 4995701 = 468347) (by norm_num)
theorem B1981061 : Blo 876568 1981061 := bbase (se 4 (by rfl) ⟨185724, by rfl⟩ : syracuseStep 1981061 = 371449) (by norm_num)
theorem B1784501 : Blo 876568 1784501 := bbase (se 5 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 1784501 = 167297) (by norm_num)
theorem B1981133 : Blo 876568 1981133 := bbase (se 3 (by rfl) ⟨371462, by rfl⟩ : syracuseStep 1981133 = 742925) (by norm_num)
theorem B3160853 : Blo 876568 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B1981205 : Blo 876568 1981205 := bbase (se 6 (by rfl) ⟨46434, by rfl⟩ : syracuseStep 1981205 = 92869) (by norm_num)
theorem B1981277 : Blo 876568 1981277 := bbase (se 3 (by rfl) ⟨371489, by rfl⟩ : syracuseStep 1981277 = 742979) (by norm_num)
theorem B2964437 : Blo 876568 2964437 := bbase (se 7 (by rfl) ⟨34739, by rfl⟩ : syracuseStep 2964437 = 69479) (by norm_num)
theorem B2112637 : Blo 876568 2112637 := bbase (se 3 (by rfl) ⟨396119, by rfl⟩ : syracuseStep 2112637 = 792239) (by norm_num)
theorem B2112733 : Blo 876568 2112733 := bbase (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) (by norm_num)
theorem B4439285 : Blo 876568 4439285 := bbase (se 5 (by rfl) ⟨208091, by rfl⟩ : syracuseStep 4439285 = 416183) (by norm_num)
theorem B7126325 : Blo 876568 7126325 := bbase (se 5 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 7126325 = 668093) (by norm_num)
theorem B2571605 : Blo 876568 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B2964869 : Blo 876568 2964869 := bbase (se 4 (by rfl) ⟨277956, by rfl⟩ : syracuseStep 2964869 = 555913) (by norm_num)
theorem B2112925 : Blo 876568 2112925 := bbase (se 3 (by rfl) ⟨396173, by rfl⟩ : syracuseStep 2112925 = 792347) (by norm_num)
theorem B3751525 : Blo 876568 3751525 := bbase (se 4 (by rfl) ⟨351705, by rfl⟩ : syracuseStep 3751525 = 703411) (by norm_num)
theorem B900721 : Blo 876568 900721 := bbase (se 2 (by rfl) ⟨337770, by rfl⟩ : syracuseStep 900721 = 675541) (by norm_num)
theorem B2375333 : Blo 876568 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B2113253 : Blo 876568 2113253 := bbase (se 4 (by rfl) ⟨198117, by rfl⟩ : syracuseStep 2113253 = 396235) (by norm_num)
theorem B2965301 : Blo 876568 2965301 := bbase (se 5 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 2965301 = 277997) (by norm_num)
theorem B2506565 : Blo 876568 2506565 := bbase (se 4 (by rfl) ⟨234990, by rfl⟩ : syracuseStep 2506565 = 469981) (by norm_num)
theorem B6668405 : Blo 876568 6668405 := bbase (se 5 (by rfl) ⟨312581, by rfl⟩ : syracuseStep 6668405 = 625163) (by norm_num)
theorem B2113685 : Blo 876568 2113685 := bbase (se 6 (by rfl) ⟨49539, by rfl⟩ : syracuseStep 2113685 = 99079) (by norm_num)
theorem B2965733 : Blo 876568 2965733 := bbase (se 4 (by rfl) ⟨278037, by rfl⟩ : syracuseStep 2965733 = 556075) (by norm_num)
theorem B999749 : Blo 876568 999749 := bbase (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) (by norm_num)
theorem B3555701 : Blo 876568 3555701 := bbase (se 5 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 3555701 = 333347) (by norm_num)
theorem B8438165 : Blo 876568 8438165 := bbase (se 6 (by rfl) ⟨197769, by rfl⟩ : syracuseStep 8438165 = 395539) (by norm_num)
theorem B10961365 : Blo 876568 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B2114021 : Blo 876568 2114021 := bbase (se 4 (by rfl) ⟨198189, by rfl⟩ : syracuseStep 2114021 = 396379) (by norm_num)
theorem B2507237 : Blo 876568 2507237 := bbase (se 4 (by rfl) ⟨235053, by rfl⟩ : syracuseStep 2507237 = 470107) (by norm_num)
theorem B3555829 : Blo 876568 3555829 := bbase (se 5 (by rfl) ⟨166679, by rfl⟩ : syracuseStep 3555829 = 333359) (by norm_num)
theorem B4440581 : Blo 876568 4440581 := bbase (se 4 (by rfl) ⟨416304, by rfl⟩ : syracuseStep 4440581 = 832609) (by norm_num)
theorem B2966165 : Blo 876568 2966165 := bbase (se 6 (by rfl) ⟨69519, by rfl⟩ : syracuseStep 2966165 = 139039) (by norm_num)
theorem B967537 : Blo 876568 967537 := bbase (se 2 (by rfl) ⟨362826, by rfl⟩ : syracuseStep 967537 = 725653) (by norm_num)
theorem B1000369 : Blo 876568 1000369 := bbase (se 2 (by rfl) ⟨375138, by rfl⟩ : syracuseStep 1000369 = 750277) (by norm_num)
theorem B3753013 : Blo 876568 3753013 := bbase (se 5 (by rfl) ⟨175922, by rfl⟩ : syracuseStep 3753013 = 351845) (by norm_num)
theorem B3753029 : Blo 876568 3753029 := bbase (se 4 (by rfl) ⟨351846, by rfl⟩ : syracuseStep 3753029 = 703693) (by norm_num)
theorem B2966597 : Blo 876568 2966597 := bbase (se 4 (by rfl) ⟨278118, by rfl⟩ : syracuseStep 2966597 = 556237) (by norm_num)
theorem B1000549 : Blo 876568 1000549 := bbase (se 4 (by rfl) ⟨93801, by rfl⟩ : syracuseStep 1000549 = 187603) (by norm_num)
theorem B1000561 : Blo 876568 1000561 := bbase (se 2 (by rfl) ⟨375210, by rfl⟩ : syracuseStep 1000561 = 750421) (by norm_num)
theorem B2967029 : Blo 876568 2967029 := bbase (se 5 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 2967029 = 278159) (by norm_num)
theorem B2115077 : Blo 876568 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B4441877 : Blo 876568 4441877 := bbase (se 6 (by rfl) ⟨104106, by rfl⟩ : syracuseStep 4441877 = 208213) (by norm_num)
theorem B4015909 : Blo 876568 4015909 := bbase (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) (by norm_num)
theorem B902977 : Blo 876568 902977 := bbase (se 2 (by rfl) ⟨338616, by rfl⟩ : syracuseStep 902977 = 677233) (by norm_num)
theorem B2967461 : Blo 876568 2967461 := bbase (se 4 (by rfl) ⟨278199, by rfl⟩ : syracuseStep 2967461 = 556399) (by norm_num)
theorem B33736661 : Blo 876568 33736661 := bbase (se 7 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 33736661 = 790703) (by norm_num)
theorem B6768629 : Blo 876568 6768629 := bbase (se 5 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 6768629 = 634559) (by norm_num)
theorem B3164197 : Blo 876568 3164197 := bbase (se 4 (by rfl) ⟨296643, by rfl⟩ : syracuseStep 3164197 = 593287) (by norm_num)
theorem B936241 : Blo 876568 936241 := bbase (se 2 (by rfl) ⟨351090, by rfl⟩ : syracuseStep 936241 = 702181) (by norm_num)
theorem B2967893 : Blo 876568 2967893 := bbase (se 10 (by rfl) ⟨4347, by rfl⟩ : syracuseStep 2967893 = 8695) (by norm_num)
theorem B2378069 : Blo 876568 2378069 := bbase (se 10 (by rfl) ⟨3483, by rfl⟩ : syracuseStep 2378069 = 6967) (by norm_num)
theorem B2378101 : Blo 876568 2378101 := bbase (se 5 (by rfl) ⟨111473, by rfl⟩ : syracuseStep 2378101 = 222947) (by norm_num)
theorem B936361 : Blo 876568 936361 := bbase (se 2 (by rfl) ⟨351135, by rfl⟩ : syracuseStep 936361 = 702271) (by norm_num)
theorem B1526293 : Blo 876568 1526293 := bbase (se 6 (by rfl) ⟨35772, by rfl⟩ : syracuseStep 1526293 = 71545) (by norm_num)
theorem B936613 : Blo 876568 936613 := bbase (se 4 (by rfl) ⟨87807, by rfl⟩ : syracuseStep 936613 = 175615) (by norm_num)
theorem B936617 : Blo 876568 936617 := bbase (se 2 (by rfl) ⟨351231, by rfl⟩ : syracuseStep 936617 = 702463) (by norm_num)
theorem B2968325 : Blo 876568 2968325 := bbase (se 4 (by rfl) ⟨278280, by rfl⟩ : syracuseStep 2968325 = 556561) (by norm_num)
theorem B4443173 : Blo 876568 4443173 := bbase (se 4 (by rfl) ⟨416547, by rfl⟩ : syracuseStep 4443173 = 833095) (by norm_num)
theorem B2968757 : Blo 876568 2968757 := bbase (se 5 (by rfl) ⟨139160, by rfl⟩ : syracuseStep 2968757 = 278321) (by norm_num)
theorem B3329221 : Blo 876568 3329221 := bbase (se 4 (by rfl) ⟨312114, by rfl⟩ : syracuseStep 3329221 = 624229) (by norm_num)
theorem B937181 : Blo 876568 937181 := bbase (se 3 (by rfl) ⟨175721, by rfl⟩ : syracuseStep 937181 = 351443) (by norm_num)
theorem B3755285 : Blo 876568 3755285 := bbase (se 6 (by rfl) ⟨88014, by rfl⟩ : syracuseStep 3755285 = 176029) (by norm_num)
theorem B2379029 : Blo 876568 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B937369 : Blo 876568 937369 := bbase (se 2 (by rfl) ⟨351513, by rfl⟩ : syracuseStep 937369 = 703027) (by norm_num)
theorem B3329525 : Blo 876568 3329525 := bbase (se 5 (by rfl) ⟨156071, by rfl⟩ : syracuseStep 3329525 = 312143) (by norm_num)
theorem B2969189 : Blo 876568 2969189 := bbase (se 4 (by rfl) ⟨278361, by rfl⟩ : syracuseStep 2969189 = 556723) (by norm_num)
theorem B5623445 : Blo 876568 5623445 := bbase (se 6 (by rfl) ⟨131799, by rfl⟩ : syracuseStep 5623445 = 263599) (by norm_num)
theorem B4738837 : Blo 876568 4738837 := bbase (se 6 (by rfl) ⟨111066, by rfl⟩ : syracuseStep 4738837 = 222133) (by norm_num)
theorem B2969621 : Blo 876568 2969621 := bbase (se 6 (by rfl) ⟨69600, by rfl⟩ : syracuseStep 2969621 = 139201) (by norm_num)
theorem B938189 : Blo 876568 938189 := bbase (se 3 (by rfl) ⟨175910, by rfl⟩ : syracuseStep 938189 = 351821) (by norm_num)
theorem B2674949 : Blo 876568 2674949 := bbase (se 4 (by rfl) ⟨250776, by rfl⟩ : syracuseStep 2674949 = 501553) (by norm_num)
theorem B4444469 : Blo 876568 4444469 := bbase (se 5 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 4444469 = 416669) (by norm_num)
theorem B3002741 : Blo 876568 3002741 := bbase (se 5 (by rfl) ⟨140753, by rfl⟩ : syracuseStep 3002741 = 281507) (by norm_num)
theorem B2249149 : Blo 876568 2249149 := bbase (se 3 (by rfl) ⟨421715, by rfl⟩ : syracuseStep 2249149 = 843431) (by norm_num)
theorem B2970053 : Blo 876568 2970053 := bbase (se 4 (by rfl) ⟨278442, by rfl⟩ : syracuseStep 2970053 = 556885) (by norm_num)
theorem B1692181 : Blo 876568 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B938633 : Blo 876568 938633 := bbase (se 2 (by rfl) ⟨351987, by rfl⟩ : syracuseStep 938633 = 703975) (by norm_num)
theorem B1692389 : Blo 876568 1692389 := bbase (se 4 (by rfl) ⟨158661, by rfl⟩ : syracuseStep 1692389 = 317323) (by norm_num)
theorem B2970485 : Blo 876568 2970485 := bbase (se 5 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 2970485 = 278483) (by norm_num)
theorem B938881 : Blo 876568 938881 := bbase (se 2 (by rfl) ⟨352080, by rfl⟩ : syracuseStep 938881 = 704161) (by norm_num)
theorem B1070029 : Blo 876568 1070029 := bbase (se 3 (by rfl) ⟨200630, by rfl⟩ : syracuseStep 1070029 = 401261) (by norm_num)
theorem B2675717 : Blo 876568 2675717 := bbase (se 4 (by rfl) ⟨250848, by rfl⟩ : syracuseStep 2675717 = 501697) (by norm_num)
theorem B2249845 : Blo 876568 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B2249869 : Blo 876568 2249869 := bbase (se 3 (by rfl) ⟨421850, by rfl⟩ : syracuseStep 2249869 = 843701) (by norm_num)
theorem B4215989 : Blo 876568 4215989 := bbase (se 5 (by rfl) ⟨197624, by rfl⟩ : syracuseStep 4215989 = 395249) (by norm_num)
theorem B2970917 : Blo 876568 2970917 := bbase (se 4 (by rfl) ⟨278523, by rfl⟩ : syracuseStep 2970917 = 557047) (by norm_num)
theorem B939313 : Blo 876568 939313 := bbase (se 2 (by rfl) ⟨352242, by rfl⟩ : syracuseStep 939313 = 704485) (by norm_num)
theorem B939385 : Blo 876568 939385 := bbase (se 2 (by rfl) ⟨352269, by rfl⟩ : syracuseStep 939385 = 704539) (by norm_num)
theorem B3331637 : Blo 876568 3331637 := bbase (se 5 (by rfl) ⟨156170, by rfl⟩ : syracuseStep 3331637 = 312341) (by norm_num)
theorem B4445765 : Blo 876568 4445765 := bbase (se 4 (by rfl) ⟨416790, by rfl⟩ : syracuseStep 4445765 = 833581) (by norm_num)
theorem B1070761 : Blo 876568 1070761 := bbase (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) (by norm_num)
theorem B2971349 : Blo 876568 2971349 := bbase (se 7 (by rfl) ⟨34820, by rfl⟩ : syracuseStep 2971349 = 69641) (by norm_num)
theorem B939757 : Blo 876568 939757 := bbase (se 3 (by rfl) ⟨176204, by rfl⟩ : syracuseStep 939757 = 352409) (by norm_num)
theorem B3331925 : Blo 876568 3331925 := bbase (se 9 (by rfl) ⟨9761, by rfl⟩ : syracuseStep 3331925 = 19523) (by norm_num)
theorem B1267813 : Blo 876568 1267813 := bbase (se 4 (by rfl) ⟨118857, by rfl⟩ : syracuseStep 1267813 = 237715) (by norm_num)
theorem B940133 : Blo 876568 940133 := bbase (se 4 (by rfl) ⟨88137, by rfl⟩ : syracuseStep 940133 = 176275) (by norm_num)
theorem B2971781 : Blo 876568 2971781 := bbase (se 4 (by rfl) ⟨278604, by rfl⟩ : syracuseStep 2971781 = 557209) (by norm_num)
theorem B940205 : Blo 876568 940205 := bbase (se 3 (by rfl) ⟨176288, by rfl⟩ : syracuseStep 940205 = 352577) (by norm_num)
theorem B5003765 : Blo 876568 5003765 := bbase (se 5 (by rfl) ⟨234551, by rfl⟩ : syracuseStep 5003765 = 469103) (by norm_num)
theorem B2808341 : Blo 876568 2808341 := bbase (se 6 (by rfl) ⟨65820, by rfl⟩ : syracuseStep 2808341 = 131641) (by norm_num)
theorem B5331701 : Blo 876568 5331701 := bbase (se 5 (by rfl) ⟨249923, by rfl⟩ : syracuseStep 5331701 = 499847) (by norm_num)
theorem B4447061 : Blo 876568 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B2218853 : Blo 876568 2218853 := bbase (se 4 (by rfl) ⟨208017, by rfl⟩ : syracuseStep 2218853 = 416035) (by norm_num)
theorem B3333109 : Blo 876568 3333109 := bbase (se 5 (by rfl) ⟨156239, by rfl⟩ : syracuseStep 3333109 = 312479) (by norm_num)
theorem B5069909 : Blo 876568 5069909 := bbase (se 8 (by rfl) ⟨29706, by rfl⟩ : syracuseStep 5069909 = 59413) (by norm_num)
theorem B3562613 : Blo 876568 3562613 := bbase (se 5 (by rfl) ⟨166997, by rfl⟩ : syracuseStep 3562613 = 333995) (by norm_num)
theorem B2219197 : Blo 876568 2219197 := bbase (se 3 (by rfl) ⟨416099, by rfl⟩ : syracuseStep 2219197 = 832199) (by norm_num)
theorem B3759317 : Blo 876568 3759317 := bbase (se 7 (by rfl) ⟨44054, by rfl⟩ : syracuseStep 3759317 = 88109) (by norm_num)
theorem B3333413 : Blo 876568 3333413 := bbase (se 4 (by rfl) ⟨312507, by rfl⟩ : syracuseStep 3333413 = 625015) (by norm_num)
theorem B2219309 : Blo 876568 2219309 := bbase (se 3 (by rfl) ⟨416120, by rfl⟩ : syracuseStep 2219309 = 832241) (by norm_num)
theorem B4513157 : Blo 876568 4513157 := bbase (se 4 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 4513157 = 846217) (by norm_num)
theorem B1334701 : Blo 876568 1334701 := bbase (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) (by norm_num)
theorem B9493973 : Blo 876568 9493973 := bbase (se 7 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 9493973 = 222515) (by norm_num)
theorem B2219501 : Blo 876568 2219501 := bbase (se 3 (by rfl) ⟨416156, by rfl⟩ : syracuseStep 2219501 = 832313) (by norm_num)
theorem B5004949 : Blo 876568 5004949 := bbase (se 6 (by rfl) ⟨117303, by rfl⟩ : syracuseStep 5004949 = 234607) (by norm_num)
theorem B6676181 : Blo 876568 6676181 := bbase (se 7 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 6676181 = 156473) (by norm_num)
theorem B2219845 : Blo 876568 2219845 := bbase (se 4 (by rfl) ⟨208110, by rfl⟩ : syracuseStep 2219845 = 416221) (by norm_num)
theorem B1269661 : Blo 876568 1269661 := bbase (se 3 (by rfl) ⟨238061, by rfl⟩ : syracuseStep 1269661 = 476123) (by norm_num)
theorem B2219957 : Blo 876568 2219957 := bbase (se 5 (by rfl) ⟨104060, by rfl⟩ : syracuseStep 2219957 = 208121) (by norm_num)
theorem B1925141 : Blo 876568 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B4448357 : Blo 876568 4448357 := bbase (se 4 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 4448357 = 834067) (by norm_num)
theorem B2220149 : Blo 876568 2220149 := bbase (se 5 (by rfl) ⟨104069, by rfl⟩ : syracuseStep 2220149 = 208139) (by norm_num)
theorem B1204517 : Blo 876568 1204517 := bbase (se 4 (by rfl) ⟨112923, by rfl⟩ : syracuseStep 1204517 = 225847) (by norm_num)
theorem B2810261 : Blo 876568 2810261 := bbase (se 6 (by rfl) ⟨65865, by rfl⟩ : syracuseStep 2810261 = 131731) (by norm_num)
theorem B2220493 : Blo 876568 2220493 := bbase (se 3 (by rfl) ⟨416342, by rfl⟩ : syracuseStep 2220493 = 832685) (by norm_num)
theorem B2220605 : Blo 876568 2220605 := bbase (se 3 (by rfl) ⟨416363, by rfl⟩ : syracuseStep 2220605 = 832727) (by norm_num)
theorem B2220797 : Blo 876568 2220797 := bbase (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) (by norm_num)
theorem B3761093 : Blo 876568 3761093 := bbase (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) (by norm_num)
theorem B2221141 : Blo 876568 2221141 := bbase (se 8 (by rfl) ⟨13014, by rfl⟩ : syracuseStep 2221141 = 26029) (by norm_num)
theorem B2221253 : Blo 876568 2221253 := bbase (se 4 (by rfl) ⟨208242, by rfl⟩ : syracuseStep 2221253 = 416485) (by norm_num)
theorem B1500493 : Blo 876568 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B3335525 : Blo 876568 3335525 := bbase (se 4 (by rfl) ⟨312705, by rfl⟩ : syracuseStep 3335525 = 625411) (by norm_num)
theorem B4449653 : Blo 876568 4449653 := bbase (se 5 (by rfl) ⟨208577, by rfl⟩ : syracuseStep 4449653 = 417155) (by norm_num)
theorem B2221445 : Blo 876568 2221445 := bbase (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) (by norm_num)
theorem B5006933 : Blo 876568 5006933 := bbase (se 8 (by rfl) ⟨29337, by rfl⟩ : syracuseStep 5006933 = 58675) (by norm_num)
theorem B2254445 : Blo 876568 2254445 := bbase (se 3 (by rfl) ⟨422708, by rfl⟩ : syracuseStep 2254445 = 845417) (by norm_num)
theorem B3335813 : Blo 876568 3335813 := bbase (se 4 (by rfl) ⟨312732, by rfl⟩ : syracuseStep 3335813 = 625465) (by norm_num)
theorem B1926805 : Blo 876568 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B1664725 : Blo 876568 1664725 := bbase (se 7 (by rfl) ⟨19508, by rfl⟩ : syracuseStep 1664725 = 39017) (by norm_num)
theorem B2221789 : Blo 876568 2221789 := bbase (se 3 (by rfl) ⟨416585, by rfl⟩ : syracuseStep 2221789 = 833171) (by norm_num)
theorem B2811685 : Blo 876568 2811685 := bbase (se 4 (by rfl) ⟨263595, by rfl⟩ : syracuseStep 2811685 = 527191) (by norm_num)
theorem B2221901 : Blo 876568 2221901 := bbase (se 3 (by rfl) ⟨416606, by rfl⟩ : syracuseStep 2221901 = 833213) (by norm_num)
theorem B1664869 : Blo 876568 1664869 := bbase (se 4 (by rfl) ⟨156081, by rfl⟩ : syracuseStep 1664869 = 312163) (by norm_num)
theorem B3172213 : Blo 876568 3172213 := bbase (se 5 (by rfl) ⟨148697, by rfl⟩ : syracuseStep 3172213 = 297395) (by norm_num)
theorem B1665029 : Blo 876568 1665029 := bbase (se 4 (by rfl) ⟨156096, by rfl⟩ : syracuseStep 1665029 = 312193) (by norm_num)
theorem B2222093 : Blo 876568 2222093 := bbase (se 3 (by rfl) ⟨416642, by rfl⟩ : syracuseStep 2222093 = 833285) (by norm_num)
theorem B1665173 : Blo 876568 1665173 := bbase (se 6 (by rfl) ⟨39027, by rfl⟩ : syracuseStep 1665173 = 78055) (by norm_num)
theorem B2812133 : Blo 876568 2812133 := bbase (se 4 (by rfl) ⟨263637, by rfl⟩ : syracuseStep 2812133 = 527275) (by norm_num)
theorem B2222437 : Blo 876568 2222437 := bbase (se 4 (by rfl) ⟨208353, by rfl⟩ : syracuseStep 2222437 = 416707) (by norm_num)
theorem B1665461 : Blo 876568 1665461 := bbase (se 5 (by rfl) ⟨78068, by rfl⟩ : syracuseStep 1665461 = 156137) (by norm_num)
theorem B2222549 : Blo 876568 2222549 := bbase (se 7 (by rfl) ⟨26045, by rfl⟩ : syracuseStep 2222549 = 52091) (by norm_num)
theorem B1665613 : Blo 876568 1665613 := bbase (se 3 (by rfl) ⟨312302, by rfl⟩ : syracuseStep 1665613 = 624605) (by norm_num)
theorem B4450949 : Blo 876568 4450949 := bbase (se 4 (by rfl) ⟨417276, by rfl⟩ : syracuseStep 4450949 = 834553) (by norm_num)
theorem B9988757 : Blo 876568 9988757 := bbase (se 6 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 9988757 = 468223) (by norm_num)
theorem B2222741 : Blo 876568 2222741 := bbase (se 6 (by rfl) ⟨52095, by rfl⟩ : syracuseStep 2222741 = 104191) (by norm_num)
theorem B1338133 : Blo 876568 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B3336997 : Blo 876568 3336997 := bbase (se 4 (by rfl) ⟨312843, by rfl⟩ : syracuseStep 3336997 = 625687) (by norm_num)
theorem B3566405 : Blo 876568 3566405 := bbase (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) (by norm_num)
theorem B1665917 : Blo 876568 1665917 := bbase (se 3 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 1665917 = 624719) (by norm_num)
theorem B2223085 : Blo 876568 2223085 := bbase (se 3 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 2223085 = 833657) (by norm_num)
theorem B4221989 : Blo 876568 4221989 := bbase (se 4 (by rfl) ⟨395811, by rfl⟩ : syracuseStep 4221989 = 791623) (by norm_num)
theorem B3337301 : Blo 876568 3337301 := bbase (se 8 (by rfl) ⟨19554, by rfl⟩ : syracuseStep 3337301 = 39109) (by norm_num)
theorem B2223197 : Blo 876568 2223197 := bbase (se 3 (by rfl) ⟨416849, by rfl⟩ : syracuseStep 2223197 = 833699) (by norm_num)
theorem B2256005 : Blo 876568 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B1404157 : Blo 876568 1404157 := bbase (se 3 (by rfl) ⟨263279, by rfl⟩ : syracuseStep 1404157 = 526559) (by norm_num)
theorem B2223389 : Blo 876568 2223389 := bbase (se 3 (by rfl) ⟨416885, by rfl⟩ : syracuseStep 2223389 = 833771) (by norm_num)
theorem B1404221 : Blo 876568 1404221 := bbase (se 3 (by rfl) ⟨263291, by rfl⟩ : syracuseStep 1404221 = 526583) (by norm_num)
theorem B1109477 : Blo 876568 1109477 := bbase (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) (by norm_num)
theorem B1109533 : Blo 876568 1109533 := bbase (se 3 (by rfl) ⟨208037, by rfl⟩ : syracuseStep 1109533 = 416075) (by norm_num)
theorem B1666669 : Blo 876568 1666669 := bbase (se 3 (by rfl) ⟨312500, by rfl⟩ : syracuseStep 1666669 = 625001) (by norm_num)
theorem B2223733 : Blo 876568 2223733 := bbase (se 5 (by rfl) ⟨104237, by rfl⟩ : syracuseStep 2223733 = 208475) (by norm_num)
theorem B1109629 : Blo 876568 1109629 := bbase (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) (by norm_num)
theorem B1044193 : Blo 876568 1044193 := bbase (se 2 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 1044193 = 783145) (by norm_num)
theorem B2223845 : Blo 876568 2223845 := bbase (se 4 (by rfl) ⟨208485, by rfl⟩ : syracuseStep 2223845 = 416971) (by norm_num)
theorem B5009141 : Blo 876568 5009141 := bbase (se 5 (by rfl) ⟨234803, by rfl⟩ : syracuseStep 5009141 = 469607) (by norm_num)
theorem B1666813 : Blo 876568 1666813 := bbase (se 3 (by rfl) ⟨312527, by rfl⟩ : syracuseStep 1666813 = 625055) (by norm_num)
theorem B1109801 : Blo 876568 1109801 := bbase (se 2 (by rfl) ⟨416175, by rfl⟩ : syracuseStep 1109801 = 832351) (by norm_num)
theorem B1929053 : Blo 876568 1929053 := bbase (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) (by norm_num)
theorem B1109857 : Blo 876568 1109857 := bbase (se 2 (by rfl) ⟨416196, by rfl⟩ : syracuseStep 1109857 = 832393) (by norm_num)
theorem B3567493 : Blo 876568 3567493 := bbase (se 4 (by rfl) ⟨334452, by rfl⟩ : syracuseStep 3567493 = 668905) (by norm_num)
theorem B4452245 : Blo 876568 4452245 := bbase (se 6 (by rfl) ⟨104349, by rfl⟩ : syracuseStep 4452245 = 208699) (by norm_num)
theorem B1666973 : Blo 876568 1666973 := bbase (se 3 (by rfl) ⟨312557, by rfl⟩ : syracuseStep 1666973 = 625115) (by norm_num)
theorem B2224037 : Blo 876568 2224037 := bbase (se 4 (by rfl) ⟨208503, by rfl⟩ : syracuseStep 2224037 = 417007) (by norm_num)
theorem B1109953 : Blo 876568 1109953 := bbase (se 2 (by rfl) ⟨416232, by rfl⟩ : syracuseStep 1109953 = 832465) (by norm_num)
theorem B1667117 : Blo 876568 1667117 := bbase (se 3 (by rfl) ⟨312584, by rfl⟩ : syracuseStep 1667117 = 625169) (by norm_num)
theorem B1110125 : Blo 876568 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B1110181 : Blo 876568 1110181 := bbase (se 4 (by rfl) ⟨104079, by rfl⟩ : syracuseStep 1110181 = 208159) (by norm_num)
theorem B1503469 : Blo 876568 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B2224381 : Blo 876568 2224381 := bbase (se 3 (by rfl) ⟨417071, by rfl⟩ : syracuseStep 2224381 = 834143) (by norm_num)
theorem B1110277 : Blo 876568 1110277 := bbase (se 4 (by rfl) ⟨104088, by rfl⟩ : syracuseStep 1110277 = 208177) (by norm_num)
theorem B1667405 : Blo 876568 1667405 := bbase (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) (by norm_num)
theorem B2224493 : Blo 876568 2224493 := bbase (se 3 (by rfl) ⟨417092, by rfl⟩ : syracuseStep 2224493 = 834185) (by norm_num)
theorem B1110449 : Blo 876568 1110449 := bbase (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) (by norm_num)
theorem B2814389 : Blo 876568 2814389 := bbase (se 5 (by rfl) ⟨131924, by rfl⟩ : syracuseStep 2814389 = 263849) (by norm_num)
theorem B1667557 : Blo 876568 1667557 := bbase (se 4 (by rfl) ⟨156333, by rfl⟩ : syracuseStep 1667557 = 312667) (by norm_num)
theorem B1110505 : Blo 876568 1110505 := bbase (se 2 (by rfl) ⟨416439, by rfl⟩ : syracuseStep 1110505 = 832879) (by norm_num)
theorem B2224685 : Blo 876568 2224685 := bbase (se 3 (by rfl) ⟨417128, by rfl⟩ : syracuseStep 2224685 = 834257) (by norm_num)
theorem B1110601 : Blo 876568 1110601 := bbase (se 2 (by rfl) ⟨416475, by rfl⟩ : syracuseStep 1110601 = 832951) (by norm_num)
theorem B1405541 : Blo 876568 1405541 := bbase (se 4 (by rfl) ⟨131769, by rfl⟩ : syracuseStep 1405541 = 263539) (by norm_num)
theorem B1405669 : Blo 876568 1405669 := bbase (se 4 (by rfl) ⟨131781, by rfl⟩ : syracuseStep 1405669 = 263563) (by norm_num)
theorem B1110773 : Blo 876568 1110773 := bbase (se 5 (by rfl) ⟨52067, by rfl⟩ : syracuseStep 1110773 = 104135) (by norm_num)
theorem B1667861 : Blo 876568 1667861 := bbase (se 6 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 1667861 = 78181) (by norm_num)
theorem B1110829 : Blo 876568 1110829 := bbase (se 3 (by rfl) ⟨208280, by rfl⟩ : syracuseStep 1110829 = 416561) (by norm_num)
theorem B5206837 : Blo 876568 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B2225029 : Blo 876568 2225029 := bbase (se 4 (by rfl) ⟨208596, by rfl⟩ : syracuseStep 2225029 = 417193) (by norm_num)
theorem B1110925 : Blo 876568 1110925 := bbase (se 3 (by rfl) ⟨208298, by rfl⟩ : syracuseStep 1110925 = 416597) (by norm_num)
theorem B2225141 : Blo 876568 2225141 := bbase (se 5 (by rfl) ⟨104303, by rfl⟩ : syracuseStep 2225141 = 208607) (by norm_num)
theorem B3568661 : Blo 876568 3568661 := bbase (se 6 (by rfl) ⟨83640, by rfl⟩ : syracuseStep 3568661 = 167281) (by norm_num)
theorem B1111097 : Blo 876568 1111097 := bbase (se 2 (by rfl) ⟨416661, by rfl⟩ : syracuseStep 1111097 = 833323) (by norm_num)
theorem B1111153 : Blo 876568 1111153 := bbase (se 2 (by rfl) ⟨416682, by rfl⟩ : syracuseStep 1111153 = 833365) (by norm_num)
theorem B3339413 : Blo 876568 3339413 := bbase (se 6 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 3339413 = 156535) (by norm_num)
theorem B4453541 : Blo 876568 4453541 := bbase (se 4 (by rfl) ⟨417519, by rfl⟩ : syracuseStep 4453541 = 835039) (by norm_num)
theorem B2225333 : Blo 876568 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B1111249 : Blo 876568 1111249 := bbase (se 2 (by rfl) ⟨416718, by rfl⟩ : syracuseStep 1111249 = 833437) (by norm_num)
theorem B1111421 : Blo 876568 1111421 := bbase (se 3 (by rfl) ⟨208391, by rfl⟩ : syracuseStep 1111421 = 416783) (by norm_num)
theorem B1111477 : Blo 876568 1111477 := bbase (se 5 (by rfl) ⟨52100, by rfl⟩ : syracuseStep 1111477 = 104201) (by norm_num)
theorem B3339701 : Blo 876568 3339701 := bbase (se 5 (by rfl) ⟨156548, by rfl⟩ : syracuseStep 3339701 = 313097) (by norm_num)
theorem B1668613 : Blo 876568 1668613 := bbase (se 4 (by rfl) ⟨156432, by rfl⟩ : syracuseStep 1668613 = 312865) (by norm_num)
theorem B1406477 : Blo 876568 1406477 := bbase (se 3 (by rfl) ⟨263714, by rfl⟩ : syracuseStep 1406477 = 527429) (by norm_num)
theorem B2225677 : Blo 876568 2225677 := bbase (se 3 (by rfl) ⟨417314, by rfl⟩ : syracuseStep 2225677 = 834629) (by norm_num)
theorem B1111573 : Blo 876568 1111573 := bbase (se 6 (by rfl) ⟨26052, by rfl⟩ : syracuseStep 1111573 = 52105) (by norm_num)
theorem B5633621 : Blo 876568 5633621 := bbase (se 8 (by rfl) ⟨33009, by rfl⟩ : syracuseStep 5633621 = 66019) (by norm_num)
theorem B1898101 : Blo 876568 1898101 := bbase (se 5 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 1898101 = 177947) (by norm_num)
theorem B2225789 : Blo 876568 2225789 := bbase (se 3 (by rfl) ⟨417335, by rfl⟩ : syracuseStep 2225789 = 834671) (by norm_num)
theorem B1668757 : Blo 876568 1668757 := bbase (se 6 (by rfl) ⟨39111, by rfl⟩ : syracuseStep 1668757 = 78223) (by norm_num)
theorem B1111745 : Blo 876568 1111745 := bbase (se 2 (by rfl) ⟨416904, by rfl⟩ : syracuseStep 1111745 = 833809) (by norm_num)
theorem B1111801 : Blo 876568 1111801 := bbase (se 2 (by rfl) ⟨416925, by rfl⟩ : syracuseStep 1111801 = 833851) (by norm_num)
theorem B1406765 : Blo 876568 1406765 := bbase (se 3 (by rfl) ⟨263768, by rfl⟩ : syracuseStep 1406765 = 527537) (by norm_num)
theorem B1668917 : Blo 876568 1668917 := bbase (se 5 (by rfl) ⟨78230, by rfl⟩ : syracuseStep 1668917 = 156461) (by norm_num)
theorem B2225981 : Blo 876568 2225981 := bbase (se 3 (by rfl) ⟨417371, by rfl⟩ : syracuseStep 2225981 = 834743) (by norm_num)
theorem B1111897 : Blo 876568 1111897 := bbase (se 2 (by rfl) ⟨416961, by rfl⟩ : syracuseStep 1111897 = 833923) (by norm_num)
theorem B1144681 : Blo 876568 1144681 := bbase (se 2 (by rfl) ⟨429255, by rfl⟩ : syracuseStep 1144681 = 858511) (by norm_num)
theorem B2258837 : Blo 876568 2258837 := bbase (se 6 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 2258837 = 105883) (by norm_num)
theorem B1669061 : Blo 876568 1669061 := bbase (se 4 (by rfl) ⟨156474, by rfl⟩ : syracuseStep 1669061 = 312949) (by norm_num)
theorem B1112069 : Blo 876568 1112069 := bbase (se 4 (by rfl) ⟨104256, by rfl⟩ : syracuseStep 1112069 = 208513) (by norm_num)
theorem B1505317 : Blo 876568 1505317 := bbase (se 4 (by rfl) ⟨141123, by rfl⟩ : syracuseStep 1505317 = 282247) (by norm_num)
theorem B1112125 : Blo 876568 1112125 := bbase (se 3 (by rfl) ⟨208523, by rfl⟩ : syracuseStep 1112125 = 417047) (by norm_num)
theorem B8124565 : Blo 876568 8124565 := bbase (se 6 (by rfl) ⟨190419, by rfl⟩ : syracuseStep 8124565 = 380839) (by norm_num)
theorem B2226325 : Blo 876568 2226325 := bbase (se 6 (by rfl) ⟨52179, by rfl⟩ : syracuseStep 2226325 = 104359) (by norm_num)
theorem B1112221 : Blo 876568 1112221 := bbase (se 3 (by rfl) ⟨208541, by rfl⟩ : syracuseStep 1112221 = 417083) (by norm_num)
theorem B1407181 : Blo 876568 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B1669349 : Blo 876568 1669349 := bbase (se 4 (by rfl) ⟨156501, by rfl⟩ : syracuseStep 1669349 = 313003) (by norm_num)
theorem B2226437 : Blo 876568 2226437 := bbase (se 4 (by rfl) ⟨208728, by rfl⟩ : syracuseStep 2226437 = 417457) (by norm_num)
theorem B12024085 : Blo 876568 12024085 := bbase (se 6 (by rfl) ⟨281814, by rfl⟩ : syracuseStep 12024085 = 563629) (by norm_num)
theorem B1112393 : Blo 876568 1112393 := bbase (se 2 (by rfl) ⟨417147, by rfl⟩ : syracuseStep 1112393 = 834295) (by norm_num)
theorem B1669501 : Blo 876568 1669501 := bbase (se 3 (by rfl) ⟨313031, by rfl⟩ : syracuseStep 1669501 = 626063) (by norm_num)
theorem B1112449 : Blo 876568 1112449 := bbase (se 2 (by rfl) ⟨417168, by rfl⟩ : syracuseStep 1112449 = 834337) (by norm_num)
theorem B4454837 : Blo 876568 4454837 := bbase (se 5 (by rfl) ⟨208820, by rfl⟩ : syracuseStep 4454837 = 417641) (by norm_num)
theorem B2226629 : Blo 876568 2226629 := bbase (se 4 (by rfl) ⟨208746, by rfl⟩ : syracuseStep 2226629 = 417493) (by norm_num)
theorem B1112545 : Blo 876568 1112545 := bbase (se 2 (by rfl) ⟨417204, by rfl⟩ : syracuseStep 1112545 = 834409) (by norm_num)
theorem B1505837 : Blo 876568 1505837 := bbase (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) (by norm_num)
theorem B3340885 : Blo 876568 3340885 := bbase (se 8 (by rfl) ⟨19575, by rfl⟩ : syracuseStep 3340885 = 39151) (by norm_num)
theorem B1112717 : Blo 876568 1112717 := bbase (se 3 (by rfl) ⟨208634, by rfl⟩ : syracuseStep 1112717 = 417269) (by norm_num)
theorem B1669805 : Blo 876568 1669805 := bbase (se 3 (by rfl) ⟨313088, by rfl⟩ : syracuseStep 1669805 = 626177) (by norm_num)
theorem B1112773 : Blo 876568 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B2226973 : Blo 876568 2226973 := bbase (se 3 (by rfl) ⟨417557, by rfl⟩ : syracuseStep 2226973 = 835115) (by norm_num)
theorem B1112869 : Blo 876568 1112869 := bbase (se 4 (by rfl) ⟨104331, by rfl⟩ : syracuseStep 1112869 = 208663) (by norm_num)
theorem B1604437 : Blo 876568 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B3341189 : Blo 876568 3341189 := bbase (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) (by norm_num)
theorem B2227085 : Blo 876568 2227085 := bbase (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) (by norm_num)
theorem B1113041 : Blo 876568 1113041 := bbase (se 2 (by rfl) ⟨417390, by rfl⟩ : syracuseStep 1113041 = 834781) (by norm_num)
theorem B1113097 : Blo 876568 1113097 := bbase (se 2 (by rfl) ⟨417411, by rfl⟩ : syracuseStep 1113097 = 834823) (by norm_num)
theorem B2227277 : Blo 876568 2227277 := bbase (se 3 (by rfl) ⟨417614, by rfl⟩ : syracuseStep 2227277 = 835229) (by norm_num)
theorem B1113193 : Blo 876568 1113193 := bbase (se 2 (by rfl) ⟨417447, by rfl⟩ : syracuseStep 1113193 = 834895) (by norm_num)
theorem B1408117 : Blo 876568 1408117 := bbase (se 5 (by rfl) ⟨66005, by rfl⟩ : syracuseStep 1408117 = 132011) (by norm_num)
theorem B1113365 : Blo 876568 1113365 := bbase (se 6 (by rfl) ⟨26094, by rfl⟩ : syracuseStep 1113365 = 52189) (by norm_num)
theorem B6683957 : Blo 876568 6683957 := bbase (se 5 (by rfl) ⟨313310, by rfl⟩ : syracuseStep 6683957 = 626621) (by norm_num)
theorem B1113421 : Blo 876568 1113421 := bbase (se 3 (by rfl) ⟨208766, by rfl⟩ : syracuseStep 1113421 = 417533) (by norm_num)
theorem B1670557 : Blo 876568 1670557 := bbase (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) (by norm_num)
theorem B2227621 : Blo 876568 2227621 := bbase (se 4 (by rfl) ⟨208839, by rfl⟩ : syracuseStep 2227621 = 417679) (by norm_num)
theorem B1113517 : Blo 876568 1113517 := bbase (se 3 (by rfl) ⟨208784, by rfl⟩ : syracuseStep 1113517 = 417569) (by norm_num)
theorem B2227733 : Blo 876568 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B1670701 : Blo 876568 1670701 := bbase (se 3 (by rfl) ⟨313256, by rfl⟩ : syracuseStep 1670701 = 626513) (by norm_num)
theorem B1113689 : Blo 876568 1113689 := bbase (se 2 (by rfl) ⟨417633, by rfl⟩ : syracuseStep 1113689 = 835267) (by norm_num)
theorem B1113745 : Blo 876568 1113745 := bbase (se 2 (by rfl) ⟨417654, by rfl⟩ : syracuseStep 1113745 = 835309) (by norm_num)
theorem B4456133 : Blo 876568 4456133 := bbase (se 4 (by rfl) ⟨417762, by rfl⟩ : syracuseStep 4456133 = 835525) (by norm_num)
theorem B1670861 : Blo 876568 1670861 := bbase (se 3 (by rfl) ⟨313286, by rfl⟩ : syracuseStep 1670861 = 626573) (by norm_num)
theorem B2227925 : Blo 876568 2227925 := bbase (se 7 (by rfl) ⟨26108, by rfl⟩ : syracuseStep 2227925 = 52217) (by norm_num)
theorem B1113841 : Blo 876568 1113841 := bbase (se 2 (by rfl) ⟨417690, by rfl⟩ : syracuseStep 1113841 = 835381) (by norm_num)
theorem B1671005 : Blo 876568 1671005 := bbase (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) (by norm_num)
theorem B1114013 : Blo 876568 1114013 := bbase (se 3 (by rfl) ⟨208877, by rfl⟩ : syracuseStep 1114013 = 417755) (by norm_num)
theorem B1114069 : Blo 876568 1114069 := bbase (se 7 (by rfl) ⟨13055, by rfl⟩ : syracuseStep 1114069 = 26111) (by norm_num)
theorem B1900525 : Blo 876568 1900525 := bbase (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) (by norm_num)
theorem B4227061 : Blo 876568 4227061 := bbase (se 5 (by rfl) ⟨198143, by rfl⟩ : syracuseStep 4227061 = 396287) (by norm_num)
theorem B1409123 : Blo 876568 1409123 := bstep (se 1 (by rfl) ⟨1056842, by rfl⟩ : syracuseStep 1409123 = 2113685) B2113685
theorem B1409347 : Blo 876568 1409347 := bstep (se 1 (by rfl) ⟨1057010, by rfl⟩ : syracuseStep 1409347 = 2114021) B2114021
theorem B1671491 : Blo 876568 1671491 := bstep (se 1 (by rfl) ⟨1253618, by rfl⟩ : syracuseStep 1671491 = 2507237) B2507237
theorem B4456781 : Blo 876568 4456781 := bstep (se 3 (by rfl) ⟨835646, by rfl⟩ : syracuseStep 4456781 = 1671293) B1671293
theorem B2228593 : Blo 876568 2228593 := bstep (se 2 (by rfl) ⟨835722, by rfl⟩ : syracuseStep 2228593 = 1671445) B1671445
theorem B14615153 : Blo 876568 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B2228867 : Blo 876568 2228867 := bstep (se 1 (by rfl) ⟨1671650, by rfl⟩ : syracuseStep 2228867 = 3343301) B3343301
theorem B3212045 : Blo 876568 3212045 := bstep (se 3 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 3212045 = 1204517) B1204517
theorem B2818925 : Blo 876568 2818925 := bstep (se 3 (by rfl) ⟨528548, by rfl⟩ : syracuseStep 2818925 = 1057097) B1057097
theorem B4752269 : Blo 876568 4752269 := bstep (se 3 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 4752269 = 1782101) B1782101
theorem B1410065 : Blo 876568 1410065 := bstep (se 2 (by rfl) ⟨528774, by rfl⟩ : syracuseStep 1410065 = 1057549) B1057549
theorem B1410257 : Blo 876568 1410257 := bstep (se 2 (by rfl) ⟨528846, by rfl⟩ : syracuseStep 1410257 = 1057693) B1057693
theorem B1410385 : Blo 876568 1410385 := bstep (se 2 (by rfl) ⟨528894, by rfl⟩ : syracuseStep 1410385 = 1057789) B1057789
theorem B13731185 : Blo 876568 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B5637539 : Blo 876568 5637539 := bstep (se 1 (by rfl) ⟨4228154, by rfl⟩ : syracuseStep 5637539 = 8456309) B8456309
theorem B2819693 : Blo 876568 2819693 := bstep (se 3 (by rfl) ⟨528692, by rfl⟩ : syracuseStep 2819693 = 1057385) B1057385
theorem B2000657 : Blo 876568 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B2820205 : Blo 876568 2820205 := bstep (se 3 (by rfl) ⟨528788, by rfl⟩ : syracuseStep 2820205 = 1057577) B1057577
theorem B4229617 : Blo 876568 4229617 := bstep (se 2 (by rfl) ⟨1586106, by rfl⟩ : syracuseStep 4229617 = 3172213) B3172213
theorem B10029581 : Blo 876568 10029581 := bstep (se 3 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 10029581 = 3761093) B3761093
theorem B2820707 : Blo 876568 2820707 := bstep (se 1 (by rfl) ⟨2115530, by rfl⟩ : syracuseStep 2820707 = 4231061) B4231061
theorem B7998065 : Blo 876568 7998065 := bstep (se 2 (by rfl) ⟨2999274, by rfl⟩ : syracuseStep 7998065 = 5998549) B5998549
theorem B5999345 : Blo 876568 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B2001827 : Blo 876568 2001827 := bstep (se 1 (by rfl) ⟨1501370, by rfl⟩ : syracuseStep 2001827 = 3002741) B3002741
theorem B6261745 : Blo 876568 6261745 := bstep (se 2 (by rfl) ⟨2348154, by rfl⟩ : syracuseStep 6261745 = 4696309) B4696309
theorem B986179 : Blo 876568 986179 := bstep (se 1 (by rfl) ⟨739634, by rfl⟩ : syracuseStep 986179 = 1479269) B1479269
theorem B11242637 : Blo 876568 11242637 := bstep (se 3 (by rfl) ⟨2107994, by rfl⟩ : syracuseStep 11242637 = 4215989) B4215989
theorem B986323 : Blo 876568 986323 := bstep (se 1 (by rfl) ⟨739742, by rfl⟩ : syracuseStep 986323 = 1479485) B1479485
theorem B1248481 : Blo 876568 1248481 := bstep (se 2 (by rfl) ⟨468180, by rfl⟩ : syracuseStep 1248481 = 936361) B936361
theorem B986467 : Blo 876568 986467 := bstep (se 1 (by rfl) ⟨739850, by rfl⟩ : syracuseStep 986467 = 1479701) B1479701
theorem B2035057 : Blo 876568 2035057 := bstep (se 2 (by rfl) ⟨763146, by rfl⟩ : syracuseStep 2035057 = 1526293) B1526293
theorem B986611 : Blo 876568 986611 := bstep (se 1 (by rfl) ⟨739958, by rfl⟩ : syracuseStep 986611 = 1479917) B1479917
theorem B986755 : Blo 876568 986755 := bstep (se 1 (by rfl) ⟨740066, by rfl⟩ : syracuseStep 986755 = 1480133) B1480133
theorem B986899 : Blo 876568 986899 := bstep (se 1 (by rfl) ⟨740174, by rfl⟩ : syracuseStep 986899 = 1480349) B1480349
theorem B1249187 : Blo 876568 1249187 := bstep (se 1 (by rfl) ⟨936890, by rfl⟩ : syracuseStep 1249187 = 1873781) B1873781
theorem B987043 : Blo 876568 987043 := bstep (se 1 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 987043 = 1480565) B1480565
theorem B5640205 : Blo 876568 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B987187 : Blo 876568 987187 := bstep (se 1 (by rfl) ⟨740390, by rfl⟩ : syracuseStep 987187 = 1480781) B1480781
theorem B1314881 : Blo 876568 1314881 := bstep (se 2 (by rfl) ⟨493080, by rfl⟩ : syracuseStep 1314881 = 986161) B986161
theorem B1314899 : Blo 876568 1314899 := bstep (se 1 (by rfl) ⟨986174, by rfl⟩ : syracuseStep 1314899 = 1972349) B1972349
theorem B1314929 : Blo 876568 1314929 := bstep (se 2 (by rfl) ⟨493098, by rfl⟩ : syracuseStep 1314929 = 986197) B986197
theorem B1314947 : Blo 876568 1314947 := bstep (se 1 (by rfl) ⟨986210, by rfl⟩ : syracuseStep 1314947 = 1972421) B1972421
theorem B1314977 : Blo 876568 1314977 := bstep (se 2 (by rfl) ⟨493116, by rfl⟩ : syracuseStep 1314977 = 986233) B986233
theorem B1314995 : Blo 876568 1314995 := bstep (se 1 (by rfl) ⟨986246, by rfl⟩ : syracuseStep 1314995 = 1972493) B1972493
theorem B987331 : Blo 876568 987331 := bstep (se 1 (by rfl) ⟨740498, by rfl⟩ : syracuseStep 987331 = 1480997) B1480997
theorem B1315025 : Blo 876568 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B1315043 : Blo 876568 1315043 := bstep (se 1 (by rfl) ⟨986282, by rfl⟩ : syracuseStep 1315043 = 1972565) B1972565
theorem B1315073 : Blo 876568 1315073 := bstep (se 2 (by rfl) ⟨493152, by rfl⟩ : syracuseStep 1315073 = 986305) B986305
theorem B1315091 : Blo 876568 1315091 := bstep (se 1 (by rfl) ⟨986318, by rfl⟩ : syracuseStep 1315091 = 1972637) B1972637
theorem B1315121 : Blo 876568 1315121 := bstep (se 2 (by rfl) ⟨493170, by rfl⟩ : syracuseStep 1315121 = 986341) B986341
theorem B1315139 : Blo 876568 1315139 := bstep (se 1 (by rfl) ⟨986354, by rfl⟩ : syracuseStep 1315139 = 1972709) B1972709
theorem B1872209 : Blo 876568 1872209 := bstep (se 2 (by rfl) ⟨702078, by rfl⟩ : syracuseStep 1872209 = 1404157) B1404157
theorem B987475 : Blo 876568 987475 := bstep (se 1 (by rfl) ⟨740606, by rfl⟩ : syracuseStep 987475 = 1481213) B1481213
theorem B1315169 : Blo 876568 1315169 := bstep (se 2 (by rfl) ⟨493188, by rfl⟩ : syracuseStep 1315169 = 986377) B986377
theorem B1872227 : Blo 876568 1872227 := bstep (se 1 (by rfl) ⟨1404170, by rfl⟩ : syracuseStep 1872227 = 2808341) B2808341
theorem B1315187 : Blo 876568 1315187 := bstep (se 1 (by rfl) ⟨986390, by rfl⟩ : syracuseStep 1315187 = 1972781) B1972781
theorem B1315217 : Blo 876568 1315217 := bstep (se 2 (by rfl) ⟨493206, by rfl⟩ : syracuseStep 1315217 = 986413) B986413
theorem B1315235 : Blo 876568 1315235 := bstep (se 1 (by rfl) ⟨986426, by rfl⟩ : syracuseStep 1315235 = 1972853) B1972853
theorem B1315265 : Blo 876568 1315265 := bstep (se 2 (by rfl) ⟨493224, by rfl⟩ : syracuseStep 1315265 = 986449) B986449
theorem B8556997 : Blo 876568 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B1315283 : Blo 876568 1315283 := bstep (se 1 (by rfl) ⟨986462, by rfl⟩ : syracuseStep 1315283 = 1972925) B1972925
theorem B987619 : Blo 876568 987619 := bstep (se 1 (by rfl) ⟨740714, by rfl⟩ : syracuseStep 987619 = 1481429) B1481429
theorem B1315313 : Blo 876568 1315313 := bstep (se 2 (by rfl) ⟨493242, by rfl⟩ : syracuseStep 1315313 = 986485) B986485
theorem B1315331 : Blo 876568 1315331 := bstep (se 1 (by rfl) ⟨986498, by rfl⟩ : syracuseStep 1315331 = 1972997) B1972997
theorem B1315361 : Blo 876568 1315361 := bstep (se 2 (by rfl) ⟨493260, by rfl⟩ : syracuseStep 1315361 = 986521) B986521
theorem B1249825 : Blo 876568 1249825 := bstep (se 2 (by rfl) ⟨468684, by rfl⟩ : syracuseStep 1249825 = 937369) B937369
theorem B1315379 : Blo 876568 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B1479235 : Blo 876568 1479235 := bstep (se 1 (by rfl) ⟨1109426, by rfl⟩ : syracuseStep 1479235 = 2218853) B2218853
theorem B1315409 : Blo 876568 1315409 := bstep (se 2 (by rfl) ⟨493278, by rfl⟩ : syracuseStep 1315409 = 986557) B986557
theorem B1315427 : Blo 876568 1315427 := bstep (se 1 (by rfl) ⟨986570, by rfl⟩ : syracuseStep 1315427 = 1973141) B1973141
theorem B987763 : Blo 876568 987763 := bstep (se 1 (by rfl) ⟨740822, by rfl⟩ : syracuseStep 987763 = 1481645) B1481645
theorem B1315457 : Blo 876568 1315457 := bstep (se 2 (by rfl) ⟨493296, by rfl⟩ : syracuseStep 1315457 = 986593) B986593
theorem B1315475 : Blo 876568 1315475 := bstep (se 1 (by rfl) ⟨986606, by rfl⟩ : syracuseStep 1315475 = 1973213) B1973213
theorem B1249939 : Blo 876568 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B1315505 : Blo 876568 1315505 := bstep (se 2 (by rfl) ⟨493314, by rfl⟩ : syracuseStep 1315505 = 986629) B986629
theorem B1315523 : Blo 876568 1315523 := bstep (se 1 (by rfl) ⟨986642, by rfl⟩ : syracuseStep 1315523 = 1973285) B1973285
theorem B1479377 : Blo 876568 1479377 := bstep (se 2 (by rfl) ⟨554766, by rfl⟩ : syracuseStep 1479377 = 1109533) B1109533
theorem B1315553 : Blo 876568 1315553 := bstep (se 2 (by rfl) ⟨493332, by rfl⟩ : syracuseStep 1315553 = 986665) B986665
theorem B1315571 : Blo 876568 1315571 := bstep (se 1 (by rfl) ⟨986678, by rfl⟩ : syracuseStep 1315571 = 1973357) B1973357
theorem B987907 : Blo 876568 987907 := bstep (se 1 (by rfl) ⟨740930, by rfl⟩ : syracuseStep 987907 = 1481861) B1481861
theorem B1315601 : Blo 876568 1315601 := bstep (se 2 (by rfl) ⟨493350, by rfl⟩ : syracuseStep 1315601 = 986701) B986701
theorem B1315619 : Blo 876568 1315619 := bstep (se 1 (by rfl) ⟨986714, by rfl⟩ : syracuseStep 1315619 = 1973429) B1973429
theorem B1315649 : Blo 876568 1315649 := bstep (se 2 (by rfl) ⟨493368, by rfl⟩ : syracuseStep 1315649 = 986737) B986737
theorem B1479505 : Blo 876568 1479505 := bstep (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) B1109629
theorem B1315667 : Blo 876568 1315667 := bstep (se 1 (by rfl) ⟨986750, by rfl⟩ : syracuseStep 1315667 = 1973501) B1973501
theorem B1315697 : Blo 876568 1315697 := bstep (se 2 (by rfl) ⟨493386, by rfl⟩ : syracuseStep 1315697 = 986773) B986773
theorem B1479539 : Blo 876568 1479539 := bstep (se 1 (by rfl) ⟨1109654, by rfl⟩ : syracuseStep 1479539 = 2219309) B2219309
theorem B1315715 : Blo 876568 1315715 := bstep (se 1 (by rfl) ⟨986786, by rfl⟩ : syracuseStep 1315715 = 1973573) B1973573
theorem B988051 : Blo 876568 988051 := bstep (se 1 (by rfl) ⟨741038, by rfl⟩ : syracuseStep 988051 = 1482077) B1482077
theorem B1315745 : Blo 876568 1315745 := bstep (se 2 (by rfl) ⟨493404, by rfl⟩ : syracuseStep 1315745 = 986809) B986809
theorem B1315763 : Blo 876568 1315763 := bstep (se 1 (by rfl) ⟨986822, by rfl⟩ : syracuseStep 1315763 = 1973645) B1973645
theorem B1315793 : Blo 876568 1315793 := bstep (se 2 (by rfl) ⟨493422, by rfl⟩ : syracuseStep 1315793 = 986845) B986845
theorem B1315811 : Blo 876568 1315811 := bstep (se 1 (by rfl) ⟨986858, by rfl⟩ : syracuseStep 1315811 = 1973717) B1973717
theorem B6329315 : Blo 876568 6329315 := bstep (se 1 (by rfl) ⟨4746986, by rfl⟩ : syracuseStep 6329315 = 9493973) B9493973
theorem B1479667 : Blo 876568 1479667 := bstep (se 1 (by rfl) ⟨1109750, by rfl⟩ : syracuseStep 1479667 = 2219501) B2219501
theorem B1315841 : Blo 876568 1315841 := bstep (se 2 (by rfl) ⟨493440, by rfl⟩ : syracuseStep 1315841 = 986881) B986881
theorem B1315859 : Blo 876568 1315859 := bstep (se 1 (by rfl) ⟨986894, by rfl⟩ : syracuseStep 1315859 = 1973789) B1973789
theorem B988195 : Blo 876568 988195 := bstep (se 1 (by rfl) ⟨741146, by rfl⟩ : syracuseStep 988195 = 1482293) B1482293
theorem B1315889 : Blo 876568 1315889 := bstep (se 2 (by rfl) ⟨493458, by rfl⟩ : syracuseStep 1315889 = 986917) B986917
theorem B1315907 : Blo 876568 1315907 := bstep (se 1 (by rfl) ⟨986930, by rfl⟩ : syracuseStep 1315907 = 1973861) B1973861
theorem B5706821 : Blo 876568 5706821 := bstep (se 4 (by rfl) ⟨535014, by rfl⟩ : syracuseStep 5706821 = 1070029) B1070029
theorem B1315937 : Blo 876568 1315937 := bstep (se 2 (by rfl) ⟨493476, by rfl⟩ : syracuseStep 1315937 = 986953) B986953
theorem B1315955 : Blo 876568 1315955 := bstep (se 1 (by rfl) ⟨986966, by rfl⟩ : syracuseStep 1315955 = 1973933) B1973933
theorem B1479809 : Blo 876568 1479809 := bstep (se 2 (by rfl) ⟨554928, by rfl⟩ : syracuseStep 1479809 = 1109857) B1109857
theorem B1315985 : Blo 876568 1315985 := bstep (se 2 (by rfl) ⟨493494, by rfl⟩ : syracuseStep 1315985 = 986989) B986989
theorem B1316003 : Blo 876568 1316003 := bstep (se 1 (by rfl) ⟨987002, by rfl⟩ : syracuseStep 1316003 = 1974005) B1974005
theorem B4756657 : Blo 876568 4756657 := bstep (se 2 (by rfl) ⟨1783746, by rfl⟩ : syracuseStep 4756657 = 3567493) B3567493
theorem B988339 : Blo 876568 988339 := bstep (se 1 (by rfl) ⟨741254, by rfl⟩ : syracuseStep 988339 = 1482509) B1482509
theorem B1316033 : Blo 876568 1316033 := bstep (se 2 (by rfl) ⟨493512, by rfl⟩ : syracuseStep 1316033 = 987025) B987025
theorem B1316051 : Blo 876568 1316051 := bstep (se 1 (by rfl) ⟨987038, by rfl⟩ : syracuseStep 1316051 = 1974077) B1974077
theorem B11277539 : Blo 876568 11277539 := bstep (se 1 (by rfl) ⟨8458154, by rfl⟩ : syracuseStep 11277539 = 16916309) B16916309
theorem B1316081 : Blo 876568 1316081 := bstep (se 2 (by rfl) ⟨493530, by rfl⟩ : syracuseStep 1316081 = 987061) B987061
theorem B1479937 : Blo 876568 1479937 := bstep (se 2 (by rfl) ⟨554976, by rfl⟩ : syracuseStep 1479937 = 1109953) B1109953
theorem B1316099 : Blo 876568 1316099 := bstep (se 1 (by rfl) ⟨987074, by rfl⟩ : syracuseStep 1316099 = 1974149) B1974149
theorem B1316129 : Blo 876568 1316129 := bstep (se 2 (by rfl) ⟨493548, by rfl⟩ : syracuseStep 1316129 = 987097) B987097
theorem B1479971 : Blo 876568 1479971 := bstep (se 1 (by rfl) ⟨1109978, by rfl⟩ : syracuseStep 1479971 = 2219957) B2219957
theorem B1316147 : Blo 876568 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B988483 : Blo 876568 988483 := bstep (se 1 (by rfl) ⟨741362, by rfl⟩ : syracuseStep 988483 = 1482725) B1482725
theorem B1316177 : Blo 876568 1316177 := bstep (se 2 (by rfl) ⟨493566, by rfl⟩ : syracuseStep 1316177 = 987133) B987133
theorem B1316195 : Blo 876568 1316195 := bstep (se 1 (by rfl) ⟨987146, by rfl⟩ : syracuseStep 1316195 = 1974293) B1974293
theorem B1316225 : Blo 876568 1316225 := bstep (se 2 (by rfl) ⟨493584, by rfl⟩ : syracuseStep 1316225 = 987169) B987169
theorem B1316243 : Blo 876568 1316243 := bstep (se 1 (by rfl) ⟨987182, by rfl⟩ : syracuseStep 1316243 = 1974365) B1974365
theorem B1480099 : Blo 876568 1480099 := bstep (se 1 (by rfl) ⟨1110074, by rfl⟩ : syracuseStep 1480099 = 2220149) B2220149
theorem B1316273 : Blo 876568 1316273 := bstep (se 2 (by rfl) ⟨493602, by rfl⟩ : syracuseStep 1316273 = 987205) B987205
theorem B1316291 : Blo 876568 1316291 := bstep (se 1 (by rfl) ⟨987218, by rfl⟩ : syracuseStep 1316291 = 1974437) B1974437
theorem B988627 : Blo 876568 988627 := bstep (se 1 (by rfl) ⟨741470, by rfl⟩ : syracuseStep 988627 = 1482941) B1482941
theorem B1316321 : Blo 876568 1316321 := bstep (se 2 (by rfl) ⟨493620, by rfl⟩ : syracuseStep 1316321 = 987241) B987241
theorem B1316339 : Blo 876568 1316339 := bstep (se 1 (by rfl) ⟨987254, by rfl⟩ : syracuseStep 1316339 = 1974509) B1974509
theorem B1316369 : Blo 876568 1316369 := bstep (se 2 (by rfl) ⟨493638, by rfl⟩ : syracuseStep 1316369 = 987277) B987277
theorem B1316387 : Blo 876568 1316387 := bstep (se 1 (by rfl) ⟨987290, by rfl⟩ : syracuseStep 1316387 = 1974581) B1974581
theorem B1480241 : Blo 876568 1480241 := bstep (se 2 (by rfl) ⟨555090, by rfl⟩ : syracuseStep 1480241 = 1110181) B1110181
theorem B1316417 : Blo 876568 1316417 := bstep (se 2 (by rfl) ⟨493656, by rfl⟩ : syracuseStep 1316417 = 987313) B987313
theorem B1316435 : Blo 876568 1316435 := bstep (se 1 (by rfl) ⟨987326, by rfl⟩ : syracuseStep 1316435 = 1974653) B1974653
theorem B988771 : Blo 876568 988771 := bstep (se 1 (by rfl) ⟨741578, by rfl⟩ : syracuseStep 988771 = 1483157) B1483157
theorem B1316465 : Blo 876568 1316465 := bstep (se 2 (by rfl) ⟨493674, by rfl⟩ : syracuseStep 1316465 = 987349) B987349
theorem B1316483 : Blo 876568 1316483 := bstep (se 1 (by rfl) ⟨987362, by rfl⟩ : syracuseStep 1316483 = 1974725) B1974725
theorem B2004625 : Blo 876568 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B1316513 : Blo 876568 1316513 := bstep (se 2 (by rfl) ⟨493692, by rfl⟩ : syracuseStep 1316513 = 987385) B987385
theorem B1480369 : Blo 876568 1480369 := bstep (se 2 (by rfl) ⟨555138, by rfl⟩ : syracuseStep 1480369 = 1110277) B1110277
theorem B1316531 : Blo 876568 1316531 := bstep (se 1 (by rfl) ⟨987398, by rfl⟩ : syracuseStep 1316531 = 1974797) B1974797
theorem B1316561 : Blo 876568 1316561 := bstep (se 2 (by rfl) ⟨493710, by rfl⟩ : syracuseStep 1316561 = 987421) B987421
theorem B1480403 : Blo 876568 1480403 := bstep (se 1 (by rfl) ⟨1110302, by rfl⟩ : syracuseStep 1480403 = 2220605) B2220605
theorem B1316579 : Blo 876568 1316579 := bstep (se 1 (by rfl) ⟨987434, by rfl⟩ : syracuseStep 1316579 = 1974869) B1974869
theorem B988915 : Blo 876568 988915 := bstep (se 1 (by rfl) ⟨741686, by rfl⟩ : syracuseStep 988915 = 1483373) B1483373
theorem B1316609 : Blo 876568 1316609 := bstep (se 2 (by rfl) ⟨493728, by rfl⟩ : syracuseStep 1316609 = 987457) B987457
theorem B1316627 : Blo 876568 1316627 := bstep (se 1 (by rfl) ⟨987470, by rfl⟩ : syracuseStep 1316627 = 1974941) B1974941
theorem B1316657 : Blo 876568 1316657 := bstep (se 2 (by rfl) ⟨493746, by rfl⟩ : syracuseStep 1316657 = 987493) B987493
theorem B1316675 : Blo 876568 1316675 := bstep (se 1 (by rfl) ⟨987506, by rfl⟩ : syracuseStep 1316675 = 1975013) B1975013
theorem B1480531 : Blo 876568 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B1316705 : Blo 876568 1316705 := bstep (se 2 (by rfl) ⟨493764, by rfl⟩ : syracuseStep 1316705 = 987529) B987529
theorem B1316723 : Blo 876568 1316723 := bstep (se 1 (by rfl) ⟨987542, by rfl⟩ : syracuseStep 1316723 = 1975085) B1975085
theorem B989059 : Blo 876568 989059 := bstep (se 1 (by rfl) ⟨741794, by rfl⟩ : syracuseStep 989059 = 1483589) B1483589
theorem B1316753 : Blo 876568 1316753 := bstep (se 2 (by rfl) ⟨493782, by rfl⟩ : syracuseStep 1316753 = 987565) B987565
theorem B1316771 : Blo 876568 1316771 := bstep (se 1 (by rfl) ⟨987578, by rfl⟩ : syracuseStep 1316771 = 1975157) B1975157
theorem B1316801 : Blo 876568 1316801 := bstep (se 2 (by rfl) ⟨493800, by rfl⟩ : syracuseStep 1316801 = 987601) B987601
theorem B11999173 : Blo 876568 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B1316819 : Blo 876568 1316819 := bstep (se 1 (by rfl) ⟨987614, by rfl⟩ : syracuseStep 1316819 = 1975229) B1975229
theorem B1251283 : Blo 876568 1251283 := bstep (se 1 (by rfl) ⟨938462, by rfl⟩ : syracuseStep 1251283 = 1876925) B1876925
theorem B1480673 : Blo 876568 1480673 := bstep (se 2 (by rfl) ⟨555252, by rfl⟩ : syracuseStep 1480673 = 1110505) B1110505
theorem B1316849 : Blo 876568 1316849 := bstep (se 2 (by rfl) ⟨493818, by rfl⟩ : syracuseStep 1316849 = 987637) B987637
theorem B1316867 : Blo 876568 1316867 := bstep (se 1 (by rfl) ⟨987650, by rfl⟩ : syracuseStep 1316867 = 1975301) B1975301
theorem B989203 : Blo 876568 989203 := bstep (se 1 (by rfl) ⟨741902, by rfl⟩ : syracuseStep 989203 = 1483805) B1483805
theorem B1316897 : Blo 876568 1316897 := bstep (se 2 (by rfl) ⟨493836, by rfl⟩ : syracuseStep 1316897 = 987673) B987673
theorem B1316915 : Blo 876568 1316915 := bstep (se 1 (by rfl) ⟨987686, by rfl⟩ : syracuseStep 1316915 = 1975373) B1975373
theorem B1316945 : Blo 876568 1316945 := bstep (se 2 (by rfl) ⟨493854, by rfl⟩ : syracuseStep 1316945 = 987709) B987709
theorem B1480801 : Blo 876568 1480801 := bstep (se 2 (by rfl) ⟨555300, by rfl⟩ : syracuseStep 1480801 = 1110601) B1110601
theorem B1316963 : Blo 876568 1316963 := bstep (se 1 (by rfl) ⟨987722, by rfl⟩ : syracuseStep 1316963 = 1975445) B1975445
theorem B1316993 : Blo 876568 1316993 := bstep (se 2 (by rfl) ⟨493872, by rfl⟩ : syracuseStep 1316993 = 987745) B987745
theorem B1480835 : Blo 876568 1480835 := bstep (se 1 (by rfl) ⟨1110626, by rfl⟩ : syracuseStep 1480835 = 2221253) B2221253
theorem B1317011 : Blo 876568 1317011 := bstep (se 1 (by rfl) ⟨987758, by rfl⟩ : syracuseStep 1317011 = 1975517) B1975517
theorem B1054867 : Blo 876568 1054867 := bstep (se 1 (by rfl) ⟨791150, by rfl⟩ : syracuseStep 1054867 = 1582301) B1582301
theorem B989347 : Blo 876568 989347 := bstep (se 1 (by rfl) ⟨742010, by rfl⟩ : syracuseStep 989347 = 1484021) B1484021
theorem B2496689 : Blo 876568 2496689 := bstep (se 2 (by rfl) ⟨936258, by rfl⟩ : syracuseStep 2496689 = 1872517) B1872517
theorem B1317041 : Blo 876568 1317041 := bstep (se 2 (by rfl) ⟨493890, by rfl⟩ : syracuseStep 1317041 = 987781) B987781
theorem B1317059 : Blo 876568 1317059 := bstep (se 1 (by rfl) ⟨987794, by rfl⟩ : syracuseStep 1317059 = 1975589) B1975589
theorem B1317089 : Blo 876568 1317089 := bstep (se 2 (by rfl) ⟨493908, by rfl⟩ : syracuseStep 1317089 = 987817) B987817
theorem B1317107 : Blo 876568 1317107 := bstep (se 1 (by rfl) ⟨987830, by rfl⟩ : syracuseStep 1317107 = 1975661) B1975661
theorem B1480963 : Blo 876568 1480963 := bstep (se 1 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 1480963 = 2221445) B2221445
theorem B1317137 : Blo 876568 1317137 := bstep (se 2 (by rfl) ⟨493926, by rfl⟩ : syracuseStep 1317137 = 987853) B987853
theorem B1317155 : Blo 876568 1317155 := bstep (se 1 (by rfl) ⟨987866, by rfl⟩ : syracuseStep 1317155 = 1975733) B1975733
theorem B1972529 : Blo 876568 1972529 := bstep (se 2 (by rfl) ⟨739698, by rfl⟩ : syracuseStep 1972529 = 1479397) B1479397
theorem B1874225 : Blo 876568 1874225 := bstep (se 2 (by rfl) ⟨702834, by rfl⟩ : syracuseStep 1874225 = 1405669) B1405669
theorem B989491 : Blo 876568 989491 := bstep (se 1 (by rfl) ⟨742118, by rfl⟩ : syracuseStep 989491 = 1484237) B1484237
theorem B1317185 : Blo 876568 1317185 := bstep (se 2 (by rfl) ⟨493944, by rfl⟩ : syracuseStep 1317185 = 987889) B987889
theorem B1972547 : Blo 876568 1972547 := bstep (se 1 (by rfl) ⟨1479410, by rfl⟩ : syracuseStep 1972547 = 2958821) B2958821
theorem B1317203 : Blo 876568 1317203 := bstep (se 1 (by rfl) ⟨987902, by rfl⟩ : syracuseStep 1317203 = 1975805) B1975805
theorem B1317233 : Blo 876568 1317233 := bstep (se 2 (by rfl) ⟨493962, by rfl⟩ : syracuseStep 1317233 = 987925) B987925
theorem B1317251 : Blo 876568 1317251 := bstep (se 1 (by rfl) ⟨987938, by rfl⟩ : syracuseStep 1317251 = 1975877) B1975877
theorem B1481105 : Blo 876568 1481105 := bstep (se 2 (by rfl) ⟨555414, by rfl⟩ : syracuseStep 1481105 = 1110829) B1110829
theorem B1317281 : Blo 876568 1317281 := bstep (se 2 (by rfl) ⟨493980, by rfl⟩ : syracuseStep 1317281 = 987961) B987961
theorem B1317299 : Blo 876568 1317299 := bstep (se 1 (by rfl) ⟨987974, by rfl⟩ : syracuseStep 1317299 = 1975949) B1975949
theorem B989635 : Blo 876568 989635 := bstep (se 1 (by rfl) ⟨742226, by rfl⟩ : syracuseStep 989635 = 1484453) B1484453
theorem B1317329 : Blo 876568 1317329 := bstep (se 2 (by rfl) ⟨493998, by rfl⟩ : syracuseStep 1317329 = 987997) B987997
theorem B1317347 : Blo 876568 1317347 := bstep (se 1 (by rfl) ⟨988010, by rfl⟩ : syracuseStep 1317347 = 1976021) B1976021
theorem B1317377 : Blo 876568 1317377 := bstep (se 2 (by rfl) ⟨494016, by rfl⟩ : syracuseStep 1317377 = 988033) B988033
theorem B1481233 : Blo 876568 1481233 := bstep (se 2 (by rfl) ⟨555462, by rfl⟩ : syracuseStep 1481233 = 1110925) B1110925
theorem B1317395 : Blo 876568 1317395 := bstep (se 1 (by rfl) ⟨988046, by rfl⟩ : syracuseStep 1317395 = 1976093) B1976093
theorem B1317425 : Blo 876568 1317425 := bstep (se 2 (by rfl) ⟨494034, by rfl⟩ : syracuseStep 1317425 = 988069) B988069
theorem B1481267 : Blo 876568 1481267 := bstep (se 1 (by rfl) ⟨1110950, by rfl⟩ : syracuseStep 1481267 = 2221901) B2221901
theorem B1317443 : Blo 876568 1317443 := bstep (se 1 (by rfl) ⟨988082, by rfl⟩ : syracuseStep 1317443 = 1976165) B1976165
theorem B1972817 : Blo 876568 1972817 := bstep (se 2 (by rfl) ⟨739806, by rfl⟩ : syracuseStep 1972817 = 1479613) B1479613
theorem B989779 : Blo 876568 989779 := bstep (se 1 (by rfl) ⟨742334, by rfl⟩ : syracuseStep 989779 = 1484669) B1484669
theorem B1317473 : Blo 876568 1317473 := bstep (se 2 (by rfl) ⟨494052, by rfl⟩ : syracuseStep 1317473 = 988105) B988105
theorem B1579619 : Blo 876568 1579619 := bstep (se 1 (by rfl) ⟨1184714, by rfl⟩ : syracuseStep 1579619 = 2369429) B2369429
theorem B1972835 : Blo 876568 1972835 := bstep (se 1 (by rfl) ⟨1479626, by rfl⟩ : syracuseStep 1972835 = 2959253) B2959253
theorem B1317491 : Blo 876568 1317491 := bstep (se 1 (by rfl) ⟨988118, by rfl⟩ : syracuseStep 1317491 = 1976237) B1976237
theorem B1317521 : Blo 876568 1317521 := bstep (se 2 (by rfl) ⟨494070, by rfl⟩ : syracuseStep 1317521 = 988141) B988141
theorem B1317539 : Blo 876568 1317539 := bstep (se 1 (by rfl) ⟨988154, by rfl⟩ : syracuseStep 1317539 = 1976309) B1976309
theorem B1481395 : Blo 876568 1481395 := bstep (se 1 (by rfl) ⟨1111046, by rfl⟩ : syracuseStep 1481395 = 2222093) B2222093
theorem B1317569 : Blo 876568 1317569 := bstep (se 2 (by rfl) ⟨494088, by rfl⟩ : syracuseStep 1317569 = 988177) B988177
theorem B1186499 : Blo 876568 1186499 := bstep (se 1 (by rfl) ⟨889874, by rfl⟩ : syracuseStep 1186499 = 1779749) B1779749
theorem B1317587 : Blo 876568 1317587 := bstep (se 1 (by rfl) ⟨988190, by rfl⟩ : syracuseStep 1317587 = 1976381) B1976381
theorem B4004579 : Blo 876568 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B989923 : Blo 876568 989923 := bstep (se 1 (by rfl) ⟨742442, by rfl⟩ : syracuseStep 989923 = 1484885) B1484885
theorem B1317617 : Blo 876568 1317617 := bstep (se 2 (by rfl) ⟨494106, by rfl⟩ : syracuseStep 1317617 = 988213) B988213
theorem B1317635 : Blo 876568 1317635 := bstep (se 1 (by rfl) ⟨988226, by rfl⟩ : syracuseStep 1317635 = 1976453) B1976453
theorem B1317665 : Blo 876568 1317665 := bstep (se 2 (by rfl) ⟨494124, by rfl⟩ : syracuseStep 1317665 = 988249) B988249
theorem B1317683 : Blo 876568 1317683 := bstep (se 1 (by rfl) ⟨988262, by rfl⟩ : syracuseStep 1317683 = 1976525) B1976525
theorem B1481537 : Blo 876568 1481537 := bstep (se 2 (by rfl) ⟨555576, by rfl⟩ : syracuseStep 1481537 = 1111153) B1111153
theorem B1874755 : Blo 876568 1874755 := bstep (se 1 (by rfl) ⟨1406066, by rfl⟩ : syracuseStep 1874755 = 2812133) B2812133
theorem B1317713 : Blo 876568 1317713 := bstep (se 2 (by rfl) ⟨494142, by rfl⟩ : syracuseStep 1317713 = 988285) B988285
theorem B1317731 : Blo 876568 1317731 := bstep (se 1 (by rfl) ⟨988298, by rfl⟩ : syracuseStep 1317731 = 1976597) B1976597
theorem B1973105 : Blo 876568 1973105 := bstep (se 2 (by rfl) ⟨739914, by rfl⟩ : syracuseStep 1973105 = 1479829) B1479829
theorem B990067 : Blo 876568 990067 := bstep (se 1 (by rfl) ⟨742550, by rfl⟩ : syracuseStep 990067 = 1485101) B1485101
theorem B1317761 : Blo 876568 1317761 := bstep (se 2 (by rfl) ⟨494160, by rfl⟩ : syracuseStep 1317761 = 988321) B988321
theorem B1973123 : Blo 876568 1973123 := bstep (se 1 (by rfl) ⟨1479842, by rfl⟩ : syracuseStep 1973123 = 2959685) B2959685
theorem B1317779 : Blo 876568 1317779 := bstep (se 1 (by rfl) ⟨988334, by rfl⟩ : syracuseStep 1317779 = 1976669) B1976669
theorem B1317809 : Blo 876568 1317809 := bstep (se 2 (by rfl) ⟨494178, by rfl⟩ : syracuseStep 1317809 = 988357) B988357
theorem B1481665 : Blo 876568 1481665 := bstep (se 2 (by rfl) ⟨555624, by rfl⟩ : syracuseStep 1481665 = 1111249) B1111249
theorem B1317827 : Blo 876568 1317827 := bstep (se 1 (by rfl) ⟨988370, by rfl⟩ : syracuseStep 1317827 = 1976741) B1976741
theorem B1317857 : Blo 876568 1317857 := bstep (se 2 (by rfl) ⟨494196, by rfl⟩ : syracuseStep 1317857 = 988393) B988393
theorem B1481699 : Blo 876568 1481699 := bstep (se 1 (by rfl) ⟨1111274, by rfl⟩ : syracuseStep 1481699 = 2222549) B2222549
theorem B1317875 : Blo 876568 1317875 := bstep (se 1 (by rfl) ⟨988406, by rfl⟩ : syracuseStep 1317875 = 1976813) B1976813
theorem B990211 : Blo 876568 990211 := bstep (se 1 (by rfl) ⟨742658, by rfl⟩ : syracuseStep 990211 = 1485317) B1485317
theorem B1317905 : Blo 876568 1317905 := bstep (se 2 (by rfl) ⟨494214, by rfl⟩ : syracuseStep 1317905 = 988429) B988429
theorem B1317923 : Blo 876568 1317923 := bstep (se 1 (by rfl) ⟨988442, by rfl⟩ : syracuseStep 1317923 = 1976885) B1976885
theorem B1317953 : Blo 876568 1317953 := bstep (se 2 (by rfl) ⟨494232, by rfl⟩ : syracuseStep 1317953 = 988465) B988465
theorem B1252417 : Blo 876568 1252417 := bstep (se 2 (by rfl) ⟨469656, by rfl⟩ : syracuseStep 1252417 = 939313) B939313
theorem B1317971 : Blo 876568 1317971 := bstep (se 1 (by rfl) ⟨988478, by rfl⟩ : syracuseStep 1317971 = 1976957) B1976957
theorem B6659171 : Blo 876568 6659171 := bstep (se 1 (by rfl) ⟨4994378, by rfl⟩ : syracuseStep 6659171 = 9988757) B9988757
theorem B1481827 : Blo 876568 1481827 := bstep (se 1 (by rfl) ⟨1111370, by rfl⟩ : syracuseStep 1481827 = 2222741) B2222741
theorem B2497645 : Blo 876568 2497645 := bstep (se 3 (by rfl) ⟨468308, by rfl⟩ : syracuseStep 2497645 = 936617) B936617
theorem B1318001 : Blo 876568 1318001 := bstep (se 2 (by rfl) ⟨494250, by rfl⟩ : syracuseStep 1318001 = 988501) B988501
theorem B1318019 : Blo 876568 1318019 := bstep (se 1 (by rfl) ⟨988514, by rfl⟩ : syracuseStep 1318019 = 1977029) B1977029
theorem B1973393 : Blo 876568 1973393 := bstep (se 2 (by rfl) ⟨740022, by rfl⟩ : syracuseStep 1973393 = 1480045) B1480045
theorem B1186963 : Blo 876568 1186963 := bstep (se 1 (by rfl) ⟨890222, by rfl⟩ : syracuseStep 1186963 = 1780445) B1780445
theorem B990355 : Blo 876568 990355 := bstep (se 1 (by rfl) ⟨742766, by rfl⟩ : syracuseStep 990355 = 1485533) B1485533
theorem B1318049 : Blo 876568 1318049 := bstep (se 2 (by rfl) ⟨494268, by rfl⟩ : syracuseStep 1318049 = 988537) B988537
theorem B1252513 : Blo 876568 1252513 := bstep (se 2 (by rfl) ⟨469692, by rfl⟩ : syracuseStep 1252513 = 939385) B939385
theorem B1973411 : Blo 876568 1973411 := bstep (se 1 (by rfl) ⟨1480058, by rfl⟩ : syracuseStep 1973411 = 2960117) B2960117
theorem B1318067 : Blo 876568 1318067 := bstep (se 1 (by rfl) ⟨988550, by rfl⟩ : syracuseStep 1318067 = 1977101) B1977101
theorem B1318097 : Blo 876568 1318097 := bstep (se 2 (by rfl) ⟨494286, by rfl⟩ : syracuseStep 1318097 = 988573) B988573
theorem B1318115 : Blo 876568 1318115 := bstep (se 1 (by rfl) ⟨988586, by rfl⟩ : syracuseStep 1318115 = 1977173) B1977173
theorem B1481969 : Blo 876568 1481969 := bstep (se 2 (by rfl) ⟨555738, by rfl⟩ : syracuseStep 1481969 = 1111477) B1111477
theorem B1318145 : Blo 876568 1318145 := bstep (se 2 (by rfl) ⟨494304, by rfl⟩ : syracuseStep 1318145 = 988609) B988609
theorem B1580305 : Blo 876568 1580305 := bstep (se 2 (by rfl) ⟨592614, by rfl⟩ : syracuseStep 1580305 = 1185229) B1185229
theorem B1318163 : Blo 876568 1318163 := bstep (se 1 (by rfl) ⟨988622, by rfl⟩ : syracuseStep 1318163 = 1977245) B1977245
theorem B990499 : Blo 876568 990499 := bstep (se 1 (by rfl) ⟨742874, by rfl⟩ : syracuseStep 990499 = 1485749) B1485749
theorem B1318193 : Blo 876568 1318193 := bstep (se 2 (by rfl) ⟨494322, by rfl⟩ : syracuseStep 1318193 = 988645) B988645
theorem B1318211 : Blo 876568 1318211 := bstep (se 1 (by rfl) ⟨988658, by rfl⟩ : syracuseStep 1318211 = 1977317) B1977317
theorem B2497873 : Blo 876568 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B1318241 : Blo 876568 1318241 := bstep (se 2 (by rfl) ⟨494340, by rfl⟩ : syracuseStep 1318241 = 988681) B988681
theorem B1482097 : Blo 876568 1482097 := bstep (se 2 (by rfl) ⟨555786, by rfl⟩ : syracuseStep 1482097 = 1111573) B1111573
theorem B1318259 : Blo 876568 1318259 := bstep (se 1 (by rfl) ⟨988694, by rfl⟩ : syracuseStep 1318259 = 1977389) B1977389
theorem B1318289 : Blo 876568 1318289 := bstep (se 2 (by rfl) ⟨494358, by rfl⟩ : syracuseStep 1318289 = 988717) B988717
theorem B1482131 : Blo 876568 1482131 := bstep (se 1 (by rfl) ⟨1111598, by rfl⟩ : syracuseStep 1482131 = 2223197) B2223197
theorem B1318307 : Blo 876568 1318307 := bstep (se 1 (by rfl) ⟨988730, by rfl⟩ : syracuseStep 1318307 = 1977461) B1977461
theorem B1973681 : Blo 876568 1973681 := bstep (se 2 (by rfl) ⟨740130, by rfl⟩ : syracuseStep 1973681 = 1480261) B1480261
theorem B1318337 : Blo 876568 1318337 := bstep (se 2 (by rfl) ⟨494376, by rfl⟩ : syracuseStep 1318337 = 988753) B988753
theorem B1973699 : Blo 876568 1973699 := bstep (se 1 (by rfl) ⟨1480274, by rfl⟩ : syracuseStep 1973699 = 2960549) B2960549
theorem B1318355 : Blo 876568 1318355 := bstep (se 1 (by rfl) ⟨988766, by rfl⟩ : syracuseStep 1318355 = 1977533) B1977533
theorem B2530801 : Blo 876568 2530801 := bstep (se 2 (by rfl) ⟨949050, by rfl⟩ : syracuseStep 2530801 = 1898101) B1898101
theorem B2498033 : Blo 876568 2498033 := bstep (se 2 (by rfl) ⟨936762, by rfl⟩ : syracuseStep 2498033 = 1873525) B1873525
theorem B1318385 : Blo 876568 1318385 := bstep (se 2 (by rfl) ⟨494394, by rfl⟩ : syracuseStep 1318385 = 988789) B988789
theorem B1318403 : Blo 876568 1318403 := bstep (se 1 (by rfl) ⟨988802, by rfl⟩ : syracuseStep 1318403 = 1977605) B1977605
theorem B1482259 : Blo 876568 1482259 := bstep (se 1 (by rfl) ⟨1111694, by rfl⟩ : syracuseStep 1482259 = 2223389) B2223389
theorem B1318433 : Blo 876568 1318433 := bstep (se 2 (by rfl) ⟨494412, by rfl⟩ : syracuseStep 1318433 = 988825) B988825
theorem B1318451 : Blo 876568 1318451 := bstep (se 1 (by rfl) ⟨988838, by rfl⟩ : syracuseStep 1318451 = 1977677) B1977677
theorem B7118405 : Blo 876568 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B1318481 : Blo 876568 1318481 := bstep (se 2 (by rfl) ⟨494430, by rfl⟩ : syracuseStep 1318481 = 988861) B988861
theorem B2498147 : Blo 876568 2498147 := bstep (se 1 (by rfl) ⟨1873610, by rfl⟩ : syracuseStep 2498147 = 3747221) B3747221
theorem B1318499 : Blo 876568 1318499 := bstep (se 1 (by rfl) ⟨988874, by rfl⟩ : syracuseStep 1318499 = 1977749) B1977749
theorem B1318529 : Blo 876568 1318529 := bstep (se 2 (by rfl) ⟨494448, by rfl⟩ : syracuseStep 1318529 = 988897) B988897
theorem B1253009 : Blo 876568 1253009 := bstep (se 2 (by rfl) ⟨469878, by rfl⟩ : syracuseStep 1253009 = 939757) B939757
theorem B1318547 : Blo 876568 1318547 := bstep (se 1 (by rfl) ⟨988910, by rfl⟩ : syracuseStep 1318547 = 1977821) B1977821
theorem B1482401 : Blo 876568 1482401 := bstep (se 2 (by rfl) ⟨555900, by rfl⟩ : syracuseStep 1482401 = 1111801) B1111801
theorem B1318577 : Blo 876568 1318577 := bstep (se 2 (by rfl) ⟨494466, by rfl⟩ : syracuseStep 1318577 = 988933) B988933
theorem B1318595 : Blo 876568 1318595 := bstep (se 1 (by rfl) ⟨988946, by rfl⟩ : syracuseStep 1318595 = 1977893) B1977893
theorem B1973969 : Blo 876568 1973969 := bstep (se 2 (by rfl) ⟨740238, by rfl⟩ : syracuseStep 1973969 = 1480477) B1480477
theorem B1973987 : Blo 876568 1973987 := bstep (se 1 (by rfl) ⟨1480490, by rfl⟩ : syracuseStep 1973987 = 2960981) B2960981
theorem B1318625 : Blo 876568 1318625 := bstep (se 2 (by rfl) ⟨494484, by rfl⟩ : syracuseStep 1318625 = 988969) B988969
theorem B1318643 : Blo 876568 1318643 := bstep (se 1 (by rfl) ⟨988982, by rfl⟩ : syracuseStep 1318643 = 1977965) B1977965
theorem B1318673 : Blo 876568 1318673 := bstep (se 2 (by rfl) ⟨494502, by rfl⟩ : syracuseStep 1318673 = 989005) B989005
theorem B1482529 : Blo 876568 1482529 := bstep (se 2 (by rfl) ⟨555948, by rfl⟩ : syracuseStep 1482529 = 1111897) B1111897
theorem B1318691 : Blo 876568 1318691 := bstep (se 1 (by rfl) ⟨989018, by rfl⟩ : syracuseStep 1318691 = 1978037) B1978037
theorem B1318721 : Blo 876568 1318721 := bstep (se 2 (by rfl) ⟨494520, by rfl⟩ : syracuseStep 1318721 = 989041) B989041
theorem B1482563 : Blo 876568 1482563 := bstep (se 1 (by rfl) ⟨1111922, by rfl⟩ : syracuseStep 1482563 = 2223845) B2223845
theorem B1318739 : Blo 876568 1318739 := bstep (se 1 (by rfl) ⟨989054, by rfl⟩ : syracuseStep 1318739 = 1978109) B1978109
theorem B1318769 : Blo 876568 1318769 := bstep (se 2 (by rfl) ⟨494538, by rfl⟩ : syracuseStep 1318769 = 989077) B989077
theorem B1318787 : Blo 876568 1318787 := bstep (se 1 (by rfl) ⟨989090, by rfl⟩ : syracuseStep 1318787 = 1978181) B1978181
theorem B1318817 : Blo 876568 1318817 := bstep (se 2 (by rfl) ⟨494556, by rfl⟩ : syracuseStep 1318817 = 989113) B989113
theorem B1318835 : Blo 876568 1318835 := bstep (se 1 (by rfl) ⟨989126, by rfl⟩ : syracuseStep 1318835 = 1978253) B1978253
theorem B1286081 : Blo 876568 1286081 := bstep (se 2 (by rfl) ⟨482280, by rfl⟩ : syracuseStep 1286081 = 964561) B964561
theorem B1482691 : Blo 876568 1482691 := bstep (se 1 (by rfl) ⟨1112018, by rfl⟩ : syracuseStep 1482691 = 2224037) B2224037
theorem B1318865 : Blo 876568 1318865 := bstep (se 2 (by rfl) ⟨494574, by rfl⟩ : syracuseStep 1318865 = 989149) B989149
theorem B1318883 : Blo 876568 1318883 := bstep (se 1 (by rfl) ⟨989162, by rfl⟩ : syracuseStep 1318883 = 1978325) B1978325
theorem B1974257 : Blo 876568 1974257 := bstep (se 2 (by rfl) ⟨740346, by rfl⟩ : syracuseStep 1974257 = 1480693) B1480693
theorem B1318913 : Blo 876568 1318913 := bstep (se 2 (by rfl) ⟨494592, by rfl⟩ : syracuseStep 1318913 = 989185) B989185
theorem B1974275 : Blo 876568 1974275 := bstep (se 1 (by rfl) ⟨1480706, by rfl⟩ : syracuseStep 1974275 = 2961413) B2961413
theorem B1318931 : Blo 876568 1318931 := bstep (se 1 (by rfl) ⟨989198, by rfl⟩ : syracuseStep 1318931 = 1978397) B1978397
theorem B1318961 : Blo 876568 1318961 := bstep (se 2 (by rfl) ⟨494610, by rfl⟩ : syracuseStep 1318961 = 989221) B989221
theorem B2007089 : Blo 876568 2007089 := bstep (se 2 (by rfl) ⟨752658, by rfl⟩ : syracuseStep 2007089 = 1505317) B1505317
theorem B1318979 : Blo 876568 1318979 := bstep (se 1 (by rfl) ⟨989234, by rfl⟩ : syracuseStep 1318979 = 1978469) B1978469
theorem B1482833 : Blo 876568 1482833 := bstep (se 2 (by rfl) ⟨556062, by rfl⟩ : syracuseStep 1482833 = 1112125) B1112125
theorem B1319009 : Blo 876568 1319009 := bstep (se 2 (by rfl) ⟨494628, by rfl⟩ : syracuseStep 1319009 = 989257) B989257
theorem B1319027 : Blo 876568 1319027 := bstep (se 1 (by rfl) ⟨989270, by rfl⟩ : syracuseStep 1319027 = 1978541) B1978541
theorem B1319057 : Blo 876568 1319057 := bstep (se 2 (by rfl) ⟨494646, by rfl⟩ : syracuseStep 1319057 = 989293) B989293
theorem B1319075 : Blo 876568 1319075 := bstep (se 1 (by rfl) ⟨989306, by rfl⟩ : syracuseStep 1319075 = 1978613) B1978613
theorem B1319105 : Blo 876568 1319105 := bstep (se 2 (by rfl) ⟨494664, by rfl⟩ : syracuseStep 1319105 = 989329) B989329
theorem B2171075 : Blo 876568 2171075 := bstep (se 1 (by rfl) ⟨1628306, by rfl⟩ : syracuseStep 2171075 = 3256613) B3256613
theorem B1482961 : Blo 876568 1482961 := bstep (se 2 (by rfl) ⟨556110, by rfl⟩ : syracuseStep 1482961 = 1112221) B1112221
theorem B1319123 : Blo 876568 1319123 := bstep (se 1 (by rfl) ⟨989342, by rfl⟩ : syracuseStep 1319123 = 1978685) B1978685
theorem B1319153 : Blo 876568 1319153 := bstep (se 2 (by rfl) ⟨494682, by rfl⟩ : syracuseStep 1319153 = 989365) B989365
theorem B1482995 : Blo 876568 1482995 := bstep (se 1 (by rfl) ⟨1112246, by rfl⟩ : syracuseStep 1482995 = 2224493) B2224493
theorem B1319171 : Blo 876568 1319171 := bstep (se 1 (by rfl) ⟨989378, by rfl⟩ : syracuseStep 1319171 = 1978757) B1978757
theorem B1974545 : Blo 876568 1974545 := bstep (se 2 (by rfl) ⟨740454, by rfl⟩ : syracuseStep 1974545 = 1480909) B1480909
theorem B1876241 : Blo 876568 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B1319201 : Blo 876568 1319201 := bstep (se 2 (by rfl) ⟨494700, by rfl⟩ : syracuseStep 1319201 = 989401) B989401
theorem B1974563 : Blo 876568 1974563 := bstep (se 1 (by rfl) ⟨1480922, by rfl⟩ : syracuseStep 1974563 = 2961845) B2961845
theorem B1876259 : Blo 876568 1876259 := bstep (se 1 (by rfl) ⟨1407194, by rfl⟩ : syracuseStep 1876259 = 2814389) B2814389
theorem B1319219 : Blo 876568 1319219 := bstep (se 1 (by rfl) ⟨989414, by rfl⟩ : syracuseStep 1319219 = 1978829) B1978829
theorem B1319249 : Blo 876568 1319249 := bstep (se 2 (by rfl) ⟨494718, by rfl⟩ : syracuseStep 1319249 = 989437) B989437
theorem B1319267 : Blo 876568 1319267 := bstep (se 1 (by rfl) ⟨989450, by rfl⟩ : syracuseStep 1319267 = 1978901) B1978901
theorem B16032113 : Blo 876568 16032113 := bstep (se 2 (by rfl) ⟨6012042, by rfl⟩ : syracuseStep 16032113 = 12024085) B12024085
theorem B1483123 : Blo 876568 1483123 := bstep (se 1 (by rfl) ⟨1112342, by rfl⟩ : syracuseStep 1483123 = 2224685) B2224685
theorem B1319297 : Blo 876568 1319297 := bstep (se 2 (by rfl) ⟨494736, by rfl⟩ : syracuseStep 1319297 = 989473) B989473
theorem B1319315 : Blo 876568 1319315 := bstep (se 1 (by rfl) ⟨989486, by rfl⟩ : syracuseStep 1319315 = 1978973) B1978973
theorem B1319345 : Blo 876568 1319345 := bstep (se 2 (by rfl) ⟨494754, by rfl⟩ : syracuseStep 1319345 = 989509) B989509
theorem B1319363 : Blo 876568 1319363 := bstep (se 1 (by rfl) ⟨989522, by rfl⟩ : syracuseStep 1319363 = 1979045) B1979045
theorem B1319393 : Blo 876568 1319393 := bstep (se 2 (by rfl) ⟨494772, by rfl⟩ : syracuseStep 1319393 = 989545) B989545
theorem B1319411 : Blo 876568 1319411 := bstep (se 1 (by rfl) ⟨989558, by rfl⟩ : syracuseStep 1319411 = 1979117) B1979117
theorem B1483265 : Blo 876568 1483265 := bstep (se 2 (by rfl) ⟨556224, by rfl⟩ : syracuseStep 1483265 = 1112449) B1112449
theorem B1319441 : Blo 876568 1319441 := bstep (se 2 (by rfl) ⟨494790, by rfl⟩ : syracuseStep 1319441 = 989581) B989581
theorem B1319459 : Blo 876568 1319459 := bstep (se 1 (by rfl) ⟨989594, by rfl⟩ : syracuseStep 1319459 = 1979189) B1979189
theorem B1974833 : Blo 876568 1974833 := bstep (se 2 (by rfl) ⟨740562, by rfl⟩ : syracuseStep 1974833 = 1481125) B1481125
theorem B1319489 : Blo 876568 1319489 := bstep (se 2 (by rfl) ⟨494808, by rfl⟩ : syracuseStep 1319489 = 989617) B989617
theorem B1974851 : Blo 876568 1974851 := bstep (se 1 (by rfl) ⟨1481138, by rfl⟩ : syracuseStep 1974851 = 2962277) B2962277
theorem B2499149 : Blo 876568 2499149 := bstep (se 3 (by rfl) ⟨468590, by rfl⟩ : syracuseStep 2499149 = 937181) B937181
theorem B1319507 : Blo 876568 1319507 := bstep (se 1 (by rfl) ⟨989630, by rfl⟩ : syracuseStep 1319507 = 1979261) B1979261
theorem B1319537 : Blo 876568 1319537 := bstep (se 2 (by rfl) ⟨494826, by rfl⟩ : syracuseStep 1319537 = 989653) B989653
theorem B1483393 : Blo 876568 1483393 := bstep (se 2 (by rfl) ⟨556272, by rfl⟩ : syracuseStep 1483393 = 1112545) B1112545
theorem B1319555 : Blo 876568 1319555 := bstep (se 1 (by rfl) ⟨989666, by rfl⟩ : syracuseStep 1319555 = 1979333) B1979333
theorem B1319585 : Blo 876568 1319585 := bstep (se 2 (by rfl) ⟨494844, by rfl⟩ : syracuseStep 1319585 = 989689) B989689
theorem B1483427 : Blo 876568 1483427 := bstep (se 1 (by rfl) ⟨1112570, by rfl⟩ : syracuseStep 1483427 = 2225141) B2225141
theorem B1188515 : Blo 876568 1188515 := bstep (se 1 (by rfl) ⟨891386, by rfl⟩ : syracuseStep 1188515 = 1782773) B1782773
theorem B1319603 : Blo 876568 1319603 := bstep (se 1 (by rfl) ⟨989702, by rfl⟩ : syracuseStep 1319603 = 1979405) B1979405
theorem B1319633 : Blo 876568 1319633 := bstep (se 2 (by rfl) ⟨494862, by rfl⟩ : syracuseStep 1319633 = 989725) B989725
theorem B1319651 : Blo 876568 1319651 := bstep (se 1 (by rfl) ⟨989738, by rfl⟩ : syracuseStep 1319651 = 1979477) B1979477
theorem B1319681 : Blo 876568 1319681 := bstep (se 2 (by rfl) ⟨494880, by rfl⟩ : syracuseStep 1319681 = 989761) B989761
theorem B2499331 : Blo 876568 2499331 := bstep (se 1 (by rfl) ⟨1874498, by rfl⟩ : syracuseStep 2499331 = 3748997) B3748997
theorem B1319699 : Blo 876568 1319699 := bstep (se 1 (by rfl) ⟨989774, by rfl⟩ : syracuseStep 1319699 = 1979549) B1979549
theorem B1483555 : Blo 876568 1483555 := bstep (se 1 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 1483555 = 2225333) B2225333
theorem B1319729 : Blo 876568 1319729 := bstep (se 2 (by rfl) ⟨494898, by rfl⟩ : syracuseStep 1319729 = 989797) B989797
theorem B1319747 : Blo 876568 1319747 := bstep (se 1 (by rfl) ⟨989810, by rfl⟩ : syracuseStep 1319747 = 1979621) B1979621
theorem B3744589 : Blo 876568 3744589 := bstep (se 3 (by rfl) ⟨702110, by rfl⟩ : syracuseStep 3744589 = 1404221) B1404221
theorem B1975121 : Blo 876568 1975121 := bstep (se 2 (by rfl) ⟨740670, by rfl⟩ : syracuseStep 1975121 = 1481341) B1481341
theorem B1319777 : Blo 876568 1319777 := bstep (se 2 (by rfl) ⟨494916, by rfl⟩ : syracuseStep 1319777 = 989833) B989833
theorem B1778531 : Blo 876568 1778531 := bstep (se 1 (by rfl) ⟨1333898, by rfl⟩ : syracuseStep 1778531 = 2667797) B2667797
theorem B1975139 : Blo 876568 1975139 := bstep (se 1 (by rfl) ⟨1481354, by rfl⟩ : syracuseStep 1975139 = 2962709) B2962709
theorem B1319795 : Blo 876568 1319795 := bstep (se 1 (by rfl) ⟨989846, by rfl⟩ : syracuseStep 1319795 = 1979693) B1979693
theorem B1778563 : Blo 876568 1778563 := bstep (se 1 (by rfl) ⟨1333922, by rfl⟩ : syracuseStep 1778563 = 2667845) B2667845
theorem B1319825 : Blo 876568 1319825 := bstep (se 2 (by rfl) ⟨494934, by rfl⟩ : syracuseStep 1319825 = 989869) B989869
theorem B2499491 : Blo 876568 2499491 := bstep (se 1 (by rfl) ⟨1874618, by rfl⟩ : syracuseStep 2499491 = 3749237) B3749237
theorem B1319843 : Blo 876568 1319843 := bstep (se 1 (by rfl) ⟨989882, by rfl⟩ : syracuseStep 1319843 = 1979765) B1979765
theorem B1483697 : Blo 876568 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B1319873 : Blo 876568 1319873 := bstep (se 2 (by rfl) ⟨494952, by rfl⟩ : syracuseStep 1319873 = 989905) B989905
theorem B1319891 : Blo 876568 1319891 := bstep (se 1 (by rfl) ⟨989918, by rfl⟩ : syracuseStep 1319891 = 1979837) B1979837
theorem B1319921 : Blo 876568 1319921 := bstep (se 2 (by rfl) ⟨494970, by rfl⟩ : syracuseStep 1319921 = 989941) B989941
theorem B1319939 : Blo 876568 1319939 := bstep (se 1 (by rfl) ⟨989954, by rfl⟩ : syracuseStep 1319939 = 1979909) B1979909
theorem B1319969 : Blo 876568 1319969 := bstep (se 2 (by rfl) ⟨494988, by rfl⟩ : syracuseStep 1319969 = 989977) B989977
theorem B1483825 : Blo 876568 1483825 := bstep (se 2 (by rfl) ⟨556434, by rfl⟩ : syracuseStep 1483825 = 1112869) B1112869
theorem B1319987 : Blo 876568 1319987 := bstep (se 1 (by rfl) ⟨989990, by rfl⟩ : syracuseStep 1319987 = 1979981) B1979981
theorem B1320017 : Blo 876568 1320017 := bstep (se 2 (by rfl) ⟨495006, by rfl⟩ : syracuseStep 1320017 = 990013) B990013
theorem B1483859 : Blo 876568 1483859 := bstep (se 1 (by rfl) ⟨1112894, by rfl⟩ : syracuseStep 1483859 = 2225789) B2225789
theorem B1320035 : Blo 876568 1320035 := bstep (se 1 (by rfl) ⟨990026, by rfl⟩ : syracuseStep 1320035 = 1980053) B1980053
theorem B1975409 : Blo 876568 1975409 := bstep (se 2 (by rfl) ⟨740778, by rfl⟩ : syracuseStep 1975409 = 1481557) B1481557
theorem B1320065 : Blo 876568 1320065 := bstep (se 2 (by rfl) ⟨495024, by rfl⟩ : syracuseStep 1320065 = 990049) B990049
theorem B1975427 : Blo 876568 1975427 := bstep (se 1 (by rfl) ⟨1481570, by rfl⟩ : syracuseStep 1975427 = 2963141) B2963141
theorem B1320083 : Blo 876568 1320083 := bstep (se 1 (by rfl) ⟨990062, by rfl⟩ : syracuseStep 1320083 = 1980125) B1980125
theorem B1320113 : Blo 876568 1320113 := bstep (se 2 (by rfl) ⟨495042, by rfl⟩ : syracuseStep 1320113 = 990085) B990085
theorem B1320131 : Blo 876568 1320131 := bstep (se 1 (by rfl) ⟨990098, by rfl⟩ : syracuseStep 1320131 = 1980197) B1980197
theorem B1483987 : Blo 876568 1483987 := bstep (se 1 (by rfl) ⟨1112990, by rfl⟩ : syracuseStep 1483987 = 2225981) B2225981
theorem B1320161 : Blo 876568 1320161 := bstep (se 2 (by rfl) ⟨495060, by rfl⟩ : syracuseStep 1320161 = 990121) B990121
theorem B1320179 : Blo 876568 1320179 := bstep (se 1 (by rfl) ⟨990134, by rfl⟩ : syracuseStep 1320179 = 1980269) B1980269
theorem B2958605 : Blo 876568 2958605 := bstep (se 3 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 2958605 = 1109477) B1109477
theorem B1320209 : Blo 876568 1320209 := bstep (se 2 (by rfl) ⟨495078, by rfl⟩ : syracuseStep 1320209 = 990157) B990157
theorem B1320227 : Blo 876568 1320227 := bstep (se 1 (by rfl) ⟨990170, by rfl⟩ : syracuseStep 1320227 = 1980341) B1980341
theorem B1320257 : Blo 876568 1320257 := bstep (se 2 (by rfl) ⟨495096, by rfl⟩ : syracuseStep 1320257 = 990193) B990193
theorem B2958659 : Blo 876568 2958659 := bstep (se 1 (by rfl) ⟨2218994, by rfl⟩ : syracuseStep 2958659 = 4437989) B4437989
theorem B1320275 : Blo 876568 1320275 := bstep (se 1 (by rfl) ⟨990206, by rfl⟩ : syracuseStep 1320275 = 1980413) B1980413
theorem B1484129 : Blo 876568 1484129 := bstep (se 2 (by rfl) ⟨556548, by rfl⟩ : syracuseStep 1484129 = 1113097) B1113097
theorem B1320305 : Blo 876568 1320305 := bstep (se 2 (by rfl) ⟨495114, by rfl⟩ : syracuseStep 1320305 = 990229) B990229
theorem B1320323 : Blo 876568 1320323 := bstep (se 1 (by rfl) ⟨990242, by rfl⟩ : syracuseStep 1320323 = 1980485) B1980485
theorem B1975697 : Blo 876568 1975697 := bstep (se 2 (by rfl) ⟨740886, by rfl⟩ : syracuseStep 1975697 = 1481773) B1481773
theorem B1320353 : Blo 876568 1320353 := bstep (se 2 (by rfl) ⟨495132, by rfl⟩ : syracuseStep 1320353 = 990265) B990265
theorem B1975715 : Blo 876568 1975715 := bstep (se 1 (by rfl) ⟨1481786, by rfl⟩ : syracuseStep 1975715 = 2963573) B2963573
theorem B1320371 : Blo 876568 1320371 := bstep (se 1 (by rfl) ⟨990278, by rfl⟩ : syracuseStep 1320371 = 1980557) B1980557
theorem B1320401 : Blo 876568 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B1484257 : Blo 876568 1484257 := bstep (se 2 (by rfl) ⟨556596, by rfl⟩ : syracuseStep 1484257 = 1113193) B1113193
theorem B1320419 : Blo 876568 1320419 := bstep (se 1 (by rfl) ⟨990314, by rfl⟩ : syracuseStep 1320419 = 1980629) B1980629
theorem B1877489 : Blo 876568 1877489 := bstep (se 2 (by rfl) ⟨704058, by rfl⟩ : syracuseStep 1877489 = 1408117) B1408117
theorem B1320449 : Blo 876568 1320449 := bstep (se 2 (by rfl) ⟨495168, by rfl⟩ : syracuseStep 1320449 = 990337) B990337
theorem B1484291 : Blo 876568 1484291 := bstep (se 1 (by rfl) ⟨1113218, by rfl⟩ : syracuseStep 1484291 = 2226437) B2226437
theorem B1320467 : Blo 876568 1320467 := bstep (se 1 (by rfl) ⟨990350, by rfl⟩ : syracuseStep 1320467 = 1980701) B1980701
theorem B1320497 : Blo 876568 1320497 := bstep (se 2 (by rfl) ⟨495186, by rfl⟩ : syracuseStep 1320497 = 990373) B990373
theorem B2106947 : Blo 876568 2106947 := bstep (se 1 (by rfl) ⟨1580210, by rfl⟩ : syracuseStep 2106947 = 3160421) B3160421
theorem B1320515 : Blo 876568 1320515 := bstep (se 1 (by rfl) ⟨990386, by rfl⟩ : syracuseStep 1320515 = 1980773) B1980773
theorem B2958929 : Blo 876568 2958929 := bstep (se 2 (by rfl) ⟨1109598, by rfl⟩ : syracuseStep 2958929 = 2219197) B2219197
theorem B1320545 : Blo 876568 1320545 := bstep (se 2 (by rfl) ⟨495204, by rfl⟩ : syracuseStep 1320545 = 990409) B990409
theorem B1320563 : Blo 876568 1320563 := bstep (se 1 (by rfl) ⟨990422, by rfl⟩ : syracuseStep 1320563 = 1980845) B1980845
theorem B1484419 : Blo 876568 1484419 := bstep (se 1 (by rfl) ⟨1113314, by rfl⟩ : syracuseStep 1484419 = 2226629) B2226629
theorem B1320593 : Blo 876568 1320593 := bstep (se 2 (by rfl) ⟨495222, by rfl⟩ : syracuseStep 1320593 = 990445) B990445
theorem B1320611 : Blo 876568 1320611 := bstep (se 1 (by rfl) ⟨990458, by rfl⟩ : syracuseStep 1320611 = 1980917) B1980917
theorem B1975985 : Blo 876568 1975985 := bstep (se 2 (by rfl) ⟨740994, by rfl⟩ : syracuseStep 1975985 = 1481989) B1481989
theorem B1320641 : Blo 876568 1320641 := bstep (se 2 (by rfl) ⟨495240, by rfl⟩ : syracuseStep 1320641 = 990481) B990481
theorem B1976003 : Blo 876568 1976003 := bstep (se 1 (by rfl) ⟨1482002, by rfl⟩ : syracuseStep 1976003 = 2964005) B2964005
theorem B1320659 : Blo 876568 1320659 := bstep (se 1 (by rfl) ⟨990494, by rfl⟩ : syracuseStep 1320659 = 1980989) B1980989
theorem B1320689 : Blo 876568 1320689 := bstep (se 2 (by rfl) ⟨495258, by rfl⟩ : syracuseStep 1320689 = 990517) B990517
theorem B1320707 : Blo 876568 1320707 := bstep (se 1 (by rfl) ⟨990530, by rfl⟩ : syracuseStep 1320707 = 1981061) B1981061
theorem B1484561 : Blo 876568 1484561 := bstep (se 2 (by rfl) ⟨556710, by rfl⟩ : syracuseStep 1484561 = 1113421) B1113421
theorem B1320737 : Blo 876568 1320737 := bstep (se 2 (by rfl) ⟨495276, by rfl⟩ : syracuseStep 1320737 = 990553) B990553
theorem B1189667 : Blo 876568 1189667 := bstep (se 1 (by rfl) ⟨892250, by rfl⟩ : syracuseStep 1189667 = 1784501) B1784501
theorem B1320755 : Blo 876568 1320755 := bstep (se 1 (by rfl) ⟨990566, by rfl⟩ : syracuseStep 1320755 = 1981133) B1981133
theorem B1320785 : Blo 876568 1320785 := bstep (se 2 (by rfl) ⟨495294, by rfl⟩ : syracuseStep 1320785 = 990589) B990589
theorem B2107235 : Blo 876568 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B1320803 : Blo 876568 1320803 := bstep (se 1 (by rfl) ⟨990602, by rfl⟩ : syracuseStep 1320803 = 1981205) B1981205
theorem B1320833 : Blo 876568 1320833 := bstep (se 2 (by rfl) ⟨495312, by rfl⟩ : syracuseStep 1320833 = 990625) B990625
theorem B6104965 : Blo 876568 6104965 := bstep (se 4 (by rfl) ⟨572340, by rfl⟩ : syracuseStep 6104965 = 1144681) B1144681
theorem B1582993 : Blo 876568 1582993 := bstep (se 2 (by rfl) ⟨593622, by rfl⟩ : syracuseStep 1582993 = 1187245) B1187245
theorem B1484689 : Blo 876568 1484689 := bstep (se 2 (by rfl) ⟨556758, by rfl⟩ : syracuseStep 1484689 = 1113517) B1113517
theorem B1320851 : Blo 876568 1320851 := bstep (se 1 (by rfl) ⟨990638, by rfl⟩ : syracuseStep 1320851 = 1981277) B1981277
theorem B1484723 : Blo 876568 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B2500561 : Blo 876568 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B1976273 : Blo 876568 1976273 := bstep (se 2 (by rfl) ⟨741102, by rfl⟩ : syracuseStep 1976273 = 1482205) B1482205
theorem B1976291 : Blo 876568 1976291 := bstep (se 1 (by rfl) ⟨1482218, by rfl⟩ : syracuseStep 1976291 = 2964437) B2964437
theorem B1484851 : Blo 876568 1484851 := bstep (se 1 (by rfl) ⟨1113638, by rfl⟩ : syracuseStep 1484851 = 2227277) B2227277
theorem B2959469 : Blo 876568 2959469 := bstep (se 3 (by rfl) ⟨554900, by rfl⟩ : syracuseStep 2959469 = 1109801) B1109801
theorem B2959523 : Blo 876568 2959523 := bstep (se 1 (by rfl) ⟨2219642, by rfl⟩ : syracuseStep 2959523 = 4439285) B4439285
theorem B1484993 : Blo 876568 1484993 := bstep (se 2 (by rfl) ⟨556872, by rfl⟩ : syracuseStep 1484993 = 1113745) B1113745
theorem B1714403 : Blo 876568 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B1976561 : Blo 876568 1976561 := bstep (se 2 (by rfl) ⟨741210, by rfl⟩ : syracuseStep 1976561 = 1482421) B1482421
theorem B1976579 : Blo 876568 1976579 := bstep (se 1 (by rfl) ⟨1482434, by rfl⟩ : syracuseStep 1976579 = 2964869) B2964869
theorem B1485121 : Blo 876568 1485121 := bstep (se 2 (by rfl) ⟨556920, by rfl⟩ : syracuseStep 1485121 = 1113841) B1113841
theorem B1485155 : Blo 876568 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B2959793 : Blo 876568 2959793 := bstep (se 2 (by rfl) ⟨1109922, by rfl⟩ : syracuseStep 2959793 = 2219845) B2219845
theorem B1583555 : Blo 876568 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B1485283 : Blo 876568 1485283 := bstep (se 1 (by rfl) ⟨1113962, by rfl⟩ : syracuseStep 1485283 = 2227925) B2227925
theorem B8006129 : Blo 876568 8006129 := bstep (se 2 (by rfl) ⟨3002298, by rfl⟩ : syracuseStep 8006129 = 6004597) B6004597
theorem B1976849 : Blo 876568 1976849 := bstep (se 2 (by rfl) ⟨741318, by rfl⟩ : syracuseStep 1976849 = 1482637) B1482637
theorem B1976867 : Blo 876568 1976867 := bstep (se 1 (by rfl) ⟨1482650, by rfl⟩ : syracuseStep 1976867 = 2965301) B2965301
theorem B1485425 : Blo 876568 1485425 := bstep (se 2 (by rfl) ⟨557034, by rfl⟩ : syracuseStep 1485425 = 1114069) B1114069
theorem B2534033 : Blo 876568 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B2108081 : Blo 876568 2108081 := bstep (se 2 (by rfl) ⟨790530, by rfl⟩ : syracuseStep 2108081 = 1581061) B1581061
theorem B1485553 : Blo 876568 1485553 := bstep (se 2 (by rfl) ⟨557082, by rfl⟩ : syracuseStep 1485553 = 1114165) B1114165
theorem B1485587 : Blo 876568 1485587 := bstep (se 1 (by rfl) ⟨1114190, by rfl⟩ : syracuseStep 1485587 = 2228381) B2228381
theorem B1977137 : Blo 876568 1977137 := bstep (se 2 (by rfl) ⟨741426, by rfl⟩ : syracuseStep 1977137 = 1482853) B1482853
theorem B1977155 : Blo 876568 1977155 := bstep (se 1 (by rfl) ⟨1482866, by rfl⟩ : syracuseStep 1977155 = 2965733) B2965733
theorem B1485715 : Blo 876568 1485715 := bstep (se 1 (by rfl) ⟨1114286, by rfl⟩ : syracuseStep 1485715 = 2228573) B2228573
theorem B2370467 : Blo 876568 2370467 := bstep (se 1 (by rfl) ⟨1777850, by rfl⟩ : syracuseStep 2370467 = 3555701) B3555701
theorem B2960333 : Blo 876568 2960333 := bstep (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) B1110125
theorem B2960387 : Blo 876568 2960387 := bstep (se 1 (by rfl) ⟨2220290, by rfl⟩ : syracuseStep 2960387 = 4440581) B4440581
theorem B1879043 : Blo 876568 1879043 := bstep (se 1 (by rfl) ⟨1409282, by rfl⟩ : syracuseStep 1879043 = 2818565) B2818565
theorem B1485857 : Blo 876568 1485857 := bstep (se 2 (by rfl) ⟨557196, by rfl⟩ : syracuseStep 1485857 = 1114393) B1114393
theorem B1977425 : Blo 876568 1977425 := bstep (se 2 (by rfl) ⟨741534, by rfl⟩ : syracuseStep 1977425 = 1483069) B1483069
theorem B1977443 : Blo 876568 1977443 := bstep (se 1 (by rfl) ⟨1483082, by rfl⟩ : syracuseStep 1977443 = 2966165) B2966165
theorem B2501837 : Blo 876568 2501837 := bstep (se 3 (by rfl) ⟨469094, by rfl⟩ : syracuseStep 2501837 = 938189) B938189
theorem B2960657 : Blo 876568 2960657 := bstep (se 2 (by rfl) ⟨1110246, by rfl⟩ : syracuseStep 2960657 = 2220493) B2220493
theorem B1977713 : Blo 876568 1977713 := bstep (se 2 (by rfl) ⟨741642, by rfl⟩ : syracuseStep 1977713 = 1483285) B1483285
theorem B2502019 : Blo 876568 2502019 := bstep (se 1 (by rfl) ⟨1876514, by rfl⟩ : syracuseStep 2502019 = 3753029) B3753029
theorem B1977731 : Blo 876568 1977731 := bstep (se 1 (by rfl) ⟨1483298, by rfl⟩ : syracuseStep 1977731 = 2966597) B2966597
theorem B2108849 : Blo 876568 2108849 := bstep (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) B1581637
theorem B2502065 : Blo 876568 2502065 := bstep (se 2 (by rfl) ⟨938274, by rfl⟩ : syracuseStep 2502065 = 1876549) B1876549
theorem B2665997 : Blo 876568 2665997 := bstep (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) B999749
theorem B1978001 : Blo 876568 1978001 := bstep (se 2 (by rfl) ⟨741750, by rfl⟩ : syracuseStep 1978001 = 1483501) B1483501
theorem B1978019 : Blo 876568 1978019 := bstep (se 1 (by rfl) ⟨1483514, by rfl⟩ : syracuseStep 1978019 = 2967029) B2967029
theorem B2961197 : Blo 876568 2961197 := bstep (se 3 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 2961197 = 1110449) B1110449
theorem B2961251 : Blo 876568 2961251 := bstep (se 1 (by rfl) ⟨2220938, by rfl⟩ : syracuseStep 2961251 = 4441877) B4441877
theorem B1978289 : Blo 876568 1978289 := bstep (se 2 (by rfl) ⟨741858, by rfl⟩ : syracuseStep 1978289 = 1483717) B1483717
theorem B1978307 : Blo 876568 1978307 := bstep (se 1 (by rfl) ⟨1483730, by rfl⟩ : syracuseStep 1978307 = 2967461) B2967461
theorem B22491107 : Blo 876568 22491107 := bstep (se 1 (by rfl) ⟨16868330, by rfl⟩ : syracuseStep 22491107 = 33736661) B33736661
theorem B2961521 : Blo 876568 2961521 := bstep (se 2 (by rfl) ⟨1110570, by rfl⟩ : syracuseStep 2961521 = 2221141) B2221141
theorem B1978577 : Blo 876568 1978577 := bstep (se 2 (by rfl) ⟨741966, by rfl⟩ : syracuseStep 1978577 = 1483933) B1483933
theorem B1978595 : Blo 876568 1978595 := bstep (se 1 (by rfl) ⟨1483946, by rfl⟩ : syracuseStep 1978595 = 2967893) B2967893
theorem B1585379 : Blo 876568 1585379 := bstep (se 1 (by rfl) ⟨1189034, by rfl⟩ : syracuseStep 1585379 = 2378069) B2378069
theorem B4993285 : Blo 876568 4993285 := bstep (se 4 (by rfl) ⟨468120, by rfl⟩ : syracuseStep 4993285 = 936241) B936241
theorem B6664517 : Blo 876568 6664517 := bstep (se 4 (by rfl) ⟨624798, by rfl⟩ : syracuseStep 6664517 = 1249597) B1249597
theorem B12038581 : Blo 876568 12038581 := bstep (se 5 (by rfl) ⟨564308, by rfl⟩ : syracuseStep 12038581 = 1128617) B1128617
theorem B1978865 : Blo 876568 1978865 := bstep (se 2 (by rfl) ⟨742074, by rfl⟩ : syracuseStep 1978865 = 1484149) B1484149
theorem B1978883 : Blo 876568 1978883 := bstep (se 1 (by rfl) ⟨1484162, by rfl⟩ : syracuseStep 1978883 = 2968325) B2968325
theorem B2962061 : Blo 876568 2962061 := bstep (se 3 (by rfl) ⟨555386, by rfl⟩ : syracuseStep 2962061 = 1110773) B1110773
theorem B2962115 : Blo 876568 2962115 := bstep (se 1 (by rfl) ⟨2221586, by rfl⟩ : syracuseStep 2962115 = 4443173) B4443173
theorem B1979153 : Blo 876568 1979153 := bstep (se 2 (by rfl) ⟨742182, by rfl⟩ : syracuseStep 1979153 = 1484365) B1484365
theorem B1979171 : Blo 876568 1979171 := bstep (se 1 (by rfl) ⟨1484378, by rfl⟩ : syracuseStep 1979171 = 2968757) B2968757
theorem B2503523 : Blo 876568 2503523 := bstep (se 1 (by rfl) ⟨1877642, by rfl⟩ : syracuseStep 2503523 = 3755285) B3755285
theorem B2569073 : Blo 876568 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B2962385 : Blo 876568 2962385 := bstep (se 2 (by rfl) ⟨1110894, by rfl⟩ : syracuseStep 2962385 = 2221789) B2221789
theorem B3748913 : Blo 876568 3748913 := bstep (se 2 (by rfl) ⟨1405842, by rfl⟩ : syracuseStep 3748913 = 2811685) B2811685
theorem B1979441 : Blo 876568 1979441 := bstep (se 2 (by rfl) ⟨742290, by rfl⟩ : syracuseStep 1979441 = 1484581) B1484581
theorem B1979459 : Blo 876568 1979459 := bstep (se 1 (by rfl) ⟨1484594, by rfl⟩ : syracuseStep 1979459 = 2969189) B2969189
theorem B3748963 : Blo 876568 3748963 := bstep (se 1 (by rfl) ⟨2811722, by rfl⟩ : syracuseStep 3748963 = 5623445) B5623445
theorem B1979729 : Blo 876568 1979729 := bstep (se 2 (by rfl) ⟨742398, by rfl⟩ : syracuseStep 1979729 = 1484797) B1484797
theorem B1979747 : Blo 876568 1979747 := bstep (se 1 (by rfl) ⟨1484810, by rfl⟩ : syracuseStep 1979747 = 2969621) B2969621
theorem B9024965 : Blo 876568 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B2962925 : Blo 876568 2962925 := bstep (se 3 (by rfl) ⟨555548, by rfl⟩ : syracuseStep 2962925 = 1111097) B1111097
theorem B2962979 : Blo 876568 2962979 := bstep (se 1 (by rfl) ⟨2222234, by rfl⟩ : syracuseStep 2962979 = 4444469) B4444469
theorem B1980017 : Blo 876568 1980017 := bstep (se 2 (by rfl) ⟨742506, by rfl⟩ : syracuseStep 1980017 = 1485013) B1485013
theorem B1980035 : Blo 876568 1980035 := bstep (se 1 (by rfl) ⟨1485026, by rfl⟩ : syracuseStep 1980035 = 2970053) B2970053
theorem B2963249 : Blo 876568 2963249 := bstep (se 2 (by rfl) ⟨1111218, by rfl⟩ : syracuseStep 2963249 = 2222437) B2222437
theorem B1128259 : Blo 876568 1128259 := bstep (se 1 (by rfl) ⟨846194, by rfl⟩ : syracuseStep 1128259 = 1692389) B1692389
theorem B1980305 : Blo 876568 1980305 := bstep (se 2 (by rfl) ⟨742614, by rfl⟩ : syracuseStep 1980305 = 1485229) B1485229
theorem B1980323 : Blo 876568 1980323 := bstep (se 1 (by rfl) ⟨1485242, by rfl⟩ : syracuseStep 1980323 = 2970485) B2970485
theorem B1783811 : Blo 876568 1783811 := bstep (se 1 (by rfl) ⟨1337858, by rfl⟩ : syracuseStep 1783811 = 2675717) B2675717
theorem B2504753 : Blo 876568 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B2373745 : Blo 876568 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B2668721 : Blo 876568 2668721 := bstep (se 2 (by rfl) ⟨1000770, by rfl⟩ : syracuseStep 2668721 = 2001541) B2001541
theorem B1980593 : Blo 876568 1980593 := bstep (se 2 (by rfl) ⟨742722, by rfl⟩ : syracuseStep 1980593 = 1485445) B1485445
theorem B1980611 : Blo 876568 1980611 := bstep (se 1 (by rfl) ⟨1485458, by rfl⟩ : syracuseStep 1980611 = 2970917) B2970917
theorem B4995269 : Blo 876568 4995269 := bstep (se 4 (by rfl) ⟨468306, by rfl⟩ : syracuseStep 4995269 = 936613) B936613
theorem B2963789 : Blo 876568 2963789 := bstep (se 3 (by rfl) ⟨555710, by rfl⟩ : syracuseStep 2963789 = 1111421) B1111421
theorem B1784177 : Blo 876568 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B2963843 : Blo 876568 2963843 := bstep (se 1 (by rfl) ⟨2222882, by rfl⟩ : syracuseStep 2963843 = 4445765) B4445765
theorem B1980881 : Blo 876568 1980881 := bstep (se 2 (by rfl) ⟨742830, by rfl⟩ : syracuseStep 1980881 = 1485661) B1485661
theorem B1980899 : Blo 876568 1980899 := bstep (se 1 (by rfl) ⟨1485674, by rfl⟩ : syracuseStep 1980899 = 2971349) B2971349
theorem B2964113 : Blo 876568 2964113 := bstep (se 2 (by rfl) ⟨1111542, by rfl⟩ : syracuseStep 2964113 = 2223085) B2223085
theorem B1981169 : Blo 876568 1981169 := bstep (se 2 (by rfl) ⟨742938, by rfl⟩ : syracuseStep 1981169 = 1485877) B1485877
theorem B1981187 : Blo 876568 1981187 := bstep (se 1 (by rfl) ⟨1485890, by rfl⟩ : syracuseStep 1981187 = 2971781) B2971781
theorem B4438961 : Blo 876568 4438961 := bstep (se 2 (by rfl) ⟨1664610, by rfl⟩ : syracuseStep 4438961 = 3329221) B3329221
theorem B2669489 : Blo 876568 2669489 := bstep (se 2 (by rfl) ⟨1001058, by rfl⟩ : syracuseStep 2669489 = 2002117) B2002117
theorem B2538467 : Blo 876568 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B2964653 : Blo 876568 2964653 := bstep (se 3 (by rfl) ⟨555872, by rfl⟩ : syracuseStep 2964653 = 1111745) B1111745
theorem B2964707 : Blo 876568 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B5160197 : Blo 876568 5160197 := bstep (se 4 (by rfl) ⟨483768, by rfl⟩ : syracuseStep 5160197 = 967537) B967537
theorem B2375075 : Blo 876568 2375075 := bstep (se 1 (by rfl) ⟨1781306, by rfl⟩ : syracuseStep 2375075 = 3562613) B3562613
theorem B3751373 : Blo 876568 3751373 := bstep (se 3 (by rfl) ⟨703382, by rfl⟩ : syracuseStep 3751373 = 1406765) B1406765
theorem B2506211 : Blo 876568 2506211 := bstep (se 1 (by rfl) ⟨1879658, by rfl⟩ : syracuseStep 2506211 = 3759317) B3759317
theorem B2964977 : Blo 876568 2964977 := bstep (se 2 (by rfl) ⟨1111866, by rfl⟩ : syracuseStep 2964977 = 2223733) B2223733
theorem B11255395 : Blo 876568 11255395 := bstep (se 1 (by rfl) ⟨8441546, by rfl⟩ : syracuseStep 11255395 = 16883093) B16883093
theorem B1392257 : Blo 876568 1392257 := bstep (se 2 (by rfl) ⟨522096, by rfl⟩ : syracuseStep 1392257 = 1044193) B1044193
theorem B7618445 : Blo 876568 7618445 := bstep (se 3 (by rfl) ⟨1428458, by rfl⟩ : syracuseStep 7618445 = 2856917) B2856917
theorem B2965517 : Blo 876568 2965517 := bstep (se 3 (by rfl) ⟨556034, by rfl⟩ : syracuseStep 2965517 = 1112069) B1112069
theorem B2965571 : Blo 876568 2965571 := bstep (se 1 (by rfl) ⟨2224178, by rfl⟩ : syracuseStep 2965571 = 4448357) B4448357
theorem B901283 : Blo 876568 901283 := bstep (se 1 (by rfl) ⟨675962, by rfl⟩ : syracuseStep 901283 = 1351925) B1351925
theorem B2507021 : Blo 876568 2507021 := bstep (se 3 (by rfl) ⟨470066, by rfl⟩ : syracuseStep 2507021 = 940133) B940133
theorem B2965841 : Blo 876568 2965841 := bstep (se 2 (by rfl) ⟨1112190, by rfl⟩ : syracuseStep 2965841 = 2224381) B2224381
theorem B4440419 : Blo 876568 4440419 := bstep (se 1 (by rfl) ⟨3330314, by rfl⟩ : syracuseStep 4440419 = 6660629) B6660629
theorem B2507213 : Blo 876568 2507213 := bstep (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) B940205
theorem B2998865 : Blo 876568 2998865 := bstep (se 2 (by rfl) ⟨1124574, by rfl⟩ : syracuseStep 2998865 = 2249149) B2249149
theorem B2966381 : Blo 876568 2966381 := bstep (se 3 (by rfl) ⟨556196, by rfl⟩ : syracuseStep 2966381 = 1112393) B1112393
theorem B2966435 : Blo 876568 2966435 := bstep (se 1 (by rfl) ⟨2224826, by rfl⟩ : syracuseStep 2966435 = 4449653) B4449653
theorem B4441229 : Blo 876568 4441229 := bstep (se 3 (by rfl) ⟨832730, by rfl⟩ : syracuseStep 4441229 = 1665461) B1665461
theorem B2966705 : Blo 876568 2966705 := bstep (se 2 (by rfl) ⟨1112514, by rfl⟩ : syracuseStep 2966705 = 2225029) B2225029
theorem B78169315 : Blo 876568 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B10012085 : Blo 876568 10012085 := bstep (se 5 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 10012085 = 938633) B938633
theorem B4015565 : Blo 876568 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B1426915 : Blo 876568 1426915 := bstep (se 1 (by rfl) ⟨1070186, by rfl⟩ : syracuseStep 1426915 = 2140373) B2140373
theorem B2999825 : Blo 876568 2999825 := bstep (se 2 (by rfl) ⟨1124934, by rfl⟩ : syracuseStep 2999825 = 2249869) B2249869
theorem B2967245 : Blo 876568 2967245 := bstep (se 3 (by rfl) ⟨556358, by rfl⟩ : syracuseStep 2967245 = 1112717) B1112717
theorem B2967299 : Blo 876568 2967299 := bstep (se 1 (by rfl) ⟨2225474, by rfl⟩ : syracuseStep 2967299 = 4450949) B4450949
theorem B2377603 : Blo 876568 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B4999117 : Blo 876568 4999117 := bstep (se 3 (by rfl) ⟨937334, by rfl⟩ : syracuseStep 4999117 = 1874669) B1874669
theorem B903155 : Blo 876568 903155 := bstep (se 1 (by rfl) ⟨677366, by rfl⟩ : syracuseStep 903155 = 1354733) B1354733
theorem B6670349 : Blo 876568 6670349 := bstep (se 3 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 6670349 = 2501381) B2501381
theorem B2967569 : Blo 876568 2967569 := bstep (se 2 (by rfl) ⟨1112838, by rfl⟩ : syracuseStep 2967569 = 2225677) B2225677
theorem B3000397 : Blo 876568 3000397 := bstep (se 3 (by rfl) ⟨562574, by rfl⟩ : syracuseStep 3000397 = 1125149) B1125149
theorem B5621957 : Blo 876568 5621957 := bstep (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) B1054117
theorem B1427681 : Blo 876568 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B2968109 : Blo 876568 2968109 := bstep (se 3 (by rfl) ⟨556520, by rfl⟩ : syracuseStep 2968109 = 1113041) B1113041
theorem B2968163 : Blo 876568 2968163 := bstep (se 1 (by rfl) ⟨2226122, by rfl⟩ : syracuseStep 2968163 = 4452245) B4452245
theorem B7621361 : Blo 876568 7621361 := bstep (se 2 (by rfl) ⟨2858010, by rfl⟩ : syracuseStep 7621361 = 5716021) B5716021
theorem B1690417 : Blo 876568 1690417 := bstep (se 2 (by rfl) ⟨633906, by rfl⟩ : syracuseStep 1690417 = 1267813) B1267813
theorem B10832753 : Blo 876568 10832753 := bstep (se 2 (by rfl) ⟨4062282, by rfl⟩ : syracuseStep 10832753 = 8124565) B8124565
theorem B2968433 : Blo 876568 2968433 := bstep (se 2 (by rfl) ⟨1113162, by rfl⟩ : syracuseStep 2968433 = 2226325) B2226325
theorem B13519757 : Blo 876568 13519757 := bstep (se 3 (by rfl) ⟨2534954, by rfl⟩ : syracuseStep 13519757 = 5069909) B5069909
theorem B3329009 : Blo 876568 3329009 := bstep (se 2 (by rfl) ⟨1248378, by rfl⟩ : syracuseStep 3329009 = 2496757) B2496757
theorem B937027 : Blo 876568 937027 := bstep (se 1 (by rfl) ⟨702770, by rfl⟩ : syracuseStep 937027 = 1405541) B1405541
theorem B2674001 : Blo 876568 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B2379107 : Blo 876568 2379107 := bstep (se 1 (by rfl) ⟨1784330, by rfl⟩ : syracuseStep 2379107 = 3568661) B3568661
theorem B2968973 : Blo 876568 2968973 := bstep (se 3 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 2968973 = 1113365) B1113365
theorem B6344077 : Blo 876568 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B2969027 : Blo 876568 2969027 := bstep (se 1 (by rfl) ⟨2226770, by rfl⟩ : syracuseStep 2969027 = 4453541) B4453541
theorem B937651 : Blo 876568 937651 := bstep (se 1 (by rfl) ⟨703238, by rfl⟩ : syracuseStep 937651 = 1406477) B1406477
theorem B2969297 : Blo 876568 2969297 := bstep (se 2 (by rfl) ⟨1113486, by rfl⟩ : syracuseStep 2969297 = 2226973) B2226973
theorem B3755747 : Blo 876568 3755747 := bstep (se 1 (by rfl) ⟨2816810, by rfl⟩ : syracuseStep 3755747 = 5633621) B5633621
theorem B2674417 : Blo 876568 2674417 := bstep (se 2 (by rfl) ⟨1002906, by rfl⟩ : syracuseStep 2674417 = 2005813) B2005813
theorem B5001101 : Blo 876568 5001101 := bstep (se 3 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 5001101 = 1875413) B1875413
theorem B4444145 : Blo 876568 4444145 := bstep (se 2 (by rfl) ⟨1666554, by rfl⟩ : syracuseStep 4444145 = 3333109) B3333109
theorem B21418181 : Blo 876568 21418181 := bstep (se 4 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 21418181 = 4015909) B4015909
theorem B2969837 : Blo 876568 2969837 := bstep (se 3 (by rfl) ⟨556844, by rfl⟩ : syracuseStep 2969837 = 1113689) B1113689
theorem B2969891 : Blo 876568 2969891 := bstep (se 1 (by rfl) ⟨2227418, by rfl⟩ : syracuseStep 2969891 = 4454837) B4454837
theorem B3330467 : Blo 876568 3330467 := bstep (se 1 (by rfl) ⟨2497850, by rfl⟩ : syracuseStep 3330467 = 4995701) B4995701
theorem B2970161 : Blo 876568 2970161 := bstep (se 2 (by rfl) ⟨1113810, by rfl⟩ : syracuseStep 2970161 = 2227621) B2227621
theorem B5002033 : Blo 876568 5002033 := bstep (se 2 (by rfl) ⟨1875762, by rfl⟩ : syracuseStep 5002033 = 3751525) B3751525
theorem B1200961 : Blo 876568 1200961 := bstep (se 2 (by rfl) ⟨450360, by rfl⟩ : syracuseStep 1200961 = 900721) B900721
theorem B6673265 : Blo 876568 6673265 := bstep (se 2 (by rfl) ⟨2502474, by rfl⟩ : syracuseStep 6673265 = 5004949) B5004949
theorem B77190029 : Blo 876568 77190029 := bstep (se 3 (by rfl) ⟨14473130, by rfl⟩ : syracuseStep 77190029 = 28946261) B28946261
theorem B2970701 : Blo 876568 2970701 := bstep (se 3 (by rfl) ⟨557006, by rfl⟩ : syracuseStep 2970701 = 1114013) B1114013
theorem B43308145 : Blo 876568 43308145 := bstep (se 2 (by rfl) ⟨16240554, by rfl⟩ : syracuseStep 43308145 = 32481109) B32481109
theorem B2970755 : Blo 876568 2970755 := bstep (se 1 (by rfl) ⟨2228066, by rfl⟩ : syracuseStep 2970755 = 4456133) B4456133
theorem B1692881 : Blo 876568 1692881 := bstep (se 2 (by rfl) ⟨634830, by rfl⟩ : syracuseStep 1692881 = 1269661) B1269661
theorem B5133709 : Blo 876568 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B3331469 : Blo 876568 3331469 := bstep (se 3 (by rfl) ⟨624650, by rfl⟩ : syracuseStep 3331469 = 1249301) B1249301
theorem B2971025 : Blo 876568 2971025 := bstep (se 2 (by rfl) ⟨1114134, by rfl⟩ : syracuseStep 2971025 = 2228269) B2228269
theorem B4445603 : Blo 876568 4445603 := bstep (se 1 (by rfl) ⟨3334202, by rfl⟩ : syracuseStep 4445603 = 6668405) B6668405
theorem B1267201 : Blo 876568 1267201 := bstep (se 2 (by rfl) ⟨475200, by rfl⟩ : syracuseStep 1267201 = 950401) B950401
theorem B939539 : Blo 876568 939539 := bstep (se 1 (by rfl) ⟨704654, by rfl⟩ : syracuseStep 939539 = 1409309) B1409309
theorem B5625443 : Blo 876568 5625443 := bstep (se 1 (by rfl) ⟨4219082, by rfl⟩ : syracuseStep 5625443 = 8438165) B8438165
theorem B3757745 : Blo 876568 3757745 := bstep (se 2 (by rfl) ⟨1409154, by rfl⟩ : syracuseStep 3757745 = 2818309) B2818309
theorem B1333139 : Blo 876568 1333139 := bstep (se 1 (by rfl) ⟨999854, by rfl⟩ : syracuseStep 1333139 = 1999709) B1999709
theorem B2971565 : Blo 876568 2971565 := bstep (se 3 (by rfl) ⟨557168, by rfl⟩ : syracuseStep 2971565 = 1114337) B1114337
theorem B2971619 : Blo 876568 2971619 := bstep (se 1 (by rfl) ⟨2228714, by rfl⟩ : syracuseStep 2971619 = 4457429) B4457429
theorem B4741105 : Blo 876568 4741105 := bstep (se 2 (by rfl) ⟨1777914, by rfl⟩ : syracuseStep 4741105 = 3555829) B3555829
theorem B7133197 : Blo 876568 7133197 := bstep (se 3 (by rfl) ⟨1337474, by rfl⟩ : syracuseStep 7133197 = 2674949) B2674949
theorem B4216931 : Blo 876568 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B4741325 : Blo 876568 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B4446413 : Blo 876568 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B5003491 : Blo 876568 5003491 := bstep (se 1 (by rfl) ⟨3752618, by rfl⟩ : syracuseStep 5003491 = 7505237) B7505237
theorem B2971889 : Blo 876568 2971889 := bstep (se 2 (by rfl) ⟨1114458, by rfl⟩ : syracuseStep 2971889 = 2228917) B2228917
theorem B7494029 : Blo 876568 7494029 := bstep (se 3 (by rfl) ⟨1405130, by rfl⟩ : syracuseStep 7494029 = 2810261) B2810261
theorem B3758669 : Blo 876568 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B4512419 : Blo 876568 4512419 := bstep (se 1 (by rfl) ⟨3384314, by rfl⟩ : syracuseStep 4512419 = 6768629) B6768629
theorem B5004017 : Blo 876568 5004017 := bstep (se 2 (by rfl) ⟨1876506, by rfl⟩ : syracuseStep 5004017 = 3753013) B3753013
theorem B1334065 : Blo 876568 1334065 := bstep (se 2 (by rfl) ⟨500274, by rfl⟩ : syracuseStep 1334065 = 1000549) B1000549
theorem B1334081 : Blo 876568 1334081 := bstep (se 2 (by rfl) ⟨500280, by rfl⟩ : syracuseStep 1334081 = 1000561) B1000561
theorem B5790733 : Blo 876568 5790733 := bstep (se 3 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 5790733 = 2171525) B2171525
theorem B1072211 : Blo 876568 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B8019299 : Blo 876568 8019299 := bstep (se 1 (by rfl) ⟨6014474, by rfl⟩ : syracuseStep 8019299 = 12028949) B12028949
theorem B3333581 : Blo 876568 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B2219633 : Blo 876568 2219633 := bstep (se 2 (by rfl) ⟨832362, by rfl⟩ : syracuseStep 2219633 = 1664725) B1664725
theorem B2219683 : Blo 876568 2219683 := bstep (se 1 (by rfl) ⟨1664762, by rfl⟩ : syracuseStep 2219683 = 3329525) B3329525
theorem B4742819 : Blo 876568 4742819 := bstep (se 1 (by rfl) ⟨3557114, by rfl⟩ : syracuseStep 4742819 = 7114229) B7114229
theorem B2285329 : Blo 876568 2285329 := bstep (se 2 (by rfl) ⟨856998, by rfl⟩ : syracuseStep 2285329 = 1713997) B1713997
theorem B2219825 : Blo 876568 2219825 := bstep (se 2 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 2219825 = 1664869) B1664869
theorem B876579 : Blo 876568 876579 := bstep (se 1 (by rfl) ⟨657434, by rfl⟩ : syracuseStep 876579 = 1314869) B1314869
theorem B4218929 : Blo 876568 4218929 := bstep (se 2 (by rfl) ⟨1582098, by rfl⟩ : syracuseStep 4218929 = 3164197) B3164197
theorem B876595 : Blo 876568 876595 := bstep (se 1 (by rfl) ⟨657446, by rfl⟩ : syracuseStep 876595 = 1314893) B1314893
theorem B876611 : Blo 876568 876611 := bstep (se 1 (by rfl) ⟨657458, by rfl⟩ : syracuseStep 876611 = 1314917) B1314917
theorem B876627 : Blo 876568 876627 := bstep (se 1 (by rfl) ⟨657470, by rfl⟩ : syracuseStep 876627 = 1314941) B1314941
theorem B1269857 : Blo 876568 1269857 := bstep (se 2 (by rfl) ⟨476196, by rfl⟩ : syracuseStep 1269857 = 952393) B952393
theorem B876643 : Blo 876568 876643 := bstep (se 1 (by rfl) ⟨657482, by rfl⟩ : syracuseStep 876643 = 1314965) B1314965
theorem B876659 : Blo 876568 876659 := bstep (se 1 (by rfl) ⟨657494, by rfl⟩ : syracuseStep 876659 = 1314989) B1314989
theorem B876675 : Blo 876568 876675 := bstep (se 1 (by rfl) ⟨657506, by rfl⟩ : syracuseStep 876675 = 1315013) B1315013
theorem B876691 : Blo 876568 876691 := bstep (se 1 (by rfl) ⟨657518, by rfl⟩ : syracuseStep 876691 = 1315037) B1315037
theorem B876707 : Blo 876568 876707 := bstep (se 1 (by rfl) ⟨657530, by rfl⟩ : syracuseStep 876707 = 1315061) B1315061
theorem B5005475 : Blo 876568 5005475 := bstep (se 1 (by rfl) ⟨3754106, by rfl⟩ : syracuseStep 5005475 = 7508213) B7508213
theorem B876723 : Blo 876568 876723 := bstep (se 1 (by rfl) ⟨657542, by rfl⟩ : syracuseStep 876723 = 1315085) B1315085
theorem B876739 : Blo 876568 876739 := bstep (se 1 (by rfl) ⟨657554, by rfl⟩ : syracuseStep 876739 = 1315109) B1315109
theorem B876755 : Blo 876568 876755 := bstep (se 1 (by rfl) ⟨657566, by rfl⟩ : syracuseStep 876755 = 1315133) B1315133
theorem B876771 : Blo 876568 876771 := bstep (se 1 (by rfl) ⟨657578, by rfl⟩ : syracuseStep 876771 = 1315157) B1315157
theorem B3334385 : Blo 876568 3334385 := bstep (se 2 (by rfl) ⟨1250394, by rfl⟩ : syracuseStep 3334385 = 2500789) B2500789
theorem B876787 : Blo 876568 876787 := bstep (se 1 (by rfl) ⟨657590, by rfl⟩ : syracuseStep 876787 = 1315181) B1315181
theorem B876803 : Blo 876568 876803 := bstep (se 1 (by rfl) ⟨657602, by rfl⟩ : syracuseStep 876803 = 1315205) B1315205
theorem B876819 : Blo 876568 876819 := bstep (se 1 (by rfl) ⟨657614, by rfl⟩ : syracuseStep 876819 = 1315229) B1315229
theorem B876835 : Blo 876568 876835 := bstep (se 1 (by rfl) ⟨657626, by rfl⟩ : syracuseStep 876835 = 1315253) B1315253
theorem B876851 : Blo 876568 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B876867 : Blo 876568 876867 := bstep (se 1 (by rfl) ⟨657650, by rfl⟩ : syracuseStep 876867 = 1315301) B1315301
theorem B876883 : Blo 876568 876883 := bstep (se 1 (by rfl) ⟨657662, by rfl⟩ : syracuseStep 876883 = 1315325) B1315325
theorem B876899 : Blo 876568 876899 := bstep (se 1 (by rfl) ⟨657674, by rfl⟩ : syracuseStep 876899 = 1315349) B1315349
theorem B3006829 : Blo 876568 3006829 := bstep (se 3 (by rfl) ⟨563780, by rfl⟩ : syracuseStep 3006829 = 1127561) B1127561
theorem B876915 : Blo 876568 876915 := bstep (se 1 (by rfl) ⟨657686, by rfl⟩ : syracuseStep 876915 = 1315373) B1315373
theorem B876931 : Blo 876568 876931 := bstep (se 1 (by rfl) ⟨657698, by rfl⟩ : syracuseStep 876931 = 1315397) B1315397
theorem B876947 : Blo 876568 876947 := bstep (se 1 (by rfl) ⟨657710, by rfl⟩ : syracuseStep 876947 = 1315421) B1315421
theorem B876963 : Blo 876568 876963 := bstep (se 1 (by rfl) ⟨657722, by rfl⟩ : syracuseStep 876963 = 1315445) B1315445
theorem B876979 : Blo 876568 876979 := bstep (se 1 (by rfl) ⟨657734, by rfl⟩ : syracuseStep 876979 = 1315469) B1315469
theorem B876995 : Blo 876568 876995 := bstep (se 1 (by rfl) ⟨657746, by rfl⟩ : syracuseStep 876995 = 1315493) B1315493
theorem B877011 : Blo 876568 877011 := bstep (se 1 (by rfl) ⟨657758, by rfl⟩ : syracuseStep 877011 = 1315517) B1315517
theorem B877027 : Blo 876568 877027 := bstep (se 1 (by rfl) ⟨657770, by rfl⟩ : syracuseStep 877027 = 1315541) B1315541
theorem B3170801 : Blo 876568 3170801 := bstep (se 2 (by rfl) ⟨1189050, by rfl⟩ : syracuseStep 3170801 = 2378101) B2378101
theorem B877043 : Blo 876568 877043 := bstep (se 1 (by rfl) ⟨657782, by rfl⟩ : syracuseStep 877043 = 1315565) B1315565
theorem B877059 : Blo 876568 877059 := bstep (se 1 (by rfl) ⟨657794, by rfl⟩ : syracuseStep 877059 = 1315589) B1315589
theorem B877075 : Blo 876568 877075 := bstep (se 1 (by rfl) ⟨657806, by rfl⟩ : syracuseStep 877075 = 1315613) B1315613
theorem B877091 : Blo 876568 877091 := bstep (se 1 (by rfl) ⟨657818, by rfl⟩ : syracuseStep 877091 = 1315637) B1315637
theorem B877107 : Blo 876568 877107 := bstep (se 1 (by rfl) ⟨657830, by rfl⟩ : syracuseStep 877107 = 1315661) B1315661
theorem B877123 : Blo 876568 877123 := bstep (se 1 (by rfl) ⟨657842, by rfl⟩ : syracuseStep 877123 = 1315685) B1315685
theorem B877139 : Blo 876568 877139 := bstep (se 1 (by rfl) ⟨657854, by rfl⟩ : syracuseStep 877139 = 1315709) B1315709
theorem B877155 : Blo 876568 877155 := bstep (se 1 (by rfl) ⟨657866, by rfl⟩ : syracuseStep 877155 = 1315733) B1315733
theorem B877171 : Blo 876568 877171 := bstep (se 1 (by rfl) ⟨657878, by rfl⟩ : syracuseStep 877171 = 1315757) B1315757
theorem B877187 : Blo 876568 877187 := bstep (se 1 (by rfl) ⟨657890, by rfl⟩ : syracuseStep 877187 = 1315781) B1315781
theorem B877203 : Blo 876568 877203 := bstep (se 1 (by rfl) ⟨657902, by rfl⟩ : syracuseStep 877203 = 1315805) B1315805
theorem B877219 : Blo 876568 877219 := bstep (se 1 (by rfl) ⟨657914, by rfl⟩ : syracuseStep 877219 = 1315829) B1315829
theorem B877235 : Blo 876568 877235 := bstep (se 1 (by rfl) ⟨657926, by rfl⟩ : syracuseStep 877235 = 1315853) B1315853
theorem B877251 : Blo 876568 877251 := bstep (se 1 (by rfl) ⟨657938, by rfl⟩ : syracuseStep 877251 = 1315877) B1315877
theorem B877267 : Blo 876568 877267 := bstep (se 1 (by rfl) ⟨657950, by rfl⟩ : syracuseStep 877267 = 1315901) B1315901
theorem B877283 : Blo 876568 877283 := bstep (se 1 (by rfl) ⟨657962, by rfl⟩ : syracuseStep 877283 = 1315925) B1315925
theorem B877299 : Blo 876568 877299 := bstep (se 1 (by rfl) ⟨657974, by rfl⟩ : syracuseStep 877299 = 1315949) B1315949
theorem B877315 : Blo 876568 877315 := bstep (se 1 (by rfl) ⟨657986, by rfl⟩ : syracuseStep 877315 = 1315973) B1315973
theorem B2220817 : Blo 876568 2220817 := bstep (se 2 (by rfl) ⟨832806, by rfl⟩ : syracuseStep 2220817 = 1665613) B1665613
theorem B877331 : Blo 876568 877331 := bstep (se 1 (by rfl) ⟨657998, by rfl⟩ : syracuseStep 877331 = 1315997) B1315997
theorem B877347 : Blo 876568 877347 := bstep (se 1 (by rfl) ⟨658010, by rfl⟩ : syracuseStep 877347 = 1316021) B1316021
theorem B877363 : Blo 876568 877363 := bstep (se 1 (by rfl) ⟨658022, by rfl⟩ : syracuseStep 877363 = 1316045) B1316045
theorem B877379 : Blo 876568 877379 := bstep (se 1 (by rfl) ⟨658034, by rfl⟩ : syracuseStep 877379 = 1316069) B1316069
theorem B877395 : Blo 876568 877395 := bstep (se 1 (by rfl) ⟨658046, by rfl⟩ : syracuseStep 877395 = 1316093) B1316093
theorem B877411 : Blo 876568 877411 := bstep (se 1 (by rfl) ⟨658058, by rfl⟩ : syracuseStep 877411 = 1316117) B1316117
theorem B877427 : Blo 876568 877427 := bstep (se 1 (by rfl) ⟨658070, by rfl⟩ : syracuseStep 877427 = 1316141) B1316141
theorem B877443 : Blo 876568 877443 := bstep (se 1 (by rfl) ⟨658082, by rfl⟩ : syracuseStep 877443 = 1316165) B1316165
theorem B3335053 : Blo 876568 3335053 := bstep (se 3 (by rfl) ⟨625322, by rfl⟩ : syracuseStep 3335053 = 1250645) B1250645
theorem B877459 : Blo 876568 877459 := bstep (se 1 (by rfl) ⟨658094, by rfl⟩ : syracuseStep 877459 = 1316189) B1316189
theorem B877475 : Blo 876568 877475 := bstep (se 1 (by rfl) ⟨658106, by rfl⟩ : syracuseStep 877475 = 1316213) B1316213
theorem B2810801 : Blo 876568 2810801 := bstep (se 2 (by rfl) ⟨1054050, by rfl⟩ : syracuseStep 2810801 = 2108101) B2108101
theorem B877491 : Blo 876568 877491 := bstep (se 1 (by rfl) ⟨658118, by rfl⟩ : syracuseStep 877491 = 1316237) B1316237
theorem B877507 : Blo 876568 877507 := bstep (se 1 (by rfl) ⟨658130, by rfl⟩ : syracuseStep 877507 = 1316261) B1316261
theorem B1336259 : Blo 876568 1336259 := bstep (se 1 (by rfl) ⟨1002194, by rfl⟩ : syracuseStep 1336259 = 2004389) B2004389
theorem B877523 : Blo 876568 877523 := bstep (se 1 (by rfl) ⟨658142, by rfl⟩ : syracuseStep 877523 = 1316285) B1316285
theorem B877539 : Blo 876568 877539 := bstep (se 1 (by rfl) ⟨658154, by rfl⟩ : syracuseStep 877539 = 1316309) B1316309
theorem B877555 : Blo 876568 877555 := bstep (se 1 (by rfl) ⟨658166, by rfl⟩ : syracuseStep 877555 = 1316333) B1316333
theorem B877571 : Blo 876568 877571 := bstep (se 1 (by rfl) ⟨658178, by rfl⟩ : syracuseStep 877571 = 1316357) B1316357
theorem B877587 : Blo 876568 877587 := bstep (se 1 (by rfl) ⟨658190, by rfl⟩ : syracuseStep 877587 = 1316381) B1316381
theorem B2221091 : Blo 876568 2221091 := bstep (se 1 (by rfl) ⟨1665818, by rfl⟩ : syracuseStep 2221091 = 3331637) B3331637
theorem B877603 : Blo 876568 877603 := bstep (se 1 (by rfl) ⟨658202, by rfl⟩ : syracuseStep 877603 = 1316405) B1316405
theorem B4449329 : Blo 876568 4449329 := bstep (se 2 (by rfl) ⟨1668498, by rfl⟩ : syracuseStep 4449329 = 3336997) B3336997
theorem B877619 : Blo 876568 877619 := bstep (se 1 (by rfl) ⟨658214, by rfl⟩ : syracuseStep 877619 = 1316429) B1316429
theorem B877635 : Blo 876568 877635 := bstep (se 1 (by rfl) ⟨658226, by rfl⟩ : syracuseStep 877635 = 1316453) B1316453
theorem B877651 : Blo 876568 877651 := bstep (se 1 (by rfl) ⟨658238, by rfl⟩ : syracuseStep 877651 = 1316477) B1316477
theorem B877667 : Blo 876568 877667 := bstep (se 1 (by rfl) ⟨658250, by rfl⟩ : syracuseStep 877667 = 1316501) B1316501
theorem B4809827 : Blo 876568 4809827 := bstep (se 1 (by rfl) ⟨3607370, by rfl⟩ : syracuseStep 4809827 = 7214741) B7214741
theorem B877683 : Blo 876568 877683 := bstep (se 1 (by rfl) ⟨658262, by rfl⟩ : syracuseStep 877683 = 1316525) B1316525
theorem B877699 : Blo 876568 877699 := bstep (se 1 (by rfl) ⟨658274, by rfl⟩ : syracuseStep 877699 = 1316549) B1316549
theorem B4220045 : Blo 876568 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B877715 : Blo 876568 877715 := bstep (se 1 (by rfl) ⟨658286, by rfl⟩ : syracuseStep 877715 = 1316573) B1316573
theorem B877731 : Blo 876568 877731 := bstep (se 1 (by rfl) ⟨658298, by rfl⟩ : syracuseStep 877731 = 1316597) B1316597
theorem B877747 : Blo 876568 877747 := bstep (se 1 (by rfl) ⟨658310, by rfl⟩ : syracuseStep 877747 = 1316621) B1316621
theorem B877763 : Blo 876568 877763 := bstep (se 1 (by rfl) ⟨658322, by rfl⟩ : syracuseStep 877763 = 1316645) B1316645
theorem B877779 : Blo 876568 877779 := bstep (se 1 (by rfl) ⟨658334, by rfl⟩ : syracuseStep 877779 = 1316669) B1316669
theorem B1500385 : Blo 876568 1500385 := bstep (se 2 (by rfl) ⟨562644, by rfl⟩ : syracuseStep 1500385 = 1125289) B1125289
theorem B9987299 : Blo 876568 9987299 := bstep (se 1 (by rfl) ⟨7490474, by rfl⟩ : syracuseStep 9987299 = 14980949) B14980949
theorem B2221283 : Blo 876568 2221283 := bstep (se 1 (by rfl) ⟨1665962, by rfl⟩ : syracuseStep 2221283 = 3331925) B3331925
theorem B877795 : Blo 876568 877795 := bstep (se 1 (by rfl) ⟨658346, by rfl⟩ : syracuseStep 877795 = 1316693) B1316693
theorem B877811 : Blo 876568 877811 := bstep (se 1 (by rfl) ⟨658358, by rfl⟩ : syracuseStep 877811 = 1316717) B1316717
theorem B877827 : Blo 876568 877827 := bstep (se 1 (by rfl) ⟨658370, by rfl⟩ : syracuseStep 877827 = 1316741) B1316741
theorem B877843 : Blo 876568 877843 := bstep (se 1 (by rfl) ⟨658382, by rfl⟩ : syracuseStep 877843 = 1316765) B1316765
theorem B877859 : Blo 876568 877859 := bstep (se 1 (by rfl) ⟨658394, by rfl⟩ : syracuseStep 877859 = 1316789) B1316789
theorem B877875 : Blo 876568 877875 := bstep (se 1 (by rfl) ⟨658406, by rfl⟩ : syracuseStep 877875 = 1316813) B1316813
theorem B877891 : Blo 876568 877891 := bstep (se 1 (by rfl) ⟨658418, by rfl⟩ : syracuseStep 877891 = 1316837) B1316837
theorem B877907 : Blo 876568 877907 := bstep (se 1 (by rfl) ⟨658430, by rfl⟩ : syracuseStep 877907 = 1316861) B1316861
theorem B877923 : Blo 876568 877923 := bstep (se 1 (by rfl) ⟨658442, by rfl⟩ : syracuseStep 877923 = 1316885) B1316885
theorem B877939 : Blo 876568 877939 := bstep (se 1 (by rfl) ⟨658454, by rfl⟩ : syracuseStep 877939 = 1316909) B1316909
theorem B877955 : Blo 876568 877955 := bstep (se 1 (by rfl) ⟨658466, by rfl⟩ : syracuseStep 877955 = 1316933) B1316933
theorem B877971 : Blo 876568 877971 := bstep (se 1 (by rfl) ⟨658478, by rfl⟩ : syracuseStep 877971 = 1316957) B1316957
theorem B877987 : Blo 876568 877987 := bstep (se 1 (by rfl) ⟨658490, by rfl⟩ : syracuseStep 877987 = 1316981) B1316981
theorem B878003 : Blo 876568 878003 := bstep (se 1 (by rfl) ⟨658502, by rfl⟩ : syracuseStep 878003 = 1317005) B1317005
theorem B878019 : Blo 876568 878019 := bstep (se 1 (by rfl) ⟨658514, by rfl⟩ : syracuseStep 878019 = 1317029) B1317029
theorem B878035 : Blo 876568 878035 := bstep (se 1 (by rfl) ⟨658526, by rfl⟩ : syracuseStep 878035 = 1317053) B1317053
theorem B878051 : Blo 876568 878051 := bstep (se 1 (by rfl) ⟨658538, by rfl⟩ : syracuseStep 878051 = 1317077) B1317077
theorem B878067 : Blo 876568 878067 := bstep (se 1 (by rfl) ⟨658550, by rfl⟩ : syracuseStep 878067 = 1317101) B1317101
theorem B1336819 : Blo 876568 1336819 := bstep (se 1 (by rfl) ⟨1002614, by rfl⟩ : syracuseStep 1336819 = 2005229) B2005229
theorem B878083 : Blo 876568 878083 := bstep (se 1 (by rfl) ⟨658562, by rfl⟩ : syracuseStep 878083 = 1317125) B1317125
theorem B878099 : Blo 876568 878099 := bstep (se 1 (by rfl) ⟨658574, by rfl⟩ : syracuseStep 878099 = 1317149) B1317149
theorem B878115 : Blo 876568 878115 := bstep (se 1 (by rfl) ⟨658586, by rfl⟩ : syracuseStep 878115 = 1317173) B1317173
theorem B878131 : Blo 876568 878131 := bstep (se 1 (by rfl) ⟨658598, by rfl⟩ : syracuseStep 878131 = 1317197) B1317197
theorem B878147 : Blo 876568 878147 := bstep (se 1 (by rfl) ⟨658610, by rfl⟩ : syracuseStep 878147 = 1317221) B1317221
theorem B878163 : Blo 876568 878163 := bstep (se 1 (by rfl) ⟨658622, by rfl⟩ : syracuseStep 878163 = 1317245) B1317245
theorem B878179 : Blo 876568 878179 := bstep (se 1 (by rfl) ⟨658634, by rfl⟩ : syracuseStep 878179 = 1317269) B1317269
theorem B878195 : Blo 876568 878195 := bstep (se 1 (by rfl) ⟨658646, by rfl⟩ : syracuseStep 878195 = 1317293) B1317293
theorem B878211 : Blo 876568 878211 := bstep (se 1 (by rfl) ⟨658658, by rfl⟩ : syracuseStep 878211 = 1317317) B1317317
theorem B878227 : Blo 876568 878227 := bstep (se 1 (by rfl) ⟨658670, by rfl⟩ : syracuseStep 878227 = 1317341) B1317341
theorem B878243 : Blo 876568 878243 := bstep (se 1 (by rfl) ⟨658682, by rfl⟩ : syracuseStep 878243 = 1317365) B1317365
theorem B3335843 : Blo 876568 3335843 := bstep (se 1 (by rfl) ⟨2501882, by rfl⟩ : syracuseStep 3335843 = 5003765) B5003765
theorem B878259 : Blo 876568 878259 := bstep (se 1 (by rfl) ⟨658694, by rfl⟩ : syracuseStep 878259 = 1317389) B1317389
theorem B878275 : Blo 876568 878275 := bstep (se 1 (by rfl) ⟨658706, by rfl⟩ : syracuseStep 878275 = 1317413) B1317413
theorem B878291 : Blo 876568 878291 := bstep (se 1 (by rfl) ⟨658718, by rfl⟩ : syracuseStep 878291 = 1317437) B1317437
theorem B878307 : Blo 876568 878307 := bstep (se 1 (by rfl) ⟨658730, by rfl⟩ : syracuseStep 878307 = 1317461) B1317461
theorem B878323 : Blo 876568 878323 := bstep (se 1 (by rfl) ⟨658742, by rfl⟩ : syracuseStep 878323 = 1317485) B1317485
theorem B878339 : Blo 876568 878339 := bstep (se 1 (by rfl) ⟨658754, by rfl⟩ : syracuseStep 878339 = 1317509) B1317509
theorem B878355 : Blo 876568 878355 := bstep (se 1 (by rfl) ⟨658766, by rfl⟩ : syracuseStep 878355 = 1317533) B1317533
theorem B878371 : Blo 876568 878371 := bstep (se 1 (by rfl) ⟨658778, by rfl⟩ : syracuseStep 878371 = 1317557) B1317557
theorem B878387 : Blo 876568 878387 := bstep (se 1 (by rfl) ⟨658790, by rfl⟩ : syracuseStep 878387 = 1317581) B1317581
theorem B878403 : Blo 876568 878403 := bstep (se 1 (by rfl) ⟨658802, by rfl⟩ : syracuseStep 878403 = 1317605) B1317605
theorem B3008333 : Blo 876568 3008333 := bstep (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) B1128125
theorem B878419 : Blo 876568 878419 := bstep (se 1 (by rfl) ⟨658814, by rfl⟩ : syracuseStep 878419 = 1317629) B1317629
theorem B878435 : Blo 876568 878435 := bstep (se 1 (by rfl) ⟨658826, by rfl⟩ : syracuseStep 878435 = 1317653) B1317653
theorem B878451 : Blo 876568 878451 := bstep (se 1 (by rfl) ⟨658838, by rfl⟩ : syracuseStep 878451 = 1317677) B1317677
theorem B878467 : Blo 876568 878467 := bstep (se 1 (by rfl) ⟨658850, by rfl⟩ : syracuseStep 878467 = 1317701) B1317701
theorem B878483 : Blo 876568 878483 := bstep (se 1 (by rfl) ⟨658862, by rfl⟩ : syracuseStep 878483 = 1317725) B1317725
theorem B878499 : Blo 876568 878499 := bstep (se 1 (by rfl) ⟨658874, by rfl⟩ : syracuseStep 878499 = 1317749) B1317749
theorem B1664945 : Blo 876568 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B878515 : Blo 876568 878515 := bstep (se 1 (by rfl) ⟨658886, by rfl⟩ : syracuseStep 878515 = 1317773) B1317773
theorem B878531 : Blo 876568 878531 := bstep (se 1 (by rfl) ⟨658898, by rfl⟩ : syracuseStep 878531 = 1317797) B1317797
theorem B878547 : Blo 876568 878547 := bstep (se 1 (by rfl) ⟨658910, by rfl⟩ : syracuseStep 878547 = 1317821) B1317821
theorem B878563 : Blo 876568 878563 := bstep (se 1 (by rfl) ⟨658922, by rfl⟩ : syracuseStep 878563 = 1317845) B1317845
theorem B878579 : Blo 876568 878579 := bstep (se 1 (by rfl) ⟨658934, by rfl⟩ : syracuseStep 878579 = 1317869) B1317869
theorem B878595 : Blo 876568 878595 := bstep (se 1 (by rfl) ⟨658946, by rfl⟩ : syracuseStep 878595 = 1317893) B1317893
theorem B5007365 : Blo 876568 5007365 := bstep (se 4 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 5007365 = 938881) B938881
theorem B878611 : Blo 876568 878611 := bstep (se 1 (by rfl) ⟨658958, by rfl⟩ : syracuseStep 878611 = 1317917) B1317917
theorem B878627 : Blo 876568 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B878643 : Blo 876568 878643 := bstep (se 1 (by rfl) ⟨658982, by rfl⟩ : syracuseStep 878643 = 1317965) B1317965
theorem B878659 : Blo 876568 878659 := bstep (se 1 (by rfl) ⟨658994, by rfl⟩ : syracuseStep 878659 = 1317989) B1317989
theorem B878675 : Blo 876568 878675 := bstep (se 1 (by rfl) ⟨659006, by rfl⟩ : syracuseStep 878675 = 1318013) B1318013
theorem B878691 : Blo 876568 878691 := bstep (se 1 (by rfl) ⟨659018, by rfl⟩ : syracuseStep 878691 = 1318037) B1318037
theorem B878707 : Blo 876568 878707 := bstep (se 1 (by rfl) ⟨659030, by rfl⟩ : syracuseStep 878707 = 1318061) B1318061
theorem B878723 : Blo 876568 878723 := bstep (se 1 (by rfl) ⟨659042, by rfl⟩ : syracuseStep 878723 = 1318085) B1318085
theorem B2222225 : Blo 876568 2222225 := bstep (se 2 (by rfl) ⟨833334, by rfl⟩ : syracuseStep 2222225 = 1666669) B1666669
theorem B878739 : Blo 876568 878739 := bstep (se 1 (by rfl) ⟨659054, by rfl⟩ : syracuseStep 878739 = 1318109) B1318109
theorem B878755 : Blo 876568 878755 := bstep (se 1 (by rfl) ⟨659066, by rfl⟩ : syracuseStep 878755 = 1318133) B1318133
theorem B878771 : Blo 876568 878771 := bstep (se 1 (by rfl) ⟨659078, by rfl⟩ : syracuseStep 878771 = 1318157) B1318157
theorem B2222275 : Blo 876568 2222275 := bstep (se 1 (by rfl) ⟨1666706, by rfl⟩ : syracuseStep 2222275 = 3333413) B3333413
theorem B878787 : Blo 876568 878787 := bstep (se 1 (by rfl) ⟨659090, by rfl⟩ : syracuseStep 878787 = 1318181) B1318181
theorem B878803 : Blo 876568 878803 := bstep (se 1 (by rfl) ⟨659102, by rfl⟩ : syracuseStep 878803 = 1318205) B1318205
theorem B878819 : Blo 876568 878819 := bstep (se 1 (by rfl) ⟨659114, by rfl⟩ : syracuseStep 878819 = 1318229) B1318229
theorem B878835 : Blo 876568 878835 := bstep (se 1 (by rfl) ⟨659126, by rfl⟩ : syracuseStep 878835 = 1318253) B1318253
theorem B878851 : Blo 876568 878851 := bstep (se 1 (by rfl) ⟨659138, by rfl⟩ : syracuseStep 878851 = 1318277) B1318277
theorem B3008771 : Blo 876568 3008771 := bstep (se 1 (by rfl) ⟨2256578, by rfl⟩ : syracuseStep 3008771 = 4513157) B4513157
theorem B5335301 : Blo 876568 5335301 := bstep (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) B1000369
theorem B878867 : Blo 876568 878867 := bstep (se 1 (by rfl) ⟨659150, by rfl⟩ : syracuseStep 878867 = 1318301) B1318301
theorem B878883 : Blo 876568 878883 := bstep (se 1 (by rfl) ⟨659162, by rfl⟩ : syracuseStep 878883 = 1318325) B1318325
theorem B3336497 : Blo 876568 3336497 := bstep (se 2 (by rfl) ⟨1251186, by rfl⟩ : syracuseStep 3336497 = 2502373) B2502373
theorem B878899 : Blo 876568 878899 := bstep (se 1 (by rfl) ⟨659174, by rfl⟩ : syracuseStep 878899 = 1318349) B1318349
theorem B878915 : Blo 876568 878915 := bstep (se 1 (by rfl) ⟨659186, by rfl⟩ : syracuseStep 878915 = 1318373) B1318373
theorem B2222417 : Blo 876568 2222417 := bstep (se 2 (by rfl) ⟨833406, by rfl⟩ : syracuseStep 2222417 = 1666813) B1666813
theorem B878931 : Blo 876568 878931 := bstep (se 1 (by rfl) ⟨659198, by rfl⟩ : syracuseStep 878931 = 1318397) B1318397
theorem B878947 : Blo 876568 878947 := bstep (se 1 (by rfl) ⟨659210, by rfl⟩ : syracuseStep 878947 = 1318421) B1318421
theorem B6318449 : Blo 876568 6318449 := bstep (se 2 (by rfl) ⟨2369418, by rfl⟩ : syracuseStep 6318449 = 4738837) B4738837
theorem B878963 : Blo 876568 878963 := bstep (se 1 (by rfl) ⟨659222, by rfl⟩ : syracuseStep 878963 = 1318445) B1318445
theorem B878979 : Blo 876568 878979 := bstep (se 1 (by rfl) ⟨659234, by rfl⟩ : syracuseStep 878979 = 1318469) B1318469
theorem B878995 : Blo 876568 878995 := bstep (se 1 (by rfl) ⟨659246, by rfl⟩ : syracuseStep 878995 = 1318493) B1318493
theorem B879011 : Blo 876568 879011 := bstep (se 1 (by rfl) ⟨659258, by rfl⟩ : syracuseStep 879011 = 1318517) B1318517
theorem B879027 : Blo 876568 879027 := bstep (se 1 (by rfl) ⟨659270, by rfl⟩ : syracuseStep 879027 = 1318541) B1318541
theorem B879043 : Blo 876568 879043 := bstep (se 1 (by rfl) ⟨659282, by rfl⟩ : syracuseStep 879043 = 1318565) B1318565
theorem B4221389 : Blo 876568 4221389 := bstep (se 3 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 4221389 = 1583021) B1583021
theorem B879059 : Blo 876568 879059 := bstep (se 1 (by rfl) ⟨659294, by rfl⟩ : syracuseStep 879059 = 1318589) B1318589
theorem B879075 : Blo 876568 879075 := bstep (se 1 (by rfl) ⟨659306, by rfl⟩ : syracuseStep 879075 = 1318613) B1318613
theorem B4450787 : Blo 876568 4450787 := bstep (se 1 (by rfl) ⟨3338090, by rfl⟩ : syracuseStep 4450787 = 6676181) B6676181
theorem B879091 : Blo 876568 879091 := bstep (se 1 (by rfl) ⟨659318, by rfl⟩ : syracuseStep 879091 = 1318637) B1318637
theorem B879107 : Blo 876568 879107 := bstep (se 1 (by rfl) ⟨659330, by rfl⟩ : syracuseStep 879107 = 1318661) B1318661
theorem B3172877 : Blo 876568 3172877 := bstep (se 3 (by rfl) ⟨594914, by rfl⟩ : syracuseStep 3172877 = 1189829) B1189829
theorem B879123 : Blo 876568 879123 := bstep (se 1 (by rfl) ⟨659342, by rfl⟩ : syracuseStep 879123 = 1318685) B1318685
theorem B879139 : Blo 876568 879139 := bstep (se 1 (by rfl) ⟨659354, by rfl⟩ : syracuseStep 879139 = 1318709) B1318709
theorem B879155 : Blo 876568 879155 := bstep (se 1 (by rfl) ⟨659366, by rfl⟩ : syracuseStep 879155 = 1318733) B1318733
theorem B879171 : Blo 876568 879171 := bstep (se 1 (by rfl) ⟨659378, by rfl⟩ : syracuseStep 879171 = 1318757) B1318757
theorem B879187 : Blo 876568 879187 := bstep (se 1 (by rfl) ⟨659390, by rfl⟩ : syracuseStep 879187 = 1318781) B1318781
theorem B879203 : Blo 876568 879203 := bstep (se 1 (by rfl) ⟨659402, by rfl⟩ : syracuseStep 879203 = 1318805) B1318805
theorem B879219 : Blo 876568 879219 := bstep (se 1 (by rfl) ⟨659414, by rfl⟩ : syracuseStep 879219 = 1318829) B1318829
theorem B879235 : Blo 876568 879235 := bstep (se 1 (by rfl) ⟨659426, by rfl⟩ : syracuseStep 879235 = 1318853) B1318853
theorem B879251 : Blo 876568 879251 := bstep (se 1 (by rfl) ⟨659438, by rfl⟩ : syracuseStep 879251 = 1318877) B1318877
theorem B879267 : Blo 876568 879267 := bstep (se 1 (by rfl) ⟨659450, by rfl⟩ : syracuseStep 879267 = 1318901) B1318901
theorem B879283 : Blo 876568 879283 := bstep (se 1 (by rfl) ⟨659462, by rfl⟩ : syracuseStep 879283 = 1318925) B1318925
theorem B879299 : Blo 876568 879299 := bstep (se 1 (by rfl) ⟨659474, by rfl⟩ : syracuseStep 879299 = 1318949) B1318949
theorem B879315 : Blo 876568 879315 := bstep (se 1 (by rfl) ⟨659486, by rfl⟩ : syracuseStep 879315 = 1318973) B1318973
theorem B879331 : Blo 876568 879331 := bstep (se 1 (by rfl) ⟨659498, by rfl⟩ : syracuseStep 879331 = 1318997) B1318997
theorem B879347 : Blo 876568 879347 := bstep (se 1 (by rfl) ⟨659510, by rfl⟩ : syracuseStep 879347 = 1319021) B1319021
theorem B879363 : Blo 876568 879363 := bstep (se 1 (by rfl) ⟨659522, by rfl⟩ : syracuseStep 879363 = 1319045) B1319045
theorem B879379 : Blo 876568 879379 := bstep (se 1 (by rfl) ⟨659534, by rfl⟩ : syracuseStep 879379 = 1319069) B1319069
theorem B879395 : Blo 876568 879395 := bstep (se 1 (by rfl) ⟨659546, by rfl⟩ : syracuseStep 879395 = 1319093) B1319093
theorem B1665841 : Blo 876568 1665841 := bstep (se 2 (by rfl) ⟨624690, by rfl⟩ : syracuseStep 1665841 = 1249381) B1249381
theorem B879411 : Blo 876568 879411 := bstep (se 1 (by rfl) ⟨659558, by rfl⟩ : syracuseStep 879411 = 1319117) B1319117
theorem B879427 : Blo 876568 879427 := bstep (se 1 (by rfl) ⟨659570, by rfl⟩ : syracuseStep 879427 = 1319141) B1319141
theorem B879443 : Blo 876568 879443 := bstep (se 1 (by rfl) ⟨659582, by rfl⟩ : syracuseStep 879443 = 1319165) B1319165
theorem B879459 : Blo 876568 879459 := bstep (se 1 (by rfl) ⟨659594, by rfl⟩ : syracuseStep 879459 = 1319189) B1319189
theorem B879475 : Blo 876568 879475 := bstep (se 1 (by rfl) ⟨659606, by rfl⟩ : syracuseStep 879475 = 1319213) B1319213
theorem B879491 : Blo 876568 879491 := bstep (se 1 (by rfl) ⟨659618, by rfl⟩ : syracuseStep 879491 = 1319237) B1319237
theorem B879507 : Blo 876568 879507 := bstep (se 1 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 879507 = 1319261) B1319261
theorem B879523 : Blo 876568 879523 := bstep (se 1 (by rfl) ⟨659642, by rfl⟩ : syracuseStep 879523 = 1319285) B1319285
theorem B879539 : Blo 876568 879539 := bstep (se 1 (by rfl) ⟨659654, by rfl⟩ : syracuseStep 879539 = 1319309) B1319309
theorem B879555 : Blo 876568 879555 := bstep (se 1 (by rfl) ⟨659666, by rfl⟩ : syracuseStep 879555 = 1319333) B1319333
theorem B2812877 : Blo 876568 2812877 := bstep (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) B1054829
theorem B1666001 : Blo 876568 1666001 := bstep (se 2 (by rfl) ⟨624750, by rfl⟩ : syracuseStep 1666001 = 1249501) B1249501
theorem B879571 : Blo 876568 879571 := bstep (se 1 (by rfl) ⟨659678, by rfl⟩ : syracuseStep 879571 = 1319357) B1319357
theorem B879587 : Blo 876568 879587 := bstep (se 1 (by rfl) ⟨659690, by rfl⟩ : syracuseStep 879587 = 1319381) B1319381
theorem B879603 : Blo 876568 879603 := bstep (se 1 (by rfl) ⟨659702, by rfl⟩ : syracuseStep 879603 = 1319405) B1319405
theorem B879619 : Blo 876568 879619 := bstep (se 1 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 879619 = 1319429) B1319429
theorem B11398157 : Blo 876568 11398157 := bstep (se 3 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 11398157 = 4274309) B4274309
theorem B879635 : Blo 876568 879635 := bstep (se 1 (by rfl) ⟨659726, by rfl⟩ : syracuseStep 879635 = 1319453) B1319453
theorem B879651 : Blo 876568 879651 := bstep (se 1 (by rfl) ⟨659738, by rfl⟩ : syracuseStep 879651 = 1319477) B1319477
theorem B879667 : Blo 876568 879667 := bstep (se 1 (by rfl) ⟨659750, by rfl⟩ : syracuseStep 879667 = 1319501) B1319501
theorem B879683 : Blo 876568 879683 := bstep (se 1 (by rfl) ⟨659762, by rfl⟩ : syracuseStep 879683 = 1319525) B1319525
theorem B879699 : Blo 876568 879699 := bstep (se 1 (by rfl) ⟨659774, by rfl⟩ : syracuseStep 879699 = 1319549) B1319549
theorem B879715 : Blo 876568 879715 := bstep (se 1 (by rfl) ⟨659786, by rfl⟩ : syracuseStep 879715 = 1319573) B1319573
theorem B879731 : Blo 876568 879731 := bstep (se 1 (by rfl) ⟨659798, by rfl⟩ : syracuseStep 879731 = 1319597) B1319597
theorem B879747 : Blo 876568 879747 := bstep (se 1 (by rfl) ⟨659810, by rfl⟩ : syracuseStep 879747 = 1319621) B1319621
theorem B879763 : Blo 876568 879763 := bstep (se 1 (by rfl) ⟨659822, by rfl⟩ : syracuseStep 879763 = 1319645) B1319645
theorem B879779 : Blo 876568 879779 := bstep (se 1 (by rfl) ⟨659834, by rfl⟩ : syracuseStep 879779 = 1319669) B1319669
theorem B3173539 : Blo 876568 3173539 := bstep (se 1 (by rfl) ⟨2380154, by rfl⟩ : syracuseStep 3173539 = 4760309) B4760309
theorem B879795 : Blo 876568 879795 := bstep (se 1 (by rfl) ⟨659846, by rfl⟩ : syracuseStep 879795 = 1319693) B1319693
theorem B879811 : Blo 876568 879811 := bstep (se 1 (by rfl) ⟨659858, by rfl⟩ : syracuseStep 879811 = 1319717) B1319717
theorem B879827 : Blo 876568 879827 := bstep (se 1 (by rfl) ⟨659870, by rfl⟩ : syracuseStep 879827 = 1319741) B1319741
theorem B879843 : Blo 876568 879843 := bstep (se 1 (by rfl) ⟨659882, by rfl⟩ : syracuseStep 879843 = 1319765) B1319765
theorem B879859 : Blo 876568 879859 := bstep (se 1 (by rfl) ⟨659894, by rfl⟩ : syracuseStep 879859 = 1319789) B1319789
theorem B879875 : Blo 876568 879875 := bstep (se 1 (by rfl) ⟨659906, by rfl⟩ : syracuseStep 879875 = 1319813) B1319813
theorem B4451597 : Blo 876568 4451597 := bstep (se 3 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 4451597 = 1669349) B1669349
theorem B879891 : Blo 876568 879891 := bstep (se 1 (by rfl) ⟨659918, by rfl⟩ : syracuseStep 879891 = 1319837) B1319837
theorem B879907 : Blo 876568 879907 := bstep (se 1 (by rfl) ⟨659930, by rfl⟩ : syracuseStep 879907 = 1319861) B1319861
theorem B2223409 : Blo 876568 2223409 := bstep (se 2 (by rfl) ⟨833778, by rfl⟩ : syracuseStep 2223409 = 1667557) B1667557
theorem B879923 : Blo 876568 879923 := bstep (se 1 (by rfl) ⟨659942, by rfl⟩ : syracuseStep 879923 = 1319885) B1319885
theorem B879939 : Blo 876568 879939 := bstep (se 1 (by rfl) ⟨659954, by rfl⟩ : syracuseStep 879939 = 1319909) B1319909
theorem B879955 : Blo 876568 879955 := bstep (se 1 (by rfl) ⟨659966, by rfl⟩ : syracuseStep 879955 = 1319933) B1319933
theorem B1404259 : Blo 876568 1404259 := bstep (se 1 (by rfl) ⟨1053194, by rfl⟩ : syracuseStep 1404259 = 2106389) B2106389
theorem B1666403 : Blo 876568 1666403 := bstep (se 1 (by rfl) ⟨1249802, by rfl⟩ : syracuseStep 1666403 = 2499605) B2499605
theorem B879971 : Blo 876568 879971 := bstep (se 1 (by rfl) ⟨659978, by rfl⟩ : syracuseStep 879971 = 1319957) B1319957
theorem B879987 : Blo 876568 879987 := bstep (se 1 (by rfl) ⟨659990, by rfl⟩ : syracuseStep 879987 = 1319981) B1319981
theorem B880003 : Blo 876568 880003 := bstep (se 1 (by rfl) ⟨660002, by rfl⟩ : syracuseStep 880003 = 1320005) B1320005
theorem B1404305 : Blo 876568 1404305 := bstep (se 2 (by rfl) ⟨526614, by rfl⟩ : syracuseStep 1404305 = 1053229) B1053229
theorem B880019 : Blo 876568 880019 := bstep (se 1 (by rfl) ⟨660014, by rfl⟩ : syracuseStep 880019 = 1320029) B1320029
theorem B880035 : Blo 876568 880035 := bstep (se 1 (by rfl) ⟨660026, by rfl⟩ : syracuseStep 880035 = 1320053) B1320053
theorem B880051 : Blo 876568 880051 := bstep (se 1 (by rfl) ⟨660038, by rfl⟩ : syracuseStep 880051 = 1320077) B1320077
theorem B880067 : Blo 876568 880067 := bstep (se 1 (by rfl) ⟨660050, by rfl⟩ : syracuseStep 880067 = 1320101) B1320101
theorem B880083 : Blo 876568 880083 := bstep (se 1 (by rfl) ⟨660062, by rfl⟩ : syracuseStep 880083 = 1320125) B1320125
theorem B880099 : Blo 876568 880099 := bstep (se 1 (by rfl) ⟨660074, by rfl⟩ : syracuseStep 880099 = 1320149) B1320149
theorem B1338851 : Blo 876568 1338851 := bstep (se 1 (by rfl) ⟨1004138, by rfl⟩ : syracuseStep 1338851 = 2008277) B2008277
theorem B10284529 : Blo 876568 10284529 := bstep (se 2 (by rfl) ⟨3856698, by rfl⟩ : syracuseStep 10284529 = 7713397) B7713397
theorem B880115 : Blo 876568 880115 := bstep (se 1 (by rfl) ⟨660086, by rfl⟩ : syracuseStep 880115 = 1320173) B1320173
theorem B880131 : Blo 876568 880131 := bstep (se 1 (by rfl) ⟨660098, by rfl⟩ : syracuseStep 880131 = 1320197) B1320197
theorem B880147 : Blo 876568 880147 := bstep (se 1 (by rfl) ⟨660110, by rfl⟩ : syracuseStep 880147 = 1320221) B1320221
theorem B880163 : Blo 876568 880163 := bstep (se 1 (by rfl) ⟨660122, by rfl⟩ : syracuseStep 880163 = 1320245) B1320245
theorem B880179 : Blo 876568 880179 := bstep (se 1 (by rfl) ⟨660134, by rfl⟩ : syracuseStep 880179 = 1320269) B1320269
theorem B2223683 : Blo 876568 2223683 := bstep (se 1 (by rfl) ⟨1667762, by rfl⟩ : syracuseStep 2223683 = 3335525) B3335525
theorem B880195 : Blo 876568 880195 := bstep (se 1 (by rfl) ⟨660146, by rfl⟩ : syracuseStep 880195 = 1320293) B1320293
theorem B880211 : Blo 876568 880211 := bstep (se 1 (by rfl) ⟨660158, by rfl⟩ : syracuseStep 880211 = 1320317) B1320317
theorem B880227 : Blo 876568 880227 := bstep (se 1 (by rfl) ⟨660170, by rfl⟩ : syracuseStep 880227 = 1320341) B1320341
theorem B880243 : Blo 876568 880243 := bstep (se 1 (by rfl) ⟨660182, by rfl⟩ : syracuseStep 880243 = 1320365) B1320365
theorem B880259 : Blo 876568 880259 := bstep (se 1 (by rfl) ⟨660194, by rfl⟩ : syracuseStep 880259 = 1320389) B1320389
theorem B880275 : Blo 876568 880275 := bstep (se 1 (by rfl) ⟨660206, by rfl⟩ : syracuseStep 880275 = 1320413) B1320413
theorem B880291 : Blo 876568 880291 := bstep (se 1 (by rfl) ⟨660218, by rfl⟩ : syracuseStep 880291 = 1320437) B1320437
theorem B880307 : Blo 876568 880307 := bstep (se 1 (by rfl) ⟨660230, by rfl⟩ : syracuseStep 880307 = 1320461) B1320461
theorem B880323 : Blo 876568 880323 := bstep (se 1 (by rfl) ⟨660242, by rfl⟩ : syracuseStep 880323 = 1320485) B1320485
theorem B880339 : Blo 876568 880339 := bstep (se 1 (by rfl) ⟨660254, by rfl⟩ : syracuseStep 880339 = 1320509) B1320509
theorem B3337955 : Blo 876568 3337955 := bstep (se 1 (by rfl) ⟨2503466, by rfl⟩ : syracuseStep 3337955 = 5006933) B5006933
theorem B880355 : Blo 876568 880355 := bstep (se 1 (by rfl) ⟨660266, by rfl⟩ : syracuseStep 880355 = 1320533) B1320533
theorem B6942449 : Blo 876568 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B3337969 : Blo 876568 3337969 := bstep (se 2 (by rfl) ⟨1251738, by rfl⟩ : syracuseStep 3337969 = 2503477) B2503477
theorem B1502963 : Blo 876568 1502963 := bstep (se 1 (by rfl) ⟨1127222, by rfl⟩ : syracuseStep 1502963 = 2254445) B2254445
theorem B880371 : Blo 876568 880371 := bstep (se 1 (by rfl) ⟨660278, by rfl⟩ : syracuseStep 880371 = 1320557) B1320557
theorem B2223875 : Blo 876568 2223875 := bstep (se 1 (by rfl) ⟨1667906, by rfl⟩ : syracuseStep 2223875 = 3335813) B3335813
theorem B880387 : Blo 876568 880387 := bstep (se 1 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 880387 = 1320581) B1320581
theorem B880403 : Blo 876568 880403 := bstep (se 1 (by rfl) ⟨660302, by rfl⟩ : syracuseStep 880403 = 1320605) B1320605
theorem B880419 : Blo 876568 880419 := bstep (se 1 (by rfl) ⟨660314, by rfl⟩ : syracuseStep 880419 = 1320629) B1320629
theorem B880435 : Blo 876568 880435 := bstep (se 1 (by rfl) ⟨660326, by rfl⟩ : syracuseStep 880435 = 1320653) B1320653
theorem B880451 : Blo 876568 880451 := bstep (se 1 (by rfl) ⟨660338, by rfl⟩ : syracuseStep 880451 = 1320677) B1320677
theorem B2813773 : Blo 876568 2813773 := bstep (se 3 (by rfl) ⟨527582, by rfl⟩ : syracuseStep 2813773 = 1055165) B1055165
theorem B880467 : Blo 876568 880467 := bstep (se 1 (by rfl) ⟨660350, by rfl⟩ : syracuseStep 880467 = 1320701) B1320701
theorem B880483 : Blo 876568 880483 := bstep (se 1 (by rfl) ⟨660362, by rfl⟩ : syracuseStep 880483 = 1320725) B1320725
theorem B880499 : Blo 876568 880499 := bstep (se 1 (by rfl) ⟨660374, by rfl⟩ : syracuseStep 880499 = 1320749) B1320749
theorem B880515 : Blo 876568 880515 := bstep (se 1 (by rfl) ⟨660386, by rfl⟩ : syracuseStep 880515 = 1320773) B1320773
theorem B880531 : Blo 876568 880531 := bstep (se 1 (by rfl) ⟨660398, by rfl⟩ : syracuseStep 880531 = 1320797) B1320797
theorem B880547 : Blo 876568 880547 := bstep (se 1 (by rfl) ⟨660410, by rfl⟩ : syracuseStep 880547 = 1320821) B1320821
theorem B880563 : Blo 876568 880563 := bstep (se 1 (by rfl) ⟨660422, by rfl⟩ : syracuseStep 880563 = 1320845) B1320845
theorem B1110019 : Blo 876568 1110019 := bstep (se 1 (by rfl) ⟨832514, by rfl⟩ : syracuseStep 1110019 = 1665029) B1665029
theorem B1110115 : Blo 876568 1110115 := bstep (se 1 (by rfl) ⟨832586, by rfl⟩ : syracuseStep 1110115 = 1665173) B1665173
theorem B11235509 : Blo 876568 11235509 := bstep (se 5 (by rfl) ⟨526664, by rfl⟩ : syracuseStep 11235509 = 1053329) B1053329
theorem B1667299 : Blo 876568 1667299 := bstep (se 1 (by rfl) ⟨1250474, by rfl⟩ : syracuseStep 1667299 = 2500949) B2500949
theorem B4878563 : Blo 876568 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B1667459 : Blo 876568 1667459 := bstep (se 1 (by rfl) ⟨1250594, by rfl⟩ : syracuseStep 1667459 = 2501189) B2501189
theorem B5632517 : Blo 876568 5632517 := bstep (se 4 (by rfl) ⟨528048, by rfl⟩ : syracuseStep 5632517 = 1056097) B1056097
theorem B1110611 : Blo 876568 1110611 := bstep (se 1 (by rfl) ⟨832958, by rfl⟩ : syracuseStep 1110611 = 1665917) B1665917
theorem B14217869 : Blo 876568 14217869 := bstep (se 3 (by rfl) ⟨2665850, by rfl⟩ : syracuseStep 14217869 = 5331701) B5331701
theorem B2224817 : Blo 876568 2224817 := bstep (se 2 (by rfl) ⟨834306, by rfl⟩ : syracuseStep 2224817 = 1668613) B1668613
theorem B2814659 : Blo 876568 2814659 := bstep (se 1 (by rfl) ⟨2110994, by rfl⟩ : syracuseStep 2814659 = 4221989) B4221989
theorem B2224867 : Blo 876568 2224867 := bstep (se 1 (by rfl) ⟨1668650, by rfl⟩ : syracuseStep 2224867 = 3337301) B3337301
theorem B1504003 : Blo 876568 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B10023749 : Blo 876568 10023749 := bstep (se 4 (by rfl) ⟨939726, by rfl⟩ : syracuseStep 10023749 = 1879453) B1879453
theorem B2225009 : Blo 876568 2225009 := bstep (se 2 (by rfl) ⟨834378, by rfl⟩ : syracuseStep 2225009 = 1668757) B1668757
theorem B1405811 : Blo 876568 1405811 := bstep (se 1 (by rfl) ⟨1054358, by rfl⟩ : syracuseStep 1405811 = 2108717) B2108717
theorem B1406099 : Blo 876568 1406099 := bstep (se 1 (by rfl) ⟨1054574, by rfl⟩ : syracuseStep 1406099 = 2109149) B2109149
theorem B3339427 : Blo 876568 3339427 := bstep (se 1 (by rfl) ⟨2504570, by rfl⟩ : syracuseStep 3339427 = 5009141) B5009141
theorem B1111315 : Blo 876568 1111315 := bstep (se 1 (by rfl) ⟨833486, by rfl⟩ : syracuseStep 1111315 = 1666973) B1666973
theorem B1111411 : Blo 876568 1111411 := bstep (se 1 (by rfl) ⟨833558, by rfl⟩ : syracuseStep 1111411 = 1667117) B1667117
theorem B1668529 : Blo 876568 1668529 := bstep (se 2 (by rfl) ⟨625698, by rfl⟩ : syracuseStep 1668529 = 1251397) B1251397
theorem B2848241 : Blo 876568 2848241 := bstep (se 2 (by rfl) ⟨1068090, by rfl⟩ : syracuseStep 2848241 = 2136181) B2136181
theorem B2226001 : Blo 876568 2226001 := bstep (se 2 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 2226001 = 1669501) B1669501
theorem B1111907 : Blo 876568 1111907 := bstep (se 1 (by rfl) ⟨833930, by rfl⟩ : syracuseStep 1111907 = 1667861) B1667861
theorem B1406899 : Blo 876568 1406899 := bstep (se 1 (by rfl) ⟨1055174, by rfl⟩ : syracuseStep 1406899 = 2110349) B2110349
theorem B1407041 : Blo 876568 1407041 := bstep (se 2 (by rfl) ⟨527640, by rfl⟩ : syracuseStep 1407041 = 1055281) B1055281
theorem B1407073 : Blo 876568 1407073 := bstep (se 2 (by rfl) ⟨527652, by rfl⟩ : syracuseStep 1407073 = 1055305) B1055305
theorem B2226275 : Blo 876568 2226275 := bstep (se 1 (by rfl) ⟨1669706, by rfl⟩ : syracuseStep 2226275 = 3339413) B3339413
theorem B4454513 : Blo 876568 4454513 := bstep (se 2 (by rfl) ⟨1670442, by rfl⟩ : syracuseStep 4454513 = 3340885) B3340885
theorem B2226467 : Blo 876568 2226467 := bstep (se 1 (by rfl) ⟨1669850, by rfl⟩ : syracuseStep 2226467 = 3339701) B3339701
theorem B1669585 : Blo 876568 1669585 := bstep (se 2 (by rfl) ⟨626094, by rfl⟩ : syracuseStep 1669585 = 1252189) B1252189
theorem B1112611 : Blo 876568 1112611 := bstep (se 1 (by rfl) ⟨834458, by rfl⟩ : syracuseStep 1112611 = 1668917) B1668917
theorem B1505891 : Blo 876568 1505891 := bstep (se 1 (by rfl) ⟨1129418, by rfl⟩ : syracuseStep 1505891 = 2258837) B2258837
theorem B1112707 : Blo 876568 1112707 := bstep (se 1 (by rfl) ⟨834530, by rfl⟩ : syracuseStep 1112707 = 1669061) B1669061
theorem B2816849 : Blo 876568 2816849 := bstep (se 2 (by rfl) ⟨1056318, by rfl⟩ : syracuseStep 2816849 = 2112637) B2112637
theorem B1669987 : Blo 876568 1669987 := bstep (se 1 (by rfl) ⟨1252490, by rfl⟩ : syracuseStep 1669987 = 2504981) B2504981
theorem B1670033 : Blo 876568 1670033 := bstep (se 2 (by rfl) ⟨626262, by rfl⟩ : syracuseStep 1670033 = 1252525) B1252525
theorem B2816977 : Blo 876568 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B1408001 : Blo 876568 1408001 := bstep (se 2 (by rfl) ⟨528000, by rfl⟩ : syracuseStep 1408001 = 1056001) B1056001
theorem B4815877 : Blo 876568 4815877 := bstep (se 4 (by rfl) ⟨451488, by rfl⟩ : syracuseStep 4815877 = 902977) B902977
theorem B4815949 : Blo 876568 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B1113203 : Blo 876568 1113203 := bstep (se 1 (by rfl) ⟨834902, by rfl⟩ : syracuseStep 1113203 = 1669805) B1669805
theorem B1670321 : Blo 876568 1670321 := bstep (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) B1252741
theorem B2817233 : Blo 876568 2817233 := bstep (se 2 (by rfl) ⟨1056462, by rfl⟩ : syracuseStep 2817233 = 2112925) B2112925
theorem B2227409 : Blo 876568 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B2227459 : Blo 876568 2227459 := bstep (se 1 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 2227459 = 3341189) B3341189
theorem B3341645 : Blo 876568 3341645 := bstep (se 3 (by rfl) ⟨626558, by rfl⟩ : syracuseStep 3341645 = 1253117) B1253117
theorem B2227601 : Blo 876568 2227601 := bstep (se 2 (by rfl) ⟨835350, by rfl⟩ : syracuseStep 2227601 = 1670701) B1670701
theorem B4750883 : Blo 876568 4750883 := bstep (se 1 (by rfl) ⟨3563162, by rfl⟩ : syracuseStep 4750883 = 7126325) B7126325
theorem B4455971 : Blo 876568 4455971 := bstep (se 1 (by rfl) ⟨3341978, by rfl⟩ : syracuseStep 4455971 = 6683957) B6683957
theorem B5144141 : Blo 876568 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B5013197 : Blo 876568 5013197 := bstep (se 3 (by rfl) ⟨939974, by rfl⟩ : syracuseStep 5013197 = 1879949) B1879949
theorem B1113907 : Blo 876568 1113907 := bstep (se 1 (by rfl) ⟨835430, by rfl⟩ : syracuseStep 1113907 = 1670861) B1670861
theorem B1408835 : Blo 876568 1408835 := bstep (se 1 (by rfl) ⟨1056626, by rfl⟩ : syracuseStep 1408835 = 2113253) B2113253
theorem B1671043 : Blo 876568 1671043 := bstep (se 1 (by rfl) ⟨1253282, by rfl⟩ : syracuseStep 1671043 = 2506565) B2506565
theorem B1114003 : Blo 876568 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B5636081 : Blo 876568 5636081 := bstep (se 2 (by rfl) ⟨2113530, by rfl⟩ : syracuseStep 5636081 = 4227061) B4227061
theorem B1671347 : Blo 876568 1671347 := bstep (se 1 (by rfl) ⟨1253510, by rfl⟩ : syracuseStep 1671347 = 2507021) B2507021
theorem B1114327 : Blo 876568 1114327 := bstep (se 1 (by rfl) ⟨835745, by rfl⟩ : syracuseStep 1114327 = 1671491) B1671491
theorem B1999243 : Blo 876568 1999243 := bstep (se 1 (by rfl) ⟨1499432, by rfl⟩ : syracuseStep 1999243 = 2998865) B2998865
theorem B13009501 : Blo 876568 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B4227677 : Blo 876568 4227677 := bstep (se 3 (by rfl) ⟨792689, by rfl⟩ : syracuseStep 4227677 = 1585379) B1585379
theorem B1999883 : Blo 876568 1999883 := bstep (se 1 (by rfl) ⟨1499912, by rfl⟩ : syracuseStep 1999883 = 2999825) B2999825
theorem B6685901 : Blo 876568 6685901 := bstep (se 3 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 6685901 = 2507213) B2507213
theorem B951787 : Blo 876568 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B2000513 : Blo 876568 2000513 := bstep (se 2 (by rfl) ⟨750192, by rfl⟩ : syracuseStep 2000513 = 1500385) B1500385
theorem B6686387 : Blo 876568 6686387 := bstep (se 1 (by rfl) ⟨5014790, by rfl⟩ : syracuseStep 6686387 = 10029581) B10029581
theorem B3999563 : Blo 876568 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B5080907 : Blo 876568 5080907 := bstep (se 1 (by rfl) ⟨3810680, by rfl⟩ : syracuseStep 5080907 = 7621361) B7621361
theorem B6850861 : Blo 876568 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B4000529 : Blo 876568 4000529 := bstep (se 2 (by rfl) ⟨1500198, by rfl⟩ : syracuseStep 4000529 = 3000397) B3000397
theorem B1248139 : Blo 876568 1248139 := bstep (se 1 (by rfl) ⟨936104, by rfl⟩ : syracuseStep 1248139 = 1872209) B1872209
theorem B1248151 : Blo 876568 1248151 := bstep (se 1 (by rfl) ⟨936113, by rfl⟩ : syracuseStep 1248151 = 1872227) B1872227
theorem B986251 : Blo 876568 986251 := bstep (se 1 (by rfl) ⟨739688, by rfl⟩ : syracuseStep 986251 = 1479377) B1479377
theorem B986359 : Blo 876568 986359 := bstep (se 1 (by rfl) ⟨739769, by rfl⟩ : syracuseStep 986359 = 1479539) B1479539
theorem B5639489 : Blo 876568 5639489 := bstep (se 2 (by rfl) ⟨2114808, by rfl⟩ : syracuseStep 5639489 = 4229617) B4229617
theorem B986539 : Blo 876568 986539 := bstep (se 1 (by rfl) ⟨739904, by rfl⟩ : syracuseStep 986539 = 1479809) B1479809
theorem B986647 : Blo 876568 986647 := bstep (se 1 (by rfl) ⟨739985, by rfl⟩ : syracuseStep 986647 = 1479971) B1479971
theorem B986827 : Blo 876568 986827 := bstep (se 1 (by rfl) ⟨740120, by rfl⟩ : syracuseStep 986827 = 1480241) B1480241
theorem B986935 : Blo 876568 986935 := bstep (se 1 (by rfl) ⟨740201, by rfl⟩ : syracuseStep 986935 = 1480403) B1480403
theorem B987115 : Blo 876568 987115 := bstep (se 1 (by rfl) ⟨740336, by rfl⟩ : syracuseStep 987115 = 1480673) B1480673
theorem B987223 : Blo 876568 987223 := bstep (se 1 (by rfl) ⟨740417, by rfl⟩ : syracuseStep 987223 = 1480835) B1480835
theorem B1314905 : Blo 876568 1314905 := bstep (se 2 (by rfl) ⟨493089, by rfl⟩ : syracuseStep 1314905 = 986179) B986179
theorem B1315019 : Blo 876568 1315019 := bstep (se 1 (by rfl) ⟨986264, by rfl⟩ : syracuseStep 1315019 = 1972529) B1972529
theorem B1315031 : Blo 876568 1315031 := bstep (se 1 (by rfl) ⟨986273, by rfl⟩ : syracuseStep 1315031 = 1972547) B1972547
theorem B4231385 : Blo 876568 4231385 := bstep (se 2 (by rfl) ⟨1586769, by rfl⟩ : syracuseStep 4231385 = 3173539) B3173539
theorem B987403 : Blo 876568 987403 := bstep (se 1 (by rfl) ⟨740552, by rfl⟩ : syracuseStep 987403 = 1481105) B1481105
theorem B1315097 : Blo 876568 1315097 := bstep (se 2 (by rfl) ⟨493161, by rfl⟩ : syracuseStep 1315097 = 986323) B986323
theorem B987511 : Blo 876568 987511 := bstep (se 1 (by rfl) ⟨740633, by rfl⟩ : syracuseStep 987511 = 1481267) B1481267
theorem B1315211 : Blo 876568 1315211 := bstep (se 1 (by rfl) ⟨986408, by rfl⟩ : syracuseStep 1315211 = 1972817) B1972817
theorem B1315223 : Blo 876568 1315223 := bstep (se 1 (by rfl) ⟨986417, by rfl⟩ : syracuseStep 1315223 = 1972835) B1972835
theorem B1315289 : Blo 876568 1315289 := bstep (se 2 (by rfl) ⟨493233, by rfl⟩ : syracuseStep 1315289 = 986467) B986467
theorem B8458769 : Blo 876568 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B987691 : Blo 876568 987691 := bstep (se 1 (by rfl) ⟨740768, by rfl⟩ : syracuseStep 987691 = 1481537) B1481537
theorem B1315403 : Blo 876568 1315403 := bstep (se 1 (by rfl) ⟨986552, by rfl⟩ : syracuseStep 1315403 = 1973105) B1973105
theorem B1315415 : Blo 876568 1315415 := bstep (se 1 (by rfl) ⟨986561, by rfl⟩ : syracuseStep 1315415 = 1973123) B1973123
theorem B987799 : Blo 876568 987799 := bstep (se 1 (by rfl) ⟨740849, by rfl⟩ : syracuseStep 987799 = 1481699) B1481699
theorem B1315481 : Blo 876568 1315481 := bstep (se 2 (by rfl) ⟨493305, by rfl⟩ : syracuseStep 1315481 = 986611) B986611
theorem B1315595 : Blo 876568 1315595 := bstep (se 1 (by rfl) ⟨986696, by rfl⟩ : syracuseStep 1315595 = 1973393) B1973393
theorem B1315607 : Blo 876568 1315607 := bstep (se 1 (by rfl) ⟨986705, by rfl⟩ : syracuseStep 1315607 = 1973411) B1973411
theorem B987979 : Blo 876568 987979 := bstep (se 1 (by rfl) ⟨740984, by rfl⟩ : syracuseStep 987979 = 1481969) B1481969
theorem B1315673 : Blo 876568 1315673 := bstep (se 2 (by rfl) ⟨493377, by rfl⟩ : syracuseStep 1315673 = 986755) B986755
theorem B5346199 : Blo 876568 5346199 := bstep (se 1 (by rfl) ⟨4009649, by rfl⟩ : syracuseStep 5346199 = 8019299) B8019299
theorem B1250201 : Blo 876568 1250201 := bstep (se 2 (by rfl) ⟨468825, by rfl⟩ : syracuseStep 1250201 = 937651) B937651
theorem B988087 : Blo 876568 988087 := bstep (se 1 (by rfl) ⟨741065, by rfl⟩ : syracuseStep 988087 = 1482131) B1482131
theorem B1315787 : Blo 876568 1315787 := bstep (se 1 (by rfl) ⟨986840, by rfl⟩ : syracuseStep 1315787 = 1973681) B1973681
theorem B1315799 : Blo 876568 1315799 := bstep (se 1 (by rfl) ⟨986849, by rfl⟩ : syracuseStep 1315799 = 1973699) B1973699
theorem B1315865 : Blo 876568 1315865 := bstep (se 2 (by rfl) ⟨493449, by rfl⟩ : syracuseStep 1315865 = 986899) B986899
theorem B1479755 : Blo 876568 1479755 := bstep (se 1 (by rfl) ⟨1109816, by rfl⟩ : syracuseStep 1479755 = 2219633) B2219633
theorem B988267 : Blo 876568 988267 := bstep (se 1 (by rfl) ⟨741200, by rfl⟩ : syracuseStep 988267 = 1482401) B1482401
theorem B1315979 : Blo 876568 1315979 := bstep (se 1 (by rfl) ⟨986984, by rfl⟩ : syracuseStep 1315979 = 1973969) B1973969
theorem B1315991 : Blo 876568 1315991 := bstep (se 1 (by rfl) ⟨986993, by rfl⟩ : syracuseStep 1315991 = 1973987) B1973987
theorem B1479883 : Blo 876568 1479883 := bstep (se 1 (by rfl) ⟨1109912, by rfl⟩ : syracuseStep 1479883 = 2219825) B2219825
theorem B988375 : Blo 876568 988375 := bstep (se 1 (by rfl) ⟨741281, by rfl⟩ : syracuseStep 988375 = 1482563) B1482563
theorem B1316057 : Blo 876568 1316057 := bstep (se 2 (by rfl) ⟨493521, by rfl⟩ : syracuseStep 1316057 = 987043) B987043
theorem B1316171 : Blo 876568 1316171 := bstep (se 1 (by rfl) ⟨987128, by rfl⟩ : syracuseStep 1316171 = 1974257) B1974257
theorem B1316183 : Blo 876568 1316183 := bstep (se 1 (by rfl) ⟨987137, by rfl⟩ : syracuseStep 1316183 = 1974275) B1974275
theorem B1480025 : Blo 876568 1480025 := bstep (se 2 (by rfl) ⟨555009, by rfl⟩ : syracuseStep 1480025 = 1110019) B1110019
theorem B988555 : Blo 876568 988555 := bstep (se 1 (by rfl) ⟨741416, by rfl⟩ : syracuseStep 988555 = 1482833) B1482833
theorem B1316249 : Blo 876568 1316249 := bstep (se 2 (by rfl) ⟨493593, by rfl⟩ : syracuseStep 1316249 = 987187) B987187
theorem B1480153 : Blo 876568 1480153 := bstep (se 2 (by rfl) ⟨555057, by rfl⟩ : syracuseStep 1480153 = 1110115) B1110115
theorem B988663 : Blo 876568 988663 := bstep (se 1 (by rfl) ⟨741497, by rfl⟩ : syracuseStep 988663 = 1482995) B1482995
theorem B1316363 : Blo 876568 1316363 := bstep (se 1 (by rfl) ⟨987272, by rfl⟩ : syracuseStep 1316363 = 1974545) B1974545
theorem B1316375 : Blo 876568 1316375 := bstep (se 1 (by rfl) ⟨987281, by rfl⟩ : syracuseStep 1316375 = 1974563) B1974563
theorem B1250839 : Blo 876568 1250839 := bstep (se 1 (by rfl) ⟨938129, by rfl⟩ : syracuseStep 1250839 = 1876259) B1876259
theorem B10688075 : Blo 876568 10688075 := bstep (se 1 (by rfl) ⟨8016056, by rfl⟩ : syracuseStep 10688075 = 16032113) B16032113
theorem B1316441 : Blo 876568 1316441 := bstep (se 2 (by rfl) ⟨493665, by rfl⟩ : syracuseStep 1316441 = 987331) B987331
theorem B988843 : Blo 876568 988843 := bstep (se 1 (by rfl) ⟨741632, by rfl⟩ : syracuseStep 988843 = 1483265) B1483265
theorem B6657713 : Blo 876568 6657713 := bstep (se 2 (by rfl) ⟨2496642, by rfl⟩ : syracuseStep 6657713 = 4993285) B4993285
theorem B1316555 : Blo 876568 1316555 := bstep (se 1 (by rfl) ⟨987416, by rfl⟩ : syracuseStep 1316555 = 1974833) B1974833
theorem B1316567 : Blo 876568 1316567 := bstep (se 1 (by rfl) ⟨987425, by rfl⟩ : syracuseStep 1316567 = 1974851) B1974851
theorem B988951 : Blo 876568 988951 := bstep (se 1 (by rfl) ⟨741713, by rfl⟩ : syracuseStep 988951 = 1483427) B1483427
theorem B1316633 : Blo 876568 1316633 := bstep (se 2 (by rfl) ⟨493737, by rfl⟩ : syracuseStep 1316633 = 987475) B987475
theorem B7116589 : Blo 876568 7116589 := bstep (se 3 (by rfl) ⟨1334360, by rfl⟩ : syracuseStep 7116589 = 2668721) B2668721
theorem B1316747 : Blo 876568 1316747 := bstep (se 1 (by rfl) ⟨987560, by rfl⟩ : syracuseStep 1316747 = 1975121) B1975121
theorem B1316759 : Blo 876568 1316759 := bstep (se 1 (by rfl) ⟨987569, by rfl⟩ : syracuseStep 1316759 = 1975139) B1975139
theorem B11409329 : Blo 876568 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B1873867 : Blo 876568 1873867 := bstep (se 1 (by rfl) ⟨1405400, by rfl⟩ : syracuseStep 1873867 = 2810801) B2810801
theorem B989131 : Blo 876568 989131 := bstep (se 1 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 989131 = 1483697) B1483697
theorem B890839 : Blo 876568 890839 := bstep (se 1 (by rfl) ⟨668129, by rfl⟩ : syracuseStep 890839 = 1336259) B1336259
theorem B1316825 : Blo 876568 1316825 := bstep (se 2 (by rfl) ⟨493809, by rfl⟩ : syracuseStep 1316825 = 987619) B987619
theorem B1480727 : Blo 876568 1480727 := bstep (se 1 (by rfl) ⟨1110545, by rfl⟩ : syracuseStep 1480727 = 2221091) B2221091
theorem B989239 : Blo 876568 989239 := bstep (se 1 (by rfl) ⟨741929, by rfl⟩ : syracuseStep 989239 = 1483859) B1483859
theorem B1316939 : Blo 876568 1316939 := bstep (se 1 (by rfl) ⟨987704, by rfl⟩ : syracuseStep 1316939 = 1975409) B1975409
theorem B1316951 : Blo 876568 1316951 := bstep (se 1 (by rfl) ⟨987713, by rfl⟩ : syracuseStep 1316951 = 1975427) B1975427
theorem B1972313 : Blo 876568 1972313 := bstep (se 2 (by rfl) ⟨739617, by rfl⟩ : syracuseStep 1972313 = 1479235) B1479235
theorem B6330469 : Blo 876568 6330469 := bstep (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) B1186963
theorem B6658199 : Blo 876568 6658199 := bstep (se 1 (by rfl) ⟨4993649, by rfl⟩ : syracuseStep 6658199 = 9987299) B9987299
theorem B1480855 : Blo 876568 1480855 := bstep (se 1 (by rfl) ⟨1110641, by rfl⟩ : syracuseStep 1480855 = 2221283) B2221283
theorem B1317017 : Blo 876568 1317017 := bstep (se 2 (by rfl) ⟨493881, by rfl⟩ : syracuseStep 1317017 = 987763) B987763
theorem B1972403 : Blo 876568 1972403 := bstep (se 1 (by rfl) ⟨1479302, by rfl⟩ : syracuseStep 1972403 = 2958605) B2958605
theorem B1972439 : Blo 876568 1972439 := bstep (se 1 (by rfl) ⟨1479329, by rfl⟩ : syracuseStep 1972439 = 2958659) B2958659
theorem B989419 : Blo 876568 989419 := bstep (se 1 (by rfl) ⟨742064, by rfl⟩ : syracuseStep 989419 = 1484129) B1484129
theorem B1317131 : Blo 876568 1317131 := bstep (se 1 (by rfl) ⟨987848, by rfl⟩ : syracuseStep 1317131 = 1975697) B1975697
theorem B1317143 : Blo 876568 1317143 := bstep (se 1 (by rfl) ⟨987857, by rfl⟩ : syracuseStep 1317143 = 1975715) B1975715
theorem B1251659 : Blo 876568 1251659 := bstep (se 1 (by rfl) ⟨938744, by rfl⟩ : syracuseStep 1251659 = 1877489) B1877489
theorem B989527 : Blo 876568 989527 := bstep (se 1 (by rfl) ⟨742145, by rfl⟩ : syracuseStep 989527 = 1484291) B1484291
theorem B1317209 : Blo 876568 1317209 := bstep (se 2 (by rfl) ⟨493953, by rfl⟩ : syracuseStep 1317209 = 987907) B987907
theorem B2005337 : Blo 876568 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B1972619 : Blo 876568 1972619 := bstep (se 1 (by rfl) ⟨1479464, by rfl⟩ : syracuseStep 1972619 = 2958929) B2958929
theorem B1972673 : Blo 876568 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B1317323 : Blo 876568 1317323 := bstep (se 1 (by rfl) ⟨987992, by rfl⟩ : syracuseStep 1317323 = 1975985) B1975985
theorem B1317335 : Blo 876568 1317335 := bstep (se 1 (by rfl) ⟨988001, by rfl⟩ : syracuseStep 1317335 = 1976003) B1976003
theorem B989707 : Blo 876568 989707 := bstep (se 1 (by rfl) ⟨742280, by rfl⟩ : syracuseStep 989707 = 1484561) B1484561
theorem B1317401 : Blo 876568 1317401 := bstep (se 2 (by rfl) ⟨494025, by rfl⟩ : syracuseStep 1317401 = 988051) B988051
theorem B2005555 : Blo 876568 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B989815 : Blo 876568 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B1317515 : Blo 876568 1317515 := bstep (se 1 (by rfl) ⟨988136, by rfl⟩ : syracuseStep 1317515 = 1976273) B1976273
theorem B1317527 : Blo 876568 1317527 := bstep (se 1 (by rfl) ⟨988145, by rfl⟩ : syracuseStep 1317527 = 1976291) B1976291
theorem B1972889 : Blo 876568 1972889 := bstep (se 2 (by rfl) ⟨739833, by rfl⟩ : syracuseStep 1972889 = 1479667) B1479667
theorem B1317593 : Blo 876568 1317593 := bstep (se 2 (by rfl) ⟨494097, by rfl⟩ : syracuseStep 1317593 = 988195) B988195
theorem B1972979 : Blo 876568 1972979 := bstep (se 1 (by rfl) ⟨1479734, by rfl⟩ : syracuseStep 1972979 = 2959469) B2959469
theorem B1481483 : Blo 876568 1481483 := bstep (se 1 (by rfl) ⟨1111112, by rfl⟩ : syracuseStep 1481483 = 2222225) B2222225
theorem B1973015 : Blo 876568 1973015 := bstep (se 1 (by rfl) ⟨1479761, by rfl⟩ : syracuseStep 1973015 = 2959523) B2959523
theorem B989995 : Blo 876568 989995 := bstep (se 1 (by rfl) ⟨742496, by rfl⟩ : syracuseStep 989995 = 1484993) B1484993
theorem B57744193 : Blo 876568 57744193 := bstep (se 2 (by rfl) ⟨21654072, by rfl⟩ : syracuseStep 57744193 = 43308145) B43308145
theorem B1317707 : Blo 876568 1317707 := bstep (se 1 (by rfl) ⟨988280, by rfl⟩ : syracuseStep 1317707 = 1976561) B1976561
theorem B1317719 : Blo 876568 1317719 := bstep (se 1 (by rfl) ⟨988289, by rfl⟩ : syracuseStep 1317719 = 1976579) B1976579
theorem B2005847 : Blo 876568 2005847 := bstep (se 1 (by rfl) ⟨1504385, by rfl⟩ : syracuseStep 2005847 = 3008771) B3008771
theorem B1481611 : Blo 876568 1481611 := bstep (se 1 (by rfl) ⟨1111208, by rfl⟩ : syracuseStep 1481611 = 2222417) B2222417
theorem B990103 : Blo 876568 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B1317785 : Blo 876568 1317785 := bstep (se 2 (by rfl) ⟨494169, by rfl⟩ : syracuseStep 1317785 = 988339) B988339
theorem B1973195 : Blo 876568 1973195 := bstep (se 1 (by rfl) ⟨1479896, by rfl⟩ : syracuseStep 1973195 = 2959793) B2959793
theorem B1973249 : Blo 876568 1973249 := bstep (se 2 (by rfl) ⟨739968, by rfl⟩ : syracuseStep 1973249 = 1479937) B1479937
theorem B1317899 : Blo 876568 1317899 := bstep (se 1 (by rfl) ⟨988424, by rfl⟩ : syracuseStep 1317899 = 1976849) B1976849
theorem B1317911 : Blo 876568 1317911 := bstep (se 1 (by rfl) ⟨988433, by rfl⟩ : syracuseStep 1317911 = 1976867) B1976867
theorem B1481753 : Blo 876568 1481753 := bstep (se 2 (by rfl) ⟨555657, by rfl⟩ : syracuseStep 1481753 = 1111315) B1111315
theorem B990283 : Blo 876568 990283 := bstep (se 1 (by rfl) ⟨742712, by rfl⟩ : syracuseStep 990283 = 1485425) B1485425
theorem B1317977 : Blo 876568 1317977 := bstep (se 2 (by rfl) ⟨494241, by rfl⟩ : syracuseStep 1317977 = 988483) B988483
theorem B1481881 : Blo 876568 1481881 := bstep (se 2 (by rfl) ⟨555705, by rfl⟩ : syracuseStep 1481881 = 1111411) B1111411
theorem B990391 : Blo 876568 990391 := bstep (se 1 (by rfl) ⟨742793, by rfl⟩ : syracuseStep 990391 = 1485587) B1485587
theorem B1318091 : Blo 876568 1318091 := bstep (se 1 (by rfl) ⟨988568, by rfl⟩ : syracuseStep 1318091 = 1977137) B1977137
theorem B1318103 : Blo 876568 1318103 := bstep (se 1 (by rfl) ⟨988577, by rfl⟩ : syracuseStep 1318103 = 1977155) B1977155
theorem B1973465 : Blo 876568 1973465 := bstep (se 2 (by rfl) ⟨740049, by rfl⟩ : syracuseStep 1973465 = 1480099) B1480099
theorem B1580311 : Blo 876568 1580311 := bstep (se 1 (by rfl) ⟨1185233, by rfl⟩ : syracuseStep 1580311 = 2370467) B2370467
theorem B1318169 : Blo 876568 1318169 := bstep (se 2 (by rfl) ⟨494313, by rfl⟩ : syracuseStep 1318169 = 988627) B988627
theorem B1973555 : Blo 876568 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B1875251 : Blo 876568 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B1973591 : Blo 876568 1973591 := bstep (se 1 (by rfl) ⟨1480193, by rfl⟩ : syracuseStep 1973591 = 2960387) B2960387
theorem B990571 : Blo 876568 990571 := bstep (se 1 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 990571 = 1485857) B1485857
theorem B1318283 : Blo 876568 1318283 := bstep (se 1 (by rfl) ⟨988712, by rfl⟩ : syracuseStep 1318283 = 1977425) B1977425
theorem B1318295 : Blo 876568 1318295 := bstep (se 1 (by rfl) ⟨988721, by rfl⟩ : syracuseStep 1318295 = 1977443) B1977443
theorem B1318361 : Blo 876568 1318361 := bstep (se 2 (by rfl) ⟨494385, by rfl⟩ : syracuseStep 1318361 = 988771) B988771
theorem B1973771 : Blo 876568 1973771 := bstep (se 1 (by rfl) ⟨1480328, by rfl⟩ : syracuseStep 1973771 = 2960657) B2960657
theorem B1973825 : Blo 876568 1973825 := bstep (se 2 (by rfl) ⟨740184, by rfl⟩ : syracuseStep 1973825 = 1480369) B1480369
theorem B1318475 : Blo 876568 1318475 := bstep (se 1 (by rfl) ⟨988856, by rfl⟩ : syracuseStep 1318475 = 1977713) B1977713
theorem B1318487 : Blo 876568 1318487 := bstep (se 1 (by rfl) ⟨988865, by rfl⟩ : syracuseStep 1318487 = 1977731) B1977731
theorem B892567 : Blo 876568 892567 := bstep (se 1 (by rfl) ⟨669425, by rfl⟩ : syracuseStep 892567 = 1338851) B1338851
theorem B1318553 : Blo 876568 1318553 := bstep (se 2 (by rfl) ⟨494457, by rfl⟩ : syracuseStep 1318553 = 988915) B988915
theorem B1777331 : Blo 876568 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B36052685 : Blo 876568 36052685 := bstep (se 3 (by rfl) ⟨6759878, by rfl⟩ : syracuseStep 36052685 = 13519757) B13519757
theorem B1482455 : Blo 876568 1482455 := bstep (se 1 (by rfl) ⟨1111841, by rfl⟩ : syracuseStep 1482455 = 2223683) B2223683
theorem B1318667 : Blo 876568 1318667 := bstep (se 1 (by rfl) ⟨989000, by rfl⟩ : syracuseStep 1318667 = 1978001) B1978001
theorem B1318679 : Blo 876568 1318679 := bstep (se 1 (by rfl) ⟨989009, by rfl⟩ : syracuseStep 1318679 = 1978019) B1978019
theorem B1974041 : Blo 876568 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B1482583 : Blo 876568 1482583 := bstep (se 1 (by rfl) ⟨1111937, by rfl⟩ : syracuseStep 1482583 = 2223875) B2223875
theorem B1318745 : Blo 876568 1318745 := bstep (se 2 (by rfl) ⟨494529, by rfl⟩ : syracuseStep 1318745 = 989059) B989059
theorem B7610213 : Blo 876568 7610213 := bstep (se 4 (by rfl) ⟨713457, by rfl⟩ : syracuseStep 7610213 = 1426915) B1426915
theorem B1974131 : Blo 876568 1974131 := bstep (se 1 (by rfl) ⟨1480598, by rfl⟩ : syracuseStep 1974131 = 2961197) B2961197
theorem B1974167 : Blo 876568 1974167 := bstep (se 1 (by rfl) ⟨1480625, by rfl⟩ : syracuseStep 1974167 = 2961251) B2961251
theorem B15998897 : Blo 876568 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B1318859 : Blo 876568 1318859 := bstep (se 1 (by rfl) ⟨989144, by rfl⟩ : syracuseStep 1318859 = 1978289) B1978289
theorem B1318871 : Blo 876568 1318871 := bstep (se 1 (by rfl) ⟨989153, by rfl⟩ : syracuseStep 1318871 = 1978307) B1978307
theorem B9510929 : Blo 876568 9510929 := bstep (se 2 (by rfl) ⟨3566598, by rfl⟩ : syracuseStep 9510929 = 7133197) B7133197
theorem B1318937 : Blo 876568 1318937 := bstep (se 2 (by rfl) ⟨494601, by rfl⟩ : syracuseStep 1318937 = 989203) B989203
theorem B1974347 : Blo 876568 1974347 := bstep (se 1 (by rfl) ⟨1480760, by rfl⟩ : syracuseStep 1974347 = 2961521) B2961521
theorem B1974401 : Blo 876568 1974401 := bstep (se 2 (by rfl) ⟨740400, by rfl⟩ : syracuseStep 1974401 = 1480801) B1480801
theorem B1876097 : Blo 876568 1876097 := bstep (se 2 (by rfl) ⟨703536, by rfl⟩ : syracuseStep 1876097 = 1407073) B1407073
theorem B1319051 : Blo 876568 1319051 := bstep (se 1 (by rfl) ⟨989288, by rfl⟩ : syracuseStep 1319051 = 1978577) B1978577
theorem B1319063 : Blo 876568 1319063 := bstep (se 1 (by rfl) ⟨989297, by rfl⟩ : syracuseStep 1319063 = 1978595) B1978595
theorem B1319129 : Blo 876568 1319129 := bstep (se 2 (by rfl) ⟨494673, by rfl⟩ : syracuseStep 1319129 = 989347) B989347
theorem B2859229 : Blo 876568 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B1319243 : Blo 876568 1319243 := bstep (se 1 (by rfl) ⟨989432, by rfl⟩ : syracuseStep 1319243 = 1978865) B1978865
theorem B1319255 : Blo 876568 1319255 := bstep (se 1 (by rfl) ⟨989441, by rfl⟩ : syracuseStep 1319255 = 1978883) B1978883
theorem B1974617 : Blo 876568 1974617 := bstep (se 2 (by rfl) ⟨740481, by rfl⟩ : syracuseStep 1974617 = 1480963) B1480963
theorem B1319321 : Blo 876568 1319321 := bstep (se 2 (by rfl) ⟨494745, by rfl⟩ : syracuseStep 1319321 = 989491) B989491
theorem B9478579 : Blo 876568 9478579 := bstep (se 1 (by rfl) ⟨7108934, by rfl⟩ : syracuseStep 9478579 = 14217869) B14217869
theorem B1974707 : Blo 876568 1974707 := bstep (se 1 (by rfl) ⟨1481030, by rfl⟩ : syracuseStep 1974707 = 2962061) B2962061
theorem B1483211 : Blo 876568 1483211 := bstep (se 1 (by rfl) ⟨1112408, by rfl⟩ : syracuseStep 1483211 = 2224817) B2224817
theorem B1974743 : Blo 876568 1974743 := bstep (se 1 (by rfl) ⟨1481057, by rfl⟩ : syracuseStep 1974743 = 2962115) B2962115
theorem B1876439 : Blo 876568 1876439 := bstep (se 1 (by rfl) ⟨1407329, by rfl⟩ : syracuseStep 1876439 = 2814659) B2814659
theorem B1319435 : Blo 876568 1319435 := bstep (se 1 (by rfl) ⟨989576, by rfl⟩ : syracuseStep 1319435 = 1979153) B1979153
theorem B1319447 : Blo 876568 1319447 := bstep (se 1 (by rfl) ⟨989585, by rfl⟩ : syracuseStep 1319447 = 1979171) B1979171
theorem B1483339 : Blo 876568 1483339 := bstep (se 1 (by rfl) ⟨1112504, by rfl⟩ : syracuseStep 1483339 = 2225009) B2225009
theorem B1319513 : Blo 876568 1319513 := bstep (se 2 (by rfl) ⟨494817, by rfl⟩ : syracuseStep 1319513 = 989635) B989635
theorem B1974923 : Blo 876568 1974923 := bstep (se 1 (by rfl) ⟨1481192, by rfl⟩ : syracuseStep 1974923 = 2962385) B2962385
theorem B1974977 : Blo 876568 1974977 := bstep (se 2 (by rfl) ⟨740616, by rfl⟩ : syracuseStep 1974977 = 1481233) B1481233
theorem B2499275 : Blo 876568 2499275 := bstep (se 1 (by rfl) ⟨1874456, by rfl⟩ : syracuseStep 2499275 = 3748913) B3748913
theorem B1319627 : Blo 876568 1319627 := bstep (se 1 (by rfl) ⟨989720, by rfl⟩ : syracuseStep 1319627 = 1979441) B1979441
theorem B1319639 : Blo 876568 1319639 := bstep (se 1 (by rfl) ⟨989729, by rfl⟩ : syracuseStep 1319639 = 1979459) B1979459
theorem B1483481 : Blo 876568 1483481 := bstep (se 2 (by rfl) ⟨556305, by rfl⟩ : syracuseStep 1483481 = 1112611) B1112611
theorem B1319705 : Blo 876568 1319705 := bstep (se 2 (by rfl) ⟨494889, by rfl⟩ : syracuseStep 1319705 = 989779) B989779
theorem B1483609 : Blo 876568 1483609 := bstep (se 2 (by rfl) ⟨556353, by rfl⟩ : syracuseStep 1483609 = 1112707) B1112707
theorem B1319819 : Blo 876568 1319819 := bstep (se 1 (by rfl) ⟨989864, by rfl⟩ : syracuseStep 1319819 = 1979729) B1979729
theorem B1319831 : Blo 876568 1319831 := bstep (se 1 (by rfl) ⟨989873, by rfl⟩ : syracuseStep 1319831 = 1979747) B1979747
theorem B1975193 : Blo 876568 1975193 := bstep (se 2 (by rfl) ⟨740697, by rfl⟩ : syracuseStep 1975193 = 1481395) B1481395
theorem B1319897 : Blo 876568 1319897 := bstep (se 2 (by rfl) ⟨494961, by rfl⟩ : syracuseStep 1319897 = 989923) B989923
theorem B1975283 : Blo 876568 1975283 := bstep (se 1 (by rfl) ⟨1481462, by rfl⟩ : syracuseStep 1975283 = 2962925) B2962925
theorem B1975319 : Blo 876568 1975319 := bstep (se 1 (by rfl) ⟨1481489, by rfl⟩ : syracuseStep 1975319 = 2962979) B2962979
theorem B1778753 : Blo 876568 1778753 := bstep (se 2 (by rfl) ⟨667032, by rfl⟩ : syracuseStep 1778753 = 1334065) B1334065
theorem B1320011 : Blo 876568 1320011 := bstep (se 1 (by rfl) ⟨990008, by rfl⟩ : syracuseStep 1320011 = 1980017) B1980017
theorem B1320023 : Blo 876568 1320023 := bstep (se 1 (by rfl) ⟨990017, by rfl⟩ : syracuseStep 1320023 = 1980035) B1980035
theorem B2499673 : Blo 876568 2499673 := bstep (se 2 (by rfl) ⟨937377, by rfl⟩ : syracuseStep 2499673 = 1874755) B1874755
theorem B1320089 : Blo 876568 1320089 := bstep (se 2 (by rfl) ⟨495033, by rfl⟩ : syracuseStep 1320089 = 990067) B990067
theorem B1975499 : Blo 876568 1975499 := bstep (se 1 (by rfl) ⟨1481624, by rfl⟩ : syracuseStep 1975499 = 2963249) B2963249
theorem B1975553 : Blo 876568 1975553 := bstep (se 2 (by rfl) ⟨740832, by rfl⟩ : syracuseStep 1975553 = 1481665) B1481665
theorem B1320203 : Blo 876568 1320203 := bstep (se 1 (by rfl) ⟨990152, by rfl⟩ : syracuseStep 1320203 = 1980305) B1980305
theorem B1320215 : Blo 876568 1320215 := bstep (se 1 (by rfl) ⟨990161, by rfl⟩ : syracuseStep 1320215 = 1980323) B1980323
theorem B1189207 : Blo 876568 1189207 := bstep (se 1 (by rfl) ⟨891905, by rfl⟩ : syracuseStep 1189207 = 1783811) B1783811
theorem B1320281 : Blo 876568 1320281 := bstep (se 2 (by rfl) ⟨495105, by rfl⟩ : syracuseStep 1320281 = 990211) B990211
theorem B1484183 : Blo 876568 1484183 := bstep (se 1 (by rfl) ⟨1113137, by rfl⟩ : syracuseStep 1484183 = 2226275) B2226275
theorem B1320395 : Blo 876568 1320395 := bstep (se 1 (by rfl) ⟨990296, by rfl⟩ : syracuseStep 1320395 = 1980593) B1980593
theorem B1320407 : Blo 876568 1320407 := bstep (se 1 (by rfl) ⟨990305, by rfl⟩ : syracuseStep 1320407 = 1980611) B1980611
theorem B1975769 : Blo 876568 1975769 := bstep (se 2 (by rfl) ⟨740913, by rfl⟩ : syracuseStep 1975769 = 1481827) B1481827
theorem B1484311 : Blo 876568 1484311 := bstep (se 1 (by rfl) ⟨1113233, by rfl⟩ : syracuseStep 1484311 = 2226467) B2226467
theorem B1320473 : Blo 876568 1320473 := bstep (se 2 (by rfl) ⟨495177, by rfl⟩ : syracuseStep 1320473 = 990355) B990355
theorem B1975859 : Blo 876568 1975859 := bstep (se 1 (by rfl) ⟨1481894, by rfl⟩ : syracuseStep 1975859 = 2963789) B2963789
theorem B1189451 : Blo 876568 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B1975895 : Blo 876568 1975895 := bstep (se 1 (by rfl) ⟨1481921, by rfl⟩ : syracuseStep 1975895 = 2963843) B2963843
theorem B1320587 : Blo 876568 1320587 := bstep (se 1 (by rfl) ⟨990440, by rfl⟩ : syracuseStep 1320587 = 1980881) B1980881
theorem B1320599 : Blo 876568 1320599 := bstep (se 1 (by rfl) ⟨990449, by rfl⟩ : syracuseStep 1320599 = 1980899) B1980899
theorem B2107073 : Blo 876568 2107073 := bstep (se 2 (by rfl) ⟨790152, by rfl⟩ : syracuseStep 2107073 = 1580305) B1580305
theorem B1320665 : Blo 876568 1320665 := bstep (se 2 (by rfl) ⟨495249, by rfl⟩ : syracuseStep 1320665 = 990499) B990499
theorem B1976075 : Blo 876568 1976075 := bstep (se 1 (by rfl) ⟨1482056, by rfl⟩ : syracuseStep 1976075 = 2964113) B2964113
theorem B1976129 : Blo 876568 1976129 := bstep (se 2 (by rfl) ⟨741048, by rfl⟩ : syracuseStep 1976129 = 1482097) B1482097
theorem B1320779 : Blo 876568 1320779 := bstep (se 1 (by rfl) ⟨990584, by rfl⟩ : syracuseStep 1320779 = 1981169) B1981169
theorem B1320791 : Blo 876568 1320791 := bstep (se 1 (by rfl) ⟨990593, by rfl⟩ : syracuseStep 1320791 = 1981187) B1981187
theorem B1877899 : Blo 876568 1877899 := bstep (se 1 (by rfl) ⟨1408424, by rfl⟩ : syracuseStep 1877899 = 2816849) B2816849
theorem B2959307 : Blo 876568 2959307 := bstep (se 1 (by rfl) ⟨2219480, by rfl⟩ : syracuseStep 2959307 = 4438961) B4438961
theorem B1779659 : Blo 876568 1779659 := bstep (se 1 (by rfl) ⟨1334744, by rfl⟩ : syracuseStep 1779659 = 2669489) B2669489
theorem B1976345 : Blo 876568 1976345 := bstep (se 2 (by rfl) ⟨741129, by rfl⟩ : syracuseStep 1976345 = 1482259) B1482259
theorem B1976435 : Blo 876568 1976435 := bstep (se 1 (by rfl) ⟨1482326, by rfl⟩ : syracuseStep 1976435 = 2964653) B2964653
theorem B1878155 : Blo 876568 1878155 := bstep (se 1 (by rfl) ⟨1408616, by rfl⟩ : syracuseStep 1878155 = 2817233) B2817233
theorem B1484939 : Blo 876568 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B1976471 : Blo 876568 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B2959577 : Blo 876568 2959577 := bstep (se 2 (by rfl) ⟨1109841, by rfl⟩ : syracuseStep 2959577 = 2219683) B2219683
theorem B1485067 : Blo 876568 1485067 := bstep (se 1 (by rfl) ⟨1113800, by rfl⟩ : syracuseStep 1485067 = 2227601) B2227601
theorem B1583383 : Blo 876568 1583383 := bstep (se 1 (by rfl) ⟨1187537, by rfl⟩ : syracuseStep 1583383 = 2375075) B2375075
theorem B2500915 : Blo 876568 2500915 := bstep (se 1 (by rfl) ⟨1875686, by rfl⟩ : syracuseStep 2500915 = 3751373) B3751373
theorem B1976651 : Blo 876568 1976651 := bstep (se 1 (by rfl) ⟨1482488, by rfl⟩ : syracuseStep 1976651 = 2964977) B2964977
theorem B1976705 : Blo 876568 1976705 := bstep (se 2 (by rfl) ⟨741264, by rfl⟩ : syracuseStep 1976705 = 1482529) B1482529
theorem B1485209 : Blo 876568 1485209 := bstep (se 2 (by rfl) ⟨556953, by rfl⟩ : syracuseStep 1485209 = 1113907) B1113907
theorem B928171 : Blo 876568 928171 := bstep (se 1 (by rfl) ⟨696128, by rfl⟩ : syracuseStep 928171 = 1392257) B1392257
theorem B1485337 : Blo 876568 1485337 := bstep (se 2 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 1485337 = 1114003) B1114003
theorem B1976921 : Blo 876568 1976921 := bstep (se 2 (by rfl) ⟨741345, by rfl⟩ : syracuseStep 1976921 = 1482691) B1482691
theorem B1977011 : Blo 876568 1977011 := bstep (se 1 (by rfl) ⟨1482758, by rfl⟩ : syracuseStep 1977011 = 2965517) B2965517
theorem B1977047 : Blo 876568 1977047 := bstep (se 1 (by rfl) ⟨1482785, by rfl⟩ : syracuseStep 1977047 = 2965571) B2965571
theorem B1977227 : Blo 876568 1977227 := bstep (se 1 (by rfl) ⟨1482920, by rfl⟩ : syracuseStep 1977227 = 2965841) B2965841
theorem B2960279 : Blo 876568 2960279 := bstep (se 1 (by rfl) ⟨2220209, by rfl⟩ : syracuseStep 2960279 = 4440419) B4440419
theorem B3386285 : Blo 876568 3386285 := bstep (se 3 (by rfl) ⟨634928, by rfl⟩ : syracuseStep 3386285 = 1269857) B1269857
theorem B1977281 : Blo 876568 1977281 := bstep (se 2 (by rfl) ⟨741480, by rfl⟩ : syracuseStep 1977281 = 1482961) B1482961
theorem B9743435 : Blo 876568 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B1485911 : Blo 876568 1485911 := bstep (se 1 (by rfl) ⟨1114433, by rfl⟩ : syracuseStep 1485911 = 2228867) B2228867
theorem B1879129 : Blo 876568 1879129 := bstep (se 2 (by rfl) ⟨704673, by rfl⟩ : syracuseStep 1879129 = 1409347) B1409347
theorem B4009105 : Blo 876568 4009105 := bstep (se 2 (by rfl) ⟨1503414, by rfl⟩ : syracuseStep 4009105 = 3006829) B3006829
theorem B1977497 : Blo 876568 1977497 := bstep (se 2 (by rfl) ⟨741561, by rfl⟩ : syracuseStep 1977497 = 1483123) B1483123
theorem B2141363 : Blo 876568 2141363 := bstep (se 1 (by rfl) ⟨1606022, by rfl⟩ : syracuseStep 2141363 = 3212045) B3212045
theorem B1977587 : Blo 876568 1977587 := bstep (se 1 (by rfl) ⟨1483190, by rfl⟩ : syracuseStep 1977587 = 2966381) B2966381
theorem B1879283 : Blo 876568 1879283 := bstep (se 1 (by rfl) ⟨1409462, by rfl⟩ : syracuseStep 1879283 = 2818925) B2818925
theorem B1977623 : Blo 876568 1977623 := bstep (se 1 (by rfl) ⟨1483217, by rfl⟩ : syracuseStep 1977623 = 2966435) B2966435
theorem B2960819 : Blo 876568 2960819 := bstep (se 1 (by rfl) ⟨2220614, by rfl⟩ : syracuseStep 2960819 = 4441229) B4441229
theorem B1977803 : Blo 876568 1977803 := bstep (se 1 (by rfl) ⟨1483352, by rfl⟩ : syracuseStep 1977803 = 2966705) B2966705
theorem B1977857 : Blo 876568 1977857 := bstep (se 2 (by rfl) ⟨741696, by rfl⟩ : syracuseStep 1977857 = 1483393) B1483393
theorem B2961089 : Blo 876568 2961089 := bstep (se 2 (by rfl) ⟨1110408, by rfl⟩ : syracuseStep 2961089 = 2220817) B2220817
theorem B1978073 : Blo 876568 1978073 := bstep (se 2 (by rfl) ⟨741777, by rfl⟩ : syracuseStep 1978073 = 1483555) B1483555
theorem B1879795 : Blo 876568 1879795 := bstep (se 1 (by rfl) ⟨1409846, by rfl⟩ : syracuseStep 1879795 = 2819693) B2819693
theorem B4992785 : Blo 876568 4992785 := bstep (se 2 (by rfl) ⟨1872294, by rfl⟩ : syracuseStep 4992785 = 3744589) B3744589
theorem B1978163 : Blo 876568 1978163 := bstep (se 1 (by rfl) ⟨1483622, by rfl⟩ : syracuseStep 1978163 = 2967245) B2967245
theorem B1978199 : Blo 876568 1978199 := bstep (se 1 (by rfl) ⟨1483649, by rfl⟩ : syracuseStep 1978199 = 2967299) B2967299
theorem B1978379 : Blo 876568 1978379 := bstep (se 1 (by rfl) ⟨1483784, by rfl⟩ : syracuseStep 1978379 = 2967569) B2967569
theorem B1978433 : Blo 876568 1978433 := bstep (se 2 (by rfl) ⟨741912, by rfl⟩ : syracuseStep 1978433 = 1483825) B1483825
theorem B3747971 : Blo 876568 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B2961629 : Blo 876568 2961629 := bstep (se 3 (by rfl) ⟨555305, by rfl⟩ : syracuseStep 2961629 = 1110611) B1110611
theorem B1978649 : Blo 876568 1978649 := bstep (se 2 (by rfl) ⟨741993, by rfl⟩ : syracuseStep 1978649 = 1483987) B1483987
theorem B1978739 : Blo 876568 1978739 := bstep (se 1 (by rfl) ⟨1484054, by rfl⟩ : syracuseStep 1978739 = 2968109) B2968109
theorem B9613685 : Blo 876568 9613685 := bstep (se 5 (by rfl) ⟨450641, by rfl⟩ : syracuseStep 9613685 = 901283) B901283
theorem B1978775 : Blo 876568 1978775 := bstep (se 1 (by rfl) ⟨1484081, by rfl⟩ : syracuseStep 1978775 = 2968163) B2968163
theorem B1880471 : Blo 876568 1880471 := bstep (se 1 (by rfl) ⟨1410353, by rfl⟩ : syracuseStep 1880471 = 2820707) B2820707
theorem B1880513 : Blo 876568 1880513 := bstep (se 2 (by rfl) ⟨705192, by rfl⟩ : syracuseStep 1880513 = 1410385) B1410385
theorem B7221835 : Blo 876568 7221835 := bstep (se 1 (by rfl) ⟨5416376, by rfl⟩ : syracuseStep 7221835 = 10832753) B10832753
theorem B1978955 : Blo 876568 1978955 := bstep (se 1 (by rfl) ⟨1484216, by rfl⟩ : syracuseStep 1978955 = 2968433) B2968433
theorem B1979009 : Blo 876568 1979009 := bstep (se 2 (by rfl) ⟨742128, by rfl⟩ : syracuseStep 1979009 = 1484257) B1484257
theorem B1782425 : Blo 876568 1782425 := bstep (se 2 (by rfl) ⟨668409, by rfl⟩ : syracuseStep 1782425 = 1336819) B1336819
theorem B1979225 : Blo 876568 1979225 := bstep (se 2 (by rfl) ⟨742209, by rfl⟩ : syracuseStep 1979225 = 1484419) B1484419
theorem B1782667 : Blo 876568 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B1586071 : Blo 876568 1586071 := bstep (se 1 (by rfl) ⟨1189553, by rfl⟩ : syracuseStep 1586071 = 2379107) B2379107
theorem B1979315 : Blo 876568 1979315 := bstep (se 1 (by rfl) ⟨1484486, by rfl⟩ : syracuseStep 1979315 = 2968973) B2968973
theorem B1979351 : Blo 876568 1979351 := bstep (se 1 (by rfl) ⟨1484513, by rfl⟩ : syracuseStep 1979351 = 2969027) B2969027
theorem B1979531 : Blo 876568 1979531 := bstep (se 1 (by rfl) ⟨1484648, by rfl⟩ : syracuseStep 1979531 = 2969297) B2969297
theorem B2503831 : Blo 876568 2503831 := bstep (se 1 (by rfl) ⟨1877873, by rfl⟩ : syracuseStep 2503831 = 3755747) B3755747
theorem B8139953 : Blo 876568 8139953 := bstep (se 2 (by rfl) ⟨3052482, by rfl⟩ : syracuseStep 8139953 = 6104965) B6104965
theorem B2110657 : Blo 876568 2110657 := bstep (se 2 (by rfl) ⟨791496, by rfl⟩ : syracuseStep 2110657 = 1582993) B1582993
theorem B1979585 : Blo 876568 1979585 := bstep (se 2 (by rfl) ⟨742344, by rfl⟩ : syracuseStep 1979585 = 1484689) B1484689
theorem B6665489 : Blo 876568 6665489 := bstep (se 2 (by rfl) ⟨2499558, by rfl⟩ : syracuseStep 6665489 = 4999117) B4999117
theorem B2962763 : Blo 876568 2962763 := bstep (se 1 (by rfl) ⟨2222072, by rfl⟩ : syracuseStep 2962763 = 4444145) B4444145
theorem B1979801 : Blo 876568 1979801 := bstep (se 2 (by rfl) ⟨742425, by rfl⟩ : syracuseStep 1979801 = 1484851) B1484851
theorem B1979891 : Blo 876568 1979891 := bstep (se 1 (by rfl) ⟨1484918, by rfl⟩ : syracuseStep 1979891 = 2969837) B2969837
theorem B15218189 : Blo 876568 15218189 := bstep (se 3 (by rfl) ⟨2853410, by rfl⟩ : syracuseStep 15218189 = 5706821) B5706821
theorem B1979927 : Blo 876568 1979927 := bstep (se 1 (by rfl) ⟨1484945, by rfl⟩ : syracuseStep 1979927 = 2969891) B2969891
theorem B2963033 : Blo 876568 2963033 := bstep (se 2 (by rfl) ⟨1111137, by rfl⟩ : syracuseStep 2963033 = 2222275) B2222275
theorem B12826205 : Blo 876568 12826205 := bstep (se 3 (by rfl) ⟨2404913, by rfl⟩ : syracuseStep 12826205 = 4809827) B4809827
theorem B1980107 : Blo 876568 1980107 := bstep (se 1 (by rfl) ⟨1485080, by rfl⟩ : syracuseStep 1980107 = 2970161) B2970161
theorem B3749597 : Blo 876568 3749597 := bstep (se 3 (by rfl) ⟨703049, by rfl⟩ : syracuseStep 3749597 = 1406099) B1406099
theorem B1980161 : Blo 876568 1980161 := bstep (se 2 (by rfl) ⟨742560, by rfl⟩ : syracuseStep 1980161 = 1485121) B1485121
theorem B51460019 : Blo 876568 51460019 := bstep (se 1 (by rfl) ⟨38595014, by rfl⟩ : syracuseStep 51460019 = 77190029) B77190029
theorem B1980377 : Blo 876568 1980377 := bstep (se 2 (by rfl) ⟨742641, by rfl⟩ : syracuseStep 1980377 = 1485283) B1485283
theorem B1980467 : Blo 876568 1980467 := bstep (se 1 (by rfl) ⟨1485350, by rfl⟩ : syracuseStep 1980467 = 2970701) B2970701
theorem B1980503 : Blo 876568 1980503 := bstep (se 1 (by rfl) ⟨1485377, by rfl⟩ : syracuseStep 1980503 = 2970755) B2970755
theorem B1128587 : Blo 876568 1128587 := bstep (se 1 (by rfl) ⟨846440, by rfl⟩ : syracuseStep 1128587 = 1692881) B1692881
theorem B7518359 : Blo 876568 7518359 := bstep (se 1 (by rfl) ⟨5638769, by rfl⟩ : syracuseStep 7518359 = 11277539) B11277539
theorem B1980683 : Blo 876568 1980683 := bstep (se 1 (by rfl) ⟨1485512, by rfl⟩ : syracuseStep 1980683 = 2971025) B2971025
theorem B2963735 : Blo 876568 2963735 := bstep (se 1 (by rfl) ⟨2222801, by rfl⟩ : syracuseStep 2963735 = 4445603) B4445603
theorem B36616493 : Blo 876568 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B1980737 : Blo 876568 1980737 := bstep (se 2 (by rfl) ⟨742776, by rfl⟩ : syracuseStep 1980737 = 1485553) B1485553
theorem B3750295 : Blo 876568 3750295 := bstep (se 1 (by rfl) ⟨2812721, by rfl⟩ : syracuseStep 3750295 = 5625443) B5625443
theorem B2505163 : Blo 876568 2505163 := bstep (se 1 (by rfl) ⟨1878872, by rfl⟩ : syracuseStep 2505163 = 3757745) B3757745
theorem B1980953 : Blo 876568 1980953 := bstep (se 2 (by rfl) ⟨742857, by rfl⟩ : syracuseStep 1980953 = 1485715) B1485715
theorem B1981043 : Blo 876568 1981043 := bstep (se 1 (by rfl) ⟨1485782, by rfl⟩ : syracuseStep 1981043 = 2971565) B2971565
theorem B1981079 : Blo 876568 1981079 := bstep (se 1 (by rfl) ⟨1485809, by rfl⟩ : syracuseStep 1981079 = 2971619) B2971619
theorem B2505437 : Blo 876568 2505437 := bstep (se 3 (by rfl) ⟨469769, by rfl⟩ : syracuseStep 2505437 = 939539) B939539
theorem B3160883 : Blo 876568 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B2964275 : Blo 876568 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1981259 : Blo 876568 1981259 := bstep (se 1 (by rfl) ⟨1485944, by rfl⟩ : syracuseStep 1981259 = 2971889) B2971889
theorem B4996019 : Blo 876568 4996019 := bstep (se 1 (by rfl) ⟨3747014, by rfl⟩ : syracuseStep 4996019 = 7494029) B7494029
theorem B2505779 : Blo 876568 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B2964545 : Blo 876568 2964545 := bstep (se 2 (by rfl) ⟨1111704, by rfl⟩ : syracuseStep 2964545 = 2223409) B2223409
theorem B13712705 : Blo 876568 13712705 := bstep (se 2 (by rfl) ⟨5142264, by rfl⟩ : syracuseStep 13712705 = 10284529) B10284529
theorem B9485669 : Blo 876568 9485669 := bstep (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) B1778563
theorem B4439447 : Blo 876568 4439447 := bstep (se 1 (by rfl) ⟨3329585, by rfl⟩ : syracuseStep 4439447 = 6659171) B6659171
theorem B5619293 : Blo 876568 5619293 := bstep (se 3 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 5619293 = 2107235) B2107235
theorem B2965085 : Blo 876568 2965085 := bstep (se 3 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 2965085 = 1111907) B1111907
theorem B3555037 : Blo 876568 3555037 := bstep (se 3 (by rfl) ⟨666569, by rfl⟩ : syracuseStep 3555037 = 1333139) B1333139
theorem B3751697 : Blo 876568 3751697 := bstep (se 2 (by rfl) ⟨1406886, by rfl⟩ : syracuseStep 3751697 = 2813773) B2813773
theorem B3161879 : Blo 876568 3161879 := bstep (se 1 (by rfl) ⟨2371409, by rfl⟩ : syracuseStep 3161879 = 4742819) B4742819
theorem B7520273 : Blo 876568 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B30883909 : Blo 876568 30883909 := bstep (se 4 (by rfl) ⟨2895366, by rfl⟩ : syracuseStep 30883909 = 5790733) B5790733
theorem B2113867 : Blo 876568 2113867 := bstep (se 1 (by rfl) ⟨1585400, by rfl⟩ : syracuseStep 2113867 = 3170801) B3170801
theorem B4997477 : Blo 876568 4997477 := bstep (se 4 (by rfl) ⟨468513, by rfl⟩ : syracuseStep 4997477 = 937027) B937027
theorem B4571741 : Blo 876568 4571741 := bstep (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) B1714403
theorem B2966219 : Blo 876568 2966219 := bstep (se 1 (by rfl) ⟨2224664, by rfl⟩ : syracuseStep 2966219 = 4449329) B4449329
theorem B4997933 : Blo 876568 4997933 := bstep (se 3 (by rfl) ⟨937112, by rfl⟩ : syracuseStep 4997933 = 1874225) B1874225
theorem B2966489 : Blo 876568 2966489 := bstep (se 2 (by rfl) ⟨1112433, by rfl⟩ : syracuseStep 2966489 = 2224867) B2224867
theorem B6669377 : Blo 876568 6669377 := bstep (se 2 (by rfl) ⟨2501016, by rfl⟩ : syracuseStep 6669377 = 5002033) B5002033
theorem B4998617 : Blo 876568 4998617 := bstep (se 2 (by rfl) ⟨1874481, by rfl⟩ : syracuseStep 4998617 = 3748963) B3748963
theorem B3556867 : Blo 876568 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B6342209 : Blo 876568 6342209 := bstep (se 2 (by rfl) ⟨2378328, by rfl⟩ : syracuseStep 6342209 = 4756657) B4756657
theorem B4212299 : Blo 876568 4212299 := bstep (se 1 (by rfl) ⟨3159224, by rfl⟩ : syracuseStep 4212299 = 6318449) B6318449
theorem B4212317 : Blo 876568 4212317 := bstep (se 3 (by rfl) ⟨789809, by rfl⟩ : syracuseStep 4212317 = 1579619) B1579619
theorem B4015709 : Blo 876568 4015709 := bstep (se 3 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 4015709 = 1505891) B1505891
theorem B2967191 : Blo 876568 2967191 := bstep (se 1 (by rfl) ⟨2225393, by rfl⟩ : syracuseStep 2967191 = 4450787) B4450787
theorem B2115251 : Blo 876568 2115251 := bstep (se 1 (by rfl) ⟨1586438, by rfl⟩ : syracuseStep 2115251 = 3172877) B3172877
theorem B1689355 : Blo 876568 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B3163997 : Blo 876568 3163997 := bstep (se 3 (by rfl) ⟨593249, by rfl⟩ : syracuseStep 3163997 = 1186499) B1186499
theorem B7489381 : Blo 876568 7489381 := bstep (se 4 (by rfl) ⟨702129, by rfl⟩ : syracuseStep 7489381 = 1404259) B1404259
theorem B1689601 : Blo 876568 1689601 := bstep (se 2 (by rfl) ⟨633600, by rfl⟩ : syracuseStep 1689601 = 1267201) B1267201
theorem B3557549 : Blo 876568 3557549 := bstep (se 3 (by rfl) ⟨667040, by rfl⟩ : syracuseStep 3557549 = 1334081) B1334081
theorem B2967731 : Blo 876568 2967731 := bstep (se 1 (by rfl) ⟨2225798, by rfl⟩ : syracuseStep 2967731 = 4451597) B4451597
theorem B2672833 : Blo 876568 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B936203 : Blo 876568 936203 := bstep (se 1 (by rfl) ⟨702152, by rfl⟩ : syracuseStep 936203 = 1404305) B1404305
theorem B2968001 : Blo 876568 2968001 := bstep (se 2 (by rfl) ⟨1113000, by rfl⟩ : syracuseStep 2968001 = 2226001) B2226001
theorem B1001975 : Blo 876568 1001975 := bstep (se 1 (by rfl) ⟨751481, by rfl⟩ : syracuseStep 1001975 = 1502963) B1502963
theorem B14994071 : Blo 876568 14994071 := bstep (se 1 (by rfl) ⟨11245553, by rfl⟩ : syracuseStep 14994071 = 22491107) B22491107
theorem B3754669 : Blo 876568 3754669 := bstep (se 3 (by rfl) ⟨704000, by rfl⟩ : syracuseStep 3754669 = 1408001) B1408001
theorem B7490339 : Blo 876568 7490339 := bstep (se 1 (by rfl) ⟨5617754, by rfl⟩ : syracuseStep 7490339 = 11235509) B11235509
theorem B3164993 : Blo 876568 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B4443011 : Blo 876568 4443011 := bstep (se 1 (by rfl) ⟨3332258, by rfl⟩ : syracuseStep 4443011 = 6664517) B6664517
theorem B6671321 : Blo 876568 6671321 := bstep (se 2 (by rfl) ⟨2501745, by rfl⟩ : syracuseStep 6671321 = 5003491) B5003491
theorem B2968541 : Blo 876568 2968541 := bstep (se 3 (by rfl) ⟨556601, by rfl⟩ : syracuseStep 2968541 = 1113203) B1113203
theorem B3755011 : Blo 876568 3755011 := bstep (se 1 (by rfl) ⟨2816258, by rfl⟩ : syracuseStep 3755011 = 5632517) B5632517
theorem B937207 : Blo 876568 937207 := bstep (se 1 (by rfl) ⟨702905, by rfl⟩ : syracuseStep 937207 = 1405811) B1405811
theorem B6016643 : Blo 876568 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B5623597 : Blo 876568 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B3755969 : Blo 876568 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B938027 : Blo 876568 938027 := bstep (se 1 (by rfl) ⟨703520, by rfl⟩ : syracuseStep 938027 = 1407041) B1407041
theorem B2969675 : Blo 876568 2969675 := bstep (se 1 (by rfl) ⟨2227256, by rfl⟩ : syracuseStep 2969675 = 4454513) B4454513
theorem B3330179 : Blo 876568 3330179 := bstep (se 1 (by rfl) ⟨2497634, by rfl⟩ : syracuseStep 3330179 = 4995269) B4995269
theorem B3330193 : Blo 876568 3330193 := bstep (se 2 (by rfl) ⟨1248822, by rfl⟩ : syracuseStep 3330193 = 2497645) B2497645
theorem B2969945 : Blo 876568 2969945 := bstep (se 2 (by rfl) ⟨1113729, by rfl⟩ : syracuseStep 2969945 = 2227459) B2227459
theorem B3330497 : Blo 876568 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B1692311 : Blo 876568 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B13718197 : Blo 876568 13718197 := bstep (se 5 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 13718197 = 1286081) B1286081
theorem B3167255 : Blo 876568 3167255 := bstep (se 1 (by rfl) ⟨2375441, by rfl⟩ : syracuseStep 3167255 = 4750883) B4750883
theorem B2970647 : Blo 876568 2970647 := bstep (se 1 (by rfl) ⟨2227985, by rfl⟩ : syracuseStep 2970647 = 4455971) B4455971
theorem B3429427 : Blo 876568 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B3331165 : Blo 876568 3331165 := bstep (se 3 (by rfl) ⟨624593, by rfl⟩ : syracuseStep 3331165 = 1249187) B1249187
theorem B939223 : Blo 876568 939223 := bstep (se 1 (by rfl) ⟨704417, by rfl⟩ : syracuseStep 939223 = 1408835) B1408835
theorem B3757387 : Blo 876568 3757387 := bstep (se 1 (by rfl) ⟨2818040, by rfl⟩ : syracuseStep 3757387 = 5636081) B5636081
theorem B2971187 : Blo 876568 2971187 := bstep (se 1 (by rfl) ⟨2228390, by rfl⟩ : syracuseStep 2971187 = 4456781) B4456781
theorem B3757661 : Blo 876568 3757661 := bstep (se 3 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 3757661 = 1409123) B1409123
theorem B2971457 : Blo 876568 2971457 := bstep (se 2 (by rfl) ⟨1114296, by rfl⟩ : syracuseStep 2971457 = 2228593) B2228593
theorem B3168179 : Blo 876568 3168179 := bstep (se 1 (by rfl) ⟨2376134, by rfl⟩ : syracuseStep 3168179 = 4752269) B4752269
theorem B940043 : Blo 876568 940043 := bstep (se 1 (by rfl) ⟨705032, by rfl⟩ : syracuseStep 940043 = 1410065) B1410065
theorem B5003309 : Blo 876568 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B940171 : Blo 876568 940171 := bstep (se 1 (by rfl) ⟨705128, by rfl⟩ : syracuseStep 940171 = 1410257) B1410257
theorem B6674723 : Blo 876568 6674723 := bstep (se 1 (by rfl) ⟨5006042, by rfl⟩ : syracuseStep 6674723 = 10012085) B10012085
theorem B2677043 : Blo 876568 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B3332441 : Blo 876568 3332441 := bstep (se 2 (by rfl) ⟨1249665, by rfl⟩ : syracuseStep 3332441 = 2499331) B2499331
theorem B4446737 : Blo 876568 4446737 := bstep (se 2 (by rfl) ⟨1667526, by rfl⟩ : syracuseStep 4446737 = 3335053) B3335053
theorem B4446899 : Blo 876568 4446899 := bstep (se 1 (by rfl) ⟨3335174, by rfl⟩ : syracuseStep 4446899 = 6670349) B6670349
theorem B104225753 : Blo 876568 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B5332043 : Blo 876568 5332043 := bstep (se 1 (by rfl) ⟨3999032, by rfl⟩ : syracuseStep 5332043 = 7998065) B7998065
theorem B3169373 : Blo 876568 3169373 := bstep (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) B1188515
theorem B1334551 : Blo 876568 1334551 := bstep (se 1 (by rfl) ⟨1000913, by rfl⟩ : syracuseStep 1334551 = 2001827) B2001827
theorem B2219339 : Blo 876568 2219339 := bstep (se 1 (by rfl) ⟨1664504, by rfl⟩ : syracuseStep 2219339 = 3329009) B3329009
theorem B23158133 : Blo 876568 23158133 := bstep (se 5 (by rfl) ⟨1085537, by rfl⟩ : syracuseStep 23158133 = 2171075) B2171075
theorem B7495091 : Blo 876568 7495091 := bstep (se 1 (by rfl) ⟨5621318, by rfl⟩ : syracuseStep 7495091 = 11242637) B11242637
theorem B4742749 : Blo 876568 4742749 := bstep (se 3 (by rfl) ⟨889265, by rfl⟩ : syracuseStep 4742749 = 1778531) B1778531
theorem B3170137 : Blo 876568 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B3334067 : Blo 876568 3334067 := bstep (se 1 (by rfl) ⟨2500550, by rfl⟩ : syracuseStep 3334067 = 5001101) B5001101
theorem B3334081 : Blo 876568 3334081 := bstep (se 2 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 3334081 = 2500561) B2500561
theorem B876587 : Blo 876568 876587 := bstep (se 1 (by rfl) ⟨657440, by rfl⟩ : syracuseStep 876587 = 1314881) B1314881
theorem B876599 : Blo 876568 876599 := bstep (se 1 (by rfl) ⟨657449, by rfl⟩ : syracuseStep 876599 = 1314899) B1314899
theorem B876619 : Blo 876568 876619 := bstep (se 1 (by rfl) ⟨657464, by rfl⟩ : syracuseStep 876619 = 1314929) B1314929
theorem B876631 : Blo 876568 876631 := bstep (se 1 (by rfl) ⟨657473, by rfl⟩ : syracuseStep 876631 = 1314947) B1314947
theorem B876651 : Blo 876568 876651 := bstep (se 1 (by rfl) ⟨657488, by rfl⟩ : syracuseStep 876651 = 1314977) B1314977
theorem B876663 : Blo 876568 876663 := bstep (se 1 (by rfl) ⟨657497, by rfl⟩ : syracuseStep 876663 = 1314995) B1314995
theorem B14278787 : Blo 876568 14278787 := bstep (se 1 (by rfl) ⟨10709090, by rfl⟩ : syracuseStep 14278787 = 21418181) B21418181
theorem B876683 : Blo 876568 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B3760273 : Blo 876568 3760273 := bstep (se 2 (by rfl) ⟨1410102, by rfl⟩ : syracuseStep 3760273 = 2820205) B2820205
theorem B876695 : Blo 876568 876695 := bstep (se 1 (by rfl) ⟨657521, by rfl⟩ : syracuseStep 876695 = 1315043) B1315043
theorem B876715 : Blo 876568 876715 := bstep (se 1 (by rfl) ⟨657536, by rfl⟩ : syracuseStep 876715 = 1315073) B1315073
theorem B876727 : Blo 876568 876727 := bstep (se 1 (by rfl) ⟨657545, by rfl⟩ : syracuseStep 876727 = 1315091) B1315091
theorem B876747 : Blo 876568 876747 := bstep (se 1 (by rfl) ⟨657560, by rfl⟩ : syracuseStep 876747 = 1315121) B1315121
theorem B876759 : Blo 876568 876759 := bstep (se 1 (by rfl) ⟨657569, by rfl⟩ : syracuseStep 876759 = 1315139) B1315139
theorem B876779 : Blo 876568 876779 := bstep (se 1 (by rfl) ⟨657584, by rfl⟩ : syracuseStep 876779 = 1315169) B1315169
theorem B876791 : Blo 876568 876791 := bstep (se 1 (by rfl) ⟨657593, by rfl⟩ : syracuseStep 876791 = 1315187) B1315187
theorem B876811 : Blo 876568 876811 := bstep (se 1 (by rfl) ⟨657608, by rfl⟩ : syracuseStep 876811 = 1315217) B1315217
theorem B876823 : Blo 876568 876823 := bstep (se 1 (by rfl) ⟨657617, by rfl⟩ : syracuseStep 876823 = 1315235) B1315235
theorem B2220311 : Blo 876568 2220311 := bstep (se 1 (by rfl) ⟨1665233, by rfl⟩ : syracuseStep 2220311 = 3330467) B3330467
theorem B876843 : Blo 876568 876843 := bstep (se 1 (by rfl) ⟨657632, by rfl⟩ : syracuseStep 876843 = 1315265) B1315265
theorem B876855 : Blo 876568 876855 := bstep (se 1 (by rfl) ⟨657641, by rfl⟩ : syracuseStep 876855 = 1315283) B1315283
theorem B876875 : Blo 876568 876875 := bstep (se 1 (by rfl) ⟨657656, by rfl⟩ : syracuseStep 876875 = 1315313) B1315313
theorem B876887 : Blo 876568 876887 := bstep (se 1 (by rfl) ⟨657665, by rfl⟩ : syracuseStep 876887 = 1315331) B1315331
theorem B876907 : Blo 876568 876907 := bstep (se 1 (by rfl) ⟨657680, by rfl⟩ : syracuseStep 876907 = 1315361) B1315361
theorem B876919 : Blo 876568 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B876939 : Blo 876568 876939 := bstep (se 1 (by rfl) ⟨657704, by rfl⟩ : syracuseStep 876939 = 1315409) B1315409
theorem B876951 : Blo 876568 876951 := bstep (se 1 (by rfl) ⟨657713, by rfl⟩ : syracuseStep 876951 = 1315427) B1315427
theorem B876971 : Blo 876568 876971 := bstep (se 1 (by rfl) ⟨657728, by rfl⟩ : syracuseStep 876971 = 1315457) B1315457
theorem B876983 : Blo 876568 876983 := bstep (se 1 (by rfl) ⟨657737, by rfl⟩ : syracuseStep 876983 = 1315475) B1315475
theorem B877003 : Blo 876568 877003 := bstep (se 1 (by rfl) ⟨657752, by rfl⟩ : syracuseStep 877003 = 1315505) B1315505
theorem B877015 : Blo 876568 877015 := bstep (se 1 (by rfl) ⟨657761, by rfl⟩ : syracuseStep 877015 = 1315523) B1315523
theorem B877035 : Blo 876568 877035 := bstep (se 1 (by rfl) ⟨657776, by rfl⟩ : syracuseStep 877035 = 1315553) B1315553
theorem B877047 : Blo 876568 877047 := bstep (se 1 (by rfl) ⟨657785, by rfl⟩ : syracuseStep 877047 = 1315571) B1315571
theorem B877067 : Blo 876568 877067 := bstep (se 1 (by rfl) ⟨657800, by rfl⟩ : syracuseStep 877067 = 1315601) B1315601
theorem B877079 : Blo 876568 877079 := bstep (se 1 (by rfl) ⟨657809, by rfl⟩ : syracuseStep 877079 = 1315619) B1315619
theorem B877099 : Blo 876568 877099 := bstep (se 1 (by rfl) ⟨657824, by rfl⟩ : syracuseStep 877099 = 1315649) B1315649
theorem B877111 : Blo 876568 877111 := bstep (se 1 (by rfl) ⟨657833, by rfl⟩ : syracuseStep 877111 = 1315667) B1315667
theorem B877131 : Blo 876568 877131 := bstep (se 1 (by rfl) ⟨657848, by rfl⟩ : syracuseStep 877131 = 1315697) B1315697
theorem B4448843 : Blo 876568 4448843 := bstep (se 1 (by rfl) ⟨3336632, by rfl⟩ : syracuseStep 4448843 = 6673265) B6673265
theorem B877143 : Blo 876568 877143 := bstep (se 1 (by rfl) ⟨657857, by rfl⟩ : syracuseStep 877143 = 1315715) B1315715
theorem B877163 : Blo 876568 877163 := bstep (se 1 (by rfl) ⟨657872, by rfl⟩ : syracuseStep 877163 = 1315745) B1315745
theorem B877175 : Blo 876568 877175 := bstep (se 1 (by rfl) ⟨657881, by rfl⟩ : syracuseStep 877175 = 1315763) B1315763
theorem B877195 : Blo 876568 877195 := bstep (se 1 (by rfl) ⟨657896, by rfl⟩ : syracuseStep 877195 = 1315793) B1315793
theorem B877207 : Blo 876568 877207 := bstep (se 1 (by rfl) ⟨657905, by rfl⟩ : syracuseStep 877207 = 1315811) B1315811
theorem B4219543 : Blo 876568 4219543 := bstep (se 1 (by rfl) ⟨3164657, by rfl⟩ : syracuseStep 4219543 = 6329315) B6329315
theorem B877227 : Blo 876568 877227 := bstep (se 1 (by rfl) ⟨657920, by rfl⟩ : syracuseStep 877227 = 1315841) B1315841
theorem B877239 : Blo 876568 877239 := bstep (se 1 (by rfl) ⟨657929, by rfl⟩ : syracuseStep 877239 = 1315859) B1315859
theorem B877259 : Blo 876568 877259 := bstep (se 1 (by rfl) ⟨657944, by rfl⟩ : syracuseStep 877259 = 1315889) B1315889
theorem B877271 : Blo 876568 877271 := bstep (se 1 (by rfl) ⟨657953, by rfl⟩ : syracuseStep 877271 = 1315907) B1315907
theorem B877291 : Blo 876568 877291 := bstep (se 1 (by rfl) ⟨657968, by rfl⟩ : syracuseStep 877291 = 1315937) B1315937
theorem B877303 : Blo 876568 877303 := bstep (se 1 (by rfl) ⟨657977, by rfl⟩ : syracuseStep 877303 = 1315955) B1315955
theorem B877323 : Blo 876568 877323 := bstep (se 1 (by rfl) ⟨657992, by rfl⟩ : syracuseStep 877323 = 1315985) B1315985
theorem B877335 : Blo 876568 877335 := bstep (se 1 (by rfl) ⟨658001, by rfl⟩ : syracuseStep 877335 = 1316003) B1316003
theorem B877355 : Blo 876568 877355 := bstep (se 1 (by rfl) ⟨658016, by rfl⟩ : syracuseStep 877355 = 1316033) B1316033
theorem B877367 : Blo 876568 877367 := bstep (se 1 (by rfl) ⟨658025, by rfl⟩ : syracuseStep 877367 = 1316051) B1316051
theorem B877387 : Blo 876568 877387 := bstep (se 1 (by rfl) ⟨658040, by rfl⟩ : syracuseStep 877387 = 1316081) B1316081
theorem B877399 : Blo 876568 877399 := bstep (se 1 (by rfl) ⟨658049, by rfl⟩ : syracuseStep 877399 = 1316099) B1316099
theorem B877419 : Blo 876568 877419 := bstep (se 1 (by rfl) ⟨658064, by rfl⟩ : syracuseStep 877419 = 1316129) B1316129
theorem B877431 : Blo 876568 877431 := bstep (se 1 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 877431 = 1316147) B1316147
theorem B877451 : Blo 876568 877451 := bstep (se 1 (by rfl) ⟨658088, by rfl⟩ : syracuseStep 877451 = 1316177) B1316177
theorem B877463 : Blo 876568 877463 := bstep (se 1 (by rfl) ⟨658097, by rfl⟩ : syracuseStep 877463 = 1316195) B1316195
theorem B877483 : Blo 876568 877483 := bstep (se 1 (by rfl) ⟨658112, by rfl⟩ : syracuseStep 877483 = 1316225) B1316225
theorem B2220979 : Blo 876568 2220979 := bstep (se 1 (by rfl) ⟨1665734, by rfl⟩ : syracuseStep 2220979 = 3331469) B3331469
theorem B877495 : Blo 876568 877495 := bstep (se 1 (by rfl) ⟨658121, by rfl⟩ : syracuseStep 877495 = 1316243) B1316243
theorem B877515 : Blo 876568 877515 := bstep (se 1 (by rfl) ⟨658136, by rfl⟩ : syracuseStep 877515 = 1316273) B1316273
theorem B877527 : Blo 876568 877527 := bstep (se 1 (by rfl) ⟨658145, by rfl⟩ : syracuseStep 877527 = 1316291) B1316291
theorem B877547 : Blo 876568 877547 := bstep (se 1 (by rfl) ⟨658160, by rfl⟩ : syracuseStep 877547 = 1316321) B1316321
theorem B877559 : Blo 876568 877559 := bstep (se 1 (by rfl) ⟨658169, by rfl⟩ : syracuseStep 877559 = 1316339) B1316339
theorem B877579 : Blo 876568 877579 := bstep (se 1 (by rfl) ⟨658184, by rfl⟩ : syracuseStep 877579 = 1316369) B1316369
theorem B877591 : Blo 876568 877591 := bstep (se 1 (by rfl) ⟨658193, by rfl⟩ : syracuseStep 877591 = 1316387) B1316387
theorem B877611 : Blo 876568 877611 := bstep (se 1 (by rfl) ⟨658208, by rfl⟩ : syracuseStep 877611 = 1316417) B1316417
theorem B877623 : Blo 876568 877623 := bstep (se 1 (by rfl) ⟨658217, by rfl⟩ : syracuseStep 877623 = 1316435) B1316435
theorem B2221121 : Blo 876568 2221121 := bstep (se 2 (by rfl) ⟨832920, by rfl⟩ : syracuseStep 2221121 = 1665841) B1665841
theorem B2253889 : Blo 876568 2253889 := bstep (se 2 (by rfl) ⟨845208, by rfl⟩ : syracuseStep 2253889 = 1690417) B1690417
theorem B877643 : Blo 876568 877643 := bstep (se 1 (by rfl) ⟨658232, by rfl⟩ : syracuseStep 877643 = 1316465) B1316465
theorem B877655 : Blo 876568 877655 := bstep (se 1 (by rfl) ⟨658241, by rfl⟩ : syracuseStep 877655 = 1316483) B1316483
theorem B15033437 : Blo 876568 15033437 := bstep (se 3 (by rfl) ⟨2818769, by rfl⟩ : syracuseStep 15033437 = 5637539) B5637539
theorem B877675 : Blo 876568 877675 := bstep (se 1 (by rfl) ⟨658256, by rfl⟩ : syracuseStep 877675 = 1316513) B1316513
theorem B877687 : Blo 876568 877687 := bstep (se 1 (by rfl) ⟨658265, by rfl⟩ : syracuseStep 877687 = 1316531) B1316531
theorem B877707 : Blo 876568 877707 := bstep (se 1 (by rfl) ⟨658280, by rfl⟩ : syracuseStep 877707 = 1316561) B1316561
theorem B877719 : Blo 876568 877719 := bstep (se 1 (by rfl) ⟨658289, by rfl⟩ : syracuseStep 877719 = 1316579) B1316579
theorem B877739 : Blo 876568 877739 := bstep (se 1 (by rfl) ⟨658304, by rfl⟩ : syracuseStep 877739 = 1316609) B1316609
theorem B877751 : Blo 876568 877751 := bstep (se 1 (by rfl) ⟨658313, by rfl⟩ : syracuseStep 877751 = 1316627) B1316627
theorem B877771 : Blo 876568 877771 := bstep (se 1 (by rfl) ⟨658328, by rfl⟩ : syracuseStep 877771 = 1316657) B1316657
theorem B877783 : Blo 876568 877783 := bstep (se 1 (by rfl) ⟨658337, by rfl⟩ : syracuseStep 877783 = 1316675) B1316675
theorem B877803 : Blo 876568 877803 := bstep (se 1 (by rfl) ⟨658352, by rfl⟩ : syracuseStep 877803 = 1316705) B1316705
theorem B877815 : Blo 876568 877815 := bstep (se 1 (by rfl) ⟨658361, by rfl⟩ : syracuseStep 877815 = 1316723) B1316723
theorem B877835 : Blo 876568 877835 := bstep (se 1 (by rfl) ⟨658376, by rfl⟩ : syracuseStep 877835 = 1316753) B1316753
theorem B877847 : Blo 876568 877847 := bstep (se 1 (by rfl) ⟨658385, by rfl⟩ : syracuseStep 877847 = 1316771) B1316771
theorem B877867 : Blo 876568 877867 := bstep (se 1 (by rfl) ⟨658400, by rfl⟩ : syracuseStep 877867 = 1316801) B1316801
theorem B7595309 : Blo 876568 7595309 := bstep (se 3 (by rfl) ⟨1424120, by rfl⟩ : syracuseStep 7595309 = 2848241) B2848241
theorem B877879 : Blo 876568 877879 := bstep (se 1 (by rfl) ⟨658409, by rfl⟩ : syracuseStep 877879 = 1316819) B1316819
theorem B8348993 : Blo 876568 8348993 := bstep (se 2 (by rfl) ⟨3130872, by rfl⟩ : syracuseStep 8348993 = 6261745) B6261745
theorem B877899 : Blo 876568 877899 := bstep (se 1 (by rfl) ⟨658424, by rfl⟩ : syracuseStep 877899 = 1316849) B1316849
theorem B877911 : Blo 876568 877911 := bstep (se 1 (by rfl) ⟨658433, by rfl⟩ : syracuseStep 877911 = 1316867) B1316867
theorem B877931 : Blo 876568 877931 := bstep (se 1 (by rfl) ⟨658448, by rfl⟩ : syracuseStep 877931 = 1316897) B1316897
theorem B877943 : Blo 876568 877943 := bstep (se 1 (by rfl) ⟨658457, by rfl⟩ : syracuseStep 877943 = 1316915) B1316915
theorem B877963 : Blo 876568 877963 := bstep (se 1 (by rfl) ⟨658472, by rfl⟩ : syracuseStep 877963 = 1316945) B1316945
theorem B2811287 : Blo 876568 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B877975 : Blo 876568 877975 := bstep (se 1 (by rfl) ⟨658481, by rfl⟩ : syracuseStep 877975 = 1316963) B1316963
theorem B877995 : Blo 876568 877995 := bstep (se 1 (by rfl) ⟨658496, by rfl⟩ : syracuseStep 877995 = 1316993) B1316993
theorem B878007 : Blo 876568 878007 := bstep (se 1 (by rfl) ⟨658505, by rfl⟩ : syracuseStep 878007 = 1317011) B1317011
theorem B1664459 : Blo 876568 1664459 := bstep (se 1 (by rfl) ⟨1248344, by rfl⟩ : syracuseStep 1664459 = 2496689) B2496689
theorem B878027 : Blo 876568 878027 := bstep (se 1 (by rfl) ⟨658520, by rfl⟩ : syracuseStep 878027 = 1317041) B1317041
theorem B878039 : Blo 876568 878039 := bstep (se 1 (by rfl) ⟨658529, by rfl⟩ : syracuseStep 878039 = 1317059) B1317059
theorem B878059 : Blo 876568 878059 := bstep (se 1 (by rfl) ⟨658544, by rfl⟩ : syracuseStep 878059 = 1317089) B1317089
theorem B878071 : Blo 876568 878071 := bstep (se 1 (by rfl) ⟨658553, by rfl⟩ : syracuseStep 878071 = 1317107) B1317107
theorem B878091 : Blo 876568 878091 := bstep (se 1 (by rfl) ⟨658568, by rfl⟩ : syracuseStep 878091 = 1317137) B1317137
theorem B878103 : Blo 876568 878103 := bstep (se 1 (by rfl) ⟨658577, by rfl⟩ : syracuseStep 878103 = 1317155) B1317155
theorem B878123 : Blo 876568 878123 := bstep (se 1 (by rfl) ⟨658592, by rfl⟩ : syracuseStep 878123 = 1317185) B1317185
theorem B878135 : Blo 876568 878135 := bstep (se 1 (by rfl) ⟨658601, by rfl⟩ : syracuseStep 878135 = 1317203) B1317203
theorem B878155 : Blo 876568 878155 := bstep (se 1 (by rfl) ⟨658616, by rfl⟩ : syracuseStep 878155 = 1317233) B1317233
theorem B878167 : Blo 876568 878167 := bstep (se 1 (by rfl) ⟨658625, by rfl⟩ : syracuseStep 878167 = 1317251) B1317251
theorem B878187 : Blo 876568 878187 := bstep (se 1 (by rfl) ⟨658640, by rfl⟩ : syracuseStep 878187 = 1317281) B1317281
theorem B878199 : Blo 876568 878199 := bstep (se 1 (by rfl) ⟨658649, by rfl⟩ : syracuseStep 878199 = 1317299) B1317299
theorem B1664641 : Blo 876568 1664641 := bstep (se 2 (by rfl) ⟨624240, by rfl⟩ : syracuseStep 1664641 = 1248481) B1248481
theorem B878219 : Blo 876568 878219 := bstep (se 1 (by rfl) ⟨658664, by rfl⟩ : syracuseStep 878219 = 1317329) B1317329
theorem B878231 : Blo 876568 878231 := bstep (se 1 (by rfl) ⟨658673, by rfl⟩ : syracuseStep 878231 = 1317347) B1317347
theorem B878251 : Blo 876568 878251 := bstep (se 1 (by rfl) ⟨658688, by rfl⟩ : syracuseStep 878251 = 1317377) B1317377
theorem B878263 : Blo 876568 878263 := bstep (se 1 (by rfl) ⟨658697, by rfl⟩ : syracuseStep 878263 = 1317395) B1317395
theorem B878283 : Blo 876568 878283 := bstep (se 1 (by rfl) ⟨658712, by rfl⟩ : syracuseStep 878283 = 1317425) B1317425
theorem B878295 : Blo 876568 878295 := bstep (se 1 (by rfl) ⟨658721, by rfl⟩ : syracuseStep 878295 = 1317443) B1317443
theorem B878315 : Blo 876568 878315 := bstep (se 1 (by rfl) ⟨658736, by rfl⟩ : syracuseStep 878315 = 1317473) B1317473
theorem B878327 : Blo 876568 878327 := bstep (se 1 (by rfl) ⟨658745, by rfl⟩ : syracuseStep 878327 = 1317491) B1317491
theorem B878347 : Blo 876568 878347 := bstep (se 1 (by rfl) ⟨658760, by rfl⟩ : syracuseStep 878347 = 1317521) B1317521
theorem B878359 : Blo 876568 878359 := bstep (se 1 (by rfl) ⟨658769, by rfl⟩ : syracuseStep 878359 = 1317539) B1317539
theorem B3008279 : Blo 876568 3008279 := bstep (se 1 (by rfl) ⟨2256209, by rfl⟩ : syracuseStep 3008279 = 4512419) B4512419
theorem B878379 : Blo 876568 878379 := bstep (se 1 (by rfl) ⟨658784, by rfl⟩ : syracuseStep 878379 = 1317569) B1317569
theorem B878391 : Blo 876568 878391 := bstep (se 1 (by rfl) ⟨658793, by rfl⟩ : syracuseStep 878391 = 1317587) B1317587
theorem B2713409 : Blo 876568 2713409 := bstep (se 2 (by rfl) ⟨1017528, by rfl⟩ : syracuseStep 2713409 = 2035057) B2035057
theorem B878411 : Blo 876568 878411 := bstep (se 1 (by rfl) ⟨658808, by rfl⟩ : syracuseStep 878411 = 1317617) B1317617
theorem B3336011 : Blo 876568 3336011 := bstep (se 1 (by rfl) ⟨2502008, by rfl⟩ : syracuseStep 3336011 = 5004017) B5004017
theorem B878423 : Blo 876568 878423 := bstep (se 1 (by rfl) ⟨658817, by rfl⟩ : syracuseStep 878423 = 1317635) B1317635
theorem B3336025 : Blo 876568 3336025 := bstep (se 2 (by rfl) ⟨1251009, by rfl⟩ : syracuseStep 3336025 = 2502019) B2502019
theorem B878443 : Blo 876568 878443 := bstep (se 1 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 878443 = 1317665) B1317665
theorem B878455 : Blo 876568 878455 := bstep (se 1 (by rfl) ⟨658841, by rfl⟩ : syracuseStep 878455 = 1317683) B1317683
theorem B878475 : Blo 876568 878475 := bstep (se 1 (by rfl) ⟨658856, by rfl⟩ : syracuseStep 878475 = 1317713) B1317713
theorem B878487 : Blo 876568 878487 := bstep (se 1 (by rfl) ⟨658865, by rfl⟩ : syracuseStep 878487 = 1317731) B1317731
theorem B878507 : Blo 876568 878507 := bstep (se 1 (by rfl) ⟨658880, by rfl⟩ : syracuseStep 878507 = 1317761) B1317761
theorem B878519 : Blo 876568 878519 := bstep (se 1 (by rfl) ⟨658889, by rfl⟩ : syracuseStep 878519 = 1317779) B1317779
theorem B878539 : Blo 876568 878539 := bstep (se 1 (by rfl) ⟨658904, by rfl⟩ : syracuseStep 878539 = 1317809) B1317809
theorem B878551 : Blo 876568 878551 := bstep (se 1 (by rfl) ⟨658913, by rfl⟩ : syracuseStep 878551 = 1317827) B1317827
theorem B878571 : Blo 876568 878571 := bstep (se 1 (by rfl) ⟨658928, by rfl⟩ : syracuseStep 878571 = 1317857) B1317857
theorem B878583 : Blo 876568 878583 := bstep (se 1 (by rfl) ⟨658937, by rfl⟩ : syracuseStep 878583 = 1317875) B1317875
theorem B878603 : Blo 876568 878603 := bstep (se 1 (by rfl) ⟨658952, by rfl⟩ : syracuseStep 878603 = 1317905) B1317905
theorem B878615 : Blo 876568 878615 := bstep (se 1 (by rfl) ⟨658961, by rfl⟩ : syracuseStep 878615 = 1317923) B1317923
theorem B878635 : Blo 876568 878635 := bstep (se 1 (by rfl) ⟨658976, by rfl⟩ : syracuseStep 878635 = 1317953) B1317953
theorem B5335085 : Blo 876568 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B878647 : Blo 876568 878647 := bstep (se 1 (by rfl) ⟨658985, by rfl⟩ : syracuseStep 878647 = 1317971) B1317971
theorem B878667 : Blo 876568 878667 := bstep (se 1 (by rfl) ⟨659000, by rfl⟩ : syracuseStep 878667 = 1318001) B1318001
theorem B878679 : Blo 876568 878679 := bstep (se 1 (by rfl) ⟨659009, by rfl⟩ : syracuseStep 878679 = 1318019) B1318019
theorem B3172445 : Blo 876568 3172445 := bstep (se 3 (by rfl) ⟨594833, by rfl⟩ : syracuseStep 3172445 = 1189667) B1189667
theorem B878699 : Blo 876568 878699 := bstep (se 1 (by rfl) ⟨659024, by rfl⟩ : syracuseStep 878699 = 1318049) B1318049
theorem B878711 : Blo 876568 878711 := bstep (se 1 (by rfl) ⟨659033, by rfl⟩ : syracuseStep 878711 = 1318067) B1318067
theorem B878731 : Blo 876568 878731 := bstep (se 1 (by rfl) ⟨659048, by rfl⟩ : syracuseStep 878731 = 1318097) B1318097
theorem B878743 : Blo 876568 878743 := bstep (se 1 (by rfl) ⟨659057, by rfl⟩ : syracuseStep 878743 = 1318115) B1318115
theorem B878763 : Blo 876568 878763 := bstep (se 1 (by rfl) ⟨659072, by rfl⟩ : syracuseStep 878763 = 1318145) B1318145
theorem B878775 : Blo 876568 878775 := bstep (se 1 (by rfl) ⟨659081, by rfl⟩ : syracuseStep 878775 = 1318163) B1318163
theorem B878795 : Blo 876568 878795 := bstep (se 1 (by rfl) ⟨659096, by rfl⟩ : syracuseStep 878795 = 1318193) B1318193
theorem B878807 : Blo 876568 878807 := bstep (se 1 (by rfl) ⟨659105, by rfl⟩ : syracuseStep 878807 = 1318211) B1318211
theorem B878827 : Blo 876568 878827 := bstep (se 1 (by rfl) ⟨659120, by rfl⟩ : syracuseStep 878827 = 1318241) B1318241
theorem B878839 : Blo 876568 878839 := bstep (se 1 (by rfl) ⟨659129, by rfl⟩ : syracuseStep 878839 = 1318259) B1318259
theorem B878859 : Blo 876568 878859 := bstep (se 1 (by rfl) ⟨659144, by rfl⟩ : syracuseStep 878859 = 1318289) B1318289
theorem B878871 : Blo 876568 878871 := bstep (se 1 (by rfl) ⟨659153, by rfl⟩ : syracuseStep 878871 = 1318307) B1318307
theorem B878891 : Blo 876568 878891 := bstep (se 1 (by rfl) ⟨659168, by rfl⟩ : syracuseStep 878891 = 1318337) B1318337
theorem B2222387 : Blo 876568 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B878903 : Blo 876568 878903 := bstep (se 1 (by rfl) ⟨659177, by rfl⟩ : syracuseStep 878903 = 1318355) B1318355
theorem B4450625 : Blo 876568 4450625 := bstep (se 2 (by rfl) ⟨1668984, by rfl⟩ : syracuseStep 4450625 = 3337969) B3337969
theorem B3565889 : Blo 876568 3565889 := bstep (se 2 (by rfl) ⟨1337208, by rfl⟩ : syracuseStep 3565889 = 2674417) B2674417
theorem B1665355 : Blo 876568 1665355 := bstep (se 1 (by rfl) ⟨1249016, by rfl⟩ : syracuseStep 1665355 = 2498033) B2498033
theorem B878923 : Blo 876568 878923 := bstep (se 1 (by rfl) ⟨659192, by rfl⟩ : syracuseStep 878923 = 1318385) B1318385
theorem B878935 : Blo 876568 878935 := bstep (se 1 (by rfl) ⟨659201, by rfl⟩ : syracuseStep 878935 = 1318403) B1318403
theorem B878955 : Blo 876568 878955 := bstep (se 1 (by rfl) ⟨659216, by rfl⟩ : syracuseStep 878955 = 1318433) B1318433
theorem B878967 : Blo 876568 878967 := bstep (se 1 (by rfl) ⟨659225, by rfl⟩ : syracuseStep 878967 = 1318451) B1318451
theorem B4745603 : Blo 876568 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B878987 : Blo 876568 878987 := bstep (se 1 (by rfl) ⟨659240, by rfl⟩ : syracuseStep 878987 = 1318481) B1318481
theorem B1665431 : Blo 876568 1665431 := bstep (se 1 (by rfl) ⟨1249073, by rfl⟩ : syracuseStep 1665431 = 2498147) B2498147
theorem B878999 : Blo 876568 878999 := bstep (se 1 (by rfl) ⟨659249, by rfl⟩ : syracuseStep 878999 = 1318499) B1318499
theorem B879019 : Blo 876568 879019 := bstep (se 1 (by rfl) ⟨659264, by rfl⟩ : syracuseStep 879019 = 1318529) B1318529
theorem B879031 : Blo 876568 879031 := bstep (se 1 (by rfl) ⟨659273, by rfl⟩ : syracuseStep 879031 = 1318547) B1318547
theorem B879051 : Blo 876568 879051 := bstep (se 1 (by rfl) ⟨659288, by rfl⟩ : syracuseStep 879051 = 1318577) B1318577
theorem B879063 : Blo 876568 879063 := bstep (se 1 (by rfl) ⟨659297, by rfl⟩ : syracuseStep 879063 = 1318595) B1318595
theorem B879083 : Blo 876568 879083 := bstep (se 1 (by rfl) ⟨659312, by rfl⟩ : syracuseStep 879083 = 1318625) B1318625
theorem B879095 : Blo 876568 879095 := bstep (se 1 (by rfl) ⟨659321, by rfl⟩ : syracuseStep 879095 = 1318643) B1318643
theorem B879115 : Blo 876568 879115 := bstep (se 1 (by rfl) ⟨659336, by rfl⟩ : syracuseStep 879115 = 1318673) B1318673
theorem B879127 : Blo 876568 879127 := bstep (se 1 (by rfl) ⟨659345, by rfl⟩ : syracuseStep 879127 = 1318691) B1318691
theorem B879147 : Blo 876568 879147 := bstep (se 1 (by rfl) ⟨659360, by rfl⟩ : syracuseStep 879147 = 1318721) B1318721
theorem B879159 : Blo 876568 879159 := bstep (se 1 (by rfl) ⟨659369, by rfl⟩ : syracuseStep 879159 = 1318739) B1318739
theorem B879179 : Blo 876568 879179 := bstep (se 1 (by rfl) ⟨659384, by rfl⟩ : syracuseStep 879179 = 1318769) B1318769
theorem B879191 : Blo 876568 879191 := bstep (se 1 (by rfl) ⟨659393, by rfl⟩ : syracuseStep 879191 = 1318787) B1318787
theorem B879211 : Blo 876568 879211 := bstep (se 1 (by rfl) ⟨659408, by rfl⟩ : syracuseStep 879211 = 1318817) B1318817
theorem B879223 : Blo 876568 879223 := bstep (se 1 (by rfl) ⟨659417, by rfl⟩ : syracuseStep 879223 = 1318835) B1318835
theorem B879243 : Blo 876568 879243 := bstep (se 1 (by rfl) ⟨659432, by rfl⟩ : syracuseStep 879243 = 1318865) B1318865
theorem B879255 : Blo 876568 879255 := bstep (se 1 (by rfl) ⟨659441, by rfl⟩ : syracuseStep 879255 = 1318883) B1318883
theorem B879275 : Blo 876568 879275 := bstep (se 1 (by rfl) ⟨659456, by rfl⟩ : syracuseStep 879275 = 1318913) B1318913
theorem B879287 : Blo 876568 879287 := bstep (se 1 (by rfl) ⟨659465, by rfl⟩ : syracuseStep 879287 = 1318931) B1318931
theorem B2812619 : Blo 876568 2812619 := bstep (se 1 (by rfl) ⟨2109464, by rfl⟩ : syracuseStep 2812619 = 4218929) B4218929
theorem B879307 : Blo 876568 879307 := bstep (se 1 (by rfl) ⟨659480, by rfl⟩ : syracuseStep 879307 = 1318961) B1318961
theorem B1338059 : Blo 876568 1338059 := bstep (se 1 (by rfl) ⟨1003544, by rfl⟩ : syracuseStep 1338059 = 2007089) B2007089
theorem B879319 : Blo 876568 879319 := bstep (se 1 (by rfl) ⟨659489, by rfl⟩ : syracuseStep 879319 = 1318979) B1318979
theorem B879339 : Blo 876568 879339 := bstep (se 1 (by rfl) ⟨659504, by rfl⟩ : syracuseStep 879339 = 1319009) B1319009
theorem B879351 : Blo 876568 879351 := bstep (se 1 (by rfl) ⟨659513, by rfl⟩ : syracuseStep 879351 = 1319027) B1319027
theorem B879371 : Blo 876568 879371 := bstep (se 1 (by rfl) ⟨659528, by rfl⟩ : syracuseStep 879371 = 1319057) B1319057
theorem B3336983 : Blo 876568 3336983 := bstep (se 1 (by rfl) ⟨2502737, by rfl⟩ : syracuseStep 3336983 = 5005475) B5005475
theorem B879383 : Blo 876568 879383 := bstep (se 1 (by rfl) ⟨659537, by rfl⟩ : syracuseStep 879383 = 1319075) B1319075
theorem B879403 : Blo 876568 879403 := bstep (se 1 (by rfl) ⟨659552, by rfl⟩ : syracuseStep 879403 = 1319105) B1319105
theorem B879415 : Blo 876568 879415 := bstep (se 1 (by rfl) ⟨659561, by rfl⟩ : syracuseStep 879415 = 1319123) B1319123
theorem B2222923 : Blo 876568 2222923 := bstep (se 1 (by rfl) ⟨1667192, by rfl⟩ : syracuseStep 2222923 = 3334385) B3334385
theorem B879435 : Blo 876568 879435 := bstep (se 1 (by rfl) ⟨659576, by rfl⟩ : syracuseStep 879435 = 1319153) B1319153
theorem B879447 : Blo 876568 879447 := bstep (se 1 (by rfl) ⟨659585, by rfl⟩ : syracuseStep 879447 = 1319171) B1319171
theorem B879467 : Blo 876568 879467 := bstep (se 1 (by rfl) ⟨659600, by rfl⟩ : syracuseStep 879467 = 1319201) B1319201
theorem B879479 : Blo 876568 879479 := bstep (se 1 (by rfl) ⟨659609, by rfl⟩ : syracuseStep 879479 = 1319219) B1319219
theorem B879499 : Blo 876568 879499 := bstep (se 1 (by rfl) ⟨659624, by rfl⟩ : syracuseStep 879499 = 1319249) B1319249
theorem B879511 : Blo 876568 879511 := bstep (se 1 (by rfl) ⟨659633, by rfl⟩ : syracuseStep 879511 = 1319267) B1319267
theorem B879531 : Blo 876568 879531 := bstep (se 1 (by rfl) ⟨659648, by rfl⟩ : syracuseStep 879531 = 1319297) B1319297
theorem B879543 : Blo 876568 879543 := bstep (se 1 (by rfl) ⟨659657, by rfl⟩ : syracuseStep 879543 = 1319315) B1319315
theorem B879563 : Blo 876568 879563 := bstep (se 1 (by rfl) ⟨659672, by rfl⟩ : syracuseStep 879563 = 1319345) B1319345
theorem B879575 : Blo 876568 879575 := bstep (se 1 (by rfl) ⟨659681, by rfl⟩ : syracuseStep 879575 = 1319363) B1319363
theorem B2223065 : Blo 876568 2223065 := bstep (se 2 (by rfl) ⟨833649, by rfl⟩ : syracuseStep 2223065 = 1667299) B1667299
theorem B879595 : Blo 876568 879595 := bstep (se 1 (by rfl) ⟨659696, by rfl⟩ : syracuseStep 879595 = 1319393) B1319393
theorem B879607 : Blo 876568 879607 := bstep (se 1 (by rfl) ⟨659705, by rfl⟩ : syracuseStep 879607 = 1319411) B1319411
theorem B879627 : Blo 876568 879627 := bstep (se 1 (by rfl) ⟨659720, by rfl⟩ : syracuseStep 879627 = 1319441) B1319441
theorem B879639 : Blo 876568 879639 := bstep (se 1 (by rfl) ⟨659729, by rfl⟩ : syracuseStep 879639 = 1319459) B1319459
theorem B879659 : Blo 876568 879659 := bstep (se 1 (by rfl) ⟨659744, by rfl⟩ : syracuseStep 879659 = 1319489) B1319489
theorem B1666099 : Blo 876568 1666099 := bstep (se 1 (by rfl) ⟨1249574, by rfl⟩ : syracuseStep 1666099 = 2499149) B2499149
theorem B879671 : Blo 876568 879671 := bstep (se 1 (by rfl) ⟨659753, by rfl⟩ : syracuseStep 879671 = 1319507) B1319507
theorem B879691 : Blo 876568 879691 := bstep (se 1 (by rfl) ⟨659768, by rfl⟩ : syracuseStep 879691 = 1319537) B1319537
theorem B879703 : Blo 876568 879703 := bstep (se 1 (by rfl) ⟨659777, by rfl⟩ : syracuseStep 879703 = 1319555) B1319555
theorem B879723 : Blo 876568 879723 := bstep (se 1 (by rfl) ⟨659792, by rfl⟩ : syracuseStep 879723 = 1319585) B1319585
theorem B879735 : Blo 876568 879735 := bstep (se 1 (by rfl) ⟨659801, by rfl⟩ : syracuseStep 879735 = 1319603) B1319603
theorem B879755 : Blo 876568 879755 := bstep (se 1 (by rfl) ⟨659816, by rfl⟩ : syracuseStep 879755 = 1319633) B1319633
theorem B879767 : Blo 876568 879767 := bstep (se 1 (by rfl) ⟨659825, by rfl⟩ : syracuseStep 879767 = 1319651) B1319651
theorem B879787 : Blo 876568 879787 := bstep (se 1 (by rfl) ⟨659840, by rfl⟩ : syracuseStep 879787 = 1319681) B1319681
theorem B879799 : Blo 876568 879799 := bstep (se 1 (by rfl) ⟨659849, by rfl⟩ : syracuseStep 879799 = 1319699) B1319699
theorem B879819 : Blo 876568 879819 := bstep (se 1 (by rfl) ⟨659864, by rfl⟩ : syracuseStep 879819 = 1319729) B1319729
theorem B879831 : Blo 876568 879831 := bstep (se 1 (by rfl) ⟨659873, by rfl⟩ : syracuseStep 879831 = 1319747) B1319747
theorem B879851 : Blo 876568 879851 := bstep (se 1 (by rfl) ⟨659888, by rfl⟩ : syracuseStep 879851 = 1319777) B1319777
theorem B16051441 : Blo 876568 16051441 := bstep (se 2 (by rfl) ⟨6019290, by rfl⟩ : syracuseStep 16051441 = 12038581) B12038581
theorem B879863 : Blo 876568 879863 := bstep (se 1 (by rfl) ⟨659897, by rfl⟩ : syracuseStep 879863 = 1319795) B1319795
theorem B879883 : Blo 876568 879883 := bstep (se 1 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 879883 = 1319825) B1319825
theorem B1666327 : Blo 876568 1666327 := bstep (se 1 (by rfl) ⟨1249745, by rfl⟩ : syracuseStep 1666327 = 2499491) B2499491
theorem B879895 : Blo 876568 879895 := bstep (se 1 (by rfl) ⟨659921, by rfl⟩ : syracuseStep 879895 = 1319843) B1319843
theorem B879915 : Blo 876568 879915 := bstep (se 1 (by rfl) ⟨659936, by rfl⟩ : syracuseStep 879915 = 1319873) B1319873
theorem B879927 : Blo 876568 879927 := bstep (se 1 (by rfl) ⟨659945, by rfl⟩ : syracuseStep 879927 = 1319891) B1319891
theorem B879947 : Blo 876568 879947 := bstep (se 1 (by rfl) ⟨659960, by rfl⟩ : syracuseStep 879947 = 1319921) B1319921
theorem B879959 : Blo 876568 879959 := bstep (se 1 (by rfl) ⟨659969, by rfl⟩ : syracuseStep 879959 = 1319939) B1319939
theorem B879979 : Blo 876568 879979 := bstep (se 1 (by rfl) ⟨659984, by rfl⟩ : syracuseStep 879979 = 1319969) B1319969
theorem B879991 : Blo 876568 879991 := bstep (se 1 (by rfl) ⟨659993, by rfl⟩ : syracuseStep 879991 = 1319987) B1319987
theorem B1666433 : Blo 876568 1666433 := bstep (se 2 (by rfl) ⟨624912, by rfl⟩ : syracuseStep 1666433 = 1249825) B1249825
theorem B880011 : Blo 876568 880011 := bstep (se 1 (by rfl) ⟨660008, by rfl⟩ : syracuseStep 880011 = 1320017) B1320017
theorem B880023 : Blo 876568 880023 := bstep (se 1 (by rfl) ⟨660017, by rfl⟩ : syracuseStep 880023 = 1320035) B1320035
theorem B880043 : Blo 876568 880043 := bstep (se 1 (by rfl) ⟨660032, by rfl⟩ : syracuseStep 880043 = 1320065) B1320065
theorem B2813363 : Blo 876568 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B880055 : Blo 876568 880055 := bstep (se 1 (by rfl) ⟨660041, by rfl⟩ : syracuseStep 880055 = 1320083) B1320083
theorem B880075 : Blo 876568 880075 := bstep (se 1 (by rfl) ⟨660056, by rfl⟩ : syracuseStep 880075 = 1320113) B1320113
theorem B880087 : Blo 876568 880087 := bstep (se 1 (by rfl) ⟨660065, by rfl⟩ : syracuseStep 880087 = 1320131) B1320131
theorem B880107 : Blo 876568 880107 := bstep (se 1 (by rfl) ⟨660080, by rfl⟩ : syracuseStep 880107 = 1320161) B1320161
theorem B880119 : Blo 876568 880119 := bstep (se 1 (by rfl) ⟨660089, by rfl⟩ : syracuseStep 880119 = 1320179) B1320179
theorem B6680069 : Blo 876568 6680069 := bstep (se 4 (by rfl) ⟨626256, by rfl⟩ : syracuseStep 6680069 = 1252513) B1252513
theorem B880139 : Blo 876568 880139 := bstep (se 1 (by rfl) ⟨660104, by rfl⟩ : syracuseStep 880139 = 1320209) B1320209
theorem B880151 : Blo 876568 880151 := bstep (se 1 (by rfl) ⟨660113, by rfl⟩ : syracuseStep 880151 = 1320227) B1320227
theorem B1666585 : Blo 876568 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B880171 : Blo 876568 880171 := bstep (se 1 (by rfl) ⟨660128, by rfl⟩ : syracuseStep 880171 = 1320257) B1320257
theorem B880183 : Blo 876568 880183 := bstep (se 1 (by rfl) ⟨660137, by rfl⟩ : syracuseStep 880183 = 1320275) B1320275
theorem B880203 : Blo 876568 880203 := bstep (se 1 (by rfl) ⟨660152, by rfl⟩ : syracuseStep 880203 = 1320305) B1320305
theorem B880215 : Blo 876568 880215 := bstep (se 1 (by rfl) ⟨660161, by rfl⟩ : syracuseStep 880215 = 1320323) B1320323
theorem B880235 : Blo 876568 880235 := bstep (se 1 (by rfl) ⟨660176, by rfl⟩ : syracuseStep 880235 = 1320353) B1320353
theorem B880247 : Blo 876568 880247 := bstep (se 1 (by rfl) ⟨660185, by rfl⟩ : syracuseStep 880247 = 1320371) B1320371
theorem B880267 : Blo 876568 880267 := bstep (se 1 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 880267 = 1320401) B1320401
theorem B880279 : Blo 876568 880279 := bstep (se 1 (by rfl) ⟨660209, by rfl⟩ : syracuseStep 880279 = 1320419) B1320419
theorem B880299 : Blo 876568 880299 := bstep (se 1 (by rfl) ⟨660224, by rfl⟩ : syracuseStep 880299 = 1320449) B1320449
theorem B880311 : Blo 876568 880311 := bstep (se 1 (by rfl) ⟨660233, by rfl⟩ : syracuseStep 880311 = 1320467) B1320467
theorem B880331 : Blo 876568 880331 := bstep (se 1 (by rfl) ⟨660248, by rfl⟩ : syracuseStep 880331 = 1320497) B1320497
theorem B1404631 : Blo 876568 1404631 := bstep (se 1 (by rfl) ⟨1053473, by rfl⟩ : syracuseStep 1404631 = 2106947) B2106947
theorem B880343 : Blo 876568 880343 := bstep (se 1 (by rfl) ⟨660257, by rfl⟩ : syracuseStep 880343 = 1320515) B1320515
theorem B880363 : Blo 876568 880363 := bstep (se 1 (by rfl) ⟨660272, by rfl⟩ : syracuseStep 880363 = 1320545) B1320545
theorem B880375 : Blo 876568 880375 := bstep (se 1 (by rfl) ⟨660281, by rfl⟩ : syracuseStep 880375 = 1320563) B1320563
theorem B1601281 : Blo 876568 1601281 := bstep (se 2 (by rfl) ⟨600480, by rfl⟩ : syracuseStep 1601281 = 1200961) B1200961
theorem B880395 : Blo 876568 880395 := bstep (se 1 (by rfl) ⟨660296, by rfl⟩ : syracuseStep 880395 = 1320593) B1320593
theorem B2223895 : Blo 876568 2223895 := bstep (se 1 (by rfl) ⟨1667921, by rfl⟩ : syracuseStep 2223895 = 3335843) B3335843
theorem B880407 : Blo 876568 880407 := bstep (se 1 (by rfl) ⟨660305, by rfl⟩ : syracuseStep 880407 = 1320611) B1320611
theorem B880427 : Blo 876568 880427 := bstep (se 1 (by rfl) ⟨660320, by rfl⟩ : syracuseStep 880427 = 1320641) B1320641
theorem B880439 : Blo 876568 880439 := bstep (se 1 (by rfl) ⟨660329, by rfl⟩ : syracuseStep 880439 = 1320659) B1320659
theorem B880459 : Blo 876568 880459 := bstep (se 1 (by rfl) ⟨660344, by rfl⟩ : syracuseStep 880459 = 1320689) B1320689
theorem B880471 : Blo 876568 880471 := bstep (se 1 (by rfl) ⟨660353, by rfl⟩ : syracuseStep 880471 = 1320707) B1320707
theorem B4222813 : Blo 876568 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B880491 : Blo 876568 880491 := bstep (se 1 (by rfl) ⟨660368, by rfl⟩ : syracuseStep 880491 = 1320737) B1320737
theorem B880503 : Blo 876568 880503 := bstep (se 1 (by rfl) ⟨660377, by rfl⟩ : syracuseStep 880503 = 1320755) B1320755
theorem B880523 : Blo 876568 880523 := bstep (se 1 (by rfl) ⟨660392, by rfl⟩ : syracuseStep 880523 = 1320785) B1320785
theorem B880535 : Blo 876568 880535 := bstep (se 1 (by rfl) ⟨660401, by rfl⟩ : syracuseStep 880535 = 1320803) B1320803
theorem B880555 : Blo 876568 880555 := bstep (se 1 (by rfl) ⟨660416, by rfl⟩ : syracuseStep 880555 = 1320833) B1320833
theorem B880567 : Blo 876568 880567 := bstep (se 1 (by rfl) ⟨660425, by rfl⟩ : syracuseStep 880567 = 1320851) B1320851
theorem B1109963 : Blo 876568 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B3338243 : Blo 876568 3338243 := bstep (se 1 (by rfl) ⟨2503682, by rfl⟩ : syracuseStep 3338243 = 5007365) B5007365
theorem B2224331 : Blo 876568 2224331 := bstep (se 1 (by rfl) ⟨1668248, by rfl⟩ : syracuseStep 2224331 = 3336497) B3336497
theorem B4452569 : Blo 876568 4452569 := bstep (se 2 (by rfl) ⟨1669713, by rfl⟩ : syracuseStep 4452569 = 3339427) B3339427
theorem B2814259 : Blo 876568 2814259 := bstep (se 1 (by rfl) ⟨2110694, by rfl⟩ : syracuseStep 2814259 = 4221389) B4221389
theorem B5337419 : Blo 876568 5337419 := bstep (se 1 (by rfl) ⟨4003064, by rfl⟩ : syracuseStep 5337419 = 8006129) B8006129
theorem B1405387 : Blo 876568 1405387 := bstep (se 1 (by rfl) ⟨1054040, by rfl⟩ : syracuseStep 1405387 = 2108081) B2108081
theorem B6844945 : Blo 876568 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B2224705 : Blo 876568 2224705 := bstep (se 2 (by rfl) ⟨834264, by rfl⟩ : syracuseStep 2224705 = 1668529) B1668529
theorem B10678877 : Blo 876568 10678877 := bstep (se 3 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 10678877 = 4004579) B4004579
theorem B1110667 : Blo 876568 1110667 := bstep (se 1 (by rfl) ⟨833000, by rfl⟩ : syracuseStep 1110667 = 1666001) B1666001
theorem B7598771 : Blo 876568 7598771 := bstep (se 1 (by rfl) ⟨5699078, by rfl⟩ : syracuseStep 7598771 = 11398157) B11398157
theorem B1667891 : Blo 876568 1667891 := bstep (se 1 (by rfl) ⟨1250918, by rfl⟩ : syracuseStep 1667891 = 2501837) B2501837
theorem B1110935 : Blo 876568 1110935 := bstep (se 1 (by rfl) ⟨833201, by rfl⟩ : syracuseStep 1110935 = 1666403) B1666403
theorem B1668043 : Blo 876568 1668043 := bstep (se 1 (by rfl) ⟨1251032, by rfl⟩ : syracuseStep 1668043 = 2502065) B2502065
theorem B1504345 : Blo 876568 1504345 := bstep (se 2 (by rfl) ⟨564129, by rfl⟩ : syracuseStep 1504345 = 1128259) B1128259
theorem B2225303 : Blo 876568 2225303 := bstep (se 1 (by rfl) ⟨1668977, by rfl⟩ : syracuseStep 2225303 = 3337955) B3337955
theorem B1668377 : Blo 876568 1668377 := bstep (se 2 (by rfl) ⟨625641, by rfl⟩ : syracuseStep 1668377 = 1251283) B1251283
theorem B6321473 : Blo 876568 6321473 := bstep (se 2 (by rfl) ⟨2370552, by rfl⟩ : syracuseStep 6321473 = 4741105) B4741105
theorem B5010781 : Blo 876568 5010781 := bstep (se 3 (by rfl) ⟨939521, by rfl⟩ : syracuseStep 5010781 = 1879043) B1879043
theorem B1406489 : Blo 876568 1406489 := bstep (se 2 (by rfl) ⟨527433, by rfl⟩ : syracuseStep 1406489 = 1054867) B1054867
theorem B1111639 : Blo 876568 1111639 := bstep (se 1 (by rfl) ⟨833729, by rfl⟩ : syracuseStep 1111639 = 1667459) B1667459
theorem B4454189 : Blo 876568 4454189 := bstep (se 3 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 4454189 = 1670321) B1670321
theorem B6682499 : Blo 876568 6682499 := bstep (se 1 (by rfl) ⟨5011874, by rfl⟩ : syracuseStep 6682499 = 10023749) B10023749
theorem B1669015 : Blo 876568 1669015 := bstep (se 1 (by rfl) ⟨1251761, by rfl⟩ : syracuseStep 1669015 = 2503523) B2503523
theorem B2226113 : Blo 876568 2226113 := bstep (se 2 (by rfl) ⟨834792, by rfl⟩ : syracuseStep 2226113 = 1669585) B1669585
theorem B13760525 : Blo 876568 13760525 := bstep (se 3 (by rfl) ⟨2580098, by rfl⟩ : syracuseStep 13760525 = 5160197) B5160197
theorem B2226649 : Blo 876568 2226649 := bstep (se 2 (by rfl) ⟨834993, by rfl⟩ : syracuseStep 2226649 = 1669987) B1669987
theorem B6421169 : Blo 876568 6421169 := bstep (se 2 (by rfl) ⟨2407938, by rfl⟩ : syracuseStep 6421169 = 4815877) B4815877
theorem B1669835 : Blo 876568 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1669889 : Blo 876568 1669889 := bstep (se 2 (by rfl) ⟨626208, by rfl⟩ : syracuseStep 1669889 = 1252417) B1252417
theorem B6421265 : Blo 876568 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B3341357 : Blo 876568 3341357 := bstep (se 3 (by rfl) ⟨626504, by rfl⟩ : syracuseStep 3341357 = 1253009) B1253009
theorem B1113355 : Blo 876568 1113355 := bstep (se 1 (by rfl) ⟨835016, by rfl⟩ : syracuseStep 1113355 = 1670033) B1670033
theorem B18513197 : Blo 876568 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B3374401 : Blo 876568 3374401 := bstep (se 2 (by rfl) ⟨1265400, by rfl⟩ : syracuseStep 3374401 = 2530801) B2530801
theorem B15007193 : Blo 876568 15007193 := bstep (se 2 (by rfl) ⟨5627697, by rfl⟩ : syracuseStep 15007193 = 11255395) B11255395
theorem B2227763 : Blo 876568 2227763 := bstep (se 1 (by rfl) ⟨1670822, by rfl⟩ : syracuseStep 2227763 = 3341645) B3341645
theorem B7503461 : Blo 876568 7503461 := bstep (se 4 (by rfl) ⟨703449, by rfl⟩ : syracuseStep 7503461 = 1406899) B1406899
theorem B1670807 : Blo 876568 1670807 := bstep (se 1 (by rfl) ⟨1253105, by rfl⟩ : syracuseStep 1670807 = 2506211) B2506211
theorem B3047105 : Blo 876568 3047105 := bstep (se 2 (by rfl) ⟨1142664, by rfl⟩ : syracuseStep 3047105 = 2285329) B2285329
theorem B3342131 : Blo 876568 3342131 := bstep (se 1 (by rfl) ⟨2506598, by rfl⟩ : syracuseStep 3342131 = 5013197) B5013197
theorem B2228057 : Blo 876568 2228057 := bstep (se 2 (by rfl) ⟨835521, by rfl⟩ : syracuseStep 2228057 = 1671043) B1671043
theorem B9633653 : Blo 876568 9633653 := bstep (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) B903155
theorem B5078963 : Blo 876568 5078963 := bstep (se 1 (by rfl) ⟨3809222, by rfl⟩ : syracuseStep 5078963 = 7618445) B7618445
theorem B5013515 : Blo 876568 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B1114231 : Blo 876568 1114231 := bstep (se 1 (by rfl) ⟨835673, by rfl⟩ : syracuseStep 1114231 = 1671347) B1671347
theorem B5013697 : Blo 876568 5013697 := bstep (se 2 (by rfl) ⟨1880136, by rfl⟩ : syracuseStep 5013697 = 3760273) B3760273
theorem B9994589 : Blo 876568 9994589 := bstep (se 3 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 9994589 = 3747971) B3747971
theorem B3047827 : Blo 876568 3047827 := bstep (se 1 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 3047827 = 4571741) B4571741
theorem B2818451 : Blo 876568 2818451 := bstep (se 1 (by rfl) ⟨2113838, by rfl⟩ : syracuseStep 2818451 = 4227677) B4227677
theorem B2818489 : Blo 876568 2818489 := bstep (se 2 (by rfl) ⟨1056933, by rfl⟩ : syracuseStep 2818489 = 2113867) B2113867
theorem B4457267 : Blo 876568 4457267 := bstep (se 1 (by rfl) ⟨3342950, by rfl⟩ : syracuseStep 4457267 = 6685901) B6685901
theorem B4228139 : Blo 876568 4228139 := bstep (se 1 (by rfl) ⟨3171104, by rfl⟩ : syracuseStep 4228139 = 6342209) B6342209
theorem B1410167 : Blo 876568 1410167 := bstep (se 1 (by rfl) ⟨1057625, by rfl⟩ : syracuseStep 1410167 = 2115251) B2115251
theorem B4457591 : Blo 876568 4457591 := bstep (se 1 (by rfl) ⟨3343193, by rfl⟩ : syracuseStep 4457591 = 6686387) B6686387
theorem B36537925 : Blo 876568 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B9996047 : Blo 876568 9996047 := bstep (se 1 (by rfl) ⟨7497035, by rfl⟩ : syracuseStep 9996047 = 14994071) B14994071
theorem B4950245 : Blo 876568 4950245 := bstep (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) B928171
theorem B2820923 : Blo 876568 2820923 := bstep (se 1 (by rfl) ⟨2115692, by rfl⟩ : syracuseStep 2820923 = 4231385) B4231385
theorem B986503 : Blo 876568 986503 := bstep (se 1 (by rfl) ⟨739877, by rfl⟩ : syracuseStep 986503 = 1479755) B1479755
theorem B20254157 : Blo 876568 20254157 := bstep (se 3 (by rfl) ⟨3797654, by rfl⟩ : syracuseStep 20254157 = 7595309) B7595309
theorem B986683 : Blo 876568 986683 := bstep (se 1 (by rfl) ⟨740012, by rfl⟩ : syracuseStep 986683 = 1480025) B1480025
theorem B7606219 : Blo 876568 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B987151 : Blo 876568 987151 := bstep (se 1 (by rfl) ⟨740363, by rfl⟩ : syracuseStep 987151 = 1480727) B1480727
theorem B1314875 : Blo 876568 1314875 := bstep (se 1 (by rfl) ⟨986156, by rfl⟩ : syracuseStep 1314875 = 1972313) B1972313
theorem B1314935 : Blo 876568 1314935 := bstep (se 1 (by rfl) ⟨986201, by rfl⟩ : syracuseStep 1314935 = 1972403) B1972403
theorem B1314959 : Blo 876568 1314959 := bstep (se 1 (by rfl) ⟨986219, by rfl⟩ : syracuseStep 1314959 = 1972439) B1972439
theorem B1315001 : Blo 876568 1315001 := bstep (se 2 (by rfl) ⟨493125, by rfl⟩ : syracuseStep 1315001 = 986251) B986251
theorem B5345473 : Blo 876568 5345473 := bstep (se 2 (by rfl) ⟨2004552, by rfl⟩ : syracuseStep 5345473 = 4009105) B4009105
theorem B1315079 : Blo 876568 1315079 := bstep (se 1 (by rfl) ⟨986309, by rfl⟩ : syracuseStep 1315079 = 1972619) B1972619
theorem B1315115 : Blo 876568 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B21401921 : Blo 876568 21401921 := bstep (se 2 (by rfl) ⟨8025720, by rfl⟩ : syracuseStep 21401921 = 16051441) B16051441
theorem B1315145 : Blo 876568 1315145 := bstep (se 2 (by rfl) ⟨493179, by rfl⟩ : syracuseStep 1315145 = 986359) B986359
theorem B1249609 : Blo 876568 1249609 := bstep (se 2 (by rfl) ⟨468603, by rfl⟩ : syracuseStep 1249609 = 937207) B937207
theorem B1315259 : Blo 876568 1315259 := bstep (se 1 (by rfl) ⟨986444, by rfl⟩ : syracuseStep 1315259 = 1972889) B1972889
theorem B1315319 : Blo 876568 1315319 := bstep (se 1 (by rfl) ⟨986489, by rfl⟩ : syracuseStep 1315319 = 1972979) B1972979
theorem B987655 : Blo 876568 987655 := bstep (se 1 (by rfl) ⟨740741, by rfl⟩ : syracuseStep 987655 = 1481483) B1481483
theorem B1315343 : Blo 876568 1315343 := bstep (se 1 (by rfl) ⟨986507, by rfl⟩ : syracuseStep 1315343 = 1973015) B1973015
theorem B1315385 : Blo 876568 1315385 := bstep (se 2 (by rfl) ⟨493269, by rfl⟩ : syracuseStep 1315385 = 986539) B986539
theorem B1315463 : Blo 876568 1315463 := bstep (se 1 (by rfl) ⟨986597, by rfl⟩ : syracuseStep 1315463 = 1973195) B1973195
theorem B1315499 : Blo 876568 1315499 := bstep (se 1 (by rfl) ⟨986624, by rfl⟩ : syracuseStep 1315499 = 1973249) B1973249
theorem B987835 : Blo 876568 987835 := bstep (se 1 (by rfl) ⟨740876, by rfl⟩ : syracuseStep 987835 = 1481753) B1481753
theorem B1315529 : Blo 876568 1315529 := bstep (se 2 (by rfl) ⟨493323, by rfl⟩ : syracuseStep 1315529 = 986647) B986647
theorem B6656741 : Blo 876568 6656741 := bstep (se 4 (by rfl) ⟨624069, by rfl⟩ : syracuseStep 6656741 = 1248139) B1248139
theorem B9507557 : Blo 876568 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B1315643 : Blo 876568 1315643 := bstep (se 1 (by rfl) ⟨986732, by rfl⟩ : syracuseStep 1315643 = 1973465) B1973465
theorem B1315703 : Blo 876568 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B1250167 : Blo 876568 1250167 := bstep (se 1 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 1250167 = 1875251) B1875251
theorem B1479559 : Blo 876568 1479559 := bstep (se 1 (by rfl) ⟨1109669, by rfl⟩ : syracuseStep 1479559 = 2219339) B2219339
theorem B1315727 : Blo 876568 1315727 := bstep (se 1 (by rfl) ⟨986795, by rfl⟩ : syracuseStep 1315727 = 1973591) B1973591
theorem B15438755 : Blo 876568 15438755 := bstep (se 1 (by rfl) ⟨11579066, by rfl⟩ : syracuseStep 15438755 = 23158133) B23158133
theorem B1315769 : Blo 876568 1315769 := bstep (se 2 (by rfl) ⟨493413, by rfl⟩ : syracuseStep 1315769 = 986827) B986827
theorem B2135041 : Blo 876568 2135041 := bstep (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) B1601281
theorem B1315847 : Blo 876568 1315847 := bstep (se 1 (by rfl) ⟨986885, by rfl⟩ : syracuseStep 1315847 = 1973771) B1973771
theorem B1315883 : Blo 876568 1315883 := bstep (se 1 (by rfl) ⟨986912, by rfl⟩ : syracuseStep 1315883 = 1973825) B1973825
theorem B1315913 : Blo 876568 1315913 := bstep (se 2 (by rfl) ⟨493467, by rfl⟩ : syracuseStep 1315913 = 986935) B986935
theorem B1184887 : Blo 876568 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B988303 : Blo 876568 988303 := bstep (se 1 (by rfl) ⟨741227, by rfl⟩ : syracuseStep 988303 = 1482455) B1482455
theorem B1316027 : Blo 876568 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B10687733 : Blo 876568 10687733 := bstep (se 5 (by rfl) ⟨500987, by rfl⟩ : syracuseStep 10687733 = 1001975) B1001975
theorem B1316087 : Blo 876568 1316087 := bstep (se 1 (by rfl) ⟨987065, by rfl⟩ : syracuseStep 1316087 = 1974131) B1974131
theorem B1316111 : Blo 876568 1316111 := bstep (se 1 (by rfl) ⟨987083, by rfl⟩ : syracuseStep 1316111 = 1974167) B1974167
theorem B1316153 : Blo 876568 1316153 := bstep (se 2 (by rfl) ⟨493557, by rfl⟩ : syracuseStep 1316153 = 987115) B987115
theorem B1316231 : Blo 876568 1316231 := bstep (se 1 (by rfl) ⟨987173, by rfl⟩ : syracuseStep 1316231 = 1974347) B1974347
theorem B1316267 : Blo 876568 1316267 := bstep (se 1 (by rfl) ⟨987200, by rfl⟩ : syracuseStep 1316267 = 1974401) B1974401
theorem B1250731 : Blo 876568 1250731 := bstep (se 1 (by rfl) ⟨938048, by rfl⟩ : syracuseStep 1250731 = 1876097) B1876097
theorem B1316297 : Blo 876568 1316297 := bstep (se 2 (by rfl) ⟨493611, by rfl⟩ : syracuseStep 1316297 = 987223) B987223
theorem B1480207 : Blo 876568 1480207 := bstep (se 1 (by rfl) ⟨1110155, by rfl⟩ : syracuseStep 1480207 = 2220311) B2220311
theorem B1316411 : Blo 876568 1316411 := bstep (se 1 (by rfl) ⟨987308, by rfl⟩ : syracuseStep 1316411 = 1974617) B1974617
theorem B1316471 : Blo 876568 1316471 := bstep (se 1 (by rfl) ⟨987353, by rfl⟩ : syracuseStep 1316471 = 1974707) B1974707
theorem B988807 : Blo 876568 988807 := bstep (se 1 (by rfl) ⟨741605, by rfl⟩ : syracuseStep 988807 = 1483211) B1483211
theorem B1316495 : Blo 876568 1316495 := bstep (se 1 (by rfl) ⟨987371, by rfl⟩ : syracuseStep 1316495 = 1974743) B1974743
theorem B1250959 : Blo 876568 1250959 := bstep (se 1 (by rfl) ⟨938219, by rfl⟩ : syracuseStep 1250959 = 1876439) B1876439
theorem B1316537 : Blo 876568 1316537 := bstep (se 2 (by rfl) ⟨493701, by rfl⟩ : syracuseStep 1316537 = 987403) B987403
theorem B1316615 : Blo 876568 1316615 := bstep (se 1 (by rfl) ⟨987461, by rfl⟩ : syracuseStep 1316615 = 1974923) B1974923
theorem B1316651 : Blo 876568 1316651 := bstep (se 1 (by rfl) ⟨987488, by rfl⟩ : syracuseStep 1316651 = 1974977) B1974977
theorem B988987 : Blo 876568 988987 := bstep (se 1 (by rfl) ⟨741740, by rfl⟩ : syracuseStep 988987 = 1483481) B1483481
theorem B1316681 : Blo 876568 1316681 := bstep (se 2 (by rfl) ⟨493755, by rfl⟩ : syracuseStep 1316681 = 987511) B987511
theorem B1873849 : Blo 876568 1873849 := bstep (se 2 (by rfl) ⟨702693, by rfl⟩ : syracuseStep 1873849 = 1405387) B1405387
theorem B1316795 : Blo 876568 1316795 := bstep (se 1 (by rfl) ⟨987596, by rfl⟩ : syracuseStep 1316795 = 1975193) B1975193
theorem B1316855 : Blo 876568 1316855 := bstep (se 1 (by rfl) ⟨987641, by rfl⟩ : syracuseStep 1316855 = 1975283) B1975283
theorem B1316879 : Blo 876568 1316879 := bstep (se 1 (by rfl) ⟨987659, by rfl⟩ : syracuseStep 1316879 = 1975319) B1975319
theorem B2496541 : Blo 876568 2496541 := bstep (se 3 (by rfl) ⟨468101, by rfl⟩ : syracuseStep 2496541 = 936203) B936203
theorem B1185835 : Blo 876568 1185835 := bstep (se 1 (by rfl) ⟨889376, by rfl⟩ : syracuseStep 1185835 = 1778753) B1778753
theorem B1480747 : Blo 876568 1480747 := bstep (se 1 (by rfl) ⟨1110560, by rfl⟩ : syracuseStep 1480747 = 2221121) B2221121
theorem B1316921 : Blo 876568 1316921 := bstep (se 2 (by rfl) ⟨493845, by rfl⟩ : syracuseStep 1316921 = 987691) B987691
theorem B1316999 : Blo 876568 1316999 := bstep (se 1 (by rfl) ⟨987749, by rfl⟩ : syracuseStep 1316999 = 1975499) B1975499
theorem B1317035 : Blo 876568 1317035 := bstep (se 1 (by rfl) ⟨987776, by rfl⟩ : syracuseStep 1317035 = 1975553) B1975553
theorem B1480889 : Blo 876568 1480889 := bstep (se 2 (by rfl) ⟨555333, by rfl⟩ : syracuseStep 1480889 = 1110667) B1110667
theorem B1317065 : Blo 876568 1317065 := bstep (se 2 (by rfl) ⟨493899, by rfl⟩ : syracuseStep 1317065 = 987799) B987799
theorem B5347565 : Blo 876568 5347565 := bstep (se 3 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 5347565 = 2005337) B2005337
theorem B18290929 : Blo 876568 18290929 := bstep (se 2 (by rfl) ⟨6859098, by rfl⟩ : syracuseStep 18290929 = 13718197) B13718197
theorem B1874191 : Blo 876568 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B989455 : Blo 876568 989455 := bstep (se 1 (by rfl) ⟨742091, by rfl⟩ : syracuseStep 989455 = 1484183) B1484183
theorem B1317179 : Blo 876568 1317179 := bstep (se 1 (by rfl) ⟨987884, by rfl⟩ : syracuseStep 1317179 = 1975769) B1975769
theorem B1317239 : Blo 876568 1317239 := bstep (se 1 (by rfl) ⟨987929, by rfl⟩ : syracuseStep 1317239 = 1975859) B1975859
theorem B1317263 : Blo 876568 1317263 := bstep (se 1 (by rfl) ⟨987947, by rfl⟩ : syracuseStep 1317263 = 1975895) B1975895
theorem B1317305 : Blo 876568 1317305 := bstep (se 2 (by rfl) ⟨493989, by rfl⟩ : syracuseStep 1317305 = 987979) B987979
theorem B1317383 : Blo 876568 1317383 := bstep (se 1 (by rfl) ⟨988037, by rfl⟩ : syracuseStep 1317383 = 1976075) B1976075
theorem B1317419 : Blo 876568 1317419 := bstep (se 1 (by rfl) ⟨988064, by rfl⟩ : syracuseStep 1317419 = 1976129) B1976129
theorem B1808939 : Blo 876568 1808939 := bstep (se 1 (by rfl) ⟨1356704, by rfl⟩ : syracuseStep 1808939 = 2713409) B2713409
theorem B1317449 : Blo 876568 1317449 := bstep (se 2 (by rfl) ⟨494043, by rfl⟩ : syracuseStep 1317449 = 988087) B988087
theorem B1972871 : Blo 876568 1972871 := bstep (se 1 (by rfl) ⟨1479653, by rfl⟩ : syracuseStep 1972871 = 2959307) B2959307
theorem B1186439 : Blo 876568 1186439 := bstep (se 1 (by rfl) ⟨889829, by rfl⟩ : syracuseStep 1186439 = 1779659) B1779659
theorem B1317563 : Blo 876568 1317563 := bstep (se 1 (by rfl) ⟨988172, by rfl⟩ : syracuseStep 1317563 = 1976345) B1976345
theorem B1317623 : Blo 876568 1317623 := bstep (se 1 (by rfl) ⟨988217, by rfl⟩ : syracuseStep 1317623 = 1976435) B1976435
theorem B1252103 : Blo 876568 1252103 := bstep (se 1 (by rfl) ⟨939077, by rfl⟩ : syracuseStep 1252103 = 1878155) B1878155
theorem B989959 : Blo 876568 989959 := bstep (se 1 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 989959 = 1484939) B1484939
theorem B1317647 : Blo 876568 1317647 := bstep (se 1 (by rfl) ⟨988235, by rfl⟩ : syracuseStep 1317647 = 1976471) B1976471
theorem B2005793 : Blo 876568 2005793 := bstep (se 2 (by rfl) ⟨752172, by rfl⟩ : syracuseStep 2005793 = 1504345) B1504345
theorem B1317689 : Blo 876568 1317689 := bstep (se 2 (by rfl) ⟨494133, by rfl⟩ : syracuseStep 1317689 = 988267) B988267
theorem B1973051 : Blo 876568 1973051 := bstep (se 1 (by rfl) ⟨1479788, by rfl⟩ : syracuseStep 1973051 = 2959577) B2959577
theorem B1481591 : Blo 876568 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B1317767 : Blo 876568 1317767 := bstep (se 1 (by rfl) ⟨988325, by rfl⟩ : syracuseStep 1317767 = 1976651) B1976651
theorem B1317803 : Blo 876568 1317803 := bstep (se 1 (by rfl) ⟨988352, by rfl⟩ : syracuseStep 1317803 = 1976705) B1976705
theorem B1973177 : Blo 876568 1973177 := bstep (se 2 (by rfl) ⟨739941, by rfl⟩ : syracuseStep 1973177 = 1479883) B1479883
theorem B990139 : Blo 876568 990139 := bstep (se 1 (by rfl) ⟨742604, by rfl⟩ : syracuseStep 990139 = 1485209) B1485209
theorem B1317833 : Blo 876568 1317833 := bstep (se 2 (by rfl) ⟨494187, by rfl⟩ : syracuseStep 1317833 = 988375) B988375
theorem B1252297 : Blo 876568 1252297 := bstep (se 2 (by rfl) ⟨469611, by rfl⟩ : syracuseStep 1252297 = 939223) B939223
theorem B1317947 : Blo 876568 1317947 := bstep (se 1 (by rfl) ⟨988460, by rfl⟩ : syracuseStep 1317947 = 1976921) B1976921
theorem B1318007 : Blo 876568 1318007 := bstep (se 1 (by rfl) ⟨988505, by rfl⟩ : syracuseStep 1318007 = 1977011) B1977011
theorem B1875079 : Blo 876568 1875079 := bstep (se 1 (by rfl) ⟨1406309, by rfl⟩ : syracuseStep 1875079 = 2812619) B2812619
theorem B1318031 : Blo 876568 1318031 := bstep (se 1 (by rfl) ⟨988523, by rfl⟩ : syracuseStep 1318031 = 1977047) B1977047
theorem B1318073 : Blo 876568 1318073 := bstep (se 2 (by rfl) ⟨494277, by rfl⟩ : syracuseStep 1318073 = 988555) B988555
theorem B1318151 : Blo 876568 1318151 := bstep (se 1 (by rfl) ⟨988613, by rfl⟩ : syracuseStep 1318151 = 1977227) B1977227
theorem B1973519 : Blo 876568 1973519 := bstep (se 1 (by rfl) ⟨1480139, by rfl⟩ : syracuseStep 1973519 = 2960279) B2960279
theorem B1973537 : Blo 876568 1973537 := bstep (se 2 (by rfl) ⟨740076, by rfl⟩ : syracuseStep 1973537 = 1480153) B1480153
theorem B1318187 : Blo 876568 1318187 := bstep (se 1 (by rfl) ⟨988640, by rfl⟩ : syracuseStep 1318187 = 1977281) B1977281
theorem B1482043 : Blo 876568 1482043 := bstep (se 1 (by rfl) ⟨1111532, by rfl⟩ : syracuseStep 1482043 = 2223065) B2223065
theorem B1318217 : Blo 876568 1318217 := bstep (se 2 (by rfl) ⟨494331, by rfl⟩ : syracuseStep 1318217 = 988663) B988663
theorem B6495623 : Blo 876568 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B990607 : Blo 876568 990607 := bstep (se 1 (by rfl) ⟨742955, by rfl⟩ : syracuseStep 990607 = 1485911) B1485911
theorem B1318331 : Blo 876568 1318331 := bstep (se 1 (by rfl) ⟨988748, by rfl⟩ : syracuseStep 1318331 = 1977497) B1977497
theorem B1482185 : Blo 876568 1482185 := bstep (se 2 (by rfl) ⟨555819, by rfl⟩ : syracuseStep 1482185 = 1111639) B1111639
theorem B1318391 : Blo 876568 1318391 := bstep (se 1 (by rfl) ⟨988793, by rfl⟩ : syracuseStep 1318391 = 1977587) B1977587
theorem B1252855 : Blo 876568 1252855 := bstep (se 1 (by rfl) ⟨939641, by rfl⟩ : syracuseStep 1252855 = 1879283) B1879283
theorem B1318415 : Blo 876568 1318415 := bstep (se 1 (by rfl) ⟨988811, by rfl⟩ : syracuseStep 1318415 = 1977623) B1977623
theorem B1318457 : Blo 876568 1318457 := bstep (se 2 (by rfl) ⟨494421, by rfl⟩ : syracuseStep 1318457 = 988843) B988843
theorem B1973879 : Blo 876568 1973879 := bstep (se 1 (by rfl) ⟨1480409, by rfl⟩ : syracuseStep 1973879 = 2960819) B2960819
theorem B1875575 : Blo 876568 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B1318535 : Blo 876568 1318535 := bstep (se 1 (by rfl) ⟨988901, by rfl⟩ : syracuseStep 1318535 = 1977803) B1977803
theorem B1318571 : Blo 876568 1318571 := bstep (se 1 (by rfl) ⟨988928, by rfl⟩ : syracuseStep 1318571 = 1977857) B1977857
theorem B1318601 : Blo 876568 1318601 := bstep (se 2 (by rfl) ⟨494475, by rfl⟩ : syracuseStep 1318601 = 988951) B988951
theorem B1974059 : Blo 876568 1974059 := bstep (se 1 (by rfl) ⟨1480544, by rfl⟩ : syracuseStep 1974059 = 2961089) B2961089
theorem B1318715 : Blo 876568 1318715 := bstep (se 1 (by rfl) ⟨989036, by rfl⟩ : syracuseStep 1318715 = 1978073) B1978073
theorem B1318775 : Blo 876568 1318775 := bstep (se 1 (by rfl) ⟨989081, by rfl⟩ : syracuseStep 1318775 = 1978163) B1978163
theorem B1318799 : Blo 876568 1318799 := bstep (se 1 (by rfl) ⟨989099, by rfl⟩ : syracuseStep 1318799 = 1978199) B1978199
theorem B2498489 : Blo 876568 2498489 := bstep (se 2 (by rfl) ⟨936933, by rfl⟩ : syracuseStep 2498489 = 1873867) B1873867
theorem B1318841 : Blo 876568 1318841 := bstep (se 2 (by rfl) ⟨494565, by rfl⟩ : syracuseStep 1318841 = 989131) B989131
theorem B1187785 : Blo 876568 1187785 := bstep (se 2 (by rfl) ⟨445419, by rfl⟩ : syracuseStep 1187785 = 890839) B890839
theorem B1318919 : Blo 876568 1318919 := bstep (se 1 (by rfl) ⟨989189, by rfl⟩ : syracuseStep 1318919 = 1978379) B1978379
theorem B1318955 : Blo 876568 1318955 := bstep (se 1 (by rfl) ⟨989216, by rfl⟩ : syracuseStep 1318955 = 1978433) B1978433
theorem B1318985 : Blo 876568 1318985 := bstep (se 2 (by rfl) ⟨494619, by rfl⟩ : syracuseStep 1318985 = 989239) B989239
theorem B1482887 : Blo 876568 1482887 := bstep (se 1 (by rfl) ⟨1112165, by rfl⟩ : syracuseStep 1482887 = 2224331) B2224331
theorem B1974419 : Blo 876568 1974419 := bstep (se 1 (by rfl) ⟨1480814, by rfl⟩ : syracuseStep 1974419 = 2961629) B2961629
theorem B1253561 : Blo 876568 1253561 := bstep (se 2 (by rfl) ⟨470085, by rfl⟩ : syracuseStep 1253561 = 940171) B940171
theorem B1319099 : Blo 876568 1319099 := bstep (se 1 (by rfl) ⟨989324, by rfl⟩ : syracuseStep 1319099 = 1978649) B1978649
theorem B1974473 : Blo 876568 1974473 := bstep (se 2 (by rfl) ⟨740427, by rfl⟩ : syracuseStep 1974473 = 1480855) B1480855
theorem B1319159 : Blo 876568 1319159 := bstep (se 1 (by rfl) ⟨989369, by rfl⟩ : syracuseStep 1319159 = 1978739) B1978739
theorem B1319183 : Blo 876568 1319183 := bstep (se 1 (by rfl) ⟨989387, by rfl⟩ : syracuseStep 1319183 = 1978775) B1978775
theorem B1253647 : Blo 876568 1253647 := bstep (se 1 (by rfl) ⟨940235, by rfl⟩ : syracuseStep 1253647 = 1880471) B1880471
theorem B1253675 : Blo 876568 1253675 := bstep (se 1 (by rfl) ⟨940256, by rfl⟩ : syracuseStep 1253675 = 1880513) B1880513
theorem B1319225 : Blo 876568 1319225 := bstep (se 2 (by rfl) ⟨494709, by rfl⟩ : syracuseStep 1319225 = 989419) B989419
theorem B1319303 : Blo 876568 1319303 := bstep (se 1 (by rfl) ⟨989477, by rfl⟩ : syracuseStep 1319303 = 1978955) B1978955
theorem B7119251 : Blo 876568 7119251 := bstep (se 1 (by rfl) ⟨5339438, by rfl⟩ : syracuseStep 7119251 = 10678877) B10678877
theorem B1319339 : Blo 876568 1319339 := bstep (se 1 (by rfl) ⟨989504, by rfl⟩ : syracuseStep 1319339 = 1979009) B1979009
theorem B1188283 : Blo 876568 1188283 := bstep (se 1 (by rfl) ⟨891212, by rfl⟩ : syracuseStep 1188283 = 1782425) B1782425
theorem B1319369 : Blo 876568 1319369 := bstep (se 2 (by rfl) ⟨494763, by rfl⟩ : syracuseStep 1319369 = 989527) B989527
theorem B5710301 : Blo 876568 5710301 := bstep (se 3 (by rfl) ⟨1070681, by rfl⟩ : syracuseStep 5710301 = 2141363) B2141363
theorem B1319483 : Blo 876568 1319483 := bstep (se 1 (by rfl) ⟨989612, by rfl⟩ : syracuseStep 1319483 = 1979225) B1979225
theorem B1319543 : Blo 876568 1319543 := bstep (se 1 (by rfl) ⟨989657, by rfl⟩ : syracuseStep 1319543 = 1979315) B1979315
theorem B1319567 : Blo 876568 1319567 := bstep (se 1 (by rfl) ⟨989675, by rfl⟩ : syracuseStep 1319567 = 1979351) B1979351
theorem B1319609 : Blo 876568 1319609 := bstep (se 2 (by rfl) ⟨494853, by rfl⟩ : syracuseStep 1319609 = 989707) B989707
theorem B1319687 : Blo 876568 1319687 := bstep (se 1 (by rfl) ⟨989765, by rfl⟩ : syracuseStep 1319687 = 1979531) B1979531
theorem B1483535 : Blo 876568 1483535 := bstep (se 1 (by rfl) ⟨1112651, by rfl⟩ : syracuseStep 1483535 = 2225303) B2225303
theorem B1319723 : Blo 876568 1319723 := bstep (se 1 (by rfl) ⟨989792, by rfl⟩ : syracuseStep 1319723 = 1979585) B1979585
theorem B1319753 : Blo 876568 1319753 := bstep (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) B989815
theorem B1975175 : Blo 876568 1975175 := bstep (se 1 (by rfl) ⟨1481381, by rfl⟩ : syracuseStep 1975175 = 2962763) B2962763
theorem B1319867 : Blo 876568 1319867 := bstep (se 1 (by rfl) ⟨989900, by rfl⟩ : syracuseStep 1319867 = 1979801) B1979801
theorem B1319927 : Blo 876568 1319927 := bstep (se 1 (by rfl) ⟨989945, by rfl⟩ : syracuseStep 1319927 = 1979891) B1979891
theorem B1319951 : Blo 876568 1319951 := bstep (se 1 (by rfl) ⟨989963, by rfl⟩ : syracuseStep 1319951 = 1979927) B1979927
theorem B1319993 : Blo 876568 1319993 := bstep (se 2 (by rfl) ⟨494997, by rfl⟩ : syracuseStep 1319993 = 989995) B989995
theorem B1975355 : Blo 876568 1975355 := bstep (se 1 (by rfl) ⟨1481516, by rfl⟩ : syracuseStep 1975355 = 2963033) B2963033
theorem B1320071 : Blo 876568 1320071 := bstep (se 1 (by rfl) ⟨990053, by rfl⟩ : syracuseStep 1320071 = 1980107) B1980107
theorem B2499731 : Blo 876568 2499731 := bstep (se 1 (by rfl) ⟨1874798, by rfl⟩ : syracuseStep 2499731 = 3749597) B3749597
theorem B1320107 : Blo 876568 1320107 := bstep (se 1 (by rfl) ⟨990080, by rfl⟩ : syracuseStep 1320107 = 1980161) B1980161
theorem B1975481 : Blo 876568 1975481 := bstep (se 2 (by rfl) ⟨740805, by rfl⟩ : syracuseStep 1975481 = 1481611) B1481611
theorem B1320137 : Blo 876568 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B1484075 : Blo 876568 1484075 := bstep (se 1 (by rfl) ⟨1113056, by rfl⟩ : syracuseStep 1484075 = 2226113) B2226113
theorem B1320251 : Blo 876568 1320251 := bstep (se 1 (by rfl) ⟨990188, by rfl⟩ : syracuseStep 1320251 = 1980377) B1980377
theorem B1320311 : Blo 876568 1320311 := bstep (se 1 (by rfl) ⟨990233, by rfl⟩ : syracuseStep 1320311 = 1980467) B1980467
theorem B1320335 : Blo 876568 1320335 := bstep (se 1 (by rfl) ⟨990251, by rfl⟩ : syracuseStep 1320335 = 1980503) B1980503
theorem B1320377 : Blo 876568 1320377 := bstep (se 2 (by rfl) ⟨495141, by rfl⟩ : syracuseStep 1320377 = 990283) B990283
theorem B1320455 : Blo 876568 1320455 := bstep (se 1 (by rfl) ⟨990341, by rfl⟩ : syracuseStep 1320455 = 1980683) B1980683
theorem B1975823 : Blo 876568 1975823 := bstep (se 1 (by rfl) ⟨1481867, by rfl⟩ : syracuseStep 1975823 = 2963735) B2963735
theorem B1975841 : Blo 876568 1975841 := bstep (se 2 (by rfl) ⟨740940, by rfl⟩ : syracuseStep 1975841 = 1481881) B1481881
theorem B1320491 : Blo 876568 1320491 := bstep (se 1 (by rfl) ⟨990368, by rfl⟩ : syracuseStep 1320491 = 1980737) B1980737
theorem B1320521 : Blo 876568 1320521 := bstep (se 2 (by rfl) ⟨495195, by rfl⟩ : syracuseStep 1320521 = 990391) B990391
theorem B1484473 : Blo 876568 1484473 := bstep (se 2 (by rfl) ⟨556677, by rfl⟩ : syracuseStep 1484473 = 1113355) B1113355
theorem B1320635 : Blo 876568 1320635 := bstep (se 1 (by rfl) ⟨990476, by rfl⟩ : syracuseStep 1320635 = 1980953) B1980953
theorem B2107081 : Blo 876568 2107081 := bstep (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) B1580311
theorem B1779401 : Blo 876568 1779401 := bstep (se 2 (by rfl) ⟨667275, by rfl⟩ : syracuseStep 1779401 = 1334551) B1334551
theorem B1320695 : Blo 876568 1320695 := bstep (se 1 (by rfl) ⟨990521, by rfl⟩ : syracuseStep 1320695 = 1981043) B1981043
theorem B4499201 : Blo 876568 4499201 := bstep (se 2 (by rfl) ⟨1687200, by rfl⟩ : syracuseStep 4499201 = 3374401) B3374401
theorem B1320719 : Blo 876568 1320719 := bstep (se 1 (by rfl) ⟨990539, by rfl⟩ : syracuseStep 1320719 = 1981079) B1981079
theorem B1320761 : Blo 876568 1320761 := bstep (se 2 (by rfl) ⟨495285, by rfl⟩ : syracuseStep 1320761 = 990571) B990571
theorem B2107255 : Blo 876568 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B1976183 : Blo 876568 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B1320839 : Blo 876568 1320839 := bstep (se 1 (by rfl) ⟨990629, by rfl⟩ : syracuseStep 1320839 = 1981259) B1981259
theorem B1976363 : Blo 876568 1976363 := bstep (se 1 (by rfl) ⟨1482272, by rfl⟩ : syracuseStep 1976363 = 2964545) B2964545
theorem B1190089 : Blo 876568 1190089 := bstep (se 2 (by rfl) ⟨446283, by rfl⟩ : syracuseStep 1190089 = 892567) B892567
theorem B2959631 : Blo 876568 2959631 := bstep (se 1 (by rfl) ⟨2219723, by rfl⟩ : syracuseStep 2959631 = 4439447) B4439447
theorem B10004795 : Blo 876568 10004795 := bstep (se 1 (by rfl) ⟨7503596, by rfl⟩ : syracuseStep 10004795 = 15007193) B15007193
theorem B1485175 : Blo 876568 1485175 := bstep (se 1 (by rfl) ⟨1113881, by rfl⟩ : syracuseStep 1485175 = 2227763) B2227763
theorem B3746195 : Blo 876568 3746195 := bstep (se 1 (by rfl) ⟨2809646, by rfl⟩ : syracuseStep 3746195 = 5619293) B5619293
theorem B1976723 : Blo 876568 1976723 := bstep (se 1 (by rfl) ⟨1482542, by rfl⟩ : syracuseStep 1976723 = 2965085) B2965085
theorem B1976777 : Blo 876568 1976777 := bstep (se 2 (by rfl) ⟨741291, by rfl⟩ : syracuseStep 1976777 = 1482583) B1482583
theorem B2501131 : Blo 876568 2501131 := bstep (se 1 (by rfl) ⟨1875848, by rfl⟩ : syracuseStep 2501131 = 3751697) B3751697
theorem B2107919 : Blo 876568 2107919 := bstep (se 1 (by rfl) ⟨1580939, by rfl⟩ : syracuseStep 2107919 = 3161879) B3161879
theorem B2959901 : Blo 876568 2959901 := bstep (se 3 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 2959901 = 1109963) B1109963
theorem B1485371 : Blo 876568 1485371 := bstep (se 1 (by rfl) ⟨1114028, by rfl⟩ : syracuseStep 1485371 = 2228057) B2228057
theorem B3385975 : Blo 876568 3385975 := bstep (se 1 (by rfl) ⟨2539481, by rfl⟩ : syracuseStep 3385975 = 5078963) B5078963
theorem B2501405 : Blo 876568 2501405 := bstep (se 3 (by rfl) ⟨469013, by rfl⟩ : syracuseStep 2501405 = 938027) B938027
theorem B1485769 : Blo 876568 1485769 := bstep (se 2 (by rfl) ⟨557163, by rfl⟩ : syracuseStep 1485769 = 1114327) B1114327
theorem B1977479 : Blo 876568 1977479 := bstep (se 1 (by rfl) ⟨1483109, by rfl⟩ : syracuseStep 1977479 = 2966219) B2966219
theorem B2665657 : Blo 876568 2665657 := bstep (se 2 (by rfl) ⟨999621, by rfl⟩ : syracuseStep 2665657 = 1999243) B1999243
theorem B1977659 : Blo 876568 1977659 := bstep (se 1 (by rfl) ⟨1483244, by rfl⟩ : syracuseStep 1977659 = 2966489) B2966489
theorem B1977785 : Blo 876568 1977785 := bstep (se 2 (by rfl) ⟨741669, by rfl⟩ : syracuseStep 1977785 = 1483339) B1483339
theorem B17346001 : Blo 876568 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B14233117 : Blo 876568 14233117 := bstep (se 3 (by rfl) ⟨2668709, by rfl⟩ : syracuseStep 14233117 = 5337419) B5337419
theorem B25636493 : Blo 876568 25636493 := bstep (se 3 (by rfl) ⟨4806842, by rfl⟩ : syracuseStep 25636493 = 9613685) B9613685
theorem B1978127 : Blo 876568 1978127 := bstep (se 1 (by rfl) ⟨1483595, by rfl⟩ : syracuseStep 1978127 = 2967191) B2967191
theorem B1978145 : Blo 876568 1978145 := bstep (se 2 (by rfl) ⟨741804, by rfl⟩ : syracuseStep 1978145 = 1483609) B1483609
theorem B15249221 : Blo 876568 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B2666375 : Blo 876568 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B3387271 : Blo 876568 3387271 := bstep (se 1 (by rfl) ⟨2540453, by rfl⟩ : syracuseStep 3387271 = 5080907) B5080907
theorem B2109331 : Blo 876568 2109331 := bstep (se 1 (by rfl) ⟨1581998, by rfl⟩ : syracuseStep 2109331 = 3163997) B3163997
theorem B2961305 : Blo 876568 2961305 := bstep (se 2 (by rfl) ⟨1110489, by rfl⟩ : syracuseStep 2961305 = 2220979) B2220979
theorem B22556717 : Blo 876568 22556717 := bstep (se 3 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 22556717 = 8458769) B8458769
theorem B2371699 : Blo 876568 2371699 := bstep (se 1 (by rfl) ⟨1778774, by rfl⟩ : syracuseStep 2371699 = 3557549) B3557549
theorem B1978487 : Blo 876568 1978487 := bstep (se 1 (by rfl) ⟨1483865, by rfl⟩ : syracuseStep 1978487 = 2967731) B2967731
theorem B1978667 : Blo 876568 1978667 := bstep (se 1 (by rfl) ⟨1484000, by rfl⟩ : syracuseStep 1978667 = 2968001) B2968001
theorem B2667019 : Blo 876568 2667019 := bstep (se 1 (by rfl) ⟨2000264, by rfl⟩ : syracuseStep 2667019 = 4000529) B4000529
theorem B4993559 : Blo 876568 4993559 := bstep (se 1 (by rfl) ⟨3745169, by rfl⟩ : syracuseStep 4993559 = 7490339) B7490339
theorem B2109995 : Blo 876568 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B2962007 : Blo 876568 2962007 := bstep (se 1 (by rfl) ⟨2221505, by rfl⟩ : syracuseStep 2962007 = 4443011) B4443011
theorem B1979027 : Blo 876568 1979027 := bstep (se 1 (by rfl) ⟨1484270, by rfl⟩ : syracuseStep 1979027 = 2968541) B2968541
theorem B1979081 : Blo 876568 1979081 := bstep (se 2 (by rfl) ⟨742155, by rfl⟩ : syracuseStep 1979081 = 1484311) B1484311
theorem B2962493 : Blo 876568 2962493 := bstep (se 3 (by rfl) ⟨555467, by rfl⟩ : syracuseStep 2962493 = 1110935) B1110935
theorem B4011095 : Blo 876568 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B2503865 : Blo 876568 2503865 := bstep (se 2 (by rfl) ⟨938949, by rfl⟩ : syracuseStep 2503865 = 1877899) B1877899
theorem B2503979 : Blo 876568 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B1979783 : Blo 876568 1979783 := bstep (se 1 (by rfl) ⟨1484837, by rfl⟩ : syracuseStep 1979783 = 2969675) B2969675
theorem B1979963 : Blo 876568 1979963 := bstep (se 1 (by rfl) ⟨1484972, by rfl⟩ : syracuseStep 1979963 = 2969945) B2969945
theorem B1980089 : Blo 876568 1980089 := bstep (se 2 (by rfl) ⟨742533, by rfl⟩ : syracuseStep 1980089 = 1485067) B1485067
theorem B2111177 : Blo 876568 2111177 := bstep (se 2 (by rfl) ⟨791691, by rfl⟩ : syracuseStep 2111177 = 1583383) B1583383
theorem B2111503 : Blo 876568 2111503 := bstep (se 1 (by rfl) ⟨1583627, by rfl⟩ : syracuseStep 2111503 = 3167255) B3167255
theorem B1980431 : Blo 876568 1980431 := bstep (se 1 (by rfl) ⟨1485323, by rfl⟩ : syracuseStep 1980431 = 2970647) B2970647
theorem B1980449 : Blo 876568 1980449 := bstep (se 2 (by rfl) ⟨742668, by rfl⟩ : syracuseStep 1980449 = 1485337) B1485337
theorem B1980791 : Blo 876568 1980791 := bstep (se 1 (by rfl) ⟨1485593, by rfl⟩ : syracuseStep 1980791 = 2971187) B2971187
theorem B7125383 : Blo 876568 7125383 := bstep (se 1 (by rfl) ⟨5344037, by rfl⟩ : syracuseStep 7125383 = 10688075) B10688075
theorem B2505107 : Blo 876568 2505107 := bstep (se 1 (by rfl) ⟨1878830, by rfl⟩ : syracuseStep 2505107 = 3757661) B3757661
theorem B2963897 : Blo 876568 2963897 := bstep (se 2 (by rfl) ⟨1111461, by rfl⟩ : syracuseStep 2963897 = 2222923) B2222923
theorem B4438475 : Blo 876568 4438475 := bstep (se 1 (by rfl) ⟨3328856, by rfl⟩ : syracuseStep 4438475 = 6657713) B6657713
theorem B1980971 : Blo 876568 1980971 := bstep (se 1 (by rfl) ⟨1485728, by rfl⟩ : syracuseStep 1980971 = 2971457) B2971457
theorem B2112119 : Blo 876568 2112119 := bstep (se 1 (by rfl) ⟨1584089, by rfl⟩ : syracuseStep 2112119 = 3168179) B3168179
theorem B3750637 : Blo 876568 3750637 := bstep (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) B1406489
theorem B4438799 : Blo 876568 4438799 := bstep (se 1 (by rfl) ⟨3329099, by rfl⟩ : syracuseStep 4438799 = 6658199) B6658199
theorem B2505505 : Blo 876568 2505505 := bstep (se 2 (by rfl) ⟨939564, by rfl⟩ : syracuseStep 2505505 = 1879129) B1879129
theorem B1784695 : Blo 876568 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B2964491 : Blo 876568 2964491 := bstep (se 1 (by rfl) ⟨2223368, by rfl⟩ : syracuseStep 2964491 = 4446737) B4446737
theorem B2964599 : Blo 876568 2964599 := bstep (se 1 (by rfl) ⟨2223449, by rfl⟩ : syracuseStep 2964599 = 4446899) B4446899
theorem B69483835 : Blo 876568 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B3554695 : Blo 876568 3554695 := bstep (se 1 (by rfl) ⟨2666021, by rfl⟩ : syracuseStep 3554695 = 5332043) B5332043
theorem B4996727 : Blo 876568 4996727 := bstep (se 1 (by rfl) ⟨3747545, by rfl⟩ : syracuseStep 4996727 = 7495091) B7495091
theorem B2506393 : Blo 876568 2506393 := bstep (se 2 (by rfl) ⟨939897, by rfl⟩ : syracuseStep 2506393 = 1879795) B1879795
theorem B2965193 : Blo 876568 2965193 := bstep (se 2 (by rfl) ⟨1111947, by rfl⟩ : syracuseStep 2965193 = 2223895) B2223895
theorem B24035123 : Blo 876568 24035123 := bstep (se 1 (by rfl) ⟨18026342, by rfl⟩ : syracuseStep 24035123 = 36052685) B36052685
theorem B10665931 : Blo 876568 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B6340619 : Blo 876568 6340619 := bstep (se 1 (by rfl) ⟨4755464, by rfl⟩ : syracuseStep 6340619 = 9510929) B9510929
theorem B2506781 : Blo 876568 2506781 := bstep (se 3 (by rfl) ⟨470021, by rfl⟩ : syracuseStep 2506781 = 940043) B940043
theorem B9519191 : Blo 876568 9519191 := bstep (se 1 (by rfl) ⟨7139393, by rfl⟩ : syracuseStep 9519191 = 14278787) B14278787
theorem B4440257 : Blo 876568 4440257 := bstep (se 2 (by rfl) ⟨1665096, by rfl⟩ : syracuseStep 4440257 = 3330193) B3330193
theorem B2965895 : Blo 876568 2965895 := bstep (se 1 (by rfl) ⟨2224421, by rfl⟩ : syracuseStep 2965895 = 4448843) B4448843
theorem B3752345 : Blo 876568 3752345 := bstep (se 2 (by rfl) ⟨1407129, by rfl⟩ : syracuseStep 3752345 = 2814259) B2814259
theorem B9126593 : Blo 876568 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B2966273 : Blo 876568 2966273 := bstep (se 2 (by rfl) ⟨1112352, by rfl⟩ : syracuseStep 2966273 = 2224705) B2224705
theorem B7128265 : Blo 876568 7128265 := bstep (se 2 (by rfl) ⟨2673099, by rfl⟩ : syracuseStep 7128265 = 5346199) B5346199
theorem B2114761 : Blo 876568 2114761 := bstep (se 2 (by rfl) ⟨793035, by rfl⟩ : syracuseStep 2114761 = 1586071) B1586071
theorem B3556723 : Blo 876568 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B2114963 : Blo 876568 2114963 := bstep (se 1 (by rfl) ⟨1586222, by rfl⟩ : syracuseStep 2114963 = 3172445) B3172445
theorem B4572569 : Blo 876568 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B4441553 : Blo 876568 4441553 := bstep (se 2 (by rfl) ⟨1665582, by rfl⟩ : syracuseStep 4441553 = 3331165) B3331165
theorem B2967083 : Blo 876568 2967083 := bstep (se 1 (by rfl) ⟨2225312, by rfl⟩ : syracuseStep 2967083 = 4450625) B4450625
theorem B2377259 : Blo 876568 2377259 := bstep (se 1 (by rfl) ⟨1782944, by rfl⟩ : syracuseStep 2377259 = 3565889) B3565889
theorem B3163735 : Blo 876568 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B6342437 : Blo 876568 6342437 := bstep (se 4 (by rfl) ⟨594603, by rfl⟩ : syracuseStep 6342437 = 1189207) B1189207
theorem B9488785 : Blo 876568 9488785 := bstep (se 2 (by rfl) ⟨3558294, by rfl⟩ : syracuseStep 9488785 = 7116589) B7116589
theorem B3328523 : Blo 876568 3328523 := bstep (se 1 (by rfl) ⟨2496392, by rfl⟩ : syracuseStep 3328523 = 4992785) B4992785
theorem B8440625 : Blo 876568 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B2968379 : Blo 876568 2968379 := bstep (se 1 (by rfl) ⟨2226284, by rfl⟩ : syracuseStep 2968379 = 4452569) B4452569
theorem B5065847 : Blo 876568 5065847 := bstep (se 1 (by rfl) ⟨3799385, by rfl⟩ : syracuseStep 5065847 = 7598771) B7598771
theorem B5000393 : Blo 876568 5000393 := bstep (se 2 (by rfl) ⟨1875147, by rfl⟩ : syracuseStep 5000393 = 3750295) B3750295
theorem B2968865 : Blo 876568 2968865 := bstep (se 2 (by rfl) ⟨1113324, by rfl⟩ : syracuseStep 2968865 = 2226649) B2226649
theorem B2674073 : Blo 876568 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B5426635 : Blo 876568 5426635 := bstep (se 1 (by rfl) ⟨4069976, by rfl⟩ : syracuseStep 5426635 = 8139953) B8139953
theorem B4443659 : Blo 876568 4443659 := bstep (se 1 (by rfl) ⟨3332744, by rfl⟩ : syracuseStep 4443659 = 6665489) B6665489
theorem B4214315 : Blo 876568 4214315 := bstep (se 1 (by rfl) ⟨3160736, by rfl⟩ : syracuseStep 4214315 = 6321473) B6321473
theorem B4443821 : Blo 876568 4443821 := bstep (se 3 (by rfl) ⟨833216, by rfl⟩ : syracuseStep 4443821 = 1666433) B1666433
theorem B10145459 : Blo 876568 10145459 := bstep (se 1 (by rfl) ⟨7609094, by rfl⟩ : syracuseStep 10145459 = 15218189) B15218189
theorem B76992257 : Blo 876568 76992257 := bstep (se 2 (by rfl) ⟨28872096, by rfl⟩ : syracuseStep 76992257 = 57744193) B57744193
theorem B7491365 : Blo 876568 7491365 := bstep (se 4 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 7491365 = 1404631) B1404631
theorem B2969459 : Blo 876568 2969459 := bstep (se 1 (by rfl) ⟨2227094, by rfl⟩ : syracuseStep 2969459 = 4454189) B4454189
theorem B4280779 : Blo 876568 4280779 := bstep (se 1 (by rfl) ⟨3210584, by rfl⟩ : syracuseStep 4280779 = 6421169) B6421169
theorem B4280843 : Blo 876568 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B3330679 : Blo 876568 3330679 := bstep (se 1 (by rfl) ⟨2498009, by rfl⟩ : syracuseStep 3330679 = 4996019) B4996019
theorem B12342131 : Blo 876568 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B4740049 : Blo 876568 4740049 := bstep (se 2 (by rfl) ⟨1777518, by rfl⟩ : syracuseStep 4740049 = 3555037) B3555037
theorem B5002307 : Blo 876568 5002307 := bstep (se 1 (by rfl) ⟨3751730, by rfl⟩ : syracuseStep 5002307 = 7503461) B7503461
theorem B4445441 : Blo 876568 4445441 := bstep (se 2 (by rfl) ⟨1667040, by rfl⟩ : syracuseStep 4445441 = 3334081) B3334081
theorem B41178545 : Blo 876568 41178545 := bstep (se 2 (by rfl) ⟨15441954, by rfl⟩ : syracuseStep 41178545 = 30883909) B30883909
theorem B3331651 : Blo 876568 3331651 := bstep (se 1 (by rfl) ⟨2498738, by rfl⟩ : syracuseStep 3331651 = 4997477) B4997477
theorem B3331955 : Blo 876568 3331955 := bstep (se 1 (by rfl) ⟨2498966, by rfl⟩ : syracuseStep 3331955 = 4997933) B4997933
theorem B12638105 : Blo 876568 12638105 := bstep (se 2 (by rfl) ⟨4739289, by rfl⟩ : syracuseStep 12638105 = 9478579) B9478579
theorem B1333255 : Blo 876568 1333255 := bstep (se 1 (by rfl) ⟨999941, by rfl⟩ : syracuseStep 1333255 = 1999883) B1999883
theorem B4446251 : Blo 876568 4446251 := bstep (se 1 (by rfl) ⟨3334688, by rfl⟩ : syracuseStep 4446251 = 6669377) B6669377
theorem B3332411 : Blo 876568 3332411 := bstep (se 1 (by rfl) ⟨2499308, by rfl⟩ : syracuseStep 3332411 = 4998617) B4998617
theorem B2808199 : Blo 876568 2808199 := bstep (se 1 (by rfl) ⟨2106149, by rfl⟩ : syracuseStep 2808199 = 4212299) B4212299
theorem B2808211 : Blo 876568 2808211 := bstep (se 1 (by rfl) ⟨2106158, by rfl⟩ : syracuseStep 2808211 = 4212317) B4212317
theorem B2677139 : Blo 876568 2677139 := bstep (se 1 (by rfl) ⟨2007854, by rfl⟩ : syracuseStep 2677139 = 4015709) B4015709
theorem B1333675 : Blo 876568 1333675 := bstep (se 1 (by rfl) ⟨1000256, by rfl⟩ : syracuseStep 1333675 = 2000513) B2000513
theorem B3005185 : Blo 876568 3005185 := bstep (se 2 (by rfl) ⟨1126944, by rfl⟩ : syracuseStep 3005185 = 2253889) B2253889
theorem B3332897 : Blo 876568 3332897 := bstep (se 2 (by rfl) ⟨1249836, by rfl⟩ : syracuseStep 3332897 = 2499673) B2499673
theorem B4512829 : Blo 876568 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B1269049 : Blo 876568 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B4447547 : Blo 876568 4447547 := bstep (se 1 (by rfl) ⟨3335660, by rfl⟩ : syracuseStep 4447547 = 6671321) B6671321
theorem B4742489 : Blo 876568 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B4447709 : Blo 876568 4447709 := bstep (se 3 (by rfl) ⟨833945, by rfl⟩ : syracuseStep 4447709 = 1667891) B1667891
theorem B2219521 : Blo 876568 2219521 := bstep (se 2 (by rfl) ⟨832320, by rfl⟩ : syracuseStep 2219521 = 1664641) B1664641
theorem B3759659 : Blo 876568 3759659 := bstep (se 1 (by rfl) ⟨2819744, by rfl⟩ : syracuseStep 3759659 = 5639489) B5639489
theorem B3333869 : Blo 876568 3333869 := bstep (se 3 (by rfl) ⟨625100, by rfl⟩ : syracuseStep 3333869 = 1250201) B1250201
theorem B4448033 : Blo 876568 4448033 := bstep (se 2 (by rfl) ⟨1668012, by rfl⟩ : syracuseStep 4448033 = 3336025) B3336025
theorem B9985841 : Blo 876568 9985841 := bstep (se 2 (by rfl) ⟨3744690, by rfl⟩ : syracuseStep 9985841 = 7489381) B7489381
theorem B2252801 : Blo 876568 2252801 := bstep (se 2 (by rfl) ⟨844800, by rfl⟩ : syracuseStep 2252801 = 1689601) B1689601
theorem B876603 : Blo 876568 876603 := bstep (se 1 (by rfl) ⟨657452, by rfl⟩ : syracuseStep 876603 = 1314905) B1314905
theorem B2220119 : Blo 876568 2220119 := bstep (se 1 (by rfl) ⟨1665089, by rfl⟩ : syracuseStep 2220119 = 3330179) B3330179
theorem B876679 : Blo 876568 876679 := bstep (se 1 (by rfl) ⟨657509, by rfl⟩ : syracuseStep 876679 = 1315019) B1315019
theorem B876687 : Blo 876568 876687 := bstep (se 1 (by rfl) ⟨657515, by rfl⟩ : syracuseStep 876687 = 1315031) B1315031
theorem B876731 : Blo 876568 876731 := bstep (se 1 (by rfl) ⟨657548, by rfl⟩ : syracuseStep 876731 = 1315097) B1315097
theorem B3563777 : Blo 876568 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B876807 : Blo 876568 876807 := bstep (se 1 (by rfl) ⟨657605, by rfl⟩ : syracuseStep 876807 = 1315211) B1315211
theorem B876815 : Blo 876568 876815 := bstep (se 1 (by rfl) ⟨657611, by rfl⟩ : syracuseStep 876815 = 1315223) B1315223
theorem B2220331 : Blo 876568 2220331 := bstep (se 1 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 2220331 = 3330497) B3330497
theorem B876859 : Blo 876568 876859 := bstep (se 1 (by rfl) ⟨657644, by rfl⟩ : syracuseStep 876859 = 1315289) B1315289
theorem B876935 : Blo 876568 876935 := bstep (se 1 (by rfl) ⟨657701, by rfl⟩ : syracuseStep 876935 = 1315403) B1315403
theorem B876943 : Blo 876568 876943 := bstep (se 1 (by rfl) ⟨657707, by rfl⟩ : syracuseStep 876943 = 1315415) B1315415
theorem B3334553 : Blo 876568 3334553 := bstep (se 2 (by rfl) ⟨1250457, by rfl⟩ : syracuseStep 3334553 = 2500915) B2500915
theorem B2220473 : Blo 876568 2220473 := bstep (se 2 (by rfl) ⟨832677, by rfl⟩ : syracuseStep 2220473 = 1665355) B1665355
theorem B876987 : Blo 876568 876987 := bstep (se 1 (by rfl) ⟨657740, by rfl⟩ : syracuseStep 876987 = 1315481) B1315481
theorem B877063 : Blo 876568 877063 := bstep (se 1 (by rfl) ⟨657797, by rfl⟩ : syracuseStep 877063 = 1315595) B1315595
theorem B877071 : Blo 876568 877071 := bstep (se 1 (by rfl) ⟨657803, by rfl⟩ : syracuseStep 877071 = 1315607) B1315607
theorem B877115 : Blo 876568 877115 := bstep (se 1 (by rfl) ⟨657836, by rfl⟩ : syracuseStep 877115 = 1315673) B1315673
theorem B877191 : Blo 876568 877191 := bstep (se 1 (by rfl) ⟨657893, by rfl⟩ : syracuseStep 877191 = 1315787) B1315787
theorem B877199 : Blo 876568 877199 := bstep (se 1 (by rfl) ⟨657899, by rfl⟩ : syracuseStep 877199 = 1315799) B1315799
theorem B877243 : Blo 876568 877243 := bstep (se 1 (by rfl) ⟨657932, by rfl⟩ : syracuseStep 877243 = 1315865) B1315865
theorem B4449005 : Blo 876568 4449005 := bstep (se 3 (by rfl) ⟨834188, by rfl⟩ : syracuseStep 4449005 = 1668377) B1668377
theorem B877319 : Blo 876568 877319 := bstep (se 1 (by rfl) ⟨657989, by rfl⟩ : syracuseStep 877319 = 1315979) B1315979
theorem B877327 : Blo 876568 877327 := bstep (se 1 (by rfl) ⟨657995, by rfl⟩ : syracuseStep 877327 = 1315991) B1315991
theorem B22504229 : Blo 876568 22504229 := bstep (se 4 (by rfl) ⟨2109771, by rfl⟩ : syracuseStep 22504229 = 4219543) B4219543
theorem B877371 : Blo 876568 877371 := bstep (se 1 (by rfl) ⟨658028, by rfl⟩ : syracuseStep 877371 = 1316057) B1316057
theorem B877447 : Blo 876568 877447 := bstep (se 1 (by rfl) ⟨658085, by rfl⟩ : syracuseStep 877447 = 1316171) B1316171
theorem B877455 : Blo 876568 877455 := bstep (se 1 (by rfl) ⟨658091, by rfl⟩ : syracuseStep 877455 = 1316183) B1316183
theorem B5006225 : Blo 876568 5006225 := bstep (se 2 (by rfl) ⟨1877334, by rfl⟩ : syracuseStep 5006225 = 3754669) B3754669
theorem B877499 : Blo 876568 877499 := bstep (se 1 (by rfl) ⟨658124, by rfl⟩ : syracuseStep 877499 = 1316249) B1316249
theorem B877575 : Blo 876568 877575 := bstep (se 1 (by rfl) ⟨658181, by rfl⟩ : syracuseStep 877575 = 1316363) B1316363
theorem B877583 : Blo 876568 877583 := bstep (se 1 (by rfl) ⟨658187, by rfl⟩ : syracuseStep 877583 = 1316375) B1316375
theorem B877627 : Blo 876568 877627 := bstep (se 1 (by rfl) ⟨658220, by rfl⟩ : syracuseStep 877627 = 1316441) B1316441
theorem B877703 : Blo 876568 877703 := bstep (se 1 (by rfl) ⟨658277, by rfl⟩ : syracuseStep 877703 = 1316555) B1316555
theorem B877711 : Blo 876568 877711 := bstep (se 1 (by rfl) ⟨658283, by rfl⟩ : syracuseStep 877711 = 1316567) B1316567
theorem B877755 : Blo 876568 877755 := bstep (se 1 (by rfl) ⟨658316, by rfl⟩ : syracuseStep 877755 = 1316633) B1316633
theorem B1664201 : Blo 876568 1664201 := bstep (se 2 (by rfl) ⟨624075, by rfl⟩ : syracuseStep 1664201 = 1248151) B1248151
theorem B877831 : Blo 876568 877831 := bstep (se 1 (by rfl) ⟨658373, by rfl⟩ : syracuseStep 877831 = 1316747) B1316747
theorem B877839 : Blo 876568 877839 := bstep (se 1 (by rfl) ⟨658379, by rfl⟩ : syracuseStep 877839 = 1316759) B1316759
theorem B877883 : Blo 876568 877883 := bstep (se 1 (by rfl) ⟨658412, by rfl⟩ : syracuseStep 877883 = 1316825) B1316825
theorem B5006681 : Blo 876568 5006681 := bstep (se 2 (by rfl) ⟨1877505, by rfl⟩ : syracuseStep 5006681 = 3755011) B3755011
theorem B3335539 : Blo 876568 3335539 := bstep (se 1 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 3335539 = 5003309) B5003309
theorem B877959 : Blo 876568 877959 := bstep (se 1 (by rfl) ⟨658469, by rfl⟩ : syracuseStep 877959 = 1316939) B1316939
theorem B877967 : Blo 876568 877967 := bstep (se 1 (by rfl) ⟨658475, by rfl⟩ : syracuseStep 877967 = 1316951) B1316951
theorem B2221465 : Blo 876568 2221465 := bstep (se 2 (by rfl) ⟨833049, by rfl⟩ : syracuseStep 2221465 = 1666099) B1666099
theorem B878011 : Blo 876568 878011 := bstep (se 1 (by rfl) ⟨658508, by rfl⟩ : syracuseStep 878011 = 1317017) B1317017
theorem B878087 : Blo 876568 878087 := bstep (se 1 (by rfl) ⟨658565, by rfl⟩ : syracuseStep 878087 = 1317131) B1317131
theorem B878095 : Blo 876568 878095 := bstep (se 1 (by rfl) ⟨658571, by rfl⟩ : syracuseStep 878095 = 1317143) B1317143
theorem B4449815 : Blo 876568 4449815 := bstep (se 1 (by rfl) ⟨3337361, by rfl⟩ : syracuseStep 4449815 = 6674723) B6674723
theorem B3171869 : Blo 876568 3171869 := bstep (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) B1189451
theorem B2221627 : Blo 876568 2221627 := bstep (se 1 (by rfl) ⟨1666220, by rfl⟩ : syracuseStep 2221627 = 3332441) B3332441
theorem B878139 : Blo 876568 878139 := bstep (se 1 (by rfl) ⟨658604, by rfl⟩ : syracuseStep 878139 = 1317209) B1317209
theorem B878215 : Blo 876568 878215 := bstep (se 1 (by rfl) ⟨658661, by rfl⟩ : syracuseStep 878215 = 1317323) B1317323
theorem B878223 : Blo 876568 878223 := bstep (se 1 (by rfl) ⟨658667, by rfl⟩ : syracuseStep 878223 = 1317335) B1317335
theorem B878267 : Blo 876568 878267 := bstep (se 1 (by rfl) ⟨658700, by rfl⟩ : syracuseStep 878267 = 1317401) B1317401
theorem B2221769 : Blo 876568 2221769 := bstep (se 2 (by rfl) ⟨833163, by rfl⟩ : syracuseStep 2221769 = 1666327) B1666327
theorem B878343 : Blo 876568 878343 := bstep (se 1 (by rfl) ⟨658757, by rfl⟩ : syracuseStep 878343 = 1317515) B1317515
theorem B878351 : Blo 876568 878351 := bstep (se 1 (by rfl) ⟨658763, by rfl⟩ : syracuseStep 878351 = 1317527) B1317527
theorem B878395 : Blo 876568 878395 := bstep (se 1 (by rfl) ⟨658796, by rfl⟩ : syracuseStep 878395 = 1317593) B1317593
theorem B878471 : Blo 876568 878471 := bstep (se 1 (by rfl) ⟨658853, by rfl⟩ : syracuseStep 878471 = 1317707) B1317707
theorem B878479 : Blo 876568 878479 := bstep (se 1 (by rfl) ⟨658859, by rfl⟩ : syracuseStep 878479 = 1317719) B1317719
theorem B1337231 : Blo 876568 1337231 := bstep (se 1 (by rfl) ⟨1002923, by rfl⟩ : syracuseStep 1337231 = 2005847) B2005847
theorem B878523 : Blo 876568 878523 := bstep (se 1 (by rfl) ⟨658892, by rfl⟩ : syracuseStep 878523 = 1317785) B1317785
theorem B878599 : Blo 876568 878599 := bstep (se 1 (by rfl) ⟨658949, by rfl⟩ : syracuseStep 878599 = 1317899) B1317899
theorem B878607 : Blo 876568 878607 := bstep (se 1 (by rfl) ⟨658955, by rfl⟩ : syracuseStep 878607 = 1317911) B1317911
theorem B2222113 : Blo 876568 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B878651 : Blo 876568 878651 := bstep (se 1 (by rfl) ⟨658988, by rfl⟩ : syracuseStep 878651 = 1317977) B1317977
theorem B8022077 : Blo 876568 8022077 := bstep (se 3 (by rfl) ⟨1504139, by rfl⟩ : syracuseStep 8022077 = 3008279) B3008279
theorem B878727 : Blo 876568 878727 := bstep (se 1 (by rfl) ⟨659045, by rfl⟩ : syracuseStep 878727 = 1318091) B1318091
theorem B878735 : Blo 876568 878735 := bstep (se 1 (by rfl) ⟨659051, by rfl⟩ : syracuseStep 878735 = 1318103) B1318103
theorem B878779 : Blo 876568 878779 := bstep (se 1 (by rfl) ⟨659084, by rfl⟩ : syracuseStep 878779 = 1318169) B1318169
theorem B878855 : Blo 876568 878855 := bstep (se 1 (by rfl) ⟨659141, by rfl⟩ : syracuseStep 878855 = 1318283) B1318283
theorem B878863 : Blo 876568 878863 := bstep (se 1 (by rfl) ⟨659147, by rfl⟩ : syracuseStep 878863 = 1318295) B1318295
theorem B878907 : Blo 876568 878907 := bstep (se 1 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 878907 = 1318361) B1318361
theorem B878983 : Blo 876568 878983 := bstep (se 1 (by rfl) ⟨659237, by rfl⟩ : syracuseStep 878983 = 1318475) B1318475
theorem B878991 : Blo 876568 878991 := bstep (se 1 (by rfl) ⟨659243, by rfl⟩ : syracuseStep 878991 = 1318487) B1318487
theorem B7498129 : Blo 876568 7498129 := bstep (se 2 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 7498129 = 5623597) B5623597
theorem B879035 : Blo 876568 879035 := bstep (se 1 (by rfl) ⟨659276, by rfl⟩ : syracuseStep 879035 = 1318553) B1318553
theorem B5630417 : Blo 876568 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B879111 : Blo 876568 879111 := bstep (se 1 (by rfl) ⟨659333, by rfl⟩ : syracuseStep 879111 = 1318667) B1318667
theorem B879119 : Blo 876568 879119 := bstep (se 1 (by rfl) ⟨659339, by rfl⟩ : syracuseStep 879119 = 1318679) B1318679
theorem B879163 : Blo 876568 879163 := bstep (se 1 (by rfl) ⟨659372, by rfl⟩ : syracuseStep 879163 = 1318745) B1318745
theorem B5073475 : Blo 876568 5073475 := bstep (se 1 (by rfl) ⟨3805106, by rfl⟩ : syracuseStep 5073475 = 7610213) B7610213
theorem B2222711 : Blo 876568 2222711 := bstep (se 1 (by rfl) ⟨1667033, by rfl⟩ : syracuseStep 2222711 = 3334067) B3334067
theorem B879239 : Blo 876568 879239 := bstep (se 1 (by rfl) ⟨659429, by rfl⟩ : syracuseStep 879239 = 1318859) B1318859
theorem B879247 : Blo 876568 879247 := bstep (se 1 (by rfl) ⟨659435, by rfl⟩ : syracuseStep 879247 = 1318871) B1318871
theorem B879291 : Blo 876568 879291 := bstep (se 1 (by rfl) ⟨659468, by rfl⟩ : syracuseStep 879291 = 1318937) B1318937
theorem B879367 : Blo 876568 879367 := bstep (se 1 (by rfl) ⟨659525, by rfl⟩ : syracuseStep 879367 = 1319051) B1319051
theorem B879375 : Blo 876568 879375 := bstep (se 1 (by rfl) ⟨659531, by rfl⟩ : syracuseStep 879375 = 1319063) B1319063
theorem B879419 : Blo 876568 879419 := bstep (se 1 (by rfl) ⟨659564, by rfl⟩ : syracuseStep 879419 = 1319129) B1319129
theorem B879495 : Blo 876568 879495 := bstep (se 1 (by rfl) ⟨659621, by rfl⟩ : syracuseStep 879495 = 1319243) B1319243
theorem B879503 : Blo 876568 879503 := bstep (se 1 (by rfl) ⟨659627, by rfl⟩ : syracuseStep 879503 = 1319255) B1319255
theorem B879547 : Blo 876568 879547 := bstep (se 1 (by rfl) ⟨659660, by rfl⟩ : syracuseStep 879547 = 1319321) B1319321
theorem B879623 : Blo 876568 879623 := bstep (se 1 (by rfl) ⟨659717, by rfl⟩ : syracuseStep 879623 = 1319435) B1319435
theorem B879631 : Blo 876568 879631 := bstep (se 1 (by rfl) ⟨659723, by rfl⟩ : syracuseStep 879631 = 1319447) B1319447
theorem B3009565 : Blo 876568 3009565 := bstep (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) B1128587
theorem B879675 : Blo 876568 879675 := bstep (se 1 (by rfl) ⟨659756, by rfl⟩ : syracuseStep 879675 = 1319513) B1319513
theorem B1666183 : Blo 876568 1666183 := bstep (se 1 (by rfl) ⟨1249637, by rfl⟩ : syracuseStep 1666183 = 2499275) B2499275
theorem B879751 : Blo 876568 879751 := bstep (se 1 (by rfl) ⟨659813, by rfl⟩ : syracuseStep 879751 = 1319627) B1319627
theorem B879759 : Blo 876568 879759 := bstep (se 1 (by rfl) ⟨659819, by rfl⟩ : syracuseStep 879759 = 1319639) B1319639
theorem B879803 : Blo 876568 879803 := bstep (se 1 (by rfl) ⟨659852, by rfl⟩ : syracuseStep 879803 = 1319705) B1319705
theorem B879879 : Blo 876568 879879 := bstep (se 1 (by rfl) ⟨659909, by rfl⟩ : syracuseStep 879879 = 1319819) B1319819
theorem B879887 : Blo 876568 879887 := bstep (se 1 (by rfl) ⟨659915, by rfl⟩ : syracuseStep 879887 = 1319831) B1319831
theorem B879931 : Blo 876568 879931 := bstep (se 1 (by rfl) ⟨659948, by rfl⟩ : syracuseStep 879931 = 1319897) B1319897
theorem B880007 : Blo 876568 880007 := bstep (se 1 (by rfl) ⟨660005, by rfl⟩ : syracuseStep 880007 = 1320011) B1320011
theorem B880015 : Blo 876568 880015 := bstep (se 1 (by rfl) ⟨660011, by rfl⟩ : syracuseStep 880015 = 1320023) B1320023
theorem B10022291 : Blo 876568 10022291 := bstep (se 1 (by rfl) ⟨7516718, by rfl⟩ : syracuseStep 10022291 = 15033437) B15033437
theorem B9629113 : Blo 876568 9629113 := bstep (se 2 (by rfl) ⟨3610917, by rfl⟩ : syracuseStep 9629113 = 7221835) B7221835
theorem B880059 : Blo 876568 880059 := bstep (se 1 (by rfl) ⟨660044, by rfl⟩ : syracuseStep 880059 = 1320089) B1320089
theorem B97643981 : Blo 876568 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B880135 : Blo 876568 880135 := bstep (se 1 (by rfl) ⟨660101, by rfl⟩ : syracuseStep 880135 = 1320203) B1320203
theorem B880143 : Blo 876568 880143 := bstep (se 1 (by rfl) ⟨660107, by rfl⟩ : syracuseStep 880143 = 1320215) B1320215
theorem B3337757 : Blo 876568 3337757 := bstep (se 3 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 3337757 = 1251659) B1251659
theorem B5565995 : Blo 876568 5565995 := bstep (se 1 (by rfl) ⟨4174496, by rfl⟩ : syracuseStep 5565995 = 8348993) B8348993
theorem B880187 : Blo 876568 880187 := bstep (se 1 (by rfl) ⟨660140, by rfl⟩ : syracuseStep 880187 = 1320281) B1320281
theorem B1109639 : Blo 876568 1109639 := bstep (se 1 (by rfl) ⟨832229, by rfl⟩ : syracuseStep 1109639 = 1664459) B1664459
theorem B880263 : Blo 876568 880263 := bstep (se 1 (by rfl) ⟨660197, by rfl⟩ : syracuseStep 880263 = 1320395) B1320395
theorem B880271 : Blo 876568 880271 := bstep (se 1 (by rfl) ⟨660203, by rfl⟩ : syracuseStep 880271 = 1320407) B1320407
theorem B880315 : Blo 876568 880315 := bstep (se 1 (by rfl) ⟨660236, by rfl⟩ : syracuseStep 880315 = 1320473) B1320473
theorem B880391 : Blo 876568 880391 := bstep (se 1 (by rfl) ⟨660293, by rfl⟩ : syracuseStep 880391 = 1320587) B1320587
theorem B880399 : Blo 876568 880399 := bstep (se 1 (by rfl) ⟨660299, by rfl⟩ : syracuseStep 880399 = 1320599) B1320599
theorem B1404715 : Blo 876568 1404715 := bstep (se 1 (by rfl) ⟨1053536, by rfl⟩ : syracuseStep 1404715 = 2107073) B2107073
theorem B880443 : Blo 876568 880443 := bstep (se 1 (by rfl) ⟨660332, by rfl⟩ : syracuseStep 880443 = 1320665) B1320665
theorem B2224007 : Blo 876568 2224007 := bstep (se 1 (by rfl) ⟨1668005, by rfl⟩ : syracuseStep 2224007 = 3336011) B3336011
theorem B880519 : Blo 876568 880519 := bstep (se 1 (by rfl) ⟨660389, by rfl⟩ : syracuseStep 880519 = 1320779) B1320779
theorem B880527 : Blo 876568 880527 := bstep (se 1 (by rfl) ⟨660395, by rfl⟩ : syracuseStep 880527 = 1320791) B1320791
theorem B2224057 : Blo 876568 2224057 := bstep (se 2 (by rfl) ⟨834021, by rfl⟩ : syracuseStep 2224057 = 1668043) B1668043
theorem B3338441 : Blo 876568 3338441 := bstep (se 2 (by rfl) ⟨1251915, by rfl⟩ : syracuseStep 3338441 = 2503831) B2503831
theorem B2814209 : Blo 876568 2814209 := bstep (se 2 (by rfl) ⟨1055328, by rfl⟩ : syracuseStep 2814209 = 2110657) B2110657
theorem B1110287 : Blo 876568 1110287 := bstep (se 1 (by rfl) ⟨832715, by rfl⟩ : syracuseStep 1110287 = 1665431) B1665431
theorem B5009849 : Blo 876568 5009849 := bstep (se 2 (by rfl) ⟨1878693, by rfl⟩ : syracuseStep 5009849 = 3757387) B3757387
theorem B6681041 : Blo 876568 6681041 := bstep (se 2 (by rfl) ⟨2505390, by rfl⟩ : syracuseStep 6681041 = 5010781) B5010781
theorem B2224655 : Blo 876568 2224655 := bstep (se 1 (by rfl) ⟨1668491, by rfl⟩ : syracuseStep 2224655 = 3336983) B3336983
theorem B4452893 : Blo 876568 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B3568157 : Blo 876568 3568157 := bstep (se 3 (by rfl) ⟨669029, by rfl⟩ : syracuseStep 3568157 = 1338059) B1338059
theorem B2257523 : Blo 876568 2257523 := bstep (se 1 (by rfl) ⟨1693142, by rfl⟩ : syracuseStep 2257523 = 3386285) B3386285
theorem B1667785 : Blo 876568 1667785 := bstep (se 2 (by rfl) ⟨625419, by rfl⟩ : syracuseStep 1667785 = 1250839) B1250839
theorem B4453379 : Blo 876568 4453379 := bstep (se 1 (by rfl) ⟨3340034, by rfl⟩ : syracuseStep 4453379 = 6680069) B6680069
theorem B2225353 : Blo 876568 2225353 := bstep (se 2 (by rfl) ⟨834507, by rfl⟩ : syracuseStep 2225353 = 1669015) B1669015
theorem B2225495 : Blo 876568 2225495 := bstep (se 1 (by rfl) ⟨1669121, by rfl⟩ : syracuseStep 2225495 = 3338243) B3338243
theorem B8451661 : Blo 876568 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B3340217 : Blo 876568 3340217 := bstep (se 2 (by rfl) ⟨1252581, by rfl⟩ : syracuseStep 3340217 = 2505163) B2505163
theorem B8550803 : Blo 876568 8550803 := bstep (se 1 (by rfl) ⟨6413102, by rfl⟩ : syracuseStep 8550803 = 12826205) B12826205
theorem B4454999 : Blo 876568 4454999 := bstep (se 1 (by rfl) ⟨3341249, by rfl⟩ : syracuseStep 4454999 = 6682499) B6682499
theorem B34306679 : Blo 876568 34306679 := bstep (se 1 (by rfl) ⟨25730009, by rfl⟩ : syracuseStep 34306679 = 51460019) B51460019
theorem B9173683 : Blo 876568 9173683 := bstep (se 1 (by rfl) ⟨6880262, by rfl⟩ : syracuseStep 9173683 = 13760525) B13760525
theorem B9009893 : Blo 876568 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B5012239 : Blo 876568 5012239 := bstep (se 1 (by rfl) ⟨3759179, by rfl⟩ : syracuseStep 5012239 = 7518359) B7518359
theorem B4455485 : Blo 876568 4455485 := bstep (se 3 (by rfl) ⟨835403, by rfl⟩ : syracuseStep 4455485 = 1670807) B1670807
theorem B1670291 : Blo 876568 1670291 := bstep (se 1 (by rfl) ⟨1252718, by rfl⟩ : syracuseStep 1670291 = 2505437) B2505437
theorem B1113259 : Blo 876568 1113259 := bstep (se 1 (by rfl) ⟨834944, by rfl⟩ : syracuseStep 1113259 = 1669889) B1669889
theorem B2227571 : Blo 876568 2227571 := bstep (se 1 (by rfl) ⟨1670678, by rfl⟩ : syracuseStep 2227571 = 3341357) B3341357
theorem B1670519 : Blo 876568 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B6323665 : Blo 876568 6323665 := bstep (se 2 (by rfl) ⟨2371374, by rfl⟩ : syracuseStep 6323665 = 4742749) B4742749
theorem B9141803 : Blo 876568 9141803 := bstep (se 1 (by rfl) ⟨6856352, by rfl⟩ : syracuseStep 9141803 = 13712705) B13712705
theorem B6323779 : Blo 876568 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B4226849 : Blo 876568 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B2031403 : Blo 876568 2031403 := bstep (se 1 (by rfl) ⟨1523552, by rfl⟩ : syracuseStep 2031403 = 3047105) B3047105
theorem B2228087 : Blo 876568 2228087 := bstep (se 1 (by rfl) ⟨1671065, by rfl⟩ : syracuseStep 2228087 = 3342131) B3342131
theorem B6422435 : Blo 876568 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B4227079 : Blo 876568 4227079 := bstep (se 1 (by rfl) ⟨3170309, by rfl⟩ : syracuseStep 4227079 = 6340619) B6340619
theorem B3342343 : Blo 876568 3342343 := bstep (se 1 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 3342343 = 5013515) B5013515
theorem B1671187 : Blo 876568 1671187 := bstep (se 1 (by rfl) ⟨1253390, by rfl⟩ : syracuseStep 1671187 = 2506781) B2506781
theorem B45547541 : Blo 876568 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B6684929 : Blo 876568 6684929 := bstep (se 2 (by rfl) ⟨2506848, by rfl⟩ : syracuseStep 6684929 = 5013697) B5013697
theorem B1671529 : Blo 876568 1671529 := bstep (se 2 (by rfl) ⟨626823, by rfl⟩ : syracuseStep 1671529 = 1253647) B1253647
theorem B3342829 : Blo 876568 3342829 := bstep (se 3 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 3342829 = 1253561) B1253561
theorem B4063769 : Blo 876568 4063769 := bstep (se 2 (by rfl) ⟨1523913, by rfl⟩ : syracuseStep 4063769 = 3047827) B3047827
theorem B12649061 : Blo 876568 12649061 := bstep (se 4 (by rfl) ⟨1185849, by rfl⟩ : syracuseStep 12649061 = 2371699) B2371699
theorem B9503405 : Blo 876568 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B2818759 : Blo 876568 2818759 := bstep (se 1 (by rfl) ⟨2114069, by rfl⟩ : syracuseStep 2818759 = 4228139) B4228139
theorem B3343133 : Blo 876568 3343133 := bstep (se 3 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 3343133 = 1253675) B1253675
theorem B1409975 : Blo 876568 1409975 := bstep (se 1 (by rfl) ⟨1057481, by rfl⟩ : syracuseStep 1409975 = 2114963) B2114963
theorem B4228291 : Blo 876568 4228291 := bstep (se 1 (by rfl) ⟨3171218, by rfl⟩ : syracuseStep 4228291 = 6342437) B6342437
theorem B9504353 : Blo 876568 9504353 := bstep (se 2 (by rfl) ⟨3564132, by rfl⟩ : syracuseStep 9504353 = 7128265) B7128265
theorem B2819681 : Blo 876568 2819681 := bstep (se 2 (by rfl) ⟨1057380, by rfl⟩ : syracuseStep 2819681 = 2114761) B2114761
theorem B3377231 : Blo 876568 3377231 := bstep (se 1 (by rfl) ⟨2532923, by rfl⟩ : syracuseStep 3377231 = 5065847) B5065847
theorem B13502771 : Blo 876568 13502771 := bstep (se 1 (by rfl) ⟨10127078, by rfl⟩ : syracuseStep 13502771 = 20254157) B20254157
theorem B2853895 : Blo 876568 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B12651713 : Blo 876568 12651713 := bstep (se 2 (by rfl) ⟨4744392, by rfl⟩ : syracuseStep 12651713 = 9488785) B9488785
theorem B9997505 : Blo 876568 9997505 := bstep (se 2 (by rfl) ⟨3749064, by rfl⟩ : syracuseStep 9997505 = 7498129) B7498129
theorem B8228087 : Blo 876568 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B10292503 : Blo 876568 10292503 := bstep (se 1 (by rfl) ⟨7719377, by rfl⟩ : syracuseStep 10292503 = 15438755) B15438755
theorem B12193517 : Blo 876568 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B8425403 : Blo 876568 8425403 := bstep (se 1 (by rfl) ⟨6319052, by rfl⟩ : syracuseStep 8425403 = 12638105) B12638105
theorem B987259 : Blo 876568 987259 := bstep (se 1 (by rfl) ⟨740444, by rfl⟩ : syracuseStep 987259 = 1480889) B1480889
theorem B1315247 : Blo 876568 1315247 := bstep (se 1 (by rfl) ⟨986435, by rfl⟩ : syracuseStep 1315247 = 1972871) B1972871
theorem B1315337 : Blo 876568 1315337 := bstep (se 2 (by rfl) ⟨493251, by rfl⟩ : syracuseStep 1315337 = 986503) B986503
theorem B1315367 : Blo 876568 1315367 := bstep (se 1 (by rfl) ⟨986525, by rfl⟩ : syracuseStep 1315367 = 1973051) B1973051
theorem B987727 : Blo 876568 987727 := bstep (se 1 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 987727 = 1481591) B1481591
theorem B1315451 : Blo 876568 1315451 := bstep (se 1 (by rfl) ⟨986588, by rfl⟩ : syracuseStep 1315451 = 1973177) B1973177
theorem B18977489 : Blo 876568 18977489 := bstep (se 2 (by rfl) ⟨7116558, by rfl⟩ : syracuseStep 18977489 = 14233117) B14233117
theorem B1315577 : Blo 876568 1315577 := bstep (se 2 (by rfl) ⟨493341, by rfl⟩ : syracuseStep 1315577 = 986683) B986683
theorem B1315679 : Blo 876568 1315679 := bstep (se 1 (by rfl) ⟨986759, by rfl⟩ : syracuseStep 1315679 = 1973519) B1973519
theorem B1315691 : Blo 876568 1315691 := bstep (se 1 (by rfl) ⟨986768, by rfl⟩ : syracuseStep 1315691 = 1973537) B1973537
theorem B4330415 : Blo 876568 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B988123 : Blo 876568 988123 := bstep (se 1 (by rfl) ⟨741092, by rfl⟩ : syracuseStep 988123 = 1482185) B1482185
theorem B1872953 : Blo 876568 1872953 := bstep (se 2 (by rfl) ⟨702357, by rfl⟩ : syracuseStep 1872953 = 1404715) B1404715
theorem B1315919 : Blo 876568 1315919 := bstep (se 1 (by rfl) ⟨986939, by rfl⟩ : syracuseStep 1315919 = 1973879) B1973879
theorem B1316039 : Blo 876568 1316039 := bstep (se 1 (by rfl) ⟨987029, by rfl⟩ : syracuseStep 1316039 = 1974059) B1974059
theorem B6657227 : Blo 876568 6657227 := bstep (se 1 (by rfl) ⟨4992920, by rfl⟩ : syracuseStep 6657227 = 9985841) B9985841
theorem B1316201 : Blo 876568 1316201 := bstep (se 2 (by rfl) ⟨493575, by rfl⟩ : syracuseStep 1316201 = 987151) B987151
theorem B1480079 : Blo 876568 1480079 := bstep (se 1 (by rfl) ⟨1110059, by rfl⟩ : syracuseStep 1480079 = 2220119) B2220119
theorem B988591 : Blo 876568 988591 := bstep (se 1 (by rfl) ⟨741443, by rfl⟩ : syracuseStep 988591 = 1482887) B1482887
theorem B1316279 : Blo 876568 1316279 := bstep (se 1 (by rfl) ⟨987209, by rfl⟩ : syracuseStep 1316279 = 1974419) B1974419
theorem B1316315 : Blo 876568 1316315 := bstep (se 1 (by rfl) ⟨987236, by rfl⟩ : syracuseStep 1316315 = 1974473) B1974473
theorem B1480315 : Blo 876568 1480315 := bstep (se 1 (by rfl) ⟨1110236, by rfl⟩ : syracuseStep 1480315 = 2220473) B2220473
theorem B3806867 : Blo 876568 3806867 := bstep (se 1 (by rfl) ⟨2855150, by rfl⟩ : syracuseStep 3806867 = 5710301) B5710301
theorem B989023 : Blo 876568 989023 := bstep (se 1 (by rfl) ⟨741767, by rfl⟩ : syracuseStep 989023 = 1483535) B1483535
theorem B1316783 : Blo 876568 1316783 := bstep (se 1 (by rfl) ⟨987587, by rfl⟩ : syracuseStep 1316783 = 1975175) B1975175
theorem B5707705 : Blo 876568 5707705 := bstep (se 2 (by rfl) ⟨2140389, by rfl⟩ : syracuseStep 5707705 = 4280779) B4280779
theorem B1316873 : Blo 876568 1316873 := bstep (se 2 (by rfl) ⟨493827, by rfl⟩ : syracuseStep 1316873 = 987655) B987655
theorem B10000421 : Blo 876568 10000421 := bstep (se 4 (by rfl) ⟨937539, by rfl⟩ : syracuseStep 10000421 = 1875079) B1875079
theorem B1316903 : Blo 876568 1316903 := bstep (se 1 (by rfl) ⟨987677, by rfl⟩ : syracuseStep 1316903 = 1975355) B1975355
theorem B1316987 : Blo 876568 1316987 := bstep (se 1 (by rfl) ⟨987740, by rfl⟩ : syracuseStep 1316987 = 1975481) B1975481
theorem B989383 : Blo 876568 989383 := bstep (se 1 (by rfl) ⟨742037, by rfl⟩ : syracuseStep 989383 = 1484075) B1484075
theorem B1317113 : Blo 876568 1317113 := bstep (se 2 (by rfl) ⟨493917, by rfl⟩ : syracuseStep 1317113 = 987835) B987835
theorem B1317215 : Blo 876568 1317215 := bstep (se 1 (by rfl) ⟨987911, by rfl⟩ : syracuseStep 1317215 = 1975823) B1975823
theorem B1317227 : Blo 876568 1317227 := bstep (se 1 (by rfl) ⟨987920, by rfl⟩ : syracuseStep 1317227 = 1975841) B1975841
theorem B1186267 : Blo 876568 1186267 := bstep (se 1 (by rfl) ⟨889700, by rfl⟩ : syracuseStep 1186267 = 1779401) B1779401
theorem B1481179 : Blo 876568 1481179 := bstep (se 1 (by rfl) ⟨1110884, by rfl⟩ : syracuseStep 1481179 = 2221769) B2221769
theorem B1972745 : Blo 876568 1972745 := bstep (se 2 (by rfl) ⟨739779, by rfl⟩ : syracuseStep 1972745 = 1479559) B1479559
theorem B1317455 : Blo 876568 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B1317575 : Blo 876568 1317575 := bstep (se 1 (by rfl) ⟨988181, by rfl⟩ : syracuseStep 1317575 = 1976363) B1976363
theorem B5348051 : Blo 876568 5348051 := bstep (se 1 (by rfl) ⟨4011038, by rfl⟩ : syracuseStep 5348051 = 8022077) B8022077
theorem B12655349 : Blo 876568 12655349 := bstep (se 5 (by rfl) ⟨593219, by rfl⟩ : syracuseStep 12655349 = 1186439) B1186439
theorem B1973087 : Blo 876568 1973087 := bstep (se 1 (by rfl) ⟨1479815, by rfl⟩ : syracuseStep 1973087 = 2959631) B2959631
theorem B1317737 : Blo 876568 1317737 := bstep (se 2 (by rfl) ⟨494151, by rfl⟩ : syracuseStep 1317737 = 988303) B988303
theorem B2497463 : Blo 876568 2497463 := bstep (se 1 (by rfl) ⟨1873097, by rfl⟩ : syracuseStep 2497463 = 3746195) B3746195
theorem B1317815 : Blo 876568 1317815 := bstep (se 1 (by rfl) ⟨988361, by rfl⟩ : syracuseStep 1317815 = 1976723) B1976723
theorem B1317851 : Blo 876568 1317851 := bstep (se 1 (by rfl) ⟨988388, by rfl⟩ : syracuseStep 1317851 = 1976777) B1976777
theorem B370580453 : Blo 876568 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B1973267 : Blo 876568 1973267 := bstep (se 1 (by rfl) ⟨1479950, by rfl⟩ : syracuseStep 1973267 = 2959901) B2959901
theorem B990247 : Blo 876568 990247 := bstep (se 1 (by rfl) ⟨742685, by rfl⟩ : syracuseStep 990247 = 1485371) B1485371
theorem B1481807 : Blo 876568 1481807 := bstep (se 1 (by rfl) ⟨1111355, by rfl⟩ : syracuseStep 1481807 = 2222711) B2222711
theorem B24026381 : Blo 876568 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B1973609 : Blo 876568 1973609 := bstep (se 2 (by rfl) ⟨740103, by rfl⟩ : syracuseStep 1973609 = 1480207) B1480207
theorem B1318319 : Blo 876568 1318319 := bstep (se 1 (by rfl) ⟨988739, by rfl⟩ : syracuseStep 1318319 = 1977479) B1977479
theorem B1318409 : Blo 876568 1318409 := bstep (se 2 (by rfl) ⟨494403, by rfl⟩ : syracuseStep 1318409 = 988807) B988807
theorem B1318439 : Blo 876568 1318439 := bstep (se 1 (by rfl) ⟨988829, by rfl⟩ : syracuseStep 1318439 = 1977659) B1977659
theorem B1318523 : Blo 876568 1318523 := bstep (se 1 (by rfl) ⟨988892, by rfl⟩ : syracuseStep 1318523 = 1977785) B1977785
theorem B3710663 : Blo 876568 3710663 := bstep (se 1 (by rfl) ⟨2782997, by rfl⟩ : syracuseStep 3710663 = 5565995) B5565995
theorem B1318649 : Blo 876568 1318649 := bstep (se 2 (by rfl) ⟨494493, by rfl⟩ : syracuseStep 1318649 = 988987) B988987
theorem B1318751 : Blo 876568 1318751 := bstep (se 1 (by rfl) ⟨989063, by rfl⟩ : syracuseStep 1318751 = 1978127) B1978127
theorem B1318763 : Blo 876568 1318763 := bstep (se 1 (by rfl) ⟨989072, by rfl⟩ : syracuseStep 1318763 = 1978145) B1978145
theorem B10166147 : Blo 876568 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B2498465 : Blo 876568 2498465 := bstep (se 2 (by rfl) ⟨936924, by rfl⟩ : syracuseStep 2498465 = 1873849) B1873849
theorem B1777583 : Blo 876568 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B1482671 : Blo 876568 1482671 := bstep (se 1 (by rfl) ⟨1112003, by rfl⟩ : syracuseStep 1482671 = 2224007) B2224007
theorem B1974203 : Blo 876568 1974203 := bstep (se 1 (by rfl) ⟨1480652, by rfl⟩ : syracuseStep 1974203 = 2961305) B2961305
theorem B1777673 : Blo 876568 1777673 := bstep (se 2 (by rfl) ⟨666627, by rfl⟩ : syracuseStep 1777673 = 1333255) B1333255
theorem B1581113 : Blo 876568 1581113 := bstep (se 2 (by rfl) ⟨592917, by rfl⟩ : syracuseStep 1581113 = 1185835) B1185835
theorem B1974329 : Blo 876568 1974329 := bstep (se 2 (by rfl) ⟨740373, by rfl⟩ : syracuseStep 1974329 = 1480747) B1480747
theorem B1318991 : Blo 876568 1318991 := bstep (se 1 (by rfl) ⟨989243, by rfl⟩ : syracuseStep 1318991 = 1978487) B1978487
theorem B1876139 : Blo 876568 1876139 := bstep (se 1 (by rfl) ⟨1407104, by rfl⟩ : syracuseStep 1876139 = 2814209) B2814209
theorem B1319111 : Blo 876568 1319111 := bstep (se 1 (by rfl) ⟨989333, by rfl⟩ : syracuseStep 1319111 = 1978667) B1978667
theorem B24387905 : Blo 876568 24387905 := bstep (se 2 (by rfl) ⟨9145464, by rfl⟩ : syracuseStep 24387905 = 18290929) B18290929
theorem B1483103 : Blo 876568 1483103 := bstep (se 1 (by rfl) ⟨1112327, by rfl⟩ : syracuseStep 1483103 = 2224655) B2224655
theorem B2498921 : Blo 876568 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B1319273 : Blo 876568 1319273 := bstep (se 2 (by rfl) ⟨494727, by rfl⟩ : syracuseStep 1319273 = 989455) B989455
theorem B1974671 : Blo 876568 1974671 := bstep (se 1 (by rfl) ⟨1481003, by rfl⟩ : syracuseStep 1974671 = 2962007) B2962007
theorem B1319351 : Blo 876568 1319351 := bstep (se 1 (by rfl) ⟨989513, by rfl⟩ : syracuseStep 1319351 = 1979027) B1979027
theorem B1319387 : Blo 876568 1319387 := bstep (se 1 (by rfl) ⟨989540, by rfl⟩ : syracuseStep 1319387 = 1979081) B1979081
theorem B3744265 : Blo 876568 3744265 := bstep (se 2 (by rfl) ⟨1404099, by rfl⟩ : syracuseStep 3744265 = 2808199) B2808199
theorem B3744281 : Blo 876568 3744281 := bstep (se 2 (by rfl) ⟨1404105, by rfl⟩ : syracuseStep 3744281 = 2808211) B2808211
theorem B1778233 : Blo 876568 1778233 := bstep (se 2 (by rfl) ⟨666837, by rfl⟩ : syracuseStep 1778233 = 1333675) B1333675
theorem B1974995 : Blo 876568 1974995 := bstep (se 1 (by rfl) ⟨1481246, by rfl⟩ : syracuseStep 1974995 = 2962493) B2962493
theorem B1483663 : Blo 876568 1483663 := bstep (se 1 (by rfl) ⟨1112747, by rfl⟩ : syracuseStep 1483663 = 2225495) B2225495
theorem B12231577 : Blo 876568 12231577 := bstep (se 2 (by rfl) ⟨4586841, by rfl⟩ : syracuseStep 12231577 = 9173683) B9173683
theorem B1319855 : Blo 876568 1319855 := bstep (se 1 (by rfl) ⟨989891, by rfl⟩ : syracuseStep 1319855 = 1979783) B1979783
theorem B4006913 : Blo 876568 4006913 := bstep (se 2 (by rfl) ⟨1502592, by rfl⟩ : syracuseStep 4006913 = 3005185) B3005185
theorem B1319945 : Blo 876568 1319945 := bstep (se 2 (by rfl) ⟨494979, by rfl⟩ : syracuseStep 1319945 = 989959) B989959
theorem B1319975 : Blo 876568 1319975 := bstep (se 1 (by rfl) ⟨989981, by rfl⟩ : syracuseStep 1319975 = 1979963) B1979963
theorem B1320059 : Blo 876568 1320059 := bstep (se 1 (by rfl) ⟨990044, by rfl⟩ : syracuseStep 1320059 = 1980089) B1980089
theorem B1320185 : Blo 876568 1320185 := bstep (se 2 (by rfl) ⟨495069, by rfl⟩ : syracuseStep 1320185 = 990139) B990139
theorem B1320287 : Blo 876568 1320287 := bstep (se 1 (by rfl) ⟨990215, by rfl⟩ : syracuseStep 1320287 = 1980431) B1980431
theorem B1320299 : Blo 876568 1320299 := bstep (se 1 (by rfl) ⟨990224, by rfl⟩ : syracuseStep 1320299 = 1980449) B1980449
theorem B1484345 : Blo 876568 1484345 := bstep (se 2 (by rfl) ⟨556629, by rfl⟩ : syracuseStep 1484345 = 1113259) B1113259
theorem B1320527 : Blo 876568 1320527 := bstep (se 1 (by rfl) ⟨990395, by rfl⟩ : syracuseStep 1320527 = 1980791) B1980791
theorem B1975931 : Blo 876568 1975931 := bstep (se 1 (by rfl) ⟨1481948, by rfl⟩ : syracuseStep 1975931 = 2963897) B2963897
theorem B2958983 : Blo 876568 2958983 := bstep (se 1 (by rfl) ⟨2219237, by rfl⟩ : syracuseStep 2958983 = 4438475) B4438475
theorem B2959037 : Blo 876568 2959037 := bstep (se 3 (by rfl) ⟨554819, by rfl⟩ : syracuseStep 2959037 = 1109639) B1109639
theorem B1320647 : Blo 876568 1320647 := bstep (se 1 (by rfl) ⟨990485, by rfl⟩ : syracuseStep 1320647 = 1980971) B1980971
theorem B1976057 : Blo 876568 1976057 := bstep (se 2 (by rfl) ⟨741021, by rfl⟩ : syracuseStep 1976057 = 1482043) B1482043
theorem B2959199 : Blo 876568 2959199 := bstep (se 1 (by rfl) ⟨2219399, by rfl⟩ : syracuseStep 2959199 = 4438799) B4438799
theorem B1320809 : Blo 876568 1320809 := bstep (se 2 (by rfl) ⟨495303, by rfl⟩ : syracuseStep 1320809 = 990607) B990607
theorem B8431553 : Blo 876568 8431553 := bstep (se 2 (by rfl) ⟨3161832, by rfl⟩ : syracuseStep 8431553 = 6323665) B6323665
theorem B2959361 : Blo 876568 2959361 := bstep (se 2 (by rfl) ⟨1109760, by rfl⟩ : syracuseStep 2959361 = 2219521) B2219521
theorem B1976327 : Blo 876568 1976327 := bstep (se 1 (by rfl) ⟨1482245, by rfl⟩ : syracuseStep 1976327 = 2964491) B2964491
theorem B1976399 : Blo 876568 1976399 := bstep (se 1 (by rfl) ⟨1482299, by rfl⟩ : syracuseStep 1976399 = 2964599) B2964599
theorem B8431705 : Blo 876568 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B1485047 : Blo 876568 1485047 := bstep (se 1 (by rfl) ⟨1113785, by rfl⟩ : syracuseStep 1485047 = 2227571) B2227571
theorem B1976795 : Blo 876568 1976795 := bstep (se 1 (by rfl) ⟨1482596, by rfl⟩ : syracuseStep 1976795 = 2965193) B2965193
theorem B1485391 : Blo 876568 1485391 := bstep (se 1 (by rfl) ⟨1114043, by rfl⟩ : syracuseStep 1485391 = 2228087) B2228087
theorem B1583713 : Blo 876568 1583713 := bstep (se 2 (by rfl) ⟨593892, by rfl⟩ : syracuseStep 1583713 = 1187785) B1187785
theorem B2960171 : Blo 876568 2960171 := bstep (se 1 (by rfl) ⟨2220128, by rfl⟩ : syracuseStep 2960171 = 4440257) B4440257
theorem B1485641 : Blo 876568 1485641 := bstep (se 2 (by rfl) ⟨557115, by rfl⟩ : syracuseStep 1485641 = 1114231) B1114231
theorem B6663059 : Blo 876568 6663059 := bstep (se 1 (by rfl) ⟨4997294, by rfl⟩ : syracuseStep 6663059 = 9994589) B9994589
theorem B1977263 : Blo 876568 1977263 := bstep (se 1 (by rfl) ⟨1482947, by rfl⟩ : syracuseStep 1977263 = 2965895) B2965895
theorem B1878967 : Blo 876568 1878967 := bstep (se 1 (by rfl) ⟨1409225, by rfl⟩ : syracuseStep 1878967 = 2818451) B2818451
theorem B2960441 : Blo 876568 2960441 := bstep (se 2 (by rfl) ⟨1110165, by rfl⟩ : syracuseStep 2960441 = 2220331) B2220331
theorem B1977515 : Blo 876568 1977515 := bstep (se 1 (by rfl) ⟨1483136, by rfl⟩ : syracuseStep 1977515 = 2966273) B2966273
theorem B1584377 : Blo 876568 1584377 := bstep (se 2 (by rfl) ⟨594141, by rfl⟩ : syracuseStep 1584377 = 1188283) B1188283
theorem B2960765 : Blo 876568 2960765 := bstep (se 3 (by rfl) ⟨555143, by rfl⟩ : syracuseStep 2960765 = 1110287) B1110287
theorem B2961035 : Blo 876568 2961035 := bstep (se 1 (by rfl) ⟨2220776, by rfl⟩ : syracuseStep 2961035 = 4441553) B4441553
theorem B1978055 : Blo 876568 1978055 := bstep (se 1 (by rfl) ⟨1483541, by rfl⟩ : syracuseStep 1978055 = 2967083) B2967083
theorem B1584839 : Blo 876568 1584839 := bstep (se 1 (by rfl) ⟨1188629, by rfl⟩ : syracuseStep 1584839 = 2377259) B2377259
theorem B10006253 : Blo 876568 10006253 := bstep (se 3 (by rfl) ⟨1876172, by rfl⟩ : syracuseStep 10006253 = 3752345) B3752345
theorem B6664031 : Blo 876568 6664031 := bstep (se 1 (by rfl) ⟨4998023, by rfl⟩ : syracuseStep 6664031 = 9996047) B9996047
theorem B2961953 : Blo 876568 2961953 := bstep (se 2 (by rfl) ⟨1110732, by rfl⟩ : syracuseStep 2961953 = 2221465) B2221465
theorem B1978919 : Blo 876568 1978919 := bstep (se 1 (by rfl) ⟨1484189, by rfl⟩ : syracuseStep 1978919 = 2968379) B2968379
theorem B1880615 : Blo 876568 1880615 := bstep (se 1 (by rfl) ⟨1410461, by rfl⟩ : syracuseStep 1880615 = 2820923) B2820923
theorem B2962169 : Blo 876568 2962169 := bstep (se 2 (by rfl) ⟨1110813, by rfl⟩ : syracuseStep 2962169 = 2221627) B2221627
theorem B1979243 : Blo 876568 1979243 := bstep (se 1 (by rfl) ⟨1484432, by rfl⟩ : syracuseStep 1979243 = 2968865) B2968865
theorem B1979297 : Blo 876568 1979297 := bstep (se 2 (by rfl) ⟨742236, by rfl⟩ : syracuseStep 1979297 = 1484473) B1484473
theorem B2962439 : Blo 876568 2962439 := bstep (se 1 (by rfl) ⟨2221829, by rfl⟩ : syracuseStep 2962439 = 4443659) B4443659
theorem B2962547 : Blo 876568 2962547 := bstep (se 1 (by rfl) ⟨2221910, by rfl⟩ : syracuseStep 2962547 = 4443821) B4443821
theorem B51328171 : Blo 876568 51328171 := bstep (se 1 (by rfl) ⟨38496128, by rfl⟩ : syracuseStep 51328171 = 76992257) B76992257
theorem B4994243 : Blo 876568 4994243 := bstep (se 1 (by rfl) ⟨3745682, by rfl⟩ : syracuseStep 4994243 = 7491365) B7491365
theorem B1979639 : Blo 876568 1979639 := bstep (se 1 (by rfl) ⟨1484729, by rfl⟩ : syracuseStep 1979639 = 2969459) B2969459
theorem B2962817 : Blo 876568 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B14267947 : Blo 876568 14267947 := bstep (se 1 (by rfl) ⟨10700960, by rfl⟩ : syracuseStep 14267947 = 21401921) B21401921
theorem B1586785 : Blo 876568 1586785 := bstep (se 2 (by rfl) ⟨595044, by rfl⟩ : syracuseStep 1586785 = 1190089) B1190089
theorem B4437827 : Blo 876568 4437827 := bstep (se 1 (by rfl) ⟨3328370, by rfl⟩ : syracuseStep 4437827 = 6656741) B6656741
theorem B6338371 : Blo 876568 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B1980233 : Blo 876568 1980233 := bstep (se 2 (by rfl) ⟨742587, by rfl⟩ : syracuseStep 1980233 = 1485175) B1485175
theorem B6764633 : Blo 876568 6764633 := bstep (se 2 (by rfl) ⟨2536737, by rfl⟩ : syracuseStep 6764633 = 5073475) B5073475
theorem B7125155 : Blo 876568 7125155 := bstep (se 1 (by rfl) ⟨5343866, by rfl⟩ : syracuseStep 7125155 = 10687733) B10687733
theorem B2963627 : Blo 876568 2963627 := bstep (se 1 (by rfl) ⟨2222720, by rfl⟩ : syracuseStep 2963627 = 4445441) B4445441
theorem B1981025 : Blo 876568 1981025 := bstep (se 2 (by rfl) ⟨742884, by rfl⟩ : syracuseStep 1981025 = 1485769) B1485769
theorem B2964167 : Blo 876568 2964167 := bstep (se 1 (by rfl) ⟨2223125, by rfl⟩ : syracuseStep 2964167 = 4446251) B4446251
theorem B4012753 : Blo 876568 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B3554209 : Blo 876568 3554209 := bstep (se 2 (by rfl) ⟨1332828, by rfl⟩ : syracuseStep 3554209 = 2665657) B2665657
theorem B1784759 : Blo 876568 1784759 := bstep (se 1 (by rfl) ⟨1338569, by rfl⟩ : syracuseStep 1784759 = 2677139) B2677139
theorem B2965031 : Blo 876568 2965031 := bstep (se 1 (by rfl) ⟨2223773, by rfl⟩ : syracuseStep 2965031 = 4447547) B4447547
theorem B2965139 : Blo 876568 2965139 := bstep (se 1 (by rfl) ⟨2223854, by rfl⟩ : syracuseStep 2965139 = 4447709) B4447709
theorem B2506439 : Blo 876568 2506439 := bstep (se 1 (by rfl) ⟨1879829, by rfl⟩ : syracuseStep 2506439 = 3759659) B3759659
theorem B2965355 : Blo 876568 2965355 := bstep (se 1 (by rfl) ⟨2224016, by rfl⟩ : syracuseStep 2965355 = 4448033) B4448033
theorem B2965409 : Blo 876568 2965409 := bstep (se 2 (by rfl) ⟨1112028, by rfl⟩ : syracuseStep 2965409 = 2224057) B2224057
theorem B10141625 : Blo 876568 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B7127297 : Blo 876568 7127297 := bstep (se 2 (by rfl) ⟨2672736, by rfl⟩ : syracuseStep 7127297 = 5345473) B5345473
theorem B2966003 : Blo 876568 2966003 := bstep (se 1 (by rfl) ⟨2224502, by rfl⟩ : syracuseStep 2966003 = 4449005) B4449005
theorem B3556025 : Blo 876568 3556025 := bstep (se 2 (by rfl) ⟨1333509, by rfl⟩ : syracuseStep 3556025 = 2667019) B2667019
theorem B4440905 : Blo 876568 4440905 := bstep (se 2 (by rfl) ⟨1665339, by rfl⟩ : syracuseStep 4440905 = 3330679) B3330679
theorem B2966543 : Blo 876568 2966543 := bstep (se 1 (by rfl) ⟨2224907, by rfl⟩ : syracuseStep 2966543 = 4449815) B4449815
theorem B2114579 : Blo 876568 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B2999467 : Blo 876568 2999467 := bstep (se 1 (by rfl) ⟨2249600, by rfl⟩ : syracuseStep 2999467 = 4499201) B4499201
theorem B6669863 : Blo 876568 6669863 := bstep (se 1 (by rfl) ⟨5002397, by rfl⟩ : syracuseStep 6669863 = 10004795) B10004795
theorem B2967137 : Blo 876568 2967137 := bstep (se 2 (by rfl) ⟨1112676, by rfl⟩ : syracuseStep 2967137 = 2225353) B2225353
theorem B3753611 : Blo 876568 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B18958373 : Blo 876568 18958373 := bstep (se 4 (by rfl) ⟨1777347, by rfl⟩ : syracuseStep 18958373 = 3554695) B3554695
theorem B4442201 : Blo 876568 4442201 := bstep (se 2 (by rfl) ⟨1665825, by rfl⟩ : syracuseStep 4442201 = 3331651) B3331651
theorem B65095987 : Blo 876568 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B17090995 : Blo 876568 17090995 := bstep (se 1 (by rfl) ⟨12818246, by rfl⟩ : syracuseStep 17090995 = 25636493) B25636493
theorem B3328721 : Blo 876568 3328721 := bstep (se 2 (by rfl) ⟨1248270, by rfl⟩ : syracuseStep 3328721 = 2496541) B2496541
theorem B3329039 : Blo 876568 3329039 := bstep (se 1 (by rfl) ⟨2496779, by rfl⟩ : syracuseStep 3329039 = 4993559) B4993559
theorem B2968595 : Blo 876568 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B2378771 : Blo 876568 2378771 := bstep (se 1 (by rfl) ⟨1784078, by rfl⟩ : syracuseStep 2378771 = 3568157) B3568157
theorem B2968919 : Blo 876568 2968919 := bstep (se 1 (by rfl) ⟨2226689, by rfl⟩ : syracuseStep 2968919 = 4453379) B4453379
theorem B2674063 : Blo 876568 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B5000849 : Blo 876568 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B7130861 : Blo 876568 7130861 := bstep (se 3 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 7130861 = 2674073) B2674073
theorem B2379593 : Blo 876568 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B6017105 : Blo 876568 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B5001533 : Blo 876568 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B2969999 : Blo 876568 2969999 := bstep (se 1 (by rfl) ⟨2227499, by rfl⟩ : syracuseStep 2969999 = 4454999) B4454999
theorem B1692065 : Blo 876568 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B27054557 : Blo 876568 27054557 := bstep (se 3 (by rfl) ⟨5072729, by rfl⟩ : syracuseStep 27054557 = 10145459) B10145459
theorem B2970323 : Blo 876568 2970323 := bstep (se 1 (by rfl) ⟨2227742, by rfl⟩ : syracuseStep 2970323 = 4455485) B4455485
theorem B2708537 : Blo 876568 2708537 := bstep (se 2 (by rfl) ⟨1015701, by rfl⟩ : syracuseStep 2708537 = 2031403) B2031403
theorem B3331151 : Blo 876568 3331151 := bstep (se 1 (by rfl) ⟨2498363, by rfl⟩ : syracuseStep 3331151 = 4996727) B4996727
theorem B4281623 : Blo 876568 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B6346127 : Blo 876568 6346127 := bstep (se 1 (by rfl) ⟨4759595, by rfl⟩ : syracuseStep 6346127 = 9519191) B9519191
theorem B6084395 : Blo 876568 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B2971511 : Blo 876568 2971511 := bstep (se 1 (by rfl) ⟨2228633, by rfl⟩ : syracuseStep 2971511 = 4457267) B4457267
theorem B3757985 : Blo 876568 3757985 := bstep (se 2 (by rfl) ⟨1409244, by rfl⟩ : syracuseStep 3757985 = 2818489) B2818489
theorem B2971727 : Blo 876568 2971727 := bstep (se 1 (by rfl) ⟨2228795, by rfl⟩ : syracuseStep 2971727 = 4457591) B4457591
theorem B2219015 : Blo 876568 2219015 := bstep (se 1 (by rfl) ⟨1664261, by rfl⟩ : syracuseStep 2219015 = 3328523) B3328523
theorem B4742297 : Blo 876568 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B4447385 : Blo 876568 4447385 := bstep (se 2 (by rfl) ⟨1667769, by rfl⟩ : syracuseStep 4447385 = 3335539) B3335539
theorem B5627083 : Blo 876568 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B48717233 : Blo 876568 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B4218313 : Blo 876568 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B3333595 : Blo 876568 3333595 := bstep (se 1 (by rfl) ⟨2500196, by rfl⟩ : syracuseStep 3333595 = 5000393) B5000393
theorem B2809441 : Blo 876568 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B2809673 : Blo 876568 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B876583 : Blo 876568 876583 := bstep (se 1 (by rfl) ⟨657437, by rfl⟩ : syracuseStep 876583 = 1314875) B1314875
theorem B876623 : Blo 876568 876623 := bstep (se 1 (by rfl) ⟨657467, by rfl⟩ : syracuseStep 876623 = 1314935) B1314935
theorem B876639 : Blo 876568 876639 := bstep (se 1 (by rfl) ⟨657479, by rfl⟩ : syracuseStep 876639 = 1314959) B1314959
theorem B876667 : Blo 876568 876667 := bstep (se 1 (by rfl) ⟨657500, by rfl⟩ : syracuseStep 876667 = 1315001) B1315001
theorem B876719 : Blo 876568 876719 := bstep (se 1 (by rfl) ⟨657539, by rfl⟩ : syracuseStep 876719 = 1315079) B1315079
theorem B876743 : Blo 876568 876743 := bstep (se 1 (by rfl) ⟨657557, by rfl⟩ : syracuseStep 876743 = 1315115) B1315115
theorem B876763 : Blo 876568 876763 := bstep (se 1 (by rfl) ⟨657572, by rfl⟩ : syracuseStep 876763 = 1315145) B1315145
theorem B876839 : Blo 876568 876839 := bstep (se 1 (by rfl) ⟨657629, by rfl⟩ : syracuseStep 876839 = 1315259) B1315259
theorem B3760445 : Blo 876568 3760445 := bstep (se 3 (by rfl) ⟨705083, by rfl⟩ : syracuseStep 3760445 = 1410167) B1410167
theorem B876879 : Blo 876568 876879 := bstep (se 1 (by rfl) ⟨657659, by rfl⟩ : syracuseStep 876879 = 1315319) B1315319
theorem B876895 : Blo 876568 876895 := bstep (se 1 (by rfl) ⟨657671, by rfl⟩ : syracuseStep 876895 = 1315343) B1315343
theorem B876923 : Blo 876568 876923 := bstep (se 1 (by rfl) ⟨657692, by rfl⟩ : syracuseStep 876923 = 1315385) B1315385
theorem B876975 : Blo 876568 876975 := bstep (se 1 (by rfl) ⟨657731, by rfl⟩ : syracuseStep 876975 = 1315463) B1315463
theorem B876999 : Blo 876568 876999 := bstep (se 1 (by rfl) ⟨657749, by rfl⟩ : syracuseStep 876999 = 1315499) B1315499
theorem B877019 : Blo 876568 877019 := bstep (se 1 (by rfl) ⟨657764, by rfl⟩ : syracuseStep 877019 = 1315529) B1315529
theorem B877095 : Blo 876568 877095 := bstep (se 1 (by rfl) ⟨657821, by rfl⟩ : syracuseStep 877095 = 1315643) B1315643
theorem B877135 : Blo 876568 877135 := bstep (se 1 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 877135 = 1315703) B1315703
theorem B877151 : Blo 876568 877151 := bstep (se 1 (by rfl) ⟨657863, by rfl⟩ : syracuseStep 877151 = 1315727) B1315727
theorem B877179 : Blo 876568 877179 := bstep (se 1 (by rfl) ⟨657884, by rfl⟩ : syracuseStep 877179 = 1315769) B1315769
theorem B877231 : Blo 876568 877231 := bstep (se 1 (by rfl) ⟨657923, by rfl⟩ : syracuseStep 877231 = 1315847) B1315847
theorem B3334841 : Blo 876568 3334841 := bstep (se 2 (by rfl) ⟨1250565, by rfl⟩ : syracuseStep 3334841 = 2501131) B2501131
theorem B877255 : Blo 876568 877255 := bstep (se 1 (by rfl) ⟨657941, by rfl⟩ : syracuseStep 877255 = 1315883) B1315883
theorem B3334871 : Blo 876568 3334871 := bstep (se 1 (by rfl) ⟨2501153, by rfl⟩ : syracuseStep 3334871 = 5002307) B5002307
theorem B877275 : Blo 876568 877275 := bstep (se 1 (by rfl) ⟨657956, by rfl⟩ : syracuseStep 877275 = 1315913) B1315913
theorem B877351 : Blo 876568 877351 := bstep (se 1 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 877351 = 1316027) B1316027
theorem B4514633 : Blo 876568 4514633 := bstep (se 2 (by rfl) ⟨1692987, by rfl⟩ : syracuseStep 4514633 = 3385975) B3385975
theorem B877391 : Blo 876568 877391 := bstep (se 1 (by rfl) ⟨658043, by rfl⟩ : syracuseStep 877391 = 1316087) B1316087
theorem B877407 : Blo 876568 877407 := bstep (se 1 (by rfl) ⟨658055, by rfl⟩ : syracuseStep 877407 = 1316111) B1316111
theorem B877435 : Blo 876568 877435 := bstep (se 1 (by rfl) ⟨658076, by rfl⟩ : syracuseStep 877435 = 1316153) B1316153
theorem B877487 : Blo 876568 877487 := bstep (se 1 (by rfl) ⟨658115, by rfl⟩ : syracuseStep 877487 = 1316231) B1316231
theorem B877511 : Blo 876568 877511 := bstep (se 1 (by rfl) ⟨658133, by rfl⟩ : syracuseStep 877511 = 1316267) B1316267
theorem B27452363 : Blo 876568 27452363 := bstep (se 1 (by rfl) ⟨20589272, by rfl⟩ : syracuseStep 27452363 = 41178545) B41178545
theorem B877531 : Blo 876568 877531 := bstep (se 1 (by rfl) ⟨658148, by rfl⟩ : syracuseStep 877531 = 1316297) B1316297
theorem B877607 : Blo 876568 877607 := bstep (se 1 (by rfl) ⟨658205, by rfl⟩ : syracuseStep 877607 = 1316411) B1316411
theorem B877647 : Blo 876568 877647 := bstep (se 1 (by rfl) ⟨658235, by rfl⟩ : syracuseStep 877647 = 1316471) B1316471
theorem B877663 : Blo 876568 877663 := bstep (se 1 (by rfl) ⟨658247, by rfl⟩ : syracuseStep 877663 = 1316495) B1316495
theorem B877691 : Blo 876568 877691 := bstep (se 1 (by rfl) ⟨658268, by rfl⟩ : syracuseStep 877691 = 1316537) B1316537
theorem B877743 : Blo 876568 877743 := bstep (se 1 (by rfl) ⟨658307, by rfl⟩ : syracuseStep 877743 = 1316615) B1316615
theorem B877767 : Blo 876568 877767 := bstep (se 1 (by rfl) ⟨658325, by rfl⟩ : syracuseStep 877767 = 1316651) B1316651
theorem B877787 : Blo 876568 877787 := bstep (se 1 (by rfl) ⟨658340, by rfl⟩ : syracuseStep 877787 = 1316681) B1316681
theorem B2221303 : Blo 876568 2221303 := bstep (se 1 (by rfl) ⟨1665977, by rfl⟩ : syracuseStep 2221303 = 3331955) B3331955
theorem B877863 : Blo 876568 877863 := bstep (se 1 (by rfl) ⟨658397, by rfl⟩ : syracuseStep 877863 = 1316795) B1316795
theorem B877903 : Blo 876568 877903 := bstep (se 1 (by rfl) ⟨658427, by rfl⟩ : syracuseStep 877903 = 1316855) B1316855
theorem B877919 : Blo 876568 877919 := bstep (se 1 (by rfl) ⟨658439, by rfl⟩ : syracuseStep 877919 = 1316879) B1316879
theorem B877947 : Blo 876568 877947 := bstep (se 1 (by rfl) ⟨658460, by rfl⟩ : syracuseStep 877947 = 1316921) B1316921
theorem B877999 : Blo 876568 877999 := bstep (se 1 (by rfl) ⟨658499, by rfl⟩ : syracuseStep 877999 = 1316999) B1316999
theorem B878023 : Blo 876568 878023 := bstep (se 1 (by rfl) ⟨658517, by rfl⟩ : syracuseStep 878023 = 1317035) B1317035
theorem B878043 : Blo 876568 878043 := bstep (se 1 (by rfl) ⟨658532, by rfl⟩ : syracuseStep 878043 = 1317065) B1317065
theorem B3565043 : Blo 876568 3565043 := bstep (se 1 (by rfl) ⟨2673782, by rfl⟩ : syracuseStep 3565043 = 5347565) B5347565
theorem B2221577 : Blo 876568 2221577 := bstep (se 2 (by rfl) ⟨833091, by rfl⟩ : syracuseStep 2221577 = 1666183) B1666183
theorem B2221607 : Blo 876568 2221607 := bstep (se 1 (by rfl) ⟨1666205, by rfl⟩ : syracuseStep 2221607 = 3332411) B3332411
theorem B878119 : Blo 876568 878119 := bstep (se 1 (by rfl) ⟨658589, by rfl⟩ : syracuseStep 878119 = 1317179) B1317179
theorem B878159 : Blo 876568 878159 := bstep (se 1 (by rfl) ⟨658619, by rfl⟩ : syracuseStep 878159 = 1317239) B1317239
theorem B878175 : Blo 876568 878175 := bstep (se 1 (by rfl) ⟨658631, by rfl⟩ : syracuseStep 878175 = 1317263) B1317263
theorem B878203 : Blo 876568 878203 := bstep (se 1 (by rfl) ⟨658652, by rfl⟩ : syracuseStep 878203 = 1317305) B1317305
theorem B878255 : Blo 876568 878255 := bstep (se 1 (by rfl) ⟨658691, by rfl⟩ : syracuseStep 878255 = 1317383) B1317383
theorem B878279 : Blo 876568 878279 := bstep (se 1 (by rfl) ⟨658709, by rfl⟩ : syracuseStep 878279 = 1317419) B1317419
theorem B1205959 : Blo 876568 1205959 := bstep (se 1 (by rfl) ⟨904469, by rfl⟩ : syracuseStep 1205959 = 1808939) B1808939
theorem B878299 : Blo 876568 878299 := bstep (se 1 (by rfl) ⟨658724, by rfl⟩ : syracuseStep 878299 = 1317449) B1317449
theorem B878375 : Blo 876568 878375 := bstep (se 1 (by rfl) ⟨658781, by rfl⟩ : syracuseStep 878375 = 1317563) B1317563
theorem B878415 : Blo 876568 878415 := bstep (se 1 (by rfl) ⟨658811, by rfl⟩ : syracuseStep 878415 = 1317623) B1317623
theorem B878431 : Blo 876568 878431 := bstep (se 1 (by rfl) ⟨658823, by rfl⟩ : syracuseStep 878431 = 1317647) B1317647
theorem B2221931 : Blo 876568 2221931 := bstep (se 1 (by rfl) ⟨1666448, by rfl⟩ : syracuseStep 2221931 = 3332897) B3332897
theorem B1337195 : Blo 876568 1337195 := bstep (se 1 (by rfl) ⟨1002896, by rfl⟩ : syracuseStep 1337195 = 2005793) B2005793
theorem B878459 : Blo 876568 878459 := bstep (se 1 (by rfl) ⟨658844, by rfl⟩ : syracuseStep 878459 = 1317689) B1317689
theorem B12838817 : Blo 876568 12838817 := bstep (se 2 (by rfl) ⟨4814556, by rfl⟩ : syracuseStep 12838817 = 9629113) B9629113
theorem B878511 : Blo 876568 878511 := bstep (se 1 (by rfl) ⟨658883, by rfl⟩ : syracuseStep 878511 = 1317767) B1317767
theorem B7235513 : Blo 876568 7235513 := bstep (se 2 (by rfl) ⟨2713317, by rfl⟩ : syracuseStep 7235513 = 5426635) B5426635
theorem B23128001 : Blo 876568 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B878535 : Blo 876568 878535 := bstep (se 1 (by rfl) ⟨658901, by rfl⟩ : syracuseStep 878535 = 1317803) B1317803
theorem B878555 : Blo 876568 878555 := bstep (se 1 (by rfl) ⟨658916, by rfl⟩ : syracuseStep 878555 = 1317833) B1317833
theorem B878631 : Blo 876568 878631 := bstep (se 1 (by rfl) ⟨658973, by rfl⟩ : syracuseStep 878631 = 1317947) B1317947
theorem B878671 : Blo 876568 878671 := bstep (se 1 (by rfl) ⟨659003, by rfl⟩ : syracuseStep 878671 = 1318007) B1318007
theorem B878687 : Blo 876568 878687 := bstep (se 1 (by rfl) ⟨659015, by rfl⟩ : syracuseStep 878687 = 1318031) B1318031
theorem B878715 : Blo 876568 878715 := bstep (se 1 (by rfl) ⟨659036, by rfl⟩ : syracuseStep 878715 = 1318073) B1318073
theorem B878767 : Blo 876568 878767 := bstep (se 1 (by rfl) ⟨659075, by rfl⟩ : syracuseStep 878767 = 1318151) B1318151
theorem B878791 : Blo 876568 878791 := bstep (se 1 (by rfl) ⟨659093, by rfl⟩ : syracuseStep 878791 = 1318187) B1318187
theorem B878811 : Blo 876568 878811 := bstep (se 1 (by rfl) ⟨659108, by rfl⟩ : syracuseStep 878811 = 1318217) B1318217
theorem B878887 : Blo 876568 878887 := bstep (se 1 (by rfl) ⟨659165, by rfl⟩ : syracuseStep 878887 = 1318331) B1318331
theorem B878927 : Blo 876568 878927 := bstep (se 1 (by rfl) ⟨659195, by rfl⟩ : syracuseStep 878927 = 1318391) B1318391
theorem B878943 : Blo 876568 878943 := bstep (se 1 (by rfl) ⟨659207, by rfl⟩ : syracuseStep 878943 = 1318415) B1318415
theorem B878971 : Blo 876568 878971 := bstep (se 1 (by rfl) ⟨659228, by rfl⟩ : syracuseStep 878971 = 1318457) B1318457
theorem B3565949 : Blo 876568 3565949 := bstep (se 3 (by rfl) ⟨668615, by rfl⟩ : syracuseStep 3565949 = 1337231) B1337231
theorem B879023 : Blo 876568 879023 := bstep (se 1 (by rfl) ⟨659267, by rfl⟩ : syracuseStep 879023 = 1318535) B1318535
theorem B879047 : Blo 876568 879047 := bstep (se 1 (by rfl) ⟨659285, by rfl⟩ : syracuseStep 879047 = 1318571) B1318571
theorem B879067 : Blo 876568 879067 := bstep (se 1 (by rfl) ⟨659300, by rfl⟩ : syracuseStep 879067 = 1318601) B1318601
theorem B2222579 : Blo 876568 2222579 := bstep (se 1 (by rfl) ⟨1666934, by rfl⟩ : syracuseStep 2222579 = 3333869) B3333869
theorem B4516361 : Blo 876568 4516361 := bstep (se 2 (by rfl) ⟨1693635, by rfl⟩ : syracuseStep 4516361 = 3387271) B3387271
theorem B2812441 : Blo 876568 2812441 := bstep (se 2 (by rfl) ⟨1054665, by rfl⟩ : syracuseStep 2812441 = 2109331) B2109331
theorem B879143 : Blo 876568 879143 := bstep (se 1 (by rfl) ⟨659357, by rfl⟩ : syracuseStep 879143 = 1318715) B1318715
theorem B879183 : Blo 876568 879183 := bstep (se 1 (by rfl) ⟨659387, by rfl⟩ : syracuseStep 879183 = 1318775) B1318775
theorem B879199 : Blo 876568 879199 := bstep (se 1 (by rfl) ⟨659399, by rfl⟩ : syracuseStep 879199 = 1318799) B1318799
theorem B1665659 : Blo 876568 1665659 := bstep (se 1 (by rfl) ⟨1249244, by rfl⟩ : syracuseStep 1665659 = 2498489) B2498489
theorem B879227 : Blo 876568 879227 := bstep (se 1 (by rfl) ⟨659420, by rfl⟩ : syracuseStep 879227 = 1318841) B1318841
theorem B1501867 : Blo 876568 1501867 := bstep (se 1 (by rfl) ⟨1126400, by rfl⟩ : syracuseStep 1501867 = 2252801) B2252801
theorem B879279 : Blo 876568 879279 := bstep (se 1 (by rfl) ⟨659459, by rfl⟩ : syracuseStep 879279 = 1318919) B1318919
theorem B879303 : Blo 876568 879303 := bstep (se 1 (by rfl) ⟨659477, by rfl⟩ : syracuseStep 879303 = 1318955) B1318955
theorem B879323 : Blo 876568 879323 := bstep (se 1 (by rfl) ⟨659492, by rfl⟩ : syracuseStep 879323 = 1318985) B1318985
theorem B879399 : Blo 876568 879399 := bstep (se 1 (by rfl) ⟨659549, by rfl⟩ : syracuseStep 879399 = 1319099) B1319099
theorem B879439 : Blo 876568 879439 := bstep (se 1 (by rfl) ⟨659579, by rfl⟩ : syracuseStep 879439 = 1319159) B1319159
theorem B879455 : Blo 876568 879455 := bstep (se 1 (by rfl) ⟨659591, by rfl⟩ : syracuseStep 879455 = 1319183) B1319183
theorem B879483 : Blo 876568 879483 := bstep (se 1 (by rfl) ⟨659612, by rfl⟩ : syracuseStep 879483 = 1319225) B1319225
theorem B879535 : Blo 876568 879535 := bstep (se 1 (by rfl) ⟨659651, by rfl⟩ : syracuseStep 879535 = 1319303) B1319303
theorem B4746167 : Blo 876568 4746167 := bstep (se 1 (by rfl) ⟨3559625, by rfl⟩ : syracuseStep 4746167 = 7119251) B7119251
theorem B2223035 : Blo 876568 2223035 := bstep (se 1 (by rfl) ⟨1667276, by rfl⟩ : syracuseStep 2223035 = 3334553) B3334553
theorem B879559 : Blo 876568 879559 := bstep (se 1 (by rfl) ⟨659669, by rfl⟩ : syracuseStep 879559 = 1319339) B1319339
theorem B879579 : Blo 876568 879579 := bstep (se 1 (by rfl) ⟨659684, by rfl⟩ : syracuseStep 879579 = 1319369) B1319369
theorem B879655 : Blo 876568 879655 := bstep (se 1 (by rfl) ⟨659741, by rfl⟩ : syracuseStep 879655 = 1319483) B1319483
theorem B879695 : Blo 876568 879695 := bstep (se 1 (by rfl) ⟨659771, by rfl⟩ : syracuseStep 879695 = 1319543) B1319543
theorem B879711 : Blo 876568 879711 := bstep (se 1 (by rfl) ⟨659783, by rfl⟩ : syracuseStep 879711 = 1319567) B1319567
theorem B1666145 : Blo 876568 1666145 := bstep (se 2 (by rfl) ⟨624804, by rfl⟩ : syracuseStep 1666145 = 1249609) B1249609
theorem B879739 : Blo 876568 879739 := bstep (se 1 (by rfl) ⟨659804, by rfl⟩ : syracuseStep 879739 = 1319609) B1319609
theorem B879791 : Blo 876568 879791 := bstep (se 1 (by rfl) ⟨659843, by rfl⟩ : syracuseStep 879791 = 1319687) B1319687
theorem B15002819 : Blo 876568 15002819 := bstep (se 1 (by rfl) ⟨11252114, by rfl⟩ : syracuseStep 15002819 = 22504229) B22504229
theorem B879815 : Blo 876568 879815 := bstep (se 1 (by rfl) ⟨659861, by rfl⟩ : syracuseStep 879815 = 1319723) B1319723
theorem B879835 : Blo 876568 879835 := bstep (se 1 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 879835 = 1319753) B1319753
theorem B3337483 : Blo 876568 3337483 := bstep (se 1 (by rfl) ⟨2503112, by rfl⟩ : syracuseStep 3337483 = 5006225) B5006225
theorem B13200653 : Blo 876568 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B6319397 : Blo 876568 6319397 := bstep (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) B1184887
theorem B879911 : Blo 876568 879911 := bstep (se 1 (by rfl) ⟨659933, by rfl⟩ : syracuseStep 879911 = 1319867) B1319867
theorem B879951 : Blo 876568 879951 := bstep (se 1 (by rfl) ⟨659963, by rfl⟩ : syracuseStep 879951 = 1319927) B1319927
theorem B879967 : Blo 876568 879967 := bstep (se 1 (by rfl) ⟨659975, by rfl⟩ : syracuseStep 879967 = 1319951) B1319951
theorem B879995 : Blo 876568 879995 := bstep (se 1 (by rfl) ⟨659996, by rfl⟩ : syracuseStep 879995 = 1319993) B1319993
theorem B880047 : Blo 876568 880047 := bstep (se 1 (by rfl) ⟨660035, by rfl⟩ : syracuseStep 880047 = 1320071) B1320071
theorem B1666487 : Blo 876568 1666487 := bstep (se 1 (by rfl) ⟨1249865, by rfl⟩ : syracuseStep 1666487 = 2499731) B2499731
theorem B880071 : Blo 876568 880071 := bstep (se 1 (by rfl) ⟨660053, by rfl⟩ : syracuseStep 880071 = 1320107) B1320107
theorem B1109467 : Blo 876568 1109467 := bstep (se 1 (by rfl) ⟨832100, by rfl⟩ : syracuseStep 1109467 = 1664201) B1664201
theorem B880091 : Blo 876568 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B880167 : Blo 876568 880167 := bstep (se 1 (by rfl) ⟨660125, by rfl⟩ : syracuseStep 880167 = 1320251) B1320251
theorem B3337787 : Blo 876568 3337787 := bstep (se 1 (by rfl) ⟨2503340, by rfl⟩ : syracuseStep 3337787 = 5006681) B5006681
theorem B880207 : Blo 876568 880207 := bstep (se 1 (by rfl) ⟨660155, by rfl⟩ : syracuseStep 880207 = 1320311) B1320311
theorem B880223 : Blo 876568 880223 := bstep (se 1 (by rfl) ⟨660167, by rfl⟩ : syracuseStep 880223 = 1320335) B1320335
theorem B2223713 : Blo 876568 2223713 := bstep (se 2 (by rfl) ⟨833892, by rfl⟩ : syracuseStep 2223713 = 1667785) B1667785
theorem B880251 : Blo 876568 880251 := bstep (se 1 (by rfl) ⟨660188, by rfl⟩ : syracuseStep 880251 = 1320377) B1320377
theorem B880303 : Blo 876568 880303 := bstep (se 1 (by rfl) ⟨660227, by rfl⟩ : syracuseStep 880303 = 1320455) B1320455
theorem B880327 : Blo 876568 880327 := bstep (se 1 (by rfl) ⟨660245, by rfl⟩ : syracuseStep 880327 = 1320491) B1320491
theorem B880347 : Blo 876568 880347 := bstep (se 1 (by rfl) ⟨660260, by rfl⟩ : syracuseStep 880347 = 1320521) B1320521
theorem B22802141 : Blo 876568 22802141 := bstep (se 3 (by rfl) ⟨4275401, by rfl⟩ : syracuseStep 22802141 = 8550803) B8550803
theorem B880423 : Blo 876568 880423 := bstep (se 1 (by rfl) ⟨660317, by rfl⟩ : syracuseStep 880423 = 1320635) B1320635
theorem B1666889 : Blo 876568 1666889 := bstep (se 2 (by rfl) ⟨625083, by rfl⟩ : syracuseStep 1666889 = 1250167) B1250167
theorem B880463 : Blo 876568 880463 := bstep (se 1 (by rfl) ⟨660347, by rfl⟩ : syracuseStep 880463 = 1320695) B1320695
theorem B880479 : Blo 876568 880479 := bstep (se 1 (by rfl) ⟨660359, by rfl⟩ : syracuseStep 880479 = 1320719) B1320719
theorem B880507 : Blo 876568 880507 := bstep (se 1 (by rfl) ⟨660380, by rfl⟩ : syracuseStep 880507 = 1320761) B1320761
theorem B880559 : Blo 876568 880559 := bstep (se 1 (by rfl) ⟨660419, by rfl⟩ : syracuseStep 880559 = 1320839) B1320839
theorem B6320065 : Blo 876568 6320065 := bstep (se 2 (by rfl) ⟨2370024, by rfl⟩ : syracuseStep 6320065 = 4740049) B4740049
theorem B1405279 : Blo 876568 1405279 := bstep (se 1 (by rfl) ⟨1053959, by rfl⟩ : syracuseStep 1405279 = 2107919) B2107919
theorem B1667603 : Blo 876568 1667603 := bstep (se 1 (by rfl) ⟨1250702, by rfl⟩ : syracuseStep 1667603 = 2501405) B2501405
theorem B1667641 : Blo 876568 1667641 := bstep (se 2 (by rfl) ⟨625365, by rfl⟩ : syracuseStep 1667641 = 1250731) B1250731
theorem B3338941 : Blo 876568 3338941 := bstep (se 3 (by rfl) ⟨626051, by rfl⟩ : syracuseStep 3338941 = 1252103) B1252103
theorem B11268881 : Blo 876568 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B1667945 : Blo 876568 1667945 := bstep (se 2 (by rfl) ⟨625479, by rfl⟩ : syracuseStep 1667945 = 1250959) B1250959
theorem B6681527 : Blo 876568 6681527 := bstep (se 1 (by rfl) ⟨5011145, by rfl⟩ : syracuseStep 6681527 = 10022291) B10022291
theorem B2225171 : Blo 876568 2225171 := bstep (se 1 (by rfl) ⟨1668878, by rfl⟩ : syracuseStep 2225171 = 3337757) B3337757
theorem B2815337 : Blo 876568 2815337 := bstep (se 2 (by rfl) ⟨1055751, by rfl⟩ : syracuseStep 2815337 = 2111503) B2111503
theorem B15037811 : Blo 876568 15037811 := bstep (se 1 (by rfl) ⟨11278358, by rfl⟩ : syracuseStep 15037811 = 22556717) B22556717
theorem B2225627 : Blo 876568 2225627 := bstep (se 1 (by rfl) ⟨1669220, by rfl⟩ : syracuseStep 2225627 = 3338441) B3338441
theorem B3339899 : Blo 876568 3339899 := bstep (se 1 (by rfl) ⟨2504924, by rfl⟩ : syracuseStep 3339899 = 5009849) B5009849
theorem B4454027 : Blo 876568 4454027 := bstep (se 1 (by rfl) ⟨3340520, by rfl⟩ : syracuseStep 4454027 = 6681041) B6681041
theorem B1406663 : Blo 876568 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B1505015 : Blo 876568 1505015 := bstep (se 1 (by rfl) ⟨1128761, by rfl⟩ : syracuseStep 1505015 = 2257523) B2257523
theorem B1669243 : Blo 876568 1669243 := bstep (se 1 (by rfl) ⟨1251932, by rfl⟩ : syracuseStep 1669243 = 2503865) B2503865
theorem B1669319 : Blo 876568 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B12646637 : Blo 876568 12646637 := bstep (se 3 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 12646637 = 4742489) B4742489
theorem B6682985 : Blo 876568 6682985 := bstep (se 2 (by rfl) ⟨2506119, by rfl⟩ : syracuseStep 6682985 = 5012239) B5012239
theorem B3340673 : Blo 876568 3340673 := bstep (se 2 (by rfl) ⟨1252752, by rfl⟩ : syracuseStep 3340673 = 2505505) B2505505
theorem B1407451 : Blo 876568 1407451 := bstep (se 1 (by rfl) ⟨1055588, by rfl⟩ : syracuseStep 1407451 = 2111177) B2111177
theorem B1669729 : Blo 876568 1669729 := bstep (se 2 (by rfl) ⟨626148, by rfl⟩ : syracuseStep 1669729 = 1252297) B1252297
theorem B2226811 : Blo 876568 2226811 := bstep (se 1 (by rfl) ⟨1670108, by rfl⟩ : syracuseStep 2226811 = 3340217) B3340217
theorem B11238173 : Blo 876568 11238173 := bstep (se 3 (by rfl) ⟨2107157, by rfl⟩ : syracuseStep 11238173 = 4214315) B4214315
theorem B4750255 : Blo 876568 4750255 := bstep (se 1 (by rfl) ⟨3562691, by rfl⟩ : syracuseStep 4750255 = 7125383) B7125383
theorem B1670071 : Blo 876568 1670071 := bstep (se 1 (by rfl) ⟨1252553, by rfl⟩ : syracuseStep 1670071 = 2505107) B2505107
theorem B1408079 : Blo 876568 1408079 := bstep (se 1 (by rfl) ⟨1056059, by rfl⟩ : syracuseStep 1408079 = 2112119) B2112119
theorem B22871119 : Blo 876568 22871119 := bstep (se 1 (by rfl) ⟨17153339, by rfl⟩ : syracuseStep 22871119 = 34306679) B34306679
theorem B1670473 : Blo 876568 1670473 := bstep (se 2 (by rfl) ⟨626427, by rfl⟩ : syracuseStep 1670473 = 1252855) B1252855
theorem B1113527 : Blo 876568 1113527 := bstep (se 1 (by rfl) ⟨835145, by rfl⟩ : syracuseStep 1113527 = 1670291) B1670291
theorem B3341857 : Blo 876568 3341857 := bstep (se 2 (by rfl) ⟨1253196, by rfl⟩ : syracuseStep 3341857 = 2506393) B2506393
theorem B1113679 : Blo 876568 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B6094535 : Blo 876568 6094535 := bstep (se 1 (by rfl) ⟨4570901, by rfl⟩ : syracuseStep 6094535 = 9141803) B9141803
theorem B2817899 : Blo 876568 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B16023415 : Blo 876568 16023415 := bstep (se 1 (by rfl) ⟨12017561, by rfl⟩ : syracuseStep 16023415 = 24035123) B24035123
theorem B14221241 : Blo 876568 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B5636105 : Blo 876568 5636105 := bstep (se 2 (by rfl) ⟨2113539, by rfl⟩ : syracuseStep 5636105 = 4227079) B4227079
theorem B4456457 : Blo 876568 4456457 := bstep (se 2 (by rfl) ⟨1671171, by rfl⟩ : syracuseStep 4456457 = 3342343) B3342343
theorem B2228249 : Blo 876568 2228249 := bstep (se 2 (by rfl) ⟨835593, by rfl⟩ : syracuseStep 2228249 = 1671187) B1671187
theorem B4751531 : Blo 876568 4751531 := bstep (se 1 (by rfl) ⟨3563648, by rfl⟩ : syracuseStep 4751531 = 7127297) B7127297
theorem B4456619 : Blo 876568 4456619 := bstep (se 1 (by rfl) ⟨3342464, by rfl⟩ : syracuseStep 4456619 = 6684929) B6684929
theorem B2228705 : Blo 876568 2228705 := bstep (se 2 (by rfl) ⟨835764, by rfl⟩ : syracuseStep 2228705 = 1671529) B1671529
theorem B2228755 : Blo 876568 2228755 := bstep (se 1 (by rfl) ⟨1671566, by rfl⟩ : syracuseStep 2228755 = 3343133) B3343133
theorem B4457105 : Blo 876568 4457105 := bstep (se 2 (by rfl) ⟨1671414, by rfl⟩ : syracuseStep 4457105 = 3342829) B3342829
theorem B1409719 : Blo 876568 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B5014973 : Blo 876568 5014973 := bstep (se 3 (by rfl) ⟨940307, by rfl⟩ : syracuseStep 5014973 = 1880615) B1880615
theorem B3999289 : Blo 876568 3999289 := bstep (se 2 (by rfl) ⟨1499733, by rfl⟩ : syracuseStep 3999289 = 2999467) B2999467
theorem B5637721 : Blo 876568 5637721 := bstep (se 2 (by rfl) ⟨2114145, by rfl⟩ : syracuseStep 5637721 = 4228291) B4228291
theorem B1607945 : Blo 876568 1607945 := bstep (se 2 (by rfl) ⟨602979, by rfl⟩ : syracuseStep 1607945 = 1205959) B1205959
theorem B8129011 : Blo 876568 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B4753907 : Blo 876568 4753907 := bstep (se 1 (by rfl) ⟨3565430, by rfl⟩ : syracuseStep 4753907 = 7130861) B7130861
theorem B73206301 : Blo 876568 73206301 := bstep (se 3 (by rfl) ⟨13726181, by rfl⟩ : syracuseStep 73206301 = 27452363) B27452363
theorem B11242273 : Blo 876568 11242273 := bstep (se 2 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 11242273 = 8431705) B8431705
theorem B12651659 : Blo 876568 12651659 := bstep (se 1 (by rfl) ⟨9488744, by rfl⟩ : syracuseStep 12651659 = 18977489) B18977489
theorem B2886943 : Blo 876568 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B1248635 : Blo 876568 1248635 := bstep (se 1 (by rfl) ⟨936476, by rfl⟩ : syracuseStep 1248635 = 1872953) B1872953
theorem B2854415 : Blo 876568 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B2002489 : Blo 876568 2002489 := bstep (se 2 (by rfl) ⟨750933, by rfl⟩ : syracuseStep 2002489 = 1501867) B1501867
theorem B986719 : Blo 876568 986719 := bstep (se 1 (by rfl) ⟨740039, by rfl⟩ : syracuseStep 986719 = 1480079) B1480079
theorem B3805193 : Blo 876568 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B1315163 : Blo 876568 1315163 := bstep (se 1 (by rfl) ⟨986372, by rfl⟩ : syracuseStep 1315163 = 1972745) B1972745
theorem B1315391 : Blo 876568 1315391 := bstep (se 1 (by rfl) ⟨986543, by rfl⟩ : syracuseStep 1315391 = 1973087) B1973087
theorem B1479289 : Blo 876568 1479289 := bstep (se 2 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 1479289 = 1109467) B1109467
theorem B1479343 : Blo 876568 1479343 := bstep (se 1 (by rfl) ⟨1109507, by rfl⟩ : syracuseStep 1479343 = 2219015) B2219015
theorem B1315511 : Blo 876568 1315511 := bstep (se 1 (by rfl) ⟨986633, by rfl⟩ : syracuseStep 1315511 = 1973267) B1973267
theorem B987871 : Blo 876568 987871 := bstep (se 1 (by rfl) ⟨740903, by rfl⟩ : syracuseStep 987871 = 1481807) B1481807
theorem B1315739 : Blo 876568 1315739 := bstep (se 1 (by rfl) ⟨986804, by rfl⟩ : syracuseStep 1315739 = 1973609) B1973609
theorem B32478155 : Blo 876568 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B1873115 : Blo 876568 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B8426753 : Blo 876568 8426753 := bstep (se 2 (by rfl) ⟨3160032, by rfl⟩ : syracuseStep 8426753 = 6320065) B6320065
theorem B988447 : Blo 876568 988447 := bstep (se 1 (by rfl) ⟨741335, by rfl⟩ : syracuseStep 988447 = 1482671) B1482671
theorem B1316135 : Blo 876568 1316135 := bstep (se 1 (by rfl) ⟨987101, by rfl⟩ : syracuseStep 1316135 = 1974203) B1974203
theorem B1185115 : Blo 876568 1185115 := bstep (se 1 (by rfl) ⟨888836, by rfl⟩ : syracuseStep 1185115 = 1777673) B1777673
theorem B1054075 : Blo 876568 1054075 := bstep (se 1 (by rfl) ⟨790556, by rfl⟩ : syracuseStep 1054075 = 1581113) B1581113
theorem B1316219 : Blo 876568 1316219 := bstep (se 1 (by rfl) ⟨987164, by rfl⟩ : syracuseStep 1316219 = 1974329) B1974329
theorem B1250759 : Blo 876568 1250759 := bstep (se 1 (by rfl) ⟨938069, by rfl⟩ : syracuseStep 1250759 = 1876139) B1876139
theorem B1316345 : Blo 876568 1316345 := bstep (se 2 (by rfl) ⟨493629, by rfl⟩ : syracuseStep 1316345 = 987259) B987259
theorem B16258603 : Blo 876568 16258603 := bstep (se 1 (by rfl) ⟨12193952, by rfl⟩ : syracuseStep 16258603 = 24387905) B24387905
theorem B988735 : Blo 876568 988735 := bstep (se 1 (by rfl) ⟨741551, by rfl⟩ : syracuseStep 988735 = 1483103) B1483103
theorem B1316447 : Blo 876568 1316447 := bstep (se 1 (by rfl) ⟨987335, by rfl⟩ : syracuseStep 1316447 = 1974671) B1974671
theorem B2496187 : Blo 876568 2496187 := bstep (se 1 (by rfl) ⟨1872140, by rfl⟩ : syracuseStep 2496187 = 3744281) B3744281
theorem B1873705 : Blo 876568 1873705 := bstep (se 2 (by rfl) ⟨702639, by rfl⟩ : syracuseStep 1873705 = 1405279) B1405279
theorem B1316663 : Blo 876568 1316663 := bstep (se 1 (by rfl) ⟨987497, by rfl⟩ : syracuseStep 1316663 = 1974995) B1974995
theorem B1316969 : Blo 876568 1316969 := bstep (se 2 (by rfl) ⟨493863, by rfl⟩ : syracuseStep 1316969 = 987727) B987727
theorem B9509197 : Blo 876568 9509197 := bstep (se 3 (by rfl) ⟨1782974, by rfl⟩ : syracuseStep 9509197 = 3565949) B3565949
theorem B1481051 : Blo 876568 1481051 := bstep (se 1 (by rfl) ⟨1110788, by rfl⟩ : syracuseStep 1481051 = 2221577) B2221577
theorem B1481071 : Blo 876568 1481071 := bstep (se 1 (by rfl) ⟨1110803, by rfl⟩ : syracuseStep 1481071 = 2221607) B2221607
theorem B989563 : Blo 876568 989563 := bstep (se 1 (by rfl) ⟨742172, by rfl⟩ : syracuseStep 989563 = 1484345) B1484345
theorem B1317287 : Blo 876568 1317287 := bstep (se 1 (by rfl) ⟨987965, by rfl⟩ : syracuseStep 1317287 = 1975931) B1975931
theorem B1972655 : Blo 876568 1972655 := bstep (se 1 (by rfl) ⟨1479491, by rfl⟩ : syracuseStep 1972655 = 2958983) B2958983
theorem B1972691 : Blo 876568 1972691 := bstep (se 1 (by rfl) ⟨1479518, by rfl⟩ : syracuseStep 1972691 = 2959037) B2959037
theorem B1317371 : Blo 876568 1317371 := bstep (se 1 (by rfl) ⟨988028, by rfl⟩ : syracuseStep 1317371 = 1976057) B1976057
theorem B1972799 : Blo 876568 1972799 := bstep (se 1 (by rfl) ⟨1479599, by rfl⟩ : syracuseStep 1972799 = 2959199) B2959199
theorem B1481287 : Blo 876568 1481287 := bstep (se 1 (by rfl) ⟨1110965, by rfl⟩ : syracuseStep 1481287 = 2221931) B2221931
theorem B1317497 : Blo 876568 1317497 := bstep (se 2 (by rfl) ⟨494061, by rfl⟩ : syracuseStep 1317497 = 988123) B988123
theorem B4823675 : Blo 876568 4823675 := bstep (se 1 (by rfl) ⟨3617756, by rfl⟩ : syracuseStep 4823675 = 7235513) B7235513
theorem B1972907 : Blo 876568 1972907 := bstep (se 1 (by rfl) ⟨1479680, by rfl⟩ : syracuseStep 1972907 = 2959361) B2959361
theorem B1317551 : Blo 876568 1317551 := bstep (se 1 (by rfl) ⟨988163, by rfl⟩ : syracuseStep 1317551 = 1976327) B1976327
theorem B1317599 : Blo 876568 1317599 := bstep (se 1 (by rfl) ⟨988199, by rfl⟩ : syracuseStep 1317599 = 1976399) B1976399
theorem B990031 : Blo 876568 990031 := bstep (se 1 (by rfl) ⟨742523, by rfl⟩ : syracuseStep 990031 = 1485047) B1485047
theorem B1317863 : Blo 876568 1317863 := bstep (se 1 (by rfl) ⟨988397, by rfl⟩ : syracuseStep 1317863 = 1976795) B1976795
theorem B1481719 : Blo 876568 1481719 := bstep (se 1 (by rfl) ⟨1111289, by rfl⟩ : syracuseStep 1481719 = 2222579) B2222579
theorem B1973447 : Blo 876568 1973447 := bstep (se 1 (by rfl) ⟨1480085, by rfl⟩ : syracuseStep 1973447 = 2960171) B2960171
theorem B990427 : Blo 876568 990427 := bstep (se 1 (by rfl) ⟨742820, by rfl⟩ : syracuseStep 990427 = 1485641) B1485641
theorem B1318121 : Blo 876568 1318121 := bstep (se 2 (by rfl) ⟨494295, by rfl⟩ : syracuseStep 1318121 = 988591) B988591
theorem B1318175 : Blo 876568 1318175 := bstep (se 1 (by rfl) ⟨988631, by rfl⟩ : syracuseStep 1318175 = 1977263) B1977263
theorem B1482023 : Blo 876568 1482023 := bstep (se 1 (by rfl) ⟨1111517, by rfl⟩ : syracuseStep 1482023 = 2223035) B2223035
theorem B1973627 : Blo 876568 1973627 := bstep (se 1 (by rfl) ⟨1480220, by rfl⟩ : syracuseStep 1973627 = 2960441) B2960441
theorem B14261669 : Blo 876568 14261669 := bstep (se 4 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 14261669 = 2674063) B2674063
theorem B1318343 : Blo 876568 1318343 := bstep (se 1 (by rfl) ⟨988757, by rfl⟩ : syracuseStep 1318343 = 1977515) B1977515
theorem B10001879 : Blo 876568 10001879 := bstep (se 1 (by rfl) ⟨7501409, by rfl⟩ : syracuseStep 10001879 = 15002819) B15002819
theorem B1973753 : Blo 876568 1973753 := bstep (se 2 (by rfl) ⟨740157, by rfl⟩ : syracuseStep 1973753 = 1480315) B1480315
theorem B1056251 : Blo 876568 1056251 := bstep (se 1 (by rfl) ⟨792188, by rfl⟩ : syracuseStep 1056251 = 1584377) B1584377
theorem B1973843 : Blo 876568 1973843 := bstep (se 1 (by rfl) ⟨1480382, by rfl⟩ : syracuseStep 1973843 = 2960765) B2960765
theorem B1482475 : Blo 876568 1482475 := bstep (se 1 (by rfl) ⟨1111856, by rfl⟩ : syracuseStep 1482475 = 2223713) B2223713
theorem B1974023 : Blo 876568 1974023 := bstep (se 1 (by rfl) ⟨1480517, by rfl⟩ : syracuseStep 1974023 = 2961035) B2961035
theorem B1318697 : Blo 876568 1318697 := bstep (se 2 (by rfl) ⟨494511, by rfl⟩ : syracuseStep 1318697 = 989023) B989023
theorem B1318703 : Blo 876568 1318703 := bstep (se 1 (by rfl) ⟨989027, by rfl⟩ : syracuseStep 1318703 = 1978055) B1978055
theorem B1056559 : Blo 876568 1056559 := bstep (se 1 (by rfl) ⟨792419, by rfl⟩ : syracuseStep 1056559 = 1584839) B1584839
theorem B4759357 : Blo 876568 4759357 := bstep (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) B1784759
theorem B7610273 : Blo 876568 7610273 := bstep (se 2 (by rfl) ⟨2853852, by rfl⟩ : syracuseStep 7610273 = 5707705) B5707705
theorem B1319177 : Blo 876568 1319177 := bstep (se 2 (by rfl) ⟨494691, by rfl⟩ : syracuseStep 1319177 = 989383) B989383
theorem B1974635 : Blo 876568 1974635 := bstep (se 1 (by rfl) ⟨1480976, by rfl⟩ : syracuseStep 1974635 = 2961953) B2961953
theorem B1319279 : Blo 876568 1319279 := bstep (se 1 (by rfl) ⟨989459, by rfl⟩ : syracuseStep 1319279 = 1978919) B1978919
theorem B1974779 : Blo 876568 1974779 := bstep (se 1 (by rfl) ⟨1481084, by rfl⟩ : syracuseStep 1974779 = 2962169) B2962169
theorem B7512587 : Blo 876568 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B1319495 : Blo 876568 1319495 := bstep (se 1 (by rfl) ⟨989621, by rfl⟩ : syracuseStep 1319495 = 1979243) B1979243
theorem B1319531 : Blo 876568 1319531 := bstep (se 1 (by rfl) ⟨989648, by rfl⟩ : syracuseStep 1319531 = 1979297) B1979297
theorem B1581689 : Blo 876568 1581689 := bstep (se 2 (by rfl) ⟨593133, by rfl⟩ : syracuseStep 1581689 = 1186267) B1186267
theorem B1974905 : Blo 876568 1974905 := bstep (se 2 (by rfl) ⟨740589, by rfl⟩ : syracuseStep 1974905 = 1481179) B1481179
theorem B1876601 : Blo 876568 1876601 := bstep (se 2 (by rfl) ⟨703725, by rfl⟩ : syracuseStep 1876601 = 1407451) B1407451
theorem B1974959 : Blo 876568 1974959 := bstep (se 1 (by rfl) ⟨1481219, by rfl⟩ : syracuseStep 1974959 = 2962439) B2962439
theorem B1483447 : Blo 876568 1483447 := bstep (se 1 (by rfl) ⟨1112585, by rfl⟩ : syracuseStep 1483447 = 2225171) B2225171
theorem B1975031 : Blo 876568 1975031 := bstep (se 1 (by rfl) ⟨1481273, by rfl⟩ : syracuseStep 1975031 = 2962547) B2962547
theorem B16851725 : Blo 876568 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B1319759 : Blo 876568 1319759 := bstep (se 1 (by rfl) ⟨989819, by rfl⟩ : syracuseStep 1319759 = 1979639) B1979639
theorem B1876891 : Blo 876568 1876891 := bstep (se 1 (by rfl) ⟨1407668, by rfl⟩ : syracuseStep 1876891 = 2815337) B2815337
theorem B1975211 : Blo 876568 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B5350337 : Blo 876568 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B1483751 : Blo 876568 1483751 := bstep (se 1 (by rfl) ⟨1112813, by rfl⟩ : syracuseStep 1483751 = 2225627) B2225627
theorem B2958551 : Blo 876568 2958551 := bstep (se 1 (by rfl) ⟨2218913, by rfl⟩ : syracuseStep 2958551 = 4437827) B4437827
theorem B1320155 : Blo 876568 1320155 := bstep (se 1 (by rfl) ⟨990116, by rfl⟩ : syracuseStep 1320155 = 1980233) B1980233
theorem B6333673 : Blo 876568 6333673 := bstep (se 2 (by rfl) ⟨2375127, by rfl⟩ : syracuseStep 6333673 = 4750255) B4750255
theorem B1320329 : Blo 876568 1320329 := bstep (se 2 (by rfl) ⟨495123, by rfl⟩ : syracuseStep 1320329 = 990247) B990247
theorem B1975751 : Blo 876568 1975751 := bstep (se 1 (by rfl) ⟨1481813, by rfl⟩ : syracuseStep 1975751 = 2963627) B2963627
theorem B8431091 : Blo 876568 8431091 := bstep (se 1 (by rfl) ⟨6323318, by rfl⟩ : syracuseStep 8431091 = 12646637) B12646637
theorem B1320683 : Blo 876568 1320683 := bstep (se 1 (by rfl) ⟨990512, by rfl⟩ : syracuseStep 1320683 = 1981025) B1981025
theorem B1976111 : Blo 876568 1976111 := bstep (se 1 (by rfl) ⟨1482083, by rfl⟩ : syracuseStep 1976111 = 2964167) B2964167
theorem B1484905 : Blo 876568 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B3745921 : Blo 876568 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B1976687 : Blo 876568 1976687 := bstep (se 1 (by rfl) ⟨1482515, by rfl⟩ : syracuseStep 1976687 = 2965031) B2965031
theorem B6662573 : Blo 876568 6662573 := bstep (se 3 (by rfl) ⟨1249232, by rfl⟩ : syracuseStep 6662573 = 2498465) B2498465
theorem B1976759 : Blo 876568 1976759 := bstep (se 1 (by rfl) ⟨1482569, by rfl⟩ : syracuseStep 1976759 = 2965139) B2965139
theorem B1976903 : Blo 876568 1976903 := bstep (se 1 (by rfl) ⟨1482677, by rfl⟩ : syracuseStep 1976903 = 2965355) B2965355
theorem B1878599 : Blo 876568 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B1976939 : Blo 876568 1976939 := bstep (se 1 (by rfl) ⟨1482704, by rfl⟩ : syracuseStep 1976939 = 2965409) B2965409
theorem B9480827 : Blo 876568 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B6761083 : Blo 876568 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B42740405 : Blo 876568 42740405 := bstep (se 5 (by rfl) ⟨2003456, by rfl⟩ : syracuseStep 42740405 = 4006913) B4006913
theorem B1977335 : Blo 876568 1977335 := bstep (se 1 (by rfl) ⟨1483001, by rfl⟩ : syracuseStep 1977335 = 2966003) B2966003
theorem B8432707 : Blo 876568 8432707 := bstep (se 1 (by rfl) ⟨6324530, by rfl⟩ : syracuseStep 8432707 = 12649061) B12649061
theorem B6335603 : Blo 876568 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B2370683 : Blo 876568 2370683 := bstep (se 1 (by rfl) ⟨1778012, by rfl⟩ : syracuseStep 2370683 = 3556025) B3556025
theorem B2960603 : Blo 876568 2960603 := bstep (se 1 (by rfl) ⟨2220452, by rfl⟩ : syracuseStep 2960603 = 4440905) B4440905
theorem B1977695 : Blo 876568 1977695 := bstep (se 1 (by rfl) ⟨1483271, by rfl⟩ : syracuseStep 1977695 = 2966543) B2966543
theorem B4992353 : Blo 876568 4992353 := bstep (se 2 (by rfl) ⟨1872132, by rfl⟩ : syracuseStep 4992353 = 3744265) B3744265
theorem B2370977 : Blo 876568 2370977 := bstep (se 2 (by rfl) ⟨889116, by rfl⟩ : syracuseStep 2370977 = 1778233) B1778233
theorem B6336235 : Blo 876568 6336235 := bstep (se 1 (by rfl) ⟨4752176, by rfl⟩ : syracuseStep 6336235 = 9504353) B9504353
theorem B1978091 : Blo 876568 1978091 := bstep (se 1 (by rfl) ⟨1483568, by rfl⟩ : syracuseStep 1978091 = 2967137) B2967137
theorem B1879787 : Blo 876568 1879787 := bstep (se 1 (by rfl) ⟨1409840, by rfl⟩ : syracuseStep 1879787 = 2819681) B2819681
theorem B2502407 : Blo 876568 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B1978217 : Blo 876568 1978217 := bstep (se 2 (by rfl) ⟨741831, by rfl⟩ : syracuseStep 1978217 = 1483663) B1483663
theorem B2961467 : Blo 876568 2961467 := bstep (se 1 (by rfl) ⟨2221100, by rfl⟩ : syracuseStep 2961467 = 4442201) B4442201
theorem B2961737 : Blo 876568 2961737 := bstep (se 2 (by rfl) ⟨1110651, by rfl⟩ : syracuseStep 2961737 = 2221303) B2221303
theorem B1979063 : Blo 876568 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B1585847 : Blo 876568 1585847 := bstep (se 1 (by rfl) ⟨1189385, by rfl⟩ : syracuseStep 1585847 = 2378771) B2378771
theorem B8434475 : Blo 876568 8434475 := bstep (se 1 (by rfl) ⟨6325856, by rfl⟩ : syracuseStep 8434475 = 12651713) B12651713
theorem B6665003 : Blo 876568 6665003 := bstep (se 1 (by rfl) ⟨4998752, by rfl⟩ : syracuseStep 6665003 = 9997505) B9997505
theorem B5485391 : Blo 876568 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B1979279 : Blo 876568 1979279 := bstep (se 1 (by rfl) ⟨1484459, by rfl⟩ : syracuseStep 1979279 = 2968919) B2968919
theorem B1586395 : Blo 876568 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B5616935 : Blo 876568 5616935 := bstep (se 1 (by rfl) ⟨4212701, by rfl⟩ : syracuseStep 5616935 = 8425403) B8425403
theorem B4011403 : Blo 876568 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B7222765 : Blo 876568 7222765 := bstep (se 3 (by rfl) ⟨1354268, by rfl⟩ : syracuseStep 7222765 = 2708537) B2708537
theorem B1979999 : Blo 876568 1979999 := bstep (se 1 (by rfl) ⟨1484999, by rfl⟩ : syracuseStep 1979999 = 2969999) B2969999
theorem B1128043 : Blo 876568 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B18036371 : Blo 876568 18036371 := bstep (se 1 (by rfl) ⟨13527278, by rfl⟩ : syracuseStep 18036371 = 27054557) B27054557
theorem B1980215 : Blo 876568 1980215 := bstep (se 1 (by rfl) ⟨1485161, by rfl⟩ : syracuseStep 1980215 = 2970323) B2970323
theorem B22787993 : Blo 876568 22787993 := bstep (se 2 (by rfl) ⟨8545497, by rfl⟩ : syracuseStep 22787993 = 17090995) B17090995
theorem B3749921 : Blo 876568 3749921 := bstep (se 2 (by rfl) ⟨1406220, by rfl⟩ : syracuseStep 3749921 = 2812441) B2812441
theorem B1980521 : Blo 876568 1980521 := bstep (se 2 (by rfl) ⟨742695, by rfl⟩ : syracuseStep 1980521 = 1485391) B1485391
theorem B2111617 : Blo 876568 2111617 := bstep (se 2 (by rfl) ⟨791856, by rfl⟩ : syracuseStep 2111617 = 1583713) B1583713
theorem B4438151 : Blo 876568 4438151 := bstep (se 1 (by rfl) ⟨3328613, by rfl⟩ : syracuseStep 4438151 = 6657227) B6657227
theorem B16923005 : Blo 876568 16923005 := bstep (se 3 (by rfl) ⟨3173063, by rfl⟩ : syracuseStep 16923005 = 6346127) B6346127
theorem B2537911 : Blo 876568 2537911 := bstep (se 1 (by rfl) ⟨1903433, by rfl⟩ : syracuseStep 2537911 = 3806867) B3806867
theorem B2505289 : Blo 876568 2505289 := bstep (se 2 (by rfl) ⟨939483, by rfl⟩ : syracuseStep 2505289 = 1878967) B1878967
theorem B1981007 : Blo 876568 1981007 := bstep (se 1 (by rfl) ⟨1485755, by rfl⟩ : syracuseStep 1981007 = 2971511) B2971511
theorem B2505323 : Blo 876568 2505323 := bstep (se 1 (by rfl) ⟨1878992, by rfl⟩ : syracuseStep 2505323 = 3757985) B3757985
theorem B6666947 : Blo 876568 6666947 := bstep (se 1 (by rfl) ⟨5000210, by rfl⟩ : syracuseStep 6666947 = 10000421) B10000421
theorem B1981151 : Blo 876568 1981151 := bstep (se 1 (by rfl) ⟨1485863, by rfl⟩ : syracuseStep 1981151 = 2971727) B2971727
theorem B8436899 : Blo 876568 8436899 := bstep (se 1 (by rfl) ⟨6327674, by rfl⟩ : syracuseStep 8436899 = 12655349) B12655349
theorem B247053635 : Blo 876568 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B3161531 : Blo 876568 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B2964923 : Blo 876568 2964923 := bstep (se 1 (by rfl) ⟨2223692, by rfl⟩ : syracuseStep 2964923 = 4447385) B4447385
theorem B2473775 : Blo 876568 2473775 := bstep (se 1 (by rfl) ⟨1855331, by rfl⟩ : syracuseStep 2473775 = 3710663) B3710663
theorem B2506963 : Blo 876568 2506963 := bstep (se 1 (by rfl) ⟨1880222, by rfl⟩ : syracuseStep 2506963 = 3760445) B3760445
theorem B2376695 : Blo 876568 2376695 := bstep (se 1 (by rfl) ⟨1782521, by rfl⟩ : syracuseStep 2376695 = 3565043) B3565043
theorem B5621035 : Blo 876568 5621035 := bstep (se 1 (by rfl) ⟨4215776, by rfl⟩ : syracuseStep 5621035 = 8431553) B8431553
theorem B15418667 : Blo 876568 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B68437561 : Blo 876568 68437561 := bstep (se 2 (by rfl) ⟨25664085, by rfl⟩ : syracuseStep 68437561 = 51328171) B51328171
theorem B4442039 : Blo 876568 4442039 := bstep (se 1 (by rfl) ⟨3331529, by rfl⟩ : syracuseStep 4442039 = 6663059) B6663059
theorem B3164111 : Blo 876568 3164111 := bstep (se 1 (by rfl) ⟨2373083, by rfl⟩ : syracuseStep 3164111 = 4746167) B4746167
theorem B19023929 : Blo 876568 19023929 := bstep (se 2 (by rfl) ⟨7133973, by rfl⟩ : syracuseStep 19023929 = 14267947) B14267947
theorem B2115713 : Blo 876568 2115713 := bstep (se 2 (by rfl) ⟨793392, by rfl⟩ : syracuseStep 2115713 = 1586785) B1586785
theorem B8800435 : Blo 876568 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B6670835 : Blo 876568 6670835 := bstep (se 1 (by rfl) ⟨5003126, by rfl⟩ : syracuseStep 6670835 = 10006253) B10006253
theorem B4442687 : Blo 876568 4442687 := bstep (se 1 (by rfl) ⟨3332015, by rfl⟩ : syracuseStep 4442687 = 6664031) B6664031
theorem B3329495 : Blo 876568 3329495 := bstep (se 1 (by rfl) ⟨2497121, by rfl⟩ : syracuseStep 3329495 = 4994243) B4994243
theorem B2969081 : Blo 876568 2969081 := bstep (se 2 (by rfl) ⟨1113405, by rfl⟩ : syracuseStep 2969081 = 2226811) B2226811
theorem B2969351 : Blo 876568 2969351 := bstep (se 1 (by rfl) ⟨2227013, by rfl⟩ : syracuseStep 2969351 = 4454027) B4454027
theorem B937775 : Blo 876568 937775 := bstep (se 1 (by rfl) ⟨703331, by rfl⟩ : syracuseStep 937775 = 1406663) B1406663
theorem B2969405 : Blo 876568 2969405 := bstep (se 3 (by rfl) ⟨556763, by rfl⟩ : syracuseStep 2969405 = 1113527) B1113527
theorem B1003343 : Blo 876568 1003343 := bstep (se 1 (by rfl) ⟨752507, by rfl⟩ : syracuseStep 1003343 = 1505015) B1505015
theorem B4738945 : Blo 876568 4738945 := bstep (se 2 (by rfl) ⟨1777104, by rfl⟩ : syracuseStep 4738945 = 3554209) B3554209
theorem B4509755 : Blo 876568 4509755 := bstep (se 1 (by rfl) ⟨3382316, by rfl⟩ : syracuseStep 4509755 = 6764633) B6764633
theorem B30494825 : Blo 876568 30494825 := bstep (se 2 (by rfl) ⟨11435559, by rfl⟩ : syracuseStep 30494825 = 22871119) B22871119
theorem B7492115 : Blo 876568 7492115 := bstep (se 1 (by rfl) ⟨5619086, by rfl⟩ : syracuseStep 7492115 = 11238173) B11238173
theorem B5624417 : Blo 876568 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B4444793 : Blo 876568 4444793 := bstep (se 2 (by rfl) ⟨1666797, by rfl⟩ : syracuseStep 4444793 = 3333595) B3333595
theorem B938719 : Blo 876568 938719 := bstep (se 1 (by rfl) ⟨704039, by rfl⟩ : syracuseStep 938719 = 1408079) B1408079
theorem B4740221 : Blo 876568 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B30365027 : Blo 876568 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B2709179 : Blo 876568 2709179 := bstep (se 1 (by rfl) ⟨2031884, by rfl⟩ : syracuseStep 2709179 = 4063769) B4063769
theorem B939983 : Blo 876568 939983 := bstep (se 1 (by rfl) ⟨704987, by rfl⟩ : syracuseStep 939983 = 1409975) B1409975
theorem B3758345 : Blo 876568 3758345 := bstep (se 2 (by rfl) ⟨1409379, by rfl⟩ : syracuseStep 3758345 = 2818759) B2818759
theorem B4446575 : Blo 876568 4446575 := bstep (se 1 (by rfl) ⟨3334931, by rfl⟩ : syracuseStep 4446575 = 6669863) B6669863
theorem B16308769 : Blo 876568 16308769 := bstep (se 2 (by rfl) ⟨6115788, by rfl⟩ : syracuseStep 16308769 = 12231577) B12231577
theorem B12638915 : Blo 876568 12638915 := bstep (se 1 (by rfl) ⟨9479186, by rfl⟩ : syracuseStep 12638915 = 18958373) B18958373
theorem B2251487 : Blo 876568 2251487 := bstep (se 1 (by rfl) ⟨1688615, by rfl⟩ : syracuseStep 2251487 = 3377231) B3377231
theorem B9001847 : Blo 876568 9001847 := bstep (se 1 (by rfl) ⟨6751385, by rfl⟩ : syracuseStep 9001847 = 13502771) B13502771
theorem B2219147 : Blo 876568 2219147 := bstep (se 1 (by rfl) ⟨1664360, by rfl⟩ : syracuseStep 2219147 = 3328721) B3328721
theorem B2219359 : Blo 876568 2219359 := bstep (se 1 (by rfl) ⟨1664519, by rfl⟩ : syracuseStep 2219359 = 3329039) B3329039
theorem B3333899 : Blo 876568 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B3334355 : Blo 876568 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B876831 : Blo 876568 876831 := bstep (se 1 (by rfl) ⟨657623, by rfl⟩ : syracuseStep 876831 = 1315247) B1315247
theorem B876891 : Blo 876568 876891 := bstep (se 1 (by rfl) ⟨657668, by rfl⟩ : syracuseStep 876891 = 1315337) B1315337
theorem B876911 : Blo 876568 876911 := bstep (se 1 (by rfl) ⟨657683, by rfl⟩ : syracuseStep 876911 = 1315367) B1315367
theorem B86794649 : Blo 876568 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B876967 : Blo 876568 876967 := bstep (se 1 (by rfl) ⟨657725, by rfl⟩ : syracuseStep 876967 = 1315451) B1315451
theorem B877051 : Blo 876568 877051 := bstep (se 1 (by rfl) ⟨657788, by rfl⟩ : syracuseStep 877051 = 1315577) B1315577
theorem B877119 : Blo 876568 877119 := bstep (se 1 (by rfl) ⟨657839, by rfl⟩ : syracuseStep 877119 = 1315679) B1315679
theorem B877127 : Blo 876568 877127 := bstep (se 1 (by rfl) ⟨657845, by rfl⟩ : syracuseStep 877127 = 1315691) B1315691
theorem B877279 : Blo 876568 877279 := bstep (se 1 (by rfl) ⟨657959, by rfl⟩ : syracuseStep 877279 = 1315919) B1315919
theorem B2220767 : Blo 876568 2220767 := bstep (se 1 (by rfl) ⟨1665575, by rfl⟩ : syracuseStep 2220767 = 3331151) B3331151
theorem B877359 : Blo 876568 877359 := bstep (se 1 (by rfl) ⟨658019, by rfl⟩ : syracuseStep 877359 = 1316039) B1316039
theorem B877467 : Blo 876568 877467 := bstep (se 1 (by rfl) ⟨658100, by rfl⟩ : syracuseStep 877467 = 1316201) B1316201
theorem B877519 : Blo 876568 877519 := bstep (se 1 (by rfl) ⟨658139, by rfl⟩ : syracuseStep 877519 = 1316279) B1316279
theorem B877543 : Blo 876568 877543 := bstep (se 1 (by rfl) ⟨658157, by rfl⟩ : syracuseStep 877543 = 1316315) B1316315
theorem B4056263 : Blo 876568 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B877855 : Blo 876568 877855 := bstep (se 1 (by rfl) ⟨658391, by rfl⟩ : syracuseStep 877855 = 1316783) B1316783
theorem B877915 : Blo 876568 877915 := bstep (se 1 (by rfl) ⟨658436, by rfl⟩ : syracuseStep 877915 = 1316873) B1316873
theorem B877935 : Blo 876568 877935 := bstep (se 1 (by rfl) ⟨658451, by rfl⟩ : syracuseStep 877935 = 1316903) B1316903
theorem B877991 : Blo 876568 877991 := bstep (se 1 (by rfl) ⟨658493, by rfl⟩ : syracuseStep 877991 = 1316987) B1316987
theorem B878075 : Blo 876568 878075 := bstep (se 1 (by rfl) ⟨658556, by rfl⟩ : syracuseStep 878075 = 1317113) B1317113
theorem B878143 : Blo 876568 878143 := bstep (se 1 (by rfl) ⟨658607, by rfl⟩ : syracuseStep 878143 = 1317215) B1317215
theorem B878151 : Blo 876568 878151 := bstep (se 1 (by rfl) ⟨658613, by rfl⟩ : syracuseStep 878151 = 1317227) B1317227
theorem B4449977 : Blo 876568 4449977 := bstep (se 2 (by rfl) ⟨1668741, by rfl⟩ : syracuseStep 4449977 = 3337483) B3337483
theorem B13723337 : Blo 876568 13723337 := bstep (se 2 (by rfl) ⟨5146251, by rfl⟩ : syracuseStep 13723337 = 10292503) B10292503
theorem B878303 : Blo 876568 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B878383 : Blo 876568 878383 := bstep (se 1 (by rfl) ⟨658787, by rfl⟩ : syracuseStep 878383 = 1317575) B1317575
theorem B3565367 : Blo 876568 3565367 := bstep (se 1 (by rfl) ⟨2674025, by rfl⟩ : syracuseStep 3565367 = 5348051) B5348051
theorem B878491 : Blo 876568 878491 := bstep (se 1 (by rfl) ⟨658868, by rfl⟩ : syracuseStep 878491 = 1317737) B1317737
theorem B1664975 : Blo 876568 1664975 := bstep (se 1 (by rfl) ⟨1248731, by rfl⟩ : syracuseStep 1664975 = 2497463) B2497463
theorem B878543 : Blo 876568 878543 := bstep (se 1 (by rfl) ⟨658907, by rfl⟩ : syracuseStep 878543 = 1317815) B1317815
theorem B878567 : Blo 876568 878567 := bstep (se 1 (by rfl) ⟨658925, by rfl⟩ : syracuseStep 878567 = 1317851) B1317851
theorem B16017587 : Blo 876568 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B3565853 : Blo 876568 3565853 := bstep (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) B1337195
theorem B878879 : Blo 876568 878879 := bstep (se 1 (by rfl) ⟨659159, by rfl⟩ : syracuseStep 878879 = 1318319) B1318319
theorem B878939 : Blo 876568 878939 := bstep (se 1 (by rfl) ⟨659204, by rfl⟩ : syracuseStep 878939 = 1318409) B1318409
theorem B878959 : Blo 876568 878959 := bstep (se 1 (by rfl) ⟨659219, by rfl⟩ : syracuseStep 878959 = 1318439) B1318439
theorem B879015 : Blo 876568 879015 := bstep (se 1 (by rfl) ⟨659261, by rfl⟩ : syracuseStep 879015 = 1318523) B1318523
theorem B34236845 : Blo 876568 34236845 := bstep (se 3 (by rfl) ⟨6419408, by rfl⟩ : syracuseStep 34236845 = 12838817) B12838817
theorem B879099 : Blo 876568 879099 := bstep (se 1 (by rfl) ⟨659324, by rfl⟩ : syracuseStep 879099 = 1318649) B1318649
theorem B879167 : Blo 876568 879167 := bstep (se 1 (by rfl) ⟨659375, by rfl⟩ : syracuseStep 879167 = 1318751) B1318751
theorem B879175 : Blo 876568 879175 := bstep (se 1 (by rfl) ⟨659381, by rfl⟩ : syracuseStep 879175 = 1318763) B1318763
theorem B6777431 : Blo 876568 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B879327 : Blo 876568 879327 := bstep (se 1 (by rfl) ⟨659495, by rfl⟩ : syracuseStep 879327 = 1318991) B1318991
theorem B879407 : Blo 876568 879407 := bstep (se 1 (by rfl) ⟨659555, by rfl⟩ : syracuseStep 879407 = 1319111) B1319111
theorem B1665947 : Blo 876568 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B879515 : Blo 876568 879515 := bstep (se 1 (by rfl) ⟨659636, by rfl⟩ : syracuseStep 879515 = 1319273) B1319273
theorem B879567 : Blo 876568 879567 := bstep (se 1 (by rfl) ⟨659675, by rfl⟩ : syracuseStep 879567 = 1319351) B1319351
theorem B879591 : Blo 876568 879591 := bstep (se 1 (by rfl) ⟨659693, by rfl⟩ : syracuseStep 879591 = 1319387) B1319387
theorem B2223227 : Blo 876568 2223227 := bstep (se 1 (by rfl) ⟨1667420, by rfl⟩ : syracuseStep 2223227 = 3334841) B3334841
theorem B2223247 : Blo 876568 2223247 := bstep (se 1 (by rfl) ⟨1667435, by rfl⟩ : syracuseStep 2223247 = 3334871) B3334871
theorem B3009755 : Blo 876568 3009755 := bstep (se 1 (by rfl) ⟨2257316, by rfl⟩ : syracuseStep 3009755 = 4514633) B4514633
theorem B879903 : Blo 876568 879903 := bstep (se 1 (by rfl) ⟨659927, by rfl⟩ : syracuseStep 879903 = 1319855) B1319855
theorem B879963 : Blo 876568 879963 := bstep (se 1 (by rfl) ⟨659972, by rfl⟩ : syracuseStep 879963 = 1319945) B1319945
theorem B879983 : Blo 876568 879983 := bstep (se 1 (by rfl) ⟨659987, by rfl⟩ : syracuseStep 879983 = 1319975) B1319975
theorem B2223521 : Blo 876568 2223521 := bstep (se 2 (by rfl) ⟨833820, by rfl⟩ : syracuseStep 2223521 = 1667641) B1667641
theorem B880039 : Blo 876568 880039 := bstep (se 1 (by rfl) ⟨660029, by rfl⟩ : syracuseStep 880039 = 1320059) B1320059
theorem B880123 : Blo 876568 880123 := bstep (se 1 (by rfl) ⟨660092, by rfl⟩ : syracuseStep 880123 = 1320185) B1320185
theorem B880191 : Blo 876568 880191 := bstep (se 1 (by rfl) ⟨660143, by rfl⟩ : syracuseStep 880191 = 1320287) B1320287
theorem B880199 : Blo 876568 880199 := bstep (se 1 (by rfl) ⟨660149, by rfl⟩ : syracuseStep 880199 = 1320299) B1320299
theorem B4451921 : Blo 876568 4451921 := bstep (se 2 (by rfl) ⟨1669470, by rfl⟩ : syracuseStep 4451921 = 3338941) B3338941
theorem B880351 : Blo 876568 880351 := bstep (se 1 (by rfl) ⟨660263, by rfl⟩ : syracuseStep 880351 = 1320527) B1320527
theorem B880431 : Blo 876568 880431 := bstep (se 1 (by rfl) ⟨660323, by rfl⟩ : syracuseStep 880431 = 1320647) B1320647
theorem B880539 : Blo 876568 880539 := bstep (se 1 (by rfl) ⟨660404, by rfl⟩ : syracuseStep 880539 = 1320809) B1320809
theorem B3010907 : Blo 876568 3010907 := bstep (se 1 (by rfl) ⟨2258180, by rfl⟩ : syracuseStep 3010907 = 4516361) B4516361
theorem B1110439 : Blo 876568 1110439 := bstep (se 1 (by rfl) ⟨832829, by rfl⟩ : syracuseStep 1110439 = 1665659) B1665659
theorem B1110763 : Blo 876568 1110763 := bstep (se 1 (by rfl) ⟨833072, by rfl⟩ : syracuseStep 1110763 = 1666145) B1666145
theorem B1110991 : Blo 876568 1110991 := bstep (se 1 (by rfl) ⟨833243, by rfl⟩ : syracuseStep 1110991 = 1666487) B1666487
theorem B2225191 : Blo 876568 2225191 := bstep (se 1 (by rfl) ⟨1668893, by rfl⟩ : syracuseStep 2225191 = 3337787) B3337787
theorem B8451161 : Blo 876568 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B15201427 : Blo 876568 15201427 := bstep (se 1 (by rfl) ⟨11401070, by rfl⟩ : syracuseStep 15201427 = 22802141) B22802141
theorem B1111259 : Blo 876568 1111259 := bstep (se 1 (by rfl) ⟨833444, by rfl⟩ : syracuseStep 1111259 = 1666889) B1666889
theorem B2225657 : Blo 876568 2225657 := bstep (se 2 (by rfl) ⟨834621, by rfl⟩ : syracuseStep 2225657 = 1669243) B1669243
theorem B1111735 : Blo 876568 1111735 := bstep (se 1 (by rfl) ⟨833801, by rfl⟩ : syracuseStep 1111735 = 1667603) B1667603
theorem B1111963 : Blo 876568 1111963 := bstep (se 1 (by rfl) ⟨833972, by rfl⟩ : syracuseStep 1111963 = 1667945) B1667945
theorem B4454351 : Blo 876568 4454351 := bstep (se 1 (by rfl) ⟨3340763, by rfl⟩ : syracuseStep 4454351 = 6681527) B6681527
theorem B2226305 : Blo 876568 2226305 := bstep (se 2 (by rfl) ⟨834864, by rfl⟩ : syracuseStep 2226305 = 1669729) B1669729
theorem B10025207 : Blo 876568 10025207 := bstep (se 1 (by rfl) ⟨7518905, by rfl⟩ : syracuseStep 10025207 = 15037811) B15037811
theorem B2226599 : Blo 876568 2226599 := bstep (se 1 (by rfl) ⟨1669949, by rfl⟩ : syracuseStep 2226599 = 3339899) B3339899
theorem B2226761 : Blo 876568 2226761 := bstep (se 2 (by rfl) ⟨835035, by rfl⟩ : syracuseStep 2226761 = 1670071) B1670071
theorem B4750103 : Blo 876568 4750103 := bstep (se 1 (by rfl) ⟨3562577, by rfl⟩ : syracuseStep 4750103 = 7125155) B7125155
theorem B1112879 : Blo 876568 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B4455323 : Blo 876568 4455323 := bstep (se 1 (by rfl) ⟨3341492, by rfl⟩ : syracuseStep 4455323 = 6682985) B6682985
theorem B2227115 : Blo 876568 2227115 := bstep (se 1 (by rfl) ⟨1670336, by rfl⟩ : syracuseStep 2227115 = 3340673) B3340673
theorem B7502777 : Blo 876568 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B2227297 : Blo 876568 2227297 := bstep (se 2 (by rfl) ⟨835236, by rfl⟩ : syracuseStep 2227297 = 1670473) B1670473
theorem B16252093 : Blo 876568 16252093 := bstep (se 3 (by rfl) ⟨3047267, by rfl⟩ : syracuseStep 16252093 = 6094535) B6094535
theorem B4455809 : Blo 876568 4455809 := bstep (se 2 (by rfl) ⟨1670928, by rfl⟩ : syracuseStep 4455809 = 3341857) B3341857
theorem B1670959 : Blo 876568 1670959 := bstep (se 1 (by rfl) ⟨1253219, by rfl⟩ : syracuseStep 1670959 = 2506439) B2506439
theorem B21364553 : Blo 876568 21364553 := bstep (se 2 (by rfl) ⟨8011707, by rfl⟩ : syracuseStep 21364553 = 16023415) B16023415
theorem B3342617 : Blo 876568 3342617 := bstep (se 2 (by rfl) ⟨1253481, by rfl⟩ : syracuseStep 3342617 = 2506963) B2506963
theorem B3343315 : Blo 876568 3343315 := bstep (se 1 (by rfl) ⟨2507486, by rfl⟩ : syracuseStep 3343315 = 5014973) B5014973
theorem B12682619 : Blo 876568 12682619 := bstep (se 1 (by rfl) ⟨9511964, by rfl⟩ : syracuseStep 12682619 = 19023929) B19023929
theorem B1410475 : Blo 876568 1410475 := bstep (se 1 (by rfl) ⟨1057856, by rfl⟩ : syracuseStep 1410475 = 2115713) B2115713
theorem B13535525 : Blo 876568 13535525 := bstep (se 4 (by rfl) ⟨1268955, by rfl⟩ : syracuseStep 13535525 = 2537911) B2537911
theorem B1902943 : Blo 876568 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B11733913 : Blo 876568 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B1248743 : Blo 876568 1248743 := bstep (se 1 (by rfl) ⟨936557, by rfl⟩ : syracuseStep 1248743 = 1873115) B1873115
theorem B9014777 : Blo 876568 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B1806119 : Blo 876568 1806119 := bstep (se 1 (by rfl) ⟨1354589, by rfl⟩ : syracuseStep 1806119 = 2709179) B2709179
theorem B11243609 : Blo 876568 11243609 := bstep (se 2 (by rfl) ⟨4216353, by rfl⟩ : syracuseStep 11243609 = 8432707) B8432707
theorem B987367 : Blo 876568 987367 := bstep (se 1 (by rfl) ⟨740525, by rfl⟩ : syracuseStep 987367 = 1481051) B1481051
theorem B1315103 : Blo 876568 1315103 := bstep (se 1 (by rfl) ⟨986327, by rfl⟩ : syracuseStep 1315103 = 1972655) B1972655
theorem B1315127 : Blo 876568 1315127 := bstep (se 1 (by rfl) ⟨986345, by rfl⟩ : syracuseStep 1315127 = 1972691) B1972691
theorem B1315199 : Blo 876568 1315199 := bstep (se 1 (by rfl) ⟨986399, by rfl⟩ : syracuseStep 1315199 = 1972799) B1972799
theorem B1315271 : Blo 876568 1315271 := bstep (se 1 (by rfl) ⟨986453, by rfl⟩ : syracuseStep 1315271 = 1972907) B1972907
theorem B8425943 : Blo 876568 8425943 := bstep (se 1 (by rfl) ⟨6319457, by rfl⟩ : syracuseStep 8425943 = 12638915) B12638915
theorem B6001231 : Blo 876568 6001231 := bstep (se 1 (by rfl) ⟨4500923, by rfl⟩ : syracuseStep 6001231 = 9001847) B9001847
theorem B1479431 : Blo 876568 1479431 := bstep (se 1 (by rfl) ⟨1109573, by rfl⟩ : syracuseStep 1479431 = 2219147) B2219147
theorem B1315625 : Blo 876568 1315625 := bstep (se 2 (by rfl) ⟨493359, by rfl⟩ : syracuseStep 1315625 = 986719) B986719
theorem B1315631 : Blo 876568 1315631 := bstep (se 1 (by rfl) ⟨986723, by rfl⟩ : syracuseStep 1315631 = 1973447) B1973447
theorem B988015 : Blo 876568 988015 := bstep (se 1 (by rfl) ⟨741011, by rfl⟩ : syracuseStep 988015 = 1482023) B1482023
theorem B1315751 : Blo 876568 1315751 := bstep (se 1 (by rfl) ⟨986813, by rfl⟩ : syracuseStep 1315751 = 1973627) B1973627
theorem B9507779 : Blo 876568 9507779 := bstep (se 1 (by rfl) ⟨7130834, by rfl⟩ : syracuseStep 9507779 = 14261669) B14261669
theorem B1315835 : Blo 876568 1315835 := bstep (se 1 (by rfl) ⟨986876, by rfl⟩ : syracuseStep 1315835 = 1973753) B1973753
theorem B1315895 : Blo 876568 1315895 := bstep (se 1 (by rfl) ⟨986921, by rfl⟩ : syracuseStep 1315895 = 1973843) B1973843
theorem B1316015 : Blo 876568 1316015 := bstep (se 1 (by rfl) ⟨987011, by rfl⟩ : syracuseStep 1316015 = 1974023) B1974023
theorem B1316423 : Blo 876568 1316423 := bstep (se 1 (by rfl) ⟨987317, by rfl⟩ : syracuseStep 1316423 = 1974635) B1974635
theorem B1316519 : Blo 876568 1316519 := bstep (se 1 (by rfl) ⟨987389, by rfl⟩ : syracuseStep 1316519 = 1974779) B1974779
theorem B1054459 : Blo 876568 1054459 := bstep (se 1 (by rfl) ⟨790844, by rfl⟩ : syracuseStep 1054459 = 1581689) B1581689
theorem B1316603 : Blo 876568 1316603 := bstep (se 1 (by rfl) ⟨987452, by rfl⟩ : syracuseStep 1316603 = 1974905) B1974905
theorem B1251067 : Blo 876568 1251067 := bstep (se 1 (by rfl) ⟨938300, by rfl⟩ : syracuseStep 1251067 = 1876601) B1876601
theorem B1316639 : Blo 876568 1316639 := bstep (se 1 (by rfl) ⟨987479, by rfl⟩ : syracuseStep 1316639 = 1974959) B1974959
theorem B1480511 : Blo 876568 1480511 := bstep (se 1 (by rfl) ⟨1110383, by rfl⟩ : syracuseStep 1480511 = 2220767) B2220767
theorem B1316687 : Blo 876568 1316687 := bstep (se 1 (by rfl) ⟨987515, by rfl⟩ : syracuseStep 1316687 = 1975031) B1975031
theorem B1480585 : Blo 876568 1480585 := bstep (se 2 (by rfl) ⟨555219, by rfl⟩ : syracuseStep 1480585 = 1110439) B1110439
theorem B1316807 : Blo 876568 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B989167 : Blo 876568 989167 := bstep (se 1 (by rfl) ⟨741875, by rfl⟩ : syracuseStep 989167 = 1483751) B1483751
theorem B1972367 : Blo 876568 1972367 := bstep (se 1 (by rfl) ⟨1479275, by rfl⟩ : syracuseStep 1972367 = 2958551) B2958551
theorem B1972385 : Blo 876568 1972385 := bstep (se 2 (by rfl) ⟨739644, by rfl⟩ : syracuseStep 1972385 = 1479289) B1479289
theorem B1972457 : Blo 876568 1972457 := bstep (se 2 (by rfl) ⟨739671, by rfl⟩ : syracuseStep 1972457 = 1479343) B1479343
theorem B1317161 : Blo 876568 1317161 := bstep (se 2 (by rfl) ⟨493935, by rfl⟩ : syracuseStep 1317161 = 987871) B987871
theorem B1251625 : Blo 876568 1251625 := bstep (se 2 (by rfl) ⟨469359, by rfl⟩ : syracuseStep 1251625 = 938719) B938719
theorem B1317167 : Blo 876568 1317167 := bstep (se 1 (by rfl) ⟨987875, by rfl⟩ : syracuseStep 1317167 = 1975751) B1975751
theorem B1481017 : Blo 876568 1481017 := bstep (se 2 (by rfl) ⟨555381, by rfl⟩ : syracuseStep 1481017 = 1110763) B1110763
theorem B9148891 : Blo 876568 9148891 := bstep (se 1 (by rfl) ⟨6861668, by rfl⟩ : syracuseStep 9148891 = 13723337) B13723337
theorem B8460773 : Blo 876568 8460773 := bstep (se 4 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 8460773 = 1586395) B1586395
theorem B1317407 : Blo 876568 1317407 := bstep (se 1 (by rfl) ⟨988055, by rfl⟩ : syracuseStep 1317407 = 1976111) B1976111
theorem B1481321 : Blo 876568 1481321 := bstep (se 2 (by rfl) ⟨555495, by rfl⟩ : syracuseStep 1481321 = 1110991) B1110991
theorem B51452533 : Blo 876568 51452533 := bstep (se 5 (by rfl) ⟨2411837, by rfl⟩ : syracuseStep 51452533 = 4823675) B4823675
theorem B1317791 : Blo 876568 1317791 := bstep (se 1 (by rfl) ⟨988343, by rfl⟩ : syracuseStep 1317791 = 1976687) B1976687
theorem B1317839 : Blo 876568 1317839 := bstep (se 1 (by rfl) ⟨988379, by rfl⟩ : syracuseStep 1317839 = 1976759) B1976759
theorem B1317929 : Blo 876568 1317929 := bstep (se 2 (by rfl) ⟨494223, by rfl⟩ : syracuseStep 1317929 = 988447) B988447
theorem B1317935 : Blo 876568 1317935 := bstep (se 1 (by rfl) ⟨988451, by rfl⟩ : syracuseStep 1317935 = 1976903) B1976903
theorem B1317959 : Blo 876568 1317959 := bstep (se 1 (by rfl) ⟨988469, by rfl⟩ : syracuseStep 1317959 = 1976939) B1976939
theorem B1580153 : Blo 876568 1580153 := bstep (se 2 (by rfl) ⟨592557, by rfl⟩ : syracuseStep 1580153 = 1185115) B1185115
theorem B5348537 : Blo 876568 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B6003965 : Blo 876568 6003965 := bstep (se 3 (by rfl) ⟨1125743, by rfl⟩ : syracuseStep 6003965 = 2251487) B2251487
theorem B1318223 : Blo 876568 1318223 := bstep (se 1 (by rfl) ⟨988667, by rfl⟩ : syracuseStep 1318223 = 1977335) B1977335
theorem B1580455 : Blo 876568 1580455 := bstep (se 1 (by rfl) ⟨1185341, by rfl⟩ : syracuseStep 1580455 = 2370683) B2370683
theorem B1482151 : Blo 876568 1482151 := bstep (se 1 (by rfl) ⟨1111613, by rfl⟩ : syracuseStep 1482151 = 2223227) B2223227
theorem B1318313 : Blo 876568 1318313 := bstep (se 2 (by rfl) ⟨494367, by rfl⟩ : syracuseStep 1318313 = 988735) B988735
theorem B1973735 : Blo 876568 1973735 := bstep (se 1 (by rfl) ⟨1480301, by rfl⟩ : syracuseStep 1973735 = 2960603) B2960603
theorem B1318463 : Blo 876568 1318463 := bstep (se 1 (by rfl) ⟨988847, by rfl⟩ : syracuseStep 1318463 = 1977695) B1977695
theorem B1482313 : Blo 876568 1482313 := bstep (se 2 (by rfl) ⟨555867, by rfl⟩ : syracuseStep 1482313 = 1111735) B1111735
theorem B1580651 : Blo 876568 1580651 := bstep (se 1 (by rfl) ⟨1185488, by rfl⟩ : syracuseStep 1580651 = 2370977) B2370977
theorem B1482347 : Blo 876568 1482347 := bstep (se 1 (by rfl) ⟨1111760, by rfl⟩ : syracuseStep 1482347 = 2223521) B2223521
theorem B2498273 : Blo 876568 2498273 := bstep (se 2 (by rfl) ⟨936852, by rfl⟩ : syracuseStep 2498273 = 1873705) B1873705
theorem B1318727 : Blo 876568 1318727 := bstep (se 1 (by rfl) ⟨989045, by rfl⟩ : syracuseStep 1318727 = 1978091) B1978091
theorem B1482617 : Blo 876568 1482617 := bstep (se 2 (by rfl) ⟨555981, by rfl⟩ : syracuseStep 1482617 = 1111963) B1111963
theorem B1318811 : Blo 876568 1318811 := bstep (se 1 (by rfl) ⟨989108, by rfl⟩ : syracuseStep 1318811 = 1978217) B1978217
theorem B1974311 : Blo 876568 1974311 := bstep (se 1 (by rfl) ⟨1480733, by rfl⟩ : syracuseStep 1974311 = 2961467) B2961467
theorem B1974491 : Blo 876568 1974491 := bstep (se 1 (by rfl) ⟨1480868, by rfl⟩ : syracuseStep 1974491 = 2961737) B2961737
theorem B2007271 : Blo 876568 2007271 := bstep (se 1 (by rfl) ⟨1505453, by rfl⟩ : syracuseStep 2007271 = 3010907) B3010907
theorem B1319375 : Blo 876568 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B1057231 : Blo 876568 1057231 := bstep (se 1 (by rfl) ⟨792923, by rfl⟩ : syracuseStep 1057231 = 1585847) B1585847
theorem B1974761 : Blo 876568 1974761 := bstep (se 2 (by rfl) ⟨740535, by rfl⟩ : syracuseStep 1974761 = 1481071) B1481071
theorem B1319417 : Blo 876568 1319417 := bstep (se 2 (by rfl) ⟨494781, by rfl⟩ : syracuseStep 1319417 = 989563) B989563
theorem B1319519 : Blo 876568 1319519 := bstep (se 1 (by rfl) ⟨989639, by rfl⟩ : syracuseStep 1319519 = 1979279) B1979279
theorem B1975049 : Blo 876568 1975049 := bstep (se 2 (by rfl) ⟨740643, by rfl⟩ : syracuseStep 1975049 = 1481287) B1481287
theorem B3744623 : Blo 876568 3744623 := bstep (se 1 (by rfl) ⟨2808467, by rfl⟩ : syracuseStep 3744623 = 5616935) B5616935
theorem B1483771 : Blo 876568 1483771 := bstep (se 1 (by rfl) ⟨1112828, by rfl⟩ : syracuseStep 1483771 = 2225657) B2225657
theorem B1319999 : Blo 876568 1319999 := bstep (se 1 (by rfl) ⟨989999, by rfl⟩ : syracuseStep 1319999 = 1979999) B1979999
theorem B1320041 : Blo 876568 1320041 := bstep (se 2 (by rfl) ⟨495015, by rfl⟩ : syracuseStep 1320041 = 990031) B990031
theorem B8430749 : Blo 876568 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B1320143 : Blo 876568 1320143 := bstep (se 1 (by rfl) ⟨990107, by rfl⟩ : syracuseStep 1320143 = 1980215) B1980215
theorem B1975625 : Blo 876568 1975625 := bstep (se 2 (by rfl) ⟨740859, by rfl⟩ : syracuseStep 1975625 = 1481719) B1481719
theorem B2499947 : Blo 876568 2499947 := bstep (se 1 (by rfl) ⟨1874960, by rfl⟩ : syracuseStep 2499947 = 3749921) B3749921
theorem B1320347 : Blo 876568 1320347 := bstep (se 1 (by rfl) ⟨990260, by rfl⟩ : syracuseStep 1320347 = 1980521) B1980521
theorem B1484203 : Blo 876568 1484203 := bstep (se 1 (by rfl) ⟨1113152, by rfl⟩ : syracuseStep 1484203 = 2226305) B2226305
theorem B2958767 : Blo 876568 2958767 := bstep (se 1 (by rfl) ⟨2219075, by rfl⟩ : syracuseStep 2958767 = 4438151) B4438151
theorem B21669457 : Blo 876568 21669457 := bstep (se 2 (by rfl) ⟨8126046, by rfl⟩ : syracuseStep 21669457 = 16252093) B16252093
theorem B11282003 : Blo 876568 11282003 := bstep (se 1 (by rfl) ⟨8461502, by rfl⟩ : syracuseStep 11282003 = 16923005) B16923005
theorem B1484399 : Blo 876568 1484399 := bstep (se 1 (by rfl) ⟨1113299, by rfl⟩ : syracuseStep 1484399 = 2226599) B2226599
theorem B1320569 : Blo 876568 1320569 := bstep (se 2 (by rfl) ⟨495213, by rfl⟩ : syracuseStep 1320569 = 990427) B990427
theorem B1484507 : Blo 876568 1484507 := bstep (se 1 (by rfl) ⟨1113380, by rfl⟩ : syracuseStep 1484507 = 2226761) B2226761
theorem B1320671 : Blo 876568 1320671 := bstep (se 1 (by rfl) ⟨990503, by rfl⟩ : syracuseStep 1320671 = 1981007) B1981007
theorem B2959145 : Blo 876568 2959145 := bstep (se 2 (by rfl) ⟨1109679, by rfl⟩ : syracuseStep 2959145 = 2219359) B2219359
theorem B1320767 : Blo 876568 1320767 := bstep (se 1 (by rfl) ⟨990575, by rfl⟩ : syracuseStep 1320767 = 1981151) B1981151
theorem B1484743 : Blo 876568 1484743 := bstep (se 1 (by rfl) ⟨1113557, by rfl⟩ : syracuseStep 1484743 = 2227115) B2227115
theorem B2500733 : Blo 876568 2500733 := bstep (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) B937775
theorem B164702423 : Blo 876568 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B1976615 : Blo 876568 1976615 := bstep (se 1 (by rfl) ⟨1482461, by rfl⟩ : syracuseStep 1976615 = 2964923) B2964923
theorem B1976633 : Blo 876568 1976633 := bstep (se 2 (by rfl) ⟨741237, by rfl⟩ : syracuseStep 1976633 = 1482475) B1482475
theorem B1649183 : Blo 876568 1649183 := bstep (se 1 (by rfl) ⟨1236887, by rfl⟩ : syracuseStep 1649183 = 2473775) B2473775
theorem B1485499 : Blo 876568 1485499 := bstep (se 1 (by rfl) ⟨1114124, by rfl⟩ : syracuseStep 1485499 = 2228249) B2228249
theorem B1485803 : Blo 876568 1485803 := bstep (se 1 (by rfl) ⟨1114352, by rfl⟩ : syracuseStep 1485803 = 2228705) B2228705
theorem B1584463 : Blo 876568 1584463 := bstep (se 1 (by rfl) ⟨1188347, by rfl⟩ : syracuseStep 1584463 = 2376695) B2376695
theorem B1977929 : Blo 876568 1977929 := bstep (se 2 (by rfl) ⟨741723, by rfl⟩ : syracuseStep 1977929 = 1483447) B1483447
theorem B1879625 : Blo 876568 1879625 := bstep (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) B1409719
theorem B2502521 : Blo 876568 2502521 := bstep (se 2 (by rfl) ⟨938445, by rfl⟩ : syracuseStep 2502521 = 1876891) B1876891
theorem B2961359 : Blo 876568 2961359 := bstep (se 1 (by rfl) ⟨2221019, by rfl⟩ : syracuseStep 2961359 = 4442039) B4442039
theorem B2109407 : Blo 876568 2109407 := bstep (se 1 (by rfl) ⟨1582055, by rfl⟩ : syracuseStep 2109407 = 3164111) B3164111
theorem B2961791 : Blo 876568 2961791 := bstep (se 1 (by rfl) ⟨2221343, by rfl⟩ : syracuseStep 2961791 = 4442687) B4442687
theorem B8434439 : Blo 876568 8434439 := bstep (se 1 (by rfl) ⟨6325829, by rfl⟩ : syracuseStep 8434439 = 12651659) B12651659
theorem B7516961 : Blo 876568 7516961 := bstep (se 2 (by rfl) ⟨2818860, by rfl⟩ : syracuseStep 7516961 = 5637721) B5637721
theorem B1979387 : Blo 876568 1979387 := bstep (se 1 (by rfl) ⟨1484540, by rfl⟩ : syracuseStep 1979387 = 2969081) B2969081
theorem B1979567 : Blo 876568 1979567 := bstep (se 1 (by rfl) ⟨1484675, by rfl⟩ : syracuseStep 1979567 = 2969351) B2969351
theorem B1979603 : Blo 876568 1979603 := bstep (se 1 (by rfl) ⟨1484702, by rfl⟩ : syracuseStep 1979603 = 2969405) B2969405
theorem B2536795 : Blo 876568 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B20329883 : Blo 876568 20329883 := bstep (se 1 (by rfl) ⟨15247412, by rfl⟩ : syracuseStep 20329883 = 30494825) B30494825
theorem B1979873 : Blo 876568 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B4994561 : Blo 876568 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B4994743 : Blo 876568 4994743 := bstep (se 1 (by rfl) ⟨3746057, by rfl⟩ : syracuseStep 4994743 = 7492115) B7492115
theorem B2963195 : Blo 876568 2963195 := bstep (se 1 (by rfl) ⟨2222396, by rfl⟩ : syracuseStep 2963195 = 4444793) B4444793
theorem B2963357 : Blo 876568 2963357 := bstep (se 3 (by rfl) ⟨555629, by rfl⟩ : syracuseStep 2963357 = 1111259) B1111259
theorem B3160147 : Blo 876568 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B5617835 : Blo 876568 5617835 := bstep (se 1 (by rfl) ⟨4213376, by rfl⟩ : syracuseStep 5617835 = 8426753) B8426753
theorem B14989697 : Blo 876568 14989697 := bstep (se 2 (by rfl) ⟨5621136, by rfl⟩ : syracuseStep 14989697 = 11242273) B11242273
theorem B2505563 : Blo 876568 2505563 := bstep (se 1 (by rfl) ⟨1879172, by rfl⟩ : syracuseStep 2505563 = 3758345) B3758345
theorem B2964329 : Blo 876568 2964329 := bstep (se 2 (by rfl) ⟨1111623, by rfl⟩ : syracuseStep 2964329 = 2223247) B2223247
theorem B2964383 : Blo 876568 2964383 := bstep (se 1 (by rfl) ⟨2223287, by rfl⟩ : syracuseStep 2964383 = 4446575) B4446575
theorem B3849257 : Blo 876568 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B6667919 : Blo 876568 6667919 := bstep (se 1 (by rfl) ⟨5000939, by rfl⟩ : syracuseStep 6667919 = 10001879) B10001879
theorem B60767981 : Blo 876568 60767981 := bstep (se 3 (by rfl) ⟨11393996, by rfl⟩ : syracuseStep 60767981 = 22787993) B22787993
theorem B4439933 : Blo 876568 4439933 := bstep (se 3 (by rfl) ⟨832487, by rfl⟩ : syracuseStep 4439933 = 1664975) B1664975
theorem B2506621 : Blo 876568 2506621 := bstep (se 3 (by rfl) ⟨469991, by rfl⟩ : syracuseStep 2506621 = 939983) B939983
theorem B2704175 : Blo 876568 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B5620727 : Blo 876568 5620727 := bstep (se 1 (by rfl) ⟨4215545, by rfl⟩ : syracuseStep 5620727 = 8431091) B8431091
theorem B2966651 : Blo 876568 2966651 := bstep (se 1 (by rfl) ⟨2224988, by rfl⟩ : syracuseStep 2966651 = 4449977) B4449977
theorem B2376911 : Blo 876568 2376911 := bstep (se 1 (by rfl) ⟨1782683, by rfl⟩ : syracuseStep 2376911 = 3565367) B3565367
theorem B2966921 : Blo 876568 2966921 := bstep (se 2 (by rfl) ⟨1112595, by rfl⟩ : syracuseStep 2966921 = 2225191) B2225191
theorem B2377235 : Blo 876568 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B20268569 : Blo 876568 20268569 := bstep (se 2 (by rfl) ⟨7600713, by rfl⟩ : syracuseStep 20268569 = 15201427) B15201427
theorem B4441715 : Blo 876568 4441715 := bstep (se 1 (by rfl) ⟨3331286, by rfl⟩ : syracuseStep 4441715 = 6662573) B6662573
theorem B22824563 : Blo 876568 22824563 := bstep (se 1 (by rfl) ⟨17118422, by rfl⟩ : syracuseStep 22824563 = 34236845) B34236845
theorem B28493603 : Blo 876568 28493603 := bstep (se 1 (by rfl) ⟨21370202, by rfl⟩ : syracuseStep 28493603 = 42740405) B42740405
theorem B21678137 : Blo 876568 21678137 := bstep (se 2 (by rfl) ⟨8129301, by rfl⟩ : syracuseStep 21678137 = 16258603) B16258603
theorem B2967677 : Blo 876568 2967677 := bstep (se 3 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 2967677 = 1112879) B1112879
theorem B3328235 : Blo 876568 3328235 := bstep (se 1 (by rfl) ⟨2496176, by rfl⟩ : syracuseStep 3328235 = 4992353) B4992353
theorem B3328249 : Blo 876568 3328249 := bstep (se 2 (by rfl) ⟨1248093, by rfl⟩ : syracuseStep 3328249 = 2496187) B2496187
theorem B2967947 : Blo 876568 2967947 := bstep (se 1 (by rfl) ⟨2225960, by rfl⟩ : syracuseStep 2967947 = 4451921) B4451921
theorem B4442525 : Blo 876568 4442525 := bstep (se 3 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 4442525 = 1665947) B1665947
theorem B5622983 : Blo 876568 5622983 := bstep (se 1 (by rfl) ⟨4217237, by rfl⟩ : syracuseStep 5622983 = 8434475) B8434475
theorem B4443335 : Blo 876568 4443335 := bstep (se 1 (by rfl) ⟨3332501, by rfl⟩ : syracuseStep 4443335 = 6665003) B6665003
theorem B3656927 : Blo 876568 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B21745025 : Blo 876568 21745025 := bstep (se 2 (by rfl) ⟨8154384, by rfl⟩ : syracuseStep 21745025 = 16308769) B16308769
theorem B3329693 : Blo 876568 3329693 := bstep (se 3 (by rfl) ⟨624317, by rfl⟩ : syracuseStep 3329693 = 1248635) B1248635
theorem B2969567 : Blo 876568 2969567 := bstep (se 1 (by rfl) ⟨2227175, by rfl⟩ : syracuseStep 2969567 = 4454351) B4454351
theorem B2969729 : Blo 876568 2969729 := bstep (se 2 (by rfl) ⟨1113648, by rfl⟩ : syracuseStep 2969729 = 2227297) B2227297
theorem B4444631 : Blo 876568 4444631 := bstep (se 1 (by rfl) ⟨3333473, by rfl⟩ : syracuseStep 4444631 = 6666947) B6666947
theorem B3166735 : Blo 876568 3166735 := bstep (se 1 (by rfl) ⟨2375051, by rfl⟩ : syracuseStep 3166735 = 4750103) B4750103
theorem B2970215 : Blo 876568 2970215 := bstep (se 1 (by rfl) ⟨2227661, by rfl⟩ : syracuseStep 2970215 = 4455323) B4455323
theorem B5001851 : Blo 876568 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B5624599 : Blo 876568 5624599 := bstep (se 1 (by rfl) ⟨4218449, by rfl⟩ : syracuseStep 5624599 = 8436899) B8436899
theorem B2675581 : Blo 876568 2675581 := bstep (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) B1003343
theorem B2970539 : Blo 876568 2970539 := bstep (se 1 (by rfl) ⟨2227904, by rfl⟩ : syracuseStep 2970539 = 4455809) B4455809
theorem B6345809 : Blo 876568 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B14243035 : Blo 876568 14243035 := bstep (se 1 (by rfl) ⟨10682276, by rfl⟩ : syracuseStep 14243035 = 21364553) B21364553
theorem B3757403 : Blo 876568 3757403 := bstep (se 1 (by rfl) ⟨2818052, by rfl⟩ : syracuseStep 3757403 = 5636105) B5636105
theorem B2970971 : Blo 876568 2970971 := bstep (se 1 (by rfl) ⟨2228228, by rfl⟩ : syracuseStep 2970971 = 4456457) B4456457
theorem B3167687 : Blo 876568 3167687 := bstep (se 1 (by rfl) ⟨2375765, by rfl⟩ : syracuseStep 3167687 = 4751531) B4751531
theorem B2971079 : Blo 876568 2971079 := bstep (se 1 (by rfl) ⟨2228309, by rfl⟩ : syracuseStep 2971079 = 4456619) B4456619
theorem B2971403 : Blo 876568 2971403 := bstep (se 1 (by rfl) ⟨2228552, by rfl⟩ : syracuseStep 2971403 = 4457105) B4457105
theorem B2971673 : Blo 876568 2971673 := bstep (se 2 (by rfl) ⟨1114377, by rfl⟩ : syracuseStep 2971673 = 2228755) B2228755
theorem B10279111 : Blo 876568 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B14998445 : Blo 876568 14998445 := bstep (se 3 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 14998445 = 5624417) B5624417
theorem B8444897 : Blo 876568 8444897 := bstep (se 2 (by rfl) ⟨3166836, by rfl⟩ : syracuseStep 8444897 = 6333673) B6333673
theorem B4447223 : Blo 876568 4447223 := bstep (se 1 (by rfl) ⟨3335417, by rfl⟩ : syracuseStep 4447223 = 6670835) B6670835
theorem B3169271 : Blo 876568 3169271 := bstep (se 1 (by rfl) ⟨2376953, by rfl⟩ : syracuseStep 3169271 = 4753907) B4753907
theorem B7494713 : Blo 876568 7494713 := bstep (se 2 (by rfl) ⟨2810517, by rfl⟩ : syracuseStep 7494713 = 5621035) B5621035
theorem B5332385 : Blo 876568 5332385 := bstep (se 2 (by rfl) ⟨1999644, by rfl⟩ : syracuseStep 5332385 = 3999289) B3999289
theorem B91250081 : Blo 876568 91250081 := bstep (se 2 (by rfl) ⟨34218780, by rfl⟩ : syracuseStep 91250081 = 68437561) B68437561
theorem B2219663 : Blo 876568 2219663 := bstep (se 1 (by rfl) ⟨1664747, by rfl⟩ : syracuseStep 2219663 = 3329495) B3329495
theorem B3006503 : Blo 876568 3006503 := bstep (se 1 (by rfl) ⟨2254877, by rfl⟩ : syracuseStep 3006503 = 4509755) B4509755
theorem B876775 : Blo 876568 876775 := bstep (se 1 (by rfl) ⟨657581, by rfl⟩ : syracuseStep 876775 = 1315163) B1315163
theorem B876927 : Blo 876568 876927 := bstep (se 1 (by rfl) ⟨657695, by rfl⟩ : syracuseStep 876927 = 1315391) B1315391
theorem B877007 : Blo 876568 877007 := bstep (se 1 (by rfl) ⟨657755, by rfl⟩ : syracuseStep 877007 = 1315511) B1315511
theorem B877159 : Blo 876568 877159 := bstep (se 1 (by rfl) ⟨657869, by rfl⟩ : syracuseStep 877159 = 1315739) B1315739
theorem B21652103 : Blo 876568 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B10838681 : Blo 876568 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B97608401 : Blo 876568 97608401 := bstep (se 2 (by rfl) ⟨36603150, by rfl⟩ : syracuseStep 97608401 = 73206301) B73206301
theorem B877423 : Blo 876568 877423 := bstep (se 1 (by rfl) ⟨658067, by rfl⟩ : syracuseStep 877423 = 1316135) B1316135
theorem B20243351 : Blo 876568 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B877479 : Blo 876568 877479 := bstep (se 1 (by rfl) ⟨658109, by rfl⟩ : syracuseStep 877479 = 1316219) B1316219
theorem B877563 : Blo 876568 877563 := bstep (se 1 (by rfl) ⟨658172, by rfl⟩ : syracuseStep 877563 = 1316345) B1316345
theorem B877631 : Blo 876568 877631 := bstep (se 1 (by rfl) ⟨658223, by rfl⟩ : syracuseStep 877631 = 1316447) B1316447
theorem B3335357 : Blo 876568 3335357 := bstep (se 3 (by rfl) ⟨625379, by rfl⟩ : syracuseStep 3335357 = 1250759) B1250759
theorem B877775 : Blo 876568 877775 := bstep (se 1 (by rfl) ⟨658331, by rfl⟩ : syracuseStep 877775 = 1316663) B1316663
theorem B877979 : Blo 876568 877979 := bstep (se 1 (by rfl) ⟨658484, by rfl⟩ : syracuseStep 877979 = 1316969) B1316969
theorem B878191 : Blo 876568 878191 := bstep (se 1 (by rfl) ⟨658643, by rfl⟩ : syracuseStep 878191 = 1317287) B1317287
theorem B878247 : Blo 876568 878247 := bstep (se 1 (by rfl) ⟨658685, by rfl⟩ : syracuseStep 878247 = 1317371) B1317371
theorem B878331 : Blo 876568 878331 := bstep (se 1 (by rfl) ⟨658748, by rfl⟩ : syracuseStep 878331 = 1317497) B1317497
theorem B878367 : Blo 876568 878367 := bstep (se 1 (by rfl) ⟨658775, by rfl⟩ : syracuseStep 878367 = 1317551) B1317551
theorem B878399 : Blo 876568 878399 := bstep (se 1 (by rfl) ⟨658799, by rfl⟩ : syracuseStep 878399 = 1317599) B1317599
theorem B878575 : Blo 876568 878575 := bstep (se 1 (by rfl) ⟨658931, by rfl⟩ : syracuseStep 878575 = 1317863) B1317863
theorem B878747 : Blo 876568 878747 := bstep (se 1 (by rfl) ⟨659060, by rfl⟩ : syracuseStep 878747 = 1318121) B1318121
theorem B878783 : Blo 876568 878783 := bstep (se 1 (by rfl) ⟨659087, by rfl⟩ : syracuseStep 878783 = 1318175) B1318175
theorem B878895 : Blo 876568 878895 := bstep (se 1 (by rfl) ⟨659171, by rfl⟩ : syracuseStep 878895 = 1318343) B1318343
theorem B8448313 : Blo 876568 8448313 := bstep (se 2 (by rfl) ⟨3168117, by rfl⟩ : syracuseStep 8448313 = 6336235) B6336235
theorem B6318593 : Blo 876568 6318593 := bstep (se 2 (by rfl) ⟨2369472, by rfl⟩ : syracuseStep 6318593 = 4738945) B4738945
theorem B2222599 : Blo 876568 2222599 := bstep (se 1 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 2222599 = 3333899) B3333899
theorem B879131 : Blo 876568 879131 := bstep (se 1 (by rfl) ⟨659348, by rfl⟩ : syracuseStep 879131 = 1318697) B1318697
theorem B879135 : Blo 876568 879135 := bstep (se 1 (by rfl) ⟨659351, by rfl⟩ : syracuseStep 879135 = 1318703) B1318703
theorem B5073515 : Blo 876568 5073515 := bstep (se 1 (by rfl) ⟨3805136, by rfl⟩ : syracuseStep 5073515 = 7610273) B7610273
theorem B2222903 : Blo 876568 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B879451 : Blo 876568 879451 := bstep (se 1 (by rfl) ⟨659588, by rfl⟩ : syracuseStep 879451 = 1319177) B1319177
theorem B879519 : Blo 876568 879519 := bstep (se 1 (by rfl) ⟨659639, by rfl⟩ : syracuseStep 879519 = 1319279) B1319279
theorem B57863099 : Blo 876568 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B5008391 : Blo 876568 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B879663 : Blo 876568 879663 := bstep (se 1 (by rfl) ⟨659747, by rfl⟩ : syracuseStep 879663 = 1319495) B1319495
theorem B879687 : Blo 876568 879687 := bstep (se 1 (by rfl) ⟨659765, by rfl⟩ : syracuseStep 879687 = 1319531) B1319531
theorem B11234483 : Blo 876568 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B879839 : Blo 876568 879839 := bstep (se 1 (by rfl) ⟨659879, by rfl⟩ : syracuseStep 879839 = 1319759) B1319759
theorem B3566891 : Blo 876568 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B4287853 : Blo 876568 4287853 := bstep (se 3 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 4287853 = 1607945) B1607945
theorem B880103 : Blo 876568 880103 := bstep (se 1 (by rfl) ⟨660077, by rfl⟩ : syracuseStep 880103 = 1320155) B1320155
theorem B880219 : Blo 876568 880219 := bstep (se 1 (by rfl) ⟨660164, by rfl⟩ : syracuseStep 880219 = 1320329) B1320329
theorem B880455 : Blo 876568 880455 := bstep (se 1 (by rfl) ⟨660341, by rfl⟩ : syracuseStep 880455 = 1320683) B1320683
theorem B10678391 : Blo 876568 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B5009597 : Blo 876568 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B4518287 : Blo 876568 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B6320551 : Blo 876568 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B1405433 : Blo 876568 1405433 := bstep (se 2 (by rfl) ⟨527037, by rfl⟩ : syracuseStep 1405433 = 1054075) B1054075
theorem B9630353 : Blo 876568 9630353 := bstep (se 2 (by rfl) ⟨3611382, by rfl⟩ : syracuseStep 9630353 = 7222765) B7222765
theorem B4223735 : Blo 876568 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B1504057 : Blo 876568 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B1668271 : Blo 876568 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B2815489 : Blo 876568 2815489 := bstep (se 2 (by rfl) ⟨1055808, by rfl⟩ : syracuseStep 2815489 = 2111617) B2111617
theorem B10679941 : Blo 876568 10679941 := bstep (se 4 (by rfl) ⟨1001244, by rfl⟩ : syracuseStep 10679941 = 2002489) B2002489
theorem B12678929 : Blo 876568 12678929 := bstep (se 2 (by rfl) ⟨4754598, by rfl⟩ : syracuseStep 12678929 = 9509197) B9509197
theorem B8026013 : Blo 876568 8026013 := bstep (se 3 (by rfl) ⟨1504877, by rfl⟩ : syracuseStep 8026013 = 3009755) B3009755
theorem B5634107 : Blo 876568 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B3340385 : Blo 876568 3340385 := bstep (se 2 (by rfl) ⟨1252644, by rfl⟩ : syracuseStep 3340385 = 2505289) B2505289
theorem B12024247 : Blo 876568 12024247 := bstep (se 1 (by rfl) ⟨9018185, by rfl⟩ : syracuseStep 12024247 = 18036371) B18036371
theorem B2816669 : Blo 876568 2816669 := bstep (se 3 (by rfl) ⟨528125, by rfl⟩ : syracuseStep 2816669 = 1056251) B1056251
theorem B6683471 : Blo 876568 6683471 := bstep (se 1 (by rfl) ⟨5012603, by rfl⟩ : syracuseStep 6683471 = 10025207) B10025207
theorem B1670215 : Blo 876568 1670215 := bstep (se 1 (by rfl) ⟨1252661, by rfl⟩ : syracuseStep 1670215 = 2505323) B2505323
theorem B5012765 : Blo 876568 5012765 := bstep (se 3 (by rfl) ⟨939893, by rfl⟩ : syracuseStep 5012765 = 1879787) B1879787
theorem B1408745 : Blo 876568 1408745 := bstep (se 2 (by rfl) ⟨528279, by rfl⟩ : syracuseStep 1408745 = 1056559) B1056559
theorem B2227945 : Blo 876568 2227945 := bstep (se 2 (by rfl) ⟨835479, by rfl⟩ : syracuseStep 2227945 = 1670959) B1670959
theorem B2228411 : Blo 876568 2228411 := bstep (se 1 (by rfl) ⟨1671308, by rfl⟩ : syracuseStep 2228411 = 3342617) B3342617
theorem B1802783 : Blo 876568 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B8455079 : Blo 876568 8455079 := bstep (se 1 (by rfl) ⟨6341309, by rfl⟩ : syracuseStep 8455079 = 12682619) B12682619
theorem B4457753 : Blo 876568 4457753 := bstep (se 2 (by rfl) ⟨1671657, by rfl⟩ : syracuseStep 4457753 = 3343315) B3343315
theorem B14452091 : Blo 876568 14452091 := bstep (se 1 (by rfl) ⟨10839068, by rfl⟩ : syracuseStep 14452091 = 21678137) B21678137
theorem B5638565 : Blo 876568 5638565 := bstep (se 4 (by rfl) ⟨528615, by rfl⟩ : syracuseStep 5638565 = 1057231) B1057231
theorem B986287 : Blo 876568 986287 := bstep (se 1 (by rfl) ⟨739715, by rfl⟩ : syracuseStep 986287 = 1479431) B1479431
theorem B4230539 : Blo 876568 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B987007 : Blo 876568 987007 := bstep (se 1 (by rfl) ⟨740255, by rfl⟩ : syracuseStep 987007 = 1480511) B1480511
theorem B1314911 : Blo 876568 1314911 := bstep (se 1 (by rfl) ⟨986183, by rfl⟩ : syracuseStep 1314911 = 1972367) B1972367
theorem B1314923 : Blo 876568 1314923 := bstep (se 1 (by rfl) ⟨986192, by rfl⟩ : syracuseStep 1314923 = 1972385) B1972385
theorem B1314971 : Blo 876568 1314971 := bstep (se 1 (by rfl) ⟨986228, by rfl⟩ : syracuseStep 1314971 = 1972457) B1972457
theorem B5640515 : Blo 876568 5640515 := bstep (se 1 (by rfl) ⟨4230386, by rfl⟩ : syracuseStep 5640515 = 8460773) B8460773
theorem B987547 : Blo 876568 987547 := bstep (se 1 (by rfl) ⟨740660, by rfl⟩ : syracuseStep 987547 = 1481321) B1481321
theorem B9998963 : Blo 876568 9998963 := bstep (se 1 (by rfl) ⟨7499222, by rfl⟩ : syracuseStep 9998963 = 14998445) B14998445
theorem B4002643 : Blo 876568 4002643 := bstep (se 1 (by rfl) ⟨3001982, by rfl⟩ : syracuseStep 4002643 = 6003965) B6003965
theorem B1315823 : Blo 876568 1315823 := bstep (se 1 (by rfl) ⟨986867, by rfl⟩ : syracuseStep 1315823 = 1973735) B1973735
theorem B1053767 : Blo 876568 1053767 := bstep (se 1 (by rfl) ⟨790325, by rfl⟩ : syracuseStep 1053767 = 1580651) B1580651
theorem B988231 : Blo 876568 988231 := bstep (se 1 (by rfl) ⟨741173, by rfl⟩ : syracuseStep 988231 = 1482347) B1482347
theorem B21402701 : Blo 876568 21402701 := bstep (se 3 (by rfl) ⟨4013006, by rfl⟩ : syracuseStep 21402701 = 8026013) B8026013
theorem B1479775 : Blo 876568 1479775 := bstep (se 1 (by rfl) ⟨1109831, by rfl⟩ : syracuseStep 1479775 = 2219663) B2219663
theorem B988411 : Blo 876568 988411 := bstep (se 1 (by rfl) ⟨741308, by rfl⟩ : syracuseStep 988411 = 1482617) B1482617
theorem B1316207 : Blo 876568 1316207 := bstep (se 1 (by rfl) ⟨987155, by rfl⟩ : syracuseStep 1316207 = 1974311) B1974311
theorem B2004335 : Blo 876568 2004335 := bstep (se 1 (by rfl) ⟨1503251, by rfl⟩ : syracuseStep 2004335 = 3006503) B3006503
theorem B1316327 : Blo 876568 1316327 := bstep (se 1 (by rfl) ⟨987245, by rfl⟩ : syracuseStep 1316327 = 1974491) B1974491
theorem B1316489 : Blo 876568 1316489 := bstep (se 2 (by rfl) ⟨493683, by rfl⟩ : syracuseStep 1316489 = 987367) B987367
theorem B1316507 : Blo 876568 1316507 := bstep (se 1 (by rfl) ⟨987380, by rfl⟩ : syracuseStep 1316507 = 1974761) B1974761
theorem B1316699 : Blo 876568 1316699 := bstep (se 1 (by rfl) ⟨987524, by rfl⟩ : syracuseStep 1316699 = 1975049) B1975049
theorem B8427401 : Blo 876568 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B2496415 : Blo 876568 2496415 := bstep (se 1 (by rfl) ⟨1872311, by rfl⟩ : syracuseStep 2496415 = 3744623) B3744623
theorem B8001641 : Blo 876568 8001641 := bstep (se 2 (by rfl) ⟨3000615, by rfl⟩ : syracuseStep 8001641 = 6001231) B6001231
theorem B1317083 : Blo 876568 1317083 := bstep (se 1 (by rfl) ⟨987812, by rfl⟩ : syracuseStep 1317083 = 1975625) B1975625
theorem B1972511 : Blo 876568 1972511 := bstep (se 1 (by rfl) ⟨1479383, by rfl⟩ : syracuseStep 1972511 = 2958767) B2958767
theorem B989599 : Blo 876568 989599 := bstep (se 1 (by rfl) ⟨742199, by rfl⟩ : syracuseStep 989599 = 1484399) B1484399
theorem B2005409 : Blo 876568 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B989671 : Blo 876568 989671 := bstep (se 1 (by rfl) ⟨742253, by rfl⟩ : syracuseStep 989671 = 1484507) B1484507
theorem B1317353 : Blo 876568 1317353 := bstep (se 2 (by rfl) ⟨494007, by rfl⟩ : syracuseStep 1317353 = 988015) B988015
theorem B1972763 : Blo 876568 1972763 := bstep (se 1 (by rfl) ⟨1479572, by rfl⟩ : syracuseStep 1972763 = 2959145) B2959145
theorem B1317743 : Blo 876568 1317743 := bstep (se 1 (by rfl) ⟨988307, by rfl⟩ : syracuseStep 1317743 = 1976615) B1976615
theorem B1317755 : Blo 876568 1317755 := bstep (se 1 (by rfl) ⟨988316, by rfl⟩ : syracuseStep 1317755 = 1976633) B1976633
theorem B3382343 : Blo 876568 3382343 := bstep (se 1 (by rfl) ⟨2536757, by rfl⟩ : syracuseStep 3382343 = 5073515) B5073515
theorem B3382393 : Blo 876568 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B1481935 : Blo 876568 1481935 := bstep (se 1 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 1481935 = 2222903) B2222903
theorem B38575399 : Blo 876568 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B990535 : Blo 876568 990535 := bstep (se 1 (by rfl) ⟨742901, by rfl⟩ : syracuseStep 990535 = 1485803) B1485803
theorem B8429093 : Blo 876568 8429093 := bstep (se 4 (by rfl) ⟨790227, by rfl⟩ : syracuseStep 8429093 = 1580455) B1580455
theorem B6659657 : Blo 876568 6659657 := bstep (se 2 (by rfl) ⟨2497371, by rfl⟩ : syracuseStep 6659657 = 4994743) B4994743
theorem B1318619 : Blo 876568 1318619 := bstep (se 1 (by rfl) ⟨988964, by rfl⟩ : syracuseStep 1318619 = 1977929) B1977929
theorem B1253083 : Blo 876568 1253083 := bstep (se 1 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 1253083 = 1879625) B1879625
theorem B1974113 : Blo 876568 1974113 := bstep (se 2 (by rfl) ⟨740292, by rfl⟩ : syracuseStep 1974113 = 1480585) B1480585
theorem B1974239 : Blo 876568 1974239 := bstep (se 1 (by rfl) ⟨1480679, by rfl⟩ : syracuseStep 1974239 = 2961359) B2961359
theorem B1318889 : Blo 876568 1318889 := bstep (se 2 (by rfl) ⟨494583, by rfl⟩ : syracuseStep 1318889 = 989167) B989167
theorem B15015941 : Blo 876568 15015941 := bstep (se 4 (by rfl) ⟨1407744, by rfl⟩ : syracuseStep 15015941 = 2815489) B2815489
theorem B7118927 : Blo 876568 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B1974527 : Blo 876568 1974527 := bstep (se 1 (by rfl) ⟨1480895, by rfl⟩ : syracuseStep 1974527 = 2961791) B2961791
theorem B13705481 : Blo 876568 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B1974689 : Blo 876568 1974689 := bstep (se 2 (by rfl) ⟨740508, by rfl⟩ : syracuseStep 1974689 = 1481017) B1481017
theorem B16032329 : Blo 876568 16032329 := bstep (se 2 (by rfl) ⟨6012123, by rfl⟩ : syracuseStep 16032329 = 12024247) B12024247
theorem B12198521 : Blo 876568 12198521 := bstep (se 2 (by rfl) ⟨4574445, by rfl⟩ : syracuseStep 12198521 = 9148891) B9148891
theorem B1319591 : Blo 876568 1319591 := bstep (se 1 (by rfl) ⟨989693, by rfl⟩ : syracuseStep 1319591 = 1979387) B1979387
theorem B56959685 : Blo 876568 56959685 := bstep (se 4 (by rfl) ⟨5339970, by rfl⟩ : syracuseStep 56959685 = 10679941) B10679941
theorem B1319711 : Blo 876568 1319711 := bstep (se 1 (by rfl) ⟨989783, by rfl⟩ : syracuseStep 1319711 = 1979567) B1979567
theorem B1319735 : Blo 876568 1319735 := bstep (se 1 (by rfl) ⟨989801, by rfl⟩ : syracuseStep 1319735 = 1979603) B1979603
theorem B1319915 : Blo 876568 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B1975463 : Blo 876568 1975463 := bstep (se 1 (by rfl) ⟨1481597, by rfl⟩ : syracuseStep 1975463 = 2963195) B2963195
theorem B1975571 : Blo 876568 1975571 := bstep (se 1 (by rfl) ⟨1481678, by rfl⟩ : syracuseStep 1975571 = 2963357) B2963357
theorem B3745223 : Blo 876568 3745223 := bstep (se 1 (by rfl) ⟨2808917, by rfl⟩ : syracuseStep 3745223 = 5617835) B5617835
theorem B1877779 : Blo 876568 1877779 := bstep (se 1 (by rfl) ⟨1408334, by rfl⟩ : syracuseStep 1877779 = 2816669) B2816669
theorem B1976201 : Blo 876568 1976201 := bstep (se 2 (by rfl) ⟨741075, by rfl⟩ : syracuseStep 1976201 = 1482151) B1482151
theorem B1976219 : Blo 876568 1976219 := bstep (se 1 (by rfl) ⟨1482164, by rfl⟩ : syracuseStep 1976219 = 2964329) B2964329
theorem B1976255 : Blo 876568 1976255 := bstep (se 1 (by rfl) ⟨1482191, by rfl⟩ : syracuseStep 1976255 = 2964383) B2964383
theorem B2566171 : Blo 876568 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B1976417 : Blo 876568 1976417 := bstep (se 2 (by rfl) ⟨741156, by rfl⟩ : syracuseStep 1976417 = 1482313) B1482313
theorem B40511987 : Blo 876568 40511987 := bstep (se 1 (by rfl) ⟨30383990, by rfl⟩ : syracuseStep 40511987 = 60767981) B60767981
theorem B2959955 : Blo 876568 2959955 := bstep (se 1 (by rfl) ⟨2219966, by rfl⟩ : syracuseStep 2959955 = 4439933) B4439933
theorem B3747151 : Blo 876568 3747151 := bstep (se 1 (by rfl) ⟨2810363, by rfl⟩ : syracuseStep 3747151 = 5620727) B5620727
theorem B1977767 : Blo 876568 1977767 := bstep (se 1 (by rfl) ⟨1483325, by rfl⟩ : syracuseStep 1977767 = 2966651) B2966651
theorem B1584607 : Blo 876568 1584607 := bstep (se 1 (by rfl) ⟨1188455, by rfl⟩ : syracuseStep 1584607 = 2376911) B2376911
theorem B1977947 : Blo 876568 1977947 := bstep (se 1 (by rfl) ⟨1483460, by rfl⟩ : syracuseStep 1977947 = 2966921) B2966921
theorem B13512379 : Blo 876568 13512379 := bstep (se 1 (by rfl) ⟨10134284, by rfl⟩ : syracuseStep 13512379 = 20268569) B20268569
theorem B2961143 : Blo 876568 2961143 := bstep (se 1 (by rfl) ⟨2220857, by rfl⟩ : syracuseStep 2961143 = 4441715) B4441715
theorem B1978361 : Blo 876568 1978361 := bstep (se 2 (by rfl) ⟨741885, by rfl⟩ : syracuseStep 1978361 = 1483771) B1483771
theorem B1978451 : Blo 876568 1978451 := bstep (se 1 (by rfl) ⟨1483838, by rfl⟩ : syracuseStep 1978451 = 2967677) B2967677
theorem B9023683 : Blo 876568 9023683 := bstep (se 1 (by rfl) ⟨6767762, by rfl⟩ : syracuseStep 9023683 = 13535525) B13535525
theorem B1978631 : Blo 876568 1978631 := bstep (se 1 (by rfl) ⟨1483973, by rfl⟩ : syracuseStep 1978631 = 2967947) B2967947
theorem B2961683 : Blo 876568 2961683 := bstep (se 1 (by rfl) ⟨2221262, by rfl⟩ : syracuseStep 2961683 = 4442525) B4442525
theorem B1978937 : Blo 876568 1978937 := bstep (se 2 (by rfl) ⟨742101, by rfl⟩ : syracuseStep 1978937 = 1484203) B1484203
theorem B1880633 : Blo 876568 1880633 := bstep (se 2 (by rfl) ⟨705237, by rfl⟩ : syracuseStep 1880633 = 1410475) B1410475
theorem B3748655 : Blo 876568 3748655 := bstep (se 1 (by rfl) ⟨2811491, by rfl⟩ : syracuseStep 3748655 = 5622983) B5622983
theorem B2962223 : Blo 876568 2962223 := bstep (se 1 (by rfl) ⟨2221667, by rfl⟩ : syracuseStep 2962223 = 4443335) B4443335
theorem B2437951 : Blo 876568 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B14496683 : Blo 876568 14496683 := bstep (se 1 (by rfl) ⟨10872512, by rfl⟩ : syracuseStep 14496683 = 21745025) B21745025
theorem B6009851 : Blo 876568 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B1979657 : Blo 876568 1979657 := bstep (se 2 (by rfl) ⟨742371, by rfl⟩ : syracuseStep 1979657 = 1484743) B1484743
theorem B1979711 : Blo 876568 1979711 := bstep (se 1 (by rfl) ⟨1484783, by rfl⟩ : syracuseStep 1979711 = 2969567) B2969567
theorem B1979819 : Blo 876568 1979819 := bstep (se 1 (by rfl) ⟨1484864, by rfl⟩ : syracuseStep 1979819 = 2969729) B2969729
theorem B5617295 : Blo 876568 5617295 := bstep (se 1 (by rfl) ⟨4212971, by rfl⟩ : syracuseStep 5617295 = 8425943) B8425943
theorem B2963087 : Blo 876568 2963087 := bstep (se 1 (by rfl) ⟨2222315, by rfl⟩ : syracuseStep 2963087 = 4444631) B4444631
theorem B4437665 : Blo 876568 4437665 := bstep (se 2 (by rfl) ⟨1664124, by rfl⟩ : syracuseStep 4437665 = 3328249) B3328249
theorem B1980143 : Blo 876568 1980143 := bstep (se 1 (by rfl) ⟨1485107, by rfl⟩ : syracuseStep 1980143 = 2970215) B2970215
theorem B2537257 : Blo 876568 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B1980359 : Blo 876568 1980359 := bstep (se 1 (by rfl) ⟨1485269, by rfl⟩ : syracuseStep 1980359 = 2970539) B2970539
theorem B6338519 : Blo 876568 6338519 := bstep (se 1 (by rfl) ⟨4753889, by rfl⟩ : syracuseStep 6338519 = 9507779) B9507779
theorem B2963465 : Blo 876568 2963465 := bstep (se 2 (by rfl) ⟨1111299, by rfl⟩ : syracuseStep 2963465 = 2222599) B2222599
theorem B2504935 : Blo 876568 2504935 := bstep (se 1 (by rfl) ⟨1878701, by rfl⟩ : syracuseStep 2504935 = 3757403) B3757403
theorem B1980647 : Blo 876568 1980647 := bstep (se 1 (by rfl) ⟨1485485, by rfl⟩ : syracuseStep 1980647 = 2970971) B2970971
theorem B1980665 : Blo 876568 1980665 := bstep (se 2 (by rfl) ⟨742749, by rfl⟩ : syracuseStep 1980665 = 1485499) B1485499
theorem B1980719 : Blo 876568 1980719 := bstep (se 1 (by rfl) ⟨1485539, by rfl⟩ : syracuseStep 1980719 = 2971079) B2971079
theorem B1980935 : Blo 876568 1980935 := bstep (se 1 (by rfl) ⟨1485701, by rfl⟩ : syracuseStep 1980935 = 2971403) B2971403
theorem B1981115 : Blo 876568 1981115 := bstep (se 1 (by rfl) ⟨1485836, by rfl⟩ : syracuseStep 1981115 = 2971673) B2971673
theorem B6339293 : Blo 876568 6339293 := bstep (se 3 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 6339293 = 2377235) B2377235
theorem B60865501 : Blo 876568 60865501 := bstep (se 3 (by rfl) ⟨11412281, by rfl⟩ : syracuseStep 60865501 = 22824563) B22824563
theorem B2112617 : Blo 876568 2112617 := bstep (se 2 (by rfl) ⟨792231, by rfl⟩ : syracuseStep 2112617 = 1584463) B1584463
theorem B5717137 : Blo 876568 5717137 := bstep (se 2 (by rfl) ⟨2143926, by rfl⟩ : syracuseStep 5717137 = 4287853) B4287853
theorem B14269765 : Blo 876568 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B2964815 : Blo 876568 2964815 := bstep (se 1 (by rfl) ⟨2223611, by rfl⟩ : syracuseStep 2964815 = 4447223) B4447223
theorem B2112847 : Blo 876568 2112847 := bstep (se 1 (by rfl) ⟨1584635, by rfl⟩ : syracuseStep 2112847 = 3169271) B3169271
theorem B4996475 : Blo 876568 4996475 := bstep (se 1 (by rfl) ⟨3747356, by rfl⟩ : syracuseStep 4996475 = 7494713) B7494713
theorem B3554923 : Blo 876568 3554923 := bstep (se 1 (by rfl) ⟨2666192, by rfl⟩ : syracuseStep 3554923 = 5332385) B5332385
theorem B60833387 : Blo 876568 60833387 := bstep (se 1 (by rfl) ⟨45625040, by rfl⟩ : syracuseStep 60833387 = 91250081) B91250081
theorem B14434735 : Blo 876568 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B7225787 : Blo 876568 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B5620499 : Blo 876568 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B7521335 : Blo 876568 7521335 := bstep (se 1 (by rfl) ⟨5641001, by rfl⟩ : syracuseStep 7521335 = 11282003) B11282003
theorem B18990713 : Blo 876568 18990713 := bstep (se 2 (by rfl) ⟨7121517, by rfl⟩ : syracuseStep 18990713 = 14243035) B14243035
theorem B4212395 : Blo 876568 4212395 := bstep (se 1 (by rfl) ⟨3159296, by rfl⟩ : syracuseStep 4212395 = 6318593) B6318593
theorem B7489655 : Blo 876568 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B2377927 : Blo 876568 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B4213529 : Blo 876568 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B4213741 : Blo 876568 4213741 := bstep (se 3 (by rfl) ⟨790076, by rfl⟩ : syracuseStep 4213741 = 1580153) B1580153
theorem B936955 : Blo 876568 936955 := bstep (se 1 (by rfl) ⟨702716, by rfl⟩ : syracuseStep 936955 = 1405433) B1405433
theorem B5622959 : Blo 876568 5622959 := bstep (se 1 (by rfl) ⟨4217219, by rfl⟩ : syracuseStep 5622959 = 8434439) B8434439
theorem B68603377 : Blo 876568 68603377 := bstep (se 2 (by rfl) ⟨25726266, by rfl⟩ : syracuseStep 68603377 = 51452533) B51452533
theorem B13553255 : Blo 876568 13553255 := bstep (se 1 (by rfl) ⟨10164941, by rfl⟩ : syracuseStep 13553255 = 20329883) B20329883
theorem B3329707 : Blo 876568 3329707 := bstep (se 1 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 3329707 = 4994561) B4994561
theorem B3329981 : Blo 876568 3329981 := bstep (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) B1248743
theorem B3756071 : Blo 876568 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B2970593 : Blo 876568 2970593 := bstep (se 2 (by rfl) ⟨1113972, by rfl⟩ : syracuseStep 2970593 = 2227945) B2227945
theorem B4445279 : Blo 876568 4445279 := bstep (se 1 (by rfl) ⟨3333959, by rfl⟩ : syracuseStep 4445279 = 6667919) B6667919
theorem B939163 : Blo 876568 939163 := bstep (se 1 (by rfl) ⟨704372, by rfl⟩ : syracuseStep 939163 = 1408745) B1408745
theorem B5625085 : Blo 876568 5625085 := bstep (se 3 (by rfl) ⟨1054703, by rfl⟩ : syracuseStep 5625085 = 2109407) B2109407
theorem B2676361 : Blo 876568 2676361 := bstep (se 2 (by rfl) ⟨1003635, by rfl⟩ : syracuseStep 2676361 = 2007271) B2007271
theorem B18995735 : Blo 876568 18995735 := bstep (se 1 (by rfl) ⟨14246801, by rfl⟩ : syracuseStep 18995735 = 28493603) B28493603
theorem B2218823 : Blo 876568 2218823 := bstep (se 1 (by rfl) ⟨1664117, by rfl⟩ : syracuseStep 2218823 = 3328235) B3328235
theorem B28892609 : Blo 876568 28892609 := bstep (se 2 (by rfl) ⟨10834728, by rfl⟩ : syracuseStep 28892609 = 21669457) B21669457
theorem B2219795 : Blo 876568 2219795 := bstep (se 1 (by rfl) ⟨1664846, by rfl⟩ : syracuseStep 2219795 = 3329693) B3329693
theorem B1204079 : Blo 876568 1204079 := bstep (se 1 (by rfl) ⟨903059, by rfl⟩ : syracuseStep 1204079 = 1806119) B1806119
theorem B7495739 : Blo 876568 7495739 := bstep (se 1 (by rfl) ⟨5621804, by rfl⟩ : syracuseStep 7495739 = 11243609) B11243609
theorem B876735 : Blo 876568 876735 := bstep (se 1 (by rfl) ⟨657551, by rfl⟩ : syracuseStep 876735 = 1315103) B1315103
theorem B876751 : Blo 876568 876751 := bstep (se 1 (by rfl) ⟨657563, by rfl⟩ : syracuseStep 876751 = 1315127) B1315127
theorem B876799 : Blo 876568 876799 := bstep (se 1 (by rfl) ⟨657599, by rfl⟩ : syracuseStep 876799 = 1315199) B1315199
theorem B876847 : Blo 876568 876847 := bstep (se 1 (by rfl) ⟨657635, by rfl⟩ : syracuseStep 876847 = 1315271) B1315271
theorem B11264417 : Blo 876568 11264417 := bstep (se 2 (by rfl) ⟨4224156, by rfl⟩ : syracuseStep 11264417 = 8448313) B8448313
theorem B3334567 : Blo 876568 3334567 := bstep (se 1 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 3334567 = 5001851) B5001851
theorem B877083 : Blo 876568 877083 := bstep (se 1 (by rfl) ⟨657812, by rfl⟩ : syracuseStep 877083 = 1315625) B1315625
theorem B877087 : Blo 876568 877087 := bstep (se 1 (by rfl) ⟨657815, by rfl⟩ : syracuseStep 877087 = 1315631) B1315631
theorem B877167 : Blo 876568 877167 := bstep (se 1 (by rfl) ⟨657875, by rfl⟩ : syracuseStep 877167 = 1315751) B1315751
theorem B877223 : Blo 876568 877223 := bstep (se 1 (by rfl) ⟨657917, by rfl⟩ : syracuseStep 877223 = 1315835) B1315835
theorem B877263 : Blo 876568 877263 := bstep (se 1 (by rfl) ⟨657947, by rfl⟩ : syracuseStep 877263 = 1315895) B1315895
theorem B877343 : Blo 876568 877343 := bstep (se 1 (by rfl) ⟨658007, by rfl⟩ : syracuseStep 877343 = 1316015) B1316015
theorem B877615 : Blo 876568 877615 := bstep (se 1 (by rfl) ⟨658211, by rfl⟩ : syracuseStep 877615 = 1316423) B1316423
theorem B877679 : Blo 876568 877679 := bstep (se 1 (by rfl) ⟨658259, by rfl⟩ : syracuseStep 877679 = 1316519) B1316519
theorem B877735 : Blo 876568 877735 := bstep (se 1 (by rfl) ⟨658301, by rfl⟩ : syracuseStep 877735 = 1316603) B1316603
theorem B8447165 : Blo 876568 8447165 := bstep (se 3 (by rfl) ⟨1583843, by rfl⟩ : syracuseStep 8447165 = 3167687) B3167687
theorem B877759 : Blo 876568 877759 := bstep (se 1 (by rfl) ⟨658319, by rfl⟩ : syracuseStep 877759 = 1316639) B1316639
theorem B877791 : Blo 876568 877791 := bstep (se 1 (by rfl) ⟨658343, by rfl⟩ : syracuseStep 877791 = 1316687) B1316687
theorem B877871 : Blo 876568 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B878107 : Blo 876568 878107 := bstep (se 1 (by rfl) ⟨658580, by rfl⟩ : syracuseStep 878107 = 1317161) B1317161
theorem B878111 : Blo 876568 878111 := bstep (se 1 (by rfl) ⟨658583, by rfl⟩ : syracuseStep 878111 = 1317167) B1317167
theorem B878271 : Blo 876568 878271 := bstep (se 1 (by rfl) ⟨658703, by rfl⟩ : syracuseStep 878271 = 1317407) B1317407
theorem B878527 : Blo 876568 878527 := bstep (se 1 (by rfl) ⟨658895, by rfl⟩ : syracuseStep 878527 = 1317791) B1317791
theorem B878559 : Blo 876568 878559 := bstep (se 1 (by rfl) ⟨658919, by rfl⟩ : syracuseStep 878559 = 1317839) B1317839
theorem B5629931 : Blo 876568 5629931 := bstep (se 1 (by rfl) ⟨4222448, by rfl⟩ : syracuseStep 5629931 = 8444897) B8444897
theorem B878619 : Blo 876568 878619 := bstep (se 1 (by rfl) ⟨658964, by rfl⟩ : syracuseStep 878619 = 1317929) B1317929
theorem B878623 : Blo 876568 878623 := bstep (se 1 (by rfl) ⟨658967, by rfl⟩ : syracuseStep 878623 = 1317935) B1317935
theorem B878639 : Blo 876568 878639 := bstep (se 1 (by rfl) ⟨658979, by rfl⟩ : syracuseStep 878639 = 1317959) B1317959
theorem B3565691 : Blo 876568 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B62580869 : Blo 876568 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B878815 : Blo 876568 878815 := bstep (se 1 (by rfl) ⟨659111, by rfl⟩ : syracuseStep 878815 = 1318223) B1318223
theorem B878875 : Blo 876568 878875 := bstep (se 1 (by rfl) ⟨659156, by rfl⟩ : syracuseStep 878875 = 1318313) B1318313
theorem B878975 : Blo 876568 878975 := bstep (se 1 (by rfl) ⟨659231, by rfl⟩ : syracuseStep 878975 = 1318463) B1318463
theorem B1665515 : Blo 876568 1665515 := bstep (se 1 (by rfl) ⟨1249136, by rfl⟩ : syracuseStep 1665515 = 2498273) B2498273
theorem B879151 : Blo 876568 879151 := bstep (se 1 (by rfl) ⟨659363, by rfl⟩ : syracuseStep 879151 = 1318727) B1318727
theorem B879207 : Blo 876568 879207 := bstep (se 1 (by rfl) ⟨659405, by rfl⟩ : syracuseStep 879207 = 1318811) B1318811
theorem B879583 : Blo 876568 879583 := bstep (se 1 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 879583 = 1319375) B1319375
theorem B17591285 : Blo 876568 17591285 := bstep (se 5 (by rfl) ⟨824591, by rfl⟩ : syracuseStep 17591285 = 1649183) B1649183
theorem B879611 : Blo 876568 879611 := bstep (se 1 (by rfl) ⟨659708, by rfl⟩ : syracuseStep 879611 = 1319417) B1319417
theorem B879679 : Blo 876568 879679 := bstep (se 1 (by rfl) ⟨659759, by rfl⟩ : syracuseStep 879679 = 1319519) B1319519
theorem B65072267 : Blo 876568 65072267 := bstep (se 1 (by rfl) ⟨48804200, by rfl⟩ : syracuseStep 65072267 = 97608401) B97608401
theorem B13495567 : Blo 876568 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B4222313 : Blo 876568 4222313 := bstep (se 2 (by rfl) ⟨1583367, by rfl⟩ : syracuseStep 4222313 = 3166735) B3166735
theorem B879999 : Blo 876568 879999 := bstep (se 1 (by rfl) ⟨659999, by rfl⟩ : syracuseStep 879999 = 1319999) B1319999
theorem B880027 : Blo 876568 880027 := bstep (se 1 (by rfl) ⟨660020, by rfl⟩ : syracuseStep 880027 = 1320041) B1320041
theorem B2223571 : Blo 876568 2223571 := bstep (se 1 (by rfl) ⟨1667678, by rfl⟩ : syracuseStep 2223571 = 3335357) B3335357
theorem B880095 : Blo 876568 880095 := bstep (se 1 (by rfl) ⟨660071, by rfl⟩ : syracuseStep 880095 = 1320143) B1320143
theorem B1666631 : Blo 876568 1666631 := bstep (se 1 (by rfl) ⟨1249973, by rfl⟩ : syracuseStep 1666631 = 2499947) B2499947
theorem B880231 : Blo 876568 880231 := bstep (se 1 (by rfl) ⟨660173, by rfl⟩ : syracuseStep 880231 = 1320347) B1320347
theorem B7499465 : Blo 876568 7499465 := bstep (se 2 (by rfl) ⟨2812299, by rfl⟩ : syracuseStep 7499465 = 5624599) B5624599
theorem B880379 : Blo 876568 880379 := bstep (se 1 (by rfl) ⟨660284, by rfl⟩ : syracuseStep 880379 = 1320569) B1320569
theorem B880447 : Blo 876568 880447 := bstep (se 1 (by rfl) ⟨660335, by rfl⟩ : syracuseStep 880447 = 1320671) B1320671
theorem B880511 : Blo 876568 880511 := bstep (se 1 (by rfl) ⟨660383, by rfl⟩ : syracuseStep 880511 = 1320767) B1320767
theorem B1667155 : Blo 876568 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B109801615 : Blo 876568 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B2224361 : Blo 876568 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B3338927 : Blo 876568 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B1405945 : Blo 876568 1405945 := bstep (se 2 (by rfl) ⟨527229, by rfl⟩ : syracuseStep 1405945 = 1054459) B1054459
theorem B1668089 : Blo 876568 1668089 := bstep (se 2 (by rfl) ⟨625533, by rfl⟩ : syracuseStep 1668089 = 1251067) B1251067
theorem B1668347 : Blo 876568 1668347 := bstep (se 1 (by rfl) ⟨1251260, by rfl⟩ : syracuseStep 1668347 = 2502521) B2502521
theorem B3339731 : Blo 876568 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B3012191 : Blo 876568 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B1668833 : Blo 876568 1668833 := bstep (se 2 (by rfl) ⟨625812, by rfl⟩ : syracuseStep 1668833 = 1251625) B1251625
theorem B6420235 : Blo 876568 6420235 := bstep (se 1 (by rfl) ⟨4815176, by rfl⟩ : syracuseStep 6420235 = 9630353) B9630353
theorem B2815823 : Blo 876568 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B5011307 : Blo 876568 5011307 := bstep (se 1 (by rfl) ⟨3758480, by rfl⟩ : syracuseStep 5011307 = 7516961) B7516961
theorem B8452619 : Blo 876568 8452619 := bstep (se 1 (by rfl) ⟨6339464, by rfl⟩ : syracuseStep 8452619 = 12678929) B12678929
theorem B2226923 : Blo 876568 2226923 := bstep (se 1 (by rfl) ⟨1670192, by rfl⟩ : syracuseStep 2226923 = 3340385) B3340385
theorem B2226953 : Blo 876568 2226953 := bstep (se 2 (by rfl) ⟨835107, by rfl⟩ : syracuseStep 2226953 = 1670215) B1670215
theorem B9993131 : Blo 876568 9993131 := bstep (se 1 (by rfl) ⟨7494848, by rfl⟩ : syracuseStep 9993131 = 14989697) B14989697
theorem B4455647 : Blo 876568 4455647 := bstep (se 1 (by rfl) ⟨3341735, by rfl⟩ : syracuseStep 4455647 = 6683471) B6683471
theorem B1670375 : Blo 876568 1670375 := bstep (se 1 (by rfl) ⟨1252781, by rfl⟩ : syracuseStep 1670375 = 2505563) B2505563
theorem B3341843 : Blo 876568 3341843 := bstep (se 1 (by rfl) ⟨2506382, by rfl⟩ : syracuseStep 3341843 = 5012765) B5012765
theorem B3342161 : Blo 876568 3342161 := bstep (se 2 (by rfl) ⟨1253310, by rfl⟩ : syracuseStep 3342161 = 2506621) B2506621
theorem B4817191 : Blo 876568 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B5636719 : Blo 876568 5636719 := bstep (se 1 (by rfl) ⟨4227539, by rfl⟩ : syracuseStep 5636719 = 8455079) B8455079
theorem B5014223 : Blo 876568 5014223 := bstep (se 1 (by rfl) ⟨3760667, by rfl⟩ : syracuseStep 5014223 = 7521335) B7521335
theorem B9634727 : Blo 876568 9634727 := bstep (se 1 (by rfl) ⟨7226045, by rfl⟩ : syracuseStep 9634727 = 14452091) B14452091
theorem B12682277 : Blo 876568 12682277 := bstep (se 4 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 12682277 = 2377927) B2377927
theorem B2820359 : Blo 876568 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B1249273 : Blo 876568 1249273 := bstep (se 2 (by rfl) ⟨468477, by rfl⟩ : syracuseStep 1249273 = 936955) B936955
theorem B1315007 : Blo 876568 1315007 := bstep (se 1 (by rfl) ⟨986255, by rfl⟩ : syracuseStep 1315007 = 1972511) B1972511
theorem B1315049 : Blo 876568 1315049 := bstep (se 2 (by rfl) ⟨493143, by rfl⟩ : syracuseStep 1315049 = 986287) B986287
theorem B1315175 : Blo 876568 1315175 := bstep (se 1 (by rfl) ⟨986381, by rfl⟩ : syracuseStep 1315175 = 1972763) B1972763
theorem B17994089 : Blo 876568 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B1479215 : Blo 876568 1479215 := bstep (se 1 (by rfl) ⟨1109411, by rfl⟩ : syracuseStep 1479215 = 2218823) B2218823
theorem B7508861 : Blo 876568 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B1316009 : Blo 876568 1316009 := bstep (se 2 (by rfl) ⟨493503, by rfl⟩ : syracuseStep 1316009 = 987007) B987007
theorem B1479863 : Blo 876568 1479863 := bstep (se 1 (by rfl) ⟨1109897, by rfl⟩ : syracuseStep 1479863 = 2219795) B2219795
theorem B1316075 : Blo 876568 1316075 := bstep (se 1 (by rfl) ⟨987056, by rfl⟩ : syracuseStep 1316075 = 1974113) B1974113
theorem B1316159 : Blo 876568 1316159 := bstep (se 1 (by rfl) ⟨987119, by rfl⟩ : syracuseStep 1316159 = 1974239) B1974239
theorem B1316351 : Blo 876568 1316351 := bstep (se 1 (by rfl) ⟨987263, by rfl⟩ : syracuseStep 1316351 = 1974527) B1974527
theorem B12031577 : Blo 876568 12031577 := bstep (se 2 (by rfl) ⟨4511841, by rfl⟩ : syracuseStep 12031577 = 9023683) B9023683
theorem B1316459 : Blo 876568 1316459 := bstep (se 1 (by rfl) ⟨987344, by rfl⟩ : syracuseStep 1316459 = 1974689) B1974689
theorem B7509611 : Blo 876568 7509611 := bstep (se 1 (by rfl) ⟨5632208, by rfl⟩ : syracuseStep 7509611 = 11264417) B11264417
theorem B10688219 : Blo 876568 10688219 := bstep (se 1 (by rfl) ⟨8016164, by rfl⟩ : syracuseStep 10688219 = 16032329) B16032329
theorem B8132347 : Blo 876568 8132347 := bstep (se 1 (by rfl) ⟨6099260, by rfl⟩ : syracuseStep 8132347 = 12198521) B12198521
theorem B1316729 : Blo 876568 1316729 := bstep (se 2 (by rfl) ⟨493773, by rfl⟩ : syracuseStep 1316729 = 987547) B987547
theorem B1316975 : Blo 876568 1316975 := bstep (se 1 (by rfl) ⟨987731, by rfl⟩ : syracuseStep 1316975 = 1975463) B1975463
theorem B1317047 : Blo 876568 1317047 := bstep (se 1 (by rfl) ⟨987785, by rfl⟩ : syracuseStep 1317047 = 1975571) B1975571
theorem B2496815 : Blo 876568 2496815 := bstep (se 1 (by rfl) ⟨1872611, by rfl⟩ : syracuseStep 2496815 = 3745223) B3745223
theorem B3250601 : Blo 876568 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B5347757 : Blo 876568 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B1317467 : Blo 876568 1317467 := bstep (se 1 (by rfl) ⟨988100, by rfl⟩ : syracuseStep 1317467 = 1976201) B1976201
theorem B1317479 : Blo 876568 1317479 := bstep (se 1 (by rfl) ⟨988109, by rfl⟩ : syracuseStep 1317479 = 1976219) B1976219
theorem B1317503 : Blo 876568 1317503 := bstep (se 1 (by rfl) ⟨988127, by rfl⟩ : syracuseStep 1317503 = 1976255) B1976255
theorem B1874593 : Blo 876568 1874593 := bstep (se 2 (by rfl) ⟨702972, by rfl⟩ : syracuseStep 1874593 = 1405945) B1405945
theorem B1317611 : Blo 876568 1317611 := bstep (se 1 (by rfl) ⟨988208, by rfl⟩ : syracuseStep 1317611 = 1976417) B1976417
theorem B41720579 : Blo 876568 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B1317641 : Blo 876568 1317641 := bstep (se 2 (by rfl) ⟨494115, by rfl⟩ : syracuseStep 1317641 = 988231) B988231
theorem B1973033 : Blo 876568 1973033 := bstep (se 2 (by rfl) ⟨739887, by rfl⟩ : syracuseStep 1973033 = 1479775) B1479775
theorem B1252217 : Blo 876568 1252217 := bstep (se 2 (by rfl) ⟨469581, by rfl⟩ : syracuseStep 1252217 = 939163) B939163
theorem B27007991 : Blo 876568 27007991 := bstep (se 1 (by rfl) ⟨20255993, by rfl⟩ : syracuseStep 27007991 = 40511987) B40511987
theorem B1317881 : Blo 876568 1317881 := bstep (se 2 (by rfl) ⟨494205, by rfl⟩ : syracuseStep 1317881 = 988411) B988411
theorem B1973303 : Blo 876568 1973303 := bstep (se 1 (by rfl) ⟨1479977, by rfl⟩ : syracuseStep 1973303 = 2959955) B2959955
theorem B1318511 : Blo 876568 1318511 := bstep (se 1 (by rfl) ⟨988883, by rfl⟩ : syracuseStep 1318511 = 1977767) B1977767
theorem B8560313 : Blo 876568 8560313 := bstep (se 2 (by rfl) ⟨3210117, by rfl⟩ : syracuseStep 8560313 = 6420235) B6420235
theorem B3383009 : Blo 876568 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B1318631 : Blo 876568 1318631 := bstep (se 1 (by rfl) ⟨988973, by rfl⟩ : syracuseStep 1318631 = 1977947) B1977947
theorem B1974095 : Blo 876568 1974095 := bstep (se 1 (by rfl) ⟨1480571, by rfl⟩ : syracuseStep 1974095 = 2961143) B2961143
theorem B1318907 : Blo 876568 1318907 := bstep (se 1 (by rfl) ⟨989180, by rfl⟩ : syracuseStep 1318907 = 1978361) B1978361
theorem B1318967 : Blo 876568 1318967 := bstep (se 1 (by rfl) ⟨989225, by rfl⟩ : syracuseStep 1318967 = 1978451) B1978451
theorem B1482907 : Blo 876568 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B1319087 : Blo 876568 1319087 := bstep (se 1 (by rfl) ⟨989315, by rfl⟩ : syracuseStep 1319087 = 1978631) B1978631
theorem B1974455 : Blo 876568 1974455 := bstep (se 1 (by rfl) ⟨1480841, by rfl⟩ : syracuseStep 1974455 = 2961683) B2961683
theorem B1319291 : Blo 876568 1319291 := bstep (se 1 (by rfl) ⟨989468, by rfl⟩ : syracuseStep 1319291 = 1978937) B1978937
theorem B1253755 : Blo 876568 1253755 := bstep (se 1 (by rfl) ⟨940316, by rfl⟩ : syracuseStep 1253755 = 1880633) B1880633
theorem B2499103 : Blo 876568 2499103 := bstep (se 1 (by rfl) ⟨1874327, by rfl⟩ : syracuseStep 2499103 = 3748655) B3748655
theorem B1974815 : Blo 876568 1974815 := bstep (se 1 (by rfl) ⟨1481111, by rfl⟩ : syracuseStep 1974815 = 2962223) B2962223
theorem B1319465 : Blo 876568 1319465 := bstep (se 2 (by rfl) ⟨494799, by rfl⟩ : syracuseStep 1319465 = 989599) B989599
theorem B1319561 : Blo 876568 1319561 := bstep (se 2 (by rfl) ⟨494835, by rfl⟩ : syracuseStep 1319561 = 989671) B989671
theorem B4006567 : Blo 876568 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B1319771 : Blo 876568 1319771 := bstep (se 1 (by rfl) ⟨989828, by rfl⟩ : syracuseStep 1319771 = 1979657) B1979657
theorem B1319807 : Blo 876568 1319807 := bstep (se 1 (by rfl) ⟨989855, by rfl⟩ : syracuseStep 1319807 = 1979711) B1979711
theorem B1319879 : Blo 876568 1319879 := bstep (se 1 (by rfl) ⟨989909, by rfl⟩ : syracuseStep 1319879 = 1979819) B1979819
theorem B3744863 : Blo 876568 3744863 := bstep (se 1 (by rfl) ⟨2808647, by rfl⟩ : syracuseStep 3744863 = 5617295) B5617295
theorem B1975391 : Blo 876568 1975391 := bstep (se 1 (by rfl) ⟨1481543, by rfl⟩ : syracuseStep 1975391 = 2963087) B2963087
theorem B2958443 : Blo 876568 2958443 := bstep (se 1 (by rfl) ⟨2218832, by rfl⟩ : syracuseStep 2958443 = 4437665) B4437665
theorem B1320095 : Blo 876568 1320095 := bstep (se 1 (by rfl) ⟨990071, by rfl⟩ : syracuseStep 1320095 = 1980143) B1980143
theorem B1320239 : Blo 876568 1320239 := bstep (se 1 (by rfl) ⟨990179, by rfl⟩ : syracuseStep 1320239 = 1980359) B1980359
theorem B1975643 : Blo 876568 1975643 := bstep (se 1 (by rfl) ⟨1481732, by rfl⟩ : syracuseStep 1975643 = 2963465) B2963465
theorem B1320431 : Blo 876568 1320431 := bstep (se 1 (by rfl) ⟨990323, by rfl⟩ : syracuseStep 1320431 = 1980647) B1980647
theorem B1320443 : Blo 876568 1320443 := bstep (se 1 (by rfl) ⟨990332, by rfl⟩ : syracuseStep 1320443 = 1980665) B1980665
theorem B1320479 : Blo 876568 1320479 := bstep (se 1 (by rfl) ⟨990359, by rfl⟩ : syracuseStep 1320479 = 1980719) B1980719
theorem B1975913 : Blo 876568 1975913 := bstep (se 2 (by rfl) ⟨740967, by rfl⟩ : syracuseStep 1975913 = 1481935) B1481935
theorem B1320623 : Blo 876568 1320623 := bstep (se 1 (by rfl) ⟨990467, by rfl⟩ : syracuseStep 1320623 = 1980935) B1980935
theorem B1320713 : Blo 876568 1320713 := bstep (se 2 (by rfl) ⟨495267, by rfl⟩ : syracuseStep 1320713 = 990535) B990535
theorem B1320743 : Blo 876568 1320743 := bstep (se 1 (by rfl) ⟨990557, by rfl⟩ : syracuseStep 1320743 = 1981115) B1981115
theorem B1484615 : Blo 876568 1484615 := bstep (se 1 (by rfl) ⟨1113461, by rfl⟩ : syracuseStep 1484615 = 2226923) B2226923
theorem B1484635 : Blo 876568 1484635 := bstep (se 1 (by rfl) ⟨1113476, by rfl⟩ : syracuseStep 1484635 = 2226953) B2226953
theorem B6662087 : Blo 876568 6662087 := bstep (se 1 (by rfl) ⟨4996565, by rfl⟩ : syracuseStep 6662087 = 9993131) B9993131
theorem B1976543 : Blo 876568 1976543 := bstep (se 1 (by rfl) ⟨1482407, by rfl⟩ : syracuseStep 1976543 = 2964815) B2964815
theorem B1485607 : Blo 876568 1485607 := bstep (se 1 (by rfl) ⟨1114205, by rfl⟩ : syracuseStep 1485607 = 2228411) B2228411
theorem B3746999 : Blo 876568 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B19246313 : Blo 876568 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B36547949 : Blo 876568 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B12660475 : Blo 876568 12660475 := bstep (se 1 (by rfl) ⟨9495356, by rfl⟩ : syracuseStep 12660475 = 18990713) B18990713
theorem B4993103 : Blo 876568 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B3748639 : Blo 876568 3748639 := bstep (se 1 (by rfl) ⟨2811479, by rfl⟩ : syracuseStep 3748639 = 5622959) B5622959
theorem B2503705 : Blo 876568 2503705 := bstep (se 2 (by rfl) ⟨938889, by rfl⟩ : syracuseStep 2503705 = 1877779) B1877779
theorem B2504047 : Blo 876568 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B6665975 : Blo 876568 6665975 := bstep (se 1 (by rfl) ⟨4999481, by rfl⟩ : syracuseStep 6665975 = 9998963) B9998963
theorem B1980395 : Blo 876568 1980395 := bstep (se 1 (by rfl) ⟨1485296, by rfl⟩ : syracuseStep 1980395 = 2970593) B2970593
theorem B14268467 : Blo 876568 14268467 := bstep (se 1 (by rfl) ⟨10701350, by rfl⟩ : syracuseStep 14268467 = 21402701) B21402701
theorem B2963519 : Blo 876568 2963519 := bstep (se 1 (by rfl) ⟨2222639, by rfl⟩ : syracuseStep 2963519 = 4445279) B4445279
theorem B5618267 : Blo 876568 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B5618321 : Blo 876568 5618321 := bstep (se 2 (by rfl) ⟨2106870, by rfl⟩ : syracuseStep 5618321 = 4213741) B4213741
theorem B12663823 : Blo 876568 12663823 := bstep (se 1 (by rfl) ⟨9497867, by rfl⟩ : syracuseStep 12663823 = 18995735) B18995735
theorem B4996201 : Blo 876568 4996201 := bstep (se 2 (by rfl) ⟨1873575, by rfl⟩ : syracuseStep 4996201 = 3747151) B3747151
theorem B2964761 : Blo 876568 2964761 := bstep (se 2 (by rfl) ⟨1111785, by rfl⟩ : syracuseStep 2964761 = 2223571) B2223571
theorem B2112809 : Blo 876568 2112809 := bstep (se 2 (by rfl) ⟨792303, by rfl⟩ : syracuseStep 2112809 = 1584607) B1584607
theorem B91471169 : Blo 876568 91471169 := bstep (se 2 (by rfl) ⟨34301688, by rfl⟩ : syracuseStep 91471169 = 68603377) B68603377
theorem B4439609 : Blo 876568 4439609 := bstep (se 2 (by rfl) ⟨1664853, by rfl⟩ : syracuseStep 4439609 = 3329707) B3329707
theorem B5619395 : Blo 876568 5619395 := bstep (se 1 (by rfl) ⟨4214546, by rfl⟩ : syracuseStep 5619395 = 8429093) B8429093
theorem B4439771 : Blo 876568 4439771 := bstep (se 1 (by rfl) ⟨3329828, by rfl⟩ : syracuseStep 4439771 = 6659657) B6659657
theorem B10010627 : Blo 876568 10010627 := bstep (se 1 (by rfl) ⟨7507970, by rfl⟩ : syracuseStep 10010627 = 15015941) B15015941
theorem B4997159 : Blo 876568 4997159 := bstep (se 1 (by rfl) ⟨3747869, by rfl⟩ : syracuseStep 4997159 = 7495739) B7495739
theorem B32130037 : Blo 876568 32130037 := bstep (se 5 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 32130037 = 3012191) B3012191
theorem B3753287 : Blo 876568 3753287 := bstep (se 1 (by rfl) ⟨2814965, by rfl⟩ : syracuseStep 3753287 = 5629931) B5629931
theorem B2377127 : Blo 876568 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B4999643 : Blo 876568 4999643 := bstep (se 1 (by rfl) ⟨3749732, by rfl⟩ : syracuseStep 4999643 = 7499465) B7499465
theorem B3328553 : Blo 876568 3328553 := bstep (se 2 (by rfl) ⟨1248207, by rfl⟩ : syracuseStep 3328553 = 2496415) B2496415
theorem B81154001 : Blo 876568 81154001 := bstep (se 2 (by rfl) ⟨30432750, by rfl⟩ : syracuseStep 81154001 = 60865501) B60865501
theorem B4509857 : Blo 876568 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B7622849 : Blo 876568 7622849 := bstep (se 2 (by rfl) ⟨2858568, by rfl⟩ : syracuseStep 7622849 = 5717137) B5717137
theorem B162222365 : Blo 876568 162222365 := bstep (se 3 (by rfl) ⟨30416693, by rfl⟩ : syracuseStep 162222365 = 60833387) B60833387
theorem B51433865 : Blo 876568 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B19026353 : Blo 876568 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B4739897 : Blo 876568 4739897 := bstep (se 2 (by rfl) ⟨1777461, by rfl⟩ : syracuseStep 4739897 = 3554923) B3554923
theorem B2970431 : Blo 876568 2970431 := bstep (se 1 (by rfl) ⟨2227823, by rfl⟩ : syracuseStep 2970431 = 4455647) B4455647
theorem B3330983 : Blo 876568 3330983 := bstep (se 1 (by rfl) ⟨2498237, by rfl⟩ : syracuseStep 3330983 = 4996475) B4996475
theorem B13686245 : Blo 876568 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B4446089 : Blo 876568 4446089 := bstep (se 2 (by rfl) ⟨1667283, by rfl⟩ : syracuseStep 4446089 = 3334567) B3334567
theorem B2971835 : Blo 876568 2971835 := bstep (se 1 (by rfl) ⟨2228876, by rfl⟩ : syracuseStep 2971835 = 4457753) B4457753
theorem B2808263 : Blo 876568 2808263 := bstep (se 1 (by rfl) ⟨2106197, by rfl⟩ : syracuseStep 2808263 = 4212395) B4212395
theorem B4807421 : Blo 876568 4807421 := bstep (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) B1802783
theorem B3759043 : Blo 876568 3759043 := bstep (se 1 (by rfl) ⟨2819282, by rfl⟩ : syracuseStep 3759043 = 5638565) B5638565
theorem B2809019 : Blo 876568 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B38657821 : Blo 876568 38657821 := bstep (se 3 (by rfl) ⟨7248341, by rfl⟩ : syracuseStep 38657821 = 14496683) B14496683
theorem B2219987 : Blo 876568 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B876607 : Blo 876568 876607 := bstep (se 1 (by rfl) ⟨657455, by rfl⟩ : syracuseStep 876607 = 1314911) B1314911
theorem B876615 : Blo 876568 876615 := bstep (se 1 (by rfl) ⟨657461, by rfl⟩ : syracuseStep 876615 = 1314923) B1314923
theorem B876647 : Blo 876568 876647 := bstep (se 1 (by rfl) ⟨657485, by rfl⟩ : syracuseStep 876647 = 1314971) B1314971
theorem B2810045 : Blo 876568 2810045 := bstep (se 3 (by rfl) ⟨526883, by rfl⟩ : syracuseStep 2810045 = 1053767) B1053767
theorem B3760343 : Blo 876568 3760343 := bstep (se 1 (by rfl) ⟨2820257, by rfl⟩ : syracuseStep 3760343 = 5640515) B5640515
theorem B877215 : Blo 876568 877215 := bstep (se 1 (by rfl) ⟨657911, by rfl⟩ : syracuseStep 877215 = 1315823) B1315823
theorem B877471 : Blo 876568 877471 := bstep (se 1 (by rfl) ⟨658103, by rfl⟩ : syracuseStep 877471 = 1316207) B1316207
theorem B1336223 : Blo 876568 1336223 := bstep (se 1 (by rfl) ⟨1002167, by rfl⟩ : syracuseStep 1336223 = 2004335) B2004335
theorem B877551 : Blo 876568 877551 := bstep (se 1 (by rfl) ⟨658163, by rfl⟩ : syracuseStep 877551 = 1316327) B1316327
theorem B877659 : Blo 876568 877659 := bstep (se 1 (by rfl) ⟨658244, by rfl⟩ : syracuseStep 877659 = 1316489) B1316489
theorem B877671 : Blo 876568 877671 := bstep (se 1 (by rfl) ⟨658253, by rfl⟩ : syracuseStep 877671 = 1316507) B1316507
theorem B877799 : Blo 876568 877799 := bstep (se 1 (by rfl) ⟨658349, by rfl⟩ : syracuseStep 877799 = 1316699) B1316699
theorem B5334427 : Blo 876568 5334427 := bstep (se 1 (by rfl) ⟨4000820, by rfl⟩ : syracuseStep 5334427 = 8001641) B8001641
theorem B878055 : Blo 876568 878055 := bstep (se 1 (by rfl) ⟨658541, by rfl⟩ : syracuseStep 878055 = 1317083) B1317083
theorem B878235 : Blo 876568 878235 := bstep (se 1 (by rfl) ⟨658676, by rfl⟩ : syracuseStep 878235 = 1317353) B1317353
theorem B878495 : Blo 876568 878495 := bstep (se 1 (by rfl) ⟨658871, by rfl⟩ : syracuseStep 878495 = 1317743) B1317743
theorem B878503 : Blo 876568 878503 := bstep (se 1 (by rfl) ⟨658877, by rfl⟩ : syracuseStep 878503 = 1317755) B1317755
theorem B2254895 : Blo 876568 2254895 := bstep (se 1 (by rfl) ⟨1691171, by rfl⟩ : syracuseStep 2254895 = 3382343) B3382343
theorem B18016505 : Blo 876568 18016505 := bstep (se 2 (by rfl) ⟨6756189, by rfl⟩ : syracuseStep 18016505 = 13512379) B13512379
theorem B19261739 : Blo 876568 19261739 := bstep (se 1 (by rfl) ⟨14446304, by rfl⟩ : syracuseStep 19261739 = 28892609) B28892609
theorem B879079 : Blo 876568 879079 := bstep (se 1 (by rfl) ⟨659309, by rfl⟩ : syracuseStep 879079 = 1318619) B1318619
theorem B879259 : Blo 876568 879259 := bstep (se 1 (by rfl) ⟨659444, by rfl⟩ : syracuseStep 879259 = 1318889) B1318889
theorem B4745951 : Blo 876568 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B2222873 : Blo 876568 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B146402153 : Blo 876568 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B879727 : Blo 876568 879727 := bstep (se 1 (by rfl) ⟨659795, by rfl⟩ : syracuseStep 879727 = 1319591) B1319591
theorem B37973123 : Blo 876568 37973123 := bstep (se 1 (by rfl) ⟨28479842, by rfl⟩ : syracuseStep 37973123 = 56959685) B56959685
theorem B879807 : Blo 876568 879807 := bstep (se 1 (by rfl) ⟨659855, by rfl⟩ : syracuseStep 879807 = 1319711) B1319711
theorem B879823 : Blo 876568 879823 := bstep (se 1 (by rfl) ⟨659867, by rfl⟩ : syracuseStep 879823 = 1319735) B1319735
theorem B879943 : Blo 876568 879943 := bstep (se 1 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 879943 = 1319915) B1319915
theorem B5631443 : Blo 876568 5631443 := bstep (se 1 (by rfl) ⟨4223582, by rfl⟩ : syracuseStep 5631443 = 8447165) B8447165
theorem B5336857 : Blo 876568 5336857 := bstep (se 2 (by rfl) ⟨2001321, by rfl⟩ : syracuseStep 5336857 = 4002643) B4002643
theorem B1110343 : Blo 876568 1110343 := bstep (se 1 (by rfl) ⟨832757, by rfl⟩ : syracuseStep 1110343 = 1665515) B1665515
theorem B7500113 : Blo 876568 7500113 := bstep (se 2 (by rfl) ⟨2812542, by rfl⟩ : syracuseStep 7500113 = 5625085) B5625085
theorem B11268517 : Blo 876568 11268517 := bstep (se 4 (by rfl) ⟨1056423, by rfl⟩ : syracuseStep 11268517 = 2112847) B2112847
theorem B11727523 : Blo 876568 11727523 := bstep (se 1 (by rfl) ⟨8795642, by rfl⟩ : syracuseStep 11727523 = 17591285) B17591285
theorem B43381511 : Blo 876568 43381511 := bstep (se 1 (by rfl) ⟨32536133, by rfl⟩ : syracuseStep 43381511 = 65072267) B65072267
theorem B3568481 : Blo 876568 3568481 := bstep (se 2 (by rfl) ⟨1338180, by rfl⟩ : syracuseStep 3568481 = 2676361) B2676361
theorem B2814875 : Blo 876568 2814875 := bstep (se 1 (by rfl) ⟨2111156, by rfl⟩ : syracuseStep 2814875 = 4222313) B4222313
theorem B1111087 : Blo 876568 1111087 := bstep (se 1 (by rfl) ⟨833315, by rfl⟩ : syracuseStep 1111087 = 1666631) B1666631
theorem B3339913 : Blo 876568 3339913 := bstep (se 2 (by rfl) ⟨1252467, by rfl⟩ : syracuseStep 3339913 = 2504935) B2504935
theorem B2225951 : Blo 876568 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B1112059 : Blo 876568 1112059 := bstep (se 1 (by rfl) ⟨834044, by rfl⟩ : syracuseStep 1112059 = 1668089) B1668089
theorem B1112231 : Blo 876568 1112231 := bstep (se 1 (by rfl) ⟨834173, by rfl⟩ : syracuseStep 1112231 = 1668347) B1668347
theorem B2226487 : Blo 876568 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B1112555 : Blo 876568 1112555 := bstep (se 1 (by rfl) ⟨834416, by rfl⟩ : syracuseStep 1112555 = 1668833) B1668833
theorem B3340871 : Blo 876568 3340871 := bstep (se 1 (by rfl) ⟨2505653, by rfl⟩ : syracuseStep 3340871 = 5011307) B5011307
theorem B4225679 : Blo 876568 4225679 := bstep (se 1 (by rfl) ⟨3169259, by rfl⟩ : syracuseStep 4225679 = 6338519) B6338519
theorem B36142013 : Blo 876568 36142013 := bstep (se 3 (by rfl) ⟨6776627, by rfl⟩ : syracuseStep 36142013 = 13553255) B13553255
theorem B5635079 : Blo 876568 5635079 := bstep (se 1 (by rfl) ⟨4226309, by rfl⟩ : syracuseStep 5635079 = 8452619) B8452619
theorem B4226195 : Blo 876568 4226195 := bstep (se 1 (by rfl) ⟨3169646, by rfl⟩ : syracuseStep 4226195 = 6339293) B6339293
theorem B1408411 : Blo 876568 1408411 := bstep (se 1 (by rfl) ⟨1056308, by rfl⟩ : syracuseStep 1408411 = 2112617) B2112617
theorem B1113583 : Blo 876568 1113583 := bstep (se 1 (by rfl) ⟨835187, by rfl⟩ : syracuseStep 1113583 = 1670375) B1670375
theorem B1670777 : Blo 876568 1670777 := bstep (se 2 (by rfl) ⟨626541, by rfl⟩ : syracuseStep 1670777 = 1253083) B1253083
theorem B3210877 : Blo 876568 3210877 := bstep (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) B1204079
theorem B2227895 : Blo 876568 2227895 := bstep (se 1 (by rfl) ⟨1670921, by rfl⟩ : syracuseStep 2227895 = 3341843) B3341843
theorem B2228107 : Blo 876568 2228107 := bstep (se 1 (by rfl) ⟨1671080, by rfl⟩ : syracuseStep 2228107 = 3342161) B3342161
theorem B6422921 : Blo 876568 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B3342815 : Blo 876568 3342815 := bstep (se 1 (by rfl) ⟨2507111, by rfl⟩ : syracuseStep 3342815 = 5014223) B5014223
theorem B1671673 : Blo 876568 1671673 := bstep (se 2 (by rfl) ⟨626877, by rfl⟩ : syracuseStep 1671673 = 1253755) B1253755
theorem B6423151 : Blo 876568 6423151 := bstep (se 1 (by rfl) ⟨4817363, by rfl⟩ : syracuseStep 6423151 = 9634727) B9634727
theorem B8454851 : Blo 876568 8454851 := bstep (se 1 (by rfl) ⟨6341138, by rfl⟩ : syracuseStep 8454851 = 12682277) B12682277
theorem B7112569 : Blo 876568 7112569 := bstep (se 2 (by rfl) ⟨2667213, by rfl⟩ : syracuseStep 7112569 = 5334427) B5334427
theorem B54102667 : Blo 876568 54102667 := bstep (se 1 (by rfl) ⟨40577000, by rfl⟩ : syracuseStep 54102667 = 81154001) B81154001
theorem B12684235 : Blo 876568 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B986143 : Blo 876568 986143 := bstep (se 1 (by rfl) ⟨739607, by rfl⟩ : syracuseStep 986143 = 1479215) B1479215
theorem B986575 : Blo 876568 986575 := bstep (se 1 (by rfl) ⟨739931, by rfl⟩ : syracuseStep 986575 = 1479863) B1479863
theorem B21368357 : Blo 876568 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B2167067 : Blo 876568 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B1872175 : Blo 876568 1872175 := bstep (se 1 (by rfl) ⟨1404131, by rfl⟩ : syracuseStep 1872175 = 2808263) B2808263
theorem B1315355 : Blo 876568 1315355 := bstep (se 1 (by rfl) ⟨986516, by rfl⟩ : syracuseStep 1315355 = 1973033) B1973033
theorem B1315535 : Blo 876568 1315535 := bstep (se 1 (by rfl) ⟨986651, by rfl⟩ : syracuseStep 1315535 = 1973303) B1973303
theorem B16880633 : Blo 876568 16880633 := bstep (se 2 (by rfl) ⟨6330237, by rfl⟩ : syracuseStep 16880633 = 12660475) B12660475
theorem B5706875 : Blo 876568 5706875 := bstep (se 1 (by rfl) ⟨4280156, by rfl⟩ : syracuseStep 5706875 = 8560313) B8560313
theorem B1316063 : Blo 876568 1316063 := bstep (se 1 (by rfl) ⟨987047, by rfl⟩ : syracuseStep 1316063 = 1974095) B1974095
theorem B1479991 : Blo 876568 1479991 := bstep (se 1 (by rfl) ⟨1109993, by rfl⟩ : syracuseStep 1479991 = 2219987) B2219987
theorem B1316303 : Blo 876568 1316303 := bstep (se 1 (by rfl) ⟨987227, by rfl⟩ : syracuseStep 1316303 = 1974455) B1974455
theorem B1873363 : Blo 876568 1873363 := bstep (se 1 (by rfl) ⟨1405022, by rfl⟩ : syracuseStep 1873363 = 2810045) B2810045
theorem B1316543 : Blo 876568 1316543 := bstep (se 1 (by rfl) ⟨987407, by rfl⟩ : syracuseStep 1316543 = 1974815) B1974815
theorem B1480457 : Blo 876568 1480457 := bstep (se 2 (by rfl) ⟨555171, by rfl⟩ : syracuseStep 1480457 = 1110343) B1110343
theorem B2496575 : Blo 876568 2496575 := bstep (se 1 (by rfl) ⟨1872431, by rfl⟩ : syracuseStep 2496575 = 3744863) B3744863
theorem B1316927 : Blo 876568 1316927 := bstep (se 1 (by rfl) ⟨987695, by rfl⟩ : syracuseStep 1316927 = 1975391) B1975391
theorem B1972295 : Blo 876568 1972295 := bstep (se 1 (by rfl) ⟨1479221, by rfl⟩ : syracuseStep 1972295 = 2958443) B2958443
theorem B1317095 : Blo 876568 1317095 := bstep (se 1 (by rfl) ⟨987821, by rfl⟩ : syracuseStep 1317095 = 1975643) B1975643
theorem B1317275 : Blo 876568 1317275 := bstep (se 1 (by rfl) ⟨987956, by rfl⟩ : syracuseStep 1317275 = 1975913) B1975913
theorem B989743 : Blo 876568 989743 := bstep (se 1 (by rfl) ⟨742307, by rfl⟩ : syracuseStep 989743 = 1484615) B1484615
theorem B1481449 : Blo 876568 1481449 := bstep (se 2 (by rfl) ⟨555543, by rfl⟩ : syracuseStep 1481449 = 1111087) B1111087
theorem B1317695 : Blo 876568 1317695 := bstep (se 1 (by rfl) ⟨988271, by rfl⟩ : syracuseStep 1317695 = 1976543) B1976543
theorem B1481915 : Blo 876568 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B2497999 : Blo 876568 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B7511525 : Blo 876568 7511525 := bstep (se 4 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 7511525 = 1408411) B1408411
theorem B1482745 : Blo 876568 1482745 := bstep (se 2 (by rfl) ⟨556029, by rfl⟩ : syracuseStep 1482745 = 1112059) B1112059
theorem B1876583 : Blo 876568 1876583 := bstep (se 1 (by rfl) ⟨1407437, by rfl⟩ : syracuseStep 1876583 = 2814875) B2814875
theorem B2499457 : Blo 876568 2499457 := bstep (se 2 (by rfl) ⟨937296, by rfl⟩ : syracuseStep 2499457 = 1874593) B1874593
theorem B1483967 : Blo 876568 1483967 := bstep (se 1 (by rfl) ⟨1112975, by rfl⟩ : syracuseStep 1483967 = 2225951) B2225951
theorem B1320263 : Blo 876568 1320263 := bstep (se 1 (by rfl) ⟨990197, by rfl⟩ : syracuseStep 1320263 = 1980395) B1980395
theorem B16885097 : Blo 876568 16885097 := bstep (se 2 (by rfl) ⟨6331911, by rfl⟩ : syracuseStep 16885097 = 12663823) B12663823
theorem B9512311 : Blo 876568 9512311 := bstep (se 1 (by rfl) ⟨7134233, by rfl⟩ : syracuseStep 9512311 = 14268467) B14268467
theorem B1975679 : Blo 876568 1975679 := bstep (se 1 (by rfl) ⟨1481759, by rfl⟩ : syracuseStep 1975679 = 2963519) B2963519
theorem B6661601 : Blo 876568 6661601 := bstep (se 2 (by rfl) ⟨2498100, by rfl⟩ : syracuseStep 6661601 = 4996201) B4996201
theorem B3745511 : Blo 876568 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B3745547 : Blo 876568 3745547 := bstep (se 1 (by rfl) ⟨2809160, by rfl⟩ : syracuseStep 3745547 = 5618321) B5618321
theorem B24094675 : Blo 876568 24094675 := bstep (se 1 (by rfl) ⟨18071006, by rfl⟩ : syracuseStep 24094675 = 36142013) B36142013
theorem B1484777 : Blo 876568 1484777 := bstep (se 2 (by rfl) ⟨556791, by rfl⟩ : syracuseStep 1484777 = 1113583) B1113583
theorem B1976507 : Blo 876568 1976507 := bstep (se 1 (by rfl) ⟨1482380, by rfl⟩ : syracuseStep 1976507 = 2964761) B2964761
theorem B2959739 : Blo 876568 2959739 := bstep (se 1 (by rfl) ⟨2219804, by rfl⟩ : syracuseStep 2959739 = 4439609) B4439609
theorem B1485263 : Blo 876568 1485263 := bstep (se 1 (by rfl) ⟨1113947, by rfl⟩ : syracuseStep 1485263 = 2227895) B2227895
theorem B3746263 : Blo 876568 3746263 := bstep (se 1 (by rfl) ⟨2809697, by rfl⟩ : syracuseStep 3746263 = 5619395) B5619395
theorem B2959847 : Blo 876568 2959847 := bstep (se 1 (by rfl) ⟨2219885, by rfl⟩ : syracuseStep 2959847 = 4439771) B4439771
theorem B1977209 : Blo 876568 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B20327597 : Blo 876568 20327597 := bstep (se 3 (by rfl) ⟨3811424, by rfl⟩ : syracuseStep 20327597 = 7622849) B7622849
theorem B7515625 : Blo 876568 7515625 := bstep (se 2 (by rfl) ⟨2818359, by rfl⟩ : syracuseStep 7515625 = 5636719) B5636719
theorem B2502191 : Blo 876568 2502191 := bstep (se 1 (by rfl) ⟨1876643, by rfl⟩ : syracuseStep 2502191 = 3753287) B3753287
theorem B47984237 : Blo 876568 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B42840049 : Blo 876568 42840049 := bstep (se 2 (by rfl) ⟨16065018, by rfl⟩ : syracuseStep 42840049 = 32130037) B32130037
theorem B1979513 : Blo 876568 1979513 := bstep (se 2 (by rfl) ⟨742317, by rfl⟩ : syracuseStep 1979513 = 1484635) B1484635
theorem B108148243 : Blo 876568 108148243 := bstep (se 1 (by rfl) ⟨81111182, by rfl⟩ : syracuseStep 108148243 = 162222365) B162222365
theorem B34289243 : Blo 876568 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B3159931 : Blo 876568 3159931 := bstep (se 1 (by rfl) ⟨2369948, by rfl⟩ : syracuseStep 3159931 = 4739897) B4739897
theorem B1980287 : Blo 876568 1980287 := bstep (se 1 (by rfl) ⟨1485215, by rfl⟩ : syracuseStep 1980287 = 2970431) B2970431
theorem B9124163 : Blo 876568 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B1980809 : Blo 876568 1980809 := bstep (se 2 (by rfl) ⟨742803, by rfl⟩ : syracuseStep 1980809 = 1485607) B1485607
theorem B6339005 : Blo 876568 6339005 := bstep (se 3 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 6339005 = 2377127) B2377127
theorem B7125479 : Blo 876568 7125479 := bstep (se 1 (by rfl) ⟨5344109, by rfl⟩ : syracuseStep 7125479 = 10688219) B10688219
theorem B2964059 : Blo 876568 2964059 := bstep (se 1 (by rfl) ⟨2223044, by rfl⟩ : syracuseStep 2964059 = 4446089) B4446089
theorem B1981223 : Blo 876568 1981223 := bstep (se 1 (by rfl) ⟨1485917, by rfl⟩ : syracuseStep 1981223 = 2971835) B2971835
theorem B18005327 : Blo 876568 18005327 := bstep (se 1 (by rfl) ⟨13503995, by rfl⟩ : syracuseStep 18005327 = 27007991) B27007991
theorem B2506895 : Blo 876568 2506895 := bstep (se 1 (by rfl) ⟨1880171, by rfl⟩ : syracuseStep 2506895 = 3760343) B3760343
theorem B2965949 : Blo 876568 2965949 := bstep (se 3 (by rfl) ⟨556115, by rfl⟩ : syracuseStep 2965949 = 1112231) B1112231
theorem B15024689 : Blo 876568 15024689 := bstep (se 2 (by rfl) ⟨5634258, by rfl⟩ : syracuseStep 15024689 = 11268517) B11268517
theorem B7520957 : Blo 876568 7520957 := bstep (se 3 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 7520957 = 2820359) B2820359
theorem B4998185 : Blo 876568 4998185 := bstep (se 2 (by rfl) ⟨1874319, by rfl⟩ : syracuseStep 4998185 = 3748639) B3748639
theorem B2966813 : Blo 876568 2966813 := bstep (se 3 (by rfl) ⟨556277, by rfl⟩ : syracuseStep 2966813 = 1112555) B1112555
theorem B4441391 : Blo 876568 4441391 := bstep (se 1 (by rfl) ⟨3331043, by rfl⟩ : syracuseStep 4441391 = 6662087) B6662087
theorem B12011003 : Blo 876568 12011003 := bstep (se 1 (by rfl) ⟨9008252, by rfl⟩ : syracuseStep 12011003 = 18016505) B18016505
theorem B3163967 : Blo 876568 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B97601435 : Blo 876568 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B25315415 : Blo 876568 25315415 := bstep (se 1 (by rfl) ⟨18986561, by rfl⟩ : syracuseStep 25315415 = 37973123) B37973123
theorem B12830875 : Blo 876568 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B24365299 : Blo 876568 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B3754295 : Blo 876568 3754295 := bstep (se 1 (by rfl) ⟨2815721, by rfl⟩ : syracuseStep 3754295 = 5631443) B5631443
theorem B3328735 : Blo 876568 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B5000075 : Blo 876568 5000075 := bstep (se 1 (by rfl) ⟨3750056, by rfl⟩ : syracuseStep 5000075 = 7500113) B7500113
theorem B2968649 : Blo 876568 2968649 := bstep (se 2 (by rfl) ⟨1113243, by rfl⟩ : syracuseStep 2968649 = 2226487) B2226487
theorem B7490717 : Blo 876568 7490717 := bstep (se 3 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 7490717 = 2809019) B2809019
theorem B28921007 : Blo 876568 28921007 := bstep (se 1 (by rfl) ⟨21690755, by rfl⟩ : syracuseStep 28921007 = 43381511) B43381511
theorem B2378987 : Blo 876568 2378987 := bstep (se 1 (by rfl) ⟨1784240, by rfl⟩ : syracuseStep 2378987 = 3568481) B3568481
theorem B4443983 : Blo 876568 4443983 := bstep (se 1 (by rfl) ⟨3332987, by rfl⟩ : syracuseStep 4443983 = 6665975) B6665975
theorem B28463237 : Blo 876568 28463237 := bstep (se 4 (by rfl) ⟨2668428, by rfl⟩ : syracuseStep 28463237 = 5336857) B5336857
theorem B3756719 : Blo 876568 3756719 := bstep (se 1 (by rfl) ⟨2817539, by rfl⟩ : syracuseStep 3756719 = 5635079) B5635079
theorem B4281169 : Blo 876568 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B2970809 : Blo 876568 2970809 := bstep (se 2 (by rfl) ⟨1114053, by rfl⟩ : syracuseStep 2970809 = 2228107) B2228107
theorem B6673751 : Blo 876568 6673751 := bstep (se 1 (by rfl) ⟨5005313, by rfl⟩ : syracuseStep 6673751 = 10010627) B10010627
theorem B3331439 : Blo 876568 3331439 := bstep (se 1 (by rfl) ⟨2498579, by rfl⟩ : syracuseStep 3331439 = 4997159) B4997159
theorem B3332137 : Blo 876568 3332137 := bstep (se 2 (by rfl) ⟨1249551, by rfl⟩ : syracuseStep 3332137 = 2499103) B2499103
theorem B3333095 : Blo 876568 3333095 := bstep (se 1 (by rfl) ⟨2499821, by rfl⟩ : syracuseStep 3333095 = 4999643) B4999643
theorem B2219035 : Blo 876568 2219035 := bstep (se 1 (by rfl) ⟨1664276, by rfl⟩ : syracuseStep 2219035 = 3328553) B3328553
theorem B3563261 : Blo 876568 3563261 := bstep (se 3 (by rfl) ⟨668111, by rfl⟩ : syracuseStep 3563261 = 1336223) B1336223
theorem B3006571 : Blo 876568 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B876671 : Blo 876568 876671 := bstep (se 1 (by rfl) ⟨657503, by rfl⟩ : syracuseStep 876671 = 1315007) B1315007
theorem B876699 : Blo 876568 876699 := bstep (se 1 (by rfl) ⟨657524, by rfl⟩ : syracuseStep 876699 = 1315049) B1315049
theorem B876783 : Blo 876568 876783 := bstep (se 1 (by rfl) ⟨657587, by rfl⟩ : syracuseStep 876783 = 1315175) B1315175
theorem B5005907 : Blo 876568 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B2220655 : Blo 876568 2220655 := bstep (se 1 (by rfl) ⟨1665491, by rfl⟩ : syracuseStep 2220655 = 3330983) B3330983
theorem B877339 : Blo 876568 877339 := bstep (se 1 (by rfl) ⟨658004, by rfl⟩ : syracuseStep 877339 = 1316009) B1316009
theorem B877383 : Blo 876568 877383 := bstep (se 1 (by rfl) ⟨658037, by rfl⟩ : syracuseStep 877383 = 1316075) B1316075
theorem B62546789 : Blo 876568 62546789 := bstep (se 4 (by rfl) ⟨5863761, by rfl⟩ : syracuseStep 62546789 = 11727523) B11727523
theorem B877439 : Blo 876568 877439 := bstep (se 1 (by rfl) ⟨658079, by rfl⟩ : syracuseStep 877439 = 1316159) B1316159
theorem B877567 : Blo 876568 877567 := bstep (se 1 (by rfl) ⟨658175, by rfl⟩ : syracuseStep 877567 = 1316351) B1316351
theorem B8021051 : Blo 876568 8021051 := bstep (se 1 (by rfl) ⟨6015788, by rfl⟩ : syracuseStep 8021051 = 12031577) B12031577
theorem B877639 : Blo 876568 877639 := bstep (se 1 (by rfl) ⟨658229, by rfl⟩ : syracuseStep 877639 = 1316459) B1316459
theorem B5006407 : Blo 876568 5006407 := bstep (se 1 (by rfl) ⟨3754805, by rfl⟩ : syracuseStep 5006407 = 7509611) B7509611
theorem B877819 : Blo 876568 877819 := bstep (se 1 (by rfl) ⟨658364, by rfl⟩ : syracuseStep 877819 = 1316729) B1316729
theorem B877983 : Blo 876568 877983 := bstep (se 1 (by rfl) ⟨658487, by rfl⟩ : syracuseStep 877983 = 1316975) B1316975
theorem B878031 : Blo 876568 878031 := bstep (se 1 (by rfl) ⟨658523, by rfl⟩ : syracuseStep 878031 = 1317047) B1317047
theorem B1664543 : Blo 876568 1664543 := bstep (se 1 (by rfl) ⟨1248407, by rfl⟩ : syracuseStep 1664543 = 2496815) B2496815
theorem B3565171 : Blo 876568 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B878311 : Blo 876568 878311 := bstep (se 1 (by rfl) ⟨658733, by rfl⟩ : syracuseStep 878311 = 1317467) B1317467
theorem B878319 : Blo 876568 878319 := bstep (se 1 (by rfl) ⟨658739, by rfl⟩ : syracuseStep 878319 = 1317479) B1317479
theorem B878335 : Blo 876568 878335 := bstep (se 1 (by rfl) ⟨658751, by rfl⟩ : syracuseStep 878335 = 1317503) B1317503
theorem B878407 : Blo 876568 878407 := bstep (se 1 (by rfl) ⟨658805, by rfl⟩ : syracuseStep 878407 = 1317611) B1317611
theorem B3204947 : Blo 876568 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B27813719 : Blo 876568 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B878427 : Blo 876568 878427 := bstep (se 1 (by rfl) ⟨658820, by rfl⟩ : syracuseStep 878427 = 1317641) B1317641
theorem B878587 : Blo 876568 878587 := bstep (se 1 (by rfl) ⟨658940, by rfl⟩ : syracuseStep 878587 = 1317881) B1317881
theorem B879007 : Blo 876568 879007 := bstep (se 1 (by rfl) ⟨659255, by rfl⟩ : syracuseStep 879007 = 1318511) B1318511
theorem B2255339 : Blo 876568 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B879087 : Blo 876568 879087 := bstep (se 1 (by rfl) ⟨659315, by rfl⟩ : syracuseStep 879087 = 1318631) B1318631
theorem B1665697 : Blo 876568 1665697 := bstep (se 2 (by rfl) ⟨624636, by rfl⟩ : syracuseStep 1665697 = 1249273) B1249273
theorem B879271 : Blo 876568 879271 := bstep (se 1 (by rfl) ⟨659453, by rfl⟩ : syracuseStep 879271 = 1318907) B1318907
theorem B879311 : Blo 876568 879311 := bstep (se 1 (by rfl) ⟨659483, by rfl⟩ : syracuseStep 879311 = 1318967) B1318967
theorem B879391 : Blo 876568 879391 := bstep (se 1 (by rfl) ⟨659543, by rfl⟩ : syracuseStep 879391 = 1319087) B1319087
theorem B879527 : Blo 876568 879527 := bstep (se 1 (by rfl) ⟨659645, by rfl⟩ : syracuseStep 879527 = 1319291) B1319291
theorem B879643 : Blo 876568 879643 := bstep (se 1 (by rfl) ⟨659732, by rfl⟩ : syracuseStep 879643 = 1319465) B1319465
theorem B879707 : Blo 876568 879707 := bstep (se 1 (by rfl) ⟨659780, by rfl⟩ : syracuseStep 879707 = 1319561) B1319561
theorem B879847 : Blo 876568 879847 := bstep (se 1 (by rfl) ⟨659885, by rfl⟩ : syracuseStep 879847 = 1319771) B1319771
theorem B879871 : Blo 876568 879871 := bstep (se 1 (by rfl) ⟨659903, by rfl⟩ : syracuseStep 879871 = 1319807) B1319807
theorem B879919 : Blo 876568 879919 := bstep (se 1 (by rfl) ⟨659939, by rfl⟩ : syracuseStep 879919 = 1319879) B1319879
theorem B880063 : Blo 876568 880063 := bstep (se 1 (by rfl) ⟨660047, by rfl⟩ : syracuseStep 880063 = 1320095) B1320095
theorem B880159 : Blo 876568 880159 := bstep (se 1 (by rfl) ⟨660119, by rfl⟩ : syracuseStep 880159 = 1320239) B1320239
theorem B880287 : Blo 876568 880287 := bstep (se 1 (by rfl) ⟨660215, by rfl⟩ : syracuseStep 880287 = 1320431) B1320431
theorem B880295 : Blo 876568 880295 := bstep (se 1 (by rfl) ⟨660221, by rfl⟩ : syracuseStep 880295 = 1320443) B1320443
theorem B880319 : Blo 876568 880319 := bstep (se 1 (by rfl) ⟨660239, by rfl⟩ : syracuseStep 880319 = 1320479) B1320479
theorem B880415 : Blo 876568 880415 := bstep (se 1 (by rfl) ⟨660311, by rfl⟩ : syracuseStep 880415 = 1320623) B1320623
theorem B880475 : Blo 876568 880475 := bstep (se 1 (by rfl) ⟨660356, by rfl⟩ : syracuseStep 880475 = 1320713) B1320713
theorem B880495 : Blo 876568 880495 := bstep (se 1 (by rfl) ⟨660371, by rfl⟩ : syracuseStep 880495 = 1320743) B1320743
theorem B1503263 : Blo 876568 1503263 := bstep (se 1 (by rfl) ⟨1127447, by rfl⟩ : syracuseStep 1503263 = 2254895) B2254895
theorem B3338273 : Blo 876568 3338273 := bstep (se 2 (by rfl) ⟨1251852, by rfl⟩ : syracuseStep 3338273 = 2503705) B2503705
theorem B12841159 : Blo 876568 12841159 := bstep (se 1 (by rfl) ⟨9630869, by rfl⟩ : syracuseStep 12841159 = 19261739) B19261739
theorem B3338729 : Blo 876568 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B4453217 : Blo 876568 4453217 := bstep (se 2 (by rfl) ⟨1669956, by rfl⟩ : syracuseStep 4453217 = 3339913) B3339913
theorem B3339245 : Blo 876568 3339245 := bstep (se 3 (by rfl) ⟨626108, by rfl⟩ : syracuseStep 3339245 = 1252217) B1252217
theorem B10843129 : Blo 876568 10843129 := bstep (se 2 (by rfl) ⟨4066173, by rfl⟩ : syracuseStep 10843129 = 8132347) B8132347
theorem B11269853 : Blo 876568 11269853 := bstep (se 3 (by rfl) ⟨2113097, by rfl⟩ : syracuseStep 11269853 = 4226195) B4226195
theorem B5634157 : Blo 876568 5634157 := bstep (se 3 (by rfl) ⟨1056404, by rfl⟩ : syracuseStep 5634157 = 2112809) B2112809
theorem B5012057 : Blo 876568 5012057 := bstep (se 2 (by rfl) ⟨1879521, by rfl⟩ : syracuseStep 5012057 = 3759043) B3759043
theorem B2227247 : Blo 876568 2227247 := bstep (se 1 (by rfl) ⟨1670435, by rfl⟩ : syracuseStep 2227247 = 3340871) B3340871
theorem B2817119 : Blo 876568 2817119 := bstep (se 1 (by rfl) ⟨2112839, by rfl⟩ : syracuseStep 2817119 = 4225679) B4225679
theorem B60980779 : Blo 876568 60980779 := bstep (se 1 (by rfl) ⟨45735584, by rfl⟩ : syracuseStep 60980779 = 91471169) B91471169
theorem B51543761 : Blo 876568 51543761 := bstep (se 2 (by rfl) ⟨19328910, by rfl⟩ : syracuseStep 51543761 = 38657821) B38657821
theorem B1113851 : Blo 876568 1113851 := bstep (se 1 (by rfl) ⟨835388, by rfl⟩ : syracuseStep 1113851 = 1670777) B1670777
theorem B1671263 : Blo 876568 1671263 := bstep (se 1 (by rfl) ⟨1253447, by rfl⟩ : syracuseStep 1671263 = 2506895) B2506895
theorem B2228543 : Blo 876568 2228543 := bstep (se 1 (by rfl) ⟨1671407, by rfl⟩ : syracuseStep 2228543 = 3342815) B3342815
theorem B5013971 : Blo 876568 5013971 := bstep (se 1 (by rfl) ⟨3760478, by rfl⟩ : syracuseStep 5013971 = 7520957) B7520957
theorem B5636567 : Blo 876568 5636567 := bstep (se 1 (by rfl) ⟨4227425, by rfl⟩ : syracuseStep 5636567 = 8454851) B8454851
theorem B2228897 : Blo 876568 2228897 := bstep (se 2 (by rfl) ⟨835836, by rfl⟩ : syracuseStep 2228897 = 1671673) B1671673
theorem B16876943 : Blo 876568 16876943 := bstep (se 1 (by rfl) ⟨12657707, by rfl⟩ : syracuseStep 16876943 = 25315415) B25315415
theorem B12683081 : Blo 876568 12683081 := bstep (se 2 (by rfl) ⟨4756155, by rfl⟩ : syracuseStep 12683081 = 9512311) B9512311
theorem B4753561 : Blo 876568 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B166791437 : Blo 876568 166791437 := bstep (se 3 (by rfl) ⟨31273394, by rfl⟩ : syracuseStep 166791437 = 62546789) B62546789
theorem B18975491 : Blo 876568 18975491 := bstep (se 1 (by rfl) ⟨14231618, by rfl⟩ : syracuseStep 18975491 = 28463237) B28463237
theorem B1444711 : Blo 876568 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B3804583 : Blo 876568 3804583 := bstep (se 1 (by rfl) ⟨2853437, by rfl⟩ : syracuseStep 3804583 = 5706875) B5706875
theorem B986971 : Blo 876568 986971 := bstep (se 1 (by rfl) ⟨740228, by rfl⟩ : syracuseStep 986971 = 1480457) B1480457
theorem B16912313 : Blo 876568 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B1314857 : Blo 876568 1314857 := bstep (se 2 (by rfl) ⟨493071, by rfl⟩ : syracuseStep 1314857 = 986143) B986143
theorem B1314863 : Blo 876568 1314863 := bstep (se 1 (by rfl) ⟨986147, by rfl⟩ : syracuseStep 1314863 = 1972295) B1972295
theorem B1315433 : Blo 876568 1315433 := bstep (se 2 (by rfl) ⟨493287, by rfl⟩ : syracuseStep 1315433 = 986575) B986575
theorem B987943 : Blo 876568 987943 := bstep (se 1 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 987943 = 1481915) B1481915
theorem B57120065 : Blo 876568 57120065 := bstep (se 2 (by rfl) ⟨21420024, by rfl⟩ : syracuseStep 57120065 = 42840049) B42840049
theorem B2496233 : Blo 876568 2496233 := bstep (se 2 (by rfl) ⟨936087, by rfl⟩ : syracuseStep 2496233 = 1872175) B1872175
theorem B1251055 : Blo 876568 1251055 := bstep (se 1 (by rfl) ⟨938291, by rfl⟩ : syracuseStep 1251055 = 1876583) B1876583
theorem B5347367 : Blo 876568 5347367 := bstep (se 1 (by rfl) ⟨4010525, by rfl⟩ : syracuseStep 5347367 = 8021051) B8021051
theorem B989311 : Blo 876568 989311 := bstep (se 1 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 989311 = 1483967) B1483967
theorem B1317119 : Blo 876568 1317119 := bstep (se 1 (by rfl) ⟨987839, by rfl⟩ : syracuseStep 1317119 = 1975679) B1975679
theorem B5708225 : Blo 876568 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B2497007 : Blo 876568 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B2497031 : Blo 876568 2497031 := bstep (se 1 (by rfl) ⟨1872773, by rfl⟩ : syracuseStep 2497031 = 3745547) B3745547
theorem B2136631 : Blo 876568 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B989851 : Blo 876568 989851 := bstep (se 1 (by rfl) ⟨742388, by rfl⟩ : syracuseStep 989851 = 1484777) B1484777
theorem B1317671 : Blo 876568 1317671 := bstep (se 1 (by rfl) ⟨988253, by rfl⟩ : syracuseStep 1317671 = 1976507) B1976507
theorem B1973159 : Blo 876568 1973159 := bstep (se 1 (by rfl) ⟨1479869, by rfl⟩ : syracuseStep 1973159 = 2959739) B2959739
theorem B990175 : Blo 876568 990175 := bstep (se 1 (by rfl) ⟨742631, by rfl⟩ : syracuseStep 990175 = 1485263) B1485263
theorem B1973231 : Blo 876568 1973231 := bstep (se 1 (by rfl) ⟨1479923, by rfl⟩ : syracuseStep 1973231 = 2959847) B2959847
theorem B1973321 : Blo 876568 1973321 := bstep (se 2 (by rfl) ⟨739995, by rfl⟩ : syracuseStep 1973321 = 1479991) B1479991
theorem B1318139 : Blo 876568 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B2497817 : Blo 876568 2497817 := bstep (se 2 (by rfl) ⟨936681, by rfl⟩ : syracuseStep 2497817 = 1873363) B1873363
theorem B31989491 : Blo 876568 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B7512209 : Blo 876568 7512209 := bstep (se 2 (by rfl) ⟨2817078, by rfl⟩ : syracuseStep 7512209 = 5634157) B5634157
theorem B325230821 : Blo 876568 325230821 := bstep (se 4 (by rfl) ⟨30490389, by rfl⟩ : syracuseStep 325230821 = 60980779) B60980779
theorem B1319657 : Blo 876568 1319657 := bstep (se 2 (by rfl) ⟨494871, by rfl⟩ : syracuseStep 1319657 = 989743) B989743
theorem B1319675 : Blo 876568 1319675 := bstep (se 1 (by rfl) ⟨989756, by rfl⟩ : syracuseStep 1319675 = 1979513) B1979513
theorem B1975265 : Blo 876568 1975265 := bstep (se 2 (by rfl) ⟨740724, by rfl⟩ : syracuseStep 1975265 = 1481449) B1481449
theorem B7513235 : Blo 876568 7513235 := bstep (se 1 (by rfl) ⟨5634926, by rfl⟩ : syracuseStep 7513235 = 11269853) B11269853
theorem B1320191 : Blo 876568 1320191 := bstep (se 1 (by rfl) ⟨990143, by rfl⟩ : syracuseStep 1320191 = 1980287) B1980287
theorem B2958713 : Blo 876568 2958713 := bstep (se 2 (by rfl) ⟨1109517, by rfl⟩ : syracuseStep 2958713 = 2219035) B2219035
theorem B1320539 : Blo 876568 1320539 := bstep (se 1 (by rfl) ⟨990404, by rfl⟩ : syracuseStep 1320539 = 1980809) B1980809
theorem B1976039 : Blo 876568 1976039 := bstep (se 1 (by rfl) ⟨1482029, by rfl⟩ : syracuseStep 1976039 = 2964059) B2964059
theorem B1320815 : Blo 876568 1320815 := bstep (se 1 (by rfl) ⟨990611, by rfl⟩ : syracuseStep 1320815 = 1981223) B1981223
theorem B1484831 : Blo 876568 1484831 := bstep (se 1 (by rfl) ⟨1113623, by rfl⟩ : syracuseStep 1484831 = 2227247) B2227247
theorem B1878079 : Blo 876568 1878079 := bstep (se 1 (by rfl) ⟨1408559, by rfl⟩ : syracuseStep 1878079 = 2817119) B2817119
theorem B12003551 : Blo 876568 12003551 := bstep (se 1 (by rfl) ⟨9002663, by rfl⟩ : syracuseStep 12003551 = 18005327) B18005327
theorem B1976993 : Blo 876568 1976993 := bstep (se 2 (by rfl) ⟨741372, by rfl⟩ : syracuseStep 1976993 = 1482745) B1482745
theorem B4008701 : Blo 876568 4008701 := bstep (se 3 (by rfl) ⟨751631, by rfl⟩ : syracuseStep 4008701 = 1503263) B1503263
theorem B4008761 : Blo 876568 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B1977299 : Blo 876568 1977299 := bstep (se 1 (by rfl) ⟨1482974, by rfl⟩ : syracuseStep 1977299 = 2965949) B2965949
theorem B68431333 : Blo 876568 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B2960873 : Blo 876568 2960873 := bstep (se 2 (by rfl) ⟨1110327, by rfl⟩ : syracuseStep 2960873 = 2220655) B2220655
theorem B8564201 : Blo 876568 8564201 := bstep (se 2 (by rfl) ⟨3211575, by rfl⟩ : syracuseStep 8564201 = 6423151) B6423151
theorem B1977875 : Blo 876568 1977875 := bstep (se 1 (by rfl) ⟨1483406, by rfl⟩ : syracuseStep 1977875 = 2966813) B2966813
theorem B2960927 : Blo 876568 2960927 := bstep (se 1 (by rfl) ⟨2220695, by rfl⟩ : syracuseStep 2960927 = 4441391) B4441391
theorem B8007335 : Blo 876568 8007335 := bstep (se 1 (by rfl) ⟨6005501, by rfl⟩ : syracuseStep 8007335 = 12011003) B12011003
theorem B2109311 : Blo 876568 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B2502863 : Blo 876568 2502863 := bstep (se 1 (by rfl) ⟨1877147, by rfl⟩ : syracuseStep 2502863 = 3754295) B3754295
theorem B1979099 : Blo 876568 1979099 := bstep (se 1 (by rfl) ⟨1484324, by rfl⟩ : syracuseStep 1979099 = 2968649) B2968649
theorem B4993811 : Blo 876568 4993811 := bstep (se 1 (by rfl) ⟨3745358, by rfl⟩ : syracuseStep 4993811 = 7490717) B7490717
theorem B1585991 : Blo 876568 1585991 := bstep (se 1 (by rfl) ⟨1189493, by rfl⟩ : syracuseStep 1585991 = 2378987) B2378987
theorem B9483425 : Blo 876568 9483425 := bstep (se 2 (by rfl) ⟨3556284, by rfl⟩ : syracuseStep 9483425 = 7112569) B7112569
theorem B2962655 : Blo 876568 2962655 := bstep (se 1 (by rfl) ⟨2221991, by rfl⟩ : syracuseStep 2962655 = 4443983) B4443983
theorem B32126233 : Blo 876568 32126233 := bstep (se 2 (by rfl) ⟨12047337, by rfl⟩ : syracuseStep 32126233 = 24094675) B24094675
theorem B32487065 : Blo 876568 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B4995017 : Blo 876568 4995017 := bstep (se 2 (by rfl) ⟨1873131, by rfl⟩ : syracuseStep 4995017 = 3746263) B3746263
theorem B11253755 : Blo 876568 11253755 := bstep (se 1 (by rfl) ⟨8440316, by rfl⟩ : syracuseStep 11253755 = 16880633) B16880633
theorem B1980539 : Blo 876568 1980539 := bstep (se 1 (by rfl) ⟨1485404, by rfl⟩ : syracuseStep 1980539 = 2970809) B2970809
theorem B72136889 : Blo 876568 72136889 := bstep (se 2 (by rfl) ⟨27051333, by rfl⟩ : syracuseStep 72136889 = 54102667) B54102667
theorem B4438313 : Blo 876568 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B2375507 : Blo 876568 2375507 := bstep (se 1 (by rfl) ⟨1781630, by rfl⟩ : syracuseStep 2375507 = 3563261) B3563261
theorem B17121545 : Blo 876568 17121545 := bstep (se 2 (by rfl) ⟨6420579, by rfl⟩ : syracuseStep 17121545 = 12841159) B12841159
theorem B11256731 : Blo 876568 11256731 := bstep (se 1 (by rfl) ⟨8442548, by rfl⟩ : syracuseStep 11256731 = 16885097) B16885097
theorem B4441067 : Blo 876568 4441067 := bstep (se 1 (by rfl) ⟨3330800, by rfl⟩ : syracuseStep 4441067 = 6661601) B6661601
theorem B144197657 : Blo 876568 144197657 := bstep (se 2 (by rfl) ⟨54074121, by rfl⟩ : syracuseStep 144197657 = 108148243) B108148243
theorem B13551731 : Blo 876568 13551731 := bstep (se 1 (by rfl) ⟨10163798, by rfl⟩ : syracuseStep 13551731 = 20327597) B20327597
theorem B4213241 : Blo 876568 4213241 := bstep (se 2 (by rfl) ⟨1579965, by rfl⟩ : syracuseStep 4213241 = 3159931) B3159931
theorem B4442849 : Blo 876568 4442849 := bstep (se 2 (by rfl) ⟨1666068, by rfl⟩ : syracuseStep 4442849 = 3332137) B3332137
theorem B77122685 : Blo 876568 77122685 := bstep (se 3 (by rfl) ⟨14460503, by rfl⟩ : syracuseStep 77122685 = 28921007) B28921007
theorem B2968811 : Blo 876568 2968811 := bstep (se 1 (by rfl) ⟨2226608, by rfl⟩ : syracuseStep 2968811 = 4453217) B4453217
theorem B22859495 : Blo 876568 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B6082775 : Blo 876568 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B137450029 : Blo 876568 137450029 := bstep (se 3 (by rfl) ⟨25771880, by rfl⟩ : syracuseStep 137450029 = 51543761) B51543761
theorem B3330665 : Blo 876568 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B2970269 : Blo 876568 2970269 := bstep (se 3 (by rfl) ⟨556925, by rfl⟩ : syracuseStep 2970269 = 1113851) B1113851
theorem B4281947 : Blo 876568 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B10016459 : Blo 876568 10016459 := bstep (se 1 (by rfl) ⟨7512344, by rfl⟩ : syracuseStep 10016459 = 15024689) B15024689
theorem B3332123 : Blo 876568 3332123 := bstep (se 1 (by rfl) ⟨2499092, by rfl⟩ : syracuseStep 3332123 = 4998185) B4998185
theorem B3332609 : Blo 876568 3332609 := bstep (se 2 (by rfl) ⟨1249728, by rfl⟩ : syracuseStep 3332609 = 2499457) B2499457
theorem B65067623 : Blo 876568 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B6675209 : Blo 876568 6675209 := bstep (se 2 (by rfl) ⟨2503203, by rfl⟩ : syracuseStep 6675209 = 5006407) B5006407
theorem B10017917 : Blo 876568 10017917 := bstep (se 3 (by rfl) ⟨1878359, by rfl⟩ : syracuseStep 10017917 = 3756719) B3756719
theorem B3333383 : Blo 876568 3333383 := bstep (se 1 (by rfl) ⟨2500037, by rfl⟩ : syracuseStep 3333383 = 5000075) B5000075
theorem B14245571 : Blo 876568 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B876903 : Blo 876568 876903 := bstep (se 1 (by rfl) ⟨657677, by rfl⟩ : syracuseStep 876903 = 1315355) B1315355
theorem B877023 : Blo 876568 877023 := bstep (se 1 (by rfl) ⟨657767, by rfl⟩ : syracuseStep 877023 = 1315535) B1315535
theorem B877375 : Blo 876568 877375 := bstep (se 1 (by rfl) ⟨658031, by rfl⟩ : syracuseStep 877375 = 1316063) B1316063
theorem B2220929 : Blo 876568 2220929 := bstep (se 2 (by rfl) ⟨832848, by rfl⟩ : syracuseStep 2220929 = 1665697) B1665697
theorem B4449167 : Blo 876568 4449167 := bstep (se 1 (by rfl) ⟨3336875, by rfl⟩ : syracuseStep 4449167 = 6673751) B6673751
theorem B2220959 : Blo 876568 2220959 := bstep (se 1 (by rfl) ⟨1665719, by rfl⟩ : syracuseStep 2220959 = 3331439) B3331439
theorem B877535 : Blo 876568 877535 := bstep (se 1 (by rfl) ⟨658151, by rfl⟩ : syracuseStep 877535 = 1316303) B1316303
theorem B877695 : Blo 876568 877695 := bstep (se 1 (by rfl) ⟨658271, by rfl⟩ : syracuseStep 877695 = 1316543) B1316543
theorem B1664383 : Blo 876568 1664383 := bstep (se 1 (by rfl) ⟨1248287, by rfl⟩ : syracuseStep 1664383 = 2496575) B2496575
theorem B877951 : Blo 876568 877951 := bstep (se 1 (by rfl) ⟨658463, by rfl⟩ : syracuseStep 877951 = 1316927) B1316927
theorem B878063 : Blo 876568 878063 := bstep (se 1 (by rfl) ⟨658547, by rfl⟩ : syracuseStep 878063 = 1317095) B1317095
theorem B878183 : Blo 876568 878183 := bstep (se 1 (by rfl) ⟨658637, by rfl⟩ : syracuseStep 878183 = 1317275) B1317275
theorem B878463 : Blo 876568 878463 := bstep (se 1 (by rfl) ⟨658847, by rfl⟩ : syracuseStep 878463 = 1317695) B1317695
theorem B10020833 : Blo 876568 10020833 := bstep (se 2 (by rfl) ⟨3757812, by rfl⟩ : syracuseStep 10020833 = 7515625) B7515625
theorem B2222063 : Blo 876568 2222063 := bstep (se 1 (by rfl) ⟨1666547, by rfl⟩ : syracuseStep 2222063 = 3333095) B3333095
theorem B5007683 : Blo 876568 5007683 := bstep (se 1 (by rfl) ⟨3755762, by rfl⟩ : syracuseStep 5007683 = 7511525) B7511525
theorem B57830021 : Blo 876568 57830021 := bstep (se 4 (by rfl) ⟨5421564, by rfl⟩ : syracuseStep 57830021 = 10843129) B10843129
theorem B3337271 : Blo 876568 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B880175 : Blo 876568 880175 := bstep (se 1 (by rfl) ⟨660131, by rfl⟩ : syracuseStep 880175 = 1320263) B1320263
theorem B1109695 : Blo 876568 1109695 := bstep (se 1 (by rfl) ⟨832271, by rfl⟩ : syracuseStep 1109695 = 1664543) B1664543
theorem B18542479 : Blo 876568 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B1503559 : Blo 876568 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B1668127 : Blo 876568 1668127 := bstep (se 1 (by rfl) ⟨1251095, by rfl⟩ : syracuseStep 1668127 = 2502191) B2502191
theorem B2225515 : Blo 876568 2225515 := bstep (se 1 (by rfl) ⟨1669136, by rfl⟩ : syracuseStep 2225515 = 3338273) B3338273
theorem B2225819 : Blo 876568 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B2226163 : Blo 876568 2226163 := bstep (se 1 (by rfl) ⟨1669622, by rfl⟩ : syracuseStep 2226163 = 3339245) B3339245
theorem B4226003 : Blo 876568 4226003 := bstep (se 1 (by rfl) ⟨3169502, by rfl⟩ : syracuseStep 4226003 = 6339005) B6339005
theorem B4750319 : Blo 876568 4750319 := bstep (se 1 (by rfl) ⟨3562739, by rfl⟩ : syracuseStep 4750319 = 7125479) B7125479
theorem B3341371 : Blo 876568 3341371 := bstep (se 1 (by rfl) ⟨2506028, by rfl⟩ : syracuseStep 3341371 = 5012057) B5012057
theorem B1114175 : Blo 876568 1114175 := bstep (se 1 (by rfl) ⟨835631, by rfl⟩ : syracuseStep 1114175 = 1671263) B1671263
theorem B3342647 : Blo 876568 3342647 := bstep (se 1 (by rfl) ⟨2506985, by rfl⟩ : syracuseStep 3342647 = 5013971) B5013971
theorem B7504487 : Blo 876568 7504487 := bstep (se 1 (by rfl) ⟨5628365, by rfl⟩ : syracuseStep 7504487 = 11256731) B11256731
theorem B8455387 : Blo 876568 8455387 := bstep (se 1 (by rfl) ⟨6341540, by rfl⟩ : syracuseStep 8455387 = 12683081) B12683081
theorem B12650327 : Blo 876568 12650327 := bstep (se 1 (by rfl) ⟨9487745, by rfl⟩ : syracuseStep 12650327 = 18975491) B18975491
theorem B51415123 : Blo 876568 51415123 := bstep (se 1 (by rfl) ⟨38561342, by rfl⟩ : syracuseStep 51415123 = 77122685) B77122685
theorem B4229309 : Blo 876568 4229309 := bstep (se 3 (by rfl) ⟨792995, by rfl⟩ : syracuseStep 4229309 = 1585991) B1585991
theorem B15239663 : Blo 876568 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B11274875 : Blo 876568 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B38080043 : Blo 876568 38080043 := bstep (se 1 (by rfl) ⟨28560032, by rfl⟩ : syracuseStep 38080043 = 57120065) B57120065
theorem B2854631 : Blo 876568 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B3805483 : Blo 876568 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B1315439 : Blo 876568 1315439 := bstep (se 1 (by rfl) ⟨986579, by rfl⟩ : syracuseStep 1315439 = 1973159) B1973159
theorem B1315487 : Blo 876568 1315487 := bstep (se 1 (by rfl) ⟨986615, by rfl⟩ : syracuseStep 1315487 = 1973231) B1973231
theorem B1315547 : Blo 876568 1315547 := bstep (se 1 (by rfl) ⟨986660, by rfl⟩ : syracuseStep 1315547 = 1973321) B1973321
theorem B1479593 : Blo 876568 1479593 := bstep (se 2 (by rfl) ⟨554847, by rfl⟩ : syracuseStep 1479593 = 1109695) B1109695
theorem B1315961 : Blo 876568 1315961 := bstep (se 2 (by rfl) ⟨493485, by rfl⟩ : syracuseStep 1315961 = 986971) B986971
theorem B2004745 : Blo 876568 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B1480619 : Blo 876568 1480619 := bstep (se 1 (by rfl) ⟨1110464, by rfl⟩ : syracuseStep 1480619 = 2220929) B2220929
theorem B1480639 : Blo 876568 1480639 := bstep (se 1 (by rfl) ⟨1110479, by rfl⟩ : syracuseStep 1480639 = 2220959) B2220959
theorem B1316843 : Blo 876568 1316843 := bstep (se 1 (by rfl) ⟨987632, by rfl⟩ : syracuseStep 1316843 = 1975265) B1975265
theorem B1972475 : Blo 876568 1972475 := bstep (se 1 (by rfl) ⟨1479356, by rfl⟩ : syracuseStep 1972475 = 2958713) B2958713
theorem B1317257 : Blo 876568 1317257 := bstep (se 2 (by rfl) ⟨493971, by rfl⟩ : syracuseStep 1317257 = 987943) B987943
theorem B1317359 : Blo 876568 1317359 := bstep (se 1 (by rfl) ⟨988019, by rfl⟩ : syracuseStep 1317359 = 1976039) B1976039
theorem B6658685 : Blo 876568 6658685 := bstep (se 3 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 6658685 = 2497007) B2497007
theorem B1481375 : Blo 876568 1481375 := bstep (se 1 (by rfl) ⟨1111031, by rfl⟩ : syracuseStep 1481375 = 2222063) B2222063
theorem B989887 : Blo 876568 989887 := bstep (se 1 (by rfl) ⟨742415, by rfl⟩ : syracuseStep 989887 = 1484831) B1484831
theorem B8002367 : Blo 876568 8002367 := bstep (se 1 (by rfl) ⟨6001775, by rfl⟩ : syracuseStep 8002367 = 12003551) B12003551
theorem B42834977 : Blo 876568 42834977 := bstep (se 2 (by rfl) ⟨16063116, by rfl⟩ : syracuseStep 42834977 = 32126233) B32126233
theorem B1317995 : Blo 876568 1317995 := bstep (se 1 (by rfl) ⟨988496, by rfl⟩ : syracuseStep 1317995 = 1976993) B1976993
theorem B1318199 : Blo 876568 1318199 := bstep (se 1 (by rfl) ⟨988649, by rfl⟩ : syracuseStep 1318199 = 1977299) B1977299
theorem B10689869 : Blo 876568 10689869 := bstep (se 3 (by rfl) ⟨2004350, by rfl⟩ : syracuseStep 10689869 = 4008701) B4008701
theorem B1973915 : Blo 876568 1973915 := bstep (se 1 (by rfl) ⟨1480436, by rfl⟩ : syracuseStep 1973915 = 2960873) B2960873
theorem B5709467 : Blo 876568 5709467 := bstep (se 1 (by rfl) ⟨4282100, by rfl⟩ : syracuseStep 5709467 = 8564201) B8564201
theorem B1318583 : Blo 876568 1318583 := bstep (se 1 (by rfl) ⟨988937, by rfl⟩ : syracuseStep 1318583 = 1977875) B1977875
theorem B1973951 : Blo 876568 1973951 := bstep (se 1 (by rfl) ⟨1480463, by rfl⟩ : syracuseStep 1973951 = 2960927) B2960927
theorem B1319081 : Blo 876568 1319081 := bstep (se 2 (by rfl) ⟨494655, by rfl⟩ : syracuseStep 1319081 = 989311) B989311
theorem B1319399 : Blo 876568 1319399 := bstep (se 1 (by rfl) ⟨989549, by rfl⟩ : syracuseStep 1319399 = 1979099) B1979099
theorem B1975103 : Blo 876568 1975103 := bstep (se 1 (by rfl) ⟨1481327, by rfl⟩ : syracuseStep 1975103 = 2962655) B2962655
theorem B1319801 : Blo 876568 1319801 := bstep (se 2 (by rfl) ⟨494925, by rfl⟩ : syracuseStep 1319801 = 989851) B989851
theorem B1483879 : Blo 876568 1483879 := bstep (se 1 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 1483879 = 2225819) B2225819
theorem B1320233 : Blo 876568 1320233 := bstep (se 2 (by rfl) ⟨495087, by rfl⟩ : syracuseStep 1320233 = 990175) B990175
theorem B1320359 : Blo 876568 1320359 := bstep (se 1 (by rfl) ⟨990269, by rfl⟩ : syracuseStep 1320359 = 1980539) B1980539
theorem B2958875 : Blo 876568 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B37988189 : Blo 876568 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B1583671 : Blo 876568 1583671 := bstep (se 1 (by rfl) ⟨1187753, by rfl⟩ : syracuseStep 1583671 = 2375507) B2375507
theorem B11414363 : Blo 876568 11414363 := bstep (se 1 (by rfl) ⟨8560772, by rfl⟩ : syracuseStep 11414363 = 17121545) B17121545
theorem B1485695 : Blo 876568 1485695 := bstep (se 1 (by rfl) ⟨1114271, by rfl⟩ : syracuseStep 1485695 = 2228543) B2228543
theorem B1485931 : Blo 876568 1485931 := bstep (se 1 (by rfl) ⟨1114448, by rfl⟩ : syracuseStep 1485931 = 2228897) B2228897
theorem B2960711 : Blo 876568 2960711 := bstep (se 1 (by rfl) ⟨2220533, by rfl⟩ : syracuseStep 2960711 = 4441067) B4441067
theorem B11251295 : Blo 876568 11251295 := bstep (se 1 (by rfl) ⟨8438471, by rfl⟩ : syracuseStep 11251295 = 16876943) B16876943
theorem B111194291 : Blo 876568 111194291 := bstep (se 1 (by rfl) ⟨83395718, by rfl⟩ : syracuseStep 111194291 = 166791437) B166791437
theorem B2961899 : Blo 876568 2961899 := bstep (se 1 (by rfl) ⟨2221424, by rfl⟩ : syracuseStep 2961899 = 4442849) B4442849
theorem B1979207 : Blo 876568 1979207 := bstep (se 1 (by rfl) ⟨1484405, by rfl⟩ : syracuseStep 1979207 = 2968811) B2968811
theorem B2504105 : Blo 876568 2504105 := bstep (se 2 (by rfl) ⟨939039, by rfl⟩ : syracuseStep 2504105 = 1878079) B1878079
theorem B6338081 : Blo 876568 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B1980179 : Blo 876568 1980179 := bstep (se 1 (by rfl) ⟨1485134, by rfl⟩ : syracuseStep 1980179 = 2970269) B2970269
theorem B91241777 : Blo 876568 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B24723305 : Blo 876568 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B2966111 : Blo 876568 2966111 := bstep (se 1 (by rfl) ⟨2224583, by rfl⟩ : syracuseStep 2966111 = 4449167) B4449167
theorem B38553347 : Blo 876568 38553347 := bstep (se 1 (by rfl) ⟨28915010, by rfl⟩ : syracuseStep 38553347 = 57830021) B57830021
theorem B2967353 : Blo 876568 2967353 := bstep (se 2 (by rfl) ⟨1112757, by rfl⟩ : syracuseStep 2967353 = 2225515) B2225515
theorem B2672507 : Blo 876568 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B2968217 : Blo 876568 2968217 := bstep (se 2 (by rfl) ⟨1113081, by rfl⟩ : syracuseStep 2968217 = 2226163) B2226163
theorem B3329207 : Blo 876568 3329207 := bstep (se 1 (by rfl) ⟨2496905, by rfl⟩ : syracuseStep 3329207 = 4993811) B4993811
theorem B6672293 : Blo 876568 6672293 := bstep (se 4 (by rfl) ⟨625527, by rfl⟩ : syracuseStep 6672293 = 1251055) B1251055
theorem B3330011 : Blo 876568 3330011 := bstep (se 1 (by rfl) ⟨2497508, by rfl⟩ : syracuseStep 3330011 = 4995017) B4995017
theorem B48091259 : Blo 876568 48091259 := bstep (se 1 (by rfl) ⟨36068444, by rfl⟩ : syracuseStep 48091259 = 72136889) B72136889
theorem B3166879 : Blo 876568 3166879 := bstep (se 1 (by rfl) ⟨2375159, by rfl⟩ : syracuseStep 3166879 = 4750319) B4750319
theorem B3757711 : Blo 876568 3757711 := bstep (se 1 (by rfl) ⟨2818283, by rfl⟩ : syracuseStep 3757711 = 5636567) B5636567
theorem B96131771 : Blo 876568 96131771 := bstep (se 1 (by rfl) ⟨72098828, by rfl⟩ : syracuseStep 96131771 = 144197657) B144197657
theorem B9034487 : Blo 876568 9034487 := bstep (se 1 (by rfl) ⟨6775865, by rfl⟩ : syracuseStep 9034487 = 13551731) B13551731
theorem B2808827 : Blo 876568 2808827 := bstep (se 1 (by rfl) ⟨2106620, by rfl⟩ : syracuseStep 2808827 = 4213241) B4213241
theorem B2219177 : Blo 876568 2219177 := bstep (se 2 (by rfl) ⟨832191, by rfl⟩ : syracuseStep 2219177 = 1664383) B1664383
theorem B876571 : Blo 876568 876571 := bstep (se 1 (by rfl) ⟨657428, by rfl⟩ : syracuseStep 876571 = 1314857) B1314857
theorem B876575 : Blo 876568 876575 := bstep (se 1 (by rfl) ⟨657431, by rfl⟩ : syracuseStep 876575 = 1314863) B1314863
theorem B4055183 : Blo 876568 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B876955 : Blo 876568 876955 := bstep (se 1 (by rfl) ⟨657716, by rfl⟩ : syracuseStep 876955 = 1315433) B1315433
theorem B2220443 : Blo 876568 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B6677639 : Blo 876568 6677639 := bstep (se 1 (by rfl) ⟨5008229, by rfl⟩ : syracuseStep 6677639 = 10016459) B10016459
theorem B1926281 : Blo 876568 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B1664155 : Blo 876568 1664155 := bstep (se 1 (by rfl) ⟨1248116, by rfl⟩ : syracuseStep 1664155 = 2496233) B2496233
theorem B2221415 : Blo 876568 2221415 := bstep (se 1 (by rfl) ⟨1666061, by rfl⟩ : syracuseStep 2221415 = 3332123) B3332123
theorem B3564911 : Blo 876568 3564911 := bstep (se 1 (by rfl) ⟨2673683, by rfl⟩ : syracuseStep 3564911 = 5347367) B5347367
theorem B878079 : Blo 876568 878079 := bstep (se 1 (by rfl) ⟨658559, by rfl⟩ : syracuseStep 878079 = 1317119) B1317119
theorem B2221739 : Blo 876568 2221739 := bstep (se 1 (by rfl) ⟨1666304, by rfl⟩ : syracuseStep 2221739 = 3332609) B3332609
theorem B1664687 : Blo 876568 1664687 := bstep (se 1 (by rfl) ⟨1248515, by rfl⟩ : syracuseStep 1664687 = 2497031) B2497031
theorem B43378415 : Blo 876568 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B4450139 : Blo 876568 4450139 := bstep (se 1 (by rfl) ⟨3337604, by rfl⟩ : syracuseStep 4450139 = 6675209) B6675209
theorem B878447 : Blo 876568 878447 := bstep (se 1 (by rfl) ⟨658835, by rfl⟩ : syracuseStep 878447 = 1317671) B1317671
theorem B5072777 : Blo 876568 5072777 := bstep (se 2 (by rfl) ⟨1902291, by rfl⟩ : syracuseStep 5072777 = 3804583) B3804583
theorem B6678611 : Blo 876568 6678611 := bstep (se 1 (by rfl) ⟨5008958, by rfl⟩ : syracuseStep 6678611 = 10017917) B10017917
theorem B878759 : Blo 876568 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B2222255 : Blo 876568 2222255 := bstep (se 1 (by rfl) ⟨1666691, by rfl⟩ : syracuseStep 2222255 = 3333383) B3333383
theorem B1665211 : Blo 876568 1665211 := bstep (se 1 (by rfl) ⟨1248908, by rfl⟩ : syracuseStep 1665211 = 2497817) B2497817
theorem B21326327 : Blo 876568 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B5008139 : Blo 876568 5008139 := bstep (se 1 (by rfl) ⟨3756104, by rfl⟩ : syracuseStep 5008139 = 7512209) B7512209
theorem B216820547 : Blo 876568 216820547 := bstep (se 1 (by rfl) ⟨162615410, by rfl⟩ : syracuseStep 216820547 = 325230821) B325230821
theorem B879771 : Blo 876568 879771 := bstep (se 1 (by rfl) ⟨659828, by rfl⟩ : syracuseStep 879771 = 1319657) B1319657
theorem B879783 : Blo 876568 879783 := bstep (se 1 (by rfl) ⟨659837, by rfl⟩ : syracuseStep 879783 = 1319675) B1319675
theorem B183266705 : Blo 876568 183266705 := bstep (se 2 (by rfl) ⟨68725014, by rfl⟩ : syracuseStep 183266705 = 137450029) B137450029
theorem B5008823 : Blo 876568 5008823 := bstep (se 1 (by rfl) ⟨3756617, by rfl⟩ : syracuseStep 5008823 = 7513235) B7513235
theorem B880127 : Blo 876568 880127 := bstep (se 1 (by rfl) ⟨660095, by rfl⟩ : syracuseStep 880127 = 1320191) B1320191
theorem B880359 : Blo 876568 880359 := bstep (se 1 (by rfl) ⟨660269, by rfl⟩ : syracuseStep 880359 = 1320539) B1320539
theorem B880543 : Blo 876568 880543 := bstep (se 1 (by rfl) ⟨660407, by rfl⟩ : syracuseStep 880543 = 1320815) B1320815
theorem B6680555 : Blo 876568 6680555 := bstep (se 1 (by rfl) ⟨5010416, by rfl⟩ : syracuseStep 6680555 = 10020833) B10020833
theorem B2224169 : Blo 876568 2224169 := bstep (se 2 (by rfl) ⟨834063, by rfl⟩ : syracuseStep 2224169 = 1668127) B1668127
theorem B3338455 : Blo 876568 3338455 := bstep (se 1 (by rfl) ⟨2503841, by rfl⟩ : syracuseStep 3338455 = 5007683) B5007683
theorem B2224847 : Blo 876568 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B5338223 : Blo 876568 5338223 := bstep (se 1 (by rfl) ⟨4003667, by rfl⟩ : syracuseStep 5338223 = 8007335) B8007335
theorem B1406207 : Blo 876568 1406207 := bstep (se 1 (by rfl) ⟨1054655, by rfl⟩ : syracuseStep 1406207 = 2109311) B2109311
theorem B1668575 : Blo 876568 1668575 := bstep (se 1 (by rfl) ⟨1251431, by rfl⟩ : syracuseStep 1668575 = 2502863) B2502863
theorem B2848841 : Blo 876568 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B6322283 : Blo 876568 6322283 := bstep (se 1 (by rfl) ⟨4741712, by rfl⟩ : syracuseStep 6322283 = 9483425) B9483425
theorem B21658043 : Blo 876568 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B7502503 : Blo 876568 7502503 := bstep (se 1 (by rfl) ⟨5626877, by rfl⟩ : syracuseStep 7502503 = 11253755) B11253755
theorem B4455161 : Blo 876568 4455161 := bstep (se 2 (by rfl) ⟨1670685, by rfl⟩ : syracuseStep 4455161 = 3341371) B3341371
theorem B2817335 : Blo 876568 2817335 := bstep (se 1 (by rfl) ⟨2113001, by rfl⟩ : syracuseStep 2817335 = 4226003) B4226003
theorem B2228431 : Blo 876568 2228431 := bstep (se 1 (by rfl) ⟨1671323, by rfl⟩ : syracuseStep 2228431 = 3342647) B3342647
theorem B2819539 : Blo 876568 2819539 := bstep (se 1 (by rfl) ⟨2114654, by rfl⟩ : syracuseStep 2819539 = 4229309) B4229309
theorem B11273849 : Blo 876568 11273849 := bstep (se 2 (by rfl) ⟨4227693, by rfl⟩ : syracuseStep 11273849 = 8455387) B8455387
theorem B10159775 : Blo 876568 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B1903087 : Blo 876568 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B68553497 : Blo 876568 68553497 := bstep (se 2 (by rfl) ⟨25707561, by rfl⟩ : syracuseStep 68553497 = 51415123) B51415123
theorem B986395 : Blo 876568 986395 := bstep (se 1 (by rfl) ⟨739796, by rfl⟩ : syracuseStep 986395 = 1479593) B1479593
theorem B9506429 : Blo 876568 9506429 := bstep (se 3 (by rfl) ⟨1782455, by rfl⟩ : syracuseStep 9506429 = 3564911) B3564911
theorem B987079 : Blo 876568 987079 := bstep (se 1 (by rfl) ⟨740309, by rfl⟩ : syracuseStep 987079 = 1480619) B1480619
theorem B1314983 : Blo 876568 1314983 := bstep (se 1 (by rfl) ⟨986237, by rfl⟩ : syracuseStep 1314983 = 1972475) B1972475
theorem B987583 : Blo 876568 987583 := bstep (se 1 (by rfl) ⟨740687, by rfl⟩ : syracuseStep 987583 = 1481375) B1481375
theorem B1872551 : Blo 876568 1872551 := bstep (se 1 (by rfl) ⟨1404413, by rfl⟩ : syracuseStep 1872551 = 2808827) B2808827
theorem B1479451 : Blo 876568 1479451 := bstep (se 1 (by rfl) ⟨1109588, by rfl⟩ : syracuseStep 1479451 = 2219177) B2219177
theorem B1315943 : Blo 876568 1315943 := bstep (se 1 (by rfl) ⟨986957, by rfl⟩ : syracuseStep 1315943 = 1973915) B1973915
theorem B1315967 : Blo 876568 1315967 := bstep (se 1 (by rfl) ⟨986975, by rfl⟩ : syracuseStep 1315967 = 1973951) B1973951
theorem B1480295 : Blo 876568 1480295 := bstep (se 1 (by rfl) ⟨1110221, by rfl⟩ : syracuseStep 1480295 = 2220443) B2220443
theorem B1316735 : Blo 876568 1316735 := bstep (se 1 (by rfl) ⟨987551, by rfl⟩ : syracuseStep 1316735 = 1975103) B1975103
theorem B1284187 : Blo 876568 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B1480943 : Blo 876568 1480943 := bstep (se 1 (by rfl) ⟨1110707, by rfl⟩ : syracuseStep 1480943 = 2221415) B2221415
theorem B1972583 : Blo 876568 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B1481159 : Blo 876568 1481159 := bstep (se 1 (by rfl) ⟨1110869, by rfl⟩ : syracuseStep 1481159 = 2221739) B2221739
theorem B3381851 : Blo 876568 3381851 := bstep (se 1 (by rfl) ⟨2536388, by rfl⟩ : syracuseStep 3381851 = 5072777) B5072777
theorem B1481503 : Blo 876568 1481503 := bstep (se 1 (by rfl) ⟨1111127, by rfl⟩ : syracuseStep 1481503 = 2222255) B2222255
theorem B144547031 : Blo 876568 144547031 := bstep (se 1 (by rfl) ⟨108410273, by rfl⟩ : syracuseStep 144547031 = 216820547) B216820547
theorem B990463 : Blo 876568 990463 := bstep (se 1 (by rfl) ⟨742847, by rfl⟩ : syracuseStep 990463 = 1485695) B1485695
theorem B1973807 : Blo 876568 1973807 := bstep (se 1 (by rfl) ⟨1480355, by rfl⟩ : syracuseStep 1973807 = 2960711) B2960711
theorem B1974185 : Blo 876568 1974185 := bstep (se 2 (by rfl) ⟨740319, by rfl⟩ : syracuseStep 1974185 = 1480639) B1480639
theorem B1482779 : Blo 876568 1482779 := bstep (se 1 (by rfl) ⟨1112084, by rfl⟩ : syracuseStep 1482779 = 2224169) B2224169
theorem B74129527 : Blo 876568 74129527 := bstep (se 1 (by rfl) ⟨55597145, by rfl⟩ : syracuseStep 74129527 = 111194291) B111194291
theorem B1974599 : Blo 876568 1974599 := bstep (se 1 (by rfl) ⟨1480949, by rfl⟩ : syracuseStep 1974599 = 2961899) B2961899
theorem B1483231 : Blo 876568 1483231 := bstep (se 1 (by rfl) ⟨1112423, by rfl⟩ : syracuseStep 1483231 = 2224847) B2224847
theorem B1319471 : Blo 876568 1319471 := bstep (se 1 (by rfl) ⟨989603, by rfl⟩ : syracuseStep 1319471 = 1979207) B1979207
theorem B10003337 : Blo 876568 10003337 := bstep (se 2 (by rfl) ⟨3751251, by rfl⟩ : syracuseStep 10003337 = 7502503) B7502503
theorem B1319849 : Blo 876568 1319849 := bstep (se 2 (by rfl) ⟨494943, by rfl⟩ : syracuseStep 1319849 = 989887) B989887
theorem B1320119 : Blo 876568 1320119 := bstep (se 1 (by rfl) ⟨990089, by rfl⟩ : syracuseStep 1320119 = 1980179) B1980179
theorem B60827851 : Blo 876568 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B1878223 : Blo 876568 1878223 := bstep (se 1 (by rfl) ⟨1408667, by rfl⟩ : syracuseStep 1878223 = 2817335) B2817335
theorem B1977407 : Blo 876568 1977407 := bstep (se 1 (by rfl) ⟨1483055, by rfl⟩ : syracuseStep 1977407 = 2966111) B2966111
theorem B1978235 : Blo 876568 1978235 := bstep (se 1 (by rfl) ⟨1483676, by rfl⟩ : syracuseStep 1978235 = 2967353) B2967353
theorem B8433551 : Blo 876568 8433551 := bstep (se 1 (by rfl) ⟨6325163, by rfl⟩ : syracuseStep 8433551 = 12650327) B12650327
theorem B1781671 : Blo 876568 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B1978505 : Blo 876568 1978505 := bstep (se 2 (by rfl) ⟨741939, by rfl⟩ : syracuseStep 1978505 = 1483879) B1483879
theorem B7516583 : Blo 876568 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B1978811 : Blo 876568 1978811 := bstep (se 1 (by rfl) ⟨1484108, by rfl⟩ : syracuseStep 1978811 = 2968217) B2968217
theorem B3749885 : Blo 876568 3749885 := bstep (se 3 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 3749885 = 1406207) B1406207
theorem B2111561 : Blo 876568 2111561 := bstep (se 2 (by rfl) ⟨791835, by rfl⟩ : syracuseStep 2111561 = 1583671) B1583671
theorem B1981241 : Blo 876568 1981241 := bstep (se 2 (by rfl) ⟨742965, by rfl⟩ : syracuseStep 1981241 = 1485931) B1485931
theorem B4439123 : Blo 876568 4439123 := bstep (se 1 (by rfl) ⟨3329342, by rfl⟩ : syracuseStep 4439123 = 6658685) B6658685
theorem B102808925 : Blo 876568 102808925 := bstep (se 3 (by rfl) ⟨19276673, by rfl⟩ : syracuseStep 102808925 = 38553347) B38553347
theorem B28556651 : Blo 876568 28556651 := bstep (se 1 (by rfl) ⟨21417488, by rfl⟩ : syracuseStep 28556651 = 42834977) B42834977
theorem B7126579 : Blo 876568 7126579 := bstep (se 1 (by rfl) ⟨5344934, by rfl⟩ : syracuseStep 7126579 = 10689869) B10689869
theorem B2703455 : Blo 876568 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B28918943 : Blo 876568 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B2966759 : Blo 876568 2966759 := bstep (se 1 (by rfl) ⟨2225069, by rfl⟩ : syracuseStep 2966759 = 4450139) B4450139
theorem B122177803 : Blo 876568 122177803 := bstep (se 1 (by rfl) ⟨91633352, by rfl⟩ : syracuseStep 122177803 = 183266705) B183266705
theorem B2672993 : Blo 876568 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B3558815 : Blo 876568 3558815 := bstep (se 1 (by rfl) ⟨2669111, by rfl⟩ : syracuseStep 3558815 = 5338223) B5338223
theorem B4214855 : Blo 876568 4214855 := bstep (se 1 (by rfl) ⟨3161141, by rfl⟩ : syracuseStep 4214855 = 6322283) B6322283
theorem B14438695 : Blo 876568 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B15225245 : Blo 876568 15225245 := bstep (se 3 (by rfl) ⟨2854733, by rfl⟩ : syracuseStep 15225245 = 5709467) B5709467
theorem B2970107 : Blo 876568 2970107 := bstep (se 1 (by rfl) ⟨2227580, by rfl⟩ : syracuseStep 2970107 = 4455161) B4455161
theorem B2971133 : Blo 876568 2971133 := bstep (se 3 (by rfl) ⟨557087, by rfl⟩ : syracuseStep 2971133 = 1114175) B1114175
theorem B128243357 : Blo 876568 128243357 := bstep (se 3 (by rfl) ⟨24045629, by rfl⟩ : syracuseStep 128243357 = 48091259) B48091259
theorem B5002991 : Blo 876568 5002991 := bstep (se 1 (by rfl) ⟨3752243, by rfl⟩ : syracuseStep 5002991 = 7504487) B7504487
theorem B2218873 : Blo 876568 2218873 := bstep (se 2 (by rfl) ⟨832077, by rfl⟩ : syracuseStep 2218873 = 1664155) B1664155
theorem B2219471 : Blo 876568 2219471 := bstep (se 1 (by rfl) ⟨1664603, by rfl⟩ : syracuseStep 2219471 = 3329207) B3329207
theorem B25386695 : Blo 876568 25386695 := bstep (se 1 (by rfl) ⟨19040021, by rfl⟩ : syracuseStep 25386695 = 38080043) B38080043
theorem B4448195 : Blo 876568 4448195 := bstep (se 1 (by rfl) ⟨3336146, by rfl⟩ : syracuseStep 4448195 = 6672293) B6672293
theorem B2220007 : Blo 876568 2220007 := bstep (se 1 (by rfl) ⟨1665005, by rfl⟩ : syracuseStep 2220007 = 3330011) B3330011
theorem B2220281 : Blo 876568 2220281 := bstep (se 2 (by rfl) ⟨832605, by rfl⟩ : syracuseStep 2220281 = 1665211) B1665211
theorem B876959 : Blo 876568 876959 := bstep (se 1 (by rfl) ⟨657719, by rfl⟩ : syracuseStep 876959 = 1315439) B1315439
theorem B876991 : Blo 876568 876991 := bstep (se 1 (by rfl) ⟨657743, by rfl⟩ : syracuseStep 876991 = 1315487) B1315487
theorem B877031 : Blo 876568 877031 := bstep (se 1 (by rfl) ⟨657773, by rfl⟩ : syracuseStep 877031 = 1315547) B1315547
theorem B877307 : Blo 876568 877307 := bstep (se 1 (by rfl) ⟨657980, by rfl⟩ : syracuseStep 877307 = 1315961) B1315961
theorem B877895 : Blo 876568 877895 := bstep (se 1 (by rfl) ⟨658421, by rfl⟩ : syracuseStep 877895 = 1316843) B1316843
theorem B878171 : Blo 876568 878171 := bstep (se 1 (by rfl) ⟨658628, by rfl⟩ : syracuseStep 878171 = 1317257) B1317257
theorem B878239 : Blo 876568 878239 := bstep (se 1 (by rfl) ⟨658679, by rfl⟩ : syracuseStep 878239 = 1317359) B1317359
theorem B64087847 : Blo 876568 64087847 := bstep (se 1 (by rfl) ⟨48065885, by rfl⟩ : syracuseStep 64087847 = 96131771) B96131771
theorem B6022991 : Blo 876568 6022991 := bstep (se 1 (by rfl) ⟨4517243, by rfl⟩ : syracuseStep 6022991 = 9034487) B9034487
theorem B5334911 : Blo 876568 5334911 := bstep (se 1 (by rfl) ⟨4001183, by rfl⟩ : syracuseStep 5334911 = 8002367) B8002367
theorem B878663 : Blo 876568 878663 := bstep (se 1 (by rfl) ⟨658997, by rfl⟩ : syracuseStep 878663 = 1317995) B1317995
theorem B878799 : Blo 876568 878799 := bstep (se 1 (by rfl) ⟨659099, by rfl⟩ : syracuseStep 878799 = 1318199) B1318199
theorem B879055 : Blo 876568 879055 := bstep (se 1 (by rfl) ⟨659291, by rfl⟩ : syracuseStep 879055 = 1318583) B1318583
theorem B879387 : Blo 876568 879387 := bstep (se 1 (by rfl) ⟨659540, by rfl⟩ : syracuseStep 879387 = 1319081) B1319081
theorem B4451273 : Blo 876568 4451273 := bstep (se 2 (by rfl) ⟨1669227, by rfl⟩ : syracuseStep 4451273 = 3338455) B3338455
theorem B879599 : Blo 876568 879599 := bstep (se 1 (by rfl) ⟨659699, by rfl⟩ : syracuseStep 879599 = 1319399) B1319399
theorem B5073977 : Blo 876568 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B879867 : Blo 876568 879867 := bstep (se 1 (by rfl) ⟨659900, by rfl⟩ : syracuseStep 879867 = 1319801) B1319801
theorem B4451759 : Blo 876568 4451759 := bstep (se 1 (by rfl) ⟨3338819, by rfl⟩ : syracuseStep 4451759 = 6677639) B6677639
theorem B880155 : Blo 876568 880155 := bstep (se 1 (by rfl) ⟨660116, by rfl⟩ : syracuseStep 880155 = 1320233) B1320233
theorem B4222505 : Blo 876568 4222505 := bstep (se 2 (by rfl) ⟨1583439, by rfl⟩ : syracuseStep 4222505 = 3166879) B3166879
theorem B880239 : Blo 876568 880239 := bstep (se 1 (by rfl) ⟨660179, by rfl⟩ : syracuseStep 880239 = 1320359) B1320359
theorem B1109791 : Blo 876568 1109791 := bstep (se 1 (by rfl) ⟨832343, by rfl⟩ : syracuseStep 1109791 = 1664687) B1664687
theorem B25325459 : Blo 876568 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B4452407 : Blo 876568 4452407 := bstep (se 1 (by rfl) ⟨3339305, by rfl⟩ : syracuseStep 4452407 = 6678611) B6678611
theorem B14217551 : Blo 876568 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B3338759 : Blo 876568 3338759 := bstep (se 1 (by rfl) ⟨2504069, by rfl⟩ : syracuseStep 3338759 = 5008139) B5008139
theorem B5010281 : Blo 876568 5010281 := bstep (se 2 (by rfl) ⟨1878855, by rfl⟩ : syracuseStep 5010281 = 3757711) B3757711
theorem B30438301 : Blo 876568 30438301 := bstep (se 3 (by rfl) ⟨5707181, by rfl⟩ : syracuseStep 30438301 = 11414363) B11414363
theorem B3339215 : Blo 876568 3339215 := bstep (se 1 (by rfl) ⟨2504411, by rfl⟩ : syracuseStep 3339215 = 5008823) B5008823
theorem B7500863 : Blo 876568 7500863 := bstep (se 1 (by rfl) ⟨5625647, by rfl⟩ : syracuseStep 7500863 = 11251295) B11251295
theorem B4453703 : Blo 876568 4453703 := bstep (se 1 (by rfl) ⟨3340277, by rfl⟩ : syracuseStep 4453703 = 6680555) B6680555
theorem B1669403 : Blo 876568 1669403 := bstep (se 1 (by rfl) ⟨1252052, by rfl⟩ : syracuseStep 1669403 = 2504105) B2504105
theorem B1112383 : Blo 876568 1112383 := bstep (se 1 (by rfl) ⟨834287, by rfl⟩ : syracuseStep 1112383 = 1668575) B1668575
theorem B4225387 : Blo 876568 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B1899227 : Blo 876568 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B16482203 : Blo 876568 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B1802303 : Blo 876568 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B81103801 : Blo 876568 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B1248367 : Blo 876568 1248367 := bstep (se 1 (by rfl) ⟨936275, by rfl⟩ : syracuseStep 1248367 = 1872551) B1872551
theorem B986863 : Blo 876568 986863 := bstep (se 1 (by rfl) ⟨740147, by rfl⟩ : syracuseStep 986863 = 1480295) B1480295
theorem B85495571 : Blo 876568 85495571 := bstep (se 1 (by rfl) ⟨64121678, by rfl⟩ : syracuseStep 85495571 = 128243357) B128243357
theorem B987295 : Blo 876568 987295 := bstep (se 1 (by rfl) ⟨740471, by rfl⟩ : syracuseStep 987295 = 1480943) B1480943
theorem B1315055 : Blo 876568 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B987439 : Blo 876568 987439 := bstep (se 1 (by rfl) ⟨740579, by rfl⟩ : syracuseStep 987439 = 1481159) B1481159
theorem B1315193 : Blo 876568 1315193 := bstep (se 2 (by rfl) ⟨493197, by rfl⟩ : syracuseStep 1315193 = 986395) B986395
theorem B1479647 : Blo 876568 1479647 := bstep (se 1 (by rfl) ⟨1109735, by rfl⟩ : syracuseStep 1479647 = 2219471) B2219471
theorem B1315871 : Blo 876568 1315871 := bstep (se 1 (by rfl) ⟨986903, by rfl⟩ : syracuseStep 1315871 = 1973807) B1973807
theorem B1479721 : Blo 876568 1479721 := bstep (se 2 (by rfl) ⟨554895, by rfl⟩ : syracuseStep 1479721 = 1109791) B1109791
theorem B1316105 : Blo 876568 1316105 := bstep (se 2 (by rfl) ⟨493539, by rfl⟩ : syracuseStep 1316105 = 987079) B987079
theorem B1316123 : Blo 876568 1316123 := bstep (se 1 (by rfl) ⟨987092, by rfl⟩ : syracuseStep 1316123 = 1974185) B1974185
theorem B988519 : Blo 876568 988519 := bstep (se 1 (by rfl) ⟨741389, by rfl⟩ : syracuseStep 988519 = 1482779) B1482779
theorem B1480187 : Blo 876568 1480187 := bstep (se 1 (by rfl) ⟨1110140, by rfl⟩ : syracuseStep 1480187 = 2220281) B2220281
theorem B1316399 : Blo 876568 1316399 := bstep (se 1 (by rfl) ⟨987299, by rfl⟩ : syracuseStep 1316399 = 1974599) B1974599
theorem B1316777 : Blo 876568 1316777 := bstep (se 2 (by rfl) ⟨493791, by rfl⟩ : syracuseStep 1316777 = 987583) B987583
theorem B1972601 : Blo 876568 1972601 := bstep (se 2 (by rfl) ⟨739725, by rfl⟩ : syracuseStep 1972601 = 1479451) B1479451
theorem B3382651 : Blo 876568 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B1318271 : Blo 876568 1318271 := bstep (se 1 (by rfl) ⟨988703, by rfl⟩ : syracuseStep 1318271 = 1977407) B1977407
theorem B1318823 : Blo 876568 1318823 := bstep (se 1 (by rfl) ⟨989117, by rfl⟩ : syracuseStep 1318823 = 1978235) B1978235
theorem B16883639 : Blo 876568 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B1319003 : Blo 876568 1319003 := bstep (se 1 (by rfl) ⟨989252, by rfl⟩ : syracuseStep 1319003 = 1978505) B1978505
theorem B1712249 : Blo 876568 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B9478367 : Blo 876568 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B1319207 : Blo 876568 1319207 := bstep (se 1 (by rfl) ⟨989405, by rfl⟩ : syracuseStep 1319207 = 1978811) B1978811
theorem B1483177 : Blo 876568 1483177 := bstep (se 2 (by rfl) ⟨556191, by rfl⟩ : syracuseStep 1483177 = 1112383) B1112383
theorem B1975337 : Blo 876568 1975337 := bstep (se 2 (by rfl) ⟨740751, by rfl⟩ : syracuseStep 1975337 = 1481503) B1481503
theorem B2958497 : Blo 876568 2958497 := bstep (se 2 (by rfl) ⟨1109436, by rfl⟩ : syracuseStep 2958497 = 2218873) B2218873
theorem B2499923 : Blo 876568 2499923 := bstep (se 1 (by rfl) ⟨1874942, by rfl⟩ : syracuseStep 2499923 = 3749885) B3749885
theorem B1320617 : Blo 876568 1320617 := bstep (se 2 (by rfl) ⟨495231, by rfl⟩ : syracuseStep 1320617 = 990463) B990463
theorem B1320827 : Blo 876568 1320827 := bstep (se 1 (by rfl) ⟨990620, by rfl⟩ : syracuseStep 1320827 = 1981241) B1981241
theorem B2959415 : Blo 876568 2959415 := bstep (se 1 (by rfl) ⟨2219561, by rfl⟩ : syracuseStep 2959415 = 4439123) B4439123
theorem B10988135 : Blo 876568 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B2960009 : Blo 876568 2960009 := bstep (se 2 (by rfl) ⟨1110003, by rfl⟩ : syracuseStep 2960009 = 2220007) B2220007
theorem B98839369 : Blo 876568 98839369 := bstep (se 2 (by rfl) ⟨37064763, by rfl⟩ : syracuseStep 98839369 = 74129527) B74129527
theorem B1977641 : Blo 876568 1977641 := bstep (se 2 (by rfl) ⟨741615, by rfl⟩ : syracuseStep 1977641 = 1483231) B1483231
theorem B19279295 : Blo 876568 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B1977839 : Blo 876568 1977839 := bstep (se 1 (by rfl) ⟨1483379, by rfl⟩ : syracuseStep 1977839 = 2966759) B2966759
theorem B7515899 : Blo 876568 7515899 := bstep (se 1 (by rfl) ⟨5636924, by rfl⟩ : syracuseStep 7515899 = 11273849) B11273849
theorem B1781995 : Blo 876568 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B2372543 : Blo 876568 2372543 := bstep (se 1 (by rfl) ⟨1779407, by rfl⟩ : syracuseStep 2372543 = 3558815) B3558815
theorem B6337619 : Blo 876568 6337619 := bstep (se 1 (by rfl) ⟨4753214, by rfl⟩ : syracuseStep 6337619 = 9506429) B9506429
theorem B2504297 : Blo 876568 2504297 := bstep (se 2 (by rfl) ⟨939111, by rfl⟩ : syracuseStep 2504297 = 1878223) B1878223
theorem B1980071 : Blo 876568 1980071 := bstep (se 1 (by rfl) ⟨1485053, by rfl⟩ : syracuseStep 1980071 = 2970107) B2970107
theorem B162903737 : Blo 876568 162903737 := bstep (se 2 (by rfl) ⟨61088901, by rfl⟩ : syracuseStep 162903737 = 122177803) B122177803
theorem B1980755 : Blo 876568 1980755 := bstep (se 1 (by rfl) ⟨1485566, by rfl⟩ : syracuseStep 1980755 = 2971133) B2971133
theorem B16924463 : Blo 876568 16924463 := bstep (se 1 (by rfl) ⟨12693347, by rfl⟩ : syracuseStep 16924463 = 25386695) B25386695
theorem B2375561 : Blo 876568 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B2965463 : Blo 876568 2965463 := bstep (se 1 (by rfl) ⟨2224097, by rfl⟩ : syracuseStep 2965463 = 4448195) B4448195
theorem B19251593 : Blo 876568 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B6668891 : Blo 876568 6668891 := bstep (se 1 (by rfl) ⟨5001668, by rfl⟩ : syracuseStep 6668891 = 10003337) B10003337
theorem B40584401 : Blo 876568 40584401 := bstep (se 2 (by rfl) ⟨15219150, by rfl⟩ : syracuseStep 40584401 = 30438301) B30438301
theorem B4015327 : Blo 876568 4015327 := bstep (se 1 (by rfl) ⟨3011495, by rfl⟩ : syracuseStep 4015327 = 6022991) B6022991
theorem B3556607 : Blo 876568 3556607 := bstep (se 1 (by rfl) ⟨2667455, by rfl⟩ : syracuseStep 3556607 = 5334911) B5334911
theorem B5064605 : Blo 876568 5064605 := bstep (se 3 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 5064605 = 1899227) B1899227
theorem B2967515 : Blo 876568 2967515 := bstep (se 1 (by rfl) ⟨2225636, by rfl⟩ : syracuseStep 2967515 = 4451273) B4451273
theorem B2967839 : Blo 876568 2967839 := bstep (se 1 (by rfl) ⟨2225879, by rfl⟩ : syracuseStep 2967839 = 4451759) B4451759
theorem B5622367 : Blo 876568 5622367 := bstep (se 1 (by rfl) ⟨4216775, by rfl⟩ : syracuseStep 5622367 = 8433551) B8433551
theorem B2968271 : Blo 876568 2968271 := bstep (se 1 (by rfl) ⟨2226203, by rfl⟩ : syracuseStep 2968271 = 4452407) B4452407
theorem B5000575 : Blo 876568 5000575 := bstep (se 1 (by rfl) ⟨3750431, by rfl⟩ : syracuseStep 5000575 = 7500863) B7500863
theorem B2969135 : Blo 876568 2969135 := bstep (se 1 (by rfl) ⟨2226851, by rfl⟩ : syracuseStep 2969135 = 4453703) B4453703
theorem B68539283 : Blo 876568 68539283 := bstep (se 1 (by rfl) ⟨51404462, by rfl⟩ : syracuseStep 68539283 = 102808925) B102808925
theorem B2971241 : Blo 876568 2971241 := bstep (se 2 (by rfl) ⟨1114215, by rfl⟩ : syracuseStep 2971241 = 2228431) B2228431
theorem B6773183 : Blo 876568 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B3759385 : Blo 876568 3759385 := bstep (se 2 (by rfl) ⟨1409769, by rfl⟩ : syracuseStep 3759385 = 2819539) B2819539
theorem B10149797 : Blo 876568 10149797 := bstep (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) B1903087
theorem B2809903 : Blo 876568 2809903 := bstep (se 1 (by rfl) ⟨2107427, by rfl⟩ : syracuseStep 2809903 = 4214855) B4214855
theorem B876655 : Blo 876568 876655 := bstep (se 1 (by rfl) ⟨657491, by rfl⟩ : syracuseStep 876655 = 1314983) B1314983
theorem B10150163 : Blo 876568 10150163 := bstep (se 1 (by rfl) ⟨7612622, by rfl⟩ : syracuseStep 10150163 = 15225245) B15225245
theorem B877295 : Blo 876568 877295 := bstep (se 1 (by rfl) ⟨657971, by rfl⟩ : syracuseStep 877295 = 1315943) B1315943
theorem B877311 : Blo 876568 877311 := bstep (se 1 (by rfl) ⟨657983, by rfl⟩ : syracuseStep 877311 = 1315967) B1315967
theorem B3335327 : Blo 876568 3335327 := bstep (se 1 (by rfl) ⟨2501495, by rfl⟩ : syracuseStep 3335327 = 5002991) B5002991
theorem B877823 : Blo 876568 877823 := bstep (se 1 (by rfl) ⟨658367, by rfl⟩ : syracuseStep 877823 = 1316735) B1316735
theorem B2254567 : Blo 876568 2254567 := bstep (se 1 (by rfl) ⟨1690925, by rfl⟩ : syracuseStep 2254567 = 3381851) B3381851
theorem B96364687 : Blo 876568 96364687 := bstep (se 1 (by rfl) ⟨72273515, by rfl⟩ : syracuseStep 96364687 = 144547031) B144547031
theorem B879647 : Blo 876568 879647 := bstep (se 1 (by rfl) ⟨659735, by rfl⟩ : syracuseStep 879647 = 1319471) B1319471
theorem B879899 : Blo 876568 879899 := bstep (se 1 (by rfl) ⟨659924, by rfl⟩ : syracuseStep 879899 = 1319849) B1319849
theorem B880079 : Blo 876568 880079 := bstep (se 1 (by rfl) ⟨660059, by rfl⟩ : syracuseStep 880079 = 1320119) B1320119
theorem B42725231 : Blo 876568 42725231 := bstep (se 1 (by rfl) ⟨32043923, by rfl⟩ : syracuseStep 42725231 = 64087847) B64087847
theorem B182809325 : Blo 876568 182809325 := bstep (se 3 (by rfl) ⟨34276748, by rfl⟩ : syracuseStep 182809325 = 68553497) B68553497
theorem B2815003 : Blo 876568 2815003 := bstep (se 1 (by rfl) ⟨2111252, by rfl⟩ : syracuseStep 2815003 = 4222505) B4222505
theorem B5011055 : Blo 876568 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B2225839 : Blo 876568 2225839 := bstep (se 1 (by rfl) ⟨1669379, by rfl⟩ : syracuseStep 2225839 = 3338759) B3338759
theorem B5633849 : Blo 876568 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B3340187 : Blo 876568 3340187 := bstep (se 1 (by rfl) ⟨2505140, by rfl⟩ : syracuseStep 3340187 = 5010281) B5010281
theorem B2226143 : Blo 876568 2226143 := bstep (se 1 (by rfl) ⟨1669607, by rfl⟩ : syracuseStep 2226143 = 3339215) B3339215
theorem B1407707 : Blo 876568 1407707 := bstep (se 1 (by rfl) ⟨1055780, by rfl⟩ : syracuseStep 1407707 = 2111561) B2111561
theorem B1112935 : Blo 876568 1112935 := bstep (se 1 (by rfl) ⟨834701, by rfl⟩ : syracuseStep 1112935 = 1669403) B1669403
theorem B9502105 : Blo 876568 9502105 := bstep (se 2 (by rfl) ⟨3563289, by rfl⟩ : syracuseStep 9502105 = 7126579) B7126579
theorem B19037767 : Blo 876568 19037767 := bstep (se 1 (by rfl) ⟨14278325, by rfl⟩ : syracuseStep 19037767 = 28556651) B28556651
theorem B3376403 : Blo 876568 3376403 := bstep (se 1 (by rfl) ⟨2532302, by rfl⟩ : syracuseStep 3376403 = 5064605) B5064605
theorem B128486249 : Blo 876568 128486249 := bstep (se 2 (by rfl) ⟨48182343, by rfl⟩ : syracuseStep 128486249 = 96364687) B96364687
theorem B986431 : Blo 876568 986431 := bstep (se 1 (by rfl) ⟨739823, by rfl⟩ : syracuseStep 986431 = 1479647) B1479647
theorem B986791 : Blo 876568 986791 := bstep (se 1 (by rfl) ⟨740093, by rfl⟩ : syracuseStep 986791 = 1480187) B1480187
theorem B108138401 : Blo 876568 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B1315067 : Blo 876568 1315067 := bstep (se 1 (by rfl) ⟨986300, by rfl⟩ : syracuseStep 1315067 = 1972601) B1972601
theorem B1315817 : Blo 876568 1315817 := bstep (se 2 (by rfl) ⟨493431, by rfl⟩ : syracuseStep 1315817 = 986863) B986863
theorem B1316393 : Blo 876568 1316393 := bstep (se 2 (by rfl) ⟨493647, by rfl⟩ : syracuseStep 1316393 = 987295) B987295
theorem B1316585 : Blo 876568 1316585 := bstep (se 2 (by rfl) ⟨493719, by rfl⟩ : syracuseStep 1316585 = 987439) B987439
theorem B1316891 : Blo 876568 1316891 := bstep (se 1 (by rfl) ⟨987668, by rfl⟩ : syracuseStep 1316891 = 1975337) B1975337
theorem B1972331 : Blo 876568 1972331 := bstep (se 1 (by rfl) ⟨1479248, by rfl⟩ : syracuseStep 1972331 = 2958497) B2958497
theorem B1972943 : Blo 876568 1972943 := bstep (se 1 (by rfl) ⟨1479707, by rfl⟩ : syracuseStep 1972943 = 2959415) B2959415
theorem B1972961 : Blo 876568 1972961 := bstep (se 2 (by rfl) ⟨739860, by rfl⟩ : syracuseStep 1972961 = 1479721) B1479721
theorem B1973339 : Blo 876568 1973339 := bstep (se 1 (by rfl) ⟨1480004, by rfl⟩ : syracuseStep 1973339 = 2960009) B2960009
theorem B1318025 : Blo 876568 1318025 := bstep (se 2 (by rfl) ⟨494259, by rfl⟩ : syracuseStep 1318025 = 988519) B988519
theorem B1318427 : Blo 876568 1318427 := bstep (se 1 (by rfl) ⟨988820, by rfl⟩ : syracuseStep 1318427 = 1977641) B1977641
theorem B12852863 : Blo 876568 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B1318559 : Blo 876568 1318559 := bstep (se 1 (by rfl) ⟨988919, by rfl⟩ : syracuseStep 1318559 = 1977839) B1977839
theorem B28483487 : Blo 876568 28483487 := bstep (se 1 (by rfl) ⟨21362615, by rfl⟩ : syracuseStep 28483487 = 42725231) B42725231
theorem B121872883 : Blo 876568 121872883 := bstep (se 1 (by rfl) ⟨91404662, by rfl⟩ : syracuseStep 121872883 = 182809325) B182809325
theorem B1581695 : Blo 876568 1581695 := bstep (se 1 (by rfl) ⟨1186271, by rfl⟩ : syracuseStep 1581695 = 2372543) B2372543
theorem B1320047 : Blo 876568 1320047 := bstep (se 1 (by rfl) ⟨990035, by rfl⟩ : syracuseStep 1320047 = 1980071) B1980071
theorem B108602491 : Blo 876568 108602491 := bstep (se 1 (by rfl) ⟨81451868, by rfl⟩ : syracuseStep 108602491 = 162903737) B162903737
theorem B1483913 : Blo 876568 1483913 := bstep (se 2 (by rfl) ⟨556467, by rfl⟩ : syracuseStep 1483913 = 1112935) B1112935
theorem B1484095 : Blo 876568 1484095 := bstep (se 1 (by rfl) ⟨1113071, by rfl⟩ : syracuseStep 1484095 = 2226143) B2226143
theorem B1320503 : Blo 876568 1320503 := bstep (se 1 (by rfl) ⟨990377, by rfl⟩ : syracuseStep 1320503 = 1980755) B1980755
theorem B11282975 : Blo 876568 11282975 := bstep (se 1 (by rfl) ⟨8462231, by rfl⟩ : syracuseStep 11282975 = 16924463) B16924463
theorem B1583707 : Blo 876568 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B1976975 : Blo 876568 1976975 := bstep (se 1 (by rfl) ⟨1482731, by rfl⟩ : syracuseStep 1976975 = 2965463) B2965463
theorem B3746537 : Blo 876568 3746537 := bstep (se 2 (by rfl) ⟨1404951, by rfl⟩ : syracuseStep 3746537 = 2809903) B2809903
theorem B1977569 : Blo 876568 1977569 := bstep (se 2 (by rfl) ⟨741588, by rfl⟩ : syracuseStep 1977569 = 1483177) B1483177
theorem B1978343 : Blo 876568 1978343 := bstep (se 1 (by rfl) ⟨1483757, by rfl⟩ : syracuseStep 1978343 = 2967515) B2967515
theorem B1978559 : Blo 876568 1978559 := bstep (se 1 (by rfl) ⟨1483919, by rfl⟩ : syracuseStep 1978559 = 2967839) B2967839
theorem B5353769 : Blo 876568 5353769 := bstep (se 2 (by rfl) ⟨2007663, by rfl⟩ : syracuseStep 5353769 = 4015327) B4015327
theorem B1978847 : Blo 876568 1978847 := bstep (se 1 (by rfl) ⟨1484135, by rfl⟩ : syracuseStep 1978847 = 2968271) B2968271
theorem B1979423 : Blo 876568 1979423 := bstep (se 1 (by rfl) ⟨1484567, by rfl⟩ : syracuseStep 1979423 = 2969135) B2969135
theorem B56997047 : Blo 876568 56997047 := bstep (se 1 (by rfl) ⟨42747785, by rfl⟩ : syracuseStep 56997047 = 85495571) B85495571
theorem B45692855 : Blo 876568 45692855 := bstep (se 1 (by rfl) ⟨34269641, by rfl⟩ : syracuseStep 45692855 = 68539283) B68539283
theorem B9484285 : Blo 876568 9484285 := bstep (se 3 (by rfl) ⟨1778303, by rfl⟩ : syracuseStep 9484285 = 3556607) B3556607
theorem B6666461 : Blo 876568 6666461 := bstep (se 3 (by rfl) ⟨1249961, by rfl⟩ : syracuseStep 6666461 = 2499923) B2499923
theorem B1980827 : Blo 876568 1980827 := bstep (se 1 (by rfl) ⟨1485620, by rfl⟩ : syracuseStep 1980827 = 2971241) B2971241
theorem B6667433 : Blo 876568 6667433 := bstep (se 2 (by rfl) ⟨2500287, by rfl⟩ : syracuseStep 6667433 = 5000575) B5000575
theorem B11255759 : Blo 876568 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B6766775 : Blo 876568 6766775 := bstep (se 1 (by rfl) ⟨5075081, by rfl⟩ : syracuseStep 6766775 = 10150163) B10150163
theorem B2375993 : Blo 876568 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B3753337 : Blo 876568 3753337 := bstep (se 2 (by rfl) ⟨1407501, by rfl⟩ : syracuseStep 3753337 = 2815003) B2815003
theorem B7325423 : Blo 876568 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B18040805 : Blo 876568 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B2967785 : Blo 876568 2967785 := bstep (se 2 (by rfl) ⟨1112919, by rfl⟩ : syracuseStep 2967785 = 2225839) B2225839
theorem B3755899 : Blo 876568 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B938471 : Blo 876568 938471 := bstep (se 1 (by rfl) ⟨703853, by rfl⟩ : syracuseStep 938471 = 1407707) B1407707
theorem B12669473 : Blo 876568 12669473 := bstep (se 2 (by rfl) ⟨4751052, by rfl⟩ : syracuseStep 12669473 = 9502105) B9502105
theorem B25383689 : Blo 876568 25383689 := bstep (se 2 (by rfl) ⟨9518883, by rfl⟩ : syracuseStep 25383689 = 19037767) B19037767
theorem B1201535 : Blo 876568 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B12834395 : Blo 876568 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B4445927 : Blo 876568 4445927 := bstep (se 1 (by rfl) ⟨3334445, by rfl⟩ : syracuseStep 4445927 = 6668891) B6668891
theorem B27056267 : Blo 876568 27056267 := bstep (se 1 (by rfl) ⟨20292200, by rfl⟩ : syracuseStep 27056267 = 40584401) B40584401
theorem B3006089 : Blo 876568 3006089 := bstep (se 2 (by rfl) ⟨1127283, by rfl⟩ : syracuseStep 3006089 = 2254567) B2254567
theorem B876703 : Blo 876568 876703 := bstep (se 1 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 876703 = 1315055) B1315055
theorem B876795 : Blo 876568 876795 := bstep (se 1 (by rfl) ⟨657596, by rfl⟩ : syracuseStep 876795 = 1315193) B1315193
theorem B877247 : Blo 876568 877247 := bstep (se 1 (by rfl) ⟨657935, by rfl⟩ : syracuseStep 877247 = 1315871) B1315871
theorem B7496489 : Blo 876568 7496489 := bstep (se 2 (by rfl) ⟨2811183, by rfl⟩ : syracuseStep 7496489 = 5622367) B5622367
theorem B877403 : Blo 876568 877403 := bstep (se 1 (by rfl) ⟨658052, by rfl⟩ : syracuseStep 877403 = 1316105) B1316105
theorem B877415 : Blo 876568 877415 := bstep (se 1 (by rfl) ⟨658061, by rfl⟩ : syracuseStep 877415 = 1316123) B1316123
theorem B877599 : Blo 876568 877599 := bstep (se 1 (by rfl) ⟨658199, by rfl⟩ : syracuseStep 877599 = 1316399) B1316399
theorem B131785825 : Blo 876568 131785825 := bstep (se 2 (by rfl) ⟨49419684, by rfl⟩ : syracuseStep 131785825 = 98839369) B98839369
theorem B877851 : Blo 876568 877851 := bstep (se 1 (by rfl) ⟨658388, by rfl⟩ : syracuseStep 877851 = 1316777) B1316777
theorem B1664489 : Blo 876568 1664489 := bstep (se 2 (by rfl) ⟨624183, by rfl⟩ : syracuseStep 1664489 = 1248367) B1248367
theorem B6678125 : Blo 876568 6678125 := bstep (se 3 (by rfl) ⟨1252148, by rfl⟩ : syracuseStep 6678125 = 2504297) B2504297
theorem B4515455 : Blo 876568 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B878847 : Blo 876568 878847 := bstep (se 1 (by rfl) ⟨659135, by rfl⟩ : syracuseStep 878847 = 1318271) B1318271
theorem B879215 : Blo 876568 879215 := bstep (se 1 (by rfl) ⟨659411, by rfl⟩ : syracuseStep 879215 = 1318823) B1318823
theorem B879335 : Blo 876568 879335 := bstep (se 1 (by rfl) ⟨659501, by rfl⟩ : syracuseStep 879335 = 1319003) B1319003
theorem B1141499 : Blo 876568 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B6318911 : Blo 876568 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B879471 : Blo 876568 879471 := bstep (se 1 (by rfl) ⟨659603, by rfl⟩ : syracuseStep 879471 = 1319207) B1319207
theorem B2223551 : Blo 876568 2223551 := bstep (se 1 (by rfl) ⟨1667663, by rfl⟩ : syracuseStep 2223551 = 3335327) B3335327
theorem B880411 : Blo 876568 880411 := bstep (se 1 (by rfl) ⟨660308, by rfl⟩ : syracuseStep 880411 = 1320617) B1320617
theorem B880551 : Blo 876568 880551 := bstep (se 1 (by rfl) ⟨660413, by rfl⟩ : syracuseStep 880551 = 1320827) B1320827
theorem B5010599 : Blo 876568 5010599 := bstep (se 1 (by rfl) ⟨3757949, by rfl⟩ : syracuseStep 5010599 = 7515899) B7515899
theorem B4225079 : Blo 876568 4225079 := bstep (se 1 (by rfl) ⟨3168809, by rfl⟩ : syracuseStep 4225079 = 6337619) B6337619
theorem B3340703 : Blo 876568 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B2226791 : Blo 876568 2226791 := bstep (se 1 (by rfl) ⟨1670093, by rfl⟩ : syracuseStep 2226791 = 3340187) B3340187
theorem B5012513 : Blo 876568 5012513 := bstep (se 2 (by rfl) ⟨1879692, by rfl⟩ : syracuseStep 5012513 = 3759385) B3759385
theorem B27066125 : Blo 876568 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B162497177 : Blo 876568 162497177 := bstep (se 2 (by rfl) ⟨60936441, by rfl⟩ : syracuseStep 162497177 = 121872883) B121872883
theorem B4883615 : Blo 876568 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B12027203 : Blo 876568 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B144803321 : Blo 876568 144803321 := bstep (se 2 (by rfl) ⟨54301245, by rfl⟩ : syracuseStep 144803321 = 108602491) B108602491
theorem B85657499 : Blo 876568 85657499 := bstep (se 1 (by rfl) ⟨64243124, by rfl⟩ : syracuseStep 85657499 = 128486249) B128486249
theorem B72092267 : Blo 876568 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B8556263 : Blo 876568 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B12816373 : Blo 876568 12816373 := bstep (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) B1201535
theorem B1314887 : Blo 876568 1314887 := bstep (se 1 (by rfl) ⟨986165, by rfl⟩ : syracuseStep 1314887 = 1972331) B1972331
theorem B1315241 : Blo 876568 1315241 := bstep (se 2 (by rfl) ⟨493215, by rfl⟩ : syracuseStep 1315241 = 986431) B986431
theorem B1315295 : Blo 876568 1315295 := bstep (se 1 (by rfl) ⟨986471, by rfl⟩ : syracuseStep 1315295 = 1972943) B1972943
theorem B1315307 : Blo 876568 1315307 := bstep (se 1 (by rfl) ⟨986480, by rfl⟩ : syracuseStep 1315307 = 1972961) B1972961
theorem B1315559 : Blo 876568 1315559 := bstep (se 1 (by rfl) ⟨986669, by rfl⟩ : syracuseStep 1315559 = 1973339) B1973339
theorem B1315721 : Blo 876568 1315721 := bstep (se 2 (by rfl) ⟨493395, by rfl⟩ : syracuseStep 1315721 = 986791) B986791
theorem B2004059 : Blo 876568 2004059 := bstep (se 1 (by rfl) ⟨1503044, by rfl⟩ : syracuseStep 2004059 = 3006089) B3006089
theorem B1054463 : Blo 876568 1054463 := bstep (se 1 (by rfl) ⟨790847, by rfl⟩ : syracuseStep 1054463 = 1581695) B1581695
theorem B989275 : Blo 876568 989275 := bstep (se 1 (by rfl) ⟨741956, by rfl⟩ : syracuseStep 989275 = 1483913) B1483913
theorem B1317983 : Blo 876568 1317983 := bstep (se 1 (by rfl) ⟨988487, by rfl⟩ : syracuseStep 1317983 = 1976975) B1976975
theorem B2497691 : Blo 876568 2497691 := bstep (se 1 (by rfl) ⟨1873268, by rfl⟩ : syracuseStep 2497691 = 3746537) B3746537
theorem B1318379 : Blo 876568 1318379 := bstep (se 1 (by rfl) ⟨988784, by rfl⟩ : syracuseStep 1318379 = 1977569) B1977569
theorem B1482367 : Blo 876568 1482367 := bstep (se 1 (by rfl) ⟨1111775, by rfl⟩ : syracuseStep 1482367 = 2223551) B2223551
theorem B1318895 : Blo 876568 1318895 := bstep (se 1 (by rfl) ⟨989171, by rfl⟩ : syracuseStep 1318895 = 1978343) B1978343
theorem B1319039 : Blo 876568 1319039 := bstep (se 1 (by rfl) ⟨989279, by rfl⟩ : syracuseStep 1319039 = 1978559) B1978559
theorem B1319231 : Blo 876568 1319231 := bstep (se 1 (by rfl) ⟨989423, by rfl⟩ : syracuseStep 1319231 = 1978847) B1978847
theorem B1319615 : Blo 876568 1319615 := bstep (se 1 (by rfl) ⟨989711, by rfl⟩ : syracuseStep 1319615 = 1979423) B1979423
theorem B1320551 : Blo 876568 1320551 := bstep (se 1 (by rfl) ⟨990413, by rfl⟩ : syracuseStep 1320551 = 1980827) B1980827
theorem B1484527 : Blo 876568 1484527 := bstep (se 1 (by rfl) ⟨1113395, by rfl⟩ : syracuseStep 1484527 = 2226791) B2226791
theorem B6335981 : Blo 876568 6335981 := bstep (se 3 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 6335981 = 2375993) B2375993
theorem B2502589 : Blo 876568 2502589 := bstep (se 3 (by rfl) ⟨469235, by rfl⟩ : syracuseStep 2502589 = 938471) B938471
theorem B175714433 : Blo 876568 175714433 := bstep (se 2 (by rfl) ⟨65892912, by rfl⟩ : syracuseStep 175714433 = 131785825) B131785825
theorem B1978523 : Blo 876568 1978523 := bstep (se 1 (by rfl) ⟨1483892, by rfl⟩ : syracuseStep 1978523 = 2967785) B2967785
theorem B1978793 : Blo 876568 1978793 := bstep (se 2 (by rfl) ⟨742047, by rfl⟩ : syracuseStep 1978793 = 1484095) B1484095
theorem B16922459 : Blo 876568 16922459 := bstep (se 1 (by rfl) ⟨12691844, by rfl⟩ : syracuseStep 16922459 = 25383689) B25383689
theorem B2111609 : Blo 876568 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B2963951 : Blo 876568 2963951 := bstep (se 1 (by rfl) ⟨2222963, by rfl⟩ : syracuseStep 2963951 = 4445927) B4445927
theorem B4438637 : Blo 876568 4438637 := bstep (se 3 (by rfl) ⟨832244, by rfl⟩ : syracuseStep 4438637 = 1664489) B1664489
theorem B18037511 : Blo 876568 18037511 := bstep (se 1 (by rfl) ⟨13528133, by rfl⟩ : syracuseStep 18037511 = 27056267) B27056267
theorem B8568575 : Blo 876568 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B18988991 : Blo 876568 18988991 := bstep (se 1 (by rfl) ⟨14241743, by rfl⟩ : syracuseStep 18988991 = 28483487) B28483487
theorem B4997659 : Blo 876568 4997659 := bstep (se 1 (by rfl) ⟨3748244, by rfl⟩ : syracuseStep 4997659 = 7496489) B7496489
theorem B7521983 : Blo 876568 7521983 := bstep (se 1 (by rfl) ⟨5641487, by rfl⟩ : syracuseStep 7521983 = 11282975) B11282975
theorem B4212607 : Blo 876568 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B37998031 : Blo 876568 37998031 := bstep (se 1 (by rfl) ⟨28498523, by rfl⟩ : syracuseStep 37998031 = 56997047) B56997047
theorem B30461903 : Blo 876568 30461903 := bstep (se 1 (by rfl) ⟨22846427, by rfl⟩ : syracuseStep 30461903 = 45692855) B45692855
theorem B4444307 : Blo 876568 4444307 := bstep (se 1 (by rfl) ⟨3333230, by rfl⟩ : syracuseStep 4444307 = 6666461) B6666461
theorem B4444955 : Blo 876568 4444955 := bstep (se 1 (by rfl) ⟨3333716, by rfl⟩ : syracuseStep 4444955 = 6667433) B6667433
theorem B18044083 : Blo 876568 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B4511183 : Blo 876568 4511183 := bstep (se 1 (by rfl) ⟨3383387, by rfl⟩ : syracuseStep 4511183 = 6766775) B6766775
theorem B2250935 : Blo 876568 2250935 := bstep (se 1 (by rfl) ⟨1688201, by rfl⟩ : syracuseStep 2250935 = 3376403) B3376403
theorem B5004449 : Blo 876568 5004449 := bstep (se 2 (by rfl) ⟨1876668, by rfl⟩ : syracuseStep 5004449 = 3753337) B3753337
theorem B876711 : Blo 876568 876711 := bstep (se 1 (by rfl) ⟨657533, by rfl⟩ : syracuseStep 876711 = 1315067) B1315067
theorem B8446315 : Blo 876568 8446315 := bstep (se 1 (by rfl) ⟨6334736, by rfl⟩ : syracuseStep 8446315 = 12669473) B12669473
theorem B877211 : Blo 876568 877211 := bstep (se 1 (by rfl) ⟨657908, by rfl⟩ : syracuseStep 877211 = 1315817) B1315817
theorem B877595 : Blo 876568 877595 := bstep (se 1 (by rfl) ⟨658196, by rfl⟩ : syracuseStep 877595 = 1316393) B1316393
theorem B877723 : Blo 876568 877723 := bstep (se 1 (by rfl) ⟨658292, by rfl⟩ : syracuseStep 877723 = 1316585) B1316585
theorem B877927 : Blo 876568 877927 := bstep (se 1 (by rfl) ⟨658445, by rfl⟩ : syracuseStep 877927 = 1316891) B1316891
theorem B878683 : Blo 876568 878683 := bstep (se 1 (by rfl) ⟨659012, by rfl⟩ : syracuseStep 878683 = 1318025) B1318025
theorem B878951 : Blo 876568 878951 := bstep (se 1 (by rfl) ⟨659213, by rfl⟩ : syracuseStep 878951 = 1318427) B1318427
theorem B879039 : Blo 876568 879039 := bstep (se 1 (by rfl) ⟨659279, by rfl⟩ : syracuseStep 879039 = 1318559) B1318559
theorem B5007865 : Blo 876568 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B11266877 : Blo 876568 11266877 := bstep (se 3 (by rfl) ⟨2112539, by rfl⟩ : syracuseStep 11266877 = 4225079) B4225079
theorem B880031 : Blo 876568 880031 := bstep (se 1 (by rfl) ⟨660023, by rfl⟩ : syracuseStep 880031 = 1320047) B1320047
theorem B880335 : Blo 876568 880335 := bstep (se 1 (by rfl) ⟨660251, by rfl⟩ : syracuseStep 880335 = 1320503) B1320503
theorem B4452083 : Blo 876568 4452083 := bstep (se 1 (by rfl) ⟨3339062, by rfl⟩ : syracuseStep 4452083 = 6678125) B6678125
theorem B3010303 : Blo 876568 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B3043997 : Blo 876568 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B12645713 : Blo 876568 12645713 := bstep (se 2 (by rfl) ⟨4742142, by rfl⟩ : syracuseStep 12645713 = 9484285) B9484285
theorem B3569179 : Blo 876568 3569179 := bstep (se 1 (by rfl) ⟨2676884, by rfl⟩ : syracuseStep 3569179 = 5353769) B5353769
theorem B3340399 : Blo 876568 3340399 := bstep (se 1 (by rfl) ⟨2505299, by rfl⟩ : syracuseStep 3340399 = 5010599) B5010599
theorem B2227135 : Blo 876568 2227135 := bstep (se 1 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 2227135 = 3340703) B3340703
theorem B3341675 : Blo 876568 3341675 := bstep (se 1 (by rfl) ⟨2506256, by rfl⟩ : syracuseStep 3341675 = 5012513) B5012513
theorem B7503839 : Blo 876568 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B108331451 : Blo 876568 108331451 := bstep (se 1 (by rfl) ⟨81248588, by rfl⟩ : syracuseStep 108331451 = 162497177) B162497177
theorem B96535547 : Blo 876568 96535547 := bstep (se 1 (by rfl) ⟨72401660, by rfl⟩ : syracuseStep 96535547 = 144803321) B144803321
theorem B5014655 : Blo 876568 5014655 := bstep (se 1 (by rfl) ⟨3760991, by rfl⟩ : syracuseStep 5014655 = 7521983) B7521983
theorem B5704175 : Blo 876568 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B5344157 : Blo 876568 5344157 := bstep (se 3 (by rfl) ⟨1002029, by rfl⟩ : syracuseStep 5344157 = 2004059) B2004059
theorem B50664041 : Blo 876568 50664041 := bstep (se 2 (by rfl) ⟨18999015, by rfl⟩ : syracuseStep 50664041 = 37998031) B37998031
theorem B24058777 : Blo 876568 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B7511251 : Blo 876568 7511251 := bstep (se 1 (by rfl) ⟨5633438, by rfl⟩ : syracuseStep 7511251 = 11266877) B11266877
theorem B4758905 : Blo 876568 4758905 := bstep (se 2 (by rfl) ⟨1784589, by rfl⟩ : syracuseStep 4758905 = 3569179) B3569179
theorem B11247605 : Blo 876568 11247605 := bstep (se 5 (by rfl) ⟨527231, by rfl⟩ : syracuseStep 11247605 = 1054463) B1054463
theorem B1319015 : Blo 876568 1319015 := bstep (se 1 (by rfl) ⟨989261, by rfl⟩ : syracuseStep 1319015 = 1978523) B1978523
theorem B1319033 : Blo 876568 1319033 := bstep (se 2 (by rfl) ⟨494637, by rfl⟩ : syracuseStep 1319033 = 989275) B989275
theorem B1319195 : Blo 876568 1319195 := bstep (se 1 (by rfl) ⟨989396, by rfl⟩ : syracuseStep 1319195 = 1978793) B1978793
theorem B8430475 : Blo 876568 8430475 := bstep (se 1 (by rfl) ⟨6322856, by rfl⟩ : syracuseStep 8430475 = 12645713) B12645713
theorem B11281639 : Blo 876568 11281639 := bstep (se 1 (by rfl) ⟨8461229, by rfl⟩ : syracuseStep 11281639 = 16922459) B16922459
theorem B1975967 : Blo 876568 1975967 := bstep (se 1 (by rfl) ⟨1481975, by rfl⟩ : syracuseStep 1975967 = 2963951) B2963951
theorem B2959091 : Blo 876568 2959091 := bstep (se 1 (by rfl) ⟨2219318, by rfl⟩ : syracuseStep 2959091 = 4438637) B4438637
theorem B1976489 : Blo 876568 1976489 := bstep (se 2 (by rfl) ⟨741183, by rfl⟩ : syracuseStep 1976489 = 1482367) B1482367
theorem B5712383 : Blo 876568 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B12659327 : Blo 876568 12659327 := bstep (se 1 (by rfl) ⟨9494495, by rfl⟩ : syracuseStep 12659327 = 18988991) B18988991
theorem B6663545 : Blo 876568 6663545 := bstep (se 2 (by rfl) ⟨2498829, by rfl⟩ : syracuseStep 6663545 = 4997659) B4997659
theorem B3255743 : Blo 876568 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B1979369 : Blo 876568 1979369 := bstep (se 2 (by rfl) ⟨742263, by rfl⟩ : syracuseStep 1979369 = 1484527) B1484527
theorem B5616809 : Blo 876568 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B2962871 : Blo 876568 2962871 := bstep (se 1 (by rfl) ⟨2222153, by rfl⟩ : syracuseStep 2962871 = 4444307) B4444307
theorem B2963303 : Blo 876568 2963303 := bstep (se 1 (by rfl) ⟨2222477, by rfl⟩ : syracuseStep 2963303 = 4444955) B4444955
theorem B48119285 : Blo 876568 48119285 := bstep (se 5 (by rfl) ⟨2255591, by rfl⟩ : syracuseStep 48119285 = 4511183) B4511183
theorem B17088497 : Blo 876568 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B2968055 : Blo 876568 2968055 := bstep (se 1 (by rfl) ⟨2226041, by rfl⟩ : syracuseStep 2968055 = 4452083) B4452083
theorem B2969513 : Blo 876568 2969513 := bstep (se 2 (by rfl) ⟨1113567, by rfl⟩ : syracuseStep 2969513 = 2227135) B2227135
theorem B5002559 : Blo 876568 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B11261753 : Blo 876568 11261753 := bstep (se 2 (by rfl) ⟨4223157, by rfl⟩ : syracuseStep 11261753 = 8446315) B8446315
theorem B8018135 : Blo 876568 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B57104999 : Blo 876568 57104999 := bstep (se 1 (by rfl) ⟨42828749, by rfl⟩ : syracuseStep 57104999 = 85657499) B85657499
theorem B48061511 : Blo 876568 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B20307935 : Blo 876568 20307935 := bstep (se 1 (by rfl) ⟨15230951, by rfl⟩ : syracuseStep 20307935 = 30461903) B30461903
theorem B876591 : Blo 876568 876591 := bstep (se 1 (by rfl) ⟨657443, by rfl⟩ : syracuseStep 876591 = 1314887) B1314887
theorem B876827 : Blo 876568 876827 := bstep (se 1 (by rfl) ⟨657620, by rfl⟩ : syracuseStep 876827 = 1315241) B1315241
theorem B876863 : Blo 876568 876863 := bstep (se 1 (by rfl) ⟨657647, by rfl⟩ : syracuseStep 876863 = 1315295) B1315295
theorem B876871 : Blo 876568 876871 := bstep (se 1 (by rfl) ⟨657653, by rfl⟩ : syracuseStep 876871 = 1315307) B1315307
theorem B877039 : Blo 876568 877039 := bstep (se 1 (by rfl) ⟨657779, by rfl⟩ : syracuseStep 877039 = 1315559) B1315559
theorem B877147 : Blo 876568 877147 := bstep (se 1 (by rfl) ⟨657860, by rfl⟩ : syracuseStep 877147 = 1315721) B1315721
theorem B6677153 : Blo 876568 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B1500623 : Blo 876568 1500623 := bstep (se 1 (by rfl) ⟨1125467, by rfl⟩ : syracuseStep 1500623 = 2250935) B2250935
theorem B878655 : Blo 876568 878655 := bstep (se 1 (by rfl) ⟨658991, by rfl⟩ : syracuseStep 878655 = 1317983) B1317983
theorem B1665127 : Blo 876568 1665127 := bstep (se 1 (by rfl) ⟨1248845, by rfl⟩ : syracuseStep 1665127 = 2497691) B2497691
theorem B3336299 : Blo 876568 3336299 := bstep (se 1 (by rfl) ⟨2502224, by rfl⟩ : syracuseStep 3336299 = 5004449) B5004449
theorem B878919 : Blo 876568 878919 := bstep (se 1 (by rfl) ⟨659189, by rfl⟩ : syracuseStep 878919 = 1318379) B1318379
theorem B3336785 : Blo 876568 3336785 := bstep (se 2 (by rfl) ⟨1251294, by rfl⟩ : syracuseStep 3336785 = 2502589) B2502589
theorem B879263 : Blo 876568 879263 := bstep (se 1 (by rfl) ⟨659447, by rfl⟩ : syracuseStep 879263 = 1318895) B1318895
theorem B879359 : Blo 876568 879359 := bstep (se 1 (by rfl) ⟨659519, by rfl⟩ : syracuseStep 879359 = 1319039) B1319039
theorem B879487 : Blo 876568 879487 := bstep (se 1 (by rfl) ⟨659615, by rfl⟩ : syracuseStep 879487 = 1319231) B1319231
theorem B5630957 : Blo 876568 5630957 := bstep (se 3 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 5630957 = 2111609) B2111609
theorem B879743 : Blo 876568 879743 := bstep (se 1 (by rfl) ⟨659807, by rfl⟩ : syracuseStep 879743 = 1319615) B1319615
theorem B880367 : Blo 876568 880367 := bstep (se 1 (by rfl) ⟨660275, by rfl⟩ : syracuseStep 880367 = 1320551) B1320551
theorem B4223987 : Blo 876568 4223987 := bstep (se 1 (by rfl) ⟨3167990, by rfl⟩ : syracuseStep 4223987 = 6335981) B6335981
theorem B117142955 : Blo 876568 117142955 := bstep (se 1 (by rfl) ⟨87857216, by rfl⟩ : syracuseStep 117142955 = 175714433) B175714433
theorem B4453865 : Blo 876568 4453865 := bstep (se 2 (by rfl) ⟨1670199, by rfl⟩ : syracuseStep 4453865 = 3340399) B3340399
theorem B2029331 : Blo 876568 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B16054949 : Blo 876568 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B12025007 : Blo 876568 12025007 := bstep (se 1 (by rfl) ⟨9018755, by rfl⟩ : syracuseStep 12025007 = 18037511) B18037511
theorem B2227783 : Blo 876568 2227783 := bstep (se 1 (by rfl) ⟨1670837, by rfl⟩ : syracuseStep 2227783 = 3341675) B3341675
theorem B72220967 : Blo 876568 72220967 := bstep (se 1 (by rfl) ⟨54165725, by rfl⟩ : syracuseStep 72220967 = 108331451) B108331451
theorem B64357031 : Blo 876568 64357031 := bstep (se 1 (by rfl) ⟨48267773, by rfl⟩ : syracuseStep 64357031 = 96535547) B96535547
theorem B3343103 : Blo 876568 3343103 := bstep (se 1 (by rfl) ⟨2507327, by rfl⟩ : syracuseStep 3343103 = 5014655) B5014655
theorem B11240633 : Blo 876568 11240633 := bstep (se 2 (by rfl) ⟨4215237, by rfl⟩ : syracuseStep 11240633 = 8430475) B8430475
theorem B15042185 : Blo 876568 15042185 := bstep (se 2 (by rfl) ⟨5640819, by rfl⟩ : syracuseStep 15042185 = 11281639) B11281639
theorem B3802783 : Blo 876568 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B7507835 : Blo 876568 7507835 := bstep (se 1 (by rfl) ⟨5630876, by rfl⟩ : syracuseStep 7507835 = 11261753) B11261753
theorem B5345423 : Blo 876568 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B5411549 : Blo 876568 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B13538623 : Blo 876568 13538623 := bstep (se 1 (by rfl) ⟨10153967, by rfl⟩ : syracuseStep 13538623 = 20307935) B20307935
theorem B1317311 : Blo 876568 1317311 := bstep (se 1 (by rfl) ⟨987983, by rfl⟩ : syracuseStep 1317311 = 1975967) B1975967
theorem B1972727 : Blo 876568 1972727 := bstep (se 1 (by rfl) ⟨1479545, by rfl⟩ : syracuseStep 1972727 = 2959091) B2959091
theorem B1317659 : Blo 876568 1317659 := bstep (se 1 (by rfl) ⟨988244, by rfl⟩ : syracuseStep 1317659 = 1976489) B1976489
theorem B3808255 : Blo 876568 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B2170495 : Blo 876568 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B1319579 : Blo 876568 1319579 := bstep (se 1 (by rfl) ⟨989684, by rfl⟩ : syracuseStep 1319579 = 1979369) B1979369
theorem B3744539 : Blo 876568 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B78095303 : Blo 876568 78095303 := bstep (se 1 (by rfl) ⟨58571477, by rfl⟩ : syracuseStep 78095303 = 117142955) B117142955
theorem B1975247 : Blo 876568 1975247 := bstep (se 1 (by rfl) ⟨1481435, by rfl⟩ : syracuseStep 1975247 = 2962871) B2962871
theorem B1975535 : Blo 876568 1975535 := bstep (se 1 (by rfl) ⟨1481651, by rfl⟩ : syracuseStep 1975535 = 2963303) B2963303
theorem B1978703 : Blo 876568 1978703 := bstep (se 1 (by rfl) ⟨1484027, by rfl⟩ : syracuseStep 1978703 = 2968055) B2968055
theorem B1979675 : Blo 876568 1979675 := bstep (se 1 (by rfl) ⟨1484756, by rfl⟩ : syracuseStep 1979675 = 2969513) B2969513
theorem B1000415 : Blo 876568 1000415 := bstep (se 1 (by rfl) ⟨750311, by rfl⟩ : syracuseStep 1000415 = 1500623) B1500623
theorem B8439551 : Blo 876568 8439551 := bstep (se 1 (by rfl) ⟨6329663, by rfl⟩ : syracuseStep 8439551 = 12659327) B12659327
theorem B3753971 : Blo 876568 3753971 := bstep (se 1 (by rfl) ⟨2815478, by rfl⟩ : syracuseStep 3753971 = 5630957) B5630957
theorem B4442363 : Blo 876568 4442363 := bstep (se 1 (by rfl) ⟨3331772, by rfl⟩ : syracuseStep 4442363 = 6663545) B6663545
theorem B2969243 : Blo 876568 2969243 := bstep (se 1 (by rfl) ⟨2226932, by rfl⟩ : syracuseStep 2969243 = 4453865) B4453865
theorem B10015001 : Blo 876568 10015001 := bstep (se 2 (by rfl) ⟨3755625, by rfl⟩ : syracuseStep 10015001 = 7511251) B7511251
theorem B10703299 : Blo 876568 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B2970377 : Blo 876568 2970377 := bstep (se 2 (by rfl) ⟨1113891, by rfl⟩ : syracuseStep 2970377 = 2227783) B2227783
theorem B8016671 : Blo 876568 8016671 := bstep (se 1 (by rfl) ⟨6012503, by rfl⟩ : syracuseStep 8016671 = 12025007) B12025007
theorem B11392331 : Blo 876568 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B2220169 : Blo 876568 2220169 := bstep (se 2 (by rfl) ⟨832563, by rfl⟩ : syracuseStep 2220169 = 1665127) B1665127
theorem B33776027 : Blo 876568 33776027 := bstep (se 1 (by rfl) ⟨25332020, by rfl⟩ : syracuseStep 33776027 = 50664041) B50664041
theorem B3335039 : Blo 876568 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B38069999 : Blo 876568 38069999 := bstep (se 1 (by rfl) ⟨28552499, by rfl⟩ : syracuseStep 38069999 = 57104999) B57104999
theorem B32041007 : Blo 876568 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B3172603 : Blo 876568 3172603 := bstep (se 1 (by rfl) ⟨2379452, by rfl⟩ : syracuseStep 3172603 = 4758905) B4758905
theorem B7498403 : Blo 876568 7498403 := bstep (se 1 (by rfl) ⟨5623802, by rfl⟩ : syracuseStep 7498403 = 11247605) B11247605
theorem B879343 : Blo 876568 879343 := bstep (se 1 (by rfl) ⟨659507, by rfl⟩ : syracuseStep 879343 = 1319015) B1319015
theorem B879355 : Blo 876568 879355 := bstep (se 1 (by rfl) ⟨659516, by rfl⟩ : syracuseStep 879355 = 1319033) B1319033
theorem B879463 : Blo 876568 879463 := bstep (se 1 (by rfl) ⟨659597, by rfl⟩ : syracuseStep 879463 = 1319195) B1319195
theorem B4451435 : Blo 876568 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B2224199 : Blo 876568 2224199 := bstep (se 1 (by rfl) ⟨1668149, by rfl⟩ : syracuseStep 2224199 = 3336299) B3336299
theorem B2224523 : Blo 876568 2224523 := bstep (se 1 (by rfl) ⟨1668392, by rfl⟩ : syracuseStep 2224523 = 3336785) B3336785
theorem B14251085 : Blo 876568 14251085 := bstep (se 3 (by rfl) ⟨2672078, by rfl⟩ : syracuseStep 14251085 = 5344157) B5344157
theorem B2815991 : Blo 876568 2815991 := bstep (se 1 (by rfl) ⟨2111993, by rfl⟩ : syracuseStep 2815991 = 4223987) B4223987
theorem B32078369 : Blo 876568 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B128318093 : Blo 876568 128318093 := bstep (se 3 (by rfl) ⟨24059642, by rfl⟩ : syracuseStep 128318093 = 48119285) B48119285
theorem B2228735 : Blo 876568 2228735 := bstep (se 1 (by rfl) ⟨1671551, by rfl⟩ : syracuseStep 2228735 = 3343103) B3343103
theorem B10028123 : Blo 876568 10028123 := bstep (se 1 (by rfl) ⟨7521092, by rfl⟩ : syracuseStep 10028123 = 15042185) B15042185
theorem B4230137 : Blo 876568 4230137 := bstep (se 2 (by rfl) ⟨1586301, by rfl⟩ : syracuseStep 4230137 = 3172603) B3172603
theorem B30379549 : Blo 876568 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B1315151 : Blo 876568 1315151 := bstep (se 1 (by rfl) ⟨986363, by rfl⟩ : syracuseStep 1315151 = 1972727) B1972727
theorem B22517351 : Blo 876568 22517351 := bstep (se 1 (by rfl) ⟨16888013, by rfl⟩ : syracuseStep 22517351 = 33776027) B33776027
theorem B2496359 : Blo 876568 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B1316831 : Blo 876568 1316831 := bstep (se 1 (by rfl) ⟨987623, by rfl⟩ : syracuseStep 1316831 = 1975247) B1975247
theorem B1317023 : Blo 876568 1317023 := bstep (se 1 (by rfl) ⟨987767, by rfl⟩ : syracuseStep 1317023 = 1975535) B1975535
theorem B1482799 : Blo 876568 1482799 := bstep (se 1 (by rfl) ⟨1112099, by rfl⟩ : syracuseStep 1482799 = 2224199) B2224199
theorem B1319135 : Blo 876568 1319135 := bstep (se 1 (by rfl) ⟨989351, by rfl⟩ : syracuseStep 1319135 = 1978703) B1978703
theorem B1483015 : Blo 876568 1483015 := bstep (se 1 (by rfl) ⟨1112261, by rfl⟩ : syracuseStep 1483015 = 2224523) B2224523
theorem B11575973 : Blo 876568 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B1319783 : Blo 876568 1319783 := bstep (se 1 (by rfl) ⟨989837, by rfl⟩ : syracuseStep 1319783 = 1979675) B1979675
theorem B1877327 : Blo 876568 1877327 := bstep (se 1 (by rfl) ⟨1407995, by rfl⟩ : syracuseStep 1877327 = 2815991) B2815991
theorem B2960225 : Blo 876568 2960225 := bstep (se 2 (by rfl) ⟨1110084, by rfl⟩ : syracuseStep 2960225 = 2220169) B2220169
theorem B48147311 : Blo 876568 48147311 := bstep (se 1 (by rfl) ⟨36110483, by rfl⟩ : syracuseStep 48147311 = 72220967) B72220967
theorem B42904687 : Blo 876568 42904687 := bstep (se 1 (by rfl) ⟨32178515, by rfl⟩ : syracuseStep 42904687 = 64357031) B64357031
theorem B2502647 : Blo 876568 2502647 := bstep (se 1 (by rfl) ⟨1876985, by rfl⟩ : syracuseStep 2502647 = 3753971) B3753971
theorem B2961575 : Blo 876568 2961575 := bstep (se 1 (by rfl) ⟨2221181, by rfl⟩ : syracuseStep 2961575 = 4442363) B4442363
theorem B14430797 : Blo 876568 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B21377789 : Blo 876568 21377789 := bstep (se 3 (by rfl) ⟨4008335, by rfl⟩ : syracuseStep 21377789 = 8016671) B8016671
theorem B1979495 : Blo 876568 1979495 := bstep (se 1 (by rfl) ⟨1484621, by rfl⟩ : syracuseStep 1979495 = 2969243) B2969243
theorem B2667773 : Blo 876568 2667773 := bstep (se 3 (by rfl) ⟨500207, by rfl⟩ : syracuseStep 2667773 = 1000415) B1000415
theorem B1980251 : Blo 876568 1980251 := bstep (se 1 (by rfl) ⟨1485188, by rfl⟩ : syracuseStep 1980251 = 2970377) B2970377
theorem B14271065 : Blo 876568 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B25379999 : Blo 876568 25379999 := bstep (se 1 (by rfl) ⟨19034999, by rfl⟩ : syracuseStep 25379999 = 38069999) B38069999
theorem B4998935 : Blo 876568 4998935 := bstep (se 1 (by rfl) ⟨3749201, by rfl⟩ : syracuseStep 4998935 = 7498403) B7498403
theorem B2967623 : Blo 876568 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B21385579 : Blo 876568 21385579 := bstep (se 1 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 21385579 = 32078369) B32078369
theorem B85545395 : Blo 876568 85545395 := bstep (se 1 (by rfl) ⟨64159046, by rfl⟩ : syracuseStep 85545395 = 128318093) B128318093
theorem B7493755 : Blo 876568 7493755 := bstep (se 1 (by rfl) ⟨5620316, by rfl⟩ : syracuseStep 7493755 = 11240633) B11240633
theorem B5626367 : Blo 876568 5626367 := bstep (se 1 (by rfl) ⟨4219775, by rfl⟩ : syracuseStep 5626367 = 8439551) B8439551
theorem B5070377 : Blo 876568 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B5005223 : Blo 876568 5005223 := bstep (se 1 (by rfl) ⟨3753917, by rfl⟩ : syracuseStep 5005223 = 7507835) B7507835
theorem B3563615 : Blo 876568 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B6676667 : Blo 876568 6676667 := bstep (se 1 (by rfl) ⟨5007500, by rfl⟩ : syracuseStep 6676667 = 10015001) B10015001
theorem B878207 : Blo 876568 878207 := bstep (se 1 (by rfl) ⟨658655, by rfl⟩ : syracuseStep 878207 = 1317311) B1317311
theorem B878439 : Blo 876568 878439 := bstep (se 1 (by rfl) ⟨658829, by rfl⟩ : syracuseStep 878439 = 1317659) B1317659
theorem B879719 : Blo 876568 879719 := bstep (se 1 (by rfl) ⟨659789, by rfl⟩ : syracuseStep 879719 = 1319579) B1319579
theorem B2223359 : Blo 876568 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B52063535 : Blo 876568 52063535 := bstep (se 1 (by rfl) ⟨39047651, by rfl⟩ : syracuseStep 52063535 = 78095303) B78095303
theorem B21360671 : Blo 876568 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B18051497 : Blo 876568 18051497 := bstep (se 2 (by rfl) ⟨6769311, by rfl⟩ : syracuseStep 18051497 = 13538623) B13538623
theorem B9500723 : Blo 876568 9500723 := bstep (se 1 (by rfl) ⟨7125542, by rfl⟩ : syracuseStep 9500723 = 14251085) B14251085
theorem B5077673 : Blo 876568 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B6685415 : Blo 876568 6685415 := bstep (se 1 (by rfl) ⟨5014061, by rfl⟩ : syracuseStep 6685415 = 10028123) B10028123
theorem B2820091 : Blo 876568 2820091 := bstep (se 1 (by rfl) ⟨2115068, by rfl⟩ : syracuseStep 2820091 = 4230137) B4230137
theorem B7114061 : Blo 876568 7114061 := bstep (se 3 (by rfl) ⟨1333886, by rfl⟩ : syracuseStep 7114061 = 2667773) B2667773
theorem B15011567 : Blo 876568 15011567 := bstep (se 1 (by rfl) ⟨11258675, by rfl⟩ : syracuseStep 15011567 = 22517351) B22517351
theorem B40506065 : Blo 876568 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B28514105 : Blo 876568 28514105 := bstep (se 2 (by rfl) ⟨10692789, by rfl⟩ : syracuseStep 28514105 = 21385579) B21385579
theorem B1251551 : Blo 876568 1251551 := bstep (se 1 (by rfl) ⟨938663, by rfl⟩ : syracuseStep 1251551 = 1877327) B1877327
theorem B1973483 : Blo 876568 1973483 := bstep (se 1 (by rfl) ⟨1480112, by rfl⟩ : syracuseStep 1973483 = 2960225) B2960225
theorem B1482239 : Blo 876568 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B34709023 : Blo 876568 34709023 := bstep (se 1 (by rfl) ⟨26031767, by rfl⟩ : syracuseStep 34709023 = 52063535) B52063535
theorem B1974383 : Blo 876568 1974383 := bstep (se 1 (by rfl) ⟨1480787, by rfl⟩ : syracuseStep 1974383 = 2961575) B2961575
theorem B12034331 : Blo 876568 12034331 := bstep (se 1 (by rfl) ⟨9025748, by rfl⟩ : syracuseStep 12034331 = 18051497) B18051497
theorem B1319663 : Blo 876568 1319663 := bstep (se 1 (by rfl) ⟨989747, by rfl⟩ : syracuseStep 1319663 = 1979495) B1979495
theorem B1320167 : Blo 876568 1320167 := bstep (se 1 (by rfl) ⟨990125, by rfl⟩ : syracuseStep 1320167 = 1980251) B1980251
theorem B6333815 : Blo 876568 6333815 := bstep (se 1 (by rfl) ⟨4750361, by rfl⟩ : syracuseStep 6333815 = 9500723) B9500723
theorem B3385115 : Blo 876568 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B1977065 : Blo 876568 1977065 := bstep (se 2 (by rfl) ⟨741399, by rfl⟩ : syracuseStep 1977065 = 1482799) B1482799
theorem B1485823 : Blo 876568 1485823 := bstep (se 1 (by rfl) ⟨1114367, by rfl⟩ : syracuseStep 1485823 = 2228735) B2228735
theorem B1977353 : Blo 876568 1977353 := bstep (se 2 (by rfl) ⟨741507, by rfl⟩ : syracuseStep 1977353 = 1483015) B1483015
theorem B9514043 : Blo 876568 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B16919999 : Blo 876568 16919999 := bstep (se 1 (by rfl) ⟨12689999, by rfl⟩ : syracuseStep 16919999 = 25379999) B25379999
theorem B1978415 : Blo 876568 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B57030263 : Blo 876568 57030263 := bstep (se 1 (by rfl) ⟨42772697, by rfl⟩ : syracuseStep 57030263 = 85545395) B85545395
theorem B3750911 : Blo 876568 3750911 := bstep (se 1 (by rfl) ⟨2813183, by rfl⟩ : syracuseStep 3750911 = 5626367) B5626367
theorem B2375743 : Blo 876568 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B7717315 : Blo 876568 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B32098207 : Blo 876568 32098207 := bstep (se 1 (by rfl) ⟨24073655, by rfl⟩ : syracuseStep 32098207 = 48147311) B48147311
theorem B14240447 : Blo 876568 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B9620531 : Blo 876568 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B13521005 : Blo 876568 13521005 := bstep (se 3 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 13521005 = 5070377) B5070377
theorem B3332623 : Blo 876568 3332623 := bstep (se 1 (by rfl) ⟨2499467, by rfl⟩ : syracuseStep 3332623 = 4998935) B4998935
theorem B876767 : Blo 876568 876767 := bstep (se 1 (by rfl) ⟨657575, by rfl⟩ : syracuseStep 876767 = 1315151) B1315151
theorem B1664239 : Blo 876568 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B877887 : Blo 876568 877887 := bstep (se 1 (by rfl) ⟨658415, by rfl⟩ : syracuseStep 877887 = 1316831) B1316831
theorem B878015 : Blo 876568 878015 := bstep (se 1 (by rfl) ⟨658511, by rfl⟩ : syracuseStep 878015 = 1317023) B1317023
theorem B57206249 : Blo 876568 57206249 := bstep (se 2 (by rfl) ⟨21452343, by rfl⟩ : syracuseStep 57206249 = 42904687) B42904687
theorem B3336815 : Blo 876568 3336815 := bstep (se 1 (by rfl) ⟨2502611, by rfl⟩ : syracuseStep 3336815 = 5005223) B5005223
theorem B4451111 : Blo 876568 4451111 := bstep (se 1 (by rfl) ⟨3338333, by rfl⟩ : syracuseStep 4451111 = 6676667) B6676667
theorem B879423 : Blo 876568 879423 := bstep (se 1 (by rfl) ⟨659567, by rfl⟩ : syracuseStep 879423 = 1319135) B1319135
theorem B879855 : Blo 876568 879855 := bstep (se 1 (by rfl) ⟨659891, by rfl⟩ : syracuseStep 879855 = 1319783) B1319783
theorem B1668431 : Blo 876568 1668431 := bstep (se 1 (by rfl) ⟨1251323, by rfl⟩ : syracuseStep 1668431 = 2502647) B2502647
theorem B9991673 : Blo 876568 9991673 := bstep (se 2 (by rfl) ⟨3746877, by rfl⟩ : syracuseStep 9991673 = 7493755) B7493755
theorem B14251859 : Blo 876568 14251859 := bstep (se 1 (by rfl) ⟨10688894, by rfl⟩ : syracuseStep 14251859 = 21377789) B21377789
theorem B4456943 : Blo 876568 4456943 := bstep (se 1 (by rfl) ⟨3342707, by rfl⟩ : syracuseStep 4456943 = 6685415) B6685415
theorem B10289753 : Blo 876568 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B42797609 : Blo 876568 42797609 := bstep (se 2 (by rfl) ⟨16049103, by rfl⟩ : syracuseStep 42797609 = 32098207) B32098207
theorem B9014003 : Blo 876568 9014003 := bstep (se 1 (by rfl) ⟨6760502, by rfl⟩ : syracuseStep 9014003 = 13521005) B13521005
theorem B27004043 : Blo 876568 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B19009403 : Blo 876568 19009403 := bstep (se 1 (by rfl) ⟨14257052, by rfl⟩ : syracuseStep 19009403 = 28514105) B28514105
theorem B1315655 : Blo 876568 1315655 := bstep (se 1 (by rfl) ⟨986741, by rfl⟩ : syracuseStep 1315655 = 1973483) B1973483
theorem B988159 : Blo 876568 988159 := bstep (se 1 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 988159 = 1482239) B1482239
theorem B1316255 : Blo 876568 1316255 := bstep (se 1 (by rfl) ⟨987191, by rfl⟩ : syracuseStep 1316255 = 1974383) B1974383
theorem B1318043 : Blo 876568 1318043 := bstep (se 1 (by rfl) ⟨988532, by rfl⟩ : syracuseStep 1318043 = 1977065) B1977065
theorem B1318235 : Blo 876568 1318235 := bstep (se 1 (by rfl) ⟨988676, by rfl⟩ : syracuseStep 1318235 = 1977353) B1977353
theorem B11279999 : Blo 876568 11279999 := bstep (se 1 (by rfl) ⟨8459999, by rfl⟩ : syracuseStep 11279999 = 16919999) B16919999
theorem B1318943 : Blo 876568 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B6661115 : Blo 876568 6661115 := bstep (se 1 (by rfl) ⟨4995836, by rfl⟩ : syracuseStep 6661115 = 9991673) B9991673
theorem B38020175 : Blo 876568 38020175 := bstep (se 1 (by rfl) ⟨28515131, by rfl⟩ : syracuseStep 38020175 = 57030263) B57030263
theorem B2500607 : Blo 876568 2500607 := bstep (se 1 (by rfl) ⟨1875455, by rfl⟩ : syracuseStep 2500607 = 3750911) B3750911
theorem B46278697 : Blo 876568 46278697 := bstep (se 2 (by rfl) ⟨17354511, by rfl⟩ : syracuseStep 46278697 = 34709023) B34709023
theorem B10007711 : Blo 876568 10007711 := bstep (se 1 (by rfl) ⟨7505783, by rfl⟩ : syracuseStep 10007711 = 15011567) B15011567
theorem B1981097 : Blo 876568 1981097 := bstep (se 2 (by rfl) ⟨742911, by rfl⟩ : syracuseStep 1981097 = 1485823) B1485823
theorem B2967407 : Blo 876568 2967407 := bstep (se 1 (by rfl) ⟨2225555, by rfl⟩ : syracuseStep 2967407 = 4451111) B4451111
theorem B6342695 : Blo 876568 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B4443497 : Blo 876568 4443497 := bstep (se 2 (by rfl) ⟨1666311, by rfl⟩ : syracuseStep 4443497 = 3332623) B3332623
theorem B3167657 : Blo 876568 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B2218985 : Blo 876568 2218985 := bstep (se 2 (by rfl) ⟨832119, by rfl⟩ : syracuseStep 2218985 = 1664239) B1664239
theorem B9493631 : Blo 876568 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B6413687 : Blo 876568 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B4742707 : Blo 876568 4742707 := bstep (se 1 (by rfl) ⟨3557030, by rfl⟩ : syracuseStep 4742707 = 7114061) B7114061
theorem B3760121 : Blo 876568 3760121 := bstep (se 2 (by rfl) ⟨1410045, by rfl⟩ : syracuseStep 3760121 = 2820091) B2820091
theorem B8022887 : Blo 876568 8022887 := bstep (se 1 (by rfl) ⟨6017165, by rfl⟩ : syracuseStep 8022887 = 12034331) B12034331
theorem B879775 : Blo 876568 879775 := bstep (se 1 (by rfl) ⟨659831, by rfl⟩ : syracuseStep 879775 = 1319663) B1319663
theorem B3337469 : Blo 876568 3337469 := bstep (se 3 (by rfl) ⟨625775, by rfl⟩ : syracuseStep 3337469 = 1251551) B1251551
theorem B880111 : Blo 876568 880111 := bstep (se 1 (by rfl) ⟨660083, by rfl⟩ : syracuseStep 880111 = 1320167) B1320167
theorem B4222543 : Blo 876568 4222543 := bstep (se 1 (by rfl) ⟨3166907, by rfl⟩ : syracuseStep 4222543 = 6333815) B6333815
theorem B38137499 : Blo 876568 38137499 := bstep (se 1 (by rfl) ⟨28603124, by rfl⟩ : syracuseStep 38137499 = 57206249) B57206249
theorem B2256743 : Blo 876568 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B2224543 : Blo 876568 2224543 := bstep (se 1 (by rfl) ⟨1668407, by rfl⟩ : syracuseStep 2224543 = 3336815) B3336815
theorem B1112287 : Blo 876568 1112287 := bstep (se 1 (by rfl) ⟨834215, by rfl⟩ : syracuseStep 1112287 = 1668431) B1668431
theorem B9501239 : Blo 876568 9501239 := bstep (se 1 (by rfl) ⟨7125929, by rfl⟩ : syracuseStep 9501239 = 14251859) B14251859
theorem B4228463 : Blo 876568 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B61704929 : Blo 876568 61704929 := bstep (se 2 (by rfl) ⟨23139348, by rfl⟩ : syracuseStep 61704929 = 46278697) B46278697
theorem B1479323 : Blo 876568 1479323 := bstep (se 1 (by rfl) ⟨1109492, by rfl⟩ : syracuseStep 1479323 = 2218985) B2218985
theorem B6329087 : Blo 876568 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B1317545 : Blo 876568 1317545 := bstep (se 2 (by rfl) ⟨494079, by rfl⟩ : syracuseStep 1317545 = 988159) B988159
theorem B25336637 : Blo 876568 25336637 := bstep (se 3 (by rfl) ⟨4750619, by rfl⟩ : syracuseStep 25336637 = 9501239) B9501239
theorem B5348591 : Blo 876568 5348591 := bstep (se 1 (by rfl) ⟨4011443, by rfl⟩ : syracuseStep 5348591 = 8022887) B8022887
theorem B1483049 : Blo 876568 1483049 := bstep (se 2 (by rfl) ⟨556143, by rfl⟩ : syracuseStep 1483049 = 1112287) B1112287
theorem B1320731 : Blo 876568 1320731 := bstep (se 1 (by rfl) ⟨990548, by rfl⟩ : syracuseStep 1320731 = 1981097) B1981097
theorem B6859835 : Blo 876568 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B1978271 : Blo 876568 1978271 := bstep (se 1 (by rfl) ⟨1483703, by rfl⟩ : syracuseStep 1978271 = 2967407) B2967407
theorem B6009335 : Blo 876568 6009335 := bstep (se 1 (by rfl) ⟨4507001, by rfl⟩ : syracuseStep 6009335 = 9014003) B9014003
theorem B2962331 : Blo 876568 2962331 := bstep (se 1 (by rfl) ⟨2221748, by rfl⟩ : syracuseStep 2962331 = 4443497) B4443497
theorem B2111771 : Blo 876568 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B4275791 : Blo 876568 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B7519999 : Blo 876568 7519999 := bstep (se 1 (by rfl) ⟨5639999, by rfl⟩ : syracuseStep 7519999 = 11279999) B11279999
theorem B2506747 : Blo 876568 2506747 := bstep (se 1 (by rfl) ⟨1880060, by rfl⟩ : syracuseStep 2506747 = 3760121) B3760121
theorem B2966057 : Blo 876568 2966057 := bstep (se 2 (by rfl) ⟨1112271, by rfl⟩ : syracuseStep 2966057 = 2224543) B2224543
theorem B4440743 : Blo 876568 4440743 := bstep (se 1 (by rfl) ⟨3330557, by rfl⟩ : syracuseStep 4440743 = 6661115) B6661115
theorem B25346783 : Blo 876568 25346783 := bstep (se 1 (by rfl) ⟨19010087, by rfl⟩ : syracuseStep 25346783 = 38020175) B38020175
theorem B72010781 : Blo 876568 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B6671807 : Blo 876568 6671807 := bstep (se 1 (by rfl) ⟨5003855, by rfl⟩ : syracuseStep 6671807 = 10007711) B10007711
theorem B2971295 : Blo 876568 2971295 := bstep (se 1 (by rfl) ⟨2228471, by rfl⟩ : syracuseStep 2971295 = 4456943) B4456943
theorem B28531739 : Blo 876568 28531739 := bstep (se 1 (by rfl) ⟨21398804, by rfl⟩ : syracuseStep 28531739 = 42797609) B42797609
theorem B12672935 : Blo 876568 12672935 := bstep (se 1 (by rfl) ⟨9504701, by rfl⟩ : syracuseStep 12672935 = 19009403) B19009403
theorem B877103 : Blo 876568 877103 := bstep (se 1 (by rfl) ⟨657827, by rfl⟩ : syracuseStep 877103 = 1315655) B1315655
theorem B877503 : Blo 876568 877503 := bstep (se 1 (by rfl) ⟨658127, by rfl⟩ : syracuseStep 877503 = 1316255) B1316255
theorem B878695 : Blo 876568 878695 := bstep (se 1 (by rfl) ⟨659021, by rfl⟩ : syracuseStep 878695 = 1318043) B1318043
theorem B5630057 : Blo 876568 5630057 := bstep (se 2 (by rfl) ⟨2111271, by rfl⟩ : syracuseStep 5630057 = 4222543) B4222543
theorem B878823 : Blo 876568 878823 := bstep (se 1 (by rfl) ⟨659117, by rfl⟩ : syracuseStep 878823 = 1318235) B1318235
theorem B879295 : Blo 876568 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B1667071 : Blo 876568 1667071 := bstep (se 1 (by rfl) ⟨1250303, by rfl⟩ : syracuseStep 1667071 = 2500607) B2500607
theorem B2224979 : Blo 876568 2224979 := bstep (se 1 (by rfl) ⟨1668734, by rfl⟩ : syracuseStep 2224979 = 3337469) B3337469
theorem B25424999 : Blo 876568 25424999 := bstep (se 1 (by rfl) ⟨19068749, by rfl⟩ : syracuseStep 25424999 = 38137499) B38137499
theorem B1504495 : Blo 876568 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B6323609 : Blo 876568 6323609 := bstep (se 2 (by rfl) ⟨2371353, by rfl⟩ : syracuseStep 6323609 = 4742707) B4742707
theorem B2818975 : Blo 876568 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B48007187 : Blo 876568 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B986215 : Blo 876568 986215 := bstep (se 1 (by rfl) ⟨739661, by rfl⟩ : syracuseStep 986215 = 1479323) B1479323
theorem B988699 : Blo 876568 988699 := bstep (se 1 (by rfl) ⟨741524, by rfl⟩ : syracuseStep 988699 = 1483049) B1483049
theorem B2005993 : Blo 876568 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B1318847 : Blo 876568 1318847 := bstep (se 1 (by rfl) ⟨989135, by rfl⟩ : syracuseStep 1318847 = 1978271) B1978271
theorem B4006223 : Blo 876568 4006223 := bstep (se 1 (by rfl) ⟨3004667, by rfl⟩ : syracuseStep 4006223 = 6009335) B6009335
theorem B1483319 : Blo 876568 1483319 := bstep (se 1 (by rfl) ⟨1112489, by rfl⟩ : syracuseStep 1483319 = 2224979) B2224979
theorem B1974887 : Blo 876568 1974887 := bstep (se 1 (by rfl) ⟨1481165, by rfl⟩ : syracuseStep 1974887 = 2962331) B2962331
theorem B16949999 : Blo 876568 16949999 := bstep (se 1 (by rfl) ⟨12712499, by rfl⟩ : syracuseStep 16949999 = 25424999) B25424999
theorem B1977371 : Blo 876568 1977371 := bstep (se 1 (by rfl) ⟨1483028, by rfl⟩ : syracuseStep 1977371 = 2966057) B2966057
theorem B2960495 : Blo 876568 2960495 := bstep (se 1 (by rfl) ⟨2220371, by rfl⟩ : syracuseStep 2960495 = 4440743) B4440743
theorem B1980863 : Blo 876568 1980863 := bstep (se 1 (by rfl) ⟨1485647, by rfl⟩ : syracuseStep 1980863 = 2971295) B2971295
theorem B16891091 : Blo 876568 16891091 := bstep (se 1 (by rfl) ⟨12668318, by rfl⟩ : syracuseStep 16891091 = 25336637) B25336637
theorem B19021159 : Blo 876568 19021159 := bstep (se 1 (by rfl) ⟨14265869, by rfl⟩ : syracuseStep 19021159 = 28531739) B28531739
theorem B3753371 : Blo 876568 3753371 := bstep (se 1 (by rfl) ⟨2815028, by rfl⟩ : syracuseStep 3753371 = 5630057) B5630057
theorem B164546477 : Blo 876568 164546477 := bstep (se 3 (by rfl) ⟨30852464, by rfl⟩ : syracuseStep 164546477 = 61704929) B61704929
theorem B4573223 : Blo 876568 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B4215739 : Blo 876568 4215739 := bstep (se 1 (by rfl) ⟨3161804, by rfl⟩ : syracuseStep 4215739 = 6323609) B6323609
theorem B16897855 : Blo 876568 16897855 := bstep (se 1 (by rfl) ⟨12673391, by rfl⟩ : syracuseStep 16897855 = 25346783) B25346783
theorem B4447871 : Blo 876568 4447871 := bstep (se 1 (by rfl) ⟨3335903, by rfl⟩ : syracuseStep 4447871 = 6671807) B6671807
theorem B4219391 : Blo 876568 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B878363 : Blo 876568 878363 := bstep (se 1 (by rfl) ⟨658772, by rfl⟩ : syracuseStep 878363 = 1317545) B1317545
theorem B3565727 : Blo 876568 3565727 := bstep (se 1 (by rfl) ⟨2674295, by rfl⟩ : syracuseStep 3565727 = 5348591) B5348591
theorem B8448623 : Blo 876568 8448623 := bstep (se 1 (by rfl) ⟨6336467, by rfl⟩ : syracuseStep 8448623 = 12672935) B12672935
theorem B2222761 : Blo 876568 2222761 := bstep (se 2 (by rfl) ⟨833535, by rfl⟩ : syracuseStep 2222761 = 1667071) B1667071
theorem B5631389 : Blo 876568 5631389 := bstep (se 3 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 5631389 = 2111771) B2111771
theorem B880487 : Blo 876568 880487 := bstep (se 1 (by rfl) ⟨660365, by rfl⟩ : syracuseStep 880487 = 1320731) B1320731
theorem B10026665 : Blo 876568 10026665 := bstep (se 2 (by rfl) ⟨3759999, by rfl⟩ : syracuseStep 10026665 = 7519999) B7519999
theorem B2850527 : Blo 876568 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B3342329 : Blo 876568 3342329 := bstep (se 2 (by rfl) ⟨1253373, by rfl⟩ : syracuseStep 3342329 = 2506747) B2506747
theorem B3048815 : Blo 876568 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B1314953 : Blo 876568 1314953 := bstep (se 2 (by rfl) ⟨493107, by rfl⟩ : syracuseStep 1314953 = 986215) B986215
theorem B988879 : Blo 876568 988879 := bstep (se 1 (by rfl) ⟨741659, by rfl⟩ : syracuseStep 988879 = 1483319) B1483319
theorem B1316591 : Blo 876568 1316591 := bstep (se 1 (by rfl) ⟨987443, by rfl⟩ : syracuseStep 1316591 = 1974887) B1974887
theorem B1318247 : Blo 876568 1318247 := bstep (se 1 (by rfl) ⟨988685, by rfl⟩ : syracuseStep 1318247 = 1977371) B1977371
theorem B1318265 : Blo 876568 1318265 := bstep (se 2 (by rfl) ⟨494349, by rfl⟩ : syracuseStep 1318265 = 988699) B988699
theorem B1973663 : Blo 876568 1973663 := bstep (se 1 (by rfl) ⟨1480247, by rfl⟩ : syracuseStep 1973663 = 2960495) B2960495
theorem B1320575 : Blo 876568 1320575 := bstep (se 1 (by rfl) ⟨990431, by rfl⟩ : syracuseStep 1320575 = 1980863) B1980863
theorem B2502247 : Blo 876568 2502247 := bstep (se 1 (by rfl) ⟨1876685, by rfl⟩ : syracuseStep 2502247 = 3753371) B3753371
theorem B2963681 : Blo 876568 2963681 := bstep (se 2 (by rfl) ⟨1111380, by rfl⟩ : syracuseStep 2963681 = 2222761) B2222761
theorem B2965247 : Blo 876568 2965247 := bstep (se 1 (by rfl) ⟨2223935, by rfl⟩ : syracuseStep 2965247 = 4447871) B4447871
theorem B2670815 : Blo 876568 2670815 := bstep (se 1 (by rfl) ⟨2003111, by rfl⟩ : syracuseStep 2670815 = 4006223) B4006223
theorem B5620985 : Blo 876568 5620985 := bstep (se 2 (by rfl) ⟨2107869, by rfl⟩ : syracuseStep 5620985 = 4215739) B4215739
theorem B2377151 : Blo 876568 2377151 := bstep (se 1 (by rfl) ⟨1782863, by rfl⟩ : syracuseStep 2377151 = 3565727) B3565727
theorem B3754259 : Blo 876568 3754259 := bstep (se 1 (by rfl) ⟨2815694, by rfl⟩ : syracuseStep 3754259 = 5631389) B5631389
theorem B22530473 : Blo 876568 22530473 := bstep (se 2 (by rfl) ⟨8448927, by rfl⟩ : syracuseStep 22530473 = 16897855) B16897855
theorem B2674657 : Blo 876568 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B11260727 : Blo 876568 11260727 := bstep (se 1 (by rfl) ⟨8445545, by rfl⟩ : syracuseStep 11260727 = 16891091) B16891091
theorem B3758633 : Blo 876568 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B109697651 : Blo 876568 109697651 := bstep (se 1 (by rfl) ⟨82273238, by rfl⟩ : syracuseStep 109697651 = 164546477) B164546477
theorem B32004791 : Blo 876568 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B879231 : Blo 876568 879231 := bstep (se 1 (by rfl) ⟨659423, by rfl⟩ : syracuseStep 879231 = 1318847) B1318847
theorem B2812927 : Blo 876568 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B11299999 : Blo 876568 11299999 := bstep (se 1 (by rfl) ⟨8474999, by rfl⟩ : syracuseStep 11299999 = 16949999) B16949999
theorem B5632415 : Blo 876568 5632415 := bstep (se 1 (by rfl) ⟨4224311, by rfl⟩ : syracuseStep 5632415 = 8448623) B8448623
theorem B25361545 : Blo 876568 25361545 := bstep (se 2 (by rfl) ⟨9510579, by rfl⟩ : syracuseStep 25361545 = 19021159) B19021159
theorem B6684443 : Blo 876568 6684443 := bstep (se 1 (by rfl) ⟨5013332, by rfl⟩ : syracuseStep 6684443 = 10026665) B10026665
theorem B1900351 : Blo 876568 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B2228219 : Blo 876568 2228219 := bstep (se 1 (by rfl) ⟨1671164, by rfl⟩ : syracuseStep 2228219 = 3342329) B3342329
theorem B2032543 : Blo 876568 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B7507151 : Blo 876568 7507151 := bstep (se 1 (by rfl) ⟨5630363, by rfl⟩ : syracuseStep 7507151 = 11260727) B11260727
theorem B21336527 : Blo 876568 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B1315775 : Blo 876568 1315775 := bstep (se 1 (by rfl) ⟨986831, by rfl⟩ : syracuseStep 1315775 = 1973663) B1973663
theorem B1318505 : Blo 876568 1318505 := bstep (se 2 (by rfl) ⟨494439, by rfl⟩ : syracuseStep 1318505 = 988879) B988879
theorem B1975787 : Blo 876568 1975787 := bstep (se 1 (by rfl) ⟨1481840, by rfl⟩ : syracuseStep 1975787 = 2963681) B2963681
theorem B10135205 : Blo 876568 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B1976831 : Blo 876568 1976831 := bstep (se 1 (by rfl) ⟨1482623, by rfl⟩ : syracuseStep 1976831 = 2965247) B2965247
theorem B1485479 : Blo 876568 1485479 := bstep (se 1 (by rfl) ⟨1114109, by rfl⟩ : syracuseStep 1485479 = 2228219) B2228219
theorem B1780543 : Blo 876568 1780543 := bstep (se 1 (by rfl) ⟨1335407, by rfl⟩ : syracuseStep 1780543 = 2670815) B2670815
theorem B3747323 : Blo 876568 3747323 := bstep (se 1 (by rfl) ⟨2810492, by rfl⟩ : syracuseStep 3747323 = 5620985) B5620985
theorem B1584767 : Blo 876568 1584767 := bstep (se 1 (by rfl) ⟨1188575, by rfl⟩ : syracuseStep 1584767 = 2377151) B2377151
theorem B2502839 : Blo 876568 2502839 := bstep (se 1 (by rfl) ⟨1877129, by rfl⟩ : syracuseStep 2502839 = 3754259) B3754259
theorem B15020315 : Blo 876568 15020315 := bstep (se 1 (by rfl) ⟨11265236, by rfl⟩ : syracuseStep 15020315 = 22530473) B22530473
theorem B3750569 : Blo 876568 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B2505755 : Blo 876568 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B3754943 : Blo 876568 3754943 := bstep (se 1 (by rfl) ⟨2816207, by rfl⟩ : syracuseStep 3754943 = 5632415) B5632415
theorem B876635 : Blo 876568 876635 := bstep (se 1 (by rfl) ⟨657476, by rfl⟩ : syracuseStep 876635 = 1314953) B1314953
theorem B877727 : Blo 876568 877727 := bstep (se 1 (by rfl) ⟨658295, by rfl⟩ : syracuseStep 877727 = 1316591) B1316591
theorem B15066665 : Blo 876568 15066665 := bstep (se 2 (by rfl) ⟨5649999, by rfl⟩ : syracuseStep 15066665 = 11299999) B11299999
theorem B73131767 : Blo 876568 73131767 := bstep (se 1 (by rfl) ⟨54848825, by rfl⟩ : syracuseStep 73131767 = 109697651) B109697651
theorem B3336329 : Blo 876568 3336329 := bstep (se 2 (by rfl) ⟨1251123, by rfl⟩ : syracuseStep 3336329 = 2502247) B2502247
theorem B878831 : Blo 876568 878831 := bstep (se 1 (by rfl) ⟨659123, by rfl⟩ : syracuseStep 878831 = 1318247) B1318247
theorem B878843 : Blo 876568 878843 := bstep (se 1 (by rfl) ⟨659132, by rfl⟩ : syracuseStep 878843 = 1318265) B1318265
theorem B3566209 : Blo 876568 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B880383 : Blo 876568 880383 := bstep (se 1 (by rfl) ⟨660287, by rfl⟩ : syracuseStep 880383 = 1320575) B1320575
theorem B33815393 : Blo 876568 33815393 := bstep (se 2 (by rfl) ⟨12680772, by rfl⟩ : syracuseStep 33815393 = 25361545) B25361545
theorem B4456295 : Blo 876568 4456295 := bstep (se 1 (by rfl) ⟨3342221, by rfl⟩ : syracuseStep 4456295 = 6684443) B6684443
theorem B14224351 : Blo 876568 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B4754945 : Blo 876568 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B1317191 : Blo 876568 1317191 := bstep (se 1 (by rfl) ⟨987893, by rfl⟩ : syracuseStep 1317191 = 1975787) B1975787
theorem B6756803 : Blo 876568 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B1317887 : Blo 876568 1317887 := bstep (se 1 (by rfl) ⟨988415, by rfl⟩ : syracuseStep 1317887 = 1976831) B1976831
theorem B990319 : Blo 876568 990319 := bstep (se 1 (by rfl) ⟨742739, by rfl⟩ : syracuseStep 990319 = 1485479) B1485479
theorem B2498215 : Blo 876568 2498215 := bstep (se 1 (by rfl) ⟨1873661, by rfl⟩ : syracuseStep 2498215 = 3747323) B3747323
theorem B1056511 : Blo 876568 1056511 := bstep (se 1 (by rfl) ⟨792383, by rfl⟩ : syracuseStep 1056511 = 1584767) B1584767
theorem B2500379 : Blo 876568 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B2503295 : Blo 876568 2503295 := bstep (se 1 (by rfl) ⟨1877471, by rfl⟩ : syracuseStep 2503295 = 3754943) B3754943
theorem B2374057 : Blo 876568 2374057 := bstep (se 2 (by rfl) ⟨890271, by rfl⟩ : syracuseStep 2374057 = 1780543) B1780543
theorem B10044443 : Blo 876568 10044443 := bstep (se 1 (by rfl) ⟨7533332, by rfl⟩ : syracuseStep 10044443 = 15066665) B15066665
theorem B10013543 : Blo 876568 10013543 := bstep (se 1 (by rfl) ⟨7510157, by rfl⟩ : syracuseStep 10013543 = 15020315) B15020315
theorem B2970863 : Blo 876568 2970863 := bstep (se 1 (by rfl) ⟨2228147, by rfl⟩ : syracuseStep 2970863 = 4456295) B4456295
theorem B6674237 : Blo 876568 6674237 := bstep (se 3 (by rfl) ⟨1251419, by rfl⟩ : syracuseStep 6674237 = 2502839) B2502839
theorem B2710057 : Blo 876568 2710057 := bstep (se 2 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 2710057 = 2032543) B2032543
theorem B5004767 : Blo 876568 5004767 := bstep (se 1 (by rfl) ⟨3753575, by rfl⟩ : syracuseStep 5004767 = 7507151) B7507151
theorem B877183 : Blo 876568 877183 := bstep (se 1 (by rfl) ⟨657887, by rfl⟩ : syracuseStep 877183 = 1315775) B1315775
theorem B879003 : Blo 876568 879003 := bstep (se 1 (by rfl) ⟨659252, by rfl⟩ : syracuseStep 879003 = 1318505) B1318505
theorem B48754511 : Blo 876568 48754511 := bstep (se 1 (by rfl) ⟨36565883, by rfl⟩ : syracuseStep 48754511 = 73131767) B73131767
theorem B2224219 : Blo 876568 2224219 := bstep (se 1 (by rfl) ⟨1668164, by rfl⟩ : syracuseStep 2224219 = 3336329) B3336329
theorem B6682013 : Blo 876568 6682013 := bstep (se 3 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 6682013 = 2505755) B2505755
theorem B22543595 : Blo 876568 22543595 := bstep (se 1 (by rfl) ⟨16907696, by rfl⟩ : syracuseStep 22543595 = 33815393) B33815393
theorem B3613409 : Blo 876568 3613409 := bstep (se 2 (by rfl) ⟨1355028, by rfl⟩ : syracuseStep 3613409 = 2710057) B2710057
theorem B1320425 : Blo 876568 1320425 := bstep (se 2 (by rfl) ⟨495159, by rfl⟩ : syracuseStep 1320425 = 990319) B990319
theorem B26785181 : Blo 876568 26785181 := bstep (se 3 (by rfl) ⟨5022221, by rfl⟩ : syracuseStep 26785181 = 10044443) B10044443
theorem B1980575 : Blo 876568 1980575 := bstep (se 1 (by rfl) ⟨1485431, by rfl⟩ : syracuseStep 1980575 = 2970863) B2970863
theorem B4504535 : Blo 876568 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B2965625 : Blo 876568 2965625 := bstep (se 2 (by rfl) ⟨1112109, by rfl⟩ : syracuseStep 2965625 = 2224219) B2224219
theorem B3165409 : Blo 876568 3165409 := bstep (se 2 (by rfl) ⟨1187028, by rfl⟩ : syracuseStep 3165409 = 2374057) B2374057
theorem B15029063 : Blo 876568 15029063 := bstep (se 1 (by rfl) ⟨11271797, by rfl⟩ : syracuseStep 15029063 = 22543595) B22543595
theorem B3330953 : Blo 876568 3330953 := bstep (se 2 (by rfl) ⟨1249107, by rfl⟩ : syracuseStep 3330953 = 2498215) B2498215
theorem B6675695 : Blo 876568 6675695 := bstep (se 1 (by rfl) ⟨5006771, by rfl⟩ : syracuseStep 6675695 = 10013543) B10013543
theorem B3169963 : Blo 876568 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B4449491 : Blo 876568 4449491 := bstep (se 1 (by rfl) ⟨3337118, by rfl⟩ : syracuseStep 4449491 = 6674237) B6674237
theorem B18965801 : Blo 876568 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B878127 : Blo 876568 878127 := bstep (se 1 (by rfl) ⟨658595, by rfl⟩ : syracuseStep 878127 = 1317191) B1317191
theorem B878591 : Blo 876568 878591 := bstep (se 1 (by rfl) ⟨658943, by rfl⟩ : syracuseStep 878591 = 1317887) B1317887
theorem B3336511 : Blo 876568 3336511 := bstep (se 1 (by rfl) ⟨2502383, by rfl⟩ : syracuseStep 3336511 = 5004767) B5004767
theorem B1666919 : Blo 876568 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B32503007 : Blo 876568 32503007 := bstep (se 1 (by rfl) ⟨24377255, by rfl⟩ : syracuseStep 32503007 = 48754511) B48754511
theorem B1668863 : Blo 876568 1668863 := bstep (se 1 (by rfl) ⟨1251647, by rfl⟩ : syracuseStep 1668863 = 2503295) B2503295
theorem B4454675 : Blo 876568 4454675 := bstep (se 1 (by rfl) ⟨3341006, by rfl⟩ : syracuseStep 4454675 = 6682013) B6682013
theorem B1408681 : Blo 876568 1408681 := bstep (se 2 (by rfl) ⟨528255, by rfl⟩ : syracuseStep 1408681 = 1056511) B1056511
theorem B21668671 : Blo 876568 21668671 := bstep (se 1 (by rfl) ⟨16251503, by rfl⟩ : syracuseStep 21668671 = 32503007) B32503007
theorem B1320383 : Blo 876568 1320383 := bstep (se 1 (by rfl) ⟨990287, by rfl⟩ : syracuseStep 1320383 = 1980575) B1980575
theorem B1878241 : Blo 876568 1878241 := bstep (se 2 (by rfl) ⟨704340, by rfl⟩ : syracuseStep 1878241 = 1408681) B1408681
theorem B1977083 : Blo 876568 1977083 := bstep (se 1 (by rfl) ⟨1482812, by rfl⟩ : syracuseStep 1977083 = 2965625) B2965625
theorem B2408939 : Blo 876568 2408939 := bstep (se 1 (by rfl) ⟨1806704, by rfl⟩ : syracuseStep 2408939 = 3613409) B3613409
theorem B2966327 : Blo 876568 2966327 := bstep (se 1 (by rfl) ⟨2224745, by rfl⟩ : syracuseStep 2966327 = 4449491) B4449491
theorem B2969783 : Blo 876568 2969783 := bstep (se 1 (by rfl) ⟨2227337, by rfl⟩ : syracuseStep 2969783 = 4454675) B4454675
theorem B3003023 : Blo 876568 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B4445117 : Blo 876568 4445117 := bstep (se 3 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 4445117 = 1666919) B1666919
theorem B4448681 : Blo 876568 4448681 := bstep (se 2 (by rfl) ⟨1668255, by rfl⟩ : syracuseStep 4448681 = 3336511) B3336511
theorem B10019375 : Blo 876568 10019375 := bstep (se 1 (by rfl) ⟨7514531, by rfl⟩ : syracuseStep 10019375 = 15029063) B15029063
theorem B2220635 : Blo 876568 2220635 := bstep (se 1 (by rfl) ⟨1665476, by rfl⟩ : syracuseStep 2220635 = 3330953) B3330953
theorem B4220545 : Blo 876568 4220545 := bstep (se 2 (by rfl) ⟨1582704, by rfl⟩ : syracuseStep 4220545 = 3165409) B3165409
theorem B4450301 : Blo 876568 4450301 := bstep (se 3 (by rfl) ⟨834431, by rfl⟩ : syracuseStep 4450301 = 1668863) B1668863
theorem B4450463 : Blo 876568 4450463 := bstep (se 1 (by rfl) ⟨3337847, by rfl⟩ : syracuseStep 4450463 = 6675695) B6675695
theorem B12643867 : Blo 876568 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B880283 : Blo 876568 880283 := bstep (se 1 (by rfl) ⟨660212, by rfl⟩ : syracuseStep 880283 = 1320425) B1320425
theorem B17856787 : Blo 876568 17856787 := bstep (se 1 (by rfl) ⟨13392590, by rfl⟩ : syracuseStep 17856787 = 26785181) B26785181
theorem B4226617 : Blo 876568 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B1605959 : Blo 876568 1605959 := bstep (se 1 (by rfl) ⟨1204469, by rfl⟩ : syracuseStep 1605959 = 2408939) B2408939
theorem B2002015 : Blo 876568 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B1480423 : Blo 876568 1480423 := bstep (se 1 (by rfl) ⟨1110317, by rfl⟩ : syracuseStep 1480423 = 2220635) B2220635
theorem B1318055 : Blo 876568 1318055 := bstep (se 1 (by rfl) ⟨988541, by rfl⟩ : syracuseStep 1318055 = 1977083) B1977083
theorem B1977551 : Blo 876568 1977551 := bstep (se 1 (by rfl) ⟨1483163, by rfl⟩ : syracuseStep 1977551 = 2966327) B2966327
theorem B1979855 : Blo 876568 1979855 := bstep (se 1 (by rfl) ⟨1484891, by rfl⟩ : syracuseStep 1979855 = 2969783) B2969783
theorem B2504321 : Blo 876568 2504321 := bstep (se 2 (by rfl) ⟨939120, by rfl⟩ : syracuseStep 2504321 = 1878241) B1878241
theorem B2963411 : Blo 876568 2963411 := bstep (se 1 (by rfl) ⟨2222558, by rfl⟩ : syracuseStep 2963411 = 4445117) B4445117
theorem B16858489 : Blo 876568 16858489 := bstep (se 2 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 16858489 = 12643867) B12643867
theorem B2965787 : Blo 876568 2965787 := bstep (se 1 (by rfl) ⟨2224340, by rfl⟩ : syracuseStep 2965787 = 4448681) B4448681
theorem B2966867 : Blo 876568 2966867 := bstep (se 1 (by rfl) ⟨2225150, by rfl⟩ : syracuseStep 2966867 = 4450301) B4450301
theorem B2966975 : Blo 876568 2966975 := bstep (se 1 (by rfl) ⟨2225231, by rfl⟩ : syracuseStep 2966975 = 4450463) B4450463
theorem B23809049 : Blo 876568 23809049 := bstep (se 2 (by rfl) ⟨8928393, by rfl⟩ : syracuseStep 23809049 = 17856787) B17856787
theorem B28891561 : Blo 876568 28891561 := bstep (se 2 (by rfl) ⟨10834335, by rfl⟩ : syracuseStep 28891561 = 21668671) B21668671
theorem B5627393 : Blo 876568 5627393 := bstep (se 2 (by rfl) ⟨2110272, by rfl⟩ : syracuseStep 5627393 = 4220545) B4220545
theorem B6679583 : Blo 876568 6679583 := bstep (se 1 (by rfl) ⟨5009687, by rfl⟩ : syracuseStep 6679583 = 10019375) B10019375
theorem B880255 : Blo 876568 880255 := bstep (se 1 (by rfl) ⟨660191, by rfl⟩ : syracuseStep 880255 = 1320383) B1320383
theorem B5635489 : Blo 876568 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B1318367 : Blo 876568 1318367 := bstep (se 1 (by rfl) ⟨988775, by rfl⟩ : syracuseStep 1318367 = 1977551) B1977551
theorem B1973897 : Blo 876568 1973897 := bstep (se 2 (by rfl) ⟨740211, by rfl⟩ : syracuseStep 1973897 = 1480423) B1480423
theorem B1319903 : Blo 876568 1319903 := bstep (se 1 (by rfl) ⟨989927, by rfl⟩ : syracuseStep 1319903 = 1979855) B1979855
theorem B1975607 : Blo 876568 1975607 := bstep (se 1 (by rfl) ⟨1481705, by rfl⟩ : syracuseStep 1975607 = 2963411) B2963411
theorem B7513985 : Blo 876568 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B1977191 : Blo 876568 1977191 := bstep (se 1 (by rfl) ⟨1482893, by rfl⟩ : syracuseStep 1977191 = 2965787) B2965787
theorem B1977911 : Blo 876568 1977911 := bstep (se 1 (by rfl) ⟨1483433, by rfl⟩ : syracuseStep 1977911 = 2966867) B2966867
theorem B1977983 : Blo 876568 1977983 := bstep (se 1 (by rfl) ⟨1483487, by rfl⟩ : syracuseStep 1977983 = 2966975) B2966975
theorem B15872699 : Blo 876568 15872699 := bstep (se 1 (by rfl) ⟨11904524, by rfl⟩ : syracuseStep 15872699 = 23809049) B23809049
theorem B3751595 : Blo 876568 3751595 := bstep (se 1 (by rfl) ⟨2813696, by rfl⟩ : syracuseStep 3751595 = 5627393) B5627393
theorem B38522081 : Blo 876568 38522081 := bstep (se 2 (by rfl) ⟨14445780, by rfl⟩ : syracuseStep 38522081 = 28891561) B28891561
theorem B1070639 : Blo 876568 1070639 := bstep (se 1 (by rfl) ⟨802979, by rfl⟩ : syracuseStep 1070639 = 1605959) B1605959
theorem B878703 : Blo 876568 878703 := bstep (se 1 (by rfl) ⟨659027, by rfl⟩ : syracuseStep 878703 = 1318055) B1318055
theorem B10677413 : Blo 876568 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B4453055 : Blo 876568 4453055 := bstep (se 1 (by rfl) ⟨3339791, by rfl⟩ : syracuseStep 4453055 = 6679583) B6679583
theorem B1669547 : Blo 876568 1669547 := bstep (se 1 (by rfl) ⟨1252160, by rfl⟩ : syracuseStep 1669547 = 2504321) B2504321
theorem B22477985 : Blo 876568 22477985 := bstep (se 2 (by rfl) ⟨8429244, by rfl⟩ : syracuseStep 22477985 = 16858489) B16858489
theorem B1315931 : Blo 876568 1315931 := bstep (se 1 (by rfl) ⟨986948, by rfl⟩ : syracuseStep 1315931 = 1973897) B1973897
theorem B1317071 : Blo 876568 1317071 := bstep (se 1 (by rfl) ⟨987803, by rfl⟩ : syracuseStep 1317071 = 1975607) B1975607
theorem B1318127 : Blo 876568 1318127 := bstep (se 1 (by rfl) ⟨988595, by rfl⟩ : syracuseStep 1318127 = 1977191) B1977191
theorem B7118275 : Blo 876568 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B1318607 : Blo 876568 1318607 := bstep (se 1 (by rfl) ⟨988955, by rfl⟩ : syracuseStep 1318607 = 1977911) B1977911
theorem B1318655 : Blo 876568 1318655 := bstep (se 1 (by rfl) ⟨988991, by rfl⟩ : syracuseStep 1318655 = 1977983) B1977983
theorem B14985323 : Blo 876568 14985323 := bstep (se 1 (by rfl) ⟨11238992, by rfl⟩ : syracuseStep 14985323 = 22477985) B22477985
theorem B2501063 : Blo 876568 2501063 := bstep (se 1 (by rfl) ⟨1875797, by rfl⟩ : syracuseStep 2501063 = 3751595) B3751595
theorem B11420149 : Blo 876568 11420149 := bstep (se 5 (by rfl) ⟨535319, by rfl⟩ : syracuseStep 11420149 = 1070639) B1070639
theorem B2968703 : Blo 876568 2968703 := bstep (se 1 (by rfl) ⟨2226527, by rfl⟩ : syracuseStep 2968703 = 4453055) B4453055
theorem B42327197 : Blo 876568 42327197 := bstep (se 3 (by rfl) ⟨7936349, by rfl⟩ : syracuseStep 42327197 = 15872699) B15872699
theorem B25681387 : Blo 876568 25681387 := bstep (se 1 (by rfl) ⟨19261040, by rfl⟩ : syracuseStep 25681387 = 38522081) B38522081
theorem B878911 : Blo 876568 878911 := bstep (se 1 (by rfl) ⟨659183, by rfl⟩ : syracuseStep 878911 = 1318367) B1318367
theorem B879935 : Blo 876568 879935 := bstep (se 1 (by rfl) ⟨659951, by rfl⟩ : syracuseStep 879935 = 1319903) B1319903
theorem B5009323 : Blo 876568 5009323 := bstep (se 1 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 5009323 = 7513985) B7513985
theorem B1113031 : Blo 876568 1113031 := bstep (se 1 (by rfl) ⟨834773, by rfl⟩ : syracuseStep 1113031 = 1669547) B1669547
theorem B28218131 : Blo 876568 28218131 := bstep (se 1 (by rfl) ⟨21163598, by rfl⟩ : syracuseStep 28218131 = 42327197) B42327197
theorem B1484041 : Blo 876568 1484041 := bstep (se 2 (by rfl) ⟨556515, by rfl⟩ : syracuseStep 1484041 = 1113031) B1113031
theorem B1979135 : Blo 876568 1979135 := bstep (se 1 (by rfl) ⟨1484351, by rfl⟩ : syracuseStep 1979135 = 2968703) B2968703
theorem B9491033 : Blo 876568 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B15226865 : Blo 876568 15226865 := bstep (se 2 (by rfl) ⟨5710074, by rfl⟩ : syracuseStep 15226865 = 11420149) B11420149
theorem B877287 : Blo 876568 877287 := bstep (se 1 (by rfl) ⟨657965, by rfl⟩ : syracuseStep 877287 = 1315931) B1315931
theorem B878047 : Blo 876568 878047 := bstep (se 1 (by rfl) ⟨658535, by rfl⟩ : syracuseStep 878047 = 1317071) B1317071
theorem B878751 : Blo 876568 878751 := bstep (se 1 (by rfl) ⟨659063, by rfl⟩ : syracuseStep 878751 = 1318127) B1318127
theorem B879071 : Blo 876568 879071 := bstep (se 1 (by rfl) ⟨659303, by rfl⟩ : syracuseStep 879071 = 1318607) B1318607
theorem B879103 : Blo 876568 879103 := bstep (se 1 (by rfl) ⟨659327, by rfl⟩ : syracuseStep 879103 = 1318655) B1318655
theorem B6679097 : Blo 876568 6679097 := bstep (se 2 (by rfl) ⟨2504661, by rfl⟩ : syracuseStep 6679097 = 5009323) B5009323
theorem B9990215 : Blo 876568 9990215 := bstep (se 1 (by rfl) ⟨7492661, by rfl⟩ : syracuseStep 9990215 = 14985323) B14985323
theorem B1667375 : Blo 876568 1667375 := bstep (se 1 (by rfl) ⟨1250531, by rfl⟩ : syracuseStep 1667375 = 2501063) B2501063
theorem B34241849 : Blo 876568 34241849 := bstep (se 2 (by rfl) ⟨12840693, by rfl⟩ : syracuseStep 34241849 = 25681387) B25681387
theorem B18812087 : Blo 876568 18812087 := bstep (se 1 (by rfl) ⟨14109065, by rfl⟩ : syracuseStep 18812087 = 28218131) B28218131
theorem B6660143 : Blo 876568 6660143 := bstep (se 1 (by rfl) ⟨4995107, by rfl⟩ : syracuseStep 6660143 = 9990215) B9990215
theorem B1319423 : Blo 876568 1319423 := bstep (se 1 (by rfl) ⟨989567, by rfl⟩ : syracuseStep 1319423 = 1979135) B1979135
theorem B25309421 : Blo 876568 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B1978721 : Blo 876568 1978721 := bstep (se 2 (by rfl) ⟨742020, by rfl⟩ : syracuseStep 1978721 = 1484041) B1484041
theorem B22827899 : Blo 876568 22827899 := bstep (se 1 (by rfl) ⟨17120924, by rfl⟩ : syracuseStep 22827899 = 34241849) B34241849
theorem B10151243 : Blo 876568 10151243 := bstep (se 1 (by rfl) ⟨7613432, by rfl⟩ : syracuseStep 10151243 = 15226865) B15226865
theorem B4452731 : Blo 876568 4452731 := bstep (se 1 (by rfl) ⟨3339548, by rfl⟩ : syracuseStep 4452731 = 6679097) B6679097
theorem B1111583 : Blo 876568 1111583 := bstep (se 1 (by rfl) ⟨833687, by rfl⟩ : syracuseStep 1111583 = 1667375) B1667375
theorem B1319147 : Blo 876568 1319147 := bstep (se 1 (by rfl) ⟨989360, by rfl⟩ : syracuseStep 1319147 = 1978721) B1978721
theorem B15218599 : Blo 876568 15218599 := bstep (se 1 (by rfl) ⟨11413949, by rfl⟩ : syracuseStep 15218599 = 22827899) B22827899
theorem B2964221 : Blo 876568 2964221 := bstep (se 3 (by rfl) ⟨555791, by rfl⟩ : syracuseStep 2964221 = 1111583) B1111583
theorem B4440095 : Blo 876568 4440095 := bstep (se 1 (by rfl) ⟨3330071, by rfl⟩ : syracuseStep 4440095 = 6660143) B6660143
theorem B6767495 : Blo 876568 6767495 := bstep (se 1 (by rfl) ⟨5075621, by rfl⟩ : syracuseStep 6767495 = 10151243) B10151243
theorem B2968487 : Blo 876568 2968487 := bstep (se 1 (by rfl) ⟨2226365, by rfl⟩ : syracuseStep 2968487 = 4452731) B4452731
theorem B12541391 : Blo 876568 12541391 := bstep (se 1 (by rfl) ⟨9406043, by rfl⟩ : syracuseStep 12541391 = 18812087) B18812087
theorem B879615 : Blo 876568 879615 := bstep (se 1 (by rfl) ⟨659711, by rfl⟩ : syracuseStep 879615 = 1319423) B1319423
theorem B16872947 : Blo 876568 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B8360927 : Blo 876568 8360927 := bstep (se 1 (by rfl) ⟨6270695, by rfl⟩ : syracuseStep 8360927 = 12541391) B12541391
theorem B20291465 : Blo 876568 20291465 := bstep (se 2 (by rfl) ⟨7609299, by rfl⟩ : syracuseStep 20291465 = 15218599) B15218599
theorem B11248631 : Blo 876568 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B1976147 : Blo 876568 1976147 := bstep (se 1 (by rfl) ⟨1482110, by rfl⟩ : syracuseStep 1976147 = 2964221) B2964221
theorem B2960063 : Blo 876568 2960063 := bstep (se 1 (by rfl) ⟨2220047, by rfl⟩ : syracuseStep 2960063 = 4440095) B4440095
theorem B1978991 : Blo 876568 1978991 := bstep (se 1 (by rfl) ⟨1484243, by rfl⟩ : syracuseStep 1978991 = 2968487) B2968487
theorem B4511663 : Blo 876568 4511663 := bstep (se 1 (by rfl) ⟨3383747, by rfl⟩ : syracuseStep 4511663 = 6767495) B6767495
theorem B879431 : Blo 876568 879431 := bstep (se 1 (by rfl) ⟨659573, by rfl⟩ : syracuseStep 879431 = 1319147) B1319147
theorem B5573951 : Blo 876568 5573951 := bstep (se 1 (by rfl) ⟨4180463, by rfl⟩ : syracuseStep 5573951 = 8360927) B8360927
theorem B1317431 : Blo 876568 1317431 := bstep (se 1 (by rfl) ⟨988073, by rfl⟩ : syracuseStep 1317431 = 1976147) B1976147
theorem B1973375 : Blo 876568 1973375 := bstep (se 1 (by rfl) ⟨1480031, by rfl⟩ : syracuseStep 1973375 = 2960063) B2960063
theorem B1319327 : Blo 876568 1319327 := bstep (se 1 (by rfl) ⟨989495, by rfl⟩ : syracuseStep 1319327 = 1978991) B1978991
theorem B3007775 : Blo 876568 3007775 := bstep (se 1 (by rfl) ⟨2255831, by rfl⟩ : syracuseStep 3007775 = 4511663) B4511663
theorem B13527643 : Blo 876568 13527643 := bstep (se 1 (by rfl) ⟨10145732, by rfl⟩ : syracuseStep 13527643 = 20291465) B20291465
theorem B7499087 : Blo 876568 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B1315583 : Blo 876568 1315583 := bstep (se 1 (by rfl) ⟨986687, by rfl⟩ : syracuseStep 1315583 = 1973375) B1973375
theorem B2005183 : Blo 876568 2005183 := bstep (se 1 (by rfl) ⟨1503887, by rfl⟩ : syracuseStep 2005183 = 3007775) B3007775
theorem B3715967 : Blo 876568 3715967 := bstep (se 1 (by rfl) ⟨2786975, by rfl⟩ : syracuseStep 3715967 = 5573951) B5573951
theorem B18036857 : Blo 876568 18036857 := bstep (se 2 (by rfl) ⟨6763821, by rfl⟩ : syracuseStep 18036857 = 13527643) B13527643
theorem B4999391 : Blo 876568 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B878287 : Blo 876568 878287 := bstep (se 1 (by rfl) ⟨658715, by rfl⟩ : syracuseStep 878287 = 1317431) B1317431
theorem B879551 : Blo 876568 879551 := bstep (se 1 (by rfl) ⟨659663, by rfl⟩ : syracuseStep 879551 = 1319327) B1319327
theorem B2673577 : Blo 876568 2673577 := bstep (se 2 (by rfl) ⟨1002591, by rfl⟩ : syracuseStep 2673577 = 2005183) B2005183
theorem B2477311 : Blo 876568 2477311 := bstep (se 1 (by rfl) ⟨1857983, by rfl⟩ : syracuseStep 2477311 = 3715967) B3715967
theorem B3332927 : Blo 876568 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B877055 : Blo 876568 877055 := bstep (se 1 (by rfl) ⟨657791, by rfl⟩ : syracuseStep 877055 = 1315583) B1315583
theorem B12024571 : Blo 876568 12024571 := bstep (se 1 (by rfl) ⟨9018428, by rfl⟩ : syracuseStep 12024571 = 18036857) B18036857
theorem B13212325 : Blo 876568 13212325 := bstep (se 4 (by rfl) ⟨1238655, by rfl⟩ : syracuseStep 13212325 = 2477311) B2477311
theorem B16032761 : Blo 876568 16032761 := bstep (se 2 (by rfl) ⟨6012285, by rfl⟩ : syracuseStep 16032761 = 12024571) B12024571
theorem B3564769 : Blo 876568 3564769 := bstep (se 2 (by rfl) ⟨1336788, by rfl⟩ : syracuseStep 3564769 = 2673577) B2673577
theorem B2221951 : Blo 876568 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B4753025 : Blo 876568 4753025 := bstep (se 2 (by rfl) ⟨1782384, by rfl⟩ : syracuseStep 4753025 = 3564769) B3564769
theorem B10688507 : Blo 876568 10688507 := bstep (se 1 (by rfl) ⟨8016380, by rfl⟩ : syracuseStep 10688507 = 16032761) B16032761
theorem B2962601 : Blo 876568 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B70465733 : Blo 876568 70465733 := bstep (se 4 (by rfl) ⟨6606162, by rfl⟩ : syracuseStep 70465733 = 13212325) B13212325
theorem B1975067 : Blo 876568 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B7125671 : Blo 876568 7125671 := bstep (se 1 (by rfl) ⟨5344253, by rfl⟩ : syracuseStep 7125671 = 10688507) B10688507
theorem B46977155 : Blo 876568 46977155 := bstep (se 1 (by rfl) ⟨35232866, by rfl⟩ : syracuseStep 46977155 = 70465733) B70465733
theorem B3168683 : Blo 876568 3168683 := bstep (se 1 (by rfl) ⟨2376512, by rfl⟩ : syracuseStep 3168683 = 4753025) B4753025
theorem B1316711 : Blo 876568 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B2112455 : Blo 876568 2112455 := bstep (se 1 (by rfl) ⟨1584341, by rfl⟩ : syracuseStep 2112455 = 3168683) B3168683
theorem B31318103 : Blo 876568 31318103 := bstep (se 1 (by rfl) ⟨23488577, by rfl⟩ : syracuseStep 31318103 = 46977155) B46977155
theorem B4750447 : Blo 876568 4750447 := bstep (se 1 (by rfl) ⟨3562835, by rfl⟩ : syracuseStep 4750447 = 7125671) B7125671
theorem B20878735 : Blo 876568 20878735 := bstep (se 1 (by rfl) ⟨15659051, by rfl⟩ : syracuseStep 20878735 = 31318103) B31318103
theorem B6333929 : Blo 876568 6333929 := bstep (se 2 (by rfl) ⟨2375223, by rfl⟩ : syracuseStep 6333929 = 4750447) B4750447
theorem B877807 : Blo 876568 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B1408303 : Blo 876568 1408303 := bstep (se 1 (by rfl) ⟨1056227, by rfl⟩ : syracuseStep 1408303 = 2112455) B2112455
theorem B1877737 : Blo 876568 1877737 := bstep (se 2 (by rfl) ⟨704151, by rfl⟩ : syracuseStep 1877737 = 1408303) B1408303
theorem B27838313 : Blo 876568 27838313 := bstep (se 2 (by rfl) ⟨10439367, by rfl⟩ : syracuseStep 27838313 = 20878735) B20878735
theorem B4222619 : Blo 876568 4222619 := bstep (se 1 (by rfl) ⟨3166964, by rfl⟩ : syracuseStep 4222619 = 6333929) B6333929
theorem B18558875 : Blo 876568 18558875 := bstep (se 1 (by rfl) ⟨13919156, by rfl⟩ : syracuseStep 18558875 = 27838313) B27838313
theorem B2503649 : Blo 876568 2503649 := bstep (se 2 (by rfl) ⟨938868, by rfl⟩ : syracuseStep 2503649 = 1877737) B1877737
theorem B2815079 : Blo 876568 2815079 := bstep (se 1 (by rfl) ⟨2111309, by rfl⟩ : syracuseStep 2815079 = 4222619) B4222619
theorem B7506877 : Blo 876568 7506877 := bstep (se 3 (by rfl) ⟨1407539, by rfl⟩ : syracuseStep 7506877 = 2815079) B2815079
theorem B12372583 : Blo 876568 12372583 := bstep (se 1 (by rfl) ⟨9279437, by rfl⟩ : syracuseStep 12372583 = 18558875) B18558875
theorem B1669099 : Blo 876568 1669099 := bstep (se 1 (by rfl) ⟨1251824, by rfl⟩ : syracuseStep 1669099 = 2503649) B2503649
theorem B16496777 : Blo 876568 16496777 := bstep (se 2 (by rfl) ⟨6186291, by rfl⟩ : syracuseStep 16496777 = 12372583) B12372583
theorem B10009169 : Blo 876568 10009169 := bstep (se 2 (by rfl) ⟨3753438, by rfl⟩ : syracuseStep 10009169 = 7506877) B7506877
theorem B2225465 : Blo 876568 2225465 := bstep (se 2 (by rfl) ⟨834549, by rfl⟩ : syracuseStep 2225465 = 1669099) B1669099
theorem B1483643 : Blo 876568 1483643 := bstep (se 1 (by rfl) ⟨1112732, by rfl⟩ : syracuseStep 1483643 = 2225465) B2225465
theorem B10997851 : Blo 876568 10997851 := bstep (se 1 (by rfl) ⟨8248388, by rfl⟩ : syracuseStep 10997851 = 16496777) B16496777
theorem B6672779 : Blo 876568 6672779 := bstep (se 1 (by rfl) ⟨5004584, by rfl⟩ : syracuseStep 6672779 = 10009169) B10009169
theorem B989095 : Blo 876568 989095 := bstep (se 1 (by rfl) ⟨741821, by rfl⟩ : syracuseStep 989095 = 1483643) B1483643
theorem B14663801 : Blo 876568 14663801 := bstep (se 2 (by rfl) ⟨5498925, by rfl⟩ : syracuseStep 14663801 = 10997851) B10997851
theorem B4448519 : Blo 876568 4448519 := bstep (se 1 (by rfl) ⟨3336389, by rfl⟩ : syracuseStep 4448519 = 6672779) B6672779
theorem B1318793 : Blo 876568 1318793 := bstep (se 2 (by rfl) ⟨494547, by rfl⟩ : syracuseStep 1318793 = 989095) B989095
theorem B39103469 : Blo 876568 39103469 := bstep (se 3 (by rfl) ⟨7331900, by rfl⟩ : syracuseStep 39103469 = 14663801) B14663801
theorem B2965679 : Blo 876568 2965679 := bstep (se 1 (by rfl) ⟨2224259, by rfl⟩ : syracuseStep 2965679 = 4448519) B4448519
theorem B1977119 : Blo 876568 1977119 := bstep (se 1 (by rfl) ⟨1482839, by rfl⟩ : syracuseStep 1977119 = 2965679) B2965679
theorem B26068979 : Blo 876568 26068979 := bstep (se 1 (by rfl) ⟨19551734, by rfl⟩ : syracuseStep 26068979 = 39103469) B39103469
theorem B879195 : Blo 876568 879195 := bstep (se 1 (by rfl) ⟨659396, by rfl⟩ : syracuseStep 879195 = 1318793) B1318793
theorem B1318079 : Blo 876568 1318079 := bstep (se 1 (by rfl) ⟨988559, by rfl⟩ : syracuseStep 1318079 = 1977119) B1977119
theorem B17379319 : Blo 876568 17379319 := bstep (se 1 (by rfl) ⟨13034489, by rfl⟩ : syracuseStep 17379319 = 26068979) B26068979
theorem B23172425 : Blo 876568 23172425 := bstep (se 2 (by rfl) ⟨8689659, by rfl⟩ : syracuseStep 23172425 = 17379319) B17379319
theorem B878719 : Blo 876568 878719 := bstep (se 1 (by rfl) ⟨659039, by rfl⟩ : syracuseStep 878719 = 1318079) B1318079
theorem B15448283 : Blo 876568 15448283 := bstep (se 1 (by rfl) ⟨11586212, by rfl⟩ : syracuseStep 15448283 = 23172425) B23172425
theorem B10298855 : Blo 876568 10298855 := bstep (se 1 (by rfl) ⟨7724141, by rfl⟩ : syracuseStep 10298855 = 15448283) B15448283
theorem B6865903 : Blo 876568 6865903 := bstep (se 1 (by rfl) ⟨5149427, by rfl⟩ : syracuseStep 6865903 = 10298855) B10298855
theorem B36618149 : Blo 876568 36618149 := bstep (se 4 (by rfl) ⟨3432951, by rfl⟩ : syracuseStep 36618149 = 6865903) B6865903
theorem B24412099 : Blo 876568 24412099 := bstep (se 1 (by rfl) ⟨18309074, by rfl⟩ : syracuseStep 24412099 = 36618149) B36618149
theorem B32549465 : Blo 876568 32549465 := bstep (se 2 (by rfl) ⟨12206049, by rfl⟩ : syracuseStep 32549465 = 24412099) B24412099
theorem B86798573 : Blo 876568 86798573 := bstep (se 3 (by rfl) ⟨16274732, by rfl⟩ : syracuseStep 86798573 = 32549465) B32549465
theorem B57865715 : Blo 876568 57865715 := bstep (se 1 (by rfl) ⟨43399286, by rfl⟩ : syracuseStep 57865715 = 86798573) B86798573
theorem B38577143 : Blo 876568 38577143 := bstep (se 1 (by rfl) ⟨28932857, by rfl⟩ : syracuseStep 38577143 = 57865715) B57865715
theorem B25718095 : Blo 876568 25718095 := bstep (se 1 (by rfl) ⟨19288571, by rfl⟩ : syracuseStep 25718095 = 38577143) B38577143
theorem B34290793 : Blo 876568 34290793 := bstep (se 2 (by rfl) ⟨12859047, by rfl⟩ : syracuseStep 34290793 = 25718095) B25718095
theorem B45721057 : Blo 876568 45721057 := bstep (se 2 (by rfl) ⟨17145396, by rfl⟩ : syracuseStep 45721057 = 34290793) B34290793
theorem B60961409 : Blo 876568 60961409 := bstep (se 2 (by rfl) ⟨22860528, by rfl⟩ : syracuseStep 60961409 = 45721057) B45721057
theorem B40640939 : Blo 876568 40640939 := bstep (se 1 (by rfl) ⟨30480704, by rfl⟩ : syracuseStep 40640939 = 60961409) B60961409
theorem B27093959 : Blo 876568 27093959 := bstep (se 1 (by rfl) ⟨20320469, by rfl⟩ : syracuseStep 27093959 = 40640939) B40640939
theorem B18062639 : Blo 876568 18062639 := bstep (se 1 (by rfl) ⟨13546979, by rfl⟩ : syracuseStep 18062639 = 27093959) B27093959
theorem B12041759 : Blo 876568 12041759 := bstep (se 1 (by rfl) ⟨9031319, by rfl⟩ : syracuseStep 12041759 = 18062639) B18062639
theorem B8027839 : Blo 876568 8027839 := bstep (se 1 (by rfl) ⟨6020879, by rfl⟩ : syracuseStep 8027839 = 12041759) B12041759
theorem B42815141 : Blo 876568 42815141 := bstep (se 4 (by rfl) ⟨4013919, by rfl⟩ : syracuseStep 42815141 = 8027839) B8027839
theorem B28543427 : Blo 876568 28543427 := bstep (se 1 (by rfl) ⟨21407570, by rfl⟩ : syracuseStep 28543427 = 42815141) B42815141
theorem B19028951 : Blo 876568 19028951 := bstep (se 1 (by rfl) ⟨14271713, by rfl⟩ : syracuseStep 19028951 = 28543427) B28543427
theorem B12685967 : Blo 876568 12685967 := bstep (se 1 (by rfl) ⟨9514475, by rfl⟩ : syracuseStep 12685967 = 19028951) B19028951
theorem B8457311 : Blo 876568 8457311 := bstep (se 1 (by rfl) ⟨6342983, by rfl⟩ : syracuseStep 8457311 = 12685967) B12685967
theorem B5638207 : Blo 876568 5638207 := bstep (se 1 (by rfl) ⟨4228655, by rfl⟩ : syracuseStep 5638207 = 8457311) B8457311
theorem B7517609 : Blo 876568 7517609 := bstep (se 2 (by rfl) ⟨2819103, by rfl⟩ : syracuseStep 7517609 = 5638207) B5638207
theorem B5011739 : Blo 876568 5011739 := bstep (se 1 (by rfl) ⟨3758804, by rfl⟩ : syracuseStep 5011739 = 7517609) B7517609
theorem B3341159 : Blo 876568 3341159 := bstep (se 1 (by rfl) ⟨2505869, by rfl⟩ : syracuseStep 3341159 = 5011739) B5011739
theorem B2227439 : Blo 876568 2227439 := bstep (se 1 (by rfl) ⟨1670579, by rfl⟩ : syracuseStep 2227439 = 3341159) B3341159
theorem B1484959 : Blo 876568 1484959 := bstep (se 1 (by rfl) ⟨1113719, by rfl⟩ : syracuseStep 1484959 = 2227439) B2227439
theorem B1979945 : Blo 876568 1979945 := bstep (se 2 (by rfl) ⟨742479, by rfl⟩ : syracuseStep 1979945 = 1484959) B1484959
theorem B1319963 : Blo 876568 1319963 := bstep (se 1 (by rfl) ⟨989972, by rfl⟩ : syracuseStep 1319963 = 1979945) B1979945
theorem B879975 : Blo 876568 879975 := bstep (se 1 (by rfl) ⟨659981, by rfl⟩ : syracuseStep 879975 = 1319963) B1319963

theorem C0 (j : ℕ) (h1 : 219142 ≤ j) (h2 : j ≤ 219841) : Blo 876568 (4 * j + 3) := by
  interval_cases j
  · exact B876571
  · exact B876575
  · exact B876579
  · exact B876583
  · exact B876587
  · exact B876591
  · exact B876595
  · exact B876599
  · exact B876603
  · exact B876607
  · exact B876611
  · exact B876615
  · exact B876619
  · exact B876623
  · exact B876627
  · exact B876631
  · exact B876635
  · exact B876639
  · exact B876643
  · exact B876647
  · exact B876651
  · exact B876655
  · exact B876659
  · exact B876663
  · exact B876667
  · exact B876671
  · exact B876675
  · exact B876679
  · exact B876683
  · exact B876687
  · exact B876691
  · exact B876695
  · exact B876699
  · exact B876703
  · exact B876707
  · exact B876711
  · exact B876715
  · exact B876719
  · exact B876723
  · exact B876727
  · exact B876731
  · exact B876735
  · exact B876739
  · exact B876743
  · exact B876747
  · exact B876751
  · exact B876755
  · exact B876759
  · exact B876763
  · exact B876767
  · exact B876771
  · exact B876775
  · exact B876779
  · exact B876783
  · exact B876787
  · exact B876791
  · exact B876795
  · exact B876799
  · exact B876803
  · exact B876807
  · exact B876811
  · exact B876815
  · exact B876819
  · exact B876823
  · exact B876827
  · exact B876831
  · exact B876835
  · exact B876839
  · exact B876843
  · exact B876847
  · exact B876851
  · exact B876855
  · exact B876859
  · exact B876863
  · exact B876867
  · exact B876871
  · exact B876875
  · exact B876879
  · exact B876883
  · exact B876887
  · exact B876891
  · exact B876895
  · exact B876899
  · exact B876903
  · exact B876907
  · exact B876911
  · exact B876915
  · exact B876919
  · exact B876923
  · exact B876927
  · exact B876931
  · exact B876935
  · exact B876939
  · exact B876943
  · exact B876947
  · exact B876951
  · exact B876955
  · exact B876959
  · exact B876963
  · exact B876967
  · exact B876971
  · exact B876975
  · exact B876979
  · exact B876983
  · exact B876987
  · exact B876991
  · exact B876995
  · exact B876999
  · exact B877003
  · exact B877007
  · exact B877011
  · exact B877015
  · exact B877019
  · exact B877023
  · exact B877027
  · exact B877031
  · exact B877035
  · exact B877039
  · exact B877043
  · exact B877047
  · exact B877051
  · exact B877055
  · exact B877059
  · exact B877063
  · exact B877067
  · exact B877071
  · exact B877075
  · exact B877079
  · exact B877083
  · exact B877087
  · exact B877091
  · exact B877095
  · exact B877099
  · exact B877103
  · exact B877107
  · exact B877111
  · exact B877115
  · exact B877119
  · exact B877123
  · exact B877127
  · exact B877131
  · exact B877135
  · exact B877139
  · exact B877143
  · exact B877147
  · exact B877151
  · exact B877155
  · exact B877159
  · exact B877163
  · exact B877167
  · exact B877171
  · exact B877175
  · exact B877179
  · exact B877183
  · exact B877187
  · exact B877191
  · exact B877195
  · exact B877199
  · exact B877203
  · exact B877207
  · exact B877211
  · exact B877215
  · exact B877219
  · exact B877223
  · exact B877227
  · exact B877231
  · exact B877235
  · exact B877239
  · exact B877243
  · exact B877247
  · exact B877251
  · exact B877255
  · exact B877259
  · exact B877263
  · exact B877267
  · exact B877271
  · exact B877275
  · exact B877279
  · exact B877283
  · exact B877287
  · exact B877291
  · exact B877295
  · exact B877299
  · exact B877303
  · exact B877307
  · exact B877311
  · exact B877315
  · exact B877319
  · exact B877323
  · exact B877327
  · exact B877331
  · exact B877335
  · exact B877339
  · exact B877343
  · exact B877347
  · exact B877351
  · exact B877355
  · exact B877359
  · exact B877363
  · exact B877367
  · exact B877371
  · exact B877375
  · exact B877379
  · exact B877383
  · exact B877387
  · exact B877391
  · exact B877395
  · exact B877399
  · exact B877403
  · exact B877407
  · exact B877411
  · exact B877415
  · exact B877419
  · exact B877423
  · exact B877427
  · exact B877431
  · exact B877435
  · exact B877439
  · exact B877443
  · exact B877447
  · exact B877451
  · exact B877455
  · exact B877459
  · exact B877463
  · exact B877467
  · exact B877471
  · exact B877475
  · exact B877479
  · exact B877483
  · exact B877487
  · exact B877491
  · exact B877495
  · exact B877499
  · exact B877503
  · exact B877507
  · exact B877511
  · exact B877515
  · exact B877519
  · exact B877523
  · exact B877527
  · exact B877531
  · exact B877535
  · exact B877539
  · exact B877543
  · exact B877547
  · exact B877551
  · exact B877555
  · exact B877559
  · exact B877563
  · exact B877567
  · exact B877571
  · exact B877575
  · exact B877579
  · exact B877583
  · exact B877587
  · exact B877591
  · exact B877595
  · exact B877599
  · exact B877603
  · exact B877607
  · exact B877611
  · exact B877615
  · exact B877619
  · exact B877623
  · exact B877627
  · exact B877631
  · exact B877635
  · exact B877639
  · exact B877643
  · exact B877647
  · exact B877651
  · exact B877655
  · exact B877659
  · exact B877663
  · exact B877667
  · exact B877671
  · exact B877675
  · exact B877679
  · exact B877683
  · exact B877687
  · exact B877691
  · exact B877695
  · exact B877699
  · exact B877703
  · exact B877707
  · exact B877711
  · exact B877715
  · exact B877719
  · exact B877723
  · exact B877727
  · exact B877731
  · exact B877735
  · exact B877739
  · exact B877743
  · exact B877747
  · exact B877751
  · exact B877755
  · exact B877759
  · exact B877763
  · exact B877767
  · exact B877771
  · exact B877775
  · exact B877779
  · exact B877783
  · exact B877787
  · exact B877791
  · exact B877795
  · exact B877799
  · exact B877803
  · exact B877807
  · exact B877811
  · exact B877815
  · exact B877819
  · exact B877823
  · exact B877827
  · exact B877831
  · exact B877835
  · exact B877839
  · exact B877843
  · exact B877847
  · exact B877851
  · exact B877855
  · exact B877859
  · exact B877863
  · exact B877867
  · exact B877871
  · exact B877875
  · exact B877879
  · exact B877883
  · exact B877887
  · exact B877891
  · exact B877895
  · exact B877899
  · exact B877903
  · exact B877907
  · exact B877911
  · exact B877915
  · exact B877919
  · exact B877923
  · exact B877927
  · exact B877931
  · exact B877935
  · exact B877939
  · exact B877943
  · exact B877947
  · exact B877951
  · exact B877955
  · exact B877959
  · exact B877963
  · exact B877967
  · exact B877971
  · exact B877975
  · exact B877979
  · exact B877983
  · exact B877987
  · exact B877991
  · exact B877995
  · exact B877999
  · exact B878003
  · exact B878007
  · exact B878011
  · exact B878015
  · exact B878019
  · exact B878023
  · exact B878027
  · exact B878031
  · exact B878035
  · exact B878039
  · exact B878043
  · exact B878047
  · exact B878051
  · exact B878055
  · exact B878059
  · exact B878063
  · exact B878067
  · exact B878071
  · exact B878075
  · exact B878079
  · exact B878083
  · exact B878087
  · exact B878091
  · exact B878095
  · exact B878099
  · exact B878103
  · exact B878107
  · exact B878111
  · exact B878115
  · exact B878119
  · exact B878123
  · exact B878127
  · exact B878131
  · exact B878135
  · exact B878139
  · exact B878143
  · exact B878147
  · exact B878151
  · exact B878155
  · exact B878159
  · exact B878163
  · exact B878167
  · exact B878171
  · exact B878175
  · exact B878179
  · exact B878183
  · exact B878187
  · exact B878191
  · exact B878195
  · exact B878199
  · exact B878203
  · exact B878207
  · exact B878211
  · exact B878215
  · exact B878219
  · exact B878223
  · exact B878227
  · exact B878231
  · exact B878235
  · exact B878239
  · exact B878243
  · exact B878247
  · exact B878251
  · exact B878255
  · exact B878259
  · exact B878263
  · exact B878267
  · exact B878271
  · exact B878275
  · exact B878279
  · exact B878283
  · exact B878287
  · exact B878291
  · exact B878295
  · exact B878299
  · exact B878303
  · exact B878307
  · exact B878311
  · exact B878315
  · exact B878319
  · exact B878323
  · exact B878327
  · exact B878331
  · exact B878335
  · exact B878339
  · exact B878343
  · exact B878347
  · exact B878351
  · exact B878355
  · exact B878359
  · exact B878363
  · exact B878367
  · exact B878371
  · exact B878375
  · exact B878379
  · exact B878383
  · exact B878387
  · exact B878391
  · exact B878395
  · exact B878399
  · exact B878403
  · exact B878407
  · exact B878411
  · exact B878415
  · exact B878419
  · exact B878423
  · exact B878427
  · exact B878431
  · exact B878435
  · exact B878439
  · exact B878443
  · exact B878447
  · exact B878451
  · exact B878455
  · exact B878459
  · exact B878463
  · exact B878467
  · exact B878471
  · exact B878475
  · exact B878479
  · exact B878483
  · exact B878487
  · exact B878491
  · exact B878495
  · exact B878499
  · exact B878503
  · exact B878507
  · exact B878511
  · exact B878515
  · exact B878519
  · exact B878523
  · exact B878527
  · exact B878531
  · exact B878535
  · exact B878539
  · exact B878543
  · exact B878547
  · exact B878551
  · exact B878555
  · exact B878559
  · exact B878563
  · exact B878567
  · exact B878571
  · exact B878575
  · exact B878579
  · exact B878583
  · exact B878587
  · exact B878591
  · exact B878595
  · exact B878599
  · exact B878603
  · exact B878607
  · exact B878611
  · exact B878615
  · exact B878619
  · exact B878623
  · exact B878627
  · exact B878631
  · exact B878635
  · exact B878639
  · exact B878643
  · exact B878647
  · exact B878651
  · exact B878655
  · exact B878659
  · exact B878663
  · exact B878667
  · exact B878671
  · exact B878675
  · exact B878679
  · exact B878683
  · exact B878687
  · exact B878691
  · exact B878695
  · exact B878699
  · exact B878703
  · exact B878707
  · exact B878711
  · exact B878715
  · exact B878719
  · exact B878723
  · exact B878727
  · exact B878731
  · exact B878735
  · exact B878739
  · exact B878743
  · exact B878747
  · exact B878751
  · exact B878755
  · exact B878759
  · exact B878763
  · exact B878767
  · exact B878771
  · exact B878775
  · exact B878779
  · exact B878783
  · exact B878787
  · exact B878791
  · exact B878795
  · exact B878799
  · exact B878803
  · exact B878807
  · exact B878811
  · exact B878815
  · exact B878819
  · exact B878823
  · exact B878827
  · exact B878831
  · exact B878835
  · exact B878839
  · exact B878843
  · exact B878847
  · exact B878851
  · exact B878855
  · exact B878859
  · exact B878863
  · exact B878867
  · exact B878871
  · exact B878875
  · exact B878879
  · exact B878883
  · exact B878887
  · exact B878891
  · exact B878895
  · exact B878899
  · exact B878903
  · exact B878907
  · exact B878911
  · exact B878915
  · exact B878919
  · exact B878923
  · exact B878927
  · exact B878931
  · exact B878935
  · exact B878939
  · exact B878943
  · exact B878947
  · exact B878951
  · exact B878955
  · exact B878959
  · exact B878963
  · exact B878967
  · exact B878971
  · exact B878975
  · exact B878979
  · exact B878983
  · exact B878987
  · exact B878991
  · exact B878995
  · exact B878999
  · exact B879003
  · exact B879007
  · exact B879011
  · exact B879015
  · exact B879019
  · exact B879023
  · exact B879027
  · exact B879031
  · exact B879035
  · exact B879039
  · exact B879043
  · exact B879047
  · exact B879051
  · exact B879055
  · exact B879059
  · exact B879063
  · exact B879067
  · exact B879071
  · exact B879075
  · exact B879079
  · exact B879083
  · exact B879087
  · exact B879091
  · exact B879095
  · exact B879099
  · exact B879103
  · exact B879107
  · exact B879111
  · exact B879115
  · exact B879119
  · exact B879123
  · exact B879127
  · exact B879131
  · exact B879135
  · exact B879139
  · exact B879143
  · exact B879147
  · exact B879151
  · exact B879155
  · exact B879159
  · exact B879163
  · exact B879167
  · exact B879171
  · exact B879175
  · exact B879179
  · exact B879183
  · exact B879187
  · exact B879191
  · exact B879195
  · exact B879199
  · exact B879203
  · exact B879207
  · exact B879211
  · exact B879215
  · exact B879219
  · exact B879223
  · exact B879227
  · exact B879231
  · exact B879235
  · exact B879239
  · exact B879243
  · exact B879247
  · exact B879251
  · exact B879255
  · exact B879259
  · exact B879263
  · exact B879267
  · exact B879271
  · exact B879275
  · exact B879279
  · exact B879283
  · exact B879287
  · exact B879291
  · exact B879295
  · exact B879299
  · exact B879303
  · exact B879307
  · exact B879311
  · exact B879315
  · exact B879319
  · exact B879323
  · exact B879327
  · exact B879331
  · exact B879335
  · exact B879339
  · exact B879343
  · exact B879347
  · exact B879351
  · exact B879355
  · exact B879359
  · exact B879363
  · exact B879367

theorem C1 (j : ℕ) (h1 : 219842 ≤ j) (h2 : j ≤ 220141) : Blo 876568 (4 * j + 3) := by
  interval_cases j
  · exact B879371
  · exact B879375
  · exact B879379
  · exact B879383
  · exact B879387
  · exact B879391
  · exact B879395
  · exact B879399
  · exact B879403
  · exact B879407
  · exact B879411
  · exact B879415
  · exact B879419
  · exact B879423
  · exact B879427
  · exact B879431
  · exact B879435
  · exact B879439
  · exact B879443
  · exact B879447
  · exact B879451
  · exact B879455
  · exact B879459
  · exact B879463
  · exact B879467
  · exact B879471
  · exact B879475
  · exact B879479
  · exact B879483
  · exact B879487
  · exact B879491
  · exact B879495
  · exact B879499
  · exact B879503
  · exact B879507
  · exact B879511
  · exact B879515
  · exact B879519
  · exact B879523
  · exact B879527
  · exact B879531
  · exact B879535
  · exact B879539
  · exact B879543
  · exact B879547
  · exact B879551
  · exact B879555
  · exact B879559
  · exact B879563
  · exact B879567
  · exact B879571
  · exact B879575
  · exact B879579
  · exact B879583
  · exact B879587
  · exact B879591
  · exact B879595
  · exact B879599
  · exact B879603
  · exact B879607
  · exact B879611
  · exact B879615
  · exact B879619
  · exact B879623
  · exact B879627
  · exact B879631
  · exact B879635
  · exact B879639
  · exact B879643
  · exact B879647
  · exact B879651
  · exact B879655
  · exact B879659
  · exact B879663
  · exact B879667
  · exact B879671
  · exact B879675
  · exact B879679
  · exact B879683
  · exact B879687
  · exact B879691
  · exact B879695
  · exact B879699
  · exact B879703
  · exact B879707
  · exact B879711
  · exact B879715
  · exact B879719
  · exact B879723
  · exact B879727
  · exact B879731
  · exact B879735
  · exact B879739
  · exact B879743
  · exact B879747
  · exact B879751
  · exact B879755
  · exact B879759
  · exact B879763
  · exact B879767
  · exact B879771
  · exact B879775
  · exact B879779
  · exact B879783
  · exact B879787
  · exact B879791
  · exact B879795
  · exact B879799
  · exact B879803
  · exact B879807
  · exact B879811
  · exact B879815
  · exact B879819
  · exact B879823
  · exact B879827
  · exact B879831
  · exact B879835
  · exact B879839
  · exact B879843
  · exact B879847
  · exact B879851
  · exact B879855
  · exact B879859
  · exact B879863
  · exact B879867
  · exact B879871
  · exact B879875
  · exact B879879
  · exact B879883
  · exact B879887
  · exact B879891
  · exact B879895
  · exact B879899
  · exact B879903
  · exact B879907
  · exact B879911
  · exact B879915
  · exact B879919
  · exact B879923
  · exact B879927
  · exact B879931
  · exact B879935
  · exact B879939
  · exact B879943
  · exact B879947
  · exact B879951
  · exact B879955
  · exact B879959
  · exact B879963
  · exact B879967
  · exact B879971
  · exact B879975
  · exact B879979
  · exact B879983
  · exact B879987
  · exact B879991
  · exact B879995
  · exact B879999
  · exact B880003
  · exact B880007
  · exact B880011
  · exact B880015
  · exact B880019
  · exact B880023
  · exact B880027
  · exact B880031
  · exact B880035
  · exact B880039
  · exact B880043
  · exact B880047
  · exact B880051
  · exact B880055
  · exact B880059
  · exact B880063
  · exact B880067
  · exact B880071
  · exact B880075
  · exact B880079
  · exact B880083
  · exact B880087
  · exact B880091
  · exact B880095
  · exact B880099
  · exact B880103
  · exact B880107
  · exact B880111
  · exact B880115
  · exact B880119
  · exact B880123
  · exact B880127
  · exact B880131
  · exact B880135
  · exact B880139
  · exact B880143
  · exact B880147
  · exact B880151
  · exact B880155
  · exact B880159
  · exact B880163
  · exact B880167
  · exact B880171
  · exact B880175
  · exact B880179
  · exact B880183
  · exact B880187
  · exact B880191
  · exact B880195
  · exact B880199
  · exact B880203
  · exact B880207
  · exact B880211
  · exact B880215
  · exact B880219
  · exact B880223
  · exact B880227
  · exact B880231
  · exact B880235
  · exact B880239
  · exact B880243
  · exact B880247
  · exact B880251
  · exact B880255
  · exact B880259
  · exact B880263
  · exact B880267
  · exact B880271
  · exact B880275
  · exact B880279
  · exact B880283
  · exact B880287
  · exact B880291
  · exact B880295
  · exact B880299
  · exact B880303
  · exact B880307
  · exact B880311
  · exact B880315
  · exact B880319
  · exact B880323
  · exact B880327
  · exact B880331
  · exact B880335
  · exact B880339
  · exact B880343
  · exact B880347
  · exact B880351
  · exact B880355
  · exact B880359
  · exact B880363
  · exact B880367
  · exact B880371
  · exact B880375
  · exact B880379
  · exact B880383
  · exact B880387
  · exact B880391
  · exact B880395
  · exact B880399
  · exact B880403
  · exact B880407
  · exact B880411
  · exact B880415
  · exact B880419
  · exact B880423
  · exact B880427
  · exact B880431
  · exact B880435
  · exact B880439
  · exact B880443
  · exact B880447
  · exact B880451
  · exact B880455
  · exact B880459
  · exact B880463
  · exact B880467
  · exact B880471
  · exact B880475
  · exact B880479
  · exact B880483
  · exact B880487
  · exact B880491
  · exact B880495
  · exact B880499
  · exact B880503
  · exact B880507
  · exact B880511
  · exact B880515
  · exact B880519
  · exact B880523
  · exact B880527
  · exact B880531
  · exact B880535
  · exact B880539
  · exact B880543
  · exact B880547
  · exact B880551
  · exact B880555
  · exact B880559
  · exact B880563
  · exact B880567

theorem solution (m : ℕ) (hlo : 876568 ≤ m) (hhi : m ≤ 880568) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 219142 ≤ j := by omega
    have hj2 : j ≤ 220141 := by omega
    have hb : Blo 876568 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 219842 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
