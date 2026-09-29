-- Prove2me | solution 1 for syracuse_descends_range_1766084_1768084
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:40:35.759655+00:00
-- url     : https://prove2.me/submissions/c1c6f1b6-f76c-443c-935c-40d87083c255

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


theorem B2981893 : Blo 1766084 2981893 := bbase (se 4 (by rfl) ⟨279552, by rfl⟩ : syracuseStep 2981893 = 559105) (by norm_num)
theorem B5963813 : Blo 1766084 5963813 := bbase (se 4 (by rfl) ⟨559107, by rfl⟩ : syracuseStep 5963813 = 1118215) (by norm_num)
theorem B2121805 : Blo 1766084 2121805 := bbase (se 3 (by rfl) ⟨397838, by rfl⟩ : syracuseStep 2121805 = 795677) (by norm_num)
theorem B2236501 : Blo 1766084 2236501 := bbase (se 8 (by rfl) ⟨13104, by rfl⟩ : syracuseStep 2236501 = 26209) (by norm_num)
theorem B2015317 : Blo 1766084 2015317 := bbase (se 8 (by rfl) ⟨11808, by rfl⟩ : syracuseStep 2015317 = 23617) (by norm_num)
theorem B2981981 : Blo 1766084 2981981 := bbase (se 3 (by rfl) ⟨559121, by rfl⟩ : syracuseStep 2981981 = 1118243) (by norm_num)
theorem B2515045 : Blo 1766084 2515045 := bbase (se 4 (by rfl) ⟨235785, by rfl⟩ : syracuseStep 2515045 = 471571) (by norm_num)
theorem B4472941 : Blo 1766084 4472941 := bbase (se 3 (by rfl) ⟨838676, by rfl⟩ : syracuseStep 4472941 = 1677353) (by norm_num)
theorem B5660837 : Blo 1766084 5660837 := bbase (se 4 (by rfl) ⟨530703, by rfl⟩ : syracuseStep 5660837 = 1061407) (by norm_num)
theorem B2515141 : Blo 1766084 2515141 := bbase (se 4 (by rfl) ⟨235794, by rfl⟩ : syracuseStep 2515141 = 471589) (by norm_num)
theorem B30613717 : Blo 1766084 30613717 := bbase (se 7 (by rfl) ⟨358754, by rfl⟩ : syracuseStep 30613717 = 717509) (by norm_num)
theorem B4473053 : Blo 1766084 4473053 := bbase (se 3 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 4473053 = 1677395) (by norm_num)
theorem B2982109 : Blo 1766084 2982109 := bbase (se 3 (by rfl) ⟨559145, by rfl⟩ : syracuseStep 2982109 = 1118291) (by norm_num)
theorem B3236069 : Blo 1766084 3236069 := bbase (se 4 (by rfl) ⟨303381, by rfl⟩ : syracuseStep 3236069 = 606763) (by norm_num)
theorem B2236673 : Blo 1766084 2236673 := bbase (se 2 (by rfl) ⟨838752, by rfl⟩ : syracuseStep 2236673 = 1677505) (by norm_num)
theorem B5447941 : Blo 1766084 5447941 := bbase (se 4 (by rfl) ⟨510744, by rfl⟩ : syracuseStep 5447941 = 1021489) (by norm_num)
theorem B2982197 : Blo 1766084 2982197 := bbase (se 5 (by rfl) ⟨139790, by rfl⟩ : syracuseStep 2982197 = 279581) (by norm_num)
theorem B2236729 : Blo 1766084 2236729 := bbase (se 2 (by rfl) ⟨838773, by rfl⟩ : syracuseStep 2236729 = 1677547) (by norm_num)
theorem B38191445 : Blo 1766084 38191445 := bbase (se 10 (by rfl) ⟨55944, by rfl⟩ : syracuseStep 38191445 = 111889) (by norm_num)
theorem B2236825 : Blo 1766084 2236825 := bbase (se 2 (by rfl) ⟨838809, by rfl⟩ : syracuseStep 2236825 = 1677619) (by norm_num)
theorem B4473245 : Blo 1766084 4473245 := bbase (se 3 (by rfl) ⟨838733, by rfl⟩ : syracuseStep 4473245 = 1677467) (by norm_num)
theorem B2982325 : Blo 1766084 2982325 := bbase (se 5 (by rfl) ⟨139796, by rfl⟩ : syracuseStep 2982325 = 279593) (by norm_num)
theorem B5964245 : Blo 1766084 5964245 := bbase (se 7 (by rfl) ⟨69893, by rfl⟩ : syracuseStep 5964245 = 139787) (by norm_num)
theorem B5374421 : Blo 1766084 5374421 := bbase (se 7 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 5374421 = 125963) (by norm_num)
theorem B8487413 : Blo 1766084 8487413 := bbase (se 5 (by rfl) ⟨397847, by rfl⟩ : syracuseStep 8487413 = 795695) (by norm_num)
theorem B2982413 : Blo 1766084 2982413 := bbase (se 3 (by rfl) ⟨559202, by rfl⟩ : syracuseStep 2982413 = 1118405) (by norm_num)
theorem B2236997 : Blo 1766084 2236997 := bbase (se 4 (by rfl) ⟨209718, by rfl⟩ : syracuseStep 2236997 = 419437) (by norm_num)
theorem B3973733 : Blo 1766084 3973733 := bbase (se 4 (by rfl) ⟨372537, by rfl⟩ : syracuseStep 3973733 = 745075) (by norm_num)
theorem B2237053 : Blo 1766084 2237053 := bbase (se 3 (by rfl) ⟨419447, by rfl⟩ : syracuseStep 2237053 = 838895) (by norm_num)
theorem B2122381 : Blo 1766084 2122381 := bbase (se 3 (by rfl) ⟨397946, by rfl⟩ : syracuseStep 2122381 = 795893) (by norm_num)
theorem B2982541 : Blo 1766084 2982541 := bbase (se 3 (by rfl) ⟨559226, by rfl⟩ : syracuseStep 2982541 = 1118453) (by norm_num)
theorem B3973805 : Blo 1766084 3973805 := bbase (se 3 (by rfl) ⟨745088, by rfl⟩ : syracuseStep 3973805 = 1490177) (by norm_num)
theorem B2515637 : Blo 1766084 2515637 := bbase (se 5 (by rfl) ⟨117920, by rfl⟩ : syracuseStep 2515637 = 235841) (by norm_num)
theorem B2237149 : Blo 1766084 2237149 := bbase (se 3 (by rfl) ⟨419465, by rfl⟩ : syracuseStep 2237149 = 838931) (by norm_num)
theorem B2982629 : Blo 1766084 2982629 := bbase (se 4 (by rfl) ⟨279621, by rfl⟩ : syracuseStep 2982629 = 559243) (by norm_num)
theorem B3973877 : Blo 1766084 3973877 := bbase (se 5 (by rfl) ⟨186275, by rfl⟩ : syracuseStep 3973877 = 372551) (by norm_num)
theorem B4473589 : Blo 1766084 4473589 := bbase (se 5 (by rfl) ⟨209699, by rfl⟩ : syracuseStep 4473589 = 419399) (by norm_num)
theorem B3023605 : Blo 1766084 3023605 := bbase (se 5 (by rfl) ⟨141731, by rfl⟩ : syracuseStep 3023605 = 283463) (by norm_num)
theorem B13607669 : Blo 1766084 13607669 := bbase (se 5 (by rfl) ⟨637859, by rfl⟩ : syracuseStep 13607669 = 1275719) (by norm_num)
theorem B5030693 : Blo 1766084 5030693 := bbase (se 4 (by rfl) ⟨471627, by rfl⟩ : syracuseStep 5030693 = 943255) (by norm_num)
theorem B3973949 : Blo 1766084 3973949 := bbase (se 3 (by rfl) ⟨745115, by rfl⟩ : syracuseStep 3973949 = 1490231) (by norm_num)
theorem B4473701 : Blo 1766084 4473701 := bbase (se 4 (by rfl) ⟨419409, by rfl⟩ : syracuseStep 4473701 = 838819) (by norm_num)
theorem B2982757 : Blo 1766084 2982757 := bbase (se 4 (by rfl) ⟨279633, by rfl⟩ : syracuseStep 2982757 = 559267) (by norm_num)
theorem B3974021 : Blo 1766084 3974021 := bbase (se 4 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 3974021 = 745129) (by norm_num)
theorem B5964677 : Blo 1766084 5964677 := bbase (se 4 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 5964677 = 1118377) (by norm_num)
theorem B2237321 : Blo 1766084 2237321 := bbase (se 2 (by rfl) ⟨838995, by rfl⟩ : syracuseStep 2237321 = 1677991) (by norm_num)
theorem B2982845 : Blo 1766084 2982845 := bbase (se 3 (by rfl) ⟨559283, by rfl⟩ : syracuseStep 2982845 = 1118567) (by norm_num)
theorem B2237377 : Blo 1766084 2237377 := bbase (se 2 (by rfl) ⟨839016, by rfl⟩ : syracuseStep 2237377 = 1678033) (by norm_num)
theorem B3974093 : Blo 1766084 3974093 := bbase (se 3 (by rfl) ⟨745142, by rfl⟩ : syracuseStep 3974093 = 1490285) (by norm_num)
theorem B3974165 : Blo 1766084 3974165 := bbase (se 6 (by rfl) ⟨93144, by rfl⟩ : syracuseStep 3974165 = 186289) (by norm_num)
theorem B2237473 : Blo 1766084 2237473 := bbase (se 2 (by rfl) ⟨839052, by rfl⟩ : syracuseStep 2237473 = 1678105) (by norm_num)
theorem B5661733 : Blo 1766084 5661733 := bbase (se 4 (by rfl) ⟨530787, by rfl⟩ : syracuseStep 5661733 = 1061575) (by norm_num)
theorem B6710309 : Blo 1766084 6710309 := bbase (se 4 (by rfl) ⟨629091, by rfl⟩ : syracuseStep 6710309 = 1258183) (by norm_num)
theorem B4473893 : Blo 1766084 4473893 := bbase (se 4 (by rfl) ⟨419427, by rfl⟩ : syracuseStep 4473893 = 838855) (by norm_num)
theorem B2982973 : Blo 1766084 2982973 := bbase (se 3 (by rfl) ⟨559307, by rfl⟩ : syracuseStep 2982973 = 1118615) (by norm_num)
theorem B8946773 : Blo 1766084 8946773 := bbase (se 8 (by rfl) ⟨52422, by rfl⟩ : syracuseStep 8946773 = 104845) (by norm_num)
theorem B3974237 : Blo 1766084 3974237 := bbase (se 3 (by rfl) ⟨745169, by rfl⟩ : syracuseStep 3974237 = 1490339) (by norm_num)
theorem B10069109 : Blo 1766084 10069109 := bbase (se 5 (by rfl) ⟨471989, by rfl⟩ : syracuseStep 10069109 = 943979) (by norm_num)
theorem B2983061 : Blo 1766084 2983061 := bbase (se 6 (by rfl) ⟨69915, by rfl⟩ : syracuseStep 2983061 = 139831) (by norm_num)
theorem B3974309 : Blo 1766084 3974309 := bbase (se 4 (by rfl) ⟨372591, by rfl⟩ : syracuseStep 3974309 = 745183) (by norm_num)
theorem B2868413 : Blo 1766084 2868413 := bbase (se 3 (by rfl) ⟨537827, by rfl⟩ : syracuseStep 2868413 = 1075655) (by norm_num)
theorem B2237645 : Blo 1766084 2237645 := bbase (se 3 (by rfl) ⟨419558, by rfl⟩ : syracuseStep 2237645 = 839117) (by norm_num)
theorem B2516189 : Blo 1766084 2516189 := bbase (se 3 (by rfl) ⟨471785, by rfl⟩ : syracuseStep 2516189 = 943571) (by norm_num)
theorem B3974381 : Blo 1766084 3974381 := bbase (se 3 (by rfl) ⟨745196, by rfl⟩ : syracuseStep 3974381 = 1490393) (by norm_num)
theorem B2688245 : Blo 1766084 2688245 := bbase (se 5 (by rfl) ⟨126011, by rfl⟩ : syracuseStep 2688245 = 252023) (by norm_num)
theorem B2237701 : Blo 1766084 2237701 := bbase (se 4 (by rfl) ⟨209784, by rfl⟩ : syracuseStep 2237701 = 419569) (by norm_num)
theorem B2983189 : Blo 1766084 2983189 := bbase (se 6 (by rfl) ⟨69918, by rfl⟩ : syracuseStep 2983189 = 139837) (by norm_num)
theorem B3974453 : Blo 1766084 3974453 := bbase (se 5 (by rfl) ⟨186302, by rfl⟩ : syracuseStep 3974453 = 372605) (by norm_num)
theorem B5965109 : Blo 1766084 5965109 := bbase (se 5 (by rfl) ⟨279614, by rfl⟩ : syracuseStep 5965109 = 559229) (by norm_num)
theorem B6710597 : Blo 1766084 6710597 := bbase (se 4 (by rfl) ⟨629118, by rfl⟩ : syracuseStep 6710597 = 1258237) (by norm_num)
theorem B2983277 : Blo 1766084 2983277 := bbase (se 3 (by rfl) ⟨559364, by rfl⟩ : syracuseStep 2983277 = 1118729) (by norm_num)
theorem B7546229 : Blo 1766084 7546229 := bbase (se 5 (by rfl) ⟨353729, by rfl⟩ : syracuseStep 7546229 = 707459) (by norm_num)
theorem B3974525 : Blo 1766084 3974525 := bbase (se 3 (by rfl) ⟨745223, by rfl⟩ : syracuseStep 3974525 = 1490447) (by norm_num)
theorem B4474237 : Blo 1766084 4474237 := bbase (se 3 (by rfl) ⟨838919, by rfl⟩ : syracuseStep 4474237 = 1677839) (by norm_num)
theorem B5662133 : Blo 1766084 5662133 := bbase (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) (by norm_num)
theorem B3974597 : Blo 1766084 3974597 := bbase (se 4 (by rfl) ⟨372618, by rfl⟩ : syracuseStep 3974597 = 745237) (by norm_num)
theorem B4474349 : Blo 1766084 4474349 := bbase (se 3 (by rfl) ⟨838940, by rfl⟩ : syracuseStep 4474349 = 1677881) (by norm_num)
theorem B2983405 : Blo 1766084 2983405 := bbase (se 3 (by rfl) ⟨559388, by rfl⟩ : syracuseStep 2983405 = 1118777) (by norm_num)
theorem B3974669 : Blo 1766084 3974669 := bbase (se 3 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 3974669 = 1490501) (by norm_num)
theorem B3065357 : Blo 1766084 3065357 := bbase (se 3 (by rfl) ⟨574754, by rfl⟩ : syracuseStep 3065357 = 1149509) (by norm_num)
theorem B3229229 : Blo 1766084 3229229 := bbase (se 3 (by rfl) ⟨605480, by rfl⟩ : syracuseStep 3229229 = 1210961) (by norm_num)
theorem B2983493 : Blo 1766084 2983493 := bbase (se 4 (by rfl) ⟨279702, by rfl⟩ : syracuseStep 2983493 = 559405) (by norm_num)
theorem B3974741 : Blo 1766084 3974741 := bbase (se 8 (by rfl) ⟨23289, by rfl⟩ : syracuseStep 3974741 = 46579) (by norm_num)
theorem B2123381 : Blo 1766084 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B7546517 : Blo 1766084 7546517 := bbase (se 6 (by rfl) ⟨176871, by rfl⟩ : syracuseStep 7546517 = 353743) (by norm_num)
theorem B3974813 : Blo 1766084 3974813 := bbase (se 3 (by rfl) ⟨745277, by rfl⟩ : syracuseStep 3974813 = 1490555) (by norm_num)
theorem B2123429 : Blo 1766084 2123429 := bbase (se 4 (by rfl) ⟨199071, by rfl⟩ : syracuseStep 2123429 = 398143) (by norm_num)
theorem B4474541 : Blo 1766084 4474541 := bbase (se 3 (by rfl) ⟨838976, by rfl⟩ : syracuseStep 4474541 = 1677953) (by norm_num)
theorem B2983621 : Blo 1766084 2983621 := bbase (se 4 (by rfl) ⟨279714, by rfl⟩ : syracuseStep 2983621 = 559429) (by norm_num)
theorem B3974885 : Blo 1766084 3974885 := bbase (se 4 (by rfl) ⟨372645, by rfl⟩ : syracuseStep 3974885 = 745291) (by norm_num)
theorem B5965541 : Blo 1766084 5965541 := bbase (se 4 (by rfl) ⟨559269, by rfl⟩ : syracuseStep 5965541 = 1118539) (by norm_num)
theorem B3974957 : Blo 1766084 3974957 := bbase (se 3 (by rfl) ⟨745304, by rfl⟩ : syracuseStep 3974957 = 1490609) (by norm_num)
theorem B4245301 : Blo 1766084 4245301 := bbase (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) (by norm_num)
theorem B3975029 : Blo 1766084 3975029 := bbase (se 5 (by rfl) ⟨186329, by rfl⟩ : syracuseStep 3975029 = 372659) (by norm_num)
theorem B4843397 : Blo 1766084 4843397 := bbase (se 4 (by rfl) ⟨454068, by rfl⟩ : syracuseStep 4843397 = 908137) (by norm_num)
theorem B1886113 : Blo 1766084 1886113 := bbase (se 2 (by rfl) ⟨707292, by rfl⟩ : syracuseStep 1886113 = 1414585) (by norm_num)
theorem B3975101 : Blo 1766084 3975101 := bbase (se 3 (by rfl) ⟨745331, by rfl⟩ : syracuseStep 3975101 = 1490663) (by norm_num)
theorem B5031877 : Blo 1766084 5031877 := bbase (se 4 (by rfl) ⟨471738, by rfl⟩ : syracuseStep 5031877 = 943477) (by norm_num)
theorem B2516941 : Blo 1766084 2516941 := bbase (se 3 (by rfl) ⟨471926, by rfl⟩ : syracuseStep 2516941 = 943853) (by norm_num)
theorem B1886185 : Blo 1766084 1886185 := bbase (se 2 (by rfl) ⟨707319, by rfl⟩ : syracuseStep 1886185 = 1414639) (by norm_num)
theorem B3975173 : Blo 1766084 3975173 := bbase (se 4 (by rfl) ⟨372672, by rfl⟩ : syracuseStep 3975173 = 745345) (by norm_num)
theorem B4474885 : Blo 1766084 4474885 := bbase (se 4 (by rfl) ⟨419520, by rfl⟩ : syracuseStep 4474885 = 839041) (by norm_num)
theorem B3975245 : Blo 1766084 3975245 := bbase (se 3 (by rfl) ⟨745358, by rfl⟩ : syracuseStep 3975245 = 1490717) (by norm_num)
theorem B5032037 : Blo 1766084 5032037 := bbase (se 4 (by rfl) ⟨471753, by rfl⟩ : syracuseStep 5032037 = 943507) (by norm_num)
theorem B4474997 : Blo 1766084 4474997 := bbase (se 5 (by rfl) ⟨209765, by rfl⟩ : syracuseStep 4474997 = 419531) (by norm_num)
theorem B4778117 : Blo 1766084 4778117 := bbase (se 4 (by rfl) ⟨447948, by rfl⟩ : syracuseStep 4778117 = 895897) (by norm_num)
theorem B3975317 : Blo 1766084 3975317 := bbase (se 6 (by rfl) ⟨93171, by rfl⟩ : syracuseStep 3975317 = 186343) (by norm_num)
theorem B20400277 : Blo 1766084 20400277 := bbase (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) (by norm_num)
theorem B5965973 : Blo 1766084 5965973 := bbase (se 6 (by rfl) ⟨139827, by rfl⟩ : syracuseStep 5965973 = 279655) (by norm_num)
theorem B1886365 : Blo 1766084 1886365 := bbase (se 3 (by rfl) ⟨353693, by rfl⟩ : syracuseStep 1886365 = 707387) (by norm_num)
theorem B2123977 : Blo 1766084 2123977 := bbase (se 2 (by rfl) ⟨796491, by rfl⟩ : syracuseStep 2123977 = 1592983) (by norm_num)
theorem B3975389 : Blo 1766084 3975389 := bbase (se 3 (by rfl) ⟨745385, by rfl⟩ : syracuseStep 3975389 = 1490771) (by norm_num)
theorem B3352853 : Blo 1766084 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B3975461 : Blo 1766084 3975461 := bbase (se 4 (by rfl) ⟨372699, by rfl⟩ : syracuseStep 3975461 = 745399) (by norm_num)
theorem B4475189 : Blo 1766084 4475189 := bbase (se 5 (by rfl) ⟨209774, by rfl⟩ : syracuseStep 4475189 = 419549) (by norm_num)
theorem B5032277 : Blo 1766084 5032277 := bbase (se 10 (by rfl) ⟨7371, by rfl⟩ : syracuseStep 5032277 = 14743) (by norm_num)
theorem B8948069 : Blo 1766084 8948069 := bbase (se 4 (by rfl) ⟨838881, by rfl⟩ : syracuseStep 8948069 = 1677763) (by norm_num)
theorem B3975533 : Blo 1766084 3975533 := bbase (se 3 (by rfl) ⟨745412, by rfl⟩ : syracuseStep 3975533 = 1490825) (by norm_num)
theorem B7547269 : Blo 1766084 7547269 := bbase (se 4 (by rfl) ⟨707556, by rfl⟩ : syracuseStep 7547269 = 1415113) (by norm_num)
theorem B8063381 : Blo 1766084 8063381 := bbase (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) (by norm_num)
theorem B3353005 : Blo 1766084 3353005 := bbase (se 3 (by rfl) ⟨628688, by rfl⟩ : syracuseStep 3353005 = 1257377) (by norm_num)
theorem B3975605 : Blo 1766084 3975605 := bbase (se 5 (by rfl) ⟨186356, by rfl⟩ : syracuseStep 3975605 = 372713) (by norm_num)
theorem B6711781 : Blo 1766084 6711781 := bbase (se 4 (by rfl) ⟨629229, by rfl⟩ : syracuseStep 6711781 = 1258459) (by norm_num)
theorem B3975677 : Blo 1766084 3975677 := bbase (se 3 (by rfl) ⟨745439, by rfl⟩ : syracuseStep 3975677 = 1490879) (by norm_num)
theorem B3582461 : Blo 1766084 3582461 := bbase (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) (by norm_num)
theorem B5097989 : Blo 1766084 5097989 := bbase (se 4 (by rfl) ⟨477936, by rfl⟩ : syracuseStep 5097989 = 955873) (by norm_num)
theorem B5032469 : Blo 1766084 5032469 := bbase (se 6 (by rfl) ⟨117948, by rfl⟩ : syracuseStep 5032469 = 235897) (by norm_num)
theorem B3975749 : Blo 1766084 3975749 := bbase (se 4 (by rfl) ⟨372726, by rfl⟩ : syracuseStep 3975749 = 745453) (by norm_num)
theorem B5966405 : Blo 1766084 5966405 := bbase (se 4 (by rfl) ⟨559350, by rfl⟩ : syracuseStep 5966405 = 1118701) (by norm_num)
theorem B1886809 : Blo 1766084 1886809 := bbase (se 2 (by rfl) ⟨707553, by rfl⟩ : syracuseStep 1886809 = 1415107) (by norm_num)
theorem B3975821 : Blo 1766084 3975821 := bbase (se 3 (by rfl) ⟨745466, by rfl⟩ : syracuseStep 3975821 = 1490933) (by norm_num)
theorem B12733109 : Blo 1766084 12733109 := bbase (se 5 (by rfl) ⟨596864, by rfl⟩ : syracuseStep 12733109 = 1193729) (by norm_num)
theorem B1886933 : Blo 1766084 1886933 := bbase (se 7 (by rfl) ⟨22112, by rfl⟩ : syracuseStep 1886933 = 44225) (by norm_num)
theorem B3975893 : Blo 1766084 3975893 := bbase (se 7 (by rfl) ⟨46592, by rfl⟩ : syracuseStep 3975893 = 93185) (by norm_num)
theorem B3353309 : Blo 1766084 3353309 := bbase (se 3 (by rfl) ⟨628745, by rfl⟩ : syracuseStep 3353309 = 1257491) (by norm_num)
theorem B6712085 : Blo 1766084 6712085 := bbase (se 6 (by rfl) ⟨157314, by rfl⟩ : syracuseStep 6712085 = 314629) (by norm_num)
theorem B3975965 : Blo 1766084 3975965 := bbase (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) (by norm_num)
theorem B3976037 : Blo 1766084 3976037 := bbase (se 4 (by rfl) ⟨372753, by rfl⟩ : syracuseStep 3976037 = 745507) (by norm_num)
theorem B3976109 : Blo 1766084 3976109 := bbase (se 3 (by rfl) ⟨745520, by rfl⟩ : syracuseStep 3976109 = 1491041) (by norm_num)
theorem B1887185 : Blo 1766084 1887185 := bbase (se 2 (by rfl) ⟨707694, by rfl⟩ : syracuseStep 1887185 = 1415389) (by norm_num)
theorem B3976181 : Blo 1766084 3976181 := bbase (se 5 (by rfl) ⟨186383, by rfl⟩ : syracuseStep 3976181 = 372767) (by norm_num)
theorem B5966837 : Blo 1766084 5966837 := bbase (se 5 (by rfl) ⟨279695, by rfl⟩ : syracuseStep 5966837 = 559391) (by norm_num)
theorem B2649149 : Blo 1766084 2649149 := bbase (se 3 (by rfl) ⟨496715, by rfl⟩ : syracuseStep 2649149 = 993431) (by norm_num)
theorem B3976253 : Blo 1766084 3976253 := bbase (se 3 (by rfl) ⟨745547, by rfl⟩ : syracuseStep 3976253 = 1491095) (by norm_num)
theorem B2649173 : Blo 1766084 2649173 := bbase (se 8 (by rfl) ⟨15522, by rfl⟩ : syracuseStep 2649173 = 31045) (by norm_num)
theorem B18377813 : Blo 1766084 18377813 := bbase (se 8 (by rfl) ⟨107682, by rfl⟩ : syracuseStep 18377813 = 215365) (by norm_num)
theorem B7548005 : Blo 1766084 7548005 := bbase (se 4 (by rfl) ⟨707625, by rfl⟩ : syracuseStep 7548005 = 1415251) (by norm_num)
theorem B2649197 : Blo 1766084 2649197 := bbase (se 3 (by rfl) ⟨496724, by rfl⟩ : syracuseStep 2649197 = 993449) (by norm_num)
theorem B2649221 : Blo 1766084 2649221 := bbase (se 4 (by rfl) ⟨248364, by rfl⟩ : syracuseStep 2649221 = 496729) (by norm_num)
theorem B3976325 : Blo 1766084 3976325 := bbase (se 4 (by rfl) ⟨372780, by rfl⟩ : syracuseStep 3976325 = 745561) (by norm_num)
theorem B19106965 : Blo 1766084 19106965 := bbase (se 6 (by rfl) ⟨447819, by rfl⟩ : syracuseStep 19106965 = 895639) (by norm_num)
theorem B2649245 : Blo 1766084 2649245 := bbase (se 3 (by rfl) ⟨496733, by rfl⟩ : syracuseStep 2649245 = 993467) (by norm_num)
theorem B4246685 : Blo 1766084 4246685 := bbase (se 3 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 4246685 = 1592507) (by norm_num)
theorem B2649269 : Blo 1766084 2649269 := bbase (se 5 (by rfl) ⟨124184, by rfl⟩ : syracuseStep 2649269 = 248369) (by norm_num)
theorem B2829509 : Blo 1766084 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B2649293 : Blo 1766084 2649293 := bbase (se 3 (by rfl) ⟨496742, by rfl⟩ : syracuseStep 2649293 = 993485) (by norm_num)
theorem B3976397 : Blo 1766084 3976397 := bbase (se 3 (by rfl) ⟨745574, by rfl⟩ : syracuseStep 3976397 = 1491149) (by norm_num)
theorem B2649317 : Blo 1766084 2649317 := bbase (se 4 (by rfl) ⟨248373, by rfl⟩ : syracuseStep 2649317 = 496747) (by norm_num)
theorem B2649341 : Blo 1766084 2649341 := bbase (se 3 (by rfl) ⟨496751, by rfl⟩ : syracuseStep 2649341 = 993503) (by norm_num)
theorem B2649365 : Blo 1766084 2649365 := bbase (se 6 (by rfl) ⟨62094, by rfl⟩ : syracuseStep 2649365 = 124189) (by norm_num)
theorem B3976469 : Blo 1766084 3976469 := bbase (se 6 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 3976469 = 186397) (by norm_num)
theorem B2649389 : Blo 1766084 2649389 := bbase (se 3 (by rfl) ⟨496760, by rfl⟩ : syracuseStep 2649389 = 993521) (by norm_num)
theorem B2649413 : Blo 1766084 2649413 := bbase (se 4 (by rfl) ⟨248382, by rfl⟩ : syracuseStep 2649413 = 496765) (by norm_num)
theorem B2649437 : Blo 1766084 2649437 := bbase (se 3 (by rfl) ⟨496769, by rfl⟩ : syracuseStep 2649437 = 993539) (by norm_num)
theorem B3976541 : Blo 1766084 3976541 := bbase (se 3 (by rfl) ⟨745601, by rfl⟩ : syracuseStep 3976541 = 1491203) (by norm_num)
theorem B4246877 : Blo 1766084 4246877 := bbase (se 3 (by rfl) ⟨796289, by rfl⟩ : syracuseStep 4246877 = 1592579) (by norm_num)
theorem B2649461 : Blo 1766084 2649461 := bbase (se 5 (by rfl) ⟨124193, by rfl⟩ : syracuseStep 2649461 = 248387) (by norm_num)
theorem B2829701 : Blo 1766084 2829701 := bbase (se 4 (by rfl) ⟨265284, by rfl⟩ : syracuseStep 2829701 = 530569) (by norm_num)
theorem B2649485 : Blo 1766084 2649485 := bbase (se 3 (by rfl) ⟨496778, by rfl⟩ : syracuseStep 2649485 = 993557) (by norm_num)
theorem B1887629 : Blo 1766084 1887629 := bbase (se 3 (by rfl) ⟨353930, by rfl⟩ : syracuseStep 1887629 = 707861) (by norm_num)
theorem B2649509 : Blo 1766084 2649509 := bbase (se 4 (by rfl) ⟨248391, by rfl⟩ : syracuseStep 2649509 = 496783) (by norm_num)
theorem B3976613 : Blo 1766084 3976613 := bbase (se 4 (by rfl) ⟨372807, by rfl⟩ : syracuseStep 3976613 = 745615) (by norm_num)
theorem B5967269 : Blo 1766084 5967269 := bbase (se 4 (by rfl) ⟨559431, by rfl⟩ : syracuseStep 5967269 = 1118863) (by norm_num)
theorem B2551213 : Blo 1766084 2551213 := bbase (se 3 (by rfl) ⟨478352, by rfl⟩ : syracuseStep 2551213 = 956705) (by norm_num)
theorem B2649533 : Blo 1766084 2649533 := bbase (se 3 (by rfl) ⟨496787, by rfl⟩ : syracuseStep 2649533 = 993575) (by norm_num)
theorem B3354061 : Blo 1766084 3354061 := bbase (se 3 (by rfl) ⟨628886, by rfl⟩ : syracuseStep 3354061 = 1257773) (by norm_num)
theorem B2649557 : Blo 1766084 2649557 := bbase (se 7 (by rfl) ⟨31049, by rfl⟩ : syracuseStep 2649557 = 62099) (by norm_num)
theorem B2649581 : Blo 1766084 2649581 := bbase (se 3 (by rfl) ⟨496796, by rfl⟩ : syracuseStep 2649581 = 993593) (by norm_num)
theorem B3976685 : Blo 1766084 3976685 := bbase (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) (by norm_num)
theorem B5033461 : Blo 1766084 5033461 := bbase (se 5 (by rfl) ⟨235943, by rfl⟩ : syracuseStep 5033461 = 471887) (by norm_num)
theorem B2649605 : Blo 1766084 2649605 := bbase (se 4 (by rfl) ⟨248400, by rfl⟩ : syracuseStep 2649605 = 496801) (by norm_num)
theorem B2649629 : Blo 1766084 2649629 := bbase (se 3 (by rfl) ⟨496805, by rfl⟩ : syracuseStep 2649629 = 993611) (by norm_num)
theorem B2387485 : Blo 1766084 2387485 := bbase (se 3 (by rfl) ⟨447653, by rfl⟩ : syracuseStep 2387485 = 895307) (by norm_num)
theorem B2649653 : Blo 1766084 2649653 := bbase (se 5 (by rfl) ⟨124202, by rfl⟩ : syracuseStep 2649653 = 248405) (by norm_num)
theorem B3976757 : Blo 1766084 3976757 := bbase (se 5 (by rfl) ⟨186410, by rfl⟩ : syracuseStep 3976757 = 372821) (by norm_num)
theorem B2649677 : Blo 1766084 2649677 := bbase (se 3 (by rfl) ⟨496814, by rfl⟩ : syracuseStep 2649677 = 993629) (by norm_num)
theorem B41938517 : Blo 1766084 41938517 := bbase (se 8 (by rfl) ⟨245733, by rfl⟩ : syracuseStep 41938517 = 491467) (by norm_num)
theorem B3354205 : Blo 1766084 3354205 := bbase (se 3 (by rfl) ⟨628913, by rfl⟩ : syracuseStep 3354205 = 1257827) (by norm_num)
theorem B2649701 : Blo 1766084 2649701 := bbase (se 4 (by rfl) ⟨248409, by rfl⟩ : syracuseStep 2649701 = 496819) (by norm_num)
theorem B3772021 : Blo 1766084 3772021 := bbase (se 5 (by rfl) ⟨176813, by rfl⟩ : syracuseStep 3772021 = 353627) (by norm_num)
theorem B8949365 : Blo 1766084 8949365 := bbase (se 5 (by rfl) ⟨419501, by rfl⟩ : syracuseStep 8949365 = 839003) (by norm_num)
theorem B2649725 : Blo 1766084 2649725 := bbase (se 3 (by rfl) ⟨496823, by rfl⟩ : syracuseStep 2649725 = 993647) (by norm_num)
theorem B3976829 : Blo 1766084 3976829 := bbase (se 3 (by rfl) ⟨745655, by rfl⟩ : syracuseStep 3976829 = 1491311) (by norm_num)
theorem B1887877 : Blo 1766084 1887877 := bbase (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) (by norm_num)
theorem B2649749 : Blo 1766084 2649749 := bbase (se 6 (by rfl) ⟨62103, by rfl⟩ : syracuseStep 2649749 = 124207) (by norm_num)
theorem B2649773 : Blo 1766084 2649773 := bbase (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) (by norm_num)
theorem B2297521 : Blo 1766084 2297521 := bbase (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) (by norm_num)
theorem B2649797 : Blo 1766084 2649797 := bbase (se 4 (by rfl) ⟨248418, by rfl⟩ : syracuseStep 2649797 = 496837) (by norm_num)
theorem B3976901 : Blo 1766084 3976901 := bbase (se 4 (by rfl) ⟨372834, by rfl⟩ : syracuseStep 3976901 = 745669) (by norm_num)
theorem B2649821 : Blo 1766084 2649821 := bbase (se 3 (by rfl) ⟨496841, by rfl⟩ : syracuseStep 2649821 = 993683) (by norm_num)
theorem B2649845 : Blo 1766084 2649845 := bbase (se 5 (by rfl) ⟨124211, by rfl⟩ : syracuseStep 2649845 = 248423) (by norm_num)
theorem B3354365 : Blo 1766084 3354365 := bbase (se 3 (by rfl) ⟨628943, by rfl⟩ : syracuseStep 3354365 = 1257887) (by norm_num)
theorem B3772165 : Blo 1766084 3772165 := bbase (se 4 (by rfl) ⟨353640, by rfl⟩ : syracuseStep 3772165 = 707281) (by norm_num)
theorem B2649869 : Blo 1766084 2649869 := bbase (se 3 (by rfl) ⟨496850, by rfl⟩ : syracuseStep 2649869 = 993701) (by norm_num)
theorem B3976973 : Blo 1766084 3976973 := bbase (se 3 (by rfl) ⟨745682, by rfl⟩ : syracuseStep 3976973 = 1491365) (by norm_num)
theorem B2649893 : Blo 1766084 2649893 := bbase (se 4 (by rfl) ⟨248427, by rfl⟩ : syracuseStep 2649893 = 496855) (by norm_num)
theorem B2649917 : Blo 1766084 2649917 := bbase (se 3 (by rfl) ⟨496859, by rfl⟩ : syracuseStep 2649917 = 993719) (by norm_num)
theorem B2649941 : Blo 1766084 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B3977045 : Blo 1766084 3977045 := bbase (se 9 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 3977045 = 23303) (by norm_num)
theorem B2649965 : Blo 1766084 2649965 := bbase (se 3 (by rfl) ⟨496868, by rfl⟩ : syracuseStep 2649965 = 993737) (by norm_num)
theorem B2649989 : Blo 1766084 2649989 := bbase (se 4 (by rfl) ⟨248436, by rfl⟩ : syracuseStep 2649989 = 496873) (by norm_num)
theorem B3354509 : Blo 1766084 3354509 := bbase (se 3 (by rfl) ⟨628970, by rfl⟩ : syracuseStep 3354509 = 1257941) (by norm_num)
theorem B2650013 : Blo 1766084 2650013 := bbase (se 3 (by rfl) ⟨496877, by rfl⟩ : syracuseStep 2650013 = 993755) (by norm_num)
theorem B3977117 : Blo 1766084 3977117 := bbase (se 3 (by rfl) ⟨745709, by rfl⟩ : syracuseStep 3977117 = 1491419) (by norm_num)
theorem B2650037 : Blo 1766084 2650037 := bbase (se 5 (by rfl) ⟨124220, by rfl⟩ : syracuseStep 2650037 = 248441) (by norm_num)
theorem B11325365 : Blo 1766084 11325365 := bbase (se 5 (by rfl) ⟨530876, by rfl⟩ : syracuseStep 11325365 = 1061753) (by norm_num)
theorem B2650061 : Blo 1766084 2650061 := bbase (se 3 (by rfl) ⟨496886, by rfl⟩ : syracuseStep 2650061 = 993773) (by norm_num)
theorem B2650085 : Blo 1766084 2650085 := bbase (se 4 (by rfl) ⟨248445, by rfl⟩ : syracuseStep 2650085 = 496891) (by norm_num)
theorem B3977189 : Blo 1766084 3977189 := bbase (se 4 (by rfl) ⟨372861, by rfl⟩ : syracuseStep 3977189 = 745723) (by norm_num)
theorem B2650109 : Blo 1766084 2650109 := bbase (se 3 (by rfl) ⟨496895, by rfl⟩ : syracuseStep 2650109 = 993791) (by norm_num)
theorem B8941589 : Blo 1766084 8941589 := bbase (se 6 (by rfl) ⟨209568, by rfl⟩ : syracuseStep 8941589 = 419137) (by norm_num)
theorem B2650133 : Blo 1766084 2650133 := bbase (se 6 (by rfl) ⟨62112, by rfl⟩ : syracuseStep 2650133 = 124225) (by norm_num)
theorem B2650157 : Blo 1766084 2650157 := bbase (se 3 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 2650157 = 993809) (by norm_num)
theorem B3977261 : Blo 1766084 3977261 := bbase (se 3 (by rfl) ⟨745736, by rfl⟩ : syracuseStep 3977261 = 1491473) (by norm_num)
theorem B2650181 : Blo 1766084 2650181 := bbase (se 4 (by rfl) ⟨248454, by rfl⟩ : syracuseStep 2650181 = 496909) (by norm_num)
theorem B2650205 : Blo 1766084 2650205 := bbase (se 3 (by rfl) ⟨496913, by rfl⟩ : syracuseStep 2650205 = 993827) (by norm_num)
theorem B12087413 : Blo 1766084 12087413 := bbase (se 5 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 12087413 = 1133195) (by norm_num)
theorem B2650229 : Blo 1766084 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B3977333 : Blo 1766084 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B3772541 : Blo 1766084 3772541 := bbase (se 3 (by rfl) ⟨707351, by rfl⟩ : syracuseStep 3772541 = 1414703) (by norm_num)
theorem B2650253 : Blo 1766084 2650253 := bbase (se 3 (by rfl) ⟨496922, by rfl⟩ : syracuseStep 2650253 = 993845) (by norm_num)
theorem B2650277 : Blo 1766084 2650277 := bbase (se 4 (by rfl) ⟨248463, by rfl⟩ : syracuseStep 2650277 = 496927) (by norm_num)
theorem B3354797 : Blo 1766084 3354797 := bbase (se 3 (by rfl) ⟨629024, by rfl⟩ : syracuseStep 3354797 = 1258049) (by norm_num)
theorem B2650301 : Blo 1766084 2650301 := bbase (se 3 (by rfl) ⟨496931, by rfl⟩ : syracuseStep 2650301 = 993863) (by norm_num)
theorem B3977405 : Blo 1766084 3977405 := bbase (se 3 (by rfl) ⟨745763, by rfl⟩ : syracuseStep 3977405 = 1491527) (by norm_num)
theorem B2650325 : Blo 1766084 2650325 := bbase (se 7 (by rfl) ⟨31058, by rfl⟩ : syracuseStep 2650325 = 62117) (by norm_num)
theorem B2650349 : Blo 1766084 2650349 := bbase (se 3 (by rfl) ⟨496940, by rfl⟩ : syracuseStep 2650349 = 993881) (by norm_num)
theorem B2650373 : Blo 1766084 2650373 := bbase (se 4 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 2650373 = 496945) (by norm_num)
theorem B3977477 : Blo 1766084 3977477 := bbase (se 4 (by rfl) ⟨372888, by rfl⟩ : syracuseStep 3977477 = 745777) (by norm_num)
theorem B2650397 : Blo 1766084 2650397 := bbase (se 3 (by rfl) ⟨496949, by rfl⟩ : syracuseStep 2650397 = 993899) (by norm_num)
theorem B1986853 : Blo 1766084 1986853 := bbase (se 4 (by rfl) ⟨186267, by rfl⟩ : syracuseStep 1986853 = 372535) (by norm_num)
theorem B2650421 : Blo 1766084 2650421 := bbase (se 5 (by rfl) ⟨124238, by rfl⟩ : syracuseStep 2650421 = 248477) (by norm_num)
theorem B3354949 : Blo 1766084 3354949 := bbase (se 4 (by rfl) ⟨314526, by rfl⟩ : syracuseStep 3354949 = 629053) (by norm_num)
theorem B1986889 : Blo 1766084 1986889 := bbase (se 2 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 1986889 = 1490167) (by norm_num)
theorem B2650445 : Blo 1766084 2650445 := bbase (se 3 (by rfl) ⟨496958, by rfl⟩ : syracuseStep 2650445 = 993917) (by norm_num)
theorem B3977549 : Blo 1766084 3977549 := bbase (se 3 (by rfl) ⟨745790, by rfl⟩ : syracuseStep 3977549 = 1491581) (by norm_num)
theorem B3584341 : Blo 1766084 3584341 := bbase (se 10 (by rfl) ⟨5250, by rfl⟩ : syracuseStep 3584341 = 10501) (by norm_num)
theorem B2650469 : Blo 1766084 2650469 := bbase (se 4 (by rfl) ⟨248481, by rfl⟩ : syracuseStep 2650469 = 496963) (by norm_num)
theorem B1986925 : Blo 1766084 1986925 := bbase (se 3 (by rfl) ⟨372548, by rfl⟩ : syracuseStep 1986925 = 745097) (by norm_num)
theorem B2650493 : Blo 1766084 2650493 := bbase (se 3 (by rfl) ⟨496967, by rfl⟩ : syracuseStep 2650493 = 993935) (by norm_num)
theorem B1986961 : Blo 1766084 1986961 := bbase (se 2 (by rfl) ⟨745110, by rfl⟩ : syracuseStep 1986961 = 1490221) (by norm_num)
theorem B1814929 : Blo 1766084 1814929 := bbase (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) (by norm_num)
theorem B2650517 : Blo 1766084 2650517 := bbase (se 6 (by rfl) ⟨62121, by rfl⟩ : syracuseStep 2650517 = 124243) (by norm_num)
theorem B3977621 : Blo 1766084 3977621 := bbase (se 6 (by rfl) ⟨93225, by rfl⟩ : syracuseStep 3977621 = 186451) (by norm_num)
theorem B2650541 : Blo 1766084 2650541 := bbase (se 3 (by rfl) ⟨496976, by rfl⟩ : syracuseStep 2650541 = 993953) (by norm_num)
theorem B1986997 : Blo 1766084 1986997 := bbase (se 5 (by rfl) ⟨93140, by rfl⟩ : syracuseStep 1986997 = 186281) (by norm_num)
theorem B2650565 : Blo 1766084 2650565 := bbase (se 4 (by rfl) ⟨248490, by rfl⟩ : syracuseStep 2650565 = 496981) (by norm_num)
theorem B1987033 : Blo 1766084 1987033 := bbase (se 2 (by rfl) ⟨745137, by rfl⟩ : syracuseStep 1987033 = 1490275) (by norm_num)
theorem B2650589 : Blo 1766084 2650589 := bbase (se 3 (by rfl) ⟨496985, by rfl⟩ : syracuseStep 2650589 = 993971) (by norm_num)
theorem B3977693 : Blo 1766084 3977693 := bbase (se 3 (by rfl) ⟨745817, by rfl⟩ : syracuseStep 3977693 = 1491635) (by norm_num)
theorem B3772909 : Blo 1766084 3772909 := bbase (se 3 (by rfl) ⟨707420, by rfl⟩ : syracuseStep 3772909 = 1414841) (by norm_num)
theorem B11473397 : Blo 1766084 11473397 := bbase (se 5 (by rfl) ⟨537815, by rfl⟩ : syracuseStep 11473397 = 1075631) (by norm_num)
theorem B2650613 : Blo 1766084 2650613 := bbase (se 5 (by rfl) ⟨124247, by rfl⟩ : syracuseStep 2650613 = 248495) (by norm_num)
theorem B1987069 : Blo 1766084 1987069 := bbase (se 3 (by rfl) ⟨372575, by rfl⟩ : syracuseStep 1987069 = 745151) (by norm_num)
theorem B2650637 : Blo 1766084 2650637 := bbase (se 3 (by rfl) ⟨496994, by rfl⟩ : syracuseStep 2650637 = 993989) (by norm_num)
theorem B16118293 : Blo 1766084 16118293 := bbase (se 6 (by rfl) ⟨377772, by rfl⟩ : syracuseStep 16118293 = 755545) (by norm_num)
theorem B1987105 : Blo 1766084 1987105 := bbase (se 2 (by rfl) ⟨745164, by rfl⟩ : syracuseStep 1987105 = 1490329) (by norm_num)
theorem B2650661 : Blo 1766084 2650661 := bbase (se 4 (by rfl) ⟨248499, by rfl⟩ : syracuseStep 2650661 = 496999) (by norm_num)
theorem B3977765 : Blo 1766084 3977765 := bbase (se 4 (by rfl) ⟨372915, by rfl⟩ : syracuseStep 3977765 = 745831) (by norm_num)
theorem B2650685 : Blo 1766084 2650685 := bbase (se 3 (by rfl) ⟨497003, by rfl⟩ : syracuseStep 2650685 = 994007) (by norm_num)
theorem B1987141 : Blo 1766084 1987141 := bbase (se 4 (by rfl) ⟨186294, by rfl⟩ : syracuseStep 1987141 = 372589) (by norm_num)
theorem B5034565 : Blo 1766084 5034565 := bbase (se 4 (by rfl) ⟨471990, by rfl⟩ : syracuseStep 5034565 = 943981) (by norm_num)
theorem B2650709 : Blo 1766084 2650709 := bbase (se 8 (by rfl) ⟨15531, by rfl⟩ : syracuseStep 2650709 = 31063) (by norm_num)
theorem B1987177 : Blo 1766084 1987177 := bbase (se 2 (by rfl) ⟨745191, by rfl⟩ : syracuseStep 1987177 = 1490383) (by norm_num)
theorem B2650733 : Blo 1766084 2650733 := bbase (se 3 (by rfl) ⟨497012, by rfl⟩ : syracuseStep 2650733 = 994025) (by norm_num)
theorem B3977837 : Blo 1766084 3977837 := bbase (se 3 (by rfl) ⟨745844, by rfl⟩ : syracuseStep 3977837 = 1491689) (by norm_num)
theorem B3355253 : Blo 1766084 3355253 := bbase (se 5 (by rfl) ⟨157277, by rfl⟩ : syracuseStep 3355253 = 314555) (by norm_num)
theorem B2650757 : Blo 1766084 2650757 := bbase (se 4 (by rfl) ⟨248508, by rfl⟩ : syracuseStep 2650757 = 497017) (by norm_num)
theorem B1987213 : Blo 1766084 1987213 := bbase (se 3 (by rfl) ⟨372602, by rfl⟩ : syracuseStep 1987213 = 745205) (by norm_num)
theorem B2650781 : Blo 1766084 2650781 := bbase (se 3 (by rfl) ⟨497021, by rfl⟩ : syracuseStep 2650781 = 994043) (by norm_num)
theorem B2831021 : Blo 1766084 2831021 := bbase (se 3 (by rfl) ⟨530816, by rfl⟩ : syracuseStep 2831021 = 1061633) (by norm_num)
theorem B1987249 : Blo 1766084 1987249 := bbase (se 2 (by rfl) ⟨745218, by rfl⟩ : syracuseStep 1987249 = 1490437) (by norm_num)
theorem B2650805 : Blo 1766084 2650805 := bbase (se 5 (by rfl) ⟨124256, by rfl⟩ : syracuseStep 2650805 = 248513) (by norm_num)
theorem B3977909 : Blo 1766084 3977909 := bbase (se 5 (by rfl) ⟨186464, by rfl⟩ : syracuseStep 3977909 = 372929) (by norm_num)
theorem B2650829 : Blo 1766084 2650829 := bbase (se 3 (by rfl) ⟨497030, by rfl⟩ : syracuseStep 2650829 = 994061) (by norm_num)
theorem B1987285 : Blo 1766084 1987285 := bbase (se 7 (by rfl) ⟨23288, by rfl⟩ : syracuseStep 1987285 = 46577) (by norm_num)
theorem B2650853 : Blo 1766084 2650853 := bbase (se 4 (by rfl) ⟨248517, by rfl⟩ : syracuseStep 2650853 = 497035) (by norm_num)
theorem B3183341 : Blo 1766084 3183341 := bbase (se 3 (by rfl) ⟨596876, by rfl⟩ : syracuseStep 3183341 = 1193753) (by norm_num)
theorem B1987321 : Blo 1766084 1987321 := bbase (se 2 (by rfl) ⟨745245, by rfl⟩ : syracuseStep 1987321 = 1490491) (by norm_num)
theorem B2650877 : Blo 1766084 2650877 := bbase (se 3 (by rfl) ⟨497039, by rfl⟩ : syracuseStep 2650877 = 994079) (by norm_num)
theorem B3977981 : Blo 1766084 3977981 := bbase (se 3 (by rfl) ⟨745871, by rfl⟩ : syracuseStep 3977981 = 1491743) (by norm_num)
theorem B2831117 : Blo 1766084 2831117 := bbase (se 3 (by rfl) ⟨530834, by rfl⟩ : syracuseStep 2831117 = 1061669) (by norm_num)
theorem B2650901 : Blo 1766084 2650901 := bbase (se 6 (by rfl) ⟨62130, by rfl⟩ : syracuseStep 2650901 = 124261) (by norm_num)
theorem B1987357 : Blo 1766084 1987357 := bbase (se 3 (by rfl) ⟨372629, by rfl⟩ : syracuseStep 1987357 = 745259) (by norm_num)
theorem B2650925 : Blo 1766084 2650925 := bbase (se 3 (by rfl) ⟨497048, by rfl⟩ : syracuseStep 2650925 = 994097) (by norm_num)
theorem B2831149 : Blo 1766084 2831149 := bbase (se 3 (by rfl) ⟨530840, by rfl⟩ : syracuseStep 2831149 = 1061681) (by norm_num)
theorem B8172341 : Blo 1766084 8172341 := bbase (se 5 (by rfl) ⟨383078, by rfl⟩ : syracuseStep 8172341 = 766157) (by norm_num)
theorem B1987393 : Blo 1766084 1987393 := bbase (se 2 (by rfl) ⟨745272, by rfl⟩ : syracuseStep 1987393 = 1490545) (by norm_num)
theorem B2650949 : Blo 1766084 2650949 := bbase (se 4 (by rfl) ⟨248526, by rfl⟩ : syracuseStep 2650949 = 497053) (by norm_num)
theorem B3978053 : Blo 1766084 3978053 := bbase (se 4 (by rfl) ⟨372942, by rfl⟩ : syracuseStep 3978053 = 745885) (by norm_num)
theorem B2650973 : Blo 1766084 2650973 := bbase (se 3 (by rfl) ⟨497057, by rfl⟩ : syracuseStep 2650973 = 994115) (by norm_num)
theorem B1987429 : Blo 1766084 1987429 := bbase (se 4 (by rfl) ⟨186321, by rfl⟩ : syracuseStep 1987429 = 372643) (by norm_num)
theorem B1790833 : Blo 1766084 1790833 := bbase (se 2 (by rfl) ⟨671562, by rfl⟩ : syracuseStep 1790833 = 1343125) (by norm_num)
theorem B2650997 : Blo 1766084 2650997 := bbase (se 5 (by rfl) ⟨124265, by rfl⟩ : syracuseStep 2650997 = 248531) (by norm_num)
theorem B8950661 : Blo 1766084 8950661 := bbase (se 4 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 8950661 = 1678249) (by norm_num)
theorem B1987465 : Blo 1766084 1987465 := bbase (se 2 (by rfl) ⟨745299, by rfl⟩ : syracuseStep 1987465 = 1490599) (by norm_num)
theorem B2651021 : Blo 1766084 2651021 := bbase (se 3 (by rfl) ⟨497066, by rfl⟩ : syracuseStep 2651021 = 994133) (by norm_num)
theorem B3978125 : Blo 1766084 3978125 := bbase (se 3 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 3978125 = 1491797) (by norm_num)
theorem B22942613 : Blo 1766084 22942613 := bbase (se 6 (by rfl) ⟨537717, by rfl⟩ : syracuseStep 22942613 = 1075435) (by norm_num)
theorem B2651045 : Blo 1766084 2651045 := bbase (se 4 (by rfl) ⟨248535, by rfl⟩ : syracuseStep 2651045 = 497071) (by norm_num)
theorem B1987501 : Blo 1766084 1987501 := bbase (se 3 (by rfl) ⟨372656, by rfl⟩ : syracuseStep 1987501 = 745313) (by norm_num)
theorem B2651069 : Blo 1766084 2651069 := bbase (se 3 (by rfl) ⟨497075, by rfl⟩ : syracuseStep 2651069 = 994151) (by norm_num)
theorem B2266061 : Blo 1766084 2266061 := bbase (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) (by norm_num)
theorem B1987537 : Blo 1766084 1987537 := bbase (se 2 (by rfl) ⟨745326, by rfl⟩ : syracuseStep 1987537 = 1490653) (by norm_num)
theorem B2651093 : Blo 1766084 2651093 := bbase (se 7 (by rfl) ⟨31067, by rfl⟩ : syracuseStep 2651093 = 62135) (by norm_num)
theorem B2651117 : Blo 1766084 2651117 := bbase (se 3 (by rfl) ⟨497084, by rfl⟩ : syracuseStep 2651117 = 994169) (by norm_num)
theorem B1987573 : Blo 1766084 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B2651141 : Blo 1766084 2651141 := bbase (se 4 (by rfl) ⟨248544, by rfl⟩ : syracuseStep 2651141 = 497089) (by norm_num)
theorem B1987609 : Blo 1766084 1987609 := bbase (se 2 (by rfl) ⟨745353, by rfl⟩ : syracuseStep 1987609 = 1490707) (by norm_num)
theorem B2651165 : Blo 1766084 2651165 := bbase (se 3 (by rfl) ⟨497093, by rfl⟩ : syracuseStep 2651165 = 994187) (by norm_num)
theorem B2651189 : Blo 1766084 2651189 := bbase (se 5 (by rfl) ⟨124274, by rfl⟩ : syracuseStep 2651189 = 248549) (by norm_num)
theorem B1987645 : Blo 1766084 1987645 := bbase (se 3 (by rfl) ⟨372683, by rfl⟩ : syracuseStep 1987645 = 745367) (by norm_num)
theorem B6370373 : Blo 1766084 6370373 := bbase (se 4 (by rfl) ⟨597222, by rfl⟩ : syracuseStep 6370373 = 1194445) (by norm_num)
theorem B2651213 : Blo 1766084 2651213 := bbase (se 3 (by rfl) ⟨497102, by rfl⟩ : syracuseStep 2651213 = 994205) (by norm_num)
theorem B5960789 : Blo 1766084 5960789 := bbase (se 8 (by rfl) ⟨34926, by rfl⟩ : syracuseStep 5960789 = 69853) (by norm_num)
theorem B1987681 : Blo 1766084 1987681 := bbase (se 2 (by rfl) ⟨745380, by rfl⟩ : syracuseStep 1987681 = 1490761) (by norm_num)
theorem B2651237 : Blo 1766084 2651237 := bbase (se 4 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 2651237 = 497107) (by norm_num)
theorem B2651261 : Blo 1766084 2651261 := bbase (se 3 (by rfl) ⟨497111, by rfl⟩ : syracuseStep 2651261 = 994223) (by norm_num)
theorem B1987717 : Blo 1766084 1987717 := bbase (se 4 (by rfl) ⟨186348, by rfl⟩ : syracuseStep 1987717 = 372697) (by norm_num)
theorem B2651285 : Blo 1766084 2651285 := bbase (se 6 (by rfl) ⟨62139, by rfl⟩ : syracuseStep 2651285 = 124279) (by norm_num)
theorem B1987753 : Blo 1766084 1987753 := bbase (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) (by norm_num)
theorem B2651309 : Blo 1766084 2651309 := bbase (se 3 (by rfl) ⟨497120, by rfl⟩ : syracuseStep 2651309 = 994241) (by norm_num)
theorem B2651333 : Blo 1766084 2651333 := bbase (se 4 (by rfl) ⟨248562, by rfl⟩ : syracuseStep 2651333 = 497125) (by norm_num)
theorem B1987789 : Blo 1766084 1987789 := bbase (se 3 (by rfl) ⟨372710, by rfl⟩ : syracuseStep 1987789 = 745421) (by norm_num)
theorem B2651357 : Blo 1766084 2651357 := bbase (se 3 (by rfl) ⟨497129, by rfl⟩ : syracuseStep 2651357 = 994259) (by norm_num)
theorem B1987825 : Blo 1766084 1987825 := bbase (se 2 (by rfl) ⟨745434, by rfl⟩ : syracuseStep 1987825 = 1490869) (by norm_num)
theorem B6706421 : Blo 1766084 6706421 := bbase (se 5 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 6706421 = 628727) (by norm_num)
theorem B2651381 : Blo 1766084 2651381 := bbase (se 5 (by rfl) ⟨124283, by rfl⟩ : syracuseStep 2651381 = 248567) (by norm_num)
theorem B2651405 : Blo 1766084 2651405 := bbase (se 3 (by rfl) ⟨497138, by rfl⟩ : syracuseStep 2651405 = 994277) (by norm_num)
theorem B1987861 : Blo 1766084 1987861 := bbase (se 6 (by rfl) ⟨46590, by rfl⟩ : syracuseStep 1987861 = 93181) (by norm_num)
theorem B8942885 : Blo 1766084 8942885 := bbase (se 4 (by rfl) ⟨838395, by rfl⟩ : syracuseStep 8942885 = 1676791) (by norm_num)
theorem B2651429 : Blo 1766084 2651429 := bbase (se 4 (by rfl) ⟨248571, by rfl⟩ : syracuseStep 2651429 = 497143) (by norm_num)
theorem B1987897 : Blo 1766084 1987897 := bbase (se 2 (by rfl) ⟨745461, by rfl⟩ : syracuseStep 1987897 = 1490923) (by norm_num)
theorem B2651453 : Blo 1766084 2651453 := bbase (se 3 (by rfl) ⟨497147, by rfl⟩ : syracuseStep 2651453 = 994295) (by norm_num)
theorem B2651477 : Blo 1766084 2651477 := bbase (se 13 (by rfl) ⟨485, by rfl⟩ : syracuseStep 2651477 = 971) (by norm_num)
theorem B1987933 : Blo 1766084 1987933 := bbase (se 3 (by rfl) ⟨372737, by rfl⟩ : syracuseStep 1987933 = 745475) (by norm_num)
theorem B3356005 : Blo 1766084 3356005 := bbase (se 4 (by rfl) ⟨314625, by rfl⟩ : syracuseStep 3356005 = 629251) (by norm_num)
theorem B2651501 : Blo 1766084 2651501 := bbase (se 3 (by rfl) ⟨497156, by rfl⟩ : syracuseStep 2651501 = 994313) (by norm_num)
theorem B1987969 : Blo 1766084 1987969 := bbase (se 2 (by rfl) ⟨745488, by rfl⟩ : syracuseStep 1987969 = 1490977) (by norm_num)
theorem B2651525 : Blo 1766084 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B2487709 : Blo 1766084 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B2651549 : Blo 1766084 2651549 := bbase (se 3 (by rfl) ⟨497165, by rfl⟩ : syracuseStep 2651549 = 994331) (by norm_num)
theorem B1988005 : Blo 1766084 1988005 := bbase (se 4 (by rfl) ⟨186375, by rfl⟩ : syracuseStep 1988005 = 372751) (by norm_num)
theorem B2651573 : Blo 1766084 2651573 := bbase (se 5 (by rfl) ⟨124292, by rfl⟩ : syracuseStep 2651573 = 248585) (by norm_num)
theorem B1988041 : Blo 1766084 1988041 := bbase (se 2 (by rfl) ⟨745515, by rfl⟩ : syracuseStep 1988041 = 1491031) (by norm_num)
theorem B2651597 : Blo 1766084 2651597 := bbase (se 3 (by rfl) ⟨497174, by rfl⟩ : syracuseStep 2651597 = 994349) (by norm_num)
theorem B3184085 : Blo 1766084 3184085 := bbase (se 7 (by rfl) ⟨37313, by rfl⟩ : syracuseStep 3184085 = 74627) (by norm_num)
theorem B2651621 : Blo 1766084 2651621 := bbase (se 4 (by rfl) ⟨248589, by rfl⟩ : syracuseStep 2651621 = 497179) (by norm_num)
theorem B1988077 : Blo 1766084 1988077 := bbase (se 3 (by rfl) ⟨372764, by rfl⟩ : syracuseStep 1988077 = 745529) (by norm_num)
theorem B3356149 : Blo 1766084 3356149 := bbase (se 5 (by rfl) ⟨157319, by rfl⟩ : syracuseStep 3356149 = 314639) (by norm_num)
theorem B2651645 : Blo 1766084 2651645 := bbase (se 3 (by rfl) ⟨497183, by rfl⟩ : syracuseStep 2651645 = 994367) (by norm_num)
theorem B5961221 : Blo 1766084 5961221 := bbase (se 4 (by rfl) ⟨558864, by rfl⟩ : syracuseStep 5961221 = 1117729) (by norm_num)
theorem B1988113 : Blo 1766084 1988113 := bbase (se 2 (by rfl) ⟨745542, by rfl⟩ : syracuseStep 1988113 = 1491085) (by norm_num)
theorem B6706709 : Blo 1766084 6706709 := bbase (se 6 (by rfl) ⟨157188, by rfl⟩ : syracuseStep 6706709 = 314377) (by norm_num)
theorem B2651669 : Blo 1766084 2651669 := bbase (se 6 (by rfl) ⟨62148, by rfl⟩ : syracuseStep 2651669 = 124297) (by norm_num)
theorem B2651693 : Blo 1766084 2651693 := bbase (se 3 (by rfl) ⟨497192, by rfl⟩ : syracuseStep 2651693 = 994385) (by norm_num)
theorem B1988149 : Blo 1766084 1988149 := bbase (se 5 (by rfl) ⟨93194, by rfl⟩ : syracuseStep 1988149 = 186389) (by norm_num)
theorem B2651717 : Blo 1766084 2651717 := bbase (se 4 (by rfl) ⟨248598, by rfl⟩ : syracuseStep 2651717 = 497197) (by norm_num)
theorem B1988185 : Blo 1766084 1988185 := bbase (se 2 (by rfl) ⟨745569, by rfl⟩ : syracuseStep 1988185 = 1491139) (by norm_num)
theorem B2651741 : Blo 1766084 2651741 := bbase (se 3 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 2651741 = 994403) (by norm_num)
theorem B2651765 : Blo 1766084 2651765 := bbase (se 5 (by rfl) ⟨124301, by rfl⟩ : syracuseStep 2651765 = 248603) (by norm_num)
theorem B1988221 : Blo 1766084 1988221 := bbase (se 3 (by rfl) ⟨372791, by rfl⟩ : syracuseStep 1988221 = 745583) (by norm_num)
theorem B3446405 : Blo 1766084 3446405 := bbase (se 4 (by rfl) ⟨323100, by rfl⟩ : syracuseStep 3446405 = 646201) (by norm_num)
theorem B2651789 : Blo 1766084 2651789 := bbase (se 3 (by rfl) ⟨497210, by rfl⟩ : syracuseStep 2651789 = 994421) (by norm_num)
theorem B3356309 : Blo 1766084 3356309 := bbase (se 6 (by rfl) ⟨78663, by rfl⟩ : syracuseStep 3356309 = 157327) (by norm_num)
theorem B1988257 : Blo 1766084 1988257 := bbase (se 2 (by rfl) ⟨745596, by rfl⟩ : syracuseStep 1988257 = 1491193) (by norm_num)
theorem B2651813 : Blo 1766084 2651813 := bbase (se 4 (by rfl) ⟨248607, by rfl⟩ : syracuseStep 2651813 = 497215) (by norm_num)
theorem B4470461 : Blo 1766084 4470461 := bbase (se 3 (by rfl) ⟨838211, by rfl⟩ : syracuseStep 4470461 = 1676423) (by norm_num)
theorem B2651837 : Blo 1766084 2651837 := bbase (se 3 (by rfl) ⟨497219, by rfl⟩ : syracuseStep 2651837 = 994439) (by norm_num)
theorem B1988293 : Blo 1766084 1988293 := bbase (se 4 (by rfl) ⟨186402, by rfl⟩ : syracuseStep 1988293 = 372805) (by norm_num)
theorem B2651861 : Blo 1766084 2651861 := bbase (se 7 (by rfl) ⟨31076, by rfl⟩ : syracuseStep 2651861 = 62153) (by norm_num)
theorem B1988329 : Blo 1766084 1988329 := bbase (se 2 (by rfl) ⟨745623, by rfl⟩ : syracuseStep 1988329 = 1491247) (by norm_num)
theorem B2651885 : Blo 1766084 2651885 := bbase (se 3 (by rfl) ⟨497228, by rfl⟩ : syracuseStep 2651885 = 994457) (by norm_num)
theorem B2651909 : Blo 1766084 2651909 := bbase (se 4 (by rfl) ⟨248616, by rfl⟩ : syracuseStep 2651909 = 497233) (by norm_num)
theorem B1988365 : Blo 1766084 1988365 := bbase (se 3 (by rfl) ⟨372818, by rfl⟩ : syracuseStep 1988365 = 745637) (by norm_num)
theorem B33969941 : Blo 1766084 33969941 := bbase (se 6 (by rfl) ⟨796170, by rfl⟩ : syracuseStep 33969941 = 1592341) (by norm_num)
theorem B2651933 : Blo 1766084 2651933 := bbase (se 3 (by rfl) ⟨497237, by rfl⟩ : syracuseStep 2651933 = 994475) (by norm_num)
theorem B1791781 : Blo 1766084 1791781 := bbase (se 4 (by rfl) ⟨167979, by rfl⟩ : syracuseStep 1791781 = 335959) (by norm_num)
theorem B3356453 : Blo 1766084 3356453 := bbase (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) (by norm_num)
theorem B1988401 : Blo 1766084 1988401 := bbase (se 2 (by rfl) ⟨745650, by rfl⟩ : syracuseStep 1988401 = 1491301) (by norm_num)
theorem B2651957 : Blo 1766084 2651957 := bbase (se 5 (by rfl) ⟨124310, by rfl⟩ : syracuseStep 2651957 = 248621) (by norm_num)
theorem B2651981 : Blo 1766084 2651981 := bbase (se 3 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 2651981 = 994493) (by norm_num)
theorem B1988437 : Blo 1766084 1988437 := bbase (se 9 (by rfl) ⟨5825, by rfl⟩ : syracuseStep 1988437 = 11651) (by norm_num)
theorem B2652005 : Blo 1766084 2652005 := bbase (se 4 (by rfl) ⟨248625, by rfl⟩ : syracuseStep 2652005 = 497251) (by norm_num)
theorem B1988473 : Blo 1766084 1988473 := bbase (se 2 (by rfl) ⟨745677, by rfl⟩ : syracuseStep 1988473 = 1491355) (by norm_num)
theorem B4470653 : Blo 1766084 4470653 := bbase (se 3 (by rfl) ⟨838247, by rfl⟩ : syracuseStep 4470653 = 1676495) (by norm_num)
theorem B2652029 : Blo 1766084 2652029 := bbase (se 3 (by rfl) ⟨497255, by rfl⟩ : syracuseStep 2652029 = 994511) (by norm_num)
theorem B2652053 : Blo 1766084 2652053 := bbase (se 6 (by rfl) ⟨62157, by rfl⟩ : syracuseStep 2652053 = 124315) (by norm_num)
theorem B1988509 : Blo 1766084 1988509 := bbase (se 3 (by rfl) ⟨372845, by rfl⟩ : syracuseStep 1988509 = 745691) (by norm_num)
theorem B2652077 : Blo 1766084 2652077 := bbase (se 3 (by rfl) ⟨497264, by rfl⟩ : syracuseStep 2652077 = 994529) (by norm_num)
theorem B5961653 : Blo 1766084 5961653 := bbase (se 5 (by rfl) ⟨279452, by rfl⟩ : syracuseStep 5961653 = 558905) (by norm_num)
theorem B1988545 : Blo 1766084 1988545 := bbase (se 2 (by rfl) ⟨745704, by rfl⟩ : syracuseStep 1988545 = 1491409) (by norm_num)
theorem B2652101 : Blo 1766084 2652101 := bbase (se 4 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 2652101 = 497269) (by norm_num)
theorem B3774413 : Blo 1766084 3774413 := bbase (se 3 (by rfl) ⟨707702, by rfl⟩ : syracuseStep 3774413 = 1415405) (by norm_num)
theorem B2652125 : Blo 1766084 2652125 := bbase (se 3 (by rfl) ⟨497273, by rfl⟩ : syracuseStep 2652125 = 994547) (by norm_num)
theorem B1988581 : Blo 1766084 1988581 := bbase (se 4 (by rfl) ⟨186429, by rfl⟩ : syracuseStep 1988581 = 372859) (by norm_num)
theorem B1988617 : Blo 1766084 1988617 := bbase (se 2 (by rfl) ⟨745731, by rfl⟩ : syracuseStep 1988617 = 1491463) (by norm_num)
theorem B21493781 : Blo 1766084 21493781 := bbase (se 6 (by rfl) ⟨503760, by rfl⟩ : syracuseStep 21493781 = 1007521) (by norm_num)
theorem B10065941 : Blo 1766084 10065941 := bbase (se 6 (by rfl) ⟨235920, by rfl⟩ : syracuseStep 10065941 = 471841) (by norm_num)
theorem B1988653 : Blo 1766084 1988653 := bbase (se 3 (by rfl) ⟨372872, by rfl⟩ : syracuseStep 1988653 = 745745) (by norm_num)
theorem B1988689 : Blo 1766084 1988689 := bbase (se 2 (by rfl) ⟨745758, by rfl⟩ : syracuseStep 1988689 = 1491517) (by norm_num)
theorem B22632533 : Blo 1766084 22632533 := bbase (se 8 (by rfl) ⟨132612, by rfl⟩ : syracuseStep 22632533 = 265225) (by norm_num)
theorem B20396117 : Blo 1766084 20396117 := bbase (se 8 (by rfl) ⟨119508, by rfl⟩ : syracuseStep 20396117 = 239017) (by norm_num)
theorem B3774557 : Blo 1766084 3774557 := bbase (se 3 (by rfl) ⟨707729, by rfl⟩ : syracuseStep 3774557 = 1415459) (by norm_num)
theorem B5740645 : Blo 1766084 5740645 := bbase (se 4 (by rfl) ⟨538185, by rfl⟩ : syracuseStep 5740645 = 1076371) (by norm_num)
theorem B1988725 : Blo 1766084 1988725 := bbase (se 5 (by rfl) ⟨93221, by rfl⟩ : syracuseStep 1988725 = 186443) (by norm_num)
theorem B1988761 : Blo 1766084 1988761 := bbase (se 2 (by rfl) ⟨745785, by rfl⟩ : syracuseStep 1988761 = 1491571) (by norm_num)
theorem B1988797 : Blo 1766084 1988797 := bbase (se 3 (by rfl) ⟨372899, by rfl⟩ : syracuseStep 1988797 = 745799) (by norm_num)
theorem B4470997 : Blo 1766084 4470997 := bbase (se 7 (by rfl) ⟨52394, by rfl⟩ : syracuseStep 4470997 = 104789) (by norm_num)
theorem B1988833 : Blo 1766084 1988833 := bbase (se 2 (by rfl) ⟨745812, by rfl⟩ : syracuseStep 1988833 = 1491625) (by norm_num)
theorem B1988869 : Blo 1766084 1988869 := bbase (se 4 (by rfl) ⟨186456, by rfl⟩ : syracuseStep 1988869 = 372913) (by norm_num)
theorem B1988905 : Blo 1766084 1988905 := bbase (se 2 (by rfl) ⟨745839, by rfl⟩ : syracuseStep 1988905 = 1491679) (by norm_num)
theorem B4471109 : Blo 1766084 4471109 := bbase (se 4 (by rfl) ⟨419166, by rfl⟩ : syracuseStep 4471109 = 838333) (by norm_num)
theorem B7551301 : Blo 1766084 7551301 := bbase (se 4 (by rfl) ⟨707934, by rfl⟩ : syracuseStep 7551301 = 1415869) (by norm_num)
theorem B1988941 : Blo 1766084 1988941 := bbase (se 3 (by rfl) ⟨372926, by rfl⟩ : syracuseStep 1988941 = 745853) (by norm_num)
theorem B5962085 : Blo 1766084 5962085 := bbase (se 4 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 5962085 = 1117891) (by norm_num)
theorem B1988977 : Blo 1766084 1988977 := bbase (se 2 (by rfl) ⟨745866, by rfl⟩ : syracuseStep 1988977 = 1491733) (by norm_num)
theorem B7649653 : Blo 1766084 7649653 := bbase (se 5 (by rfl) ⟨358577, by rfl⟩ : syracuseStep 7649653 = 717155) (by norm_num)
theorem B2685325 : Blo 1766084 2685325 := bbase (se 3 (by rfl) ⟨503498, by rfl⟩ : syracuseStep 2685325 = 1006997) (by norm_num)
theorem B18127253 : Blo 1766084 18127253 := bbase (se 6 (by rfl) ⟨424857, by rfl⟩ : syracuseStep 18127253 = 849715) (by norm_num)
theorem B1989013 : Blo 1766084 1989013 := bbase (se 6 (by rfl) ⟨46617, by rfl⟩ : syracuseStep 1989013 = 93235) (by norm_num)
theorem B1989049 : Blo 1766084 1989049 := bbase (se 2 (by rfl) ⟨745893, by rfl⟩ : syracuseStep 1989049 = 1491787) (by norm_num)
theorem B3774917 : Blo 1766084 3774917 := bbase (se 4 (by rfl) ⟨353898, by rfl⟩ : syracuseStep 3774917 = 707797) (by norm_num)
theorem B1989085 : Blo 1766084 1989085 := bbase (se 3 (by rfl) ⟨372953, by rfl⟩ : syracuseStep 1989085 = 745907) (by norm_num)
theorem B4471301 : Blo 1766084 4471301 := bbase (se 4 (by rfl) ⟨419184, by rfl⟩ : syracuseStep 4471301 = 838369) (by norm_num)
theorem B2980381 : Blo 1766084 2980381 := bbase (se 3 (by rfl) ⟨558821, by rfl⟩ : syracuseStep 2980381 = 1117643) (by norm_num)
theorem B8944181 : Blo 1766084 8944181 := bbase (se 5 (by rfl) ⟨419258, by rfl⟩ : syracuseStep 8944181 = 838517) (by norm_num)
theorem B2980469 : Blo 1766084 2980469 := bbase (se 5 (by rfl) ⟨139709, by rfl⟩ : syracuseStep 2980469 = 279419) (by norm_num)
theorem B6707893 : Blo 1766084 6707893 := bbase (se 5 (by rfl) ⟨314432, by rfl⟩ : syracuseStep 6707893 = 628865) (by norm_num)
theorem B2685653 : Blo 1766084 2685653 := bbase (se 7 (by rfl) ⟨31472, by rfl⟩ : syracuseStep 2685653 = 62945) (by norm_num)
theorem B2980597 : Blo 1766084 2980597 := bbase (se 5 (by rfl) ⟨139715, by rfl⟩ : syracuseStep 2980597 = 279431) (by norm_num)
theorem B5962517 : Blo 1766084 5962517 := bbase (se 6 (by rfl) ⟨139746, by rfl⟩ : syracuseStep 5962517 = 279493) (by norm_num)
theorem B2235205 : Blo 1766084 2235205 := bbase (se 4 (by rfl) ⟨209550, by rfl⟩ : syracuseStep 2235205 = 419101) (by norm_num)
theorem B2980685 : Blo 1766084 2980685 := bbase (se 3 (by rfl) ⟨558878, by rfl⟩ : syracuseStep 2980685 = 1117757) (by norm_num)
theorem B61193045 : Blo 1766084 61193045 := bbase (se 9 (by rfl) ⟨179276, by rfl⟩ : syracuseStep 61193045 = 358553) (by norm_num)
theorem B8059733 : Blo 1766084 8059733 := bbase (se 9 (by rfl) ⟨23612, by rfl⟩ : syracuseStep 8059733 = 47225) (by norm_num)
theorem B4471645 : Blo 1766084 4471645 := bbase (se 3 (by rfl) ⟨838433, by rfl⟩ : syracuseStep 4471645 = 1676867) (by norm_num)
theorem B6454117 : Blo 1766084 6454117 := bbase (se 4 (by rfl) ⟨605073, by rfl⟩ : syracuseStep 6454117 = 1210147) (by norm_num)
theorem B15096725 : Blo 1766084 15096725 := bbase (se 6 (by rfl) ⟨353829, by rfl⟩ : syracuseStep 15096725 = 707659) (by norm_num)
theorem B3185605 : Blo 1766084 3185605 := bbase (se 4 (by rfl) ⟨298650, by rfl⟩ : syracuseStep 3185605 = 597301) (by norm_num)
theorem B2980813 : Blo 1766084 2980813 := bbase (se 3 (by rfl) ⟨558902, by rfl⟩ : syracuseStep 2980813 = 1117805) (by norm_num)
theorem B4471757 : Blo 1766084 4471757 := bbase (se 3 (by rfl) ⟨838454, by rfl⟩ : syracuseStep 4471757 = 1676909) (by norm_num)
theorem B6708197 : Blo 1766084 6708197 := bbase (se 4 (by rfl) ⟨628893, by rfl⟩ : syracuseStep 6708197 = 1257787) (by norm_num)
theorem B2235377 : Blo 1766084 2235377 := bbase (se 2 (by rfl) ⟨838266, by rfl⟩ : syracuseStep 2235377 = 1676533) (by norm_num)
theorem B14334965 : Blo 1766084 14334965 := bbase (se 5 (by rfl) ⟨671951, by rfl⟩ : syracuseStep 14334965 = 1343903) (by norm_num)
theorem B2980901 : Blo 1766084 2980901 := bbase (se 4 (by rfl) ⟨279459, by rfl⟩ : syracuseStep 2980901 = 558919) (by norm_num)
theorem B2235433 : Blo 1766084 2235433 := bbase (se 2 (by rfl) ⟨838287, by rfl⟩ : syracuseStep 2235433 = 1676575) (by norm_num)
theorem B13425749 : Blo 1766084 13425749 := bbase (se 8 (by rfl) ⟨78666, by rfl⟩ : syracuseStep 13425749 = 157333) (by norm_num)
theorem B2235529 : Blo 1766084 2235529 := bbase (se 2 (by rfl) ⟨838323, by rfl⟩ : syracuseStep 2235529 = 1676647) (by norm_num)
theorem B2014345 : Blo 1766084 2014345 := bbase (se 2 (by rfl) ⟨755379, by rfl⟩ : syracuseStep 2014345 = 1510759) (by norm_num)
theorem B2014349 : Blo 1766084 2014349 := bbase (se 3 (by rfl) ⟨377690, by rfl⟩ : syracuseStep 2014349 = 755381) (by norm_num)
theorem B4471949 : Blo 1766084 4471949 := bbase (se 3 (by rfl) ⟨838490, by rfl⟩ : syracuseStep 4471949 = 1676981) (by norm_num)
theorem B3185821 : Blo 1766084 3185821 := bbase (se 3 (by rfl) ⟨597341, by rfl⟩ : syracuseStep 3185821 = 1194683) (by norm_num)
theorem B2981029 : Blo 1766084 2981029 := bbase (se 4 (by rfl) ⟨279471, by rfl⟩ : syracuseStep 2981029 = 558943) (by norm_num)
theorem B10067125 : Blo 1766084 10067125 := bbase (se 5 (by rfl) ⟨471896, by rfl⟩ : syracuseStep 10067125 = 943793) (by norm_num)
theorem B5962949 : Blo 1766084 5962949 := bbase (se 4 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 5962949 = 1118053) (by norm_num)
theorem B2981117 : Blo 1766084 2981117 := bbase (se 3 (by rfl) ⟨558959, by rfl⟩ : syracuseStep 2981117 = 1117919) (by norm_num)
theorem B2686213 : Blo 1766084 2686213 := bbase (se 4 (by rfl) ⟨251832, by rfl⟩ : syracuseStep 2686213 = 503665) (by norm_num)
theorem B2235701 : Blo 1766084 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B3775805 : Blo 1766084 3775805 := bbase (se 3 (by rfl) ⟨707963, by rfl⟩ : syracuseStep 3775805 = 1415927) (by norm_num)
theorem B2235757 : Blo 1766084 2235757 := bbase (se 3 (by rfl) ⟨419204, by rfl⟩ : syracuseStep 2235757 = 838409) (by norm_num)
theorem B2981245 : Blo 1766084 2981245 := bbase (se 3 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 2981245 = 1117967) (by norm_num)
theorem B3186109 : Blo 1766084 3186109 := bbase (se 3 (by rfl) ⟨597395, by rfl⟩ : syracuseStep 3186109 = 1194791) (by norm_num)
theorem B2235853 : Blo 1766084 2235853 := bbase (se 3 (by rfl) ⟨419222, by rfl⟩ : syracuseStep 2235853 = 838445) (by norm_num)
theorem B2981333 : Blo 1766084 2981333 := bbase (se 7 (by rfl) ⟨34937, by rfl⟩ : syracuseStep 2981333 = 69875) (by norm_num)
theorem B4472293 : Blo 1766084 4472293 := bbase (se 4 (by rfl) ⟨419277, by rfl⟩ : syracuseStep 4472293 = 838555) (by norm_num)
theorem B13417973 : Blo 1766084 13417973 := bbase (se 5 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 13417973 = 1257935) (by norm_num)
theorem B9068021 : Blo 1766084 9068021 := bbase (se 5 (by rfl) ⟨425063, by rfl⟩ : syracuseStep 9068021 = 850127) (by norm_num)
theorem B3776053 : Blo 1766084 3776053 := bbase (se 5 (by rfl) ⟨177002, by rfl⟩ : syracuseStep 3776053 = 354005) (by norm_num)
theorem B2981461 : Blo 1766084 2981461 := bbase (se 8 (by rfl) ⟨17469, by rfl⟩ : syracuseStep 2981461 = 34939) (by norm_num)
theorem B4472405 : Blo 1766084 4472405 := bbase (se 8 (by rfl) ⟨26205, by rfl⟩ : syracuseStep 4472405 = 52411) (by norm_num)
theorem B5963381 : Blo 1766084 5963381 := bbase (se 5 (by rfl) ⟨279533, by rfl⟩ : syracuseStep 5963381 = 559067) (by norm_num)
theorem B2236025 : Blo 1766084 2236025 := bbase (se 2 (by rfl) ⟨838509, by rfl⟩ : syracuseStep 2236025 = 1677019) (by norm_num)
theorem B2981549 : Blo 1766084 2981549 := bbase (se 3 (by rfl) ⟨559040, by rfl⟩ : syracuseStep 2981549 = 1118081) (by norm_num)
theorem B2236081 : Blo 1766084 2236081 := bbase (se 2 (by rfl) ⟨838530, by rfl⟩ : syracuseStep 2236081 = 1677061) (by norm_num)
theorem B2014897 : Blo 1766084 2014897 := bbase (se 2 (by rfl) ⟨755586, by rfl⟩ : syracuseStep 2014897 = 1511173) (by norm_num)
theorem B4030157 : Blo 1766084 4030157 := bbase (se 3 (by rfl) ⟨755654, by rfl⟩ : syracuseStep 4030157 = 1511309) (by norm_num)
theorem B2236177 : Blo 1766084 2236177 := bbase (se 2 (by rfl) ⟨838566, by rfl⟩ : syracuseStep 2236177 = 1677133) (by norm_num)
theorem B4472597 : Blo 1766084 4472597 := bbase (se 6 (by rfl) ⟨104826, by rfl⟩ : syracuseStep 4472597 = 209653) (by norm_num)
theorem B2981677 : Blo 1766084 2981677 := bbase (se 3 (by rfl) ⟨559064, by rfl⟩ : syracuseStep 2981677 = 1118129) (by norm_num)
theorem B8945477 : Blo 1766084 8945477 := bbase (se 4 (by rfl) ⟨838638, by rfl⟩ : syracuseStep 8945477 = 1677277) (by norm_num)
theorem B2981765 : Blo 1766084 2981765 := bbase (se 4 (by rfl) ⟨279540, by rfl⟩ : syracuseStep 2981765 = 559081) (by norm_num)
theorem B2514845 : Blo 1766084 2514845 := bbase (se 3 (by rfl) ⟨471533, by rfl⟩ : syracuseStep 2514845 = 943067) (by norm_num)
theorem B2015161 : Blo 1766084 2015161 := bbase (se 2 (by rfl) ⟨755685, by rfl⟩ : syracuseStep 2015161 = 1511371) (by norm_num)
theorem B2236349 : Blo 1766084 2236349 := bbase (se 3 (by rfl) ⟨419315, by rfl⟩ : syracuseStep 2236349 = 838631) (by norm_num)
theorem B16981973 : Blo 1766084 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B2121709 : Blo 1766084 2121709 := bbase (se 3 (by rfl) ⟨397820, by rfl⟩ : syracuseStep 2121709 = 795641) (by norm_num)
theorem B2514925 : Blo 1766084 2514925 := bbase (se 3 (by rfl) ⟨471548, by rfl⟩ : syracuseStep 2514925 = 943097) (by norm_num)
theorem B2236405 : Blo 1766084 2236405 := bbase (se 5 (by rfl) ⟨104831, by rfl⟩ : syracuseStep 2236405 = 209663) (by norm_num)
theorem B2015221 : Blo 1766084 2015221 := bbase (se 5 (by rfl) ⟨94463, by rfl⟩ : syracuseStep 2015221 = 188927) (by norm_num)
theorem B2982001 : Blo 1766084 2982001 := bstep (se 2 (by rfl) ⟨1118250, by rfl⟩ : syracuseStep 2982001 = 2236501) B2236501
theorem B2687089 : Blo 1766084 2687089 := bstep (se 2 (by rfl) ⟨1007658, by rfl⟩ : syracuseStep 2687089 = 2015317) B2015317
theorem B5963921 : Blo 1766084 5963921 := bstep (se 2 (by rfl) ⟨2236470, by rfl⟩ : syracuseStep 5963921 = 4472941) B4472941
theorem B2982035 : Blo 1766084 2982035 := bstep (se 1 (by rfl) ⟨2236526, by rfl⟩ : syracuseStep 2982035 = 4473053) B4473053
theorem B2515153 : Blo 1766084 2515153 := bstep (se 2 (by rfl) ⟨943182, by rfl⟩ : syracuseStep 2515153 = 1886365) B1886365
theorem B25460963 : Blo 1766084 25460963 := bstep (se 1 (by rfl) ⟨19095722, by rfl⟩ : syracuseStep 25460963 = 38191445) B38191445
theorem B2982163 : Blo 1766084 2982163 := bstep (se 1 (by rfl) ⟨2236622, by rfl⟩ : syracuseStep 2982163 = 4473245) B4473245
theorem B10060109 : Blo 1766084 10060109 := bstep (se 3 (by rfl) ⟨1886270, by rfl⟩ : syracuseStep 10060109 = 3772541) B3772541
theorem B2982305 : Blo 1766084 2982305 := bstep (se 2 (by rfl) ⟨1118364, by rfl⟩ : syracuseStep 2982305 = 2236729) B2236729
theorem B2236835 : Blo 1766084 2236835 := bstep (se 1 (by rfl) ⟨1677626, by rfl⟩ : syracuseStep 2236835 = 3355253) B3355253
theorem B4473265 : Blo 1766084 4473265 := bstep (se 2 (by rfl) ⟨1677474, by rfl⟩ : syracuseStep 4473265 = 3354949) B3354949
theorem B10068401 : Blo 1766084 10068401 := bstep (se 2 (by rfl) ⟨3775650, by rfl⟩ : syracuseStep 10068401 = 7551301) B7551301
theorem B8946125 : Blo 1766084 8946125 := bstep (se 3 (by rfl) ⟨1677398, by rfl⟩ : syracuseStep 8946125 = 3354797) B3354797
theorem B10199537 : Blo 1766084 10199537 := bstep (se 2 (by rfl) ⟨3824826, by rfl⟩ : syracuseStep 10199537 = 7649653) B7649653
theorem B3580433 : Blo 1766084 3580433 := bstep (se 2 (by rfl) ⟨1342662, by rfl⟩ : syracuseStep 3580433 = 2685325) B2685325
theorem B2982433 : Blo 1766084 2982433 := bstep (se 2 (by rfl) ⟨1118412, by rfl⟩ : syracuseStep 2982433 = 2236825) B2236825
theorem B5448227 : Blo 1766084 5448227 := bstep (se 1 (by rfl) ⟨4086170, by rfl⟩ : syracuseStep 5448227 = 8172341) B8172341
theorem B2982467 : Blo 1766084 2982467 := bstep (se 1 (by rfl) ⟨2236850, by rfl⟩ : syracuseStep 2982467 = 4473701) B4473701
theorem B6709837 : Blo 1766084 6709837 := bstep (se 3 (by rfl) ⟨1258094, by rfl⟩ : syracuseStep 6709837 = 2516189) B2516189
theorem B15295075 : Blo 1766084 15295075 := bstep (se 1 (by rfl) ⟨11471306, by rfl⟩ : syracuseStep 15295075 = 22942613) B22942613
theorem B5030545 : Blo 1766084 5030545 := bstep (se 2 (by rfl) ⟨1886454, by rfl⟩ : syracuseStep 5030545 = 3772909) B3772909
theorem B5964461 : Blo 1766084 5964461 := bstep (se 3 (by rfl) ⟨1118336, by rfl⟩ : syracuseStep 5964461 = 2236673) B2236673
theorem B4473539 : Blo 1766084 4473539 := bstep (se 1 (by rfl) ⟨3355154, by rfl⟩ : syracuseStep 4473539 = 6710309) B6710309
theorem B2982595 : Blo 1766084 2982595 := bstep (se 1 (by rfl) ⟨2236946, by rfl⟩ : syracuseStep 2982595 = 4473893) B4473893
theorem B3973841 : Blo 1766084 3973841 := bstep (se 2 (by rfl) ⟨1490190, by rfl⟩ : syracuseStep 3973841 = 2980381) B2980381
theorem B3973859 : Blo 1766084 3973859 := bstep (se 1 (by rfl) ⟨2980394, by rfl⟩ : syracuseStep 3973859 = 5960789) B5960789
theorem B5964515 : Blo 1766084 5964515 := bstep (se 1 (by rfl) ⟨4473386, by rfl⟩ : syracuseStep 5964515 = 8946773) B8946773
theorem B2515745 : Blo 1766084 2515745 := bstep (se 2 (by rfl) ⟨943404, by rfl⟩ : syracuseStep 2515745 = 1886809) B1886809
theorem B16991045 : Blo 1766084 16991045 := bstep (se 4 (by rfl) ⟨1592910, by rfl⟩ : syracuseStep 16991045 = 3185821) B3185821
theorem B2982737 : Blo 1766084 2982737 := bstep (se 2 (by rfl) ⟨1118526, by rfl⟩ : syracuseStep 2982737 = 2237053) B2237053
theorem B4473731 : Blo 1766084 4473731 := bstep (se 1 (by rfl) ⟨3355298, by rfl⟩ : syracuseStep 4473731 = 6710597) B6710597
theorem B5030819 : Blo 1766084 5030819 := bstep (se 1 (by rfl) ⟨3773114, by rfl⟩ : syracuseStep 5030819 = 7546229) B7546229
theorem B2982865 : Blo 1766084 2982865 := bstep (se 2 (by rfl) ⟨1118574, by rfl⟩ : syracuseStep 2982865 = 2237149) B2237149
theorem B2122723 : Blo 1766084 2122723 := bstep (se 1 (by rfl) ⟨1592042, by rfl⟩ : syracuseStep 2122723 = 3184085) B3184085
theorem B3974129 : Blo 1766084 3974129 := bstep (se 2 (by rfl) ⟨1490298, by rfl⟩ : syracuseStep 3974129 = 2980597) B2980597
theorem B5964785 : Blo 1766084 5964785 := bstep (se 2 (by rfl) ⟨2236794, by rfl⟩ : syracuseStep 5964785 = 4473589) B4473589
theorem B2982899 : Blo 1766084 2982899 := bstep (se 1 (by rfl) ⟨2237174, by rfl⟩ : syracuseStep 2982899 = 4474349) B4474349
theorem B4031473 : Blo 1766084 4031473 := bstep (se 2 (by rfl) ⟨1511802, by rfl⟩ : syracuseStep 4031473 = 3023605) B3023605
theorem B3974147 : Blo 1766084 3974147 := bstep (se 1 (by rfl) ⟨2980610, by rfl⟩ : syracuseStep 3974147 = 5961221) B5961221
theorem B7545869 : Blo 1766084 7545869 := bstep (se 3 (by rfl) ⟨1414850, by rfl⟩ : syracuseStep 7545869 = 2829701) B2829701
theorem B5031011 : Blo 1766084 5031011 := bstep (se 1 (by rfl) ⟨3773258, by rfl⟩ : syracuseStep 5031011 = 7546517) B7546517
theorem B2237539 : Blo 1766084 2237539 := bstep (se 1 (by rfl) ⟨1678154, by rfl⟩ : syracuseStep 2237539 = 3356309) B3356309
theorem B2983027 : Blo 1766084 2983027 := bstep (se 1 (by rfl) ⟨2237270, by rfl⟩ : syracuseStep 2983027 = 4474541) B4474541
theorem B2237635 : Blo 1766084 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B2983169 : Blo 1766084 2983169 := bstep (se 2 (by rfl) ⟨1118688, by rfl⟩ : syracuseStep 2983169 = 2237377) B2237377
theorem B3228931 : Blo 1766084 3228931 := bstep (se 1 (by rfl) ⟨2421698, by rfl⟩ : syracuseStep 3228931 = 4843397) B4843397
theorem B3974417 : Blo 1766084 3974417 := bstep (se 2 (by rfl) ⟨1490406, by rfl⟩ : syracuseStep 3974417 = 2980813) B2980813
theorem B3974435 : Blo 1766084 3974435 := bstep (se 1 (by rfl) ⟨2980826, by rfl⟩ : syracuseStep 3974435 = 5961653) B5961653
theorem B2516275 : Blo 1766084 2516275 := bstep (se 1 (by rfl) ⟨1887206, by rfl⟩ : syracuseStep 2516275 = 3774413) B3774413
theorem B14329187 : Blo 1766084 14329187 := bstep (se 1 (by rfl) ⟨10746890, by rfl⟩ : syracuseStep 14329187 = 21493781) B21493781
theorem B6710627 : Blo 1766084 6710627 := bstep (se 1 (by rfl) ⟨5032970, by rfl⟩ : syracuseStep 6710627 = 10065941) B10065941
theorem B2983297 : Blo 1766084 2983297 := bstep (se 2 (by rfl) ⟨1118736, by rfl⟩ : syracuseStep 2983297 = 2237473) B2237473
theorem B13419917 : Blo 1766084 13419917 := bstep (se 3 (by rfl) ⟨2516234, by rfl⟩ : syracuseStep 13419917 = 5032469) B5032469
theorem B2983331 : Blo 1766084 2983331 := bstep (se 1 (by rfl) ⟨2237498, by rfl⟩ : syracuseStep 2983331 = 4474997) B4474997
theorem B5965325 : Blo 1766084 5965325 := bstep (se 3 (by rfl) ⟨1118498, by rfl⟩ : syracuseStep 5965325 = 2236997) B2236997
theorem B2983459 : Blo 1766084 2983459 := bstep (se 1 (by rfl) ⟨2237594, by rfl⟩ : syracuseStep 2983459 = 4475189) B4475189
theorem B3974705 : Blo 1766084 3974705 := bstep (se 2 (by rfl) ⟨1490514, by rfl⟩ : syracuseStep 3974705 = 2981029) B2981029
theorem B3974723 : Blo 1766084 3974723 := bstep (se 1 (by rfl) ⟨2981042, by rfl⟩ : syracuseStep 3974723 = 5962085) B5962085
theorem B5965379 : Blo 1766084 5965379 := bstep (se 1 (by rfl) ⟨4474034, by rfl⟩ : syracuseStep 5965379 = 8948069) B8948069
theorem B12084835 : Blo 1766084 12084835 := bstep (se 1 (by rfl) ⟨9063626, by rfl⟩ : syracuseStep 12084835 = 18127253) B18127253
theorem B5375587 : Blo 1766084 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B2516611 : Blo 1766084 2516611 := bstep (se 1 (by rfl) ⟨1887458, by rfl⟩ : syracuseStep 2516611 = 3774917) B3774917
theorem B5662349 : Blo 1766084 5662349 := bstep (se 3 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 5662349 = 2123381) B2123381
theorem B2983601 : Blo 1766084 2983601 := bstep (se 2 (by rfl) ⟨1118850, by rfl⟩ : syracuseStep 2983601 = 2237701) B2237701
theorem B5662477 : Blo 1766084 5662477 := bstep (se 3 (by rfl) ⟨1061714, by rfl⟩ : syracuseStep 5662477 = 2123429) B2123429
theorem B8488739 : Blo 1766084 8488739 := bstep (se 1 (by rfl) ⟨6366554, by rfl⟩ : syracuseStep 8488739 = 12733109) B12733109
theorem B4474673 : Blo 1766084 4474673 := bstep (se 2 (by rfl) ⟨1678002, by rfl⟩ : syracuseStep 4474673 = 3356005) B3356005
theorem B3974993 : Blo 1766084 3974993 := bstep (se 2 (by rfl) ⟨1490622, by rfl⟩ : syracuseStep 3974993 = 2981245) B2981245
theorem B5965649 : Blo 1766084 5965649 := bstep (se 2 (by rfl) ⟨2237118, by rfl⟩ : syracuseStep 5965649 = 4474237) B4474237
theorem B3975011 : Blo 1766084 3975011 := bstep (se 1 (by rfl) ⟨2981258, by rfl⟩ : syracuseStep 3975011 = 5962517) B5962517
theorem B4474723 : Blo 1766084 4474723 := bstep (se 1 (by rfl) ⟨3356042, by rfl⟩ : syracuseStep 4474723 = 6712085) B6712085
theorem B5031821 : Blo 1766084 5031821 := bstep (se 3 (by rfl) ⟨943466, by rfl⟩ : syracuseStep 5031821 = 1886933) B1886933
theorem B3401617 : Blo 1766084 3401617 := bstep (se 2 (by rfl) ⟨1275606, by rfl⟩ : syracuseStep 3401617 = 2551213) B2551213
theorem B8488909 : Blo 1766084 8488909 := bstep (se 3 (by rfl) ⟨1591670, by rfl⟩ : syracuseStep 8488909 = 3183341) B3183341
theorem B6711281 : Blo 1766084 6711281 := bstep (se 2 (by rfl) ⟨2516730, by rfl⟩ : syracuseStep 6711281 = 5033461) B5033461
theorem B4474865 : Blo 1766084 4474865 := bstep (se 2 (by rfl) ⟨1678074, by rfl⟩ : syracuseStep 4474865 = 3356149) B3356149
theorem B5032003 : Blo 1766084 5032003 := bstep (se 1 (by rfl) ⟨3774002, by rfl⟩ : syracuseStep 5032003 = 7548005) B7548005
theorem B3975281 : Blo 1766084 3975281 := bstep (se 2 (by rfl) ⟨1490730, by rfl⟩ : syracuseStep 3975281 = 2981461) B2981461
theorem B1886339 : Blo 1766084 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B3975299 : Blo 1766084 3975299 := bstep (se 1 (by rfl) ⟨2981474, by rfl⟩ : syracuseStep 3975299 = 5962949) B5962949
theorem B2517169 : Blo 1766084 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B2517203 : Blo 1766084 2517203 := bstep (se 1 (by rfl) ⟨1887902, by rfl⟩ : syracuseStep 2517203 = 3775805) B3775805
theorem B5966189 : Blo 1766084 5966189 := bstep (se 3 (by rfl) ⟨1118660, by rfl⟩ : syracuseStep 5966189 = 2237321) B2237321
theorem B3975569 : Blo 1766084 3975569 := bstep (se 2 (by rfl) ⟨1490838, by rfl⟩ : syracuseStep 3975569 = 2981677) B2981677
theorem B3975587 : Blo 1766084 3975587 := bstep (se 1 (by rfl) ⟨2981690, by rfl⟩ : syracuseStep 3975587 = 5963381) B5963381
theorem B5966243 : Blo 1766084 5966243 := bstep (se 1 (by rfl) ⟨4474682, by rfl⟩ : syracuseStep 5966243 = 8949365) B8949365
theorem B5032493 : Blo 1766084 5032493 := bstep (se 3 (by rfl) ⟨943592, by rfl⟩ : syracuseStep 5032493 = 1887185) B1887185
theorem B2828945 : Blo 1766084 2828945 := bstep (se 2 (by rfl) ⟨1060854, by rfl⟩ : syracuseStep 2828945 = 2121709) B2121709
theorem B3353233 : Blo 1766084 3353233 := bstep (se 2 (by rfl) ⟨1257462, by rfl⟩ : syracuseStep 3353233 = 2514925) B2514925
theorem B3975857 : Blo 1766084 3975857 := bstep (se 2 (by rfl) ⟨1490946, by rfl⟩ : syracuseStep 3975857 = 2981893) B2981893
theorem B5966513 : Blo 1766084 5966513 := bstep (se 2 (by rfl) ⟨2237442, by rfl⟩ : syracuseStep 5966513 = 4474885) B4474885
theorem B3975875 : Blo 1766084 3975875 := bstep (se 1 (by rfl) ⟨2981906, by rfl⟩ : syracuseStep 3975875 = 5963813) B5963813
theorem B2829073 : Blo 1766084 2829073 := bstep (se 2 (by rfl) ⟨1060902, by rfl⟩ : syracuseStep 2829073 = 2121805) B2121805
theorem B3353393 : Blo 1766084 3353393 := bstep (se 2 (by rfl) ⟨1257522, by rfl⟩ : syracuseStep 3353393 = 2515045) B2515045
theorem B7654193 : Blo 1766084 7654193 := bstep (se 2 (by rfl) ⟨2870322, by rfl⟩ : syracuseStep 7654193 = 5740645) B5740645
theorem B27200369 : Blo 1766084 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B49007501 : Blo 1766084 49007501 := bstep (se 3 (by rfl) ⟨9188906, by rfl⟩ : syracuseStep 49007501 = 18377813) B18377813
theorem B3976145 : Blo 1766084 3976145 := bstep (se 2 (by rfl) ⟨1491054, by rfl⟩ : syracuseStep 3976145 = 2982109) B2982109
theorem B3976163 : Blo 1766084 3976163 := bstep (se 1 (by rfl) ⟨2982122, by rfl⟩ : syracuseStep 3976163 = 5964245) B5964245
theorem B3582947 : Blo 1766084 3582947 := bstep (se 1 (by rfl) ⟨2687210, by rfl⟩ : syracuseStep 3582947 = 5374421) B5374421
theorem B2649137 : Blo 1766084 2649137 := bstep (se 2 (by rfl) ⟨993426, by rfl⟩ : syracuseStep 2649137 = 1986853) B1986853
theorem B2649155 : Blo 1766084 2649155 := bstep (se 1 (by rfl) ⟨1986866, by rfl⟩ : syracuseStep 2649155 = 3973733) B3973733
theorem B2649185 : Blo 1766084 2649185 := bstep (se 2 (by rfl) ⟨993444, by rfl⟩ : syracuseStep 2649185 = 1986889) B1986889
theorem B2649203 : Blo 1766084 2649203 := bstep (se 1 (by rfl) ⟨1986902, by rfl⟩ : syracuseStep 2649203 = 3973805) B3973805
theorem B1887347 : Blo 1766084 1887347 := bstep (se 1 (by rfl) ⟨1415510, by rfl⟩ : syracuseStep 1887347 = 2831021) B2831021
theorem B2649233 : Blo 1766084 2649233 := bstep (se 2 (by rfl) ⟨993462, by rfl⟩ : syracuseStep 2649233 = 1986925) B1986925
theorem B2649251 : Blo 1766084 2649251 := bstep (se 1 (by rfl) ⟨1986938, by rfl⟩ : syracuseStep 2649251 = 3973877) B3973877
theorem B9071779 : Blo 1766084 9071779 := bstep (se 1 (by rfl) ⟨6803834, by rfl⟩ : syracuseStep 9071779 = 13607669) B13607669
theorem B10063025 : Blo 1766084 10063025 := bstep (se 2 (by rfl) ⟨3773634, by rfl⟩ : syracuseStep 10063025 = 7547269) B7547269
theorem B2649281 : Blo 1766084 2649281 := bstep (se 2 (by rfl) ⟨993480, by rfl⟩ : syracuseStep 2649281 = 1986961) B1986961
theorem B3353795 : Blo 1766084 3353795 := bstep (se 1 (by rfl) ⟨2515346, by rfl⟩ : syracuseStep 3353795 = 5030693) B5030693
theorem B5967053 : Blo 1766084 5967053 := bstep (se 3 (by rfl) ⟨1118822, by rfl⟩ : syracuseStep 5967053 = 2237645) B2237645
theorem B2649299 : Blo 1766084 2649299 := bstep (se 1 (by rfl) ⟨1986974, by rfl⟩ : syracuseStep 2649299 = 3973949) B3973949
theorem B2649329 : Blo 1766084 2649329 := bstep (se 2 (by rfl) ⟨993498, by rfl⟩ : syracuseStep 2649329 = 1986997) B1986997
theorem B3976433 : Blo 1766084 3976433 := bstep (se 2 (by rfl) ⟨1491162, by rfl⟩ : syracuseStep 3976433 = 2982325) B2982325
theorem B2649347 : Blo 1766084 2649347 := bstep (se 1 (by rfl) ⟨1987010, by rfl⟩ : syracuseStep 2649347 = 3974021) B3974021
theorem B3976451 : Blo 1766084 3976451 := bstep (se 1 (by rfl) ⟨2982338, by rfl⟩ : syracuseStep 3976451 = 5964677) B5964677
theorem B5967107 : Blo 1766084 5967107 := bstep (se 1 (by rfl) ⟨4475330, by rfl⟩ : syracuseStep 5967107 = 8950661) B8950661
theorem B8629517 : Blo 1766084 8629517 := bstep (se 3 (by rfl) ⟨1618034, by rfl⟩ : syracuseStep 8629517 = 3236069) B3236069
theorem B2649377 : Blo 1766084 2649377 := bstep (se 2 (by rfl) ⟨993516, by rfl⟩ : syracuseStep 2649377 = 1987033) B1987033
theorem B8949041 : Blo 1766084 8949041 := bstep (se 2 (by rfl) ⟨3355890, by rfl⟩ : syracuseStep 8949041 = 6711781) B6711781
theorem B2649395 : Blo 1766084 2649395 := bstep (se 1 (by rfl) ⟨1987046, by rfl⟩ : syracuseStep 2649395 = 3974093) B3974093
theorem B2649425 : Blo 1766084 2649425 := bstep (se 2 (by rfl) ⟨993534, by rfl⟩ : syracuseStep 2649425 = 1987069) B1987069
theorem B2649443 : Blo 1766084 2649443 := bstep (se 1 (by rfl) ⟨1987082, by rfl⟩ : syracuseStep 2649443 = 3974165) B3974165
theorem B21491057 : Blo 1766084 21491057 := bstep (se 2 (by rfl) ⟨8059146, by rfl⟩ : syracuseStep 21491057 = 16118293) B16118293
theorem B2649473 : Blo 1766084 2649473 := bstep (se 2 (by rfl) ⟨993552, by rfl⟩ : syracuseStep 2649473 = 1987105) B1987105
theorem B4246915 : Blo 1766084 4246915 := bstep (se 1 (by rfl) ⟨3185186, by rfl⟩ : syracuseStep 4246915 = 6370373) B6370373
theorem B8940941 : Blo 1766084 8940941 := bstep (se 3 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 8940941 = 3352853) B3352853
theorem B2649491 : Blo 1766084 2649491 := bstep (se 1 (by rfl) ⟨1987118, by rfl⟩ : syracuseStep 2649491 = 3974237) B3974237
theorem B6712739 : Blo 1766084 6712739 := bstep (se 1 (by rfl) ⟨5034554, by rfl⟩ : syracuseStep 6712739 = 10069109) B10069109
theorem B2649521 : Blo 1766084 2649521 := bstep (se 2 (by rfl) ⟨993570, by rfl⟩ : syracuseStep 2649521 = 1987141) B1987141
theorem B6712753 : Blo 1766084 6712753 := bstep (se 2 (by rfl) ⟨2517282, by rfl⟩ : syracuseStep 6712753 = 5034565) B5034565
theorem B2649539 : Blo 1766084 2649539 := bstep (se 1 (by rfl) ⟨1987154, by rfl⟩ : syracuseStep 2649539 = 3974309) B3974309
theorem B2649569 : Blo 1766084 2649569 := bstep (se 2 (by rfl) ⟨993588, by rfl⟩ : syracuseStep 2649569 = 1987177) B1987177
theorem B2649587 : Blo 1766084 2649587 := bstep (se 1 (by rfl) ⟨1987190, by rfl⟩ : syracuseStep 2649587 = 3974381) B3974381
theorem B2649617 : Blo 1766084 2649617 := bstep (se 2 (by rfl) ⟨993606, by rfl⟩ : syracuseStep 2649617 = 1987213) B1987213
theorem B3976721 : Blo 1766084 3976721 := bstep (se 2 (by rfl) ⟨1491270, by rfl⟩ : syracuseStep 3976721 = 2982541) B2982541
theorem B2649635 : Blo 1766084 2649635 := bstep (se 1 (by rfl) ⟨1987226, by rfl⟩ : syracuseStep 2649635 = 3974453) B3974453
theorem B3976739 : Blo 1766084 3976739 := bstep (se 1 (by rfl) ⟨2982554, by rfl⟩ : syracuseStep 3976739 = 5965109) B5965109
theorem B2649665 : Blo 1766084 2649665 := bstep (se 2 (by rfl) ⟨993624, by rfl⟩ : syracuseStep 2649665 = 1987249) B1987249
theorem B11325005 : Blo 1766084 11325005 := bstep (se 3 (by rfl) ⟨2123438, by rfl⟩ : syracuseStep 11325005 = 4246877) B4246877
theorem B2649683 : Blo 1766084 2649683 := bstep (se 1 (by rfl) ⟨1987262, by rfl⟩ : syracuseStep 2649683 = 3974525) B3974525
theorem B2649713 : Blo 1766084 2649713 := bstep (se 2 (by rfl) ⟨993642, by rfl⟩ : syracuseStep 2649713 = 1987285) B1987285
theorem B2649731 : Blo 1766084 2649731 := bstep (se 1 (by rfl) ⟨1987298, by rfl⟩ : syracuseStep 2649731 = 3974597) B3974597
theorem B2649761 : Blo 1766084 2649761 := bstep (se 2 (by rfl) ⟨993660, by rfl⟩ : syracuseStep 2649761 = 1987321) B1987321
theorem B2649779 : Blo 1766084 2649779 := bstep (se 1 (by rfl) ⟨1987334, by rfl⟩ : syracuseStep 2649779 = 3974669) B3974669
theorem B2043571 : Blo 1766084 2043571 := bstep (se 1 (by rfl) ⟨1532678, by rfl⟩ : syracuseStep 2043571 = 3065357) B3065357
theorem B13414085 : Blo 1766084 13414085 := bstep (se 4 (by rfl) ⟨1257570, by rfl⟩ : syracuseStep 13414085 = 2515141) B2515141
theorem B5033677 : Blo 1766084 5033677 := bstep (se 3 (by rfl) ⟨943814, by rfl⟩ : syracuseStep 5033677 = 1887629) B1887629
theorem B2649809 : Blo 1766084 2649809 := bstep (se 2 (by rfl) ⟨993678, by rfl⟩ : syracuseStep 2649809 = 1987357) B1987357
theorem B2649827 : Blo 1766084 2649827 := bstep (se 1 (by rfl) ⟨1987370, by rfl⟩ : syracuseStep 2649827 = 3974741) B3974741
theorem B2649857 : Blo 1766084 2649857 := bstep (se 2 (by rfl) ⟨993696, by rfl⟩ : syracuseStep 2649857 = 1987393) B1987393
theorem B2297603 : Blo 1766084 2297603 := bstep (se 1 (by rfl) ⟨1723202, by rfl⟩ : syracuseStep 2297603 = 3446405) B3446405
theorem B2649875 : Blo 1766084 2649875 := bstep (se 1 (by rfl) ⟨1987406, by rfl⟩ : syracuseStep 2649875 = 3974813) B3974813
theorem B2649905 : Blo 1766084 2649905 := bstep (se 2 (by rfl) ⟨993714, by rfl⟩ : syracuseStep 2649905 = 1987429) B1987429
theorem B8605489 : Blo 1766084 8605489 := bstep (se 2 (by rfl) ⟨3227058, by rfl⟩ : syracuseStep 8605489 = 6454117) B6454117
theorem B3977009 : Blo 1766084 3977009 := bstep (se 2 (by rfl) ⟨1491378, by rfl⟩ : syracuseStep 3977009 = 2982757) B2982757
theorem B2387777 : Blo 1766084 2387777 := bstep (se 2 (by rfl) ⟨895416, by rfl⟩ : syracuseStep 2387777 = 1790833) B1790833
theorem B2649923 : Blo 1766084 2649923 := bstep (se 1 (by rfl) ⟨1987442, by rfl⟩ : syracuseStep 2649923 = 3974885) B3974885
theorem B3977027 : Blo 1766084 3977027 := bstep (se 1 (by rfl) ⟨2982770, by rfl⟩ : syracuseStep 3977027 = 5965541) B5965541
theorem B2649953 : Blo 1766084 2649953 := bstep (se 2 (by rfl) ⟨993732, by rfl⟩ : syracuseStep 2649953 = 1987465) B1987465
theorem B22646627 : Blo 1766084 22646627 := bstep (se 1 (by rfl) ⟨16984970, by rfl⟩ : syracuseStep 22646627 = 33969941) B33969941
theorem B2649971 : Blo 1766084 2649971 := bstep (se 1 (by rfl) ⟨1987478, by rfl⟩ : syracuseStep 2649971 = 3974957) B3974957
theorem B2650001 : Blo 1766084 2650001 := bstep (se 2 (by rfl) ⟨993750, by rfl⟩ : syracuseStep 2650001 = 1987501) B1987501
theorem B2650019 : Blo 1766084 2650019 := bstep (se 1 (by rfl) ⟨1987514, by rfl⟩ : syracuseStep 2650019 = 3975029) B3975029
theorem B4247473 : Blo 1766084 4247473 := bstep (se 2 (by rfl) ⟨1592802, by rfl⟩ : syracuseStep 4247473 = 3185605) B3185605
theorem B2650049 : Blo 1766084 2650049 := bstep (se 2 (by rfl) ⟨993768, by rfl⟩ : syracuseStep 2650049 = 1987537) B1987537
theorem B2650067 : Blo 1766084 2650067 := bstep (se 1 (by rfl) ⟨1987550, by rfl⟩ : syracuseStep 2650067 = 3975101) B3975101
theorem B2650097 : Blo 1766084 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B2650115 : Blo 1766084 2650115 := bstep (se 1 (by rfl) ⟨1987586, by rfl⟩ : syracuseStep 2650115 = 3975173) B3975173
theorem B2650145 : Blo 1766084 2650145 := bstep (se 2 (by rfl) ⟨993804, by rfl⟩ : syracuseStep 2650145 = 1987609) B1987609
theorem B7548977 : Blo 1766084 7548977 := bstep (se 2 (by rfl) ⟨2830866, by rfl⟩ : syracuseStep 7548977 = 5661733) B5661733
theorem B2650163 : Blo 1766084 2650163 := bstep (se 1 (by rfl) ⟨1987622, by rfl⟩ : syracuseStep 2650163 = 3975245) B3975245
theorem B3354691 : Blo 1766084 3354691 := bstep (se 1 (by rfl) ⟨2516018, by rfl⟩ : syracuseStep 3354691 = 5032037) B5032037
theorem B2650193 : Blo 1766084 2650193 := bstep (se 2 (by rfl) ⟨993822, by rfl⟩ : syracuseStep 2650193 = 1987645) B1987645
theorem B3977297 : Blo 1766084 3977297 := bstep (se 2 (by rfl) ⟨1491486, by rfl⟩ : syracuseStep 3977297 = 2982973) B2982973
theorem B2650211 : Blo 1766084 2650211 := bstep (se 1 (by rfl) ⟨1987658, by rfl⟩ : syracuseStep 2650211 = 3975317) B3975317
theorem B3977315 : Blo 1766084 3977315 := bstep (se 1 (by rfl) ⟨2982986, by rfl⟩ : syracuseStep 3977315 = 5965973) B5965973
theorem B2650241 : Blo 1766084 2650241 := bstep (se 2 (by rfl) ⟨993840, by rfl⟩ : syracuseStep 2650241 = 1987681) B1987681
theorem B2650259 : Blo 1766084 2650259 := bstep (se 1 (by rfl) ⟨1987694, by rfl⟩ : syracuseStep 2650259 = 3975389) B3975389
theorem B2650289 : Blo 1766084 2650289 := bstep (se 2 (by rfl) ⟨993858, by rfl⟩ : syracuseStep 2650289 = 1987717) B1987717
theorem B2650307 : Blo 1766084 2650307 := bstep (se 1 (by rfl) ⟨1987730, by rfl⟩ : syracuseStep 2650307 = 3975461) B3975461
theorem B9556165 : Blo 1766084 9556165 := bstep (se 4 (by rfl) ⟨895890, by rfl⟩ : syracuseStep 9556165 = 1791781) B1791781
theorem B2650337 : Blo 1766084 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B3354851 : Blo 1766084 3354851 := bstep (se 1 (by rfl) ⟨2516138, by rfl⟩ : syracuseStep 3354851 = 5032277) B5032277
theorem B13422833 : Blo 1766084 13422833 := bstep (se 2 (by rfl) ⟨5033562, by rfl⟩ : syracuseStep 13422833 = 10067125) B10067125
theorem B2650355 : Blo 1766084 2650355 := bstep (se 1 (by rfl) ⟨1987766, by rfl⟩ : syracuseStep 2650355 = 3975533) B3975533
theorem B2650385 : Blo 1766084 2650385 := bstep (se 2 (by rfl) ⟨993894, by rfl⟩ : syracuseStep 2650385 = 1987789) B1987789
theorem B2650403 : Blo 1766084 2650403 := bstep (se 1 (by rfl) ⟨1987802, by rfl⟩ : syracuseStep 2650403 = 3975605) B3975605
theorem B2650433 : Blo 1766084 2650433 := bstep (se 2 (by rfl) ⟨993912, by rfl⟩ : syracuseStep 2650433 = 1987825) B1987825
theorem B2650451 : Blo 1766084 2650451 := bstep (se 1 (by rfl) ⟨1987838, by rfl⟩ : syracuseStep 2650451 = 3975677) B3975677
theorem B2388307 : Blo 1766084 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B2650481 : Blo 1766084 2650481 := bstep (se 2 (by rfl) ⟨993930, by rfl⟩ : syracuseStep 2650481 = 1987861) B1987861
theorem B3977585 : Blo 1766084 3977585 := bstep (se 2 (by rfl) ⟨1491594, by rfl⟩ : syracuseStep 3977585 = 2983189) B2983189
theorem B2650499 : Blo 1766084 2650499 := bstep (se 1 (by rfl) ⟨1987874, by rfl⟩ : syracuseStep 2650499 = 3975749) B3975749
theorem B3977603 : Blo 1766084 3977603 := bstep (se 1 (by rfl) ⟨2983202, by rfl⟩ : syracuseStep 3977603 = 5966405) B5966405
theorem B2650529 : Blo 1766084 2650529 := bstep (se 2 (by rfl) ⟨993948, by rfl⟩ : syracuseStep 2650529 = 1987897) B1987897
theorem B1986979 : Blo 1766084 1986979 := bstep (se 1 (by rfl) ⟨1490234, by rfl⟩ : syracuseStep 1986979 = 2980469) B2980469
theorem B2650547 : Blo 1766084 2650547 := bstep (se 1 (by rfl) ⟨1987910, by rfl⟩ : syracuseStep 2650547 = 3975821) B3975821
theorem B19116485 : Blo 1766084 19116485 := bstep (se 4 (by rfl) ⟨1792170, by rfl⟩ : syracuseStep 19116485 = 3584341) B3584341
theorem B2650577 : Blo 1766084 2650577 := bstep (se 2 (by rfl) ⟨993966, by rfl⟩ : syracuseStep 2650577 = 1987933) B1987933
theorem B1790435 : Blo 1766084 1790435 := bstep (se 1 (by rfl) ⟨1342826, by rfl⟩ : syracuseStep 1790435 = 2685653) B2685653
theorem B2650595 : Blo 1766084 2650595 := bstep (se 1 (by rfl) ⟨1987946, by rfl⟩ : syracuseStep 2650595 = 3975893) B3975893
theorem B2650625 : Blo 1766084 2650625 := bstep (se 2 (by rfl) ⟨993984, by rfl⟩ : syracuseStep 2650625 = 1987969) B1987969
theorem B2650643 : Blo 1766084 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B2650673 : Blo 1766084 2650673 := bstep (se 2 (by rfl) ⟨994002, by rfl⟩ : syracuseStep 2650673 = 1988005) B1988005
theorem B1987123 : Blo 1766084 1987123 := bstep (se 1 (by rfl) ⟨1490342, by rfl⟩ : syracuseStep 1987123 = 2980685) B2980685
theorem B2650691 : Blo 1766084 2650691 := bstep (se 1 (by rfl) ⟨1988018, by rfl⟩ : syracuseStep 2650691 = 3976037) B3976037
theorem B4248145 : Blo 1766084 4248145 := bstep (se 2 (by rfl) ⟨1593054, by rfl⟩ : syracuseStep 4248145 = 3186109) B3186109
theorem B2650721 : Blo 1766084 2650721 := bstep (se 2 (by rfl) ⟨994020, by rfl⟩ : syracuseStep 2650721 = 1988041) B1988041
theorem B10064483 : Blo 1766084 10064483 := bstep (se 1 (by rfl) ⟨7548362, by rfl⟩ : syracuseStep 10064483 = 15096725) B15096725
theorem B2650739 : Blo 1766084 2650739 := bstep (se 1 (by rfl) ⟨1988054, by rfl⟩ : syracuseStep 2650739 = 3976109) B3976109
theorem B2650769 : Blo 1766084 2650769 := bstep (se 2 (by rfl) ⟨994038, by rfl⟩ : syracuseStep 2650769 = 1988077) B1988077
theorem B3977873 : Blo 1766084 3977873 := bstep (se 2 (by rfl) ⟨1491702, by rfl⟩ : syracuseStep 3977873 = 2983405) B2983405
theorem B2650787 : Blo 1766084 2650787 := bstep (se 1 (by rfl) ⟨1988090, by rfl⟩ : syracuseStep 2650787 = 3976181) B3976181
theorem B9556643 : Blo 1766084 9556643 := bstep (se 1 (by rfl) ⟨7167482, by rfl⟩ : syracuseStep 9556643 = 14334965) B14334965
theorem B3977891 : Blo 1766084 3977891 := bstep (se 1 (by rfl) ⟨2983418, by rfl⟩ : syracuseStep 3977891 = 5966837) B5966837
theorem B2650817 : Blo 1766084 2650817 := bstep (se 2 (by rfl) ⟨994056, by rfl⟩ : syracuseStep 2650817 = 1988113) B1988113
theorem B1987267 : Blo 1766084 1987267 := bstep (se 1 (by rfl) ⟨1490450, by rfl⟩ : syracuseStep 1987267 = 2980901) B2980901
theorem B7549645 : Blo 1766084 7549645 := bstep (se 3 (by rfl) ⟨1415558, by rfl⟩ : syracuseStep 7549645 = 2831117) B2831117
theorem B3183313 : Blo 1766084 3183313 := bstep (se 2 (by rfl) ⟨1193742, by rfl⟩ : syracuseStep 3183313 = 2387485) B2387485
theorem B1766099 : Blo 1766084 1766099 := bstep (se 1 (by rfl) ⟨1324574, by rfl⟩ : syracuseStep 1766099 = 2649149) B2649149
theorem B2650835 : Blo 1766084 2650835 := bstep (se 1 (by rfl) ⟨1988126, by rfl⟩ : syracuseStep 2650835 = 3976253) B3976253
theorem B1766115 : Blo 1766084 1766115 := bstep (se 1 (by rfl) ⟨1324586, by rfl⟩ : syracuseStep 1766115 = 2649173) B2649173
theorem B8950499 : Blo 1766084 8950499 := bstep (se 1 (by rfl) ⟨6712874, by rfl⟩ : syracuseStep 8950499 = 13425749) B13425749
theorem B2650865 : Blo 1766084 2650865 := bstep (se 2 (by rfl) ⟨994074, by rfl⟩ : syracuseStep 2650865 = 1988149) B1988149
theorem B5034737 : Blo 1766084 5034737 := bstep (se 2 (by rfl) ⟨1888026, by rfl⟩ : syracuseStep 5034737 = 3776053) B3776053
theorem B1766131 : Blo 1766084 1766131 := bstep (se 1 (by rfl) ⟨1324598, by rfl⟩ : syracuseStep 1766131 = 2649197) B2649197
theorem B1766147 : Blo 1766084 1766147 := bstep (se 1 (by rfl) ⟨1324610, by rfl⟩ : syracuseStep 1766147 = 2649221) B2649221
theorem B2650883 : Blo 1766084 2650883 := bstep (se 1 (by rfl) ⟨1988162, by rfl⟩ : syracuseStep 2650883 = 3976325) B3976325
theorem B9679621 : Blo 1766084 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B1766163 : Blo 1766084 1766163 := bstep (se 1 (by rfl) ⟨1324622, by rfl⟩ : syracuseStep 1766163 = 2649245) B2649245
theorem B2831123 : Blo 1766084 2831123 := bstep (se 1 (by rfl) ⟨2123342, by rfl⟩ : syracuseStep 2831123 = 4246685) B4246685
theorem B2650913 : Blo 1766084 2650913 := bstep (se 2 (by rfl) ⟨994092, by rfl⟩ : syracuseStep 2650913 = 1988185) B1988185
theorem B1766179 : Blo 1766084 1766179 := bstep (se 1 (by rfl) ⟨1324634, by rfl⟩ : syracuseStep 1766179 = 2649269) B2649269
theorem B1766195 : Blo 1766084 1766195 := bstep (se 1 (by rfl) ⟨1324646, by rfl⟩ : syracuseStep 1766195 = 2649293) B2649293
theorem B2650931 : Blo 1766084 2650931 := bstep (se 1 (by rfl) ⟨1988198, by rfl⟩ : syracuseStep 2650931 = 3976397) B3976397
theorem B24171317 : Blo 1766084 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B1766211 : Blo 1766084 1766211 := bstep (se 1 (by rfl) ⟨1324658, by rfl⟩ : syracuseStep 1766211 = 2649317) B2649317
theorem B2650961 : Blo 1766084 2650961 := bstep (se 2 (by rfl) ⟨994110, by rfl⟩ : syracuseStep 2650961 = 1988221) B1988221
theorem B1766227 : Blo 1766084 1766227 := bstep (se 1 (by rfl) ⟨1324670, by rfl⟩ : syracuseStep 1766227 = 2649341) B2649341
theorem B1987411 : Blo 1766084 1987411 := bstep (se 1 (by rfl) ⟨1490558, by rfl⟩ : syracuseStep 1987411 = 2981117) B2981117
theorem B1766243 : Blo 1766084 1766243 := bstep (se 1 (by rfl) ⟨1324682, by rfl⟩ : syracuseStep 1766243 = 2649365) B2649365
theorem B2650979 : Blo 1766084 2650979 := bstep (se 1 (by rfl) ⟨1988234, by rfl⟩ : syracuseStep 2650979 = 3976469) B3976469
theorem B1766259 : Blo 1766084 1766259 := bstep (se 1 (by rfl) ⟨1324694, by rfl⟩ : syracuseStep 1766259 = 2649389) B2649389
theorem B2651009 : Blo 1766084 2651009 := bstep (se 2 (by rfl) ⟨994128, by rfl⟩ : syracuseStep 2651009 = 1988257) B1988257
theorem B1766275 : Blo 1766084 1766275 := bstep (se 1 (by rfl) ⟨1324706, by rfl⟩ : syracuseStep 1766275 = 2649413) B2649413
theorem B1766291 : Blo 1766084 1766291 := bstep (se 1 (by rfl) ⟨1324718, by rfl⟩ : syracuseStep 1766291 = 2649437) B2649437
theorem B2651027 : Blo 1766084 2651027 := bstep (se 1 (by rfl) ⟨1988270, by rfl⟩ : syracuseStep 2651027 = 3976541) B3976541
theorem B1766307 : Blo 1766084 1766307 := bstep (se 1 (by rfl) ⟨1324730, by rfl⟩ : syracuseStep 1766307 = 2649461) B2649461
theorem B2651057 : Blo 1766084 2651057 := bstep (se 2 (by rfl) ⟨994146, by rfl⟩ : syracuseStep 2651057 = 1988293) B1988293
theorem B3978161 : Blo 1766084 3978161 := bstep (se 2 (by rfl) ⟨1491810, by rfl⟩ : syracuseStep 3978161 = 2983621) B2983621
theorem B1766323 : Blo 1766084 1766323 := bstep (se 1 (by rfl) ⟨1324742, by rfl⟩ : syracuseStep 1766323 = 2649485) B2649485
theorem B1766339 : Blo 1766084 1766339 := bstep (se 1 (by rfl) ⟨1324754, by rfl⟩ : syracuseStep 1766339 = 2649509) B2649509
theorem B2651075 : Blo 1766084 2651075 := bstep (se 1 (by rfl) ⟨1988306, by rfl⟩ : syracuseStep 2651075 = 3976613) B3976613
theorem B3978179 : Blo 1766084 3978179 := bstep (se 1 (by rfl) ⟨2983634, by rfl⟩ : syracuseStep 3978179 = 5967269) B5967269
theorem B1766355 : Blo 1766084 1766355 := bstep (se 1 (by rfl) ⟨1324766, by rfl⟩ : syracuseStep 1766355 = 2649533) B2649533
theorem B1766371 : Blo 1766084 1766371 := bstep (se 1 (by rfl) ⟨1324778, by rfl⟩ : syracuseStep 1766371 = 2649557) B2649557
theorem B1987555 : Blo 1766084 1987555 := bstep (se 1 (by rfl) ⟨1490666, by rfl⟩ : syracuseStep 1987555 = 2981333) B2981333
theorem B2651105 : Blo 1766084 2651105 := bstep (se 2 (by rfl) ⟨994164, by rfl⟩ : syracuseStep 2651105 = 1988329) B1988329
theorem B1766387 : Blo 1766084 1766387 := bstep (se 1 (by rfl) ⟨1324790, by rfl⟩ : syracuseStep 1766387 = 2649581) B2649581
theorem B2651123 : Blo 1766084 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B1766403 : Blo 1766084 1766403 := bstep (se 1 (by rfl) ⟨1324802, by rfl⟩ : syracuseStep 1766403 = 2649605) B2649605
theorem B2651153 : Blo 1766084 2651153 := bstep (se 2 (by rfl) ⟨994182, by rfl⟩ : syracuseStep 2651153 = 1988365) B1988365
theorem B1766419 : Blo 1766084 1766419 := bstep (se 1 (by rfl) ⟨1324814, by rfl⟩ : syracuseStep 1766419 = 2649629) B2649629
theorem B1766435 : Blo 1766084 1766435 := bstep (se 1 (by rfl) ⟨1324826, by rfl⟩ : syracuseStep 1766435 = 2649653) B2649653
theorem B2651171 : Blo 1766084 2651171 := bstep (se 1 (by rfl) ⟨1988378, by rfl⟩ : syracuseStep 2651171 = 3976757) B3976757
theorem B1766451 : Blo 1766084 1766451 := bstep (se 1 (by rfl) ⟨1324838, by rfl⟩ : syracuseStep 1766451 = 2649677) B2649677
theorem B1766467 : Blo 1766084 1766467 := bstep (se 1 (by rfl) ⟨1324850, by rfl⟩ : syracuseStep 1766467 = 2649701) B2649701
theorem B2651201 : Blo 1766084 2651201 := bstep (se 2 (by rfl) ⟨994200, by rfl⟩ : syracuseStep 2651201 = 1988401) B1988401
theorem B6706253 : Blo 1766084 6706253 := bstep (se 3 (by rfl) ⟨1257422, by rfl⟩ : syracuseStep 6706253 = 2514845) B2514845
theorem B1766483 : Blo 1766084 1766483 := bstep (se 1 (by rfl) ⟨1324862, by rfl⟩ : syracuseStep 1766483 = 2649725) B2649725
theorem B2651219 : Blo 1766084 2651219 := bstep (se 1 (by rfl) ⟨1988414, by rfl⟩ : syracuseStep 2651219 = 3976829) B3976829
theorem B1766499 : Blo 1766084 1766499 := bstep (se 1 (by rfl) ⟨1324874, by rfl⟩ : syracuseStep 1766499 = 2649749) B2649749
theorem B2651249 : Blo 1766084 2651249 := bstep (se 2 (by rfl) ⟨994218, by rfl⟩ : syracuseStep 2651249 = 1988437) B1988437
theorem B1987699 : Blo 1766084 1987699 := bstep (se 1 (by rfl) ⟨1490774, by rfl⟩ : syracuseStep 1987699 = 2981549) B2981549
theorem B1766515 : Blo 1766084 1766515 := bstep (se 1 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 1766515 = 2649773) B2649773
theorem B1766531 : Blo 1766084 1766531 := bstep (se 1 (by rfl) ⟨1324898, by rfl⟩ : syracuseStep 1766531 = 2649797) B2649797
theorem B2651267 : Blo 1766084 2651267 := bstep (se 1 (by rfl) ⟨1988450, by rfl⟩ : syracuseStep 2651267 = 3976901) B3976901
theorem B1766547 : Blo 1766084 1766547 := bstep (se 1 (by rfl) ⟨1324910, by rfl⟩ : syracuseStep 1766547 = 2649821) B2649821
theorem B2651297 : Blo 1766084 2651297 := bstep (se 2 (by rfl) ⟨994236, by rfl⟩ : syracuseStep 2651297 = 1988473) B1988473
theorem B1766563 : Blo 1766084 1766563 := bstep (se 1 (by rfl) ⟨1324922, by rfl⟩ : syracuseStep 1766563 = 2649845) B2649845
theorem B1766579 : Blo 1766084 1766579 := bstep (se 1 (by rfl) ⟨1324934, by rfl⟩ : syracuseStep 1766579 = 2649869) B2649869
theorem B2651315 : Blo 1766084 2651315 := bstep (se 1 (by rfl) ⟨1988486, by rfl⟩ : syracuseStep 2651315 = 3976973) B3976973
theorem B1766595 : Blo 1766084 1766595 := bstep (se 1 (by rfl) ⟨1324946, by rfl⟩ : syracuseStep 1766595 = 2649893) B2649893
theorem B2651345 : Blo 1766084 2651345 := bstep (se 2 (by rfl) ⟨994254, by rfl⟩ : syracuseStep 2651345 = 1988509) B1988509
theorem B1766611 : Blo 1766084 1766611 := bstep (se 1 (by rfl) ⟨1324958, by rfl⟩ : syracuseStep 1766611 = 2649917) B2649917
theorem B1766627 : Blo 1766084 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B2651363 : Blo 1766084 2651363 := bstep (se 1 (by rfl) ⟨1988522, by rfl⟩ : syracuseStep 2651363 = 3977045) B3977045
theorem B1766643 : Blo 1766084 1766643 := bstep (se 1 (by rfl) ⟨1324982, by rfl⟩ : syracuseStep 1766643 = 2649965) B2649965
theorem B2651393 : Blo 1766084 2651393 := bstep (se 2 (by rfl) ⟨994272, by rfl⟩ : syracuseStep 2651393 = 1988545) B1988545
theorem B1766659 : Blo 1766084 1766659 := bstep (se 1 (by rfl) ⟨1324994, by rfl⟩ : syracuseStep 1766659 = 2649989) B2649989
theorem B1987843 : Blo 1766084 1987843 := bstep (se 1 (by rfl) ⟨1490882, by rfl⟩ : syracuseStep 1987843 = 2981765) B2981765
theorem B1766675 : Blo 1766084 1766675 := bstep (se 1 (by rfl) ⟨1325006, by rfl⟩ : syracuseStep 1766675 = 2650013) B2650013
theorem B2651411 : Blo 1766084 2651411 := bstep (se 1 (by rfl) ⟨1988558, by rfl⟩ : syracuseStep 2651411 = 3977117) B3977117
theorem B3355921 : Blo 1766084 3355921 := bstep (se 2 (by rfl) ⟨1258470, by rfl⟩ : syracuseStep 3355921 = 2516941) B2516941
theorem B1766691 : Blo 1766084 1766691 := bstep (se 1 (by rfl) ⟨1325018, by rfl⟩ : syracuseStep 1766691 = 2650037) B2650037
theorem B7550243 : Blo 1766084 7550243 := bstep (se 1 (by rfl) ⟨5662682, by rfl⟩ : syracuseStep 7550243 = 11325365) B11325365
theorem B5961005 : Blo 1766084 5961005 := bstep (se 3 (by rfl) ⟨1117688, by rfl⟩ : syracuseStep 5961005 = 2235377) B2235377
theorem B2651441 : Blo 1766084 2651441 := bstep (se 2 (by rfl) ⟨994290, by rfl⟩ : syracuseStep 2651441 = 1988581) B1988581
theorem B1766707 : Blo 1766084 1766707 := bstep (se 1 (by rfl) ⟨1325030, by rfl⟩ : syracuseStep 1766707 = 2650061) B2650061
theorem B1766723 : Blo 1766084 1766723 := bstep (se 1 (by rfl) ⟨1325042, by rfl⟩ : syracuseStep 1766723 = 2650085) B2650085
theorem B2651459 : Blo 1766084 2651459 := bstep (se 1 (by rfl) ⟨1988594, by rfl⟩ : syracuseStep 2651459 = 3977189) B3977189
theorem B1766739 : Blo 1766084 1766739 := bstep (se 1 (by rfl) ⟨1325054, by rfl⟩ : syracuseStep 1766739 = 2650109) B2650109
theorem B2651489 : Blo 1766084 2651489 := bstep (se 2 (by rfl) ⟨994308, by rfl⟩ : syracuseStep 2651489 = 1988617) B1988617
theorem B5961059 : Blo 1766084 5961059 := bstep (se 1 (by rfl) ⟨4470794, by rfl⟩ : syracuseStep 5961059 = 8941589) B8941589
theorem B1766755 : Blo 1766084 1766755 := bstep (se 1 (by rfl) ⟨1325066, by rfl⟩ : syracuseStep 1766755 = 2650133) B2650133
theorem B1766771 : Blo 1766084 1766771 := bstep (se 1 (by rfl) ⟨1325078, by rfl⟩ : syracuseStep 1766771 = 2650157) B2650157
theorem B2651507 : Blo 1766084 2651507 := bstep (se 1 (by rfl) ⟨1988630, by rfl⟩ : syracuseStep 2651507 = 3977261) B3977261
theorem B1766787 : Blo 1766084 1766787 := bstep (se 1 (by rfl) ⟨1325090, by rfl⟩ : syracuseStep 1766787 = 2650181) B2650181
theorem B2651537 : Blo 1766084 2651537 := bstep (se 2 (by rfl) ⟨994326, by rfl⟩ : syracuseStep 2651537 = 1988653) B1988653
theorem B1766803 : Blo 1766084 1766803 := bstep (se 1 (by rfl) ⟨1325102, by rfl⟩ : syracuseStep 1766803 = 2650205) B2650205
theorem B1987987 : Blo 1766084 1987987 := bstep (se 1 (by rfl) ⟨1490990, by rfl⟩ : syracuseStep 1987987 = 2981981) B2981981
theorem B8058275 : Blo 1766084 8058275 := bstep (se 1 (by rfl) ⟨6043706, by rfl⟩ : syracuseStep 8058275 = 12087413) B12087413
theorem B1766819 : Blo 1766084 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B2651555 : Blo 1766084 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B1766835 : Blo 1766084 1766835 := bstep (se 1 (by rfl) ⟨1325126, by rfl⟩ : syracuseStep 1766835 = 2650253) B2650253
theorem B2651585 : Blo 1766084 2651585 := bstep (se 2 (by rfl) ⟨994344, by rfl⟩ : syracuseStep 2651585 = 1988689) B1988689
theorem B1766851 : Blo 1766084 1766851 := bstep (se 1 (by rfl) ⟨1325138, by rfl⟩ : syracuseStep 1766851 = 2650277) B2650277
theorem B3773891 : Blo 1766084 3773891 := bstep (se 1 (by rfl) ⟨2830418, by rfl⟩ : syracuseStep 3773891 = 5660837) B5660837
theorem B1766867 : Blo 1766084 1766867 := bstep (se 1 (by rfl) ⟨1325150, by rfl⟩ : syracuseStep 1766867 = 2650301) B2650301
theorem B2651603 : Blo 1766084 2651603 := bstep (se 1 (by rfl) ⟨1988702, by rfl⟩ : syracuseStep 2651603 = 3977405) B3977405
theorem B1766883 : Blo 1766084 1766883 := bstep (se 1 (by rfl) ⟨1325162, by rfl⟩ : syracuseStep 1766883 = 2650325) B2650325
theorem B2651633 : Blo 1766084 2651633 := bstep (se 2 (by rfl) ⟨994362, by rfl⟩ : syracuseStep 2651633 = 1988725) B1988725
theorem B1766899 : Blo 1766084 1766899 := bstep (se 1 (by rfl) ⟨1325174, by rfl⟩ : syracuseStep 1766899 = 2650349) B2650349
theorem B1766915 : Blo 1766084 1766915 := bstep (se 1 (by rfl) ⟨1325186, by rfl⟩ : syracuseStep 1766915 = 2650373) B2650373
theorem B2651651 : Blo 1766084 2651651 := bstep (se 1 (by rfl) ⟨1988738, by rfl⟩ : syracuseStep 2651651 = 3977477) B3977477
theorem B1766931 : Blo 1766084 1766931 := bstep (se 1 (by rfl) ⟨1325198, by rfl⟩ : syracuseStep 1766931 = 2650397) B2650397
theorem B2651681 : Blo 1766084 2651681 := bstep (se 2 (by rfl) ⟨994380, by rfl⟩ : syracuseStep 2651681 = 1988761) B1988761
theorem B1766947 : Blo 1766084 1766947 := bstep (se 1 (by rfl) ⟨1325210, by rfl⟩ : syracuseStep 1766947 = 2650421) B2650421
theorem B1988131 : Blo 1766084 1988131 := bstep (se 1 (by rfl) ⟨1491098, by rfl⟩ : syracuseStep 1988131 = 2982197) B2982197
theorem B1766963 : Blo 1766084 1766963 := bstep (se 1 (by rfl) ⟨1325222, by rfl⟩ : syracuseStep 1766963 = 2650445) B2650445
theorem B2651699 : Blo 1766084 2651699 := bstep (se 1 (by rfl) ⟨1988774, by rfl⟩ : syracuseStep 2651699 = 3977549) B3977549
theorem B1766979 : Blo 1766084 1766979 := bstep (se 1 (by rfl) ⟨1325234, by rfl⟩ : syracuseStep 1766979 = 2650469) B2650469
theorem B10065485 : Blo 1766084 10065485 := bstep (se 3 (by rfl) ⟨1887278, by rfl⟩ : syracuseStep 10065485 = 3774557) B3774557
theorem B2651729 : Blo 1766084 2651729 := bstep (se 2 (by rfl) ⟨994398, by rfl⟩ : syracuseStep 2651729 = 1988797) B1988797
theorem B1766995 : Blo 1766084 1766995 := bstep (se 1 (by rfl) ⟨1325246, by rfl⟩ : syracuseStep 1766995 = 2650493) B2650493
theorem B2831969 : Blo 1766084 2831969 := bstep (se 2 (by rfl) ⟨1061988, by rfl⟩ : syracuseStep 2831969 = 2123977) B2123977
theorem B1767011 : Blo 1766084 1767011 := bstep (se 1 (by rfl) ⟨1325258, by rfl⟩ : syracuseStep 1767011 = 2650517) B2650517
theorem B2651747 : Blo 1766084 2651747 := bstep (se 1 (by rfl) ⟨1988810, by rfl⟩ : syracuseStep 2651747 = 3977621) B3977621
theorem B5961329 : Blo 1766084 5961329 := bstep (se 2 (by rfl) ⟨2235498, by rfl⟩ : syracuseStep 5961329 = 4470997) B4470997
theorem B40818289 : Blo 1766084 40818289 := bstep (se 2 (by rfl) ⟨15306858, by rfl⟩ : syracuseStep 40818289 = 30613717) B30613717
theorem B1767027 : Blo 1766084 1767027 := bstep (se 1 (by rfl) ⟨1325270, by rfl⟩ : syracuseStep 1767027 = 2650541) B2650541
theorem B2651777 : Blo 1766084 2651777 := bstep (se 2 (by rfl) ⟨994416, by rfl⟩ : syracuseStep 2651777 = 1988833) B1988833
theorem B1767043 : Blo 1766084 1767043 := bstep (se 1 (by rfl) ⟨1325282, by rfl⟩ : syracuseStep 1767043 = 2650565) B2650565
theorem B1767059 : Blo 1766084 1767059 := bstep (se 1 (by rfl) ⟨1325294, by rfl⟩ : syracuseStep 1767059 = 2650589) B2650589
theorem B2651795 : Blo 1766084 2651795 := bstep (se 1 (by rfl) ⟨1988846, by rfl⟩ : syracuseStep 2651795 = 3977693) B3977693
theorem B5658275 : Blo 1766084 5658275 := bstep (se 1 (by rfl) ⟨4243706, by rfl⟩ : syracuseStep 5658275 = 8487413) B8487413
theorem B7648931 : Blo 1766084 7648931 := bstep (se 1 (by rfl) ⟨5736698, by rfl⟩ : syracuseStep 7648931 = 11473397) B11473397
theorem B1767075 : Blo 1766084 1767075 := bstep (se 1 (by rfl) ⟨1325306, by rfl⟩ : syracuseStep 1767075 = 2650613) B2650613
theorem B2651825 : Blo 1766084 2651825 := bstep (se 2 (by rfl) ⟨994434, by rfl⟩ : syracuseStep 2651825 = 1988869) B1988869
theorem B1767091 : Blo 1766084 1767091 := bstep (se 1 (by rfl) ⟨1325318, by rfl⟩ : syracuseStep 1767091 = 2650637) B2650637
theorem B1988275 : Blo 1766084 1988275 := bstep (se 1 (by rfl) ⟨1491206, by rfl⟩ : syracuseStep 1988275 = 2982413) B2982413
theorem B1767107 : Blo 1766084 1767107 := bstep (se 1 (by rfl) ⟨1325330, by rfl⟩ : syracuseStep 1767107 = 2650661) B2650661
theorem B2651843 : Blo 1766084 2651843 := bstep (se 1 (by rfl) ⟨1988882, by rfl⟩ : syracuseStep 2651843 = 3977765) B3977765
theorem B5371597 : Blo 1766084 5371597 := bstep (se 3 (by rfl) ⟨1007174, by rfl⟩ : syracuseStep 5371597 = 2014349) B2014349
theorem B1767123 : Blo 1766084 1767123 := bstep (se 1 (by rfl) ⟨1325342, by rfl⟩ : syracuseStep 1767123 = 2650685) B2650685
theorem B2651873 : Blo 1766084 2651873 := bstep (se 2 (by rfl) ⟨994452, by rfl⟩ : syracuseStep 2651873 = 1988905) B1988905
theorem B1767139 : Blo 1766084 1767139 := bstep (se 1 (by rfl) ⟨1325354, by rfl⟩ : syracuseStep 1767139 = 2650709) B2650709
theorem B1767155 : Blo 1766084 1767155 := bstep (se 1 (by rfl) ⟨1325366, by rfl⟩ : syracuseStep 1767155 = 2650733) B2650733
theorem B2651891 : Blo 1766084 2651891 := bstep (se 1 (by rfl) ⟨1988918, by rfl⟩ : syracuseStep 2651891 = 3977837) B3977837
theorem B1767171 : Blo 1766084 1767171 := bstep (se 1 (by rfl) ⟨1325378, by rfl⟩ : syracuseStep 1767171 = 2650757) B2650757
theorem B2651921 : Blo 1766084 2651921 := bstep (se 2 (by rfl) ⟨994470, by rfl⟩ : syracuseStep 2651921 = 1988941) B1988941
theorem B1767187 : Blo 1766084 1767187 := bstep (se 1 (by rfl) ⟨1325390, by rfl⟩ : syracuseStep 1767187 = 2650781) B2650781
theorem B1767203 : Blo 1766084 1767203 := bstep (se 1 (by rfl) ⟨1325402, by rfl⟩ : syracuseStep 1767203 = 2650805) B2650805
theorem B2651939 : Blo 1766084 2651939 := bstep (se 1 (by rfl) ⟨1988954, by rfl⟩ : syracuseStep 2651939 = 3977909) B3977909
theorem B1767219 : Blo 1766084 1767219 := bstep (se 1 (by rfl) ⟨1325414, by rfl⟩ : syracuseStep 1767219 = 2650829) B2650829
theorem B2651969 : Blo 1766084 2651969 := bstep (se 2 (by rfl) ⟨994488, by rfl⟩ : syracuseStep 2651969 = 1988977) B1988977
theorem B1767235 : Blo 1766084 1767235 := bstep (se 1 (by rfl) ⟨1325426, by rfl⟩ : syracuseStep 1767235 = 2650853) B2650853
theorem B1988419 : Blo 1766084 1988419 := bstep (se 1 (by rfl) ⟨1491314, by rfl⟩ : syracuseStep 1988419 = 2982629) B2982629
theorem B7649101 : Blo 1766084 7649101 := bstep (se 3 (by rfl) ⟨1434206, by rfl⟩ : syracuseStep 7649101 = 2868413) B2868413
theorem B1767251 : Blo 1766084 1767251 := bstep (se 1 (by rfl) ⟨1325438, by rfl⟩ : syracuseStep 1767251 = 2650877) B2650877
theorem B2651987 : Blo 1766084 2651987 := bstep (se 1 (by rfl) ⟨1988990, by rfl⟩ : syracuseStep 2651987 = 3977981) B3977981
theorem B1767267 : Blo 1766084 1767267 := bstep (se 1 (by rfl) ⟨1325450, by rfl⟩ : syracuseStep 1767267 = 2650901) B2650901
theorem B2652017 : Blo 1766084 2652017 := bstep (se 2 (by rfl) ⟨994506, by rfl⟩ : syracuseStep 2652017 = 1989013) B1989013
theorem B1767283 : Blo 1766084 1767283 := bstep (se 1 (by rfl) ⟨1325462, by rfl⟩ : syracuseStep 1767283 = 2650925) B2650925
theorem B1767299 : Blo 1766084 1767299 := bstep (se 1 (by rfl) ⟨1325474, by rfl⟩ : syracuseStep 1767299 = 2650949) B2650949
theorem B2652035 : Blo 1766084 2652035 := bstep (se 1 (by rfl) ⟨1989026, by rfl⟩ : syracuseStep 2652035 = 3978053) B3978053
theorem B4470673 : Blo 1766084 4470673 := bstep (se 2 (by rfl) ⟨1676502, by rfl⟩ : syracuseStep 4470673 = 3353005) B3353005
theorem B1767315 : Blo 1766084 1767315 := bstep (se 1 (by rfl) ⟨1325486, by rfl⟩ : syracuseStep 1767315 = 2650973) B2650973
theorem B2652065 : Blo 1766084 2652065 := bstep (se 2 (by rfl) ⟨994524, by rfl⟩ : syracuseStep 2652065 = 1989049) B1989049
theorem B1767331 : Blo 1766084 1767331 := bstep (se 1 (by rfl) ⟨1325498, by rfl⟩ : syracuseStep 1767331 = 2650997) B2650997
theorem B1767347 : Blo 1766084 1767347 := bstep (se 1 (by rfl) ⟨1325510, by rfl⟩ : syracuseStep 1767347 = 2651021) B2651021
theorem B2652083 : Blo 1766084 2652083 := bstep (se 1 (by rfl) ⟨1989062, by rfl⟩ : syracuseStep 2652083 = 3978125) B3978125
theorem B1767363 : Blo 1766084 1767363 := bstep (se 1 (by rfl) ⟨1325522, by rfl⟩ : syracuseStep 1767363 = 2651045) B2651045
theorem B2652113 : Blo 1766084 2652113 := bstep (se 2 (by rfl) ⟨994542, by rfl⟩ : syracuseStep 2652113 = 1989085) B1989085
theorem B1767379 : Blo 1766084 1767379 := bstep (se 1 (by rfl) ⟨1325534, by rfl⟩ : syracuseStep 1767379 = 2651069) B2651069
theorem B1988563 : Blo 1766084 1988563 := bstep (se 1 (by rfl) ⟨1491422, by rfl⟩ : syracuseStep 1988563 = 2982845) B2982845
theorem B1767395 : Blo 1766084 1767395 := bstep (se 1 (by rfl) ⟨1325546, by rfl⟩ : syracuseStep 1767395 = 2651093) B2651093
theorem B1767411 : Blo 1766084 1767411 := bstep (se 1 (by rfl) ⟨1325558, by rfl⟩ : syracuseStep 1767411 = 2651117) B2651117
theorem B1767427 : Blo 1766084 1767427 := bstep (se 1 (by rfl) ⟨1325570, by rfl⟩ : syracuseStep 1767427 = 2651141) B2651141
theorem B1767443 : Blo 1766084 1767443 := bstep (se 1 (by rfl) ⟨1325582, by rfl⟩ : syracuseStep 1767443 = 2651165) B2651165
theorem B1767459 : Blo 1766084 1767459 := bstep (se 1 (by rfl) ⟨1325594, by rfl⟩ : syracuseStep 1767459 = 2651189) B2651189
theorem B1767475 : Blo 1766084 1767475 := bstep (se 1 (by rfl) ⟨1325606, by rfl⟩ : syracuseStep 1767475 = 2651213) B2651213
theorem B1767491 : Blo 1766084 1767491 := bstep (se 1 (by rfl) ⟨1325618, by rfl⟩ : syracuseStep 1767491 = 2651237) B2651237
theorem B11319365 : Blo 1766084 11319365 := bstep (se 4 (by rfl) ⟨1061190, by rfl⟩ : syracuseStep 11319365 = 2122381) B2122381
theorem B1767507 : Blo 1766084 1767507 := bstep (se 1 (by rfl) ⟨1325630, by rfl⟩ : syracuseStep 1767507 = 2651261) B2651261
theorem B1767523 : Blo 1766084 1767523 := bstep (se 1 (by rfl) ⟨1325642, by rfl⟩ : syracuseStep 1767523 = 2651285) B2651285
theorem B1988707 : Blo 1766084 1988707 := bstep (se 1 (by rfl) ⟨1491530, by rfl⟩ : syracuseStep 1988707 = 2983061) B2983061
theorem B1767539 : Blo 1766084 1767539 := bstep (se 1 (by rfl) ⟨1325654, by rfl⟩ : syracuseStep 1767539 = 2651309) B2651309
theorem B1767555 : Blo 1766084 1767555 := bstep (se 1 (by rfl) ⟨1325666, by rfl⟩ : syracuseStep 1767555 = 2651333) B2651333
theorem B5961869 : Blo 1766084 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B1767571 : Blo 1766084 1767571 := bstep (se 1 (by rfl) ⟨1325678, by rfl⟩ : syracuseStep 1767571 = 2651357) B2651357
theorem B4470947 : Blo 1766084 4470947 := bstep (se 1 (by rfl) ⟨3353210, by rfl⟩ : syracuseStep 4470947 = 6706421) B6706421
theorem B1767587 : Blo 1766084 1767587 := bstep (se 1 (by rfl) ⟨1325690, by rfl⟩ : syracuseStep 1767587 = 2651381) B2651381
theorem B1792163 : Blo 1766084 1792163 := bstep (se 1 (by rfl) ⟨1344122, by rfl⟩ : syracuseStep 1792163 = 2688245) B2688245
theorem B1767603 : Blo 1766084 1767603 := bstep (se 1 (by rfl) ⟨1325702, by rfl⟩ : syracuseStep 1767603 = 2651405) B2651405
theorem B5961923 : Blo 1766084 5961923 := bstep (se 1 (by rfl) ⟨4471442, by rfl⟩ : syracuseStep 5961923 = 8942885) B8942885
theorem B1767619 : Blo 1766084 1767619 := bstep (se 1 (by rfl) ⟨1325714, by rfl⟩ : syracuseStep 1767619 = 2651429) B2651429
theorem B1767635 : Blo 1766084 1767635 := bstep (se 1 (by rfl) ⟨1325726, by rfl⟩ : syracuseStep 1767635 = 2651453) B2651453
theorem B1767651 : Blo 1766084 1767651 := bstep (se 1 (by rfl) ⟨1325738, by rfl⟩ : syracuseStep 1767651 = 2651477) B2651477
theorem B8943857 : Blo 1766084 8943857 := bstep (se 2 (by rfl) ⟨3353946, by rfl⟩ : syracuseStep 8943857 = 6707893) B6707893
theorem B1767667 : Blo 1766084 1767667 := bstep (se 1 (by rfl) ⟨1325750, by rfl⟩ : syracuseStep 1767667 = 2651501) B2651501
theorem B1988851 : Blo 1766084 1988851 := bstep (se 1 (by rfl) ⟨1491638, by rfl⟩ : syracuseStep 1988851 = 2983277) B2983277
theorem B1767683 : Blo 1766084 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B1767699 : Blo 1766084 1767699 := bstep (se 1 (by rfl) ⟨1325774, by rfl⟩ : syracuseStep 1767699 = 2651549) B2651549
theorem B3774755 : Blo 1766084 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B1767715 : Blo 1766084 1767715 := bstep (se 1 (by rfl) ⟨1325786, by rfl⟩ : syracuseStep 1767715 = 2651573) B2651573
theorem B1767731 : Blo 1766084 1767731 := bstep (se 1 (by rfl) ⟨1325798, by rfl⟩ : syracuseStep 1767731 = 2651597) B2651597
theorem B1767747 : Blo 1766084 1767747 := bstep (se 1 (by rfl) ⟨1325810, by rfl⟩ : syracuseStep 1767747 = 2651621) B2651621
theorem B1767763 : Blo 1766084 1767763 := bstep (se 1 (by rfl) ⟨1325822, by rfl⟩ : syracuseStep 1767763 = 2651645) B2651645
theorem B4471139 : Blo 1766084 4471139 := bstep (se 1 (by rfl) ⟨3353354, by rfl⟩ : syracuseStep 4471139 = 6706709) B6706709
theorem B1767779 : Blo 1766084 1767779 := bstep (se 1 (by rfl) ⟨1325834, by rfl⟩ : syracuseStep 1767779 = 2651669) B2651669
theorem B1767795 : Blo 1766084 1767795 := bstep (se 1 (by rfl) ⟨1325846, by rfl⟩ : syracuseStep 1767795 = 2651693) B2651693
theorem B2152819 : Blo 1766084 2152819 := bstep (se 1 (by rfl) ⟨1614614, by rfl⟩ : syracuseStep 2152819 = 3229229) B3229229
theorem B1767811 : Blo 1766084 1767811 := bstep (se 1 (by rfl) ⟨1325858, by rfl⟩ : syracuseStep 1767811 = 2651717) B2651717
theorem B1988995 : Blo 1766084 1988995 := bstep (se 1 (by rfl) ⟨1491746, by rfl⟩ : syracuseStep 1988995 = 2983493) B2983493
theorem B3774865 : Blo 1766084 3774865 := bstep (se 2 (by rfl) ⟨1415574, by rfl⟩ : syracuseStep 3774865 = 2831149) B2831149
theorem B1767827 : Blo 1766084 1767827 := bstep (se 1 (by rfl) ⟨1325870, by rfl⟩ : syracuseStep 1767827 = 2651741) B2651741
theorem B1767843 : Blo 1766084 1767843 := bstep (se 1 (by rfl) ⟨1325882, by rfl⟩ : syracuseStep 1767843 = 2651765) B2651765
theorem B2980273 : Blo 1766084 2980273 := bstep (se 2 (by rfl) ⟨1117602, by rfl⟩ : syracuseStep 2980273 = 2235205) B2235205
theorem B1767859 : Blo 1766084 1767859 := bstep (se 1 (by rfl) ⟨1325894, by rfl⟩ : syracuseStep 1767859 = 2651789) B2651789
theorem B1767875 : Blo 1766084 1767875 := bstep (se 1 (by rfl) ⟨1325906, by rfl⟩ : syracuseStep 1767875 = 2651813) B2651813
theorem B5962193 : Blo 1766084 5962193 := bstep (se 2 (by rfl) ⟨2235822, by rfl⟩ : syracuseStep 5962193 = 4471645) B4471645
theorem B2980307 : Blo 1766084 2980307 := bstep (se 1 (by rfl) ⟨2235230, by rfl⟩ : syracuseStep 2980307 = 4470461) B4470461
theorem B1767891 : Blo 1766084 1767891 := bstep (se 1 (by rfl) ⟨1325918, by rfl⟩ : syracuseStep 1767891 = 2651837) B2651837
theorem B1767907 : Blo 1766084 1767907 := bstep (se 1 (by rfl) ⟨1325930, by rfl⟩ : syracuseStep 1767907 = 2651861) B2651861
theorem B1767923 : Blo 1766084 1767923 := bstep (se 1 (by rfl) ⟨1325942, by rfl⟩ : syracuseStep 1767923 = 2651885) B2651885
theorem B1767939 : Blo 1766084 1767939 := bstep (se 1 (by rfl) ⟨1325954, by rfl⟩ : syracuseStep 1767939 = 2651909) B2651909
theorem B1767955 : Blo 1766084 1767955 := bstep (se 1 (by rfl) ⟨1325966, by rfl⟩ : syracuseStep 1767955 = 2651933) B2651933
theorem B42990101 : Blo 1766084 42990101 := bstep (se 6 (by rfl) ⟨1007580, by rfl⟩ : syracuseStep 42990101 = 2015161) B2015161
theorem B1767971 : Blo 1766084 1767971 := bstep (se 1 (by rfl) ⟨1325978, by rfl⟩ : syracuseStep 1767971 = 2651957) B2651957
theorem B1767987 : Blo 1766084 1767987 := bstep (se 1 (by rfl) ⟨1325990, by rfl⟩ : syracuseStep 1767987 = 2651981) B2651981
theorem B1768003 : Blo 1766084 1768003 := bstep (se 1 (by rfl) ⟨1326002, by rfl⟩ : syracuseStep 1768003 = 2652005) B2652005
theorem B2980435 : Blo 1766084 2980435 := bstep (se 1 (by rfl) ⟨2235326, by rfl⟩ : syracuseStep 2980435 = 4470653) B4470653
theorem B1768019 : Blo 1766084 1768019 := bstep (se 1 (by rfl) ⟨1326014, by rfl⟩ : syracuseStep 1768019 = 2652029) B2652029
theorem B1768035 : Blo 1766084 1768035 := bstep (se 1 (by rfl) ⟨1326026, by rfl⟩ : syracuseStep 1768035 = 2652053) B2652053
theorem B1768051 : Blo 1766084 1768051 := bstep (se 1 (by rfl) ⟨1326038, by rfl⟩ : syracuseStep 1768051 = 2652077) B2652077
theorem B1768067 : Blo 1766084 1768067 := bstep (se 1 (by rfl) ⟨1326050, by rfl⟩ : syracuseStep 1768067 = 2652101) B2652101
theorem B1768083 : Blo 1766084 1768083 := bstep (se 1 (by rfl) ⟨1326062, by rfl⟩ : syracuseStep 1768083 = 2652125) B2652125
theorem B14326469 : Blo 1766084 14326469 := bstep (se 4 (by rfl) ⟨1343106, by rfl⟩ : syracuseStep 14326469 = 2686213) B2686213
theorem B29055685 : Blo 1766084 29055685 := bstep (se 4 (by rfl) ⟨2723970, by rfl⟩ : syracuseStep 29055685 = 5447941) B5447941
theorem B2980577 : Blo 1766084 2980577 := bstep (se 2 (by rfl) ⟨1117716, by rfl⟩ : syracuseStep 2980577 = 2235433) B2235433
theorem B15088355 : Blo 1766084 15088355 := bstep (se 1 (by rfl) ⟨11316266, by rfl⟩ : syracuseStep 15088355 = 22632533) B22632533
theorem B13597411 : Blo 1766084 13597411 := bstep (se 1 (by rfl) ⟨10198058, by rfl⟩ : syracuseStep 13597411 = 20396117) B20396117
theorem B3185411 : Blo 1766084 3185411 := bstep (se 1 (by rfl) ⟨2389058, by rfl⟩ : syracuseStep 3185411 = 4778117) B4778117
theorem B2980705 : Blo 1766084 2980705 := bstep (se 2 (by rfl) ⟨1117764, by rfl⟩ : syracuseStep 2980705 = 2235529) B2235529
theorem B2685793 : Blo 1766084 2685793 := bstep (se 2 (by rfl) ⟨1007172, by rfl⟩ : syracuseStep 2685793 = 2014345) B2014345
theorem B25475953 : Blo 1766084 25475953 := bstep (se 2 (by rfl) ⟨9553482, by rfl⟩ : syracuseStep 25475953 = 19106965) B19106965
theorem B2980739 : Blo 1766084 2980739 := bstep (se 1 (by rfl) ⟨2235554, by rfl⟩ : syracuseStep 2980739 = 4471109) B4471109
theorem B5962733 : Blo 1766084 5962733 := bstep (se 3 (by rfl) ⟨1118012, by rfl⟩ : syracuseStep 5962733 = 2236025) B2236025
theorem B3398659 : Blo 1766084 3398659 := bstep (se 1 (by rfl) ⟨2548994, by rfl⟩ : syracuseStep 3398659 = 5097989) B5097989
theorem B2980867 : Blo 1766084 2980867 := bstep (se 1 (by rfl) ⟨2235650, by rfl⟩ : syracuseStep 2980867 = 4471301) B4471301
theorem B5962787 : Blo 1766084 5962787 := bstep (se 1 (by rfl) ⟨4472090, by rfl⟩ : syracuseStep 5962787 = 8944181) B8944181
theorem B6708365 : Blo 1766084 6708365 := bstep (se 3 (by rfl) ⟨1257818, by rfl⟩ : syracuseStep 6708365 = 2515637) B2515637
theorem B2981009 : Blo 1766084 2981009 := bstep (se 2 (by rfl) ⟨1117878, by rfl⟩ : syracuseStep 2981009 = 2235757) B2235757
theorem B2235539 : Blo 1766084 2235539 := bstep (se 1 (by rfl) ⟨1676654, by rfl⟩ : syracuseStep 2235539 = 3353309) B3353309
theorem B10747085 : Blo 1766084 10747085 := bstep (se 3 (by rfl) ⟨2015078, by rfl⟩ : syracuseStep 10747085 = 4030157) B4030157
theorem B3316945 : Blo 1766084 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B40795363 : Blo 1766084 40795363 := bstep (se 1 (by rfl) ⟨30596522, by rfl⟩ : syracuseStep 40795363 = 61193045) B61193045
theorem B5373155 : Blo 1766084 5373155 := bstep (se 1 (by rfl) ⟨4029866, by rfl⟩ : syracuseStep 5373155 = 8059733) B8059733
theorem B2981137 : Blo 1766084 2981137 := bstep (se 2 (by rfl) ⟨1117926, by rfl⟩ : syracuseStep 2981137 = 2235853) B2235853
theorem B4472081 : Blo 1766084 4472081 := bstep (se 2 (by rfl) ⟨1677030, by rfl⟩ : syracuseStep 4472081 = 3354061) B3354061
theorem B5963057 : Blo 1766084 5963057 := bstep (se 2 (by rfl) ⟨2236146, by rfl⟩ : syracuseStep 5963057 = 4472293) B4472293
theorem B2981171 : Blo 1766084 2981171 := bstep (se 1 (by rfl) ⟨2235878, by rfl⟩ : syracuseStep 2981171 = 4471757) B4471757
theorem B4472131 : Blo 1766084 4472131 := bstep (se 1 (by rfl) ⟨3354098, by rfl⟩ : syracuseStep 4472131 = 6708197) B6708197
theorem B2981299 : Blo 1766084 2981299 := bstep (se 1 (by rfl) ⟨2235974, by rfl⟩ : syracuseStep 2981299 = 4471949) B4471949
theorem B4472273 : Blo 1766084 4472273 := bstep (se 2 (by rfl) ⟨1677102, by rfl⟩ : syracuseStep 4472273 = 3354205) B3354205
theorem B5029361 : Blo 1766084 5029361 := bstep (se 2 (by rfl) ⟨1886010, by rfl⟩ : syracuseStep 5029361 = 3772021) B3772021
theorem B2981441 : Blo 1766084 2981441 := bstep (se 2 (by rfl) ⟨1118040, by rfl⟩ : syracuseStep 2981441 = 2236081) B2236081
theorem B3063361 : Blo 1766084 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B2686529 : Blo 1766084 2686529 := bstep (se 2 (by rfl) ⟨1007448, by rfl⟩ : syracuseStep 2686529 = 2014897) B2014897
theorem B8945315 : Blo 1766084 8945315 := bstep (se 1 (by rfl) ⟨6708986, by rfl⟩ : syracuseStep 8945315 = 13417973) B13417973
theorem B6045347 : Blo 1766084 6045347 := bstep (se 1 (by rfl) ⟨4534010, by rfl⟩ : syracuseStep 6045347 = 9068021) B9068021
theorem B5029553 : Blo 1766084 5029553 := bstep (se 2 (by rfl) ⟨1886082, by rfl⟩ : syracuseStep 5029553 = 3772165) B3772165
theorem B2981569 : Blo 1766084 2981569 := bstep (se 2 (by rfl) ⟨1118088, by rfl⟩ : syracuseStep 2981569 = 2236177) B2236177
theorem B2981603 : Blo 1766084 2981603 := bstep (se 1 (by rfl) ⟨2236202, by rfl⟩ : syracuseStep 2981603 = 4472405) B4472405
theorem B27959011 : Blo 1766084 27959011 := bstep (se 1 (by rfl) ⟨20969258, by rfl⟩ : syracuseStep 27959011 = 41938517) B41938517
theorem B5660401 : Blo 1766084 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B5963597 : Blo 1766084 5963597 := bstep (se 3 (by rfl) ⟨1118174, by rfl⟩ : syracuseStep 5963597 = 2236349) B2236349
theorem B2236243 : Blo 1766084 2236243 := bstep (se 1 (by rfl) ⟨1677182, by rfl⟩ : syracuseStep 2236243 = 3354365) B3354365
theorem B2981731 : Blo 1766084 2981731 := bstep (se 1 (by rfl) ⟨2236298, by rfl⟩ : syracuseStep 2981731 = 4472597) B4472597
theorem B2514817 : Blo 1766084 2514817 := bstep (se 2 (by rfl) ⟨943056, by rfl⟩ : syracuseStep 2514817 = 1886113) B1886113
theorem B5963651 : Blo 1766084 5963651 := bstep (se 1 (by rfl) ⟨4472738, by rfl⟩ : syracuseStep 5963651 = 8945477) B8945477
theorem B10059653 : Blo 1766084 10059653 := bstep (se 4 (by rfl) ⟨943092, by rfl⟩ : syracuseStep 10059653 = 1886185) B1886185
theorem B6709169 : Blo 1766084 6709169 := bstep (se 2 (by rfl) ⟨2515938, by rfl⟩ : syracuseStep 6709169 = 5031877) B5031877
theorem B2236339 : Blo 1766084 2236339 := bstep (se 1 (by rfl) ⟨1677254, by rfl⟩ : syracuseStep 2236339 = 3354509) B3354509
theorem B11321315 : Blo 1766084 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B2981873 : Blo 1766084 2981873 := bstep (se 2 (by rfl) ⟨1118202, by rfl⟩ : syracuseStep 2981873 = 2236405) B2236405
theorem B2686961 : Blo 1766084 2686961 := bstep (se 2 (by rfl) ⟨1007610, by rfl⟩ : syracuseStep 2686961 = 2015221) B2015221
theorem B6709337 : Blo 1766084 6709337 := bstep (se 2 (by rfl) ⟨2516001, by rfl⟩ : syracuseStep 6709337 = 5032003) B5032003
theorem B4472921 : Blo 1766084 4472921 := bstep (se 2 (by rfl) ⟨1677345, by rfl⟩ : syracuseStep 4472921 = 3354691) B3354691
theorem B16973975 : Blo 1766084 16973975 := bstep (se 1 (by rfl) ⟨12730481, by rfl⟩ : syracuseStep 16973975 = 25460963) B25460963
theorem B2236567 : Blo 1766084 2236567 := bstep (se 1 (by rfl) ⟨1677425, by rfl⟩ : syracuseStep 2236567 = 3354851) B3354851
theorem B5964083 : Blo 1766084 5964083 := bstep (se 1 (by rfl) ⟨4473062, by rfl⟩ : syracuseStep 5964083 = 8946125) B8946125
theorem B6799691 : Blo 1766084 6799691 := bstep (se 1 (by rfl) ⟨5099768, by rfl⟩ : syracuseStep 6799691 = 10199537) B10199537
theorem B5030237 : Blo 1766084 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B58114421 : Blo 1766084 58114421 := bstep (se 5 (by rfl) ⟨2724113, by rfl⟩ : syracuseStep 58114421 = 5448227) B5448227
theorem B6709655 : Blo 1766084 6709655 := bstep (se 1 (by rfl) ⟨5032241, by rfl⟩ : syracuseStep 6709655 = 10064483) B10064483
theorem B2982359 : Blo 1766084 2982359 := bstep (se 1 (by rfl) ⟨2236769, by rfl⟩ : syracuseStep 2982359 = 4473539) B4473539
theorem B16114211 : Blo 1766084 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B3973697 : Blo 1766084 3973697 := bstep (se 2 (by rfl) ⟨1490136, by rfl⟩ : syracuseStep 3973697 = 2980273) B2980273
theorem B5964353 : Blo 1766084 5964353 := bstep (se 2 (by rfl) ⟨2236632, by rfl⟩ : syracuseStep 5964353 = 4473265) B4473265
theorem B2982487 : Blo 1766084 2982487 := bstep (se 1 (by rfl) ⟨2236865, by rfl⟩ : syracuseStep 2982487 = 4473731) B4473731
theorem B14328413 : Blo 1766084 14328413 := bstep (se 3 (by rfl) ⟨2686577, by rfl⟩ : syracuseStep 14328413 = 5373155) B5373155
theorem B5030579 : Blo 1766084 5030579 := bstep (se 1 (by rfl) ⟨3772934, by rfl⟩ : syracuseStep 5030579 = 7545869) B7545869
theorem B23012045 : Blo 1766084 23012045 := bstep (se 3 (by rfl) ⟨4314758, by rfl⟩ : syracuseStep 23012045 = 8629517) B8629517
theorem B8946449 : Blo 1766084 8946449 := bstep (se 2 (by rfl) ⟨3354918, by rfl⟩ : syracuseStep 8946449 = 6709837) B6709837
theorem B3973913 : Blo 1766084 3973913 := bstep (se 2 (by rfl) ⟨1490217, by rfl⟩ : syracuseStep 3973913 = 2980435) B2980435
theorem B3974003 : Blo 1766084 3974003 := bstep (se 1 (by rfl) ⟨2980502, by rfl⟩ : syracuseStep 3974003 = 5961005) B5961005
theorem B3974039 : Blo 1766084 3974039 := bstep (se 1 (by rfl) ⟨2980529, by rfl⟩ : syracuseStep 3974039 = 5961059) B5961059
theorem B9552791 : Blo 1766084 9552791 := bstep (se 1 (by rfl) ⟨7164593, by rfl⟩ : syracuseStep 9552791 = 14329187) B14329187
theorem B4473751 : Blo 1766084 4473751 := bstep (se 1 (by rfl) ⟨3355313, by rfl⟩ : syracuseStep 4473751 = 6710627) B6710627
theorem B38740913 : Blo 1766084 38740913 := bstep (se 2 (by rfl) ⟨14527842, by rfl⟩ : syracuseStep 38740913 = 29055685) B29055685
theorem B8946611 : Blo 1766084 8946611 := bstep (se 1 (by rfl) ⟨6709958, by rfl⟩ : syracuseStep 8946611 = 13419917) B13419917
theorem B4244417 : Blo 1766084 4244417 := bstep (se 2 (by rfl) ⟨1591656, by rfl⟩ : syracuseStep 4244417 = 3183313) B3183313
theorem B18129881 : Blo 1766084 18129881 := bstep (se 2 (by rfl) ⟨6798705, by rfl⟩ : syracuseStep 18129881 = 13597411) B13597411
theorem B6710323 : Blo 1766084 6710323 := bstep (se 1 (by rfl) ⟨5032742, by rfl⟩ : syracuseStep 6710323 = 10065485) B10065485
theorem B3974219 : Blo 1766084 3974219 := bstep (se 1 (by rfl) ⟨2980664, by rfl⟩ : syracuseStep 3974219 = 5961329) B5961329
theorem B5964893 : Blo 1766084 5964893 := bstep (se 3 (by rfl) ⟨1118417, by rfl⟩ : syracuseStep 5964893 = 2236835) B2236835
theorem B3974273 : Blo 1766084 3974273 := bstep (se 2 (by rfl) ⟨1490352, by rfl⟩ : syracuseStep 3974273 = 2980705) B2980705
theorem B3581057 : Blo 1766084 3581057 := bstep (se 2 (by rfl) ⟨1342896, by rfl⟩ : syracuseStep 3581057 = 2685793) B2685793
theorem B2983115 : Blo 1766084 2983115 := bstep (se 1 (by rfl) ⟨2237336, by rfl⟩ : syracuseStep 2983115 = 4474673) B4474673
theorem B5375297 : Blo 1766084 5375297 := bstep (se 2 (by rfl) ⟨2015736, by rfl⟩ : syracuseStep 5375297 = 4031473) B4031473
theorem B4474187 : Blo 1766084 4474187 := bstep (se 1 (by rfl) ⟨3355640, by rfl⟩ : syracuseStep 4474187 = 6711281) B6711281
theorem B2983243 : Blo 1766084 2983243 := bstep (se 1 (by rfl) ⟨2237432, by rfl⟩ : syracuseStep 2983243 = 4474865) B4474865
theorem B3974489 : Blo 1766084 3974489 := bstep (se 2 (by rfl) ⟨1490433, by rfl⟩ : syracuseStep 3974489 = 2980867) B2980867
theorem B3974579 : Blo 1766084 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B3974615 : Blo 1766084 3974615 := bstep (se 1 (by rfl) ⟨2980961, by rfl⟩ : syracuseStep 3974615 = 5961923) B5961923
theorem B2983385 : Blo 1766084 2983385 := bstep (se 2 (by rfl) ⟨1118769, by rfl⟩ : syracuseStep 2983385 = 2237539) B2237539
theorem B2516503 : Blo 1766084 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B2983513 : Blo 1766084 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B3974795 : Blo 1766084 3974795 := bstep (se 1 (by rfl) ⟨2981096, by rfl⟩ : syracuseStep 3974795 = 5962193) B5962193
theorem B3974849 : Blo 1766084 3974849 := bstep (se 2 (by rfl) ⟨1490568, by rfl⟩ : syracuseStep 3974849 = 2981137) B2981137
theorem B4474561 : Blo 1766084 4474561 := bstep (se 2 (by rfl) ⟨1677960, by rfl⟩ : syracuseStep 4474561 = 3355921) B3355921
theorem B13412141 : Blo 1766084 13412141 := bstep (se 3 (by rfl) ⟨2514776, by rfl⟩ : syracuseStep 13412141 = 5029553) B5029553
theorem B5662553 : Blo 1766084 5662553 := bstep (se 2 (by rfl) ⟨2123457, by rfl⟩ : syracuseStep 5662553 = 4246915) B4246915
theorem B3975065 : Blo 1766084 3975065 := bstep (se 2 (by rfl) ⟨1490649, by rfl⟩ : syracuseStep 3975065 = 2981299) B2981299
theorem B32671667 : Blo 1766084 32671667 := bstep (se 1 (by rfl) ⟨24503750, by rfl⟩ : syracuseStep 32671667 = 49007501) B49007501
theorem B3975155 : Blo 1766084 3975155 := bstep (se 1 (by rfl) ⟨2981366, by rfl⟩ : syracuseStep 3975155 = 5962733) B5962733
theorem B3975191 : Blo 1766084 3975191 := bstep (se 1 (by rfl) ⟨2981393, by rfl⟩ : syracuseStep 3975191 = 5962787) B5962787
theorem B6367405 : Blo 1766084 6367405 := bstep (se 3 (by rfl) ⟨1193888, by rfl⟩ : syracuseStep 6367405 = 2387777) B2387777
theorem B3975371 : Blo 1766084 3975371 := bstep (se 1 (by rfl) ⟨2981528, by rfl⟩ : syracuseStep 3975371 = 5963057) B5963057
theorem B5966027 : Blo 1766084 5966027 := bstep (se 1 (by rfl) ⟨4474520, by rfl⟩ : syracuseStep 5966027 = 8949041) B8949041
theorem B3975425 : Blo 1766084 3975425 := bstep (se 2 (by rfl) ⟨1490784, by rfl⟩ : syracuseStep 3975425 = 2981569) B2981569
theorem B7162129 : Blo 1766084 7162129 := bstep (se 2 (by rfl) ⟨2685798, by rfl⟩ : syracuseStep 7162129 = 5371597) B5371597
theorem B6711569 : Blo 1766084 6711569 := bstep (se 2 (by rfl) ⟨2516838, by rfl⟩ : syracuseStep 6711569 = 5033677) B5033677
theorem B4475159 : Blo 1766084 4475159 := bstep (se 1 (by rfl) ⟨3356369, by rfl⟩ : syracuseStep 4475159 = 6712739) B6712739
theorem B7547201 : Blo 1766084 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B3352907 : Blo 1766084 3352907 := bstep (se 1 (by rfl) ⟨2514680, by rfl⟩ : syracuseStep 3352907 = 5029361) B5029361
theorem B3975641 : Blo 1766084 3975641 := bstep (se 2 (by rfl) ⟨1490865, by rfl⟩ : syracuseStep 3975641 = 2981731) B2981731
theorem B5966297 : Blo 1766084 5966297 := bstep (se 2 (by rfl) ⟨2237361, by rfl⟩ : syracuseStep 5966297 = 4474723) B4474723
theorem B3353089 : Blo 1766084 3353089 := bstep (se 2 (by rfl) ⟨1257408, by rfl⟩ : syracuseStep 3353089 = 2514817) B2514817
theorem B3975731 : Blo 1766084 3975731 := bstep (se 1 (by rfl) ⟨2981798, by rfl⟩ : syracuseStep 3975731 = 5963597) B5963597
theorem B5663297 : Blo 1766084 5663297 := bstep (se 2 (by rfl) ⟨2123736, by rfl⟩ : syracuseStep 5663297 = 4247473) B4247473
theorem B3975767 : Blo 1766084 3975767 := bstep (se 1 (by rfl) ⟨2981825, by rfl⟩ : syracuseStep 3975767 = 5963651) B5963651
theorem B7547543 : Blo 1766084 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B3975947 : Blo 1766084 3975947 := bstep (se 1 (by rfl) ⟨2981960, by rfl⟩ : syracuseStep 3975947 = 5963921) B5963921
theorem B20130605 : Blo 1766084 20130605 := bstep (se 3 (by rfl) ⟨3774488, by rfl⟩ : syracuseStep 20130605 = 7548977) B7548977
theorem B3976001 : Blo 1766084 3976001 := bstep (se 2 (by rfl) ⟨1491000, by rfl⟩ : syracuseStep 3976001 = 2982001) B2982001
theorem B3582785 : Blo 1766084 3582785 := bstep (se 2 (by rfl) ⟨1343544, by rfl⟩ : syracuseStep 3582785 = 2687089) B2687089
theorem B8948555 : Blo 1766084 8948555 := bstep (se 1 (by rfl) ⟨6711416, by rfl⟩ : syracuseStep 8948555 = 13422833) B13422833
theorem B12741553 : Blo 1766084 12741553 := bstep (se 2 (by rfl) ⟨4778082, by rfl⟩ : syracuseStep 12741553 = 9556165) B9556165
theorem B3353537 : Blo 1766084 3353537 := bstep (se 2 (by rfl) ⟨1257576, by rfl⟩ : syracuseStep 3353537 = 2515153) B2515153
theorem B6712267 : Blo 1766084 6712267 := bstep (se 1 (by rfl) ⟨5034200, by rfl⟩ : syracuseStep 6712267 = 10068401) B10068401
theorem B5032925 : Blo 1766084 5032925 := bstep (se 3 (by rfl) ⟨943673, by rfl⟩ : syracuseStep 5032925 = 1887347) B1887347
theorem B2386955 : Blo 1766084 2386955 := bstep (se 1 (by rfl) ⟨1790216, by rfl⟩ : syracuseStep 2386955 = 3580433) B3580433
theorem B3976217 : Blo 1766084 3976217 := bstep (se 2 (by rfl) ⟨1491081, by rfl⟩ : syracuseStep 3976217 = 2982163) B2982163
theorem B4779101 : Blo 1766084 4779101 := bstep (se 3 (by rfl) ⟨896081, by rfl⟩ : syracuseStep 4779101 = 1792163) B1792163
theorem B3976307 : Blo 1766084 3976307 := bstep (se 1 (by rfl) ⟨2982230, by rfl⟩ : syracuseStep 3976307 = 5964461) B5964461
theorem B2649227 : Blo 1766084 2649227 := bstep (se 1 (by rfl) ⟨1986920, by rfl⟩ : syracuseStep 2649227 = 3973841) B3973841
theorem B2649239 : Blo 1766084 2649239 := bstep (se 1 (by rfl) ⟨1986929, by rfl⟩ : syracuseStep 2649239 = 3973859) B3973859
theorem B3976343 : Blo 1766084 3976343 := bstep (se 1 (by rfl) ⟨2982257, by rfl⟩ : syracuseStep 3976343 = 5964515) B5964515
theorem B2870425 : Blo 1766084 2870425 := bstep (se 2 (by rfl) ⟨1076409, by rfl⟩ : syracuseStep 2870425 = 2152819) B2152819
theorem B5966999 : Blo 1766084 5966999 := bstep (se 1 (by rfl) ⟨4475249, by rfl⟩ : syracuseStep 5966999 = 8950499) B8950499
theorem B5033153 : Blo 1766084 5033153 := bstep (se 2 (by rfl) ⟨1887432, by rfl⟩ : syracuseStep 5033153 = 3774865) B3774865
theorem B28658893 : Blo 1766084 28658893 := bstep (se 3 (by rfl) ⟨5373542, by rfl⟩ : syracuseStep 28658893 = 10747085) B10747085
theorem B2649305 : Blo 1766084 2649305 := bstep (se 2 (by rfl) ⟨993489, by rfl⟩ : syracuseStep 2649305 = 1986979) B1986979
theorem B6712541 : Blo 1766084 6712541 := bstep (se 3 (by rfl) ⟨1258601, by rfl⟩ : syracuseStep 6712541 = 2517203) B2517203
theorem B3353879 : Blo 1766084 3353879 := bstep (se 1 (by rfl) ⟨2515409, by rfl⟩ : syracuseStep 3353879 = 5030819) B5030819
theorem B2649419 : Blo 1766084 2649419 := bstep (se 1 (by rfl) ⟨1987064, by rfl⟩ : syracuseStep 2649419 = 3974129) B3974129
theorem B3976523 : Blo 1766084 3976523 := bstep (se 1 (by rfl) ⟨2982392, by rfl⟩ : syracuseStep 3976523 = 5964785) B5964785
theorem B2649431 : Blo 1766084 2649431 := bstep (se 1 (by rfl) ⟨1987073, by rfl⟩ : syracuseStep 2649431 = 3974147) B3974147
theorem B3976577 : Blo 1766084 3976577 := bstep (se 2 (by rfl) ⟨1491216, by rfl⟩ : syracuseStep 3976577 = 2982433) B2982433
theorem B2649497 : Blo 1766084 2649497 := bstep (se 2 (by rfl) ⟨993561, by rfl⟩ : syracuseStep 2649497 = 1987123) B1987123
theorem B2649611 : Blo 1766084 2649611 := bstep (se 1 (by rfl) ⟨1987208, by rfl⟩ : syracuseStep 2649611 = 3974417) B3974417
theorem B2649623 : Blo 1766084 2649623 := bstep (se 1 (by rfl) ⟨1987217, by rfl⟩ : syracuseStep 2649623 = 3974435) B3974435
theorem B5033495 : Blo 1766084 5033495 := bstep (se 1 (by rfl) ⟨3775121, by rfl⟩ : syracuseStep 5033495 = 7550243) B7550243
theorem B2649689 : Blo 1766084 2649689 := bstep (se 2 (by rfl) ⟨993633, by rfl⟩ : syracuseStep 2649689 = 1987267) B1987267
theorem B3976793 : Blo 1766084 3976793 := bstep (se 2 (by rfl) ⟨1491297, by rfl⟩ : syracuseStep 3976793 = 2982595) B2982595
theorem B12906161 : Blo 1766084 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B3976883 : Blo 1766084 3976883 := bstep (se 1 (by rfl) ⟨2982662, by rfl⟩ : syracuseStep 3976883 = 5965325) B5965325
theorem B3772097 : Blo 1766084 3772097 := bstep (se 2 (by rfl) ⟨1414536, by rfl⟩ : syracuseStep 3772097 = 2829073) B2829073
theorem B2649803 : Blo 1766084 2649803 := bstep (se 1 (by rfl) ⟨1987352, by rfl⟩ : syracuseStep 2649803 = 3974705) B3974705
theorem B2649815 : Blo 1766084 2649815 := bstep (se 1 (by rfl) ⟨1987361, by rfl⟩ : syracuseStep 2649815 = 3974723) B3974723
theorem B3976919 : Blo 1766084 3976919 := bstep (se 1 (by rfl) ⟨2982689, by rfl⟩ : syracuseStep 3976919 = 5965379) B5965379
theorem B3772183 : Blo 1766084 3772183 := bstep (se 1 (by rfl) ⟨2829137, by rfl⟩ : syracuseStep 3772183 = 5658275) B5658275
theorem B5099287 : Blo 1766084 5099287 := bstep (se 1 (by rfl) ⟨3824465, by rfl⟩ : syracuseStep 5099287 = 7648931) B7648931
theorem B2649881 : Blo 1766084 2649881 := bstep (se 2 (by rfl) ⟨993705, by rfl⟩ : syracuseStep 2649881 = 1987411) B1987411
theorem B33967937 : Blo 1766084 33967937 := bstep (se 2 (by rfl) ⟨12737976, by rfl⟩ : syracuseStep 33967937 = 25475953) B25475953
theorem B10063709 : Blo 1766084 10063709 := bstep (se 3 (by rfl) ⟨1886945, by rfl⟩ : syracuseStep 10063709 = 3773891) B3773891
theorem B149114725 : Blo 1766084 149114725 := bstep (se 4 (by rfl) ⟨13979505, by rfl⟩ : syracuseStep 149114725 = 27959011) B27959011
theorem B2649995 : Blo 1766084 2649995 := bstep (se 1 (by rfl) ⟨1987496, by rfl⟩ : syracuseStep 2649995 = 3974993) B3974993
theorem B3977099 : Blo 1766084 3977099 := bstep (se 1 (by rfl) ⟨2982824, by rfl⟩ : syracuseStep 3977099 = 5965649) B5965649
theorem B2650007 : Blo 1766084 2650007 := bstep (se 1 (by rfl) ⟨1987505, by rfl⟩ : syracuseStep 2650007 = 3975011) B3975011
theorem B3354547 : Blo 1766084 3354547 := bstep (se 1 (by rfl) ⟨2515910, by rfl⟩ : syracuseStep 3354547 = 5031821) B5031821
theorem B3977153 : Blo 1766084 3977153 := bstep (se 2 (by rfl) ⟨1491432, by rfl⟩ : syracuseStep 3977153 = 2982865) B2982865
theorem B2650073 : Blo 1766084 2650073 := bstep (se 2 (by rfl) ⟨993777, by rfl⟩ : syracuseStep 2650073 = 1987555) B1987555
theorem B2830297 : Blo 1766084 2830297 := bstep (se 2 (by rfl) ⟨1061361, by rfl⟩ : syracuseStep 2830297 = 2122723) B2122723
theorem B2650187 : Blo 1766084 2650187 := bstep (se 1 (by rfl) ⟨1987640, by rfl⟩ : syracuseStep 2650187 = 3975281) B3975281
theorem B2650199 : Blo 1766084 2650199 := bstep (se 1 (by rfl) ⟨1987649, by rfl⟩ : syracuseStep 2650199 = 3975299) B3975299
theorem B2650265 : Blo 1766084 2650265 := bstep (se 2 (by rfl) ⟨993849, by rfl⟩ : syracuseStep 2650265 = 1987699) B1987699
theorem B3977369 : Blo 1766084 3977369 := bstep (se 2 (by rfl) ⟨1491513, by rfl⟩ : syracuseStep 3977369 = 2983027) B2983027
theorem B12095705 : Blo 1766084 12095705 := bstep (se 2 (by rfl) ⟨4535889, by rfl⟩ : syracuseStep 12095705 = 9071779) B9071779
theorem B3977459 : Blo 1766084 3977459 := bstep (se 1 (by rfl) ⟨2983094, by rfl⟩ : syracuseStep 3977459 = 5966189) B5966189
theorem B2650379 : Blo 1766084 2650379 := bstep (se 1 (by rfl) ⟨1987784, by rfl⟩ : syracuseStep 2650379 = 3975569) B3975569
theorem B2650391 : Blo 1766084 2650391 := bstep (se 1 (by rfl) ⟨1987793, by rfl⟩ : syracuseStep 2650391 = 3975587) B3975587
theorem B3977495 : Blo 1766084 3977495 := bstep (se 1 (by rfl) ⟨2983121, by rfl⟩ : syracuseStep 3977495 = 5966243) B5966243
theorem B1986871 : Blo 1766084 1986871 := bstep (se 1 (by rfl) ⟨1490153, by rfl⟩ : syracuseStep 1986871 = 2980307) B2980307
theorem B2650457 : Blo 1766084 2650457 := bstep (se 2 (by rfl) ⟨993921, by rfl⟩ : syracuseStep 2650457 = 1987843) B1987843
theorem B4305241 : Blo 1766084 4305241 := bstep (se 2 (by rfl) ⟨1614465, by rfl⟩ : syracuseStep 4305241 = 3228931) B3228931
theorem B28660067 : Blo 1766084 28660067 := bstep (se 1 (by rfl) ⟨21495050, by rfl⟩ : syracuseStep 28660067 = 42990101) B42990101
theorem B3354995 : Blo 1766084 3354995 := bstep (se 1 (by rfl) ⟨2516246, by rfl⟩ : syracuseStep 3354995 = 5032493) B5032493
theorem B3355033 : Blo 1766084 3355033 := bstep (se 2 (by rfl) ⟨1258137, by rfl⟩ : syracuseStep 3355033 = 2516275) B2516275
theorem B2650571 : Blo 1766084 2650571 := bstep (se 1 (by rfl) ⟨1987928, by rfl⟩ : syracuseStep 2650571 = 3975857) B3975857
theorem B3977675 : Blo 1766084 3977675 := bstep (se 1 (by rfl) ⟨2983256, by rfl⟩ : syracuseStep 3977675 = 5966513) B5966513
theorem B2650583 : Blo 1766084 2650583 := bstep (se 1 (by rfl) ⟨1987937, by rfl⟩ : syracuseStep 2650583 = 3975875) B3975875
theorem B1987051 : Blo 1766084 1987051 := bstep (se 1 (by rfl) ⟨1490288, by rfl⟩ : syracuseStep 1987051 = 2980577) B2980577
theorem B3977729 : Blo 1766084 3977729 := bstep (se 2 (by rfl) ⟨1491648, by rfl⟩ : syracuseStep 3977729 = 2983297) B2983297
theorem B2650649 : Blo 1766084 2650649 := bstep (se 2 (by rfl) ⟨993993, by rfl⟩ : syracuseStep 2650649 = 1987987) B1987987
theorem B8950337 : Blo 1766084 8950337 := bstep (se 2 (by rfl) ⟨3356376, by rfl⟩ : syracuseStep 8950337 = 6712753) B6712753
theorem B18133579 : Blo 1766084 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B1987159 : Blo 1766084 1987159 := bstep (se 1 (by rfl) ⟨1490369, by rfl⟩ : syracuseStep 1987159 = 2980739) B2980739
theorem B2650763 : Blo 1766084 2650763 := bstep (se 1 (by rfl) ⟨1988072, by rfl⟩ : syracuseStep 2650763 = 3976145) B3976145
theorem B2650775 : Blo 1766084 2650775 := bstep (se 1 (by rfl) ⟨1988081, by rfl⟩ : syracuseStep 2650775 = 3976163) B3976163
theorem B2388631 : Blo 1766084 2388631 := bstep (se 1 (by rfl) ⟨1791473, by rfl⟩ : syracuseStep 2388631 = 3582947) B3582947
theorem B1766091 : Blo 1766084 1766091 := bstep (se 1 (by rfl) ⟨1324568, by rfl⟩ : syracuseStep 1766091 = 2649137) B2649137
theorem B1766103 : Blo 1766084 1766103 := bstep (se 1 (by rfl) ⟨1324577, by rfl⟩ : syracuseStep 1766103 = 2649155) B2649155
theorem B2650841 : Blo 1766084 2650841 := bstep (se 2 (by rfl) ⟨994065, by rfl⟩ : syracuseStep 2650841 = 1988131) B1988131
theorem B7549661 : Blo 1766084 7549661 := bstep (se 3 (by rfl) ⟨1415561, by rfl⟩ : syracuseStep 7549661 = 2831123) B2831123
theorem B3977945 : Blo 1766084 3977945 := bstep (se 2 (by rfl) ⟨1491729, by rfl⟩ : syracuseStep 3977945 = 2983459) B2983459
theorem B1766123 : Blo 1766084 1766123 := bstep (se 1 (by rfl) ⟨1324592, by rfl⟩ : syracuseStep 1766123 = 2649185) B2649185
theorem B1766135 : Blo 1766084 1766135 := bstep (se 1 (by rfl) ⟨1324601, by rfl⟩ : syracuseStep 1766135 = 2649203) B2649203
theorem B4084481 : Blo 1766084 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B1766155 : Blo 1766084 1766155 := bstep (se 1 (by rfl) ⟨1324616, by rfl⟩ : syracuseStep 1766155 = 2649233) B2649233
theorem B1987339 : Blo 1766084 1987339 := bstep (se 1 (by rfl) ⟨1490504, by rfl⟩ : syracuseStep 1987339 = 2981009) B2981009
theorem B1766167 : Blo 1766084 1766167 := bstep (se 1 (by rfl) ⟨1324625, by rfl⟩ : syracuseStep 1766167 = 2649251) B2649251
theorem B1766187 : Blo 1766084 1766187 := bstep (se 1 (by rfl) ⟨1324640, by rfl⟩ : syracuseStep 1766187 = 2649281) B2649281
theorem B1766199 : Blo 1766084 1766199 := bstep (se 1 (by rfl) ⟨1324649, by rfl⟩ : syracuseStep 1766199 = 2649299) B2649299
theorem B3978035 : Blo 1766084 3978035 := bstep (se 1 (by rfl) ⟨2983526, by rfl⟩ : syracuseStep 3978035 = 5967053) B5967053
theorem B54424385 : Blo 1766084 54424385 := bstep (se 2 (by rfl) ⟨20409144, by rfl⟩ : syracuseStep 54424385 = 40818289) B40818289
theorem B1766219 : Blo 1766084 1766219 := bstep (se 1 (by rfl) ⟨1324664, by rfl⟩ : syracuseStep 1766219 = 2649329) B2649329
theorem B2650955 : Blo 1766084 2650955 := bstep (se 1 (by rfl) ⟨1988216, by rfl⟩ : syracuseStep 2650955 = 3976433) B3976433
theorem B1766231 : Blo 1766084 1766231 := bstep (se 1 (by rfl) ⟨1324673, by rfl⟩ : syracuseStep 1766231 = 2649347) B2649347
theorem B2650967 : Blo 1766084 2650967 := bstep (se 1 (by rfl) ⟨1988225, by rfl⟩ : syracuseStep 2650967 = 3976451) B3976451
theorem B3355481 : Blo 1766084 3355481 := bstep (se 2 (by rfl) ⟨1258305, by rfl⟩ : syracuseStep 3355481 = 2516611) B2516611
theorem B3978071 : Blo 1766084 3978071 := bstep (se 1 (by rfl) ⟨2983553, by rfl⟩ : syracuseStep 3978071 = 5967107) B5967107
theorem B1766251 : Blo 1766084 1766251 := bstep (se 1 (by rfl) ⟨1324688, by rfl⟩ : syracuseStep 1766251 = 2649377) B2649377
theorem B1766263 : Blo 1766084 1766263 := bstep (se 1 (by rfl) ⟨1324697, by rfl⟩ : syracuseStep 1766263 = 2649395) B2649395
theorem B1987447 : Blo 1766084 1987447 := bstep (se 1 (by rfl) ⟨1490585, by rfl⟩ : syracuseStep 1987447 = 2981171) B2981171
theorem B1766283 : Blo 1766084 1766283 := bstep (se 1 (by rfl) ⟨1324712, by rfl⟩ : syracuseStep 1766283 = 2649425) B2649425
theorem B1766295 : Blo 1766084 1766295 := bstep (se 1 (by rfl) ⟨1324721, by rfl⟩ : syracuseStep 1766295 = 2649443) B2649443
theorem B2651033 : Blo 1766084 2651033 := bstep (se 2 (by rfl) ⟨994137, by rfl⟩ : syracuseStep 2651033 = 1988275) B1988275
theorem B2724761 : Blo 1766084 2724761 := bstep (se 2 (by rfl) ⟨1021785, by rfl⟩ : syracuseStep 2724761 = 2043571) B2043571
theorem B1766315 : Blo 1766084 1766315 := bstep (se 1 (by rfl) ⟨1324736, by rfl⟩ : syracuseStep 1766315 = 2649473) B2649473
theorem B5960627 : Blo 1766084 5960627 := bstep (se 1 (by rfl) ⟨4470470, by rfl⟩ : syracuseStep 5960627 = 8940941) B8940941
theorem B1766327 : Blo 1766084 1766327 := bstep (se 1 (by rfl) ⟨1324745, by rfl⟩ : syracuseStep 1766327 = 2649491) B2649491
theorem B1766347 : Blo 1766084 1766347 := bstep (se 1 (by rfl) ⟨1324760, by rfl⟩ : syracuseStep 1766347 = 2649521) B2649521
theorem B1766359 : Blo 1766084 1766359 := bstep (se 1 (by rfl) ⟨1324769, by rfl⟩ : syracuseStep 1766359 = 2649539) B2649539
theorem B1766379 : Blo 1766084 1766379 := bstep (se 1 (by rfl) ⟨1324784, by rfl⟩ : syracuseStep 1766379 = 2649569) B2649569
theorem B1766391 : Blo 1766084 1766391 := bstep (se 1 (by rfl) ⟨1324793, by rfl⟩ : syracuseStep 1766391 = 2649587) B2649587
theorem B1766411 : Blo 1766084 1766411 := bstep (se 1 (by rfl) ⟨1324808, by rfl⟩ : syracuseStep 1766411 = 2649617) B2649617
theorem B2651147 : Blo 1766084 2651147 := bstep (se 1 (by rfl) ⟨1988360, by rfl⟩ : syracuseStep 2651147 = 3976721) B3976721
theorem B7549969 : Blo 1766084 7549969 := bstep (se 2 (by rfl) ⟨2831238, by rfl⟩ : syracuseStep 7549969 = 5662477) B5662477
theorem B1766423 : Blo 1766084 1766423 := bstep (se 1 (by rfl) ⟨1324817, by rfl⟩ : syracuseStep 1766423 = 2649635) B2649635
theorem B2651159 : Blo 1766084 2651159 := bstep (se 1 (by rfl) ⟨1988369, by rfl⟩ : syracuseStep 2651159 = 3976739) B3976739
theorem B1766443 : Blo 1766084 1766443 := bstep (se 1 (by rfl) ⟨1324832, by rfl⟩ : syracuseStep 1766443 = 2649665) B2649665
theorem B1987627 : Blo 1766084 1987627 := bstep (se 1 (by rfl) ⟨1490720, by rfl⟩ : syracuseStep 1987627 = 2981441) B2981441
theorem B1791019 : Blo 1766084 1791019 := bstep (se 1 (by rfl) ⟨1343264, by rfl⟩ : syracuseStep 1791019 = 2686529) B2686529
theorem B7550003 : Blo 1766084 7550003 := bstep (se 1 (by rfl) ⟨5662502, by rfl⟩ : syracuseStep 7550003 = 11325005) B11325005
theorem B1766455 : Blo 1766084 1766455 := bstep (se 1 (by rfl) ⟨1324841, by rfl⟩ : syracuseStep 1766455 = 2649683) B2649683
theorem B11473985 : Blo 1766084 11473985 := bstep (se 2 (by rfl) ⟨4302744, by rfl⟩ : syracuseStep 11473985 = 8605489) B8605489
theorem B1766475 : Blo 1766084 1766475 := bstep (se 1 (by rfl) ⟨1324856, by rfl⟩ : syracuseStep 1766475 = 2649713) B2649713
theorem B1766487 : Blo 1766084 1766487 := bstep (se 1 (by rfl) ⟨1324865, by rfl⟩ : syracuseStep 1766487 = 2649731) B2649731
theorem B2651225 : Blo 1766084 2651225 := bstep (se 2 (by rfl) ⟨994209, by rfl⟩ : syracuseStep 2651225 = 1988419) B1988419
theorem B1766507 : Blo 1766084 1766507 := bstep (se 1 (by rfl) ⟨1324880, by rfl⟩ : syracuseStep 1766507 = 2649761) B2649761
theorem B1766519 : Blo 1766084 1766519 := bstep (se 1 (by rfl) ⟨1324889, by rfl⟩ : syracuseStep 1766519 = 2649779) B2649779
theorem B8942723 : Blo 1766084 8942723 := bstep (se 1 (by rfl) ⟨6707042, by rfl⟩ : syracuseStep 8942723 = 13414085) B13414085
theorem B1766539 : Blo 1766084 1766539 := bstep (se 1 (by rfl) ⟨1324904, by rfl⟩ : syracuseStep 1766539 = 2649809) B2649809
theorem B1766551 : Blo 1766084 1766551 := bstep (se 1 (by rfl) ⟨1324913, by rfl⟩ : syracuseStep 1766551 = 2649827) B2649827
theorem B1987735 : Blo 1766084 1987735 := bstep (se 1 (by rfl) ⟨1490801, by rfl⟩ : syracuseStep 1987735 = 2981603) B2981603
theorem B1766571 : Blo 1766084 1766571 := bstep (se 1 (by rfl) ⟨1324928, by rfl⟩ : syracuseStep 1766571 = 2649857) B2649857
theorem B1766583 : Blo 1766084 1766583 := bstep (se 1 (by rfl) ⟨1324937, by rfl⟩ : syracuseStep 1766583 = 2649875) B2649875
theorem B5960897 : Blo 1766084 5960897 := bstep (se 2 (by rfl) ⟨2235336, by rfl⟩ : syracuseStep 5960897 = 4470673) B4470673
theorem B4535489 : Blo 1766084 4535489 := bstep (se 2 (by rfl) ⟨1700808, by rfl⟩ : syracuseStep 4535489 = 3401617) B3401617
theorem B1766603 : Blo 1766084 1766603 := bstep (se 1 (by rfl) ⟨1324952, by rfl⟩ : syracuseStep 1766603 = 2649905) B2649905
theorem B2651339 : Blo 1766084 2651339 := bstep (se 1 (by rfl) ⟨1988504, by rfl⟩ : syracuseStep 2651339 = 3977009) B3977009
theorem B1766615 : Blo 1766084 1766615 := bstep (se 1 (by rfl) ⟨1324961, by rfl⟩ : syracuseStep 1766615 = 2649923) B2649923
theorem B2651351 : Blo 1766084 2651351 := bstep (se 1 (by rfl) ⟨1988513, by rfl⟩ : syracuseStep 2651351 = 3977027) B3977027
theorem B1766635 : Blo 1766084 1766635 := bstep (se 1 (by rfl) ⟨1324976, by rfl⟩ : syracuseStep 1766635 = 2649953) B2649953
theorem B1766647 : Blo 1766084 1766647 := bstep (se 1 (by rfl) ⟨1324985, by rfl⟩ : syracuseStep 1766647 = 2649971) B2649971
theorem B6706435 : Blo 1766084 6706435 := bstep (se 1 (by rfl) ⟨5029826, by rfl⟩ : syracuseStep 6706435 = 10059653) B10059653
theorem B1766667 : Blo 1766084 1766667 := bstep (se 1 (by rfl) ⟨1325000, by rfl⟩ : syracuseStep 1766667 = 2650001) B2650001
theorem B11318545 : Blo 1766084 11318545 := bstep (se 2 (by rfl) ⟨4244454, by rfl⟩ : syracuseStep 11318545 = 8488909) B8488909
theorem B1766679 : Blo 1766084 1766679 := bstep (se 1 (by rfl) ⟨1325009, by rfl⟩ : syracuseStep 1766679 = 2650019) B2650019
theorem B2651417 : Blo 1766084 2651417 := bstep (se 2 (by rfl) ⟨994281, by rfl⟩ : syracuseStep 2651417 = 1988563) B1988563
theorem B1766699 : Blo 1766084 1766699 := bstep (se 1 (by rfl) ⟨1325024, by rfl⟩ : syracuseStep 1766699 = 2650049) B2650049
theorem B1766711 : Blo 1766084 1766711 := bstep (se 1 (by rfl) ⟨1325033, by rfl⟩ : syracuseStep 1766711 = 2650067) B2650067
theorem B1766731 : Blo 1766084 1766731 := bstep (se 1 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 1766731 = 2650097) B2650097
theorem B1987915 : Blo 1766084 1987915 := bstep (se 1 (by rfl) ⟨1490936, by rfl⟩ : syracuseStep 1987915 = 2981873) B2981873
theorem B1791307 : Blo 1766084 1791307 := bstep (se 1 (by rfl) ⟨1343480, by rfl⟩ : syracuseStep 1791307 = 2686961) B2686961
theorem B1766743 : Blo 1766084 1766743 := bstep (se 1 (by rfl) ⟨1325057, by rfl⟩ : syracuseStep 1766743 = 2650115) B2650115
theorem B18126181 : Blo 1766084 18126181 := bstep (se 4 (by rfl) ⟨1699329, by rfl⟩ : syracuseStep 18126181 = 3398659) B3398659
theorem B1766763 : Blo 1766084 1766763 := bstep (se 1 (by rfl) ⟨1325072, by rfl⟩ : syracuseStep 1766763 = 2650145) B2650145
theorem B1766775 : Blo 1766084 1766775 := bstep (se 1 (by rfl) ⟨1325081, by rfl⟩ : syracuseStep 1766775 = 2650163) B2650163
theorem B1766795 : Blo 1766084 1766795 := bstep (se 1 (by rfl) ⟨1325096, by rfl⟩ : syracuseStep 1766795 = 2650193) B2650193
theorem B2651531 : Blo 1766084 2651531 := bstep (se 1 (by rfl) ⟨1988648, by rfl⟩ : syracuseStep 2651531 = 3977297) B3977297
theorem B1766807 : Blo 1766084 1766807 := bstep (se 1 (by rfl) ⟨1325105, by rfl⟩ : syracuseStep 1766807 = 2650211) B2650211
theorem B2651543 : Blo 1766084 2651543 := bstep (se 1 (by rfl) ⟨1988657, by rfl⟩ : syracuseStep 2651543 = 3977315) B3977315
theorem B1766827 : Blo 1766084 1766827 := bstep (se 1 (by rfl) ⟨1325120, by rfl⟩ : syracuseStep 1766827 = 2650241) B2650241
theorem B1766839 : Blo 1766084 1766839 := bstep (se 1 (by rfl) ⟨1325129, by rfl⟩ : syracuseStep 1766839 = 2650259) B2650259
theorem B1988023 : Blo 1766084 1988023 := bstep (se 1 (by rfl) ⟨1491017, by rfl⟩ : syracuseStep 1988023 = 2982035) B2982035
theorem B1766859 : Blo 1766084 1766859 := bstep (se 1 (by rfl) ⟨1325144, by rfl⟩ : syracuseStep 1766859 = 2650289) B2650289
theorem B1766871 : Blo 1766084 1766871 := bstep (se 1 (by rfl) ⟨1325153, by rfl⟩ : syracuseStep 1766871 = 2650307) B2650307
theorem B2651609 : Blo 1766084 2651609 := bstep (se 2 (by rfl) ⟨994353, by rfl⟩ : syracuseStep 2651609 = 1988707) B1988707
theorem B1766891 : Blo 1766084 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B1766903 : Blo 1766084 1766903 := bstep (se 1 (by rfl) ⟨1325177, by rfl⟩ : syracuseStep 1766903 = 2650355) B2650355
theorem B1766923 : Blo 1766084 1766923 := bstep (se 1 (by rfl) ⟨1325192, by rfl⟩ : syracuseStep 1766923 = 2650385) B2650385
theorem B30184973 : Blo 1766084 30184973 := bstep (se 3 (by rfl) ⟨5659682, by rfl⟩ : syracuseStep 30184973 = 11319365) B11319365
theorem B1766935 : Blo 1766084 1766935 := bstep (se 1 (by rfl) ⟨1325201, by rfl⟩ : syracuseStep 1766935 = 2650403) B2650403
theorem B1766955 : Blo 1766084 1766955 := bstep (se 1 (by rfl) ⟨1325216, by rfl⟩ : syracuseStep 1766955 = 2650433) B2650433
theorem B6706739 : Blo 1766084 6706739 := bstep (se 1 (by rfl) ⟨5030054, by rfl⟩ : syracuseStep 6706739 = 10060109) B10060109
theorem B1766967 : Blo 1766084 1766967 := bstep (se 1 (by rfl) ⟨1325225, by rfl⟩ : syracuseStep 1766967 = 2650451) B2650451
theorem B3356225 : Blo 1766084 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B1766987 : Blo 1766084 1766987 := bstep (se 1 (by rfl) ⟨1325240, by rfl⟩ : syracuseStep 1766987 = 2650481) B2650481
theorem B2651723 : Blo 1766084 2651723 := bstep (se 1 (by rfl) ⟨1988792, by rfl⟩ : syracuseStep 2651723 = 3977585) B3977585
theorem B1766999 : Blo 1766084 1766999 := bstep (se 1 (by rfl) ⟨1325249, by rfl⟩ : syracuseStep 1766999 = 2650499) B2650499
theorem B2651735 : Blo 1766084 2651735 := bstep (se 1 (by rfl) ⟨1988801, by rfl⟩ : syracuseStep 2651735 = 3977603) B3977603
theorem B13416029 : Blo 1766084 13416029 := bstep (se 3 (by rfl) ⟨2515505, by rfl⟩ : syracuseStep 13416029 = 5031011) B5031011
theorem B1767019 : Blo 1766084 1767019 := bstep (se 1 (by rfl) ⟨1325264, by rfl⟩ : syracuseStep 1767019 = 2650529) B2650529
theorem B1988203 : Blo 1766084 1988203 := bstep (se 1 (by rfl) ⟨1491152, by rfl⟩ : syracuseStep 1988203 = 2982305) B2982305
theorem B1767031 : Blo 1766084 1767031 := bstep (se 1 (by rfl) ⟨1325273, by rfl⟩ : syracuseStep 1767031 = 2650547) B2650547
theorem B12744323 : Blo 1766084 12744323 := bstep (se 1 (by rfl) ⟨9558242, by rfl⟩ : syracuseStep 12744323 = 19116485) B19116485
theorem B1767051 : Blo 1766084 1767051 := bstep (se 1 (by rfl) ⟨1325288, by rfl⟩ : syracuseStep 1767051 = 2650577) B2650577
theorem B1767063 : Blo 1766084 1767063 := bstep (se 1 (by rfl) ⟨1325297, by rfl⟩ : syracuseStep 1767063 = 2650595) B2650595
theorem B2651801 : Blo 1766084 2651801 := bstep (se 2 (by rfl) ⟨994425, by rfl⟩ : syracuseStep 2651801 = 1988851) B1988851
theorem B1767083 : Blo 1766084 1767083 := bstep (se 1 (by rfl) ⟨1325312, by rfl⟩ : syracuseStep 1767083 = 2650625) B2650625
theorem B1767095 : Blo 1766084 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B1767115 : Blo 1766084 1767115 := bstep (se 1 (by rfl) ⟨1325336, by rfl⟩ : syracuseStep 1767115 = 2650673) B2650673
theorem B1767127 : Blo 1766084 1767127 := bstep (se 1 (by rfl) ⟨1325345, by rfl⟩ : syracuseStep 1767127 = 2650691) B2650691
theorem B1988311 : Blo 1766084 1988311 := bstep (se 1 (by rfl) ⟨1491233, by rfl⟩ : syracuseStep 1988311 = 2982467) B2982467
theorem B5961437 : Blo 1766084 5961437 := bstep (se 3 (by rfl) ⟨1117769, by rfl⟩ : syracuseStep 5961437 = 2235539) B2235539
theorem B1767147 : Blo 1766084 1767147 := bstep (se 1 (by rfl) ⟨1325360, by rfl⟩ : syracuseStep 1767147 = 2650721) B2650721
theorem B1767159 : Blo 1766084 1767159 := bstep (se 1 (by rfl) ⟨1325369, by rfl⟩ : syracuseStep 1767159 = 2650739) B2650739
theorem B22656773 : Blo 1766084 22656773 := bstep (se 4 (by rfl) ⟨2124072, by rfl⟩ : syracuseStep 22656773 = 4248145) B4248145
theorem B1767179 : Blo 1766084 1767179 := bstep (se 1 (by rfl) ⟨1325384, by rfl⟩ : syracuseStep 1767179 = 2650769) B2650769
theorem B2651915 : Blo 1766084 2651915 := bstep (se 1 (by rfl) ⟨1988936, by rfl⟩ : syracuseStep 2651915 = 3977873) B3977873
theorem B1767191 : Blo 1766084 1767191 := bstep (se 1 (by rfl) ⟨1325393, by rfl⟩ : syracuseStep 1767191 = 2650787) B2650787
theorem B2651927 : Blo 1766084 2651927 := bstep (se 1 (by rfl) ⟨1988945, by rfl⟩ : syracuseStep 2651927 = 3977891) B3977891
theorem B3184409 : Blo 1766084 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B1767211 : Blo 1766084 1767211 := bstep (se 1 (by rfl) ⟨1325408, by rfl⟩ : syracuseStep 1767211 = 2650817) B2650817
theorem B1767223 : Blo 1766084 1767223 := bstep (se 1 (by rfl) ⟨1325417, by rfl⟩ : syracuseStep 1767223 = 2650835) B2650835
theorem B1767243 : Blo 1766084 1767243 := bstep (se 1 (by rfl) ⟨1325432, by rfl⟩ : syracuseStep 1767243 = 2650865) B2650865
theorem B3356491 : Blo 1766084 3356491 := bstep (se 1 (by rfl) ⟨2517368, by rfl⟩ : syracuseStep 3356491 = 5034737) B5034737
theorem B1767255 : Blo 1766084 1767255 := bstep (se 1 (by rfl) ⟨1325441, by rfl⟩ : syracuseStep 1767255 = 2650883) B2650883
theorem B2651993 : Blo 1766084 2651993 := bstep (se 2 (by rfl) ⟨994497, by rfl⟩ : syracuseStep 2651993 = 1988995) B1988995
theorem B81573733 : Blo 1766084 81573733 := bstep (se 4 (by rfl) ⟨7647537, by rfl⟩ : syracuseStep 81573733 = 15295075) B15295075
theorem B1767275 : Blo 1766084 1767275 := bstep (se 1 (by rfl) ⟨1325456, by rfl⟩ : syracuseStep 1767275 = 2650913) B2650913
theorem B1767287 : Blo 1766084 1767287 := bstep (se 1 (by rfl) ⟨1325465, by rfl⟩ : syracuseStep 1767287 = 2650931) B2650931
theorem B11327363 : Blo 1766084 11327363 := bstep (se 1 (by rfl) ⟨8495522, by rfl⟩ : syracuseStep 11327363 = 16991045) B16991045
theorem B1767307 : Blo 1766084 1767307 := bstep (se 1 (by rfl) ⟨1325480, by rfl⟩ : syracuseStep 1767307 = 2650961) B2650961
theorem B1988491 : Blo 1766084 1988491 := bstep (se 1 (by rfl) ⟨1491368, by rfl⟩ : syracuseStep 1988491 = 2982737) B2982737
theorem B1767319 : Blo 1766084 1767319 := bstep (se 1 (by rfl) ⟨1325489, by rfl⟩ : syracuseStep 1767319 = 2650979) B2650979
theorem B1767339 : Blo 1766084 1767339 := bstep (se 1 (by rfl) ⟨1325504, by rfl⟩ : syracuseStep 1767339 = 2651009) B2651009
theorem B1767351 : Blo 1766084 1767351 := bstep (se 1 (by rfl) ⟨1325513, by rfl⟩ : syracuseStep 1767351 = 2651027) B2651027
theorem B1767371 : Blo 1766084 1767371 := bstep (se 1 (by rfl) ⟨1325528, by rfl⟩ : syracuseStep 1767371 = 2651057) B2651057
theorem B2652107 : Blo 1766084 2652107 := bstep (se 1 (by rfl) ⟨1989080, by rfl⟩ : syracuseStep 2652107 = 3978161) B3978161
theorem B1767383 : Blo 1766084 1767383 := bstep (se 1 (by rfl) ⟨1325537, by rfl⟩ : syracuseStep 1767383 = 2651075) B2651075
theorem B2652119 : Blo 1766084 2652119 := bstep (se 1 (by rfl) ⟨1989089, by rfl⟩ : syracuseStep 2652119 = 3978179) B3978179
theorem B1767403 : Blo 1766084 1767403 := bstep (se 1 (by rfl) ⟨1325552, by rfl⟩ : syracuseStep 1767403 = 2651105) B2651105
theorem B1767415 : Blo 1766084 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B1988599 : Blo 1766084 1988599 := bstep (se 1 (by rfl) ⟨1491449, by rfl⟩ : syracuseStep 1988599 = 2982899) B2982899
theorem B1767435 : Blo 1766084 1767435 := bstep (se 1 (by rfl) ⟨1325576, by rfl⟩ : syracuseStep 1767435 = 2651153) B2651153
theorem B1767447 : Blo 1766084 1767447 := bstep (se 1 (by rfl) ⟨1325585, by rfl⟩ : syracuseStep 1767447 = 2651171) B2651171
theorem B1767467 : Blo 1766084 1767467 := bstep (se 1 (by rfl) ⟨1325600, by rfl⟩ : syracuseStep 1767467 = 2651201) B2651201
theorem B4470835 : Blo 1766084 4470835 := bstep (se 1 (by rfl) ⟨3353126, by rfl⟩ : syracuseStep 4470835 = 6706253) B6706253
theorem B1767479 : Blo 1766084 1767479 := bstep (se 1 (by rfl) ⟨1325609, by rfl⟩ : syracuseStep 1767479 = 2651219) B2651219
theorem B1767499 : Blo 1766084 1767499 := bstep (se 1 (by rfl) ⟨1325624, by rfl⟩ : syracuseStep 1767499 = 2651249) B2651249
theorem B1767511 : Blo 1766084 1767511 := bstep (se 1 (by rfl) ⟨1325633, by rfl⟩ : syracuseStep 1767511 = 2651267) B2651267
theorem B1767531 : Blo 1766084 1767531 := bstep (se 1 (by rfl) ⟨1325648, by rfl⟩ : syracuseStep 1767531 = 2651297) B2651297
theorem B1767543 : Blo 1766084 1767543 := bstep (se 1 (by rfl) ⟨1325657, by rfl⟩ : syracuseStep 1767543 = 2651315) B2651315
theorem B1767563 : Blo 1766084 1767563 := bstep (se 1 (by rfl) ⟨1325672, by rfl⟩ : syracuseStep 1767563 = 2651345) B2651345
theorem B1767575 : Blo 1766084 1767575 := bstep (se 1 (by rfl) ⟨1325681, by rfl⟩ : syracuseStep 1767575 = 2651363) B2651363
theorem B1767595 : Blo 1766084 1767595 := bstep (se 1 (by rfl) ⟨1325696, by rfl⟩ : syracuseStep 1767595 = 2651393) B2651393
theorem B1988779 : Blo 1766084 1988779 := bstep (se 1 (by rfl) ⟨1491584, by rfl⟩ : syracuseStep 1988779 = 2983169) B2983169
theorem B1767607 : Blo 1766084 1767607 := bstep (se 1 (by rfl) ⟨1325705, by rfl⟩ : syracuseStep 1767607 = 2651411) B2651411
theorem B4470977 : Blo 1766084 4470977 := bstep (se 2 (by rfl) ⟨1676616, by rfl⟩ : syracuseStep 4470977 = 3353233) B3353233
theorem B6707393 : Blo 1766084 6707393 := bstep (se 2 (by rfl) ⟨2515272, by rfl⟩ : syracuseStep 6707393 = 5030545) B5030545
theorem B1767627 : Blo 1766084 1767627 := bstep (se 1 (by rfl) ⟨1325720, by rfl⟩ : syracuseStep 1767627 = 2651441) B2651441
theorem B1767639 : Blo 1766084 1767639 := bstep (se 1 (by rfl) ⟨1325729, by rfl⟩ : syracuseStep 1767639 = 2651459) B2651459
theorem B1767659 : Blo 1766084 1767659 := bstep (se 1 (by rfl) ⟨1325744, by rfl⟩ : syracuseStep 1767659 = 2651489) B2651489
theorem B1767671 : Blo 1766084 1767671 := bstep (se 1 (by rfl) ⟨1325753, by rfl⟩ : syracuseStep 1767671 = 2651507) B2651507
theorem B1767691 : Blo 1766084 1767691 := bstep (se 1 (by rfl) ⟨1325768, by rfl⟩ : syracuseStep 1767691 = 2651537) B2651537
theorem B10066193 : Blo 1766084 10066193 := bstep (se 2 (by rfl) ⟨3774822, by rfl⟩ : syracuseStep 10066193 = 7549645) B7549645
theorem B5372183 : Blo 1766084 5372183 := bstep (se 1 (by rfl) ⟨4029137, by rfl⟩ : syracuseStep 5372183 = 8058275) B8058275
theorem B1767703 : Blo 1766084 1767703 := bstep (se 1 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 1767703 = 2651555) B2651555
theorem B1988887 : Blo 1766084 1988887 := bstep (se 1 (by rfl) ⟨1491665, by rfl⟩ : syracuseStep 1988887 = 2983331) B2983331
theorem B1767723 : Blo 1766084 1767723 := bstep (se 1 (by rfl) ⟨1325792, by rfl⟩ : syracuseStep 1767723 = 2651585) B2651585
theorem B1767735 : Blo 1766084 1767735 := bstep (se 1 (by rfl) ⟨1325801, by rfl⟩ : syracuseStep 1767735 = 2651603) B2651603
theorem B1767755 : Blo 1766084 1767755 := bstep (se 1 (by rfl) ⟨1325816, by rfl⟩ : syracuseStep 1767755 = 2651633) B2651633
theorem B1767767 : Blo 1766084 1767767 := bstep (se 1 (by rfl) ⟨1325825, by rfl⟩ : syracuseStep 1767767 = 2651651) B2651651
theorem B1767787 : Blo 1766084 1767787 := bstep (se 1 (by rfl) ⟨1325840, by rfl⟩ : syracuseStep 1767787 = 2651681) B2651681
theorem B1767799 : Blo 1766084 1767799 := bstep (se 1 (by rfl) ⟨1325849, by rfl⟩ : syracuseStep 1767799 = 2651699) B2651699
theorem B1767819 : Blo 1766084 1767819 := bstep (se 1 (by rfl) ⟨1325864, by rfl⟩ : syracuseStep 1767819 = 2651729) B2651729
theorem B1767831 : Blo 1766084 1767831 := bstep (se 1 (by rfl) ⟨1325873, by rfl⟩ : syracuseStep 1767831 = 2651747) B2651747
theorem B1767851 : Blo 1766084 1767851 := bstep (se 1 (by rfl) ⟨1325888, by rfl⟩ : syracuseStep 1767851 = 2651777) B2651777
theorem B3774899 : Blo 1766084 3774899 := bstep (se 1 (by rfl) ⟨2831174, by rfl⟩ : syracuseStep 3774899 = 5662349) B5662349
theorem B1767863 : Blo 1766084 1767863 := bstep (se 1 (by rfl) ⟨1325897, by rfl⟩ : syracuseStep 1767863 = 2651795) B2651795
theorem B1767883 : Blo 1766084 1767883 := bstep (se 1 (by rfl) ⟨1325912, by rfl⟩ : syracuseStep 1767883 = 2651825) B2651825
theorem B1989067 : Blo 1766084 1989067 := bstep (se 1 (by rfl) ⟨1491800, by rfl⟩ : syracuseStep 1989067 = 2983601) B2983601
theorem B1767895 : Blo 1766084 1767895 := bstep (se 1 (by rfl) ⟨1325921, by rfl⟩ : syracuseStep 1767895 = 2651843) B2651843
theorem B1767915 : Blo 1766084 1767915 := bstep (se 1 (by rfl) ⟨1325936, by rfl⟩ : syracuseStep 1767915 = 2651873) B2651873
theorem B1767927 : Blo 1766084 1767927 := bstep (se 1 (by rfl) ⟨1325945, by rfl⟩ : syracuseStep 1767927 = 2651891) B2651891
theorem B1767947 : Blo 1766084 1767947 := bstep (se 1 (by rfl) ⟨1325960, by rfl⟩ : syracuseStep 1767947 = 2651921) B2651921
theorem B5659159 : Blo 1766084 5659159 := bstep (se 1 (by rfl) ⟨4244369, by rfl⟩ : syracuseStep 5659159 = 8488739) B8488739
theorem B1767959 : Blo 1766084 1767959 := bstep (se 1 (by rfl) ⟨1325969, by rfl⟩ : syracuseStep 1767959 = 2651939) B2651939
theorem B1767979 : Blo 1766084 1767979 := bstep (se 1 (by rfl) ⟨1325984, by rfl⟩ : syracuseStep 1767979 = 2651969) B2651969
theorem B1767991 : Blo 1766084 1767991 := bstep (se 1 (by rfl) ⟨1325993, by rfl⟩ : syracuseStep 1767991 = 2651987) B2651987
theorem B1768011 : Blo 1766084 1768011 := bstep (se 1 (by rfl) ⟨1326008, by rfl⟩ : syracuseStep 1768011 = 2652017) B2652017
theorem B1768023 : Blo 1766084 1768023 := bstep (se 1 (by rfl) ⟨1326017, by rfl⟩ : syracuseStep 1768023 = 2652035) B2652035
theorem B4774493 : Blo 1766084 4774493 := bstep (se 3 (by rfl) ⟨895217, by rfl⟩ : syracuseStep 4774493 = 1790435) B1790435
theorem B1768043 : Blo 1766084 1768043 := bstep (se 1 (by rfl) ⟨1326032, by rfl⟩ : syracuseStep 1768043 = 2652065) B2652065
theorem B1768055 : Blo 1766084 1768055 := bstep (se 1 (by rfl) ⟨1326041, by rfl⟩ : syracuseStep 1768055 = 2652083) B2652083
theorem B1768075 : Blo 1766084 1768075 := bstep (se 1 (by rfl) ⟨1326056, by rfl⟩ : syracuseStep 1768075 = 2652113) B2652113
theorem B2980631 : Blo 1766084 2980631 := bstep (se 1 (by rfl) ⟨2235473, by rfl⟩ : syracuseStep 2980631 = 4470947) B4470947
theorem B5962571 : Blo 1766084 5962571 := bstep (se 1 (by rfl) ⟨4471928, by rfl⟩ : syracuseStep 5962571 = 8943857) B8943857
theorem B2980759 : Blo 1766084 2980759 := bstep (se 1 (by rfl) ⟨2235569, by rfl⟩ : syracuseStep 2980759 = 4471139) B4471139
theorem B7551917 : Blo 1766084 7551917 := bstep (se 3 (by rfl) ⟨1415984, by rfl⟩ : syracuseStep 7551917 = 2831969) B2831969
theorem B4422593 : Blo 1766084 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B54393817 : Blo 1766084 54393817 := bstep (se 2 (by rfl) ⟨20397681, by rfl⟩ : syracuseStep 54393817 = 40795363) B40795363
theorem B7543853 : Blo 1766084 7543853 := bstep (se 3 (by rfl) ⟨1414472, by rfl⟩ : syracuseStep 7543853 = 2828945) B2828945
theorem B5962841 : Blo 1766084 5962841 := bstep (se 2 (by rfl) ⟨2236065, by rfl⟩ : syracuseStep 5962841 = 4472131) B4472131
theorem B25484381 : Blo 1766084 25484381 := bstep (se 3 (by rfl) ⟨4778321, by rfl⟩ : syracuseStep 25484381 = 9556643) B9556643
theorem B9550979 : Blo 1766084 9550979 := bstep (se 1 (by rfl) ⟨7163234, by rfl⟩ : syracuseStep 9550979 = 14326469) B14326469
theorem B10058903 : Blo 1766084 10058903 := bstep (se 1 (by rfl) ⟨7544177, by rfl⟩ : syracuseStep 10058903 = 15088355) B15088355
theorem B2235595 : Blo 1766084 2235595 := bstep (se 1 (by rfl) ⟨1676696, by rfl⟩ : syracuseStep 2235595 = 3353393) B3353393
theorem B5102795 : Blo 1766084 5102795 := bstep (se 1 (by rfl) ⟨3827096, by rfl⟩ : syracuseStep 5102795 = 7654193) B7654193
theorem B6126941 : Blo 1766084 6126941 := bstep (se 3 (by rfl) ⟨1148801, by rfl⟩ : syracuseStep 6126941 = 2297603) B2297603
theorem B8494429 : Blo 1766084 8494429 := bstep (se 3 (by rfl) ⟨1592705, by rfl⟩ : syracuseStep 8494429 = 3185411) B3185411
theorem B6708653 : Blo 1766084 6708653 := bstep (se 3 (by rfl) ⟨1257872, by rfl⟩ : syracuseStep 6708653 = 2515745) B2515745
theorem B4472243 : Blo 1766084 4472243 := bstep (se 1 (by rfl) ⟨3354182, by rfl⟩ : syracuseStep 4472243 = 6708365) B6708365
theorem B6708683 : Blo 1766084 6708683 := bstep (se 1 (by rfl) ⟨5031512, by rfl⟩ : syracuseStep 6708683 = 10063025) B10063025
theorem B2235863 : Blo 1766084 2235863 := bstep (se 1 (by rfl) ⟨1676897, by rfl⟩ : syracuseStep 2235863 = 3353795) B3353795
theorem B16113113 : Blo 1766084 16113113 := bstep (se 2 (by rfl) ⟨6042417, by rfl⟩ : syracuseStep 16113113 = 12084835) B12084835
theorem B7167449 : Blo 1766084 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B2981387 : Blo 1766084 2981387 := bstep (se 1 (by rfl) ⟨2236040, by rfl⟩ : syracuseStep 2981387 = 4472081) B4472081
theorem B14327371 : Blo 1766084 14327371 := bstep (se 1 (by rfl) ⟨10745528, by rfl⟩ : syracuseStep 14327371 = 21491057) B21491057
theorem B2981515 : Blo 1766084 2981515 := bstep (se 1 (by rfl) ⟨2236136, by rfl⟩ : syracuseStep 2981515 = 4472273) B4472273
theorem B10198801 : Blo 1766084 10198801 := bstep (se 2 (by rfl) ⟨3824550, by rfl⟩ : syracuseStep 10198801 = 7649101) B7649101
theorem B5963543 : Blo 1766084 5963543 := bstep (se 1 (by rfl) ⟨4472657, by rfl⟩ : syracuseStep 5963543 = 8945315) B8945315
theorem B4030231 : Blo 1766084 4030231 := bstep (se 1 (by rfl) ⟨3022673, by rfl⟩ : syracuseStep 4030231 = 6045347) B6045347
theorem B2981657 : Blo 1766084 2981657 := bstep (se 2 (by rfl) ⟨1118121, by rfl⟩ : syracuseStep 2981657 = 2236243) B2236243
theorem B15097751 : Blo 1766084 15097751 := bstep (se 1 (by rfl) ⟨11323313, by rfl⟩ : syracuseStep 15097751 = 22646627) B22646627
theorem B2981785 : Blo 1766084 2981785 := bstep (se 2 (by rfl) ⟨1118169, by rfl⟩ : syracuseStep 2981785 = 2236339) B2236339
theorem B4472779 : Blo 1766084 4472779 := bstep (se 1 (by rfl) ⟨3354584, by rfl⟩ : syracuseStep 4472779 = 6709169) B6709169
theorem B6365213 : Blo 1766084 6365213 := bstep (se 3 (by rfl) ⟨1193477, by rfl⟩ : syracuseStep 6365213 = 2386955) B2386955
theorem B4472891 : Blo 1766084 4472891 := bstep (se 1 (by rfl) ⟨3354668, by rfl⟩ : syracuseStep 4472891 = 6709337) B6709337
theorem B2981947 : Blo 1766084 2981947 := bstep (se 1 (by rfl) ⟨2236460, by rfl⟩ : syracuseStep 2981947 = 4472921) B4472921
theorem B2982089 : Blo 1766084 2982089 := bstep (se 2 (by rfl) ⟨1118283, by rfl⟩ : syracuseStep 2982089 = 2236567) B2236567
theorem B2236663 : Blo 1766084 2236663 := bstep (se 1 (by rfl) ⟨1677497, by rfl⟩ : syracuseStep 2236663 = 3354995) B3354995
theorem B4473103 : Blo 1766084 4473103 := bstep (se 1 (by rfl) ⟨3354827, by rfl⟩ : syracuseStep 4473103 = 6709655) B6709655
theorem B9552275 : Blo 1766084 9552275 := bstep (se 1 (by rfl) ⟨7164206, by rfl⟩ : syracuseStep 9552275 = 14328413) B14328413
theorem B5964299 : Blo 1766084 5964299 := bstep (se 1 (by rfl) ⟨4473224, by rfl⟩ : syracuseStep 5964299 = 8946449) B8946449
theorem B13607453 : Blo 1766084 13607453 := bstep (se 3 (by rfl) ⟨2551397, by rfl⟩ : syracuseStep 13607453 = 5102795) B5102795
theorem B4473377 : Blo 1766084 4473377 := bstep (se 2 (by rfl) ⟨1677516, by rfl⟩ : syracuseStep 4473377 = 3355033) B3355033
theorem B36282923 : Blo 1766084 36282923 := bstep (se 1 (by rfl) ⟨27212192, by rfl⟩ : syracuseStep 36282923 = 54424385) B54424385
theorem B2236987 : Blo 1766084 2236987 := bstep (se 1 (by rfl) ⟨1677740, by rfl⟩ : syracuseStep 2236987 = 3355481) B3355481
theorem B3973751 : Blo 1766084 3973751 := bstep (se 1 (by rfl) ⟨2980313, by rfl⟩ : syracuseStep 3973751 = 5960627) B5960627
theorem B5964407 : Blo 1766084 5964407 := bstep (se 1 (by rfl) ⟨4473305, by rfl⟩ : syracuseStep 5964407 = 8946611) B8946611
theorem B7545545 : Blo 1766084 7545545 := bstep (se 2 (by rfl) ⟨2829579, by rfl⟩ : syracuseStep 7545545 = 5659159) B5659159
theorem B3973931 : Blo 1766084 3973931 := bstep (se 1 (by rfl) ⟨2980448, by rfl⟩ : syracuseStep 3973931 = 5960897) B5960897
theorem B3023659 : Blo 1766084 3023659 := bstep (se 1 (by rfl) ⟨2267744, by rfl⟩ : syracuseStep 3023659 = 4535489) B4535489
theorem B2982791 : Blo 1766084 2982791 := bstep (se 1 (by rfl) ⟨2237093, by rfl⟩ : syracuseStep 2982791 = 4474187) B4474187
theorem B2237483 : Blo 1766084 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B8496215 : Blo 1766084 8496215 := bstep (se 1 (by rfl) ⟨6372161, by rfl⟩ : syracuseStep 8496215 = 12744323) B12744323
theorem B3974291 : Blo 1766084 3974291 := bstep (se 1 (by rfl) ⟨2980718, by rfl⟩ : syracuseStep 3974291 = 5961437) B5961437
theorem B2122939 : Blo 1766084 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B3974345 : Blo 1766084 3974345 := bstep (se 2 (by rfl) ⟨1490379, by rfl⟩ : syracuseStep 3974345 = 2980759) B2980759
theorem B5965001 : Blo 1766084 5965001 := bstep (se 2 (by rfl) ⟨2236875, by rfl⟩ : syracuseStep 5965001 = 4473751) B4473751
theorem B72525089 : Blo 1766084 72525089 := bstep (se 2 (by rfl) ⟨27196908, by rfl⟩ : syracuseStep 72525089 = 54393817) B54393817
theorem B8947097 : Blo 1766084 8947097 := bstep (se 2 (by rfl) ⟨3355161, by rfl⟩ : syracuseStep 8947097 = 6710323) B6710323
theorem B6710795 : Blo 1766084 6710795 := bstep (se 1 (by rfl) ⟨5033096, by rfl⟩ : syracuseStep 6710795 = 10066193) B10066193
theorem B4474379 : Blo 1766084 4474379 := bstep (se 1 (by rfl) ⟨3355784, by rfl⟩ : syracuseStep 4474379 = 6711569) B6711569
theorem B2983439 : Blo 1766084 2983439 := bstep (se 1 (by rfl) ⟨2237579, by rfl⟩ : syracuseStep 2983439 = 4475159) B4475159
theorem B3827233 : Blo 1766084 3827233 := bstep (se 2 (by rfl) ⟨1435212, by rfl⟩ : syracuseStep 3827233 = 2870425) B2870425
theorem B5031467 : Blo 1766084 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B2516599 : Blo 1766084 2516599 := bstep (se 1 (by rfl) ⟨1887449, by rfl⟩ : syracuseStep 2516599 = 3774899) B3774899
theorem B15091393 : Blo 1766084 15091393 := bstep (se 2 (by rfl) ⟨5659272, by rfl⟩ : syracuseStep 15091393 = 11318545) B11318545
theorem B5031695 : Blo 1766084 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B24168241 : Blo 1766084 24168241 := bstep (se 2 (by rfl) ⟨9063090, by rfl⟩ : syracuseStep 24168241 = 18126181) B18126181
theorem B13420403 : Blo 1766084 13420403 := bstep (se 1 (by rfl) ⟨10065302, by rfl⟩ : syracuseStep 13420403 = 20130605) B20130605
theorem B3975047 : Blo 1766084 3975047 := bstep (se 1 (by rfl) ⟨2981285, by rfl⟩ : syracuseStep 3975047 = 5962571) B5962571
theorem B5965703 : Blo 1766084 5965703 := bstep (se 1 (by rfl) ⟨4474277, by rfl⟩ : syracuseStep 5965703 = 8948555) B8948555
theorem B3975227 : Blo 1766084 3975227 := bstep (se 1 (by rfl) ⟨2981420, by rfl⟩ : syracuseStep 3975227 = 5962841) B5962841
theorem B6367319 : Blo 1766084 6367319 := bstep (se 1 (by rfl) ⟨4775489, by rfl⟩ : syracuseStep 6367319 = 9550979) B9550979
theorem B4475027 : Blo 1766084 4475027 := bstep (se 1 (by rfl) ⟨3356270, by rfl⟩ : syracuseStep 4475027 = 6712541) B6712541
theorem B3975353 : Blo 1766084 3975353 := bstep (se 2 (by rfl) ⟨1490757, by rfl⟩ : syracuseStep 3975353 = 2981515) B2981515
theorem B15100141 : Blo 1766084 15100141 := bstep (se 3 (by rfl) ⟨2831276, by rfl⟩ : syracuseStep 15100141 = 5662553) B5662553
theorem B5966081 : Blo 1766084 5966081 := bstep (se 2 (by rfl) ⟨2237280, by rfl⟩ : syracuseStep 5966081 = 4474561) B4474561
theorem B10742075 : Blo 1766084 10742075 := bstep (se 1 (by rfl) ⟨8056556, by rfl⟩ : syracuseStep 10742075 = 16113113) B16113113
theorem B4778299 : Blo 1766084 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B4475321 : Blo 1766084 4475321 := bstep (se 2 (by rfl) ⟨1678245, by rfl⟩ : syracuseStep 4475321 = 3356491) B3356491
theorem B8604107 : Blo 1766084 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B3975695 : Blo 1766084 3975695 := bstep (se 1 (by rfl) ⟨2981771, by rfl⟩ : syracuseStep 3975695 = 5963543) B5963543
theorem B3975713 : Blo 1766084 3975713 := bstep (se 2 (by rfl) ⟨1490892, by rfl⟩ : syracuseStep 3975713 = 2981785) B2981785
theorem B22645291 : Blo 1766084 22645291 := bstep (se 1 (by rfl) ⟨16983968, by rfl⟩ : syracuseStep 22645291 = 33967937) B33967937
theorem B11315983 : Blo 1766084 11315983 := bstep (se 1 (by rfl) ⟨8486987, by rfl⟩ : syracuseStep 11315983 = 16973975) B16973975
theorem B8063803 : Blo 1766084 8063803 := bstep (se 1 (by rfl) ⟨6047852, by rfl⟩ : syracuseStep 8063803 = 12095705) B12095705
theorem B3976055 : Blo 1766084 3976055 := bstep (se 1 (by rfl) ⟨2982041, by rfl⟩ : syracuseStep 3976055 = 5964083) B5964083
theorem B4533127 : Blo 1766084 4533127 := bstep (se 1 (by rfl) ⟨3399845, by rfl⟩ : syracuseStep 4533127 = 6799691) B6799691
theorem B8489873 : Blo 1766084 8489873 := bstep (se 2 (by rfl) ⟨3183702, by rfl⟩ : syracuseStep 8489873 = 6367405) B6367405
theorem B3353491 : Blo 1766084 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B19106711 : Blo 1766084 19106711 := bstep (se 1 (by rfl) ⟨14330033, by rfl⟩ : syracuseStep 19106711 = 28660067) B28660067
theorem B38742947 : Blo 1766084 38742947 := bstep (se 1 (by rfl) ⟨29057210, by rfl⟩ : syracuseStep 38742947 = 58114421) B58114421
theorem B10742807 : Blo 1766084 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B2649131 : Blo 1766084 2649131 := bstep (se 1 (by rfl) ⟨1986848, by rfl⟩ : syracuseStep 2649131 = 3973697) B3973697
theorem B3976235 : Blo 1766084 3976235 := bstep (se 1 (by rfl) ⟨2982176, by rfl⟩ : syracuseStep 3976235 = 5964353) B5964353
theorem B5966891 : Blo 1766084 5966891 := bstep (se 1 (by rfl) ⟨4475168, by rfl⟩ : syracuseStep 5966891 = 8950337) B8950337
theorem B2649161 : Blo 1766084 2649161 := bstep (se 2 (by rfl) ⟨993435, by rfl⟩ : syracuseStep 2649161 = 1986871) B1986871
theorem B3353719 : Blo 1766084 3353719 := bstep (se 1 (by rfl) ⟨2515289, by rfl⟩ : syracuseStep 3353719 = 5030579) B5030579
theorem B5033107 : Blo 1766084 5033107 := bstep (se 1 (by rfl) ⟨3774830, by rfl⟩ : syracuseStep 5033107 = 7549661) B7549661
theorem B2722987 : Blo 1766084 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B2649275 : Blo 1766084 2649275 := bstep (se 1 (by rfl) ⟨1986956, by rfl⟩ : syracuseStep 2649275 = 3973913) B3973913
theorem B2649335 : Blo 1766084 2649335 := bstep (se 1 (by rfl) ⟨1987001, by rfl⟩ : syracuseStep 2649335 = 3974003) B3974003
theorem B2649359 : Blo 1766084 2649359 := bstep (se 1 (by rfl) ⟨1987019, by rfl⟩ : syracuseStep 2649359 = 3974039) B3974039
theorem B6368527 : Blo 1766084 6368527 := bstep (se 1 (by rfl) ⟨4776395, by rfl⟩ : syracuseStep 6368527 = 9552791) B9552791
theorem B2829611 : Blo 1766084 2829611 := bstep (se 1 (by rfl) ⟨2122208, by rfl⟩ : syracuseStep 2829611 = 4244417) B4244417
theorem B2649401 : Blo 1766084 2649401 := bstep (se 2 (by rfl) ⟨993525, by rfl⟩ : syracuseStep 2649401 = 1987051) B1987051
theorem B12086587 : Blo 1766084 12086587 := bstep (se 1 (by rfl) ⟨9064940, by rfl⟩ : syracuseStep 12086587 = 18129881) B18129881
theorem B5033335 : Blo 1766084 5033335 := bstep (se 1 (by rfl) ⟨3775001, by rfl⟩ : syracuseStep 5033335 = 7550003) B7550003
theorem B2649479 : Blo 1766084 2649479 := bstep (se 1 (by rfl) ⟨1987109, by rfl⟩ : syracuseStep 2649479 = 3974219) B3974219
theorem B3976595 : Blo 1766084 3976595 := bstep (se 1 (by rfl) ⟨2982446, by rfl⟩ : syracuseStep 3976595 = 5964893) B5964893
theorem B2649515 : Blo 1766084 2649515 := bstep (se 1 (by rfl) ⟨1987136, by rfl⟩ : syracuseStep 2649515 = 3974273) B3974273
theorem B24178105 : Blo 1766084 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B2649545 : Blo 1766084 2649545 := bstep (se 2 (by rfl) ⟨993579, by rfl⟩ : syracuseStep 2649545 = 1987159) B1987159
theorem B3976649 : Blo 1766084 3976649 := bstep (se 2 (by rfl) ⟨1491243, by rfl⟩ : syracuseStep 3976649 = 2982487) B2982487
theorem B3583531 : Blo 1766084 3583531 := bstep (se 1 (by rfl) ⟨2687648, by rfl⟩ : syracuseStep 3583531 = 5375297) B5375297
theorem B2649659 : Blo 1766084 2649659 := bstep (se 1 (by rfl) ⟨1987244, by rfl⟩ : syracuseStep 2649659 = 3974489) B3974489
theorem B16338509 : Blo 1766084 16338509 := bstep (se 3 (by rfl) ⟨3063470, by rfl⟩ : syracuseStep 16338509 = 6126941) B6126941
theorem B2649719 : Blo 1766084 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B2649743 : Blo 1766084 2649743 := bstep (se 1 (by rfl) ⟨1987307, by rfl⟩ : syracuseStep 2649743 = 3974615) B3974615
theorem B20123315 : Blo 1766084 20123315 := bstep (se 1 (by rfl) ⟨15092486, by rfl⟩ : syracuseStep 20123315 = 30184973) B30184973
theorem B2649785 : Blo 1766084 2649785 := bstep (se 2 (by rfl) ⟨993669, by rfl⟩ : syracuseStep 2649785 = 1987339) B1987339
theorem B2649863 : Blo 1766084 2649863 := bstep (se 1 (by rfl) ⟨1987397, by rfl⟩ : syracuseStep 2649863 = 3974795) B3974795
theorem B2649899 : Blo 1766084 2649899 := bstep (se 1 (by rfl) ⟨1987424, by rfl⟩ : syracuseStep 2649899 = 3974849) B3974849
theorem B2649929 : Blo 1766084 2649929 := bstep (se 2 (by rfl) ⟨993723, by rfl⟩ : syracuseStep 2649929 = 1987447) B1987447
theorem B8941427 : Blo 1766084 8941427 := bstep (se 1 (by rfl) ⟨6706070, by rfl⟩ : syracuseStep 8941427 = 13412141) B13412141
theorem B8949689 : Blo 1766084 8949689 := bstep (se 2 (by rfl) ⟨3356133, by rfl⟩ : syracuseStep 8949689 = 6712267) B6712267
theorem B2650043 : Blo 1766084 2650043 := bstep (se 1 (by rfl) ⟨1987532, by rfl⟩ : syracuseStep 2650043 = 3975065) B3975065
theorem B2650103 : Blo 1766084 2650103 := bstep (se 1 (by rfl) ⟨1987577, by rfl⟩ : syracuseStep 2650103 = 3975155) B3975155
theorem B2650127 : Blo 1766084 2650127 := bstep (se 1 (by rfl) ⟨1987595, by rfl⟩ : syracuseStep 2650127 = 3975191) B3975191
theorem B2650169 : Blo 1766084 2650169 := bstep (se 2 (by rfl) ⟨993813, by rfl⟩ : syracuseStep 2650169 = 1987627) B1987627
theorem B2388025 : Blo 1766084 2388025 := bstep (se 2 (by rfl) ⟨895509, by rfl⟩ : syracuseStep 2388025 = 1791019) B1791019
theorem B2650247 : Blo 1766084 2650247 := bstep (se 1 (by rfl) ⟨1987685, by rfl⟩ : syracuseStep 2650247 = 3975371) B3975371
theorem B3977351 : Blo 1766084 3977351 := bstep (se 1 (by rfl) ⟨2983013, by rfl⟩ : syracuseStep 3977351 = 5966027) B5966027
theorem B2650283 : Blo 1766084 2650283 := bstep (se 1 (by rfl) ⟨1987712, by rfl⟩ : syracuseStep 2650283 = 3975425) B3975425
theorem B15102125 : Blo 1766084 15102125 := bstep (se 3 (by rfl) ⟨2831648, by rfl⟩ : syracuseStep 15102125 = 5663297) B5663297
theorem B2650313 : Blo 1766084 2650313 := bstep (se 2 (by rfl) ⟨993867, by rfl⟩ : syracuseStep 2650313 = 1987735) B1987735
theorem B38211857 : Blo 1766084 38211857 := bstep (se 2 (by rfl) ⟨14329446, by rfl⟩ : syracuseStep 38211857 = 28658893) B28658893
theorem B2650427 : Blo 1766084 2650427 := bstep (se 1 (by rfl) ⟨1987820, by rfl⟩ : syracuseStep 2650427 = 3975641) B3975641
theorem B3977531 : Blo 1766084 3977531 := bstep (se 1 (by rfl) ⟨2983148, by rfl⟩ : syracuseStep 3977531 = 5966297) B5966297
theorem B8941913 : Blo 1766084 8941913 := bstep (se 2 (by rfl) ⟨3353217, by rfl⟩ : syracuseStep 8941913 = 6706435) B6706435
theorem B2650487 : Blo 1766084 2650487 := bstep (se 1 (by rfl) ⟨1987865, by rfl⟩ : syracuseStep 2650487 = 3975731) B3975731
theorem B2650511 : Blo 1766084 2650511 := bstep (se 1 (by rfl) ⟨1987883, by rfl⟩ : syracuseStep 2650511 = 3975767) B3975767
theorem B3182995 : Blo 1766084 3182995 := bstep (se 1 (by rfl) ⟨2387246, by rfl⟩ : syracuseStep 3182995 = 4774493) B4774493
theorem B2650553 : Blo 1766084 2650553 := bstep (se 2 (by rfl) ⟨993957, by rfl⟩ : syracuseStep 2650553 = 1987915) B1987915
theorem B2388409 : Blo 1766084 2388409 := bstep (se 2 (by rfl) ⟨895653, by rfl⟩ : syracuseStep 2388409 = 1791307) B1791307
theorem B3977657 : Blo 1766084 3977657 := bstep (se 2 (by rfl) ⟨1491621, by rfl⟩ : syracuseStep 3977657 = 2983243) B2983243
theorem B11325905 : Blo 1766084 11325905 := bstep (se 2 (by rfl) ⟨4247214, by rfl⟩ : syracuseStep 11325905 = 8494429) B8494429
theorem B2650631 : Blo 1766084 2650631 := bstep (se 1 (by rfl) ⟨1987973, by rfl⟩ : syracuseStep 2650631 = 3975947) B3975947
theorem B1987087 : Blo 1766084 1987087 := bstep (se 1 (by rfl) ⟨1490315, by rfl⟩ : syracuseStep 1987087 = 2980631) B2980631
theorem B2650667 : Blo 1766084 2650667 := bstep (se 1 (by rfl) ⟨1988000, by rfl⟩ : syracuseStep 2650667 = 3976001) B3976001
theorem B2388523 : Blo 1766084 2388523 := bstep (se 1 (by rfl) ⟨1791392, by rfl⟩ : syracuseStep 2388523 = 3582785) B3582785
theorem B2650697 : Blo 1766084 2650697 := bstep (se 2 (by rfl) ⟨994011, by rfl⟩ : syracuseStep 2650697 = 1988023) B1988023
theorem B5034611 : Blo 1766084 5034611 := bstep (se 1 (by rfl) ⟨3775958, by rfl⟩ : syracuseStep 5034611 = 7551917) B7551917
theorem B3355283 : Blo 1766084 3355283 := bstep (se 1 (by rfl) ⟨2516462, by rfl⟩ : syracuseStep 3355283 = 5032925) B5032925
theorem B2650811 : Blo 1766084 2650811 := bstep (se 1 (by rfl) ⟨1988108, by rfl⟩ : syracuseStep 2650811 = 3976217) B3976217
theorem B3355337 : Blo 1766084 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B2650871 : Blo 1766084 2650871 := bstep (se 1 (by rfl) ⟨1988153, by rfl⟩ : syracuseStep 2650871 = 3976307) B3976307
theorem B1766151 : Blo 1766084 1766151 := bstep (se 1 (by rfl) ⟨1324613, by rfl⟩ : syracuseStep 1766151 = 2649227) B2649227
theorem B1766159 : Blo 1766084 1766159 := bstep (se 1 (by rfl) ⟨1324619, by rfl⟩ : syracuseStep 1766159 = 2649239) B2649239
theorem B6705935 : Blo 1766084 6705935 := bstep (se 1 (by rfl) ⟨5029451, by rfl⟩ : syracuseStep 6705935 = 10058903) B10058903
theorem B2650895 : Blo 1766084 2650895 := bstep (se 1 (by rfl) ⟨1988171, by rfl⟩ : syracuseStep 2650895 = 3976343) B3976343
theorem B3977999 : Blo 1766084 3977999 := bstep (se 1 (by rfl) ⟨2983499, by rfl⟩ : syracuseStep 3977999 = 5966999) B5966999
theorem B3181114133 : Blo 1766084 3181114133 := bstep (se 6 (by rfl) ⟨74557362, by rfl⟩ : syracuseStep 3181114133 = 149114725) B149114725
theorem B3978017 : Blo 1766084 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B3355435 : Blo 1766084 3355435 := bstep (se 1 (by rfl) ⟨2516576, by rfl⟩ : syracuseStep 3355435 = 5033153) B5033153
theorem B2650937 : Blo 1766084 2650937 := bstep (se 2 (by rfl) ⟨994101, by rfl⟩ : syracuseStep 2650937 = 1988203) B1988203
theorem B1766203 : Blo 1766084 1766203 := bstep (se 1 (by rfl) ⟨1324652, by rfl⟩ : syracuseStep 1766203 = 2649305) B2649305
theorem B1766279 : Blo 1766084 1766279 := bstep (se 1 (by rfl) ⟨1324709, by rfl⟩ : syracuseStep 1766279 = 2649419) B2649419
theorem B2651015 : Blo 1766084 2651015 := bstep (se 1 (by rfl) ⟨1988261, by rfl⟩ : syracuseStep 2651015 = 3976523) B3976523
theorem B1766287 : Blo 1766084 1766287 := bstep (se 1 (by rfl) ⟨1324715, by rfl⟩ : syracuseStep 1766287 = 2649431) B2649431
theorem B2651051 : Blo 1766084 2651051 := bstep (se 1 (by rfl) ⟨1988288, by rfl⟩ : syracuseStep 2651051 = 3976577) B3976577
theorem B1766331 : Blo 1766084 1766331 := bstep (se 1 (by rfl) ⟨1324748, by rfl⟩ : syracuseStep 1766331 = 2649497) B2649497
theorem B2651081 : Blo 1766084 2651081 := bstep (se 2 (by rfl) ⟨994155, by rfl⟩ : syracuseStep 2651081 = 1988311) B1988311
theorem B1766407 : Blo 1766084 1766407 := bstep (se 1 (by rfl) ⟨1324805, by rfl⟩ : syracuseStep 1766407 = 2649611) B2649611
theorem B1987591 : Blo 1766084 1987591 := bstep (se 1 (by rfl) ⟨1490693, by rfl⟩ : syracuseStep 1987591 = 2981387) B2981387
theorem B1766415 : Blo 1766084 1766415 := bstep (se 1 (by rfl) ⟨1324811, by rfl⟩ : syracuseStep 1766415 = 2649623) B2649623
theorem B3355663 : Blo 1766084 3355663 := bstep (se 1 (by rfl) ⟨2516747, by rfl⟩ : syracuseStep 3355663 = 5033495) B5033495
theorem B1766459 : Blo 1766084 1766459 := bstep (se 1 (by rfl) ⟨1324844, by rfl⟩ : syracuseStep 1766459 = 2649689) B2649689
theorem B2651195 : Blo 1766084 2651195 := bstep (se 1 (by rfl) ⟨1988396, by rfl⟩ : syracuseStep 2651195 = 3976793) B3976793
theorem B2651255 : Blo 1766084 2651255 := bstep (se 1 (by rfl) ⟨1988441, by rfl⟩ : syracuseStep 2651255 = 3976883) B3976883
theorem B1766535 : Blo 1766084 1766535 := bstep (se 1 (by rfl) ⟨1324901, by rfl⟩ : syracuseStep 1766535 = 2649803) B2649803
theorem B1766543 : Blo 1766084 1766543 := bstep (se 1 (by rfl) ⟨1324907, by rfl⟩ : syracuseStep 1766543 = 2649815) B2649815
theorem B2651279 : Blo 1766084 2651279 := bstep (se 1 (by rfl) ⟨1988459, by rfl⟩ : syracuseStep 2651279 = 3976919) B3976919
theorem B2651321 : Blo 1766084 2651321 := bstep (se 2 (by rfl) ⟨994245, by rfl⟩ : syracuseStep 2651321 = 1988491) B1988491
theorem B1987771 : Blo 1766084 1987771 := bstep (se 1 (by rfl) ⟨1490828, by rfl⟩ : syracuseStep 1987771 = 2981657) B2981657
theorem B1766587 : Blo 1766084 1766587 := bstep (se 1 (by rfl) ⟨1324940, by rfl⟩ : syracuseStep 1766587 = 2649881) B2649881
theorem B1766663 : Blo 1766084 1766663 := bstep (se 1 (by rfl) ⟨1324997, by rfl⟩ : syracuseStep 1766663 = 2649995) B2649995
theorem B2651399 : Blo 1766084 2651399 := bstep (se 1 (by rfl) ⟨1988549, by rfl⟩ : syracuseStep 2651399 = 3977099) B3977099
theorem B1766671 : Blo 1766084 1766671 := bstep (se 1 (by rfl) ⟨1325003, by rfl⟩ : syracuseStep 1766671 = 2650007) B2650007
theorem B10065167 : Blo 1766084 10065167 := bstep (se 1 (by rfl) ⟨7548875, by rfl⟩ : syracuseStep 10065167 = 15097751) B15097751
theorem B3773729 : Blo 1766084 3773729 := bstep (se 2 (by rfl) ⟨1415148, by rfl⟩ : syracuseStep 3773729 = 2830297) B2830297
theorem B2651435 : Blo 1766084 2651435 := bstep (se 1 (by rfl) ⟨1988576, by rfl⟩ : syracuseStep 2651435 = 3977153) B3977153
theorem B1766715 : Blo 1766084 1766715 := bstep (se 1 (by rfl) ⟨1325036, by rfl⟩ : syracuseStep 1766715 = 2650073) B2650073
theorem B2651465 : Blo 1766084 2651465 := bstep (se 2 (by rfl) ⟨994299, by rfl⟩ : syracuseStep 2651465 = 1988599) B1988599
theorem B1766791 : Blo 1766084 1766791 := bstep (se 1 (by rfl) ⟨1325093, by rfl⟩ : syracuseStep 1766791 = 2650187) B2650187
theorem B1766799 : Blo 1766084 1766799 := bstep (se 1 (by rfl) ⟨1325099, by rfl⟩ : syracuseStep 1766799 = 2650199) B2650199
theorem B5961113 : Blo 1766084 5961113 := bstep (se 2 (by rfl) ⟨2235417, by rfl⟩ : syracuseStep 5961113 = 4470835) B4470835
theorem B1766843 : Blo 1766084 1766843 := bstep (se 1 (by rfl) ⟨1325132, by rfl⟩ : syracuseStep 1766843 = 2650265) B2650265
theorem B2651579 : Blo 1766084 2651579 := bstep (se 1 (by rfl) ⟨1988684, by rfl⟩ : syracuseStep 2651579 = 3977369) B3977369
theorem B2651639 : Blo 1766084 2651639 := bstep (se 1 (by rfl) ⟨1988729, by rfl⟩ : syracuseStep 2651639 = 3977459) B3977459
theorem B1766919 : Blo 1766084 1766919 := bstep (se 1 (by rfl) ⟨1325189, by rfl⟩ : syracuseStep 1766919 = 2650379) B2650379
theorem B1766927 : Blo 1766084 1766927 := bstep (se 1 (by rfl) ⟨1325195, by rfl⟩ : syracuseStep 1766927 = 2650391) B2650391
theorem B2651663 : Blo 1766084 2651663 := bstep (se 1 (by rfl) ⟨1988747, by rfl⟩ : syracuseStep 2651663 = 3977495) B3977495
theorem B2651705 : Blo 1766084 2651705 := bstep (se 2 (by rfl) ⟨994389, by rfl⟩ : syracuseStep 2651705 = 1988779) B1988779
theorem B1766971 : Blo 1766084 1766971 := bstep (se 1 (by rfl) ⟨1325228, by rfl⟩ : syracuseStep 1766971 = 2650457) B2650457
theorem B1767047 : Blo 1766084 1767047 := bstep (se 1 (by rfl) ⟨1325285, by rfl⟩ : syracuseStep 1767047 = 2650571) B2650571
theorem B2651783 : Blo 1766084 2651783 := bstep (se 1 (by rfl) ⟨1988837, by rfl⟩ : syracuseStep 2651783 = 3977675) B3977675
theorem B1767055 : Blo 1766084 1767055 := bstep (se 1 (by rfl) ⟨1325291, by rfl⟩ : syracuseStep 1767055 = 2650583) B2650583
theorem B1988239 : Blo 1766084 1988239 := bstep (se 1 (by rfl) ⟨1491179, by rfl⟩ : syracuseStep 1988239 = 2982359) B2982359
theorem B2651819 : Blo 1766084 2651819 := bstep (se 1 (by rfl) ⟨1988864, by rfl⟩ : syracuseStep 2651819 = 3977729) B3977729
theorem B9549485 : Blo 1766084 9549485 := bstep (se 3 (by rfl) ⟨1790528, by rfl⟩ : syracuseStep 9549485 = 3581057) B3581057
theorem B1767099 : Blo 1766084 1767099 := bstep (se 1 (by rfl) ⟨1325324, by rfl⟩ : syracuseStep 1767099 = 2650649) B2650649
theorem B9549505 : Blo 1766084 9549505 := bstep (se 2 (by rfl) ⟨3581064, by rfl⟩ : syracuseStep 9549505 = 7162129) B7162129
theorem B2651849 : Blo 1766084 2651849 := bstep (se 2 (by rfl) ⟨994443, by rfl⟩ : syracuseStep 2651849 = 1988887) B1988887
theorem B1767175 : Blo 1766084 1767175 := bstep (se 1 (by rfl) ⟨1325381, by rfl⟩ : syracuseStep 1767175 = 2650763) B2650763
theorem B1767183 : Blo 1766084 1767183 := bstep (se 1 (by rfl) ⟨1325387, by rfl⟩ : syracuseStep 1767183 = 2650775) B2650775
theorem B5740321 : Blo 1766084 5740321 := bstep (se 2 (by rfl) ⟨2152620, by rfl⟩ : syracuseStep 5740321 = 4305241) B4305241
theorem B15341363 : Blo 1766084 15341363 := bstep (se 1 (by rfl) ⟨11506022, by rfl⟩ : syracuseStep 15341363 = 23012045) B23012045
theorem B1767227 : Blo 1766084 1767227 := bstep (se 1 (by rfl) ⟨1325420, by rfl⟩ : syracuseStep 1767227 = 2650841) B2650841
theorem B2651963 : Blo 1766084 2651963 := bstep (se 1 (by rfl) ⟨1988972, by rfl⟩ : syracuseStep 2651963 = 3977945) B3977945
theorem B2652023 : Blo 1766084 2652023 := bstep (se 1 (by rfl) ⟨1989017, by rfl⟩ : syracuseStep 2652023 = 3978035) B3978035
theorem B1767303 : Blo 1766084 1767303 := bstep (se 1 (by rfl) ⟨1325477, by rfl⟩ : syracuseStep 1767303 = 2650955) B2650955
theorem B1767311 : Blo 1766084 1767311 := bstep (se 1 (by rfl) ⟨1325483, by rfl⟩ : syracuseStep 1767311 = 2650967) B2650967
theorem B2652047 : Blo 1766084 2652047 := bstep (se 1 (by rfl) ⟨1989035, by rfl⟩ : syracuseStep 2652047 = 3978071) B3978071
theorem B2652089 : Blo 1766084 2652089 := bstep (se 2 (by rfl) ⟨994533, by rfl⟩ : syracuseStep 2652089 = 1989067) B1989067
theorem B1767355 : Blo 1766084 1767355 := bstep (se 1 (by rfl) ⟨1325516, by rfl⟩ : syracuseStep 1767355 = 2651033) B2651033
theorem B1816507 : Blo 1766084 1816507 := bstep (se 1 (by rfl) ⟨1362380, by rfl⟩ : syracuseStep 1816507 = 2724761) B2724761
theorem B25827275 : Blo 1766084 25827275 := bstep (se 1 (by rfl) ⟨19370456, by rfl⟩ : syracuseStep 25827275 = 38740913) B38740913
theorem B4470785 : Blo 1766084 4470785 := bstep (se 2 (by rfl) ⟨1676544, by rfl⟩ : syracuseStep 4470785 = 3353089) B3353089
theorem B1767431 : Blo 1766084 1767431 := bstep (se 1 (by rfl) ⟨1325573, by rfl⟩ : syracuseStep 1767431 = 2651147) B2651147
theorem B1767439 : Blo 1766084 1767439 := bstep (se 1 (by rfl) ⟨1325579, by rfl⟩ : syracuseStep 1767439 = 2651159) B2651159
theorem B7649323 : Blo 1766084 7649323 := bstep (se 1 (by rfl) ⟨5736992, by rfl⟩ : syracuseStep 7649323 = 11473985) B11473985
theorem B1767483 : Blo 1766084 1767483 := bstep (se 1 (by rfl) ⟨1325612, by rfl⟩ : syracuseStep 1767483 = 2651225) B2651225
theorem B14325821 : Blo 1766084 14325821 := bstep (se 3 (by rfl) ⟨2686091, by rfl⟩ : syracuseStep 14325821 = 5372183) B5372183
theorem B5961815 : Blo 1766084 5961815 := bstep (se 1 (by rfl) ⟨4471361, by rfl⟩ : syracuseStep 5961815 = 8942723) B8942723
theorem B1767559 : Blo 1766084 1767559 := bstep (se 1 (by rfl) ⟨1325669, by rfl⟩ : syracuseStep 1767559 = 2651339) B2651339
theorem B1988743 : Blo 1766084 1988743 := bstep (se 1 (by rfl) ⟨1491557, by rfl⟩ : syracuseStep 1988743 = 2983115) B2983115
theorem B1767567 : Blo 1766084 1767567 := bstep (se 1 (by rfl) ⟨1325675, by rfl⟩ : syracuseStep 1767567 = 2651351) B2651351
theorem B1767611 : Blo 1766084 1767611 := bstep (se 1 (by rfl) ⟨1325708, by rfl⟩ : syracuseStep 1767611 = 2651417) B2651417
theorem B3184841 : Blo 1766084 3184841 := bstep (se 2 (by rfl) ⟨1194315, by rfl⟩ : syracuseStep 3184841 = 2388631) B2388631
theorem B1767687 : Blo 1766084 1767687 := bstep (se 1 (by rfl) ⟨1325765, by rfl⟩ : syracuseStep 1767687 = 2651531) B2651531
theorem B1767695 : Blo 1766084 1767695 := bstep (se 1 (by rfl) ⟨1325771, by rfl⟩ : syracuseStep 1767695 = 2651543) B2651543
theorem B1767739 : Blo 1766084 1767739 := bstep (se 1 (by rfl) ⟨1325804, by rfl⟩ : syracuseStep 1767739 = 2651609) B2651609
theorem B1988923 : Blo 1766084 1988923 := bstep (se 1 (by rfl) ⟨1491692, by rfl⟩ : syracuseStep 1988923 = 2983385) B2983385
theorem B4471159 : Blo 1766084 4471159 := bstep (se 1 (by rfl) ⟨3353369, by rfl⟩ : syracuseStep 4471159 = 6706739) B6706739
theorem B1767815 : Blo 1766084 1767815 := bstep (se 1 (by rfl) ⟨1325861, by rfl⟩ : syracuseStep 1767815 = 2651723) B2651723
theorem B1767823 : Blo 1766084 1767823 := bstep (se 1 (by rfl) ⟨1325867, by rfl⟩ : syracuseStep 1767823 = 2651735) B2651735
theorem B8944019 : Blo 1766084 8944019 := bstep (se 1 (by rfl) ⟨6708014, by rfl⟩ : syracuseStep 8944019 = 13416029) B13416029
theorem B1767867 : Blo 1766084 1767867 := bstep (se 1 (by rfl) ⟨1325900, by rfl⟩ : syracuseStep 1767867 = 2651801) B2651801
theorem B15104515 : Blo 1766084 15104515 := bstep (se 1 (by rfl) ⟨11328386, by rfl⟩ : syracuseStep 15104515 = 22656773) B22656773
theorem B1767943 : Blo 1766084 1767943 := bstep (se 1 (by rfl) ⟨1325957, by rfl⟩ : syracuseStep 1767943 = 2651915) B2651915
theorem B1767951 : Blo 1766084 1767951 := bstep (se 1 (by rfl) ⟨1325963, by rfl⟩ : syracuseStep 1767951 = 2651927) B2651927
theorem B1767995 : Blo 1766084 1767995 := bstep (se 1 (by rfl) ⟨1325996, by rfl⟩ : syracuseStep 1767995 = 2651993) B2651993
theorem B5962301 : Blo 1766084 5962301 := bstep (se 3 (by rfl) ⟨1117931, by rfl⟩ : syracuseStep 5962301 = 2235863) B2235863
theorem B16988737 : Blo 1766084 16988737 := bstep (se 2 (by rfl) ⟨6370776, by rfl⟩ : syracuseStep 16988737 = 12741553) B12741553
theorem B7551575 : Blo 1766084 7551575 := bstep (se 1 (by rfl) ⟨5663681, by rfl⟩ : syracuseStep 7551575 = 11327363) B11327363
theorem B21781111 : Blo 1766084 21781111 := bstep (se 1 (by rfl) ⟨16335833, by rfl⟩ : syracuseStep 21781111 = 32671667) B32671667
theorem B1768071 : Blo 1766084 1768071 := bstep (se 1 (by rfl) ⟨1326053, by rfl⟩ : syracuseStep 1768071 = 2652107) B2652107
theorem B1768079 : Blo 1766084 1768079 := bstep (se 1 (by rfl) ⟨1326059, by rfl⟩ : syracuseStep 1768079 = 2652119) B2652119
theorem B10066625 : Blo 1766084 10066625 := bstep (se 2 (by rfl) ⟨3774984, by rfl⟩ : syracuseStep 10066625 = 7549969) B7549969
theorem B2980651 : Blo 1766084 2980651 := bstep (se 1 (by rfl) ⟨2235488, by rfl⟩ : syracuseStep 2980651 = 4470977) B4470977
theorem B4471595 : Blo 1766084 4471595 := bstep (se 1 (by rfl) ⟨3353696, by rfl⟩ : syracuseStep 4471595 = 6707393) B6707393
theorem B2235271 : Blo 1766084 2235271 := bstep (se 1 (by rfl) ⟨1676453, by rfl⟩ : syracuseStep 2235271 = 3352907) B3352907
theorem B2980793 : Blo 1766084 2980793 := bstep (se 2 (by rfl) ⟨1117797, by rfl⟩ : syracuseStep 2980793 = 2235595) B2235595
theorem B2235691 : Blo 1766084 2235691 := bstep (se 1 (by rfl) ⟨1676768, by rfl⟩ : syracuseStep 2235691 = 3353537) B3353537
theorem B2948395 : Blo 1766084 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B5029235 : Blo 1766084 5029235 := bstep (se 1 (by rfl) ⟨3771926, by rfl⟩ : syracuseStep 5029235 = 7543853) B7543853
theorem B16989587 : Blo 1766084 16989587 := bstep (se 1 (by rfl) ⟨12742190, by rfl⟩ : syracuseStep 16989587 = 25484381) B25484381
theorem B3186067 : Blo 1766084 3186067 := bstep (se 1 (by rfl) ⟨2389550, by rfl⟩ : syracuseStep 3186067 = 4779101) B4779101
theorem B19103161 : Blo 1766084 19103161 := bstep (se 2 (by rfl) ⟨7163685, by rfl⟩ : syracuseStep 19103161 = 14327371) B14327371
theorem B2235919 : Blo 1766084 2235919 := bstep (se 1 (by rfl) ⟨1676939, by rfl⟩ : syracuseStep 2235919 = 3353879) B3353879
theorem B4472435 : Blo 1766084 4472435 := bstep (se 1 (by rfl) ⟨3354326, by rfl⟩ : syracuseStep 4472435 = 6708653) B6708653
theorem B2981495 : Blo 1766084 2981495 := bstep (se 1 (by rfl) ⟨2236121, by rfl⟩ : syracuseStep 2981495 = 4472243) B4472243
theorem B4472455 : Blo 1766084 4472455 := bstep (se 1 (by rfl) ⟨3354341, by rfl⟩ : syracuseStep 4472455 = 6708683) B6708683
theorem B13598401 : Blo 1766084 13598401 := bstep (se 2 (by rfl) ⟨5099400, by rfl⟩ : syracuseStep 13598401 = 10198801) B10198801
theorem B5029577 : Blo 1766084 5029577 := bstep (se 2 (by rfl) ⟨1886091, by rfl⟩ : syracuseStep 5029577 = 3772183) B3772183
theorem B6799049 : Blo 1766084 6799049 := bstep (se 2 (by rfl) ⟨2549643, by rfl⟩ : syracuseStep 6799049 = 5099287) B5099287
theorem B5373641 : Blo 1766084 5373641 := bstep (se 2 (by rfl) ⟨2015115, by rfl⟩ : syracuseStep 5373641 = 4030231) B4030231
theorem B2514731 : Blo 1766084 2514731 := bstep (se 1 (by rfl) ⟨1886048, by rfl⟩ : syracuseStep 2514731 = 3772097) B3772097
theorem B108764977 : Blo 1766084 108764977 := bstep (se 2 (by rfl) ⟨40786866, by rfl⟩ : syracuseStep 108764977 = 81573733) B81573733
theorem B6709139 : Blo 1766084 6709139 := bstep (se 1 (by rfl) ⟨5031854, by rfl⟩ : syracuseStep 6709139 = 10063709) B10063709
theorem B4472729 : Blo 1766084 4472729 := bstep (se 2 (by rfl) ⟨1677273, by rfl⟩ : syracuseStep 4472729 = 3354547) B3354547
theorem B5963705 : Blo 1766084 5963705 := bstep (se 2 (by rfl) ⟨2236389, by rfl⟩ : syracuseStep 5963705 = 4472779) B4472779
theorem B4243475 : Blo 1766084 4243475 := bstep (se 1 (by rfl) ⟨3182606, by rfl⟩ : syracuseStep 4243475 = 6365213) B6365213
theorem B2981927 : Blo 1766084 2981927 := bstep (se 1 (by rfl) ⟨2236445, by rfl⟩ : syracuseStep 2981927 = 4472891) B4472891
theorem B10068083 : Blo 1766084 10068083 := bstep (se 1 (by rfl) ⟨7551062, by rfl⟩ : syracuseStep 10068083 = 15102125) B15102125
theorem B40796389 : Blo 1766084 40796389 := bstep (se 4 (by rfl) ⟨3824661, by rfl⟩ : syracuseStep 40796389 = 7649323) B7649323
theorem B2982217 : Blo 1766084 2982217 := bstep (se 2 (by rfl) ⟨1118331, by rfl⟩ : syracuseStep 2982217 = 2236663) B2236663
theorem B5964137 : Blo 1766084 5964137 := bstep (se 2 (by rfl) ⟨2236551, by rfl⟩ : syracuseStep 5964137 = 4473103) B4473103
theorem B2982251 : Blo 1766084 2982251 := bstep (se 1 (by rfl) ⟨2236688, by rfl⟩ : syracuseStep 2982251 = 4473377) B4473377
theorem B5030363 : Blo 1766084 5030363 := bstep (se 1 (by rfl) ⟨3772772, by rfl⟩ : syracuseStep 5030363 = 7545545) B7545545
theorem B2236891 : Blo 1766084 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B2982649 : Blo 1766084 2982649 := bstep (se 2 (by rfl) ⟨1118493, by rfl⟩ : syracuseStep 2982649 = 2236987) B2236987
theorem B22651649 : Blo 1766084 22651649 := bstep (se 2 (by rfl) ⟨8494368, by rfl⟩ : syracuseStep 22651649 = 16988737) B16988737
theorem B7545629 : Blo 1766084 7545629 := bstep (se 3 (by rfl) ⟨1414805, by rfl⟩ : syracuseStep 7545629 = 2829611) B2829611
theorem B29041481 : Blo 1766084 29041481 := bstep (se 2 (by rfl) ⟨10890555, by rfl⟩ : syracuseStep 29041481 = 21781111) B21781111
theorem B6710111 : Blo 1766084 6710111 := bstep (se 1 (by rfl) ⟨5032583, by rfl⟩ : syracuseStep 6710111 = 10065167) B10065167
theorem B3974075 : Blo 1766084 3974075 := bstep (se 1 (by rfl) ⟨2980556, by rfl⟩ : syracuseStep 3974075 = 5961113) B5961113
theorem B5964731 : Blo 1766084 5964731 := bstep (se 1 (by rfl) ⟨4473548, by rfl⟩ : syracuseStep 5964731 = 8947097) B8947097
theorem B11322341 : Blo 1766084 11322341 := bstep (se 4 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 11322341 = 2122939) B2122939
theorem B4473863 : Blo 1766084 4473863 := bstep (se 1 (by rfl) ⟨3355397, by rfl⟩ : syracuseStep 4473863 = 6710795) B6710795
theorem B2982919 : Blo 1766084 2982919 := bstep (se 1 (by rfl) ⟨2237189, by rfl⟩ : syracuseStep 2982919 = 4474379) B4474379
theorem B3974201 : Blo 1766084 3974201 := bstep (se 2 (by rfl) ⟨1490325, by rfl⟩ : syracuseStep 3974201 = 2980651) B2980651
theorem B4473913 : Blo 1766084 4473913 := bstep (se 2 (by rfl) ⟨1677717, by rfl⟩ : syracuseStep 4473913 = 3355435) B3355435
theorem B4031545 : Blo 1766084 4031545 := bstep (se 2 (by rfl) ⟨1511829, by rfl⟩ : syracuseStep 4031545 = 3023659) B3023659
theorem B6366323 : Blo 1766084 6366323 := bstep (se 1 (by rfl) ⟨4774742, by rfl⟩ : syracuseStep 6366323 = 9549485) B9549485
theorem B8946935 : Blo 1766084 8946935 := bstep (se 1 (by rfl) ⟨6710201, by rfl⟩ : syracuseStep 8946935 = 13420403) B13420403
theorem B4474217 : Blo 1766084 4474217 := bstep (se 2 (by rfl) ⟨1677831, by rfl⟩ : syracuseStep 4474217 = 3355663) B3355663
theorem B3974543 : Blo 1766084 3974543 := bstep (se 1 (by rfl) ⟨2980907, by rfl⟩ : syracuseStep 3974543 = 5961815) B5961815
theorem B4244879 : Blo 1766084 4244879 := bstep (se 1 (by rfl) ⟨3183659, by rfl⟩ : syracuseStep 4244879 = 6367319) B6367319
theorem B33965477 : Blo 1766084 33965477 := bstep (se 4 (by rfl) ⟨3184263, by rfl⟩ : syracuseStep 33965477 = 6368527) B6368527
theorem B2983351 : Blo 1766084 2983351 := bstep (se 1 (by rfl) ⟨2237513, by rfl⟩ : syracuseStep 2983351 = 4475027) B4475027
theorem B2123227 : Blo 1766084 2123227 := bstep (se 1 (by rfl) ⟨1592420, by rfl⟩ : syracuseStep 2123227 = 3184841) B3184841
theorem B6710809 : Blo 1766084 6710809 := bstep (se 2 (by rfl) ⟨2516553, by rfl⟩ : syracuseStep 6710809 = 5033107) B5033107
theorem B7161383 : Blo 1766084 7161383 := bstep (se 1 (by rfl) ⟨5371037, by rfl⟩ : syracuseStep 7161383 = 10742075) B10742075
theorem B2983547 : Blo 1766084 2983547 := bstep (se 1 (by rfl) ⟨2237660, by rfl⟩ : syracuseStep 2983547 = 4475321) B4475321
theorem B5736071 : Blo 1766084 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B3974867 : Blo 1766084 3974867 := bstep (se 1 (by rfl) ⟨2981150, by rfl⟩ : syracuseStep 3974867 = 5962301) B5962301
theorem B8947421 : Blo 1766084 8947421 := bstep (se 3 (by rfl) ⟨1677641, by rfl⟩ : syracuseStep 8947421 = 3355283) B3355283
theorem B16115449 : Blo 1766084 16115449 := bstep (se 2 (by rfl) ⟨6043293, by rfl⟩ : syracuseStep 16115449 = 12086587) B12086587
theorem B6711083 : Blo 1766084 6711083 := bstep (se 1 (by rfl) ⟨5033312, by rfl⟩ : syracuseStep 6711083 = 10066625) B10066625
theorem B6711113 : Blo 1766084 6711113 := bstep (se 2 (by rfl) ⟨2516667, by rfl⟩ : syracuseStep 6711113 = 5033335) B5033335
theorem B14329709 : Blo 1766084 14329709 := bstep (se 3 (by rfl) ⟨2686820, by rfl⟩ : syracuseStep 14329709 = 5373641) B5373641
theorem B25470881 : Blo 1766084 25470881 := bstep (se 2 (by rfl) ⟨9551580, by rfl⟩ : syracuseStep 25470881 = 19103161) B19103161
theorem B32237473 : Blo 1766084 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B7161871 : Blo 1766084 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B24176677 : Blo 1766084 24176677 := bstep (se 4 (by rfl) ⟨2266563, by rfl⟩ : syracuseStep 24176677 = 4533127) B4533127
theorem B4778041 : Blo 1766084 4778041 := bstep (se 2 (by rfl) ⟨1791765, by rfl⟩ : syracuseStep 4778041 = 3583531) B3583531
theorem B16975973 : Blo 1766084 16975973 := bstep (se 4 (by rfl) ⟨1591497, by rfl⟩ : syracuseStep 16975973 = 3182995) B3182995
theorem B3352823 : Blo 1766084 3352823 := bstep (se 1 (by rfl) ⟨2514617, by rfl⟩ : syracuseStep 3352823 = 5029235) B5029235
theorem B12732673 : Blo 1766084 12732673 := bstep (se 2 (by rfl) ⟨4774752, by rfl⟩ : syracuseStep 12732673 = 9549505) B9549505
theorem B20121857 : Blo 1766084 20121857 := bstep (se 2 (by rfl) ⟨7545696, by rfl⟩ : syracuseStep 20121857 = 15091393) B15091393
theorem B18131201 : Blo 1766084 18131201 := bstep (se 2 (by rfl) ⟨6799200, by rfl⟩ : syracuseStep 18131201 = 13598401) B13598401
theorem B7653761 : Blo 1766084 7653761 := bstep (se 2 (by rfl) ⟨2870160, by rfl⟩ : syracuseStep 7653761 = 5740321) B5740321
theorem B3353051 : Blo 1766084 3353051 := bstep (se 1 (by rfl) ⟨2514788, by rfl⟩ : syracuseStep 3353051 = 5029577) B5029577
theorem B4532699 : Blo 1766084 4532699 := bstep (se 1 (by rfl) ⟨3399524, by rfl⟩ : syracuseStep 4532699 = 6799049) B6799049
theorem B3975803 : Blo 1766084 3975803 := bstep (se 1 (by rfl) ⟨2981852, by rfl⟩ : syracuseStep 3975803 = 5963705) B5963705
theorem B5966459 : Blo 1766084 5966459 := bstep (se 1 (by rfl) ⟨4474844, by rfl⟩ : syracuseStep 5966459 = 8949689) B8949689
theorem B3975929 : Blo 1766084 3975929 := bstep (se 2 (by rfl) ⟨1490973, by rfl⟩ : syracuseStep 3975929 = 2981947) B2981947
theorem B5966621 : Blo 1766084 5966621 := bstep (se 3 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 5966621 = 2237483) B2237483
theorem B6368183 : Blo 1766084 6368183 := bstep (se 1 (by rfl) ⟨4776137, by rfl⟩ : syracuseStep 6368183 = 9552275) B9552275
theorem B3976199 : Blo 1766084 3976199 := bstep (se 1 (by rfl) ⟨2982149, by rfl⟩ : syracuseStep 3976199 = 5964299) B5964299
theorem B9071635 : Blo 1766084 9071635 := bstep (se 1 (by rfl) ⟨6803726, by rfl⟩ : syracuseStep 9071635 = 13607453) B13607453
theorem B2649167 : Blo 1766084 2649167 := bstep (se 1 (by rfl) ⟨1986875, by rfl⟩ : syracuseStep 2649167 = 3973751) B3973751
theorem B3976271 : Blo 1766084 3976271 := bstep (se 1 (by rfl) ⟨2982203, by rfl⟩ : syracuseStep 3976271 = 5964407) B5964407
theorem B2649287 : Blo 1766084 2649287 := bstep (se 1 (by rfl) ⟨1986965, by rfl⟩ : syracuseStep 2649287 = 3973931) B3973931
theorem B13421861 : Blo 1766084 13421861 := bstep (se 4 (by rfl) ⟨1258299, by rfl⟩ : syracuseStep 13421861 = 2516599) B2516599
theorem B20139353 : Blo 1766084 20139353 := bstep (se 2 (by rfl) ⟨7552257, by rfl⟩ : syracuseStep 20139353 = 15104515) B15104515
theorem B2649449 : Blo 1766084 2649449 := bstep (se 2 (by rfl) ⟨993543, by rfl⟩ : syracuseStep 2649449 = 1987087) B1987087
theorem B5664143 : Blo 1766084 5664143 := bstep (se 1 (by rfl) ⟨4248107, by rfl⟩ : syracuseStep 5664143 = 8496215) B8496215
theorem B193400237 : Blo 1766084 193400237 := bstep (se 3 (by rfl) ⟨36262544, by rfl⟩ : syracuseStep 193400237 = 72525089) B72525089
theorem B10063277 : Blo 1766084 10063277 := bstep (se 3 (by rfl) ⟨1886864, by rfl⟩ : syracuseStep 10063277 = 3773729) B3773729
theorem B2649527 : Blo 1766084 2649527 := bstep (se 1 (by rfl) ⟨1987145, by rfl⟩ : syracuseStep 2649527 = 3974291) B3974291
theorem B2649563 : Blo 1766084 2649563 := bstep (se 1 (by rfl) ⟨1987172, by rfl⟩ : syracuseStep 2649563 = 3974345) B3974345
theorem B3976667 : Blo 1766084 3976667 := bstep (se 1 (by rfl) ⟨2982500, by rfl⟩ : syracuseStep 3976667 = 5965001) B5965001
theorem B3354311 : Blo 1766084 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B10751737 : Blo 1766084 10751737 := bstep (se 2 (by rfl) ⟨4031901, by rfl⟩ : syracuseStep 10751737 = 8063803) B8063803
theorem B3354463 : Blo 1766084 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B10227575 : Blo 1766084 10227575 := bstep (se 1 (by rfl) ⟨7670681, by rfl⟩ : syracuseStep 10227575 = 15341363) B15341363
theorem B2650031 : Blo 1766084 2650031 := bstep (se 1 (by rfl) ⟨1987523, by rfl⟩ : syracuseStep 2650031 = 3975047) B3975047
theorem B3977135 : Blo 1766084 3977135 := bstep (se 1 (by rfl) ⟨2982851, by rfl⟩ : syracuseStep 3977135 = 5965703) B5965703
theorem B2650121 : Blo 1766084 2650121 := bstep (se 2 (by rfl) ⟨993795, by rfl⟩ : syracuseStep 2650121 = 1987591) B1987591
theorem B2650151 : Blo 1766084 2650151 := bstep (se 1 (by rfl) ⟨1987613, by rfl⟩ : syracuseStep 2650151 = 3975227) B3975227
theorem B2650235 : Blo 1766084 2650235 := bstep (se 1 (by rfl) ⟨1987676, by rfl⟩ : syracuseStep 2650235 = 3975353) B3975353
theorem B3977387 : Blo 1766084 3977387 := bstep (se 1 (by rfl) ⟨2983040, by rfl⟩ : syracuseStep 3977387 = 5966081) B5966081
theorem B2650361 : Blo 1766084 2650361 := bstep (se 2 (by rfl) ⟨993885, by rfl⟩ : syracuseStep 2650361 = 1987771) B1987771
theorem B2650463 : Blo 1766084 2650463 := bstep (se 1 (by rfl) ⟨1987847, by rfl⟩ : syracuseStep 2650463 = 3975695) B3975695
theorem B2650475 : Blo 1766084 2650475 := bstep (se 1 (by rfl) ⟨1987856, by rfl⟩ : syracuseStep 2650475 = 3975713) B3975713
theorem B5034383 : Blo 1766084 5034383 := bstep (se 1 (by rfl) ⟨3775787, by rfl⟩ : syracuseStep 5034383 = 7551575) B7551575
theorem B4248089 : Blo 1766084 4248089 := bstep (se 2 (by rfl) ⟨1593033, by rfl⟩ : syracuseStep 4248089 = 3186067) B3186067
theorem B2650703 : Blo 1766084 2650703 := bstep (se 1 (by rfl) ⟨1988027, by rfl⟩ : syracuseStep 2650703 = 3976055) B3976055
theorem B1987195 : Blo 1766084 1987195 := bstep (se 1 (by rfl) ⟨1490396, by rfl⟩ : syracuseStep 1987195 = 2980793) B2980793
theorem B1766087 : Blo 1766084 1766087 := bstep (se 1 (by rfl) ⟨1324565, by rfl⟩ : syracuseStep 1766087 = 2649131) B2649131
theorem B2650823 : Blo 1766084 2650823 := bstep (se 1 (by rfl) ⟨1988117, by rfl⟩ : syracuseStep 2650823 = 3976235) B3976235
theorem B3977927 : Blo 1766084 3977927 := bstep (se 1 (by rfl) ⟨2983445, by rfl⟩ : syracuseStep 3977927 = 5966891) B5966891
theorem B1766107 : Blo 1766084 1766107 := bstep (se 1 (by rfl) ⟨1324580, by rfl⟩ : syracuseStep 1766107 = 2649161) B2649161
theorem B6705949 : Blo 1766084 6705949 := bstep (se 3 (by rfl) ⟨1257365, by rfl⟩ : syracuseStep 6705949 = 2514731) B2514731
theorem B1766183 : Blo 1766084 1766183 := bstep (se 1 (by rfl) ⟨1324637, by rfl⟩ : syracuseStep 1766183 = 2649275) B2649275
theorem B1766223 : Blo 1766084 1766223 := bstep (se 1 (by rfl) ⟨1324667, by rfl⟩ : syracuseStep 1766223 = 2649335) B2649335
theorem B1766239 : Blo 1766084 1766239 := bstep (se 1 (by rfl) ⟨1324679, by rfl⟩ : syracuseStep 1766239 = 2649359) B2649359
theorem B2650985 : Blo 1766084 2650985 := bstep (se 2 (by rfl) ⟨994119, by rfl⟩ : syracuseStep 2650985 = 1988239) B1988239
theorem B1766267 : Blo 1766084 1766267 := bstep (se 1 (by rfl) ⟨1324700, by rfl⟩ : syracuseStep 1766267 = 2649401) B2649401
theorem B1766319 : Blo 1766084 1766319 := bstep (se 1 (by rfl) ⟨1324739, by rfl⟩ : syracuseStep 1766319 = 2649479) B2649479
theorem B2651063 : Blo 1766084 2651063 := bstep (se 1 (by rfl) ⟨1988297, by rfl⟩ : syracuseStep 2651063 = 3976595) B3976595
theorem B11326391 : Blo 1766084 11326391 := bstep (se 1 (by rfl) ⟨8494793, by rfl⟩ : syracuseStep 11326391 = 16989587) B16989587
theorem B1766343 : Blo 1766084 1766343 := bstep (se 1 (by rfl) ⟨1324757, by rfl⟩ : syracuseStep 1766343 = 2649515) B2649515
theorem B1766363 : Blo 1766084 1766363 := bstep (se 1 (by rfl) ⟨1324772, by rfl⟩ : syracuseStep 1766363 = 2649545) B2649545
theorem B2651099 : Blo 1766084 2651099 := bstep (se 1 (by rfl) ⟨1988324, by rfl⟩ : syracuseStep 2651099 = 3976649) B3976649
theorem B1766439 : Blo 1766084 1766439 := bstep (se 1 (by rfl) ⟨1324829, by rfl⟩ : syracuseStep 1766439 = 2649659) B2649659
theorem B10892339 : Blo 1766084 10892339 := bstep (se 1 (by rfl) ⟨8169254, by rfl⟩ : syracuseStep 10892339 = 16338509) B16338509
theorem B32224321 : Blo 1766084 32224321 := bstep (se 2 (by rfl) ⟨12084120, by rfl⟩ : syracuseStep 32224321 = 24168241) B24168241
theorem B145019969 : Blo 1766084 145019969 := bstep (se 2 (by rfl) ⟨54382488, by rfl⟩ : syracuseStep 145019969 = 108764977) B108764977
theorem B1766479 : Blo 1766084 1766479 := bstep (se 1 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 1766479 = 2649719) B2649719
theorem B1987663 : Blo 1766084 1987663 := bstep (se 1 (by rfl) ⟨1490747, by rfl⟩ : syracuseStep 1987663 = 2981495) B2981495
theorem B1766495 : Blo 1766084 1766495 := bstep (se 1 (by rfl) ⟨1324871, by rfl⟩ : syracuseStep 1766495 = 2649743) B2649743
theorem B13415543 : Blo 1766084 13415543 := bstep (se 1 (by rfl) ⟨10061657, by rfl⟩ : syracuseStep 13415543 = 20123315) B20123315
theorem B1766523 : Blo 1766084 1766523 := bstep (se 1 (by rfl) ⟨1324892, by rfl⟩ : syracuseStep 1766523 = 2649785) B2649785
theorem B1766575 : Blo 1766084 1766575 := bstep (se 1 (by rfl) ⟨1324931, by rfl⟩ : syracuseStep 1766575 = 2649863) B2649863
theorem B1766599 : Blo 1766084 1766599 := bstep (se 1 (by rfl) ⟨1324949, by rfl⟩ : syracuseStep 1766599 = 2649899) B2649899
theorem B1766619 : Blo 1766084 1766619 := bstep (se 1 (by rfl) ⟨1324964, by rfl⟩ : syracuseStep 1766619 = 2649929) B2649929
theorem B5960951 : Blo 1766084 5960951 := bstep (se 1 (by rfl) ⟨4470713, by rfl⟩ : syracuseStep 5960951 = 8941427) B8941427
theorem B2422009 : Blo 1766084 2422009 := bstep (se 2 (by rfl) ⟨908253, by rfl⟩ : syracuseStep 2422009 = 1816507) B1816507
theorem B1766695 : Blo 1766084 1766695 := bstep (se 1 (by rfl) ⟨1325021, by rfl⟩ : syracuseStep 1766695 = 2650043) B2650043
theorem B1766735 : Blo 1766084 1766735 := bstep (se 1 (by rfl) ⟨1325051, by rfl⟩ : syracuseStep 1766735 = 2650103) B2650103
theorem B1766751 : Blo 1766084 1766751 := bstep (se 1 (by rfl) ⟨1325063, by rfl⟩ : syracuseStep 1766751 = 2650127) B2650127
theorem B1766779 : Blo 1766084 1766779 := bstep (se 1 (by rfl) ⟨1325084, by rfl⟩ : syracuseStep 1766779 = 2650169) B2650169
theorem B3184033 : Blo 1766084 3184033 := bstep (se 2 (by rfl) ⟨1194012, by rfl⟩ : syracuseStep 3184033 = 2388025) B2388025
theorem B1766831 : Blo 1766084 1766831 := bstep (se 1 (by rfl) ⟨1325123, by rfl⟩ : syracuseStep 1766831 = 2650247) B2650247
theorem B2651567 : Blo 1766084 2651567 := bstep (se 1 (by rfl) ⟨1988675, by rfl⟩ : syracuseStep 2651567 = 3977351) B3977351
theorem B1766855 : Blo 1766084 1766855 := bstep (se 1 (by rfl) ⟨1325141, by rfl⟩ : syracuseStep 1766855 = 2650283) B2650283
theorem B1766875 : Blo 1766084 1766875 := bstep (se 1 (by rfl) ⟨1325156, by rfl⟩ : syracuseStep 1766875 = 2650313) B2650313
theorem B1988059 : Blo 1766084 1988059 := bstep (se 1 (by rfl) ⟨1491044, by rfl⟩ : syracuseStep 1988059 = 2982089) B2982089
theorem B20411909 : Blo 1766084 20411909 := bstep (se 4 (by rfl) ⟨1913616, by rfl⟩ : syracuseStep 20411909 = 3827233) B3827233
theorem B2651657 : Blo 1766084 2651657 := bstep (se 2 (by rfl) ⟨994371, by rfl⟩ : syracuseStep 2651657 = 1988743) B1988743
theorem B25474571 : Blo 1766084 25474571 := bstep (se 1 (by rfl) ⟨19105928, by rfl⟩ : syracuseStep 25474571 = 38211857) B38211857
theorem B1766951 : Blo 1766084 1766951 := bstep (se 1 (by rfl) ⟨1325213, by rfl⟩ : syracuseStep 1766951 = 2650427) B2650427
theorem B2651687 : Blo 1766084 2651687 := bstep (se 1 (by rfl) ⟨1988765, by rfl⟩ : syracuseStep 2651687 = 3977531) B3977531
theorem B5961275 : Blo 1766084 5961275 := bstep (se 1 (by rfl) ⟨4470956, by rfl⟩ : syracuseStep 5961275 = 8941913) B8941913
theorem B1766991 : Blo 1766084 1766991 := bstep (se 1 (by rfl) ⟨1325243, by rfl⟩ : syracuseStep 1766991 = 2650487) B2650487
theorem B1767007 : Blo 1766084 1767007 := bstep (se 1 (by rfl) ⟨1325255, by rfl⟩ : syracuseStep 1767007 = 2650511) B2650511
theorem B1767035 : Blo 1766084 1767035 := bstep (se 1 (by rfl) ⟨1325276, by rfl⟩ : syracuseStep 1767035 = 2650553) B2650553
theorem B2651771 : Blo 1766084 2651771 := bstep (se 1 (by rfl) ⟨1988828, by rfl⟩ : syracuseStep 2651771 = 3977657) B3977657
theorem B7550603 : Blo 1766084 7550603 := bstep (se 1 (by rfl) ⟨5662952, by rfl⟩ : syracuseStep 7550603 = 11325905) B11325905
theorem B20133521 : Blo 1766084 20133521 := bstep (se 2 (by rfl) ⟨7550070, by rfl⟩ : syracuseStep 20133521 = 15100141) B15100141
theorem B1767087 : Blo 1766084 1767087 := bstep (se 1 (by rfl) ⟨1325315, by rfl⟩ : syracuseStep 1767087 = 2650631) B2650631
theorem B1767111 : Blo 1766084 1767111 := bstep (se 1 (by rfl) ⟨1325333, by rfl⟩ : syracuseStep 1767111 = 2650667) B2650667
theorem B24188615 : Blo 1766084 24188615 := bstep (se 1 (by rfl) ⟨18141461, by rfl⟩ : syracuseStep 24188615 = 36282923) B36282923
theorem B1767131 : Blo 1766084 1767131 := bstep (se 1 (by rfl) ⟨1325348, by rfl⟩ : syracuseStep 1767131 = 2650697) B2650697
theorem B6371065 : Blo 1766084 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B2651897 : Blo 1766084 2651897 := bstep (se 2 (by rfl) ⟨994461, by rfl⟩ : syracuseStep 2651897 = 1988923) B1988923
theorem B3356407 : Blo 1766084 3356407 := bstep (se 1 (by rfl) ⟨2517305, by rfl⟩ : syracuseStep 3356407 = 5034611) B5034611
theorem B1767207 : Blo 1766084 1767207 := bstep (se 1 (by rfl) ⟨1325405, by rfl⟩ : syracuseStep 1767207 = 2650811) B2650811
theorem B5961545 : Blo 1766084 5961545 := bstep (se 2 (by rfl) ⟨2235579, by rfl⟩ : syracuseStep 5961545 = 4471159) B4471159
theorem B1767247 : Blo 1766084 1767247 := bstep (se 1 (by rfl) ⟨1325435, by rfl⟩ : syracuseStep 1767247 = 2650871) B2650871
theorem B4470623 : Blo 1766084 4470623 := bstep (se 1 (by rfl) ⟨3352967, by rfl⟩ : syracuseStep 4470623 = 6705935) B6705935
theorem B1767263 : Blo 1766084 1767263 := bstep (se 1 (by rfl) ⟨1325447, by rfl⟩ : syracuseStep 1767263 = 2650895) B2650895
theorem B2651999 : Blo 1766084 2651999 := bstep (se 1 (by rfl) ⟨1988999, by rfl⟩ : syracuseStep 2651999 = 3977999) B3977999
theorem B2120742755 : Blo 1766084 2120742755 := bstep (se 1 (by rfl) ⟨1590557066, by rfl⟩ : syracuseStep 2120742755 = 3181114133) B3181114133
theorem B2652011 : Blo 1766084 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B1767291 : Blo 1766084 1767291 := bstep (se 1 (by rfl) ⟨1325468, by rfl⟩ : syracuseStep 1767291 = 2650937) B2650937
theorem B1767343 : Blo 1766084 1767343 := bstep (se 1 (by rfl) ⟨1325507, by rfl⟩ : syracuseStep 1767343 = 2651015) B2651015
theorem B1988527 : Blo 1766084 1988527 := bstep (se 1 (by rfl) ⟨1491395, by rfl⟩ : syracuseStep 1988527 = 2982791) B2982791
theorem B1767367 : Blo 1766084 1767367 := bstep (se 1 (by rfl) ⟨1325525, by rfl⟩ : syracuseStep 1767367 = 2651051) B2651051
theorem B1767387 : Blo 1766084 1767387 := bstep (se 1 (by rfl) ⟨1325540, by rfl⟩ : syracuseStep 1767387 = 2651081) B2651081
theorem B1767463 : Blo 1766084 1767463 := bstep (se 1 (by rfl) ⟨1325597, by rfl⟩ : syracuseStep 1767463 = 2651195) B2651195
theorem B30193721 : Blo 1766084 30193721 := bstep (se 2 (by rfl) ⟨11322645, by rfl⟩ : syracuseStep 30193721 = 22645291) B22645291
theorem B3184697 : Blo 1766084 3184697 := bstep (se 2 (by rfl) ⟨1194261, by rfl⟩ : syracuseStep 3184697 = 2388523) B2388523
theorem B1767503 : Blo 1766084 1767503 := bstep (se 1 (by rfl) ⟨1325627, by rfl⟩ : syracuseStep 1767503 = 2651255) B2651255
theorem B1767519 : Blo 1766084 1767519 := bstep (se 1 (by rfl) ⟨1325639, by rfl⟩ : syracuseStep 1767519 = 2651279) B2651279
theorem B1767547 : Blo 1766084 1767547 := bstep (se 1 (by rfl) ⟨1325660, by rfl⟩ : syracuseStep 1767547 = 2651321) B2651321
theorem B1767599 : Blo 1766084 1767599 := bstep (se 1 (by rfl) ⟨1325699, by rfl⟩ : syracuseStep 1767599 = 2651399) B2651399
theorem B1767623 : Blo 1766084 1767623 := bstep (se 1 (by rfl) ⟨1325717, by rfl⟩ : syracuseStep 1767623 = 2651435) B2651435
theorem B1767643 : Blo 1766084 1767643 := bstep (se 1 (by rfl) ⟨1325732, by rfl⟩ : syracuseStep 1767643 = 2651465) B2651465
theorem B14522597 : Blo 1766084 14522597 := bstep (se 4 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 14522597 = 2722987) B2722987
theorem B1767719 : Blo 1766084 1767719 := bstep (se 1 (by rfl) ⟨1325789, by rfl⟩ : syracuseStep 1767719 = 2651579) B2651579
theorem B1767759 : Blo 1766084 1767759 := bstep (se 1 (by rfl) ⟨1325819, by rfl⟩ : syracuseStep 1767759 = 2651639) B2651639
theorem B1767775 : Blo 1766084 1767775 := bstep (se 1 (by rfl) ⟨1325831, by rfl⟩ : syracuseStep 1767775 = 2651663) B2651663
theorem B1988959 : Blo 1766084 1988959 := bstep (se 1 (by rfl) ⟨1491719, by rfl⟩ : syracuseStep 1988959 = 2983439) B2983439
theorem B15087977 : Blo 1766084 15087977 := bstep (se 2 (by rfl) ⟨5657991, by rfl⟩ : syracuseStep 15087977 = 11315983) B11315983
theorem B1767803 : Blo 1766084 1767803 := bstep (se 1 (by rfl) ⟨1325852, by rfl⟩ : syracuseStep 1767803 = 2651705) B2651705
theorem B1767855 : Blo 1766084 1767855 := bstep (se 1 (by rfl) ⟨1325891, by rfl⟩ : syracuseStep 1767855 = 2651783) B2651783
theorem B1767879 : Blo 1766084 1767879 := bstep (se 1 (by rfl) ⟨1325909, by rfl⟩ : syracuseStep 1767879 = 2651819) B2651819
theorem B1767899 : Blo 1766084 1767899 := bstep (se 1 (by rfl) ⟨1325924, by rfl⟩ : syracuseStep 1767899 = 2651849) B2651849
theorem B2980361 : Blo 1766084 2980361 := bstep (se 2 (by rfl) ⟨1117635, by rfl⟩ : syracuseStep 2980361 = 2235271) B2235271
theorem B50952725 : Blo 1766084 50952725 := bstep (se 6 (by rfl) ⟨1194204, by rfl⟩ : syracuseStep 50952725 = 2388409) B2388409
theorem B4471321 : Blo 1766084 4471321 := bstep (se 2 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 4471321 = 3353491) B3353491
theorem B1767975 : Blo 1766084 1767975 := bstep (se 1 (by rfl) ⟨1325981, by rfl⟩ : syracuseStep 1767975 = 2651963) B2651963
theorem B1768015 : Blo 1766084 1768015 := bstep (se 1 (by rfl) ⟨1326011, by rfl⟩ : syracuseStep 1768015 = 2652023) B2652023
theorem B1768031 : Blo 1766084 1768031 := bstep (se 1 (by rfl) ⟨1326023, by rfl⟩ : syracuseStep 1768031 = 2652047) B2652047
theorem B1768059 : Blo 1766084 1768059 := bstep (se 1 (by rfl) ⟨1326044, by rfl⟩ : syracuseStep 1768059 = 2652089) B2652089
theorem B17218183 : Blo 1766084 17218183 := bstep (se 1 (by rfl) ⟨12913637, by rfl⟩ : syracuseStep 17218183 = 25827275) B25827275
theorem B2980523 : Blo 1766084 2980523 := bstep (se 1 (by rfl) ⟨2235392, by rfl⟩ : syracuseStep 2980523 = 4470785) B4470785
theorem B9550547 : Blo 1766084 9550547 := bstep (se 1 (by rfl) ⟨7162910, by rfl⟩ : syracuseStep 9550547 = 14325821) B14325821
theorem B4471625 : Blo 1766084 4471625 := bstep (se 2 (by rfl) ⟨1676859, by rfl⟩ : syracuseStep 4471625 = 3353719) B3353719
theorem B5962679 : Blo 1766084 5962679 := bstep (se 1 (by rfl) ⟨4472009, by rfl⟩ : syracuseStep 5962679 = 8944019) B8944019
theorem B2980921 : Blo 1766084 2980921 := bstep (se 2 (by rfl) ⟨1117845, by rfl⟩ : syracuseStep 2980921 = 2235691) B2235691
theorem B3931193 : Blo 1766084 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B2981063 : Blo 1766084 2981063 := bstep (se 1 (by rfl) ⟨2235797, by rfl⟩ : syracuseStep 2981063 = 4471595) B4471595
theorem B5659915 : Blo 1766084 5659915 := bstep (se 1 (by rfl) ⟨4244936, by rfl⟩ : syracuseStep 5659915 = 8489873) B8489873
theorem B12737807 : Blo 1766084 12737807 := bstep (se 1 (by rfl) ⟨9553355, by rfl⟩ : syracuseStep 12737807 = 19106711) B19106711
theorem B25828631 : Blo 1766084 25828631 := bstep (se 1 (by rfl) ⟨19371473, by rfl⟩ : syracuseStep 25828631 = 38742947) B38742947
theorem B2981225 : Blo 1766084 2981225 := bstep (se 2 (by rfl) ⟨1117959, by rfl⟩ : syracuseStep 2981225 = 2235919) B2235919
theorem B5963273 : Blo 1766084 5963273 := bstep (se 2 (by rfl) ⟨2236227, by rfl⟩ : syracuseStep 5963273 = 4472455) B4472455
theorem B2981623 : Blo 1766084 2981623 := bstep (se 1 (by rfl) ⟨2236217, by rfl⟩ : syracuseStep 2981623 = 4472435) B4472435
theorem B4472759 : Blo 1766084 4472759 := bstep (se 1 (by rfl) ⟨3354569, by rfl⟩ : syracuseStep 4472759 = 6709139) B6709139
theorem B2981819 : Blo 1766084 2981819 := bstep (se 1 (by rfl) ⟨2236364, by rfl⟩ : syracuseStep 2981819 = 4472729) B4472729
theorem B32235569 : Blo 1766084 32235569 := bstep (se 2 (by rfl) ⟨12088338, by rfl⟩ : syracuseStep 32235569 = 24176677) B24176677
theorem B54395185 : Blo 1766084 54395185 := bstep (se 2 (by rfl) ⟨20398194, by rfl⟩ : syracuseStep 54395185 = 40796389) B40796389
theorem B5030419 : Blo 1766084 5030419 := bstep (se 1 (by rfl) ⟨3772814, by rfl⟩ : syracuseStep 5030419 = 7545629) B7545629
theorem B4473407 : Blo 1766084 4473407 := bstep (se 1 (by rfl) ⟨3355055, by rfl⟩ : syracuseStep 4473407 = 6710111) B6710111
theorem B2982521 : Blo 1766084 2982521 := bstep (se 2 (by rfl) ⟨1118445, by rfl⟩ : syracuseStep 2982521 = 2236891) B2236891
theorem B2982575 : Blo 1766084 2982575 := bstep (se 1 (by rfl) ⟨2236931, by rfl⟩ : syracuseStep 2982575 = 4473863) B4473863
theorem B3973967 : Blo 1766084 3973967 := bstep (se 1 (by rfl) ⟨2980475, by rfl⟩ : syracuseStep 3973967 = 5960951) B5960951
theorem B5964623 : Blo 1766084 5964623 := bstep (se 1 (by rfl) ⟨4473467, by rfl⟩ : syracuseStep 5964623 = 8946935) B8946935
theorem B2982811 : Blo 1766084 2982811 := bstep (se 1 (by rfl) ⟨2237108, by rfl⟩ : syracuseStep 2982811 = 4474217) B4474217
theorem B22643651 : Blo 1766084 22643651 := bstep (se 1 (by rfl) ⟨16982738, by rfl⟩ : syracuseStep 22643651 = 33965477) B33965477
theorem B13607939 : Blo 1766084 13607939 := bstep (se 1 (by rfl) ⟨10205954, by rfl⟩ : syracuseStep 13607939 = 20411909) B20411909
theorem B16983047 : Blo 1766084 16983047 := bstep (se 1 (by rfl) ⟨12737285, by rfl⟩ : syracuseStep 16983047 = 25474571) B25474571
theorem B3974183 : Blo 1766084 3974183 := bstep (se 1 (by rfl) ⟨2980637, by rfl⟩ : syracuseStep 3974183 = 5961275) B5961275
theorem B5964947 : Blo 1766084 5964947 := bstep (se 1 (by rfl) ⟨4473710, by rfl⟩ : syracuseStep 5964947 = 8947421) B8947421
theorem B4474055 : Blo 1766084 4474055 := bstep (se 1 (by rfl) ⟨3355541, by rfl⟩ : syracuseStep 4474055 = 6711083) B6711083
theorem B3974363 : Blo 1766084 3974363 := bstep (se 1 (by rfl) ⟨2980772, by rfl⟩ : syracuseStep 3974363 = 5961545) B5961545
theorem B4474075 : Blo 1766084 4474075 := bstep (se 1 (by rfl) ⟨3355556, by rfl⟩ : syracuseStep 4474075 = 6711113) B6711113
theorem B9553139 : Blo 1766084 9553139 := bstep (se 1 (by rfl) ⟨7164854, by rfl⟩ : syracuseStep 9553139 = 14329709) B14329709
theorem B20129147 : Blo 1766084 20129147 := bstep (se 1 (by rfl) ⟨15096860, by rfl⟩ : syracuseStep 20129147 = 30193721) B30193721
theorem B3974561 : Blo 1766084 3974561 := bstep (se 2 (by rfl) ⟨1490460, by rfl⟩ : syracuseStep 3974561 = 2980921) B2980921
theorem B5965217 : Blo 1766084 5965217 := bstep (se 2 (by rfl) ⟨2236956, by rfl⟩ : syracuseStep 5965217 = 4473913) B4473913
theorem B5375393 : Blo 1766084 5375393 := bstep (se 2 (by rfl) ⟨2015772, by rfl⟩ : syracuseStep 5375393 = 4031545) B4031545
theorem B19097021 : Blo 1766084 19097021 := bstep (se 3 (by rfl) ⟨3580691, by rfl⟩ : syracuseStep 19097021 = 7161383) B7161383
theorem B3229345 : Blo 1766084 3229345 := bstep (se 2 (by rfl) ⟨1211004, by rfl⟩ : syracuseStep 3229345 = 2422009) B2422009
theorem B7546553 : Blo 1766084 7546553 := bstep (se 2 (by rfl) ⟨2829957, by rfl⟩ : syracuseStep 7546553 = 5659915) B5659915
theorem B6367031 : Blo 1766084 6367031 := bstep (se 1 (by rfl) ⟨4775273, by rfl⟩ : syracuseStep 6367031 = 9550547) B9550547
theorem B4245377 : Blo 1766084 4245377 := bstep (se 2 (by rfl) ⟨1592016, by rfl⟩ : syracuseStep 4245377 = 3184033) B3184033
theorem B3975119 : Blo 1766084 3975119 := bstep (se 1 (by rfl) ⟨2981339, by rfl⟩ : syracuseStep 3975119 = 5962679) B5962679
theorem B4245455 : Blo 1766084 4245455 := bstep (se 1 (by rfl) ⟨3184091, by rfl⟩ : syracuseStep 4245455 = 6368183) B6368183
theorem B8947745 : Blo 1766084 8947745 := bstep (se 2 (by rfl) ⟨3355404, by rfl⟩ : syracuseStep 8947745 = 6710809) B6710809
theorem B8947907 : Blo 1766084 8947907 := bstep (se 1 (by rfl) ⟨6710930, by rfl⟩ : syracuseStep 8947907 = 13421861) B13421861
theorem B3975497 : Blo 1766084 3975497 := bstep (se 2 (by rfl) ⟨1490811, by rfl⟩ : syracuseStep 3975497 = 2981623) B2981623
theorem B4475209 : Blo 1766084 4475209 := bstep (se 2 (by rfl) ⟨1678203, by rfl⟩ : syracuseStep 4475209 = 3356407) B3356407
theorem B3975515 : Blo 1766084 3975515 := bstep (se 1 (by rfl) ⟨2981636, by rfl⟩ : syracuseStep 3975515 = 5963273) B5963273
theorem B6818383 : Blo 1766084 6818383 := bstep (se 1 (by rfl) ⟨5113787, by rfl⟩ : syracuseStep 6818383 = 10227575) B10227575
theorem B11315933 : Blo 1766084 11315933 := bstep (se 3 (by rfl) ⟨2121737, by rfl⟩ : syracuseStep 11315933 = 4243475) B4243475
theorem B6712055 : Blo 1766084 6712055 := bstep (se 1 (by rfl) ⟨5034041, by rfl⟩ : syracuseStep 6712055 = 10068083) B10068083
theorem B3976091 : Blo 1766084 3976091 := bstep (se 1 (by rfl) ⟨2982068, by rfl⟩ : syracuseStep 3976091 = 5964137) B5964137
theorem B16976861 : Blo 1766084 16976861 := bstep (se 3 (by rfl) ⟨3183161, by rfl⟩ : syracuseStep 16976861 = 6366323) B6366323
theorem B3353575 : Blo 1766084 3353575 := bstep (se 1 (by rfl) ⟨2515181, by rfl⟩ : syracuseStep 3353575 = 5030363) B5030363
theorem B16976897 : Blo 1766084 16976897 := bstep (se 2 (by rfl) ⟨6366336, by rfl⟩ : syracuseStep 16976897 = 12732673) B12732673
theorem B3976289 : Blo 1766084 3976289 := bstep (se 2 (by rfl) ⟨1491108, by rfl⟩ : syracuseStep 3976289 = 2982217) B2982217
theorem B15101099 : Blo 1766084 15101099 := bstep (se 1 (by rfl) ⟨11325824, by rfl⟩ : syracuseStep 15101099 = 22651649) B22651649
theorem B19360987 : Blo 1766084 19360987 := bstep (se 1 (by rfl) ⟨14520740, by rfl⟩ : syracuseStep 19360987 = 29041481) B29041481
theorem B2649383 : Blo 1766084 2649383 := bstep (se 1 (by rfl) ⟨1987037, by rfl⟩ : syracuseStep 2649383 = 3974075) B3974075
theorem B3976487 : Blo 1766084 3976487 := bstep (se 1 (by rfl) ⟨2982365, by rfl⟩ : syracuseStep 3976487 = 5964731) B5964731
theorem B7548227 : Blo 1766084 7548227 := bstep (se 1 (by rfl) ⟨5661170, by rfl⟩ : syracuseStep 7548227 = 11322341) B11322341
theorem B7261559 : Blo 1766084 7261559 := bstep (se 1 (by rfl) ⟨5446169, by rfl⟩ : syracuseStep 7261559 = 10892339) B10892339
theorem B2649467 : Blo 1766084 2649467 := bstep (se 1 (by rfl) ⟨1987100, by rfl⟩ : syracuseStep 2649467 = 3974201) B3974201
theorem B2649593 : Blo 1766084 2649593 := bstep (se 2 (by rfl) ⟨993597, by rfl⟩ : syracuseStep 2649593 = 1987195) B1987195
theorem B22957577 : Blo 1766084 22957577 := bstep (se 2 (by rfl) ⟨8609091, by rfl⟩ : syracuseStep 22957577 = 17218183) B17218183
theorem B2649695 : Blo 1766084 2649695 := bstep (se 1 (by rfl) ⟨1987271, by rfl⟩ : syracuseStep 2649695 = 3974543) B3974543
theorem B2829919 : Blo 1766084 2829919 := bstep (se 1 (by rfl) ⟨2122439, by rfl⟩ : syracuseStep 2829919 = 4244879) B4244879
theorem B3976865 : Blo 1766084 3976865 := bstep (se 2 (by rfl) ⟨1491324, by rfl⟩ : syracuseStep 3976865 = 2982649) B2982649
theorem B8941265 : Blo 1766084 8941265 := bstep (se 2 (by rfl) ⟨3352974, by rfl⟩ : syracuseStep 8941265 = 6705949) B6705949
theorem B5033735 : Blo 1766084 5033735 := bstep (se 1 (by rfl) ⟨3775301, by rfl⟩ : syracuseStep 5033735 = 7550603) B7550603
theorem B13422347 : Blo 1766084 13422347 := bstep (se 1 (by rfl) ⟨10066760, by rfl⟩ : syracuseStep 13422347 = 20133521) B20133521
theorem B16125743 : Blo 1766084 16125743 := bstep (se 1 (by rfl) ⟨12094307, by rfl⟩ : syracuseStep 16125743 = 24188615) B24188615
theorem B2649911 : Blo 1766084 2649911 := bstep (se 1 (by rfl) ⟨1987433, by rfl⟩ : syracuseStep 2649911 = 3974867) B3974867
theorem B1413828503 : Blo 1766084 1413828503 := bstep (se 1 (by rfl) ⟨1060371377, by rfl⟩ : syracuseStep 1413828503 = 2120742755) B2120742755
theorem B3977225 : Blo 1766084 3977225 := bstep (se 2 (by rfl) ⟨1491459, by rfl⟩ : syracuseStep 3977225 = 2982919) B2982919
theorem B12095513 : Blo 1766084 12095513 := bstep (se 2 (by rfl) ⟨4535817, by rfl⟩ : syracuseStep 12095513 = 9071635) B9071635
theorem B11317315 : Blo 1766084 11317315 := bstep (se 1 (by rfl) ⟨8487986, by rfl⟩ : syracuseStep 11317315 = 16975973) B16975973
theorem B2650217 : Blo 1766084 2650217 := bstep (se 2 (by rfl) ⟨993831, by rfl⟩ : syracuseStep 2650217 = 1987663) B1987663
theorem B13414571 : Blo 1766084 13414571 := bstep (se 1 (by rfl) ⟨10060928, by rfl⟩ : syracuseStep 13414571 = 20121857) B20121857
theorem B12087467 : Blo 1766084 12087467 := bstep (se 1 (by rfl) ⟨9065600, by rfl⟩ : syracuseStep 12087467 = 18131201) B18131201
theorem B1986907 : Blo 1766084 1986907 := bstep (se 1 (by rfl) ⟨1490180, by rfl⟩ : syracuseStep 1986907 = 2980361) B2980361
theorem B33968483 : Blo 1766084 33968483 := bstep (se 1 (by rfl) ⟨25476362, by rfl⟩ : syracuseStep 33968483 = 50952725) B50952725
theorem B2650535 : Blo 1766084 2650535 := bstep (se 1 (by rfl) ⟨1987901, by rfl⟩ : syracuseStep 2650535 = 3975803) B3975803
theorem B3977639 : Blo 1766084 3977639 := bstep (se 1 (by rfl) ⟨2983229, by rfl⟩ : syracuseStep 3977639 = 5966459) B5966459
theorem B1987015 : Blo 1766084 1987015 := bstep (se 1 (by rfl) ⟨1490261, by rfl⟩ : syracuseStep 1987015 = 2980523) B2980523
theorem B2650619 : Blo 1766084 2650619 := bstep (se 1 (by rfl) ⟨1987964, by rfl⟩ : syracuseStep 2650619 = 3975929) B3975929
theorem B3977747 : Blo 1766084 3977747 := bstep (se 1 (by rfl) ⟨2983310, by rfl⟩ : syracuseStep 3977747 = 5966621) B5966621
theorem B3977801 : Blo 1766084 3977801 := bstep (se 2 (by rfl) ⟨1491675, by rfl⟩ : syracuseStep 3977801 = 2983351) B2983351
theorem B2650745 : Blo 1766084 2650745 := bstep (se 2 (by rfl) ⟨994029, by rfl⟩ : syracuseStep 2650745 = 1988059) B1988059
theorem B2830969 : Blo 1766084 2830969 := bstep (se 2 (by rfl) ⟨1061613, by rfl⟩ : syracuseStep 2830969 = 2123227) B2123227
theorem B2650799 : Blo 1766084 2650799 := bstep (se 1 (by rfl) ⟨1988099, by rfl⟩ : syracuseStep 2650799 = 3976199) B3976199
theorem B1766111 : Blo 1766084 1766111 := bstep (se 1 (by rfl) ⟨1324583, by rfl⟩ : syracuseStep 1766111 = 2649167) B2649167
theorem B2650847 : Blo 1766084 2650847 := bstep (se 1 (by rfl) ⟨1988135, by rfl⟩ : syracuseStep 2650847 = 3976271) B3976271
theorem B1766191 : Blo 1766084 1766191 := bstep (se 1 (by rfl) ⟨1324643, by rfl⟩ : syracuseStep 1766191 = 2649287) B2649287
theorem B1987375 : Blo 1766084 1987375 := bstep (se 1 (by rfl) ⟨1490531, by rfl⟩ : syracuseStep 1987375 = 2981063) B2981063
theorem B8491871 : Blo 1766084 8491871 := bstep (se 1 (by rfl) ⟨6368903, by rfl⟩ : syracuseStep 8491871 = 12737807) B12737807
theorem B1766299 : Blo 1766084 1766299 := bstep (se 1 (by rfl) ⟨1324724, by rfl⟩ : syracuseStep 1766299 = 2649449) B2649449
theorem B1987483 : Blo 1766084 1987483 := bstep (se 1 (by rfl) ⟨1490612, by rfl⟩ : syracuseStep 1987483 = 2981225) B2981225
theorem B1766351 : Blo 1766084 1766351 := bstep (se 1 (by rfl) ⟨1324763, by rfl⟩ : syracuseStep 1766351 = 2649527) B2649527
theorem B1766375 : Blo 1766084 1766375 := bstep (se 1 (by rfl) ⟨1324781, by rfl⟩ : syracuseStep 1766375 = 2649563) B2649563
theorem B2651111 : Blo 1766084 2651111 := bstep (se 1 (by rfl) ⟨1988333, by rfl⟩ : syracuseStep 2651111 = 3976667) B3976667
theorem B2651369 : Blo 1766084 2651369 := bstep (se 2 (by rfl) ⟨994263, by rfl⟩ : syracuseStep 2651369 = 1988527) B1988527
theorem B1766687 : Blo 1766084 1766687 := bstep (se 1 (by rfl) ⟨1325015, by rfl⟩ : syracuseStep 1766687 = 2650031) B2650031
theorem B2651423 : Blo 1766084 2651423 := bstep (se 1 (by rfl) ⟨1988567, by rfl⟩ : syracuseStep 2651423 = 3977135) B3977135
theorem B1987879 : Blo 1766084 1987879 := bstep (se 1 (by rfl) ⟨1490909, by rfl⟩ : syracuseStep 1987879 = 2981819) B2981819
theorem B1766747 : Blo 1766084 1766747 := bstep (se 1 (by rfl) ⟨1325060, by rfl⟩ : syracuseStep 1766747 = 2650121) B2650121
theorem B9549161 : Blo 1766084 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B1766767 : Blo 1766084 1766767 := bstep (se 1 (by rfl) ⟨1325075, by rfl⟩ : syracuseStep 1766767 = 2650151) B2650151
theorem B1987951 : Blo 1766084 1987951 := bstep (se 1 (by rfl) ⟨1490963, by rfl⟩ : syracuseStep 1987951 = 2981927) B2981927
theorem B6370721 : Blo 1766084 6370721 := bstep (se 2 (by rfl) ⟨2389020, by rfl⟩ : syracuseStep 6370721 = 4778041) B4778041
theorem B1766823 : Blo 1766084 1766823 := bstep (se 1 (by rfl) ⟨1325117, by rfl⟩ : syracuseStep 1766823 = 2650235) B2650235
theorem B2651591 : Blo 1766084 2651591 := bstep (se 1 (by rfl) ⟨1988693, by rfl⟩ : syracuseStep 2651591 = 3977387) B3977387
theorem B8492525 : Blo 1766084 8492525 := bstep (se 3 (by rfl) ⟨1592348, by rfl⟩ : syracuseStep 8492525 = 3184697) B3184697
theorem B10483181 : Blo 1766084 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B1766907 : Blo 1766084 1766907 := bstep (se 1 (by rfl) ⟨1325180, by rfl⟩ : syracuseStep 1766907 = 2650361) B2650361
theorem B1766975 : Blo 1766084 1766975 := bstep (se 1 (by rfl) ⟨1325231, by rfl⟩ : syracuseStep 1766975 = 2650463) B2650463
theorem B1766983 : Blo 1766084 1766983 := bstep (se 1 (by rfl) ⟨1325237, by rfl⟩ : syracuseStep 1766983 = 2650475) B2650475
theorem B1988167 : Blo 1766084 1988167 := bstep (se 1 (by rfl) ⟨1491125, by rfl⟩ : syracuseStep 1988167 = 2982251) B2982251
theorem B3356255 : Blo 1766084 3356255 := bstep (se 1 (by rfl) ⟨2517191, by rfl⟩ : syracuseStep 3356255 = 5034383) B5034383
theorem B2832059 : Blo 1766084 2832059 := bstep (se 1 (by rfl) ⟨2124044, by rfl⟩ : syracuseStep 2832059 = 4248089) B4248089
theorem B1767135 : Blo 1766084 1767135 := bstep (se 1 (by rfl) ⟨1325351, by rfl⟩ : syracuseStep 1767135 = 2650703) B2650703
theorem B2651945 : Blo 1766084 2651945 := bstep (se 2 (by rfl) ⟨994479, by rfl⟩ : syracuseStep 2651945 = 1988959) B1988959
theorem B1767215 : Blo 1766084 1767215 := bstep (se 1 (by rfl) ⟨1325411, by rfl⟩ : syracuseStep 1767215 = 2650823) B2650823
theorem B2651951 : Blo 1766084 2651951 := bstep (se 1 (by rfl) ⟨1988963, by rfl⟩ : syracuseStep 2651951 = 3977927) B3977927
theorem B1767323 : Blo 1766084 1767323 := bstep (se 1 (by rfl) ⟨1325492, by rfl⟩ : syracuseStep 1767323 = 2650985) B2650985
theorem B1767375 : Blo 1766084 1767375 := bstep (se 1 (by rfl) ⟨1325531, by rfl⟩ : syracuseStep 1767375 = 2651063) B2651063
theorem B7550927 : Blo 1766084 7550927 := bstep (se 1 (by rfl) ⟨5663195, by rfl⟩ : syracuseStep 7550927 = 11326391) B11326391
theorem B1767399 : Blo 1766084 1767399 := bstep (se 1 (by rfl) ⟨1325549, by rfl⟩ : syracuseStep 1767399 = 2651099) B2651099
theorem B5961761 : Blo 1766084 5961761 := bstep (se 2 (by rfl) ⟨2235660, by rfl⟩ : syracuseStep 5961761 = 4471321) B4471321
theorem B96679979 : Blo 1766084 96679979 := bstep (se 1 (by rfl) ⟨72509984, by rfl⟩ : syracuseStep 96679979 = 145019969) B145019969
theorem B8943695 : Blo 1766084 8943695 := bstep (se 1 (by rfl) ⟨6707771, by rfl⟩ : syracuseStep 8943695 = 13415543) B13415543
theorem B1767711 : Blo 1766084 1767711 := bstep (se 1 (by rfl) ⟨1325783, by rfl⟩ : syracuseStep 1767711 = 2651567) B2651567
theorem B1767771 : Blo 1766084 1767771 := bstep (se 1 (by rfl) ⟨1325828, by rfl⟩ : syracuseStep 1767771 = 2651657) B2651657
theorem B1767791 : Blo 1766084 1767791 := bstep (se 1 (by rfl) ⟨1325843, by rfl⟩ : syracuseStep 1767791 = 2651687) B2651687
theorem B1767847 : Blo 1766084 1767847 := bstep (se 1 (by rfl) ⟨1325885, by rfl⟩ : syracuseStep 1767847 = 2651771) B2651771
theorem B1989031 : Blo 1766084 1989031 := bstep (se 1 (by rfl) ⟨1491773, by rfl⟩ : syracuseStep 1989031 = 2983547) B2983547
theorem B3824047 : Blo 1766084 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B1767931 : Blo 1766084 1767931 := bstep (se 1 (by rfl) ⟨1325948, by rfl⟩ : syracuseStep 1767931 = 2651897) B2651897
theorem B2980415 : Blo 1766084 2980415 := bstep (se 1 (by rfl) ⟨2235311, by rfl⟩ : syracuseStep 2980415 = 4470623) B4470623
theorem B1767999 : Blo 1766084 1767999 := bstep (se 1 (by rfl) ⟨1325999, by rfl⟩ : syracuseStep 1767999 = 2651999) B2651999
theorem B1768007 : Blo 1766084 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B16980587 : Blo 1766084 16980587 := bstep (se 1 (by rfl) ⟨12735440, by rfl⟩ : syracuseStep 16980587 = 25470881) B25470881
theorem B42965761 : Blo 1766084 42965761 := bstep (se 2 (by rfl) ⟨16112160, by rfl⟩ : syracuseStep 42965761 = 32224321) B32224321
theorem B9681731 : Blo 1766084 9681731 := bstep (se 1 (by rfl) ⟨7261298, by rfl⟩ : syracuseStep 9681731 = 14522597) B14522597
theorem B2235215 : Blo 1766084 2235215 := bstep (se 1 (by rfl) ⟨1676411, by rfl⟩ : syracuseStep 2235215 = 3352823) B3352823
theorem B10058651 : Blo 1766084 10058651 := bstep (se 1 (by rfl) ⟨7543988, by rfl⟩ : syracuseStep 10058651 = 15087977) B15087977
theorem B5102507 : Blo 1766084 5102507 := bstep (se 1 (by rfl) ⟨3826880, by rfl⟩ : syracuseStep 5102507 = 7653761) B7653761
theorem B2235367 : Blo 1766084 2235367 := bstep (se 1 (by rfl) ⟨1676525, by rfl⟩ : syracuseStep 2235367 = 3353051) B3353051
theorem B3021799 : Blo 1766084 3021799 := bstep (se 1 (by rfl) ⟨2266349, by rfl⟩ : syracuseStep 3021799 = 4532699) B4532699
theorem B8944829 : Blo 1766084 8944829 := bstep (se 3 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 8944829 = 3354311) B3354311
theorem B2981083 : Blo 1766084 2981083 := bstep (se 1 (by rfl) ⟨2235812, by rfl⟩ : syracuseStep 2981083 = 4471625) B4471625
theorem B17219087 : Blo 1766084 17219087 := bstep (se 1 (by rfl) ⟨12914315, by rfl⟩ : syracuseStep 17219087 = 25828631) B25828631
theorem B13426235 : Blo 1766084 13426235 := bstep (se 1 (by rfl) ⟨10069676, by rfl⟩ : syracuseStep 13426235 = 20139353) B20139353
theorem B3776095 : Blo 1766084 3776095 := bstep (se 1 (by rfl) ⟨2832071, by rfl⟩ : syracuseStep 3776095 = 5664143) B5664143
theorem B128933491 : Blo 1766084 128933491 := bstep (se 1 (by rfl) ⟨96700118, by rfl⟩ : syracuseStep 128933491 = 193400237) B193400237
theorem B6708851 : Blo 1766084 6708851 := bstep (se 1 (by rfl) ⟨5031638, by rfl⟩ : syracuseStep 6708851 = 10063277) B10063277
theorem B21487265 : Blo 1766084 21487265 := bstep (se 2 (by rfl) ⟨8057724, by rfl⟩ : syracuseStep 21487265 = 16115449) B16115449
theorem B8494753 : Blo 1766084 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B14335649 : Blo 1766084 14335649 := bstep (se 2 (by rfl) ⟨5375868, by rfl⟩ : syracuseStep 14335649 = 10751737) B10751737
theorem B4472617 : Blo 1766084 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B42983297 : Blo 1766084 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B2981839 : Blo 1766084 2981839 := bstep (se 1 (by rfl) ⟨2236379, by rfl⟩ : syracuseStep 2981839 = 4472759) B4472759
theorem B15089753 : Blo 1766084 15089753 := bstep (se 2 (by rfl) ⟨5658657, by rfl⟩ : syracuseStep 15089753 = 11317315) B11317315
theorem B2982271 : Blo 1766084 2982271 := bstep (se 1 (by rfl) ⟨2236703, by rfl⟩ : syracuseStep 2982271 = 4473407) B4473407
theorem B5661247 : Blo 1766084 5661247 := bstep (se 1 (by rfl) ⟨4245935, by rfl⟩ : syracuseStep 5661247 = 8491871) B8491871
theorem B15098501 : Blo 1766084 15098501 := bstep (se 4 (by rfl) ⟨1415484, by rfl⟩ : syracuseStep 15098501 = 2830969) B2830969
theorem B11322031 : Blo 1766084 11322031 := bstep (se 1 (by rfl) ⟨8491523, by rfl⟩ : syracuseStep 11322031 = 16983047) B16983047
theorem B2982703 : Blo 1766084 2982703 := bstep (se 1 (by rfl) ⟨2237027, by rfl⟩ : syracuseStep 2982703 = 4474055) B4474055
theorem B6366107 : Blo 1766084 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B13419431 : Blo 1766084 13419431 := bstep (se 1 (by rfl) ⟨10064573, by rfl⟩ : syracuseStep 13419431 = 20129147) B20129147
theorem B12731347 : Blo 1766084 12731347 := bstep (se 1 (by rfl) ⟨9548510, by rfl⟩ : syracuseStep 12731347 = 19097021) B19097021
theorem B5661683 : Blo 1766084 5661683 := bstep (se 1 (by rfl) ⟨4246262, by rfl⟩ : syracuseStep 5661683 = 8492525) B8492525
theorem B6988787 : Blo 1766084 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B57287681 : Blo 1766084 57287681 := bstep (se 2 (by rfl) ⟨21482880, by rfl⟩ : syracuseStep 57287681 = 42965761) B42965761
theorem B5031035 : Blo 1766084 5031035 := bstep (se 1 (by rfl) ⟨3773276, by rfl⟩ : syracuseStep 5031035 = 7546553) B7546553
theorem B4244687 : Blo 1766084 4244687 := bstep (se 1 (by rfl) ⟨3183515, by rfl⟩ : syracuseStep 4244687 = 6367031) B6367031
theorem B3974507 : Blo 1766084 3974507 := bstep (se 1 (by rfl) ⟨2980880, by rfl⟩ : syracuseStep 3974507 = 5961761) B5961761
theorem B5965163 : Blo 1766084 5965163 := bstep (se 1 (by rfl) ⟨4473872, by rfl⟩ : syracuseStep 5965163 = 8947745) B8947745
theorem B5965271 : Blo 1766084 5965271 := bstep (se 1 (by rfl) ⟨4473953, by rfl⟩ : syracuseStep 5965271 = 8947907) B8947907
theorem B3974777 : Blo 1766084 3974777 := bstep (se 2 (by rfl) ⟨1490541, by rfl⟩ : syracuseStep 3974777 = 2981083) B2981083
theorem B5965433 : Blo 1766084 5965433 := bstep (se 2 (by rfl) ⟨2237037, by rfl⟩ : syracuseStep 5965433 = 4474075) B4474075
theorem B4474703 : Blo 1766084 4474703 := bstep (se 1 (by rfl) ⟨3356027, by rfl⟩ : syracuseStep 4474703 = 6712055) B6712055
theorem B3401671 : Blo 1766084 3401671 := bstep (se 1 (by rfl) ⟨2551253, by rfl⟩ : syracuseStep 3401671 = 5102507) B5102507
theorem B171911321 : Blo 1766084 171911321 := bstep (se 2 (by rfl) ⟨64466745, by rfl⟩ : syracuseStep 171911321 = 128933491) B128933491
theorem B5032151 : Blo 1766084 5032151 := bstep (se 1 (by rfl) ⟨3774113, by rfl⟩ : syracuseStep 5032151 = 7548227) B7548227
theorem B15305051 : Blo 1766084 15305051 := bstep (se 1 (by rfl) ⟨11478788, by rfl⟩ : syracuseStep 15305051 = 22957577) B22957577
theorem B11479391 : Blo 1766084 11479391 := bstep (se 1 (by rfl) ⟨8609543, by rfl⟩ : syracuseStep 11479391 = 17219087) B17219087
theorem B8948231 : Blo 1766084 8948231 := bstep (se 1 (by rfl) ⟨6711173, by rfl⟩ : syracuseStep 8948231 = 13422347) B13422347
theorem B10750495 : Blo 1766084 10750495 := bstep (se 1 (by rfl) ⟨8062871, by rfl⟩ : syracuseStep 10750495 = 16125743) B16125743
theorem B3975785 : Blo 1766084 3975785 := bstep (se 2 (by rfl) ⟨1490919, by rfl⟩ : syracuseStep 3975785 = 2981839) B2981839
theorem B8063675 : Blo 1766084 8063675 := bstep (se 1 (by rfl) ⟨6047756, by rfl⟩ : syracuseStep 8063675 = 12095513) B12095513
theorem B21490379 : Blo 1766084 21490379 := bstep (se 1 (by rfl) ⟨16117784, by rfl⟩ : syracuseStep 21490379 = 32235569) B32235569
theorem B22645655 : Blo 1766084 22645655 := bstep (se 1 (by rfl) ⟨16984241, by rfl⟩ : syracuseStep 22645655 = 33968483) B33968483
theorem B72526913 : Blo 1766084 72526913 := bstep (se 2 (by rfl) ⟨27197592, by rfl⟩ : syracuseStep 72526913 = 54395185) B54395185
theorem B5966945 : Blo 1766084 5966945 := bstep (se 2 (by rfl) ⟨2237604, by rfl⟩ : syracuseStep 5966945 = 4475209) B4475209
theorem B2649209 : Blo 1766084 2649209 := bstep (se 2 (by rfl) ⟨993453, by rfl⟩ : syracuseStep 2649209 = 1986907) B1986907
theorem B2649311 : Blo 1766084 2649311 := bstep (se 1 (by rfl) ⟨1986983, by rfl⟩ : syracuseStep 2649311 = 3973967) B3973967
theorem B3976415 : Blo 1766084 3976415 := bstep (se 1 (by rfl) ⟨2982311, by rfl⟩ : syracuseStep 3976415 = 5964623) B5964623
theorem B5098729 : Blo 1766084 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B2649353 : Blo 1766084 2649353 := bstep (se 2 (by rfl) ⟨993507, by rfl⟩ : syracuseStep 2649353 = 1987015) B1987015
theorem B9071959 : Blo 1766084 9071959 := bstep (se 1 (by rfl) ⟨6803969, by rfl⟩ : syracuseStep 9071959 = 13607939) B13607939
theorem B2649455 : Blo 1766084 2649455 := bstep (se 1 (by rfl) ⟨1987091, by rfl⟩ : syracuseStep 2649455 = 3974183) B3974183
theorem B3976631 : Blo 1766084 3976631 := bstep (se 1 (by rfl) ⟨2982473, by rfl⟩ : syracuseStep 3976631 = 5964947) B5964947
theorem B2649575 : Blo 1766084 2649575 := bstep (se 1 (by rfl) ⟨1987181, by rfl⟩ : syracuseStep 2649575 = 3974363) B3974363
theorem B6368759 : Blo 1766084 6368759 := bstep (se 1 (by rfl) ⟨4776569, by rfl⟩ : syracuseStep 6368759 = 9553139) B9553139
theorem B2649707 : Blo 1766084 2649707 := bstep (se 1 (by rfl) ⟨1987280, by rfl⟩ : syracuseStep 2649707 = 3974561) B3974561
theorem B3976811 : Blo 1766084 3976811 := bstep (se 1 (by rfl) ⟨2982608, by rfl⟩ : syracuseStep 3976811 = 5965217) B5965217
theorem B4247147 : Blo 1766084 4247147 := bstep (se 1 (by rfl) ⟨3185360, by rfl⟩ : syracuseStep 4247147 = 6370721) B6370721
theorem B3583595 : Blo 1766084 3583595 := bstep (se 1 (by rfl) ⟨2687696, by rfl⟩ : syracuseStep 3583595 = 5375393) B5375393
theorem B2649833 : Blo 1766084 2649833 := bstep (se 2 (by rfl) ⟨993687, by rfl⟩ : syracuseStep 2649833 = 1987375) B1987375
theorem B1888039 : Blo 1766084 1888039 := bstep (se 1 (by rfl) ⟨1416029, by rfl⟩ : syracuseStep 1888039 = 2832059) B2832059
theorem B2649977 : Blo 1766084 2649977 := bstep (se 2 (by rfl) ⟨993741, by rfl⟩ : syracuseStep 2649977 = 1987483) B1987483
theorem B3977081 : Blo 1766084 3977081 := bstep (se 2 (by rfl) ⟨1491405, by rfl⟩ : syracuseStep 3977081 = 2982811) B2982811
theorem B2650079 : Blo 1766084 2650079 := bstep (se 1 (by rfl) ⟨1987559, by rfl⟩ : syracuseStep 2650079 = 3975119) B3975119
theorem B2830303 : Blo 1766084 2830303 := bstep (se 1 (by rfl) ⟨2122727, by rfl⟩ : syracuseStep 2830303 = 4245455) B4245455
theorem B5033951 : Blo 1766084 5033951 := bstep (se 1 (by rfl) ⟨3775463, by rfl⟩ : syracuseStep 5033951 = 7550927) B7550927
theorem B2650331 : Blo 1766084 2650331 := bstep (se 1 (by rfl) ⟨1987748, by rfl⟩ : syracuseStep 2650331 = 3975497) B3975497
theorem B2650343 : Blo 1766084 2650343 := bstep (se 1 (by rfl) ⟨1987757, by rfl⟩ : syracuseStep 2650343 = 3975515) B3975515
theorem B8950013 : Blo 1766084 8950013 := bstep (se 3 (by rfl) ⟨1678127, by rfl⟩ : syracuseStep 8950013 = 3356255) B3356255
theorem B1986943 : Blo 1766084 1986943 := bstep (se 1 (by rfl) ⟨1490207, by rfl⟩ : syracuseStep 1986943 = 2980415) B2980415
theorem B2650505 : Blo 1766084 2650505 := bstep (se 2 (by rfl) ⟨993939, by rfl⟩ : syracuseStep 2650505 = 1987879) B1987879
theorem B2650601 : Blo 1766084 2650601 := bstep (se 2 (by rfl) ⟨993975, by rfl⟩ : syracuseStep 2650601 = 1987951) B1987951
theorem B6705767 : Blo 1766084 6705767 := bstep (se 1 (by rfl) ⟨5029325, by rfl⟩ : syracuseStep 6705767 = 10058651) B10058651
theorem B2650727 : Blo 1766084 2650727 := bstep (se 1 (by rfl) ⟨1988045, by rfl⟩ : syracuseStep 2650727 = 3976091) B3976091
theorem B11317907 : Blo 1766084 11317907 := bstep (se 1 (by rfl) ⟨8488430, by rfl⟩ : syracuseStep 11317907 = 16976861) B16976861
theorem B11317931 : Blo 1766084 11317931 := bstep (se 1 (by rfl) ⟨8488448, by rfl⟩ : syracuseStep 11317931 = 16976897) B16976897
theorem B2650859 : Blo 1766084 2650859 := bstep (se 1 (by rfl) ⟨1988144, by rfl⟩ : syracuseStep 2650859 = 3976289) B3976289
theorem B2650889 : Blo 1766084 2650889 := bstep (se 2 (by rfl) ⟨994083, by rfl⟩ : syracuseStep 2650889 = 1988167) B1988167
theorem B3773225 : Blo 1766084 3773225 := bstep (se 2 (by rfl) ⟨1414959, by rfl⟩ : syracuseStep 3773225 = 2829919) B2829919
theorem B5034793 : Blo 1766084 5034793 := bstep (se 2 (by rfl) ⟨1888047, by rfl⟩ : syracuseStep 5034793 = 3776095) B3776095
theorem B1766255 : Blo 1766084 1766255 := bstep (se 1 (by rfl) ⟨1324691, by rfl⟩ : syracuseStep 1766255 = 2649383) B2649383
theorem B2650991 : Blo 1766084 2650991 := bstep (se 1 (by rfl) ⟨1988243, by rfl⟩ : syracuseStep 2650991 = 3976487) B3976487
theorem B5960573 : Blo 1766084 5960573 := bstep (se 3 (by rfl) ⟨1117607, by rfl⟩ : syracuseStep 5960573 = 2235215) B2235215
theorem B11326337 : Blo 1766084 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B4305793 : Blo 1766084 4305793 := bstep (se 2 (by rfl) ⟨1614672, by rfl⟩ : syracuseStep 4305793 = 3229345) B3229345
theorem B1766311 : Blo 1766084 1766311 := bstep (se 1 (by rfl) ⟨1324733, by rfl⟩ : syracuseStep 1766311 = 2649467) B2649467
theorem B1766395 : Blo 1766084 1766395 := bstep (se 1 (by rfl) ⟨1324796, by rfl⟩ : syracuseStep 1766395 = 2649593) B2649593
theorem B8950823 : Blo 1766084 8950823 := bstep (se 1 (by rfl) ⟨6713117, by rfl⟩ : syracuseStep 8950823 = 13426235) B13426235
theorem B1766463 : Blo 1766084 1766463 := bstep (se 1 (by rfl) ⟨1324847, by rfl⟩ : syracuseStep 1766463 = 2649695) B2649695
theorem B14324843 : Blo 1766084 14324843 := bstep (se 1 (by rfl) ⟨10743632, by rfl⟩ : syracuseStep 14324843 = 21487265) B21487265
theorem B2651243 : Blo 1766084 2651243 := bstep (se 1 (by rfl) ⟨1988432, by rfl⟩ : syracuseStep 2651243 = 3976865) B3976865
theorem B9557099 : Blo 1766084 9557099 := bstep (se 1 (by rfl) ⟨7167824, by rfl⟩ : syracuseStep 9557099 = 14335649) B14335649
theorem B5960843 : Blo 1766084 5960843 := bstep (se 1 (by rfl) ⟨4470632, by rfl⟩ : syracuseStep 5960843 = 8941265) B8941265
theorem B3355823 : Blo 1766084 3355823 := bstep (se 1 (by rfl) ⟨2516867, by rfl⟩ : syracuseStep 3355823 = 5033735) B5033735
theorem B1766607 : Blo 1766084 1766607 := bstep (se 1 (by rfl) ⟨1324955, by rfl⟩ : syracuseStep 1766607 = 2649911) B2649911
theorem B942552335 : Blo 1766084 942552335 := bstep (se 1 (by rfl) ⟨706914251, by rfl⟩ : syracuseStep 942552335 = 1413828503) B1413828503
theorem B2651483 : Blo 1766084 2651483 := bstep (se 1 (by rfl) ⟨1988612, by rfl⟩ : syracuseStep 2651483 = 3977225) B3977225
theorem B1766811 : Blo 1766084 1766811 := bstep (se 1 (by rfl) ⟨1325108, by rfl⟩ : syracuseStep 1766811 = 2650217) B2650217
theorem B8943047 : Blo 1766084 8943047 := bstep (se 1 (by rfl) ⟨6707285, by rfl⟩ : syracuseStep 8943047 = 13414571) B13414571
theorem B8058311 : Blo 1766084 8058311 := bstep (se 1 (by rfl) ⟨6043733, by rfl⟩ : syracuseStep 8058311 = 12087467) B12087467
theorem B1767023 : Blo 1766084 1767023 := bstep (se 1 (by rfl) ⟨1325267, by rfl⟩ : syracuseStep 1767023 = 2650535) B2650535
theorem B2651759 : Blo 1766084 2651759 := bstep (se 1 (by rfl) ⟨1988819, by rfl⟩ : syracuseStep 2651759 = 3977639) B3977639
theorem B1767079 : Blo 1766084 1767079 := bstep (se 1 (by rfl) ⟨1325309, by rfl⟩ : syracuseStep 1767079 = 2650619) B2650619
theorem B2651831 : Blo 1766084 2651831 := bstep (se 1 (by rfl) ⟨1988873, by rfl⟩ : syracuseStep 2651831 = 3977747) B3977747
theorem B2651867 : Blo 1766084 2651867 := bstep (se 1 (by rfl) ⟨1988900, by rfl⟩ : syracuseStep 2651867 = 3977801) B3977801
theorem B1767163 : Blo 1766084 1767163 := bstep (se 1 (by rfl) ⟨1325372, by rfl⟩ : syracuseStep 1767163 = 2650745) B2650745
theorem B1988347 : Blo 1766084 1988347 := bstep (se 1 (by rfl) ⟨1491260, by rfl⟩ : syracuseStep 1988347 = 2982521) B2982521
theorem B1767199 : Blo 1766084 1767199 := bstep (se 1 (by rfl) ⟨1325399, by rfl⟩ : syracuseStep 1767199 = 2650799) B2650799
theorem B1988383 : Blo 1766084 1988383 := bstep (se 1 (by rfl) ⟨1491287, by rfl⟩ : syracuseStep 1988383 = 2982575) B2982575
theorem B1767231 : Blo 1766084 1767231 := bstep (se 1 (by rfl) ⟨1325423, by rfl⟩ : syracuseStep 1767231 = 2650847) B2650847
theorem B2652041 : Blo 1766084 2652041 := bstep (se 2 (by rfl) ⟨994515, by rfl⟩ : syracuseStep 2652041 = 1989031) B1989031
theorem B15095767 : Blo 1766084 15095767 := bstep (se 1 (by rfl) ⟨11321825, by rfl⟩ : syracuseStep 15095767 = 22643651) B22643651
theorem B1767407 : Blo 1766084 1767407 := bstep (se 1 (by rfl) ⟨1325555, by rfl⟩ : syracuseStep 1767407 = 2651111) B2651111
theorem B6707225 : Blo 1766084 6707225 := bstep (se 2 (by rfl) ⟨2515209, by rfl⟩ : syracuseStep 6707225 = 5030419) B5030419
theorem B9091177 : Blo 1766084 9091177 := bstep (se 2 (by rfl) ⟨3409191, by rfl⟩ : syracuseStep 9091177 = 6818383) B6818383
theorem B1767579 : Blo 1766084 1767579 := bstep (se 1 (by rfl) ⟨1325684, by rfl⟩ : syracuseStep 1767579 = 2651369) B2651369
theorem B1767615 : Blo 1766084 1767615 := bstep (se 1 (by rfl) ⟨1325711, by rfl⟩ : syracuseStep 1767615 = 2651423) B2651423
theorem B1767727 : Blo 1766084 1767727 := bstep (se 1 (by rfl) ⟨1325795, by rfl⟩ : syracuseStep 1767727 = 2651591) B2651591
theorem B103258597 : Blo 1766084 103258597 := bstep (se 4 (by rfl) ⟨9680493, by rfl⟩ : syracuseStep 103258597 = 19360987) B19360987
theorem B1767963 : Blo 1766084 1767963 := bstep (se 1 (by rfl) ⟨1325972, by rfl⟩ : syracuseStep 1767963 = 2651945) B2651945
theorem B1767967 : Blo 1766084 1767967 := bstep (se 1 (by rfl) ⟨1325975, by rfl⟩ : syracuseStep 1767967 = 2651951) B2651951
theorem B2980489 : Blo 1766084 2980489 := bstep (se 2 (by rfl) ⟨1117683, by rfl⟩ : syracuseStep 2980489 = 2235367) B2235367
theorem B4471433 : Blo 1766084 4471433 := bstep (se 2 (by rfl) ⟨1676787, by rfl⟩ : syracuseStep 4471433 = 3353575) B3353575
theorem B4029065 : Blo 1766084 4029065 := bstep (se 2 (by rfl) ⟨1510899, by rfl⟩ : syracuseStep 4029065 = 3021799) B3021799
theorem B45284021 : Blo 1766084 45284021 := bstep (se 5 (by rfl) ⟨2122688, by rfl⟩ : syracuseStep 45284021 = 4245377) B4245377
theorem B64453319 : Blo 1766084 64453319 := bstep (se 1 (by rfl) ⟨48339989, by rfl⟩ : syracuseStep 64453319 = 96679979) B96679979
theorem B5962463 : Blo 1766084 5962463 := bstep (se 1 (by rfl) ⟨4471847, by rfl⟩ : syracuseStep 5962463 = 8943695) B8943695
theorem B11320391 : Blo 1766084 11320391 := bstep (se 1 (by rfl) ⟨8490293, by rfl⟩ : syracuseStep 11320391 = 16980587) B16980587
theorem B7543955 : Blo 1766084 7543955 := bstep (se 1 (by rfl) ⟨5657966, by rfl⟩ : syracuseStep 7543955 = 11315933) B11315933
theorem B6454487 : Blo 1766084 6454487 := bstep (se 1 (by rfl) ⟨4840865, by rfl⟩ : syracuseStep 6454487 = 9681731) B9681731
theorem B10067399 : Blo 1766084 10067399 := bstep (se 1 (by rfl) ⟨7550549, by rfl⟩ : syracuseStep 10067399 = 15101099) B15101099
theorem B5963219 : Blo 1766084 5963219 := bstep (se 1 (by rfl) ⟨4472414, by rfl⟩ : syracuseStep 5963219 = 8944829) B8944829
theorem B4841039 : Blo 1766084 4841039 := bstep (se 1 (by rfl) ⟨3630779, by rfl⟩ : syracuseStep 4841039 = 7261559) B7261559
theorem B5963489 : Blo 1766084 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B4472567 : Blo 1766084 4472567 := bstep (se 1 (by rfl) ⟨3354425, by rfl⟩ : syracuseStep 4472567 = 6708851) B6708851
theorem B28655531 : Blo 1766084 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B10059835 : Blo 1766084 10059835 := bstep (se 1 (by rfl) ⟨7544876, by rfl⟩ : syracuseStep 10059835 = 15089753) B15089753
theorem B7545271 : Blo 1766084 7545271 := bstep (se 1 (by rfl) ⟨5658953, by rfl⟩ : syracuseStep 7545271 = 11317907) B11317907
theorem B7545287 : Blo 1766084 7545287 := bstep (se 1 (by rfl) ⟨5658965, by rfl⟩ : syracuseStep 7545287 = 11317931) B11317931
theorem B2515483 : Blo 1766084 2515483 := bstep (se 1 (by rfl) ⟨1886612, by rfl⟩ : syracuseStep 2515483 = 3773225) B3773225
theorem B3973715 : Blo 1766084 3973715 := bstep (se 1 (by rfl) ⟨2980286, by rfl⟩ : syracuseStep 3973715 = 5960573) B5960573
theorem B4244071 : Blo 1766084 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B8946287 : Blo 1766084 8946287 := bstep (se 1 (by rfl) ⟨6709715, by rfl⟩ : syracuseStep 8946287 = 13419431) B13419431
theorem B38191787 : Blo 1766084 38191787 := bstep (se 1 (by rfl) ⟨28643840, by rfl⟩ : syracuseStep 38191787 = 57287681) B57287681
theorem B3973895 : Blo 1766084 3973895 := bstep (se 1 (by rfl) ⟨2980421, by rfl⟩ : syracuseStep 3973895 = 5960843) B5960843
theorem B2237215 : Blo 1766084 2237215 := bstep (se 1 (by rfl) ⟨1677911, by rfl⟩ : syracuseStep 2237215 = 3355823) B3355823
theorem B3973985 : Blo 1766084 3973985 := bstep (se 2 (by rfl) ⟨1490244, by rfl⟩ : syracuseStep 3973985 = 2980489) B2980489
theorem B2983135 : Blo 1766084 2983135 := bstep (se 1 (by rfl) ⟨2237351, by rfl⟩ : syracuseStep 2983135 = 4474703) B4474703
theorem B16975129 : Blo 1766084 16975129 := bstep (se 2 (by rfl) ⟨6365673, by rfl⟩ : syracuseStep 16975129 = 12731347) B12731347
theorem B114607547 : Blo 1766084 114607547 := bstep (se 1 (by rfl) ⟨85955660, by rfl⟩ : syracuseStep 114607547 = 171911321) B171911321
theorem B10069541 : Blo 1766084 10069541 := bstep (se 4 (by rfl) ⟨944019, by rfl⟩ : syracuseStep 10069541 = 1888039) B1888039
theorem B7652927 : Blo 1766084 7652927 := bstep (se 1 (by rfl) ⟨5739695, by rfl⟩ : syracuseStep 7652927 = 11479391) B11479391
theorem B5965487 : Blo 1766084 5965487 := bstep (se 1 (by rfl) ⟨4474115, by rfl⟩ : syracuseStep 5965487 = 8948231) B8948231
theorem B30189347 : Blo 1766084 30189347 := bstep (se 1 (by rfl) ⟨22642010, by rfl⟩ : syracuseStep 30189347 = 45284021) B45284021
theorem B5375783 : Blo 1766084 5375783 := bstep (se 1 (by rfl) ⟨4031837, by rfl⟩ : syracuseStep 5375783 = 8063675) B8063675
theorem B42968879 : Blo 1766084 42968879 := bstep (se 1 (by rfl) ⟨32226659, by rfl⟩ : syracuseStep 42968879 = 64453319) B64453319
theorem B3974975 : Blo 1766084 3974975 := bstep (se 1 (by rfl) ⟨2981231, by rfl⟩ : syracuseStep 3974975 = 5962463) B5962463
theorem B48351275 : Blo 1766084 48351275 := bstep (se 1 (by rfl) ⟨36263456, by rfl⟩ : syracuseStep 48351275 = 72526913) B72526913
theorem B7546927 : Blo 1766084 7546927 := bstep (se 1 (by rfl) ⟨5660195, by rfl⟩ : syracuseStep 7546927 = 11320391) B11320391
theorem B4302991 : Blo 1766084 4302991 := bstep (se 1 (by rfl) ⟨3227243, by rfl⟩ : syracuseStep 4302991 = 6454487) B6454487
theorem B6711599 : Blo 1766084 6711599 := bstep (se 1 (by rfl) ⟨5033699, by rfl⟩ : syracuseStep 6711599 = 10067399) B10067399
theorem B3975479 : Blo 1766084 3975479 := bstep (se 1 (by rfl) ⟨2981609, by rfl⟩ : syracuseStep 3975479 = 5963219) B5963219
theorem B4245839 : Blo 1766084 4245839 := bstep (se 1 (by rfl) ⟨3184379, by rfl⟩ : syracuseStep 4245839 = 6368759) B6368759
theorem B3975659 : Blo 1766084 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B5966675 : Blo 1766084 5966675 := bstep (se 1 (by rfl) ⟨4475006, by rfl⟩ : syracuseStep 5966675 = 8950013) B8950013
theorem B2649257 : Blo 1766084 2649257 := bstep (se 2 (by rfl) ⟨993471, by rfl⟩ : syracuseStep 2649257 = 1986943) B1986943
theorem B3976361 : Blo 1766084 3976361 := bstep (se 2 (by rfl) ⟨1491135, by rfl⟩ : syracuseStep 3976361 = 2982271) B2982271
theorem B137678129 : Blo 1766084 137678129 := bstep (se 2 (by rfl) ⟨51629298, by rfl⟩ : syracuseStep 137678129 = 103258597) B103258597
theorem B5967215 : Blo 1766084 5967215 := bstep (se 1 (by rfl) ⟨4475411, by rfl⟩ : syracuseStep 5967215 = 8950823) B8950823
theorem B2513472893 : Blo 1766084 2513472893 := bstep (se 3 (by rfl) ⟨471276167, by rfl⟩ : syracuseStep 2513472893 = 942552335) B942552335
theorem B3354023 : Blo 1766084 3354023 := bstep (se 1 (by rfl) ⟨2515517, by rfl⟩ : syracuseStep 3354023 = 5031035) B5031035
theorem B7548329 : Blo 1766084 7548329 := bstep (se 2 (by rfl) ⟨2830623, by rfl⟩ : syracuseStep 7548329 = 5661247) B5661247
theorem B2829791 : Blo 1766084 2829791 := bstep (se 1 (by rfl) ⟨2122343, by rfl⟩ : syracuseStep 2829791 = 4244687) B4244687
theorem B2649671 : Blo 1766084 2649671 := bstep (se 1 (by rfl) ⟨1987253, by rfl⟩ : syracuseStep 2649671 = 3974507) B3974507
theorem B3976775 : Blo 1766084 3976775 := bstep (se 1 (by rfl) ⟨2982581, by rfl⟩ : syracuseStep 3976775 = 5965163) B5965163
theorem B3976847 : Blo 1766084 3976847 := bstep (se 1 (by rfl) ⟨2982635, by rfl⟩ : syracuseStep 3976847 = 5965271) B5965271
theorem B6713057 : Blo 1766084 6713057 := bstep (se 2 (by rfl) ⟨2517396, by rfl⟩ : syracuseStep 6713057 = 5034793) B5034793
theorem B3976937 : Blo 1766084 3976937 := bstep (se 2 (by rfl) ⟨1491351, by rfl⟩ : syracuseStep 3976937 = 2982703) B2982703
theorem B2649851 : Blo 1766084 2649851 := bstep (se 1 (by rfl) ⟨1987388, by rfl⟩ : syracuseStep 2649851 = 3974777) B3974777
theorem B3976955 : Blo 1766084 3976955 := bstep (se 1 (by rfl) ⟨2982716, by rfl⟩ : syracuseStep 3976955 = 5965433) B5965433
theorem B3354767 : Blo 1766084 3354767 := bstep (se 1 (by rfl) ⟨2516075, by rfl⟩ : syracuseStep 3354767 = 5032151) B5032151
theorem B10203367 : Blo 1766084 10203367 := bstep (se 1 (by rfl) ⟨7652525, by rfl⟩ : syracuseStep 10203367 = 15305051) B15305051
theorem B2650523 : Blo 1766084 2650523 := bstep (se 1 (by rfl) ⟨1987892, by rfl⟩ : syracuseStep 2650523 = 3975785) B3975785
theorem B12095945 : Blo 1766084 12095945 := bstep (se 2 (by rfl) ⟨4535979, by rfl⟩ : syracuseStep 12095945 = 9071959) B9071959
theorem B3977963 : Blo 1766084 3977963 := bstep (se 1 (by rfl) ⟨2983472, by rfl⟩ : syracuseStep 3977963 = 5966945) B5966945
theorem B1766139 : Blo 1766084 1766139 := bstep (se 1 (by rfl) ⟨1324604, by rfl⟩ : syracuseStep 1766139 = 2649209) B2649209
theorem B1766207 : Blo 1766084 1766207 := bstep (se 1 (by rfl) ⟨1324655, by rfl⟩ : syracuseStep 1766207 = 2649311) B2649311
theorem B2650943 : Blo 1766084 2650943 := bstep (se 1 (by rfl) ⟨1988207, by rfl⟩ : syracuseStep 2650943 = 3976415) B3976415
theorem B1766235 : Blo 1766084 1766235 := bstep (se 1 (by rfl) ⟨1324676, by rfl⟩ : syracuseStep 1766235 = 2649353) B2649353
theorem B1766303 : Blo 1766084 1766303 := bstep (se 1 (by rfl) ⟨1324727, by rfl⟩ : syracuseStep 1766303 = 2649455) B2649455
theorem B2651087 : Blo 1766084 2651087 := bstep (se 1 (by rfl) ⟨1988315, by rfl⟩ : syracuseStep 2651087 = 3976631) B3976631
theorem B1766383 : Blo 1766084 1766383 := bstep (se 1 (by rfl) ⟨1324787, by rfl⟩ : syracuseStep 1766383 = 2649575) B2649575
theorem B2651129 : Blo 1766084 2651129 := bstep (se 2 (by rfl) ⟨994173, by rfl⟩ : syracuseStep 2651129 = 1988347) B1988347
theorem B2651177 : Blo 1766084 2651177 := bstep (se 2 (by rfl) ⟨994191, by rfl⟩ : syracuseStep 2651177 = 1988383) B1988383
theorem B1766471 : Blo 1766084 1766471 := bstep (se 1 (by rfl) ⟨1324853, by rfl⟩ : syracuseStep 1766471 = 2649707) B2649707
theorem B2651207 : Blo 1766084 2651207 := bstep (se 1 (by rfl) ⟨1988405, by rfl⟩ : syracuseStep 2651207 = 3976811) B3976811
theorem B2831431 : Blo 1766084 2831431 := bstep (se 1 (by rfl) ⟨2123573, by rfl⟩ : syracuseStep 2831431 = 4247147) B4247147
theorem B2389063 : Blo 1766084 2389063 := bstep (se 1 (by rfl) ⟨1791797, by rfl⟩ : syracuseStep 2389063 = 3583595) B3583595
theorem B1766555 : Blo 1766084 1766555 := bstep (se 1 (by rfl) ⟨1324916, by rfl⟩ : syracuseStep 1766555 = 2649833) B2649833
theorem B1766651 : Blo 1766084 1766651 := bstep (se 1 (by rfl) ⟨1324988, by rfl⟩ : syracuseStep 1766651 = 2649977) B2649977
theorem B2651387 : Blo 1766084 2651387 := bstep (se 1 (by rfl) ⟨1988540, by rfl⟩ : syracuseStep 2651387 = 3977081) B3977081
theorem B4535561 : Blo 1766084 4535561 := bstep (se 2 (by rfl) ⟨1700835, by rfl⟩ : syracuseStep 4535561 = 3401671) B3401671
theorem B3773737 : Blo 1766084 3773737 := bstep (se 2 (by rfl) ⟨1415151, by rfl⟩ : syracuseStep 3773737 = 2830303) B2830303
theorem B1766719 : Blo 1766084 1766719 := bstep (se 1 (by rfl) ⟨1325039, by rfl⟩ : syracuseStep 1766719 = 2650079) B2650079
theorem B3355967 : Blo 1766084 3355967 := bstep (se 1 (by rfl) ⟨2516975, by rfl⟩ : syracuseStep 3355967 = 5033951) B5033951
theorem B1766887 : Blo 1766084 1766887 := bstep (se 1 (by rfl) ⟨1325165, by rfl⟩ : syracuseStep 1766887 = 2650331) B2650331
theorem B1766895 : Blo 1766084 1766895 := bstep (se 1 (by rfl) ⟨1325171, by rfl⟩ : syracuseStep 1766895 = 2650343) B2650343
theorem B1767003 : Blo 1766084 1767003 := bstep (se 1 (by rfl) ⟨1325252, by rfl⟩ : syracuseStep 1767003 = 2650505) B2650505
theorem B1767067 : Blo 1766084 1767067 := bstep (se 1 (by rfl) ⟨1325300, by rfl⟩ : syracuseStep 1767067 = 2650601) B2650601
theorem B4470511 : Blo 1766084 4470511 := bstep (se 1 (by rfl) ⟨3352883, by rfl⟩ : syracuseStep 4470511 = 6705767) B6705767
theorem B1767151 : Blo 1766084 1767151 := bstep (se 1 (by rfl) ⟨1325363, by rfl⟩ : syracuseStep 1767151 = 2650727) B2650727
theorem B10065667 : Blo 1766084 10065667 := bstep (se 1 (by rfl) ⟨7549250, by rfl⟩ : syracuseStep 10065667 = 15098501) B15098501
theorem B1767239 : Blo 1766084 1767239 := bstep (se 1 (by rfl) ⟨1325429, by rfl⟩ : syracuseStep 1767239 = 2650859) B2650859
theorem B1767259 : Blo 1766084 1767259 := bstep (se 1 (by rfl) ⟨1325444, by rfl⟩ : syracuseStep 1767259 = 2650889) B2650889
theorem B48486277 : Blo 1766084 48486277 := bstep (se 4 (by rfl) ⟨4545588, by rfl⟩ : syracuseStep 48486277 = 9091177) B9091177
theorem B1767327 : Blo 1766084 1767327 := bstep (se 1 (by rfl) ⟨1325495, by rfl⟩ : syracuseStep 1767327 = 2650991) B2650991
theorem B7550891 : Blo 1766084 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B3774455 : Blo 1766084 3774455 := bstep (se 1 (by rfl) ⟨2830841, by rfl⟩ : syracuseStep 3774455 = 5661683) B5661683
theorem B4659191 : Blo 1766084 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B14333993 : Blo 1766084 14333993 := bstep (se 2 (by rfl) ⟨5375247, by rfl⟩ : syracuseStep 14333993 = 10750495) B10750495
theorem B9549895 : Blo 1766084 9549895 := bstep (se 1 (by rfl) ⟨7162421, by rfl⟩ : syracuseStep 9549895 = 14324843) B14324843
theorem B1767495 : Blo 1766084 1767495 := bstep (se 1 (by rfl) ⟨1325621, by rfl⟩ : syracuseStep 1767495 = 2651243) B2651243
theorem B6371399 : Blo 1766084 6371399 := bstep (se 1 (by rfl) ⟨4778549, by rfl⟩ : syracuseStep 6371399 = 9557099) B9557099
theorem B1767655 : Blo 1766084 1767655 := bstep (se 1 (by rfl) ⟨1325741, by rfl⟩ : syracuseStep 1767655 = 2651483) B2651483
theorem B15096041 : Blo 1766084 15096041 := bstep (se 2 (by rfl) ⟨5661015, by rfl⟩ : syracuseStep 15096041 = 11322031) B11322031
theorem B5962031 : Blo 1766084 5962031 := bstep (se 1 (by rfl) ⟨4471523, by rfl⟩ : syracuseStep 5962031 = 8943047) B8943047
theorem B5372207 : Blo 1766084 5372207 := bstep (se 1 (by rfl) ⟨4029155, by rfl⟩ : syracuseStep 5372207 = 8058311) B8058311
theorem B1767839 : Blo 1766084 1767839 := bstep (se 1 (by rfl) ⟨1325879, by rfl⟩ : syracuseStep 1767839 = 2651759) B2651759
theorem B1767887 : Blo 1766084 1767887 := bstep (se 1 (by rfl) ⟨1325915, by rfl⟩ : syracuseStep 1767887 = 2651831) B2651831
theorem B1767911 : Blo 1766084 1767911 := bstep (se 1 (by rfl) ⟨1325933, by rfl⟩ : syracuseStep 1767911 = 2651867) B2651867
theorem B5741057 : Blo 1766084 5741057 := bstep (se 2 (by rfl) ⟨2152896, by rfl⟩ : syracuseStep 5741057 = 4305793) B4305793
theorem B1768027 : Blo 1766084 1768027 := bstep (se 1 (by rfl) ⟨1326020, by rfl⟩ : syracuseStep 1768027 = 2652041) B2652041
theorem B4471483 : Blo 1766084 4471483 := bstep (se 1 (by rfl) ⟨3353612, by rfl⟩ : syracuseStep 4471483 = 6707225) B6707225
theorem B6798305 : Blo 1766084 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B2980955 : Blo 1766084 2980955 := bstep (se 1 (by rfl) ⟨2235716, by rfl⟩ : syracuseStep 2980955 = 4471433) B4471433
theorem B2686043 : Blo 1766084 2686043 := bstep (se 1 (by rfl) ⟨2014532, by rfl⟩ : syracuseStep 2686043 = 4029065) B4029065
theorem B14326919 : Blo 1766084 14326919 := bstep (se 1 (by rfl) ⟨10745189, by rfl⟩ : syracuseStep 14326919 = 21490379) B21490379
theorem B15097103 : Blo 1766084 15097103 := bstep (se 1 (by rfl) ⟨11322827, by rfl⟩ : syracuseStep 15097103 = 22645655) B22645655
theorem B5029303 : Blo 1766084 5029303 := bstep (se 1 (by rfl) ⟨3771977, by rfl⟩ : syracuseStep 5029303 = 7543955) B7543955
theorem B3227359 : Blo 1766084 3227359 := bstep (se 1 (by rfl) ⟨2420519, by rfl⟩ : syracuseStep 3227359 = 4841039) B4841039
theorem B2981711 : Blo 1766084 2981711 := bstep (se 1 (by rfl) ⟨2236283, by rfl⟩ : syracuseStep 2981711 = 4472567) B4472567
theorem B19103687 : Blo 1766084 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B20127689 : Blo 1766084 20127689 := bstep (se 2 (by rfl) ⟨7547883, by rfl⟩ : syracuseStep 20127689 = 15095767) B15095767
theorem B2236511 : Blo 1766084 2236511 := bstep (se 1 (by rfl) ⟨1677383, by rfl⟩ : syracuseStep 2236511 = 3354767) B3354767
theorem B5030191 : Blo 1766084 5030191 := bstep (se 1 (by rfl) ⟨3772643, by rfl⟩ : syracuseStep 5030191 = 7545287) B7545287
theorem B5964191 : Blo 1766084 5964191 := bstep (se 1 (by rfl) ⟨4473143, by rfl⟩ : syracuseStep 5964191 = 8946287) B8946287
theorem B25461191 : Blo 1766084 25461191 := bstep (se 1 (by rfl) ⟨19095893, by rfl⟩ : syracuseStep 25461191 = 38191787) B38191787
theorem B10060361 : Blo 1766084 10060361 := bstep (se 2 (by rfl) ⟨3772635, by rfl⟩ : syracuseStep 10060361 = 7545271) B7545271
theorem B2237311 : Blo 1766084 2237311 := bstep (se 1 (by rfl) ⟨1677983, by rfl⟩ : syracuseStep 2237311 = 3355967) B3355967
theorem B2982953 : Blo 1766084 2982953 := bstep (se 2 (by rfl) ⟨1118607, by rfl⟩ : syracuseStep 2982953 = 2237215) B2237215
theorem B2516303 : Blo 1766084 2516303 := bstep (se 1 (by rfl) ⟨1887227, by rfl⟩ : syracuseStep 2516303 = 3774455) B3774455
theorem B3106127 : Blo 1766084 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B3974687 : Blo 1766084 3974687 := bstep (se 1 (by rfl) ⟨2981015, by rfl⟩ : syracuseStep 3974687 = 5962031) B5962031
theorem B3581471 : Blo 1766084 3581471 := bstep (se 1 (by rfl) ⟨2686103, by rfl⟩ : syracuseStep 3581471 = 5372207) B5372207
theorem B4474399 : Blo 1766084 4474399 := bstep (se 1 (by rfl) ⟨3355799, by rfl⟩ : syracuseStep 4474399 = 6711599) B6711599
theorem B5031649 : Blo 1766084 5031649 := bstep (se 2 (by rfl) ⟨1886868, by rfl⟩ : syracuseStep 5031649 = 3773737) B3773737
theorem B4532203 : Blo 1766084 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B91785419 : Blo 1766084 91785419 := bstep (se 1 (by rfl) ⟨68839064, by rfl⟩ : syracuseStep 91785419 = 137678129) B137678129
theorem B5032219 : Blo 1766084 5032219 := bstep (se 1 (by rfl) ⟨3774164, by rfl⟩ : syracuseStep 5032219 = 7548329) B7548329
theorem B4303145 : Blo 1766084 4303145 := bstep (se 2 (by rfl) ⟨1613679, by rfl⟩ : syracuseStep 4303145 = 3227359) B3227359
theorem B1886527 : Blo 1766084 1886527 := bstep (se 1 (by rfl) ⟨1414895, by rfl⟩ : syracuseStep 1886527 = 2829791) B2829791
theorem B13420889 : Blo 1766084 13420889 := bstep (se 2 (by rfl) ⟨5032833, by rfl⟩ : syracuseStep 13420889 = 10065667) B10065667
theorem B4475371 : Blo 1766084 4475371 := bstep (se 1 (by rfl) ⟨3356528, by rfl⟩ : syracuseStep 4475371 = 6713057) B6713057
theorem B10062569 : Blo 1766084 10062569 := bstep (se 2 (by rfl) ⟨3773463, by rfl⟩ : syracuseStep 10062569 = 7546927) B7546927
theorem B13413113 : Blo 1766084 13413113 := bstep (se 2 (by rfl) ⟨5029917, by rfl⟩ : syracuseStep 13413113 = 10059835) B10059835
theorem B12733193 : Blo 1766084 12733193 := bstep (se 2 (by rfl) ⟨4774947, by rfl⟩ : syracuseStep 12733193 = 9549895) B9549895
theorem B5737321 : Blo 1766084 5737321 := bstep (se 2 (by rfl) ⟨2151495, by rfl⟩ : syracuseStep 5737321 = 4302991) B4302991
theorem B8063963 : Blo 1766084 8063963 := bstep (se 1 (by rfl) ⟨6047972, by rfl⟩ : syracuseStep 8063963 = 12095945) B12095945
theorem B2649143 : Blo 1766084 2649143 := bstep (se 1 (by rfl) ⟨1986857, by rfl⟩ : syracuseStep 2649143 = 3973715) B3973715
theorem B2649263 : Blo 1766084 2649263 := bstep (se 1 (by rfl) ⟨1986947, by rfl⟩ : syracuseStep 2649263 = 3973895) B3973895
theorem B2649323 : Blo 1766084 2649323 := bstep (se 1 (by rfl) ⟨1986992, by rfl⟩ : syracuseStep 2649323 = 3973985) B3973985
theorem B12094829 : Blo 1766084 12094829 := bstep (se 3 (by rfl) ⟨2267780, by rfl⟩ : syracuseStep 12094829 = 4535561) B4535561
theorem B3353977 : Blo 1766084 3353977 := bstep (se 2 (by rfl) ⟨1257741, by rfl⟩ : syracuseStep 3353977 = 2515483) B2515483
theorem B6713027 : Blo 1766084 6713027 := bstep (se 1 (by rfl) ⟨5034770, by rfl⟩ : syracuseStep 6713027 = 10069541) B10069541
theorem B3976991 : Blo 1766084 3976991 := bstep (se 1 (by rfl) ⟨2982743, by rfl⟩ : syracuseStep 3976991 = 5965487) B5965487
theorem B3583855 : Blo 1766084 3583855 := bstep (se 1 (by rfl) ⟨2687891, by rfl⟩ : syracuseStep 3583855 = 5375783) B5375783
theorem B2649983 : Blo 1766084 2649983 := bstep (se 1 (by rfl) ⟨1987487, by rfl⟩ : syracuseStep 2649983 = 3974975) B3974975
theorem B5033927 : Blo 1766084 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B9555995 : Blo 1766084 9555995 := bstep (se 1 (by rfl) ⟨7166996, by rfl⟩ : syracuseStep 9555995 = 14333993) B14333993
theorem B4247599 : Blo 1766084 4247599 := bstep (se 1 (by rfl) ⟨3185699, by rfl⟩ : syracuseStep 4247599 = 6371399) B6371399
theorem B10064027 : Blo 1766084 10064027 := bstep (se 1 (by rfl) ⟨7548020, by rfl⟩ : syracuseStep 10064027 = 15096041) B15096041
theorem B2650319 : Blo 1766084 2650319 := bstep (se 1 (by rfl) ⟨1987739, by rfl⟩ : syracuseStep 2650319 = 3975479) B3975479
theorem B2830559 : Blo 1766084 2830559 := bstep (se 1 (by rfl) ⟨2122919, by rfl⟩ : syracuseStep 2830559 = 4245839) B4245839
theorem B3977513 : Blo 1766084 3977513 := bstep (se 2 (by rfl) ⟨1491567, by rfl⟩ : syracuseStep 3977513 = 2983135) B2983135
theorem B2650439 : Blo 1766084 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B3977783 : Blo 1766084 3977783 := bstep (se 1 (by rfl) ⟨2983337, by rfl⟩ : syracuseStep 3977783 = 5966675) B5966675
theorem B6705737 : Blo 1766084 6705737 := bstep (se 2 (by rfl) ⟨2514651, by rfl⟩ : syracuseStep 6705737 = 5029303) B5029303
theorem B258593477 : Blo 1766084 258593477 := bstep (se 4 (by rfl) ⟨24243138, by rfl⟩ : syracuseStep 258593477 = 48486277) B48486277
theorem B1987303 : Blo 1766084 1987303 := bstep (se 1 (by rfl) ⟨1490477, by rfl⟩ : syracuseStep 1987303 = 2980955) B2980955
theorem B1790695 : Blo 1766084 1790695 := bstep (se 1 (by rfl) ⟨1343021, by rfl⟩ : syracuseStep 1790695 = 2686043) B2686043
theorem B1766171 : Blo 1766084 1766171 := bstep (se 1 (by rfl) ⟨1324628, by rfl⟩ : syracuseStep 1766171 = 2649257) B2649257
theorem B2650907 : Blo 1766084 2650907 := bstep (se 1 (by rfl) ⟨1988180, by rfl⟩ : syracuseStep 2650907 = 3976361) B3976361
theorem B10064735 : Blo 1766084 10064735 := bstep (se 1 (by rfl) ⟨7548551, by rfl⟩ : syracuseStep 10064735 = 15097103) B15097103
theorem B3978143 : Blo 1766084 3978143 := bstep (se 1 (by rfl) ⟨2983607, by rfl⟩ : syracuseStep 3978143 = 5967215) B5967215
theorem B5960681 : Blo 1766084 5960681 := bstep (se 2 (by rfl) ⟨2235255, by rfl⟩ : syracuseStep 5960681 = 4470511) B4470511
theorem B1766447 : Blo 1766084 1766447 := bstep (se 1 (by rfl) ⟨1324835, by rfl⟩ : syracuseStep 1766447 = 2649671) B2649671
theorem B2651183 : Blo 1766084 2651183 := bstep (se 1 (by rfl) ⟨1988387, by rfl⟩ : syracuseStep 2651183 = 3976775) B3976775
theorem B2651231 : Blo 1766084 2651231 := bstep (se 1 (by rfl) ⟨1988423, by rfl⟩ : syracuseStep 2651231 = 3976847) B3976847
theorem B2651291 : Blo 1766084 2651291 := bstep (se 1 (by rfl) ⟨1988468, by rfl⟩ : syracuseStep 2651291 = 3976937) B3976937
theorem B1766567 : Blo 1766084 1766567 := bstep (se 1 (by rfl) ⟨1324925, by rfl⟩ : syracuseStep 1766567 = 2649851) B2649851
theorem B2651303 : Blo 1766084 2651303 := bstep (se 1 (by rfl) ⟨1988477, by rfl⟩ : syracuseStep 2651303 = 3976955) B3976955
theorem B1987807 : Blo 1766084 1987807 := bstep (se 1 (by rfl) ⟨1490855, by rfl⟩ : syracuseStep 1987807 = 2981711) B2981711
theorem B12735791 : Blo 1766084 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B1767015 : Blo 1766084 1767015 := bstep (se 1 (by rfl) ⟨1325261, by rfl⟩ : syracuseStep 1767015 = 2650523) B2650523
theorem B13604489 : Blo 1766084 13604489 := bstep (se 2 (by rfl) ⟨5101683, by rfl⟩ : syracuseStep 13604489 = 10203367) B10203367
theorem B2651975 : Blo 1766084 2651975 := bstep (se 1 (by rfl) ⟨1988981, by rfl⟩ : syracuseStep 2651975 = 3977963) B3977963
theorem B1767295 : Blo 1766084 1767295 := bstep (se 1 (by rfl) ⟨1325471, by rfl⟩ : syracuseStep 1767295 = 2650943) B2650943
theorem B1767391 : Blo 1766084 1767391 := bstep (se 1 (by rfl) ⟨1325543, by rfl⟩ : syracuseStep 1767391 = 2651087) B2651087
theorem B1767419 : Blo 1766084 1767419 := bstep (se 1 (by rfl) ⟨1325564, by rfl⟩ : syracuseStep 1767419 = 2651129) B2651129
theorem B1767451 : Blo 1766084 1767451 := bstep (se 1 (by rfl) ⟨1325588, by rfl⟩ : syracuseStep 1767451 = 2651177) B2651177
theorem B1767471 : Blo 1766084 1767471 := bstep (se 1 (by rfl) ⟨1325603, by rfl⟩ : syracuseStep 1767471 = 2651207) B2651207
theorem B5658761 : Blo 1766084 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B1767591 : Blo 1766084 1767591 := bstep (se 1 (by rfl) ⟨1325693, by rfl⟩ : syracuseStep 1767591 = 2651387) B2651387
theorem B5961977 : Blo 1766084 5961977 := bstep (se 2 (by rfl) ⟨2235741, by rfl⟩ : syracuseStep 5961977 = 4471483) B4471483
theorem B76405031 : Blo 1766084 76405031 := bstep (se 1 (by rfl) ⟨57303773, by rfl⟩ : syracuseStep 76405031 = 114607547) B114607547
theorem B5101951 : Blo 1766084 5101951 := bstep (se 1 (by rfl) ⟨3826463, by rfl⟩ : syracuseStep 5101951 = 7652927) B7652927
theorem B20126231 : Blo 1766084 20126231 := bstep (se 1 (by rfl) ⟨15094673, by rfl⟩ : syracuseStep 20126231 = 30189347) B30189347
theorem B28645919 : Blo 1766084 28645919 := bstep (se 1 (by rfl) ⟨21484439, by rfl⟩ : syracuseStep 28645919 = 42968879) B42968879
theorem B15309485 : Blo 1766084 15309485 := bstep (se 3 (by rfl) ⟨2870528, by rfl⟩ : syracuseStep 15309485 = 5741057) B5741057
theorem B32234183 : Blo 1766084 32234183 := bstep (se 1 (by rfl) ⟨24175637, by rfl⟩ : syracuseStep 32234183 = 48351275) B48351275
theorem B3775241 : Blo 1766084 3775241 := bstep (se 2 (by rfl) ⟨1415715, by rfl⟩ : syracuseStep 3775241 = 2831431) B2831431
theorem B3185417 : Blo 1766084 3185417 := bstep (se 2 (by rfl) ⟨1194531, by rfl⟩ : syracuseStep 3185417 = 2389063) B2389063
theorem B22633505 : Blo 1766084 22633505 := bstep (se 2 (by rfl) ⟨8487564, by rfl⟩ : syracuseStep 22633505 = 16975129) B16975129
theorem B9551279 : Blo 1766084 9551279 := bstep (se 1 (by rfl) ⟨7163459, by rfl⟩ : syracuseStep 9551279 = 14326919) B14326919
theorem B1675648595 : Blo 1766084 1675648595 := bstep (se 1 (by rfl) ⟨1256736446, by rfl⟩ : syracuseStep 1675648595 = 2513472893) B2513472893
theorem B2236015 : Blo 1766084 2236015 := bstep (se 1 (by rfl) ⟨1677011, by rfl⟩ : syracuseStep 2236015 = 3354023) B3354023
theorem B13418459 : Blo 1766084 13418459 := bstep (se 1 (by rfl) ⟨10063844, by rfl⟩ : syracuseStep 13418459 = 20127689) B20127689
theorem B6709351 : Blo 1766084 6709351 := bstep (se 1 (by rfl) ⟨5032013, by rfl⟩ : syracuseStep 6709351 = 10064027) B10064027
theorem B5964029 : Blo 1766084 5964029 := bstep (se 3 (by rfl) ⟨1118255, by rfl⟩ : syracuseStep 5964029 = 2236511) B2236511
theorem B16974127 : Blo 1766084 16974127 := bstep (se 1 (by rfl) ⟨12730595, by rfl⟩ : syracuseStep 16974127 = 25461191) B25461191
theorem B6709625 : Blo 1766084 6709625 := bstep (se 2 (by rfl) ⟨2516109, by rfl⟩ : syracuseStep 6709625 = 5032219) B5032219
theorem B2515369 : Blo 1766084 2515369 := bstep (se 2 (by rfl) ⟨943263, by rfl⟩ : syracuseStep 2515369 = 1886527) B1886527
theorem B6709823 : Blo 1766084 6709823 := bstep (se 1 (by rfl) ⟨5032367, by rfl⟩ : syracuseStep 6709823 = 10064735) B10064735
theorem B3973787 : Blo 1766084 3973787 := bstep (se 1 (by rfl) ⟨2980340, by rfl⟩ : syracuseStep 3973787 = 5960681) B5960681
theorem B6710141 : Blo 1766084 6710141 := bstep (se 3 (by rfl) ⟨1258151, by rfl⟩ : syracuseStep 6710141 = 2516303) B2516303
theorem B8283005 : Blo 1766084 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B9069659 : Blo 1766084 9069659 := bstep (se 1 (by rfl) ⟨6802244, by rfl⟩ : syracuseStep 9069659 = 13604489) B13604489
theorem B2983081 : Blo 1766084 2983081 := bstep (se 2 (by rfl) ⟨1118655, by rfl⟩ : syracuseStep 2983081 = 2237311) B2237311
theorem B3974651 : Blo 1766084 3974651 := bstep (se 1 (by rfl) ⟨2980988, by rfl⟩ : syracuseStep 3974651 = 5961977) B5961977
theorem B8947259 : Blo 1766084 8947259 := bstep (se 1 (by rfl) ⟨6710444, by rfl⟩ : syracuseStep 8947259 = 13420889) B13420889
theorem B19097279 : Blo 1766084 19097279 := bstep (se 1 (by rfl) ⟨14322959, by rfl⟩ : syracuseStep 19097279 = 28645919) B28645919
theorem B21489455 : Blo 1766084 21489455 := bstep (se 1 (by rfl) ⟨16117091, by rfl⟩ : syracuseStep 21489455 = 32234183) B32234183
theorem B8488795 : Blo 1766084 8488795 := bstep (se 1 (by rfl) ⟨6366596, by rfl⟩ : syracuseStep 8488795 = 12733193) B12733193
theorem B2516827 : Blo 1766084 2516827 := bstep (se 1 (by rfl) ⟨1887620, by rfl⟩ : syracuseStep 2516827 = 3775241) B3775241
theorem B5375975 : Blo 1766084 5375975 := bstep (se 1 (by rfl) ⟨4031981, by rfl⟩ : syracuseStep 5375975 = 8063963) B8063963
theorem B5965865 : Blo 1766084 5965865 := bstep (se 2 (by rfl) ⟨2237199, by rfl⟩ : syracuseStep 5965865 = 4474399) B4474399
theorem B8063219 : Blo 1766084 8063219 := bstep (se 1 (by rfl) ⟨6047414, by rfl⟩ : syracuseStep 8063219 = 12094829) B12094829
theorem B6367519 : Blo 1766084 6367519 := bstep (se 1 (by rfl) ⟨4775639, by rfl⟩ : syracuseStep 6367519 = 9551279) B9551279
theorem B4475351 : Blo 1766084 4475351 := bstep (se 1 (by rfl) ⟨3356513, by rfl⟩ : syracuseStep 4475351 = 6713027) B6713027
theorem B4778473 : Blo 1766084 4778473 := bstep (se 2 (by rfl) ⟨1791927, by rfl⟩ : syracuseStep 4778473 = 3583855) B3583855
theorem B5663465 : Blo 1766084 5663465 := bstep (se 2 (by rfl) ⟨2123799, by rfl⟩ : syracuseStep 5663465 = 4247599) B4247599
theorem B3976127 : Blo 1766084 3976127 := bstep (se 1 (by rfl) ⟨2982095, by rfl⟩ : syracuseStep 3976127 = 5964191) B5964191
theorem B6802601 : Blo 1766084 6802601 := bstep (se 2 (by rfl) ⟨2550975, by rfl⟩ : syracuseStep 6802601 = 5101951) B5101951
theorem B7548157 : Blo 1766084 7548157 := bstep (se 3 (by rfl) ⟨1415279, by rfl⟩ : syracuseStep 7548157 = 2830559) B2830559
theorem B5967161 : Blo 1766084 5967161 := bstep (se 2 (by rfl) ⟨2237685, by rfl⟩ : syracuseStep 5967161 = 4475371) B4475371
theorem B8490527 : Blo 1766084 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B2649737 : Blo 1766084 2649737 := bstep (se 2 (by rfl) ⟨993651, by rfl⟩ : syracuseStep 2649737 = 1987303) B1987303
theorem B2387593 : Blo 1766084 2387593 := bstep (se 2 (by rfl) ⟨895347, by rfl⟩ : syracuseStep 2387593 = 1790695) B1790695
theorem B2649791 : Blo 1766084 2649791 := bstep (se 1 (by rfl) ⟨1987343, by rfl⟩ : syracuseStep 2649791 = 3974687) B3974687
theorem B2387647 : Blo 1766084 2387647 := bstep (se 1 (by rfl) ⟨1790735, by rfl⟩ : syracuseStep 2387647 = 3581471) B3581471
theorem B3772507 : Blo 1766084 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B61190279 : Blo 1766084 61190279 := bstep (se 1 (by rfl) ⟨45892709, by rfl⟩ : syracuseStep 61190279 = 91785419) B91785419
theorem B2650409 : Blo 1766084 2650409 := bstep (se 2 (by rfl) ⟨993903, by rfl⟩ : syracuseStep 2650409 = 1987807) B1987807
theorem B8942075 : Blo 1766084 8942075 := bstep (se 1 (by rfl) ⟨6706556, by rfl⟩ : syracuseStep 8942075 = 13413113) B13413113
theorem B689582605 : Blo 1766084 689582605 := bstep (se 3 (by rfl) ⟨129296738, by rfl⟩ : syracuseStep 689582605 = 258593477) B258593477
theorem B1766095 : Blo 1766084 1766095 := bstep (se 1 (by rfl) ⟨1324571, by rfl⟩ : syracuseStep 1766095 = 2649143) B2649143
theorem B1766175 : Blo 1766084 1766175 := bstep (se 1 (by rfl) ⟨1324631, by rfl⟩ : syracuseStep 1766175 = 2649263) B2649263
theorem B1766215 : Blo 1766084 1766215 := bstep (se 1 (by rfl) ⟨1324661, by rfl⟩ : syracuseStep 1766215 = 2649323) B2649323
theorem B1117099063 : Blo 1766084 1117099063 := bstep (se 1 (by rfl) ⟨837824297, by rfl⟩ : syracuseStep 1117099063 = 1675648595) B1675648595
theorem B13423805 : Blo 1766084 13423805 := bstep (se 3 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 13423805 = 5033927) B5033927
theorem B2651327 : Blo 1766084 2651327 := bstep (se 1 (by rfl) ⟨1988495, by rfl⟩ : syracuseStep 2651327 = 3976991) B3976991
theorem B1766655 : Blo 1766084 1766655 := bstep (se 1 (by rfl) ⟨1324991, by rfl⟩ : syracuseStep 1766655 = 2649983) B2649983
theorem B6042937 : Blo 1766084 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B6370663 : Blo 1766084 6370663 := bstep (se 1 (by rfl) ⟨4777997, by rfl⟩ : syracuseStep 6370663 = 9555995) B9555995
theorem B1766879 : Blo 1766084 1766879 := bstep (se 1 (by rfl) ⟨1325159, by rfl⟩ : syracuseStep 1766879 = 2650319) B2650319
theorem B2651675 : Blo 1766084 2651675 := bstep (se 1 (by rfl) ⟨1988756, by rfl⟩ : syracuseStep 2651675 = 3977513) B3977513
theorem B1766959 : Blo 1766084 1766959 := bstep (se 1 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 1766959 = 2650439) B2650439
theorem B2651855 : Blo 1766084 2651855 := bstep (se 1 (by rfl) ⟨1988891, by rfl⟩ : syracuseStep 2651855 = 3977783) B3977783
theorem B4470491 : Blo 1766084 4470491 := bstep (se 1 (by rfl) ⟨3352868, by rfl⟩ : syracuseStep 4470491 = 6705737) B6705737
theorem B6706907 : Blo 1766084 6706907 := bstep (se 1 (by rfl) ⟨5030180, by rfl⟩ : syracuseStep 6706907 = 10060361) B10060361
theorem B6706921 : Blo 1766084 6706921 := bstep (se 2 (by rfl) ⟨2515095, by rfl⟩ : syracuseStep 6706921 = 5030191) B5030191
theorem B1767271 : Blo 1766084 1767271 := bstep (se 1 (by rfl) ⟨1325453, by rfl⟩ : syracuseStep 1767271 = 2650907) B2650907
theorem B2652095 : Blo 1766084 2652095 := bstep (se 1 (by rfl) ⟨1989071, by rfl⟩ : syracuseStep 2652095 = 3978143) B3978143
theorem B1988635 : Blo 1766084 1988635 := bstep (se 1 (by rfl) ⟨1491476, by rfl⟩ : syracuseStep 1988635 = 2982953) B2982953
theorem B1767455 : Blo 1766084 1767455 := bstep (se 1 (by rfl) ⟨1325591, by rfl⟩ : syracuseStep 1767455 = 2651183) B2651183
theorem B1767487 : Blo 1766084 1767487 := bstep (se 1 (by rfl) ⟨1325615, by rfl⟩ : syracuseStep 1767487 = 2651231) B2651231
theorem B1767527 : Blo 1766084 1767527 := bstep (se 1 (by rfl) ⟨1325645, by rfl⟩ : syracuseStep 1767527 = 2651291) B2651291
theorem B11475053 : Blo 1766084 11475053 := bstep (se 3 (by rfl) ⟨2151572, by rfl⟩ : syracuseStep 11475053 = 4303145) B4303145
theorem B1767535 : Blo 1766084 1767535 := bstep (se 1 (by rfl) ⟨1325651, by rfl⟩ : syracuseStep 1767535 = 2651303) B2651303
theorem B7649761 : Blo 1766084 7649761 := bstep (se 2 (by rfl) ⟨2868660, by rfl⟩ : syracuseStep 7649761 = 5737321) B5737321
theorem B1767983 : Blo 1766084 1767983 := bstep (se 1 (by rfl) ⟨1325987, by rfl⟩ : syracuseStep 1767983 = 2651975) B2651975
theorem B50936687 : Blo 1766084 50936687 := bstep (se 1 (by rfl) ⟨38202515, by rfl⟩ : syracuseStep 50936687 = 76405031) B76405031
theorem B13417487 : Blo 1766084 13417487 := bstep (se 1 (by rfl) ⟨10063115, by rfl⟩ : syracuseStep 13417487 = 20126231) B20126231
theorem B10206323 : Blo 1766084 10206323 := bstep (se 1 (by rfl) ⟨7654742, by rfl⟩ : syracuseStep 10206323 = 15309485) B15309485
theorem B6708379 : Blo 1766084 6708379 := bstep (se 1 (by rfl) ⟨5031284, by rfl⟩ : syracuseStep 6708379 = 10062569) B10062569
theorem B4471969 : Blo 1766084 4471969 := bstep (se 2 (by rfl) ⟨1676988, by rfl⟩ : syracuseStep 4471969 = 3353977) B3353977
theorem B15089003 : Blo 1766084 15089003 := bstep (se 1 (by rfl) ⟨11316752, by rfl⟩ : syracuseStep 15089003 = 22633505) B22633505
theorem B8494445 : Blo 1766084 8494445 := bstep (se 3 (by rfl) ⟨1592708, by rfl⟩ : syracuseStep 8494445 = 3185417) B3185417
theorem B2981353 : Blo 1766084 2981353 := bstep (se 2 (by rfl) ⟨1118007, by rfl⟩ : syracuseStep 2981353 = 2236015) B2236015
theorem B6708865 : Blo 1766084 6708865 := bstep (se 2 (by rfl) ⟨2515824, by rfl⟩ : syracuseStep 6708865 = 5031649) B5031649
theorem B8945639 : Blo 1766084 8945639 := bstep (se 1 (by rfl) ⟨6709229, by rfl⟩ : syracuseStep 8945639 = 13418459) B13418459
theorem B5030009 : Blo 1766084 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B8945801 : Blo 1766084 8945801 := bstep (se 2 (by rfl) ⟨3354675, by rfl⟩ : syracuseStep 8945801 = 6709351) B6709351
theorem B4473083 : Blo 1766084 4473083 := bstep (se 1 (by rfl) ⟨3354812, by rfl⟩ : syracuseStep 4473083 = 6709625) B6709625
theorem B4473215 : Blo 1766084 4473215 := bstep (se 1 (by rfl) ⟨3354911, by rfl⟩ : syracuseStep 4473215 = 6709823) B6709823
theorem B4473427 : Blo 1766084 4473427 := bstep (se 1 (by rfl) ⟨3355070, by rfl⟩ : syracuseStep 4473427 = 6710141) B6710141
theorem B5522003 : Blo 1766084 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B10199681 : Blo 1766084 10199681 := bstep (se 2 (by rfl) ⟨3824880, by rfl⟩ : syracuseStep 10199681 = 7649761) B7649761
theorem B6046439 : Blo 1766084 6046439 := bstep (se 1 (by rfl) ⟨4534829, by rfl⟩ : syracuseStep 6046439 = 9069659) B9069659
theorem B5964839 : Blo 1766084 5964839 := bstep (se 1 (by rfl) ⟨4473629, by rfl⟩ : syracuseStep 5964839 = 8947259) B8947259
theorem B12731519 : Blo 1766084 12731519 := bstep (se 1 (by rfl) ⟨9548639, by rfl⟩ : syracuseStep 12731519 = 19097279) B19097279
theorem B5375479 : Blo 1766084 5375479 := bstep (se 1 (by rfl) ⟨4031609, by rfl⟩ : syracuseStep 5375479 = 8063219) B8063219
theorem B2983567 : Blo 1766084 2983567 := bstep (se 1 (by rfl) ⟨2237675, by rfl⟩ : syracuseStep 2983567 = 4475351) B4475351
theorem B33957791 : Blo 1766084 33957791 := bstep (se 1 (by rfl) ⟨25468343, by rfl⟩ : syracuseStep 33957791 = 50936687) B50936687
theorem B3975137 : Blo 1766084 3975137 := bstep (se 2 (by rfl) ⟨1490676, by rfl⟩ : syracuseStep 3975137 = 2981353) B2981353
theorem B5662963 : Blo 1766084 5662963 := bstep (se 1 (by rfl) ⟨4247222, by rfl⟩ : syracuseStep 5662963 = 8494445) B8494445
theorem B3976019 : Blo 1766084 3976019 := bstep (se 1 (by rfl) ⟨2982014, by rfl⟩ : syracuseStep 3976019 = 5964029) B5964029
theorem B8490025 : Blo 1766084 8490025 := bstep (se 2 (by rfl) ⟨3183759, by rfl⟩ : syracuseStep 8490025 = 6367519) B6367519
theorem B2649191 : Blo 1766084 2649191 := bstep (se 1 (by rfl) ⟨1986893, by rfl⟩ : syracuseStep 2649191 = 3973787) B3973787
theorem B18140269 : Blo 1766084 18140269 := bstep (se 3 (by rfl) ⟨3401300, by rfl⟩ : syracuseStep 18140269 = 6802601) B6802601
theorem B3353825 : Blo 1766084 3353825 := bstep (se 2 (by rfl) ⟨1257684, by rfl⟩ : syracuseStep 3353825 = 2515369) B2515369
theorem B8949203 : Blo 1766084 8949203 := bstep (se 1 (by rfl) ⟨6711902, by rfl⟩ : syracuseStep 8949203 = 13423805) B13423805
theorem B12734117 : Blo 1766084 12734117 := bstep (se 4 (by rfl) ⟨1193823, by rfl⟩ : syracuseStep 12734117 = 2387647) B2387647
theorem B2649767 : Blo 1766084 2649767 := bstep (se 1 (by rfl) ⟨1987325, by rfl⟩ : syracuseStep 2649767 = 3974651) B3974651
theorem B3977243 : Blo 1766084 3977243 := bstep (se 1 (by rfl) ⟨2982932, by rfl⟩ : syracuseStep 3977243 = 5965865) B5965865
theorem B1489465417 : Blo 1766084 1489465417 := bstep (se 2 (by rfl) ⟨558549531, by rfl⟩ : syracuseStep 1489465417 = 1117099063) B1117099063
theorem B3977441 : Blo 1766084 3977441 := bstep (se 2 (by rfl) ⟨1491540, by rfl⟩ : syracuseStep 3977441 = 2983081) B2983081
theorem B10064209 : Blo 1766084 10064209 := bstep (se 2 (by rfl) ⟨3774078, by rfl⟩ : syracuseStep 10064209 = 7548157) B7548157
theorem B8057249 : Blo 1766084 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B2650751 : Blo 1766084 2650751 := bstep (se 1 (by rfl) ⟨1988063, by rfl⟩ : syracuseStep 2650751 = 3976127) B3976127
theorem B6804215 : Blo 1766084 6804215 := bstep (se 1 (by rfl) ⟨5103161, by rfl⟩ : syracuseStep 6804215 = 10206323) B10206323
theorem B3183457 : Blo 1766084 3183457 := bstep (se 2 (by rfl) ⟨1193796, by rfl⟩ : syracuseStep 3183457 = 2387593) B2387593
theorem B3978107 : Blo 1766084 3978107 := bstep (se 1 (by rfl) ⟨2983580, by rfl⟩ : syracuseStep 3978107 = 5967161) B5967161
theorem B8942561 : Blo 1766084 8942561 := bstep (se 2 (by rfl) ⟨3353460, by rfl⟩ : syracuseStep 8942561 = 6706921) B6706921
theorem B1766491 : Blo 1766084 1766491 := bstep (se 1 (by rfl) ⟨1324868, by rfl⟩ : syracuseStep 1766491 = 2649737) B2649737
theorem B11318393 : Blo 1766084 11318393 := bstep (se 2 (by rfl) ⟨4244397, by rfl⟩ : syracuseStep 11318393 = 8488795) B8488795
theorem B1766527 : Blo 1766084 1766527 := bstep (se 1 (by rfl) ⟨1324895, by rfl⟩ : syracuseStep 1766527 = 2649791) B2649791
theorem B3355769 : Blo 1766084 3355769 := bstep (se 2 (by rfl) ⟨1258413, by rfl⟩ : syracuseStep 3355769 = 2516827) B2516827
theorem B2651513 : Blo 1766084 2651513 := bstep (se 2 (by rfl) ⟨994317, by rfl⟩ : syracuseStep 2651513 = 1988635) B1988635
theorem B40793519 : Blo 1766084 40793519 := bstep (se 1 (by rfl) ⟨30595139, by rfl⟩ : syracuseStep 40793519 = 61190279) B61190279
theorem B1766939 : Blo 1766084 1766939 := bstep (se 1 (by rfl) ⟨1325204, by rfl⟩ : syracuseStep 1766939 = 2650409) B2650409
theorem B5961383 : Blo 1766084 5961383 := bstep (se 1 (by rfl) ⟨4471037, by rfl⟩ : syracuseStep 5961383 = 8942075) B8942075
theorem B22632169 : Blo 1766084 22632169 := bstep (se 2 (by rfl) ⟨8487063, by rfl⟩ : syracuseStep 22632169 = 16974127) B16974127
theorem B6371297 : Blo 1766084 6371297 := bstep (se 2 (by rfl) ⟨2389236, by rfl⟩ : syracuseStep 6371297 = 4778473) B4778473
theorem B919443473 : Blo 1766084 919443473 := bstep (se 2 (by rfl) ⟨344791302, by rfl⟩ : syracuseStep 919443473 = 689582605) B689582605
theorem B1767551 : Blo 1766084 1767551 := bstep (se 1 (by rfl) ⟨1325663, by rfl⟩ : syracuseStep 1767551 = 2651327) B2651327
theorem B1767783 : Blo 1766084 1767783 := bstep (se 1 (by rfl) ⟨1325837, by rfl⟩ : syracuseStep 1767783 = 2651675) B2651675
theorem B1767903 : Blo 1766084 1767903 := bstep (se 1 (by rfl) ⟨1325927, by rfl⟩ : syracuseStep 1767903 = 2651855) B2651855
theorem B2980327 : Blo 1766084 2980327 := bstep (se 1 (by rfl) ⟨2235245, by rfl⟩ : syracuseStep 2980327 = 4470491) B4470491
theorem B4471271 : Blo 1766084 4471271 := bstep (se 1 (by rfl) ⟨3353453, by rfl⟩ : syracuseStep 4471271 = 6706907) B6706907
theorem B14326303 : Blo 1766084 14326303 := bstep (se 1 (by rfl) ⟨10744727, by rfl⟩ : syracuseStep 14326303 = 21489455) B21489455
theorem B1768063 : Blo 1766084 1768063 := bstep (se 1 (by rfl) ⟨1326047, by rfl⟩ : syracuseStep 1768063 = 2652095) B2652095
theorem B7650035 : Blo 1766084 7650035 := bstep (se 1 (by rfl) ⟨5737526, by rfl⟩ : syracuseStep 7650035 = 11475053) B11475053
theorem B8944505 : Blo 1766084 8944505 := bstep (se 2 (by rfl) ⟨3354189, by rfl⟩ : syracuseStep 8944505 = 6708379) B6708379
theorem B5962625 : Blo 1766084 5962625 := bstep (se 2 (by rfl) ⟨2235984, by rfl⟩ : syracuseStep 5962625 = 4471969) B4471969
theorem B8494217 : Blo 1766084 8494217 := bstep (se 2 (by rfl) ⟨3185331, by rfl⟩ : syracuseStep 8494217 = 6370663) B6370663
theorem B3775643 : Blo 1766084 3775643 := bstep (se 1 (by rfl) ⟨2831732, by rfl⟩ : syracuseStep 3775643 = 5663465) B5663465
theorem B8944991 : Blo 1766084 8944991 := bstep (se 1 (by rfl) ⟨6708743, by rfl⟩ : syracuseStep 8944991 = 13417487) B13417487
theorem B8945153 : Blo 1766084 8945153 := bstep (se 2 (by rfl) ⟨3354432, by rfl⟩ : syracuseStep 8945153 = 6708865) B6708865
theorem B10059335 : Blo 1766084 10059335 := bstep (se 1 (by rfl) ⟨7544501, by rfl⟩ : syracuseStep 10059335 = 15089003) B15089003
theorem B5660351 : Blo 1766084 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B57343733 : Blo 1766084 57343733 := bstep (se 5 (by rfl) ⟨2687987, by rfl⟩ : syracuseStep 57343733 = 5375975) B5375975
theorem B5963759 : Blo 1766084 5963759 := bstep (se 1 (by rfl) ⟨4472819, by rfl⟩ : syracuseStep 5963759 = 8945639) B8945639
theorem B5963867 : Blo 1766084 5963867 := bstep (se 1 (by rfl) ⟨4472900, by rfl⟩ : syracuseStep 5963867 = 8945801) B8945801
theorem B1985953889 : Blo 1766084 1985953889 := bstep (se 2 (by rfl) ⟨744732708, by rfl⟩ : syracuseStep 1985953889 = 1489465417) B1489465417
theorem B2982055 : Blo 1766084 2982055 := bstep (se 1 (by rfl) ⟨2236541, by rfl⟩ : syracuseStep 2982055 = 4473083) B4473083
theorem B2982143 : Blo 1766084 2982143 := bstep (se 1 (by rfl) ⟨2236607, by rfl⟩ : syracuseStep 2982143 = 4473215) B4473215
theorem B6799787 : Blo 1766084 6799787 := bstep (se 1 (by rfl) ⟨5099840, by rfl⟩ : syracuseStep 6799787 = 10199681) B10199681
theorem B13418945 : Blo 1766084 13418945 := bstep (se 2 (by rfl) ⟨5032104, by rfl⟩ : syracuseStep 13418945 = 10064209) B10064209
theorem B3973769 : Blo 1766084 3973769 := bstep (se 2 (by rfl) ⟨1490163, by rfl⟩ : syracuseStep 3973769 = 2980327) B2980327
theorem B7545595 : Blo 1766084 7545595 := bstep (se 1 (by rfl) ⟨5659196, by rfl⟩ : syracuseStep 7545595 = 11318393) B11318393
theorem B8487679 : Blo 1766084 8487679 := bstep (se 1 (by rfl) ⟨6365759, by rfl⟩ : syracuseStep 8487679 = 12731519) B12731519
theorem B5964569 : Blo 1766084 5964569 := bstep (se 2 (by rfl) ⟨2236713, by rfl⟩ : syracuseStep 5964569 = 4473427) B4473427
theorem B3974255 : Blo 1766084 3974255 := bstep (se 1 (by rfl) ⟨2980691, by rfl⟩ : syracuseStep 3974255 = 5961383) B5961383
theorem B4244609 : Blo 1766084 4244609 := bstep (se 2 (by rfl) ⟨1591728, by rfl⟩ : syracuseStep 4244609 = 3183457) B3183457
theorem B3975083 : Blo 1766084 3975083 := bstep (se 1 (by rfl) ⟨2981312, by rfl⟩ : syracuseStep 3975083 = 5962625) B5962625
theorem B5662811 : Blo 1766084 5662811 := bstep (se 1 (by rfl) ⟨4247108, by rfl⟩ : syracuseStep 5662811 = 8494217) B8494217
theorem B2517095 : Blo 1766084 2517095 := bstep (se 1 (by rfl) ⟨1887821, by rfl⟩ : syracuseStep 2517095 = 3775643) B3775643
theorem B5966135 : Blo 1766084 5966135 := bstep (se 1 (by rfl) ⟨4474601, by rfl⟩ : syracuseStep 5966135 = 8949203) B8949203
theorem B8489411 : Blo 1766084 8489411 := bstep (se 1 (by rfl) ⟨6367058, by rfl⟩ : syracuseStep 8489411 = 12734117) B12734117
theorem B3975839 : Blo 1766084 3975839 := bstep (se 1 (by rfl) ⟨2981879, by rfl⟩ : syracuseStep 3975839 = 5963759) B5963759
theorem B3353339 : Blo 1766084 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B8948717 : Blo 1766084 8948717 := bstep (se 3 (by rfl) ⟨1677884, by rfl⟩ : syracuseStep 8948717 = 3355769) B3355769
theorem B3681335 : Blo 1766084 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B3976559 : Blo 1766084 3976559 := bstep (se 1 (by rfl) ⟨2982419, by rfl⟩ : syracuseStep 3976559 = 5964839) B5964839
theorem B22638527 : Blo 1766084 22638527 := bstep (se 1 (by rfl) ⟨16978895, by rfl⟩ : syracuseStep 22638527 = 33957791) B33957791
theorem B2650091 : Blo 1766084 2650091 := bstep (se 1 (by rfl) ⟨1987568, by rfl⟩ : syracuseStep 2650091 = 3975137) B3975137
theorem B4247531 : Blo 1766084 4247531 := bstep (se 1 (by rfl) ⟨3185648, by rfl⟩ : syracuseStep 4247531 = 6371297) B6371297
theorem B612962315 : Blo 1766084 612962315 := bstep (se 1 (by rfl) ⟨459721736, by rfl⟩ : syracuseStep 612962315 = 919443473) B919443473
theorem B24187025 : Blo 1766084 24187025 := bstep (se 2 (by rfl) ⟨9070134, by rfl⟩ : syracuseStep 24187025 = 18140269) B18140269
theorem B5100023 : Blo 1766084 5100023 := bstep (se 1 (by rfl) ⟨3825017, by rfl⟩ : syracuseStep 5100023 = 7650035) B7650035
theorem B2650679 : Blo 1766084 2650679 := bstep (se 1 (by rfl) ⟨1988009, by rfl⟩ : syracuseStep 2650679 = 3976019) B3976019
theorem B1766127 : Blo 1766084 1766127 := bstep (se 1 (by rfl) ⟨1324595, by rfl⟩ : syracuseStep 1766127 = 2649191) B2649191
theorem B3978089 : Blo 1766084 3978089 := bstep (se 2 (by rfl) ⟨1491783, by rfl⟩ : syracuseStep 3978089 = 2983567) B2983567
theorem B30176225 : Blo 1766084 30176225 := bstep (se 2 (by rfl) ⟨11316084, by rfl⟩ : syracuseStep 30176225 = 22632169) B22632169
theorem B6706223 : Blo 1766084 6706223 := bstep (se 1 (by rfl) ⟨5029667, by rfl⟩ : syracuseStep 6706223 = 10059335) B10059335
theorem B1766511 : Blo 1766084 1766511 := bstep (se 1 (by rfl) ⟨1324883, by rfl⟩ : syracuseStep 1766511 = 2649767) B2649767
theorem B3773567 : Blo 1766084 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B38229155 : Blo 1766084 38229155 := bstep (se 1 (by rfl) ⟨28671866, by rfl⟩ : syracuseStep 38229155 = 57343733) B57343733
theorem B2651495 : Blo 1766084 2651495 := bstep (se 1 (by rfl) ⟨1988621, by rfl⟩ : syracuseStep 2651495 = 3977243) B3977243
theorem B2651627 : Blo 1766084 2651627 := bstep (se 1 (by rfl) ⟨1988720, by rfl⟩ : syracuseStep 2651627 = 3977441) B3977441
theorem B5371499 : Blo 1766084 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B1767167 : Blo 1766084 1767167 := bstep (se 1 (by rfl) ⟨1325375, by rfl⟩ : syracuseStep 1767167 = 2650751) B2650751
theorem B4536143 : Blo 1766084 4536143 := bstep (se 1 (by rfl) ⟨3402107, by rfl⟩ : syracuseStep 4536143 = 6804215) B6804215
theorem B2652071 : Blo 1766084 2652071 := bstep (se 1 (by rfl) ⟨1989053, by rfl⟩ : syracuseStep 2652071 = 3978107) B3978107
theorem B8943533 : Blo 1766084 8943533 := bstep (se 3 (by rfl) ⟨1676912, by rfl⟩ : syracuseStep 8943533 = 3353825) B3353825
theorem B5961707 : Blo 1766084 5961707 := bstep (se 1 (by rfl) ⟨4471280, by rfl⟩ : syracuseStep 5961707 = 8942561) B8942561
theorem B19101737 : Blo 1766084 19101737 := bstep (se 2 (by rfl) ⟨7163151, by rfl⟩ : syracuseStep 19101737 = 14326303) B14326303
theorem B1767675 : Blo 1766084 1767675 := bstep (se 1 (by rfl) ⟨1325756, by rfl⟩ : syracuseStep 1767675 = 2651513) B2651513
theorem B27195679 : Blo 1766084 27195679 := bstep (se 1 (by rfl) ⟨20396759, by rfl⟩ : syracuseStep 27195679 = 40793519) B40793519
theorem B30202469 : Blo 1766084 30202469 := bstep (se 4 (by rfl) ⟨2831481, by rfl⟩ : syracuseStep 30202469 = 5662963) B5662963
theorem B11320033 : Blo 1766084 11320033 := bstep (se 2 (by rfl) ⟨4245012, by rfl⟩ : syracuseStep 11320033 = 8490025) B8490025
theorem B2980847 : Blo 1766084 2980847 := bstep (se 1 (by rfl) ⟨2235635, by rfl⟩ : syracuseStep 2980847 = 4471271) B4471271
theorem B5963003 : Blo 1766084 5963003 := bstep (se 1 (by rfl) ⟨4472252, by rfl⟩ : syracuseStep 5963003 = 8944505) B8944505
theorem B7167305 : Blo 1766084 7167305 := bstep (se 2 (by rfl) ⟨2687739, by rfl⟩ : syracuseStep 7167305 = 5375479) B5375479
theorem B5963327 : Blo 1766084 5963327 := bstep (se 1 (by rfl) ⟨4472495, by rfl⟩ : syracuseStep 5963327 = 8944991) B8944991
theorem B5963435 : Blo 1766084 5963435 := bstep (se 1 (by rfl) ⟨4472576, by rfl⟩ : syracuseStep 5963435 = 8945153) B8945153
theorem B64495349 : Blo 1766084 64495349 := bstep (se 5 (by rfl) ⟨3023219, by rfl⟩ : syracuseStep 64495349 = 6046439) B6046439
theorem B408641543 : Blo 1766084 408641543 := bstep (se 1 (by rfl) ⟨306481157, by rfl⟩ : syracuseStep 408641543 = 612962315) B612962315
theorem B8945963 : Blo 1766084 8945963 := bstep (se 1 (by rfl) ⟨6709472, by rfl⟩ : syracuseStep 8945963 = 13418945) B13418945
theorem B3400015 : Blo 1766084 3400015 := bstep (se 1 (by rfl) ⟨2550011, by rfl⟩ : syracuseStep 3400015 = 5100023) B5100023
theorem B2515711 : Blo 1766084 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B25486103 : Blo 1766084 25486103 := bstep (se 1 (by rfl) ⟨19114577, by rfl⟩ : syracuseStep 25486103 = 38229155) B38229155
theorem B10060793 : Blo 1766084 10060793 := bstep (se 2 (by rfl) ⟨3772797, by rfl⟩ : syracuseStep 10060793 = 7545595) B7545595
theorem B3580999 : Blo 1766084 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B3974471 : Blo 1766084 3974471 := bstep (se 1 (by rfl) ⟨2980853, by rfl⟩ : syracuseStep 3974471 = 5961707) B5961707
theorem B5965811 : Blo 1766084 5965811 := bstep (se 1 (by rfl) ⟨4474358, by rfl⟩ : syracuseStep 5965811 = 8948717) B8948717
theorem B3975335 : Blo 1766084 3975335 := bstep (se 1 (by rfl) ⟨2981501, by rfl⟩ : syracuseStep 3975335 = 5963003) B5963003
theorem B4778203 : Blo 1766084 4778203 := bstep (se 1 (by rfl) ⟨3583652, by rfl⟩ : syracuseStep 4778203 = 7167305) B7167305
theorem B3975551 : Blo 1766084 3975551 := bstep (se 1 (by rfl) ⟨2981663, by rfl⟩ : syracuseStep 3975551 = 5963327) B5963327
theorem B3975623 : Blo 1766084 3975623 := bstep (se 1 (by rfl) ⟨2981717, by rfl⟩ : syracuseStep 3975623 = 5963435) B5963435
theorem B15092351 : Blo 1766084 15092351 := bstep (se 1 (by rfl) ⟨11319263, by rfl⟩ : syracuseStep 15092351 = 22638527) B22638527
theorem B3975911 : Blo 1766084 3975911 := bstep (se 1 (by rfl) ⟨2981933, by rfl⟩ : syracuseStep 3975911 = 5963867) B5963867
theorem B16124683 : Blo 1766084 16124683 := bstep (se 1 (by rfl) ⟨12093512, by rfl⟩ : syracuseStep 16124683 = 24187025) B24187025
theorem B3976073 : Blo 1766084 3976073 := bstep (se 2 (by rfl) ⟨1491027, by rfl⟩ : syracuseStep 3976073 = 2982055) B2982055
theorem B5295877037 : Blo 1766084 5295877037 := bstep (se 3 (by rfl) ⟨992976944, by rfl⟩ : syracuseStep 5295877037 = 1985953889) B1985953889
theorem B6712253 : Blo 1766084 6712253 := bstep (se 3 (by rfl) ⟨1258547, by rfl⟩ : syracuseStep 6712253 = 2517095) B2517095
theorem B4533191 : Blo 1766084 4533191 := bstep (se 1 (by rfl) ⟨3399893, by rfl⟩ : syracuseStep 4533191 = 6799787) B6799787
theorem B36260905 : Blo 1766084 36260905 := bstep (se 2 (by rfl) ⟨13597839, by rfl⟩ : syracuseStep 36260905 = 27195679) B27195679
theorem B2649179 : Blo 1766084 2649179 := bstep (se 1 (by rfl) ⟨1986884, by rfl⟩ : syracuseStep 2649179 = 3973769) B3973769
theorem B3976379 : Blo 1766084 3976379 := bstep (se 1 (by rfl) ⟨2982284, by rfl⟩ : syracuseStep 3976379 = 5964569) B5964569
theorem B2649503 : Blo 1766084 2649503 := bstep (se 1 (by rfl) ⟨1987127, by rfl⟩ : syracuseStep 2649503 = 3974255) B3974255
theorem B2829739 : Blo 1766084 2829739 := bstep (se 1 (by rfl) ⟨2122304, by rfl⟩ : syracuseStep 2829739 = 4244609) B4244609
theorem B48385525 : Blo 1766084 48385525 := bstep (se 5 (by rfl) ⟨2268071, by rfl⟩ : syracuseStep 48385525 = 4536143) B4536143
theorem B15093377 : Blo 1766084 15093377 := bstep (se 2 (by rfl) ⟨5660016, by rfl⟩ : syracuseStep 15093377 = 11320033) B11320033
theorem B11316905 : Blo 1766084 11316905 := bstep (se 2 (by rfl) ⟨4243839, by rfl⟩ : syracuseStep 11316905 = 8487679) B8487679
theorem B2650055 : Blo 1766084 2650055 := bstep (se 1 (by rfl) ⟨1987541, by rfl⟩ : syracuseStep 2650055 = 3975083) B3975083
theorem B12734491 : Blo 1766084 12734491 := bstep (se 1 (by rfl) ⟨9550868, by rfl⟩ : syracuseStep 12734491 = 19101737) B19101737
theorem B3977423 : Blo 1766084 3977423 := bstep (se 1 (by rfl) ⟨2983067, by rfl⟩ : syracuseStep 3977423 = 5966135) B5966135
theorem B2650559 : Blo 1766084 2650559 := bstep (se 1 (by rfl) ⟨1987919, by rfl⟩ : syracuseStep 2650559 = 3975839) B3975839
theorem B8942237 : Blo 1766084 8942237 := bstep (se 3 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 8942237 = 3353339) B3353339
theorem B1987231 : Blo 1766084 1987231 := bstep (se 1 (by rfl) ⟨1490423, by rfl⟩ : syracuseStep 1987231 = 2980847) B2980847
theorem B2454223 : Blo 1766084 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B2651039 : Blo 1766084 2651039 := bstep (se 1 (by rfl) ⟨1988279, by rfl⟩ : syracuseStep 2651039 = 3976559) B3976559
theorem B42996899 : Blo 1766084 42996899 := bstep (se 1 (by rfl) ⟨32247674, by rfl⟩ : syracuseStep 42996899 = 64495349) B64495349
theorem B1766727 : Blo 1766084 1766727 := bstep (se 1 (by rfl) ⟨1325045, by rfl⟩ : syracuseStep 1766727 = 2650091) B2650091
theorem B2831687 : Blo 1766084 2831687 := bstep (se 1 (by rfl) ⟨2123765, by rfl⟩ : syracuseStep 2831687 = 4247531) B4247531
theorem B1988095 : Blo 1766084 1988095 := bstep (se 1 (by rfl) ⟨1491071, by rfl⟩ : syracuseStep 1988095 = 2982143) B2982143
theorem B1767119 : Blo 1766084 1767119 := bstep (se 1 (by rfl) ⟨1325339, by rfl⟩ : syracuseStep 1767119 = 2650679) B2650679
theorem B2652059 : Blo 1766084 2652059 := bstep (se 1 (by rfl) ⟨1989044, by rfl⟩ : syracuseStep 2652059 = 3978089) B3978089
theorem B20117483 : Blo 1766084 20117483 := bstep (se 1 (by rfl) ⟨15088112, by rfl⟩ : syracuseStep 20117483 = 30176225) B30176225
theorem B4470815 : Blo 1766084 4470815 := bstep (se 1 (by rfl) ⟨3353111, by rfl⟩ : syracuseStep 4470815 = 6706223) B6706223
theorem B1767663 : Blo 1766084 1767663 := bstep (se 1 (by rfl) ⟨1325747, by rfl⟩ : syracuseStep 1767663 = 2651495) B2651495
theorem B1767751 : Blo 1766084 1767751 := bstep (se 1 (by rfl) ⟨1325813, by rfl⟩ : syracuseStep 1767751 = 2651627) B2651627
theorem B1768047 : Blo 1766084 1768047 := bstep (se 1 (by rfl) ⟨1326035, by rfl⟩ : syracuseStep 1768047 = 2652071) B2652071
theorem B5962355 : Blo 1766084 5962355 := bstep (se 1 (by rfl) ⟨4471766, by rfl⟩ : syracuseStep 5962355 = 8943533) B8943533
theorem B3775207 : Blo 1766084 3775207 := bstep (se 1 (by rfl) ⟨2831405, by rfl⟩ : syracuseStep 3775207 = 5662811) B5662811
theorem B5659607 : Blo 1766084 5659607 := bstep (se 1 (by rfl) ⟨4244705, by rfl⟩ : syracuseStep 5659607 = 8489411) B8489411
theorem B20134979 : Blo 1766084 20134979 := bstep (se 1 (by rfl) ⟨15101234, by rfl⟩ : syracuseStep 20134979 = 30202469) B30202469
theorem B5963975 : Blo 1766084 5963975 := bstep (se 1 (by rfl) ⟨4472981, by rfl⟩ : syracuseStep 5963975 = 8945963) B8945963
theorem B16990735 : Blo 1766084 16990735 := bstep (se 1 (by rfl) ⟨12743051, by rfl⟩ : syracuseStep 16990735 = 25486103) B25486103
theorem B28664599 : Blo 1766084 28664599 := bstep (se 1 (by rfl) ⟨21498449, by rfl⟩ : syracuseStep 28664599 = 42996899) B42996899
theorem B13411655 : Blo 1766084 13411655 := bstep (se 1 (by rfl) ⟨10058741, by rfl⟩ : syracuseStep 13411655 = 20117483) B20117483
theorem B3974903 : Blo 1766084 3974903 := bstep (se 1 (by rfl) ⟨2981177, by rfl⟩ : syracuseStep 3974903 = 5962355) B5962355
theorem B10061567 : Blo 1766084 10061567 := bstep (se 1 (by rfl) ⟨7546175, by rfl⟩ : syracuseStep 10061567 = 15092351) B15092351
theorem B4474835 : Blo 1766084 4474835 := bstep (se 1 (by rfl) ⟨3356126, by rfl⟩ : syracuseStep 4474835 = 6712253) B6712253
theorem B64514033 : Blo 1766084 64514033 := bstep (se 2 (by rfl) ⟨24192762, by rfl⟩ : syracuseStep 64514033 = 48385525) B48385525
theorem B10062251 : Blo 1766084 10062251 := bstep (se 1 (by rfl) ⟨7546688, by rfl⟩ : syracuseStep 10062251 = 15093377) B15093377
theorem B272427695 : Blo 1766084 272427695 := bstep (se 1 (by rfl) ⟨204320771, by rfl⟩ : syracuseStep 272427695 = 408641543) B408641543
theorem B19098661 : Blo 1766084 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B4533353 : Blo 1766084 4533353 := bstep (se 2 (by rfl) ⟨1700007, by rfl⟩ : syracuseStep 4533353 = 3400015) B3400015
theorem B2649641 : Blo 1766084 2649641 := bstep (se 2 (by rfl) ⟨993615, by rfl⟩ : syracuseStep 2649641 = 1987231) B1987231
theorem B2649647 : Blo 1766084 2649647 := bstep (se 1 (by rfl) ⟨1987235, by rfl⟩ : syracuseStep 2649647 = 3974471) B3974471
theorem B1887791 : Blo 1766084 1887791 := bstep (se 1 (by rfl) ⟨1415843, by rfl⟩ : syracuseStep 1887791 = 2831687) B2831687
theorem B3272297 : Blo 1766084 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B5033609 : Blo 1766084 5033609 := bstep (se 2 (by rfl) ⟨1887603, by rfl⟩ : syracuseStep 5033609 = 3775207) B3775207
theorem B3354281 : Blo 1766084 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B21499577 : Blo 1766084 21499577 := bstep (se 2 (by rfl) ⟨8062341, by rfl⟩ : syracuseStep 21499577 = 16124683) B16124683
theorem B3977207 : Blo 1766084 3977207 := bstep (se 1 (by rfl) ⟨2982905, by rfl⟩ : syracuseStep 3977207 = 5965811) B5965811
theorem B2650223 : Blo 1766084 2650223 := bstep (se 1 (by rfl) ⟨1987667, by rfl⟩ : syracuseStep 2650223 = 3975335) B3975335
theorem B2650367 : Blo 1766084 2650367 := bstep (se 1 (by rfl) ⟨1987775, by rfl⟩ : syracuseStep 2650367 = 3975551) B3975551
theorem B2650415 : Blo 1766084 2650415 := bstep (se 1 (by rfl) ⟨1987811, by rfl⟩ : syracuseStep 2650415 = 3975623) B3975623
theorem B2650607 : Blo 1766084 2650607 := bstep (se 1 (by rfl) ⟨1987955, by rfl⟩ : syracuseStep 2650607 = 3975911) B3975911
theorem B3772985 : Blo 1766084 3772985 := bstep (se 2 (by rfl) ⟨1414869, by rfl⟩ : syracuseStep 3772985 = 2829739) B2829739
theorem B2650715 : Blo 1766084 2650715 := bstep (se 1 (by rfl) ⟨1988036, by rfl⟩ : syracuseStep 2650715 = 3976073) B3976073
theorem B3530584691 : Blo 1766084 3530584691 := bstep (se 1 (by rfl) ⟨2647938518, by rfl⟩ : syracuseStep 3530584691 = 5295877037) B5295877037
theorem B3773071 : Blo 1766084 3773071 := bstep (se 1 (by rfl) ⟨2829803, by rfl⟩ : syracuseStep 3773071 = 5659607) B5659607
theorem B2650793 : Blo 1766084 2650793 := bstep (se 2 (by rfl) ⟨994047, by rfl⟩ : syracuseStep 2650793 = 1988095) B1988095
theorem B13423319 : Blo 1766084 13423319 := bstep (se 1 (by rfl) ⟨10067489, by rfl⟩ : syracuseStep 13423319 = 20134979) B20134979
theorem B1766119 : Blo 1766084 1766119 := bstep (se 1 (by rfl) ⟨1324589, by rfl⟩ : syracuseStep 1766119 = 2649179) B2649179
theorem B2650919 : Blo 1766084 2650919 := bstep (se 1 (by rfl) ⟨1988189, by rfl⟩ : syracuseStep 2650919 = 3976379) B3976379
theorem B1766335 : Blo 1766084 1766335 := bstep (se 1 (by rfl) ⟨1324751, by rfl⟩ : syracuseStep 1766335 = 2649503) B2649503
theorem B1766703 : Blo 1766084 1766703 := bstep (se 1 (by rfl) ⟨1325027, by rfl⟩ : syracuseStep 1766703 = 2650055) B2650055
theorem B16979321 : Blo 1766084 16979321 := bstep (se 2 (by rfl) ⟨6367245, by rfl⟩ : syracuseStep 16979321 = 12734491) B12734491
theorem B2651615 : Blo 1766084 2651615 := bstep (se 1 (by rfl) ⟨1988711, by rfl⟩ : syracuseStep 2651615 = 3977423) B3977423
theorem B6370937 : Blo 1766084 6370937 := bstep (se 2 (by rfl) ⟨2389101, by rfl⟩ : syracuseStep 6370937 = 4778203) B4778203
theorem B1767039 : Blo 1766084 1767039 := bstep (se 1 (by rfl) ⟨1325279, by rfl⟩ : syracuseStep 1767039 = 2650559) B2650559
theorem B5961491 : Blo 1766084 5961491 := bstep (se 1 (by rfl) ⟨4471118, by rfl⟩ : syracuseStep 5961491 = 8942237) B8942237
theorem B1767359 : Blo 1766084 1767359 := bstep (se 1 (by rfl) ⟨1325519, by rfl⟩ : syracuseStep 1767359 = 2651039) B2651039
theorem B6707195 : Blo 1766084 6707195 := bstep (se 1 (by rfl) ⟨5030396, by rfl⟩ : syracuseStep 6707195 = 10060793) B10060793
theorem B1768039 : Blo 1766084 1768039 := bstep (se 1 (by rfl) ⟨1326029, by rfl⟩ : syracuseStep 1768039 = 2652059) B2652059
theorem B2980543 : Blo 1766084 2980543 := bstep (se 1 (by rfl) ⟨2235407, by rfl⟩ : syracuseStep 2980543 = 4470815) B4470815
theorem B48347873 : Blo 1766084 48347873 := bstep (se 2 (by rfl) ⟨18130452, by rfl⟩ : syracuseStep 48347873 = 36260905) B36260905
theorem B3022127 : Blo 1766084 3022127 := bstep (se 1 (by rfl) ⟨2266595, by rfl⟩ : syracuseStep 3022127 = 4533191) B4533191
theorem B7544603 : Blo 1766084 7544603 := bstep (se 1 (by rfl) ⟨5658452, by rfl⟩ : syracuseStep 7544603 = 11316905) B11316905
theorem B20136437 : Blo 1766084 20136437 := bstep (se 5 (by rfl) ⟨943895, by rfl⟩ : syracuseStep 20136437 = 1887791) B1887791
theorem B5030761 : Blo 1766084 5030761 := bstep (se 2 (by rfl) ⟨1886535, by rfl⟩ : syracuseStep 5030761 = 3773071) B3773071
theorem B3974057 : Blo 1766084 3974057 := bstep (se 2 (by rfl) ⟨1490271, by rfl⟩ : syracuseStep 3974057 = 2980543) B2980543
theorem B3974327 : Blo 1766084 3974327 := bstep (se 1 (by rfl) ⟨2980745, by rfl⟩ : syracuseStep 3974327 = 5961491) B5961491
theorem B2983223 : Blo 1766084 2983223 := bstep (se 1 (by rfl) ⟨2237417, by rfl⟩ : syracuseStep 2983223 = 4474835) B4474835
theorem B43009355 : Blo 1766084 43009355 := bstep (se 1 (by rfl) ⟨32257016, by rfl⟩ : syracuseStep 43009355 = 64514033) B64514033
theorem B10061293 : Blo 1766084 10061293 := bstep (se 3 (by rfl) ⟨1886492, by rfl⟩ : syracuseStep 10061293 = 3772985) B3772985
theorem B8726125 : Blo 1766084 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B181618463 : Blo 1766084 181618463 := bstep (se 1 (by rfl) ⟨136213847, by rfl⟩ : syracuseStep 181618463 = 272427695) B272427695
theorem B3975983 : Blo 1766084 3975983 := bstep (se 1 (by rfl) ⟨2981987, by rfl⟩ : syracuseStep 3975983 = 5963975) B5963975
theorem B8948879 : Blo 1766084 8948879 := bstep (se 1 (by rfl) ⟨6711659, by rfl⟩ : syracuseStep 8948879 = 13423319) B13423319
theorem B22654313 : Blo 1766084 22654313 := bstep (se 2 (by rfl) ⟨8495367, by rfl⟩ : syracuseStep 22654313 = 16990735) B16990735
theorem B8941103 : Blo 1766084 8941103 := bstep (se 1 (by rfl) ⟨6705827, by rfl⟩ : syracuseStep 8941103 = 13411655) B13411655
theorem B38219465 : Blo 1766084 38219465 := bstep (se 2 (by rfl) ⟨14332299, by rfl⟩ : syracuseStep 38219465 = 28664599) B28664599
theorem B4247291 : Blo 1766084 4247291 := bstep (se 1 (by rfl) ⟨3185468, by rfl⟩ : syracuseStep 4247291 = 6370937) B6370937
theorem B2649935 : Blo 1766084 2649935 := bstep (se 1 (by rfl) ⟨1987451, by rfl⟩ : syracuseStep 2649935 = 3974903) B3974903
theorem B25464881 : Blo 1766084 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B32231915 : Blo 1766084 32231915 := bstep (se 1 (by rfl) ⟨24173936, by rfl⟩ : syracuseStep 32231915 = 48347873) B48347873
theorem B1766427 : Blo 1766084 1766427 := bstep (se 1 (by rfl) ⟨1324820, by rfl⟩ : syracuseStep 1766427 = 2649641) B2649641
theorem B1766431 : Blo 1766084 1766431 := bstep (se 1 (by rfl) ⟨1324823, by rfl⟩ : syracuseStep 1766431 = 2649647) B2649647
theorem B3355739 : Blo 1766084 3355739 := bstep (se 1 (by rfl) ⟨2516804, by rfl⟩ : syracuseStep 3355739 = 5033609) B5033609
theorem B14333051 : Blo 1766084 14333051 := bstep (se 1 (by rfl) ⟨10749788, by rfl⟩ : syracuseStep 14333051 = 21499577) B21499577
theorem B2651471 : Blo 1766084 2651471 := bstep (se 1 (by rfl) ⟨1988603, by rfl⟩ : syracuseStep 2651471 = 3977207) B3977207
theorem B1766815 : Blo 1766084 1766815 := bstep (se 1 (by rfl) ⟨1325111, by rfl⟩ : syracuseStep 1766815 = 2650223) B2650223
theorem B1766911 : Blo 1766084 1766911 := bstep (se 1 (by rfl) ⟨1325183, by rfl⟩ : syracuseStep 1766911 = 2650367) B2650367
theorem B1766943 : Blo 1766084 1766943 := bstep (se 1 (by rfl) ⟨1325207, by rfl⟩ : syracuseStep 1766943 = 2650415) B2650415
theorem B1767071 : Blo 1766084 1767071 := bstep (se 1 (by rfl) ⟨1325303, by rfl⟩ : syracuseStep 1767071 = 2650607) B2650607
theorem B1767143 : Blo 1766084 1767143 := bstep (se 1 (by rfl) ⟨1325357, by rfl⟩ : syracuseStep 1767143 = 2650715) B2650715
theorem B2353723127 : Blo 1766084 2353723127 := bstep (se 1 (by rfl) ⟨1765292345, by rfl⟩ : syracuseStep 2353723127 = 3530584691) B3530584691
theorem B1767195 : Blo 1766084 1767195 := bstep (se 1 (by rfl) ⟨1325396, by rfl⟩ : syracuseStep 1767195 = 2650793) B2650793
theorem B1767279 : Blo 1766084 1767279 := bstep (se 1 (by rfl) ⟨1325459, by rfl⟩ : syracuseStep 1767279 = 2650919) B2650919
theorem B11319547 : Blo 1766084 11319547 := bstep (se 1 (by rfl) ⟨8489660, by rfl⟩ : syracuseStep 11319547 = 16979321) B16979321
theorem B1767743 : Blo 1766084 1767743 := bstep (se 1 (by rfl) ⟨1325807, by rfl⟩ : syracuseStep 1767743 = 2651615) B2651615
theorem B6707711 : Blo 1766084 6707711 := bstep (se 1 (by rfl) ⟨5030783, by rfl⟩ : syracuseStep 6707711 = 10061567) B10061567
theorem B4471463 : Blo 1766084 4471463 := bstep (se 1 (by rfl) ⟨3353597, by rfl⟩ : syracuseStep 4471463 = 6707195) B6707195
theorem B6708167 : Blo 1766084 6708167 := bstep (se 1 (by rfl) ⟨5031125, by rfl⟩ : syracuseStep 6708167 = 10062251) B10062251
theorem B3022235 : Blo 1766084 3022235 := bstep (se 1 (by rfl) ⟨2266676, by rfl⟩ : syracuseStep 3022235 = 4533353) B4533353
theorem B20118941 : Blo 1766084 20118941 := bstep (se 3 (by rfl) ⟨3772301, by rfl⟩ : syracuseStep 20118941 = 7544603) B7544603
theorem B2014751 : Blo 1766084 2014751 := bstep (se 1 (by rfl) ⟨1511063, by rfl⟩ : syracuseStep 2014751 = 3022127) B3022127
theorem B2236187 : Blo 1766084 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B21487943 : Blo 1766084 21487943 := bstep (se 1 (by rfl) ⟨16115957, by rfl⟩ : syracuseStep 21487943 = 32231915) B32231915
theorem B2237159 : Blo 1766084 2237159 := bstep (se 1 (by rfl) ⟨1677869, by rfl⟩ : syracuseStep 2237159 = 3355739) B3355739
theorem B28672903 : Blo 1766084 28672903 := bstep (se 1 (by rfl) ⟨21504677, by rfl⟩ : syracuseStep 28672903 = 43009355) B43009355
theorem B101918573 : Blo 1766084 101918573 := bstep (se 3 (by rfl) ⟨19109732, by rfl⟩ : syracuseStep 101918573 = 38219465) B38219465
theorem B5965919 : Blo 1766084 5965919 := bstep (se 1 (by rfl) ⟨4474439, by rfl⟩ : syracuseStep 5965919 = 8948879) B8948879
theorem B11634833 : Blo 1766084 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B13412627 : Blo 1766084 13412627 := bstep (se 1 (by rfl) ⟨10059470, by rfl⟩ : syracuseStep 13412627 = 20118941) B20118941
theorem B67906349 : Blo 1766084 67906349 := bstep (se 3 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 67906349 = 25464881) B25464881
theorem B15092729 : Blo 1766084 15092729 := bstep (se 2 (by rfl) ⟨5659773, by rfl⟩ : syracuseStep 15092729 = 11319547) B11319547
theorem B2649371 : Blo 1766084 2649371 := bstep (se 1 (by rfl) ⟨1987028, by rfl⟩ : syracuseStep 2649371 = 3974057) B3974057
theorem B2649551 : Blo 1766084 2649551 := bstep (se 1 (by rfl) ⟨1987163, by rfl⟩ : syracuseStep 2649551 = 3974327) B3974327
theorem B1569148751 : Blo 1766084 1569148751 := bstep (se 1 (by rfl) ⟨1176861563, by rfl⟩ : syracuseStep 1569148751 = 2353723127) B2353723127
theorem B2650655 : Blo 1766084 2650655 := bstep (se 1 (by rfl) ⟨1987991, by rfl⟩ : syracuseStep 2650655 = 3975983) B3975983
theorem B13415057 : Blo 1766084 13415057 := bstep (se 2 (by rfl) ⟨5030646, by rfl⟩ : syracuseStep 13415057 = 10061293) B10061293
theorem B484315901 : Blo 1766084 484315901 := bstep (se 3 (by rfl) ⟨90809231, by rfl⟩ : syracuseStep 484315901 = 181618463) B181618463
theorem B15102875 : Blo 1766084 15102875 := bstep (se 1 (by rfl) ⟨11327156, by rfl⟩ : syracuseStep 15102875 = 22654313) B22654313
theorem B5960735 : Blo 1766084 5960735 := bstep (se 1 (by rfl) ⟨4470551, by rfl⟩ : syracuseStep 5960735 = 8941103) B8941103
theorem B2831527 : Blo 1766084 2831527 := bstep (se 1 (by rfl) ⟨2123645, by rfl⟩ : syracuseStep 2831527 = 4247291) B4247291
theorem B1766623 : Blo 1766084 1766623 := bstep (se 1 (by rfl) ⟨1324967, by rfl⟩ : syracuseStep 1766623 = 2649935) B2649935
theorem B38221469 : Blo 1766084 38221469 := bstep (se 3 (by rfl) ⟨7166525, by rfl⟩ : syracuseStep 38221469 = 14333051) B14333051
theorem B13424291 : Blo 1766084 13424291 := bstep (se 1 (by rfl) ⟨10068218, by rfl⟩ : syracuseStep 13424291 = 20136437) B20136437
theorem B1988815 : Blo 1766084 1988815 := bstep (se 1 (by rfl) ⟨1491611, by rfl⟩ : syracuseStep 1988815 = 2983223) B2983223
theorem B1767647 : Blo 1766084 1767647 := bstep (se 1 (by rfl) ⟨1325735, by rfl⟩ : syracuseStep 1767647 = 2651471) B2651471
theorem B6707681 : Blo 1766084 6707681 := bstep (se 2 (by rfl) ⟨2515380, by rfl⟩ : syracuseStep 6707681 = 5030761) B5030761
theorem B5372669 : Blo 1766084 5372669 := bstep (se 3 (by rfl) ⟨1007375, by rfl⟩ : syracuseStep 5372669 = 2014751) B2014751
theorem B4471807 : Blo 1766084 4471807 := bstep (se 1 (by rfl) ⟨3353855, by rfl⟩ : syracuseStep 4471807 = 6707711) B6707711
theorem B2980975 : Blo 1766084 2980975 := bstep (se 1 (by rfl) ⟨2235731, by rfl⟩ : syracuseStep 2980975 = 4471463) B4471463
theorem B4472111 : Blo 1766084 4472111 := bstep (se 1 (by rfl) ⟨3354083, by rfl⟩ : syracuseStep 4472111 = 6708167) B6708167
theorem B5963165 : Blo 1766084 5963165 := bstep (se 3 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 5963165 = 2236187) B2236187
theorem B2014823 : Blo 1766084 2014823 := bstep (se 1 (by rfl) ⟨1511117, by rfl⟩ : syracuseStep 2014823 = 3022235) B3022235
theorem B10068583 : Blo 1766084 10068583 := bstep (se 1 (by rfl) ⟨7551437, by rfl⟩ : syracuseStep 10068583 = 15102875) B15102875
theorem B3973823 : Blo 1766084 3973823 := bstep (se 1 (by rfl) ⟨2980367, by rfl⟩ : syracuseStep 3973823 = 5960735) B5960735
theorem B67945715 : Blo 1766084 67945715 := bstep (se 1 (by rfl) ⟨50959286, by rfl⟩ : syracuseStep 67945715 = 101918573) B101918573
theorem B3974633 : Blo 1766084 3974633 := bstep (se 2 (by rfl) ⟨1490487, by rfl⟩ : syracuseStep 3974633 = 2980975) B2980975
theorem B3581779 : Blo 1766084 3581779 := bstep (se 1 (by rfl) ⟨2686334, by rfl⟩ : syracuseStep 3581779 = 5372669) B5372669
theorem B45270899 : Blo 1766084 45270899 := bstep (se 1 (by rfl) ⟨33953174, by rfl⟩ : syracuseStep 45270899 = 67906349) B67906349
theorem B5965757 : Blo 1766084 5965757 := bstep (se 3 (by rfl) ⟨1118579, by rfl⟩ : syracuseStep 5965757 = 2237159) B2237159
theorem B10061819 : Blo 1766084 10061819 := bstep (se 1 (by rfl) ⟨7546364, by rfl⟩ : syracuseStep 10061819 = 15092729) B15092729
theorem B3975443 : Blo 1766084 3975443 := bstep (se 1 (by rfl) ⟨2981582, by rfl⟩ : syracuseStep 3975443 = 5963165) B5963165
theorem B15101477 : Blo 1766084 15101477 := bstep (se 4 (by rfl) ⟨1415763, by rfl⟩ : syracuseStep 15101477 = 2831527) B2831527
theorem B25480979 : Blo 1766084 25480979 := bstep (se 1 (by rfl) ⟨19110734, by rfl⟩ : syracuseStep 25480979 = 38221469) B38221469
theorem B8949527 : Blo 1766084 8949527 := bstep (se 1 (by rfl) ⟨6712145, by rfl⟩ : syracuseStep 8949527 = 13424291) B13424291
theorem B3977279 : Blo 1766084 3977279 := bstep (se 1 (by rfl) ⟨2982959, by rfl⟩ : syracuseStep 3977279 = 5965919) B5965919
theorem B8941751 : Blo 1766084 8941751 := bstep (se 1 (by rfl) ⟨6706313, by rfl⟩ : syracuseStep 8941751 = 13412627) B13412627
theorem B1766247 : Blo 1766084 1766247 := bstep (se 1 (by rfl) ⟨1324685, by rfl⟩ : syracuseStep 1766247 = 2649371) B2649371
theorem B1766367 : Blo 1766084 1766367 := bstep (se 1 (by rfl) ⟨1324775, by rfl⟩ : syracuseStep 1766367 = 2649551) B2649551
theorem B1046099167 : Blo 1766084 1046099167 := bstep (se 1 (by rfl) ⟨784574375, by rfl⟩ : syracuseStep 1046099167 = 1569148751) B1569148751
theorem B14325295 : Blo 1766084 14325295 := bstep (se 1 (by rfl) ⟨10743971, by rfl⟩ : syracuseStep 14325295 = 21487943) B21487943
theorem B2651753 : Blo 1766084 2651753 := bstep (se 2 (by rfl) ⟨994407, by rfl⟩ : syracuseStep 2651753 = 1988815) B1988815
theorem B1767103 : Blo 1766084 1767103 := bstep (se 1 (by rfl) ⟨1325327, by rfl⟩ : syracuseStep 1767103 = 2650655) B2650655
theorem B8943371 : Blo 1766084 8943371 := bstep (se 1 (by rfl) ⟨6707528, by rfl⟩ : syracuseStep 8943371 = 13415057) B13415057
theorem B322877267 : Blo 1766084 322877267 := bstep (se 1 (by rfl) ⟨242157950, by rfl⟩ : syracuseStep 322877267 = 484315901) B484315901
theorem B38230537 : Blo 1766084 38230537 := bstep (se 2 (by rfl) ⟨14336451, by rfl⟩ : syracuseStep 38230537 = 28672903) B28672903
theorem B5962409 : Blo 1766084 5962409 := bstep (se 2 (by rfl) ⟨2235903, by rfl⟩ : syracuseStep 5962409 = 4471807) B4471807
theorem B7756555 : Blo 1766084 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B5372861 : Blo 1766084 5372861 := bstep (se 3 (by rfl) ⟨1007411, by rfl⟩ : syracuseStep 5372861 = 2014823) B2014823
theorem B4471787 : Blo 1766084 4471787 := bstep (se 1 (by rfl) ⟨3353840, by rfl⟩ : syracuseStep 4471787 = 6707681) B6707681
theorem B2981407 : Blo 1766084 2981407 := bstep (se 1 (by rfl) ⟨2236055, by rfl⟩ : syracuseStep 2981407 = 4472111) B4472111
theorem B5579195557 : Blo 1766084 5579195557 := bstep (se 4 (by rfl) ⟨523049583, by rfl⟩ : syracuseStep 5579195557 = 1046099167) B1046099167
theorem B30180599 : Blo 1766084 30180599 := bstep (se 1 (by rfl) ⟨22635449, by rfl⟩ : syracuseStep 30180599 = 45270899) B45270899
theorem B3974939 : Blo 1766084 3974939 := bstep (se 1 (by rfl) ⟨2981204, by rfl⟩ : syracuseStep 3974939 = 5962409) B5962409
theorem B3975209 : Blo 1766084 3975209 := bstep (se 2 (by rfl) ⟨1490703, by rfl⟩ : syracuseStep 3975209 = 2981407) B2981407
theorem B5966351 : Blo 1766084 5966351 := bstep (se 1 (by rfl) ⟨4474763, by rfl⟩ : syracuseStep 5966351 = 8949527) B8949527
theorem B2649215 : Blo 1766084 2649215 := bstep (se 1 (by rfl) ⟨1986911, by rfl⟩ : syracuseStep 2649215 = 3973823) B3973823
theorem B50974049 : Blo 1766084 50974049 := bstep (se 2 (by rfl) ⟨19115268, by rfl⟩ : syracuseStep 50974049 = 38230537) B38230537
theorem B45297143 : Blo 1766084 45297143 := bstep (se 1 (by rfl) ⟨33972857, by rfl⟩ : syracuseStep 45297143 = 67945715) B67945715
theorem B2649755 : Blo 1766084 2649755 := bstep (se 1 (by rfl) ⟨1987316, by rfl⟩ : syracuseStep 2649755 = 3974633) B3974633
theorem B10342073 : Blo 1766084 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B3977171 : Blo 1766084 3977171 := bstep (se 1 (by rfl) ⟨2982878, by rfl⟩ : syracuseStep 3977171 = 5965757) B5965757
theorem B2650295 : Blo 1766084 2650295 := bstep (se 1 (by rfl) ⟨1987721, by rfl⟩ : syracuseStep 2650295 = 3975443) B3975443
theorem B19100393 : Blo 1766084 19100393 := bstep (se 2 (by rfl) ⟨7162647, by rfl⟩ : syracuseStep 19100393 = 14325295) B14325295
theorem B16987319 : Blo 1766084 16987319 := bstep (se 1 (by rfl) ⟨12740489, by rfl⟩ : syracuseStep 16987319 = 25480979) B25480979
theorem B2651519 : Blo 1766084 2651519 := bstep (se 1 (by rfl) ⟨1988639, by rfl⟩ : syracuseStep 2651519 = 3977279) B3977279
theorem B5961167 : Blo 1766084 5961167 := bstep (se 1 (by rfl) ⟨4470875, by rfl⟩ : syracuseStep 5961167 = 8941751) B8941751
theorem B13424777 : Blo 1766084 13424777 := bstep (se 2 (by rfl) ⟨5034291, by rfl⟩ : syracuseStep 13424777 = 10068583) B10068583
theorem B1767835 : Blo 1766084 1767835 := bstep (se 1 (by rfl) ⟨1325876, by rfl⟩ : syracuseStep 1767835 = 2651753) B2651753
theorem B5962247 : Blo 1766084 5962247 := bstep (se 1 (by rfl) ⟨4471685, by rfl⟩ : syracuseStep 5962247 = 8943371) B8943371
theorem B215251511 : Blo 1766084 215251511 := bstep (se 1 (by rfl) ⟨161438633, by rfl⟩ : syracuseStep 215251511 = 322877267) B322877267
theorem B6707879 : Blo 1766084 6707879 := bstep (se 1 (by rfl) ⟨5030909, by rfl⟩ : syracuseStep 6707879 = 10061819) B10061819
theorem B57310517 : Blo 1766084 57310517 := bstep (se 5 (by rfl) ⟨2686430, by rfl⟩ : syracuseStep 57310517 = 5372861) B5372861
theorem B2981191 : Blo 1766084 2981191 := bstep (se 1 (by rfl) ⟨2235893, by rfl⟩ : syracuseStep 2981191 = 4471787) B4471787
theorem B10067651 : Blo 1766084 10067651 := bstep (se 1 (by rfl) ⟨7550738, by rfl⟩ : syracuseStep 10067651 = 15101477) B15101477
theorem B4775705 : Blo 1766084 4775705 := bstep (se 2 (by rfl) ⟨1790889, by rfl⟩ : syracuseStep 4775705 = 3581779) B3581779
theorem B20120399 : Blo 1766084 20120399 := bstep (se 1 (by rfl) ⟨15090299, by rfl⟩ : syracuseStep 20120399 = 30180599) B30180599
theorem B3974111 : Blo 1766084 3974111 := bstep (se 1 (by rfl) ⟨2980583, by rfl⟩ : syracuseStep 3974111 = 5961167) B5961167
theorem B7438927409 : Blo 1766084 7438927409 := bstep (se 2 (by rfl) ⟨2789597778, by rfl⟩ : syracuseStep 7438927409 = 5579195557) B5579195557
theorem B3974831 : Blo 1766084 3974831 := bstep (se 1 (by rfl) ⟨2981123, by rfl⟩ : syracuseStep 3974831 = 5962247) B5962247
theorem B3974921 : Blo 1766084 3974921 := bstep (se 2 (by rfl) ⟨1490595, by rfl⟩ : syracuseStep 3974921 = 2981191) B2981191
theorem B33982699 : Blo 1766084 33982699 := bstep (se 1 (by rfl) ⟨25487024, by rfl⟩ : syracuseStep 33982699 = 50974049) B50974049
theorem B30198095 : Blo 1766084 30198095 := bstep (se 1 (by rfl) ⟨22648571, by rfl⟩ : syracuseStep 30198095 = 45297143) B45297143
theorem B6711767 : Blo 1766084 6711767 := bstep (se 1 (by rfl) ⟨5033825, by rfl⟩ : syracuseStep 6711767 = 10067651) B10067651
theorem B12733595 : Blo 1766084 12733595 := bstep (se 1 (by rfl) ⟨9550196, by rfl⟩ : syracuseStep 12733595 = 19100393) B19100393
theorem B11324879 : Blo 1766084 11324879 := bstep (se 1 (by rfl) ⟨8493659, by rfl⟩ : syracuseStep 11324879 = 16987319) B16987319
theorem B2649959 : Blo 1766084 2649959 := bstep (se 1 (by rfl) ⟨1987469, by rfl⟩ : syracuseStep 2649959 = 3974939) B3974939
theorem B2650139 : Blo 1766084 2650139 := bstep (se 1 (by rfl) ⟨1987604, by rfl⟩ : syracuseStep 2650139 = 3975209) B3975209
theorem B8949851 : Blo 1766084 8949851 := bstep (se 1 (by rfl) ⟨6712388, by rfl⟩ : syracuseStep 8949851 = 13424777) B13424777
theorem B3977567 : Blo 1766084 3977567 := bstep (se 1 (by rfl) ⟨2983175, by rfl⟩ : syracuseStep 3977567 = 5966351) B5966351
theorem B1766143 : Blo 1766084 1766143 := bstep (se 1 (by rfl) ⟨1324607, by rfl⟩ : syracuseStep 1766143 = 2649215) B2649215
theorem B1766503 : Blo 1766084 1766503 := bstep (se 1 (by rfl) ⟨1324877, by rfl⟩ : syracuseStep 1766503 = 2649755) B2649755
theorem B6894715 : Blo 1766084 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B3183803 : Blo 1766084 3183803 := bstep (se 1 (by rfl) ⟨2387852, by rfl⟩ : syracuseStep 3183803 = 4775705) B4775705
theorem B2651447 : Blo 1766084 2651447 := bstep (se 1 (by rfl) ⟨1988585, by rfl⟩ : syracuseStep 2651447 = 3977171) B3977171
theorem B1766863 : Blo 1766084 1766863 := bstep (se 1 (by rfl) ⟨1325147, by rfl⟩ : syracuseStep 1766863 = 2650295) B2650295
theorem B1767679 : Blo 1766084 1767679 := bstep (se 1 (by rfl) ⟨1325759, by rfl⟩ : syracuseStep 1767679 = 2651519) B2651519
theorem B574004029 : Blo 1766084 574004029 := bstep (se 3 (by rfl) ⟨107625755, by rfl⟩ : syracuseStep 574004029 = 215251511) B215251511
theorem B4471919 : Blo 1766084 4471919 := bstep (se 1 (by rfl) ⟨3353939, by rfl⟩ : syracuseStep 4471919 = 6707879) B6707879
theorem B38207011 : Blo 1766084 38207011 := bstep (se 1 (by rfl) ⟨28655258, by rfl⟩ : syracuseStep 38207011 = 57310517) B57310517
theorem B45310265 : Blo 1766084 45310265 := bstep (se 2 (by rfl) ⟨16991349, by rfl⟩ : syracuseStep 45310265 = 33982699) B33982699
theorem B2122535 : Blo 1766084 2122535 := bstep (se 1 (by rfl) ⟨1591901, by rfl⟩ : syracuseStep 2122535 = 3183803) B3183803
theorem B765338705 : Blo 1766084 765338705 := bstep (se 2 (by rfl) ⟨287002014, by rfl⟩ : syracuseStep 765338705 = 574004029) B574004029
theorem B9192953 : Blo 1766084 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B4474511 : Blo 1766084 4474511 := bstep (se 1 (by rfl) ⟨3355883, by rfl⟩ : syracuseStep 4474511 = 6711767) B6711767
theorem B8489063 : Blo 1766084 8489063 := bstep (se 1 (by rfl) ⟨6366797, by rfl⟩ : syracuseStep 8489063 = 12733595) B12733595
theorem B5966567 : Blo 1766084 5966567 := bstep (se 1 (by rfl) ⟨4474925, by rfl⟩ : syracuseStep 5966567 = 8949851) B8949851
theorem B13413599 : Blo 1766084 13413599 := bstep (se 1 (by rfl) ⟨10060199, by rfl⟩ : syracuseStep 13413599 = 20120399) B20120399
theorem B2649407 : Blo 1766084 2649407 := bstep (se 1 (by rfl) ⟨1987055, by rfl⟩ : syracuseStep 2649407 = 3974111) B3974111
theorem B4959284939 : Blo 1766084 4959284939 := bstep (se 1 (by rfl) ⟨3719463704, by rfl⟩ : syracuseStep 4959284939 = 7438927409) B7438927409
theorem B2649887 : Blo 1766084 2649887 := bstep (se 1 (by rfl) ⟨1987415, by rfl⟩ : syracuseStep 2649887 = 3974831) B3974831
theorem B2649947 : Blo 1766084 2649947 := bstep (se 1 (by rfl) ⟨1987460, by rfl⟩ : syracuseStep 2649947 = 3974921) B3974921
theorem B20132063 : Blo 1766084 20132063 := bstep (se 1 (by rfl) ⟨15099047, by rfl⟩ : syracuseStep 20132063 = 30198095) B30198095
theorem B50942681 : Blo 1766084 50942681 := bstep (se 2 (by rfl) ⟨19103505, by rfl⟩ : syracuseStep 50942681 = 38207011) B38207011
theorem B7549919 : Blo 1766084 7549919 := bstep (se 1 (by rfl) ⟨5662439, by rfl⟩ : syracuseStep 7549919 = 11324879) B11324879
theorem B1766639 : Blo 1766084 1766639 := bstep (se 1 (by rfl) ⟨1324979, by rfl⟩ : syracuseStep 1766639 = 2649959) B2649959
theorem B1766759 : Blo 1766084 1766759 := bstep (se 1 (by rfl) ⟨1325069, by rfl⟩ : syracuseStep 1766759 = 2650139) B2650139
theorem B2651711 : Blo 1766084 2651711 := bstep (se 1 (by rfl) ⟨1988783, by rfl⟩ : syracuseStep 2651711 = 3977567) B3977567
theorem B1767631 : Blo 1766084 1767631 := bstep (se 1 (by rfl) ⟨1325723, by rfl⟩ : syracuseStep 1767631 = 2651447) B2651447
theorem B2981279 : Blo 1766084 2981279 := bstep (se 1 (by rfl) ⟨2235959, by rfl⟩ : syracuseStep 2981279 = 4471919) B4471919
theorem B6128635 : Blo 1766084 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B2983007 : Blo 1766084 2983007 := bstep (se 1 (by rfl) ⟨2237255, by rfl⟩ : syracuseStep 2983007 = 4474511) B4474511
theorem B13421375 : Blo 1766084 13421375 := bstep (se 1 (by rfl) ⟨10066031, by rfl⟩ : syracuseStep 13421375 = 20132063) B20132063
theorem B30206843 : Blo 1766084 30206843 := bstep (se 1 (by rfl) ⟨22655132, by rfl⟩ : syracuseStep 30206843 = 45310265) B45310265
theorem B22637501 : Blo 1766084 22637501 := bstep (se 3 (by rfl) ⟨4244531, by rfl⟩ : syracuseStep 22637501 = 8489063) B8489063
theorem B5033279 : Blo 1766084 5033279 := bstep (se 1 (by rfl) ⟨3774959, by rfl⟩ : syracuseStep 5033279 = 7549919) B7549919
theorem B510225803 : Blo 1766084 510225803 := bstep (se 1 (by rfl) ⟨382669352, by rfl⟩ : syracuseStep 510225803 = 765338705) B765338705
theorem B3977711 : Blo 1766084 3977711 := bstep (se 1 (by rfl) ⟨2983283, by rfl⟩ : syracuseStep 3977711 = 5966567) B5966567
theorem B8942399 : Blo 1766084 8942399 := bstep (se 1 (by rfl) ⟨6706799, by rfl⟩ : syracuseStep 8942399 = 13413599) B13413599
theorem B1766271 : Blo 1766084 1766271 := bstep (se 1 (by rfl) ⟨1324703, by rfl⟩ : syracuseStep 1766271 = 2649407) B2649407
theorem B1987519 : Blo 1766084 1987519 := bstep (se 1 (by rfl) ⟨1490639, by rfl⟩ : syracuseStep 1987519 = 2981279) B2981279
theorem B3306189959 : Blo 1766084 3306189959 := bstep (se 1 (by rfl) ⟨2479642469, by rfl⟩ : syracuseStep 3306189959 = 4959284939) B4959284939
theorem B1766591 : Blo 1766084 1766591 := bstep (se 1 (by rfl) ⟨1324943, by rfl⟩ : syracuseStep 1766591 = 2649887) B2649887
theorem B1766631 : Blo 1766084 1766631 := bstep (se 1 (by rfl) ⟨1324973, by rfl⟩ : syracuseStep 1766631 = 2649947) B2649947
theorem B33961787 : Blo 1766084 33961787 := bstep (se 1 (by rfl) ⟨25471340, by rfl⟩ : syracuseStep 33961787 = 50942681) B50942681
theorem B1767807 : Blo 1766084 1767807 := bstep (se 1 (by rfl) ⟨1325855, by rfl⟩ : syracuseStep 1767807 = 2651711) B2651711
theorem B5660093 : Blo 1766084 5660093 := bstep (se 3 (by rfl) ⟨1061267, by rfl⟩ : syracuseStep 5660093 = 2122535) B2122535
theorem B8947583 : Blo 1766084 8947583 := bstep (se 1 (by rfl) ⟨6710687, by rfl⟩ : syracuseStep 8947583 = 13421375) B13421375
theorem B20137895 : Blo 1766084 20137895 := bstep (se 1 (by rfl) ⟨15103421, by rfl⟩ : syracuseStep 20137895 = 30206843) B30206843
theorem B15091667 : Blo 1766084 15091667 := bstep (se 1 (by rfl) ⟨11318750, by rfl⟩ : syracuseStep 15091667 = 22637501) B22637501
theorem B340150535 : Blo 1766084 340150535 := bstep (se 1 (by rfl) ⟨255112901, by rfl⟩ : syracuseStep 340150535 = 510225803) B510225803
theorem B2204126639 : Blo 1766084 2204126639 := bstep (se 1 (by rfl) ⟨1653094979, by rfl⟩ : syracuseStep 2204126639 = 3306189959) B3306189959
theorem B2650025 : Blo 1766084 2650025 := bstep (se 2 (by rfl) ⟨993759, by rfl⟩ : syracuseStep 2650025 = 1987519) B1987519
theorem B8171513 : Blo 1766084 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B3355519 : Blo 1766084 3355519 := bstep (se 1 (by rfl) ⟨2516639, by rfl⟩ : syracuseStep 3355519 = 5033279) B5033279
theorem B3773395 : Blo 1766084 3773395 := bstep (se 1 (by rfl) ⟨2830046, by rfl⟩ : syracuseStep 3773395 = 5660093) B5660093
theorem B2651807 : Blo 1766084 2651807 := bstep (se 1 (by rfl) ⟨1988855, by rfl⟩ : syracuseStep 2651807 = 3977711) B3977711
theorem B5961599 : Blo 1766084 5961599 := bstep (se 1 (by rfl) ⟨4471199, by rfl⟩ : syracuseStep 5961599 = 8942399) B8942399
theorem B1988671 : Blo 1766084 1988671 := bstep (se 1 (by rfl) ⟨1491503, by rfl⟩ : syracuseStep 1988671 = 2983007) B2983007
theorem B22641191 : Blo 1766084 22641191 := bstep (se 1 (by rfl) ⟨16980893, by rfl⟩ : syracuseStep 22641191 = 33961787) B33961787
theorem B4474025 : Blo 1766084 4474025 := bstep (se 2 (by rfl) ⟨1677759, by rfl⟩ : syracuseStep 4474025 = 3355519) B3355519
theorem B3974399 : Blo 1766084 3974399 := bstep (se 1 (by rfl) ⟨2980799, by rfl⟩ : syracuseStep 3974399 = 5961599) B5961599
theorem B5965055 : Blo 1766084 5965055 := bstep (se 1 (by rfl) ⟨4473791, by rfl⟩ : syracuseStep 5965055 = 8947583) B8947583
theorem B10061111 : Blo 1766084 10061111 := bstep (se 1 (by rfl) ⟨7545833, by rfl⟩ : syracuseStep 10061111 = 15091667) B15091667
theorem B1469417759 : Blo 1766084 1469417759 := bstep (se 1 (by rfl) ⟨1102063319, by rfl⟩ : syracuseStep 1469417759 = 2204126639) B2204126639
theorem B226767023 : Blo 1766084 226767023 := bstep (se 1 (by rfl) ⟨170075267, by rfl⟩ : syracuseStep 226767023 = 340150535) B340150535
theorem B15094127 : Blo 1766084 15094127 := bstep (se 1 (by rfl) ⟨11320595, by rfl⟩ : syracuseStep 15094127 = 22641191) B22641191
theorem B20124773 : Blo 1766084 20124773 := bstep (se 4 (by rfl) ⟨1886697, by rfl⟩ : syracuseStep 20124773 = 3773395) B3773395
theorem B1766683 : Blo 1766084 1766683 := bstep (se 1 (by rfl) ⟨1325012, by rfl⟩ : syracuseStep 1766683 = 2650025) B2650025
theorem B2651561 : Blo 1766084 2651561 := bstep (se 2 (by rfl) ⟨994335, by rfl⟩ : syracuseStep 2651561 = 1988671) B1988671
theorem B1767871 : Blo 1766084 1767871 := bstep (se 1 (by rfl) ⟨1325903, by rfl⟩ : syracuseStep 1767871 = 2651807) B2651807
theorem B13425263 : Blo 1766084 13425263 := bstep (se 1 (by rfl) ⟨10068947, by rfl⟩ : syracuseStep 13425263 = 20137895) B20137895
theorem B5447675 : Blo 1766084 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B2982683 : Blo 1766084 2982683 := bstep (se 1 (by rfl) ⟨2237012, by rfl⟩ : syracuseStep 2982683 = 4474025) B4474025
theorem B14527133 : Blo 1766084 14527133 := bstep (se 3 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 14527133 = 5447675) B5447675
theorem B151178015 : Blo 1766084 151178015 := bstep (se 1 (by rfl) ⟨113383511, by rfl⟩ : syracuseStep 151178015 = 226767023) B226767023
theorem B10062751 : Blo 1766084 10062751 := bstep (se 1 (by rfl) ⟨7547063, by rfl⟩ : syracuseStep 10062751 = 15094127) B15094127
theorem B2649599 : Blo 1766084 2649599 := bstep (se 1 (by rfl) ⟨1987199, by rfl⟩ : syracuseStep 2649599 = 3974399) B3974399
theorem B3976703 : Blo 1766084 3976703 := bstep (se 1 (by rfl) ⟨2982527, by rfl⟩ : syracuseStep 3976703 = 5965055) B5965055
theorem B979611839 : Blo 1766084 979611839 := bstep (se 1 (by rfl) ⟨734708879, by rfl⟩ : syracuseStep 979611839 = 1469417759) B1469417759
theorem B8950175 : Blo 1766084 8950175 := bstep (se 1 (by rfl) ⟨6712631, by rfl⟩ : syracuseStep 8950175 = 13425263) B13425263
theorem B13416515 : Blo 1766084 13416515 := bstep (se 1 (by rfl) ⟨10062386, by rfl⟩ : syracuseStep 13416515 = 20124773) B20124773
theorem B6707407 : Blo 1766084 6707407 := bstep (se 1 (by rfl) ⟨5030555, by rfl⟩ : syracuseStep 6707407 = 10061111) B10061111
theorem B1767707 : Blo 1766084 1767707 := bstep (se 1 (by rfl) ⟨1325780, by rfl⟩ : syracuseStep 1767707 = 2651561) B2651561
theorem B653074559 : Blo 1766084 653074559 := bstep (se 1 (by rfl) ⟨489805919, by rfl⟩ : syracuseStep 653074559 = 979611839) B979611839
theorem B9684755 : Blo 1766084 9684755 := bstep (se 1 (by rfl) ⟨7263566, by rfl⟩ : syracuseStep 9684755 = 14527133) B14527133
theorem B5966783 : Blo 1766084 5966783 := bstep (se 1 (by rfl) ⟨4475087, by rfl⟩ : syracuseStep 5966783 = 8950175) B8950175
theorem B1766399 : Blo 1766084 1766399 := bstep (se 1 (by rfl) ⟨1324799, by rfl⟩ : syracuseStep 1766399 = 2649599) B2649599
theorem B2651135 : Blo 1766084 2651135 := bstep (se 1 (by rfl) ⟨1988351, by rfl⟩ : syracuseStep 2651135 = 3976703) B3976703
theorem B8943209 : Blo 1766084 8943209 := bstep (se 2 (by rfl) ⟨3353703, by rfl⟩ : syracuseStep 8943209 = 6707407) B6707407
theorem B1988455 : Blo 1766084 1988455 := bstep (se 1 (by rfl) ⟨1491341, by rfl⟩ : syracuseStep 1988455 = 2982683) B2982683
theorem B13417001 : Blo 1766084 13417001 := bstep (se 2 (by rfl) ⟨5031375, by rfl⟩ : syracuseStep 13417001 = 10062751) B10062751
theorem B8944343 : Blo 1766084 8944343 := bstep (se 1 (by rfl) ⟨6708257, by rfl⟩ : syracuseStep 8944343 = 13416515) B13416515
theorem B100785343 : Blo 1766084 100785343 := bstep (se 1 (by rfl) ⟨75589007, by rfl⟩ : syracuseStep 100785343 = 151178015) B151178015
theorem B6456503 : Blo 1766084 6456503 := bstep (se 1 (by rfl) ⟨4842377, by rfl⟩ : syracuseStep 6456503 = 9684755) B9684755
theorem B435383039 : Blo 1766084 435383039 := bstep (se 1 (by rfl) ⟨326537279, by rfl⟩ : syracuseStep 435383039 = 653074559) B653074559
theorem B3977855 : Blo 1766084 3977855 := bstep (se 1 (by rfl) ⟨2983391, by rfl⟩ : syracuseStep 3977855 = 5966783) B5966783
theorem B2651273 : Blo 1766084 2651273 := bstep (se 2 (by rfl) ⟨994227, by rfl⟩ : syracuseStep 2651273 = 1988455) B1988455
theorem B1767423 : Blo 1766084 1767423 := bstep (se 1 (by rfl) ⟨1325567, by rfl⟩ : syracuseStep 1767423 = 2651135) B2651135
theorem B5962139 : Blo 1766084 5962139 := bstep (se 1 (by rfl) ⟨4471604, by rfl⟩ : syracuseStep 5962139 = 8943209) B8943209
theorem B134380457 : Blo 1766084 134380457 := bstep (se 2 (by rfl) ⟨50392671, by rfl⟩ : syracuseStep 134380457 = 100785343) B100785343
theorem B8944667 : Blo 1766084 8944667 := bstep (se 1 (by rfl) ⟨6708500, by rfl⟩ : syracuseStep 8944667 = 13417001) B13417001
theorem B5962895 : Blo 1766084 5962895 := bstep (se 1 (by rfl) ⟨4472171, by rfl⟩ : syracuseStep 5962895 = 8944343) B8944343
theorem B3974759 : Blo 1766084 3974759 := bstep (se 1 (by rfl) ⟨2981069, by rfl⟩ : syracuseStep 3974759 = 5962139) B5962139
theorem B3975263 : Blo 1766084 3975263 := bstep (se 1 (by rfl) ⟨2981447, by rfl⟩ : syracuseStep 3975263 = 5962895) B5962895
theorem B4304335 : Blo 1766084 4304335 := bstep (se 1 (by rfl) ⟨3228251, by rfl⟩ : syracuseStep 4304335 = 6456503) B6456503
theorem B290255359 : Blo 1766084 290255359 := bstep (se 1 (by rfl) ⟨217691519, by rfl⟩ : syracuseStep 290255359 = 435383039) B435383039
theorem B2651903 : Blo 1766084 2651903 := bstep (se 1 (by rfl) ⟨1988927, by rfl⟩ : syracuseStep 2651903 = 3977855) B3977855
theorem B1767515 : Blo 1766084 1767515 := bstep (se 1 (by rfl) ⟨1325636, by rfl⟩ : syracuseStep 1767515 = 2651273) B2651273
theorem B89586971 : Blo 1766084 89586971 := bstep (se 1 (by rfl) ⟨67190228, by rfl⟩ : syracuseStep 89586971 = 134380457) B134380457
theorem B5963111 : Blo 1766084 5963111 := bstep (se 1 (by rfl) ⟨4472333, by rfl⟩ : syracuseStep 5963111 = 8944667) B8944667
theorem B387007145 : Blo 1766084 387007145 := bstep (se 2 (by rfl) ⟨145127679, by rfl⟩ : syracuseStep 387007145 = 290255359) B290255359
theorem B3975407 : Blo 1766084 3975407 := bstep (se 1 (by rfl) ⟨2981555, by rfl⟩ : syracuseStep 3975407 = 5963111) B5963111
theorem B2649839 : Blo 1766084 2649839 := bstep (se 1 (by rfl) ⟨1987379, by rfl⟩ : syracuseStep 2649839 = 3974759) B3974759
theorem B2650175 : Blo 1766084 2650175 := bstep (se 1 (by rfl) ⟨1987631, by rfl⟩ : syracuseStep 2650175 = 3975263) B3975263
theorem B5739113 : Blo 1766084 5739113 := bstep (se 2 (by rfl) ⟨2152167, by rfl⟩ : syracuseStep 5739113 = 4304335) B4304335
theorem B59724647 : Blo 1766084 59724647 := bstep (se 1 (by rfl) ⟨44793485, by rfl⟩ : syracuseStep 59724647 = 89586971) B89586971
theorem B1767935 : Blo 1766084 1767935 := bstep (se 1 (by rfl) ⟨1325951, by rfl⟩ : syracuseStep 1767935 = 2651903) B2651903
theorem B3826075 : Blo 1766084 3826075 := bstep (se 1 (by rfl) ⟨2869556, by rfl⟩ : syracuseStep 3826075 = 5739113) B5739113
theorem B39816431 : Blo 1766084 39816431 := bstep (se 1 (by rfl) ⟨29862323, by rfl⟩ : syracuseStep 39816431 = 59724647) B59724647
theorem B2650271 : Blo 1766084 2650271 := bstep (se 1 (by rfl) ⟨1987703, by rfl⟩ : syracuseStep 2650271 = 3975407) B3975407
theorem B1766559 : Blo 1766084 1766559 := bstep (se 1 (by rfl) ⟨1324919, by rfl⟩ : syracuseStep 1766559 = 2649839) B2649839
theorem B1766783 : Blo 1766084 1766783 := bstep (se 1 (by rfl) ⟨1325087, by rfl⟩ : syracuseStep 1766783 = 2650175) B2650175
theorem B258004763 : Blo 1766084 258004763 := bstep (se 1 (by rfl) ⟨193503572, by rfl⟩ : syracuseStep 258004763 = 387007145) B387007145
theorem B26544287 : Blo 1766084 26544287 := bstep (se 1 (by rfl) ⟨19908215, by rfl⟩ : syracuseStep 26544287 = 39816431) B39816431
theorem B172003175 : Blo 1766084 172003175 := bstep (se 1 (by rfl) ⟨129002381, by rfl⟩ : syracuseStep 172003175 = 258004763) B258004763
theorem B1766847 : Blo 1766084 1766847 := bstep (se 1 (by rfl) ⟨1325135, by rfl⟩ : syracuseStep 1766847 = 2650271) B2650271
theorem B5101433 : Blo 1766084 5101433 := bstep (se 2 (by rfl) ⟨1913037, by rfl⟩ : syracuseStep 5101433 = 3826075) B3826075
theorem B3400955 : Blo 1766084 3400955 := bstep (se 1 (by rfl) ⟨2550716, by rfl⟩ : syracuseStep 3400955 = 5101433) B5101433
theorem B17696191 : Blo 1766084 17696191 := bstep (se 1 (by rfl) ⟨13272143, by rfl⟩ : syracuseStep 17696191 = 26544287) B26544287
theorem B114668783 : Blo 1766084 114668783 := bstep (se 1 (by rfl) ⟨86001587, by rfl⟩ : syracuseStep 114668783 = 172003175) B172003175
theorem B23594921 : Blo 1766084 23594921 := bstep (se 2 (by rfl) ⟨8848095, by rfl⟩ : syracuseStep 23594921 = 17696191) B17696191
theorem B76445855 : Blo 1766084 76445855 := bstep (se 1 (by rfl) ⟨57334391, by rfl⟩ : syracuseStep 76445855 = 114668783) B114668783
theorem B2267303 : Blo 1766084 2267303 := bstep (se 1 (by rfl) ⟨1700477, by rfl⟩ : syracuseStep 2267303 = 3400955) B3400955
theorem B15729947 : Blo 1766084 15729947 := bstep (se 1 (by rfl) ⟨11797460, by rfl⟩ : syracuseStep 15729947 = 23594921) B23594921
theorem B50963903 : Blo 1766084 50963903 := bstep (se 1 (by rfl) ⟨38222927, by rfl⟩ : syracuseStep 50963903 = 76445855) B76445855
theorem B24184565 : Blo 1766084 24184565 := bstep (se 5 (by rfl) ⟨1133651, by rfl⟩ : syracuseStep 24184565 = 2267303) B2267303
theorem B10486631 : Blo 1766084 10486631 := bstep (se 1 (by rfl) ⟨7864973, by rfl⟩ : syracuseStep 10486631 = 15729947) B15729947
theorem B16123043 : Blo 1766084 16123043 := bstep (se 1 (by rfl) ⟨12092282, by rfl⟩ : syracuseStep 16123043 = 24184565) B24184565
theorem B33975935 : Blo 1766084 33975935 := bstep (se 1 (by rfl) ⟨25481951, by rfl⟩ : syracuseStep 33975935 = 50963903) B50963903
theorem B10748695 : Blo 1766084 10748695 := bstep (se 1 (by rfl) ⟨8061521, by rfl⟩ : syracuseStep 10748695 = 16123043) B16123043
theorem B27964349 : Blo 1766084 27964349 := bstep (se 3 (by rfl) ⟨5243315, by rfl⟩ : syracuseStep 27964349 = 10486631) B10486631
theorem B22650623 : Blo 1766084 22650623 := bstep (se 1 (by rfl) ⟨16987967, by rfl⟩ : syracuseStep 22650623 = 33975935) B33975935
theorem B15100415 : Blo 1766084 15100415 := bstep (se 1 (by rfl) ⟨11325311, by rfl⟩ : syracuseStep 15100415 = 22650623) B22650623
theorem B14331593 : Blo 1766084 14331593 := bstep (se 2 (by rfl) ⟨5374347, by rfl⟩ : syracuseStep 14331593 = 10748695) B10748695
theorem B18642899 : Blo 1766084 18642899 := bstep (se 1 (by rfl) ⟨13982174, by rfl⟩ : syracuseStep 18642899 = 27964349) B27964349
theorem B12428599 : Blo 1766084 12428599 := bstep (se 1 (by rfl) ⟨9321449, by rfl⟩ : syracuseStep 12428599 = 18642899) B18642899
theorem B9554395 : Blo 1766084 9554395 := bstep (se 1 (by rfl) ⟨7165796, by rfl⟩ : syracuseStep 9554395 = 14331593) B14331593
theorem B10066943 : Blo 1766084 10066943 := bstep (se 1 (by rfl) ⟨7550207, by rfl⟩ : syracuseStep 10066943 = 15100415) B15100415
theorem B12739193 : Blo 1766084 12739193 := bstep (se 2 (by rfl) ⟨4777197, by rfl⟩ : syracuseStep 12739193 = 9554395) B9554395
theorem B6711295 : Blo 1766084 6711295 := bstep (se 1 (by rfl) ⟨5033471, by rfl⟩ : syracuseStep 6711295 = 10066943) B10066943
theorem B16571465 : Blo 1766084 16571465 := bstep (se 2 (by rfl) ⟨6214299, by rfl⟩ : syracuseStep 16571465 = 12428599) B12428599
theorem B8948393 : Blo 1766084 8948393 := bstep (se 2 (by rfl) ⟨3355647, by rfl⟩ : syracuseStep 8948393 = 6711295) B6711295
theorem B11047643 : Blo 1766084 11047643 := bstep (se 1 (by rfl) ⟨8285732, by rfl⟩ : syracuseStep 11047643 = 16571465) B16571465
theorem B8492795 : Blo 1766084 8492795 := bstep (se 1 (by rfl) ⟨6369596, by rfl⟩ : syracuseStep 8492795 = 12739193) B12739193
theorem B7365095 : Blo 1766084 7365095 := bstep (se 1 (by rfl) ⟨5523821, by rfl⟩ : syracuseStep 7365095 = 11047643) B11047643
theorem B5661863 : Blo 1766084 5661863 := bstep (se 1 (by rfl) ⟨4246397, by rfl⟩ : syracuseStep 5661863 = 8492795) B8492795
theorem B5965595 : Blo 1766084 5965595 := bstep (se 1 (by rfl) ⟨4474196, by rfl⟩ : syracuseStep 5965595 = 8948393) B8948393
theorem B4910063 : Blo 1766084 4910063 := bstep (se 1 (by rfl) ⟨3682547, by rfl⟩ : syracuseStep 4910063 = 7365095) B7365095
theorem B3977063 : Blo 1766084 3977063 := bstep (se 1 (by rfl) ⟨2982797, by rfl⟩ : syracuseStep 3977063 = 5965595) B5965595
theorem B3774575 : Blo 1766084 3774575 := bstep (se 1 (by rfl) ⟨2830931, by rfl⟩ : syracuseStep 3774575 = 5661863) B5661863
theorem B2516383 : Blo 1766084 2516383 := bstep (se 1 (by rfl) ⟨1887287, by rfl⟩ : syracuseStep 2516383 = 3774575) B3774575
theorem B13093501 : Blo 1766084 13093501 := bstep (se 3 (by rfl) ⟨2455031, by rfl⟩ : syracuseStep 13093501 = 4910063) B4910063
theorem B2651375 : Blo 1766084 2651375 := bstep (se 1 (by rfl) ⟨1988531, by rfl⟩ : syracuseStep 2651375 = 3977063) B3977063
theorem B17458001 : Blo 1766084 17458001 := bstep (se 2 (by rfl) ⟨6546750, by rfl⟩ : syracuseStep 17458001 = 13093501) B13093501
theorem B3355177 : Blo 1766084 3355177 := bstep (se 2 (by rfl) ⟨1258191, by rfl⟩ : syracuseStep 3355177 = 2516383) B2516383
theorem B1767583 : Blo 1766084 1767583 := bstep (se 1 (by rfl) ⟨1325687, by rfl⟩ : syracuseStep 1767583 = 2651375) B2651375
theorem B4473569 : Blo 1766084 4473569 := bstep (se 2 (by rfl) ⟨1677588, by rfl⟩ : syracuseStep 4473569 = 3355177) B3355177
theorem B11638667 : Blo 1766084 11638667 := bstep (se 1 (by rfl) ⟨8729000, by rfl⟩ : syracuseStep 11638667 = 17458001) B17458001
theorem B2982379 : Blo 1766084 2982379 := bstep (se 1 (by rfl) ⟨2236784, by rfl⟩ : syracuseStep 2982379 = 4473569) B4473569
theorem B7759111 : Blo 1766084 7759111 := bstep (se 1 (by rfl) ⟨5819333, by rfl⟩ : syracuseStep 7759111 = 11638667) B11638667
theorem B3976505 : Blo 1766084 3976505 := bstep (se 2 (by rfl) ⟨1491189, by rfl⟩ : syracuseStep 3976505 = 2982379) B2982379
theorem B10345481 : Blo 1766084 10345481 := bstep (se 2 (by rfl) ⟨3879555, by rfl⟩ : syracuseStep 10345481 = 7759111) B7759111
theorem B2651003 : Blo 1766084 2651003 := bstep (se 1 (by rfl) ⟨1988252, by rfl⟩ : syracuseStep 2651003 = 3976505) B3976505
theorem B6896987 : Blo 1766084 6896987 := bstep (se 1 (by rfl) ⟨5172740, by rfl⟩ : syracuseStep 6896987 = 10345481) B10345481
theorem B4597991 : Blo 1766084 4597991 := bstep (se 1 (by rfl) ⟨3448493, by rfl⟩ : syracuseStep 4597991 = 6896987) B6896987
theorem B1767335 : Blo 1766084 1767335 := bstep (se 1 (by rfl) ⟨1325501, by rfl⟩ : syracuseStep 1767335 = 2651003) B2651003
theorem B3065327 : Blo 1766084 3065327 := bstep (se 1 (by rfl) ⟨2298995, by rfl⟩ : syracuseStep 3065327 = 4597991) B4597991
theorem B32696821 : Blo 1766084 32696821 := bstep (se 5 (by rfl) ⟨1532663, by rfl⟩ : syracuseStep 32696821 = 3065327) B3065327
theorem B43595761 : Blo 1766084 43595761 := bstep (se 2 (by rfl) ⟨16348410, by rfl⟩ : syracuseStep 43595761 = 32696821) B32696821
theorem B58127681 : Blo 1766084 58127681 := bstep (se 2 (by rfl) ⟨21797880, by rfl⟩ : syracuseStep 58127681 = 43595761) B43595761
theorem B38751787 : Blo 1766084 38751787 := bstep (se 1 (by rfl) ⟨29063840, by rfl⟩ : syracuseStep 38751787 = 58127681) B58127681
theorem B51669049 : Blo 1766084 51669049 := bstep (se 2 (by rfl) ⟨19375893, by rfl⟩ : syracuseStep 51669049 = 38751787) B38751787
theorem B68892065 : Blo 1766084 68892065 := bstep (se 2 (by rfl) ⟨25834524, by rfl⟩ : syracuseStep 68892065 = 51669049) B51669049
theorem B45928043 : Blo 1766084 45928043 := bstep (se 1 (by rfl) ⟨34446032, by rfl⟩ : syracuseStep 45928043 = 68892065) B68892065
theorem B30618695 : Blo 1766084 30618695 := bstep (se 1 (by rfl) ⟨22964021, by rfl⟩ : syracuseStep 30618695 = 45928043) B45928043
theorem B81649853 : Blo 1766084 81649853 := bstep (se 3 (by rfl) ⟨15309347, by rfl⟩ : syracuseStep 81649853 = 30618695) B30618695
theorem B54433235 : Blo 1766084 54433235 := bstep (se 1 (by rfl) ⟨40824926, by rfl⟩ : syracuseStep 54433235 = 81649853) B81649853
theorem B36288823 : Blo 1766084 36288823 := bstep (se 1 (by rfl) ⟨27216617, by rfl⟩ : syracuseStep 36288823 = 54433235) B54433235
theorem B48385097 : Blo 1766084 48385097 := bstep (se 2 (by rfl) ⟨18144411, by rfl⟩ : syracuseStep 48385097 = 36288823) B36288823
theorem B32256731 : Blo 1766084 32256731 := bstep (se 1 (by rfl) ⟨24192548, by rfl⟩ : syracuseStep 32256731 = 48385097) B48385097
theorem B21504487 : Blo 1766084 21504487 := bstep (se 1 (by rfl) ⟨16128365, by rfl⟩ : syracuseStep 21504487 = 32256731) B32256731
theorem B28672649 : Blo 1766084 28672649 := bstep (se 2 (by rfl) ⟨10752243, by rfl⟩ : syracuseStep 28672649 = 21504487) B21504487
theorem B19115099 : Blo 1766084 19115099 := bstep (se 1 (by rfl) ⟨14336324, by rfl⟩ : syracuseStep 19115099 = 28672649) B28672649
theorem B12743399 : Blo 1766084 12743399 := bstep (se 1 (by rfl) ⟨9557549, by rfl⟩ : syracuseStep 12743399 = 19115099) B19115099
theorem B8495599 : Blo 1766084 8495599 := bstep (se 1 (by rfl) ⟨6371699, by rfl⟩ : syracuseStep 8495599 = 12743399) B12743399
theorem B11327465 : Blo 1766084 11327465 := bstep (se 2 (by rfl) ⟨4247799, by rfl⟩ : syracuseStep 11327465 = 8495599) B8495599
theorem B7551643 : Blo 1766084 7551643 := bstep (se 1 (by rfl) ⟨5663732, by rfl⟩ : syracuseStep 7551643 = 11327465) B11327465
theorem B10068857 : Blo 1766084 10068857 := bstep (se 2 (by rfl) ⟨3775821, by rfl⟩ : syracuseStep 10068857 = 7551643) B7551643
theorem B6712571 : Blo 1766084 6712571 := bstep (se 1 (by rfl) ⟨5034428, by rfl⟩ : syracuseStep 6712571 = 10068857) B10068857
theorem B4475047 : Blo 1766084 4475047 := bstep (se 1 (by rfl) ⟨3356285, by rfl⟩ : syracuseStep 4475047 = 6712571) B6712571
theorem B5966729 : Blo 1766084 5966729 := bstep (se 2 (by rfl) ⟨2237523, by rfl⟩ : syracuseStep 5966729 = 4475047) B4475047
theorem B3977819 : Blo 1766084 3977819 := bstep (se 1 (by rfl) ⟨2983364, by rfl⟩ : syracuseStep 3977819 = 5966729) B5966729
theorem B2651879 : Blo 1766084 2651879 := bstep (se 1 (by rfl) ⟨1988909, by rfl⟩ : syracuseStep 2651879 = 3977819) B3977819
theorem B1767919 : Blo 1766084 1767919 := bstep (se 1 (by rfl) ⟨1325939, by rfl⟩ : syracuseStep 1767919 = 2651879) B2651879

theorem C0 (j : ℕ) (h1 : 441521 ≤ j) (h2 : j ≤ 442020) : Blo 1766084 (4 * j + 3) := by
  interval_cases j
  · exact B1766087
  · exact B1766091
  · exact B1766095
  · exact B1766099
  · exact B1766103
  · exact B1766107
  · exact B1766111
  · exact B1766115
  · exact B1766119
  · exact B1766123
  · exact B1766127
  · exact B1766131
  · exact B1766135
  · exact B1766139
  · exact B1766143
  · exact B1766147
  · exact B1766151
  · exact B1766155
  · exact B1766159
  · exact B1766163
  · exact B1766167
  · exact B1766171
  · exact B1766175
  · exact B1766179
  · exact B1766183
  · exact B1766187
  · exact B1766191
  · exact B1766195
  · exact B1766199
  · exact B1766203
  · exact B1766207
  · exact B1766211
  · exact B1766215
  · exact B1766219
  · exact B1766223
  · exact B1766227
  · exact B1766231
  · exact B1766235
  · exact B1766239
  · exact B1766243
  · exact B1766247
  · exact B1766251
  · exact B1766255
  · exact B1766259
  · exact B1766263
  · exact B1766267
  · exact B1766271
  · exact B1766275
  · exact B1766279
  · exact B1766283
  · exact B1766287
  · exact B1766291
  · exact B1766295
  · exact B1766299
  · exact B1766303
  · exact B1766307
  · exact B1766311
  · exact B1766315
  · exact B1766319
  · exact B1766323
  · exact B1766327
  · exact B1766331
  · exact B1766335
  · exact B1766339
  · exact B1766343
  · exact B1766347
  · exact B1766351
  · exact B1766355
  · exact B1766359
  · exact B1766363
  · exact B1766367
  · exact B1766371
  · exact B1766375
  · exact B1766379
  · exact B1766383
  · exact B1766387
  · exact B1766391
  · exact B1766395
  · exact B1766399
  · exact B1766403
  · exact B1766407
  · exact B1766411
  · exact B1766415
  · exact B1766419
  · exact B1766423
  · exact B1766427
  · exact B1766431
  · exact B1766435
  · exact B1766439
  · exact B1766443
  · exact B1766447
  · exact B1766451
  · exact B1766455
  · exact B1766459
  · exact B1766463
  · exact B1766467
  · exact B1766471
  · exact B1766475
  · exact B1766479
  · exact B1766483
  · exact B1766487
  · exact B1766491
  · exact B1766495
  · exact B1766499
  · exact B1766503
  · exact B1766507
  · exact B1766511
  · exact B1766515
  · exact B1766519
  · exact B1766523
  · exact B1766527
  · exact B1766531
  · exact B1766535
  · exact B1766539
  · exact B1766543
  · exact B1766547
  · exact B1766551
  · exact B1766555
  · exact B1766559
  · exact B1766563
  · exact B1766567
  · exact B1766571
  · exact B1766575
  · exact B1766579
  · exact B1766583
  · exact B1766587
  · exact B1766591
  · exact B1766595
  · exact B1766599
  · exact B1766603
  · exact B1766607
  · exact B1766611
  · exact B1766615
  · exact B1766619
  · exact B1766623
  · exact B1766627
  · exact B1766631
  · exact B1766635
  · exact B1766639
  · exact B1766643
  · exact B1766647
  · exact B1766651
  · exact B1766655
  · exact B1766659
  · exact B1766663
  · exact B1766667
  · exact B1766671
  · exact B1766675
  · exact B1766679
  · exact B1766683
  · exact B1766687
  · exact B1766691
  · exact B1766695
  · exact B1766699
  · exact B1766703
  · exact B1766707
  · exact B1766711
  · exact B1766715
  · exact B1766719
  · exact B1766723
  · exact B1766727
  · exact B1766731
  · exact B1766735
  · exact B1766739
  · exact B1766743
  · exact B1766747
  · exact B1766751
  · exact B1766755
  · exact B1766759
  · exact B1766763
  · exact B1766767
  · exact B1766771
  · exact B1766775
  · exact B1766779
  · exact B1766783
  · exact B1766787
  · exact B1766791
  · exact B1766795
  · exact B1766799
  · exact B1766803
  · exact B1766807
  · exact B1766811
  · exact B1766815
  · exact B1766819
  · exact B1766823
  · exact B1766827
  · exact B1766831
  · exact B1766835
  · exact B1766839
  · exact B1766843
  · exact B1766847
  · exact B1766851
  · exact B1766855
  · exact B1766859
  · exact B1766863
  · exact B1766867
  · exact B1766871
  · exact B1766875
  · exact B1766879
  · exact B1766883
  · exact B1766887
  · exact B1766891
  · exact B1766895
  · exact B1766899
  · exact B1766903
  · exact B1766907
  · exact B1766911
  · exact B1766915
  · exact B1766919
  · exact B1766923
  · exact B1766927
  · exact B1766931
  · exact B1766935
  · exact B1766939
  · exact B1766943
  · exact B1766947
  · exact B1766951
  · exact B1766955
  · exact B1766959
  · exact B1766963
  · exact B1766967
  · exact B1766971
  · exact B1766975
  · exact B1766979
  · exact B1766983
  · exact B1766987
  · exact B1766991
  · exact B1766995
  · exact B1766999
  · exact B1767003
  · exact B1767007
  · exact B1767011
  · exact B1767015
  · exact B1767019
  · exact B1767023
  · exact B1767027
  · exact B1767031
  · exact B1767035
  · exact B1767039
  · exact B1767043
  · exact B1767047
  · exact B1767051
  · exact B1767055
  · exact B1767059
  · exact B1767063
  · exact B1767067
  · exact B1767071
  · exact B1767075
  · exact B1767079
  · exact B1767083
  · exact B1767087
  · exact B1767091
  · exact B1767095
  · exact B1767099
  · exact B1767103
  · exact B1767107
  · exact B1767111
  · exact B1767115
  · exact B1767119
  · exact B1767123
  · exact B1767127
  · exact B1767131
  · exact B1767135
  · exact B1767139
  · exact B1767143
  · exact B1767147
  · exact B1767151
  · exact B1767155
  · exact B1767159
  · exact B1767163
  · exact B1767167
  · exact B1767171
  · exact B1767175
  · exact B1767179
  · exact B1767183
  · exact B1767187
  · exact B1767191
  · exact B1767195
  · exact B1767199
  · exact B1767203
  · exact B1767207
  · exact B1767211
  · exact B1767215
  · exact B1767219
  · exact B1767223
  · exact B1767227
  · exact B1767231
  · exact B1767235
  · exact B1767239
  · exact B1767243
  · exact B1767247
  · exact B1767251
  · exact B1767255
  · exact B1767259
  · exact B1767263
  · exact B1767267
  · exact B1767271
  · exact B1767275
  · exact B1767279
  · exact B1767283
  · exact B1767287
  · exact B1767291
  · exact B1767295
  · exact B1767299
  · exact B1767303
  · exact B1767307
  · exact B1767311
  · exact B1767315
  · exact B1767319
  · exact B1767323
  · exact B1767327
  · exact B1767331
  · exact B1767335
  · exact B1767339
  · exact B1767343
  · exact B1767347
  · exact B1767351
  · exact B1767355
  · exact B1767359
  · exact B1767363
  · exact B1767367
  · exact B1767371
  · exact B1767375
  · exact B1767379
  · exact B1767383
  · exact B1767387
  · exact B1767391
  · exact B1767395
  · exact B1767399
  · exact B1767403
  · exact B1767407
  · exact B1767411
  · exact B1767415
  · exact B1767419
  · exact B1767423
  · exact B1767427
  · exact B1767431
  · exact B1767435
  · exact B1767439
  · exact B1767443
  · exact B1767447
  · exact B1767451
  · exact B1767455
  · exact B1767459
  · exact B1767463
  · exact B1767467
  · exact B1767471
  · exact B1767475
  · exact B1767479
  · exact B1767483
  · exact B1767487
  · exact B1767491
  · exact B1767495
  · exact B1767499
  · exact B1767503
  · exact B1767507
  · exact B1767511
  · exact B1767515
  · exact B1767519
  · exact B1767523
  · exact B1767527
  · exact B1767531
  · exact B1767535
  · exact B1767539
  · exact B1767543
  · exact B1767547
  · exact B1767551
  · exact B1767555
  · exact B1767559
  · exact B1767563
  · exact B1767567
  · exact B1767571
  · exact B1767575
  · exact B1767579
  · exact B1767583
  · exact B1767587
  · exact B1767591
  · exact B1767595
  · exact B1767599
  · exact B1767603
  · exact B1767607
  · exact B1767611
  · exact B1767615
  · exact B1767619
  · exact B1767623
  · exact B1767627
  · exact B1767631
  · exact B1767635
  · exact B1767639
  · exact B1767643
  · exact B1767647
  · exact B1767651
  · exact B1767655
  · exact B1767659
  · exact B1767663
  · exact B1767667
  · exact B1767671
  · exact B1767675
  · exact B1767679
  · exact B1767683
  · exact B1767687
  · exact B1767691
  · exact B1767695
  · exact B1767699
  · exact B1767703
  · exact B1767707
  · exact B1767711
  · exact B1767715
  · exact B1767719
  · exact B1767723
  · exact B1767727
  · exact B1767731
  · exact B1767735
  · exact B1767739
  · exact B1767743
  · exact B1767747
  · exact B1767751
  · exact B1767755
  · exact B1767759
  · exact B1767763
  · exact B1767767
  · exact B1767771
  · exact B1767775
  · exact B1767779
  · exact B1767783
  · exact B1767787
  · exact B1767791
  · exact B1767795
  · exact B1767799
  · exact B1767803
  · exact B1767807
  · exact B1767811
  · exact B1767815
  · exact B1767819
  · exact B1767823
  · exact B1767827
  · exact B1767831
  · exact B1767835
  · exact B1767839
  · exact B1767843
  · exact B1767847
  · exact B1767851
  · exact B1767855
  · exact B1767859
  · exact B1767863
  · exact B1767867
  · exact B1767871
  · exact B1767875
  · exact B1767879
  · exact B1767883
  · exact B1767887
  · exact B1767891
  · exact B1767895
  · exact B1767899
  · exact B1767903
  · exact B1767907
  · exact B1767911
  · exact B1767915
  · exact B1767919
  · exact B1767923
  · exact B1767927
  · exact B1767931
  · exact B1767935
  · exact B1767939
  · exact B1767943
  · exact B1767947
  · exact B1767951
  · exact B1767955
  · exact B1767959
  · exact B1767963
  · exact B1767967
  · exact B1767971
  · exact B1767975
  · exact B1767979
  · exact B1767983
  · exact B1767987
  · exact B1767991
  · exact B1767995
  · exact B1767999
  · exact B1768003
  · exact B1768007
  · exact B1768011
  · exact B1768015
  · exact B1768019
  · exact B1768023
  · exact B1768027
  · exact B1768031
  · exact B1768035
  · exact B1768039
  · exact B1768043
  · exact B1768047
  · exact B1768051
  · exact B1768055
  · exact B1768059
  · exact B1768063
  · exact B1768067
  · exact B1768071
  · exact B1768075
  · exact B1768079
  · exact B1768083

theorem solution (m : ℕ) (hlo : 1766084 ≤ m) (hhi : m ≤ 1768084) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 441521 ≤ j := by omega
    have hj2 : j ≤ 442020 := by omega
    have hb : Blo 1766084 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
