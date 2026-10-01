-- Prove2me | solution 1 for syracuse_descends_range_1979435_1981435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:11.64853+00:00
-- url     : https://prove2.me/submissions/da460e39-01f5-40bb-b7ca-22ed47db604c

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

theorem B2226865 : Blo 1979435 2226865 := bbase (se 2 (by rfl) ⟨835074, by rfl⟩ : syracuseStep 2226865 = 1670149) (by norm_num)
theorem B2969153 : Blo 1979435 2969153 := bstep (se 2 (by rfl) ⟨1113432, by rfl⟩ : syracuseStep 2969153 = 2226865) B2226865
theorem B1979435 : Blo 1979435 1979435 := bstep (se 1 (by rfl) ⟨1484576, by rfl⟩ : syracuseStep 1979435 = 2969153) B2969153
theorem B20315285 : Blo 1979435 20315285 := bbase (se 6 (by rfl) ⟨476139, by rfl⟩ : syracuseStep 20315285 = 952279) (by norm_num)
theorem B13543523 : Blo 1979435 13543523 := bstep (se 1 (by rfl) ⟨10157642, by rfl⟩ : syracuseStep 13543523 = 20315285) B20315285
theorem B9029015 : Blo 1979435 9029015 := bstep (se 1 (by rfl) ⟨6771761, by rfl⟩ : syracuseStep 9029015 = 13543523) B13543523
theorem B6019343 : Blo 1979435 6019343 := bstep (se 1 (by rfl) ⟨4514507, by rfl⟩ : syracuseStep 6019343 = 9029015) B9029015
theorem B4012895 : Blo 1979435 4012895 := bstep (se 1 (by rfl) ⟨3009671, by rfl⟩ : syracuseStep 4012895 = 6019343) B6019343
theorem B2675263 : Blo 1979435 2675263 := bstep (se 1 (by rfl) ⟨2006447, by rfl⟩ : syracuseStep 2675263 = 4012895) B4012895
theorem B3567017 : Blo 1979435 3567017 := bstep (se 2 (by rfl) ⟨1337631, by rfl⟩ : syracuseStep 3567017 = 2675263) B2675263
theorem B2378011 : Blo 1979435 2378011 := bstep (se 1 (by rfl) ⟨1783508, by rfl⟩ : syracuseStep 2378011 = 3567017) B3567017
theorem B3170681 : Blo 1979435 3170681 := bstep (se 2 (by rfl) ⟨1189005, by rfl⟩ : syracuseStep 3170681 = 2378011) B2378011
theorem B2113787 : Blo 1979435 2113787 := bstep (se 1 (by rfl) ⟨1585340, by rfl⟩ : syracuseStep 2113787 = 3170681) B3170681
theorem B5636765 : Blo 1979435 5636765 := bstep (se 3 (by rfl) ⟨1056893, by rfl⟩ : syracuseStep 5636765 = 2113787) B2113787
theorem B3757843 : Blo 1979435 3757843 := bstep (se 1 (by rfl) ⟨2818382, by rfl⟩ : syracuseStep 3757843 = 5636765) B5636765
theorem B5010457 : Blo 1979435 5010457 := bstep (se 2 (by rfl) ⟨1878921, by rfl⟩ : syracuseStep 5010457 = 3757843) B3757843
theorem B6680609 : Blo 1979435 6680609 := bstep (se 2 (by rfl) ⟨2505228, by rfl⟩ : syracuseStep 6680609 = 5010457) B5010457
theorem B4453739 : Blo 1979435 4453739 := bstep (se 1 (by rfl) ⟨3340304, by rfl⟩ : syracuseStep 4453739 = 6680609) B6680609
theorem B2969159 : Blo 1979435 2969159 := bstep (se 1 (by rfl) ⟨2226869, by rfl⟩ : syracuseStep 2969159 = 4453739) B4453739
theorem B1979439 : Blo 1979435 1979439 := bstep (se 1 (by rfl) ⟨1484579, by rfl⟩ : syracuseStep 1979439 = 2969159) B2969159
theorem B2969165 : Blo 1979435 2969165 := bbase (se 3 (by rfl) ⟨556718, by rfl⟩ : syracuseStep 2969165 = 1113437) (by norm_num)
theorem B1979443 : Blo 1979435 1979443 := bstep (se 1 (by rfl) ⟨1484582, by rfl⟩ : syracuseStep 1979443 = 2969165) B2969165
theorem B4453757 : Blo 1979435 4453757 := bbase (se 3 (by rfl) ⟨835079, by rfl⟩ : syracuseStep 4453757 = 1670159) (by norm_num)
theorem B2969171 : Blo 1979435 2969171 := bstep (se 1 (by rfl) ⟨2226878, by rfl⟩ : syracuseStep 2969171 = 4453757) B4453757
theorem B1979447 : Blo 1979435 1979447 := bstep (se 1 (by rfl) ⟨1484585, by rfl⟩ : syracuseStep 1979447 = 2969171) B2969171
theorem B3340325 : Blo 1979435 3340325 := bbase (se 4 (by rfl) ⟨313155, by rfl⟩ : syracuseStep 3340325 = 626311) (by norm_num)
theorem B2226883 : Blo 1979435 2226883 := bstep (se 1 (by rfl) ⟨1670162, by rfl⟩ : syracuseStep 2226883 = 3340325) B3340325
theorem B2969177 : Blo 1979435 2969177 := bstep (se 2 (by rfl) ⟨1113441, by rfl⟩ : syracuseStep 2969177 = 2226883) B2226883
theorem B1979451 : Blo 1979435 1979451 := bstep (se 1 (by rfl) ⟨1484588, by rfl⟩ : syracuseStep 1979451 = 2969177) B2969177
theorem B2818405 : Blo 1979435 2818405 := bbase (se 4 (by rfl) ⟨264225, by rfl⟩ : syracuseStep 2818405 = 528451) (by norm_num)
theorem B15031493 : Blo 1979435 15031493 := bstep (se 4 (by rfl) ⟨1409202, by rfl⟩ : syracuseStep 15031493 = 2818405) B2818405
theorem B10020995 : Blo 1979435 10020995 := bstep (se 1 (by rfl) ⟨7515746, by rfl⟩ : syracuseStep 10020995 = 15031493) B15031493
theorem B6680663 : Blo 1979435 6680663 := bstep (se 1 (by rfl) ⟨5010497, by rfl⟩ : syracuseStep 6680663 = 10020995) B10020995
theorem B4453775 : Blo 1979435 4453775 := bstep (se 1 (by rfl) ⟨3340331, by rfl⟩ : syracuseStep 4453775 = 6680663) B6680663
theorem B2969183 : Blo 1979435 2969183 := bstep (se 1 (by rfl) ⟨2226887, by rfl⟩ : syracuseStep 2969183 = 4453775) B4453775
theorem B1979455 : Blo 1979435 1979455 := bstep (se 1 (by rfl) ⟨1484591, by rfl⟩ : syracuseStep 1979455 = 2969183) B2969183
theorem B2969189 : Blo 1979435 2969189 := bbase (se 4 (by rfl) ⟨278361, by rfl⟩ : syracuseStep 2969189 = 556723) (by norm_num)
theorem B1979459 : Blo 1979435 1979459 := bstep (se 1 (by rfl) ⟨1484594, by rfl⟩ : syracuseStep 1979459 = 2969189) B2969189
theorem B2113813 : Blo 1979435 2113813 := bbase (se 6 (by rfl) ⟨49542, by rfl⟩ : syracuseStep 2113813 = 99085) (by norm_num)
theorem B2818417 : Blo 1979435 2818417 := bstep (se 2 (by rfl) ⟨1056906, by rfl⟩ : syracuseStep 2818417 = 2113813) B2113813
theorem B3757889 : Blo 1979435 3757889 := bstep (se 2 (by rfl) ⟨1409208, by rfl⟩ : syracuseStep 3757889 = 2818417) B2818417
theorem B2505259 : Blo 1979435 2505259 := bstep (se 1 (by rfl) ⟨1878944, by rfl⟩ : syracuseStep 2505259 = 3757889) B3757889
theorem B3340345 : Blo 1979435 3340345 := bstep (se 2 (by rfl) ⟨1252629, by rfl⟩ : syracuseStep 3340345 = 2505259) B2505259
theorem B4453793 : Blo 1979435 4453793 := bstep (se 2 (by rfl) ⟨1670172, by rfl⟩ : syracuseStep 4453793 = 3340345) B3340345
theorem B2969195 : Blo 1979435 2969195 := bstep (se 1 (by rfl) ⟨2226896, by rfl⟩ : syracuseStep 2969195 = 4453793) B4453793
theorem B1979463 : Blo 1979435 1979463 := bstep (se 1 (by rfl) ⟨1484597, by rfl⟩ : syracuseStep 1979463 = 2969195) B2969195
theorem B2226901 : Blo 1979435 2226901 := bbase (se 7 (by rfl) ⟨26096, by rfl⟩ : syracuseStep 2226901 = 52193) (by norm_num)
theorem B2969201 : Blo 1979435 2969201 := bstep (se 2 (by rfl) ⟨1113450, by rfl⟩ : syracuseStep 2969201 = 2226901) B2226901
theorem B1979467 : Blo 1979435 1979467 := bstep (se 1 (by rfl) ⟨1484600, by rfl⟩ : syracuseStep 1979467 = 2969201) B2969201
theorem B2505269 : Blo 1979435 2505269 := bbase (se 5 (by rfl) ⟨117434, by rfl⟩ : syracuseStep 2505269 = 234869) (by norm_num)
theorem B6680717 : Blo 1979435 6680717 := bstep (se 3 (by rfl) ⟨1252634, by rfl⟩ : syracuseStep 6680717 = 2505269) B2505269
theorem B4453811 : Blo 1979435 4453811 := bstep (se 1 (by rfl) ⟨3340358, by rfl⟩ : syracuseStep 4453811 = 6680717) B6680717
theorem B2969207 : Blo 1979435 2969207 := bstep (se 1 (by rfl) ⟨2226905, by rfl⟩ : syracuseStep 2969207 = 4453811) B4453811
theorem B1979471 : Blo 1979435 1979471 := bstep (se 1 (by rfl) ⟨1484603, by rfl⟩ : syracuseStep 1979471 = 2969207) B2969207
theorem B2969213 : Blo 1979435 2969213 := bbase (se 3 (by rfl) ⟨556727, by rfl⟩ : syracuseStep 2969213 = 1113455) (by norm_num)
theorem B1979475 : Blo 1979435 1979475 := bstep (se 1 (by rfl) ⟨1484606, by rfl⟩ : syracuseStep 1979475 = 2969213) B2969213
theorem B4453829 : Blo 1979435 4453829 := bbase (se 4 (by rfl) ⟨417546, by rfl⟩ : syracuseStep 4453829 = 835093) (by norm_num)
theorem B2969219 : Blo 1979435 2969219 := bstep (se 1 (by rfl) ⟨2226914, by rfl⟩ : syracuseStep 2969219 = 4453829) B4453829
theorem B1979479 : Blo 1979435 1979479 := bstep (se 1 (by rfl) ⟨1484609, by rfl⟩ : syracuseStep 1979479 = 2969219) B2969219
theorem B2288101 : Blo 1979435 2288101 := bbase (se 4 (by rfl) ⟨214509, by rfl⟩ : syracuseStep 2288101 = 429019) (by norm_num)
theorem B3050801 : Blo 1979435 3050801 := bstep (se 2 (by rfl) ⟨1144050, by rfl⟩ : syracuseStep 3050801 = 2288101) B2288101
theorem B2033867 : Blo 1979435 2033867 := bstep (se 1 (by rfl) ⟨1525400, by rfl⟩ : syracuseStep 2033867 = 3050801) B3050801
theorem B5423645 : Blo 1979435 5423645 := bstep (se 3 (by rfl) ⟨1016933, by rfl⟩ : syracuseStep 5423645 = 2033867) B2033867
theorem B14463053 : Blo 1979435 14463053 := bstep (se 3 (by rfl) ⟨2711822, by rfl⟩ : syracuseStep 14463053 = 5423645) B5423645
theorem B9642035 : Blo 1979435 9642035 := bstep (se 1 (by rfl) ⟨7231526, by rfl⟩ : syracuseStep 9642035 = 14463053) B14463053
theorem B25712093 : Blo 1979435 25712093 := bstep (se 3 (by rfl) ⟨4821017, by rfl⟩ : syracuseStep 25712093 = 9642035) B9642035
theorem B17141395 : Blo 1979435 17141395 := bstep (se 1 (by rfl) ⟨12856046, by rfl⟩ : syracuseStep 17141395 = 25712093) B25712093
theorem B22855193 : Blo 1979435 22855193 := bstep (se 2 (by rfl) ⟨8570697, by rfl⟩ : syracuseStep 22855193 = 17141395) B17141395
theorem B15236795 : Blo 1979435 15236795 := bstep (se 1 (by rfl) ⟨11427596, by rfl⟩ : syracuseStep 15236795 = 22855193) B22855193
theorem B40631453 : Blo 1979435 40631453 := bstep (se 3 (by rfl) ⟨7618397, by rfl⟩ : syracuseStep 40631453 = 15236795) B15236795
theorem B27087635 : Blo 1979435 27087635 := bstep (se 1 (by rfl) ⟨20315726, by rfl⟩ : syracuseStep 27087635 = 40631453) B40631453
theorem B72233693 : Blo 1979435 72233693 := bstep (se 3 (by rfl) ⟨13543817, by rfl⟩ : syracuseStep 72233693 = 27087635) B27087635
theorem B48155795 : Blo 1979435 48155795 := bstep (se 1 (by rfl) ⟨36116846, by rfl⟩ : syracuseStep 48155795 = 72233693) B72233693
theorem B32103863 : Blo 1979435 32103863 := bstep (se 1 (by rfl) ⟨24077897, by rfl⟩ : syracuseStep 32103863 = 48155795) B48155795
theorem B21402575 : Blo 1979435 21402575 := bstep (se 1 (by rfl) ⟨16051931, by rfl⟩ : syracuseStep 21402575 = 32103863) B32103863
theorem B14268383 : Blo 1979435 14268383 := bstep (se 1 (by rfl) ⟨10701287, by rfl⟩ : syracuseStep 14268383 = 21402575) B21402575
theorem B9512255 : Blo 1979435 9512255 := bstep (se 1 (by rfl) ⟨7134191, by rfl⟩ : syracuseStep 9512255 = 14268383) B14268383
theorem B6341503 : Blo 1979435 6341503 := bstep (se 1 (by rfl) ⟨4756127, by rfl⟩ : syracuseStep 6341503 = 9512255) B9512255
theorem B8455337 : Blo 1979435 8455337 := bstep (se 2 (by rfl) ⟨3170751, by rfl⟩ : syracuseStep 8455337 = 6341503) B6341503
theorem B5636891 : Blo 1979435 5636891 := bstep (se 1 (by rfl) ⟨4227668, by rfl⟩ : syracuseStep 5636891 = 8455337) B8455337
theorem B3757927 : Blo 1979435 3757927 := bstep (se 1 (by rfl) ⟨2818445, by rfl⟩ : syracuseStep 3757927 = 5636891) B5636891
theorem B5010569 : Blo 1979435 5010569 := bstep (se 2 (by rfl) ⟨1878963, by rfl⟩ : syracuseStep 5010569 = 3757927) B3757927
theorem B3340379 : Blo 1979435 3340379 := bstep (se 1 (by rfl) ⟨2505284, by rfl⟩ : syracuseStep 3340379 = 5010569) B5010569
theorem B2226919 : Blo 1979435 2226919 := bstep (se 1 (by rfl) ⟨1670189, by rfl⟩ : syracuseStep 2226919 = 3340379) B3340379
theorem B2969225 : Blo 1979435 2969225 := bstep (se 2 (by rfl) ⟨1113459, by rfl⟩ : syracuseStep 2969225 = 2226919) B2226919
theorem B1979483 : Blo 1979435 1979483 := bstep (se 1 (by rfl) ⟨1484612, by rfl⟩ : syracuseStep 1979483 = 2969225) B2969225
theorem B10021157 : Blo 1979435 10021157 := bbase (se 4 (by rfl) ⟨939483, by rfl⟩ : syracuseStep 10021157 = 1878967) (by norm_num)
theorem B6680771 : Blo 1979435 6680771 := bstep (se 1 (by rfl) ⟨5010578, by rfl⟩ : syracuseStep 6680771 = 10021157) B10021157
theorem B4453847 : Blo 1979435 4453847 := bstep (se 1 (by rfl) ⟨3340385, by rfl⟩ : syracuseStep 4453847 = 6680771) B6680771
theorem B2969231 : Blo 1979435 2969231 := bstep (se 1 (by rfl) ⟨2226923, by rfl⟩ : syracuseStep 2969231 = 4453847) B4453847
theorem B1979487 : Blo 1979435 1979487 := bstep (se 1 (by rfl) ⟨1484615, by rfl⟩ : syracuseStep 1979487 = 2969231) B2969231
theorem B2969237 : Blo 1979435 2969237 := bbase (se 6 (by rfl) ⟨69591, by rfl⟩ : syracuseStep 2969237 = 139183) (by norm_num)
theorem B1979491 : Blo 1979435 1979491 := bstep (se 1 (by rfl) ⟨1484618, by rfl⟩ : syracuseStep 1979491 = 2969237) B2969237
theorem B2856917 : Blo 1979435 2856917 := bbase (se 7 (by rfl) ⟨33479, by rfl⟩ : syracuseStep 2856917 = 66959) (by norm_num)
theorem B7618445 : Blo 1979435 7618445 := bstep (se 3 (by rfl) ⟨1428458, by rfl⟩ : syracuseStep 7618445 = 2856917) B2856917
theorem B5078963 : Blo 1979435 5078963 := bstep (se 1 (by rfl) ⟨3809222, by rfl⟩ : syracuseStep 5078963 = 7618445) B7618445
theorem B3385975 : Blo 1979435 3385975 := bstep (se 1 (by rfl) ⟨2539481, by rfl⟩ : syracuseStep 3385975 = 5078963) B5078963
theorem B4514633 : Blo 1979435 4514633 := bstep (se 2 (by rfl) ⟨1692987, by rfl⟩ : syracuseStep 4514633 = 3385975) B3385975
theorem B3009755 : Blo 1979435 3009755 := bstep (se 1 (by rfl) ⟨2257316, by rfl⟩ : syracuseStep 3009755 = 4514633) B4514633
theorem B8026013 : Blo 1979435 8026013 := bstep (se 3 (by rfl) ⟨1504877, by rfl⟩ : syracuseStep 8026013 = 3009755) B3009755
theorem B21402701 : Blo 1979435 21402701 := bstep (se 3 (by rfl) ⟨4013006, by rfl⟩ : syracuseStep 21402701 = 8026013) B8026013
theorem B14268467 : Blo 1979435 14268467 := bstep (se 1 (by rfl) ⟨10701350, by rfl⟩ : syracuseStep 14268467 = 21402701) B21402701
theorem B9512311 : Blo 1979435 9512311 := bstep (se 1 (by rfl) ⟨7134233, by rfl⟩ : syracuseStep 9512311 = 14268467) B14268467
theorem B12683081 : Blo 1979435 12683081 := bstep (se 2 (by rfl) ⟨4756155, by rfl⟩ : syracuseStep 12683081 = 9512311) B9512311
theorem B8455387 : Blo 1979435 8455387 := bstep (se 1 (by rfl) ⟨6341540, by rfl⟩ : syracuseStep 8455387 = 12683081) B12683081
theorem B11273849 : Blo 1979435 11273849 := bstep (se 2 (by rfl) ⟨4227693, by rfl⟩ : syracuseStep 11273849 = 8455387) B8455387
theorem B7515899 : Blo 1979435 7515899 := bstep (se 1 (by rfl) ⟨5636924, by rfl⟩ : syracuseStep 7515899 = 11273849) B11273849
theorem B5010599 : Blo 1979435 5010599 := bstep (se 1 (by rfl) ⟨3757949, by rfl⟩ : syracuseStep 5010599 = 7515899) B7515899
theorem B3340399 : Blo 1979435 3340399 := bstep (se 1 (by rfl) ⟨2505299, by rfl⟩ : syracuseStep 3340399 = 5010599) B5010599
theorem B4453865 : Blo 1979435 4453865 := bstep (se 2 (by rfl) ⟨1670199, by rfl⟩ : syracuseStep 4453865 = 3340399) B3340399
theorem B2969243 : Blo 1979435 2969243 := bstep (se 1 (by rfl) ⟨2226932, by rfl⟩ : syracuseStep 2969243 = 4453865) B4453865
theorem B1979495 : Blo 1979435 1979495 := bstep (se 1 (by rfl) ⟨1484621, by rfl⟩ : syracuseStep 1979495 = 2969243) B2969243
theorem B2226937 : Blo 1979435 2226937 := bbase (se 2 (by rfl) ⟨835101, by rfl⟩ : syracuseStep 2226937 = 1670203) (by norm_num)
theorem B2969249 : Blo 1979435 2969249 := bstep (se 2 (by rfl) ⟨1113468, by rfl⟩ : syracuseStep 2969249 = 2226937) B2226937
theorem B1979499 : Blo 1979435 1979499 := bstep (se 1 (by rfl) ⟨1484624, by rfl⟩ : syracuseStep 1979499 = 2969249) B2969249
theorem B5423701 : Blo 1979435 5423701 := bbase (se 8 (by rfl) ⟨31779, by rfl⟩ : syracuseStep 5423701 = 63559) (by norm_num)
theorem B7231601 : Blo 1979435 7231601 := bstep (se 2 (by rfl) ⟨2711850, by rfl⟩ : syracuseStep 7231601 = 5423701) B5423701
theorem B4821067 : Blo 1979435 4821067 := bstep (se 1 (by rfl) ⟨3615800, by rfl⟩ : syracuseStep 4821067 = 7231601) B7231601
theorem B6428089 : Blo 1979435 6428089 := bstep (se 2 (by rfl) ⟨2410533, by rfl⟩ : syracuseStep 6428089 = 4821067) B4821067
theorem B8570785 : Blo 1979435 8570785 := bstep (se 2 (by rfl) ⟨3214044, by rfl⟩ : syracuseStep 8570785 = 6428089) B6428089
theorem B11427713 : Blo 1979435 11427713 := bstep (se 2 (by rfl) ⟨4285392, by rfl⟩ : syracuseStep 11427713 = 8570785) B8570785
theorem B7618475 : Blo 1979435 7618475 := bstep (se 1 (by rfl) ⟨5713856, by rfl⟩ : syracuseStep 7618475 = 11427713) B11427713
theorem B20315933 : Blo 1979435 20315933 := bstep (se 3 (by rfl) ⟨3809237, by rfl⟩ : syracuseStep 20315933 = 7618475) B7618475
theorem B13543955 : Blo 1979435 13543955 := bstep (se 1 (by rfl) ⟨10157966, by rfl⟩ : syracuseStep 13543955 = 20315933) B20315933
theorem B9029303 : Blo 1979435 9029303 := bstep (se 1 (by rfl) ⟨6771977, by rfl⟩ : syracuseStep 9029303 = 13543955) B13543955
theorem B6019535 : Blo 1979435 6019535 := bstep (se 1 (by rfl) ⟨4514651, by rfl⟩ : syracuseStep 6019535 = 9029303) B9029303
theorem B16052093 : Blo 1979435 16052093 := bstep (se 3 (by rfl) ⟨3009767, by rfl⟩ : syracuseStep 16052093 = 6019535) B6019535
theorem B10701395 : Blo 1979435 10701395 := bstep (se 1 (by rfl) ⟨8026046, by rfl⟩ : syracuseStep 10701395 = 16052093) B16052093
theorem B7134263 : Blo 1979435 7134263 := bstep (se 1 (by rfl) ⟨5350697, by rfl⟩ : syracuseStep 7134263 = 10701395) B10701395
theorem B4756175 : Blo 1979435 4756175 := bstep (se 1 (by rfl) ⟨3567131, by rfl⟩ : syracuseStep 4756175 = 7134263) B7134263
theorem B3170783 : Blo 1979435 3170783 := bstep (se 1 (by rfl) ⟨2378087, by rfl⟩ : syracuseStep 3170783 = 4756175) B4756175
theorem B8455421 : Blo 1979435 8455421 := bstep (se 3 (by rfl) ⟨1585391, by rfl⟩ : syracuseStep 8455421 = 3170783) B3170783
theorem B5636947 : Blo 1979435 5636947 := bstep (se 1 (by rfl) ⟨4227710, by rfl⟩ : syracuseStep 5636947 = 8455421) B8455421
theorem B7515929 : Blo 1979435 7515929 := bstep (se 2 (by rfl) ⟨2818473, by rfl⟩ : syracuseStep 7515929 = 5636947) B5636947
theorem B5010619 : Blo 1979435 5010619 := bstep (se 1 (by rfl) ⟨3757964, by rfl⟩ : syracuseStep 5010619 = 7515929) B7515929
theorem B6680825 : Blo 1979435 6680825 := bstep (se 2 (by rfl) ⟨2505309, by rfl⟩ : syracuseStep 6680825 = 5010619) B5010619
theorem B4453883 : Blo 1979435 4453883 := bstep (se 1 (by rfl) ⟨3340412, by rfl⟩ : syracuseStep 4453883 = 6680825) B6680825
theorem B2969255 : Blo 1979435 2969255 := bstep (se 1 (by rfl) ⟨2226941, by rfl⟩ : syracuseStep 2969255 = 4453883) B4453883
theorem B1979503 : Blo 1979435 1979503 := bstep (se 1 (by rfl) ⟨1484627, by rfl⟩ : syracuseStep 1979503 = 2969255) B2969255
theorem B2969261 : Blo 1979435 2969261 := bbase (se 3 (by rfl) ⟨556736, by rfl⟩ : syracuseStep 2969261 = 1113473) (by norm_num)
theorem B1979507 : Blo 1979435 1979507 := bstep (se 1 (by rfl) ⟨1484630, by rfl⟩ : syracuseStep 1979507 = 2969261) B2969261
theorem B4453901 : Blo 1979435 4453901 := bbase (se 3 (by rfl) ⟨835106, by rfl⟩ : syracuseStep 4453901 = 1670213) (by norm_num)
theorem B2969267 : Blo 1979435 2969267 := bstep (se 1 (by rfl) ⟨2226950, by rfl⟩ : syracuseStep 2969267 = 4453901) B4453901
theorem B1979511 : Blo 1979435 1979511 := bstep (se 1 (by rfl) ⟨1484633, by rfl⟩ : syracuseStep 1979511 = 2969267) B2969267
theorem B2505325 : Blo 1979435 2505325 := bbase (se 3 (by rfl) ⟨469748, by rfl⟩ : syracuseStep 2505325 = 939497) (by norm_num)
theorem B3340433 : Blo 1979435 3340433 := bstep (se 2 (by rfl) ⟨1252662, by rfl⟩ : syracuseStep 3340433 = 2505325) B2505325
theorem B2226955 : Blo 1979435 2226955 := bstep (se 1 (by rfl) ⟨1670216, by rfl⟩ : syracuseStep 2226955 = 3340433) B3340433
theorem B2969273 : Blo 1979435 2969273 := bstep (se 2 (by rfl) ⟨1113477, by rfl⟩ : syracuseStep 2969273 = 2226955) B2226955
theorem B1979515 : Blo 1979435 1979515 := bstep (se 1 (by rfl) ⟨1484636, by rfl⟩ : syracuseStep 1979515 = 2969273) B2969273
theorem B12856277 : Blo 1979435 12856277 := bbase (se 7 (by rfl) ⟨150659, by rfl⟩ : syracuseStep 12856277 = 301319) (by norm_num)
theorem B34283405 : Blo 1979435 34283405 := bstep (se 3 (by rfl) ⟨6428138, by rfl⟩ : syracuseStep 34283405 = 12856277) B12856277
theorem B22855603 : Blo 1979435 22855603 := bstep (se 1 (by rfl) ⟨17141702, by rfl⟩ : syracuseStep 22855603 = 34283405) B34283405
theorem B30474137 : Blo 1979435 30474137 := bstep (se 2 (by rfl) ⟨11427801, by rfl⟩ : syracuseStep 30474137 = 22855603) B22855603
theorem B20316091 : Blo 1979435 20316091 := bstep (se 1 (by rfl) ⟨15237068, by rfl⟩ : syracuseStep 20316091 = 30474137) B30474137
theorem B27088121 : Blo 1979435 27088121 := bstep (se 2 (by rfl) ⟨10158045, by rfl⟩ : syracuseStep 27088121 = 20316091) B20316091
theorem B18058747 : Blo 1979435 18058747 := bstep (se 1 (by rfl) ⟨13544060, by rfl⟩ : syracuseStep 18058747 = 27088121) B27088121
theorem B24078329 : Blo 1979435 24078329 := bstep (se 2 (by rfl) ⟨9029373, by rfl⟩ : syracuseStep 24078329 = 18058747) B18058747
theorem B16052219 : Blo 1979435 16052219 := bstep (se 1 (by rfl) ⟨12039164, by rfl⟩ : syracuseStep 16052219 = 24078329) B24078329
theorem B10701479 : Blo 1979435 10701479 := bstep (se 1 (by rfl) ⟨8026109, by rfl⟩ : syracuseStep 10701479 = 16052219) B16052219
theorem B7134319 : Blo 1979435 7134319 := bstep (se 1 (by rfl) ⟨5350739, by rfl⟩ : syracuseStep 7134319 = 10701479) B10701479
theorem B9512425 : Blo 1979435 9512425 := bstep (se 2 (by rfl) ⟨3567159, by rfl⟩ : syracuseStep 9512425 = 7134319) B7134319
theorem B12683233 : Blo 1979435 12683233 := bstep (se 2 (by rfl) ⟨4756212, by rfl⟩ : syracuseStep 12683233 = 9512425) B9512425
theorem B16910977 : Blo 1979435 16910977 := bstep (se 2 (by rfl) ⟨6341616, by rfl⟩ : syracuseStep 16910977 = 12683233) B12683233
theorem B22547969 : Blo 1979435 22547969 := bstep (se 2 (by rfl) ⟨8455488, by rfl⟩ : syracuseStep 22547969 = 16910977) B16910977
theorem B15031979 : Blo 1979435 15031979 := bstep (se 1 (by rfl) ⟨11273984, by rfl⟩ : syracuseStep 15031979 = 22547969) B22547969
theorem B10021319 : Blo 1979435 10021319 := bstep (se 1 (by rfl) ⟨7515989, by rfl⟩ : syracuseStep 10021319 = 15031979) B15031979
theorem B6680879 : Blo 1979435 6680879 := bstep (se 1 (by rfl) ⟨5010659, by rfl⟩ : syracuseStep 6680879 = 10021319) B10021319
theorem B4453919 : Blo 1979435 4453919 := bstep (se 1 (by rfl) ⟨3340439, by rfl⟩ : syracuseStep 4453919 = 6680879) B6680879
theorem B2969279 : Blo 1979435 2969279 := bstep (se 1 (by rfl) ⟨2226959, by rfl⟩ : syracuseStep 2969279 = 4453919) B4453919
theorem B1979519 : Blo 1979435 1979519 := bstep (se 1 (by rfl) ⟨1484639, by rfl⟩ : syracuseStep 1979519 = 2969279) B2969279
theorem B2969285 : Blo 1979435 2969285 := bbase (se 4 (by rfl) ⟨278370, by rfl⟩ : syracuseStep 2969285 = 556741) (by norm_num)
theorem B1979523 : Blo 1979435 1979523 := bstep (se 1 (by rfl) ⟨1484642, by rfl⟩ : syracuseStep 1979523 = 2969285) B2969285
theorem B3340453 : Blo 1979435 3340453 := bbase (se 4 (by rfl) ⟨313167, by rfl⟩ : syracuseStep 3340453 = 626335) (by norm_num)
theorem B4453937 : Blo 1979435 4453937 := bstep (se 2 (by rfl) ⟨1670226, by rfl⟩ : syracuseStep 4453937 = 3340453) B3340453
theorem B2969291 : Blo 1979435 2969291 := bstep (se 1 (by rfl) ⟨2226968, by rfl⟩ : syracuseStep 2969291 = 4453937) B4453937
theorem B1979527 : Blo 1979435 1979527 := bstep (se 1 (by rfl) ⟨1484645, by rfl⟩ : syracuseStep 1979527 = 2969291) B2969291
theorem B2226973 : Blo 1979435 2226973 := bbase (se 3 (by rfl) ⟨417557, by rfl⟩ : syracuseStep 2226973 = 835115) (by norm_num)
theorem B2969297 : Blo 1979435 2969297 := bstep (se 2 (by rfl) ⟨1113486, by rfl⟩ : syracuseStep 2969297 = 2226973) B2226973
theorem B1979531 : Blo 1979435 1979531 := bstep (se 1 (by rfl) ⟨1484648, by rfl⟩ : syracuseStep 1979531 = 2969297) B2969297
theorem B6680933 : Blo 1979435 6680933 := bbase (se 4 (by rfl) ⟨626337, by rfl⟩ : syracuseStep 6680933 = 1252675) (by norm_num)
theorem B4453955 : Blo 1979435 4453955 := bstep (se 1 (by rfl) ⟨3340466, by rfl⟩ : syracuseStep 4453955 = 6680933) B6680933
theorem B2969303 : Blo 1979435 2969303 := bstep (se 1 (by rfl) ⟨2226977, by rfl⟩ : syracuseStep 2969303 = 4453955) B4453955
theorem B1979535 : Blo 1979435 1979535 := bstep (se 1 (by rfl) ⟨1484651, by rfl⟩ : syracuseStep 1979535 = 2969303) B2969303
theorem B2969309 : Blo 1979435 2969309 := bbase (se 3 (by rfl) ⟨556745, by rfl⟩ : syracuseStep 2969309 = 1113491) (by norm_num)
theorem B1979539 : Blo 1979435 1979539 := bstep (se 1 (by rfl) ⟨1484654, by rfl⟩ : syracuseStep 1979539 = 2969309) B2969309
theorem B4453973 : Blo 1979435 4453973 := bbase (se 8 (by rfl) ⟨26097, by rfl⟩ : syracuseStep 4453973 = 52195) (by norm_num)
theorem B2969315 : Blo 1979435 2969315 := bstep (se 1 (by rfl) ⟨2226986, by rfl⟩ : syracuseStep 2969315 = 4453973) B4453973
theorem B1979543 : Blo 1979435 1979543 := bstep (se 1 (by rfl) ⟨1484657, by rfl⟩ : syracuseStep 1979543 = 2969315) B2969315
theorem B4227805 : Blo 1979435 4227805 := bbase (se 3 (by rfl) ⟨792713, by rfl⟩ : syracuseStep 4227805 = 1585427) (by norm_num)
theorem B5637073 : Blo 1979435 5637073 := bstep (se 2 (by rfl) ⟨2113902, by rfl⟩ : syracuseStep 5637073 = 4227805) B4227805
theorem B7516097 : Blo 1979435 7516097 := bstep (se 2 (by rfl) ⟨2818536, by rfl⟩ : syracuseStep 7516097 = 5637073) B5637073
theorem B5010731 : Blo 1979435 5010731 := bstep (se 1 (by rfl) ⟨3758048, by rfl⟩ : syracuseStep 5010731 = 7516097) B7516097
theorem B3340487 : Blo 1979435 3340487 := bstep (se 1 (by rfl) ⟨2505365, by rfl⟩ : syracuseStep 3340487 = 5010731) B5010731
theorem B2226991 : Blo 1979435 2226991 := bstep (se 1 (by rfl) ⟨1670243, by rfl⟩ : syracuseStep 2226991 = 3340487) B3340487
theorem B2969321 : Blo 1979435 2969321 := bstep (se 2 (by rfl) ⟨1113495, by rfl⟩ : syracuseStep 2969321 = 2226991) B2226991
theorem B1979547 : Blo 1979435 1979547 := bstep (se 1 (by rfl) ⟨1484660, by rfl⟩ : syracuseStep 1979547 = 2969321) B2969321
theorem B2675413 : Blo 1979435 2675413 := bbase (se 7 (by rfl) ⟨31352, by rfl⟩ : syracuseStep 2675413 = 62705) (by norm_num)
theorem B14268869 : Blo 1979435 14268869 := bstep (se 4 (by rfl) ⟨1337706, by rfl⟩ : syracuseStep 14268869 = 2675413) B2675413
theorem B9512579 : Blo 1979435 9512579 := bstep (se 1 (by rfl) ⟨7134434, by rfl⟩ : syracuseStep 9512579 = 14268869) B14268869
theorem B25366877 : Blo 1979435 25366877 := bstep (se 3 (by rfl) ⟨4756289, by rfl⟩ : syracuseStep 25366877 = 9512579) B9512579
theorem B16911251 : Blo 1979435 16911251 := bstep (se 1 (by rfl) ⟨12683438, by rfl⟩ : syracuseStep 16911251 = 25366877) B25366877
theorem B11274167 : Blo 1979435 11274167 := bstep (se 1 (by rfl) ⟨8455625, by rfl⟩ : syracuseStep 11274167 = 16911251) B16911251
theorem B7516111 : Blo 1979435 7516111 := bstep (se 1 (by rfl) ⟨5637083, by rfl⟩ : syracuseStep 7516111 = 11274167) B11274167
theorem B10021481 : Blo 1979435 10021481 := bstep (se 2 (by rfl) ⟨3758055, by rfl⟩ : syracuseStep 10021481 = 7516111) B7516111
theorem B6680987 : Blo 1979435 6680987 := bstep (se 1 (by rfl) ⟨5010740, by rfl⟩ : syracuseStep 6680987 = 10021481) B10021481
theorem B4453991 : Blo 1979435 4453991 := bstep (se 1 (by rfl) ⟨3340493, by rfl⟩ : syracuseStep 4453991 = 6680987) B6680987
theorem B2969327 : Blo 1979435 2969327 := bstep (se 1 (by rfl) ⟨2226995, by rfl⟩ : syracuseStep 2969327 = 4453991) B4453991
theorem B1979551 : Blo 1979435 1979551 := bstep (se 1 (by rfl) ⟨1484663, by rfl⟩ : syracuseStep 1979551 = 2969327) B2969327
theorem B2969333 : Blo 1979435 2969333 := bbase (se 5 (by rfl) ⟨139187, by rfl⟩ : syracuseStep 2969333 = 278375) (by norm_num)
theorem B1979555 : Blo 1979435 1979555 := bstep (se 1 (by rfl) ⟨1484666, by rfl⟩ : syracuseStep 1979555 = 2969333) B2969333
theorem B2006569 : Blo 1979435 2006569 := bbase (se 2 (by rfl) ⟨752463, by rfl⟩ : syracuseStep 2006569 = 1504927) (by norm_num)
theorem B2675425 : Blo 1979435 2675425 := bstep (se 2 (by rfl) ⟨1003284, by rfl⟩ : syracuseStep 2675425 = 2006569) B2006569
theorem B3567233 : Blo 1979435 3567233 := bstep (se 2 (by rfl) ⟨1337712, by rfl⟩ : syracuseStep 3567233 = 2675425) B2675425
theorem B2378155 : Blo 1979435 2378155 := bstep (se 1 (by rfl) ⟨1783616, by rfl⟩ : syracuseStep 2378155 = 3567233) B3567233
theorem B3170873 : Blo 1979435 3170873 := bstep (se 2 (by rfl) ⟨1189077, by rfl⟩ : syracuseStep 3170873 = 2378155) B2378155
theorem B8455661 : Blo 1979435 8455661 := bstep (se 3 (by rfl) ⟨1585436, by rfl⟩ : syracuseStep 8455661 = 3170873) B3170873
theorem B5637107 : Blo 1979435 5637107 := bstep (se 1 (by rfl) ⟨4227830, by rfl⟩ : syracuseStep 5637107 = 8455661) B8455661
theorem B3758071 : Blo 1979435 3758071 := bstep (se 1 (by rfl) ⟨2818553, by rfl⟩ : syracuseStep 3758071 = 5637107) B5637107
theorem B5010761 : Blo 1979435 5010761 := bstep (se 2 (by rfl) ⟨1879035, by rfl⟩ : syracuseStep 5010761 = 3758071) B3758071
theorem B3340507 : Blo 1979435 3340507 := bstep (se 1 (by rfl) ⟨2505380, by rfl⟩ : syracuseStep 3340507 = 5010761) B5010761
theorem B4454009 : Blo 1979435 4454009 := bstep (se 2 (by rfl) ⟨1670253, by rfl⟩ : syracuseStep 4454009 = 3340507) B3340507
theorem B2969339 : Blo 1979435 2969339 := bstep (se 1 (by rfl) ⟨2227004, by rfl⟩ : syracuseStep 2969339 = 4454009) B4454009
theorem B1979559 : Blo 1979435 1979559 := bstep (se 1 (by rfl) ⟨1484669, by rfl⟩ : syracuseStep 1979559 = 2969339) B2969339
theorem B2227009 : Blo 1979435 2227009 := bbase (se 2 (by rfl) ⟨835128, by rfl⟩ : syracuseStep 2227009 = 1670257) (by norm_num)
theorem B2969345 : Blo 1979435 2969345 := bstep (se 2 (by rfl) ⟨1113504, by rfl⟩ : syracuseStep 2969345 = 2227009) B2227009
theorem B1979563 : Blo 1979435 1979563 := bstep (se 1 (by rfl) ⟨1484672, by rfl⟩ : syracuseStep 1979563 = 2969345) B2969345
theorem B5010781 : Blo 1979435 5010781 := bbase (se 3 (by rfl) ⟨939521, by rfl⟩ : syracuseStep 5010781 = 1879043) (by norm_num)
theorem B6681041 : Blo 1979435 6681041 := bstep (se 2 (by rfl) ⟨2505390, by rfl⟩ : syracuseStep 6681041 = 5010781) B5010781
theorem B4454027 : Blo 1979435 4454027 := bstep (se 1 (by rfl) ⟨3340520, by rfl⟩ : syracuseStep 4454027 = 6681041) B6681041
theorem B2969351 : Blo 1979435 2969351 := bstep (se 1 (by rfl) ⟨2227013, by rfl⟩ : syracuseStep 2969351 = 4454027) B4454027
theorem B1979567 : Blo 1979435 1979567 := bstep (se 1 (by rfl) ⟨1484675, by rfl⟩ : syracuseStep 1979567 = 2969351) B2969351
theorem B2969357 : Blo 1979435 2969357 := bbase (se 3 (by rfl) ⟨556754, by rfl⟩ : syracuseStep 2969357 = 1113509) (by norm_num)
theorem B1979571 : Blo 1979435 1979571 := bstep (se 1 (by rfl) ⟨1484678, by rfl⟩ : syracuseStep 1979571 = 2969357) B2969357
theorem B4454045 : Blo 1979435 4454045 := bbase (se 3 (by rfl) ⟨835133, by rfl⟩ : syracuseStep 4454045 = 1670267) (by norm_num)
theorem B2969363 : Blo 1979435 2969363 := bstep (se 1 (by rfl) ⟨2227022, by rfl⟩ : syracuseStep 2969363 = 4454045) B4454045
theorem B1979575 : Blo 1979435 1979575 := bstep (se 1 (by rfl) ⟨1484681, by rfl⟩ : syracuseStep 1979575 = 2969363) B2969363
theorem B3340541 : Blo 1979435 3340541 := bbase (se 3 (by rfl) ⟨626351, by rfl⟩ : syracuseStep 3340541 = 1252703) (by norm_num)
theorem B2227027 : Blo 1979435 2227027 := bstep (se 1 (by rfl) ⟨1670270, by rfl⟩ : syracuseStep 2227027 = 3340541) B3340541
theorem B2969369 : Blo 1979435 2969369 := bstep (se 2 (by rfl) ⟨1113513, by rfl⟩ : syracuseStep 2969369 = 2227027) B2227027
theorem B1979579 : Blo 1979435 1979579 := bstep (se 1 (by rfl) ⟨1484684, by rfl⟩ : syracuseStep 1979579 = 2969369) B2969369
theorem B2257417 : Blo 1979435 2257417 := bbase (se 2 (by rfl) ⟨846531, by rfl⟩ : syracuseStep 2257417 = 1693063) (by norm_num)
theorem B3009889 : Blo 1979435 3009889 := bstep (se 2 (by rfl) ⟨1128708, by rfl⟩ : syracuseStep 3009889 = 2257417) B2257417
theorem B16052741 : Blo 1979435 16052741 := bstep (se 4 (by rfl) ⟨1504944, by rfl⟩ : syracuseStep 16052741 = 3009889) B3009889
theorem B10701827 : Blo 1979435 10701827 := bstep (se 1 (by rfl) ⟨8026370, by rfl⟩ : syracuseStep 10701827 = 16052741) B16052741
theorem B7134551 : Blo 1979435 7134551 := bstep (se 1 (by rfl) ⟨5350913, by rfl⟩ : syracuseStep 7134551 = 10701827) B10701827
theorem B4756367 : Blo 1979435 4756367 := bstep (se 1 (by rfl) ⟨3567275, by rfl⟩ : syracuseStep 4756367 = 7134551) B7134551
theorem B3170911 : Blo 1979435 3170911 := bstep (se 1 (by rfl) ⟨2378183, by rfl⟩ : syracuseStep 3170911 = 4756367) B4756367
theorem B4227881 : Blo 1979435 4227881 := bstep (se 2 (by rfl) ⟨1585455, by rfl⟩ : syracuseStep 4227881 = 3170911) B3170911
theorem B11274349 : Blo 1979435 11274349 := bstep (se 3 (by rfl) ⟨2113940, by rfl⟩ : syracuseStep 11274349 = 4227881) B4227881
theorem B15032465 : Blo 1979435 15032465 := bstep (se 2 (by rfl) ⟨5637174, by rfl⟩ : syracuseStep 15032465 = 11274349) B11274349
theorem B10021643 : Blo 1979435 10021643 := bstep (se 1 (by rfl) ⟨7516232, by rfl⟩ : syracuseStep 10021643 = 15032465) B15032465
theorem B6681095 : Blo 1979435 6681095 := bstep (se 1 (by rfl) ⟨5010821, by rfl⟩ : syracuseStep 6681095 = 10021643) B10021643
theorem B4454063 : Blo 1979435 4454063 := bstep (se 1 (by rfl) ⟨3340547, by rfl⟩ : syracuseStep 4454063 = 6681095) B6681095
theorem B2969375 : Blo 1979435 2969375 := bstep (se 1 (by rfl) ⟨2227031, by rfl⟩ : syracuseStep 2969375 = 4454063) B4454063
theorem B1979583 : Blo 1979435 1979583 := bstep (se 1 (by rfl) ⟨1484687, by rfl⟩ : syracuseStep 1979583 = 2969375) B2969375
theorem B2969381 : Blo 1979435 2969381 := bbase (se 4 (by rfl) ⟨278379, by rfl⟩ : syracuseStep 2969381 = 556759) (by norm_num)
theorem B1979587 : Blo 1979435 1979587 := bstep (se 1 (by rfl) ⟨1484690, by rfl⟩ : syracuseStep 1979587 = 2969381) B2969381
theorem B2505421 : Blo 1979435 2505421 := bbase (se 3 (by rfl) ⟨469766, by rfl⟩ : syracuseStep 2505421 = 939533) (by norm_num)
theorem B3340561 : Blo 1979435 3340561 := bstep (se 2 (by rfl) ⟨1252710, by rfl⟩ : syracuseStep 3340561 = 2505421) B2505421
theorem B4454081 : Blo 1979435 4454081 := bstep (se 2 (by rfl) ⟨1670280, by rfl⟩ : syracuseStep 4454081 = 3340561) B3340561
theorem B2969387 : Blo 1979435 2969387 := bstep (se 1 (by rfl) ⟨2227040, by rfl⟩ : syracuseStep 2969387 = 4454081) B4454081
theorem B1979591 : Blo 1979435 1979591 := bstep (se 1 (by rfl) ⟨1484693, by rfl⟩ : syracuseStep 1979591 = 2969387) B2969387
theorem B2227045 : Blo 1979435 2227045 := bbase (se 4 (by rfl) ⟨208785, by rfl⟩ : syracuseStep 2227045 = 417571) (by norm_num)
theorem B2969393 : Blo 1979435 2969393 := bstep (se 2 (by rfl) ⟨1113522, by rfl⟩ : syracuseStep 2969393 = 2227045) B2227045
theorem B1979595 : Blo 1979435 1979595 := bstep (se 1 (by rfl) ⟨1484696, by rfl⟩ : syracuseStep 1979595 = 2969393) B2969393
theorem B5637221 : Blo 1979435 5637221 := bbase (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) (by norm_num)
theorem B3758147 : Blo 1979435 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B2505431 : Blo 1979435 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B6681149 : Blo 1979435 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B4454099 : Blo 1979435 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B2969399 : Blo 1979435 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B1979599 : Blo 1979435 1979599 := bstep (se 1 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 1979599 = 2969399) B2969399
theorem B2969405 : Blo 1979435 2969405 := bbase (se 3 (by rfl) ⟨556763, by rfl⟩ : syracuseStep 2969405 = 1113527) (by norm_num)
theorem B1979603 : Blo 1979435 1979603 := bstep (se 1 (by rfl) ⟨1484702, by rfl⟩ : syracuseStep 1979603 = 2969405) B2969405
theorem B4454117 : Blo 1979435 4454117 := bbase (se 4 (by rfl) ⟨417573, by rfl⟩ : syracuseStep 4454117 = 835147) (by norm_num)
theorem B2969411 : Blo 1979435 2969411 := bstep (se 1 (by rfl) ⟨2227058, by rfl⟩ : syracuseStep 2969411 = 4454117) B4454117
theorem B1979607 : Blo 1979435 1979607 := bstep (se 1 (by rfl) ⟨1484705, by rfl⟩ : syracuseStep 1979607 = 2969411) B2969411
theorem B5010893 : Blo 1979435 5010893 := bbase (se 3 (by rfl) ⟨939542, by rfl⟩ : syracuseStep 5010893 = 1879085) (by norm_num)
theorem B3340595 : Blo 1979435 3340595 := bstep (se 1 (by rfl) ⟨2505446, by rfl⟩ : syracuseStep 3340595 = 5010893) B5010893
theorem B2227063 : Blo 1979435 2227063 := bstep (se 1 (by rfl) ⟨1670297, by rfl⟩ : syracuseStep 2227063 = 3340595) B3340595
theorem B2969417 : Blo 1979435 2969417 := bstep (se 2 (by rfl) ⟨1113531, by rfl⟩ : syracuseStep 2969417 = 2227063) B2227063
theorem B1979611 : Blo 1979435 1979611 := bstep (se 1 (by rfl) ⟨1484708, by rfl⟩ : syracuseStep 1979611 = 2969417) B2969417
theorem B4756445 : Blo 1979435 4756445 := bbase (se 3 (by rfl) ⟨891833, by rfl⟩ : syracuseStep 4756445 = 1783667) (by norm_num)
theorem B3170963 : Blo 1979435 3170963 := bstep (se 1 (by rfl) ⟨2378222, by rfl⟩ : syracuseStep 3170963 = 4756445) B4756445
theorem B2113975 : Blo 1979435 2113975 := bstep (se 1 (by rfl) ⟨1585481, by rfl⟩ : syracuseStep 2113975 = 3170963) B3170963
theorem B2818633 : Blo 1979435 2818633 := bstep (se 2 (by rfl) ⟨1056987, by rfl⟩ : syracuseStep 2818633 = 2113975) B2113975
theorem B3758177 : Blo 1979435 3758177 := bstep (se 2 (by rfl) ⟨1409316, by rfl⟩ : syracuseStep 3758177 = 2818633) B2818633
theorem B10021805 : Blo 1979435 10021805 := bstep (se 3 (by rfl) ⟨1879088, by rfl⟩ : syracuseStep 10021805 = 3758177) B3758177
theorem B6681203 : Blo 1979435 6681203 := bstep (se 1 (by rfl) ⟨5010902, by rfl⟩ : syracuseStep 6681203 = 10021805) B10021805
theorem B4454135 : Blo 1979435 4454135 := bstep (se 1 (by rfl) ⟨3340601, by rfl⟩ : syracuseStep 4454135 = 6681203) B6681203
theorem B2969423 : Blo 1979435 2969423 := bstep (se 1 (by rfl) ⟨2227067, by rfl⟩ : syracuseStep 2969423 = 4454135) B4454135
theorem B1979615 : Blo 1979435 1979615 := bstep (se 1 (by rfl) ⟨1484711, by rfl⟩ : syracuseStep 1979615 = 2969423) B2969423
theorem B2969429 : Blo 1979435 2969429 := bbase (se 9 (by rfl) ⟨8699, by rfl⟩ : syracuseStep 2969429 = 17399) (by norm_num)
theorem B1979619 : Blo 1979435 1979619 := bstep (se 1 (by rfl) ⟨1484714, by rfl⟩ : syracuseStep 1979619 = 2969429) B2969429
theorem B10158581 : Blo 1979435 10158581 := bbase (se 5 (by rfl) ⟨476183, by rfl⟩ : syracuseStep 10158581 = 952367) (by norm_num)
theorem B27089549 : Blo 1979435 27089549 := bstep (se 3 (by rfl) ⟨5079290, by rfl⟩ : syracuseStep 27089549 = 10158581) B10158581
theorem B18059699 : Blo 1979435 18059699 := bstep (se 1 (by rfl) ⟨13544774, by rfl⟩ : syracuseStep 18059699 = 27089549) B27089549
theorem B48159197 : Blo 1979435 48159197 := bstep (se 3 (by rfl) ⟨9029849, by rfl⟩ : syracuseStep 48159197 = 18059699) B18059699
theorem B32106131 : Blo 1979435 32106131 := bstep (se 1 (by rfl) ⟨24079598, by rfl⟩ : syracuseStep 32106131 = 48159197) B48159197
theorem B21404087 : Blo 1979435 21404087 := bstep (se 1 (by rfl) ⟨16053065, by rfl⟩ : syracuseStep 21404087 = 32106131) B32106131
theorem B14269391 : Blo 1979435 14269391 := bstep (se 1 (by rfl) ⟨10702043, by rfl⟩ : syracuseStep 14269391 = 21404087) B21404087
theorem B9512927 : Blo 1979435 9512927 := bstep (se 1 (by rfl) ⟨7134695, by rfl⟩ : syracuseStep 9512927 = 14269391) B14269391
theorem B6341951 : Blo 1979435 6341951 := bstep (se 1 (by rfl) ⟨4756463, by rfl⟩ : syracuseStep 6341951 = 9512927) B9512927
theorem B4227967 : Blo 1979435 4227967 := bstep (se 1 (by rfl) ⟨3170975, by rfl⟩ : syracuseStep 4227967 = 6341951) B6341951
theorem B5637289 : Blo 1979435 5637289 := bstep (se 2 (by rfl) ⟨2113983, by rfl⟩ : syracuseStep 5637289 = 4227967) B4227967
theorem B7516385 : Blo 1979435 7516385 := bstep (se 2 (by rfl) ⟨2818644, by rfl⟩ : syracuseStep 7516385 = 5637289) B5637289
theorem B5010923 : Blo 1979435 5010923 := bstep (se 1 (by rfl) ⟨3758192, by rfl⟩ : syracuseStep 5010923 = 7516385) B7516385
theorem B3340615 : Blo 1979435 3340615 := bstep (se 1 (by rfl) ⟨2505461, by rfl⟩ : syracuseStep 3340615 = 5010923) B5010923
theorem B4454153 : Blo 1979435 4454153 := bstep (se 2 (by rfl) ⟨1670307, by rfl⟩ : syracuseStep 4454153 = 3340615) B3340615
theorem B2969435 : Blo 1979435 2969435 := bstep (se 1 (by rfl) ⟨2227076, by rfl⟩ : syracuseStep 2969435 = 4454153) B4454153
theorem B1979623 : Blo 1979435 1979623 := bstep (se 1 (by rfl) ⟨1484717, by rfl⟩ : syracuseStep 1979623 = 2969435) B2969435
theorem B2227081 : Blo 1979435 2227081 := bbase (se 2 (by rfl) ⟨835155, by rfl⟩ : syracuseStep 2227081 = 1670311) (by norm_num)
theorem B2969441 : Blo 1979435 2969441 := bstep (se 2 (by rfl) ⟨1113540, by rfl⟩ : syracuseStep 2969441 = 2227081) B2227081
theorem B1979627 : Blo 1979435 1979627 := bstep (se 1 (by rfl) ⟨1484720, by rfl⟩ : syracuseStep 1979627 = 2969441) B2969441
theorem B17142677 : Blo 1979435 17142677 := bbase (se 6 (by rfl) ⟨401781, by rfl⟩ : syracuseStep 17142677 = 803563) (by norm_num)
theorem B11428451 : Blo 1979435 11428451 := bstep (se 1 (by rfl) ⟨8571338, by rfl⟩ : syracuseStep 11428451 = 17142677) B17142677
theorem B7618967 : Blo 1979435 7618967 := bstep (se 1 (by rfl) ⟨5714225, by rfl⟩ : syracuseStep 7618967 = 11428451) B11428451
theorem B5079311 : Blo 1979435 5079311 := bstep (se 1 (by rfl) ⟨3809483, by rfl⟩ : syracuseStep 5079311 = 7618967) B7618967
theorem B3386207 : Blo 1979435 3386207 := bstep (se 1 (by rfl) ⟨2539655, by rfl⟩ : syracuseStep 3386207 = 5079311) B5079311
theorem B2257471 : Blo 1979435 2257471 := bstep (se 1 (by rfl) ⟨1693103, by rfl⟩ : syracuseStep 2257471 = 3386207) B3386207
theorem B12039845 : Blo 1979435 12039845 := bstep (se 4 (by rfl) ⟨1128735, by rfl⟩ : syracuseStep 12039845 = 2257471) B2257471
theorem B128425013 : Blo 1979435 128425013 := bstep (se 5 (by rfl) ⟨6019922, by rfl⟩ : syracuseStep 128425013 = 12039845) B12039845
theorem B85616675 : Blo 1979435 85616675 := bstep (se 1 (by rfl) ⟨64212506, by rfl⟩ : syracuseStep 85616675 = 128425013) B128425013
theorem B57077783 : Blo 1979435 57077783 := bstep (se 1 (by rfl) ⟨42808337, by rfl⟩ : syracuseStep 57077783 = 85616675) B85616675
theorem B38051855 : Blo 1979435 38051855 := bstep (se 1 (by rfl) ⟨28538891, by rfl⟩ : syracuseStep 38051855 = 57077783) B57077783
theorem B25367903 : Blo 1979435 25367903 := bstep (se 1 (by rfl) ⟨19025927, by rfl⟩ : syracuseStep 25367903 = 38051855) B38051855
theorem B16911935 : Blo 1979435 16911935 := bstep (se 1 (by rfl) ⟨12683951, by rfl⟩ : syracuseStep 16911935 = 25367903) B25367903
theorem B11274623 : Blo 1979435 11274623 := bstep (se 1 (by rfl) ⟨8455967, by rfl⟩ : syracuseStep 11274623 = 16911935) B16911935
theorem B7516415 : Blo 1979435 7516415 := bstep (se 1 (by rfl) ⟨5637311, by rfl⟩ : syracuseStep 7516415 = 11274623) B11274623
theorem B5010943 : Blo 1979435 5010943 := bstep (se 1 (by rfl) ⟨3758207, by rfl⟩ : syracuseStep 5010943 = 7516415) B7516415
theorem B6681257 : Blo 1979435 6681257 := bstep (se 2 (by rfl) ⟨2505471, by rfl⟩ : syracuseStep 6681257 = 5010943) B5010943
theorem B4454171 : Blo 1979435 4454171 := bstep (se 1 (by rfl) ⟨3340628, by rfl⟩ : syracuseStep 4454171 = 6681257) B6681257
theorem B2969447 : Blo 1979435 2969447 := bstep (se 1 (by rfl) ⟨2227085, by rfl⟩ : syracuseStep 2969447 = 4454171) B4454171
theorem B1979631 : Blo 1979435 1979631 := bstep (se 1 (by rfl) ⟨1484723, by rfl⟩ : syracuseStep 1979631 = 2969447) B2969447
theorem B2969453 : Blo 1979435 2969453 := bbase (se 3 (by rfl) ⟨556772, by rfl⟩ : syracuseStep 2969453 = 1113545) (by norm_num)
theorem B1979635 : Blo 1979435 1979635 := bstep (se 1 (by rfl) ⟨1484726, by rfl⟩ : syracuseStep 1979635 = 2969453) B2969453
theorem B4454189 : Blo 1979435 4454189 := bbase (se 3 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 4454189 = 1670321) (by norm_num)
theorem B2969459 : Blo 1979435 2969459 := bstep (se 1 (by rfl) ⟨2227094, by rfl⟩ : syracuseStep 2969459 = 4454189) B4454189
theorem B1979639 : Blo 1979435 1979639 := bstep (se 1 (by rfl) ⟨1484729, by rfl⟩ : syracuseStep 1979639 = 2969459) B2969459
theorem B8456021 : Blo 1979435 8456021 := bbase (se 9 (by rfl) ⟨24773, by rfl⟩ : syracuseStep 8456021 = 49547) (by norm_num)
theorem B5637347 : Blo 1979435 5637347 := bstep (se 1 (by rfl) ⟨4228010, by rfl⟩ : syracuseStep 5637347 = 8456021) B8456021
theorem B3758231 : Blo 1979435 3758231 := bstep (se 1 (by rfl) ⟨2818673, by rfl⟩ : syracuseStep 3758231 = 5637347) B5637347
theorem B2505487 : Blo 1979435 2505487 := bstep (se 1 (by rfl) ⟨1879115, by rfl⟩ : syracuseStep 2505487 = 3758231) B3758231
theorem B3340649 : Blo 1979435 3340649 := bstep (se 2 (by rfl) ⟨1252743, by rfl⟩ : syracuseStep 3340649 = 2505487) B2505487
theorem B2227099 : Blo 1979435 2227099 := bstep (se 1 (by rfl) ⟨1670324, by rfl⟩ : syracuseStep 2227099 = 3340649) B3340649
theorem B2969465 : Blo 1979435 2969465 := bstep (se 2 (by rfl) ⟨1113549, by rfl⟩ : syracuseStep 2969465 = 2227099) B2227099
theorem B1979643 : Blo 1979435 1979643 := bstep (se 1 (by rfl) ⟨1484732, by rfl⟩ : syracuseStep 1979643 = 2969465) B2969465
theorem B12684053 : Blo 1979435 12684053 := bbase (se 6 (by rfl) ⟨297282, by rfl⟩ : syracuseStep 12684053 = 594565) (by norm_num)
theorem B33824141 : Blo 1979435 33824141 := bstep (se 3 (by rfl) ⟨6342026, by rfl⟩ : syracuseStep 33824141 = 12684053) B12684053
theorem B22549427 : Blo 1979435 22549427 := bstep (se 1 (by rfl) ⟨16912070, by rfl⟩ : syracuseStep 22549427 = 33824141) B33824141
theorem B15032951 : Blo 1979435 15032951 := bstep (se 1 (by rfl) ⟨11274713, by rfl⟩ : syracuseStep 15032951 = 22549427) B22549427
theorem B10021967 : Blo 1979435 10021967 := bstep (se 1 (by rfl) ⟨7516475, by rfl⟩ : syracuseStep 10021967 = 15032951) B15032951
theorem B6681311 : Blo 1979435 6681311 := bstep (se 1 (by rfl) ⟨5010983, by rfl⟩ : syracuseStep 6681311 = 10021967) B10021967
theorem B4454207 : Blo 1979435 4454207 := bstep (se 1 (by rfl) ⟨3340655, by rfl⟩ : syracuseStep 4454207 = 6681311) B6681311
theorem B2969471 : Blo 1979435 2969471 := bstep (se 1 (by rfl) ⟨2227103, by rfl⟩ : syracuseStep 2969471 = 4454207) B4454207
theorem B1979647 : Blo 1979435 1979647 := bstep (se 1 (by rfl) ⟨1484735, by rfl⟩ : syracuseStep 1979647 = 2969471) B2969471
theorem B2969477 : Blo 1979435 2969477 := bbase (se 4 (by rfl) ⟨278388, by rfl⟩ : syracuseStep 2969477 = 556777) (by norm_num)
theorem B1979651 : Blo 1979435 1979651 := bstep (se 1 (by rfl) ⟨1484738, by rfl⟩ : syracuseStep 1979651 = 2969477) B2969477
theorem B3340669 : Blo 1979435 3340669 := bbase (se 3 (by rfl) ⟨626375, by rfl⟩ : syracuseStep 3340669 = 1252751) (by norm_num)
theorem B4454225 : Blo 1979435 4454225 := bstep (se 2 (by rfl) ⟨1670334, by rfl⟩ : syracuseStep 4454225 = 3340669) B3340669
theorem B2969483 : Blo 1979435 2969483 := bstep (se 1 (by rfl) ⟨2227112, by rfl⟩ : syracuseStep 2969483 = 4454225) B4454225
theorem B1979655 : Blo 1979435 1979655 := bstep (se 1 (by rfl) ⟨1484741, by rfl⟩ : syracuseStep 1979655 = 2969483) B2969483
theorem B2227117 : Blo 1979435 2227117 := bbase (se 3 (by rfl) ⟨417584, by rfl⟩ : syracuseStep 2227117 = 835169) (by norm_num)
theorem B2969489 : Blo 1979435 2969489 := bstep (se 2 (by rfl) ⟨1113558, by rfl⟩ : syracuseStep 2969489 = 2227117) B2227117
theorem B1979659 : Blo 1979435 1979659 := bstep (se 1 (by rfl) ⟨1484744, by rfl⟩ : syracuseStep 1979659 = 2969489) B2969489
theorem B6681365 : Blo 1979435 6681365 := bbase (se 6 (by rfl) ⟨156594, by rfl⟩ : syracuseStep 6681365 = 313189) (by norm_num)
theorem B4454243 : Blo 1979435 4454243 := bstep (se 1 (by rfl) ⟨3340682, by rfl⟩ : syracuseStep 4454243 = 6681365) B6681365
theorem B2969495 : Blo 1979435 2969495 := bstep (se 1 (by rfl) ⟨2227121, by rfl⟩ : syracuseStep 2969495 = 4454243) B4454243
theorem B1979663 : Blo 1979435 1979663 := bstep (se 1 (by rfl) ⟨1484747, by rfl⟩ : syracuseStep 1979663 = 2969495) B2969495
theorem B2969501 : Blo 1979435 2969501 := bbase (se 3 (by rfl) ⟨556781, by rfl⟩ : syracuseStep 2969501 = 1113563) (by norm_num)
theorem B1979667 : Blo 1979435 1979667 := bstep (se 1 (by rfl) ⟨1484750, by rfl⟩ : syracuseStep 1979667 = 2969501) B2969501
theorem B4454261 : Blo 1979435 4454261 := bbase (se 5 (by rfl) ⟨208793, by rfl⟩ : syracuseStep 4454261 = 417587) (by norm_num)
theorem B2969507 : Blo 1979435 2969507 := bstep (se 1 (by rfl) ⟨2227130, by rfl⟩ : syracuseStep 2969507 = 4454261) B4454261
theorem B1979671 : Blo 1979435 1979671 := bstep (se 1 (by rfl) ⟨1484753, by rfl⟩ : syracuseStep 1979671 = 2969507) B2969507
theorem B2675581 : Blo 1979435 2675581 := bbase (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) (by norm_num)
theorem B14269765 : Blo 1979435 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B19026353 : Blo 1979435 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B12684235 : Blo 1979435 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B16912313 : Blo 1979435 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B11274875 : Blo 1979435 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B7516583 : Blo 1979435 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B5011055 : Blo 1979435 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B3340703 : Blo 1979435 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B2227135 : Blo 1979435 2227135 := bstep (se 1 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 2227135 = 3340703) B3340703
theorem B2969513 : Blo 1979435 2969513 := bstep (se 2 (by rfl) ⟨1113567, by rfl⟩ : syracuseStep 2969513 = 2227135) B2227135
theorem B1979675 : Blo 1979435 1979675 := bstep (se 1 (by rfl) ⟨1484756, by rfl⟩ : syracuseStep 1979675 = 2969513) B2969513
theorem B7516597 : Blo 1979435 7516597 := bbase (se 5 (by rfl) ⟨352340, by rfl⟩ : syracuseStep 7516597 = 704681) (by norm_num)
theorem B10022129 : Blo 1979435 10022129 := bstep (se 2 (by rfl) ⟨3758298, by rfl⟩ : syracuseStep 10022129 = 7516597) B7516597
theorem B6681419 : Blo 1979435 6681419 := bstep (se 1 (by rfl) ⟨5011064, by rfl⟩ : syracuseStep 6681419 = 10022129) B10022129
theorem B4454279 : Blo 1979435 4454279 := bstep (se 1 (by rfl) ⟨3340709, by rfl⟩ : syracuseStep 4454279 = 6681419) B6681419
theorem B2969519 : Blo 1979435 2969519 := bstep (se 1 (by rfl) ⟨2227139, by rfl⟩ : syracuseStep 2969519 = 4454279) B4454279
theorem B1979679 : Blo 1979435 1979679 := bstep (se 1 (by rfl) ⟨1484759, by rfl⟩ : syracuseStep 1979679 = 2969519) B2969519
theorem B2969525 : Blo 1979435 2969525 := bbase (se 5 (by rfl) ⟨139196, by rfl⟩ : syracuseStep 2969525 = 278393) (by norm_num)
theorem B1979683 : Blo 1979435 1979683 := bstep (se 1 (by rfl) ⟨1484762, by rfl⟩ : syracuseStep 1979683 = 2969525) B2969525
theorem B5011085 : Blo 1979435 5011085 := bbase (se 3 (by rfl) ⟨939578, by rfl⟩ : syracuseStep 5011085 = 1879157) (by norm_num)
theorem B3340723 : Blo 1979435 3340723 := bstep (se 1 (by rfl) ⟨2505542, by rfl⟩ : syracuseStep 3340723 = 5011085) B5011085
theorem B4454297 : Blo 1979435 4454297 := bstep (se 2 (by rfl) ⟨1670361, by rfl⟩ : syracuseStep 4454297 = 3340723) B3340723
theorem B2969531 : Blo 1979435 2969531 := bstep (se 1 (by rfl) ⟨2227148, by rfl⟩ : syracuseStep 2969531 = 4454297) B4454297
theorem B1979687 : Blo 1979435 1979687 := bstep (se 1 (by rfl) ⟨1484765, by rfl⟩ : syracuseStep 1979687 = 2969531) B2969531
theorem B2227153 : Blo 1979435 2227153 := bbase (se 2 (by rfl) ⟨835182, by rfl⟩ : syracuseStep 2227153 = 1670365) (by norm_num)
theorem B2969537 : Blo 1979435 2969537 := bstep (se 2 (by rfl) ⟨1113576, by rfl⟩ : syracuseStep 2969537 = 2227153) B2227153
theorem B1979691 : Blo 1979435 1979691 := bstep (se 1 (by rfl) ⟨1484768, by rfl⟩ : syracuseStep 1979691 = 2969537) B2969537
theorem B4756637 : Blo 1979435 4756637 := bbase (se 3 (by rfl) ⟨891869, by rfl⟩ : syracuseStep 4756637 = 1783739) (by norm_num)
theorem B3171091 : Blo 1979435 3171091 := bstep (se 1 (by rfl) ⟨2378318, by rfl⟩ : syracuseStep 3171091 = 4756637) B4756637
theorem B4228121 : Blo 1979435 4228121 := bstep (se 2 (by rfl) ⟨1585545, by rfl⟩ : syracuseStep 4228121 = 3171091) B3171091
theorem B2818747 : Blo 1979435 2818747 := bstep (se 1 (by rfl) ⟨2114060, by rfl⟩ : syracuseStep 2818747 = 4228121) B4228121
theorem B3758329 : Blo 1979435 3758329 := bstep (se 2 (by rfl) ⟨1409373, by rfl⟩ : syracuseStep 3758329 = 2818747) B2818747
theorem B5011105 : Blo 1979435 5011105 := bstep (se 2 (by rfl) ⟨1879164, by rfl⟩ : syracuseStep 5011105 = 3758329) B3758329
theorem B6681473 : Blo 1979435 6681473 := bstep (se 2 (by rfl) ⟨2505552, by rfl⟩ : syracuseStep 6681473 = 5011105) B5011105
theorem B4454315 : Blo 1979435 4454315 := bstep (se 1 (by rfl) ⟨3340736, by rfl⟩ : syracuseStep 4454315 = 6681473) B6681473
theorem B2969543 : Blo 1979435 2969543 := bstep (se 1 (by rfl) ⟨2227157, by rfl⟩ : syracuseStep 2969543 = 4454315) B4454315
theorem B1979695 : Blo 1979435 1979695 := bstep (se 1 (by rfl) ⟨1484771, by rfl⟩ : syracuseStep 1979695 = 2969543) B2969543
theorem B2969549 : Blo 1979435 2969549 := bbase (se 3 (by rfl) ⟨556790, by rfl⟩ : syracuseStep 2969549 = 1113581) (by norm_num)
theorem B1979699 : Blo 1979435 1979699 := bstep (se 1 (by rfl) ⟨1484774, by rfl⟩ : syracuseStep 1979699 = 2969549) B2969549
theorem B4454333 : Blo 1979435 4454333 := bbase (se 3 (by rfl) ⟨835187, by rfl⟩ : syracuseStep 4454333 = 1670375) (by norm_num)
theorem B2969555 : Blo 1979435 2969555 := bstep (se 1 (by rfl) ⟨2227166, by rfl⟩ : syracuseStep 2969555 = 4454333) B4454333
theorem B1979703 : Blo 1979435 1979703 := bstep (se 1 (by rfl) ⟨1484777, by rfl⟩ : syracuseStep 1979703 = 2969555) B2969555
theorem B3340757 : Blo 1979435 3340757 := bbase (se 7 (by rfl) ⟨39149, by rfl⟩ : syracuseStep 3340757 = 78299) (by norm_num)
theorem B2227171 : Blo 1979435 2227171 := bstep (se 1 (by rfl) ⟨1670378, by rfl⟩ : syracuseStep 2227171 = 3340757) B3340757
theorem B2969561 : Blo 1979435 2969561 := bstep (se 2 (by rfl) ⟨1113585, by rfl⟩ : syracuseStep 2969561 = 2227171) B2227171
theorem B1979707 : Blo 1979435 1979707 := bstep (se 1 (by rfl) ⟨1484780, by rfl⟩ : syracuseStep 1979707 = 2969561) B2969561
theorem B8456309 : Blo 1979435 8456309 := bbase (se 5 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 8456309 = 792779) (by norm_num)
theorem B5637539 : Blo 1979435 5637539 := bstep (se 1 (by rfl) ⟨4228154, by rfl⟩ : syracuseStep 5637539 = 8456309) B8456309
theorem B15033437 : Blo 1979435 15033437 := bstep (se 3 (by rfl) ⟨2818769, by rfl⟩ : syracuseStep 15033437 = 5637539) B5637539
theorem B10022291 : Blo 1979435 10022291 := bstep (se 1 (by rfl) ⟨7516718, by rfl⟩ : syracuseStep 10022291 = 15033437) B15033437
theorem B6681527 : Blo 1979435 6681527 := bstep (se 1 (by rfl) ⟨5011145, by rfl⟩ : syracuseStep 6681527 = 10022291) B10022291
theorem B4454351 : Blo 1979435 4454351 := bstep (se 1 (by rfl) ⟨3340763, by rfl⟩ : syracuseStep 4454351 = 6681527) B6681527
theorem B2969567 : Blo 1979435 2969567 := bstep (se 1 (by rfl) ⟨2227175, by rfl⟩ : syracuseStep 2969567 = 4454351) B4454351
theorem B1979711 : Blo 1979435 1979711 := bstep (se 1 (by rfl) ⟨1484783, by rfl⟩ : syracuseStep 1979711 = 2969567) B2969567
theorem B2969573 : Blo 1979435 2969573 := bbase (se 4 (by rfl) ⟨278397, by rfl⟩ : syracuseStep 2969573 = 556795) (by norm_num)
theorem B1979715 : Blo 1979435 1979715 := bstep (se 1 (by rfl) ⟨1484786, by rfl⟩ : syracuseStep 1979715 = 2969573) B2969573
theorem B2257573 : Blo 1979435 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B3010097 : Blo 1979435 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B2006731 : Blo 1979435 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B2675641 : Blo 1979435 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B3567521 : Blo 1979435 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B9513389 : Blo 1979435 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B6342259 : Blo 1979435 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B8456345 : Blo 1979435 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B5637563 : Blo 1979435 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B3758375 : Blo 1979435 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B2505583 : Blo 1979435 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B3340777 : Blo 1979435 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B4454369 : Blo 1979435 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B2969579 : Blo 1979435 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B1979719 : Blo 1979435 1979719 := bstep (se 1 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 1979719 = 2969579) B2969579
theorem B2227189 : Blo 1979435 2227189 := bbase (se 5 (by rfl) ⟨104399, by rfl⟩ : syracuseStep 2227189 = 208799) (by norm_num)
theorem B2969585 : Blo 1979435 2969585 := bstep (se 2 (by rfl) ⟨1113594, by rfl⟩ : syracuseStep 2969585 = 2227189) B2227189
theorem B1979723 : Blo 1979435 1979723 := bstep (se 1 (by rfl) ⟨1484792, by rfl⟩ : syracuseStep 1979723 = 2969585) B2969585
theorem B2505593 : Blo 1979435 2505593 := bbase (se 2 (by rfl) ⟨939597, by rfl⟩ : syracuseStep 2505593 = 1879195) (by norm_num)
theorem B6681581 : Blo 1979435 6681581 := bstep (se 3 (by rfl) ⟨1252796, by rfl⟩ : syracuseStep 6681581 = 2505593) B2505593
theorem B4454387 : Blo 1979435 4454387 := bstep (se 1 (by rfl) ⟨3340790, by rfl⟩ : syracuseStep 4454387 = 6681581) B6681581
theorem B2969591 : Blo 1979435 2969591 := bstep (se 1 (by rfl) ⟨2227193, by rfl⟩ : syracuseStep 2969591 = 4454387) B4454387
theorem B1979727 : Blo 1979435 1979727 := bstep (se 1 (by rfl) ⟨1484795, by rfl⟩ : syracuseStep 1979727 = 2969591) B2969591
theorem B2969597 : Blo 1979435 2969597 := bbase (se 3 (by rfl) ⟨556799, by rfl⟩ : syracuseStep 2969597 = 1113599) (by norm_num)
theorem B1979731 : Blo 1979435 1979731 := bstep (se 1 (by rfl) ⟨1484798, by rfl⟩ : syracuseStep 1979731 = 2969597) B2969597
theorem B4454405 : Blo 1979435 4454405 := bbase (se 4 (by rfl) ⟨417600, by rfl⟩ : syracuseStep 4454405 = 835201) (by norm_num)
theorem B2969603 : Blo 1979435 2969603 := bstep (se 1 (by rfl) ⟨2227202, by rfl⟩ : syracuseStep 2969603 = 4454405) B4454405
theorem B1979735 : Blo 1979435 1979735 := bstep (se 1 (by rfl) ⟨1484801, by rfl⟩ : syracuseStep 1979735 = 2969603) B2969603
theorem B3758413 : Blo 1979435 3758413 := bbase (se 3 (by rfl) ⟨704702, by rfl⟩ : syracuseStep 3758413 = 1409405) (by norm_num)
theorem B5011217 : Blo 1979435 5011217 := bstep (se 2 (by rfl) ⟨1879206, by rfl⟩ : syracuseStep 5011217 = 3758413) B3758413
theorem B3340811 : Blo 1979435 3340811 := bstep (se 1 (by rfl) ⟨2505608, by rfl⟩ : syracuseStep 3340811 = 5011217) B5011217
theorem B2227207 : Blo 1979435 2227207 := bstep (se 1 (by rfl) ⟨1670405, by rfl⟩ : syracuseStep 2227207 = 3340811) B3340811
theorem B2969609 : Blo 1979435 2969609 := bstep (se 2 (by rfl) ⟨1113603, by rfl⟩ : syracuseStep 2969609 = 2227207) B2227207
theorem B1979739 : Blo 1979435 1979739 := bstep (se 1 (by rfl) ⟨1484804, by rfl⟩ : syracuseStep 1979739 = 2969609) B2969609
theorem B10022453 : Blo 1979435 10022453 := bbase (se 5 (by rfl) ⟨469802, by rfl⟩ : syracuseStep 10022453 = 939605) (by norm_num)
theorem B6681635 : Blo 1979435 6681635 := bstep (se 1 (by rfl) ⟨5011226, by rfl⟩ : syracuseStep 6681635 = 10022453) B10022453
theorem B4454423 : Blo 1979435 4454423 := bstep (se 1 (by rfl) ⟨3340817, by rfl⟩ : syracuseStep 4454423 = 6681635) B6681635
theorem B2969615 : Blo 1979435 2969615 := bstep (se 1 (by rfl) ⟨2227211, by rfl⟩ : syracuseStep 2969615 = 4454423) B4454423
theorem B1979743 : Blo 1979435 1979743 := bstep (se 1 (by rfl) ⟨1484807, by rfl⟩ : syracuseStep 1979743 = 2969615) B2969615
theorem B2969621 : Blo 1979435 2969621 := bbase (se 6 (by rfl) ⟨69600, by rfl⟩ : syracuseStep 2969621 = 139201) (by norm_num)
theorem B1979747 : Blo 1979435 1979747 := bstep (se 1 (by rfl) ⟨1484810, by rfl⟩ : syracuseStep 1979747 = 2969621) B2969621
theorem B9513541 : Blo 1979435 9513541 := bbase (se 4 (by rfl) ⟨891894, by rfl⟩ : syracuseStep 9513541 = 1783789) (by norm_num)
theorem B12684721 : Blo 1979435 12684721 := bstep (se 2 (by rfl) ⟨4756770, by rfl⟩ : syracuseStep 12684721 = 9513541) B9513541
theorem B16912961 : Blo 1979435 16912961 := bstep (se 2 (by rfl) ⟨6342360, by rfl⟩ : syracuseStep 16912961 = 12684721) B12684721
theorem B11275307 : Blo 1979435 11275307 := bstep (se 1 (by rfl) ⟨8456480, by rfl⟩ : syracuseStep 11275307 = 16912961) B16912961
theorem B7516871 : Blo 1979435 7516871 := bstep (se 1 (by rfl) ⟨5637653, by rfl⟩ : syracuseStep 7516871 = 11275307) B11275307
theorem B5011247 : Blo 1979435 5011247 := bstep (se 1 (by rfl) ⟨3758435, by rfl⟩ : syracuseStep 5011247 = 7516871) B7516871
theorem B3340831 : Blo 1979435 3340831 := bstep (se 1 (by rfl) ⟨2505623, by rfl⟩ : syracuseStep 3340831 = 5011247) B5011247
theorem B4454441 : Blo 1979435 4454441 := bstep (se 2 (by rfl) ⟨1670415, by rfl⟩ : syracuseStep 4454441 = 3340831) B3340831
theorem B2969627 : Blo 1979435 2969627 := bstep (se 1 (by rfl) ⟨2227220, by rfl⟩ : syracuseStep 2969627 = 4454441) B4454441
theorem B1979751 : Blo 1979435 1979751 := bstep (se 1 (by rfl) ⟨1484813, by rfl⟩ : syracuseStep 1979751 = 2969627) B2969627
theorem B2227225 : Blo 1979435 2227225 := bbase (se 2 (by rfl) ⟨835209, by rfl⟩ : syracuseStep 2227225 = 1670419) (by norm_num)
theorem B2969633 : Blo 1979435 2969633 := bstep (se 2 (by rfl) ⟨1113612, by rfl⟩ : syracuseStep 2969633 = 2227225) B2227225
theorem B1979755 : Blo 1979435 1979755 := bstep (se 1 (by rfl) ⟨1484816, by rfl⟩ : syracuseStep 1979755 = 2969633) B2969633
theorem B7516901 : Blo 1979435 7516901 := bbase (se 4 (by rfl) ⟨704709, by rfl⟩ : syracuseStep 7516901 = 1409419) (by norm_num)
theorem B5011267 : Blo 1979435 5011267 := bstep (se 1 (by rfl) ⟨3758450, by rfl⟩ : syracuseStep 5011267 = 7516901) B7516901
theorem B6681689 : Blo 1979435 6681689 := bstep (se 2 (by rfl) ⟨2505633, by rfl⟩ : syracuseStep 6681689 = 5011267) B5011267
theorem B4454459 : Blo 1979435 4454459 := bstep (se 1 (by rfl) ⟨3340844, by rfl⟩ : syracuseStep 4454459 = 6681689) B6681689
theorem B2969639 : Blo 1979435 2969639 := bstep (se 1 (by rfl) ⟨2227229, by rfl⟩ : syracuseStep 2969639 = 4454459) B4454459
theorem B1979759 : Blo 1979435 1979759 := bstep (se 1 (by rfl) ⟨1484819, by rfl⟩ : syracuseStep 1979759 = 2969639) B2969639
theorem B2969645 : Blo 1979435 2969645 := bbase (se 3 (by rfl) ⟨556808, by rfl⟩ : syracuseStep 2969645 = 1113617) (by norm_num)
theorem B1979763 : Blo 1979435 1979763 := bstep (se 1 (by rfl) ⟨1484822, by rfl⟩ : syracuseStep 1979763 = 2969645) B2969645
theorem B4454477 : Blo 1979435 4454477 := bbase (se 3 (by rfl) ⟨835214, by rfl⟩ : syracuseStep 4454477 = 1670429) (by norm_num)
theorem B2969651 : Blo 1979435 2969651 := bstep (se 1 (by rfl) ⟨2227238, by rfl⟩ : syracuseStep 2969651 = 4454477) B4454477
theorem B1979767 : Blo 1979435 1979767 := bstep (se 1 (by rfl) ⟨1484825, by rfl⟩ : syracuseStep 1979767 = 2969651) B2969651
theorem B2505649 : Blo 1979435 2505649 := bbase (se 2 (by rfl) ⟨939618, by rfl⟩ : syracuseStep 2505649 = 1879237) (by norm_num)
theorem B3340865 : Blo 1979435 3340865 := bstep (se 2 (by rfl) ⟨1252824, by rfl⟩ : syracuseStep 3340865 = 2505649) B2505649
theorem B2227243 : Blo 1979435 2227243 := bstep (se 1 (by rfl) ⟨1670432, by rfl⟩ : syracuseStep 2227243 = 3340865) B3340865
theorem B2969657 : Blo 1979435 2969657 := bstep (se 2 (by rfl) ⟨1113621, by rfl⟩ : syracuseStep 2969657 = 2227243) B2227243
theorem B1979771 : Blo 1979435 1979771 := bstep (se 1 (by rfl) ⟨1484828, by rfl⟩ : syracuseStep 1979771 = 2969657) B2969657
theorem B6342437 : Blo 1979435 6342437 := bbase (se 4 (by rfl) ⟨594603, by rfl⟩ : syracuseStep 6342437 = 1189207) (by norm_num)
theorem B4228291 : Blo 1979435 4228291 := bstep (se 1 (by rfl) ⟨3171218, by rfl⟩ : syracuseStep 4228291 = 6342437) B6342437
theorem B22550885 : Blo 1979435 22550885 := bstep (se 4 (by rfl) ⟨2114145, by rfl⟩ : syracuseStep 22550885 = 4228291) B4228291
theorem B15033923 : Blo 1979435 15033923 := bstep (se 1 (by rfl) ⟨11275442, by rfl⟩ : syracuseStep 15033923 = 22550885) B22550885
theorem B10022615 : Blo 1979435 10022615 := bstep (se 1 (by rfl) ⟨7516961, by rfl⟩ : syracuseStep 10022615 = 15033923) B15033923
theorem B6681743 : Blo 1979435 6681743 := bstep (se 1 (by rfl) ⟨5011307, by rfl⟩ : syracuseStep 6681743 = 10022615) B10022615
theorem B4454495 : Blo 1979435 4454495 := bstep (se 1 (by rfl) ⟨3340871, by rfl⟩ : syracuseStep 4454495 = 6681743) B6681743
theorem B2969663 : Blo 1979435 2969663 := bstep (se 1 (by rfl) ⟨2227247, by rfl⟩ : syracuseStep 2969663 = 4454495) B4454495
theorem B1979775 : Blo 1979435 1979775 := bstep (se 1 (by rfl) ⟨1484831, by rfl⟩ : syracuseStep 1979775 = 2969663) B2969663
theorem B2969669 : Blo 1979435 2969669 := bbase (se 4 (by rfl) ⟨278406, by rfl⟩ : syracuseStep 2969669 = 556813) (by norm_num)
theorem B1979779 : Blo 1979435 1979779 := bstep (se 1 (by rfl) ⟨1484834, by rfl⟩ : syracuseStep 1979779 = 2969669) B2969669
theorem B3340885 : Blo 1979435 3340885 := bbase (se 8 (by rfl) ⟨19575, by rfl⟩ : syracuseStep 3340885 = 39151) (by norm_num)
theorem B4454513 : Blo 1979435 4454513 := bstep (se 2 (by rfl) ⟨1670442, by rfl⟩ : syracuseStep 4454513 = 3340885) B3340885
theorem B2969675 : Blo 1979435 2969675 := bstep (se 1 (by rfl) ⟨2227256, by rfl⟩ : syracuseStep 2969675 = 4454513) B4454513
theorem B1979783 : Blo 1979435 1979783 := bstep (se 1 (by rfl) ⟨1484837, by rfl⟩ : syracuseStep 1979783 = 2969675) B2969675
theorem B2227261 : Blo 1979435 2227261 := bbase (se 3 (by rfl) ⟨417611, by rfl⟩ : syracuseStep 2227261 = 835223) (by norm_num)
theorem B2969681 : Blo 1979435 2969681 := bstep (se 2 (by rfl) ⟨1113630, by rfl⟩ : syracuseStep 2969681 = 2227261) B2227261
theorem B1979787 : Blo 1979435 1979787 := bstep (se 1 (by rfl) ⟨1484840, by rfl⟩ : syracuseStep 1979787 = 2969681) B2969681
theorem B6681797 : Blo 1979435 6681797 := bbase (se 4 (by rfl) ⟨626418, by rfl⟩ : syracuseStep 6681797 = 1252837) (by norm_num)
theorem B4454531 : Blo 1979435 4454531 := bstep (se 1 (by rfl) ⟨3340898, by rfl⟩ : syracuseStep 4454531 = 6681797) B6681797
theorem B2969687 : Blo 1979435 2969687 := bstep (se 1 (by rfl) ⟨2227265, by rfl⟩ : syracuseStep 2969687 = 4454531) B4454531
theorem B1979791 : Blo 1979435 1979791 := bstep (se 1 (by rfl) ⟨1484843, by rfl⟩ : syracuseStep 1979791 = 2969687) B2969687
theorem B2969693 : Blo 1979435 2969693 := bbase (se 3 (by rfl) ⟨556817, by rfl⟩ : syracuseStep 2969693 = 1113635) (by norm_num)
theorem B1979795 : Blo 1979435 1979795 := bstep (se 1 (by rfl) ⟨1484846, by rfl⟩ : syracuseStep 1979795 = 2969693) B2969693
theorem B4454549 : Blo 1979435 4454549 := bbase (se 6 (by rfl) ⟨104403, by rfl⟩ : syracuseStep 4454549 = 208807) (by norm_num)
theorem B2969699 : Blo 1979435 2969699 := bstep (se 1 (by rfl) ⟨2227274, by rfl⟩ : syracuseStep 2969699 = 4454549) B4454549
theorem B1979799 : Blo 1979435 1979799 := bstep (se 1 (by rfl) ⟨1484849, by rfl⟩ : syracuseStep 1979799 = 2969699) B2969699
theorem B2818901 : Blo 1979435 2818901 := bbase (se 9 (by rfl) ⟨8258, by rfl⟩ : syracuseStep 2818901 = 16517) (by norm_num)
theorem B7517069 : Blo 1979435 7517069 := bstep (se 3 (by rfl) ⟨1409450, by rfl⟩ : syracuseStep 7517069 = 2818901) B2818901
theorem B5011379 : Blo 1979435 5011379 := bstep (se 1 (by rfl) ⟨3758534, by rfl⟩ : syracuseStep 5011379 = 7517069) B7517069
theorem B3340919 : Blo 1979435 3340919 := bstep (se 1 (by rfl) ⟨2505689, by rfl⟩ : syracuseStep 3340919 = 5011379) B5011379
theorem B2227279 : Blo 1979435 2227279 := bstep (se 1 (by rfl) ⟨1670459, by rfl⟩ : syracuseStep 2227279 = 3340919) B3340919
theorem B2969705 : Blo 1979435 2969705 := bstep (se 2 (by rfl) ⟨1113639, by rfl⟩ : syracuseStep 2969705 = 2227279) B2227279
theorem B1979803 : Blo 1979435 1979803 := bstep (se 1 (by rfl) ⟨1484852, by rfl⟩ : syracuseStep 1979803 = 2969705) B2969705
theorem B6429077 : Blo 1979435 6429077 := bbase (se 6 (by rfl) ⟨150681, by rfl⟩ : syracuseStep 6429077 = 301363) (by norm_num)
theorem B4286051 : Blo 1979435 4286051 := bstep (se 1 (by rfl) ⟨3214538, by rfl⟩ : syracuseStep 4286051 = 6429077) B6429077
theorem B2857367 : Blo 1979435 2857367 := bstep (se 1 (by rfl) ⟨2143025, by rfl⟩ : syracuseStep 2857367 = 4286051) B4286051
theorem B7619645 : Blo 1979435 7619645 := bstep (se 3 (by rfl) ⟨1428683, by rfl⟩ : syracuseStep 7619645 = 2857367) B2857367
theorem B5079763 : Blo 1979435 5079763 := bstep (se 1 (by rfl) ⟨3809822, by rfl⟩ : syracuseStep 5079763 = 7619645) B7619645
theorem B6773017 : Blo 1979435 6773017 := bstep (se 2 (by rfl) ⟨2539881, by rfl⟩ : syracuseStep 6773017 = 5079763) B5079763
theorem B9030689 : Blo 1979435 9030689 := bstep (se 2 (by rfl) ⟨3386508, by rfl⟩ : syracuseStep 9030689 = 6773017) B6773017
theorem B6020459 : Blo 1979435 6020459 := bstep (se 1 (by rfl) ⟨4515344, by rfl⟩ : syracuseStep 6020459 = 9030689) B9030689
theorem B4013639 : Blo 1979435 4013639 := bstep (se 1 (by rfl) ⟨3010229, by rfl⟩ : syracuseStep 4013639 = 6020459) B6020459
theorem B2675759 : Blo 1979435 2675759 := bstep (se 1 (by rfl) ⟨2006819, by rfl⟩ : syracuseStep 2675759 = 4013639) B4013639
theorem B28541429 : Blo 1979435 28541429 := bstep (se 5 (by rfl) ⟨1337879, by rfl⟩ : syracuseStep 28541429 = 2675759) B2675759
theorem B19027619 : Blo 1979435 19027619 := bstep (se 1 (by rfl) ⟨14270714, by rfl⟩ : syracuseStep 19027619 = 28541429) B28541429
theorem B12685079 : Blo 1979435 12685079 := bstep (se 1 (by rfl) ⟨9513809, by rfl⟩ : syracuseStep 12685079 = 19027619) B19027619
theorem B8456719 : Blo 1979435 8456719 := bstep (se 1 (by rfl) ⟨6342539, by rfl⟩ : syracuseStep 8456719 = 12685079) B12685079
theorem B11275625 : Blo 1979435 11275625 := bstep (se 2 (by rfl) ⟨4228359, by rfl⟩ : syracuseStep 11275625 = 8456719) B8456719
theorem B7517083 : Blo 1979435 7517083 := bstep (se 1 (by rfl) ⟨5637812, by rfl⟩ : syracuseStep 7517083 = 11275625) B11275625
theorem B10022777 : Blo 1979435 10022777 := bstep (se 2 (by rfl) ⟨3758541, by rfl⟩ : syracuseStep 10022777 = 7517083) B7517083
theorem B6681851 : Blo 1979435 6681851 := bstep (se 1 (by rfl) ⟨5011388, by rfl⟩ : syracuseStep 6681851 = 10022777) B10022777
theorem B4454567 : Blo 1979435 4454567 := bstep (se 1 (by rfl) ⟨3340925, by rfl⟩ : syracuseStep 4454567 = 6681851) B6681851
theorem B2969711 : Blo 1979435 2969711 := bstep (se 1 (by rfl) ⟨2227283, by rfl⟩ : syracuseStep 2969711 = 4454567) B4454567
theorem B1979807 : Blo 1979435 1979807 := bstep (se 1 (by rfl) ⟨1484855, by rfl⟩ : syracuseStep 1979807 = 2969711) B2969711
theorem B2969717 : Blo 1979435 2969717 := bbase (se 5 (by rfl) ⟨139205, by rfl⟩ : syracuseStep 2969717 = 278411) (by norm_num)
theorem B1979811 : Blo 1979435 1979811 := bstep (se 1 (by rfl) ⟨1484858, by rfl⟩ : syracuseStep 1979811 = 2969717) B2969717
theorem B3758557 : Blo 1979435 3758557 := bbase (se 3 (by rfl) ⟨704729, by rfl⟩ : syracuseStep 3758557 = 1409459) (by norm_num)
theorem B5011409 : Blo 1979435 5011409 := bstep (se 2 (by rfl) ⟨1879278, by rfl⟩ : syracuseStep 5011409 = 3758557) B3758557
theorem B3340939 : Blo 1979435 3340939 := bstep (se 1 (by rfl) ⟨2505704, by rfl⟩ : syracuseStep 3340939 = 5011409) B5011409
theorem B4454585 : Blo 1979435 4454585 := bstep (se 2 (by rfl) ⟨1670469, by rfl⟩ : syracuseStep 4454585 = 3340939) B3340939
theorem B2969723 : Blo 1979435 2969723 := bstep (se 1 (by rfl) ⟨2227292, by rfl⟩ : syracuseStep 2969723 = 4454585) B4454585
theorem B1979815 : Blo 1979435 1979815 := bstep (se 1 (by rfl) ⟨1484861, by rfl⟩ : syracuseStep 1979815 = 2969723) B2969723
theorem B2227297 : Blo 1979435 2227297 := bbase (se 2 (by rfl) ⟨835236, by rfl⟩ : syracuseStep 2227297 = 1670473) (by norm_num)
theorem B2969729 : Blo 1979435 2969729 := bstep (se 2 (by rfl) ⟨1113648, by rfl⟩ : syracuseStep 2969729 = 2227297) B2227297
theorem B1979819 : Blo 1979435 1979819 := bstep (se 1 (by rfl) ⟨1484864, by rfl⟩ : syracuseStep 1979819 = 2969729) B2969729
theorem B5011429 : Blo 1979435 5011429 := bbase (se 4 (by rfl) ⟨469821, by rfl⟩ : syracuseStep 5011429 = 939643) (by norm_num)
theorem B6681905 : Blo 1979435 6681905 := bstep (se 2 (by rfl) ⟨2505714, by rfl⟩ : syracuseStep 6681905 = 5011429) B5011429
theorem B4454603 : Blo 1979435 4454603 := bstep (se 1 (by rfl) ⟨3340952, by rfl⟩ : syracuseStep 4454603 = 6681905) B6681905
theorem B2969735 : Blo 1979435 2969735 := bstep (se 1 (by rfl) ⟨2227301, by rfl⟩ : syracuseStep 2969735 = 4454603) B4454603
theorem B1979823 : Blo 1979435 1979823 := bstep (se 1 (by rfl) ⟨1484867, by rfl⟩ : syracuseStep 1979823 = 2969735) B2969735
theorem B2969741 : Blo 1979435 2969741 := bbase (se 3 (by rfl) ⟨556826, by rfl⟩ : syracuseStep 2969741 = 1113653) (by norm_num)
theorem B1979827 : Blo 1979435 1979827 := bstep (se 1 (by rfl) ⟨1484870, by rfl⟩ : syracuseStep 1979827 = 2969741) B2969741
theorem B4454621 : Blo 1979435 4454621 := bbase (se 3 (by rfl) ⟨835241, by rfl⟩ : syracuseStep 4454621 = 1670483) (by norm_num)
theorem B2969747 : Blo 1979435 2969747 := bstep (se 1 (by rfl) ⟨2227310, by rfl⟩ : syracuseStep 2969747 = 4454621) B4454621
theorem B1979831 : Blo 1979435 1979831 := bstep (se 1 (by rfl) ⟨1484873, by rfl⟩ : syracuseStep 1979831 = 2969747) B2969747
theorem B3340973 : Blo 1979435 3340973 := bbase (se 3 (by rfl) ⟨626432, by rfl⟩ : syracuseStep 3340973 = 1252865) (by norm_num)
theorem B2227315 : Blo 1979435 2227315 := bstep (se 1 (by rfl) ⟨1670486, by rfl⟩ : syracuseStep 2227315 = 3340973) B3340973
theorem B2969753 : Blo 1979435 2969753 := bstep (se 2 (by rfl) ⟨1113657, by rfl⟩ : syracuseStep 2969753 = 2227315) B2227315
theorem B1979835 : Blo 1979435 1979835 := bstep (se 1 (by rfl) ⟨1484876, by rfl⟩ : syracuseStep 1979835 = 2969753) B2969753
theorem B7619765 : Blo 1979435 7619765 := bbase (se 5 (by rfl) ⟨357176, by rfl⟩ : syracuseStep 7619765 = 714353) (by norm_num)
theorem B20319373 : Blo 1979435 20319373 := bstep (se 3 (by rfl) ⟨3809882, by rfl⟩ : syracuseStep 20319373 = 7619765) B7619765
theorem B27092497 : Blo 1979435 27092497 := bstep (se 2 (by rfl) ⟨10159686, by rfl⟩ : syracuseStep 27092497 = 20319373) B20319373
theorem B36123329 : Blo 1979435 36123329 := bstep (se 2 (by rfl) ⟨13546248, by rfl⟩ : syracuseStep 36123329 = 27092497) B27092497
theorem B24082219 : Blo 1979435 24082219 := bstep (se 1 (by rfl) ⟨18061664, by rfl⟩ : syracuseStep 24082219 = 36123329) B36123329
theorem B32109625 : Blo 1979435 32109625 := bstep (se 2 (by rfl) ⟨12041109, by rfl⟩ : syracuseStep 32109625 = 24082219) B24082219
theorem B42812833 : Blo 1979435 42812833 := bstep (se 2 (by rfl) ⟨16054812, by rfl⟩ : syracuseStep 42812833 = 32109625) B32109625
theorem B57083777 : Blo 1979435 57083777 := bstep (se 2 (by rfl) ⟨21406416, by rfl⟩ : syracuseStep 57083777 = 42812833) B42812833
theorem B38055851 : Blo 1979435 38055851 := bstep (se 1 (by rfl) ⟨28541888, by rfl⟩ : syracuseStep 38055851 = 57083777) B57083777
theorem B25370567 : Blo 1979435 25370567 := bstep (se 1 (by rfl) ⟨19027925, by rfl⟩ : syracuseStep 25370567 = 38055851) B38055851
theorem B16913711 : Blo 1979435 16913711 := bstep (se 1 (by rfl) ⟨12685283, by rfl⟩ : syracuseStep 16913711 = 25370567) B25370567
theorem B11275807 : Blo 1979435 11275807 := bstep (se 1 (by rfl) ⟨8456855, by rfl⟩ : syracuseStep 11275807 = 16913711) B16913711
theorem B15034409 : Blo 1979435 15034409 := bstep (se 2 (by rfl) ⟨5637903, by rfl⟩ : syracuseStep 15034409 = 11275807) B11275807
theorem B10022939 : Blo 1979435 10022939 := bstep (se 1 (by rfl) ⟨7517204, by rfl⟩ : syracuseStep 10022939 = 15034409) B15034409
theorem B6681959 : Blo 1979435 6681959 := bstep (se 1 (by rfl) ⟨5011469, by rfl⟩ : syracuseStep 6681959 = 10022939) B10022939
theorem B4454639 : Blo 1979435 4454639 := bstep (se 1 (by rfl) ⟨3340979, by rfl⟩ : syracuseStep 4454639 = 6681959) B6681959
theorem B2969759 : Blo 1979435 2969759 := bstep (se 1 (by rfl) ⟨2227319, by rfl⟩ : syracuseStep 2969759 = 4454639) B4454639
theorem B1979839 : Blo 1979435 1979839 := bstep (se 1 (by rfl) ⟨1484879, by rfl⟩ : syracuseStep 1979839 = 2969759) B2969759
theorem B2969765 : Blo 1979435 2969765 := bbase (se 4 (by rfl) ⟨278415, by rfl⟩ : syracuseStep 2969765 = 556831) (by norm_num)
theorem B1979843 : Blo 1979435 1979843 := bstep (se 1 (by rfl) ⟨1484882, by rfl⟩ : syracuseStep 1979843 = 2969765) B2969765
theorem B2505745 : Blo 1979435 2505745 := bbase (se 2 (by rfl) ⟨939654, by rfl⟩ : syracuseStep 2505745 = 1879309) (by norm_num)
theorem B3340993 : Blo 1979435 3340993 := bstep (se 2 (by rfl) ⟨1252872, by rfl⟩ : syracuseStep 3340993 = 2505745) B2505745
theorem B4454657 : Blo 1979435 4454657 := bstep (se 2 (by rfl) ⟨1670496, by rfl⟩ : syracuseStep 4454657 = 3340993) B3340993
theorem B2969771 : Blo 1979435 2969771 := bstep (se 1 (by rfl) ⟨2227328, by rfl⟩ : syracuseStep 2969771 = 4454657) B4454657
theorem B1979847 : Blo 1979435 1979847 := bstep (se 1 (by rfl) ⟨1484885, by rfl⟩ : syracuseStep 1979847 = 2969771) B2969771
theorem B2227333 : Blo 1979435 2227333 := bbase (se 4 (by rfl) ⟨208812, by rfl⟩ : syracuseStep 2227333 = 417625) (by norm_num)
theorem B2969777 : Blo 1979435 2969777 := bstep (se 2 (by rfl) ⟨1113666, by rfl⟩ : syracuseStep 2969777 = 2227333) B2227333
theorem B1979851 : Blo 1979435 1979851 := bstep (se 1 (by rfl) ⟨1484888, by rfl⟩ : syracuseStep 1979851 = 2969777) B2969777
theorem B10298389 : Blo 1979435 10298389 := bbase (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) (by norm_num)
theorem B13731185 : Blo 1979435 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B36616493 : Blo 1979435 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B97643981 : Blo 1979435 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B65095987 : Blo 1979435 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B86794649 : Blo 1979435 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B57863099 : Blo 1979435 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B38575399 : Blo 1979435 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B51433865 : Blo 1979435 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B34289243 : Blo 1979435 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B22859495 : Blo 1979435 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B15239663 : Blo 1979435 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B10159775 : Blo 1979435 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B6773183 : Blo 1979435 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B4515455 : Blo 1979435 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B3010303 : Blo 1979435 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B16054949 : Blo 1979435 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B10703299 : Blo 1979435 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B14271065 : Blo 1979435 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B9514043 : Blo 1979435 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B6342695 : Blo 1979435 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B4228463 : Blo 1979435 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B2818975 : Blo 1979435 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B3758633 : Blo 1979435 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B2505755 : Blo 1979435 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B6682013 : Blo 1979435 6682013 := bstep (se 3 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 6682013 = 2505755) B2505755
theorem B4454675 : Blo 1979435 4454675 := bstep (se 1 (by rfl) ⟨3341006, by rfl⟩ : syracuseStep 4454675 = 6682013) B6682013
theorem B2969783 : Blo 1979435 2969783 := bstep (se 1 (by rfl) ⟨2227337, by rfl⟩ : syracuseStep 2969783 = 4454675) B4454675
theorem B1979855 : Blo 1979435 1979855 := bstep (se 1 (by rfl) ⟨1484891, by rfl⟩ : syracuseStep 1979855 = 2969783) B2969783
theorem B2969789 : Blo 1979435 2969789 := bbase (se 3 (by rfl) ⟨556835, by rfl⟩ : syracuseStep 2969789 = 1113671) (by norm_num)
theorem B1979859 : Blo 1979435 1979859 := bstep (se 1 (by rfl) ⟨1484894, by rfl⟩ : syracuseStep 1979859 = 2969789) B2969789
theorem B4454693 : Blo 1979435 4454693 := bbase (se 4 (by rfl) ⟨417627, by rfl⟩ : syracuseStep 4454693 = 835255) (by norm_num)
theorem B2969795 : Blo 1979435 2969795 := bstep (se 1 (by rfl) ⟨2227346, by rfl⟩ : syracuseStep 2969795 = 4454693) B4454693
theorem B1979863 : Blo 1979435 1979863 := bstep (se 1 (by rfl) ⟨1484897, by rfl⟩ : syracuseStep 1979863 = 2969795) B2969795
theorem B5011541 : Blo 1979435 5011541 := bbase (se 8 (by rfl) ⟨29364, by rfl⟩ : syracuseStep 5011541 = 58729) (by norm_num)
theorem B3341027 : Blo 1979435 3341027 := bstep (se 1 (by rfl) ⟨2505770, by rfl⟩ : syracuseStep 3341027 = 5011541) B5011541
theorem B2227351 : Blo 1979435 2227351 := bstep (se 1 (by rfl) ⟨1670513, by rfl⟩ : syracuseStep 2227351 = 3341027) B3341027
theorem B2969801 : Blo 1979435 2969801 := bstep (se 2 (by rfl) ⟨1113675, by rfl⟩ : syracuseStep 2969801 = 2227351) B2227351
theorem B1979867 : Blo 1979435 1979867 := bstep (se 1 (by rfl) ⟨1484900, by rfl⟩ : syracuseStep 1979867 = 2969801) B2969801
theorem B7135589 : Blo 1979435 7135589 := bbase (se 4 (by rfl) ⟨668961, by rfl⟩ : syracuseStep 7135589 = 1337923) (by norm_num)
theorem B4757059 : Blo 1979435 4757059 := bstep (se 1 (by rfl) ⟨3567794, by rfl⟩ : syracuseStep 4757059 = 7135589) B7135589
theorem B6342745 : Blo 1979435 6342745 := bstep (se 2 (by rfl) ⟨2378529, by rfl⟩ : syracuseStep 6342745 = 4757059) B4757059
theorem B8456993 : Blo 1979435 8456993 := bstep (se 2 (by rfl) ⟨3171372, by rfl⟩ : syracuseStep 8456993 = 6342745) B6342745
theorem B5637995 : Blo 1979435 5637995 := bstep (se 1 (by rfl) ⟨4228496, by rfl⟩ : syracuseStep 5637995 = 8456993) B8456993
theorem B3758663 : Blo 1979435 3758663 := bstep (se 1 (by rfl) ⟨2818997, by rfl⟩ : syracuseStep 3758663 = 5637995) B5637995
theorem B10023101 : Blo 1979435 10023101 := bstep (se 3 (by rfl) ⟨1879331, by rfl⟩ : syracuseStep 10023101 = 3758663) B3758663
theorem B6682067 : Blo 1979435 6682067 := bstep (se 1 (by rfl) ⟨5011550, by rfl⟩ : syracuseStep 6682067 = 10023101) B10023101
theorem B4454711 : Blo 1979435 4454711 := bstep (se 1 (by rfl) ⟨3341033, by rfl⟩ : syracuseStep 4454711 = 6682067) B6682067
theorem B2969807 : Blo 1979435 2969807 := bstep (se 1 (by rfl) ⟨2227355, by rfl⟩ : syracuseStep 2969807 = 4454711) B4454711
theorem B1979871 : Blo 1979435 1979871 := bstep (se 1 (by rfl) ⟨1484903, by rfl⟩ : syracuseStep 1979871 = 2969807) B2969807
theorem B2969813 : Blo 1979435 2969813 := bbase (se 7 (by rfl) ⟨34802, by rfl⟩ : syracuseStep 2969813 = 69605) (by norm_num)
theorem B1979875 : Blo 1979435 1979875 := bstep (se 1 (by rfl) ⟨1484906, by rfl⟩ : syracuseStep 1979875 = 2969813) B2969813
theorem B2114257 : Blo 1979435 2114257 := bbase (se 2 (by rfl) ⟨792846, by rfl⟩ : syracuseStep 2114257 = 1585693) (by norm_num)
theorem B2819009 : Blo 1979435 2819009 := bstep (se 2 (by rfl) ⟨1057128, by rfl⟩ : syracuseStep 2819009 = 2114257) B2114257
theorem B7517357 : Blo 1979435 7517357 := bstep (se 3 (by rfl) ⟨1409504, by rfl⟩ : syracuseStep 7517357 = 2819009) B2819009
theorem B5011571 : Blo 1979435 5011571 := bstep (se 1 (by rfl) ⟨3758678, by rfl⟩ : syracuseStep 5011571 = 7517357) B7517357
theorem B3341047 : Blo 1979435 3341047 := bstep (se 1 (by rfl) ⟨2505785, by rfl⟩ : syracuseStep 3341047 = 5011571) B5011571
theorem B4454729 : Blo 1979435 4454729 := bstep (se 2 (by rfl) ⟨1670523, by rfl⟩ : syracuseStep 4454729 = 3341047) B3341047
theorem B2969819 : Blo 1979435 2969819 := bstep (se 1 (by rfl) ⟨2227364, by rfl⟩ : syracuseStep 2969819 = 4454729) B4454729
theorem B1979879 : Blo 1979435 1979879 := bstep (se 1 (by rfl) ⟨1484909, by rfl⟩ : syracuseStep 1979879 = 2969819) B2969819
theorem B2227369 : Blo 1979435 2227369 := bbase (se 2 (by rfl) ⟨835263, by rfl⟩ : syracuseStep 2227369 = 1670527) (by norm_num)
theorem B2969825 : Blo 1979435 2969825 := bstep (se 2 (by rfl) ⟨1113684, by rfl⟩ : syracuseStep 2969825 = 2227369) B2227369
theorem B1979883 : Blo 1979435 1979883 := bstep (se 1 (by rfl) ⟨1484912, by rfl⟩ : syracuseStep 1979883 = 2969825) B2969825
theorem B8457061 : Blo 1979435 8457061 := bbase (se 4 (by rfl) ⟨792849, by rfl⟩ : syracuseStep 8457061 = 1585699) (by norm_num)
theorem B11276081 : Blo 1979435 11276081 := bstep (se 2 (by rfl) ⟨4228530, by rfl⟩ : syracuseStep 11276081 = 8457061) B8457061
theorem B7517387 : Blo 1979435 7517387 := bstep (se 1 (by rfl) ⟨5638040, by rfl⟩ : syracuseStep 7517387 = 11276081) B11276081
theorem B5011591 : Blo 1979435 5011591 := bstep (se 1 (by rfl) ⟨3758693, by rfl⟩ : syracuseStep 5011591 = 7517387) B7517387
theorem B6682121 : Blo 1979435 6682121 := bstep (se 2 (by rfl) ⟨2505795, by rfl⟩ : syracuseStep 6682121 = 5011591) B5011591
theorem B4454747 : Blo 1979435 4454747 := bstep (se 1 (by rfl) ⟨3341060, by rfl⟩ : syracuseStep 4454747 = 6682121) B6682121
theorem B2969831 : Blo 1979435 2969831 := bstep (se 1 (by rfl) ⟨2227373, by rfl⟩ : syracuseStep 2969831 = 4454747) B4454747
theorem B1979887 : Blo 1979435 1979887 := bstep (se 1 (by rfl) ⟨1484915, by rfl⟩ : syracuseStep 1979887 = 2969831) B2969831
theorem B2969837 : Blo 1979435 2969837 := bbase (se 3 (by rfl) ⟨556844, by rfl⟩ : syracuseStep 2969837 = 1113689) (by norm_num)
theorem B1979891 : Blo 1979435 1979891 := bstep (se 1 (by rfl) ⟨1484918, by rfl⟩ : syracuseStep 1979891 = 2969837) B2969837
theorem B4454765 : Blo 1979435 4454765 := bbase (se 3 (by rfl) ⟨835268, by rfl⟩ : syracuseStep 4454765 = 1670537) (by norm_num)
theorem B2969843 : Blo 1979435 2969843 := bstep (se 1 (by rfl) ⟨2227382, by rfl⟩ : syracuseStep 2969843 = 4454765) B4454765
theorem B1979895 : Blo 1979435 1979895 := bstep (se 1 (by rfl) ⟨1484921, by rfl⟩ : syracuseStep 1979895 = 2969843) B2969843
theorem B3758717 : Blo 1979435 3758717 := bbase (se 3 (by rfl) ⟨704759, by rfl⟩ : syracuseStep 3758717 = 1409519) (by norm_num)
theorem B2505811 : Blo 1979435 2505811 := bstep (se 1 (by rfl) ⟨1879358, by rfl⟩ : syracuseStep 2505811 = 3758717) B3758717
theorem B3341081 : Blo 1979435 3341081 := bstep (se 2 (by rfl) ⟨1252905, by rfl⟩ : syracuseStep 3341081 = 2505811) B2505811
theorem B2227387 : Blo 1979435 2227387 := bstep (se 1 (by rfl) ⟨1670540, by rfl⟩ : syracuseStep 2227387 = 3341081) B3341081
theorem B2969849 : Blo 1979435 2969849 := bstep (se 2 (by rfl) ⟨1113693, by rfl⟩ : syracuseStep 2969849 = 2227387) B2227387
theorem B1979899 : Blo 1979435 1979899 := bstep (se 1 (by rfl) ⟨1484924, by rfl⟩ : syracuseStep 1979899 = 2969849) B2969849
theorem B8572517 : Blo 1979435 8572517 := bbase (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) (by norm_num)
theorem B5715011 : Blo 1979435 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B3810007 : Blo 1979435 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B5080009 : Blo 1979435 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B6773345 : Blo 1979435 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B4515563 : Blo 1979435 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B3010375 : Blo 1979435 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B16055333 : Blo 1979435 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B10703555 : Blo 1979435 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B7135703 : Blo 1979435 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B4757135 : Blo 1979435 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B50742773 : Blo 1979435 50742773 := bstep (se 5 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 50742773 = 4757135) B4757135
theorem B33828515 : Blo 1979435 33828515 := bstep (se 1 (by rfl) ⟨25371386, by rfl⟩ : syracuseStep 33828515 = 50742773) B50742773
theorem B22552343 : Blo 1979435 22552343 := bstep (se 1 (by rfl) ⟨16914257, by rfl⟩ : syracuseStep 22552343 = 33828515) B33828515
theorem B15034895 : Blo 1979435 15034895 := bstep (se 1 (by rfl) ⟨11276171, by rfl⟩ : syracuseStep 15034895 = 22552343) B22552343
theorem B10023263 : Blo 1979435 10023263 := bstep (se 1 (by rfl) ⟨7517447, by rfl⟩ : syracuseStep 10023263 = 15034895) B15034895
theorem B6682175 : Blo 1979435 6682175 := bstep (se 1 (by rfl) ⟨5011631, by rfl⟩ : syracuseStep 6682175 = 10023263) B10023263
theorem B4454783 : Blo 1979435 4454783 := bstep (se 1 (by rfl) ⟨3341087, by rfl⟩ : syracuseStep 4454783 = 6682175) B6682175
theorem B2969855 : Blo 1979435 2969855 := bstep (se 1 (by rfl) ⟨2227391, by rfl⟩ : syracuseStep 2969855 = 4454783) B4454783
theorem B1979903 : Blo 1979435 1979903 := bstep (se 1 (by rfl) ⟨1484927, by rfl⟩ : syracuseStep 1979903 = 2969855) B2969855
theorem B2969861 : Blo 1979435 2969861 := bbase (se 4 (by rfl) ⟨278424, by rfl⟩ : syracuseStep 2969861 = 556849) (by norm_num)
theorem B1979907 : Blo 1979435 1979907 := bstep (se 1 (by rfl) ⟨1484930, by rfl⟩ : syracuseStep 1979907 = 2969861) B2969861
theorem B3341101 : Blo 1979435 3341101 := bbase (se 3 (by rfl) ⟨626456, by rfl⟩ : syracuseStep 3341101 = 1252913) (by norm_num)
theorem B4454801 : Blo 1979435 4454801 := bstep (se 2 (by rfl) ⟨1670550, by rfl⟩ : syracuseStep 4454801 = 3341101) B3341101
theorem B2969867 : Blo 1979435 2969867 := bstep (se 1 (by rfl) ⟨2227400, by rfl⟩ : syracuseStep 2969867 = 4454801) B4454801
theorem B1979911 : Blo 1979435 1979911 := bstep (se 1 (by rfl) ⟨1484933, by rfl⟩ : syracuseStep 1979911 = 2969867) B2969867
theorem B2227405 : Blo 1979435 2227405 := bbase (se 3 (by rfl) ⟨417638, by rfl⟩ : syracuseStep 2227405 = 835277) (by norm_num)
theorem B2969873 : Blo 1979435 2969873 := bstep (se 2 (by rfl) ⟨1113702, by rfl⟩ : syracuseStep 2969873 = 2227405) B2227405
theorem B1979915 : Blo 1979435 1979915 := bstep (se 1 (by rfl) ⟨1484936, by rfl⟩ : syracuseStep 1979915 = 2969873) B2969873
theorem B6682229 : Blo 1979435 6682229 := bbase (se 5 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 6682229 = 626459) (by norm_num)
theorem B4454819 : Blo 1979435 4454819 := bstep (se 1 (by rfl) ⟨3341114, by rfl⟩ : syracuseStep 4454819 = 6682229) B6682229
theorem B2969879 : Blo 1979435 2969879 := bstep (se 1 (by rfl) ⟨2227409, by rfl⟩ : syracuseStep 2969879 = 4454819) B4454819
theorem B1979919 : Blo 1979435 1979919 := bstep (se 1 (by rfl) ⟨1484939, by rfl⟩ : syracuseStep 1979919 = 2969879) B2969879
theorem B2969885 : Blo 1979435 2969885 := bbase (se 3 (by rfl) ⟨556853, by rfl⟩ : syracuseStep 2969885 = 1113707) (by norm_num)
theorem B1979923 : Blo 1979435 1979923 := bstep (se 1 (by rfl) ⟨1484942, by rfl⟩ : syracuseStep 1979923 = 2969885) B2969885
theorem B4454837 : Blo 1979435 4454837 := bbase (se 5 (by rfl) ⟨208820, by rfl⟩ : syracuseStep 4454837 = 417641) (by norm_num)
theorem B2969891 : Blo 1979435 2969891 := bstep (se 1 (by rfl) ⟨2227418, by rfl⟩ : syracuseStep 2969891 = 4454837) B4454837
theorem B1979927 : Blo 1979435 1979927 := bstep (se 1 (by rfl) ⟨1484945, by rfl⟩ : syracuseStep 1979927 = 2969891) B2969891
theorem B3171469 : Blo 1979435 3171469 := bbase (se 3 (by rfl) ⟨594650, by rfl⟩ : syracuseStep 3171469 = 1189301) (by norm_num)
theorem B4228625 : Blo 1979435 4228625 := bstep (se 2 (by rfl) ⟨1585734, by rfl⟩ : syracuseStep 4228625 = 3171469) B3171469
theorem B11276333 : Blo 1979435 11276333 := bstep (se 3 (by rfl) ⟨2114312, by rfl⟩ : syracuseStep 11276333 = 4228625) B4228625
theorem B7517555 : Blo 1979435 7517555 := bstep (se 1 (by rfl) ⟨5638166, by rfl⟩ : syracuseStep 7517555 = 11276333) B11276333
theorem B5011703 : Blo 1979435 5011703 := bstep (se 1 (by rfl) ⟨3758777, by rfl⟩ : syracuseStep 5011703 = 7517555) B7517555
theorem B3341135 : Blo 1979435 3341135 := bstep (se 1 (by rfl) ⟨2505851, by rfl⟩ : syracuseStep 3341135 = 5011703) B5011703
theorem B2227423 : Blo 1979435 2227423 := bstep (se 1 (by rfl) ⟨1670567, by rfl⟩ : syracuseStep 2227423 = 3341135) B3341135
theorem B2969897 : Blo 1979435 2969897 := bstep (se 2 (by rfl) ⟨1113711, by rfl⟩ : syracuseStep 2969897 = 2227423) B2227423
theorem B1979931 : Blo 1979435 1979931 := bstep (se 1 (by rfl) ⟨1484948, by rfl⟩ : syracuseStep 1979931 = 2969897) B2969897
theorem B4757213 : Blo 1979435 4757213 := bbase (se 3 (by rfl) ⟨891977, by rfl⟩ : syracuseStep 4757213 = 1783955) (by norm_num)
theorem B3171475 : Blo 1979435 3171475 := bstep (se 1 (by rfl) ⟨2378606, by rfl⟩ : syracuseStep 3171475 = 4757213) B4757213
theorem B4228633 : Blo 1979435 4228633 := bstep (se 2 (by rfl) ⟨1585737, by rfl⟩ : syracuseStep 4228633 = 3171475) B3171475
theorem B5638177 : Blo 1979435 5638177 := bstep (se 2 (by rfl) ⟨2114316, by rfl⟩ : syracuseStep 5638177 = 4228633) B4228633
theorem B7517569 : Blo 1979435 7517569 := bstep (se 2 (by rfl) ⟨2819088, by rfl⟩ : syracuseStep 7517569 = 5638177) B5638177
theorem B10023425 : Blo 1979435 10023425 := bstep (se 2 (by rfl) ⟨3758784, by rfl⟩ : syracuseStep 10023425 = 7517569) B7517569
theorem B6682283 : Blo 1979435 6682283 := bstep (se 1 (by rfl) ⟨5011712, by rfl⟩ : syracuseStep 6682283 = 10023425) B10023425
theorem B4454855 : Blo 1979435 4454855 := bstep (se 1 (by rfl) ⟨3341141, by rfl⟩ : syracuseStep 4454855 = 6682283) B6682283
theorem B2969903 : Blo 1979435 2969903 := bstep (se 1 (by rfl) ⟨2227427, by rfl⟩ : syracuseStep 2969903 = 4454855) B4454855
theorem B1979935 : Blo 1979435 1979935 := bstep (se 1 (by rfl) ⟨1484951, by rfl⟩ : syracuseStep 1979935 = 2969903) B2969903
theorem B2969909 : Blo 1979435 2969909 := bbase (se 5 (by rfl) ⟨139214, by rfl⟩ : syracuseStep 2969909 = 278429) (by norm_num)
theorem B1979939 : Blo 1979435 1979939 := bstep (se 1 (by rfl) ⟨1484954, by rfl⟩ : syracuseStep 1979939 = 2969909) B2969909
theorem B5011733 : Blo 1979435 5011733 := bbase (se 6 (by rfl) ⟨117462, by rfl⟩ : syracuseStep 5011733 = 234925) (by norm_num)
theorem B3341155 : Blo 1979435 3341155 := bstep (se 1 (by rfl) ⟨2505866, by rfl⟩ : syracuseStep 3341155 = 5011733) B5011733
theorem B4454873 : Blo 1979435 4454873 := bstep (se 2 (by rfl) ⟨1670577, by rfl⟩ : syracuseStep 4454873 = 3341155) B3341155
theorem B2969915 : Blo 1979435 2969915 := bstep (se 1 (by rfl) ⟨2227436, by rfl⟩ : syracuseStep 2969915 = 4454873) B4454873
theorem B1979943 : Blo 1979435 1979943 := bstep (se 1 (by rfl) ⟨1484957, by rfl⟩ : syracuseStep 1979943 = 2969915) B2969915
theorem B2227441 : Blo 1979435 2227441 := bbase (se 2 (by rfl) ⟨835290, by rfl⟩ : syracuseStep 2227441 = 1670581) (by norm_num)
theorem B2969921 : Blo 1979435 2969921 := bstep (se 2 (by rfl) ⟨1113720, by rfl⟩ : syracuseStep 2969921 = 2227441) B2227441
theorem B1979947 : Blo 1979435 1979947 := bstep (se 1 (by rfl) ⟨1484960, by rfl⟩ : syracuseStep 1979947 = 2969921) B2969921
theorem B7135877 : Blo 1979435 7135877 := bbase (se 4 (by rfl) ⟨668988, by rfl⟩ : syracuseStep 7135877 = 1337977) (by norm_num)
theorem B19029005 : Blo 1979435 19029005 := bstep (se 3 (by rfl) ⟨3567938, by rfl⟩ : syracuseStep 19029005 = 7135877) B7135877
theorem B12686003 : Blo 1979435 12686003 := bstep (se 1 (by rfl) ⟨9514502, by rfl⟩ : syracuseStep 12686003 = 19029005) B19029005
theorem B8457335 : Blo 1979435 8457335 := bstep (se 1 (by rfl) ⟨6343001, by rfl⟩ : syracuseStep 8457335 = 12686003) B12686003
theorem B5638223 : Blo 1979435 5638223 := bstep (se 1 (by rfl) ⟨4228667, by rfl⟩ : syracuseStep 5638223 = 8457335) B8457335
theorem B3758815 : Blo 1979435 3758815 := bstep (se 1 (by rfl) ⟨2819111, by rfl⟩ : syracuseStep 3758815 = 5638223) B5638223
theorem B5011753 : Blo 1979435 5011753 := bstep (se 2 (by rfl) ⟨1879407, by rfl⟩ : syracuseStep 5011753 = 3758815) B3758815
theorem B6682337 : Blo 1979435 6682337 := bstep (se 2 (by rfl) ⟨2505876, by rfl⟩ : syracuseStep 6682337 = 5011753) B5011753
theorem B4454891 : Blo 1979435 4454891 := bstep (se 1 (by rfl) ⟨3341168, by rfl⟩ : syracuseStep 4454891 = 6682337) B6682337
theorem B2969927 : Blo 1979435 2969927 := bstep (se 1 (by rfl) ⟨2227445, by rfl⟩ : syracuseStep 2969927 = 4454891) B4454891
theorem B1979951 : Blo 1979435 1979951 := bstep (se 1 (by rfl) ⟨1484963, by rfl⟩ : syracuseStep 1979951 = 2969927) B2969927
theorem B2969933 : Blo 1979435 2969933 := bbase (se 3 (by rfl) ⟨556862, by rfl⟩ : syracuseStep 2969933 = 1113725) (by norm_num)
theorem B1979955 : Blo 1979435 1979955 := bstep (se 1 (by rfl) ⟨1484966, by rfl⟩ : syracuseStep 1979955 = 2969933) B2969933
theorem B4454909 : Blo 1979435 4454909 := bbase (se 3 (by rfl) ⟨835295, by rfl⟩ : syracuseStep 4454909 = 1670591) (by norm_num)
theorem B2969939 : Blo 1979435 2969939 := bstep (se 1 (by rfl) ⟨2227454, by rfl⟩ : syracuseStep 2969939 = 4454909) B4454909
theorem B1979959 : Blo 1979435 1979959 := bstep (se 1 (by rfl) ⟨1484969, by rfl⟩ : syracuseStep 1979959 = 2969939) B2969939
theorem B3341189 : Blo 1979435 3341189 := bbase (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) (by norm_num)
theorem B2227459 : Blo 1979435 2227459 := bstep (se 1 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 2227459 = 3341189) B3341189
theorem B2969945 : Blo 1979435 2969945 := bstep (se 2 (by rfl) ⟨1113729, by rfl⟩ : syracuseStep 2969945 = 2227459) B2227459
theorem B1979963 : Blo 1979435 1979963 := bstep (se 1 (by rfl) ⟨1484972, by rfl⟩ : syracuseStep 1979963 = 2969945) B2969945
theorem B15035381 : Blo 1979435 15035381 := bbase (se 5 (by rfl) ⟨704783, by rfl⟩ : syracuseStep 15035381 = 1409567) (by norm_num)
theorem B10023587 : Blo 1979435 10023587 := bstep (se 1 (by rfl) ⟨7517690, by rfl⟩ : syracuseStep 10023587 = 15035381) B15035381
theorem B6682391 : Blo 1979435 6682391 := bstep (se 1 (by rfl) ⟨5011793, by rfl⟩ : syracuseStep 6682391 = 10023587) B10023587
theorem B4454927 : Blo 1979435 4454927 := bstep (se 1 (by rfl) ⟨3341195, by rfl⟩ : syracuseStep 4454927 = 6682391) B6682391
theorem B2969951 : Blo 1979435 2969951 := bstep (se 1 (by rfl) ⟨2227463, by rfl⟩ : syracuseStep 2969951 = 4454927) B4454927
theorem B1979967 : Blo 1979435 1979967 := bstep (se 1 (by rfl) ⟨1484975, by rfl⟩ : syracuseStep 1979967 = 2969951) B2969951
theorem B2969957 : Blo 1979435 2969957 := bbase (se 4 (by rfl) ⟨278433, by rfl⟩ : syracuseStep 2969957 = 556867) (by norm_num)
theorem B1979971 : Blo 1979435 1979971 := bstep (se 1 (by rfl) ⟨1484978, by rfl⟩ : syracuseStep 1979971 = 2969957) B2969957
theorem B3758861 : Blo 1979435 3758861 := bbase (se 3 (by rfl) ⟨704786, by rfl⟩ : syracuseStep 3758861 = 1409573) (by norm_num)
theorem B2505907 : Blo 1979435 2505907 := bstep (se 1 (by rfl) ⟨1879430, by rfl⟩ : syracuseStep 2505907 = 3758861) B3758861
theorem B3341209 : Blo 1979435 3341209 := bstep (se 2 (by rfl) ⟨1252953, by rfl⟩ : syracuseStep 3341209 = 2505907) B2505907
theorem B4454945 : Blo 1979435 4454945 := bstep (se 2 (by rfl) ⟨1670604, by rfl⟩ : syracuseStep 4454945 = 3341209) B3341209
theorem B2969963 : Blo 1979435 2969963 := bstep (se 1 (by rfl) ⟨2227472, by rfl⟩ : syracuseStep 2969963 = 4454945) B4454945
theorem B1979975 : Blo 1979435 1979975 := bstep (se 1 (by rfl) ⟨1484981, by rfl⟩ : syracuseStep 1979975 = 2969963) B2969963
theorem B2227477 : Blo 1979435 2227477 := bbase (se 6 (by rfl) ⟨52206, by rfl⟩ : syracuseStep 2227477 = 104413) (by norm_num)
theorem B2969969 : Blo 1979435 2969969 := bstep (se 2 (by rfl) ⟨1113738, by rfl⟩ : syracuseStep 2969969 = 2227477) B2227477
theorem B1979979 : Blo 1979435 1979979 := bstep (se 1 (by rfl) ⟨1484984, by rfl⟩ : syracuseStep 1979979 = 2969969) B2969969
theorem B2505917 : Blo 1979435 2505917 := bbase (se 3 (by rfl) ⟨469859, by rfl⟩ : syracuseStep 2505917 = 939719) (by norm_num)
theorem B6682445 : Blo 1979435 6682445 := bstep (se 3 (by rfl) ⟨1252958, by rfl⟩ : syracuseStep 6682445 = 2505917) B2505917
theorem B4454963 : Blo 1979435 4454963 := bstep (se 1 (by rfl) ⟨3341222, by rfl⟩ : syracuseStep 4454963 = 6682445) B6682445
theorem B2969975 : Blo 1979435 2969975 := bstep (se 1 (by rfl) ⟨2227481, by rfl⟩ : syracuseStep 2969975 = 4454963) B4454963
theorem B1979983 : Blo 1979435 1979983 := bstep (se 1 (by rfl) ⟨1484987, by rfl⟩ : syracuseStep 1979983 = 2969975) B2969975
theorem B2969981 : Blo 1979435 2969981 := bbase (se 3 (by rfl) ⟨556871, by rfl⟩ : syracuseStep 2969981 = 1113743) (by norm_num)
theorem B1979987 : Blo 1979435 1979987 := bstep (se 1 (by rfl) ⟨1484990, by rfl⟩ : syracuseStep 1979987 = 2969981) B2969981
theorem B4454981 : Blo 1979435 4454981 := bbase (se 4 (by rfl) ⟨417654, by rfl⟩ : syracuseStep 4454981 = 835309) (by norm_num)
theorem B2969987 : Blo 1979435 2969987 := bstep (se 1 (by rfl) ⟨2227490, by rfl⟩ : syracuseStep 2969987 = 4454981) B4454981
theorem B1979991 : Blo 1979435 1979991 := bstep (se 1 (by rfl) ⟨1484993, by rfl⟩ : syracuseStep 1979991 = 2969987) B2969987
theorem B2114381 : Blo 1979435 2114381 := bbase (se 3 (by rfl) ⟨396446, by rfl⟩ : syracuseStep 2114381 = 792893) (by norm_num)
theorem B5638349 : Blo 1979435 5638349 := bstep (se 3 (by rfl) ⟨1057190, by rfl⟩ : syracuseStep 5638349 = 2114381) B2114381
theorem B3758899 : Blo 1979435 3758899 := bstep (se 1 (by rfl) ⟨2819174, by rfl⟩ : syracuseStep 3758899 = 5638349) B5638349
theorem B5011865 : Blo 1979435 5011865 := bstep (se 2 (by rfl) ⟨1879449, by rfl⟩ : syracuseStep 5011865 = 3758899) B3758899
theorem B3341243 : Blo 1979435 3341243 := bstep (se 1 (by rfl) ⟨2505932, by rfl⟩ : syracuseStep 3341243 = 5011865) B5011865
theorem B2227495 : Blo 1979435 2227495 := bstep (se 1 (by rfl) ⟨1670621, by rfl⟩ : syracuseStep 2227495 = 3341243) B3341243
theorem B2969993 : Blo 1979435 2969993 := bstep (se 2 (by rfl) ⟨1113747, by rfl⟩ : syracuseStep 2969993 = 2227495) B2227495
theorem B1979995 : Blo 1979435 1979995 := bstep (se 1 (by rfl) ⟨1484996, by rfl⟩ : syracuseStep 1979995 = 2969993) B2969993
theorem B10023749 : Blo 1979435 10023749 := bbase (se 4 (by rfl) ⟨939726, by rfl⟩ : syracuseStep 10023749 = 1879453) (by norm_num)
theorem B6682499 : Blo 1979435 6682499 := bstep (se 1 (by rfl) ⟨5011874, by rfl⟩ : syracuseStep 6682499 = 10023749) B10023749
theorem B4454999 : Blo 1979435 4454999 := bstep (se 1 (by rfl) ⟨3341249, by rfl⟩ : syracuseStep 4454999 = 6682499) B6682499
theorem B2969999 : Blo 1979435 2969999 := bstep (se 1 (by rfl) ⟨2227499, by rfl⟩ : syracuseStep 2969999 = 4454999) B4454999
theorem B1979999 : Blo 1979435 1979999 := bstep (se 1 (by rfl) ⟨1484999, by rfl⟩ : syracuseStep 1979999 = 2969999) B2969999
theorem B2970005 : Blo 1979435 2970005 := bbase (se 6 (by rfl) ⟨69609, by rfl⟩ : syracuseStep 2970005 = 139219) (by norm_num)
theorem B1980003 : Blo 1979435 1980003 := bstep (se 1 (by rfl) ⟨1485002, by rfl⟩ : syracuseStep 1980003 = 2970005) B2970005
theorem B2378693 : Blo 1979435 2378693 := bbase (se 4 (by rfl) ⟨223002, by rfl⟩ : syracuseStep 2378693 = 446005) (by norm_num)
theorem B6343181 : Blo 1979435 6343181 := bstep (se 3 (by rfl) ⟨1189346, by rfl⟩ : syracuseStep 6343181 = 2378693) B2378693
theorem B4228787 : Blo 1979435 4228787 := bstep (se 1 (by rfl) ⟨3171590, by rfl⟩ : syracuseStep 4228787 = 6343181) B6343181
theorem B11276765 : Blo 1979435 11276765 := bstep (se 3 (by rfl) ⟨2114393, by rfl⟩ : syracuseStep 11276765 = 4228787) B4228787
theorem B7517843 : Blo 1979435 7517843 := bstep (se 1 (by rfl) ⟨5638382, by rfl⟩ : syracuseStep 7517843 = 11276765) B11276765
theorem B5011895 : Blo 1979435 5011895 := bstep (se 1 (by rfl) ⟨3758921, by rfl⟩ : syracuseStep 5011895 = 7517843) B7517843
theorem B3341263 : Blo 1979435 3341263 := bstep (se 1 (by rfl) ⟨2505947, by rfl⟩ : syracuseStep 3341263 = 5011895) B5011895
theorem B4455017 : Blo 1979435 4455017 := bstep (se 2 (by rfl) ⟨1670631, by rfl⟩ : syracuseStep 4455017 = 3341263) B3341263
theorem B2970011 : Blo 1979435 2970011 := bstep (se 1 (by rfl) ⟨2227508, by rfl⟩ : syracuseStep 2970011 = 4455017) B4455017
theorem B1980007 : Blo 1979435 1980007 := bstep (se 1 (by rfl) ⟨1485005, by rfl⟩ : syracuseStep 1980007 = 2970011) B2970011
theorem B2227513 : Blo 1979435 2227513 := bbase (se 2 (by rfl) ⟨835317, by rfl⟩ : syracuseStep 2227513 = 1670635) (by norm_num)
theorem B2970017 : Blo 1979435 2970017 := bstep (se 2 (by rfl) ⟨1113756, by rfl⟩ : syracuseStep 2970017 = 2227513) B2227513
theorem B1980011 : Blo 1979435 1980011 := bstep (se 1 (by rfl) ⟨1485008, by rfl⟩ : syracuseStep 1980011 = 2970017) B2970017
theorem B5638405 : Blo 1979435 5638405 := bbase (se 4 (by rfl) ⟨528600, by rfl⟩ : syracuseStep 5638405 = 1057201) (by norm_num)
theorem B7517873 : Blo 1979435 7517873 := bstep (se 2 (by rfl) ⟨2819202, by rfl⟩ : syracuseStep 7517873 = 5638405) B5638405
theorem B5011915 : Blo 1979435 5011915 := bstep (se 1 (by rfl) ⟨3758936, by rfl⟩ : syracuseStep 5011915 = 7517873) B7517873
theorem B6682553 : Blo 1979435 6682553 := bstep (se 2 (by rfl) ⟨2505957, by rfl⟩ : syracuseStep 6682553 = 5011915) B5011915
theorem B4455035 : Blo 1979435 4455035 := bstep (se 1 (by rfl) ⟨3341276, by rfl⟩ : syracuseStep 4455035 = 6682553) B6682553
theorem B2970023 : Blo 1979435 2970023 := bstep (se 1 (by rfl) ⟨2227517, by rfl⟩ : syracuseStep 2970023 = 4455035) B4455035
theorem B1980015 : Blo 1979435 1980015 := bstep (se 1 (by rfl) ⟨1485011, by rfl⟩ : syracuseStep 1980015 = 2970023) B2970023
theorem B2970029 : Blo 1979435 2970029 := bbase (se 3 (by rfl) ⟨556880, by rfl⟩ : syracuseStep 2970029 = 1113761) (by norm_num)
theorem B1980019 : Blo 1979435 1980019 := bstep (se 1 (by rfl) ⟨1485014, by rfl⟩ : syracuseStep 1980019 = 2970029) B2970029
theorem B4455053 : Blo 1979435 4455053 := bbase (se 3 (by rfl) ⟨835322, by rfl⟩ : syracuseStep 4455053 = 1670645) (by norm_num)
theorem B2970035 : Blo 1979435 2970035 := bstep (se 1 (by rfl) ⟨2227526, by rfl⟩ : syracuseStep 2970035 = 4455053) B4455053
theorem B1980023 : Blo 1979435 1980023 := bstep (se 1 (by rfl) ⟨1485017, by rfl⟩ : syracuseStep 1980023 = 2970035) B2970035
theorem B2505973 : Blo 1979435 2505973 := bbase (se 5 (by rfl) ⟨117467, by rfl⟩ : syracuseStep 2505973 = 234935) (by norm_num)
theorem B3341297 : Blo 1979435 3341297 := bstep (se 2 (by rfl) ⟨1252986, by rfl⟩ : syracuseStep 3341297 = 2505973) B2505973
theorem B2227531 : Blo 1979435 2227531 := bstep (se 1 (by rfl) ⟨1670648, by rfl⟩ : syracuseStep 2227531 = 3341297) B3341297
theorem B2970041 : Blo 1979435 2970041 := bstep (se 2 (by rfl) ⟨1113765, by rfl⟩ : syracuseStep 2970041 = 2227531) B2227531
theorem B1980027 : Blo 1979435 1980027 := bstep (se 1 (by rfl) ⟨1485020, by rfl⟩ : syracuseStep 1980027 = 2970041) B2970041
theorem B38059541 : Blo 1979435 38059541 := bbase (se 6 (by rfl) ⟨892020, by rfl⟩ : syracuseStep 38059541 = 1784041) (by norm_num)
theorem B25373027 : Blo 1979435 25373027 := bstep (se 1 (by rfl) ⟨19029770, by rfl⟩ : syracuseStep 25373027 = 38059541) B38059541
theorem B16915351 : Blo 1979435 16915351 := bstep (se 1 (by rfl) ⟨12686513, by rfl⟩ : syracuseStep 16915351 = 25373027) B25373027
theorem B22553801 : Blo 1979435 22553801 := bstep (se 2 (by rfl) ⟨8457675, by rfl⟩ : syracuseStep 22553801 = 16915351) B16915351
theorem B15035867 : Blo 1979435 15035867 := bstep (se 1 (by rfl) ⟨11276900, by rfl⟩ : syracuseStep 15035867 = 22553801) B22553801
theorem B10023911 : Blo 1979435 10023911 := bstep (se 1 (by rfl) ⟨7517933, by rfl⟩ : syracuseStep 10023911 = 15035867) B15035867
theorem B6682607 : Blo 1979435 6682607 := bstep (se 1 (by rfl) ⟨5011955, by rfl⟩ : syracuseStep 6682607 = 10023911) B10023911
theorem B4455071 : Blo 1979435 4455071 := bstep (se 1 (by rfl) ⟨3341303, by rfl⟩ : syracuseStep 4455071 = 6682607) B6682607
theorem B2970047 : Blo 1979435 2970047 := bstep (se 1 (by rfl) ⟨2227535, by rfl⟩ : syracuseStep 2970047 = 4455071) B4455071
theorem B1980031 : Blo 1979435 1980031 := bstep (se 1 (by rfl) ⟨1485023, by rfl⟩ : syracuseStep 1980031 = 2970047) B2970047
theorem B2970053 : Blo 1979435 2970053 := bbase (se 4 (by rfl) ⟨278442, by rfl⟩ : syracuseStep 2970053 = 556885) (by norm_num)
theorem B1980035 : Blo 1979435 1980035 := bstep (se 1 (by rfl) ⟨1485026, by rfl⟩ : syracuseStep 1980035 = 2970053) B2970053
theorem B3341317 : Blo 1979435 3341317 := bbase (se 4 (by rfl) ⟨313248, by rfl⟩ : syracuseStep 3341317 = 626497) (by norm_num)
theorem B4455089 : Blo 1979435 4455089 := bstep (se 2 (by rfl) ⟨1670658, by rfl⟩ : syracuseStep 4455089 = 3341317) B3341317
theorem B2970059 : Blo 1979435 2970059 := bstep (se 1 (by rfl) ⟨2227544, by rfl⟩ : syracuseStep 2970059 = 4455089) B4455089
theorem B1980039 : Blo 1979435 1980039 := bstep (se 1 (by rfl) ⟨1485029, by rfl⟩ : syracuseStep 1980039 = 2970059) B2970059
theorem B2227549 : Blo 1979435 2227549 := bbase (se 3 (by rfl) ⟨417665, by rfl⟩ : syracuseStep 2227549 = 835331) (by norm_num)
theorem B2970065 : Blo 1979435 2970065 := bstep (se 2 (by rfl) ⟨1113774, by rfl⟩ : syracuseStep 2970065 = 2227549) B2227549
theorem B1980043 : Blo 1979435 1980043 := bstep (se 1 (by rfl) ⟨1485032, by rfl⟩ : syracuseStep 1980043 = 2970065) B2970065
theorem B6682661 : Blo 1979435 6682661 := bbase (se 4 (by rfl) ⟨626499, by rfl⟩ : syracuseStep 6682661 = 1252999) (by norm_num)
theorem B4455107 : Blo 1979435 4455107 := bstep (se 1 (by rfl) ⟨3341330, by rfl⟩ : syracuseStep 4455107 = 6682661) B6682661
theorem B2970071 : Blo 1979435 2970071 := bstep (se 1 (by rfl) ⟨2227553, by rfl⟩ : syracuseStep 2970071 = 4455107) B4455107
theorem B1980047 : Blo 1979435 1980047 := bstep (se 1 (by rfl) ⟨1485035, by rfl⟩ : syracuseStep 1980047 = 2970071) B2970071
theorem B2970077 : Blo 1979435 2970077 := bbase (se 3 (by rfl) ⟨556889, by rfl⟩ : syracuseStep 2970077 = 1113779) (by norm_num)
theorem B1980051 : Blo 1979435 1980051 := bstep (se 1 (by rfl) ⟨1485038, by rfl⟩ : syracuseStep 1980051 = 2970077) B2970077
theorem B4455125 : Blo 1979435 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B2970083 : Blo 1979435 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B1980055 : Blo 1979435 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B8457797 : Blo 1979435 8457797 := bbase (se 4 (by rfl) ⟨792918, by rfl⟩ : syracuseStep 8457797 = 1585837) (by norm_num)
theorem B5638531 : Blo 1979435 5638531 := bstep (se 1 (by rfl) ⟨4228898, by rfl⟩ : syracuseStep 5638531 = 8457797) B8457797
theorem B7518041 : Blo 1979435 7518041 := bstep (se 2 (by rfl) ⟨2819265, by rfl⟩ : syracuseStep 7518041 = 5638531) B5638531
theorem B5012027 : Blo 1979435 5012027 := bstep (se 1 (by rfl) ⟨3759020, by rfl⟩ : syracuseStep 5012027 = 7518041) B7518041
theorem B3341351 : Blo 1979435 3341351 := bstep (se 1 (by rfl) ⟨2506013, by rfl⟩ : syracuseStep 3341351 = 5012027) B5012027
theorem B2227567 : Blo 1979435 2227567 := bstep (se 1 (by rfl) ⟨1670675, by rfl⟩ : syracuseStep 2227567 = 3341351) B3341351
theorem B2970089 : Blo 1979435 2970089 := bstep (se 2 (by rfl) ⟨1113783, by rfl⟩ : syracuseStep 2970089 = 2227567) B2227567
theorem B1980059 : Blo 1979435 1980059 := bstep (se 1 (by rfl) ⟨1485044, by rfl⟩ : syracuseStep 1980059 = 2970089) B2970089
theorem B4822429 : Blo 1979435 4822429 := bbase (se 3 (by rfl) ⟨904205, by rfl⟩ : syracuseStep 4822429 = 1808411) (by norm_num)
theorem B6429905 : Blo 1979435 6429905 := bstep (se 2 (by rfl) ⟨2411214, by rfl⟩ : syracuseStep 6429905 = 4822429) B4822429
theorem B4286603 : Blo 1979435 4286603 := bstep (se 1 (by rfl) ⟨3214952, by rfl⟩ : syracuseStep 4286603 = 6429905) B6429905
theorem B11430941 : Blo 1979435 11430941 := bstep (se 3 (by rfl) ⟨2143301, by rfl⟩ : syracuseStep 11430941 = 4286603) B4286603
theorem B30482509 : Blo 1979435 30482509 := bstep (se 3 (by rfl) ⟨5715470, by rfl⟩ : syracuseStep 30482509 = 11430941) B11430941
theorem B40643345 : Blo 1979435 40643345 := bstep (se 2 (by rfl) ⟨15241254, by rfl⟩ : syracuseStep 40643345 = 30482509) B30482509
theorem B27095563 : Blo 1979435 27095563 := bstep (se 1 (by rfl) ⟨20321672, by rfl⟩ : syracuseStep 27095563 = 40643345) B40643345
theorem B144509669 : Blo 1979435 144509669 := bstep (se 4 (by rfl) ⟨13547781, by rfl⟩ : syracuseStep 144509669 = 27095563) B27095563
theorem B96339779 : Blo 1979435 96339779 := bstep (se 1 (by rfl) ⟨72254834, by rfl⟩ : syracuseStep 96339779 = 144509669) B144509669
theorem B64226519 : Blo 1979435 64226519 := bstep (se 1 (by rfl) ⟨48169889, by rfl⟩ : syracuseStep 64226519 = 96339779) B96339779
theorem B42817679 : Blo 1979435 42817679 := bstep (se 1 (by rfl) ⟨32113259, by rfl⟩ : syracuseStep 42817679 = 64226519) B64226519
theorem B28545119 : Blo 1979435 28545119 := bstep (se 1 (by rfl) ⟨21408839, by rfl⟩ : syracuseStep 28545119 = 42817679) B42817679
theorem B19030079 : Blo 1979435 19030079 := bstep (se 1 (by rfl) ⟨14272559, by rfl⟩ : syracuseStep 19030079 = 28545119) B28545119
theorem B12686719 : Blo 1979435 12686719 := bstep (se 1 (by rfl) ⟨9515039, by rfl⟩ : syracuseStep 12686719 = 19030079) B19030079
theorem B16915625 : Blo 1979435 16915625 := bstep (se 2 (by rfl) ⟨6343359, by rfl⟩ : syracuseStep 16915625 = 12686719) B12686719
theorem B11277083 : Blo 1979435 11277083 := bstep (se 1 (by rfl) ⟨8457812, by rfl⟩ : syracuseStep 11277083 = 16915625) B16915625
theorem B7518055 : Blo 1979435 7518055 := bstep (se 1 (by rfl) ⟨5638541, by rfl⟩ : syracuseStep 7518055 = 11277083) B11277083
theorem B10024073 : Blo 1979435 10024073 := bstep (se 2 (by rfl) ⟨3759027, by rfl⟩ : syracuseStep 10024073 = 7518055) B7518055
theorem B6682715 : Blo 1979435 6682715 := bstep (se 1 (by rfl) ⟨5012036, by rfl⟩ : syracuseStep 6682715 = 10024073) B10024073
theorem B4455143 : Blo 1979435 4455143 := bstep (se 1 (by rfl) ⟨3341357, by rfl⟩ : syracuseStep 4455143 = 6682715) B6682715
theorem B2970095 : Blo 1979435 2970095 := bstep (se 1 (by rfl) ⟨2227571, by rfl⟩ : syracuseStep 2970095 = 4455143) B4455143
theorem B1980063 : Blo 1979435 1980063 := bstep (se 1 (by rfl) ⟨1485047, by rfl⟩ : syracuseStep 1980063 = 2970095) B2970095
theorem B2970101 : Blo 1979435 2970101 := bbase (se 5 (by rfl) ⟨139223, by rfl⟩ : syracuseStep 2970101 = 278447) (by norm_num)
theorem B1980067 : Blo 1979435 1980067 := bstep (se 1 (by rfl) ⟨1485050, by rfl⟩ : syracuseStep 1980067 = 2970101) B2970101
theorem B5638565 : Blo 1979435 5638565 := bbase (se 4 (by rfl) ⟨528615, by rfl⟩ : syracuseStep 5638565 = 1057231) (by norm_num)
theorem B3759043 : Blo 1979435 3759043 := bstep (se 1 (by rfl) ⟨2819282, by rfl⟩ : syracuseStep 3759043 = 5638565) B5638565
theorem B5012057 : Blo 1979435 5012057 := bstep (se 2 (by rfl) ⟨1879521, by rfl⟩ : syracuseStep 5012057 = 3759043) B3759043
theorem B3341371 : Blo 1979435 3341371 := bstep (se 1 (by rfl) ⟨2506028, by rfl⟩ : syracuseStep 3341371 = 5012057) B5012057
theorem B4455161 : Blo 1979435 4455161 := bstep (se 2 (by rfl) ⟨1670685, by rfl⟩ : syracuseStep 4455161 = 3341371) B3341371
theorem B2970107 : Blo 1979435 2970107 := bstep (se 1 (by rfl) ⟨2227580, by rfl⟩ : syracuseStep 2970107 = 4455161) B4455161
theorem B1980071 : Blo 1979435 1980071 := bstep (se 1 (by rfl) ⟨1485053, by rfl⟩ : syracuseStep 1980071 = 2970107) B2970107
theorem B2227585 : Blo 1979435 2227585 := bbase (se 2 (by rfl) ⟨835344, by rfl⟩ : syracuseStep 2227585 = 1670689) (by norm_num)
theorem B2970113 : Blo 1979435 2970113 := bstep (se 2 (by rfl) ⟨1113792, by rfl⟩ : syracuseStep 2970113 = 2227585) B2227585
theorem B1980075 : Blo 1979435 1980075 := bstep (se 1 (by rfl) ⟨1485056, by rfl⟩ : syracuseStep 1980075 = 2970113) B2970113
theorem B5012077 : Blo 1979435 5012077 := bbase (se 3 (by rfl) ⟨939764, by rfl⟩ : syracuseStep 5012077 = 1879529) (by norm_num)
theorem B6682769 : Blo 1979435 6682769 := bstep (se 2 (by rfl) ⟨2506038, by rfl⟩ : syracuseStep 6682769 = 5012077) B5012077
theorem B4455179 : Blo 1979435 4455179 := bstep (se 1 (by rfl) ⟨3341384, by rfl⟩ : syracuseStep 4455179 = 6682769) B6682769
theorem B2970119 : Blo 1979435 2970119 := bstep (se 1 (by rfl) ⟨2227589, by rfl⟩ : syracuseStep 2970119 = 4455179) B4455179
theorem B1980079 : Blo 1979435 1980079 := bstep (se 1 (by rfl) ⟨1485059, by rfl⟩ : syracuseStep 1980079 = 2970119) B2970119
theorem B2970125 : Blo 1979435 2970125 := bbase (se 3 (by rfl) ⟨556898, by rfl⟩ : syracuseStep 2970125 = 1113797) (by norm_num)
theorem B1980083 : Blo 1979435 1980083 := bstep (se 1 (by rfl) ⟨1485062, by rfl⟩ : syracuseStep 1980083 = 2970125) B2970125
theorem B4455197 : Blo 1979435 4455197 := bbase (se 3 (by rfl) ⟨835349, by rfl⟩ : syracuseStep 4455197 = 1670699) (by norm_num)
theorem B2970131 : Blo 1979435 2970131 := bstep (se 1 (by rfl) ⟨2227598, by rfl⟩ : syracuseStep 2970131 = 4455197) B4455197
theorem B1980087 : Blo 1979435 1980087 := bstep (se 1 (by rfl) ⟨1485065, by rfl⟩ : syracuseStep 1980087 = 2970131) B2970131
theorem B3341405 : Blo 1979435 3341405 := bbase (se 3 (by rfl) ⟨626513, by rfl⟩ : syracuseStep 3341405 = 1253027) (by norm_num)
theorem B2227603 : Blo 1979435 2227603 := bstep (se 1 (by rfl) ⟨1670702, by rfl⟩ : syracuseStep 2227603 = 3341405) B3341405
theorem B2970137 : Blo 1979435 2970137 := bstep (se 2 (by rfl) ⟨1113801, by rfl⟩ : syracuseStep 2970137 = 2227603) B2227603
theorem B1980091 : Blo 1979435 1980091 := bstep (se 1 (by rfl) ⟨1485068, by rfl⟩ : syracuseStep 1980091 = 2970137) B2970137
theorem B4757597 : Blo 1979435 4757597 := bbase (se 3 (by rfl) ⟨892049, by rfl⟩ : syracuseStep 4757597 = 1784099) (by norm_num)
theorem B3171731 : Blo 1979435 3171731 := bstep (se 1 (by rfl) ⟨2378798, by rfl⟩ : syracuseStep 3171731 = 4757597) B4757597
theorem B8457949 : Blo 1979435 8457949 := bstep (se 3 (by rfl) ⟨1585865, by rfl⟩ : syracuseStep 8457949 = 3171731) B3171731
theorem B11277265 : Blo 1979435 11277265 := bstep (se 2 (by rfl) ⟨4228974, by rfl⟩ : syracuseStep 11277265 = 8457949) B8457949
theorem B15036353 : Blo 1979435 15036353 := bstep (se 2 (by rfl) ⟨5638632, by rfl⟩ : syracuseStep 15036353 = 11277265) B11277265
theorem B10024235 : Blo 1979435 10024235 := bstep (se 1 (by rfl) ⟨7518176, by rfl⟩ : syracuseStep 10024235 = 15036353) B15036353
theorem B6682823 : Blo 1979435 6682823 := bstep (se 1 (by rfl) ⟨5012117, by rfl⟩ : syracuseStep 6682823 = 10024235) B10024235
theorem B4455215 : Blo 1979435 4455215 := bstep (se 1 (by rfl) ⟨3341411, by rfl⟩ : syracuseStep 4455215 = 6682823) B6682823
theorem B2970143 : Blo 1979435 2970143 := bstep (se 1 (by rfl) ⟨2227607, by rfl⟩ : syracuseStep 2970143 = 4455215) B4455215
theorem B1980095 : Blo 1979435 1980095 := bstep (se 1 (by rfl) ⟨1485071, by rfl⟩ : syracuseStep 1980095 = 2970143) B2970143
theorem B2970149 : Blo 1979435 2970149 := bbase (se 4 (by rfl) ⟨278451, by rfl⟩ : syracuseStep 2970149 = 556903) (by norm_num)
theorem B1980099 : Blo 1979435 1980099 := bstep (se 1 (by rfl) ⟨1485074, by rfl⟩ : syracuseStep 1980099 = 2970149) B2970149
theorem B2506069 : Blo 1979435 2506069 := bbase (se 11 (by rfl) ⟨1835, by rfl⟩ : syracuseStep 2506069 = 3671) (by norm_num)
theorem B3341425 : Blo 1979435 3341425 := bstep (se 2 (by rfl) ⟨1253034, by rfl⟩ : syracuseStep 3341425 = 2506069) B2506069
theorem B4455233 : Blo 1979435 4455233 := bstep (se 2 (by rfl) ⟨1670712, by rfl⟩ : syracuseStep 4455233 = 3341425) B3341425
theorem B2970155 : Blo 1979435 2970155 := bstep (se 1 (by rfl) ⟨2227616, by rfl⟩ : syracuseStep 2970155 = 4455233) B4455233
theorem B1980103 : Blo 1979435 1980103 := bstep (se 1 (by rfl) ⟨1485077, by rfl⟩ : syracuseStep 1980103 = 2970155) B2970155
theorem B2227621 : Blo 1979435 2227621 := bbase (se 4 (by rfl) ⟨208839, by rfl⟩ : syracuseStep 2227621 = 417679) (by norm_num)
theorem B2970161 : Blo 1979435 2970161 := bstep (se 2 (by rfl) ⟨1113810, by rfl⟩ : syracuseStep 2970161 = 2227621) B2227621
theorem B1980107 : Blo 1979435 1980107 := bstep (se 1 (by rfl) ⟨1485080, by rfl⟩ : syracuseStep 1980107 = 2970161) B2970161
theorem B12687029 : Blo 1979435 12687029 := bbase (se 5 (by rfl) ⟨594704, by rfl⟩ : syracuseStep 12687029 = 1189409) (by norm_num)
theorem B8458019 : Blo 1979435 8458019 := bstep (se 1 (by rfl) ⟨6343514, by rfl⟩ : syracuseStep 8458019 = 12687029) B12687029
theorem B5638679 : Blo 1979435 5638679 := bstep (se 1 (by rfl) ⟨4229009, by rfl⟩ : syracuseStep 5638679 = 8458019) B8458019
theorem B3759119 : Blo 1979435 3759119 := bstep (se 1 (by rfl) ⟨2819339, by rfl⟩ : syracuseStep 3759119 = 5638679) B5638679
theorem B2506079 : Blo 1979435 2506079 := bstep (se 1 (by rfl) ⟨1879559, by rfl⟩ : syracuseStep 2506079 = 3759119) B3759119
theorem B6682877 : Blo 1979435 6682877 := bstep (se 3 (by rfl) ⟨1253039, by rfl⟩ : syracuseStep 6682877 = 2506079) B2506079
theorem B4455251 : Blo 1979435 4455251 := bstep (se 1 (by rfl) ⟨3341438, by rfl⟩ : syracuseStep 4455251 = 6682877) B6682877
theorem B2970167 : Blo 1979435 2970167 := bstep (se 1 (by rfl) ⟨2227625, by rfl⟩ : syracuseStep 2970167 = 4455251) B4455251
theorem B1980111 : Blo 1979435 1980111 := bstep (se 1 (by rfl) ⟨1485083, by rfl⟩ : syracuseStep 1980111 = 2970167) B2970167
theorem B2970173 : Blo 1979435 2970173 := bbase (se 3 (by rfl) ⟨556907, by rfl⟩ : syracuseStep 2970173 = 1113815) (by norm_num)
theorem B1980115 : Blo 1979435 1980115 := bstep (se 1 (by rfl) ⟨1485086, by rfl⟩ : syracuseStep 1980115 = 2970173) B2970173
theorem B4455269 : Blo 1979435 4455269 := bbase (se 4 (by rfl) ⟨417681, by rfl⟩ : syracuseStep 4455269 = 835363) (by norm_num)
theorem B2970179 : Blo 1979435 2970179 := bstep (se 1 (by rfl) ⟨2227634, by rfl⟩ : syracuseStep 2970179 = 4455269) B4455269
theorem B1980119 : Blo 1979435 1980119 := bstep (se 1 (by rfl) ⟨1485089, by rfl⟩ : syracuseStep 1980119 = 2970179) B2970179
theorem B5012189 : Blo 1979435 5012189 := bbase (se 3 (by rfl) ⟨939785, by rfl⟩ : syracuseStep 5012189 = 1879571) (by norm_num)
theorem B3341459 : Blo 1979435 3341459 := bstep (se 1 (by rfl) ⟨2506094, by rfl⟩ : syracuseStep 3341459 = 5012189) B5012189
theorem B2227639 : Blo 1979435 2227639 := bstep (se 1 (by rfl) ⟨1670729, by rfl⟩ : syracuseStep 2227639 = 3341459) B3341459
theorem B2970185 : Blo 1979435 2970185 := bstep (se 2 (by rfl) ⟨1113819, by rfl⟩ : syracuseStep 2970185 = 2227639) B2227639
theorem B1980123 : Blo 1979435 1980123 := bstep (se 1 (by rfl) ⟨1485092, by rfl⟩ : syracuseStep 1980123 = 2970185) B2970185
theorem B3759149 : Blo 1979435 3759149 := bbase (se 3 (by rfl) ⟨704840, by rfl⟩ : syracuseStep 3759149 = 1409681) (by norm_num)
theorem B10024397 : Blo 1979435 10024397 := bstep (se 3 (by rfl) ⟨1879574, by rfl⟩ : syracuseStep 10024397 = 3759149) B3759149
theorem B6682931 : Blo 1979435 6682931 := bstep (se 1 (by rfl) ⟨5012198, by rfl⟩ : syracuseStep 6682931 = 10024397) B10024397
theorem B4455287 : Blo 1979435 4455287 := bstep (se 1 (by rfl) ⟨3341465, by rfl⟩ : syracuseStep 4455287 = 6682931) B6682931
theorem B2970191 : Blo 1979435 2970191 := bstep (se 1 (by rfl) ⟨2227643, by rfl⟩ : syracuseStep 2970191 = 4455287) B4455287
theorem B1980127 : Blo 1979435 1980127 := bstep (se 1 (by rfl) ⟨1485095, by rfl⟩ : syracuseStep 1980127 = 2970191) B2970191
theorem B2970197 : Blo 1979435 2970197 := bbase (se 8 (by rfl) ⟨17403, by rfl⟩ : syracuseStep 2970197 = 34807) (by norm_num)
theorem B1980131 : Blo 1979435 1980131 := bstep (se 1 (by rfl) ⟨1485098, by rfl⟩ : syracuseStep 1980131 = 2970197) B2970197
theorem B5149925 : Blo 1979435 5149925 := bbase (se 4 (by rfl) ⟨482805, by rfl⟩ : syracuseStep 5149925 = 965611) (by norm_num)
theorem B3433283 : Blo 1979435 3433283 := bstep (se 1 (by rfl) ⟨2574962, by rfl⟩ : syracuseStep 3433283 = 5149925) B5149925
theorem B2288855 : Blo 1979435 2288855 := bstep (se 1 (by rfl) ⟨1716641, by rfl⟩ : syracuseStep 2288855 = 3433283) B3433283
theorem B6103613 : Blo 1979435 6103613 := bstep (se 3 (by rfl) ⟨1144427, by rfl⟩ : syracuseStep 6103613 = 2288855) B2288855
theorem B4069075 : Blo 1979435 4069075 := bstep (se 1 (by rfl) ⟨3051806, by rfl⟩ : syracuseStep 4069075 = 6103613) B6103613
theorem B5425433 : Blo 1979435 5425433 := bstep (se 2 (by rfl) ⟨2034537, by rfl⟩ : syracuseStep 5425433 = 4069075) B4069075
theorem B3616955 : Blo 1979435 3616955 := bstep (se 1 (by rfl) ⟨2712716, by rfl⟩ : syracuseStep 3616955 = 5425433) B5425433
theorem B2411303 : Blo 1979435 2411303 := bstep (se 1 (by rfl) ⟨1808477, by rfl⟩ : syracuseStep 2411303 = 3616955) B3616955
theorem B6430141 : Blo 1979435 6430141 := bstep (se 3 (by rfl) ⟨1205651, by rfl⟩ : syracuseStep 6430141 = 2411303) B2411303
theorem B8573521 : Blo 1979435 8573521 := bstep (se 2 (by rfl) ⟨3215070, by rfl⟩ : syracuseStep 8573521 = 6430141) B6430141
theorem B11431361 : Blo 1979435 11431361 := bstep (se 2 (by rfl) ⟨4286760, by rfl⟩ : syracuseStep 11431361 = 8573521) B8573521
theorem B7620907 : Blo 1979435 7620907 := bstep (se 1 (by rfl) ⟨5715680, by rfl⟩ : syracuseStep 7620907 = 11431361) B11431361
theorem B10161209 : Blo 1979435 10161209 := bstep (se 2 (by rfl) ⟨3810453, by rfl⟩ : syracuseStep 10161209 = 7620907) B7620907
theorem B6774139 : Blo 1979435 6774139 := bstep (se 1 (by rfl) ⟨5080604, by rfl⟩ : syracuseStep 6774139 = 10161209) B10161209
theorem B9032185 : Blo 1979435 9032185 := bstep (se 2 (by rfl) ⟨3387069, by rfl⟩ : syracuseStep 9032185 = 6774139) B6774139
theorem B12042913 : Blo 1979435 12042913 := bstep (se 2 (by rfl) ⟨4516092, by rfl⟩ : syracuseStep 12042913 = 9032185) B9032185
theorem B16057217 : Blo 1979435 16057217 := bstep (se 2 (by rfl) ⟨6021456, by rfl⟩ : syracuseStep 16057217 = 12042913) B12042913
theorem B10704811 : Blo 1979435 10704811 := bstep (se 1 (by rfl) ⟨8028608, by rfl⟩ : syracuseStep 10704811 = 16057217) B16057217
theorem B14273081 : Blo 1979435 14273081 := bstep (se 2 (by rfl) ⟨5352405, by rfl⟩ : syracuseStep 14273081 = 10704811) B10704811
theorem B9515387 : Blo 1979435 9515387 := bstep (se 1 (by rfl) ⟨7136540, by rfl⟩ : syracuseStep 9515387 = 14273081) B14273081
theorem B6343591 : Blo 1979435 6343591 := bstep (se 1 (by rfl) ⟨4757693, by rfl⟩ : syracuseStep 6343591 = 9515387) B9515387
theorem B8458121 : Blo 1979435 8458121 := bstep (se 2 (by rfl) ⟨3171795, by rfl⟩ : syracuseStep 8458121 = 6343591) B6343591
theorem B5638747 : Blo 1979435 5638747 := bstep (se 1 (by rfl) ⟨4229060, by rfl⟩ : syracuseStep 5638747 = 8458121) B8458121
theorem B7518329 : Blo 1979435 7518329 := bstep (se 2 (by rfl) ⟨2819373, by rfl⟩ : syracuseStep 7518329 = 5638747) B5638747
theorem B5012219 : Blo 1979435 5012219 := bstep (se 1 (by rfl) ⟨3759164, by rfl⟩ : syracuseStep 5012219 = 7518329) B7518329
theorem B3341479 : Blo 1979435 3341479 := bstep (se 1 (by rfl) ⟨2506109, by rfl⟩ : syracuseStep 3341479 = 5012219) B5012219
theorem B4455305 : Blo 1979435 4455305 := bstep (se 2 (by rfl) ⟨1670739, by rfl⟩ : syracuseStep 4455305 = 3341479) B3341479
theorem B2970203 : Blo 1979435 2970203 := bstep (se 1 (by rfl) ⟨2227652, by rfl⟩ : syracuseStep 2970203 = 4455305) B4455305
theorem B1980135 : Blo 1979435 1980135 := bstep (se 1 (by rfl) ⟨1485101, by rfl⟩ : syracuseStep 1980135 = 2970203) B2970203
theorem B2227657 : Blo 1979435 2227657 := bbase (se 2 (by rfl) ⟨835371, by rfl⟩ : syracuseStep 2227657 = 1670743) (by norm_num)
theorem B2970209 : Blo 1979435 2970209 := bstep (se 2 (by rfl) ⟨1113828, by rfl⟩ : syracuseStep 2970209 = 2227657) B2227657
theorem B1980139 : Blo 1979435 1980139 := bstep (se 1 (by rfl) ⟨1485104, by rfl⟩ : syracuseStep 1980139 = 2970209) B2970209
theorem B16916309 : Blo 1979435 16916309 := bbase (se 9 (by rfl) ⟨49559, by rfl⟩ : syracuseStep 16916309 = 99119) (by norm_num)
theorem B11277539 : Blo 1979435 11277539 := bstep (se 1 (by rfl) ⟨8458154, by rfl⟩ : syracuseStep 11277539 = 16916309) B16916309
theorem B7518359 : Blo 1979435 7518359 := bstep (se 1 (by rfl) ⟨5638769, by rfl⟩ : syracuseStep 7518359 = 11277539) B11277539
theorem B5012239 : Blo 1979435 5012239 := bstep (se 1 (by rfl) ⟨3759179, by rfl⟩ : syracuseStep 5012239 = 7518359) B7518359
theorem B6682985 : Blo 1979435 6682985 := bstep (se 2 (by rfl) ⟨2506119, by rfl⟩ : syracuseStep 6682985 = 5012239) B5012239
theorem B4455323 : Blo 1979435 4455323 := bstep (se 1 (by rfl) ⟨3341492, by rfl⟩ : syracuseStep 4455323 = 6682985) B6682985
theorem B2970215 : Blo 1979435 2970215 := bstep (se 1 (by rfl) ⟨2227661, by rfl⟩ : syracuseStep 2970215 = 4455323) B4455323
theorem B1980143 : Blo 1979435 1980143 := bstep (se 1 (by rfl) ⟨1485107, by rfl⟩ : syracuseStep 1980143 = 2970215) B2970215
theorem B2970221 : Blo 1979435 2970221 := bbase (se 3 (by rfl) ⟨556916, by rfl⟩ : syracuseStep 2970221 = 1113833) (by norm_num)
theorem B1980147 : Blo 1979435 1980147 := bstep (se 1 (by rfl) ⟨1485110, by rfl⟩ : syracuseStep 1980147 = 2970221) B2970221
theorem B4455341 : Blo 1979435 4455341 := bbase (se 3 (by rfl) ⟨835376, by rfl⟩ : syracuseStep 4455341 = 1670753) (by norm_num)
theorem B2970227 : Blo 1979435 2970227 := bstep (se 1 (by rfl) ⟨2227670, by rfl⟩ : syracuseStep 2970227 = 4455341) B4455341
theorem B1980151 : Blo 1979435 1980151 := bstep (se 1 (by rfl) ⟨1485113, by rfl⟩ : syracuseStep 1980151 = 2970227) B2970227
theorem B5638805 : Blo 1979435 5638805 := bbase (se 6 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 5638805 = 264319) (by norm_num)
theorem B3759203 : Blo 1979435 3759203 := bstep (se 1 (by rfl) ⟨2819402, by rfl⟩ : syracuseStep 3759203 = 5638805) B5638805
theorem B2506135 : Blo 1979435 2506135 := bstep (se 1 (by rfl) ⟨1879601, by rfl⟩ : syracuseStep 2506135 = 3759203) B3759203
theorem B3341513 : Blo 1979435 3341513 := bstep (se 2 (by rfl) ⟨1253067, by rfl⟩ : syracuseStep 3341513 = 2506135) B2506135
theorem B2227675 : Blo 1979435 2227675 := bstep (se 1 (by rfl) ⟨1670756, by rfl⟩ : syracuseStep 2227675 = 3341513) B3341513
theorem B2970233 : Blo 1979435 2970233 := bstep (se 2 (by rfl) ⟨1113837, by rfl⟩ : syracuseStep 2970233 = 2227675) B2227675
theorem B1980155 : Blo 1979435 1980155 := bstep (se 1 (by rfl) ⟨1485116, by rfl⟩ : syracuseStep 1980155 = 2970233) B2970233
theorem B5352469 : Blo 1979435 5352469 := bbase (se 6 (by rfl) ⟨125448, by rfl⟩ : syracuseStep 5352469 = 250897) (by norm_num)
theorem B28546501 : Blo 1979435 28546501 := bstep (se 4 (by rfl) ⟨2676234, by rfl⟩ : syracuseStep 28546501 = 5352469) B5352469
theorem B38062001 : Blo 1979435 38062001 := bstep (se 2 (by rfl) ⟨14273250, by rfl⟩ : syracuseStep 38062001 = 28546501) B28546501
theorem B25374667 : Blo 1979435 25374667 := bstep (se 1 (by rfl) ⟨19031000, by rfl⟩ : syracuseStep 25374667 = 38062001) B38062001
theorem B33832889 : Blo 1979435 33832889 := bstep (se 2 (by rfl) ⟨12687333, by rfl⟩ : syracuseStep 33832889 = 25374667) B25374667
theorem B22555259 : Blo 1979435 22555259 := bstep (se 1 (by rfl) ⟨16916444, by rfl⟩ : syracuseStep 22555259 = 33832889) B33832889
theorem B15036839 : Blo 1979435 15036839 := bstep (se 1 (by rfl) ⟨11277629, by rfl⟩ : syracuseStep 15036839 = 22555259) B22555259
theorem B10024559 : Blo 1979435 10024559 := bstep (se 1 (by rfl) ⟨7518419, by rfl⟩ : syracuseStep 10024559 = 15036839) B15036839
theorem B6683039 : Blo 1979435 6683039 := bstep (se 1 (by rfl) ⟨5012279, by rfl⟩ : syracuseStep 6683039 = 10024559) B10024559
theorem B4455359 : Blo 1979435 4455359 := bstep (se 1 (by rfl) ⟨3341519, by rfl⟩ : syracuseStep 4455359 = 6683039) B6683039
theorem B2970239 : Blo 1979435 2970239 := bstep (se 1 (by rfl) ⟨2227679, by rfl⟩ : syracuseStep 2970239 = 4455359) B4455359
theorem B1980159 : Blo 1979435 1980159 := bstep (se 1 (by rfl) ⟨1485119, by rfl⟩ : syracuseStep 1980159 = 2970239) B2970239
theorem B2970245 : Blo 1979435 2970245 := bbase (se 4 (by rfl) ⟨278460, by rfl⟩ : syracuseStep 2970245 = 556921) (by norm_num)
theorem B1980163 : Blo 1979435 1980163 := bstep (se 1 (by rfl) ⟨1485122, by rfl⟩ : syracuseStep 1980163 = 2970245) B2970245
theorem B3341533 : Blo 1979435 3341533 := bbase (se 3 (by rfl) ⟨626537, by rfl⟩ : syracuseStep 3341533 = 1253075) (by norm_num)
theorem B4455377 : Blo 1979435 4455377 := bstep (se 2 (by rfl) ⟨1670766, by rfl⟩ : syracuseStep 4455377 = 3341533) B3341533
theorem B2970251 : Blo 1979435 2970251 := bstep (se 1 (by rfl) ⟨2227688, by rfl⟩ : syracuseStep 2970251 = 4455377) B4455377
theorem B1980167 : Blo 1979435 1980167 := bstep (se 1 (by rfl) ⟨1485125, by rfl⟩ : syracuseStep 1980167 = 2970251) B2970251
theorem B2227693 : Blo 1979435 2227693 := bbase (se 3 (by rfl) ⟨417692, by rfl⟩ : syracuseStep 2227693 = 835385) (by norm_num)
theorem B2970257 : Blo 1979435 2970257 := bstep (se 2 (by rfl) ⟨1113846, by rfl⟩ : syracuseStep 2970257 = 2227693) B2227693
theorem B1980171 : Blo 1979435 1980171 := bstep (se 1 (by rfl) ⟨1485128, by rfl⟩ : syracuseStep 1980171 = 2970257) B2970257
theorem B6683093 : Blo 1979435 6683093 := bbase (se 7 (by rfl) ⟨78317, by rfl⟩ : syracuseStep 6683093 = 156635) (by norm_num)
theorem B4455395 : Blo 1979435 4455395 := bstep (se 1 (by rfl) ⟨3341546, by rfl⟩ : syracuseStep 4455395 = 6683093) B6683093
theorem B2970263 : Blo 1979435 2970263 := bstep (se 1 (by rfl) ⟨2227697, by rfl⟩ : syracuseStep 2970263 = 4455395) B4455395
theorem B1980175 : Blo 1979435 1980175 := bstep (se 1 (by rfl) ⟨1485131, by rfl⟩ : syracuseStep 1980175 = 2970263) B2970263
theorem B2970269 : Blo 1979435 2970269 := bbase (se 3 (by rfl) ⟨556925, by rfl⟩ : syracuseStep 2970269 = 1113851) (by norm_num)
theorem B1980179 : Blo 1979435 1980179 := bstep (se 1 (by rfl) ⟨1485134, by rfl⟩ : syracuseStep 1980179 = 2970269) B2970269
theorem B4455413 : Blo 1979435 4455413 := bbase (se 5 (by rfl) ⟨208847, by rfl⟩ : syracuseStep 4455413 = 417695) (by norm_num)
theorem B2970275 : Blo 1979435 2970275 := bstep (se 1 (by rfl) ⟨2227706, by rfl⟩ : syracuseStep 2970275 = 4455413) B4455413
theorem B1980183 : Blo 1979435 1980183 := bstep (se 1 (by rfl) ⟨1485137, by rfl⟩ : syracuseStep 1980183 = 2970275) B2970275
theorem B36129685 : Blo 1979435 36129685 := bbase (se 6 (by rfl) ⟨846789, by rfl⟩ : syracuseStep 36129685 = 1693579) (by norm_num)
theorem B48172913 : Blo 1979435 48172913 := bstep (se 2 (by rfl) ⟨18064842, by rfl⟩ : syracuseStep 48172913 = 36129685) B36129685
theorem B32115275 : Blo 1979435 32115275 := bstep (se 1 (by rfl) ⟨24086456, by rfl⟩ : syracuseStep 32115275 = 48172913) B48172913
theorem B21410183 : Blo 1979435 21410183 := bstep (se 1 (by rfl) ⟨16057637, by rfl⟩ : syracuseStep 21410183 = 32115275) B32115275
theorem B57093821 : Blo 1979435 57093821 := bstep (se 3 (by rfl) ⟨10705091, by rfl⟩ : syracuseStep 57093821 = 21410183) B21410183
theorem B38062547 : Blo 1979435 38062547 := bstep (se 1 (by rfl) ⟨28546910, by rfl⟩ : syracuseStep 38062547 = 57093821) B57093821
theorem B25375031 : Blo 1979435 25375031 := bstep (se 1 (by rfl) ⟨19031273, by rfl⟩ : syracuseStep 25375031 = 38062547) B38062547
theorem B16916687 : Blo 1979435 16916687 := bstep (se 1 (by rfl) ⟨12687515, by rfl⟩ : syracuseStep 16916687 = 25375031) B25375031
theorem B11277791 : Blo 1979435 11277791 := bstep (se 1 (by rfl) ⟨8458343, by rfl⟩ : syracuseStep 11277791 = 16916687) B16916687
theorem B7518527 : Blo 1979435 7518527 := bstep (se 1 (by rfl) ⟨5638895, by rfl⟩ : syracuseStep 7518527 = 11277791) B11277791
theorem B5012351 : Blo 1979435 5012351 := bstep (se 1 (by rfl) ⟨3759263, by rfl⟩ : syracuseStep 5012351 = 7518527) B7518527
theorem B3341567 : Blo 1979435 3341567 := bstep (se 1 (by rfl) ⟨2506175, by rfl⟩ : syracuseStep 3341567 = 5012351) B5012351
theorem B2227711 : Blo 1979435 2227711 := bstep (se 1 (by rfl) ⟨1670783, by rfl⟩ : syracuseStep 2227711 = 3341567) B3341567
theorem B2970281 : Blo 1979435 2970281 := bstep (se 2 (by rfl) ⟨1113855, by rfl⟩ : syracuseStep 2970281 = 2227711) B2227711
theorem B1980187 : Blo 1979435 1980187 := bstep (se 1 (by rfl) ⟨1485140, by rfl⟩ : syracuseStep 1980187 = 2970281) B2970281
theorem B2819453 : Blo 1979435 2819453 := bbase (se 3 (by rfl) ⟨528647, by rfl⟩ : syracuseStep 2819453 = 1057295) (by norm_num)
theorem B7518541 : Blo 1979435 7518541 := bstep (se 3 (by rfl) ⟨1409726, by rfl⟩ : syracuseStep 7518541 = 2819453) B2819453
theorem B10024721 : Blo 1979435 10024721 := bstep (se 2 (by rfl) ⟨3759270, by rfl⟩ : syracuseStep 10024721 = 7518541) B7518541
theorem B6683147 : Blo 1979435 6683147 := bstep (se 1 (by rfl) ⟨5012360, by rfl⟩ : syracuseStep 6683147 = 10024721) B10024721
theorem B4455431 : Blo 1979435 4455431 := bstep (se 1 (by rfl) ⟨3341573, by rfl⟩ : syracuseStep 4455431 = 6683147) B6683147
theorem B2970287 : Blo 1979435 2970287 := bstep (se 1 (by rfl) ⟨2227715, by rfl⟩ : syracuseStep 2970287 = 4455431) B4455431
theorem B1980191 : Blo 1979435 1980191 := bstep (se 1 (by rfl) ⟨1485143, by rfl⟩ : syracuseStep 1980191 = 2970287) B2970287
theorem B2970293 : Blo 1979435 2970293 := bbase (se 5 (by rfl) ⟨139232, by rfl⟩ : syracuseStep 2970293 = 278465) (by norm_num)
theorem B1980195 : Blo 1979435 1980195 := bstep (se 1 (by rfl) ⟨1485146, by rfl⟩ : syracuseStep 1980195 = 2970293) B2970293
theorem B5012381 : Blo 1979435 5012381 := bbase (se 3 (by rfl) ⟨939821, by rfl⟩ : syracuseStep 5012381 = 1879643) (by norm_num)
theorem B3341587 : Blo 1979435 3341587 := bstep (se 1 (by rfl) ⟨2506190, by rfl⟩ : syracuseStep 3341587 = 5012381) B5012381
theorem B4455449 : Blo 1979435 4455449 := bstep (se 2 (by rfl) ⟨1670793, by rfl⟩ : syracuseStep 4455449 = 3341587) B3341587
theorem B2970299 : Blo 1979435 2970299 := bstep (se 1 (by rfl) ⟨2227724, by rfl⟩ : syracuseStep 2970299 = 4455449) B4455449
theorem B1980199 : Blo 1979435 1980199 := bstep (se 1 (by rfl) ⟨1485149, by rfl⟩ : syracuseStep 1980199 = 2970299) B2970299
theorem B2227729 : Blo 1979435 2227729 := bbase (se 2 (by rfl) ⟨835398, by rfl⟩ : syracuseStep 2227729 = 1670797) (by norm_num)
theorem B2970305 : Blo 1979435 2970305 := bstep (se 2 (by rfl) ⟨1113864, by rfl⟩ : syracuseStep 2970305 = 2227729) B2227729
theorem B1980203 : Blo 1979435 1980203 := bstep (se 1 (by rfl) ⟨1485152, by rfl⟩ : syracuseStep 1980203 = 2970305) B2970305
theorem B3759301 : Blo 1979435 3759301 := bbase (se 4 (by rfl) ⟨352434, by rfl⟩ : syracuseStep 3759301 = 704869) (by norm_num)
theorem B5012401 : Blo 1979435 5012401 := bstep (se 2 (by rfl) ⟨1879650, by rfl⟩ : syracuseStep 5012401 = 3759301) B3759301
theorem B6683201 : Blo 1979435 6683201 := bstep (se 2 (by rfl) ⟨2506200, by rfl⟩ : syracuseStep 6683201 = 5012401) B5012401
theorem B4455467 : Blo 1979435 4455467 := bstep (se 1 (by rfl) ⟨3341600, by rfl⟩ : syracuseStep 4455467 = 6683201) B6683201
theorem B2970311 : Blo 1979435 2970311 := bstep (se 1 (by rfl) ⟨2227733, by rfl⟩ : syracuseStep 2970311 = 4455467) B4455467
theorem B1980207 : Blo 1979435 1980207 := bstep (se 1 (by rfl) ⟨1485155, by rfl⟩ : syracuseStep 1980207 = 2970311) B2970311
theorem B2970317 : Blo 1979435 2970317 := bbase (se 3 (by rfl) ⟨556934, by rfl⟩ : syracuseStep 2970317 = 1113869) (by norm_num)
theorem B1980211 : Blo 1979435 1980211 := bstep (se 1 (by rfl) ⟨1485158, by rfl⟩ : syracuseStep 1980211 = 2970317) B2970317
theorem B4455485 : Blo 1979435 4455485 := bbase (se 3 (by rfl) ⟨835403, by rfl⟩ : syracuseStep 4455485 = 1670807) (by norm_num)
theorem B2970323 : Blo 1979435 2970323 := bstep (se 1 (by rfl) ⟨2227742, by rfl⟩ : syracuseStep 2970323 = 4455485) B4455485
theorem B1980215 : Blo 1979435 1980215 := bstep (se 1 (by rfl) ⟨1485161, by rfl⟩ : syracuseStep 1980215 = 2970323) B2970323
theorem B3341621 : Blo 1979435 3341621 := bbase (se 5 (by rfl) ⟨156638, by rfl⟩ : syracuseStep 3341621 = 313277) (by norm_num)
theorem B2227747 : Blo 1979435 2227747 := bstep (se 1 (by rfl) ⟨1670810, by rfl⟩ : syracuseStep 2227747 = 3341621) B3341621
theorem B2970329 : Blo 1979435 2970329 := bstep (se 2 (by rfl) ⟨1113873, by rfl⟩ : syracuseStep 2970329 = 2227747) B2227747
theorem B1980219 : Blo 1979435 1980219 := bstep (se 1 (by rfl) ⟨1485164, by rfl⟩ : syracuseStep 1980219 = 2970329) B2970329
theorem B5638997 : Blo 1979435 5638997 := bbase (se 9 (by rfl) ⟨16520, by rfl⟩ : syracuseStep 5638997 = 33041) (by norm_num)
theorem B15037325 : Blo 1979435 15037325 := bstep (se 3 (by rfl) ⟨2819498, by rfl⟩ : syracuseStep 15037325 = 5638997) B5638997
theorem B10024883 : Blo 1979435 10024883 := bstep (se 1 (by rfl) ⟨7518662, by rfl⟩ : syracuseStep 10024883 = 15037325) B15037325
theorem B6683255 : Blo 1979435 6683255 := bstep (se 1 (by rfl) ⟨5012441, by rfl⟩ : syracuseStep 6683255 = 10024883) B10024883
theorem B4455503 : Blo 1979435 4455503 := bstep (se 1 (by rfl) ⟨3341627, by rfl⟩ : syracuseStep 4455503 = 6683255) B6683255
theorem B2970335 : Blo 1979435 2970335 := bstep (se 1 (by rfl) ⟨2227751, by rfl⟩ : syracuseStep 2970335 = 4455503) B4455503
theorem B1980223 : Blo 1979435 1980223 := bstep (se 1 (by rfl) ⟨1485167, by rfl⟩ : syracuseStep 1980223 = 2970335) B2970335
theorem B2970341 : Blo 1979435 2970341 := bbase (se 4 (by rfl) ⟨278469, by rfl⟩ : syracuseStep 2970341 = 556939) (by norm_num)
theorem B1980227 : Blo 1979435 1980227 := bstep (se 1 (by rfl) ⟨1485170, by rfl⟩ : syracuseStep 1980227 = 2970341) B2970341
theorem B2114633 : Blo 1979435 2114633 := bbase (se 2 (by rfl) ⟨792987, by rfl⟩ : syracuseStep 2114633 = 1585975) (by norm_num)
theorem B5639021 : Blo 1979435 5639021 := bstep (se 3 (by rfl) ⟨1057316, by rfl⟩ : syracuseStep 5639021 = 2114633) B2114633
theorem B3759347 : Blo 1979435 3759347 := bstep (se 1 (by rfl) ⟨2819510, by rfl⟩ : syracuseStep 3759347 = 5639021) B5639021
theorem B2506231 : Blo 1979435 2506231 := bstep (se 1 (by rfl) ⟨1879673, by rfl⟩ : syracuseStep 2506231 = 3759347) B3759347
theorem B3341641 : Blo 1979435 3341641 := bstep (se 2 (by rfl) ⟨1253115, by rfl⟩ : syracuseStep 3341641 = 2506231) B2506231
theorem B4455521 : Blo 1979435 4455521 := bstep (se 2 (by rfl) ⟨1670820, by rfl⟩ : syracuseStep 4455521 = 3341641) B3341641
theorem B2970347 : Blo 1979435 2970347 := bstep (se 1 (by rfl) ⟨2227760, by rfl⟩ : syracuseStep 2970347 = 4455521) B4455521
theorem B1980231 : Blo 1979435 1980231 := bstep (se 1 (by rfl) ⟨1485173, by rfl⟩ : syracuseStep 1980231 = 2970347) B2970347
theorem B2227765 : Blo 1979435 2227765 := bbase (se 5 (by rfl) ⟨104426, by rfl⟩ : syracuseStep 2227765 = 208853) (by norm_num)
theorem B2970353 : Blo 1979435 2970353 := bstep (se 2 (by rfl) ⟨1113882, by rfl⟩ : syracuseStep 2970353 = 2227765) B2227765
theorem B1980235 : Blo 1979435 1980235 := bstep (se 1 (by rfl) ⟨1485176, by rfl⟩ : syracuseStep 1980235 = 2970353) B2970353
theorem B2506241 : Blo 1979435 2506241 := bbase (se 2 (by rfl) ⟨939840, by rfl⟩ : syracuseStep 2506241 = 1879681) (by norm_num)
theorem B6683309 : Blo 1979435 6683309 := bstep (se 3 (by rfl) ⟨1253120, by rfl⟩ : syracuseStep 6683309 = 2506241) B2506241
theorem B4455539 : Blo 1979435 4455539 := bstep (se 1 (by rfl) ⟨3341654, by rfl⟩ : syracuseStep 4455539 = 6683309) B6683309
theorem B2970359 : Blo 1979435 2970359 := bstep (se 1 (by rfl) ⟨2227769, by rfl⟩ : syracuseStep 2970359 = 4455539) B4455539
theorem B1980239 : Blo 1979435 1980239 := bstep (se 1 (by rfl) ⟨1485179, by rfl⟩ : syracuseStep 1980239 = 2970359) B2970359
theorem B2970365 : Blo 1979435 2970365 := bbase (se 3 (by rfl) ⟨556943, by rfl⟩ : syracuseStep 2970365 = 1113887) (by norm_num)
theorem B1980243 : Blo 1979435 1980243 := bstep (se 1 (by rfl) ⟨1485182, by rfl⟩ : syracuseStep 1980243 = 2970365) B2970365
theorem B4455557 : Blo 1979435 4455557 := bbase (se 4 (by rfl) ⟨417708, by rfl⟩ : syracuseStep 4455557 = 835417) (by norm_num)
theorem B2970371 : Blo 1979435 2970371 := bstep (se 1 (by rfl) ⟨2227778, by rfl⟩ : syracuseStep 2970371 = 4455557) B4455557
theorem B1980247 : Blo 1979435 1980247 := bstep (se 1 (by rfl) ⟨1485185, by rfl⟩ : syracuseStep 1980247 = 2970371) B2970371
theorem B4229309 : Blo 1979435 4229309 := bbase (se 3 (by rfl) ⟨792995, by rfl⟩ : syracuseStep 4229309 = 1585991) (by norm_num)
theorem B2819539 : Blo 1979435 2819539 := bstep (se 1 (by rfl) ⟨2114654, by rfl⟩ : syracuseStep 2819539 = 4229309) B4229309
theorem B3759385 : Blo 1979435 3759385 := bstep (se 2 (by rfl) ⟨1409769, by rfl⟩ : syracuseStep 3759385 = 2819539) B2819539
theorem B5012513 : Blo 1979435 5012513 := bstep (se 2 (by rfl) ⟨1879692, by rfl⟩ : syracuseStep 5012513 = 3759385) B3759385
theorem B3341675 : Blo 1979435 3341675 := bstep (se 1 (by rfl) ⟨2506256, by rfl⟩ : syracuseStep 3341675 = 5012513) B5012513
theorem B2227783 : Blo 1979435 2227783 := bstep (se 1 (by rfl) ⟨1670837, by rfl⟩ : syracuseStep 2227783 = 3341675) B3341675
theorem B2970377 : Blo 1979435 2970377 := bstep (se 2 (by rfl) ⟨1113891, by rfl⟩ : syracuseStep 2970377 = 2227783) B2227783
theorem B1980251 : Blo 1979435 1980251 := bstep (se 1 (by rfl) ⟨1485188, by rfl⟩ : syracuseStep 1980251 = 2970377) B2970377
theorem B10025045 : Blo 1979435 10025045 := bbase (se 8 (by rfl) ⟨58740, by rfl⟩ : syracuseStep 10025045 = 117481) (by norm_num)
theorem B6683363 : Blo 1979435 6683363 := bstep (se 1 (by rfl) ⟨5012522, by rfl⟩ : syracuseStep 6683363 = 10025045) B10025045
theorem B4455575 : Blo 1979435 4455575 := bstep (se 1 (by rfl) ⟨3341681, by rfl⟩ : syracuseStep 4455575 = 6683363) B6683363
theorem B2970383 : Blo 1979435 2970383 := bstep (se 1 (by rfl) ⟨2227787, by rfl⟩ : syracuseStep 2970383 = 4455575) B4455575
theorem B1980255 : Blo 1979435 1980255 := bstep (se 1 (by rfl) ⟨1485191, by rfl⟩ : syracuseStep 1980255 = 2970383) B2970383
theorem B2970389 : Blo 1979435 2970389 := bbase (se 6 (by rfl) ⟨69618, by rfl⟩ : syracuseStep 2970389 = 139237) (by norm_num)
theorem B1980259 : Blo 1979435 1980259 := bstep (se 1 (by rfl) ⟨1485194, by rfl⟩ : syracuseStep 1980259 = 2970389) B2970389
theorem B17148149 : Blo 1979435 17148149 := bbase (se 5 (by rfl) ⟨803819, by rfl⟩ : syracuseStep 17148149 = 1607639) (by norm_num)
theorem B11432099 : Blo 1979435 11432099 := bstep (se 1 (by rfl) ⟨8574074, by rfl⟩ : syracuseStep 11432099 = 17148149) B17148149
theorem B7621399 : Blo 1979435 7621399 := bstep (se 1 (by rfl) ⟨5716049, by rfl⟩ : syracuseStep 7621399 = 11432099) B11432099
theorem B10161865 : Blo 1979435 10161865 := bstep (se 2 (by rfl) ⟨3810699, by rfl⟩ : syracuseStep 10161865 = 7621399) B7621399
theorem B13549153 : Blo 1979435 13549153 := bstep (se 2 (by rfl) ⟨5080932, by rfl⟩ : syracuseStep 13549153 = 10161865) B10161865
theorem B18065537 : Blo 1979435 18065537 := bstep (se 2 (by rfl) ⟨6774576, by rfl⟩ : syracuseStep 18065537 = 13549153) B13549153
theorem B12043691 : Blo 1979435 12043691 := bstep (se 1 (by rfl) ⟨9032768, by rfl⟩ : syracuseStep 12043691 = 18065537) B18065537
theorem B8029127 : Blo 1979435 8029127 := bstep (se 1 (by rfl) ⟨6021845, by rfl⟩ : syracuseStep 8029127 = 12043691) B12043691
theorem B5352751 : Blo 1979435 5352751 := bstep (se 1 (by rfl) ⟨4014563, by rfl⟩ : syracuseStep 5352751 = 8029127) B8029127
theorem B7137001 : Blo 1979435 7137001 := bstep (se 2 (by rfl) ⟨2676375, by rfl⟩ : syracuseStep 7137001 = 5352751) B5352751
theorem B38064005 : Blo 1979435 38064005 := bstep (se 4 (by rfl) ⟨3568500, by rfl⟩ : syracuseStep 38064005 = 7137001) B7137001
theorem B25376003 : Blo 1979435 25376003 := bstep (se 1 (by rfl) ⟨19032002, by rfl⟩ : syracuseStep 25376003 = 38064005) B38064005
theorem B16917335 : Blo 1979435 16917335 := bstep (se 1 (by rfl) ⟨12688001, by rfl⟩ : syracuseStep 16917335 = 25376003) B25376003
theorem B11278223 : Blo 1979435 11278223 := bstep (se 1 (by rfl) ⟨8458667, by rfl⟩ : syracuseStep 11278223 = 16917335) B16917335
theorem B7518815 : Blo 1979435 7518815 := bstep (se 1 (by rfl) ⟨5639111, by rfl⟩ : syracuseStep 7518815 = 11278223) B11278223
theorem B5012543 : Blo 1979435 5012543 := bstep (se 1 (by rfl) ⟨3759407, by rfl⟩ : syracuseStep 5012543 = 7518815) B7518815
theorem B3341695 : Blo 1979435 3341695 := bstep (se 1 (by rfl) ⟨2506271, by rfl⟩ : syracuseStep 3341695 = 5012543) B5012543
theorem B4455593 : Blo 1979435 4455593 := bstep (se 2 (by rfl) ⟨1670847, by rfl⟩ : syracuseStep 4455593 = 3341695) B3341695
theorem B2970395 : Blo 1979435 2970395 := bstep (se 1 (by rfl) ⟨2227796, by rfl⟩ : syracuseStep 2970395 = 4455593) B4455593
theorem B1980263 : Blo 1979435 1980263 := bstep (se 1 (by rfl) ⟨1485197, by rfl⟩ : syracuseStep 1980263 = 2970395) B2970395
theorem B2227801 : Blo 1979435 2227801 := bbase (se 2 (by rfl) ⟨835425, by rfl⟩ : syracuseStep 2227801 = 1670851) (by norm_num)
theorem B2970401 : Blo 1979435 2970401 := bstep (se 2 (by rfl) ⟨1113900, by rfl⟩ : syracuseStep 2970401 = 2227801) B2227801
theorem B1980267 : Blo 1979435 1980267 := bstep (se 1 (by rfl) ⟨1485200, by rfl⟩ : syracuseStep 1980267 = 2970401) B2970401
theorem B2540477 : Blo 1979435 2540477 := bbase (se 3 (by rfl) ⟨476339, by rfl⟩ : syracuseStep 2540477 = 952679) (by norm_num)
theorem B6774605 : Blo 1979435 6774605 := bstep (se 3 (by rfl) ⟨1270238, by rfl⟩ : syracuseStep 6774605 = 2540477) B2540477
theorem B4516403 : Blo 1979435 4516403 := bstep (se 1 (by rfl) ⟨3387302, by rfl⟩ : syracuseStep 4516403 = 6774605) B6774605
theorem B12043741 : Blo 1979435 12043741 := bstep (se 3 (by rfl) ⟨2258201, by rfl⟩ : syracuseStep 12043741 = 4516403) B4516403
theorem B16058321 : Blo 1979435 16058321 := bstep (se 2 (by rfl) ⟨6021870, by rfl⟩ : syracuseStep 16058321 = 12043741) B12043741
theorem B10705547 : Blo 1979435 10705547 := bstep (se 1 (by rfl) ⟨8029160, by rfl⟩ : syracuseStep 10705547 = 16058321) B16058321
theorem B7137031 : Blo 1979435 7137031 := bstep (se 1 (by rfl) ⟨5352773, by rfl⟩ : syracuseStep 7137031 = 10705547) B10705547
theorem B9516041 : Blo 1979435 9516041 := bstep (se 2 (by rfl) ⟨3568515, by rfl⟩ : syracuseStep 9516041 = 7137031) B7137031
theorem B6344027 : Blo 1979435 6344027 := bstep (se 1 (by rfl) ⟨4758020, by rfl⟩ : syracuseStep 6344027 = 9516041) B9516041
theorem B4229351 : Blo 1979435 4229351 := bstep (se 1 (by rfl) ⟨3172013, by rfl⟩ : syracuseStep 4229351 = 6344027) B6344027
theorem B2819567 : Blo 1979435 2819567 := bstep (se 1 (by rfl) ⟨2114675, by rfl⟩ : syracuseStep 2819567 = 4229351) B4229351
theorem B7518845 : Blo 1979435 7518845 := bstep (se 3 (by rfl) ⟨1409783, by rfl⟩ : syracuseStep 7518845 = 2819567) B2819567
theorem B5012563 : Blo 1979435 5012563 := bstep (se 1 (by rfl) ⟨3759422, by rfl⟩ : syracuseStep 5012563 = 7518845) B7518845
theorem B6683417 : Blo 1979435 6683417 := bstep (se 2 (by rfl) ⟨2506281, by rfl⟩ : syracuseStep 6683417 = 5012563) B5012563
theorem B4455611 : Blo 1979435 4455611 := bstep (se 1 (by rfl) ⟨3341708, by rfl⟩ : syracuseStep 4455611 = 6683417) B6683417
theorem B2970407 : Blo 1979435 2970407 := bstep (se 1 (by rfl) ⟨2227805, by rfl⟩ : syracuseStep 2970407 = 4455611) B4455611
theorem B1980271 : Blo 1979435 1980271 := bstep (se 1 (by rfl) ⟨1485203, by rfl⟩ : syracuseStep 1980271 = 2970407) B2970407
theorem B2970413 : Blo 1979435 2970413 := bbase (se 3 (by rfl) ⟨556952, by rfl⟩ : syracuseStep 2970413 = 1113905) (by norm_num)
theorem B1980275 : Blo 1979435 1980275 := bstep (se 1 (by rfl) ⟨1485206, by rfl⟩ : syracuseStep 1980275 = 2970413) B2970413
theorem B4455629 : Blo 1979435 4455629 := bbase (se 3 (by rfl) ⟨835430, by rfl⟩ : syracuseStep 4455629 = 1670861) (by norm_num)
theorem B2970419 : Blo 1979435 2970419 := bstep (se 1 (by rfl) ⟨2227814, by rfl⟩ : syracuseStep 2970419 = 4455629) B4455629
theorem B1980279 : Blo 1979435 1980279 := bstep (se 1 (by rfl) ⟨1485209, by rfl⟩ : syracuseStep 1980279 = 2970419) B2970419
theorem B2506297 : Blo 1979435 2506297 := bbase (se 2 (by rfl) ⟨939861, by rfl⟩ : syracuseStep 2506297 = 1879723) (by norm_num)
theorem B3341729 : Blo 1979435 3341729 := bstep (se 2 (by rfl) ⟨1253148, by rfl⟩ : syracuseStep 3341729 = 2506297) B2506297
theorem B2227819 : Blo 1979435 2227819 := bstep (se 1 (by rfl) ⟨1670864, by rfl⟩ : syracuseStep 2227819 = 3341729) B3341729
theorem B2970425 : Blo 1979435 2970425 := bstep (se 2 (by rfl) ⟨1113909, by rfl⟩ : syracuseStep 2970425 = 2227819) B2227819
theorem B1980283 : Blo 1979435 1980283 := bstep (se 1 (by rfl) ⟨1485212, by rfl⟩ : syracuseStep 1980283 = 2970425) B2970425
theorem B2379029 : Blo 1979435 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B6344077 : Blo 1979435 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B8458769 : Blo 1979435 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B22556717 : Blo 1979435 22556717 := bstep (se 3 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 22556717 = 8458769) B8458769
theorem B15037811 : Blo 1979435 15037811 := bstep (se 1 (by rfl) ⟨11278358, by rfl⟩ : syracuseStep 15037811 = 22556717) B22556717
theorem B10025207 : Blo 1979435 10025207 := bstep (se 1 (by rfl) ⟨7518905, by rfl⟩ : syracuseStep 10025207 = 15037811) B15037811
theorem B6683471 : Blo 1979435 6683471 := bstep (se 1 (by rfl) ⟨5012603, by rfl⟩ : syracuseStep 6683471 = 10025207) B10025207
theorem B4455647 : Blo 1979435 4455647 := bstep (se 1 (by rfl) ⟨3341735, by rfl⟩ : syracuseStep 4455647 = 6683471) B6683471
theorem B2970431 : Blo 1979435 2970431 := bstep (se 1 (by rfl) ⟨2227823, by rfl⟩ : syracuseStep 2970431 = 4455647) B4455647
theorem B1980287 : Blo 1979435 1980287 := bstep (se 1 (by rfl) ⟨1485215, by rfl⟩ : syracuseStep 1980287 = 2970431) B2970431
theorem B2970437 : Blo 1979435 2970437 := bbase (se 4 (by rfl) ⟨278478, by rfl⟩ : syracuseStep 2970437 = 556957) (by norm_num)
theorem B1980291 : Blo 1979435 1980291 := bstep (se 1 (by rfl) ⟨1485218, by rfl⟩ : syracuseStep 1980291 = 2970437) B2970437
theorem B3341749 : Blo 1979435 3341749 := bbase (se 5 (by rfl) ⟨156644, by rfl⟩ : syracuseStep 3341749 = 313289) (by norm_num)
theorem B4455665 : Blo 1979435 4455665 := bstep (se 2 (by rfl) ⟨1670874, by rfl⟩ : syracuseStep 4455665 = 3341749) B3341749
theorem B2970443 : Blo 1979435 2970443 := bstep (se 1 (by rfl) ⟨2227832, by rfl⟩ : syracuseStep 2970443 = 4455665) B4455665
theorem B1980295 : Blo 1979435 1980295 := bstep (se 1 (by rfl) ⟨1485221, by rfl⟩ : syracuseStep 1980295 = 2970443) B2970443
theorem B2227837 : Blo 1979435 2227837 := bbase (se 3 (by rfl) ⟨417719, by rfl⟩ : syracuseStep 2227837 = 835439) (by norm_num)
theorem B2970449 : Blo 1979435 2970449 := bstep (se 2 (by rfl) ⟨1113918, by rfl⟩ : syracuseStep 2970449 = 2227837) B2227837
theorem B1980299 : Blo 1979435 1980299 := bstep (se 1 (by rfl) ⟨1485224, by rfl⟩ : syracuseStep 1980299 = 2970449) B2970449
theorem B6683525 : Blo 1979435 6683525 := bbase (se 4 (by rfl) ⟨626580, by rfl⟩ : syracuseStep 6683525 = 1253161) (by norm_num)
theorem B4455683 : Blo 1979435 4455683 := bstep (se 1 (by rfl) ⟨3341762, by rfl⟩ : syracuseStep 4455683 = 6683525) B6683525
theorem B2970455 : Blo 1979435 2970455 := bstep (se 1 (by rfl) ⟨2227841, by rfl⟩ : syracuseStep 2970455 = 4455683) B4455683
theorem B1980303 : Blo 1979435 1980303 := bstep (se 1 (by rfl) ⟨1485227, by rfl⟩ : syracuseStep 1980303 = 2970455) B2970455
theorem B2970461 : Blo 1979435 2970461 := bbase (se 3 (by rfl) ⟨556961, by rfl⟩ : syracuseStep 2970461 = 1113923) (by norm_num)
theorem B1980307 : Blo 1979435 1980307 := bstep (se 1 (by rfl) ⟨1485230, by rfl⟩ : syracuseStep 1980307 = 2970461) B2970461
theorem B4455701 : Blo 1979435 4455701 := bbase (se 6 (by rfl) ⟨104430, by rfl⟩ : syracuseStep 4455701 = 208861) (by norm_num)
theorem B2970467 : Blo 1979435 2970467 := bstep (se 1 (by rfl) ⟨2227850, by rfl⟩ : syracuseStep 2970467 = 4455701) B4455701
theorem B1980311 : Blo 1979435 1980311 := bstep (se 1 (by rfl) ⟨1485233, by rfl⟩ : syracuseStep 1980311 = 2970467) B2970467
theorem B7519013 : Blo 1979435 7519013 := bbase (se 4 (by rfl) ⟨704907, by rfl⟩ : syracuseStep 7519013 = 1409815) (by norm_num)
theorem B5012675 : Blo 1979435 5012675 := bstep (se 1 (by rfl) ⟨3759506, by rfl⟩ : syracuseStep 5012675 = 7519013) B7519013
theorem B3341783 : Blo 1979435 3341783 := bstep (se 1 (by rfl) ⟨2506337, by rfl⟩ : syracuseStep 3341783 = 5012675) B5012675
theorem B2227855 : Blo 1979435 2227855 := bstep (se 1 (by rfl) ⟨1670891, by rfl⟩ : syracuseStep 2227855 = 3341783) B3341783
theorem B2970473 : Blo 1979435 2970473 := bstep (se 2 (by rfl) ⟨1113927, by rfl⟩ : syracuseStep 2970473 = 2227855) B2227855
theorem B1980315 : Blo 1979435 1980315 := bstep (se 1 (by rfl) ⟨1485236, by rfl⟩ : syracuseStep 1980315 = 2970473) B2970473
theorem B4229453 : Blo 1979435 4229453 := bbase (se 3 (by rfl) ⟨793022, by rfl⟩ : syracuseStep 4229453 = 1586045) (by norm_num)
theorem B11278541 : Blo 1979435 11278541 := bstep (se 3 (by rfl) ⟨2114726, by rfl⟩ : syracuseStep 11278541 = 4229453) B4229453
theorem B7519027 : Blo 1979435 7519027 := bstep (se 1 (by rfl) ⟨5639270, by rfl⟩ : syracuseStep 7519027 = 11278541) B11278541
theorem B10025369 : Blo 1979435 10025369 := bstep (se 2 (by rfl) ⟨3759513, by rfl⟩ : syracuseStep 10025369 = 7519027) B7519027
theorem B6683579 : Blo 1979435 6683579 := bstep (se 1 (by rfl) ⟨5012684, by rfl⟩ : syracuseStep 6683579 = 10025369) B10025369
theorem B4455719 : Blo 1979435 4455719 := bstep (se 1 (by rfl) ⟨3341789, by rfl⟩ : syracuseStep 4455719 = 6683579) B6683579
theorem B2970479 : Blo 1979435 2970479 := bstep (se 1 (by rfl) ⟨2227859, by rfl⟩ : syracuseStep 2970479 = 4455719) B4455719
theorem B1980319 : Blo 1979435 1980319 := bstep (se 1 (by rfl) ⟨1485239, by rfl⟩ : syracuseStep 1980319 = 2970479) B2970479
theorem B2970485 : Blo 1979435 2970485 := bbase (se 5 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 2970485 = 278483) (by norm_num)
theorem B1980323 : Blo 1979435 1980323 := bstep (se 1 (by rfl) ⟨1485242, by rfl⟩ : syracuseStep 1980323 = 2970485) B2970485
theorem B3011021 : Blo 1979435 3011021 := bbase (se 3 (by rfl) ⟨564566, by rfl⟩ : syracuseStep 3011021 = 1129133) (by norm_num)
theorem B2007347 : Blo 1979435 2007347 := bstep (se 1 (by rfl) ⟨1505510, by rfl⟩ : syracuseStep 2007347 = 3011021) B3011021
theorem B21411701 : Blo 1979435 21411701 := bstep (se 5 (by rfl) ⟨1003673, by rfl⟩ : syracuseStep 21411701 = 2007347) B2007347
theorem B14274467 : Blo 1979435 14274467 := bstep (se 1 (by rfl) ⟨10705850, by rfl⟩ : syracuseStep 14274467 = 21411701) B21411701
theorem B9516311 : Blo 1979435 9516311 := bstep (se 1 (by rfl) ⟨7137233, by rfl⟩ : syracuseStep 9516311 = 14274467) B14274467
theorem B6344207 : Blo 1979435 6344207 := bstep (se 1 (by rfl) ⟨4758155, by rfl⟩ : syracuseStep 6344207 = 9516311) B9516311
theorem B4229471 : Blo 1979435 4229471 := bstep (se 1 (by rfl) ⟨3172103, by rfl⟩ : syracuseStep 4229471 = 6344207) B6344207
theorem B2819647 : Blo 1979435 2819647 := bstep (se 1 (by rfl) ⟨2114735, by rfl⟩ : syracuseStep 2819647 = 4229471) B4229471
theorem B3759529 : Blo 1979435 3759529 := bstep (se 2 (by rfl) ⟨1409823, by rfl⟩ : syracuseStep 3759529 = 2819647) B2819647
theorem B5012705 : Blo 1979435 5012705 := bstep (se 2 (by rfl) ⟨1879764, by rfl⟩ : syracuseStep 5012705 = 3759529) B3759529
theorem B3341803 : Blo 1979435 3341803 := bstep (se 1 (by rfl) ⟨2506352, by rfl⟩ : syracuseStep 3341803 = 5012705) B5012705
theorem B4455737 : Blo 1979435 4455737 := bstep (se 2 (by rfl) ⟨1670901, by rfl⟩ : syracuseStep 4455737 = 3341803) B3341803
theorem B2970491 : Blo 1979435 2970491 := bstep (se 1 (by rfl) ⟨2227868, by rfl⟩ : syracuseStep 2970491 = 4455737) B4455737
theorem B1980327 : Blo 1979435 1980327 := bstep (se 1 (by rfl) ⟨1485245, by rfl⟩ : syracuseStep 1980327 = 2970491) B2970491
theorem B2227873 : Blo 1979435 2227873 := bbase (se 2 (by rfl) ⟨835452, by rfl⟩ : syracuseStep 2227873 = 1670905) (by norm_num)
theorem B2970497 : Blo 1979435 2970497 := bstep (se 2 (by rfl) ⟨1113936, by rfl⟩ : syracuseStep 2970497 = 2227873) B2227873
theorem B1980331 : Blo 1979435 1980331 := bstep (se 1 (by rfl) ⟨1485248, by rfl⟩ : syracuseStep 1980331 = 2970497) B2970497
theorem B5012725 : Blo 1979435 5012725 := bbase (se 5 (by rfl) ⟨234971, by rfl⟩ : syracuseStep 5012725 = 469943) (by norm_num)
theorem B6683633 : Blo 1979435 6683633 := bstep (se 2 (by rfl) ⟨2506362, by rfl⟩ : syracuseStep 6683633 = 5012725) B5012725
theorem B4455755 : Blo 1979435 4455755 := bstep (se 1 (by rfl) ⟨3341816, by rfl⟩ : syracuseStep 4455755 = 6683633) B6683633
theorem B2970503 : Blo 1979435 2970503 := bstep (se 1 (by rfl) ⟨2227877, by rfl⟩ : syracuseStep 2970503 = 4455755) B4455755
theorem B1980335 : Blo 1979435 1980335 := bstep (se 1 (by rfl) ⟨1485251, by rfl⟩ : syracuseStep 1980335 = 2970503) B2970503
theorem B2970509 : Blo 1979435 2970509 := bbase (se 3 (by rfl) ⟨556970, by rfl⟩ : syracuseStep 2970509 = 1113941) (by norm_num)
theorem B1980339 : Blo 1979435 1980339 := bstep (se 1 (by rfl) ⟨1485254, by rfl⟩ : syracuseStep 1980339 = 2970509) B2970509
theorem B4455773 : Blo 1979435 4455773 := bbase (se 3 (by rfl) ⟨835457, by rfl⟩ : syracuseStep 4455773 = 1670915) (by norm_num)
theorem B2970515 : Blo 1979435 2970515 := bstep (se 1 (by rfl) ⟨2227886, by rfl⟩ : syracuseStep 2970515 = 4455773) B4455773
theorem B1980343 : Blo 1979435 1980343 := bstep (se 1 (by rfl) ⟨1485257, by rfl⟩ : syracuseStep 1980343 = 2970515) B2970515
theorem B3341837 : Blo 1979435 3341837 := bbase (se 3 (by rfl) ⟨626594, by rfl⟩ : syracuseStep 3341837 = 1253189) (by norm_num)
theorem B2227891 : Blo 1979435 2227891 := bstep (se 1 (by rfl) ⟨1670918, by rfl⟩ : syracuseStep 2227891 = 3341837) B3341837
theorem B2970521 : Blo 1979435 2970521 := bstep (se 2 (by rfl) ⟨1113945, by rfl⟩ : syracuseStep 2970521 = 2227891) B2227891
theorem B1980347 : Blo 1979435 1980347 := bstep (se 1 (by rfl) ⟨1485260, by rfl⟩ : syracuseStep 1980347 = 2970521) B2970521
theorem B3172141 : Blo 1979435 3172141 := bbase (se 3 (by rfl) ⟨594776, by rfl⟩ : syracuseStep 3172141 = 1189553) (by norm_num)
theorem B16918085 : Blo 1979435 16918085 := bstep (se 4 (by rfl) ⟨1586070, by rfl⟩ : syracuseStep 16918085 = 3172141) B3172141
theorem B11278723 : Blo 1979435 11278723 := bstep (se 1 (by rfl) ⟨8459042, by rfl⟩ : syracuseStep 11278723 = 16918085) B16918085
theorem B15038297 : Blo 1979435 15038297 := bstep (se 2 (by rfl) ⟨5639361, by rfl⟩ : syracuseStep 15038297 = 11278723) B11278723
theorem B10025531 : Blo 1979435 10025531 := bstep (se 1 (by rfl) ⟨7519148, by rfl⟩ : syracuseStep 10025531 = 15038297) B15038297
theorem B6683687 : Blo 1979435 6683687 := bstep (se 1 (by rfl) ⟨5012765, by rfl⟩ : syracuseStep 6683687 = 10025531) B10025531
theorem B4455791 : Blo 1979435 4455791 := bstep (se 1 (by rfl) ⟨3341843, by rfl⟩ : syracuseStep 4455791 = 6683687) B6683687
theorem B2970527 : Blo 1979435 2970527 := bstep (se 1 (by rfl) ⟨2227895, by rfl⟩ : syracuseStep 2970527 = 4455791) B4455791
theorem B1980351 : Blo 1979435 1980351 := bstep (se 1 (by rfl) ⟨1485263, by rfl⟩ : syracuseStep 1980351 = 2970527) B2970527
theorem B2970533 : Blo 1979435 2970533 := bbase (se 4 (by rfl) ⟨278487, by rfl⟩ : syracuseStep 2970533 = 556975) (by norm_num)
theorem B1980355 : Blo 1979435 1980355 := bstep (se 1 (by rfl) ⟨1485266, by rfl⟩ : syracuseStep 1980355 = 2970533) B2970533
theorem B2506393 : Blo 1979435 2506393 := bbase (se 2 (by rfl) ⟨939897, by rfl⟩ : syracuseStep 2506393 = 1879795) (by norm_num)
theorem B3341857 : Blo 1979435 3341857 := bstep (se 2 (by rfl) ⟨1253196, by rfl⟩ : syracuseStep 3341857 = 2506393) B2506393
theorem B4455809 : Blo 1979435 4455809 := bstep (se 2 (by rfl) ⟨1670928, by rfl⟩ : syracuseStep 4455809 = 3341857) B3341857
theorem B2970539 : Blo 1979435 2970539 := bstep (se 1 (by rfl) ⟨2227904, by rfl⟩ : syracuseStep 2970539 = 4455809) B4455809
theorem B1980359 : Blo 1979435 1980359 := bstep (se 1 (by rfl) ⟨1485269, by rfl⟩ : syracuseStep 1980359 = 2970539) B2970539
theorem B2227909 : Blo 1979435 2227909 := bbase (se 4 (by rfl) ⟨208866, by rfl⟩ : syracuseStep 2227909 = 417733) (by norm_num)
theorem B2970545 : Blo 1979435 2970545 := bstep (se 2 (by rfl) ⟨1113954, by rfl⟩ : syracuseStep 2970545 = 2227909) B2227909
theorem B1980363 : Blo 1979435 1980363 := bstep (se 1 (by rfl) ⟨1485272, by rfl⟩ : syracuseStep 1980363 = 2970545) B2970545
theorem B3759605 : Blo 1979435 3759605 := bbase (se 5 (by rfl) ⟨176231, by rfl⟩ : syracuseStep 3759605 = 352463) (by norm_num)
theorem B2506403 : Blo 1979435 2506403 := bstep (se 1 (by rfl) ⟨1879802, by rfl⟩ : syracuseStep 2506403 = 3759605) B3759605
theorem B6683741 : Blo 1979435 6683741 := bstep (se 3 (by rfl) ⟨1253201, by rfl⟩ : syracuseStep 6683741 = 2506403) B2506403
theorem B4455827 : Blo 1979435 4455827 := bstep (se 1 (by rfl) ⟨3341870, by rfl⟩ : syracuseStep 4455827 = 6683741) B6683741
theorem B2970551 : Blo 1979435 2970551 := bstep (se 1 (by rfl) ⟨2227913, by rfl⟩ : syracuseStep 2970551 = 4455827) B4455827
theorem B1980367 : Blo 1979435 1980367 := bstep (se 1 (by rfl) ⟨1485275, by rfl⟩ : syracuseStep 1980367 = 2970551) B2970551
theorem B2970557 : Blo 1979435 2970557 := bbase (se 3 (by rfl) ⟨556979, by rfl⟩ : syracuseStep 2970557 = 1113959) (by norm_num)
theorem B1980371 : Blo 1979435 1980371 := bstep (se 1 (by rfl) ⟨1485278, by rfl⟩ : syracuseStep 1980371 = 2970557) B2970557
theorem B4455845 : Blo 1979435 4455845 := bbase (se 4 (by rfl) ⟨417735, by rfl⟩ : syracuseStep 4455845 = 835471) (by norm_num)
theorem B2970563 : Blo 1979435 2970563 := bstep (se 1 (by rfl) ⟨2227922, by rfl⟩ : syracuseStep 2970563 = 4455845) B4455845
theorem B1980375 : Blo 1979435 1980375 := bstep (se 1 (by rfl) ⟨1485281, by rfl⟩ : syracuseStep 1980375 = 2970563) B2970563
theorem B5012837 : Blo 1979435 5012837 := bbase (se 4 (by rfl) ⟨469953, by rfl⟩ : syracuseStep 5012837 = 939907) (by norm_num)
theorem B3341891 : Blo 1979435 3341891 := bstep (se 1 (by rfl) ⟨2506418, by rfl⟩ : syracuseStep 3341891 = 5012837) B5012837
theorem B2227927 : Blo 1979435 2227927 := bstep (se 1 (by rfl) ⟨1670945, by rfl⟩ : syracuseStep 2227927 = 3341891) B3341891
theorem B2970569 : Blo 1979435 2970569 := bstep (se 2 (by rfl) ⟨1113963, by rfl⟩ : syracuseStep 2970569 = 2227927) B2227927
theorem B1980379 : Blo 1979435 1980379 := bstep (se 1 (by rfl) ⟨1485284, by rfl⟩ : syracuseStep 1980379 = 2970569) B2970569
theorem B2379145 : Blo 1979435 2379145 := bbase (se 2 (by rfl) ⟨892179, by rfl⟩ : syracuseStep 2379145 = 1784359) (by norm_num)
theorem B3172193 : Blo 1979435 3172193 := bstep (se 2 (by rfl) ⟨1189572, by rfl⟩ : syracuseStep 3172193 = 2379145) B2379145
theorem B2114795 : Blo 1979435 2114795 := bstep (se 1 (by rfl) ⟨1586096, by rfl⟩ : syracuseStep 2114795 = 3172193) B3172193
theorem B5639453 : Blo 1979435 5639453 := bstep (se 3 (by rfl) ⟨1057397, by rfl⟩ : syracuseStep 5639453 = 2114795) B2114795
theorem B3759635 : Blo 1979435 3759635 := bstep (se 1 (by rfl) ⟨2819726, by rfl⟩ : syracuseStep 3759635 = 5639453) B5639453
theorem B10025693 : Blo 1979435 10025693 := bstep (se 3 (by rfl) ⟨1879817, by rfl⟩ : syracuseStep 10025693 = 3759635) B3759635
theorem B6683795 : Blo 1979435 6683795 := bstep (se 1 (by rfl) ⟨5012846, by rfl⟩ : syracuseStep 6683795 = 10025693) B10025693
theorem B4455863 : Blo 1979435 4455863 := bstep (se 1 (by rfl) ⟨3341897, by rfl⟩ : syracuseStep 4455863 = 6683795) B6683795
theorem B2970575 : Blo 1979435 2970575 := bstep (se 1 (by rfl) ⟨2227931, by rfl⟩ : syracuseStep 2970575 = 4455863) B4455863
theorem B1980383 : Blo 1979435 1980383 := bstep (se 1 (by rfl) ⟨1485287, by rfl⟩ : syracuseStep 1980383 = 2970575) B2970575
theorem B2970581 : Blo 1979435 2970581 := bbase (se 7 (by rfl) ⟨34811, by rfl⟩ : syracuseStep 2970581 = 69623) (by norm_num)
theorem B1980387 : Blo 1979435 1980387 := bstep (se 1 (by rfl) ⟨1485290, by rfl⟩ : syracuseStep 1980387 = 2970581) B2970581
theorem B7519301 : Blo 1979435 7519301 := bbase (se 4 (by rfl) ⟨704934, by rfl⟩ : syracuseStep 7519301 = 1409869) (by norm_num)
theorem B5012867 : Blo 1979435 5012867 := bstep (se 1 (by rfl) ⟨3759650, by rfl⟩ : syracuseStep 5012867 = 7519301) B7519301
theorem B3341911 : Blo 1979435 3341911 := bstep (se 1 (by rfl) ⟨2506433, by rfl⟩ : syracuseStep 3341911 = 5012867) B5012867
theorem B4455881 : Blo 1979435 4455881 := bstep (se 2 (by rfl) ⟨1670955, by rfl⟩ : syracuseStep 4455881 = 3341911) B3341911
theorem B2970587 : Blo 1979435 2970587 := bstep (se 1 (by rfl) ⟨2227940, by rfl⟩ : syracuseStep 2970587 = 4455881) B4455881
theorem B1980391 : Blo 1979435 1980391 := bstep (se 1 (by rfl) ⟨1485293, by rfl⟩ : syracuseStep 1980391 = 2970587) B2970587
theorem B2227945 : Blo 1979435 2227945 := bbase (se 2 (by rfl) ⟨835479, by rfl⟩ : syracuseStep 2227945 = 1670959) (by norm_num)
theorem B2970593 : Blo 1979435 2970593 := bstep (se 2 (by rfl) ⟨1113972, by rfl⟩ : syracuseStep 2970593 = 2227945) B2227945
theorem B1980395 : Blo 1979435 1980395 := bstep (se 1 (by rfl) ⟨1485296, by rfl⟩ : syracuseStep 1980395 = 2970593) B2970593
theorem B11278997 : Blo 1979435 11278997 := bbase (se 6 (by rfl) ⟨264351, by rfl⟩ : syracuseStep 11278997 = 528703) (by norm_num)
theorem B7519331 : Blo 1979435 7519331 := bstep (se 1 (by rfl) ⟨5639498, by rfl⟩ : syracuseStep 7519331 = 11278997) B11278997
theorem B5012887 : Blo 1979435 5012887 := bstep (se 1 (by rfl) ⟨3759665, by rfl⟩ : syracuseStep 5012887 = 7519331) B7519331
theorem B6683849 : Blo 1979435 6683849 := bstep (se 2 (by rfl) ⟨2506443, by rfl⟩ : syracuseStep 6683849 = 5012887) B5012887
theorem B4455899 : Blo 1979435 4455899 := bstep (se 1 (by rfl) ⟨3341924, by rfl⟩ : syracuseStep 4455899 = 6683849) B6683849
theorem B2970599 : Blo 1979435 2970599 := bstep (se 1 (by rfl) ⟨2227949, by rfl⟩ : syracuseStep 2970599 = 4455899) B4455899
theorem B1980399 : Blo 1979435 1980399 := bstep (se 1 (by rfl) ⟨1485299, by rfl⟩ : syracuseStep 1980399 = 2970599) B2970599
theorem B2970605 : Blo 1979435 2970605 := bbase (se 3 (by rfl) ⟨556988, by rfl⟩ : syracuseStep 2970605 = 1113977) (by norm_num)
theorem B1980403 : Blo 1979435 1980403 := bstep (se 1 (by rfl) ⟨1485302, by rfl⟩ : syracuseStep 1980403 = 2970605) B2970605
theorem B4455917 : Blo 1979435 4455917 := bbase (se 3 (by rfl) ⟨835484, by rfl⟩ : syracuseStep 4455917 = 1670969) (by norm_num)
theorem B2970611 : Blo 1979435 2970611 := bstep (se 1 (by rfl) ⟨2227958, by rfl⟩ : syracuseStep 2970611 = 4455917) B4455917
theorem B1980407 : Blo 1979435 1980407 := bstep (se 1 (by rfl) ⟨1485305, by rfl⟩ : syracuseStep 1980407 = 2970611) B2970611
theorem B2007433 : Blo 1979435 2007433 := bbase (se 2 (by rfl) ⟨752787, by rfl⟩ : syracuseStep 2007433 = 1505575) (by norm_num)
theorem B2676577 : Blo 1979435 2676577 := bstep (se 2 (by rfl) ⟨1003716, by rfl⟩ : syracuseStep 2676577 = 2007433) B2007433
theorem B3568769 : Blo 1979435 3568769 := bstep (se 2 (by rfl) ⟨1338288, by rfl⟩ : syracuseStep 3568769 = 2676577) B2676577
theorem B2379179 : Blo 1979435 2379179 := bstep (se 1 (by rfl) ⟨1784384, by rfl⟩ : syracuseStep 2379179 = 3568769) B3568769
theorem B6344477 : Blo 1979435 6344477 := bstep (se 3 (by rfl) ⟨1189589, by rfl⟩ : syracuseStep 6344477 = 2379179) B2379179
theorem B4229651 : Blo 1979435 4229651 := bstep (se 1 (by rfl) ⟨3172238, by rfl⟩ : syracuseStep 4229651 = 6344477) B6344477
theorem B2819767 : Blo 1979435 2819767 := bstep (se 1 (by rfl) ⟨2114825, by rfl⟩ : syracuseStep 2819767 = 4229651) B4229651
theorem B3759689 : Blo 1979435 3759689 := bstep (se 2 (by rfl) ⟨1409883, by rfl⟩ : syracuseStep 3759689 = 2819767) B2819767
theorem B2506459 : Blo 1979435 2506459 := bstep (se 1 (by rfl) ⟨1879844, by rfl⟩ : syracuseStep 2506459 = 3759689) B3759689
theorem B3341945 : Blo 1979435 3341945 := bstep (se 2 (by rfl) ⟨1253229, by rfl⟩ : syracuseStep 3341945 = 2506459) B2506459
theorem B2227963 : Blo 1979435 2227963 := bstep (se 1 (by rfl) ⟨1670972, by rfl⟩ : syracuseStep 2227963 = 3341945) B3341945
theorem B2970617 : Blo 1979435 2970617 := bstep (se 2 (by rfl) ⟨1113981, by rfl⟩ : syracuseStep 2970617 = 2227963) B2227963
theorem B1980411 : Blo 1979435 1980411 := bstep (se 1 (by rfl) ⟨1485308, by rfl⟩ : syracuseStep 1980411 = 2970617) B2970617
theorem B4287365 : Blo 1979435 4287365 := bbase (se 4 (by rfl) ⟨401940, by rfl⟩ : syracuseStep 4287365 = 803881) (by norm_num)
theorem B2858243 : Blo 1979435 2858243 := bstep (se 1 (by rfl) ⟨2143682, by rfl⟩ : syracuseStep 2858243 = 4287365) B4287365
theorem B30487925 : Blo 1979435 30487925 := bstep (se 5 (by rfl) ⟨1429121, by rfl⟩ : syracuseStep 30487925 = 2858243) B2858243
theorem B81301133 : Blo 1979435 81301133 := bstep (se 3 (by rfl) ⟨15243962, by rfl⟩ : syracuseStep 81301133 = 30487925) B30487925
theorem B54200755 : Blo 1979435 54200755 := bstep (se 1 (by rfl) ⟨40650566, by rfl⟩ : syracuseStep 54200755 = 81301133) B81301133
theorem B72267673 : Blo 1979435 72267673 := bstep (se 2 (by rfl) ⟨27100377, by rfl⟩ : syracuseStep 72267673 = 54200755) B54200755
theorem B96356897 : Blo 1979435 96356897 := bstep (se 2 (by rfl) ⟨36133836, by rfl⟩ : syracuseStep 96356897 = 72267673) B72267673
theorem B64237931 : Blo 1979435 64237931 := bstep (se 1 (by rfl) ⟨48178448, by rfl⟩ : syracuseStep 64237931 = 96356897) B96356897
theorem B42825287 : Blo 1979435 42825287 := bstep (se 1 (by rfl) ⟨32118965, by rfl⟩ : syracuseStep 42825287 = 64237931) B64237931
theorem B114200765 : Blo 1979435 114200765 := bstep (se 3 (by rfl) ⟨21412643, by rfl⟩ : syracuseStep 114200765 = 42825287) B42825287
theorem B76133843 : Blo 1979435 76133843 := bstep (se 1 (by rfl) ⟨57100382, by rfl⟩ : syracuseStep 76133843 = 114200765) B114200765
theorem B50755895 : Blo 1979435 50755895 := bstep (se 1 (by rfl) ⟨38066921, by rfl⟩ : syracuseStep 50755895 = 76133843) B76133843
theorem B33837263 : Blo 1979435 33837263 := bstep (se 1 (by rfl) ⟨25377947, by rfl⟩ : syracuseStep 33837263 = 50755895) B50755895
theorem B22558175 : Blo 1979435 22558175 := bstep (se 1 (by rfl) ⟨16918631, by rfl⟩ : syracuseStep 22558175 = 33837263) B33837263
theorem B15038783 : Blo 1979435 15038783 := bstep (se 1 (by rfl) ⟨11279087, by rfl⟩ : syracuseStep 15038783 = 22558175) B22558175
theorem B10025855 : Blo 1979435 10025855 := bstep (se 1 (by rfl) ⟨7519391, by rfl⟩ : syracuseStep 10025855 = 15038783) B15038783
theorem B6683903 : Blo 1979435 6683903 := bstep (se 1 (by rfl) ⟨5012927, by rfl⟩ : syracuseStep 6683903 = 10025855) B10025855
theorem B4455935 : Blo 1979435 4455935 := bstep (se 1 (by rfl) ⟨3341951, by rfl⟩ : syracuseStep 4455935 = 6683903) B6683903
theorem B2970623 : Blo 1979435 2970623 := bstep (se 1 (by rfl) ⟨2227967, by rfl⟩ : syracuseStep 2970623 = 4455935) B4455935
theorem B1980415 : Blo 1979435 1980415 := bstep (se 1 (by rfl) ⟨1485311, by rfl⟩ : syracuseStep 1980415 = 2970623) B2970623
theorem B2970629 : Blo 1979435 2970629 := bbase (se 4 (by rfl) ⟨278496, by rfl⟩ : syracuseStep 2970629 = 556993) (by norm_num)
theorem B1980419 : Blo 1979435 1980419 := bstep (se 1 (by rfl) ⟨1485314, by rfl⟩ : syracuseStep 1980419 = 2970629) B2970629
theorem B3341965 : Blo 1979435 3341965 := bbase (se 3 (by rfl) ⟨626618, by rfl⟩ : syracuseStep 3341965 = 1253237) (by norm_num)
theorem B4455953 : Blo 1979435 4455953 := bstep (se 2 (by rfl) ⟨1670982, by rfl⟩ : syracuseStep 4455953 = 3341965) B3341965
theorem B2970635 : Blo 1979435 2970635 := bstep (se 1 (by rfl) ⟨2227976, by rfl⟩ : syracuseStep 2970635 = 4455953) B4455953
theorem B1980423 : Blo 1979435 1980423 := bstep (se 1 (by rfl) ⟨1485317, by rfl⟩ : syracuseStep 1980423 = 2970635) B2970635
theorem B2227981 : Blo 1979435 2227981 := bbase (se 3 (by rfl) ⟨417746, by rfl⟩ : syracuseStep 2227981 = 835493) (by norm_num)
theorem B2970641 : Blo 1979435 2970641 := bstep (se 2 (by rfl) ⟨1113990, by rfl⟩ : syracuseStep 2970641 = 2227981) B2227981
theorem B1980427 : Blo 1979435 1980427 := bstep (se 1 (by rfl) ⟨1485320, by rfl⟩ : syracuseStep 1980427 = 2970641) B2970641
theorem B6683957 : Blo 1979435 6683957 := bbase (se 5 (by rfl) ⟨313310, by rfl⟩ : syracuseStep 6683957 = 626621) (by norm_num)
theorem B4455971 : Blo 1979435 4455971 := bstep (se 1 (by rfl) ⟨3341978, by rfl⟩ : syracuseStep 4455971 = 6683957) B6683957
theorem B2970647 : Blo 1979435 2970647 := bstep (se 1 (by rfl) ⟨2227985, by rfl⟩ : syracuseStep 2970647 = 4455971) B4455971
theorem B1980431 : Blo 1979435 1980431 := bstep (se 1 (by rfl) ⟨1485323, by rfl⟩ : syracuseStep 1980431 = 2970647) B2970647
theorem B2970653 : Blo 1979435 2970653 := bbase (se 3 (by rfl) ⟨556997, by rfl⟩ : syracuseStep 2970653 = 1113995) (by norm_num)
theorem B1980435 : Blo 1979435 1980435 := bstep (se 1 (by rfl) ⟨1485326, by rfl⟩ : syracuseStep 1980435 = 2970653) B2970653
theorem B4455989 : Blo 1979435 4455989 := bbase (se 5 (by rfl) ⟨208874, by rfl⟩ : syracuseStep 4455989 = 417749) (by norm_num)
theorem B2970659 : Blo 1979435 2970659 := bstep (se 1 (by rfl) ⟨2227994, by rfl⟩ : syracuseStep 2970659 = 4455989) B4455989
theorem B1980439 : Blo 1979435 1980439 := bstep (se 1 (by rfl) ⟨1485329, by rfl⟩ : syracuseStep 1980439 = 2970659) B2970659
theorem B2379217 : Blo 1979435 2379217 := bbase (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) (by norm_num)
theorem B3172289 : Blo 1979435 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B8459437 : Blo 1979435 8459437 := bstep (se 3 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 8459437 = 3172289) B3172289
theorem B11279249 : Blo 1979435 11279249 := bstep (se 2 (by rfl) ⟨4229718, by rfl⟩ : syracuseStep 11279249 = 8459437) B8459437
theorem B7519499 : Blo 1979435 7519499 := bstep (se 1 (by rfl) ⟨5639624, by rfl⟩ : syracuseStep 7519499 = 11279249) B11279249
theorem B5012999 : Blo 1979435 5012999 := bstep (se 1 (by rfl) ⟨3759749, by rfl⟩ : syracuseStep 5012999 = 7519499) B7519499
theorem B3341999 : Blo 1979435 3341999 := bstep (se 1 (by rfl) ⟨2506499, by rfl⟩ : syracuseStep 3341999 = 5012999) B5012999
theorem B2227999 : Blo 1979435 2227999 := bstep (se 1 (by rfl) ⟨1670999, by rfl⟩ : syracuseStep 2227999 = 3341999) B3341999
theorem B2970665 : Blo 1979435 2970665 := bstep (se 2 (by rfl) ⟨1113999, by rfl⟩ : syracuseStep 2970665 = 2227999) B2227999
theorem B1980443 : Blo 1979435 1980443 := bstep (se 1 (by rfl) ⟨1485332, by rfl⟩ : syracuseStep 1980443 = 2970665) B2970665
theorem B4516805 : Blo 1979435 4516805 := bbase (se 4 (by rfl) ⟨423450, by rfl⟩ : syracuseStep 4516805 = 846901) (by norm_num)
theorem B3011203 : Blo 1979435 3011203 := bstep (se 1 (by rfl) ⟨2258402, by rfl⟩ : syracuseStep 3011203 = 4516805) B4516805
theorem B4014937 : Blo 1979435 4014937 := bstep (se 2 (by rfl) ⟨1505601, by rfl⟩ : syracuseStep 4014937 = 3011203) B3011203
theorem B5353249 : Blo 1979435 5353249 := bstep (se 2 (by rfl) ⟨2007468, by rfl⟩ : syracuseStep 5353249 = 4014937) B4014937
theorem B7137665 : Blo 1979435 7137665 := bstep (se 2 (by rfl) ⟨2676624, by rfl⟩ : syracuseStep 7137665 = 5353249) B5353249
theorem B4758443 : Blo 1979435 4758443 := bstep (se 1 (by rfl) ⟨3568832, by rfl⟩ : syracuseStep 4758443 = 7137665) B7137665
theorem B3172295 : Blo 1979435 3172295 := bstep (se 1 (by rfl) ⟨2379221, by rfl⟩ : syracuseStep 3172295 = 4758443) B4758443
theorem B8459453 : Blo 1979435 8459453 := bstep (se 3 (by rfl) ⟨1586147, by rfl⟩ : syracuseStep 8459453 = 3172295) B3172295
theorem B5639635 : Blo 1979435 5639635 := bstep (se 1 (by rfl) ⟨4229726, by rfl⟩ : syracuseStep 5639635 = 8459453) B8459453
theorem B7519513 : Blo 1979435 7519513 := bstep (se 2 (by rfl) ⟨2819817, by rfl⟩ : syracuseStep 7519513 = 5639635) B5639635
theorem B10026017 : Blo 1979435 10026017 := bstep (se 2 (by rfl) ⟨3759756, by rfl⟩ : syracuseStep 10026017 = 7519513) B7519513
theorem B6684011 : Blo 1979435 6684011 := bstep (se 1 (by rfl) ⟨5013008, by rfl⟩ : syracuseStep 6684011 = 10026017) B10026017
theorem B4456007 : Blo 1979435 4456007 := bstep (se 1 (by rfl) ⟨3342005, by rfl⟩ : syracuseStep 4456007 = 6684011) B6684011
theorem B2970671 : Blo 1979435 2970671 := bstep (se 1 (by rfl) ⟨2228003, by rfl⟩ : syracuseStep 2970671 = 4456007) B4456007
theorem B1980447 : Blo 1979435 1980447 := bstep (se 1 (by rfl) ⟨1485335, by rfl⟩ : syracuseStep 1980447 = 2970671) B2970671
theorem B2970677 : Blo 1979435 2970677 := bbase (se 5 (by rfl) ⟨139250, by rfl⟩ : syracuseStep 2970677 = 278501) (by norm_num)
theorem B1980451 : Blo 1979435 1980451 := bstep (se 1 (by rfl) ⟨1485338, by rfl⟩ : syracuseStep 1980451 = 2970677) B2970677
theorem B5013029 : Blo 1979435 5013029 := bbase (se 4 (by rfl) ⟨469971, by rfl⟩ : syracuseStep 5013029 = 939943) (by norm_num)
theorem B3342019 : Blo 1979435 3342019 := bstep (se 1 (by rfl) ⟨2506514, by rfl⟩ : syracuseStep 3342019 = 5013029) B5013029
theorem B4456025 : Blo 1979435 4456025 := bstep (se 2 (by rfl) ⟨1671009, by rfl⟩ : syracuseStep 4456025 = 3342019) B3342019
theorem B2970683 : Blo 1979435 2970683 := bstep (se 1 (by rfl) ⟨2228012, by rfl⟩ : syracuseStep 2970683 = 4456025) B4456025
theorem B1980455 : Blo 1979435 1980455 := bstep (se 1 (by rfl) ⟨1485341, by rfl⟩ : syracuseStep 1980455 = 2970683) B2970683
theorem B2228017 : Blo 1979435 2228017 := bbase (se 2 (by rfl) ⟨835506, by rfl⟩ : syracuseStep 2228017 = 1671013) (by norm_num)
theorem B2970689 : Blo 1979435 2970689 := bstep (se 2 (by rfl) ⟨1114008, by rfl⟩ : syracuseStep 2970689 = 2228017) B2228017
theorem B1980459 : Blo 1979435 1980459 := bstep (se 1 (by rfl) ⟨1485344, by rfl⟩ : syracuseStep 1980459 = 2970689) B2970689
theorem B2379241 : Blo 1979435 2379241 := bbase (se 2 (by rfl) ⟨892215, by rfl⟩ : syracuseStep 2379241 = 1784431) (by norm_num)
theorem B3172321 : Blo 1979435 3172321 := bstep (se 2 (by rfl) ⟨1189620, by rfl⟩ : syracuseStep 3172321 = 2379241) B2379241
theorem B4229761 : Blo 1979435 4229761 := bstep (se 2 (by rfl) ⟨1586160, by rfl⟩ : syracuseStep 4229761 = 3172321) B3172321
theorem B5639681 : Blo 1979435 5639681 := bstep (se 2 (by rfl) ⟨2114880, by rfl⟩ : syracuseStep 5639681 = 4229761) B4229761
theorem B3759787 : Blo 1979435 3759787 := bstep (se 1 (by rfl) ⟨2819840, by rfl⟩ : syracuseStep 3759787 = 5639681) B5639681
theorem B5013049 : Blo 1979435 5013049 := bstep (se 2 (by rfl) ⟨1879893, by rfl⟩ : syracuseStep 5013049 = 3759787) B3759787
theorem B6684065 : Blo 1979435 6684065 := bstep (se 2 (by rfl) ⟨2506524, by rfl⟩ : syracuseStep 6684065 = 5013049) B5013049
theorem B4456043 : Blo 1979435 4456043 := bstep (se 1 (by rfl) ⟨3342032, by rfl⟩ : syracuseStep 4456043 = 6684065) B6684065
theorem B2970695 : Blo 1979435 2970695 := bstep (se 1 (by rfl) ⟨2228021, by rfl⟩ : syracuseStep 2970695 = 4456043) B4456043
theorem B1980463 : Blo 1979435 1980463 := bstep (se 1 (by rfl) ⟨1485347, by rfl⟩ : syracuseStep 1980463 = 2970695) B2970695
theorem B2970701 : Blo 1979435 2970701 := bbase (se 3 (by rfl) ⟨557006, by rfl⟩ : syracuseStep 2970701 = 1114013) (by norm_num)
theorem B1980467 : Blo 1979435 1980467 := bstep (se 1 (by rfl) ⟨1485350, by rfl⟩ : syracuseStep 1980467 = 2970701) B2970701
theorem B4456061 : Blo 1979435 4456061 := bbase (se 3 (by rfl) ⟨835511, by rfl⟩ : syracuseStep 4456061 = 1671023) (by norm_num)
theorem B2970707 : Blo 1979435 2970707 := bstep (se 1 (by rfl) ⟨2228030, by rfl⟩ : syracuseStep 2970707 = 4456061) B4456061
theorem B1980471 : Blo 1979435 1980471 := bstep (se 1 (by rfl) ⟨1485353, by rfl⟩ : syracuseStep 1980471 = 2970707) B2970707
theorem B3342053 : Blo 1979435 3342053 := bbase (se 4 (by rfl) ⟨313317, by rfl⟩ : syracuseStep 3342053 = 626635) (by norm_num)
theorem B2228035 : Blo 1979435 2228035 := bstep (se 1 (by rfl) ⟨1671026, by rfl⟩ : syracuseStep 2228035 = 3342053) B3342053
theorem B2970713 : Blo 1979435 2970713 := bstep (se 2 (by rfl) ⟨1114017, by rfl⟩ : syracuseStep 2970713 = 2228035) B2228035
theorem B1980475 : Blo 1979435 1980475 := bstep (se 1 (by rfl) ⟨1485356, by rfl⟩ : syracuseStep 1980475 = 2970713) B2970713
theorem B6344693 : Blo 1979435 6344693 := bbase (se 5 (by rfl) ⟨297407, by rfl⟩ : syracuseStep 6344693 = 594815) (by norm_num)
theorem B4229795 : Blo 1979435 4229795 := bstep (se 1 (by rfl) ⟨3172346, by rfl⟩ : syracuseStep 4229795 = 6344693) B6344693
theorem B2819863 : Blo 1979435 2819863 := bstep (se 1 (by rfl) ⟨2114897, by rfl⟩ : syracuseStep 2819863 = 4229795) B4229795
theorem B15039269 : Blo 1979435 15039269 := bstep (se 4 (by rfl) ⟨1409931, by rfl⟩ : syracuseStep 15039269 = 2819863) B2819863
theorem B10026179 : Blo 1979435 10026179 := bstep (se 1 (by rfl) ⟨7519634, by rfl⟩ : syracuseStep 10026179 = 15039269) B15039269
theorem B6684119 : Blo 1979435 6684119 := bstep (se 1 (by rfl) ⟨5013089, by rfl⟩ : syracuseStep 6684119 = 10026179) B10026179
theorem B4456079 : Blo 1979435 4456079 := bstep (se 1 (by rfl) ⟨3342059, by rfl⟩ : syracuseStep 4456079 = 6684119) B6684119
theorem B2970719 : Blo 1979435 2970719 := bstep (se 1 (by rfl) ⟨2228039, by rfl⟩ : syracuseStep 2970719 = 4456079) B4456079
theorem B1980479 : Blo 1979435 1980479 := bstep (se 1 (by rfl) ⟨1485359, by rfl⟩ : syracuseStep 1980479 = 2970719) B2970719
theorem B2970725 : Blo 1979435 2970725 := bbase (se 4 (by rfl) ⟨278505, by rfl⟩ : syracuseStep 2970725 = 557011) (by norm_num)
theorem B1980483 : Blo 1979435 1980483 := bstep (se 1 (by rfl) ⟨1485362, by rfl⟩ : syracuseStep 1980483 = 2970725) B2970725
theorem B4229813 : Blo 1979435 4229813 := bbase (se 5 (by rfl) ⟨198272, by rfl⟩ : syracuseStep 4229813 = 396545) (by norm_num)
theorem B2819875 : Blo 1979435 2819875 := bstep (se 1 (by rfl) ⟨2114906, by rfl⟩ : syracuseStep 2819875 = 4229813) B4229813
theorem B3759833 : Blo 1979435 3759833 := bstep (se 2 (by rfl) ⟨1409937, by rfl⟩ : syracuseStep 3759833 = 2819875) B2819875
theorem B2506555 : Blo 1979435 2506555 := bstep (se 1 (by rfl) ⟨1879916, by rfl⟩ : syracuseStep 2506555 = 3759833) B3759833
theorem B3342073 : Blo 1979435 3342073 := bstep (se 2 (by rfl) ⟨1253277, by rfl⟩ : syracuseStep 3342073 = 2506555) B2506555
theorem B4456097 : Blo 1979435 4456097 := bstep (se 2 (by rfl) ⟨1671036, by rfl⟩ : syracuseStep 4456097 = 3342073) B3342073
theorem B2970731 : Blo 1979435 2970731 := bstep (se 1 (by rfl) ⟨2228048, by rfl⟩ : syracuseStep 2970731 = 4456097) B4456097
theorem B1980487 : Blo 1979435 1980487 := bstep (se 1 (by rfl) ⟨1485365, by rfl⟩ : syracuseStep 1980487 = 2970731) B2970731
theorem B2228053 : Blo 1979435 2228053 := bbase (se 9 (by rfl) ⟨6527, by rfl⟩ : syracuseStep 2228053 = 13055) (by norm_num)
theorem B2970737 : Blo 1979435 2970737 := bstep (se 2 (by rfl) ⟨1114026, by rfl⟩ : syracuseStep 2970737 = 2228053) B2228053
theorem B1980491 : Blo 1979435 1980491 := bstep (se 1 (by rfl) ⟨1485368, by rfl⟩ : syracuseStep 1980491 = 2970737) B2970737
theorem B2506565 : Blo 1979435 2506565 := bbase (se 4 (by rfl) ⟨234990, by rfl⟩ : syracuseStep 2506565 = 469981) (by norm_num)
theorem B6684173 : Blo 1979435 6684173 := bstep (se 3 (by rfl) ⟨1253282, by rfl⟩ : syracuseStep 6684173 = 2506565) B2506565
theorem B4456115 : Blo 1979435 4456115 := bstep (se 1 (by rfl) ⟨3342086, by rfl⟩ : syracuseStep 4456115 = 6684173) B6684173
theorem B2970743 : Blo 1979435 2970743 := bstep (se 1 (by rfl) ⟨2228057, by rfl⟩ : syracuseStep 2970743 = 4456115) B4456115
theorem B1980495 : Blo 1979435 1980495 := bstep (se 1 (by rfl) ⟨1485371, by rfl⟩ : syracuseStep 1980495 = 2970743) B2970743
theorem B2970749 : Blo 1979435 2970749 := bbase (se 3 (by rfl) ⟨557015, by rfl⟩ : syracuseStep 2970749 = 1114031) (by norm_num)
theorem B1980499 : Blo 1979435 1980499 := bstep (se 1 (by rfl) ⟨1485374, by rfl⟩ : syracuseStep 1980499 = 2970749) B2970749
theorem B4456133 : Blo 1979435 4456133 := bbase (se 4 (by rfl) ⟨417762, by rfl⟩ : syracuseStep 4456133 = 835525) (by norm_num)
theorem B2970755 : Blo 1979435 2970755 := bstep (se 1 (by rfl) ⟨2228066, by rfl⟩ : syracuseStep 2970755 = 4456133) B4456133
theorem B1980503 : Blo 1979435 1980503 := bstep (se 1 (by rfl) ⟨1485377, by rfl⟩ : syracuseStep 1980503 = 2970755) B2970755
theorem B5873813 : Blo 1979435 5873813 := bbase (se 6 (by rfl) ⟨137667, by rfl⟩ : syracuseStep 5873813 = 275335) (by norm_num)
theorem B3915875 : Blo 1979435 3915875 := bstep (se 1 (by rfl) ⟨2936906, by rfl⟩ : syracuseStep 3915875 = 5873813) B5873813
theorem B10442333 : Blo 1979435 10442333 := bstep (se 3 (by rfl) ⟨1957937, by rfl⟩ : syracuseStep 10442333 = 3915875) B3915875
theorem B6961555 : Blo 1979435 6961555 := bstep (se 1 (by rfl) ⟨5221166, by rfl⟩ : syracuseStep 6961555 = 10442333) B10442333
theorem B9282073 : Blo 1979435 9282073 := bstep (se 2 (by rfl) ⟨3480777, by rfl⟩ : syracuseStep 9282073 = 6961555) B6961555
theorem B12376097 : Blo 1979435 12376097 := bstep (se 2 (by rfl) ⟨4641036, by rfl⟩ : syracuseStep 12376097 = 9282073) B9282073
theorem B8250731 : Blo 1979435 8250731 := bstep (se 1 (by rfl) ⟨6188048, by rfl⟩ : syracuseStep 8250731 = 12376097) B12376097
theorem B5500487 : Blo 1979435 5500487 := bstep (se 1 (by rfl) ⟨4125365, by rfl⟩ : syracuseStep 5500487 = 8250731) B8250731
theorem B3666991 : Blo 1979435 3666991 := bstep (se 1 (by rfl) ⟨2750243, by rfl⟩ : syracuseStep 3666991 = 5500487) B5500487
theorem B4889321 : Blo 1979435 4889321 := bstep (se 2 (by rfl) ⟨1833495, by rfl⟩ : syracuseStep 4889321 = 3666991) B3666991
theorem B3259547 : Blo 1979435 3259547 := bstep (se 1 (by rfl) ⟨2444660, by rfl⟩ : syracuseStep 3259547 = 4889321) B4889321
theorem B2173031 : Blo 1979435 2173031 := bstep (se 1 (by rfl) ⟨1629773, by rfl⟩ : syracuseStep 2173031 = 3259547) B3259547
theorem B23178997 : Blo 1979435 23178997 := bstep (se 5 (by rfl) ⟨1086515, by rfl⟩ : syracuseStep 23178997 = 2173031) B2173031
theorem B30905329 : Blo 1979435 30905329 := bstep (se 2 (by rfl) ⟨11589498, by rfl⟩ : syracuseStep 30905329 = 23178997) B23178997
theorem B41207105 : Blo 1979435 41207105 := bstep (se 2 (by rfl) ⟨15452664, by rfl⟩ : syracuseStep 41207105 = 30905329) B30905329
theorem B27471403 : Blo 1979435 27471403 := bstep (se 1 (by rfl) ⟨20603552, by rfl⟩ : syracuseStep 27471403 = 41207105) B41207105
theorem B36628537 : Blo 1979435 36628537 := bstep (se 2 (by rfl) ⟨13735701, by rfl⟩ : syracuseStep 36628537 = 27471403) B27471403
theorem B48838049 : Blo 1979435 48838049 := bstep (se 2 (by rfl) ⟨18314268, by rfl⟩ : syracuseStep 48838049 = 36628537) B36628537
theorem B32558699 : Blo 1979435 32558699 := bstep (se 1 (by rfl) ⟨24419024, by rfl⟩ : syracuseStep 32558699 = 48838049) B48838049
theorem B21705799 : Blo 1979435 21705799 := bstep (se 1 (by rfl) ⟨16279349, by rfl⟩ : syracuseStep 21705799 = 32558699) B32558699
theorem B28941065 : Blo 1979435 28941065 := bstep (se 2 (by rfl) ⟨10852899, by rfl⟩ : syracuseStep 28941065 = 21705799) B21705799
theorem B19294043 : Blo 1979435 19294043 := bstep (se 1 (by rfl) ⟨14470532, by rfl⟩ : syracuseStep 19294043 = 28941065) B28941065
theorem B205803125 : Blo 1979435 205803125 := bstep (se 5 (by rfl) ⟨9647021, by rfl⟩ : syracuseStep 205803125 = 19294043) B19294043
theorem B137202083 : Blo 1979435 137202083 := bstep (se 1 (by rfl) ⟨102901562, by rfl⟩ : syracuseStep 137202083 = 205803125) B205803125
theorem B91468055 : Blo 1979435 91468055 := bstep (se 1 (by rfl) ⟨68601041, by rfl⟩ : syracuseStep 91468055 = 137202083) B137202083
theorem B243914813 : Blo 1979435 243914813 := bstep (se 3 (by rfl) ⟨45734027, by rfl⟩ : syracuseStep 243914813 = 91468055) B91468055
theorem B162609875 : Blo 1979435 162609875 := bstep (se 1 (by rfl) ⟨121957406, by rfl⟩ : syracuseStep 162609875 = 243914813) B243914813
theorem B108406583 : Blo 1979435 108406583 := bstep (se 1 (by rfl) ⟨81304937, by rfl⟩ : syracuseStep 108406583 = 162609875) B162609875
theorem B72271055 : Blo 1979435 72271055 := bstep (se 1 (by rfl) ⟨54203291, by rfl⟩ : syracuseStep 72271055 = 108406583) B108406583
theorem B48180703 : Blo 1979435 48180703 := bstep (se 1 (by rfl) ⟨36135527, by rfl⟩ : syracuseStep 48180703 = 72271055) B72271055
theorem B64240937 : Blo 1979435 64240937 := bstep (se 2 (by rfl) ⟨24090351, by rfl⟩ : syracuseStep 64240937 = 48180703) B48180703
theorem B42827291 : Blo 1979435 42827291 := bstep (se 1 (by rfl) ⟨32120468, by rfl⟩ : syracuseStep 42827291 = 64240937) B64240937
theorem B28551527 : Blo 1979435 28551527 := bstep (se 1 (by rfl) ⟨21413645, by rfl⟩ : syracuseStep 28551527 = 42827291) B42827291
theorem B19034351 : Blo 1979435 19034351 := bstep (se 1 (by rfl) ⟨14275763, by rfl⟩ : syracuseStep 19034351 = 28551527) B28551527
theorem B12689567 : Blo 1979435 12689567 := bstep (se 1 (by rfl) ⟨9517175, by rfl⟩ : syracuseStep 12689567 = 19034351) B19034351
theorem B8459711 : Blo 1979435 8459711 := bstep (se 1 (by rfl) ⟨6344783, by rfl⟩ : syracuseStep 8459711 = 12689567) B12689567
theorem B5639807 : Blo 1979435 5639807 := bstep (se 1 (by rfl) ⟨4229855, by rfl⟩ : syracuseStep 5639807 = 8459711) B8459711
theorem B3759871 : Blo 1979435 3759871 := bstep (se 1 (by rfl) ⟨2819903, by rfl⟩ : syracuseStep 3759871 = 5639807) B5639807
theorem B5013161 : Blo 1979435 5013161 := bstep (se 2 (by rfl) ⟨1879935, by rfl⟩ : syracuseStep 5013161 = 3759871) B3759871
theorem B3342107 : Blo 1979435 3342107 := bstep (se 1 (by rfl) ⟨2506580, by rfl⟩ : syracuseStep 3342107 = 5013161) B5013161
theorem B2228071 : Blo 1979435 2228071 := bstep (se 1 (by rfl) ⟨1671053, by rfl⟩ : syracuseStep 2228071 = 3342107) B3342107
theorem B2970761 : Blo 1979435 2970761 := bstep (se 2 (by rfl) ⟨1114035, by rfl⟩ : syracuseStep 2970761 = 2228071) B2228071
theorem B1980507 : Blo 1979435 1980507 := bstep (se 1 (by rfl) ⟨1485380, by rfl⟩ : syracuseStep 1980507 = 2970761) B2970761
theorem B10026341 : Blo 1979435 10026341 := bbase (se 4 (by rfl) ⟨939969, by rfl⟩ : syracuseStep 10026341 = 1879939) (by norm_num)
theorem B6684227 : Blo 1979435 6684227 := bstep (se 1 (by rfl) ⟨5013170, by rfl⟩ : syracuseStep 6684227 = 10026341) B10026341
theorem B4456151 : Blo 1979435 4456151 := bstep (se 1 (by rfl) ⟨3342113, by rfl⟩ : syracuseStep 4456151 = 6684227) B6684227
theorem B2970767 : Blo 1979435 2970767 := bstep (se 1 (by rfl) ⟨2228075, by rfl⟩ : syracuseStep 2970767 = 4456151) B4456151
theorem B1980511 : Blo 1979435 1980511 := bstep (se 1 (by rfl) ⟨1485383, by rfl⟩ : syracuseStep 1980511 = 2970767) B2970767
theorem B2970773 : Blo 1979435 2970773 := bbase (se 6 (by rfl) ⟨69627, by rfl⟩ : syracuseStep 2970773 = 139255) (by norm_num)
theorem B1980515 : Blo 1979435 1980515 := bstep (se 1 (by rfl) ⟨1485386, by rfl⟩ : syracuseStep 1980515 = 2970773) B2970773
theorem B6344821 : Blo 1979435 6344821 := bbase (se 5 (by rfl) ⟨297413, by rfl⟩ : syracuseStep 6344821 = 594827) (by norm_num)
theorem B8459761 : Blo 1979435 8459761 := bstep (se 2 (by rfl) ⟨3172410, by rfl⟩ : syracuseStep 8459761 = 6344821) B6344821
theorem B11279681 : Blo 1979435 11279681 := bstep (se 2 (by rfl) ⟨4229880, by rfl⟩ : syracuseStep 11279681 = 8459761) B8459761
theorem B7519787 : Blo 1979435 7519787 := bstep (se 1 (by rfl) ⟨5639840, by rfl⟩ : syracuseStep 7519787 = 11279681) B11279681
theorem B5013191 : Blo 1979435 5013191 := bstep (se 1 (by rfl) ⟨3759893, by rfl⟩ : syracuseStep 5013191 = 7519787) B7519787
theorem B3342127 : Blo 1979435 3342127 := bstep (se 1 (by rfl) ⟨2506595, by rfl⟩ : syracuseStep 3342127 = 5013191) B5013191
theorem B4456169 : Blo 1979435 4456169 := bstep (se 2 (by rfl) ⟨1671063, by rfl⟩ : syracuseStep 4456169 = 3342127) B3342127
theorem B2970779 : Blo 1979435 2970779 := bstep (se 1 (by rfl) ⟨2228084, by rfl⟩ : syracuseStep 2970779 = 4456169) B4456169
theorem B1980519 : Blo 1979435 1980519 := bstep (se 1 (by rfl) ⟨1485389, by rfl⟩ : syracuseStep 1980519 = 2970779) B2970779
theorem B2228089 : Blo 1979435 2228089 := bbase (se 2 (by rfl) ⟨835533, by rfl⟩ : syracuseStep 2228089 = 1671067) (by norm_num)
theorem B2970785 : Blo 1979435 2970785 := bstep (se 2 (by rfl) ⟨1114044, by rfl⟩ : syracuseStep 2970785 = 2228089) B2228089
theorem B1980523 : Blo 1979435 1980523 := bstep (se 1 (by rfl) ⟨1485392, by rfl⟩ : syracuseStep 1980523 = 2970785) B2970785
theorem B2143805 : Blo 1979435 2143805 := bbase (se 3 (by rfl) ⟨401963, by rfl⟩ : syracuseStep 2143805 = 803927) (by norm_num)
theorem B5716813 : Blo 1979435 5716813 := bstep (se 3 (by rfl) ⟨1071902, by rfl⟩ : syracuseStep 5716813 = 2143805) B2143805
theorem B7622417 : Blo 1979435 7622417 := bstep (se 2 (by rfl) ⟨2858406, by rfl⟩ : syracuseStep 7622417 = 5716813) B5716813
theorem B5081611 : Blo 1979435 5081611 := bstep (se 1 (by rfl) ⟨3811208, by rfl⟩ : syracuseStep 5081611 = 7622417) B7622417
theorem B6775481 : Blo 1979435 6775481 := bstep (se 2 (by rfl) ⟨2540805, by rfl⟩ : syracuseStep 6775481 = 5081611) B5081611
theorem B4516987 : Blo 1979435 4516987 := bstep (se 1 (by rfl) ⟨3387740, by rfl⟩ : syracuseStep 4516987 = 6775481) B6775481
theorem B6022649 : Blo 1979435 6022649 := bstep (se 2 (by rfl) ⟨2258493, by rfl⟩ : syracuseStep 6022649 = 4516987) B4516987
theorem B4015099 : Blo 1979435 4015099 := bstep (se 1 (by rfl) ⟨3011324, by rfl⟩ : syracuseStep 4015099 = 6022649) B6022649
theorem B5353465 : Blo 1979435 5353465 := bstep (se 2 (by rfl) ⟨2007549, by rfl⟩ : syracuseStep 5353465 = 4015099) B4015099
theorem B7137953 : Blo 1979435 7137953 := bstep (se 2 (by rfl) ⟨2676732, by rfl⟩ : syracuseStep 7137953 = 5353465) B5353465
theorem B4758635 : Blo 1979435 4758635 := bstep (se 1 (by rfl) ⟨3568976, by rfl⟩ : syracuseStep 4758635 = 7137953) B7137953
theorem B12689693 : Blo 1979435 12689693 := bstep (se 3 (by rfl) ⟨2379317, by rfl⟩ : syracuseStep 12689693 = 4758635) B4758635
theorem B8459795 : Blo 1979435 8459795 := bstep (se 1 (by rfl) ⟨6344846, by rfl⟩ : syracuseStep 8459795 = 12689693) B12689693
theorem B5639863 : Blo 1979435 5639863 := bstep (se 1 (by rfl) ⟨4229897, by rfl⟩ : syracuseStep 5639863 = 8459795) B8459795
theorem B7519817 : Blo 1979435 7519817 := bstep (se 2 (by rfl) ⟨2819931, by rfl⟩ : syracuseStep 7519817 = 5639863) B5639863
theorem B5013211 : Blo 1979435 5013211 := bstep (se 1 (by rfl) ⟨3759908, by rfl⟩ : syracuseStep 5013211 = 7519817) B7519817
theorem B6684281 : Blo 1979435 6684281 := bstep (se 2 (by rfl) ⟨2506605, by rfl⟩ : syracuseStep 6684281 = 5013211) B5013211
theorem B4456187 : Blo 1979435 4456187 := bstep (se 1 (by rfl) ⟨3342140, by rfl⟩ : syracuseStep 4456187 = 6684281) B6684281
theorem B2970791 : Blo 1979435 2970791 := bstep (se 1 (by rfl) ⟨2228093, by rfl⟩ : syracuseStep 2970791 = 4456187) B4456187
theorem B1980527 : Blo 1979435 1980527 := bstep (se 1 (by rfl) ⟨1485395, by rfl⟩ : syracuseStep 1980527 = 2970791) B2970791
theorem B2970797 : Blo 1979435 2970797 := bbase (se 3 (by rfl) ⟨557024, by rfl⟩ : syracuseStep 2970797 = 1114049) (by norm_num)
theorem B1980531 : Blo 1979435 1980531 := bstep (se 1 (by rfl) ⟨1485398, by rfl⟩ : syracuseStep 1980531 = 2970797) B2970797
theorem B4456205 : Blo 1979435 4456205 := bbase (se 3 (by rfl) ⟨835538, by rfl⟩ : syracuseStep 4456205 = 1671077) (by norm_num)
theorem B2970803 : Blo 1979435 2970803 := bstep (se 1 (by rfl) ⟨2228102, by rfl⟩ : syracuseStep 2970803 = 4456205) B4456205
theorem B1980535 : Blo 1979435 1980535 := bstep (se 1 (by rfl) ⟨1485401, by rfl⟩ : syracuseStep 1980535 = 2970803) B2970803
theorem B2506621 : Blo 1979435 2506621 := bbase (se 3 (by rfl) ⟨469991, by rfl⟩ : syracuseStep 2506621 = 939983) (by norm_num)
theorem B3342161 : Blo 1979435 3342161 := bstep (se 2 (by rfl) ⟨1253310, by rfl⟩ : syracuseStep 3342161 = 2506621) B2506621
theorem B2228107 : Blo 1979435 2228107 := bstep (se 1 (by rfl) ⟨1671080, by rfl⟩ : syracuseStep 2228107 = 3342161) B3342161
theorem B2970809 : Blo 1979435 2970809 := bstep (se 2 (by rfl) ⟨1114053, by rfl⟩ : syracuseStep 2970809 = 2228107) B2228107
theorem B1980539 : Blo 1979435 1980539 := bstep (se 1 (by rfl) ⟨1485404, by rfl⟩ : syracuseStep 1980539 = 2970809) B2970809
theorem B3569005 : Blo 1979435 3569005 := bbase (se 3 (by rfl) ⟨669188, by rfl⟩ : syracuseStep 3569005 = 1338377) (by norm_num)
theorem B4758673 : Blo 1979435 4758673 := bstep (se 2 (by rfl) ⟨1784502, by rfl⟩ : syracuseStep 4758673 = 3569005) B3569005
theorem B6344897 : Blo 1979435 6344897 := bstep (se 2 (by rfl) ⟨2379336, by rfl⟩ : syracuseStep 6344897 = 4758673) B4758673
theorem B16919725 : Blo 1979435 16919725 := bstep (se 3 (by rfl) ⟨3172448, by rfl⟩ : syracuseStep 16919725 = 6344897) B6344897
theorem B22559633 : Blo 1979435 22559633 := bstep (se 2 (by rfl) ⟨8459862, by rfl⟩ : syracuseStep 22559633 = 16919725) B16919725
theorem B15039755 : Blo 1979435 15039755 := bstep (se 1 (by rfl) ⟨11279816, by rfl⟩ : syracuseStep 15039755 = 22559633) B22559633
theorem B10026503 : Blo 1979435 10026503 := bstep (se 1 (by rfl) ⟨7519877, by rfl⟩ : syracuseStep 10026503 = 15039755) B15039755
theorem B6684335 : Blo 1979435 6684335 := bstep (se 1 (by rfl) ⟨5013251, by rfl⟩ : syracuseStep 6684335 = 10026503) B10026503
theorem B4456223 : Blo 1979435 4456223 := bstep (se 1 (by rfl) ⟨3342167, by rfl⟩ : syracuseStep 4456223 = 6684335) B6684335
theorem B2970815 : Blo 1979435 2970815 := bstep (se 1 (by rfl) ⟨2228111, by rfl⟩ : syracuseStep 2970815 = 4456223) B4456223
theorem B1980543 : Blo 1979435 1980543 := bstep (se 1 (by rfl) ⟨1485407, by rfl⟩ : syracuseStep 1980543 = 2970815) B2970815
theorem B2970821 : Blo 1979435 2970821 := bbase (se 4 (by rfl) ⟨278514, by rfl⟩ : syracuseStep 2970821 = 557029) (by norm_num)
theorem B1980547 : Blo 1979435 1980547 := bstep (se 1 (by rfl) ⟨1485410, by rfl⟩ : syracuseStep 1980547 = 2970821) B2970821
theorem B3342181 : Blo 1979435 3342181 := bbase (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) (by norm_num)
theorem B4456241 : Blo 1979435 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B2970827 : Blo 1979435 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B1980551 : Blo 1979435 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B2228125 : Blo 1979435 2228125 := bbase (se 3 (by rfl) ⟨417773, by rfl⟩ : syracuseStep 2228125 = 835547) (by norm_num)
theorem B2970833 : Blo 1979435 2970833 := bstep (se 2 (by rfl) ⟨1114062, by rfl⟩ : syracuseStep 2970833 = 2228125) B2228125
theorem B1980555 : Blo 1979435 1980555 := bstep (se 1 (by rfl) ⟨1485416, by rfl⟩ : syracuseStep 1980555 = 2970833) B2970833
theorem B6684389 : Blo 1979435 6684389 := bbase (se 4 (by rfl) ⟨626661, by rfl⟩ : syracuseStep 6684389 = 1253323) (by norm_num)
theorem B4456259 : Blo 1979435 4456259 := bstep (se 1 (by rfl) ⟨3342194, by rfl⟩ : syracuseStep 4456259 = 6684389) B6684389
theorem B2970839 : Blo 1979435 2970839 := bstep (se 1 (by rfl) ⟨2228129, by rfl⟩ : syracuseStep 2970839 = 4456259) B4456259
theorem B1980559 : Blo 1979435 1980559 := bstep (se 1 (by rfl) ⟨1485419, by rfl⟩ : syracuseStep 1980559 = 2970839) B2970839
theorem B2970845 : Blo 1979435 2970845 := bbase (se 3 (by rfl) ⟨557033, by rfl⟩ : syracuseStep 2970845 = 1114067) (by norm_num)
theorem B1980563 : Blo 1979435 1980563 := bstep (se 1 (by rfl) ⟨1485422, by rfl⟩ : syracuseStep 1980563 = 2970845) B2970845
theorem B4456277 : Blo 1979435 4456277 := bbase (se 9 (by rfl) ⟨13055, by rfl⟩ : syracuseStep 4456277 = 26111) (by norm_num)
theorem B2970851 : Blo 1979435 2970851 := bstep (se 1 (by rfl) ⟨2228138, by rfl⟩ : syracuseStep 2970851 = 4456277) B4456277
theorem B1980567 : Blo 1979435 1980567 := bstep (se 1 (by rfl) ⟨1485425, by rfl⟩ : syracuseStep 1980567 = 2970851) B2970851
theorem B5639989 : Blo 1979435 5639989 := bbase (se 5 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 5639989 = 528749) (by norm_num)
theorem B7519985 : Blo 1979435 7519985 := bstep (se 2 (by rfl) ⟨2819994, by rfl⟩ : syracuseStep 7519985 = 5639989) B5639989
theorem B5013323 : Blo 1979435 5013323 := bstep (se 1 (by rfl) ⟨3759992, by rfl⟩ : syracuseStep 5013323 = 7519985) B7519985
theorem B3342215 : Blo 1979435 3342215 := bstep (se 1 (by rfl) ⟨2506661, by rfl⟩ : syracuseStep 3342215 = 5013323) B5013323
theorem B2228143 : Blo 1979435 2228143 := bstep (se 1 (by rfl) ⟨1671107, by rfl⟩ : syracuseStep 2228143 = 3342215) B3342215
theorem B2970857 : Blo 1979435 2970857 := bstep (se 2 (by rfl) ⟨1114071, by rfl⟩ : syracuseStep 2970857 = 2228143) B2228143
theorem B1980571 : Blo 1979435 1980571 := bstep (se 1 (by rfl) ⟨1485428, by rfl⟩ : syracuseStep 1980571 = 2970857) B2970857
theorem B6104965 : Blo 1979435 6104965 := bbase (se 4 (by rfl) ⟨572340, by rfl⟩ : syracuseStep 6104965 = 1144681) (by norm_num)
theorem B8139953 : Blo 1979435 8139953 := bstep (se 2 (by rfl) ⟨3052482, by rfl⟩ : syracuseStep 8139953 = 6104965) B6104965
theorem B5426635 : Blo 1979435 5426635 := bstep (se 1 (by rfl) ⟨4069976, by rfl⟩ : syracuseStep 5426635 = 8139953) B8139953
theorem B7235513 : Blo 1979435 7235513 := bstep (se 2 (by rfl) ⟨2713317, by rfl⟩ : syracuseStep 7235513 = 5426635) B5426635
theorem B4823675 : Blo 1979435 4823675 := bstep (se 1 (by rfl) ⟨3617756, by rfl⟩ : syracuseStep 4823675 = 7235513) B7235513
theorem B51452533 : Blo 1979435 51452533 := bstep (se 5 (by rfl) ⟨2411837, by rfl⟩ : syracuseStep 51452533 = 4823675) B4823675
theorem B68603377 : Blo 1979435 68603377 := bstep (se 2 (by rfl) ⟨25726266, by rfl⟩ : syracuseStep 68603377 = 51452533) B51452533
theorem B91471169 : Blo 1979435 91471169 := bstep (se 2 (by rfl) ⟨34301688, by rfl⟩ : syracuseStep 91471169 = 68603377) B68603377
theorem B60980779 : Blo 1979435 60980779 := bstep (se 1 (by rfl) ⟨45735584, by rfl⟩ : syracuseStep 60980779 = 91471169) B91471169
theorem B325230821 : Blo 1979435 325230821 := bstep (se 4 (by rfl) ⟨30490389, by rfl⟩ : syracuseStep 325230821 = 60980779) B60980779
theorem B216820547 : Blo 1979435 216820547 := bstep (se 1 (by rfl) ⟨162615410, by rfl⟩ : syracuseStep 216820547 = 325230821) B325230821
theorem B144547031 : Blo 1979435 144547031 := bstep (se 1 (by rfl) ⟨108410273, by rfl⟩ : syracuseStep 144547031 = 216820547) B216820547
theorem B96364687 : Blo 1979435 96364687 := bstep (se 1 (by rfl) ⟨72273515, by rfl⟩ : syracuseStep 96364687 = 144547031) B144547031
theorem B128486249 : Blo 1979435 128486249 := bstep (se 2 (by rfl) ⟨48182343, by rfl⟩ : syracuseStep 128486249 = 96364687) B96364687
theorem B85657499 : Blo 1979435 85657499 := bstep (se 1 (by rfl) ⟨64243124, by rfl⟩ : syracuseStep 85657499 = 128486249) B128486249
theorem B57104999 : Blo 1979435 57104999 := bstep (se 1 (by rfl) ⟨42828749, by rfl⟩ : syracuseStep 57104999 = 85657499) B85657499
theorem B38069999 : Blo 1979435 38069999 := bstep (se 1 (by rfl) ⟨28552499, by rfl⟩ : syracuseStep 38069999 = 57104999) B57104999
theorem B25379999 : Blo 1979435 25379999 := bstep (se 1 (by rfl) ⟨19034999, by rfl⟩ : syracuseStep 25379999 = 38069999) B38069999
theorem B16919999 : Blo 1979435 16919999 := bstep (se 1 (by rfl) ⟨12689999, by rfl⟩ : syracuseStep 16919999 = 25379999) B25379999
theorem B11279999 : Blo 1979435 11279999 := bstep (se 1 (by rfl) ⟨8459999, by rfl⟩ : syracuseStep 11279999 = 16919999) B16919999
theorem B7519999 : Blo 1979435 7519999 := bstep (se 1 (by rfl) ⟨5639999, by rfl⟩ : syracuseStep 7519999 = 11279999) B11279999
theorem B10026665 : Blo 1979435 10026665 := bstep (se 2 (by rfl) ⟨3759999, by rfl⟩ : syracuseStep 10026665 = 7519999) B7519999
theorem B6684443 : Blo 1979435 6684443 := bstep (se 1 (by rfl) ⟨5013332, by rfl⟩ : syracuseStep 6684443 = 10026665) B10026665
theorem B4456295 : Blo 1979435 4456295 := bstep (se 1 (by rfl) ⟨3342221, by rfl⟩ : syracuseStep 4456295 = 6684443) B6684443
theorem B2970863 : Blo 1979435 2970863 := bstep (se 1 (by rfl) ⟨2228147, by rfl⟩ : syracuseStep 2970863 = 4456295) B4456295
theorem B1980575 : Blo 1979435 1980575 := bstep (se 1 (by rfl) ⟨1485431, by rfl⟩ : syracuseStep 1980575 = 2970863) B2970863
theorem B2970869 : Blo 1979435 2970869 := bbase (se 5 (by rfl) ⟨139259, by rfl⟩ : syracuseStep 2970869 = 278519) (by norm_num)
theorem B1980579 : Blo 1979435 1980579 := bstep (se 1 (by rfl) ⟨1485434, by rfl⟩ : syracuseStep 1980579 = 2970869) B2970869
theorem B2379385 : Blo 1979435 2379385 := bbase (se 2 (by rfl) ⟨892269, by rfl⟩ : syracuseStep 2379385 = 1784539) (by norm_num)
theorem B12690053 : Blo 1979435 12690053 := bstep (se 4 (by rfl) ⟨1189692, by rfl⟩ : syracuseStep 12690053 = 2379385) B2379385
theorem B8460035 : Blo 1979435 8460035 := bstep (se 1 (by rfl) ⟨6345026, by rfl⟩ : syracuseStep 8460035 = 12690053) B12690053
theorem B5640023 : Blo 1979435 5640023 := bstep (se 1 (by rfl) ⟨4230017, by rfl⟩ : syracuseStep 5640023 = 8460035) B8460035
theorem B3760015 : Blo 1979435 3760015 := bstep (se 1 (by rfl) ⟨2820011, by rfl⟩ : syracuseStep 3760015 = 5640023) B5640023
theorem B5013353 : Blo 1979435 5013353 := bstep (se 2 (by rfl) ⟨1880007, by rfl⟩ : syracuseStep 5013353 = 3760015) B3760015
theorem B3342235 : Blo 1979435 3342235 := bstep (se 1 (by rfl) ⟨2506676, by rfl⟩ : syracuseStep 3342235 = 5013353) B5013353
theorem B4456313 : Blo 1979435 4456313 := bstep (se 2 (by rfl) ⟨1671117, by rfl⟩ : syracuseStep 4456313 = 3342235) B3342235
theorem B2970875 : Blo 1979435 2970875 := bstep (se 1 (by rfl) ⟨2228156, by rfl⟩ : syracuseStep 2970875 = 4456313) B4456313
theorem B1980583 : Blo 1979435 1980583 := bstep (se 1 (by rfl) ⟨1485437, by rfl⟩ : syracuseStep 1980583 = 2970875) B2970875
theorem B2228161 : Blo 1979435 2228161 := bbase (se 2 (by rfl) ⟨835560, by rfl⟩ : syracuseStep 2228161 = 1671121) (by norm_num)
theorem B2970881 : Blo 1979435 2970881 := bstep (se 2 (by rfl) ⟨1114080, by rfl⟩ : syracuseStep 2970881 = 2228161) B2228161
theorem B1980587 : Blo 1979435 1980587 := bstep (se 1 (by rfl) ⟨1485440, by rfl⟩ : syracuseStep 1980587 = 2970881) B2970881
theorem B5013373 : Blo 1979435 5013373 := bbase (se 3 (by rfl) ⟨940007, by rfl⟩ : syracuseStep 5013373 = 1880015) (by norm_num)
theorem B6684497 : Blo 1979435 6684497 := bstep (se 2 (by rfl) ⟨2506686, by rfl⟩ : syracuseStep 6684497 = 5013373) B5013373
theorem B4456331 : Blo 1979435 4456331 := bstep (se 1 (by rfl) ⟨3342248, by rfl⟩ : syracuseStep 4456331 = 6684497) B6684497
theorem B2970887 : Blo 1979435 2970887 := bstep (se 1 (by rfl) ⟨2228165, by rfl⟩ : syracuseStep 2970887 = 4456331) B4456331
theorem B1980591 : Blo 1979435 1980591 := bstep (se 1 (by rfl) ⟨1485443, by rfl⟩ : syracuseStep 1980591 = 2970887) B2970887
theorem B2970893 : Blo 1979435 2970893 := bbase (se 3 (by rfl) ⟨557042, by rfl⟩ : syracuseStep 2970893 = 1114085) (by norm_num)
theorem B1980595 : Blo 1979435 1980595 := bstep (se 1 (by rfl) ⟨1485446, by rfl⟩ : syracuseStep 1980595 = 2970893) B2970893
theorem B4456349 : Blo 1979435 4456349 := bbase (se 3 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 4456349 = 1671131) (by norm_num)
theorem B2970899 : Blo 1979435 2970899 := bstep (se 1 (by rfl) ⟨2228174, by rfl⟩ : syracuseStep 2970899 = 4456349) B4456349
theorem B1980599 : Blo 1979435 1980599 := bstep (se 1 (by rfl) ⟨1485449, by rfl⟩ : syracuseStep 1980599 = 2970899) B2970899
theorem B3342269 : Blo 1979435 3342269 := bbase (se 3 (by rfl) ⟨626675, by rfl⟩ : syracuseStep 3342269 = 1253351) (by norm_num)
theorem B2228179 : Blo 1979435 2228179 := bstep (se 1 (by rfl) ⟨1671134, by rfl⟩ : syracuseStep 2228179 = 3342269) B3342269
theorem B2970905 : Blo 1979435 2970905 := bstep (se 2 (by rfl) ⟨1114089, by rfl⟩ : syracuseStep 2970905 = 2228179) B2228179
theorem B1980603 : Blo 1979435 1980603 := bstep (se 1 (by rfl) ⟨1485452, by rfl⟩ : syracuseStep 1980603 = 2970905) B2970905
theorem B11280181 : Blo 1979435 11280181 := bbase (se 5 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 11280181 = 1057517) (by norm_num)
theorem B15040241 : Blo 1979435 15040241 := bstep (se 2 (by rfl) ⟨5640090, by rfl⟩ : syracuseStep 15040241 = 11280181) B11280181
theorem B10026827 : Blo 1979435 10026827 := bstep (se 1 (by rfl) ⟨7520120, by rfl⟩ : syracuseStep 10026827 = 15040241) B15040241
theorem B6684551 : Blo 1979435 6684551 := bstep (se 1 (by rfl) ⟨5013413, by rfl⟩ : syracuseStep 6684551 = 10026827) B10026827
theorem B4456367 : Blo 1979435 4456367 := bstep (se 1 (by rfl) ⟨3342275, by rfl⟩ : syracuseStep 4456367 = 6684551) B6684551
theorem B2970911 : Blo 1979435 2970911 := bstep (se 1 (by rfl) ⟨2228183, by rfl⟩ : syracuseStep 2970911 = 4456367) B4456367
theorem B1980607 : Blo 1979435 1980607 := bstep (se 1 (by rfl) ⟨1485455, by rfl⟩ : syracuseStep 1980607 = 2970911) B2970911
theorem B2970917 : Blo 1979435 2970917 := bbase (se 4 (by rfl) ⟨278523, by rfl⟩ : syracuseStep 2970917 = 557047) (by norm_num)
theorem B1980611 : Blo 1979435 1980611 := bstep (se 1 (by rfl) ⟨1485458, by rfl⟩ : syracuseStep 1980611 = 2970917) B2970917
theorem B2506717 : Blo 1979435 2506717 := bbase (se 3 (by rfl) ⟨470009, by rfl⟩ : syracuseStep 2506717 = 940019) (by norm_num)
theorem B3342289 : Blo 1979435 3342289 := bstep (se 2 (by rfl) ⟨1253358, by rfl⟩ : syracuseStep 3342289 = 2506717) B2506717
theorem B4456385 : Blo 1979435 4456385 := bstep (se 2 (by rfl) ⟨1671144, by rfl⟩ : syracuseStep 4456385 = 3342289) B3342289
theorem B2970923 : Blo 1979435 2970923 := bstep (se 1 (by rfl) ⟨2228192, by rfl⟩ : syracuseStep 2970923 = 4456385) B4456385
theorem B1980615 : Blo 1979435 1980615 := bstep (se 1 (by rfl) ⟨1485461, by rfl⟩ : syracuseStep 1980615 = 2970923) B2970923
theorem B2228197 : Blo 1979435 2228197 := bbase (se 4 (by rfl) ⟨208893, by rfl⟩ : syracuseStep 2228197 = 417787) (by norm_num)
theorem B2970929 : Blo 1979435 2970929 := bstep (se 2 (by rfl) ⟨1114098, by rfl⟩ : syracuseStep 2970929 = 2228197) B2228197
theorem B1980619 : Blo 1979435 1980619 := bstep (se 1 (by rfl) ⟨1485464, by rfl⟩ : syracuseStep 1980619 = 2970929) B2970929
theorem B9517733 : Blo 1979435 9517733 := bbase (se 4 (by rfl) ⟨892287, by rfl⟩ : syracuseStep 9517733 = 1784575) (by norm_num)
theorem B6345155 : Blo 1979435 6345155 := bstep (se 1 (by rfl) ⟨4758866, by rfl⟩ : syracuseStep 6345155 = 9517733) B9517733
theorem B4230103 : Blo 1979435 4230103 := bstep (se 1 (by rfl) ⟨3172577, by rfl⟩ : syracuseStep 4230103 = 6345155) B6345155
theorem B5640137 : Blo 1979435 5640137 := bstep (se 2 (by rfl) ⟨2115051, by rfl⟩ : syracuseStep 5640137 = 4230103) B4230103
theorem B3760091 : Blo 1979435 3760091 := bstep (se 1 (by rfl) ⟨2820068, by rfl⟩ : syracuseStep 3760091 = 5640137) B5640137
theorem B2506727 : Blo 1979435 2506727 := bstep (se 1 (by rfl) ⟨1880045, by rfl⟩ : syracuseStep 2506727 = 3760091) B3760091
theorem B6684605 : Blo 1979435 6684605 := bstep (se 3 (by rfl) ⟨1253363, by rfl⟩ : syracuseStep 6684605 = 2506727) B2506727
theorem B4456403 : Blo 1979435 4456403 := bstep (se 1 (by rfl) ⟨3342302, by rfl⟩ : syracuseStep 4456403 = 6684605) B6684605
theorem B2970935 : Blo 1979435 2970935 := bstep (se 1 (by rfl) ⟨2228201, by rfl⟩ : syracuseStep 2970935 = 4456403) B4456403
theorem B1980623 : Blo 1979435 1980623 := bstep (se 1 (by rfl) ⟨1485467, by rfl⟩ : syracuseStep 1980623 = 2970935) B2970935
theorem B2970941 : Blo 1979435 2970941 := bbase (se 3 (by rfl) ⟨557051, by rfl⟩ : syracuseStep 2970941 = 1114103) (by norm_num)
theorem B1980627 : Blo 1979435 1980627 := bstep (se 1 (by rfl) ⟨1485470, by rfl⟩ : syracuseStep 1980627 = 2970941) B2970941
theorem B4456421 : Blo 1979435 4456421 := bbase (se 4 (by rfl) ⟨417789, by rfl⟩ : syracuseStep 4456421 = 835579) (by norm_num)
theorem B2970947 : Blo 1979435 2970947 := bstep (se 1 (by rfl) ⟨2228210, by rfl⟩ : syracuseStep 2970947 = 4456421) B4456421
theorem B1980631 : Blo 1979435 1980631 := bstep (se 1 (by rfl) ⟨1485473, by rfl⟩ : syracuseStep 1980631 = 2970947) B2970947
theorem B5013485 : Blo 1979435 5013485 := bbase (se 3 (by rfl) ⟨940028, by rfl⟩ : syracuseStep 5013485 = 1880057) (by norm_num)
theorem B3342323 : Blo 1979435 3342323 := bstep (se 1 (by rfl) ⟨2506742, by rfl⟩ : syracuseStep 3342323 = 5013485) B5013485
theorem B2228215 : Blo 1979435 2228215 := bstep (se 1 (by rfl) ⟨1671161, by rfl⟩ : syracuseStep 2228215 = 3342323) B3342323
theorem B2970953 : Blo 1979435 2970953 := bstep (se 2 (by rfl) ⟨1114107, by rfl⟩ : syracuseStep 2970953 = 2228215) B2228215
theorem B1980635 : Blo 1979435 1980635 := bstep (se 1 (by rfl) ⟨1485476, by rfl⟩ : syracuseStep 1980635 = 2970953) B2970953
theorem B4287853 : Blo 1979435 4287853 := bbase (se 3 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 4287853 = 1607945) (by norm_num)
theorem B5717137 : Blo 1979435 5717137 := bstep (se 2 (by rfl) ⟨2143926, by rfl⟩ : syracuseStep 5717137 = 4287853) B4287853
theorem B7622849 : Blo 1979435 7622849 := bstep (se 2 (by rfl) ⟨2858568, by rfl⟩ : syracuseStep 7622849 = 5717137) B5717137
theorem B20327597 : Blo 1979435 20327597 := bstep (se 3 (by rfl) ⟨3811424, by rfl⟩ : syracuseStep 20327597 = 7622849) B7622849
theorem B13551731 : Blo 1979435 13551731 := bstep (se 1 (by rfl) ⟨10163798, by rfl⟩ : syracuseStep 13551731 = 20327597) B20327597
theorem B9034487 : Blo 1979435 9034487 := bstep (se 1 (by rfl) ⟨6775865, by rfl⟩ : syracuseStep 9034487 = 13551731) B13551731
theorem B6022991 : Blo 1979435 6022991 := bstep (se 1 (by rfl) ⟨4517243, by rfl⟩ : syracuseStep 6022991 = 9034487) B9034487
theorem B4015327 : Blo 1979435 4015327 := bstep (se 1 (by rfl) ⟨3011495, by rfl⟩ : syracuseStep 4015327 = 6022991) B6022991
theorem B5353769 : Blo 1979435 5353769 := bstep (se 2 (by rfl) ⟨2007663, by rfl⟩ : syracuseStep 5353769 = 4015327) B4015327
theorem B3569179 : Blo 1979435 3569179 := bstep (se 1 (by rfl) ⟨2676884, by rfl⟩ : syracuseStep 3569179 = 5353769) B5353769
theorem B4758905 : Blo 1979435 4758905 := bstep (se 2 (by rfl) ⟨1784589, by rfl⟩ : syracuseStep 4758905 = 3569179) B3569179
theorem B3172603 : Blo 1979435 3172603 := bstep (se 1 (by rfl) ⟨2379452, by rfl⟩ : syracuseStep 3172603 = 4758905) B4758905
theorem B4230137 : Blo 1979435 4230137 := bstep (se 2 (by rfl) ⟨1586301, by rfl⟩ : syracuseStep 4230137 = 3172603) B3172603
theorem B2820091 : Blo 1979435 2820091 := bstep (se 1 (by rfl) ⟨2115068, by rfl⟩ : syracuseStep 2820091 = 4230137) B4230137
theorem B3760121 : Blo 1979435 3760121 := bstep (se 2 (by rfl) ⟨1410045, by rfl⟩ : syracuseStep 3760121 = 2820091) B2820091
theorem B10026989 : Blo 1979435 10026989 := bstep (se 3 (by rfl) ⟨1880060, by rfl⟩ : syracuseStep 10026989 = 3760121) B3760121
theorem B6684659 : Blo 1979435 6684659 := bstep (se 1 (by rfl) ⟨5013494, by rfl⟩ : syracuseStep 6684659 = 10026989) B10026989
theorem B4456439 : Blo 1979435 4456439 := bstep (se 1 (by rfl) ⟨3342329, by rfl⟩ : syracuseStep 4456439 = 6684659) B6684659
theorem B2970959 : Blo 1979435 2970959 := bstep (se 1 (by rfl) ⟨2228219, by rfl⟩ : syracuseStep 2970959 = 4456439) B4456439
theorem B1980639 : Blo 1979435 1980639 := bstep (se 1 (by rfl) ⟨1485479, by rfl⟩ : syracuseStep 1980639 = 2970959) B2970959
theorem B2970965 : Blo 1979435 2970965 := bbase (se 19 (by rfl) ⟨8, by rfl⟩ : syracuseStep 2970965 = 17) (by norm_num)
theorem B1980643 : Blo 1979435 1980643 := bstep (se 1 (by rfl) ⟨1485482, by rfl⟩ : syracuseStep 1980643 = 2970965) B2970965
theorem B2115077 : Blo 1979435 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B5640205 : Blo 1979435 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B7520273 : Blo 1979435 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B5013515 : Blo 1979435 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B3342343 : Blo 1979435 3342343 := bstep (se 1 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 3342343 = 5013515) B5013515
theorem B4456457 : Blo 1979435 4456457 := bstep (se 2 (by rfl) ⟨1671171, by rfl⟩ : syracuseStep 4456457 = 3342343) B3342343
theorem B2970971 : Blo 1979435 2970971 := bstep (se 1 (by rfl) ⟨2228228, by rfl⟩ : syracuseStep 2970971 = 4456457) B4456457
theorem B1980647 : Blo 1979435 1980647 := bstep (se 1 (by rfl) ⟨1485485, by rfl⟩ : syracuseStep 1980647 = 2970971) B2970971
theorem B2228233 : Blo 1979435 2228233 := bbase (se 2 (by rfl) ⟨835587, by rfl⟩ : syracuseStep 2228233 = 1671175) (by norm_num)
theorem B2970977 : Blo 1979435 2970977 := bstep (se 2 (by rfl) ⟨1114116, by rfl⟩ : syracuseStep 2970977 = 2228233) B2228233
theorem B1980651 : Blo 1979435 1980651 := bstep (se 1 (by rfl) ⟨1485488, by rfl⟩ : syracuseStep 1980651 = 2970977) B2970977
theorem B15245813 : Blo 1979435 15245813 := bbase (se 5 (by rfl) ⟨714647, by rfl⟩ : syracuseStep 15245813 = 1429295) (by norm_num)
theorem B10163875 : Blo 1979435 10163875 := bstep (se 1 (by rfl) ⟨7622906, by rfl⟩ : syracuseStep 10163875 = 15245813) B15245813
theorem B13551833 : Blo 1979435 13551833 := bstep (se 2 (by rfl) ⟨5081937, by rfl⟩ : syracuseStep 13551833 = 10163875) B10163875
theorem B36138221 : Blo 1979435 36138221 := bstep (se 3 (by rfl) ⟨6775916, by rfl⟩ : syracuseStep 36138221 = 13551833) B13551833
theorem B24092147 : Blo 1979435 24092147 := bstep (se 1 (by rfl) ⟨18069110, by rfl⟩ : syracuseStep 24092147 = 36138221) B36138221
theorem B16061431 : Blo 1979435 16061431 := bstep (se 1 (by rfl) ⟨12046073, by rfl⟩ : syracuseStep 16061431 = 24092147) B24092147
theorem B21415241 : Blo 1979435 21415241 := bstep (se 2 (by rfl) ⟨8030715, by rfl⟩ : syracuseStep 21415241 = 16061431) B16061431
theorem B14276827 : Blo 1979435 14276827 := bstep (se 1 (by rfl) ⟨10707620, by rfl⟩ : syracuseStep 14276827 = 21415241) B21415241
theorem B19035769 : Blo 1979435 19035769 := bstep (se 2 (by rfl) ⟨7138413, by rfl⟩ : syracuseStep 19035769 = 14276827) B14276827
theorem B25381025 : Blo 1979435 25381025 := bstep (se 2 (by rfl) ⟨9517884, by rfl⟩ : syracuseStep 25381025 = 19035769) B19035769
theorem B16920683 : Blo 1979435 16920683 := bstep (se 1 (by rfl) ⟨12690512, by rfl⟩ : syracuseStep 16920683 = 25381025) B25381025
theorem B11280455 : Blo 1979435 11280455 := bstep (se 1 (by rfl) ⟨8460341, by rfl⟩ : syracuseStep 11280455 = 16920683) B16920683
theorem B7520303 : Blo 1979435 7520303 := bstep (se 1 (by rfl) ⟨5640227, by rfl⟩ : syracuseStep 7520303 = 11280455) B11280455
theorem B5013535 : Blo 1979435 5013535 := bstep (se 1 (by rfl) ⟨3760151, by rfl⟩ : syracuseStep 5013535 = 7520303) B7520303
theorem B6684713 : Blo 1979435 6684713 := bstep (se 2 (by rfl) ⟨2506767, by rfl⟩ : syracuseStep 6684713 = 5013535) B5013535
theorem B4456475 : Blo 1979435 4456475 := bstep (se 1 (by rfl) ⟨3342356, by rfl⟩ : syracuseStep 4456475 = 6684713) B6684713
theorem B2970983 : Blo 1979435 2970983 := bstep (se 1 (by rfl) ⟨2228237, by rfl⟩ : syracuseStep 2970983 = 4456475) B4456475
theorem B1980655 : Blo 1979435 1980655 := bstep (se 1 (by rfl) ⟨1485491, by rfl⟩ : syracuseStep 1980655 = 2970983) B2970983
theorem B2970989 : Blo 1979435 2970989 := bbase (se 3 (by rfl) ⟨557060, by rfl⟩ : syracuseStep 2970989 = 1114121) (by norm_num)
theorem B1980659 : Blo 1979435 1980659 := bstep (se 1 (by rfl) ⟨1485494, by rfl⟩ : syracuseStep 1980659 = 2970989) B2970989
theorem B4456493 : Blo 1979435 4456493 := bbase (se 3 (by rfl) ⟨835592, by rfl⟩ : syracuseStep 4456493 = 1671185) (by norm_num)
theorem B2970995 : Blo 1979435 2970995 := bstep (se 1 (by rfl) ⟨2228246, by rfl⟩ : syracuseStep 2970995 = 4456493) B4456493
theorem B1980663 : Blo 1979435 1980663 := bstep (se 1 (by rfl) ⟨1485497, by rfl⟩ : syracuseStep 1980663 = 2970995) B2970995
theorem B6105253 : Blo 1979435 6105253 := bbase (se 4 (by rfl) ⟨572367, by rfl⟩ : syracuseStep 6105253 = 1144735) (by norm_num)
theorem B8140337 : Blo 1979435 8140337 := bstep (se 2 (by rfl) ⟨3052626, by rfl⟩ : syracuseStep 8140337 = 6105253) B6105253
theorem B5426891 : Blo 1979435 5426891 := bstep (se 1 (by rfl) ⟨4070168, by rfl⟩ : syracuseStep 5426891 = 8140337) B8140337
theorem B3617927 : Blo 1979435 3617927 := bstep (se 1 (by rfl) ⟨2713445, by rfl⟩ : syracuseStep 3617927 = 5426891) B5426891
theorem B2411951 : Blo 1979435 2411951 := bstep (se 1 (by rfl) ⟨1808963, by rfl⟩ : syracuseStep 2411951 = 3617927) B3617927
theorem B6431869 : Blo 1979435 6431869 := bstep (se 3 (by rfl) ⟨1205975, by rfl⟩ : syracuseStep 6431869 = 2411951) B2411951
theorem B34303301 : Blo 1979435 34303301 := bstep (se 4 (by rfl) ⟨3215934, by rfl⟩ : syracuseStep 34303301 = 6431869) B6431869
theorem B22868867 : Blo 1979435 22868867 := bstep (se 1 (by rfl) ⟨17151650, by rfl⟩ : syracuseStep 22868867 = 34303301) B34303301
theorem B15245911 : Blo 1979435 15245911 := bstep (se 1 (by rfl) ⟨11434433, by rfl⟩ : syracuseStep 15245911 = 22868867) B22868867
theorem B20327881 : Blo 1979435 20327881 := bstep (se 2 (by rfl) ⟨7622955, by rfl⟩ : syracuseStep 20327881 = 15245911) B15245911
theorem B27103841 : Blo 1979435 27103841 := bstep (se 2 (by rfl) ⟨10163940, by rfl⟩ : syracuseStep 27103841 = 20327881) B20327881
theorem B18069227 : Blo 1979435 18069227 := bstep (se 1 (by rfl) ⟨13551920, by rfl⟩ : syracuseStep 18069227 = 27103841) B27103841
theorem B12046151 : Blo 1979435 12046151 := bstep (se 1 (by rfl) ⟨9034613, by rfl⟩ : syracuseStep 12046151 = 18069227) B18069227
theorem B8030767 : Blo 1979435 8030767 := bstep (se 1 (by rfl) ⟨6023075, by rfl⟩ : syracuseStep 8030767 = 12046151) B12046151
theorem B10707689 : Blo 1979435 10707689 := bstep (se 2 (by rfl) ⟨4015383, by rfl⟩ : syracuseStep 10707689 = 8030767) B8030767
theorem B7138459 : Blo 1979435 7138459 := bstep (se 1 (by rfl) ⟨5353844, by rfl⟩ : syracuseStep 7138459 = 10707689) B10707689
theorem B9517945 : Blo 1979435 9517945 := bstep (se 2 (by rfl) ⟨3569229, by rfl⟩ : syracuseStep 9517945 = 7138459) B7138459
theorem B12690593 : Blo 1979435 12690593 := bstep (se 2 (by rfl) ⟨4758972, by rfl⟩ : syracuseStep 12690593 = 9517945) B9517945
theorem B8460395 : Blo 1979435 8460395 := bstep (se 1 (by rfl) ⟨6345296, by rfl⟩ : syracuseStep 8460395 = 12690593) B12690593
theorem B5640263 : Blo 1979435 5640263 := bstep (se 1 (by rfl) ⟨4230197, by rfl⟩ : syracuseStep 5640263 = 8460395) B8460395
theorem B3760175 : Blo 1979435 3760175 := bstep (se 1 (by rfl) ⟨2820131, by rfl⟩ : syracuseStep 3760175 = 5640263) B5640263
theorem B2506783 : Blo 1979435 2506783 := bstep (se 1 (by rfl) ⟨1880087, by rfl⟩ : syracuseStep 2506783 = 3760175) B3760175
theorem B3342377 : Blo 1979435 3342377 := bstep (se 2 (by rfl) ⟨1253391, by rfl⟩ : syracuseStep 3342377 = 2506783) B2506783
theorem B2228251 : Blo 1979435 2228251 := bstep (se 1 (by rfl) ⟨1671188, by rfl⟩ : syracuseStep 2228251 = 3342377) B3342377
theorem B2971001 : Blo 1979435 2971001 := bstep (se 2 (by rfl) ⟨1114125, by rfl⟩ : syracuseStep 2971001 = 2228251) B2228251
theorem B1980667 : Blo 1979435 1980667 := bstep (se 1 (by rfl) ⟨1485500, by rfl⟩ : syracuseStep 1980667 = 2971001) B2971001
theorem B5221597 : Blo 1979435 5221597 := bbase (se 3 (by rfl) ⟨979049, by rfl⟩ : syracuseStep 5221597 = 1958099) (by norm_num)
theorem B6962129 : Blo 1979435 6962129 := bstep (se 2 (by rfl) ⟨2610798, by rfl⟩ : syracuseStep 6962129 = 5221597) B5221597
theorem B4641419 : Blo 1979435 4641419 := bstep (se 1 (by rfl) ⟨3481064, by rfl⟩ : syracuseStep 4641419 = 6962129) B6962129
theorem B12377117 : Blo 1979435 12377117 := bstep (se 3 (by rfl) ⟨2320709, by rfl⟩ : syracuseStep 12377117 = 4641419) B4641419
theorem B8251411 : Blo 1979435 8251411 := bstep (se 1 (by rfl) ⟨6188558, by rfl⟩ : syracuseStep 8251411 = 12377117) B12377117
theorem B11001881 : Blo 1979435 11001881 := bstep (se 2 (by rfl) ⟨4125705, by rfl⟩ : syracuseStep 11001881 = 8251411) B8251411
theorem B7334587 : Blo 1979435 7334587 := bstep (se 1 (by rfl) ⟨5500940, by rfl⟩ : syracuseStep 7334587 = 11001881) B11001881
theorem B9779449 : Blo 1979435 9779449 := bstep (se 2 (by rfl) ⟨3667293, by rfl⟩ : syracuseStep 9779449 = 7334587) B7334587
theorem B13039265 : Blo 1979435 13039265 := bstep (se 2 (by rfl) ⟨4889724, by rfl⟩ : syracuseStep 13039265 = 9779449) B9779449
theorem B8692843 : Blo 1979435 8692843 := bstep (se 1 (by rfl) ⟨6519632, by rfl⟩ : syracuseStep 8692843 = 13039265) B13039265
theorem B11590457 : Blo 1979435 11590457 := bstep (se 2 (by rfl) ⟨4346421, by rfl⟩ : syracuseStep 11590457 = 8692843) B8692843
theorem B30907885 : Blo 1979435 30907885 := bstep (se 3 (by rfl) ⟨5795228, by rfl⟩ : syracuseStep 30907885 = 11590457) B11590457
theorem B41210513 : Blo 1979435 41210513 := bstep (se 2 (by rfl) ⟨15453942, by rfl⟩ : syracuseStep 41210513 = 30907885) B30907885
theorem B27473675 : Blo 1979435 27473675 := bstep (se 1 (by rfl) ⟨20605256, by rfl⟩ : syracuseStep 27473675 = 41210513) B41210513
theorem B73263133 : Blo 1979435 73263133 := bstep (se 3 (by rfl) ⟨13736837, by rfl⟩ : syracuseStep 73263133 = 27473675) B27473675
theorem B97684177 : Blo 1979435 97684177 := bstep (se 2 (by rfl) ⟨36631566, by rfl⟩ : syracuseStep 97684177 = 73263133) B73263133
theorem B130245569 : Blo 1979435 130245569 := bstep (se 2 (by rfl) ⟨48842088, by rfl⟩ : syracuseStep 130245569 = 97684177) B97684177
theorem B86830379 : Blo 1979435 86830379 := bstep (se 1 (by rfl) ⟨65122784, by rfl⟩ : syracuseStep 86830379 = 130245569) B130245569
theorem B57886919 : Blo 1979435 57886919 := bstep (se 1 (by rfl) ⟨43415189, by rfl⟩ : syracuseStep 57886919 = 86830379) B86830379
theorem B38591279 : Blo 1979435 38591279 := bstep (se 1 (by rfl) ⟨28943459, by rfl⟩ : syracuseStep 38591279 = 57886919) B57886919
theorem B25727519 : Blo 1979435 25727519 := bstep (se 1 (by rfl) ⟨19295639, by rfl⟩ : syracuseStep 25727519 = 38591279) B38591279
theorem B17151679 : Blo 1979435 17151679 := bstep (se 1 (by rfl) ⟨12863759, by rfl⟩ : syracuseStep 17151679 = 25727519) B25727519
theorem B22868905 : Blo 1979435 22868905 := bstep (se 2 (by rfl) ⟨8575839, by rfl⟩ : syracuseStep 22868905 = 17151679) B17151679
theorem B30491873 : Blo 1979435 30491873 := bstep (se 2 (by rfl) ⟨11434452, by rfl⟩ : syracuseStep 30491873 = 22868905) B22868905
theorem B20327915 : Blo 1979435 20327915 := bstep (se 1 (by rfl) ⟨15245936, by rfl⟩ : syracuseStep 20327915 = 30491873) B30491873
theorem B13551943 : Blo 1979435 13551943 := bstep (se 1 (by rfl) ⟨10163957, by rfl⟩ : syracuseStep 13551943 = 20327915) B20327915
theorem B18069257 : Blo 1979435 18069257 := bstep (se 2 (by rfl) ⟨6775971, by rfl⟩ : syracuseStep 18069257 = 13551943) B13551943
theorem B12046171 : Blo 1979435 12046171 := bstep (se 1 (by rfl) ⟨9034628, by rfl⟩ : syracuseStep 12046171 = 18069257) B18069257
theorem B16061561 : Blo 1979435 16061561 := bstep (se 2 (by rfl) ⟨6023085, by rfl⟩ : syracuseStep 16061561 = 12046171) B12046171
theorem B10707707 : Blo 1979435 10707707 := bstep (se 1 (by rfl) ⟨8030780, by rfl⟩ : syracuseStep 10707707 = 16061561) B16061561
theorem B7138471 : Blo 1979435 7138471 := bstep (se 1 (by rfl) ⟨5353853, by rfl⟩ : syracuseStep 7138471 = 10707707) B10707707
theorem B9517961 : Blo 1979435 9517961 := bstep (se 2 (by rfl) ⟨3569235, by rfl⟩ : syracuseStep 9517961 = 7138471) B7138471
theorem B6345307 : Blo 1979435 6345307 := bstep (se 1 (by rfl) ⟨4758980, by rfl⟩ : syracuseStep 6345307 = 9517961) B9517961
theorem B33841637 : Blo 1979435 33841637 := bstep (se 4 (by rfl) ⟨3172653, by rfl⟩ : syracuseStep 33841637 = 6345307) B6345307
theorem B22561091 : Blo 1979435 22561091 := bstep (se 1 (by rfl) ⟨16920818, by rfl⟩ : syracuseStep 22561091 = 33841637) B33841637
theorem B15040727 : Blo 1979435 15040727 := bstep (se 1 (by rfl) ⟨11280545, by rfl⟩ : syracuseStep 15040727 = 22561091) B22561091
theorem B10027151 : Blo 1979435 10027151 := bstep (se 1 (by rfl) ⟨7520363, by rfl⟩ : syracuseStep 10027151 = 15040727) B15040727
theorem B6684767 : Blo 1979435 6684767 := bstep (se 1 (by rfl) ⟨5013575, by rfl⟩ : syracuseStep 6684767 = 10027151) B10027151
theorem B4456511 : Blo 1979435 4456511 := bstep (se 1 (by rfl) ⟨3342383, by rfl⟩ : syracuseStep 4456511 = 6684767) B6684767
theorem B2971007 : Blo 1979435 2971007 := bstep (se 1 (by rfl) ⟨2228255, by rfl⟩ : syracuseStep 2971007 = 4456511) B4456511
theorem B1980671 : Blo 1979435 1980671 := bstep (se 1 (by rfl) ⟨1485503, by rfl⟩ : syracuseStep 1980671 = 2971007) B2971007
theorem B2971013 : Blo 1979435 2971013 := bbase (se 4 (by rfl) ⟨278532, by rfl⟩ : syracuseStep 2971013 = 557065) (by norm_num)
theorem B1980675 : Blo 1979435 1980675 := bstep (se 1 (by rfl) ⟨1485506, by rfl⟩ : syracuseStep 1980675 = 2971013) B2971013
theorem B3342397 : Blo 1979435 3342397 := bbase (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) (by norm_num)
theorem B4456529 : Blo 1979435 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B2971019 : Blo 1979435 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B1980679 : Blo 1979435 1980679 := bstep (se 1 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 1980679 = 2971019) B2971019
theorem B2228269 : Blo 1979435 2228269 := bbase (se 3 (by rfl) ⟨417800, by rfl⟩ : syracuseStep 2228269 = 835601) (by norm_num)
theorem B2971025 : Blo 1979435 2971025 := bstep (se 2 (by rfl) ⟨1114134, by rfl⟩ : syracuseStep 2971025 = 2228269) B2228269
theorem B1980683 : Blo 1979435 1980683 := bstep (se 1 (by rfl) ⟨1485512, by rfl⟩ : syracuseStep 1980683 = 2971025) B2971025
theorem B6684821 : Blo 1979435 6684821 := bbase (se 6 (by rfl) ⟨156675, by rfl⟩ : syracuseStep 6684821 = 313351) (by norm_num)
theorem B4456547 : Blo 1979435 4456547 := bstep (se 1 (by rfl) ⟨3342410, by rfl⟩ : syracuseStep 4456547 = 6684821) B6684821
theorem B2971031 : Blo 1979435 2971031 := bstep (se 1 (by rfl) ⟨2228273, by rfl⟩ : syracuseStep 2971031 = 4456547) B4456547
theorem B1980687 : Blo 1979435 1980687 := bstep (se 1 (by rfl) ⟨1485515, by rfl⟩ : syracuseStep 1980687 = 2971031) B2971031
theorem B2971037 : Blo 1979435 2971037 := bbase (se 3 (by rfl) ⟨557069, by rfl⟩ : syracuseStep 2971037 = 1114139) (by norm_num)
theorem B1980691 : Blo 1979435 1980691 := bstep (se 1 (by rfl) ⟨1485518, by rfl⟩ : syracuseStep 1980691 = 2971037) B2971037
theorem B4456565 : Blo 1979435 4456565 := bbase (se 5 (by rfl) ⟨208901, by rfl⟩ : syracuseStep 4456565 = 417803) (by norm_num)
theorem B2971043 : Blo 1979435 2971043 := bstep (se 1 (by rfl) ⟨2228282, by rfl⟩ : syracuseStep 2971043 = 4456565) B4456565
theorem B1980695 : Blo 1979435 1980695 := bstep (se 1 (by rfl) ⟨1485521, by rfl⟩ : syracuseStep 1980695 = 2971043) B2971043
theorem B6023173 : Blo 1979435 6023173 := bbase (se 4 (by rfl) ⟨564672, by rfl⟩ : syracuseStep 6023173 = 1129345) (by norm_num)
theorem B8030897 : Blo 1979435 8030897 := bstep (se 2 (by rfl) ⟨3011586, by rfl⟩ : syracuseStep 8030897 = 6023173) B6023173
theorem B5353931 : Blo 1979435 5353931 := bstep (se 1 (by rfl) ⟨4015448, by rfl⟩ : syracuseStep 5353931 = 8030897) B8030897
theorem B3569287 : Blo 1979435 3569287 := bstep (se 1 (by rfl) ⟨2676965, by rfl⟩ : syracuseStep 3569287 = 5353931) B5353931
theorem B4759049 : Blo 1979435 4759049 := bstep (se 2 (by rfl) ⟨1784643, by rfl⟩ : syracuseStep 4759049 = 3569287) B3569287
theorem B3172699 : Blo 1979435 3172699 := bstep (se 1 (by rfl) ⟨2379524, by rfl⟩ : syracuseStep 3172699 = 4759049) B4759049
theorem B16921061 : Blo 1979435 16921061 := bstep (se 4 (by rfl) ⟨1586349, by rfl⟩ : syracuseStep 16921061 = 3172699) B3172699
theorem B11280707 : Blo 1979435 11280707 := bstep (se 1 (by rfl) ⟨8460530, by rfl⟩ : syracuseStep 11280707 = 16921061) B16921061
theorem B7520471 : Blo 1979435 7520471 := bstep (se 1 (by rfl) ⟨5640353, by rfl⟩ : syracuseStep 7520471 = 11280707) B11280707
theorem B5013647 : Blo 1979435 5013647 := bstep (se 1 (by rfl) ⟨3760235, by rfl⟩ : syracuseStep 5013647 = 7520471) B7520471
theorem B3342431 : Blo 1979435 3342431 := bstep (se 1 (by rfl) ⟨2506823, by rfl⟩ : syracuseStep 3342431 = 5013647) B5013647
theorem B2228287 : Blo 1979435 2228287 := bstep (se 1 (by rfl) ⟨1671215, by rfl⟩ : syracuseStep 2228287 = 3342431) B3342431
theorem B2971049 : Blo 1979435 2971049 := bstep (se 2 (by rfl) ⟨1114143, by rfl⟩ : syracuseStep 2971049 = 2228287) B2228287
theorem B1980699 : Blo 1979435 1980699 := bstep (se 1 (by rfl) ⟨1485524, by rfl⟩ : syracuseStep 1980699 = 2971049) B2971049
theorem B7520485 : Blo 1979435 7520485 := bbase (se 4 (by rfl) ⟨705045, by rfl⟩ : syracuseStep 7520485 = 1410091) (by norm_num)
theorem B10027313 : Blo 1979435 10027313 := bstep (se 2 (by rfl) ⟨3760242, by rfl⟩ : syracuseStep 10027313 = 7520485) B7520485
theorem B6684875 : Blo 1979435 6684875 := bstep (se 1 (by rfl) ⟨5013656, by rfl⟩ : syracuseStep 6684875 = 10027313) B10027313
theorem B4456583 : Blo 1979435 4456583 := bstep (se 1 (by rfl) ⟨3342437, by rfl⟩ : syracuseStep 4456583 = 6684875) B6684875
theorem B2971055 : Blo 1979435 2971055 := bstep (se 1 (by rfl) ⟨2228291, by rfl⟩ : syracuseStep 2971055 = 4456583) B4456583
theorem B1980703 : Blo 1979435 1980703 := bstep (se 1 (by rfl) ⟨1485527, by rfl⟩ : syracuseStep 1980703 = 2971055) B2971055
theorem B2971061 : Blo 1979435 2971061 := bbase (se 5 (by rfl) ⟨139268, by rfl⟩ : syracuseStep 2971061 = 278537) (by norm_num)
theorem B1980707 : Blo 1979435 1980707 := bstep (se 1 (by rfl) ⟨1485530, by rfl⟩ : syracuseStep 1980707 = 2971061) B2971061
theorem B5013677 : Blo 1979435 5013677 := bbase (se 3 (by rfl) ⟨940064, by rfl⟩ : syracuseStep 5013677 = 1880129) (by norm_num)
theorem B3342451 : Blo 1979435 3342451 := bstep (se 1 (by rfl) ⟨2506838, by rfl⟩ : syracuseStep 3342451 = 5013677) B5013677
theorem B4456601 : Blo 1979435 4456601 := bstep (se 2 (by rfl) ⟨1671225, by rfl⟩ : syracuseStep 4456601 = 3342451) B3342451
theorem B2971067 : Blo 1979435 2971067 := bstep (se 1 (by rfl) ⟨2228300, by rfl⟩ : syracuseStep 2971067 = 4456601) B4456601
theorem B1980711 : Blo 1979435 1980711 := bstep (se 1 (by rfl) ⟨1485533, by rfl⟩ : syracuseStep 1980711 = 2971067) B2971067
theorem B2228305 : Blo 1979435 2228305 := bbase (se 2 (by rfl) ⟨835614, by rfl⟩ : syracuseStep 2228305 = 1671229) (by norm_num)
theorem B2971073 : Blo 1979435 2971073 := bstep (se 2 (by rfl) ⟨1114152, by rfl⟩ : syracuseStep 2971073 = 2228305) B2228305
theorem B1980715 : Blo 1979435 1980715 := bstep (se 1 (by rfl) ⟨1485536, by rfl⟩ : syracuseStep 1980715 = 2971073) B2971073
theorem B2820205 : Blo 1979435 2820205 := bbase (se 3 (by rfl) ⟨528788, by rfl⟩ : syracuseStep 2820205 = 1057577) (by norm_num)
theorem B3760273 : Blo 1979435 3760273 := bstep (se 2 (by rfl) ⟨1410102, by rfl⟩ : syracuseStep 3760273 = 2820205) B2820205
theorem B5013697 : Blo 1979435 5013697 := bstep (se 2 (by rfl) ⟨1880136, by rfl⟩ : syracuseStep 5013697 = 3760273) B3760273
theorem B6684929 : Blo 1979435 6684929 := bstep (se 2 (by rfl) ⟨2506848, by rfl⟩ : syracuseStep 6684929 = 5013697) B5013697
theorem B4456619 : Blo 1979435 4456619 := bstep (se 1 (by rfl) ⟨3342464, by rfl⟩ : syracuseStep 4456619 = 6684929) B6684929
theorem B2971079 : Blo 1979435 2971079 := bstep (se 1 (by rfl) ⟨2228309, by rfl⟩ : syracuseStep 2971079 = 4456619) B4456619
theorem B1980719 : Blo 1979435 1980719 := bstep (se 1 (by rfl) ⟨1485539, by rfl⟩ : syracuseStep 1980719 = 2971079) B2971079
theorem B2971085 : Blo 1979435 2971085 := bbase (se 3 (by rfl) ⟨557078, by rfl⟩ : syracuseStep 2971085 = 1114157) (by norm_num)
theorem B1980723 : Blo 1979435 1980723 := bstep (se 1 (by rfl) ⟨1485542, by rfl⟩ : syracuseStep 1980723 = 2971085) B2971085
theorem B4456637 : Blo 1979435 4456637 := bbase (se 3 (by rfl) ⟨835619, by rfl⟩ : syracuseStep 4456637 = 1671239) (by norm_num)
theorem B2971091 : Blo 1979435 2971091 := bstep (se 1 (by rfl) ⟨2228318, by rfl⟩ : syracuseStep 2971091 = 4456637) B4456637
theorem B1980727 : Blo 1979435 1980727 := bstep (se 1 (by rfl) ⟨1485545, by rfl⟩ : syracuseStep 1980727 = 2971091) B2971091
theorem B3342485 : Blo 1979435 3342485 := bbase (se 6 (by rfl) ⟨78339, by rfl⟩ : syracuseStep 3342485 = 156679) (by norm_num)
theorem B2228323 : Blo 1979435 2228323 := bstep (se 1 (by rfl) ⟨1671242, by rfl⟩ : syracuseStep 2228323 = 3342485) B3342485
theorem B2971097 : Blo 1979435 2971097 := bstep (se 2 (by rfl) ⟨1114161, by rfl⟩ : syracuseStep 2971097 = 2228323) B2228323
theorem B1980731 : Blo 1979435 1980731 := bstep (se 1 (by rfl) ⟨1485548, by rfl⟩ : syracuseStep 1980731 = 2971097) B2971097
theorem B4517461 : Blo 1979435 4517461 := bbase (se 8 (by rfl) ⟨26469, by rfl⟩ : syracuseStep 4517461 = 52939) (by norm_num)
theorem B6023281 : Blo 1979435 6023281 := bstep (se 2 (by rfl) ⟨2258730, by rfl⟩ : syracuseStep 6023281 = 4517461) B4517461
theorem B8031041 : Blo 1979435 8031041 := bstep (se 2 (by rfl) ⟨3011640, by rfl⟩ : syracuseStep 8031041 = 6023281) B6023281
theorem B5354027 : Blo 1979435 5354027 := bstep (se 1 (by rfl) ⟨4015520, by rfl⟩ : syracuseStep 5354027 = 8031041) B8031041
theorem B3569351 : Blo 1979435 3569351 := bstep (se 1 (by rfl) ⟨2677013, by rfl⟩ : syracuseStep 3569351 = 5354027) B5354027
theorem B9518269 : Blo 1979435 9518269 := bstep (se 3 (by rfl) ⟨1784675, by rfl⟩ : syracuseStep 9518269 = 3569351) B3569351
theorem B12691025 : Blo 1979435 12691025 := bstep (se 2 (by rfl) ⟨4759134, by rfl⟩ : syracuseStep 12691025 = 9518269) B9518269
theorem B8460683 : Blo 1979435 8460683 := bstep (se 1 (by rfl) ⟨6345512, by rfl⟩ : syracuseStep 8460683 = 12691025) B12691025
theorem B5640455 : Blo 1979435 5640455 := bstep (se 1 (by rfl) ⟨4230341, by rfl⟩ : syracuseStep 5640455 = 8460683) B8460683
theorem B15041213 : Blo 1979435 15041213 := bstep (se 3 (by rfl) ⟨2820227, by rfl⟩ : syracuseStep 15041213 = 5640455) B5640455
theorem B10027475 : Blo 1979435 10027475 := bstep (se 1 (by rfl) ⟨7520606, by rfl⟩ : syracuseStep 10027475 = 15041213) B15041213
theorem B6684983 : Blo 1979435 6684983 := bstep (se 1 (by rfl) ⟨5013737, by rfl⟩ : syracuseStep 6684983 = 10027475) B10027475
theorem B4456655 : Blo 1979435 4456655 := bstep (se 1 (by rfl) ⟨3342491, by rfl⟩ : syracuseStep 4456655 = 6684983) B6684983
theorem B2971103 : Blo 1979435 2971103 := bstep (se 1 (by rfl) ⟨2228327, by rfl⟩ : syracuseStep 2971103 = 4456655) B4456655
theorem B1980735 : Blo 1979435 1980735 := bstep (se 1 (by rfl) ⟨1485551, by rfl⟩ : syracuseStep 1980735 = 2971103) B2971103
theorem B2971109 : Blo 1979435 2971109 := bbase (se 4 (by rfl) ⟨278541, by rfl⟩ : syracuseStep 2971109 = 557083) (by norm_num)
theorem B1980739 : Blo 1979435 1980739 := bstep (se 1 (by rfl) ⟨1485554, by rfl⟩ : syracuseStep 1980739 = 2971109) B2971109
theorem B3011653 : Blo 1979435 3011653 := bbase (se 4 (by rfl) ⟨282342, by rfl⟩ : syracuseStep 3011653 = 564685) (by norm_num)
theorem B4015537 : Blo 1979435 4015537 := bstep (se 2 (by rfl) ⟨1505826, by rfl⟩ : syracuseStep 4015537 = 3011653) B3011653
theorem B21416197 : Blo 1979435 21416197 := bstep (se 4 (by rfl) ⟨2007768, by rfl⟩ : syracuseStep 21416197 = 4015537) B4015537
theorem B28554929 : Blo 1979435 28554929 := bstep (se 2 (by rfl) ⟨10708098, by rfl⟩ : syracuseStep 28554929 = 21416197) B21416197
theorem B19036619 : Blo 1979435 19036619 := bstep (se 1 (by rfl) ⟨14277464, by rfl⟩ : syracuseStep 19036619 = 28554929) B28554929
theorem B12691079 : Blo 1979435 12691079 := bstep (se 1 (by rfl) ⟨9518309, by rfl⟩ : syracuseStep 12691079 = 19036619) B19036619
theorem B8460719 : Blo 1979435 8460719 := bstep (se 1 (by rfl) ⟨6345539, by rfl⟩ : syracuseStep 8460719 = 12691079) B12691079
theorem B5640479 : Blo 1979435 5640479 := bstep (se 1 (by rfl) ⟨4230359, by rfl⟩ : syracuseStep 5640479 = 8460719) B8460719
theorem B3760319 : Blo 1979435 3760319 := bstep (se 1 (by rfl) ⟨2820239, by rfl⟩ : syracuseStep 3760319 = 5640479) B5640479
theorem B2506879 : Blo 1979435 2506879 := bstep (se 1 (by rfl) ⟨1880159, by rfl⟩ : syracuseStep 2506879 = 3760319) B3760319
theorem B3342505 : Blo 1979435 3342505 := bstep (se 2 (by rfl) ⟨1253439, by rfl⟩ : syracuseStep 3342505 = 2506879) B2506879
theorem B4456673 : Blo 1979435 4456673 := bstep (se 2 (by rfl) ⟨1671252, by rfl⟩ : syracuseStep 4456673 = 3342505) B3342505
theorem B2971115 : Blo 1979435 2971115 := bstep (se 1 (by rfl) ⟨2228336, by rfl⟩ : syracuseStep 2971115 = 4456673) B4456673
theorem B1980743 : Blo 1979435 1980743 := bstep (se 1 (by rfl) ⟨1485557, by rfl⟩ : syracuseStep 1980743 = 2971115) B2971115
theorem B2228341 : Blo 1979435 2228341 := bbase (se 5 (by rfl) ⟨104453, by rfl⟩ : syracuseStep 2228341 = 208907) (by norm_num)
theorem B2971121 : Blo 1979435 2971121 := bstep (se 2 (by rfl) ⟨1114170, by rfl⟩ : syracuseStep 2971121 = 2228341) B2228341
theorem B1980747 : Blo 1979435 1980747 := bstep (se 1 (by rfl) ⟨1485560, by rfl⟩ : syracuseStep 1980747 = 2971121) B2971121
theorem B2506889 : Blo 1979435 2506889 := bbase (se 2 (by rfl) ⟨940083, by rfl⟩ : syracuseStep 2506889 = 1880167) (by norm_num)
theorem B6685037 : Blo 1979435 6685037 := bstep (se 3 (by rfl) ⟨1253444, by rfl⟩ : syracuseStep 6685037 = 2506889) B2506889
theorem B4456691 : Blo 1979435 4456691 := bstep (se 1 (by rfl) ⟨3342518, by rfl⟩ : syracuseStep 4456691 = 6685037) B6685037
theorem B2971127 : Blo 1979435 2971127 := bstep (se 1 (by rfl) ⟨2228345, by rfl⟩ : syracuseStep 2971127 = 4456691) B4456691
theorem B1980751 : Blo 1979435 1980751 := bstep (se 1 (by rfl) ⟨1485563, by rfl⟩ : syracuseStep 1980751 = 2971127) B2971127
theorem B2971133 : Blo 1979435 2971133 := bbase (se 3 (by rfl) ⟨557087, by rfl⟩ : syracuseStep 2971133 = 1114175) (by norm_num)
theorem B1980755 : Blo 1979435 1980755 := bstep (se 1 (by rfl) ⟨1485566, by rfl⟩ : syracuseStep 1980755 = 2971133) B2971133
theorem B4456709 : Blo 1979435 4456709 := bbase (se 4 (by rfl) ⟨417816, by rfl⟩ : syracuseStep 4456709 = 835633) (by norm_num)
theorem B2971139 : Blo 1979435 2971139 := bstep (se 1 (by rfl) ⟨2228354, by rfl⟩ : syracuseStep 2971139 = 4456709) B4456709
theorem B1980759 : Blo 1979435 1980759 := bstep (se 1 (by rfl) ⟨1485569, by rfl⟩ : syracuseStep 1980759 = 2971139) B2971139
theorem B3760357 : Blo 1979435 3760357 := bbase (se 4 (by rfl) ⟨352533, by rfl⟩ : syracuseStep 3760357 = 705067) (by norm_num)
theorem B5013809 : Blo 1979435 5013809 := bstep (se 2 (by rfl) ⟨1880178, by rfl⟩ : syracuseStep 5013809 = 3760357) B3760357
theorem B3342539 : Blo 1979435 3342539 := bstep (se 1 (by rfl) ⟨2506904, by rfl⟩ : syracuseStep 3342539 = 5013809) B5013809
theorem B2228359 : Blo 1979435 2228359 := bstep (se 1 (by rfl) ⟨1671269, by rfl⟩ : syracuseStep 2228359 = 3342539) B3342539
theorem B2971145 : Blo 1979435 2971145 := bstep (se 2 (by rfl) ⟨1114179, by rfl⟩ : syracuseStep 2971145 = 2228359) B2228359
theorem B1980763 : Blo 1979435 1980763 := bstep (se 1 (by rfl) ⟨1485572, by rfl⟩ : syracuseStep 1980763 = 2971145) B2971145
theorem B10027637 : Blo 1979435 10027637 := bbase (se 5 (by rfl) ⟨470045, by rfl⟩ : syracuseStep 10027637 = 940091) (by norm_num)
theorem B6685091 : Blo 1979435 6685091 := bstep (se 1 (by rfl) ⟨5013818, by rfl⟩ : syracuseStep 6685091 = 10027637) B10027637
theorem B4456727 : Blo 1979435 4456727 := bstep (se 1 (by rfl) ⟨3342545, by rfl⟩ : syracuseStep 4456727 = 6685091) B6685091
theorem B2971151 : Blo 1979435 2971151 := bstep (se 1 (by rfl) ⟨2228363, by rfl⟩ : syracuseStep 2971151 = 4456727) B4456727
theorem B1980767 : Blo 1979435 1980767 := bstep (se 1 (by rfl) ⟨1485575, by rfl⟩ : syracuseStep 1980767 = 2971151) B2971151
theorem B2971157 : Blo 1979435 2971157 := bbase (se 6 (by rfl) ⟨69636, by rfl⟩ : syracuseStep 2971157 = 139273) (by norm_num)
theorem B1980771 : Blo 1979435 1980771 := bstep (se 1 (by rfl) ⟨1485578, by rfl⟩ : syracuseStep 1980771 = 2971157) B2971157
theorem B12864437 : Blo 1979435 12864437 := bbase (se 5 (by rfl) ⟨603020, by rfl⟩ : syracuseStep 12864437 = 1206041) (by norm_num)
theorem B8576291 : Blo 1979435 8576291 := bstep (se 1 (by rfl) ⟨6432218, by rfl⟩ : syracuseStep 8576291 = 12864437) B12864437
theorem B22870109 : Blo 1979435 22870109 := bstep (se 3 (by rfl) ⟨4288145, by rfl⟩ : syracuseStep 22870109 = 8576291) B8576291
theorem B15246739 : Blo 1979435 15246739 := bstep (se 1 (by rfl) ⟨11435054, by rfl⟩ : syracuseStep 15246739 = 22870109) B22870109
theorem B20328985 : Blo 1979435 20328985 := bstep (se 2 (by rfl) ⟨7623369, by rfl⟩ : syracuseStep 20328985 = 15246739) B15246739
theorem B27105313 : Blo 1979435 27105313 := bstep (se 2 (by rfl) ⟨10164492, by rfl⟩ : syracuseStep 27105313 = 20328985) B20328985
theorem B36140417 : Blo 1979435 36140417 := bstep (se 2 (by rfl) ⟨13552656, by rfl⟩ : syracuseStep 36140417 = 27105313) B27105313
theorem B24093611 : Blo 1979435 24093611 := bstep (se 1 (by rfl) ⟨18070208, by rfl⟩ : syracuseStep 24093611 = 36140417) B36140417
theorem B16062407 : Blo 1979435 16062407 := bstep (se 1 (by rfl) ⟨12046805, by rfl⟩ : syracuseStep 16062407 = 24093611) B24093611
theorem B10708271 : Blo 1979435 10708271 := bstep (se 1 (by rfl) ⟨8031203, by rfl⟩ : syracuseStep 10708271 = 16062407) B16062407
theorem B7138847 : Blo 1979435 7138847 := bstep (se 1 (by rfl) ⟨5354135, by rfl⟩ : syracuseStep 7138847 = 10708271) B10708271
theorem B4759231 : Blo 1979435 4759231 := bstep (se 1 (by rfl) ⟨3569423, by rfl⟩ : syracuseStep 4759231 = 7138847) B7138847
theorem B6345641 : Blo 1979435 6345641 := bstep (se 2 (by rfl) ⟨2379615, by rfl⟩ : syracuseStep 6345641 = 4759231) B4759231
theorem B16921709 : Blo 1979435 16921709 := bstep (se 3 (by rfl) ⟨3172820, by rfl⟩ : syracuseStep 16921709 = 6345641) B6345641
theorem B11281139 : Blo 1979435 11281139 := bstep (se 1 (by rfl) ⟨8460854, by rfl⟩ : syracuseStep 11281139 = 16921709) B16921709
theorem B7520759 : Blo 1979435 7520759 := bstep (se 1 (by rfl) ⟨5640569, by rfl⟩ : syracuseStep 7520759 = 11281139) B11281139
theorem B5013839 : Blo 1979435 5013839 := bstep (se 1 (by rfl) ⟨3760379, by rfl⟩ : syracuseStep 5013839 = 7520759) B7520759
theorem B3342559 : Blo 1979435 3342559 := bstep (se 1 (by rfl) ⟨2506919, by rfl⟩ : syracuseStep 3342559 = 5013839) B5013839
theorem B4456745 : Blo 1979435 4456745 := bstep (se 2 (by rfl) ⟨1671279, by rfl⟩ : syracuseStep 4456745 = 3342559) B3342559
theorem B2971163 : Blo 1979435 2971163 := bstep (se 1 (by rfl) ⟨2228372, by rfl⟩ : syracuseStep 2971163 = 4456745) B4456745
theorem B1980775 : Blo 1979435 1980775 := bstep (se 1 (by rfl) ⟨1485581, by rfl⟩ : syracuseStep 1980775 = 2971163) B2971163
theorem B2228377 : Blo 1979435 2228377 := bbase (se 2 (by rfl) ⟨835641, by rfl⟩ : syracuseStep 2228377 = 1671283) (by norm_num)
theorem B2971169 : Blo 1979435 2971169 := bstep (se 2 (by rfl) ⟨1114188, by rfl⟩ : syracuseStep 2971169 = 2228377) B2228377
theorem B1980779 : Blo 1979435 1980779 := bstep (se 1 (by rfl) ⟨1485584, by rfl⟩ : syracuseStep 1980779 = 2971169) B2971169
theorem B7520789 : Blo 1979435 7520789 := bbase (se 6 (by rfl) ⟨176268, by rfl⟩ : syracuseStep 7520789 = 352537) (by norm_num)
theorem B5013859 : Blo 1979435 5013859 := bstep (se 1 (by rfl) ⟨3760394, by rfl⟩ : syracuseStep 5013859 = 7520789) B7520789
theorem B6685145 : Blo 1979435 6685145 := bstep (se 2 (by rfl) ⟨2506929, by rfl⟩ : syracuseStep 6685145 = 5013859) B5013859
theorem B4456763 : Blo 1979435 4456763 := bstep (se 1 (by rfl) ⟨3342572, by rfl⟩ : syracuseStep 4456763 = 6685145) B6685145
theorem B2971175 : Blo 1979435 2971175 := bstep (se 1 (by rfl) ⟨2228381, by rfl⟩ : syracuseStep 2971175 = 4456763) B4456763
theorem B1980783 : Blo 1979435 1980783 := bstep (se 1 (by rfl) ⟨1485587, by rfl⟩ : syracuseStep 1980783 = 2971175) B2971175
theorem B2971181 : Blo 1979435 2971181 := bbase (se 3 (by rfl) ⟨557096, by rfl⟩ : syracuseStep 2971181 = 1114193) (by norm_num)
theorem B1980787 : Blo 1979435 1980787 := bstep (se 1 (by rfl) ⟨1485590, by rfl⟩ : syracuseStep 1980787 = 2971181) B2971181
theorem B4456781 : Blo 1979435 4456781 := bbase (se 3 (by rfl) ⟨835646, by rfl⟩ : syracuseStep 4456781 = 1671293) (by norm_num)
theorem B2971187 : Blo 1979435 2971187 := bstep (se 1 (by rfl) ⟨2228390, by rfl⟩ : syracuseStep 2971187 = 4456781) B4456781
theorem B1980791 : Blo 1979435 1980791 := bstep (se 1 (by rfl) ⟨1485593, by rfl⟩ : syracuseStep 1980791 = 2971187) B2971187
theorem B2506945 : Blo 1979435 2506945 := bbase (se 2 (by rfl) ⟨940104, by rfl⟩ : syracuseStep 2506945 = 1880209) (by norm_num)
theorem B3342593 : Blo 1979435 3342593 := bstep (se 2 (by rfl) ⟨1253472, by rfl⟩ : syracuseStep 3342593 = 2506945) B2506945
theorem B2228395 : Blo 1979435 2228395 := bstep (se 1 (by rfl) ⟨1671296, by rfl⟩ : syracuseStep 2228395 = 3342593) B3342593
theorem B2971193 : Blo 1979435 2971193 := bstep (se 2 (by rfl) ⟨1114197, by rfl⟩ : syracuseStep 2971193 = 2228395) B2228395
theorem B1980795 : Blo 1979435 1980795 := bstep (se 1 (by rfl) ⟨1485596, by rfl⟩ : syracuseStep 1980795 = 2971193) B2971193
theorem B6023477 : Blo 1979435 6023477 := bbase (se 5 (by rfl) ⟨282350, by rfl⟩ : syracuseStep 6023477 = 564701) (by norm_num)
theorem B4015651 : Blo 1979435 4015651 := bstep (se 1 (by rfl) ⟨3011738, by rfl⟩ : syracuseStep 4015651 = 6023477) B6023477
theorem B5354201 : Blo 1979435 5354201 := bstep (se 2 (by rfl) ⟨2007825, by rfl⟩ : syracuseStep 5354201 = 4015651) B4015651
theorem B3569467 : Blo 1979435 3569467 := bstep (se 1 (by rfl) ⟨2677100, by rfl⟩ : syracuseStep 3569467 = 5354201) B5354201
theorem B4759289 : Blo 1979435 4759289 := bstep (se 2 (by rfl) ⟨1784733, by rfl⟩ : syracuseStep 4759289 = 3569467) B3569467
theorem B3172859 : Blo 1979435 3172859 := bstep (se 1 (by rfl) ⟨2379644, by rfl⟩ : syracuseStep 3172859 = 4759289) B4759289
theorem B2115239 : Blo 1979435 2115239 := bstep (se 1 (by rfl) ⟨1586429, by rfl⟩ : syracuseStep 2115239 = 3172859) B3172859
theorem B22562549 : Blo 1979435 22562549 := bstep (se 5 (by rfl) ⟨1057619, by rfl⟩ : syracuseStep 22562549 = 2115239) B2115239
theorem B15041699 : Blo 1979435 15041699 := bstep (se 1 (by rfl) ⟨11281274, by rfl⟩ : syracuseStep 15041699 = 22562549) B22562549
theorem B10027799 : Blo 1979435 10027799 := bstep (se 1 (by rfl) ⟨7520849, by rfl⟩ : syracuseStep 10027799 = 15041699) B15041699
theorem B6685199 : Blo 1979435 6685199 := bstep (se 1 (by rfl) ⟨5013899, by rfl⟩ : syracuseStep 6685199 = 10027799) B10027799
theorem B4456799 : Blo 1979435 4456799 := bstep (se 1 (by rfl) ⟨3342599, by rfl⟩ : syracuseStep 4456799 = 6685199) B6685199
theorem B2971199 : Blo 1979435 2971199 := bstep (se 1 (by rfl) ⟨2228399, by rfl⟩ : syracuseStep 2971199 = 4456799) B4456799
theorem B1980799 : Blo 1979435 1980799 := bstep (se 1 (by rfl) ⟨1485599, by rfl⟩ : syracuseStep 1980799 = 2971199) B2971199
theorem B2971205 : Blo 1979435 2971205 := bbase (se 4 (by rfl) ⟨278550, by rfl⟩ : syracuseStep 2971205 = 557101) (by norm_num)
theorem B1980803 : Blo 1979435 1980803 := bstep (se 1 (by rfl) ⟨1485602, by rfl⟩ : syracuseStep 1980803 = 2971205) B2971205
theorem B3342613 : Blo 1979435 3342613 := bbase (se 6 (by rfl) ⟨78342, by rfl⟩ : syracuseStep 3342613 = 156685) (by norm_num)
theorem B4456817 : Blo 1979435 4456817 := bstep (se 2 (by rfl) ⟨1671306, by rfl⟩ : syracuseStep 4456817 = 3342613) B3342613
theorem B2971211 : Blo 1979435 2971211 := bstep (se 1 (by rfl) ⟨2228408, by rfl⟩ : syracuseStep 2971211 = 4456817) B4456817
theorem B1980807 : Blo 1979435 1980807 := bstep (se 1 (by rfl) ⟨1485605, by rfl⟩ : syracuseStep 1980807 = 2971211) B2971211
theorem B2228413 : Blo 1979435 2228413 := bbase (se 3 (by rfl) ⟨417827, by rfl⟩ : syracuseStep 2228413 = 835655) (by norm_num)
theorem B2971217 : Blo 1979435 2971217 := bstep (se 2 (by rfl) ⟨1114206, by rfl⟩ : syracuseStep 2971217 = 2228413) B2228413
theorem B1980811 : Blo 1979435 1980811 := bstep (se 1 (by rfl) ⟨1485608, by rfl⟩ : syracuseStep 1980811 = 2971217) B2971217
theorem B6685253 : Blo 1979435 6685253 := bbase (se 4 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 6685253 = 1253485) (by norm_num)
theorem B4456835 : Blo 1979435 4456835 := bstep (se 1 (by rfl) ⟨3342626, by rfl⟩ : syracuseStep 4456835 = 6685253) B6685253
theorem B2971223 : Blo 1979435 2971223 := bstep (se 1 (by rfl) ⟨2228417, by rfl⟩ : syracuseStep 2971223 = 4456835) B4456835
theorem B1980815 : Blo 1979435 1980815 := bstep (se 1 (by rfl) ⟨1485611, by rfl⟩ : syracuseStep 1980815 = 2971223) B2971223
theorem B2971229 : Blo 1979435 2971229 := bbase (se 3 (by rfl) ⟨557105, by rfl⟩ : syracuseStep 2971229 = 1114211) (by norm_num)
theorem B1980819 : Blo 1979435 1980819 := bstep (se 1 (by rfl) ⟨1485614, by rfl⟩ : syracuseStep 1980819 = 2971229) B2971229
theorem B4456853 : Blo 1979435 4456853 := bbase (se 6 (by rfl) ⟨104457, by rfl⟩ : syracuseStep 4456853 = 208915) (by norm_num)
theorem B2971235 : Blo 1979435 2971235 := bstep (se 1 (by rfl) ⟨2228426, by rfl⟩ : syracuseStep 2971235 = 4456853) B4456853
theorem B1980823 : Blo 1979435 1980823 := bstep (se 1 (by rfl) ⟨1485617, by rfl⟩ : syracuseStep 1980823 = 2971235) B2971235
theorem B4759357 : Blo 1979435 4759357 := bbase (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) (by norm_num)
theorem B6345809 : Blo 1979435 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B4230539 : Blo 1979435 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B2820359 : Blo 1979435 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B7520957 : Blo 1979435 7520957 := bstep (se 3 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 7520957 = 2820359) B2820359
theorem B5013971 : Blo 1979435 5013971 := bstep (se 1 (by rfl) ⟨3760478, by rfl⟩ : syracuseStep 5013971 = 7520957) B7520957
theorem B3342647 : Blo 1979435 3342647 := bstep (se 1 (by rfl) ⟨2506985, by rfl⟩ : syracuseStep 3342647 = 5013971) B5013971
theorem B2228431 : Blo 1979435 2228431 := bstep (se 1 (by rfl) ⟨1671323, by rfl⟩ : syracuseStep 2228431 = 3342647) B3342647
theorem B2971241 : Blo 1979435 2971241 := bstep (se 2 (by rfl) ⟨1114215, by rfl⟩ : syracuseStep 2971241 = 2228431) B2228431
theorem B1980827 : Blo 1979435 1980827 := bstep (se 1 (by rfl) ⟨1485620, by rfl⟩ : syracuseStep 1980827 = 2971241) B2971241
theorem B8461093 : Blo 1979435 8461093 := bbase (se 4 (by rfl) ⟨793227, by rfl⟩ : syracuseStep 8461093 = 1586455) (by norm_num)
theorem B11281457 : Blo 1979435 11281457 := bstep (se 2 (by rfl) ⟨4230546, by rfl⟩ : syracuseStep 11281457 = 8461093) B8461093
theorem B7520971 : Blo 1979435 7520971 := bstep (se 1 (by rfl) ⟨5640728, by rfl⟩ : syracuseStep 7520971 = 11281457) B11281457
theorem B10027961 : Blo 1979435 10027961 := bstep (se 2 (by rfl) ⟨3760485, by rfl⟩ : syracuseStep 10027961 = 7520971) B7520971
theorem B6685307 : Blo 1979435 6685307 := bstep (se 1 (by rfl) ⟨5013980, by rfl⟩ : syracuseStep 6685307 = 10027961) B10027961
theorem B4456871 : Blo 1979435 4456871 := bstep (se 1 (by rfl) ⟨3342653, by rfl⟩ : syracuseStep 4456871 = 6685307) B6685307
theorem B2971247 : Blo 1979435 2971247 := bstep (se 1 (by rfl) ⟨2228435, by rfl⟩ : syracuseStep 2971247 = 4456871) B4456871
theorem B1980831 : Blo 1979435 1980831 := bstep (se 1 (by rfl) ⟨1485623, by rfl⟩ : syracuseStep 1980831 = 2971247) B2971247
theorem B2971253 : Blo 1979435 2971253 := bbase (se 5 (by rfl) ⟨139277, by rfl⟩ : syracuseStep 2971253 = 278555) (by norm_num)
theorem B1980835 : Blo 1979435 1980835 := bstep (se 1 (by rfl) ⟨1485626, by rfl⟩ : syracuseStep 1980835 = 2971253) B2971253
theorem B3760501 : Blo 1979435 3760501 := bbase (se 5 (by rfl) ⟨176273, by rfl⟩ : syracuseStep 3760501 = 352547) (by norm_num)
theorem B5014001 : Blo 1979435 5014001 := bstep (se 2 (by rfl) ⟨1880250, by rfl⟩ : syracuseStep 5014001 = 3760501) B3760501
theorem B3342667 : Blo 1979435 3342667 := bstep (se 1 (by rfl) ⟨2507000, by rfl⟩ : syracuseStep 3342667 = 5014001) B5014001
theorem B4456889 : Blo 1979435 4456889 := bstep (se 2 (by rfl) ⟨1671333, by rfl⟩ : syracuseStep 4456889 = 3342667) B3342667
theorem B2971259 : Blo 1979435 2971259 := bstep (se 1 (by rfl) ⟨2228444, by rfl⟩ : syracuseStep 2971259 = 4456889) B4456889
theorem B1980839 : Blo 1979435 1980839 := bstep (se 1 (by rfl) ⟨1485629, by rfl⟩ : syracuseStep 1980839 = 2971259) B2971259
theorem B2228449 : Blo 1979435 2228449 := bbase (se 2 (by rfl) ⟨835668, by rfl⟩ : syracuseStep 2228449 = 1671337) (by norm_num)
theorem B2971265 : Blo 1979435 2971265 := bstep (se 2 (by rfl) ⟨1114224, by rfl⟩ : syracuseStep 2971265 = 2228449) B2228449
theorem B1980843 : Blo 1979435 1980843 := bstep (se 1 (by rfl) ⟨1485632, by rfl⟩ : syracuseStep 1980843 = 2971265) B2971265
theorem B5014021 : Blo 1979435 5014021 := bbase (se 4 (by rfl) ⟨470064, by rfl⟩ : syracuseStep 5014021 = 940129) (by norm_num)
theorem B6685361 : Blo 1979435 6685361 := bstep (se 2 (by rfl) ⟨2507010, by rfl⟩ : syracuseStep 6685361 = 5014021) B5014021
theorem B4456907 : Blo 1979435 4456907 := bstep (se 1 (by rfl) ⟨3342680, by rfl⟩ : syracuseStep 4456907 = 6685361) B6685361
theorem B2971271 : Blo 1979435 2971271 := bstep (se 1 (by rfl) ⟨2228453, by rfl⟩ : syracuseStep 2971271 = 4456907) B4456907
theorem B1980847 : Blo 1979435 1980847 := bstep (se 1 (by rfl) ⟨1485635, by rfl⟩ : syracuseStep 1980847 = 2971271) B2971271
theorem B2971277 : Blo 1979435 2971277 := bbase (se 3 (by rfl) ⟨557114, by rfl⟩ : syracuseStep 2971277 = 1114229) (by norm_num)
theorem B1980851 : Blo 1979435 1980851 := bstep (se 1 (by rfl) ⟨1485638, by rfl⟩ : syracuseStep 1980851 = 2971277) B2971277
theorem B4456925 : Blo 1979435 4456925 := bbase (se 3 (by rfl) ⟨835673, by rfl⟩ : syracuseStep 4456925 = 1671347) (by norm_num)
theorem B2971283 : Blo 1979435 2971283 := bstep (se 1 (by rfl) ⟨2228462, by rfl⟩ : syracuseStep 2971283 = 4456925) B4456925
theorem B1980855 : Blo 1979435 1980855 := bstep (se 1 (by rfl) ⟨1485641, by rfl⟩ : syracuseStep 1980855 = 2971283) B2971283
theorem B3342701 : Blo 1979435 3342701 := bbase (se 3 (by rfl) ⟨626756, by rfl⟩ : syracuseStep 3342701 = 1253513) (by norm_num)
theorem B2228467 : Blo 1979435 2228467 := bstep (se 1 (by rfl) ⟨1671350, by rfl⟩ : syracuseStep 2228467 = 3342701) B3342701
theorem B2971289 : Blo 1979435 2971289 := bstep (se 2 (by rfl) ⟨1114233, by rfl⟩ : syracuseStep 2971289 = 2228467) B2228467
theorem B1980859 : Blo 1979435 1980859 := bstep (se 1 (by rfl) ⟨1485644, by rfl⟩ : syracuseStep 1980859 = 2971289) B2971289
theorem B28946261 : Blo 1979435 28946261 := bbase (se 9 (by rfl) ⟨84803, by rfl⟩ : syracuseStep 28946261 = 169607) (by norm_num)
theorem B77190029 : Blo 1979435 77190029 := bstep (se 3 (by rfl) ⟨14473130, by rfl⟩ : syracuseStep 77190029 = 28946261) B28946261
theorem B51460019 : Blo 1979435 51460019 := bstep (se 1 (by rfl) ⟨38595014, by rfl⟩ : syracuseStep 51460019 = 77190029) B77190029
theorem B34306679 : Blo 1979435 34306679 := bstep (se 1 (by rfl) ⟨25730009, by rfl⟩ : syracuseStep 34306679 = 51460019) B51460019
theorem B22871119 : Blo 1979435 22871119 := bstep (se 1 (by rfl) ⟨17153339, by rfl⟩ : syracuseStep 22871119 = 34306679) B34306679
theorem B30494825 : Blo 1979435 30494825 := bstep (se 2 (by rfl) ⟨11435559, by rfl⟩ : syracuseStep 30494825 = 22871119) B22871119
theorem B20329883 : Blo 1979435 20329883 := bstep (se 1 (by rfl) ⟨15247412, by rfl⟩ : syracuseStep 20329883 = 30494825) B30494825
theorem B13553255 : Blo 1979435 13553255 := bstep (se 1 (by rfl) ⟨10164941, by rfl⟩ : syracuseStep 13553255 = 20329883) B20329883
theorem B36142013 : Blo 1979435 36142013 := bstep (se 3 (by rfl) ⟨6776627, by rfl⟩ : syracuseStep 36142013 = 13553255) B13553255
theorem B24094675 : Blo 1979435 24094675 := bstep (se 1 (by rfl) ⟨18071006, by rfl⟩ : syracuseStep 24094675 = 36142013) B36142013
theorem B32126233 : Blo 1979435 32126233 := bstep (se 2 (by rfl) ⟨12047337, by rfl⟩ : syracuseStep 32126233 = 24094675) B24094675
theorem B42834977 : Blo 1979435 42834977 := bstep (se 2 (by rfl) ⟨16063116, by rfl⟩ : syracuseStep 42834977 = 32126233) B32126233
theorem B28556651 : Blo 1979435 28556651 := bstep (se 1 (by rfl) ⟨21417488, by rfl⟩ : syracuseStep 28556651 = 42834977) B42834977
theorem B19037767 : Blo 1979435 19037767 := bstep (se 1 (by rfl) ⟨14278325, by rfl⟩ : syracuseStep 19037767 = 28556651) B28556651
theorem B25383689 : Blo 1979435 25383689 := bstep (se 2 (by rfl) ⟨9518883, by rfl⟩ : syracuseStep 25383689 = 19037767) B19037767
theorem B16922459 : Blo 1979435 16922459 := bstep (se 1 (by rfl) ⟨12691844, by rfl⟩ : syracuseStep 16922459 = 25383689) B25383689
theorem B11281639 : Blo 1979435 11281639 := bstep (se 1 (by rfl) ⟨8461229, by rfl⟩ : syracuseStep 11281639 = 16922459) B16922459
theorem B15042185 : Blo 1979435 15042185 := bstep (se 2 (by rfl) ⟨5640819, by rfl⟩ : syracuseStep 15042185 = 11281639) B11281639
theorem B10028123 : Blo 1979435 10028123 := bstep (se 1 (by rfl) ⟨7521092, by rfl⟩ : syracuseStep 10028123 = 15042185) B15042185
theorem B6685415 : Blo 1979435 6685415 := bstep (se 1 (by rfl) ⟨5014061, by rfl⟩ : syracuseStep 6685415 = 10028123) B10028123
theorem B4456943 : Blo 1979435 4456943 := bstep (se 1 (by rfl) ⟨3342707, by rfl⟩ : syracuseStep 4456943 = 6685415) B6685415
theorem B2971295 : Blo 1979435 2971295 := bstep (se 1 (by rfl) ⟨2228471, by rfl⟩ : syracuseStep 2971295 = 4456943) B4456943
theorem B1980863 : Blo 1979435 1980863 := bstep (se 1 (by rfl) ⟨1485647, by rfl⟩ : syracuseStep 1980863 = 2971295) B2971295
theorem B2971301 : Blo 1979435 2971301 := bbase (se 4 (by rfl) ⟨278559, by rfl⟩ : syracuseStep 2971301 = 557119) (by norm_num)
theorem B1980867 : Blo 1979435 1980867 := bstep (se 1 (by rfl) ⟨1485650, by rfl⟩ : syracuseStep 1980867 = 2971301) B2971301
theorem B2507041 : Blo 1979435 2507041 := bbase (se 2 (by rfl) ⟨940140, by rfl⟩ : syracuseStep 2507041 = 1880281) (by norm_num)
theorem B3342721 : Blo 1979435 3342721 := bstep (se 2 (by rfl) ⟨1253520, by rfl⟩ : syracuseStep 3342721 = 2507041) B2507041
theorem B4456961 : Blo 1979435 4456961 := bstep (se 2 (by rfl) ⟨1671360, by rfl⟩ : syracuseStep 4456961 = 3342721) B3342721
theorem B2971307 : Blo 1979435 2971307 := bstep (se 1 (by rfl) ⟨2228480, by rfl⟩ : syracuseStep 2971307 = 4456961) B4456961
theorem B1980871 : Blo 1979435 1980871 := bstep (se 1 (by rfl) ⟨1485653, by rfl⟩ : syracuseStep 1980871 = 2971307) B2971307
theorem B2228485 : Blo 1979435 2228485 := bbase (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) (by norm_num)
theorem B2971313 : Blo 1979435 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B1980875 : Blo 1979435 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B2115325 : Blo 1979435 2115325 := bbase (se 3 (by rfl) ⟨396623, by rfl⟩ : syracuseStep 2115325 = 793247) (by norm_num)
theorem B2820433 : Blo 1979435 2820433 := bstep (se 2 (by rfl) ⟨1057662, by rfl⟩ : syracuseStep 2820433 = 2115325) B2115325
theorem B3760577 : Blo 1979435 3760577 := bstep (se 2 (by rfl) ⟨1410216, by rfl⟩ : syracuseStep 3760577 = 2820433) B2820433
theorem B2507051 : Blo 1979435 2507051 := bstep (se 1 (by rfl) ⟨1880288, by rfl⟩ : syracuseStep 2507051 = 3760577) B3760577
theorem B6685469 : Blo 1979435 6685469 := bstep (se 3 (by rfl) ⟨1253525, by rfl⟩ : syracuseStep 6685469 = 2507051) B2507051
theorem B4456979 : Blo 1979435 4456979 := bstep (se 1 (by rfl) ⟨3342734, by rfl⟩ : syracuseStep 4456979 = 6685469) B6685469
theorem B2971319 : Blo 1979435 2971319 := bstep (se 1 (by rfl) ⟨2228489, by rfl⟩ : syracuseStep 2971319 = 4456979) B4456979
theorem B1980879 : Blo 1979435 1980879 := bstep (se 1 (by rfl) ⟨1485659, by rfl⟩ : syracuseStep 1980879 = 2971319) B2971319
theorem B2971325 : Blo 1979435 2971325 := bbase (se 3 (by rfl) ⟨557123, by rfl⟩ : syracuseStep 2971325 = 1114247) (by norm_num)
theorem B1980883 : Blo 1979435 1980883 := bstep (se 1 (by rfl) ⟨1485662, by rfl⟩ : syracuseStep 1980883 = 2971325) B2971325
theorem B4456997 : Blo 1979435 4456997 := bbase (se 4 (by rfl) ⟨417843, by rfl⟩ : syracuseStep 4456997 = 835687) (by norm_num)
theorem B2971331 : Blo 1979435 2971331 := bstep (se 1 (by rfl) ⟨2228498, by rfl⟩ : syracuseStep 2971331 = 4456997) B4456997
theorem B1980887 : Blo 1979435 1980887 := bstep (se 1 (by rfl) ⟨1485665, by rfl⟩ : syracuseStep 1980887 = 2971331) B2971331
theorem B5014133 : Blo 1979435 5014133 := bbase (se 5 (by rfl) ⟨235037, by rfl⟩ : syracuseStep 5014133 = 470075) (by norm_num)
theorem B3342755 : Blo 1979435 3342755 := bstep (se 1 (by rfl) ⟨2507066, by rfl⟩ : syracuseStep 3342755 = 5014133) B5014133
theorem B2228503 : Blo 1979435 2228503 := bstep (se 1 (by rfl) ⟨1671377, by rfl⟩ : syracuseStep 2228503 = 3342755) B3342755
theorem B2971337 : Blo 1979435 2971337 := bstep (se 2 (by rfl) ⟨1114251, by rfl⟩ : syracuseStep 2971337 = 2228503) B2228503
theorem B1980891 : Blo 1979435 1980891 := bstep (se 1 (by rfl) ⟨1485668, by rfl⟩ : syracuseStep 1980891 = 2971337) B2971337
theorem B2541277 : Blo 1979435 2541277 := bbase (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) (by norm_num)
theorem B13553477 : Blo 1979435 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B9035651 : Blo 1979435 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B24095069 : Blo 1979435 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B16063379 : Blo 1979435 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B10708919 : Blo 1979435 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B7139279 : Blo 1979435 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B19038077 : Blo 1979435 19038077 := bstep (se 3 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 19038077 = 7139279) B7139279
theorem B12692051 : Blo 1979435 12692051 := bstep (se 1 (by rfl) ⟨9519038, by rfl⟩ : syracuseStep 12692051 = 19038077) B19038077
theorem B8461367 : Blo 1979435 8461367 := bstep (se 1 (by rfl) ⟨6346025, by rfl⟩ : syracuseStep 8461367 = 12692051) B12692051
theorem B5640911 : Blo 1979435 5640911 := bstep (se 1 (by rfl) ⟨4230683, by rfl⟩ : syracuseStep 5640911 = 8461367) B8461367
theorem B3760607 : Blo 1979435 3760607 := bstep (se 1 (by rfl) ⟨2820455, by rfl⟩ : syracuseStep 3760607 = 5640911) B5640911
theorem B10028285 : Blo 1979435 10028285 := bstep (se 3 (by rfl) ⟨1880303, by rfl⟩ : syracuseStep 10028285 = 3760607) B3760607
theorem B6685523 : Blo 1979435 6685523 := bstep (se 1 (by rfl) ⟨5014142, by rfl⟩ : syracuseStep 6685523 = 10028285) B10028285
theorem B4457015 : Blo 1979435 4457015 := bstep (se 1 (by rfl) ⟨3342761, by rfl⟩ : syracuseStep 4457015 = 6685523) B6685523
theorem B2971343 : Blo 1979435 2971343 := bstep (se 1 (by rfl) ⟨2228507, by rfl⟩ : syracuseStep 2971343 = 4457015) B4457015
theorem B1980895 : Blo 1979435 1980895 := bstep (se 1 (by rfl) ⟨1485671, by rfl⟩ : syracuseStep 1980895 = 2971343) B2971343
theorem B2971349 : Blo 1979435 2971349 := bbase (se 7 (by rfl) ⟨34820, by rfl⟩ : syracuseStep 2971349 = 69641) (by norm_num)
theorem B1980899 : Blo 1979435 1980899 := bstep (se 1 (by rfl) ⟨1485674, by rfl⟩ : syracuseStep 1980899 = 2971349) B2971349
theorem B4230701 : Blo 1979435 4230701 := bbase (se 3 (by rfl) ⟨793256, by rfl⟩ : syracuseStep 4230701 = 1586513) (by norm_num)
theorem B2820467 : Blo 1979435 2820467 := bstep (se 1 (by rfl) ⟨2115350, by rfl⟩ : syracuseStep 2820467 = 4230701) B4230701
theorem B7521245 : Blo 1979435 7521245 := bstep (se 3 (by rfl) ⟨1410233, by rfl⟩ : syracuseStep 7521245 = 2820467) B2820467
theorem B5014163 : Blo 1979435 5014163 := bstep (se 1 (by rfl) ⟨3760622, by rfl⟩ : syracuseStep 5014163 = 7521245) B7521245
theorem B3342775 : Blo 1979435 3342775 := bstep (se 1 (by rfl) ⟨2507081, by rfl⟩ : syracuseStep 3342775 = 5014163) B5014163
theorem B4457033 : Blo 1979435 4457033 := bstep (se 2 (by rfl) ⟨1671387, by rfl⟩ : syracuseStep 4457033 = 3342775) B3342775
theorem B2971355 : Blo 1979435 2971355 := bstep (se 1 (by rfl) ⟨2228516, by rfl⟩ : syracuseStep 2971355 = 4457033) B4457033
theorem B1980903 : Blo 1979435 1980903 := bstep (se 1 (by rfl) ⟨1485677, by rfl⟩ : syracuseStep 1980903 = 2971355) B2971355
theorem B2228521 : Blo 1979435 2228521 := bbase (se 2 (by rfl) ⟨835695, by rfl⟩ : syracuseStep 2228521 = 1671391) (by norm_num)
theorem B2971361 : Blo 1979435 2971361 := bstep (se 2 (by rfl) ⟨1114260, by rfl⟩ : syracuseStep 2971361 = 2228521) B2228521
theorem B1980907 : Blo 1979435 1980907 := bstep (se 1 (by rfl) ⟨1485680, by rfl⟩ : syracuseStep 1980907 = 2971361) B2971361
theorem B4015877 : Blo 1979435 4015877 := bbase (se 4 (by rfl) ⟨376488, by rfl⟩ : syracuseStep 4015877 = 752977) (by norm_num)
theorem B10709005 : Blo 1979435 10709005 := bstep (se 3 (by rfl) ⟨2007938, by rfl⟩ : syracuseStep 10709005 = 4015877) B4015877
theorem B14278673 : Blo 1979435 14278673 := bstep (se 2 (by rfl) ⟨5354502, by rfl⟩ : syracuseStep 14278673 = 10709005) B10709005
theorem B9519115 : Blo 1979435 9519115 := bstep (se 1 (by rfl) ⟨7139336, by rfl⟩ : syracuseStep 9519115 = 14278673) B14278673
theorem B12692153 : Blo 1979435 12692153 := bstep (se 2 (by rfl) ⟨4759557, by rfl⟩ : syracuseStep 12692153 = 9519115) B9519115
theorem B8461435 : Blo 1979435 8461435 := bstep (se 1 (by rfl) ⟨6346076, by rfl⟩ : syracuseStep 8461435 = 12692153) B12692153
theorem B11281913 : Blo 1979435 11281913 := bstep (se 2 (by rfl) ⟨4230717, by rfl⟩ : syracuseStep 11281913 = 8461435) B8461435
theorem B7521275 : Blo 1979435 7521275 := bstep (se 1 (by rfl) ⟨5640956, by rfl⟩ : syracuseStep 7521275 = 11281913) B11281913
theorem B5014183 : Blo 1979435 5014183 := bstep (se 1 (by rfl) ⟨3760637, by rfl⟩ : syracuseStep 5014183 = 7521275) B7521275
theorem B6685577 : Blo 1979435 6685577 := bstep (se 2 (by rfl) ⟨2507091, by rfl⟩ : syracuseStep 6685577 = 5014183) B5014183
theorem B4457051 : Blo 1979435 4457051 := bstep (se 1 (by rfl) ⟨3342788, by rfl⟩ : syracuseStep 4457051 = 6685577) B6685577
theorem B2971367 : Blo 1979435 2971367 := bstep (se 1 (by rfl) ⟨2228525, by rfl⟩ : syracuseStep 2971367 = 4457051) B4457051
theorem B1980911 : Blo 1979435 1980911 := bstep (se 1 (by rfl) ⟨1485683, by rfl⟩ : syracuseStep 1980911 = 2971367) B2971367
theorem B2971373 : Blo 1979435 2971373 := bbase (se 3 (by rfl) ⟨557132, by rfl⟩ : syracuseStep 2971373 = 1114265) (by norm_num)
theorem B1980915 : Blo 1979435 1980915 := bstep (se 1 (by rfl) ⟨1485686, by rfl⟩ : syracuseStep 1980915 = 2971373) B2971373
theorem B4457069 : Blo 1979435 4457069 := bbase (se 3 (by rfl) ⟨835700, by rfl⟩ : syracuseStep 4457069 = 1671401) (by norm_num)
theorem B2971379 : Blo 1979435 2971379 := bstep (se 1 (by rfl) ⟨2228534, by rfl⟩ : syracuseStep 2971379 = 4457069) B4457069
theorem B1980919 : Blo 1979435 1980919 := bstep (se 1 (by rfl) ⟨1485689, by rfl⟩ : syracuseStep 1980919 = 2971379) B2971379
theorem B3760661 : Blo 1979435 3760661 := bbase (se 6 (by rfl) ⟨88140, by rfl⟩ : syracuseStep 3760661 = 176281) (by norm_num)
theorem B2507107 : Blo 1979435 2507107 := bstep (se 1 (by rfl) ⟨1880330, by rfl⟩ : syracuseStep 2507107 = 3760661) B3760661
theorem B3342809 : Blo 1979435 3342809 := bstep (se 2 (by rfl) ⟨1253553, by rfl⟩ : syracuseStep 3342809 = 2507107) B2507107
theorem B2228539 : Blo 1979435 2228539 := bstep (se 1 (by rfl) ⟨1671404, by rfl⟩ : syracuseStep 2228539 = 3342809) B3342809
theorem B2971385 : Blo 1979435 2971385 := bstep (se 2 (by rfl) ⟨1114269, by rfl⟩ : syracuseStep 2971385 = 2228539) B2228539
theorem B1980923 : Blo 1979435 1980923 := bstep (se 1 (by rfl) ⟨1485692, by rfl⟩ : syracuseStep 1980923 = 2971385) B2971385
theorem B2144237 : Blo 1979435 2144237 := bbase (se 3 (by rfl) ⟨402044, by rfl⟩ : syracuseStep 2144237 = 804089) (by norm_num)
theorem B5717965 : Blo 1979435 5717965 := bstep (se 3 (by rfl) ⟨1072118, by rfl⟩ : syracuseStep 5717965 = 2144237) B2144237
theorem B7623953 : Blo 1979435 7623953 := bstep (se 2 (by rfl) ⟨2858982, by rfl⟩ : syracuseStep 7623953 = 5717965) B5717965
theorem B5082635 : Blo 1979435 5082635 := bstep (se 1 (by rfl) ⟨3811976, by rfl⟩ : syracuseStep 5082635 = 7623953) B7623953
theorem B3388423 : Blo 1979435 3388423 := bstep (se 1 (by rfl) ⟨2541317, by rfl⟩ : syracuseStep 3388423 = 5082635) B5082635
theorem B72286357 : Blo 1979435 72286357 := bstep (se 6 (by rfl) ⟨1694211, by rfl⟩ : syracuseStep 72286357 = 3388423) B3388423
theorem B96381809 : Blo 1979435 96381809 := bstep (se 2 (by rfl) ⟨36143178, by rfl⟩ : syracuseStep 96381809 = 72286357) B72286357
theorem B64254539 : Blo 1979435 64254539 := bstep (se 1 (by rfl) ⟨48190904, by rfl⟩ : syracuseStep 64254539 = 96381809) B96381809
theorem B42836359 : Blo 1979435 42836359 := bstep (se 1 (by rfl) ⟨32127269, by rfl⟩ : syracuseStep 42836359 = 64254539) B64254539
theorem B57115145 : Blo 1979435 57115145 := bstep (se 2 (by rfl) ⟨21418179, by rfl⟩ : syracuseStep 57115145 = 42836359) B42836359
theorem B38076763 : Blo 1979435 38076763 := bstep (se 1 (by rfl) ⟨28557572, by rfl⟩ : syracuseStep 38076763 = 57115145) B57115145
theorem B50769017 : Blo 1979435 50769017 := bstep (se 2 (by rfl) ⟨19038381, by rfl⟩ : syracuseStep 50769017 = 38076763) B38076763
theorem B33846011 : Blo 1979435 33846011 := bstep (se 1 (by rfl) ⟨25384508, by rfl⟩ : syracuseStep 33846011 = 50769017) B50769017
theorem B22564007 : Blo 1979435 22564007 := bstep (se 1 (by rfl) ⟨16923005, by rfl⟩ : syracuseStep 22564007 = 33846011) B33846011
theorem B15042671 : Blo 1979435 15042671 := bstep (se 1 (by rfl) ⟨11282003, by rfl⟩ : syracuseStep 15042671 = 22564007) B22564007
theorem B10028447 : Blo 1979435 10028447 := bstep (se 1 (by rfl) ⟨7521335, by rfl⟩ : syracuseStep 10028447 = 15042671) B15042671
theorem B6685631 : Blo 1979435 6685631 := bstep (se 1 (by rfl) ⟨5014223, by rfl⟩ : syracuseStep 6685631 = 10028447) B10028447
theorem B4457087 : Blo 1979435 4457087 := bstep (se 1 (by rfl) ⟨3342815, by rfl⟩ : syracuseStep 4457087 = 6685631) B6685631
theorem B2971391 : Blo 1979435 2971391 := bstep (se 1 (by rfl) ⟨2228543, by rfl⟩ : syracuseStep 2971391 = 4457087) B4457087
theorem B1980927 : Blo 1979435 1980927 := bstep (se 1 (by rfl) ⟨1485695, by rfl⟩ : syracuseStep 1980927 = 2971391) B2971391
theorem B2971397 : Blo 1979435 2971397 := bbase (se 4 (by rfl) ⟨278568, by rfl⟩ : syracuseStep 2971397 = 557137) (by norm_num)
theorem B1980931 : Blo 1979435 1980931 := bstep (se 1 (by rfl) ⟨1485698, by rfl⟩ : syracuseStep 1980931 = 2971397) B2971397
theorem B3342829 : Blo 1979435 3342829 := bbase (se 3 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 3342829 = 1253561) (by norm_num)
theorem B4457105 : Blo 1979435 4457105 := bstep (se 2 (by rfl) ⟨1671414, by rfl⟩ : syracuseStep 4457105 = 3342829) B3342829
theorem B2971403 : Blo 1979435 2971403 := bstep (se 1 (by rfl) ⟨2228552, by rfl⟩ : syracuseStep 2971403 = 4457105) B4457105
theorem B1980935 : Blo 1979435 1980935 := bstep (se 1 (by rfl) ⟨1485701, by rfl⟩ : syracuseStep 1980935 = 2971403) B2971403
theorem B2228557 : Blo 1979435 2228557 := bbase (se 3 (by rfl) ⟨417854, by rfl⟩ : syracuseStep 2228557 = 835709) (by norm_num)
theorem B2971409 : Blo 1979435 2971409 := bstep (se 2 (by rfl) ⟨1114278, by rfl⟩ : syracuseStep 2971409 = 2228557) B2228557
theorem B1980939 : Blo 1979435 1980939 := bstep (se 1 (by rfl) ⟨1485704, by rfl⟩ : syracuseStep 1980939 = 2971409) B2971409
theorem B6685685 : Blo 1979435 6685685 := bbase (se 5 (by rfl) ⟨313391, by rfl⟩ : syracuseStep 6685685 = 626783) (by norm_num)
theorem B4457123 : Blo 1979435 4457123 := bstep (se 1 (by rfl) ⟨3342842, by rfl⟩ : syracuseStep 4457123 = 6685685) B6685685
theorem B2971415 : Blo 1979435 2971415 := bstep (se 1 (by rfl) ⟨2228561, by rfl⟩ : syracuseStep 2971415 = 4457123) B4457123
theorem B1980943 : Blo 1979435 1980943 := bstep (se 1 (by rfl) ⟨1485707, by rfl⟩ : syracuseStep 1980943 = 2971415) B2971415
theorem B2971421 : Blo 1979435 2971421 := bbase (se 3 (by rfl) ⟨557141, by rfl⟩ : syracuseStep 2971421 = 1114283) (by norm_num)
theorem B1980947 : Blo 1979435 1980947 := bstep (se 1 (by rfl) ⟨1485710, by rfl⟩ : syracuseStep 1980947 = 2971421) B2971421
theorem B4457141 : Blo 1979435 4457141 := bbase (se 5 (by rfl) ⟨208928, by rfl⟩ : syracuseStep 4457141 = 417857) (by norm_num)
theorem B2971427 : Blo 1979435 2971427 := bstep (se 1 (by rfl) ⟨2228570, by rfl⟩ : syracuseStep 2971427 = 4457141) B4457141
theorem B1980951 : Blo 1979435 1980951 := bstep (se 1 (by rfl) ⟨1485713, by rfl⟩ : syracuseStep 1980951 = 2971427) B2971427
theorem B11282165 : Blo 1979435 11282165 := bbase (se 5 (by rfl) ⟨528851, by rfl⟩ : syracuseStep 11282165 = 1057703) (by norm_num)
theorem B7521443 : Blo 1979435 7521443 := bstep (se 1 (by rfl) ⟨5641082, by rfl⟩ : syracuseStep 7521443 = 11282165) B11282165
theorem B5014295 : Blo 1979435 5014295 := bstep (se 1 (by rfl) ⟨3760721, by rfl⟩ : syracuseStep 5014295 = 7521443) B7521443
theorem B3342863 : Blo 1979435 3342863 := bstep (se 1 (by rfl) ⟨2507147, by rfl⟩ : syracuseStep 3342863 = 5014295) B5014295
theorem B2228575 : Blo 1979435 2228575 := bstep (se 1 (by rfl) ⟨1671431, by rfl⟩ : syracuseStep 2228575 = 3342863) B3342863
theorem B2971433 : Blo 1979435 2971433 := bstep (se 2 (by rfl) ⟨1114287, by rfl⟩ : syracuseStep 2971433 = 2228575) B2228575
theorem B1980955 : Blo 1979435 1980955 := bstep (se 1 (by rfl) ⟨1485716, by rfl⟩ : syracuseStep 1980955 = 2971433) B2971433
theorem B5641093 : Blo 1979435 5641093 := bbase (se 4 (by rfl) ⟨528852, by rfl⟩ : syracuseStep 5641093 = 1057705) (by norm_num)
theorem B7521457 : Blo 1979435 7521457 := bstep (se 2 (by rfl) ⟨2820546, by rfl⟩ : syracuseStep 7521457 = 5641093) B5641093
theorem B10028609 : Blo 1979435 10028609 := bstep (se 2 (by rfl) ⟨3760728, by rfl⟩ : syracuseStep 10028609 = 7521457) B7521457
theorem B6685739 : Blo 1979435 6685739 := bstep (se 1 (by rfl) ⟨5014304, by rfl⟩ : syracuseStep 6685739 = 10028609) B10028609
theorem B4457159 : Blo 1979435 4457159 := bstep (se 1 (by rfl) ⟨3342869, by rfl⟩ : syracuseStep 4457159 = 6685739) B6685739
theorem B2971439 : Blo 1979435 2971439 := bstep (se 1 (by rfl) ⟨2228579, by rfl⟩ : syracuseStep 2971439 = 4457159) B4457159
theorem B1980959 : Blo 1979435 1980959 := bstep (se 1 (by rfl) ⟨1485719, by rfl⟩ : syracuseStep 1980959 = 2971439) B2971439
theorem B2971445 : Blo 1979435 2971445 := bbase (se 5 (by rfl) ⟨139286, by rfl⟩ : syracuseStep 2971445 = 278573) (by norm_num)
theorem B1980963 : Blo 1979435 1980963 := bstep (se 1 (by rfl) ⟨1485722, by rfl⟩ : syracuseStep 1980963 = 2971445) B2971445
theorem B5014325 : Blo 1979435 5014325 := bbase (se 5 (by rfl) ⟨235046, by rfl⟩ : syracuseStep 5014325 = 470093) (by norm_num)
theorem B3342883 : Blo 1979435 3342883 := bstep (se 1 (by rfl) ⟨2507162, by rfl⟩ : syracuseStep 3342883 = 5014325) B5014325
theorem B4457177 : Blo 1979435 4457177 := bstep (se 2 (by rfl) ⟨1671441, by rfl⟩ : syracuseStep 4457177 = 3342883) B3342883
theorem B2971451 : Blo 1979435 2971451 := bstep (se 1 (by rfl) ⟨2228588, by rfl⟩ : syracuseStep 2971451 = 4457177) B4457177
theorem B1980967 : Blo 1979435 1980967 := bstep (se 1 (by rfl) ⟨1485725, by rfl⟩ : syracuseStep 1980967 = 2971451) B2971451
theorem B2228593 : Blo 1979435 2228593 := bbase (se 2 (by rfl) ⟨835722, by rfl⟩ : syracuseStep 2228593 = 1671445) (by norm_num)
theorem B2971457 : Blo 1979435 2971457 := bstep (se 2 (by rfl) ⟨1114296, by rfl⟩ : syracuseStep 2971457 = 2228593) B2228593
theorem B1980971 : Blo 1979435 1980971 := bstep (se 1 (by rfl) ⟨1485728, by rfl⟩ : syracuseStep 1980971 = 2971457) B2971457
theorem B3173141 : Blo 1979435 3173141 := bbase (se 6 (by rfl) ⟨74370, by rfl⟩ : syracuseStep 3173141 = 148741) (by norm_num)
theorem B8461709 : Blo 1979435 8461709 := bstep (se 3 (by rfl) ⟨1586570, by rfl⟩ : syracuseStep 8461709 = 3173141) B3173141
theorem B5641139 : Blo 1979435 5641139 := bstep (se 1 (by rfl) ⟨4230854, by rfl⟩ : syracuseStep 5641139 = 8461709) B8461709
theorem B3760759 : Blo 1979435 3760759 := bstep (se 1 (by rfl) ⟨2820569, by rfl⟩ : syracuseStep 3760759 = 5641139) B5641139
theorem B5014345 : Blo 1979435 5014345 := bstep (se 2 (by rfl) ⟨1880379, by rfl⟩ : syracuseStep 5014345 = 3760759) B3760759
theorem B6685793 : Blo 1979435 6685793 := bstep (se 2 (by rfl) ⟨2507172, by rfl⟩ : syracuseStep 6685793 = 5014345) B5014345
theorem B4457195 : Blo 1979435 4457195 := bstep (se 1 (by rfl) ⟨3342896, by rfl⟩ : syracuseStep 4457195 = 6685793) B6685793
theorem B2971463 : Blo 1979435 2971463 := bstep (se 1 (by rfl) ⟨2228597, by rfl⟩ : syracuseStep 2971463 = 4457195) B4457195
theorem B1980975 : Blo 1979435 1980975 := bstep (se 1 (by rfl) ⟨1485731, by rfl⟩ : syracuseStep 1980975 = 2971463) B2971463
theorem B2971469 : Blo 1979435 2971469 := bbase (se 3 (by rfl) ⟨557150, by rfl⟩ : syracuseStep 2971469 = 1114301) (by norm_num)
theorem B1980979 : Blo 1979435 1980979 := bstep (se 1 (by rfl) ⟨1485734, by rfl⟩ : syracuseStep 1980979 = 2971469) B2971469
theorem B4457213 : Blo 1979435 4457213 := bbase (se 3 (by rfl) ⟨835727, by rfl⟩ : syracuseStep 4457213 = 1671455) (by norm_num)
theorem B2971475 : Blo 1979435 2971475 := bstep (se 1 (by rfl) ⟨2228606, by rfl⟩ : syracuseStep 2971475 = 4457213) B4457213
theorem B1980983 : Blo 1979435 1980983 := bstep (se 1 (by rfl) ⟨1485737, by rfl⟩ : syracuseStep 1980983 = 2971475) B2971475
theorem B3342917 : Blo 1979435 3342917 := bbase (se 4 (by rfl) ⟨313398, by rfl⟩ : syracuseStep 3342917 = 626797) (by norm_num)
theorem B2228611 : Blo 1979435 2228611 := bstep (se 1 (by rfl) ⟨1671458, by rfl⟩ : syracuseStep 2228611 = 3342917) B3342917
theorem B2971481 : Blo 1979435 2971481 := bstep (se 2 (by rfl) ⟨1114305, by rfl⟩ : syracuseStep 2971481 = 2228611) B2228611
theorem B1980987 : Blo 1979435 1980987 := bstep (se 1 (by rfl) ⟨1485740, by rfl⟩ : syracuseStep 1980987 = 2971481) B2971481
theorem B15043157 : Blo 1979435 15043157 := bbase (se 8 (by rfl) ⟨88143, by rfl⟩ : syracuseStep 15043157 = 176287) (by norm_num)
theorem B10028771 : Blo 1979435 10028771 := bstep (se 1 (by rfl) ⟨7521578, by rfl⟩ : syracuseStep 10028771 = 15043157) B15043157
theorem B6685847 : Blo 1979435 6685847 := bstep (se 1 (by rfl) ⟨5014385, by rfl⟩ : syracuseStep 6685847 = 10028771) B10028771
theorem B4457231 : Blo 1979435 4457231 := bstep (se 1 (by rfl) ⟨3342923, by rfl⟩ : syracuseStep 4457231 = 6685847) B6685847
theorem B2971487 : Blo 1979435 2971487 := bstep (se 1 (by rfl) ⟨2228615, by rfl⟩ : syracuseStep 2971487 = 4457231) B4457231
theorem B1980991 : Blo 1979435 1980991 := bstep (se 1 (by rfl) ⟨1485743, by rfl⟩ : syracuseStep 1980991 = 2971487) B2971487
theorem B2971493 : Blo 1979435 2971493 := bbase (se 4 (by rfl) ⟨278577, by rfl⟩ : syracuseStep 2971493 = 557155) (by norm_num)
theorem B1980995 : Blo 1979435 1980995 := bstep (se 1 (by rfl) ⟨1485746, by rfl⟩ : syracuseStep 1980995 = 2971493) B2971493
theorem B3760805 : Blo 1979435 3760805 := bbase (se 4 (by rfl) ⟨352575, by rfl⟩ : syracuseStep 3760805 = 705151) (by norm_num)
theorem B2507203 : Blo 1979435 2507203 := bstep (se 1 (by rfl) ⟨1880402, by rfl⟩ : syracuseStep 2507203 = 3760805) B3760805
theorem B3342937 : Blo 1979435 3342937 := bstep (se 2 (by rfl) ⟨1253601, by rfl⟩ : syracuseStep 3342937 = 2507203) B2507203
theorem B4457249 : Blo 1979435 4457249 := bstep (se 2 (by rfl) ⟨1671468, by rfl⟩ : syracuseStep 4457249 = 3342937) B3342937
theorem B2971499 : Blo 1979435 2971499 := bstep (se 1 (by rfl) ⟨2228624, by rfl⟩ : syracuseStep 2971499 = 4457249) B4457249
theorem B1980999 : Blo 1979435 1980999 := bstep (se 1 (by rfl) ⟨1485749, by rfl⟩ : syracuseStep 1980999 = 2971499) B2971499
theorem B2228629 : Blo 1979435 2228629 := bbase (se 6 (by rfl) ⟨52233, by rfl⟩ : syracuseStep 2228629 = 104467) (by norm_num)
theorem B2971505 : Blo 1979435 2971505 := bstep (se 2 (by rfl) ⟨1114314, by rfl⟩ : syracuseStep 2971505 = 2228629) B2228629
theorem B1981003 : Blo 1979435 1981003 := bstep (se 1 (by rfl) ⟨1485752, by rfl⟩ : syracuseStep 1981003 = 2971505) B2971505
theorem B2507213 : Blo 1979435 2507213 := bbase (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) (by norm_num)
theorem B6685901 : Blo 1979435 6685901 := bstep (se 3 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 6685901 = 2507213) B2507213
theorem B4457267 : Blo 1979435 4457267 := bstep (se 1 (by rfl) ⟨3342950, by rfl⟩ : syracuseStep 4457267 = 6685901) B6685901
theorem B2971511 : Blo 1979435 2971511 := bstep (se 1 (by rfl) ⟨2228633, by rfl⟩ : syracuseStep 2971511 = 4457267) B4457267
theorem B1981007 : Blo 1979435 1981007 := bstep (se 1 (by rfl) ⟨1485755, by rfl⟩ : syracuseStep 1981007 = 2971511) B2971511
theorem B2971517 : Blo 1979435 2971517 := bbase (se 3 (by rfl) ⟨557159, by rfl⟩ : syracuseStep 2971517 = 1114319) (by norm_num)
theorem B1981011 : Blo 1979435 1981011 := bstep (se 1 (by rfl) ⟨1485758, by rfl⟩ : syracuseStep 1981011 = 2971517) B2971517
theorem B4457285 : Blo 1979435 4457285 := bbase (se 4 (by rfl) ⟨417870, by rfl⟩ : syracuseStep 4457285 = 835741) (by norm_num)
theorem B2971523 : Blo 1979435 2971523 := bstep (se 1 (by rfl) ⟨2228642, by rfl⟩ : syracuseStep 2971523 = 4457285) B4457285
theorem B1981015 : Blo 1979435 1981015 := bstep (se 1 (by rfl) ⟨1485761, by rfl⟩ : syracuseStep 1981015 = 2971523) B2971523
theorem B4230949 : Blo 1979435 4230949 := bbase (se 4 (by rfl) ⟨396651, by rfl⟩ : syracuseStep 4230949 = 793303) (by norm_num)
theorem B5641265 : Blo 1979435 5641265 := bstep (se 2 (by rfl) ⟨2115474, by rfl⟩ : syracuseStep 5641265 = 4230949) B4230949
theorem B3760843 : Blo 1979435 3760843 := bstep (se 1 (by rfl) ⟨2820632, by rfl⟩ : syracuseStep 3760843 = 5641265) B5641265
theorem B5014457 : Blo 1979435 5014457 := bstep (se 2 (by rfl) ⟨1880421, by rfl⟩ : syracuseStep 5014457 = 3760843) B3760843
theorem B3342971 : Blo 1979435 3342971 := bstep (se 1 (by rfl) ⟨2507228, by rfl⟩ : syracuseStep 3342971 = 5014457) B5014457
theorem B2228647 : Blo 1979435 2228647 := bstep (se 1 (by rfl) ⟨1671485, by rfl⟩ : syracuseStep 2228647 = 3342971) B3342971
theorem B2971529 : Blo 1979435 2971529 := bstep (se 2 (by rfl) ⟨1114323, by rfl⟩ : syracuseStep 2971529 = 2228647) B2228647
theorem B1981019 : Blo 1979435 1981019 := bstep (se 1 (by rfl) ⟨1485764, by rfl⟩ : syracuseStep 1981019 = 2971529) B2971529
theorem B10028933 : Blo 1979435 10028933 := bbase (se 4 (by rfl) ⟨940212, by rfl⟩ : syracuseStep 10028933 = 1880425) (by norm_num)
theorem B6685955 : Blo 1979435 6685955 := bstep (se 1 (by rfl) ⟨5014466, by rfl⟩ : syracuseStep 6685955 = 10028933) B10028933
theorem B4457303 : Blo 1979435 4457303 := bstep (se 1 (by rfl) ⟨3342977, by rfl⟩ : syracuseStep 4457303 = 6685955) B6685955
theorem B2971535 : Blo 1979435 2971535 := bstep (se 1 (by rfl) ⟨2228651, by rfl⟩ : syracuseStep 2971535 = 4457303) B4457303
theorem B1981023 : Blo 1979435 1981023 := bstep (se 1 (by rfl) ⟨1485767, by rfl⟩ : syracuseStep 1981023 = 2971535) B2971535
theorem B2971541 : Blo 1979435 2971541 := bbase (se 6 (by rfl) ⟨69645, by rfl⟩ : syracuseStep 2971541 = 139291) (by norm_num)
theorem B1981027 : Blo 1979435 1981027 := bstep (se 1 (by rfl) ⟨1485770, by rfl⟩ : syracuseStep 1981027 = 2971541) B2971541
theorem B3053189 : Blo 1979435 3053189 := bbase (se 4 (by rfl) ⟨286236, by rfl⟩ : syracuseStep 3053189 = 572473) (by norm_num)
theorem B2035459 : Blo 1979435 2035459 := bstep (se 1 (by rfl) ⟨1526594, by rfl⟩ : syracuseStep 2035459 = 3053189) B3053189
theorem B10855781 : Blo 1979435 10855781 := bstep (se 4 (by rfl) ⟨1017729, by rfl⟩ : syracuseStep 10855781 = 2035459) B2035459
theorem B7237187 : Blo 1979435 7237187 := bstep (se 1 (by rfl) ⟨5427890, by rfl⟩ : syracuseStep 7237187 = 10855781) B10855781
theorem B4824791 : Blo 1979435 4824791 := bstep (se 1 (by rfl) ⟨3618593, by rfl⟩ : syracuseStep 4824791 = 7237187) B7237187
theorem B3216527 : Blo 1979435 3216527 := bstep (se 1 (by rfl) ⟨2412395, by rfl⟩ : syracuseStep 3216527 = 4824791) B4824791
theorem B2144351 : Blo 1979435 2144351 := bstep (se 1 (by rfl) ⟨1608263, by rfl⟩ : syracuseStep 2144351 = 3216527) B3216527
theorem B5718269 : Blo 1979435 5718269 := bstep (se 3 (by rfl) ⟨1072175, by rfl⟩ : syracuseStep 5718269 = 2144351) B2144351
theorem B3812179 : Blo 1979435 3812179 := bstep (se 1 (by rfl) ⟨2859134, by rfl⟩ : syracuseStep 3812179 = 5718269) B5718269
theorem B5082905 : Blo 1979435 5082905 := bstep (se 2 (by rfl) ⟨1906089, by rfl⟩ : syracuseStep 5082905 = 3812179) B3812179
theorem B3388603 : Blo 1979435 3388603 := bstep (se 1 (by rfl) ⟨2541452, by rfl⟩ : syracuseStep 3388603 = 5082905) B5082905
theorem B4518137 : Blo 1979435 4518137 := bstep (se 2 (by rfl) ⟨1694301, by rfl⟩ : syracuseStep 4518137 = 3388603) B3388603
theorem B12048365 : Blo 1979435 12048365 := bstep (se 3 (by rfl) ⟨2259068, by rfl⟩ : syracuseStep 12048365 = 4518137) B4518137
theorem B8032243 : Blo 1979435 8032243 := bstep (se 1 (by rfl) ⟨6024182, by rfl⟩ : syracuseStep 8032243 = 12048365) B12048365
theorem B10709657 : Blo 1979435 10709657 := bstep (se 2 (by rfl) ⟨4016121, by rfl⟩ : syracuseStep 10709657 = 8032243) B8032243
theorem B7139771 : Blo 1979435 7139771 := bstep (se 1 (by rfl) ⟨5354828, by rfl⟩ : syracuseStep 7139771 = 10709657) B10709657
theorem B4759847 : Blo 1979435 4759847 := bstep (se 1 (by rfl) ⟨3569885, by rfl⟩ : syracuseStep 4759847 = 7139771) B7139771
theorem B3173231 : Blo 1979435 3173231 := bstep (se 1 (by rfl) ⟨2379923, by rfl⟩ : syracuseStep 3173231 = 4759847) B4759847
theorem B2115487 : Blo 1979435 2115487 := bstep (se 1 (by rfl) ⟨1586615, by rfl⟩ : syracuseStep 2115487 = 3173231) B3173231
theorem B11282597 : Blo 1979435 11282597 := bstep (se 4 (by rfl) ⟨1057743, by rfl⟩ : syracuseStep 11282597 = 2115487) B2115487
theorem B7521731 : Blo 1979435 7521731 := bstep (se 1 (by rfl) ⟨5641298, by rfl⟩ : syracuseStep 7521731 = 11282597) B11282597
theorem B5014487 : Blo 1979435 5014487 := bstep (se 1 (by rfl) ⟨3760865, by rfl⟩ : syracuseStep 5014487 = 7521731) B7521731
theorem B3342991 : Blo 1979435 3342991 := bstep (se 1 (by rfl) ⟨2507243, by rfl⟩ : syracuseStep 3342991 = 5014487) B5014487
theorem B4457321 : Blo 1979435 4457321 := bstep (se 2 (by rfl) ⟨1671495, by rfl⟩ : syracuseStep 4457321 = 3342991) B3342991
theorem B2971547 : Blo 1979435 2971547 := bstep (se 1 (by rfl) ⟨2228660, by rfl⟩ : syracuseStep 2971547 = 4457321) B4457321
theorem B1981031 : Blo 1979435 1981031 := bstep (se 1 (by rfl) ⟨1485773, by rfl⟩ : syracuseStep 1981031 = 2971547) B2971547
theorem B2228665 : Blo 1979435 2228665 := bbase (se 2 (by rfl) ⟨835749, by rfl⟩ : syracuseStep 2228665 = 1671499) (by norm_num)
theorem B2971553 : Blo 1979435 2971553 := bstep (se 2 (by rfl) ⟨1114332, by rfl⟩ : syracuseStep 2971553 = 2228665) B2228665
theorem B1981035 : Blo 1979435 1981035 := bstep (se 1 (by rfl) ⟨1485776, by rfl⟩ : syracuseStep 1981035 = 2971553) B2971553
theorem B5082925 : Blo 1979435 5082925 := bbase (se 3 (by rfl) ⟨953048, by rfl⟩ : syracuseStep 5082925 = 1906097) (by norm_num)
theorem B6777233 : Blo 1979435 6777233 := bstep (se 2 (by rfl) ⟨2541462, by rfl⟩ : syracuseStep 6777233 = 5082925) B5082925
theorem B4518155 : Blo 1979435 4518155 := bstep (se 1 (by rfl) ⟨3388616, by rfl⟩ : syracuseStep 4518155 = 6777233) B6777233
theorem B3012103 : Blo 1979435 3012103 := bstep (se 1 (by rfl) ⟨2259077, by rfl⟩ : syracuseStep 3012103 = 4518155) B4518155
theorem B4016137 : Blo 1979435 4016137 := bstep (se 2 (by rfl) ⟨1506051, by rfl⟩ : syracuseStep 4016137 = 3012103) B3012103
theorem B5354849 : Blo 1979435 5354849 := bstep (se 2 (by rfl) ⟨2008068, by rfl⟩ : syracuseStep 5354849 = 4016137) B4016137
theorem B14279597 : Blo 1979435 14279597 := bstep (se 3 (by rfl) ⟨2677424, by rfl⟩ : syracuseStep 14279597 = 5354849) B5354849
theorem B9519731 : Blo 1979435 9519731 := bstep (se 1 (by rfl) ⟨7139798, by rfl⟩ : syracuseStep 9519731 = 14279597) B14279597
theorem B6346487 : Blo 1979435 6346487 := bstep (se 1 (by rfl) ⟨4759865, by rfl⟩ : syracuseStep 6346487 = 9519731) B9519731
theorem B4230991 : Blo 1979435 4230991 := bstep (se 1 (by rfl) ⟨3173243, by rfl⟩ : syracuseStep 4230991 = 6346487) B6346487
theorem B5641321 : Blo 1979435 5641321 := bstep (se 2 (by rfl) ⟨2115495, by rfl⟩ : syracuseStep 5641321 = 4230991) B4230991
theorem B7521761 : Blo 1979435 7521761 := bstep (se 2 (by rfl) ⟨2820660, by rfl⟩ : syracuseStep 7521761 = 5641321) B5641321
theorem B5014507 : Blo 1979435 5014507 := bstep (se 1 (by rfl) ⟨3760880, by rfl⟩ : syracuseStep 5014507 = 7521761) B7521761
theorem B6686009 : Blo 1979435 6686009 := bstep (se 2 (by rfl) ⟨2507253, by rfl⟩ : syracuseStep 6686009 = 5014507) B5014507
theorem B4457339 : Blo 1979435 4457339 := bstep (se 1 (by rfl) ⟨3343004, by rfl⟩ : syracuseStep 4457339 = 6686009) B6686009
theorem B2971559 : Blo 1979435 2971559 := bstep (se 1 (by rfl) ⟨2228669, by rfl⟩ : syracuseStep 2971559 = 4457339) B4457339
theorem B1981039 : Blo 1979435 1981039 := bstep (se 1 (by rfl) ⟨1485779, by rfl⟩ : syracuseStep 1981039 = 2971559) B2971559
theorem B2971565 : Blo 1979435 2971565 := bbase (se 3 (by rfl) ⟨557168, by rfl⟩ : syracuseStep 2971565 = 1114337) (by norm_num)
theorem B1981043 : Blo 1979435 1981043 := bstep (se 1 (by rfl) ⟨1485782, by rfl⟩ : syracuseStep 1981043 = 2971565) B2971565
theorem B4457357 : Blo 1979435 4457357 := bbase (se 3 (by rfl) ⟨835754, by rfl⟩ : syracuseStep 4457357 = 1671509) (by norm_num)
theorem B2971571 : Blo 1979435 2971571 := bstep (se 1 (by rfl) ⟨2228678, by rfl⟩ : syracuseStep 2971571 = 4457357) B4457357
theorem B1981047 : Blo 1979435 1981047 := bstep (se 1 (by rfl) ⟨1485785, by rfl⟩ : syracuseStep 1981047 = 2971571) B2971571
theorem B2507269 : Blo 1979435 2507269 := bbase (se 4 (by rfl) ⟨235056, by rfl⟩ : syracuseStep 2507269 = 470113) (by norm_num)
theorem B3343025 : Blo 1979435 3343025 := bstep (se 2 (by rfl) ⟨1253634, by rfl⟩ : syracuseStep 3343025 = 2507269) B2507269
theorem B2228683 : Blo 1979435 2228683 := bstep (se 1 (by rfl) ⟨1671512, by rfl⟩ : syracuseStep 2228683 = 3343025) B3343025
theorem B2971577 : Blo 1979435 2971577 := bstep (se 2 (by rfl) ⟨1114341, by rfl⟩ : syracuseStep 2971577 = 2228683) B2228683
theorem B1981051 : Blo 1979435 1981051 := bstep (se 1 (by rfl) ⟨1485788, by rfl⟩ : syracuseStep 1981051 = 2971577) B2971577
theorem B5082965 : Blo 1979435 5082965 := bbase (se 9 (by rfl) ⟨14891, by rfl⟩ : syracuseStep 5082965 = 29783) (by norm_num)
theorem B3388643 : Blo 1979435 3388643 := bstep (se 1 (by rfl) ⟨2541482, by rfl⟩ : syracuseStep 3388643 = 5082965) B5082965
theorem B2259095 : Blo 1979435 2259095 := bstep (se 1 (by rfl) ⟨1694321, by rfl⟩ : syracuseStep 2259095 = 3388643) B3388643
theorem B24097013 : Blo 1979435 24097013 := bstep (se 5 (by rfl) ⟨1129547, by rfl⟩ : syracuseStep 24097013 = 2259095) B2259095
theorem B16064675 : Blo 1979435 16064675 := bstep (se 1 (by rfl) ⟨12048506, by rfl⟩ : syracuseStep 16064675 = 24097013) B24097013
theorem B10709783 : Blo 1979435 10709783 := bstep (se 1 (by rfl) ⟨8032337, by rfl⟩ : syracuseStep 10709783 = 16064675) B16064675
theorem B7139855 : Blo 1979435 7139855 := bstep (se 1 (by rfl) ⟨5354891, by rfl⟩ : syracuseStep 7139855 = 10709783) B10709783
theorem B4759903 : Blo 1979435 4759903 := bstep (se 1 (by rfl) ⟨3569927, by rfl⟩ : syracuseStep 4759903 = 7139855) B7139855
theorem B25386149 : Blo 1979435 25386149 := bstep (se 4 (by rfl) ⟨2379951, by rfl⟩ : syracuseStep 25386149 = 4759903) B4759903
theorem B16924099 : Blo 1979435 16924099 := bstep (se 1 (by rfl) ⟨12693074, by rfl⟩ : syracuseStep 16924099 = 25386149) B25386149
theorem B22565465 : Blo 1979435 22565465 := bstep (se 2 (by rfl) ⟨8462049, by rfl⟩ : syracuseStep 22565465 = 16924099) B16924099
theorem B15043643 : Blo 1979435 15043643 := bstep (se 1 (by rfl) ⟨11282732, by rfl⟩ : syracuseStep 15043643 = 22565465) B22565465
theorem B10029095 : Blo 1979435 10029095 := bstep (se 1 (by rfl) ⟨7521821, by rfl⟩ : syracuseStep 10029095 = 15043643) B15043643
theorem B6686063 : Blo 1979435 6686063 := bstep (se 1 (by rfl) ⟨5014547, by rfl⟩ : syracuseStep 6686063 = 10029095) B10029095
theorem B4457375 : Blo 1979435 4457375 := bstep (se 1 (by rfl) ⟨3343031, by rfl⟩ : syracuseStep 4457375 = 6686063) B6686063
theorem B2971583 : Blo 1979435 2971583 := bstep (se 1 (by rfl) ⟨2228687, by rfl⟩ : syracuseStep 2971583 = 4457375) B4457375
theorem B1981055 : Blo 1979435 1981055 := bstep (se 1 (by rfl) ⟨1485791, by rfl⟩ : syracuseStep 1981055 = 2971583) B2971583
theorem B2971589 : Blo 1979435 2971589 := bbase (se 4 (by rfl) ⟨278586, by rfl⟩ : syracuseStep 2971589 = 557173) (by norm_num)
theorem B1981059 : Blo 1979435 1981059 := bstep (se 1 (by rfl) ⟨1485794, by rfl⟩ : syracuseStep 1981059 = 2971589) B2971589
theorem B3343045 : Blo 1979435 3343045 := bbase (se 4 (by rfl) ⟨313410, by rfl⟩ : syracuseStep 3343045 = 626821) (by norm_num)
theorem B4457393 : Blo 1979435 4457393 := bstep (se 2 (by rfl) ⟨1671522, by rfl⟩ : syracuseStep 4457393 = 3343045) B3343045
theorem B2971595 : Blo 1979435 2971595 := bstep (se 1 (by rfl) ⟨2228696, by rfl⟩ : syracuseStep 2971595 = 4457393) B4457393
theorem B1981063 : Blo 1979435 1981063 := bstep (se 1 (by rfl) ⟨1485797, by rfl⟩ : syracuseStep 1981063 = 2971595) B2971595
theorem B2228701 : Blo 1979435 2228701 := bbase (se 3 (by rfl) ⟨417881, by rfl⟩ : syracuseStep 2228701 = 835763) (by norm_num)
theorem B2971601 : Blo 1979435 2971601 := bstep (se 2 (by rfl) ⟨1114350, by rfl⟩ : syracuseStep 2971601 = 2228701) B2228701
theorem B1981067 : Blo 1979435 1981067 := bstep (se 1 (by rfl) ⟨1485800, by rfl⟩ : syracuseStep 1981067 = 2971601) B2971601
theorem B6686117 : Blo 1979435 6686117 := bbase (se 4 (by rfl) ⟨626823, by rfl⟩ : syracuseStep 6686117 = 1253647) (by norm_num)
theorem B4457411 : Blo 1979435 4457411 := bstep (se 1 (by rfl) ⟨3343058, by rfl⟩ : syracuseStep 4457411 = 6686117) B6686117
theorem B2971607 : Blo 1979435 2971607 := bstep (se 1 (by rfl) ⟨2228705, by rfl⟩ : syracuseStep 2971607 = 4457411) B4457411
theorem B1981071 : Blo 1979435 1981071 := bstep (se 1 (by rfl) ⟨1485803, by rfl⟩ : syracuseStep 1981071 = 2971607) B2971607
theorem B2971613 : Blo 1979435 2971613 := bbase (se 3 (by rfl) ⟨557177, by rfl⟩ : syracuseStep 2971613 = 1114355) (by norm_num)
theorem B1981075 : Blo 1979435 1981075 := bstep (se 1 (by rfl) ⟨1485806, by rfl⟩ : syracuseStep 1981075 = 2971613) B2971613
theorem B4457429 : Blo 1979435 4457429 := bbase (se 7 (by rfl) ⟨52235, by rfl⟩ : syracuseStep 4457429 = 104471) (by norm_num)
theorem B2971619 : Blo 1979435 2971619 := bstep (se 1 (by rfl) ⟨2228714, by rfl⟩ : syracuseStep 2971619 = 4457429) B4457429
theorem B1981079 : Blo 1979435 1981079 := bstep (se 1 (by rfl) ⟨1485809, by rfl⟩ : syracuseStep 1981079 = 2971619) B2971619
theorem B9649829 : Blo 1979435 9649829 := bbase (se 4 (by rfl) ⟨904671, by rfl⟩ : syracuseStep 9649829 = 1809343) (by norm_num)
theorem B6433219 : Blo 1979435 6433219 := bstep (se 1 (by rfl) ⟨4824914, by rfl⟩ : syracuseStep 6433219 = 9649829) B9649829
theorem B8577625 : Blo 1979435 8577625 := bstep (se 2 (by rfl) ⟨3216609, by rfl⟩ : syracuseStep 8577625 = 6433219) B6433219
theorem B11436833 : Blo 1979435 11436833 := bstep (se 2 (by rfl) ⟨4288812, by rfl⟩ : syracuseStep 11436833 = 8577625) B8577625
theorem B30498221 : Blo 1979435 30498221 := bstep (se 3 (by rfl) ⟨5718416, by rfl⟩ : syracuseStep 30498221 = 11436833) B11436833
theorem B20332147 : Blo 1979435 20332147 := bstep (se 1 (by rfl) ⟨15249110, by rfl⟩ : syracuseStep 20332147 = 30498221) B30498221
theorem B27109529 : Blo 1979435 27109529 := bstep (se 2 (by rfl) ⟨10166073, by rfl⟩ : syracuseStep 27109529 = 20332147) B20332147
theorem B18073019 : Blo 1979435 18073019 := bstep (se 1 (by rfl) ⟨13554764, by rfl⟩ : syracuseStep 18073019 = 27109529) B27109529
theorem B12048679 : Blo 1979435 12048679 := bstep (se 1 (by rfl) ⟨9036509, by rfl⟩ : syracuseStep 12048679 = 18073019) B18073019
theorem B16064905 : Blo 1979435 16064905 := bstep (se 2 (by rfl) ⟨6024339, by rfl⟩ : syracuseStep 16064905 = 12048679) B12048679
theorem B21419873 : Blo 1979435 21419873 := bstep (se 2 (by rfl) ⟨8032452, by rfl⟩ : syracuseStep 21419873 = 16064905) B16064905
theorem B14279915 : Blo 1979435 14279915 := bstep (se 1 (by rfl) ⟨10709936, by rfl⟩ : syracuseStep 14279915 = 21419873) B21419873
theorem B9519943 : Blo 1979435 9519943 := bstep (se 1 (by rfl) ⟨7139957, by rfl⟩ : syracuseStep 9519943 = 14279915) B14279915
theorem B12693257 : Blo 1979435 12693257 := bstep (se 2 (by rfl) ⟨4759971, by rfl⟩ : syracuseStep 12693257 = 9519943) B9519943
theorem B8462171 : Blo 1979435 8462171 := bstep (se 1 (by rfl) ⟨6346628, by rfl⟩ : syracuseStep 8462171 = 12693257) B12693257
theorem B5641447 : Blo 1979435 5641447 := bstep (se 1 (by rfl) ⟨4231085, by rfl⟩ : syracuseStep 5641447 = 8462171) B8462171
theorem B7521929 : Blo 1979435 7521929 := bstep (se 2 (by rfl) ⟨2820723, by rfl⟩ : syracuseStep 7521929 = 5641447) B5641447
theorem B5014619 : Blo 1979435 5014619 := bstep (se 1 (by rfl) ⟨3760964, by rfl⟩ : syracuseStep 5014619 = 7521929) B7521929
theorem B3343079 : Blo 1979435 3343079 := bstep (se 1 (by rfl) ⟨2507309, by rfl⟩ : syracuseStep 3343079 = 5014619) B5014619
theorem B2228719 : Blo 1979435 2228719 := bstep (se 1 (by rfl) ⟨1671539, by rfl⟩ : syracuseStep 2228719 = 3343079) B3343079
theorem B2971625 : Blo 1979435 2971625 := bstep (se 2 (by rfl) ⟨1114359, by rfl⟩ : syracuseStep 2971625 = 2228719) B2228719
theorem B1981083 : Blo 1979435 1981083 := bstep (se 1 (by rfl) ⟨1485812, by rfl⟩ : syracuseStep 1981083 = 2971625) B2971625
theorem B16924373 : Blo 1979435 16924373 := bbase (se 7 (by rfl) ⟨198332, by rfl⟩ : syracuseStep 16924373 = 396665) (by norm_num)
theorem B11282915 : Blo 1979435 11282915 := bstep (se 1 (by rfl) ⟨8462186, by rfl⟩ : syracuseStep 11282915 = 16924373) B16924373
theorem B7521943 : Blo 1979435 7521943 := bstep (se 1 (by rfl) ⟨5641457, by rfl⟩ : syracuseStep 7521943 = 11282915) B11282915
theorem B10029257 : Blo 1979435 10029257 := bstep (se 2 (by rfl) ⟨3760971, by rfl⟩ : syracuseStep 10029257 = 7521943) B7521943
theorem B6686171 : Blo 1979435 6686171 := bstep (se 1 (by rfl) ⟨5014628, by rfl⟩ : syracuseStep 6686171 = 10029257) B10029257
theorem B4457447 : Blo 1979435 4457447 := bstep (se 1 (by rfl) ⟨3343085, by rfl⟩ : syracuseStep 4457447 = 6686171) B6686171
theorem B2971631 : Blo 1979435 2971631 := bstep (se 1 (by rfl) ⟨2228723, by rfl⟩ : syracuseStep 2971631 = 4457447) B4457447
theorem B1981087 : Blo 1979435 1981087 := bstep (se 1 (by rfl) ⟨1485815, by rfl⟩ : syracuseStep 1981087 = 2971631) B2971631
theorem B2971637 : Blo 1979435 2971637 := bbase (se 5 (by rfl) ⟨139295, by rfl⟩ : syracuseStep 2971637 = 278591) (by norm_num)
theorem B1981091 : Blo 1979435 1981091 := bstep (se 1 (by rfl) ⟨1485818, by rfl⟩ : syracuseStep 1981091 = 2971637) B2971637
theorem B5083069 : Blo 1979435 5083069 := bbase (se 3 (by rfl) ⟨953075, by rfl⟩ : syracuseStep 5083069 = 1906151) (by norm_num)
theorem B6777425 : Blo 1979435 6777425 := bstep (se 2 (by rfl) ⟨2541534, by rfl⟩ : syracuseStep 6777425 = 5083069) B5083069
theorem B4518283 : Blo 1979435 4518283 := bstep (se 1 (by rfl) ⟨3388712, by rfl⟩ : syracuseStep 4518283 = 6777425) B6777425
theorem B6024377 : Blo 1979435 6024377 := bstep (se 2 (by rfl) ⟨2259141, by rfl⟩ : syracuseStep 6024377 = 4518283) B4518283
theorem B4016251 : Blo 1979435 4016251 := bstep (se 1 (by rfl) ⟨3012188, by rfl⟩ : syracuseStep 4016251 = 6024377) B6024377
theorem B5355001 : Blo 1979435 5355001 := bstep (se 2 (by rfl) ⟨2008125, by rfl⟩ : syracuseStep 5355001 = 4016251) B4016251
theorem B7140001 : Blo 1979435 7140001 := bstep (se 2 (by rfl) ⟨2677500, by rfl⟩ : syracuseStep 7140001 = 5355001) B5355001
theorem B9520001 : Blo 1979435 9520001 := bstep (se 2 (by rfl) ⟨3570000, by rfl⟩ : syracuseStep 9520001 = 7140001) B7140001
theorem B6346667 : Blo 1979435 6346667 := bstep (se 1 (by rfl) ⟨4760000, by rfl⟩ : syracuseStep 6346667 = 9520001) B9520001
theorem B4231111 : Blo 1979435 4231111 := bstep (se 1 (by rfl) ⟨3173333, by rfl⟩ : syracuseStep 4231111 = 6346667) B6346667
theorem B5641481 : Blo 1979435 5641481 := bstep (se 2 (by rfl) ⟨2115555, by rfl⟩ : syracuseStep 5641481 = 4231111) B4231111
theorem B3760987 : Blo 1979435 3760987 := bstep (se 1 (by rfl) ⟨2820740, by rfl⟩ : syracuseStep 3760987 = 5641481) B5641481
theorem B5014649 : Blo 1979435 5014649 := bstep (se 2 (by rfl) ⟨1880493, by rfl⟩ : syracuseStep 5014649 = 3760987) B3760987
theorem B3343099 : Blo 1979435 3343099 := bstep (se 1 (by rfl) ⟨2507324, by rfl⟩ : syracuseStep 3343099 = 5014649) B5014649
theorem B4457465 : Blo 1979435 4457465 := bstep (se 2 (by rfl) ⟨1671549, by rfl⟩ : syracuseStep 4457465 = 3343099) B3343099
theorem B2971643 : Blo 1979435 2971643 := bstep (se 1 (by rfl) ⟨2228732, by rfl⟩ : syracuseStep 2971643 = 4457465) B4457465
theorem B1981095 : Blo 1979435 1981095 := bstep (se 1 (by rfl) ⟨1485821, by rfl⟩ : syracuseStep 1981095 = 2971643) B2971643
theorem B2228737 : Blo 1979435 2228737 := bbase (se 2 (by rfl) ⟨835776, by rfl⟩ : syracuseStep 2228737 = 1671553) (by norm_num)
theorem B2971649 : Blo 1979435 2971649 := bstep (se 2 (by rfl) ⟨1114368, by rfl⟩ : syracuseStep 2971649 = 2228737) B2228737
theorem B1981099 : Blo 1979435 1981099 := bstep (se 1 (by rfl) ⟨1485824, by rfl⟩ : syracuseStep 1981099 = 2971649) B2971649
theorem B5014669 : Blo 1979435 5014669 := bbase (se 3 (by rfl) ⟨940250, by rfl⟩ : syracuseStep 5014669 = 1880501) (by norm_num)
theorem B6686225 : Blo 1979435 6686225 := bstep (se 2 (by rfl) ⟨2507334, by rfl⟩ : syracuseStep 6686225 = 5014669) B5014669
theorem B4457483 : Blo 1979435 4457483 := bstep (se 1 (by rfl) ⟨3343112, by rfl⟩ : syracuseStep 4457483 = 6686225) B6686225
theorem B2971655 : Blo 1979435 2971655 := bstep (se 1 (by rfl) ⟨2228741, by rfl⟩ : syracuseStep 2971655 = 4457483) B4457483
theorem B1981103 : Blo 1979435 1981103 := bstep (se 1 (by rfl) ⟨1485827, by rfl⟩ : syracuseStep 1981103 = 2971655) B2971655
theorem B2971661 : Blo 1979435 2971661 := bbase (se 3 (by rfl) ⟨557186, by rfl⟩ : syracuseStep 2971661 = 1114373) (by norm_num)
theorem B1981107 : Blo 1979435 1981107 := bstep (se 1 (by rfl) ⟨1485830, by rfl⟩ : syracuseStep 1981107 = 2971661) B2971661
theorem B4457501 : Blo 1979435 4457501 := bbase (se 3 (by rfl) ⟨835781, by rfl⟩ : syracuseStep 4457501 = 1671563) (by norm_num)
theorem B2971667 : Blo 1979435 2971667 := bstep (se 1 (by rfl) ⟨2228750, by rfl⟩ : syracuseStep 2971667 = 4457501) B4457501
theorem B1981111 : Blo 1979435 1981111 := bstep (se 1 (by rfl) ⟨1485833, by rfl⟩ : syracuseStep 1981111 = 2971667) B2971667
theorem B3343133 : Blo 1979435 3343133 := bbase (se 3 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 3343133 = 1253675) (by norm_num)
theorem B2228755 : Blo 1979435 2228755 := bstep (se 1 (by rfl) ⟨1671566, by rfl⟩ : syracuseStep 2228755 = 3343133) B3343133
theorem B2971673 : Blo 1979435 2971673 := bstep (se 2 (by rfl) ⟨1114377, by rfl⟩ : syracuseStep 2971673 = 2228755) B2228755
theorem B1981115 : Blo 1979435 1981115 := bstep (se 1 (by rfl) ⟨1485836, by rfl⟩ : syracuseStep 1981115 = 2971673) B2971673
theorem B2541565 : Blo 1979435 2541565 := bbase (se 3 (by rfl) ⟨476543, by rfl⟩ : syracuseStep 2541565 = 953087) (by norm_num)
theorem B3388753 : Blo 1979435 3388753 := bstep (se 2 (by rfl) ⟨1270782, by rfl⟩ : syracuseStep 3388753 = 2541565) B2541565
theorem B4518337 : Blo 1979435 4518337 := bstep (se 2 (by rfl) ⟨1694376, by rfl⟩ : syracuseStep 4518337 = 3388753) B3388753
theorem B6024449 : Blo 1979435 6024449 := bstep (se 2 (by rfl) ⟨2259168, by rfl⟩ : syracuseStep 6024449 = 4518337) B4518337
theorem B4016299 : Blo 1979435 4016299 := bstep (se 1 (by rfl) ⟨3012224, by rfl⟩ : syracuseStep 4016299 = 6024449) B6024449
theorem B5355065 : Blo 1979435 5355065 := bstep (se 2 (by rfl) ⟨2008149, by rfl⟩ : syracuseStep 5355065 = 4016299) B4016299
theorem B3570043 : Blo 1979435 3570043 := bstep (se 1 (by rfl) ⟨2677532, by rfl⟩ : syracuseStep 3570043 = 5355065) B5355065
theorem B4760057 : Blo 1979435 4760057 := bstep (se 2 (by rfl) ⟨1785021, by rfl⟩ : syracuseStep 4760057 = 3570043) B3570043
theorem B12693485 : Blo 1979435 12693485 := bstep (se 3 (by rfl) ⟨2380028, by rfl⟩ : syracuseStep 12693485 = 4760057) B4760057
theorem B8462323 : Blo 1979435 8462323 := bstep (se 1 (by rfl) ⟨6346742, by rfl⟩ : syracuseStep 8462323 = 12693485) B12693485
theorem B11283097 : Blo 1979435 11283097 := bstep (se 2 (by rfl) ⟨4231161, by rfl⟩ : syracuseStep 11283097 = 8462323) B8462323
theorem B15044129 : Blo 1979435 15044129 := bstep (se 2 (by rfl) ⟨5641548, by rfl⟩ : syracuseStep 15044129 = 11283097) B11283097
theorem B10029419 : Blo 1979435 10029419 := bstep (se 1 (by rfl) ⟨7522064, by rfl⟩ : syracuseStep 10029419 = 15044129) B15044129
theorem B6686279 : Blo 1979435 6686279 := bstep (se 1 (by rfl) ⟨5014709, by rfl⟩ : syracuseStep 6686279 = 10029419) B10029419
theorem B4457519 : Blo 1979435 4457519 := bstep (se 1 (by rfl) ⟨3343139, by rfl⟩ : syracuseStep 4457519 = 6686279) B6686279
theorem B2971679 : Blo 1979435 2971679 := bstep (se 1 (by rfl) ⟨2228759, by rfl⟩ : syracuseStep 2971679 = 4457519) B4457519
theorem B1981119 : Blo 1979435 1981119 := bstep (se 1 (by rfl) ⟨1485839, by rfl⟩ : syracuseStep 1981119 = 2971679) B2971679
theorem B2971685 : Blo 1979435 2971685 := bbase (se 4 (by rfl) ⟨278595, by rfl⟩ : syracuseStep 2971685 = 557191) (by norm_num)
theorem B1981123 : Blo 1979435 1981123 := bstep (se 1 (by rfl) ⟨1485842, by rfl⟩ : syracuseStep 1981123 = 2971685) B2971685
theorem B2507365 : Blo 1979435 2507365 := bbase (se 4 (by rfl) ⟨235065, by rfl⟩ : syracuseStep 2507365 = 470131) (by norm_num)
theorem B3343153 : Blo 1979435 3343153 := bstep (se 2 (by rfl) ⟨1253682, by rfl⟩ : syracuseStep 3343153 = 2507365) B2507365
theorem B4457537 : Blo 1979435 4457537 := bstep (se 2 (by rfl) ⟨1671576, by rfl⟩ : syracuseStep 4457537 = 3343153) B3343153
theorem B2971691 : Blo 1979435 2971691 := bstep (se 1 (by rfl) ⟨2228768, by rfl⟩ : syracuseStep 2971691 = 4457537) B4457537
theorem B1981127 : Blo 1979435 1981127 := bstep (se 1 (by rfl) ⟨1485845, by rfl⟩ : syracuseStep 1981127 = 2971691) B2971691
theorem B2228773 : Blo 1979435 2228773 := bbase (se 4 (by rfl) ⟨208947, by rfl⟩ : syracuseStep 2228773 = 417895) (by norm_num)
theorem B2971697 : Blo 1979435 2971697 := bstep (se 2 (by rfl) ⟨1114386, by rfl⟩ : syracuseStep 2971697 = 2228773) B2228773
theorem B1981131 : Blo 1979435 1981131 := bstep (se 1 (by rfl) ⟨1485848, by rfl⟩ : syracuseStep 1981131 = 2971697) B2971697
theorem B5355109 : Blo 1979435 5355109 := bbase (se 4 (by rfl) ⟨502041, by rfl⟩ : syracuseStep 5355109 = 1004083) (by norm_num)
theorem B7140145 : Blo 1979435 7140145 := bstep (se 2 (by rfl) ⟨2677554, by rfl⟩ : syracuseStep 7140145 = 5355109) B5355109
theorem B9520193 : Blo 1979435 9520193 := bstep (se 2 (by rfl) ⟨3570072, by rfl⟩ : syracuseStep 9520193 = 7140145) B7140145
theorem B6346795 : Blo 1979435 6346795 := bstep (se 1 (by rfl) ⟨4760096, by rfl⟩ : syracuseStep 6346795 = 9520193) B9520193
theorem B8462393 : Blo 1979435 8462393 := bstep (se 2 (by rfl) ⟨3173397, by rfl⟩ : syracuseStep 8462393 = 6346795) B6346795
theorem B5641595 : Blo 1979435 5641595 := bstep (se 1 (by rfl) ⟨4231196, by rfl⟩ : syracuseStep 5641595 = 8462393) B8462393
theorem B3761063 : Blo 1979435 3761063 := bstep (se 1 (by rfl) ⟨2820797, by rfl⟩ : syracuseStep 3761063 = 5641595) B5641595
theorem B2507375 : Blo 1979435 2507375 := bstep (se 1 (by rfl) ⟨1880531, by rfl⟩ : syracuseStep 2507375 = 3761063) B3761063
theorem B6686333 : Blo 1979435 6686333 := bstep (se 3 (by rfl) ⟨1253687, by rfl⟩ : syracuseStep 6686333 = 2507375) B2507375
theorem B4457555 : Blo 1979435 4457555 := bstep (se 1 (by rfl) ⟨3343166, by rfl⟩ : syracuseStep 4457555 = 6686333) B6686333
theorem B2971703 : Blo 1979435 2971703 := bstep (se 1 (by rfl) ⟨2228777, by rfl⟩ : syracuseStep 2971703 = 4457555) B4457555
theorem B1981135 : Blo 1979435 1981135 := bstep (se 1 (by rfl) ⟨1485851, by rfl⟩ : syracuseStep 1981135 = 2971703) B2971703
theorem B2971709 : Blo 1979435 2971709 := bbase (se 3 (by rfl) ⟨557195, by rfl⟩ : syracuseStep 2971709 = 1114391) (by norm_num)
theorem B1981139 : Blo 1979435 1981139 := bstep (se 1 (by rfl) ⟨1485854, by rfl⟩ : syracuseStep 1981139 = 2971709) B2971709
theorem B4457573 : Blo 1979435 4457573 := bbase (se 4 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 4457573 = 835795) (by norm_num)
theorem B2971715 : Blo 1979435 2971715 := bstep (se 1 (by rfl) ⟨2228786, by rfl⟩ : syracuseStep 2971715 = 4457573) B4457573
theorem B1981143 : Blo 1979435 1981143 := bstep (se 1 (by rfl) ⟨1485857, by rfl⟩ : syracuseStep 1981143 = 2971715) B2971715
theorem B5014781 : Blo 1979435 5014781 := bbase (se 3 (by rfl) ⟨940271, by rfl⟩ : syracuseStep 5014781 = 1880543) (by norm_num)
theorem B3343187 : Blo 1979435 3343187 := bstep (se 1 (by rfl) ⟨2507390, by rfl⟩ : syracuseStep 3343187 = 5014781) B5014781
theorem B2228791 : Blo 1979435 2228791 := bstep (se 1 (by rfl) ⟨1671593, by rfl⟩ : syracuseStep 2228791 = 3343187) B3343187
theorem B2971721 : Blo 1979435 2971721 := bstep (se 2 (by rfl) ⟨1114395, by rfl⟩ : syracuseStep 2971721 = 2228791) B2228791
theorem B1981147 : Blo 1979435 1981147 := bstep (se 1 (by rfl) ⟨1485860, by rfl⟩ : syracuseStep 1981147 = 2971721) B2971721
theorem B3761093 : Blo 1979435 3761093 := bbase (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) (by norm_num)
theorem B10029581 : Blo 1979435 10029581 := bstep (se 3 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 10029581 = 3761093) B3761093
theorem B6686387 : Blo 1979435 6686387 := bstep (se 1 (by rfl) ⟨5014790, by rfl⟩ : syracuseStep 6686387 = 10029581) B10029581
theorem B4457591 : Blo 1979435 4457591 := bstep (se 1 (by rfl) ⟨3343193, by rfl⟩ : syracuseStep 4457591 = 6686387) B6686387
theorem B2971727 : Blo 1979435 2971727 := bstep (se 1 (by rfl) ⟨2228795, by rfl⟩ : syracuseStep 2971727 = 4457591) B4457591
theorem B1981151 : Blo 1979435 1981151 := bstep (se 1 (by rfl) ⟨1485863, by rfl⟩ : syracuseStep 1981151 = 2971727) B2971727
theorem B2971733 : Blo 1979435 2971733 := bbase (se 8 (by rfl) ⟨17412, by rfl⟩ : syracuseStep 2971733 = 34825) (by norm_num)
theorem B1981155 : Blo 1979435 1981155 := bstep (se 1 (by rfl) ⟨1485866, by rfl⟩ : syracuseStep 1981155 = 2971733) B2971733
theorem B3668197 : Blo 1979435 3668197 := bbase (se 4 (by rfl) ⟨343893, by rfl⟩ : syracuseStep 3668197 = 687787) (by norm_num)
theorem B4890929 : Blo 1979435 4890929 := bstep (se 2 (by rfl) ⟨1834098, by rfl⟩ : syracuseStep 4890929 = 3668197) B3668197
theorem B13042477 : Blo 1979435 13042477 := bstep (se 3 (by rfl) ⟨2445464, by rfl⟩ : syracuseStep 13042477 = 4890929) B4890929
theorem B69559877 : Blo 1979435 69559877 := bstep (se 4 (by rfl) ⟨6521238, by rfl⟩ : syracuseStep 69559877 = 13042477) B13042477
theorem B46373251 : Blo 1979435 46373251 := bstep (se 1 (by rfl) ⟨34779938, by rfl⟩ : syracuseStep 46373251 = 69559877) B69559877
theorem B61831001 : Blo 1979435 61831001 := bstep (se 2 (by rfl) ⟨23186625, by rfl⟩ : syracuseStep 61831001 = 46373251) B46373251
theorem B41220667 : Blo 1979435 41220667 := bstep (se 1 (by rfl) ⟨30915500, by rfl⟩ : syracuseStep 41220667 = 61831001) B61831001
theorem B54960889 : Blo 1979435 54960889 := bstep (se 2 (by rfl) ⟨20610333, by rfl⟩ : syracuseStep 54960889 = 41220667) B41220667
theorem B73281185 : Blo 1979435 73281185 := bstep (se 2 (by rfl) ⟨27480444, by rfl⟩ : syracuseStep 73281185 = 54960889) B54960889
theorem B48854123 : Blo 1979435 48854123 := bstep (se 1 (by rfl) ⟨36640592, by rfl⟩ : syracuseStep 48854123 = 73281185) B73281185
theorem B32569415 : Blo 1979435 32569415 := bstep (se 1 (by rfl) ⟨24427061, by rfl⟩ : syracuseStep 32569415 = 48854123) B48854123
theorem B21712943 : Blo 1979435 21712943 := bstep (se 1 (by rfl) ⟨16284707, by rfl⟩ : syracuseStep 21712943 = 32569415) B32569415
theorem B14475295 : Blo 1979435 14475295 := bstep (se 1 (by rfl) ⟨10856471, by rfl⟩ : syracuseStep 14475295 = 21712943) B21712943
theorem B19300393 : Blo 1979435 19300393 := bstep (se 2 (by rfl) ⟨7237647, by rfl⟩ : syracuseStep 19300393 = 14475295) B14475295
theorem B25733857 : Blo 1979435 25733857 := bstep (se 2 (by rfl) ⟨9650196, by rfl⟩ : syracuseStep 25733857 = 19300393) B19300393
theorem B34311809 : Blo 1979435 34311809 := bstep (se 2 (by rfl) ⟨12866928, by rfl⟩ : syracuseStep 34311809 = 25733857) B25733857
theorem B91498157 : Blo 1979435 91498157 := bstep (se 3 (by rfl) ⟨17155904, by rfl⟩ : syracuseStep 91498157 = 34311809) B34311809
theorem B60998771 : Blo 1979435 60998771 := bstep (se 1 (by rfl) ⟨45749078, by rfl⟩ : syracuseStep 60998771 = 91498157) B91498157
theorem B162663389 : Blo 1979435 162663389 := bstep (se 3 (by rfl) ⟨30499385, by rfl⟩ : syracuseStep 162663389 = 60998771) B60998771
theorem B108442259 : Blo 1979435 108442259 := bstep (se 1 (by rfl) ⟨81331694, by rfl⟩ : syracuseStep 108442259 = 162663389) B162663389
theorem B72294839 : Blo 1979435 72294839 := bstep (se 1 (by rfl) ⟨54221129, by rfl⟩ : syracuseStep 72294839 = 108442259) B108442259
theorem B48196559 : Blo 1979435 48196559 := bstep (se 1 (by rfl) ⟨36147419, by rfl⟩ : syracuseStep 48196559 = 72294839) B72294839
theorem B32131039 : Blo 1979435 32131039 := bstep (se 1 (by rfl) ⟨24098279, by rfl⟩ : syracuseStep 32131039 = 48196559) B48196559
theorem B42841385 : Blo 1979435 42841385 := bstep (se 2 (by rfl) ⟨16065519, by rfl⟩ : syracuseStep 42841385 = 32131039) B32131039
theorem B28560923 : Blo 1979435 28560923 := bstep (se 1 (by rfl) ⟨21420692, by rfl⟩ : syracuseStep 28560923 = 42841385) B42841385
theorem B19040615 : Blo 1979435 19040615 := bstep (se 1 (by rfl) ⟨14280461, by rfl⟩ : syracuseStep 19040615 = 28560923) B28560923
theorem B12693743 : Blo 1979435 12693743 := bstep (se 1 (by rfl) ⟨9520307, by rfl⟩ : syracuseStep 12693743 = 19040615) B19040615
theorem B8462495 : Blo 1979435 8462495 := bstep (se 1 (by rfl) ⟨6346871, by rfl⟩ : syracuseStep 8462495 = 12693743) B12693743
theorem B5641663 : Blo 1979435 5641663 := bstep (se 1 (by rfl) ⟨4231247, by rfl⟩ : syracuseStep 5641663 = 8462495) B8462495
theorem B7522217 : Blo 1979435 7522217 := bstep (se 2 (by rfl) ⟨2820831, by rfl⟩ : syracuseStep 7522217 = 5641663) B5641663
theorem B5014811 : Blo 1979435 5014811 := bstep (se 1 (by rfl) ⟨3761108, by rfl⟩ : syracuseStep 5014811 = 7522217) B7522217
theorem B3343207 : Blo 1979435 3343207 := bstep (se 1 (by rfl) ⟨2507405, by rfl⟩ : syracuseStep 3343207 = 5014811) B5014811
theorem B4457609 : Blo 1979435 4457609 := bstep (se 2 (by rfl) ⟨1671603, by rfl⟩ : syracuseStep 4457609 = 3343207) B3343207
theorem B2971739 : Blo 1979435 2971739 := bstep (se 1 (by rfl) ⟨2228804, by rfl⟩ : syracuseStep 2971739 = 4457609) B4457609
theorem B1981159 : Blo 1979435 1981159 := bstep (se 1 (by rfl) ⟨1485869, by rfl⟩ : syracuseStep 1981159 = 2971739) B2971739
theorem B2228809 : Blo 1979435 2228809 := bbase (se 2 (by rfl) ⟨835803, by rfl⟩ : syracuseStep 2228809 = 1671607) (by norm_num)
theorem B2971745 : Blo 1979435 2971745 := bstep (se 2 (by rfl) ⟨1114404, by rfl⟩ : syracuseStep 2971745 = 2228809) B2228809
theorem B1981163 : Blo 1979435 1981163 := bstep (se 1 (by rfl) ⟨1485872, by rfl⟩ : syracuseStep 1981163 = 2971745) B2971745
theorem B10710389 : Blo 1979435 10710389 := bbase (se 5 (by rfl) ⟨502049, by rfl⟩ : syracuseStep 10710389 = 1004099) (by norm_num)
theorem B7140259 : Blo 1979435 7140259 := bstep (se 1 (by rfl) ⟨5355194, by rfl⟩ : syracuseStep 7140259 = 10710389) B10710389
theorem B9520345 : Blo 1979435 9520345 := bstep (se 2 (by rfl) ⟨3570129, by rfl⟩ : syracuseStep 9520345 = 7140259) B7140259
theorem B12693793 : Blo 1979435 12693793 := bstep (se 2 (by rfl) ⟨4760172, by rfl⟩ : syracuseStep 12693793 = 9520345) B9520345
theorem B16925057 : Blo 1979435 16925057 := bstep (se 2 (by rfl) ⟨6346896, by rfl⟩ : syracuseStep 16925057 = 12693793) B12693793
theorem B11283371 : Blo 1979435 11283371 := bstep (se 1 (by rfl) ⟨8462528, by rfl⟩ : syracuseStep 11283371 = 16925057) B16925057
theorem B7522247 : Blo 1979435 7522247 := bstep (se 1 (by rfl) ⟨5641685, by rfl⟩ : syracuseStep 7522247 = 11283371) B11283371
theorem B5014831 : Blo 1979435 5014831 := bstep (se 1 (by rfl) ⟨3761123, by rfl⟩ : syracuseStep 5014831 = 7522247) B7522247
theorem B6686441 : Blo 1979435 6686441 := bstep (se 2 (by rfl) ⟨2507415, by rfl⟩ : syracuseStep 6686441 = 5014831) B5014831
theorem B4457627 : Blo 1979435 4457627 := bstep (se 1 (by rfl) ⟨3343220, by rfl⟩ : syracuseStep 4457627 = 6686441) B6686441
theorem B2971751 : Blo 1979435 2971751 := bstep (se 1 (by rfl) ⟨2228813, by rfl⟩ : syracuseStep 2971751 = 4457627) B4457627
theorem B1981167 : Blo 1979435 1981167 := bstep (se 1 (by rfl) ⟨1485875, by rfl⟩ : syracuseStep 1981167 = 2971751) B2971751
theorem B2971757 : Blo 1979435 2971757 := bbase (se 3 (by rfl) ⟨557204, by rfl⟩ : syracuseStep 2971757 = 1114409) (by norm_num)
theorem B1981171 : Blo 1979435 1981171 := bstep (se 1 (by rfl) ⟨1485878, by rfl⟩ : syracuseStep 1981171 = 2971757) B2971757
theorem B4457645 : Blo 1979435 4457645 := bbase (se 3 (by rfl) ⟨835808, by rfl⟩ : syracuseStep 4457645 = 1671617) (by norm_num)
theorem B2971763 : Blo 1979435 2971763 := bstep (se 1 (by rfl) ⟨2228822, by rfl⟩ : syracuseStep 2971763 = 4457645) B4457645
theorem B1981175 : Blo 1979435 1981175 := bstep (se 1 (by rfl) ⟨1485881, by rfl⟩ : syracuseStep 1981175 = 2971763) B2971763
theorem B3012317 : Blo 1979435 3012317 := bbase (se 3 (by rfl) ⟨564809, by rfl⟩ : syracuseStep 3012317 = 1129619) (by norm_num)
theorem B2008211 : Blo 1979435 2008211 := bstep (se 1 (by rfl) ⟨1506158, by rfl⟩ : syracuseStep 2008211 = 3012317) B3012317
theorem B5355229 : Blo 1979435 5355229 := bstep (se 3 (by rfl) ⟨1004105, by rfl⟩ : syracuseStep 5355229 = 2008211) B2008211
theorem B7140305 : Blo 1979435 7140305 := bstep (se 2 (by rfl) ⟨2677614, by rfl⟩ : syracuseStep 7140305 = 5355229) B5355229
theorem B4760203 : Blo 1979435 4760203 := bstep (se 1 (by rfl) ⟨3570152, by rfl⟩ : syracuseStep 4760203 = 7140305) B7140305
theorem B6346937 : Blo 1979435 6346937 := bstep (se 2 (by rfl) ⟨2380101, by rfl⟩ : syracuseStep 6346937 = 4760203) B4760203
theorem B4231291 : Blo 1979435 4231291 := bstep (se 1 (by rfl) ⟨3173468, by rfl⟩ : syracuseStep 4231291 = 6346937) B6346937
theorem B5641721 : Blo 1979435 5641721 := bstep (se 2 (by rfl) ⟨2115645, by rfl⟩ : syracuseStep 5641721 = 4231291) B4231291
theorem B3761147 : Blo 1979435 3761147 := bstep (se 1 (by rfl) ⟨2820860, by rfl⟩ : syracuseStep 3761147 = 5641721) B5641721
theorem B2507431 : Blo 1979435 2507431 := bstep (se 1 (by rfl) ⟨1880573, by rfl⟩ : syracuseStep 2507431 = 3761147) B3761147
theorem B3343241 : Blo 1979435 3343241 := bstep (se 2 (by rfl) ⟨1253715, by rfl⟩ : syracuseStep 3343241 = 2507431) B2507431
theorem B2228827 : Blo 1979435 2228827 := bstep (se 1 (by rfl) ⟨1671620, by rfl⟩ : syracuseStep 2228827 = 3343241) B3343241
theorem B2971769 : Blo 1979435 2971769 := bstep (se 2 (by rfl) ⟨1114413, by rfl⟩ : syracuseStep 2971769 = 2228827) B2228827
theorem B1981179 : Blo 1979435 1981179 := bstep (se 1 (by rfl) ⟨1485884, by rfl⟩ : syracuseStep 1981179 = 2971769) B2971769
theorem B9520421 : Blo 1979435 9520421 := bbase (se 4 (by rfl) ⟨892539, by rfl⟩ : syracuseStep 9520421 = 1785079) (by norm_num)
theorem B25387789 : Blo 1979435 25387789 := bstep (se 3 (by rfl) ⟨4760210, by rfl⟩ : syracuseStep 25387789 = 9520421) B9520421
theorem B33850385 : Blo 1979435 33850385 := bstep (se 2 (by rfl) ⟨12693894, by rfl⟩ : syracuseStep 33850385 = 25387789) B25387789
theorem B22566923 : Blo 1979435 22566923 := bstep (se 1 (by rfl) ⟨16925192, by rfl⟩ : syracuseStep 22566923 = 33850385) B33850385
theorem B15044615 : Blo 1979435 15044615 := bstep (se 1 (by rfl) ⟨11283461, by rfl⟩ : syracuseStep 15044615 = 22566923) B22566923
theorem B10029743 : Blo 1979435 10029743 := bstep (se 1 (by rfl) ⟨7522307, by rfl⟩ : syracuseStep 10029743 = 15044615) B15044615
theorem B6686495 : Blo 1979435 6686495 := bstep (se 1 (by rfl) ⟨5014871, by rfl⟩ : syracuseStep 6686495 = 10029743) B10029743
theorem B4457663 : Blo 1979435 4457663 := bstep (se 1 (by rfl) ⟨3343247, by rfl⟩ : syracuseStep 4457663 = 6686495) B6686495
theorem B2971775 : Blo 1979435 2971775 := bstep (se 1 (by rfl) ⟨2228831, by rfl⟩ : syracuseStep 2971775 = 4457663) B4457663
theorem B1981183 : Blo 1979435 1981183 := bstep (se 1 (by rfl) ⟨1485887, by rfl⟩ : syracuseStep 1981183 = 2971775) B2971775
theorem B2971781 : Blo 1979435 2971781 := bbase (se 4 (by rfl) ⟨278604, by rfl⟩ : syracuseStep 2971781 = 557209) (by norm_num)
theorem B1981187 : Blo 1979435 1981187 := bstep (se 1 (by rfl) ⟨1485890, by rfl⟩ : syracuseStep 1981187 = 2971781) B2971781
theorem B3343261 : Blo 1979435 3343261 := bbase (se 3 (by rfl) ⟨626861, by rfl⟩ : syracuseStep 3343261 = 1253723) (by norm_num)
theorem B4457681 : Blo 1979435 4457681 := bstep (se 2 (by rfl) ⟨1671630, by rfl⟩ : syracuseStep 4457681 = 3343261) B3343261
theorem B2971787 : Blo 1979435 2971787 := bstep (se 1 (by rfl) ⟨2228840, by rfl⟩ : syracuseStep 2971787 = 4457681) B4457681
theorem B1981191 : Blo 1979435 1981191 := bstep (se 1 (by rfl) ⟨1485893, by rfl⟩ : syracuseStep 1981191 = 2971787) B2971787
theorem B2228845 : Blo 1979435 2228845 := bbase (se 3 (by rfl) ⟨417908, by rfl⟩ : syracuseStep 2228845 = 835817) (by norm_num)
theorem B2971793 : Blo 1979435 2971793 := bstep (se 2 (by rfl) ⟨1114422, by rfl⟩ : syracuseStep 2971793 = 2228845) B2228845
theorem B1981195 : Blo 1979435 1981195 := bstep (se 1 (by rfl) ⟨1485896, by rfl⟩ : syracuseStep 1981195 = 2971793) B2971793
theorem B6686549 : Blo 1979435 6686549 := bbase (se 9 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 6686549 = 39179) (by norm_num)
theorem B4457699 : Blo 1979435 4457699 := bstep (se 1 (by rfl) ⟨3343274, by rfl⟩ : syracuseStep 4457699 = 6686549) B6686549
theorem B2971799 : Blo 1979435 2971799 := bstep (se 1 (by rfl) ⟨2228849, by rfl⟩ : syracuseStep 2971799 = 4457699) B4457699
theorem B1981199 : Blo 1979435 1981199 := bstep (se 1 (by rfl) ⟨1485899, by rfl⟩ : syracuseStep 1981199 = 2971799) B2971799
theorem B2971805 : Blo 1979435 2971805 := bbase (se 3 (by rfl) ⟨557213, by rfl⟩ : syracuseStep 2971805 = 1114427) (by norm_num)
theorem B1981203 : Blo 1979435 1981203 := bstep (se 1 (by rfl) ⟨1485902, by rfl⟩ : syracuseStep 1981203 = 2971805) B2971805
theorem B4457717 : Blo 1979435 4457717 := bbase (se 5 (by rfl) ⟨208955, by rfl⟩ : syracuseStep 4457717 = 417911) (by norm_num)
theorem B2971811 : Blo 1979435 2971811 := bstep (se 1 (by rfl) ⟨2228858, by rfl⟩ : syracuseStep 2971811 = 4457717) B4457717
theorem B1981207 : Blo 1979435 1981207 := bstep (se 1 (by rfl) ⟨1485905, by rfl⟩ : syracuseStep 1981207 = 2971811) B2971811
theorem B2412613 : Blo 1979435 2412613 := bbase (se 4 (by rfl) ⟨226182, by rfl⟩ : syracuseStep 2412613 = 452365) (by norm_num)
theorem B3216817 : Blo 1979435 3216817 := bstep (se 2 (by rfl) ⟨1206306, by rfl⟩ : syracuseStep 3216817 = 2412613) B2412613
theorem B17156357 : Blo 1979435 17156357 := bstep (se 4 (by rfl) ⟨1608408, by rfl⟩ : syracuseStep 17156357 = 3216817) B3216817
theorem B11437571 : Blo 1979435 11437571 := bstep (se 1 (by rfl) ⟨8578178, by rfl⟩ : syracuseStep 11437571 = 17156357) B17156357
theorem B7625047 : Blo 1979435 7625047 := bstep (se 1 (by rfl) ⟨5718785, by rfl⟩ : syracuseStep 7625047 = 11437571) B11437571
theorem B10166729 : Blo 1979435 10166729 := bstep (se 2 (by rfl) ⟨3812523, by rfl⟩ : syracuseStep 10166729 = 7625047) B7625047
theorem B27111277 : Blo 1979435 27111277 := bstep (se 3 (by rfl) ⟨5083364, by rfl⟩ : syracuseStep 27111277 = 10166729) B10166729
theorem B36148369 : Blo 1979435 36148369 := bstep (se 2 (by rfl) ⟨13555638, by rfl⟩ : syracuseStep 36148369 = 27111277) B27111277
theorem B48197825 : Blo 1979435 48197825 := bstep (se 2 (by rfl) ⟨18074184, by rfl⟩ : syracuseStep 48197825 = 36148369) B36148369
theorem B32131883 : Blo 1979435 32131883 := bstep (se 1 (by rfl) ⟨24098912, by rfl⟩ : syracuseStep 32131883 = 48197825) B48197825
theorem B21421255 : Blo 1979435 21421255 := bstep (se 1 (by rfl) ⟨16065941, by rfl⟩ : syracuseStep 21421255 = 32131883) B32131883
theorem B28561673 : Blo 1979435 28561673 := bstep (se 2 (by rfl) ⟨10710627, by rfl⟩ : syracuseStep 28561673 = 21421255) B21421255
theorem B19041115 : Blo 1979435 19041115 := bstep (se 1 (by rfl) ⟨14280836, by rfl⟩ : syracuseStep 19041115 = 28561673) B28561673
theorem B25388153 : Blo 1979435 25388153 := bstep (se 2 (by rfl) ⟨9520557, by rfl⟩ : syracuseStep 25388153 = 19041115) B19041115
theorem B16925435 : Blo 1979435 16925435 := bstep (se 1 (by rfl) ⟨12694076, by rfl⟩ : syracuseStep 16925435 = 25388153) B25388153
theorem B11283623 : Blo 1979435 11283623 := bstep (se 1 (by rfl) ⟨8462717, by rfl⟩ : syracuseStep 11283623 = 16925435) B16925435
theorem B7522415 : Blo 1979435 7522415 := bstep (se 1 (by rfl) ⟨5641811, by rfl⟩ : syracuseStep 7522415 = 11283623) B11283623
theorem B5014943 : Blo 1979435 5014943 := bstep (se 1 (by rfl) ⟨3761207, by rfl⟩ : syracuseStep 5014943 = 7522415) B7522415
theorem B3343295 : Blo 1979435 3343295 := bstep (se 1 (by rfl) ⟨2507471, by rfl⟩ : syracuseStep 3343295 = 5014943) B5014943
theorem B2228863 : Blo 1979435 2228863 := bstep (se 1 (by rfl) ⟨1671647, by rfl⟩ : syracuseStep 2228863 = 3343295) B3343295
theorem B2971817 : Blo 1979435 2971817 := bstep (se 2 (by rfl) ⟨1114431, by rfl⟩ : syracuseStep 2971817 = 2228863) B2228863
theorem B1981211 : Blo 1979435 1981211 := bstep (se 1 (by rfl) ⟨1485908, by rfl⟩ : syracuseStep 1981211 = 2971817) B2971817
theorem B4518557 : Blo 1979435 4518557 := bbase (se 3 (by rfl) ⟨847229, by rfl⟩ : syracuseStep 4518557 = 1694459) (by norm_num)
theorem B3012371 : Blo 1979435 3012371 := bstep (se 1 (by rfl) ⟨2259278, by rfl⟩ : syracuseStep 3012371 = 4518557) B4518557
theorem B2008247 : Blo 1979435 2008247 := bstep (se 1 (by rfl) ⟨1506185, by rfl⟩ : syracuseStep 2008247 = 3012371) B3012371
theorem B5355325 : Blo 1979435 5355325 := bstep (se 3 (by rfl) ⟨1004123, by rfl⟩ : syracuseStep 5355325 = 2008247) B2008247
theorem B7140433 : Blo 1979435 7140433 := bstep (se 2 (by rfl) ⟨2677662, by rfl⟩ : syracuseStep 7140433 = 5355325) B5355325
theorem B9520577 : Blo 1979435 9520577 := bstep (se 2 (by rfl) ⟨3570216, by rfl⟩ : syracuseStep 9520577 = 7140433) B7140433
theorem B6347051 : Blo 1979435 6347051 := bstep (se 1 (by rfl) ⟨4760288, by rfl⟩ : syracuseStep 6347051 = 9520577) B9520577
theorem B4231367 : Blo 1979435 4231367 := bstep (se 1 (by rfl) ⟨3173525, by rfl⟩ : syracuseStep 4231367 = 6347051) B6347051
theorem B2820911 : Blo 1979435 2820911 := bstep (se 1 (by rfl) ⟨2115683, by rfl⟩ : syracuseStep 2820911 = 4231367) B4231367
theorem B7522429 : Blo 1979435 7522429 := bstep (se 3 (by rfl) ⟨1410455, by rfl⟩ : syracuseStep 7522429 = 2820911) B2820911
theorem B10029905 : Blo 1979435 10029905 := bstep (se 2 (by rfl) ⟨3761214, by rfl⟩ : syracuseStep 10029905 = 7522429) B7522429
theorem B6686603 : Blo 1979435 6686603 := bstep (se 1 (by rfl) ⟨5014952, by rfl⟩ : syracuseStep 6686603 = 10029905) B10029905
theorem B4457735 : Blo 1979435 4457735 := bstep (se 1 (by rfl) ⟨3343301, by rfl⟩ : syracuseStep 4457735 = 6686603) B6686603
theorem B2971823 : Blo 1979435 2971823 := bstep (se 1 (by rfl) ⟨2228867, by rfl⟩ : syracuseStep 2971823 = 4457735) B4457735
theorem B1981215 : Blo 1979435 1981215 := bstep (se 1 (by rfl) ⟨1485911, by rfl⟩ : syracuseStep 1981215 = 2971823) B2971823
theorem B2971829 : Blo 1979435 2971829 := bbase (se 5 (by rfl) ⟨139304, by rfl⟩ : syracuseStep 2971829 = 278609) (by norm_num)
theorem B1981219 : Blo 1979435 1981219 := bstep (se 1 (by rfl) ⟨1485914, by rfl⟩ : syracuseStep 1981219 = 2971829) B2971829
theorem B5014973 : Blo 1979435 5014973 := bbase (se 3 (by rfl) ⟨940307, by rfl⟩ : syracuseStep 5014973 = 1880615) (by norm_num)
theorem B3343315 : Blo 1979435 3343315 := bstep (se 1 (by rfl) ⟨2507486, by rfl⟩ : syracuseStep 3343315 = 5014973) B5014973
theorem B4457753 : Blo 1979435 4457753 := bstep (se 2 (by rfl) ⟨1671657, by rfl⟩ : syracuseStep 4457753 = 3343315) B3343315
theorem B2971835 : Blo 1979435 2971835 := bstep (se 1 (by rfl) ⟨2228876, by rfl⟩ : syracuseStep 2971835 = 4457753) B4457753
theorem B1981223 : Blo 1979435 1981223 := bstep (se 1 (by rfl) ⟨1485917, by rfl⟩ : syracuseStep 1981223 = 2971835) B2971835
theorem B2228881 : Blo 1979435 2228881 := bbase (se 2 (by rfl) ⟨835830, by rfl⟩ : syracuseStep 2228881 = 1671661) (by norm_num)
theorem B2971841 : Blo 1979435 2971841 := bstep (se 2 (by rfl) ⟨1114440, by rfl⟩ : syracuseStep 2971841 = 2228881) B2228881
theorem B1981227 : Blo 1979435 1981227 := bstep (se 1 (by rfl) ⟨1485920, by rfl⟩ : syracuseStep 1981227 = 2971841) B2971841
theorem B3761245 : Blo 1979435 3761245 := bbase (se 3 (by rfl) ⟨705233, by rfl⟩ : syracuseStep 3761245 = 1410467) (by norm_num)
theorem B5014993 : Blo 1979435 5014993 := bstep (se 2 (by rfl) ⟨1880622, by rfl⟩ : syracuseStep 5014993 = 3761245) B3761245
theorem B6686657 : Blo 1979435 6686657 := bstep (se 2 (by rfl) ⟨2507496, by rfl⟩ : syracuseStep 6686657 = 5014993) B5014993
theorem B4457771 : Blo 1979435 4457771 := bstep (se 1 (by rfl) ⟨3343328, by rfl⟩ : syracuseStep 4457771 = 6686657) B6686657
theorem B2971847 : Blo 1979435 2971847 := bstep (se 1 (by rfl) ⟨2228885, by rfl⟩ : syracuseStep 2971847 = 4457771) B4457771
theorem B1981231 : Blo 1979435 1981231 := bstep (se 1 (by rfl) ⟨1485923, by rfl⟩ : syracuseStep 1981231 = 2971847) B2971847
theorem B2971853 : Blo 1979435 2971853 := bbase (se 3 (by rfl) ⟨557222, by rfl⟩ : syracuseStep 2971853 = 1114445) (by norm_num)
theorem B1981235 : Blo 1979435 1981235 := bstep (se 1 (by rfl) ⟨1485926, by rfl⟩ : syracuseStep 1981235 = 2971853) B2971853
theorem B4457789 : Blo 1979435 4457789 := bbase (se 3 (by rfl) ⟨835835, by rfl⟩ : syracuseStep 4457789 = 1671671) (by norm_num)
theorem B2971859 : Blo 1979435 2971859 := bstep (se 1 (by rfl) ⟨2228894, by rfl⟩ : syracuseStep 2971859 = 4457789) B4457789
theorem B1981239 : Blo 1979435 1981239 := bstep (se 1 (by rfl) ⟨1485929, by rfl⟩ : syracuseStep 1981239 = 2971859) B2971859
theorem B3343349 : Blo 1979435 3343349 := bbase (se 5 (by rfl) ⟨156719, by rfl⟩ : syracuseStep 3343349 = 313439) (by norm_num)
theorem B2228899 : Blo 1979435 2228899 := bstep (se 1 (by rfl) ⟨1671674, by rfl⟩ : syracuseStep 2228899 = 3343349) B3343349
theorem B2971865 : Blo 1979435 2971865 := bstep (se 2 (by rfl) ⟨1114449, by rfl⟩ : syracuseStep 2971865 = 2228899) B2228899
theorem B1981243 : Blo 1979435 1981243 := bstep (se 1 (by rfl) ⟨1485932, by rfl⟩ : syracuseStep 1981243 = 2971865) B2971865
theorem B4760365 : Blo 1979435 4760365 := bbase (se 3 (by rfl) ⟨892568, by rfl⟩ : syracuseStep 4760365 = 1785137) (by norm_num)
theorem B6347153 : Blo 1979435 6347153 := bstep (se 2 (by rfl) ⟨2380182, by rfl⟩ : syracuseStep 6347153 = 4760365) B4760365
theorem B4231435 : Blo 1979435 4231435 := bstep (se 1 (by rfl) ⟨3173576, by rfl⟩ : syracuseStep 4231435 = 6347153) B6347153
theorem B5641913 : Blo 1979435 5641913 := bstep (se 2 (by rfl) ⟨2115717, by rfl⟩ : syracuseStep 5641913 = 4231435) B4231435
theorem B15045101 : Blo 1979435 15045101 := bstep (se 3 (by rfl) ⟨2820956, by rfl⟩ : syracuseStep 15045101 = 5641913) B5641913
theorem B10030067 : Blo 1979435 10030067 := bstep (se 1 (by rfl) ⟨7522550, by rfl⟩ : syracuseStep 10030067 = 15045101) B15045101
theorem B6686711 : Blo 1979435 6686711 := bstep (se 1 (by rfl) ⟨5015033, by rfl⟩ : syracuseStep 6686711 = 10030067) B10030067
theorem B4457807 : Blo 1979435 4457807 := bstep (se 1 (by rfl) ⟨3343355, by rfl⟩ : syracuseStep 4457807 = 6686711) B6686711
theorem B2971871 : Blo 1979435 2971871 := bstep (se 1 (by rfl) ⟨2228903, by rfl⟩ : syracuseStep 2971871 = 4457807) B4457807
theorem B1981247 : Blo 1979435 1981247 := bstep (se 1 (by rfl) ⟨1485935, by rfl⟩ : syracuseStep 1981247 = 2971871) B2971871
theorem B2971877 : Blo 1979435 2971877 := bbase (se 4 (by rfl) ⟨278613, by rfl⟩ : syracuseStep 2971877 = 557227) (by norm_num)
theorem B1981251 : Blo 1979435 1981251 := bstep (se 1 (by rfl) ⟨1485938, by rfl⟩ : syracuseStep 1981251 = 2971877) B2971877
theorem B4231453 : Blo 1979435 4231453 := bbase (se 3 (by rfl) ⟨793397, by rfl⟩ : syracuseStep 4231453 = 1586795) (by norm_num)
theorem B5641937 : Blo 1979435 5641937 := bstep (se 2 (by rfl) ⟨2115726, by rfl⟩ : syracuseStep 5641937 = 4231453) B4231453
theorem B3761291 : Blo 1979435 3761291 := bstep (se 1 (by rfl) ⟨2820968, by rfl⟩ : syracuseStep 3761291 = 5641937) B5641937
theorem B2507527 : Blo 1979435 2507527 := bstep (se 1 (by rfl) ⟨1880645, by rfl⟩ : syracuseStep 2507527 = 3761291) B3761291
theorem B3343369 : Blo 1979435 3343369 := bstep (se 2 (by rfl) ⟨1253763, by rfl⟩ : syracuseStep 3343369 = 2507527) B2507527
theorem B4457825 : Blo 1979435 4457825 := bstep (se 2 (by rfl) ⟨1671684, by rfl⟩ : syracuseStep 4457825 = 3343369) B3343369
theorem B2971883 : Blo 1979435 2971883 := bstep (se 1 (by rfl) ⟨2228912, by rfl⟩ : syracuseStep 2971883 = 4457825) B4457825
theorem B1981255 : Blo 1979435 1981255 := bstep (se 1 (by rfl) ⟨1485941, by rfl⟩ : syracuseStep 1981255 = 2971883) B2971883
theorem B2228917 : Blo 1979435 2228917 := bbase (se 5 (by rfl) ⟨104480, by rfl⟩ : syracuseStep 2228917 = 208961) (by norm_num)
theorem B2971889 : Blo 1979435 2971889 := bstep (se 2 (by rfl) ⟨1114458, by rfl⟩ : syracuseStep 2971889 = 2228917) B2228917
theorem B1981259 : Blo 1979435 1981259 := bstep (se 1 (by rfl) ⟨1485944, by rfl⟩ : syracuseStep 1981259 = 2971889) B2971889
theorem B2507537 : Blo 1979435 2507537 := bbase (se 2 (by rfl) ⟨940326, by rfl⟩ : syracuseStep 2507537 = 1880653) (by norm_num)
theorem B6686765 : Blo 1979435 6686765 := bstep (se 3 (by rfl) ⟨1253768, by rfl⟩ : syracuseStep 6686765 = 2507537) B2507537
theorem B4457843 : Blo 1979435 4457843 := bstep (se 1 (by rfl) ⟨3343382, by rfl⟩ : syracuseStep 4457843 = 6686765) B6686765
theorem B2971895 : Blo 1979435 2971895 := bstep (se 1 (by rfl) ⟨2228921, by rfl⟩ : syracuseStep 2971895 = 4457843) B4457843
theorem B1981263 : Blo 1979435 1981263 := bstep (se 1 (by rfl) ⟨1485947, by rfl⟩ : syracuseStep 1981263 = 2971895) B2971895
theorem B2971901 : Blo 1979435 2971901 := bbase (se 3 (by rfl) ⟨557231, by rfl⟩ : syracuseStep 2971901 = 1114463) (by norm_num)
theorem B1981267 : Blo 1979435 1981267 := bstep (se 1 (by rfl) ⟨1485950, by rfl⟩ : syracuseStep 1981267 = 2971901) B2971901
theorem B4457861 : Blo 1979435 4457861 := bbase (se 4 (by rfl) ⟨417924, by rfl⟩ : syracuseStep 4457861 = 835849) (by norm_num)
theorem B2971907 : Blo 1979435 2971907 := bstep (se 1 (by rfl) ⟨2228930, by rfl⟩ : syracuseStep 2971907 = 4457861) B4457861
theorem B1981271 : Blo 1979435 1981271 := bstep (se 1 (by rfl) ⟨1485953, by rfl⟩ : syracuseStep 1981271 = 2971907) B2971907
theorem B2820997 : Blo 1979435 2820997 := bbase (se 4 (by rfl) ⟨264468, by rfl⟩ : syracuseStep 2820997 = 528937) (by norm_num)
theorem B3761329 : Blo 1979435 3761329 := bstep (se 2 (by rfl) ⟨1410498, by rfl⟩ : syracuseStep 3761329 = 2820997) B2820997
theorem B5015105 : Blo 1979435 5015105 := bstep (se 2 (by rfl) ⟨1880664, by rfl⟩ : syracuseStep 5015105 = 3761329) B3761329
theorem B3343403 : Blo 1979435 3343403 := bstep (se 1 (by rfl) ⟨2507552, by rfl⟩ : syracuseStep 3343403 = 5015105) B5015105
theorem B2228935 : Blo 1979435 2228935 := bstep (se 1 (by rfl) ⟨1671701, by rfl⟩ : syracuseStep 2228935 = 3343403) B3343403
theorem B2971913 : Blo 1979435 2971913 := bstep (se 2 (by rfl) ⟨1114467, by rfl⟩ : syracuseStep 2971913 = 2228935) B2228935
theorem B1981275 : Blo 1979435 1981275 := bstep (se 1 (by rfl) ⟨1485956, by rfl⟩ : syracuseStep 1981275 = 2971913) B2971913
theorem B10030229 : Blo 1979435 10030229 := bbase (se 6 (by rfl) ⟨235083, by rfl⟩ : syracuseStep 10030229 = 470167) (by norm_num)
theorem B6686819 : Blo 1979435 6686819 := bstep (se 1 (by rfl) ⟨5015114, by rfl⟩ : syracuseStep 6686819 = 10030229) B10030229
theorem B4457879 : Blo 1979435 4457879 := bstep (se 1 (by rfl) ⟨3343409, by rfl⟩ : syracuseStep 4457879 = 6686819) B6686819
theorem B2971919 : Blo 1979435 2971919 := bstep (se 1 (by rfl) ⟨2228939, by rfl⟩ : syracuseStep 2971919 = 4457879) B4457879
theorem B1981279 : Blo 1979435 1981279 := bstep (se 1 (by rfl) ⟨1485959, by rfl⟩ : syracuseStep 1981279 = 2971919) B2971919
theorem B2971925 : Blo 1979435 2971925 := bbase (se 6 (by rfl) ⟨69654, by rfl⟩ : syracuseStep 2971925 = 139309) (by norm_num)
theorem B1981283 : Blo 1979435 1981283 := bstep (se 1 (by rfl) ⟨1485962, by rfl⟩ : syracuseStep 1981283 = 2971925) B2971925
theorem B4760461 : Blo 1979435 4760461 := bbase (se 3 (by rfl) ⟨892586, by rfl⟩ : syracuseStep 4760461 = 1785173) (by norm_num)
theorem B25389125 : Blo 1979435 25389125 := bstep (se 4 (by rfl) ⟨2380230, by rfl⟩ : syracuseStep 25389125 = 4760461) B4760461
theorem B16926083 : Blo 1979435 16926083 := bstep (se 1 (by rfl) ⟨12694562, by rfl⟩ : syracuseStep 16926083 = 25389125) B25389125
theorem B11284055 : Blo 1979435 11284055 := bstep (se 1 (by rfl) ⟨8463041, by rfl⟩ : syracuseStep 11284055 = 16926083) B16926083
theorem B7522703 : Blo 1979435 7522703 := bstep (se 1 (by rfl) ⟨5642027, by rfl⟩ : syracuseStep 7522703 = 11284055) B11284055
theorem B5015135 : Blo 1979435 5015135 := bstep (se 1 (by rfl) ⟨3761351, by rfl⟩ : syracuseStep 5015135 = 7522703) B7522703
theorem B3343423 : Blo 1979435 3343423 := bstep (se 1 (by rfl) ⟨2507567, by rfl⟩ : syracuseStep 3343423 = 5015135) B5015135
theorem B4457897 : Blo 1979435 4457897 := bstep (se 2 (by rfl) ⟨1671711, by rfl⟩ : syracuseStep 4457897 = 3343423) B3343423
theorem B2971931 : Blo 1979435 2971931 := bstep (se 1 (by rfl) ⟨2228948, by rfl⟩ : syracuseStep 2971931 = 4457897) B4457897
theorem B1981287 : Blo 1979435 1981287 := bstep (se 1 (by rfl) ⟨1485965, by rfl⟩ : syracuseStep 1981287 = 2971931) B2971931
theorem B2228953 : Blo 1979435 2228953 := bbase (se 2 (by rfl) ⟨835857, by rfl⟩ : syracuseStep 2228953 = 1671715) (by norm_num)
theorem B2971937 : Blo 1979435 2971937 := bstep (se 2 (by rfl) ⟨1114476, by rfl⟩ : syracuseStep 2971937 = 2228953) B2228953
theorem B1981291 : Blo 1979435 1981291 := bstep (se 1 (by rfl) ⟨1485968, by rfl⟩ : syracuseStep 1981291 = 2971937) B2971937
theorem B2115769 : Blo 1979435 2115769 := bbase (se 2 (by rfl) ⟨793413, by rfl⟩ : syracuseStep 2115769 = 1586827) (by norm_num)
theorem B2821025 : Blo 1979435 2821025 := bstep (se 2 (by rfl) ⟨1057884, by rfl⟩ : syracuseStep 2821025 = 2115769) B2115769
theorem B7522733 : Blo 1979435 7522733 := bstep (se 3 (by rfl) ⟨1410512, by rfl⟩ : syracuseStep 7522733 = 2821025) B2821025
theorem B5015155 : Blo 1979435 5015155 := bstep (se 1 (by rfl) ⟨3761366, by rfl⟩ : syracuseStep 5015155 = 7522733) B7522733
theorem B6686873 : Blo 1979435 6686873 := bstep (se 2 (by rfl) ⟨2507577, by rfl⟩ : syracuseStep 6686873 = 5015155) B5015155
theorem B4457915 : Blo 1979435 4457915 := bstep (se 1 (by rfl) ⟨3343436, by rfl⟩ : syracuseStep 4457915 = 6686873) B6686873
theorem B2971943 : Blo 1979435 2971943 := bstep (se 1 (by rfl) ⟨2228957, by rfl⟩ : syracuseStep 2971943 = 4457915) B4457915
theorem B1981295 : Blo 1979435 1981295 := bstep (se 1 (by rfl) ⟨1485971, by rfl⟩ : syracuseStep 1981295 = 2971943) B2971943
theorem B2971949 : Blo 1979435 2971949 := bbase (se 3 (by rfl) ⟨557240, by rfl⟩ : syracuseStep 2971949 = 1114481) (by norm_num)
theorem B1981299 : Blo 1979435 1981299 := bstep (se 1 (by rfl) ⟨1485974, by rfl⟩ : syracuseStep 1981299 = 2971949) B2971949
theorem B4457933 : Blo 1979435 4457933 := bbase (se 3 (by rfl) ⟨835862, by rfl⟩ : syracuseStep 4457933 = 1671725) (by norm_num)
theorem B2971955 : Blo 1979435 2971955 := bstep (se 1 (by rfl) ⟨2228966, by rfl⟩ : syracuseStep 2971955 = 4457933) B4457933
theorem B1981303 : Blo 1979435 1981303 := bstep (se 1 (by rfl) ⟨1485977, by rfl⟩ : syracuseStep 1981303 = 2971955) B2971955
theorem B2507593 : Blo 1979435 2507593 := bbase (se 2 (by rfl) ⟨940347, by rfl⟩ : syracuseStep 2507593 = 1880695) (by norm_num)
theorem B3343457 : Blo 1979435 3343457 := bstep (se 2 (by rfl) ⟨1253796, by rfl⟩ : syracuseStep 3343457 = 2507593) B2507593
theorem B2228971 : Blo 1979435 2228971 := bstep (se 1 (by rfl) ⟨1671728, by rfl⟩ : syracuseStep 2228971 = 3343457) B3343457
theorem B2971961 : Blo 1979435 2971961 := bstep (se 2 (by rfl) ⟨1114485, by rfl⟩ : syracuseStep 2971961 = 2228971) B2228971
theorem B1981307 : Blo 1979435 1981307 := bstep (se 1 (by rfl) ⟨1485980, by rfl⟩ : syracuseStep 1981307 = 2971961) B2971961
theorem B4825469 : Blo 1979435 4825469 := bbase (se 3 (by rfl) ⟨904775, by rfl⟩ : syracuseStep 4825469 = 1809551) (by norm_num)
theorem B3216979 : Blo 1979435 3216979 := bstep (se 1 (by rfl) ⟨2412734, by rfl⟩ : syracuseStep 3216979 = 4825469) B4825469
theorem B17157221 : Blo 1979435 17157221 := bstep (se 4 (by rfl) ⟨1608489, by rfl⟩ : syracuseStep 17157221 = 3216979) B3216979
theorem B11438147 : Blo 1979435 11438147 := bstep (se 1 (by rfl) ⟨8578610, by rfl⟩ : syracuseStep 11438147 = 17157221) B17157221
theorem B7625431 : Blo 1979435 7625431 := bstep (se 1 (by rfl) ⟨5719073, by rfl⟩ : syracuseStep 7625431 = 11438147) B11438147
theorem B40668965 : Blo 1979435 40668965 := bstep (se 4 (by rfl) ⟨3812715, by rfl⟩ : syracuseStep 40668965 = 7625431) B7625431
theorem B27112643 : Blo 1979435 27112643 := bstep (se 1 (by rfl) ⟨20334482, by rfl⟩ : syracuseStep 27112643 = 40668965) B40668965
theorem B18075095 : Blo 1979435 18075095 := bstep (se 1 (by rfl) ⟨13556321, by rfl⟩ : syracuseStep 18075095 = 27112643) B27112643
theorem B12050063 : Blo 1979435 12050063 := bstep (se 1 (by rfl) ⟨9037547, by rfl⟩ : syracuseStep 12050063 = 18075095) B18075095
theorem B8033375 : Blo 1979435 8033375 := bstep (se 1 (by rfl) ⟨6025031, by rfl⟩ : syracuseStep 8033375 = 12050063) B12050063
theorem B21422333 : Blo 1979435 21422333 := bstep (se 3 (by rfl) ⟨4016687, by rfl⟩ : syracuseStep 21422333 = 8033375) B8033375
theorem B14281555 : Blo 1979435 14281555 := bstep (se 1 (by rfl) ⟨10711166, by rfl⟩ : syracuseStep 14281555 = 21422333) B21422333
theorem B19042073 : Blo 1979435 19042073 := bstep (se 2 (by rfl) ⟨7140777, by rfl⟩ : syracuseStep 19042073 = 14281555) B14281555
theorem B12694715 : Blo 1979435 12694715 := bstep (se 1 (by rfl) ⟨9521036, by rfl⟩ : syracuseStep 12694715 = 19042073) B19042073
theorem B8463143 : Blo 1979435 8463143 := bstep (se 1 (by rfl) ⟨6347357, by rfl⟩ : syracuseStep 8463143 = 12694715) B12694715
theorem B22568381 : Blo 1979435 22568381 := bstep (se 3 (by rfl) ⟨4231571, by rfl⟩ : syracuseStep 22568381 = 8463143) B8463143
theorem B15045587 : Blo 1979435 15045587 := bstep (se 1 (by rfl) ⟨11284190, by rfl⟩ : syracuseStep 15045587 = 22568381) B22568381
theorem B10030391 : Blo 1979435 10030391 := bstep (se 1 (by rfl) ⟨7522793, by rfl⟩ : syracuseStep 10030391 = 15045587) B15045587
theorem B6686927 : Blo 1979435 6686927 := bstep (se 1 (by rfl) ⟨5015195, by rfl⟩ : syracuseStep 6686927 = 10030391) B10030391
theorem B4457951 : Blo 1979435 4457951 := bstep (se 1 (by rfl) ⟨3343463, by rfl⟩ : syracuseStep 4457951 = 6686927) B6686927
theorem B2971967 : Blo 1979435 2971967 := bstep (se 1 (by rfl) ⟨2228975, by rfl⟩ : syracuseStep 2971967 = 4457951) B4457951
theorem B1981311 : Blo 1979435 1981311 := bstep (se 1 (by rfl) ⟨1485983, by rfl⟩ : syracuseStep 1981311 = 2971967) B2971967
theorem B2971973 : Blo 1979435 2971973 := bbase (se 4 (by rfl) ⟨278622, by rfl⟩ : syracuseStep 2971973 = 557245) (by norm_num)
theorem B1981315 : Blo 1979435 1981315 := bstep (se 1 (by rfl) ⟨1485986, by rfl⟩ : syracuseStep 1981315 = 2971973) B2971973
theorem B3343477 : Blo 1979435 3343477 := bbase (se 5 (by rfl) ⟨156725, by rfl⟩ : syracuseStep 3343477 = 313451) (by norm_num)
theorem B4457969 : Blo 1979435 4457969 := bstep (se 2 (by rfl) ⟨1671738, by rfl⟩ : syracuseStep 4457969 = 3343477) B3343477
theorem B2971979 : Blo 1979435 2971979 := bstep (se 1 (by rfl) ⟨2228984, by rfl⟩ : syracuseStep 2971979 = 4457969) B4457969
theorem B1981319 : Blo 1979435 1981319 := bstep (se 1 (by rfl) ⟨1485989, by rfl⟩ : syracuseStep 1981319 = 2971979) B2971979
theorem B2228989 : Blo 1979435 2228989 := bbase (se 3 (by rfl) ⟨417935, by rfl⟩ : syracuseStep 2228989 = 835871) (by norm_num)
theorem B2971985 : Blo 1979435 2971985 := bstep (se 2 (by rfl) ⟨1114494, by rfl⟩ : syracuseStep 2971985 = 2228989) B2228989
theorem B1981323 : Blo 1979435 1981323 := bstep (se 1 (by rfl) ⟨1485992, by rfl⟩ : syracuseStep 1981323 = 2971985) B2971985
theorem B6686981 : Blo 1979435 6686981 := bbase (se 4 (by rfl) ⟨626904, by rfl⟩ : syracuseStep 6686981 = 1253809) (by norm_num)
theorem B4457987 : Blo 1979435 4457987 := bstep (se 1 (by rfl) ⟨3343490, by rfl⟩ : syracuseStep 4457987 = 6686981) B6686981
theorem B2971991 : Blo 1979435 2971991 := bstep (se 1 (by rfl) ⟨2228993, by rfl⟩ : syracuseStep 2971991 = 4457987) B4457987
theorem B1981327 : Blo 1979435 1981327 := bstep (se 1 (by rfl) ⟨1485995, by rfl⟩ : syracuseStep 1981327 = 2971991) B2971991
theorem B2971997 : Blo 1979435 2971997 := bbase (se 3 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 2971997 = 1114499) (by norm_num)
theorem B1981331 : Blo 1979435 1981331 := bstep (se 1 (by rfl) ⟨1485998, by rfl⟩ : syracuseStep 1981331 = 2971997) B2971997
theorem B4458005 : Blo 1979435 4458005 := bbase (se 6 (by rfl) ⟨104484, by rfl⟩ : syracuseStep 4458005 = 208969) (by norm_num)
theorem B2972003 : Blo 1979435 2972003 := bstep (se 1 (by rfl) ⟨2229002, by rfl⟩ : syracuseStep 2972003 = 4458005) B4458005
theorem B1981335 : Blo 1979435 1981335 := bstep (se 1 (by rfl) ⟨1486001, by rfl⟩ : syracuseStep 1981335 = 2972003) B2972003
theorem B7522901 : Blo 1979435 7522901 := bbase (se 8 (by rfl) ⟨44079, by rfl⟩ : syracuseStep 7522901 = 88159) (by norm_num)
theorem B5015267 : Blo 1979435 5015267 := bstep (se 1 (by rfl) ⟨3761450, by rfl⟩ : syracuseStep 5015267 = 7522901) B7522901
theorem B3343511 : Blo 1979435 3343511 := bstep (se 1 (by rfl) ⟨2507633, by rfl⟩ : syracuseStep 3343511 = 5015267) B5015267
theorem B2229007 : Blo 1979435 2229007 := bstep (se 1 (by rfl) ⟨1671755, by rfl⟩ : syracuseStep 2229007 = 3343511) B3343511
theorem B2972009 : Blo 1979435 2972009 := bstep (se 2 (by rfl) ⟨1114503, by rfl⟩ : syracuseStep 2972009 = 2229007) B2229007
theorem B1981339 : Blo 1979435 1981339 := bstep (se 1 (by rfl) ⟨1486004, by rfl⟩ : syracuseStep 1981339 = 2972009) B2972009
theorem B11284373 : Blo 1979435 11284373 := bbase (se 6 (by rfl) ⟨264477, by rfl⟩ : syracuseStep 11284373 = 528955) (by norm_num)
theorem B7522915 : Blo 1979435 7522915 := bstep (se 1 (by rfl) ⟨5642186, by rfl⟩ : syracuseStep 7522915 = 11284373) B11284373
theorem B10030553 : Blo 1979435 10030553 := bstep (se 2 (by rfl) ⟨3761457, by rfl⟩ : syracuseStep 10030553 = 7522915) B7522915
theorem B6687035 : Blo 1979435 6687035 := bstep (se 1 (by rfl) ⟨5015276, by rfl⟩ : syracuseStep 6687035 = 10030553) B10030553
theorem B4458023 : Blo 1979435 4458023 := bstep (se 1 (by rfl) ⟨3343517, by rfl⟩ : syracuseStep 4458023 = 6687035) B6687035
theorem B2972015 : Blo 1979435 2972015 := bstep (se 1 (by rfl) ⟨2229011, by rfl⟩ : syracuseStep 2972015 = 4458023) B4458023
theorem B1981343 : Blo 1979435 1981343 := bstep (se 1 (by rfl) ⟨1486007, by rfl⟩ : syracuseStep 1981343 = 2972015) B2972015
theorem B2972021 : Blo 1979435 2972021 := bbase (se 5 (by rfl) ⟨139313, by rfl⟩ : syracuseStep 2972021 = 278627) (by norm_num)
theorem B1981347 : Blo 1979435 1981347 := bstep (se 1 (by rfl) ⟨1486010, by rfl⟩ : syracuseStep 1981347 = 2972021) B2972021
theorem B2115829 : Blo 1979435 2115829 := bbase (se 5 (by rfl) ⟨99179, by rfl⟩ : syracuseStep 2115829 = 198359) (by norm_num)
theorem B2821105 : Blo 1979435 2821105 := bstep (se 2 (by rfl) ⟨1057914, by rfl⟩ : syracuseStep 2821105 = 2115829) B2115829
theorem B3761473 : Blo 1979435 3761473 := bstep (se 2 (by rfl) ⟨1410552, by rfl⟩ : syracuseStep 3761473 = 2821105) B2821105
theorem B5015297 : Blo 1979435 5015297 := bstep (se 2 (by rfl) ⟨1880736, by rfl⟩ : syracuseStep 5015297 = 3761473) B3761473
theorem B3343531 : Blo 1979435 3343531 := bstep (se 1 (by rfl) ⟨2507648, by rfl⟩ : syracuseStep 3343531 = 5015297) B5015297
theorem B4458041 : Blo 1979435 4458041 := bstep (se 2 (by rfl) ⟨1671765, by rfl⟩ : syracuseStep 4458041 = 3343531) B3343531
theorem B2972027 : Blo 1979435 2972027 := bstep (se 1 (by rfl) ⟨2229020, by rfl⟩ : syracuseStep 2972027 = 4458041) B4458041
theorem B1981351 : Blo 1979435 1981351 := bstep (se 1 (by rfl) ⟨1486013, by rfl⟩ : syracuseStep 1981351 = 2972027) B2972027
theorem B2229025 : Blo 1979435 2229025 := bbase (se 2 (by rfl) ⟨835884, by rfl⟩ : syracuseStep 2229025 = 1671769) (by norm_num)
theorem B2972033 : Blo 1979435 2972033 := bstep (se 2 (by rfl) ⟨1114512, by rfl⟩ : syracuseStep 2972033 = 2229025) B2229025
theorem B1981355 : Blo 1979435 1981355 := bstep (se 1 (by rfl) ⟨1486016, by rfl⟩ : syracuseStep 1981355 = 2972033) B2972033
theorem B5015317 : Blo 1979435 5015317 := bbase (se 6 (by rfl) ⟨117546, by rfl⟩ : syracuseStep 5015317 = 235093) (by norm_num)
theorem B6687089 : Blo 1979435 6687089 := bstep (se 2 (by rfl) ⟨2507658, by rfl⟩ : syracuseStep 6687089 = 5015317) B5015317
theorem B4458059 : Blo 1979435 4458059 := bstep (se 1 (by rfl) ⟨3343544, by rfl⟩ : syracuseStep 4458059 = 6687089) B6687089
theorem B2972039 : Blo 1979435 2972039 := bstep (se 1 (by rfl) ⟨2229029, by rfl⟩ : syracuseStep 2972039 = 4458059) B4458059
theorem B1981359 : Blo 1979435 1981359 := bstep (se 1 (by rfl) ⟨1486019, by rfl⟩ : syracuseStep 1981359 = 2972039) B2972039
theorem B2972045 : Blo 1979435 2972045 := bbase (se 3 (by rfl) ⟨557258, by rfl⟩ : syracuseStep 2972045 = 1114517) (by norm_num)
theorem B1981363 : Blo 1979435 1981363 := bstep (se 1 (by rfl) ⟨1486022, by rfl⟩ : syracuseStep 1981363 = 2972045) B2972045
theorem B4458077 : Blo 1979435 4458077 := bbase (se 3 (by rfl) ⟨835889, by rfl⟩ : syracuseStep 4458077 = 1671779) (by norm_num)
theorem B2972051 : Blo 1979435 2972051 := bstep (se 1 (by rfl) ⟨2229038, by rfl⟩ : syracuseStep 2972051 = 4458077) B4458077
theorem B1981367 : Blo 1979435 1981367 := bstep (se 1 (by rfl) ⟨1486025, by rfl⟩ : syracuseStep 1981367 = 2972051) B2972051
theorem B3343565 : Blo 1979435 3343565 := bbase (se 3 (by rfl) ⟨626918, by rfl⟩ : syracuseStep 3343565 = 1253837) (by norm_num)
theorem B2229043 : Blo 1979435 2229043 := bstep (se 1 (by rfl) ⟨1671782, by rfl⟩ : syracuseStep 2229043 = 3343565) B3343565
theorem B2972057 : Blo 1979435 2972057 := bstep (se 2 (by rfl) ⟨1114521, by rfl⟩ : syracuseStep 2972057 = 2229043) B2229043
theorem B1981371 : Blo 1979435 1981371 := bstep (se 1 (by rfl) ⟨1486028, by rfl⟩ : syracuseStep 1981371 = 2972057) B2972057
theorem B12695125 : Blo 1979435 12695125 := bbase (se 8 (by rfl) ⟨74385, by rfl⟩ : syracuseStep 12695125 = 148771) (by norm_num)
theorem B16926833 : Blo 1979435 16926833 := bstep (se 2 (by rfl) ⟨6347562, by rfl⟩ : syracuseStep 16926833 = 12695125) B12695125
theorem B11284555 : Blo 1979435 11284555 := bstep (se 1 (by rfl) ⟨8463416, by rfl⟩ : syracuseStep 11284555 = 16926833) B16926833
theorem B15046073 : Blo 1979435 15046073 := bstep (se 2 (by rfl) ⟨5642277, by rfl⟩ : syracuseStep 15046073 = 11284555) B11284555
theorem B10030715 : Blo 1979435 10030715 := bstep (se 1 (by rfl) ⟨7523036, by rfl⟩ : syracuseStep 10030715 = 15046073) B15046073
theorem B6687143 : Blo 1979435 6687143 := bstep (se 1 (by rfl) ⟨5015357, by rfl⟩ : syracuseStep 6687143 = 10030715) B10030715
theorem B4458095 : Blo 1979435 4458095 := bstep (se 1 (by rfl) ⟨3343571, by rfl⟩ : syracuseStep 4458095 = 6687143) B6687143
theorem B2972063 : Blo 1979435 2972063 := bstep (se 1 (by rfl) ⟨2229047, by rfl⟩ : syracuseStep 2972063 = 4458095) B4458095
theorem B1981375 : Blo 1979435 1981375 := bstep (se 1 (by rfl) ⟨1486031, by rfl⟩ : syracuseStep 1981375 = 2972063) B2972063
theorem B2972069 : Blo 1979435 2972069 := bbase (se 4 (by rfl) ⟨278631, by rfl⟩ : syracuseStep 2972069 = 557263) (by norm_num)
theorem B1981379 : Blo 1979435 1981379 := bstep (se 1 (by rfl) ⟨1486034, by rfl⟩ : syracuseStep 1981379 = 2972069) B2972069
theorem B2507689 : Blo 1979435 2507689 := bbase (se 2 (by rfl) ⟨940383, by rfl⟩ : syracuseStep 2507689 = 1880767) (by norm_num)
theorem B3343585 : Blo 1979435 3343585 := bstep (se 2 (by rfl) ⟨1253844, by rfl⟩ : syracuseStep 3343585 = 2507689) B2507689
theorem B4458113 : Blo 1979435 4458113 := bstep (se 2 (by rfl) ⟨1671792, by rfl⟩ : syracuseStep 4458113 = 3343585) B3343585
theorem B2972075 : Blo 1979435 2972075 := bstep (se 1 (by rfl) ⟨2229056, by rfl⟩ : syracuseStep 2972075 = 4458113) B4458113
theorem B1981383 : Blo 1979435 1981383 := bstep (se 1 (by rfl) ⟨1486037, by rfl⟩ : syracuseStep 1981383 = 2972075) B2972075
theorem B2229061 : Blo 1979435 2229061 := bbase (se 4 (by rfl) ⟨208974, by rfl⟩ : syracuseStep 2229061 = 417949) (by norm_num)
theorem B2972081 : Blo 1979435 2972081 := bstep (se 2 (by rfl) ⟨1114530, by rfl⟩ : syracuseStep 2972081 = 2229061) B2229061
theorem B1981387 : Blo 1979435 1981387 := bstep (se 1 (by rfl) ⟨1486040, by rfl⟩ : syracuseStep 1981387 = 2972081) B2972081
theorem B3761549 : Blo 1979435 3761549 := bbase (se 3 (by rfl) ⟨705290, by rfl⟩ : syracuseStep 3761549 = 1410581) (by norm_num)
theorem B2507699 : Blo 1979435 2507699 := bstep (se 1 (by rfl) ⟨1880774, by rfl⟩ : syracuseStep 2507699 = 3761549) B3761549
theorem B6687197 : Blo 1979435 6687197 := bstep (se 3 (by rfl) ⟨1253849, by rfl⟩ : syracuseStep 6687197 = 2507699) B2507699
theorem B4458131 : Blo 1979435 4458131 := bstep (se 1 (by rfl) ⟨3343598, by rfl⟩ : syracuseStep 4458131 = 6687197) B6687197
theorem B2972087 : Blo 1979435 2972087 := bstep (se 1 (by rfl) ⟨2229065, by rfl⟩ : syracuseStep 2972087 = 4458131) B4458131
theorem B1981391 : Blo 1979435 1981391 := bstep (se 1 (by rfl) ⟨1486043, by rfl⟩ : syracuseStep 1981391 = 2972087) B2972087
theorem B2972093 : Blo 1979435 2972093 := bbase (se 3 (by rfl) ⟨557267, by rfl⟩ : syracuseStep 2972093 = 1114535) (by norm_num)
theorem B1981395 : Blo 1979435 1981395 := bstep (se 1 (by rfl) ⟨1486046, by rfl⟩ : syracuseStep 1981395 = 2972093) B2972093
theorem B4458149 : Blo 1979435 4458149 := bbase (se 4 (by rfl) ⟨417951, by rfl⟩ : syracuseStep 4458149 = 835903) (by norm_num)
theorem B2972099 : Blo 1979435 2972099 := bstep (se 1 (by rfl) ⟨2229074, by rfl⟩ : syracuseStep 2972099 = 4458149) B4458149
theorem B1981399 : Blo 1979435 1981399 := bstep (se 1 (by rfl) ⟨1486049, by rfl⟩ : syracuseStep 1981399 = 2972099) B2972099
theorem B5015429 : Blo 1979435 5015429 := bbase (se 4 (by rfl) ⟨470196, by rfl⟩ : syracuseStep 5015429 = 940393) (by norm_num)
theorem B3343619 : Blo 1979435 3343619 := bstep (se 1 (by rfl) ⟨2507714, by rfl⟩ : syracuseStep 3343619 = 5015429) B5015429
theorem B2229079 : Blo 1979435 2229079 := bstep (se 1 (by rfl) ⟨1671809, by rfl⟩ : syracuseStep 2229079 = 3343619) B3343619
theorem B2972105 : Blo 1979435 2972105 := bstep (se 2 (by rfl) ⟨1114539, by rfl⟩ : syracuseStep 2972105 = 2229079) B2229079
theorem B1981403 : Blo 1979435 1981403 := bstep (se 1 (by rfl) ⟨1486052, by rfl⟩ : syracuseStep 1981403 = 2972105) B2972105
theorem B5355845 : Blo 1979435 5355845 := bbase (se 4 (by rfl) ⟨502110, by rfl⟩ : syracuseStep 5355845 = 1004221) (by norm_num)
theorem B3570563 : Blo 1979435 3570563 := bstep (se 1 (by rfl) ⟨2677922, by rfl⟩ : syracuseStep 3570563 = 5355845) B5355845
theorem B2380375 : Blo 1979435 2380375 := bstep (se 1 (by rfl) ⟨1785281, by rfl⟩ : syracuseStep 2380375 = 3570563) B3570563
theorem B3173833 : Blo 1979435 3173833 := bstep (se 2 (by rfl) ⟨1190187, by rfl⟩ : syracuseStep 3173833 = 2380375) B2380375
theorem B4231777 : Blo 1979435 4231777 := bstep (se 2 (by rfl) ⟨1586916, by rfl⟩ : syracuseStep 4231777 = 3173833) B3173833
theorem B5642369 : Blo 1979435 5642369 := bstep (se 2 (by rfl) ⟨2115888, by rfl⟩ : syracuseStep 5642369 = 4231777) B4231777
theorem B3761579 : Blo 1979435 3761579 := bstep (se 1 (by rfl) ⟨2821184, by rfl⟩ : syracuseStep 3761579 = 5642369) B5642369
theorem B10030877 : Blo 1979435 10030877 := bstep (se 3 (by rfl) ⟨1880789, by rfl⟩ : syracuseStep 10030877 = 3761579) B3761579
theorem B6687251 : Blo 1979435 6687251 := bstep (se 1 (by rfl) ⟨5015438, by rfl⟩ : syracuseStep 6687251 = 10030877) B10030877
theorem B4458167 : Blo 1979435 4458167 := bstep (se 1 (by rfl) ⟨3343625, by rfl⟩ : syracuseStep 4458167 = 6687251) B6687251
theorem B2972111 : Blo 1979435 2972111 := bstep (se 1 (by rfl) ⟨2229083, by rfl⟩ : syracuseStep 2972111 = 4458167) B4458167
theorem B1981407 : Blo 1979435 1981407 := bstep (se 1 (by rfl) ⟨1486055, by rfl⟩ : syracuseStep 1981407 = 2972111) B2972111
theorem B2972117 : Blo 1979435 2972117 := bbase (se 7 (by rfl) ⟨34829, by rfl⟩ : syracuseStep 2972117 = 69659) (by norm_num)
theorem B1981411 : Blo 1979435 1981411 := bstep (se 1 (by rfl) ⟨1486058, by rfl⟩ : syracuseStep 1981411 = 2972117) B2972117
theorem B7523189 : Blo 1979435 7523189 := bbase (se 5 (by rfl) ⟨352649, by rfl⟩ : syracuseStep 7523189 = 705299) (by norm_num)
theorem B5015459 : Blo 1979435 5015459 := bstep (se 1 (by rfl) ⟨3761594, by rfl⟩ : syracuseStep 5015459 = 7523189) B7523189
theorem B3343639 : Blo 1979435 3343639 := bstep (se 1 (by rfl) ⟨2507729, by rfl⟩ : syracuseStep 3343639 = 5015459) B5015459
theorem B4458185 : Blo 1979435 4458185 := bstep (se 2 (by rfl) ⟨1671819, by rfl⟩ : syracuseStep 4458185 = 3343639) B3343639
theorem B2972123 : Blo 1979435 2972123 := bstep (se 1 (by rfl) ⟨2229092, by rfl⟩ : syracuseStep 2972123 = 4458185) B4458185
theorem B1981415 : Blo 1979435 1981415 := bstep (se 1 (by rfl) ⟨1486061, by rfl⟩ : syracuseStep 1981415 = 2972123) B2972123
theorem B2229097 : Blo 1979435 2229097 := bbase (se 2 (by rfl) ⟨835911, by rfl⟩ : syracuseStep 2229097 = 1671823) (by norm_num)
theorem B2972129 : Blo 1979435 2972129 := bstep (se 2 (by rfl) ⟨1114548, by rfl⟩ : syracuseStep 2972129 = 2229097) B2229097
theorem B1981419 : Blo 1979435 1981419 := bstep (se 1 (by rfl) ⟨1486064, by rfl⟩ : syracuseStep 1981419 = 2972129) B2972129
theorem B6347717 : Blo 1979435 6347717 := bbase (se 4 (by rfl) ⟨595098, by rfl⟩ : syracuseStep 6347717 = 1190197) (by norm_num)
theorem B4231811 : Blo 1979435 4231811 := bstep (se 1 (by rfl) ⟨3173858, by rfl⟩ : syracuseStep 4231811 = 6347717) B6347717
theorem B11284829 : Blo 1979435 11284829 := bstep (se 3 (by rfl) ⟨2115905, by rfl⟩ : syracuseStep 11284829 = 4231811) B4231811
theorem B7523219 : Blo 1979435 7523219 := bstep (se 1 (by rfl) ⟨5642414, by rfl⟩ : syracuseStep 7523219 = 11284829) B11284829
theorem B5015479 : Blo 1979435 5015479 := bstep (se 1 (by rfl) ⟨3761609, by rfl⟩ : syracuseStep 5015479 = 7523219) B7523219
theorem B6687305 : Blo 1979435 6687305 := bstep (se 2 (by rfl) ⟨2507739, by rfl⟩ : syracuseStep 6687305 = 5015479) B5015479
theorem B4458203 : Blo 1979435 4458203 := bstep (se 1 (by rfl) ⟨3343652, by rfl⟩ : syracuseStep 4458203 = 6687305) B6687305
theorem B2972135 : Blo 1979435 2972135 := bstep (se 1 (by rfl) ⟨2229101, by rfl⟩ : syracuseStep 2972135 = 4458203) B4458203
theorem B1981423 : Blo 1979435 1981423 := bstep (se 1 (by rfl) ⟨1486067, by rfl⟩ : syracuseStep 1981423 = 2972135) B2972135
theorem B2972141 : Blo 1979435 2972141 := bbase (se 3 (by rfl) ⟨557276, by rfl⟩ : syracuseStep 2972141 = 1114553) (by norm_num)
theorem B1981427 : Blo 1979435 1981427 := bstep (se 1 (by rfl) ⟨1486070, by rfl⟩ : syracuseStep 1981427 = 2972141) B2972141
theorem B4458221 : Blo 1979435 4458221 := bbase (se 3 (by rfl) ⟨835916, by rfl⟩ : syracuseStep 4458221 = 1671833) (by norm_num)
theorem B2972147 : Blo 1979435 2972147 := bstep (se 1 (by rfl) ⟨2229110, by rfl⟩ : syracuseStep 2972147 = 4458221) B4458221
theorem B1981431 : Blo 1979435 1981431 := bstep (se 1 (by rfl) ⟨1486073, by rfl⟩ : syracuseStep 1981431 = 2972147) B2972147
theorem B4519061 : Blo 1979435 4519061 := bbase (se 6 (by rfl) ⟨105915, by rfl⟩ : syracuseStep 4519061 = 211831) (by norm_num)
theorem B3012707 : Blo 1979435 3012707 := bstep (se 1 (by rfl) ⟨2259530, by rfl⟩ : syracuseStep 3012707 = 4519061) B4519061
theorem B2008471 : Blo 1979435 2008471 := bstep (se 1 (by rfl) ⟨1506353, by rfl⟩ : syracuseStep 2008471 = 3012707) B3012707
theorem B2677961 : Blo 1979435 2677961 := bstep (se 2 (by rfl) ⟨1004235, by rfl⟩ : syracuseStep 2677961 = 2008471) B2008471
theorem B7141229 : Blo 1979435 7141229 := bstep (se 3 (by rfl) ⟨1338980, by rfl⟩ : syracuseStep 7141229 = 2677961) B2677961
theorem B4760819 : Blo 1979435 4760819 := bstep (se 1 (by rfl) ⟨3570614, by rfl⟩ : syracuseStep 4760819 = 7141229) B7141229
theorem B3173879 : Blo 1979435 3173879 := bstep (se 1 (by rfl) ⟨2380409, by rfl⟩ : syracuseStep 3173879 = 4760819) B4760819
theorem B2115919 : Blo 1979435 2115919 := bstep (se 1 (by rfl) ⟨1586939, by rfl⟩ : syracuseStep 2115919 = 3173879) B3173879
theorem B2821225 : Blo 1979435 2821225 := bstep (se 2 (by rfl) ⟨1057959, by rfl⟩ : syracuseStep 2821225 = 2115919) B2115919
theorem B3761633 : Blo 1979435 3761633 := bstep (se 2 (by rfl) ⟨1410612, by rfl⟩ : syracuseStep 3761633 = 2821225) B2821225
theorem B2507755 : Blo 1979435 2507755 := bstep (se 1 (by rfl) ⟨1880816, by rfl⟩ : syracuseStep 2507755 = 3761633) B3761633
theorem B3343673 : Blo 1979435 3343673 := bstep (se 2 (by rfl) ⟨1253877, by rfl⟩ : syracuseStep 3343673 = 2507755) B2507755
theorem B2229115 : Blo 1979435 2229115 := bstep (se 1 (by rfl) ⟨1671836, by rfl⟩ : syracuseStep 2229115 = 3343673) B3343673
theorem B2972153 : Blo 1979435 2972153 := bstep (se 2 (by rfl) ⟨1114557, by rfl⟩ : syracuseStep 2972153 = 2229115) B2229115
theorem B1981435 : Blo 1979435 1981435 := bstep (se 1 (by rfl) ⟨1486076, by rfl⟩ : syracuseStep 1981435 = 2972153) B2972153
theorem C0 (j : ℕ) (h1 : 494858 ≤ j) (h2 : j ≤ 495358) : Blo 1979435 (4 * j + 3) := by
  interval_cases j
  · exact B1979435
  · exact B1979439
  · exact B1979443
  · exact B1979447
  · exact B1979451
  · exact B1979455
  · exact B1979459
  · exact B1979463
  · exact B1979467
  · exact B1979471
  · exact B1979475
  · exact B1979479
  · exact B1979483
  · exact B1979487
  · exact B1979491
  · exact B1979495
  · exact B1979499
  · exact B1979503
  · exact B1979507
  · exact B1979511
  · exact B1979515
  · exact B1979519
  · exact B1979523
  · exact B1979527
  · exact B1979531
  · exact B1979535
  · exact B1979539
  · exact B1979543
  · exact B1979547
  · exact B1979551
  · exact B1979555
  · exact B1979559
  · exact B1979563
  · exact B1979567
  · exact B1979571
  · exact B1979575
  · exact B1979579
  · exact B1979583
  · exact B1979587
  · exact B1979591
  · exact B1979595
  · exact B1979599
  · exact B1979603
  · exact B1979607
  · exact B1979611
  · exact B1979615
  · exact B1979619
  · exact B1979623
  · exact B1979627
  · exact B1979631
  · exact B1979635
  · exact B1979639
  · exact B1979643
  · exact B1979647
  · exact B1979651
  · exact B1979655
  · exact B1979659
  · exact B1979663
  · exact B1979667
  · exact B1979671
  · exact B1979675
  · exact B1979679
  · exact B1979683
  · exact B1979687
  · exact B1979691
  · exact B1979695
  · exact B1979699
  · exact B1979703
  · exact B1979707
  · exact B1979711
  · exact B1979715
  · exact B1979719
  · exact B1979723
  · exact B1979727
  · exact B1979731
  · exact B1979735
  · exact B1979739
  · exact B1979743
  · exact B1979747
  · exact B1979751
  · exact B1979755
  · exact B1979759
  · exact B1979763
  · exact B1979767
  · exact B1979771
  · exact B1979775
  · exact B1979779
  · exact B1979783
  · exact B1979787
  · exact B1979791
  · exact B1979795
  · exact B1979799
  · exact B1979803
  · exact B1979807
  · exact B1979811
  · exact B1979815
  · exact B1979819
  · exact B1979823
  · exact B1979827
  · exact B1979831
  · exact B1979835
  · exact B1979839
  · exact B1979843
  · exact B1979847
  · exact B1979851
  · exact B1979855
  · exact B1979859
  · exact B1979863
  · exact B1979867
  · exact B1979871
  · exact B1979875
  · exact B1979879
  · exact B1979883
  · exact B1979887
  · exact B1979891
  · exact B1979895
  · exact B1979899
  · exact B1979903
  · exact B1979907
  · exact B1979911
  · exact B1979915
  · exact B1979919
  · exact B1979923
  · exact B1979927
  · exact B1979931
  · exact B1979935
  · exact B1979939
  · exact B1979943
  · exact B1979947
  · exact B1979951
  · exact B1979955
  · exact B1979959
  · exact B1979963
  · exact B1979967
  · exact B1979971
  · exact B1979975
  · exact B1979979
  · exact B1979983
  · exact B1979987
  · exact B1979991
  · exact B1979995
  · exact B1979999
  · exact B1980003
  · exact B1980007
  · exact B1980011
  · exact B1980015
  · exact B1980019
  · exact B1980023
  · exact B1980027
  · exact B1980031
  · exact B1980035
  · exact B1980039
  · exact B1980043
  · exact B1980047
  · exact B1980051
  · exact B1980055
  · exact B1980059
  · exact B1980063
  · exact B1980067
  · exact B1980071
  · exact B1980075
  · exact B1980079
  · exact B1980083
  · exact B1980087
  · exact B1980091
  · exact B1980095
  · exact B1980099
  · exact B1980103
  · exact B1980107
  · exact B1980111
  · exact B1980115
  · exact B1980119
  · exact B1980123
  · exact B1980127
  · exact B1980131
  · exact B1980135
  · exact B1980139
  · exact B1980143
  · exact B1980147
  · exact B1980151
  · exact B1980155
  · exact B1980159
  · exact B1980163
  · exact B1980167
  · exact B1980171
  · exact B1980175
  · exact B1980179
  · exact B1980183
  · exact B1980187
  · exact B1980191
  · exact B1980195
  · exact B1980199
  · exact B1980203
  · exact B1980207
  · exact B1980211
  · exact B1980215
  · exact B1980219
  · exact B1980223
  · exact B1980227
  · exact B1980231
  · exact B1980235
  · exact B1980239
  · exact B1980243
  · exact B1980247
  · exact B1980251
  · exact B1980255
  · exact B1980259
  · exact B1980263
  · exact B1980267
  · exact B1980271
  · exact B1980275
  · exact B1980279
  · exact B1980283
  · exact B1980287
  · exact B1980291
  · exact B1980295
  · exact B1980299
  · exact B1980303
  · exact B1980307
  · exact B1980311
  · exact B1980315
  · exact B1980319
  · exact B1980323
  · exact B1980327
  · exact B1980331
  · exact B1980335
  · exact B1980339
  · exact B1980343
  · exact B1980347
  · exact B1980351
  · exact B1980355
  · exact B1980359
  · exact B1980363
  · exact B1980367
  · exact B1980371
  · exact B1980375
  · exact B1980379
  · exact B1980383
  · exact B1980387
  · exact B1980391
  · exact B1980395
  · exact B1980399
  · exact B1980403
  · exact B1980407
  · exact B1980411
  · exact B1980415
  · exact B1980419
  · exact B1980423
  · exact B1980427
  · exact B1980431
  · exact B1980435
  · exact B1980439
  · exact B1980443
  · exact B1980447
  · exact B1980451
  · exact B1980455
  · exact B1980459
  · exact B1980463
  · exact B1980467
  · exact B1980471
  · exact B1980475
  · exact B1980479
  · exact B1980483
  · exact B1980487
  · exact B1980491
  · exact B1980495
  · exact B1980499
  · exact B1980503
  · exact B1980507
  · exact B1980511
  · exact B1980515
  · exact B1980519
  · exact B1980523
  · exact B1980527
  · exact B1980531
  · exact B1980535
  · exact B1980539
  · exact B1980543
  · exact B1980547
  · exact B1980551
  · exact B1980555
  · exact B1980559
  · exact B1980563
  · exact B1980567
  · exact B1980571
  · exact B1980575
  · exact B1980579
  · exact B1980583
  · exact B1980587
  · exact B1980591
  · exact B1980595
  · exact B1980599
  · exact B1980603
  · exact B1980607
  · exact B1980611
  · exact B1980615
  · exact B1980619
  · exact B1980623
  · exact B1980627
  · exact B1980631
  · exact B1980635
  · exact B1980639
  · exact B1980643
  · exact B1980647
  · exact B1980651
  · exact B1980655
  · exact B1980659
  · exact B1980663
  · exact B1980667
  · exact B1980671
  · exact B1980675
  · exact B1980679
  · exact B1980683
  · exact B1980687
  · exact B1980691
  · exact B1980695
  · exact B1980699
  · exact B1980703
  · exact B1980707
  · exact B1980711
  · exact B1980715
  · exact B1980719
  · exact B1980723
  · exact B1980727
  · exact B1980731
  · exact B1980735
  · exact B1980739
  · exact B1980743
  · exact B1980747
  · exact B1980751
  · exact B1980755
  · exact B1980759
  · exact B1980763
  · exact B1980767
  · exact B1980771
  · exact B1980775
  · exact B1980779
  · exact B1980783
  · exact B1980787
  · exact B1980791
  · exact B1980795
  · exact B1980799
  · exact B1980803
  · exact B1980807
  · exact B1980811
  · exact B1980815
  · exact B1980819
  · exact B1980823
  · exact B1980827
  · exact B1980831
  · exact B1980835
  · exact B1980839
  · exact B1980843
  · exact B1980847
  · exact B1980851
  · exact B1980855
  · exact B1980859
  · exact B1980863
  · exact B1980867
  · exact B1980871
  · exact B1980875
  · exact B1980879
  · exact B1980883
  · exact B1980887
  · exact B1980891
  · exact B1980895
  · exact B1980899
  · exact B1980903
  · exact B1980907
  · exact B1980911
  · exact B1980915
  · exact B1980919
  · exact B1980923
  · exact B1980927
  · exact B1980931
  · exact B1980935
  · exact B1980939
  · exact B1980943
  · exact B1980947
  · exact B1980951
  · exact B1980955
  · exact B1980959
  · exact B1980963
  · exact B1980967
  · exact B1980971
  · exact B1980975
  · exact B1980979
  · exact B1980983
  · exact B1980987
  · exact B1980991
  · exact B1980995
  · exact B1980999
  · exact B1981003
  · exact B1981007
  · exact B1981011
  · exact B1981015
  · exact B1981019
  · exact B1981023
  · exact B1981027
  · exact B1981031
  · exact B1981035
  · exact B1981039
  · exact B1981043
  · exact B1981047
  · exact B1981051
  · exact B1981055
  · exact B1981059
  · exact B1981063
  · exact B1981067
  · exact B1981071
  · exact B1981075
  · exact B1981079
  · exact B1981083
  · exact B1981087
  · exact B1981091
  · exact B1981095
  · exact B1981099
  · exact B1981103
  · exact B1981107
  · exact B1981111
  · exact B1981115
  · exact B1981119
  · exact B1981123
  · exact B1981127
  · exact B1981131
  · exact B1981135
  · exact B1981139
  · exact B1981143
  · exact B1981147
  · exact B1981151
  · exact B1981155
  · exact B1981159
  · exact B1981163
  · exact B1981167
  · exact B1981171
  · exact B1981175
  · exact B1981179
  · exact B1981183
  · exact B1981187
  · exact B1981191
  · exact B1981195
  · exact B1981199
  · exact B1981203
  · exact B1981207
  · exact B1981211
  · exact B1981215
  · exact B1981219
  · exact B1981223
  · exact B1981227
  · exact B1981231
  · exact B1981235
  · exact B1981239
  · exact B1981243
  · exact B1981247
  · exact B1981251
  · exact B1981255
  · exact B1981259
  · exact B1981263
  · exact B1981267
  · exact B1981271
  · exact B1981275
  · exact B1981279
  · exact B1981283
  · exact B1981287
  · exact B1981291
  · exact B1981295
  · exact B1981299
  · exact B1981303
  · exact B1981307
  · exact B1981311
  · exact B1981315
  · exact B1981319
  · exact B1981323
  · exact B1981327
  · exact B1981331
  · exact B1981335
  · exact B1981339
  · exact B1981343
  · exact B1981347
  · exact B1981351
  · exact B1981355
  · exact B1981359
  · exact B1981363
  · exact B1981367
  · exact B1981371
  · exact B1981375
  · exact B1981379
  · exact B1981383
  · exact B1981387
  · exact B1981391
  · exact B1981395
  · exact B1981399
  · exact B1981403
  · exact B1981407
  · exact B1981411
  · exact B1981415
  · exact B1981419
  · exact B1981423
  · exact B1981427
  · exact B1981431
  · exact B1981435
theorem solution (m : ℕ) (hlo : 1979435 ≤ m) (hhi : m ≤ 1981435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 494858 ≤ j := by omega
    have hj2 : j ≤ 495358 := by omega
    have hb : Blo 1979435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
