-- Prove2me | solution 1 for syracuse_descends_range_2291435_2293435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:48.118384+00:00
-- url     : https://prove2.me/submissions/f0553060-3d4b-429d-a23c-e95df06f18ae

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

theorem B2577865 : Blo 2291435 2577865 := bbase (se 2 (by rfl) ⟨966699, by rfl⟩ : syracuseStep 2577865 = 1933399) (by norm_num)
theorem B3437153 : Blo 2291435 3437153 := bstep (se 2 (by rfl) ⟨1288932, by rfl⟩ : syracuseStep 3437153 = 2577865) B2577865
theorem B2291435 : Blo 2291435 2291435 := bstep (se 1 (by rfl) ⟨1718576, by rfl⟩ : syracuseStep 2291435 = 3437153) B3437153
theorem B19575701 : Blo 2291435 19575701 := bbase (se 6 (by rfl) ⟨458805, by rfl⟩ : syracuseStep 19575701 = 917611) (by norm_num)
theorem B13050467 : Blo 2291435 13050467 := bstep (se 1 (by rfl) ⟨9787850, by rfl⟩ : syracuseStep 13050467 = 19575701) B19575701
theorem B8700311 : Blo 2291435 8700311 := bstep (se 1 (by rfl) ⟨6525233, by rfl⟩ : syracuseStep 8700311 = 13050467) B13050467
theorem B5800207 : Blo 2291435 5800207 := bstep (se 1 (by rfl) ⟨4350155, by rfl⟩ : syracuseStep 5800207 = 8700311) B8700311
theorem B7733609 : Blo 2291435 7733609 := bstep (se 2 (by rfl) ⟨2900103, by rfl⟩ : syracuseStep 7733609 = 5800207) B5800207
theorem B5155739 : Blo 2291435 5155739 := bstep (se 1 (by rfl) ⟨3866804, by rfl⟩ : syracuseStep 5155739 = 7733609) B7733609
theorem B3437159 : Blo 2291435 3437159 := bstep (se 1 (by rfl) ⟨2577869, by rfl⟩ : syracuseStep 3437159 = 5155739) B5155739
theorem B2291439 : Blo 2291435 2291439 := bstep (se 1 (by rfl) ⟨1718579, by rfl⟩ : syracuseStep 2291439 = 3437159) B3437159
theorem B3437165 : Blo 2291435 3437165 := bbase (se 3 (by rfl) ⟨644468, by rfl⟩ : syracuseStep 3437165 = 1288937) (by norm_num)
theorem B2291443 : Blo 2291435 2291443 := bstep (se 1 (by rfl) ⟨1718582, by rfl⟩ : syracuseStep 2291443 = 3437165) B3437165
theorem B5155757 : Blo 2291435 5155757 := bbase (se 3 (by rfl) ⟨966704, by rfl⟩ : syracuseStep 5155757 = 1933409) (by norm_num)
theorem B3437171 : Blo 2291435 3437171 := bstep (se 1 (by rfl) ⟨2577878, by rfl⟩ : syracuseStep 3437171 = 5155757) B5155757
theorem B2291447 : Blo 2291435 2291447 := bstep (se 1 (by rfl) ⟨1718585, by rfl⟩ : syracuseStep 2291447 = 3437171) B3437171
theorem B6525269 : Blo 2291435 6525269 := bbase (se 10 (by rfl) ⟨9558, by rfl⟩ : syracuseStep 6525269 = 19117) (by norm_num)
theorem B4350179 : Blo 2291435 4350179 := bstep (se 1 (by rfl) ⟨3262634, by rfl⟩ : syracuseStep 4350179 = 6525269) B6525269
theorem B2900119 : Blo 2291435 2900119 := bstep (se 1 (by rfl) ⟨2175089, by rfl⟩ : syracuseStep 2900119 = 4350179) B4350179
theorem B3866825 : Blo 2291435 3866825 := bstep (se 2 (by rfl) ⟨1450059, by rfl⟩ : syracuseStep 3866825 = 2900119) B2900119
theorem B2577883 : Blo 2291435 2577883 := bstep (se 1 (by rfl) ⟨1933412, by rfl⟩ : syracuseStep 2577883 = 3866825) B3866825
theorem B3437177 : Blo 2291435 3437177 := bstep (se 2 (by rfl) ⟨1288941, by rfl⟩ : syracuseStep 3437177 = 2577883) B2577883
theorem B2291451 : Blo 2291435 2291451 := bstep (se 1 (by rfl) ⟨1718588, by rfl⟩ : syracuseStep 2291451 = 3437177) B3437177
theorem B8819077 : Blo 2291435 8819077 := bbase (se 4 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 8819077 = 1653577) (by norm_num)
theorem B11758769 : Blo 2291435 11758769 := bstep (se 2 (by rfl) ⟨4409538, by rfl⟩ : syracuseStep 11758769 = 8819077) B8819077
theorem B7839179 : Blo 2291435 7839179 := bstep (se 1 (by rfl) ⟨5879384, by rfl⟩ : syracuseStep 7839179 = 11758769) B11758769
theorem B5226119 : Blo 2291435 5226119 := bstep (se 1 (by rfl) ⟨3919589, by rfl⟩ : syracuseStep 5226119 = 7839179) B7839179
theorem B3484079 : Blo 2291435 3484079 := bstep (se 1 (by rfl) ⟨2613059, by rfl⟩ : syracuseStep 3484079 = 5226119) B5226119
theorem B2322719 : Blo 2291435 2322719 := bstep (se 1 (by rfl) ⟨1742039, by rfl⟩ : syracuseStep 2322719 = 3484079) B3484079
theorem B24775669 : Blo 2291435 24775669 := bstep (se 5 (by rfl) ⟨1161359, by rfl⟩ : syracuseStep 24775669 = 2322719) B2322719
theorem B33034225 : Blo 2291435 33034225 := bstep (se 2 (by rfl) ⟨12387834, by rfl⟩ : syracuseStep 33034225 = 24775669) B24775669
theorem B44045633 : Blo 2291435 44045633 := bstep (se 2 (by rfl) ⟨16517112, by rfl⟩ : syracuseStep 44045633 = 33034225) B33034225
theorem B29363755 : Blo 2291435 29363755 := bstep (se 1 (by rfl) ⟨22022816, by rfl⟩ : syracuseStep 29363755 = 44045633) B44045633
theorem B39151673 : Blo 2291435 39151673 := bstep (se 2 (by rfl) ⟨14681877, by rfl⟩ : syracuseStep 39151673 = 29363755) B29363755
theorem B26101115 : Blo 2291435 26101115 := bstep (se 1 (by rfl) ⟨19575836, by rfl⟩ : syracuseStep 26101115 = 39151673) B39151673
theorem B17400743 : Blo 2291435 17400743 := bstep (se 1 (by rfl) ⟨13050557, by rfl⟩ : syracuseStep 17400743 = 26101115) B26101115
theorem B11600495 : Blo 2291435 11600495 := bstep (se 1 (by rfl) ⟨8700371, by rfl⟩ : syracuseStep 11600495 = 17400743) B17400743
theorem B7733663 : Blo 2291435 7733663 := bstep (se 1 (by rfl) ⟨5800247, by rfl⟩ : syracuseStep 7733663 = 11600495) B11600495
theorem B5155775 : Blo 2291435 5155775 := bstep (se 1 (by rfl) ⟨3866831, by rfl⟩ : syracuseStep 5155775 = 7733663) B7733663
theorem B3437183 : Blo 2291435 3437183 := bstep (se 1 (by rfl) ⟨2577887, by rfl⟩ : syracuseStep 3437183 = 5155775) B5155775
theorem B2291455 : Blo 2291435 2291455 := bstep (se 1 (by rfl) ⟨1718591, by rfl⟩ : syracuseStep 2291455 = 3437183) B3437183
theorem B3437189 : Blo 2291435 3437189 := bbase (se 4 (by rfl) ⟨322236, by rfl⟩ : syracuseStep 3437189 = 644473) (by norm_num)
theorem B2291459 : Blo 2291435 2291459 := bstep (se 1 (by rfl) ⟨1718594, by rfl⟩ : syracuseStep 2291459 = 3437189) B3437189
theorem B3866845 : Blo 2291435 3866845 := bbase (se 3 (by rfl) ⟨725033, by rfl⟩ : syracuseStep 3866845 = 1450067) (by norm_num)
theorem B5155793 : Blo 2291435 5155793 := bstep (se 2 (by rfl) ⟨1933422, by rfl⟩ : syracuseStep 5155793 = 3866845) B3866845
theorem B3437195 : Blo 2291435 3437195 := bstep (se 1 (by rfl) ⟨2577896, by rfl⟩ : syracuseStep 3437195 = 5155793) B5155793
theorem B2291463 : Blo 2291435 2291463 := bstep (se 1 (by rfl) ⟨1718597, by rfl⟩ : syracuseStep 2291463 = 3437195) B3437195
theorem B2577901 : Blo 2291435 2577901 := bbase (se 3 (by rfl) ⟨483356, by rfl⟩ : syracuseStep 2577901 = 966713) (by norm_num)
theorem B3437201 : Blo 2291435 3437201 := bstep (se 2 (by rfl) ⟨1288950, by rfl⟩ : syracuseStep 3437201 = 2577901) B2577901
theorem B2291467 : Blo 2291435 2291467 := bstep (se 1 (by rfl) ⟨1718600, by rfl⟩ : syracuseStep 2291467 = 3437201) B3437201
theorem B7733717 : Blo 2291435 7733717 := bbase (se 7 (by rfl) ⟨90629, by rfl⟩ : syracuseStep 7733717 = 181259) (by norm_num)
theorem B5155811 : Blo 2291435 5155811 := bstep (se 1 (by rfl) ⟨3866858, by rfl⟩ : syracuseStep 5155811 = 7733717) B7733717
theorem B3437207 : Blo 2291435 3437207 := bstep (se 1 (by rfl) ⟨2577905, by rfl⟩ : syracuseStep 3437207 = 5155811) B5155811
theorem B2291471 : Blo 2291435 2291471 := bstep (se 1 (by rfl) ⟨1718603, by rfl⟩ : syracuseStep 2291471 = 3437207) B3437207
theorem B3437213 : Blo 2291435 3437213 := bbase (se 3 (by rfl) ⟨644477, by rfl⟩ : syracuseStep 3437213 = 1288955) (by norm_num)
theorem B2291475 : Blo 2291435 2291475 := bstep (se 1 (by rfl) ⟨1718606, by rfl⟩ : syracuseStep 2291475 = 3437213) B3437213
theorem B5155829 : Blo 2291435 5155829 := bbase (se 5 (by rfl) ⟨241679, by rfl⟩ : syracuseStep 5155829 = 483359) (by norm_num)
theorem B3437219 : Blo 2291435 3437219 := bstep (se 1 (by rfl) ⟨2577914, by rfl⟩ : syracuseStep 3437219 = 5155829) B5155829
theorem B2291479 : Blo 2291435 2291479 := bstep (se 1 (by rfl) ⟨1718609, by rfl⟩ : syracuseStep 2291479 = 3437219) B3437219
theorem B3096997 : Blo 2291435 3096997 := bbase (se 4 (by rfl) ⟨290343, by rfl⟩ : syracuseStep 3096997 = 580687) (by norm_num)
theorem B66069269 : Blo 2291435 66069269 := bstep (se 6 (by rfl) ⟨1548498, by rfl⟩ : syracuseStep 66069269 = 3096997) B3096997
theorem B44046179 : Blo 2291435 44046179 := bstep (se 1 (by rfl) ⟨33034634, by rfl⟩ : syracuseStep 44046179 = 66069269) B66069269
theorem B29364119 : Blo 2291435 29364119 := bstep (se 1 (by rfl) ⟨22023089, by rfl⟩ : syracuseStep 29364119 = 44046179) B44046179
theorem B19576079 : Blo 2291435 19576079 := bstep (se 1 (by rfl) ⟨14682059, by rfl⟩ : syracuseStep 19576079 = 29364119) B29364119
theorem B13050719 : Blo 2291435 13050719 := bstep (se 1 (by rfl) ⟨9788039, by rfl⟩ : syracuseStep 13050719 = 19576079) B19576079
theorem B8700479 : Blo 2291435 8700479 := bstep (se 1 (by rfl) ⟨6525359, by rfl⟩ : syracuseStep 8700479 = 13050719) B13050719
theorem B5800319 : Blo 2291435 5800319 := bstep (se 1 (by rfl) ⟨4350239, by rfl⟩ : syracuseStep 5800319 = 8700479) B8700479
theorem B3866879 : Blo 2291435 3866879 := bstep (se 1 (by rfl) ⟨2900159, by rfl⟩ : syracuseStep 3866879 = 5800319) B5800319
theorem B2577919 : Blo 2291435 2577919 := bstep (se 1 (by rfl) ⟨1933439, by rfl⟩ : syracuseStep 2577919 = 3866879) B3866879
theorem B3437225 : Blo 2291435 3437225 := bstep (se 2 (by rfl) ⟨1288959, by rfl⟩ : syracuseStep 3437225 = 2577919) B2577919
theorem B2291483 : Blo 2291435 2291483 := bstep (se 1 (by rfl) ⟨1718612, by rfl⟩ : syracuseStep 2291483 = 3437225) B3437225
theorem B3262685 : Blo 2291435 3262685 := bbase (se 3 (by rfl) ⟨611753, by rfl⟩ : syracuseStep 3262685 = 1223507) (by norm_num)
theorem B8700493 : Blo 2291435 8700493 := bstep (se 3 (by rfl) ⟨1631342, by rfl⟩ : syracuseStep 8700493 = 3262685) B3262685
theorem B11600657 : Blo 2291435 11600657 := bstep (se 2 (by rfl) ⟨4350246, by rfl⟩ : syracuseStep 11600657 = 8700493) B8700493
theorem B7733771 : Blo 2291435 7733771 := bstep (se 1 (by rfl) ⟨5800328, by rfl⟩ : syracuseStep 7733771 = 11600657) B11600657
theorem B5155847 : Blo 2291435 5155847 := bstep (se 1 (by rfl) ⟨3866885, by rfl⟩ : syracuseStep 5155847 = 7733771) B7733771
theorem B3437231 : Blo 2291435 3437231 := bstep (se 1 (by rfl) ⟨2577923, by rfl⟩ : syracuseStep 3437231 = 5155847) B5155847
theorem B2291487 : Blo 2291435 2291487 := bstep (se 1 (by rfl) ⟨1718615, by rfl⟩ : syracuseStep 2291487 = 3437231) B3437231
theorem B3437237 : Blo 2291435 3437237 := bbase (se 5 (by rfl) ⟨161120, by rfl⟩ : syracuseStep 3437237 = 322241) (by norm_num)
theorem B2291491 : Blo 2291435 2291491 := bstep (se 1 (by rfl) ⟨1718618, by rfl⟩ : syracuseStep 2291491 = 3437237) B3437237
theorem B5800349 : Blo 2291435 5800349 := bbase (se 3 (by rfl) ⟨1087565, by rfl⟩ : syracuseStep 5800349 = 2175131) (by norm_num)
theorem B3866899 : Blo 2291435 3866899 := bstep (se 1 (by rfl) ⟨2900174, by rfl⟩ : syracuseStep 3866899 = 5800349) B5800349
theorem B5155865 : Blo 2291435 5155865 := bstep (se 2 (by rfl) ⟨1933449, by rfl⟩ : syracuseStep 5155865 = 3866899) B3866899
theorem B3437243 : Blo 2291435 3437243 := bstep (se 1 (by rfl) ⟨2577932, by rfl⟩ : syracuseStep 3437243 = 5155865) B5155865
theorem B2291495 : Blo 2291435 2291495 := bstep (se 1 (by rfl) ⟨1718621, by rfl⟩ : syracuseStep 2291495 = 3437243) B3437243
theorem B2577937 : Blo 2291435 2577937 := bbase (se 2 (by rfl) ⟨966726, by rfl⟩ : syracuseStep 2577937 = 1933453) (by norm_num)
theorem B3437249 : Blo 2291435 3437249 := bstep (se 2 (by rfl) ⟨1288968, by rfl⟩ : syracuseStep 3437249 = 2577937) B2577937
theorem B2291499 : Blo 2291435 2291499 := bstep (se 1 (by rfl) ⟨1718624, by rfl⟩ : syracuseStep 2291499 = 3437249) B3437249
theorem B4350277 : Blo 2291435 4350277 := bbase (se 4 (by rfl) ⟨407838, by rfl⟩ : syracuseStep 4350277 = 815677) (by norm_num)
theorem B5800369 : Blo 2291435 5800369 := bstep (se 2 (by rfl) ⟨2175138, by rfl⟩ : syracuseStep 5800369 = 4350277) B4350277
theorem B7733825 : Blo 2291435 7733825 := bstep (se 2 (by rfl) ⟨2900184, by rfl⟩ : syracuseStep 7733825 = 5800369) B5800369
theorem B5155883 : Blo 2291435 5155883 := bstep (se 1 (by rfl) ⟨3866912, by rfl⟩ : syracuseStep 5155883 = 7733825) B7733825
theorem B3437255 : Blo 2291435 3437255 := bstep (se 1 (by rfl) ⟨2577941, by rfl⟩ : syracuseStep 3437255 = 5155883) B5155883
theorem B2291503 : Blo 2291435 2291503 := bstep (se 1 (by rfl) ⟨1718627, by rfl⟩ : syracuseStep 2291503 = 3437255) B3437255
theorem B3437261 : Blo 2291435 3437261 := bbase (se 3 (by rfl) ⟨644486, by rfl⟩ : syracuseStep 3437261 = 1288973) (by norm_num)
theorem B2291507 : Blo 2291435 2291507 := bstep (se 1 (by rfl) ⟨1718630, by rfl⟩ : syracuseStep 2291507 = 3437261) B3437261
theorem B5155901 : Blo 2291435 5155901 := bbase (se 3 (by rfl) ⟨966731, by rfl⟩ : syracuseStep 5155901 = 1933463) (by norm_num)
theorem B3437267 : Blo 2291435 3437267 := bstep (se 1 (by rfl) ⟨2577950, by rfl⟩ : syracuseStep 3437267 = 5155901) B5155901
theorem B2291511 : Blo 2291435 2291511 := bstep (se 1 (by rfl) ⟨1718633, by rfl⟩ : syracuseStep 2291511 = 3437267) B3437267
theorem B3866933 : Blo 2291435 3866933 := bbase (se 5 (by rfl) ⟨181262, by rfl⟩ : syracuseStep 3866933 = 362525) (by norm_num)
theorem B2577955 : Blo 2291435 2577955 := bstep (se 1 (by rfl) ⟨1933466, by rfl⟩ : syracuseStep 2577955 = 3866933) B3866933
theorem B3437273 : Blo 2291435 3437273 := bstep (se 2 (by rfl) ⟨1288977, by rfl⟩ : syracuseStep 3437273 = 2577955) B2577955
theorem B2291515 : Blo 2291435 2291515 := bstep (se 1 (by rfl) ⟨1718636, by rfl⟩ : syracuseStep 2291515 = 3437273) B3437273
theorem B6525461 : Blo 2291435 6525461 := bbase (se 6 (by rfl) ⟨152940, by rfl⟩ : syracuseStep 6525461 = 305881) (by norm_num)
theorem B17401229 : Blo 2291435 17401229 := bstep (se 3 (by rfl) ⟨3262730, by rfl⟩ : syracuseStep 17401229 = 6525461) B6525461
theorem B11600819 : Blo 2291435 11600819 := bstep (se 1 (by rfl) ⟨8700614, by rfl⟩ : syracuseStep 11600819 = 17401229) B17401229
theorem B7733879 : Blo 2291435 7733879 := bstep (se 1 (by rfl) ⟨5800409, by rfl⟩ : syracuseStep 7733879 = 11600819) B11600819
theorem B5155919 : Blo 2291435 5155919 := bstep (se 1 (by rfl) ⟨3866939, by rfl⟩ : syracuseStep 5155919 = 7733879) B7733879
theorem B3437279 : Blo 2291435 3437279 := bstep (se 1 (by rfl) ⟨2577959, by rfl⟩ : syracuseStep 3437279 = 5155919) B5155919
theorem B2291519 : Blo 2291435 2291519 := bstep (se 1 (by rfl) ⟨1718639, by rfl⟩ : syracuseStep 2291519 = 3437279) B3437279
theorem B3437285 : Blo 2291435 3437285 := bbase (se 4 (by rfl) ⟨322245, by rfl⟩ : syracuseStep 3437285 = 644491) (by norm_num)
theorem B2291523 : Blo 2291435 2291523 := bstep (se 1 (by rfl) ⟨1718642, by rfl⟩ : syracuseStep 2291523 = 3437285) B3437285
theorem B2447057 : Blo 2291435 2447057 := bbase (se 2 (by rfl) ⟨917646, by rfl⟩ : syracuseStep 2447057 = 1835293) (by norm_num)
theorem B6525485 : Blo 2291435 6525485 := bstep (se 3 (by rfl) ⟨1223528, by rfl⟩ : syracuseStep 6525485 = 2447057) B2447057
theorem B4350323 : Blo 2291435 4350323 := bstep (se 1 (by rfl) ⟨3262742, by rfl⟩ : syracuseStep 4350323 = 6525485) B6525485
theorem B2900215 : Blo 2291435 2900215 := bstep (se 1 (by rfl) ⟨2175161, by rfl⟩ : syracuseStep 2900215 = 4350323) B4350323
theorem B3866953 : Blo 2291435 3866953 := bstep (se 2 (by rfl) ⟨1450107, by rfl⟩ : syracuseStep 3866953 = 2900215) B2900215
theorem B5155937 : Blo 2291435 5155937 := bstep (se 2 (by rfl) ⟨1933476, by rfl⟩ : syracuseStep 5155937 = 3866953) B3866953
theorem B3437291 : Blo 2291435 3437291 := bstep (se 1 (by rfl) ⟨2577968, by rfl⟩ : syracuseStep 3437291 = 5155937) B5155937
theorem B2291527 : Blo 2291435 2291527 := bstep (se 1 (by rfl) ⟨1718645, by rfl⟩ : syracuseStep 2291527 = 3437291) B3437291
theorem B2577973 : Blo 2291435 2577973 := bbase (se 5 (by rfl) ⟨120842, by rfl⟩ : syracuseStep 2577973 = 241685) (by norm_num)
theorem B3437297 : Blo 2291435 3437297 := bstep (se 2 (by rfl) ⟨1288986, by rfl⟩ : syracuseStep 3437297 = 2577973) B2577973
theorem B2291531 : Blo 2291435 2291531 := bstep (se 1 (by rfl) ⟨1718648, by rfl⟩ : syracuseStep 2291531 = 3437297) B3437297
theorem B2900225 : Blo 2291435 2900225 := bbase (se 2 (by rfl) ⟨1087584, by rfl⟩ : syracuseStep 2900225 = 2175169) (by norm_num)
theorem B7733933 : Blo 2291435 7733933 := bstep (se 3 (by rfl) ⟨1450112, by rfl⟩ : syracuseStep 7733933 = 2900225) B2900225
theorem B5155955 : Blo 2291435 5155955 := bstep (se 1 (by rfl) ⟨3866966, by rfl⟩ : syracuseStep 5155955 = 7733933) B7733933
theorem B3437303 : Blo 2291435 3437303 := bstep (se 1 (by rfl) ⟨2577977, by rfl⟩ : syracuseStep 3437303 = 5155955) B5155955
theorem B2291535 : Blo 2291435 2291535 := bstep (se 1 (by rfl) ⟨1718651, by rfl⟩ : syracuseStep 2291535 = 3437303) B3437303
theorem B3437309 : Blo 2291435 3437309 := bbase (se 3 (by rfl) ⟨644495, by rfl⟩ : syracuseStep 3437309 = 1288991) (by norm_num)
theorem B2291539 : Blo 2291435 2291539 := bstep (se 1 (by rfl) ⟨1718654, by rfl⟩ : syracuseStep 2291539 = 3437309) B3437309
theorem B5155973 : Blo 2291435 5155973 := bbase (se 4 (by rfl) ⟨483372, by rfl⟩ : syracuseStep 5155973 = 966745) (by norm_num)
theorem B3437315 : Blo 2291435 3437315 := bstep (se 1 (by rfl) ⟨2577986, by rfl⟩ : syracuseStep 3437315 = 5155973) B5155973
theorem B2291543 : Blo 2291435 2291543 := bstep (se 1 (by rfl) ⟨1718657, by rfl⟩ : syracuseStep 2291543 = 3437315) B3437315
theorem B4894157 : Blo 2291435 4894157 := bbase (se 3 (by rfl) ⟨917654, by rfl⟩ : syracuseStep 4894157 = 1835309) (by norm_num)
theorem B3262771 : Blo 2291435 3262771 := bstep (se 1 (by rfl) ⟨2447078, by rfl⟩ : syracuseStep 3262771 = 4894157) B4894157
theorem B4350361 : Blo 2291435 4350361 := bstep (se 2 (by rfl) ⟨1631385, by rfl⟩ : syracuseStep 4350361 = 3262771) B3262771
theorem B5800481 : Blo 2291435 5800481 := bstep (se 2 (by rfl) ⟨2175180, by rfl⟩ : syracuseStep 5800481 = 4350361) B4350361
theorem B3866987 : Blo 2291435 3866987 := bstep (se 1 (by rfl) ⟨2900240, by rfl⟩ : syracuseStep 3866987 = 5800481) B5800481
theorem B2577991 : Blo 2291435 2577991 := bstep (se 1 (by rfl) ⟨1933493, by rfl⟩ : syracuseStep 2577991 = 3866987) B3866987
theorem B3437321 : Blo 2291435 3437321 := bstep (se 2 (by rfl) ⟨1288995, by rfl⟩ : syracuseStep 3437321 = 2577991) B2577991
theorem B2291547 : Blo 2291435 2291547 := bstep (se 1 (by rfl) ⟨1718660, by rfl⟩ : syracuseStep 2291547 = 3437321) B3437321
theorem B11600981 : Blo 2291435 11600981 := bbase (se 8 (by rfl) ⟨67974, by rfl⟩ : syracuseStep 11600981 = 135949) (by norm_num)
theorem B7733987 : Blo 2291435 7733987 := bstep (se 1 (by rfl) ⟨5800490, by rfl⟩ : syracuseStep 7733987 = 11600981) B11600981
theorem B5155991 : Blo 2291435 5155991 := bstep (se 1 (by rfl) ⟨3866993, by rfl⟩ : syracuseStep 5155991 = 7733987) B7733987
theorem B3437327 : Blo 2291435 3437327 := bstep (se 1 (by rfl) ⟨2577995, by rfl⟩ : syracuseStep 3437327 = 5155991) B5155991
theorem B2291551 : Blo 2291435 2291551 := bstep (se 1 (by rfl) ⟨1718663, by rfl⟩ : syracuseStep 2291551 = 3437327) B3437327
theorem B3437333 : Blo 2291435 3437333 := bbase (se 6 (by rfl) ⟨80562, by rfl⟩ : syracuseStep 3437333 = 161125) (by norm_num)
theorem B2291555 : Blo 2291435 2291555 := bstep (se 1 (by rfl) ⟨1718666, by rfl⟩ : syracuseStep 2291555 = 3437333) B3437333
theorem B44047637 : Blo 2291435 44047637 := bbase (se 6 (by rfl) ⟨1032366, by rfl⟩ : syracuseStep 44047637 = 2064733) (by norm_num)
theorem B29365091 : Blo 2291435 29365091 := bstep (se 1 (by rfl) ⟨22023818, by rfl⟩ : syracuseStep 29365091 = 44047637) B44047637
theorem B19576727 : Blo 2291435 19576727 := bstep (se 1 (by rfl) ⟨14682545, by rfl⟩ : syracuseStep 19576727 = 29365091) B29365091
theorem B13051151 : Blo 2291435 13051151 := bstep (se 1 (by rfl) ⟨9788363, by rfl⟩ : syracuseStep 13051151 = 19576727) B19576727
theorem B8700767 : Blo 2291435 8700767 := bstep (se 1 (by rfl) ⟨6525575, by rfl⟩ : syracuseStep 8700767 = 13051151) B13051151
theorem B5800511 : Blo 2291435 5800511 := bstep (se 1 (by rfl) ⟨4350383, by rfl⟩ : syracuseStep 5800511 = 8700767) B8700767
theorem B3867007 : Blo 2291435 3867007 := bstep (se 1 (by rfl) ⟨2900255, by rfl⟩ : syracuseStep 3867007 = 5800511) B5800511
theorem B5156009 : Blo 2291435 5156009 := bstep (se 2 (by rfl) ⟨1933503, by rfl⟩ : syracuseStep 5156009 = 3867007) B3867007
theorem B3437339 : Blo 2291435 3437339 := bstep (se 1 (by rfl) ⟨2578004, by rfl⟩ : syracuseStep 3437339 = 5156009) B5156009
theorem B2291559 : Blo 2291435 2291559 := bstep (se 1 (by rfl) ⟨1718669, by rfl⟩ : syracuseStep 2291559 = 3437339) B3437339
theorem B2578009 : Blo 2291435 2578009 := bbase (se 2 (by rfl) ⟨966753, by rfl⟩ : syracuseStep 2578009 = 1933507) (by norm_num)
theorem B3437345 : Blo 2291435 3437345 := bstep (se 2 (by rfl) ⟨1289004, by rfl⟩ : syracuseStep 3437345 = 2578009) B2578009
theorem B2291563 : Blo 2291435 2291563 := bstep (se 1 (by rfl) ⟨1718672, by rfl⟩ : syracuseStep 2291563 = 3437345) B3437345
theorem B6968501 : Blo 2291435 6968501 := bbase (se 5 (by rfl) ⟨326648, by rfl⟩ : syracuseStep 6968501 = 653297) (by norm_num)
theorem B4645667 : Blo 2291435 4645667 := bstep (se 1 (by rfl) ⟨3484250, by rfl⟩ : syracuseStep 4645667 = 6968501) B6968501
theorem B3097111 : Blo 2291435 3097111 := bstep (se 1 (by rfl) ⟨2322833, by rfl⟩ : syracuseStep 3097111 = 4645667) B4645667
theorem B4129481 : Blo 2291435 4129481 := bstep (se 2 (by rfl) ⟨1548555, by rfl⟩ : syracuseStep 4129481 = 3097111) B3097111
theorem B11011949 : Blo 2291435 11011949 := bstep (se 3 (by rfl) ⟨2064740, by rfl⟩ : syracuseStep 11011949 = 4129481) B4129481
theorem B7341299 : Blo 2291435 7341299 := bstep (se 1 (by rfl) ⟨5505974, by rfl⟩ : syracuseStep 7341299 = 11011949) B11011949
theorem B4894199 : Blo 2291435 4894199 := bstep (se 1 (by rfl) ⟨3670649, by rfl⟩ : syracuseStep 4894199 = 7341299) B7341299
theorem B3262799 : Blo 2291435 3262799 := bstep (se 1 (by rfl) ⟨2447099, by rfl⟩ : syracuseStep 3262799 = 4894199) B4894199
theorem B8700797 : Blo 2291435 8700797 := bstep (se 3 (by rfl) ⟨1631399, by rfl⟩ : syracuseStep 8700797 = 3262799) B3262799
theorem B5800531 : Blo 2291435 5800531 := bstep (se 1 (by rfl) ⟨4350398, by rfl⟩ : syracuseStep 5800531 = 8700797) B8700797
theorem B7734041 : Blo 2291435 7734041 := bstep (se 2 (by rfl) ⟨2900265, by rfl⟩ : syracuseStep 7734041 = 5800531) B5800531
theorem B5156027 : Blo 2291435 5156027 := bstep (se 1 (by rfl) ⟨3867020, by rfl⟩ : syracuseStep 5156027 = 7734041) B7734041
theorem B3437351 : Blo 2291435 3437351 := bstep (se 1 (by rfl) ⟨2578013, by rfl⟩ : syracuseStep 3437351 = 5156027) B5156027
theorem B2291567 : Blo 2291435 2291567 := bstep (se 1 (by rfl) ⟨1718675, by rfl⟩ : syracuseStep 2291567 = 3437351) B3437351
theorem B3437357 : Blo 2291435 3437357 := bbase (se 3 (by rfl) ⟨644504, by rfl⟩ : syracuseStep 3437357 = 1289009) (by norm_num)
theorem B2291571 : Blo 2291435 2291571 := bstep (se 1 (by rfl) ⟨1718678, by rfl⟩ : syracuseStep 2291571 = 3437357) B3437357
theorem B5156045 : Blo 2291435 5156045 := bbase (se 3 (by rfl) ⟨966758, by rfl⟩ : syracuseStep 5156045 = 1933517) (by norm_num)
theorem B3437363 : Blo 2291435 3437363 := bstep (se 1 (by rfl) ⟨2578022, by rfl⟩ : syracuseStep 3437363 = 5156045) B5156045
theorem B2291575 : Blo 2291435 2291575 := bstep (se 1 (by rfl) ⟨1718681, by rfl⟩ : syracuseStep 2291575 = 3437363) B3437363
theorem B2900281 : Blo 2291435 2900281 := bbase (se 2 (by rfl) ⟨1087605, by rfl⟩ : syracuseStep 2900281 = 2175211) (by norm_num)
theorem B3867041 : Blo 2291435 3867041 := bstep (se 2 (by rfl) ⟨1450140, by rfl⟩ : syracuseStep 3867041 = 2900281) B2900281
theorem B2578027 : Blo 2291435 2578027 := bstep (se 1 (by rfl) ⟨1933520, by rfl⟩ : syracuseStep 2578027 = 3867041) B3867041
theorem B3437369 : Blo 2291435 3437369 := bstep (se 2 (by rfl) ⟨1289013, by rfl⟩ : syracuseStep 3437369 = 2578027) B2578027
theorem B2291579 : Blo 2291435 2291579 := bstep (se 1 (by rfl) ⟨1718684, by rfl⟩ : syracuseStep 2291579 = 3437369) B3437369
theorem B7341349 : Blo 2291435 7341349 := bbase (se 4 (by rfl) ⟨688251, by rfl⟩ : syracuseStep 7341349 = 1376503) (by norm_num)
theorem B9788465 : Blo 2291435 9788465 := bstep (se 2 (by rfl) ⟨3670674, by rfl⟩ : syracuseStep 9788465 = 7341349) B7341349
theorem B26102573 : Blo 2291435 26102573 := bstep (se 3 (by rfl) ⟨4894232, by rfl⟩ : syracuseStep 26102573 = 9788465) B9788465
theorem B17401715 : Blo 2291435 17401715 := bstep (se 1 (by rfl) ⟨13051286, by rfl⟩ : syracuseStep 17401715 = 26102573) B26102573
theorem B11601143 : Blo 2291435 11601143 := bstep (se 1 (by rfl) ⟨8700857, by rfl⟩ : syracuseStep 11601143 = 17401715) B17401715
theorem B7734095 : Blo 2291435 7734095 := bstep (se 1 (by rfl) ⟨5800571, by rfl⟩ : syracuseStep 7734095 = 11601143) B11601143
theorem B5156063 : Blo 2291435 5156063 := bstep (se 1 (by rfl) ⟨3867047, by rfl⟩ : syracuseStep 5156063 = 7734095) B7734095
theorem B3437375 : Blo 2291435 3437375 := bstep (se 1 (by rfl) ⟨2578031, by rfl⟩ : syracuseStep 3437375 = 5156063) B5156063
theorem B2291583 : Blo 2291435 2291583 := bstep (se 1 (by rfl) ⟨1718687, by rfl⟩ : syracuseStep 2291583 = 3437375) B3437375
theorem B3437381 : Blo 2291435 3437381 := bbase (se 4 (by rfl) ⟨322254, by rfl⟩ : syracuseStep 3437381 = 644509) (by norm_num)
theorem B2291587 : Blo 2291435 2291587 := bstep (se 1 (by rfl) ⟨1718690, by rfl⟩ : syracuseStep 2291587 = 3437381) B3437381
theorem B3867061 : Blo 2291435 3867061 := bbase (se 5 (by rfl) ⟨181268, by rfl⟩ : syracuseStep 3867061 = 362537) (by norm_num)
theorem B5156081 : Blo 2291435 5156081 := bstep (se 2 (by rfl) ⟨1933530, by rfl⟩ : syracuseStep 5156081 = 3867061) B3867061
theorem B3437387 : Blo 2291435 3437387 := bstep (se 1 (by rfl) ⟨2578040, by rfl⟩ : syracuseStep 3437387 = 5156081) B5156081
theorem B2291591 : Blo 2291435 2291591 := bstep (se 1 (by rfl) ⟨1718693, by rfl⟩ : syracuseStep 2291591 = 3437387) B3437387
theorem B2578045 : Blo 2291435 2578045 := bbase (se 3 (by rfl) ⟨483383, by rfl⟩ : syracuseStep 2578045 = 966767) (by norm_num)
theorem B3437393 : Blo 2291435 3437393 := bstep (se 2 (by rfl) ⟨1289022, by rfl⟩ : syracuseStep 3437393 = 2578045) B2578045
theorem B2291595 : Blo 2291435 2291595 := bstep (se 1 (by rfl) ⟨1718696, by rfl⟩ : syracuseStep 2291595 = 3437393) B3437393
theorem B7734149 : Blo 2291435 7734149 := bbase (se 4 (by rfl) ⟨725076, by rfl⟩ : syracuseStep 7734149 = 1450153) (by norm_num)
theorem B5156099 : Blo 2291435 5156099 := bstep (se 1 (by rfl) ⟨3867074, by rfl⟩ : syracuseStep 5156099 = 7734149) B7734149
theorem B3437399 : Blo 2291435 3437399 := bstep (se 1 (by rfl) ⟨2578049, by rfl⟩ : syracuseStep 3437399 = 5156099) B5156099
theorem B2291599 : Blo 2291435 2291599 := bstep (se 1 (by rfl) ⟨1718699, by rfl⟩ : syracuseStep 2291599 = 3437399) B3437399
theorem B3437405 : Blo 2291435 3437405 := bbase (se 3 (by rfl) ⟨644513, by rfl⟩ : syracuseStep 3437405 = 1289027) (by norm_num)
theorem B2291603 : Blo 2291435 2291603 := bstep (se 1 (by rfl) ⟨1718702, by rfl⟩ : syracuseStep 2291603 = 3437405) B3437405
theorem B5156117 : Blo 2291435 5156117 := bbase (se 6 (by rfl) ⟨120846, by rfl⟩ : syracuseStep 5156117 = 241693) (by norm_num)
theorem B3437411 : Blo 2291435 3437411 := bstep (se 1 (by rfl) ⟨2578058, by rfl⟩ : syracuseStep 3437411 = 5156117) B5156117
theorem B2291607 : Blo 2291435 2291607 := bstep (se 1 (by rfl) ⟨1718705, by rfl⟩ : syracuseStep 2291607 = 3437411) B3437411
theorem B8700965 : Blo 2291435 8700965 := bbase (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) (by norm_num)
theorem B5800643 : Blo 2291435 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B3867095 : Blo 2291435 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B2578063 : Blo 2291435 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B3437417 : Blo 2291435 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B2291611 : Blo 2291435 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B4894301 : Blo 2291435 4894301 := bbase (se 3 (by rfl) ⟨917681, by rfl⟩ : syracuseStep 4894301 = 1835363) (by norm_num)
theorem B13051469 : Blo 2291435 13051469 := bstep (se 3 (by rfl) ⟨2447150, by rfl⟩ : syracuseStep 13051469 = 4894301) B4894301
theorem B8700979 : Blo 2291435 8700979 := bstep (se 1 (by rfl) ⟨6525734, by rfl⟩ : syracuseStep 8700979 = 13051469) B13051469
theorem B11601305 : Blo 2291435 11601305 := bstep (se 2 (by rfl) ⟨4350489, by rfl⟩ : syracuseStep 11601305 = 8700979) B8700979
theorem B7734203 : Blo 2291435 7734203 := bstep (se 1 (by rfl) ⟨5800652, by rfl⟩ : syracuseStep 7734203 = 11601305) B11601305
theorem B5156135 : Blo 2291435 5156135 := bstep (se 1 (by rfl) ⟨3867101, by rfl⟩ : syracuseStep 5156135 = 7734203) B7734203
theorem B3437423 : Blo 2291435 3437423 := bstep (se 1 (by rfl) ⟨2578067, by rfl⟩ : syracuseStep 3437423 = 5156135) B5156135
theorem B2291615 : Blo 2291435 2291615 := bstep (se 1 (by rfl) ⟨1718711, by rfl⟩ : syracuseStep 2291615 = 3437423) B3437423
theorem B3437429 : Blo 2291435 3437429 := bbase (se 5 (by rfl) ⟨161129, by rfl⟩ : syracuseStep 3437429 = 322259) (by norm_num)
theorem B2291619 : Blo 2291435 2291619 := bstep (se 1 (by rfl) ⟨1718714, by rfl⟩ : syracuseStep 2291619 = 3437429) B3437429
theorem B3307397 : Blo 2291435 3307397 := bbase (se 4 (by rfl) ⟨310068, by rfl⟩ : syracuseStep 3307397 = 620137) (by norm_num)
theorem B8819725 : Blo 2291435 8819725 := bstep (se 3 (by rfl) ⟨1653698, by rfl⟩ : syracuseStep 8819725 = 3307397) B3307397
theorem B11759633 : Blo 2291435 11759633 := bstep (se 2 (by rfl) ⟨4409862, by rfl⟩ : syracuseStep 11759633 = 8819725) B8819725
theorem B7839755 : Blo 2291435 7839755 := bstep (se 1 (by rfl) ⟨5879816, by rfl⟩ : syracuseStep 7839755 = 11759633) B11759633
theorem B5226503 : Blo 2291435 5226503 := bstep (se 1 (by rfl) ⟨3919877, by rfl⟩ : syracuseStep 5226503 = 7839755) B7839755
theorem B13937341 : Blo 2291435 13937341 := bstep (se 3 (by rfl) ⟨2613251, by rfl⟩ : syracuseStep 13937341 = 5226503) B5226503
theorem B18583121 : Blo 2291435 18583121 := bstep (se 2 (by rfl) ⟨6968670, by rfl⟩ : syracuseStep 18583121 = 13937341) B13937341
theorem B12388747 : Blo 2291435 12388747 := bstep (se 1 (by rfl) ⟨9291560, by rfl⟩ : syracuseStep 12388747 = 18583121) B18583121
theorem B16518329 : Blo 2291435 16518329 := bstep (se 2 (by rfl) ⟨6194373, by rfl⟩ : syracuseStep 16518329 = 12388747) B12388747
theorem B11012219 : Blo 2291435 11012219 := bstep (se 1 (by rfl) ⟨8259164, by rfl⟩ : syracuseStep 11012219 = 16518329) B16518329
theorem B7341479 : Blo 2291435 7341479 := bstep (se 1 (by rfl) ⟨5506109, by rfl⟩ : syracuseStep 7341479 = 11012219) B11012219
theorem B4894319 : Blo 2291435 4894319 := bstep (se 1 (by rfl) ⟨3670739, by rfl⟩ : syracuseStep 4894319 = 7341479) B7341479
theorem B3262879 : Blo 2291435 3262879 := bstep (se 1 (by rfl) ⟨2447159, by rfl⟩ : syracuseStep 3262879 = 4894319) B4894319
theorem B4350505 : Blo 2291435 4350505 := bstep (se 2 (by rfl) ⟨1631439, by rfl⟩ : syracuseStep 4350505 = 3262879) B3262879
theorem B5800673 : Blo 2291435 5800673 := bstep (se 2 (by rfl) ⟨2175252, by rfl⟩ : syracuseStep 5800673 = 4350505) B4350505
theorem B3867115 : Blo 2291435 3867115 := bstep (se 1 (by rfl) ⟨2900336, by rfl⟩ : syracuseStep 3867115 = 5800673) B5800673
theorem B5156153 : Blo 2291435 5156153 := bstep (se 2 (by rfl) ⟨1933557, by rfl⟩ : syracuseStep 5156153 = 3867115) B3867115
theorem B3437435 : Blo 2291435 3437435 := bstep (se 1 (by rfl) ⟨2578076, by rfl⟩ : syracuseStep 3437435 = 5156153) B5156153
theorem B2291623 : Blo 2291435 2291623 := bstep (se 1 (by rfl) ⟨1718717, by rfl⟩ : syracuseStep 2291623 = 3437435) B3437435
theorem B2578081 : Blo 2291435 2578081 := bbase (se 2 (by rfl) ⟨966780, by rfl⟩ : syracuseStep 2578081 = 1933561) (by norm_num)
theorem B3437441 : Blo 2291435 3437441 := bstep (se 2 (by rfl) ⟨1289040, by rfl⟩ : syracuseStep 3437441 = 2578081) B2578081
theorem B2291627 : Blo 2291435 2291627 := bstep (se 1 (by rfl) ⟨1718720, by rfl⟩ : syracuseStep 2291627 = 3437441) B3437441
theorem B5800693 : Blo 2291435 5800693 := bbase (se 5 (by rfl) ⟨271907, by rfl⟩ : syracuseStep 5800693 = 543815) (by norm_num)
theorem B7734257 : Blo 2291435 7734257 := bstep (se 2 (by rfl) ⟨2900346, by rfl⟩ : syracuseStep 7734257 = 5800693) B5800693
theorem B5156171 : Blo 2291435 5156171 := bstep (se 1 (by rfl) ⟨3867128, by rfl⟩ : syracuseStep 5156171 = 7734257) B7734257
theorem B3437447 : Blo 2291435 3437447 := bstep (se 1 (by rfl) ⟨2578085, by rfl⟩ : syracuseStep 3437447 = 5156171) B5156171
theorem B2291631 : Blo 2291435 2291631 := bstep (se 1 (by rfl) ⟨1718723, by rfl⟩ : syracuseStep 2291631 = 3437447) B3437447
theorem B3437453 : Blo 2291435 3437453 := bbase (se 3 (by rfl) ⟨644522, by rfl⟩ : syracuseStep 3437453 = 1289045) (by norm_num)
theorem B2291635 : Blo 2291435 2291635 := bstep (se 1 (by rfl) ⟨1718726, by rfl⟩ : syracuseStep 2291635 = 3437453) B3437453
theorem B5156189 : Blo 2291435 5156189 := bbase (se 3 (by rfl) ⟨966785, by rfl⟩ : syracuseStep 5156189 = 1933571) (by norm_num)
theorem B3437459 : Blo 2291435 3437459 := bstep (se 1 (by rfl) ⟨2578094, by rfl⟩ : syracuseStep 3437459 = 5156189) B5156189
theorem B2291639 : Blo 2291435 2291639 := bstep (se 1 (by rfl) ⟨1718729, by rfl⟩ : syracuseStep 2291639 = 3437459) B3437459
theorem B3867149 : Blo 2291435 3867149 := bbase (se 3 (by rfl) ⟨725090, by rfl⟩ : syracuseStep 3867149 = 1450181) (by norm_num)
theorem B2578099 : Blo 2291435 2578099 := bstep (se 1 (by rfl) ⟨1933574, by rfl⟩ : syracuseStep 2578099 = 3867149) B3867149
theorem B3437465 : Blo 2291435 3437465 := bstep (se 2 (by rfl) ⟨1289049, by rfl⟩ : syracuseStep 3437465 = 2578099) B2578099
theorem B2291643 : Blo 2291435 2291643 := bstep (se 1 (by rfl) ⟨1718732, by rfl⟩ : syracuseStep 2291643 = 3437465) B3437465
theorem B4645829 : Blo 2291435 4645829 := bbase (se 4 (by rfl) ⟨435546, by rfl⟩ : syracuseStep 4645829 = 871093) (by norm_num)
theorem B3097219 : Blo 2291435 3097219 := bstep (se 1 (by rfl) ⟨2322914, by rfl⟩ : syracuseStep 3097219 = 4645829) B4645829
theorem B4129625 : Blo 2291435 4129625 := bstep (se 2 (by rfl) ⟨1548609, by rfl⟩ : syracuseStep 4129625 = 3097219) B3097219
theorem B2753083 : Blo 2291435 2753083 := bstep (se 1 (by rfl) ⟨2064812, by rfl⟩ : syracuseStep 2753083 = 4129625) B4129625
theorem B3670777 : Blo 2291435 3670777 := bstep (se 2 (by rfl) ⟨1376541, by rfl⟩ : syracuseStep 3670777 = 2753083) B2753083
theorem B19577477 : Blo 2291435 19577477 := bstep (se 4 (by rfl) ⟨1835388, by rfl⟩ : syracuseStep 19577477 = 3670777) B3670777
theorem B13051651 : Blo 2291435 13051651 := bstep (se 1 (by rfl) ⟨9788738, by rfl⟩ : syracuseStep 13051651 = 19577477) B19577477
theorem B17402201 : Blo 2291435 17402201 := bstep (se 2 (by rfl) ⟨6525825, by rfl⟩ : syracuseStep 17402201 = 13051651) B13051651
theorem B11601467 : Blo 2291435 11601467 := bstep (se 1 (by rfl) ⟨8701100, by rfl⟩ : syracuseStep 11601467 = 17402201) B17402201
theorem B7734311 : Blo 2291435 7734311 := bstep (se 1 (by rfl) ⟨5800733, by rfl⟩ : syracuseStep 7734311 = 11601467) B11601467
theorem B5156207 : Blo 2291435 5156207 := bstep (se 1 (by rfl) ⟨3867155, by rfl⟩ : syracuseStep 5156207 = 7734311) B7734311
theorem B3437471 : Blo 2291435 3437471 := bstep (se 1 (by rfl) ⟨2578103, by rfl⟩ : syracuseStep 3437471 = 5156207) B5156207
theorem B2291647 : Blo 2291435 2291647 := bstep (se 1 (by rfl) ⟨1718735, by rfl⟩ : syracuseStep 2291647 = 3437471) B3437471
theorem B3437477 : Blo 2291435 3437477 := bbase (se 4 (by rfl) ⟨322263, by rfl⟩ : syracuseStep 3437477 = 644527) (by norm_num)
theorem B2291651 : Blo 2291435 2291651 := bstep (se 1 (by rfl) ⟨1718738, by rfl⟩ : syracuseStep 2291651 = 3437477) B3437477
theorem B2900377 : Blo 2291435 2900377 := bbase (se 2 (by rfl) ⟨1087641, by rfl⟩ : syracuseStep 2900377 = 2175283) (by norm_num)
theorem B3867169 : Blo 2291435 3867169 := bstep (se 2 (by rfl) ⟨1450188, by rfl⟩ : syracuseStep 3867169 = 2900377) B2900377
theorem B5156225 : Blo 2291435 5156225 := bstep (se 2 (by rfl) ⟨1933584, by rfl⟩ : syracuseStep 5156225 = 3867169) B3867169
theorem B3437483 : Blo 2291435 3437483 := bstep (se 1 (by rfl) ⟨2578112, by rfl⟩ : syracuseStep 3437483 = 5156225) B5156225
theorem B2291655 : Blo 2291435 2291655 := bstep (se 1 (by rfl) ⟨1718741, by rfl⟩ : syracuseStep 2291655 = 3437483) B3437483
theorem B2578117 : Blo 2291435 2578117 := bbase (se 4 (by rfl) ⟨241698, by rfl⟩ : syracuseStep 2578117 = 483397) (by norm_num)
theorem B3437489 : Blo 2291435 3437489 := bstep (se 2 (by rfl) ⟨1289058, by rfl⟩ : syracuseStep 3437489 = 2578117) B2578117
theorem B2291659 : Blo 2291435 2291659 := bstep (se 1 (by rfl) ⟨1718744, by rfl⟩ : syracuseStep 2291659 = 3437489) B3437489
theorem B4350581 : Blo 2291435 4350581 := bbase (se 5 (by rfl) ⟨203933, by rfl⟩ : syracuseStep 4350581 = 407867) (by norm_num)
theorem B2900387 : Blo 2291435 2900387 := bstep (se 1 (by rfl) ⟨2175290, by rfl⟩ : syracuseStep 2900387 = 4350581) B4350581
theorem B7734365 : Blo 2291435 7734365 := bstep (se 3 (by rfl) ⟨1450193, by rfl⟩ : syracuseStep 7734365 = 2900387) B2900387
theorem B5156243 : Blo 2291435 5156243 := bstep (se 1 (by rfl) ⟨3867182, by rfl⟩ : syracuseStep 5156243 = 7734365) B7734365
theorem B3437495 : Blo 2291435 3437495 := bstep (se 1 (by rfl) ⟨2578121, by rfl⟩ : syracuseStep 3437495 = 5156243) B5156243
theorem B2291663 : Blo 2291435 2291663 := bstep (se 1 (by rfl) ⟨1718747, by rfl⟩ : syracuseStep 2291663 = 3437495) B3437495
theorem B3437501 : Blo 2291435 3437501 := bbase (se 3 (by rfl) ⟨644531, by rfl⟩ : syracuseStep 3437501 = 1289063) (by norm_num)
theorem B2291667 : Blo 2291435 2291667 := bstep (se 1 (by rfl) ⟨1718750, by rfl⟩ : syracuseStep 2291667 = 3437501) B3437501
theorem B5156261 : Blo 2291435 5156261 := bbase (se 4 (by rfl) ⟨483399, by rfl⟩ : syracuseStep 5156261 = 966799) (by norm_num)
theorem B3437507 : Blo 2291435 3437507 := bstep (se 1 (by rfl) ⟨2578130, by rfl⟩ : syracuseStep 3437507 = 5156261) B5156261
theorem B2291671 : Blo 2291435 2291671 := bstep (se 1 (by rfl) ⟨1718753, by rfl⟩ : syracuseStep 2291671 = 3437507) B3437507
theorem B5800805 : Blo 2291435 5800805 := bbase (se 4 (by rfl) ⟨543825, by rfl⟩ : syracuseStep 5800805 = 1087651) (by norm_num)
theorem B3867203 : Blo 2291435 3867203 := bstep (se 1 (by rfl) ⟨2900402, by rfl⟩ : syracuseStep 3867203 = 5800805) B5800805
theorem B2578135 : Blo 2291435 2578135 := bstep (se 1 (by rfl) ⟨1933601, by rfl⟩ : syracuseStep 2578135 = 3867203) B3867203
theorem B3437513 : Blo 2291435 3437513 := bstep (se 2 (by rfl) ⟨1289067, by rfl⟩ : syracuseStep 3437513 = 2578135) B2578135
theorem B2291675 : Blo 2291435 2291675 := bstep (se 1 (by rfl) ⟨1718756, by rfl⟩ : syracuseStep 2291675 = 3437513) B3437513
theorem B3670829 : Blo 2291435 3670829 := bbase (se 3 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 3670829 = 1376561) (by norm_num)
theorem B2447219 : Blo 2291435 2447219 := bstep (se 1 (by rfl) ⟨1835414, by rfl⟩ : syracuseStep 2447219 = 3670829) B3670829
theorem B6525917 : Blo 2291435 6525917 := bstep (se 3 (by rfl) ⟨1223609, by rfl⟩ : syracuseStep 6525917 = 2447219) B2447219
theorem B4350611 : Blo 2291435 4350611 := bstep (se 1 (by rfl) ⟨3262958, by rfl⟩ : syracuseStep 4350611 = 6525917) B6525917
theorem B11601629 : Blo 2291435 11601629 := bstep (se 3 (by rfl) ⟨2175305, by rfl⟩ : syracuseStep 11601629 = 4350611) B4350611
theorem B7734419 : Blo 2291435 7734419 := bstep (se 1 (by rfl) ⟨5800814, by rfl⟩ : syracuseStep 7734419 = 11601629) B11601629
theorem B5156279 : Blo 2291435 5156279 := bstep (se 1 (by rfl) ⟨3867209, by rfl⟩ : syracuseStep 5156279 = 7734419) B7734419
theorem B3437519 : Blo 2291435 3437519 := bstep (se 1 (by rfl) ⟨2578139, by rfl⟩ : syracuseStep 3437519 = 5156279) B5156279
theorem B2291679 : Blo 2291435 2291679 := bstep (se 1 (by rfl) ⟨1718759, by rfl⟩ : syracuseStep 2291679 = 3437519) B3437519
theorem B3437525 : Blo 2291435 3437525 := bbase (se 7 (by rfl) ⟨40283, by rfl⟩ : syracuseStep 3437525 = 80567) (by norm_num)
theorem B2291683 : Blo 2291435 2291683 := bstep (se 1 (by rfl) ⟨1718762, by rfl⟩ : syracuseStep 2291683 = 3437525) B3437525
theorem B8701253 : Blo 2291435 8701253 := bbase (se 4 (by rfl) ⟨815742, by rfl⟩ : syracuseStep 8701253 = 1631485) (by norm_num)
theorem B5800835 : Blo 2291435 5800835 := bstep (se 1 (by rfl) ⟨4350626, by rfl⟩ : syracuseStep 5800835 = 8701253) B8701253
theorem B3867223 : Blo 2291435 3867223 := bstep (se 1 (by rfl) ⟨2900417, by rfl⟩ : syracuseStep 3867223 = 5800835) B5800835
theorem B5156297 : Blo 2291435 5156297 := bstep (se 2 (by rfl) ⟨1933611, by rfl⟩ : syracuseStep 5156297 = 3867223) B3867223
theorem B3437531 : Blo 2291435 3437531 := bstep (se 1 (by rfl) ⟨2578148, by rfl⟩ : syracuseStep 3437531 = 5156297) B5156297
theorem B2291687 : Blo 2291435 2291687 := bstep (se 1 (by rfl) ⟨1718765, by rfl⟩ : syracuseStep 2291687 = 3437531) B3437531
theorem B2578153 : Blo 2291435 2578153 := bbase (se 2 (by rfl) ⟨966807, by rfl⟩ : syracuseStep 2578153 = 1933615) (by norm_num)
theorem B3437537 : Blo 2291435 3437537 := bstep (se 2 (by rfl) ⟨1289076, by rfl⟩ : syracuseStep 3437537 = 2578153) B2578153
theorem B2291691 : Blo 2291435 2291691 := bstep (se 1 (by rfl) ⟨1718768, by rfl⟩ : syracuseStep 2291691 = 3437537) B3437537
theorem B13051925 : Blo 2291435 13051925 := bbase (se 6 (by rfl) ⟨305904, by rfl⟩ : syracuseStep 13051925 = 611809) (by norm_num)
theorem B8701283 : Blo 2291435 8701283 := bstep (se 1 (by rfl) ⟨6525962, by rfl⟩ : syracuseStep 8701283 = 13051925) B13051925
theorem B5800855 : Blo 2291435 5800855 := bstep (se 1 (by rfl) ⟨4350641, by rfl⟩ : syracuseStep 5800855 = 8701283) B8701283
theorem B7734473 : Blo 2291435 7734473 := bstep (se 2 (by rfl) ⟨2900427, by rfl⟩ : syracuseStep 7734473 = 5800855) B5800855
theorem B5156315 : Blo 2291435 5156315 := bstep (se 1 (by rfl) ⟨3867236, by rfl⟩ : syracuseStep 5156315 = 7734473) B7734473
theorem B3437543 : Blo 2291435 3437543 := bstep (se 1 (by rfl) ⟨2578157, by rfl⟩ : syracuseStep 3437543 = 5156315) B5156315
theorem B2291695 : Blo 2291435 2291695 := bstep (se 1 (by rfl) ⟨1718771, by rfl⟩ : syracuseStep 2291695 = 3437543) B3437543
theorem B3437549 : Blo 2291435 3437549 := bbase (se 3 (by rfl) ⟨644540, by rfl⟩ : syracuseStep 3437549 = 1289081) (by norm_num)
theorem B2291699 : Blo 2291435 2291699 := bstep (se 1 (by rfl) ⟨1718774, by rfl⟩ : syracuseStep 2291699 = 3437549) B3437549
theorem B5156333 : Blo 2291435 5156333 := bbase (se 3 (by rfl) ⟨966812, by rfl⟩ : syracuseStep 5156333 = 1933625) (by norm_num)
theorem B3437555 : Blo 2291435 3437555 := bstep (se 1 (by rfl) ⟨2578166, by rfl⟩ : syracuseStep 3437555 = 5156333) B5156333
theorem B2291703 : Blo 2291435 2291703 := bstep (se 1 (by rfl) ⟨1718777, by rfl⟩ : syracuseStep 2291703 = 3437555) B3437555
theorem B7341749 : Blo 2291435 7341749 := bbase (se 5 (by rfl) ⟨344144, by rfl⟩ : syracuseStep 7341749 = 688289) (by norm_num)
theorem B4894499 : Blo 2291435 4894499 := bstep (se 1 (by rfl) ⟨3670874, by rfl⟩ : syracuseStep 4894499 = 7341749) B7341749
theorem B3262999 : Blo 2291435 3262999 := bstep (se 1 (by rfl) ⟨2447249, by rfl⟩ : syracuseStep 3262999 = 4894499) B4894499
theorem B4350665 : Blo 2291435 4350665 := bstep (se 2 (by rfl) ⟨1631499, by rfl⟩ : syracuseStep 4350665 = 3262999) B3262999
theorem B2900443 : Blo 2291435 2900443 := bstep (se 1 (by rfl) ⟨2175332, by rfl⟩ : syracuseStep 2900443 = 4350665) B4350665
theorem B3867257 : Blo 2291435 3867257 := bstep (se 2 (by rfl) ⟨1450221, by rfl⟩ : syracuseStep 3867257 = 2900443) B2900443
theorem B2578171 : Blo 2291435 2578171 := bstep (se 1 (by rfl) ⟨1933628, by rfl⟩ : syracuseStep 2578171 = 3867257) B3867257
theorem B3437561 : Blo 2291435 3437561 := bstep (se 2 (by rfl) ⟨1289085, by rfl⟩ : syracuseStep 3437561 = 2578171) B2578171
theorem B2291707 : Blo 2291435 2291707 := bstep (se 1 (by rfl) ⟨1718780, by rfl⟩ : syracuseStep 2291707 = 3437561) B3437561
theorem B6279125 : Blo 2291435 6279125 := bbase (se 7 (by rfl) ⟨73583, by rfl⟩ : syracuseStep 6279125 = 147167) (by norm_num)
theorem B16744333 : Blo 2291435 16744333 := bstep (se 3 (by rfl) ⟨3139562, by rfl⟩ : syracuseStep 16744333 = 6279125) B6279125
theorem B22325777 : Blo 2291435 22325777 := bstep (se 2 (by rfl) ⟨8372166, by rfl⟩ : syracuseStep 22325777 = 16744333) B16744333
theorem B14883851 : Blo 2291435 14883851 := bstep (se 1 (by rfl) ⟨11162888, by rfl⟩ : syracuseStep 14883851 = 22325777) B22325777
theorem B9922567 : Blo 2291435 9922567 := bstep (se 1 (by rfl) ⟨7441925, by rfl⟩ : syracuseStep 9922567 = 14883851) B14883851
theorem B13230089 : Blo 2291435 13230089 := bstep (se 2 (by rfl) ⟨4961283, by rfl⟩ : syracuseStep 13230089 = 9922567) B9922567
theorem B8820059 : Blo 2291435 8820059 := bstep (se 1 (by rfl) ⟨6615044, by rfl⟩ : syracuseStep 8820059 = 13230089) B13230089
theorem B94080629 : Blo 2291435 94080629 := bstep (se 5 (by rfl) ⟨4410029, by rfl⟩ : syracuseStep 94080629 = 8820059) B8820059
theorem B62720419 : Blo 2291435 62720419 := bstep (se 1 (by rfl) ⟨47040314, by rfl⟩ : syracuseStep 62720419 = 94080629) B94080629
theorem B83627225 : Blo 2291435 83627225 := bstep (se 2 (by rfl) ⟨31360209, by rfl⟩ : syracuseStep 83627225 = 62720419) B62720419
theorem B55751483 : Blo 2291435 55751483 := bstep (se 1 (by rfl) ⟨41813612, by rfl⟩ : syracuseStep 55751483 = 83627225) B83627225
theorem B37167655 : Blo 2291435 37167655 := bstep (se 1 (by rfl) ⟨27875741, by rfl⟩ : syracuseStep 37167655 = 55751483) B55751483
theorem B49556873 : Blo 2291435 49556873 := bstep (se 2 (by rfl) ⟨18583827, by rfl⟩ : syracuseStep 49556873 = 37167655) B37167655
theorem B132151661 : Blo 2291435 132151661 := bstep (se 3 (by rfl) ⟨24778436, by rfl⟩ : syracuseStep 132151661 = 49556873) B49556873
theorem B88101107 : Blo 2291435 88101107 := bstep (se 1 (by rfl) ⟨66075830, by rfl⟩ : syracuseStep 88101107 = 132151661) B132151661
theorem B58734071 : Blo 2291435 58734071 := bstep (se 1 (by rfl) ⟨44050553, by rfl⟩ : syracuseStep 58734071 = 88101107) B88101107
theorem B39156047 : Blo 2291435 39156047 := bstep (se 1 (by rfl) ⟨29367035, by rfl⟩ : syracuseStep 39156047 = 58734071) B58734071
theorem B26104031 : Blo 2291435 26104031 := bstep (se 1 (by rfl) ⟨19578023, by rfl⟩ : syracuseStep 26104031 = 39156047) B39156047
theorem B17402687 : Blo 2291435 17402687 := bstep (se 1 (by rfl) ⟨13052015, by rfl⟩ : syracuseStep 17402687 = 26104031) B26104031
theorem B11601791 : Blo 2291435 11601791 := bstep (se 1 (by rfl) ⟨8701343, by rfl⟩ : syracuseStep 11601791 = 17402687) B17402687
theorem B7734527 : Blo 2291435 7734527 := bstep (se 1 (by rfl) ⟨5800895, by rfl⟩ : syracuseStep 7734527 = 11601791) B11601791
theorem B5156351 : Blo 2291435 5156351 := bstep (se 1 (by rfl) ⟨3867263, by rfl⟩ : syracuseStep 5156351 = 7734527) B7734527
theorem B3437567 : Blo 2291435 3437567 := bstep (se 1 (by rfl) ⟨2578175, by rfl⟩ : syracuseStep 3437567 = 5156351) B5156351
theorem B2291711 : Blo 2291435 2291711 := bstep (se 1 (by rfl) ⟨1718783, by rfl⟩ : syracuseStep 2291711 = 3437567) B3437567
theorem B3437573 : Blo 2291435 3437573 := bbase (se 4 (by rfl) ⟨322272, by rfl⟩ : syracuseStep 3437573 = 644545) (by norm_num)
theorem B2291715 : Blo 2291435 2291715 := bstep (se 1 (by rfl) ⟨1718786, by rfl⟩ : syracuseStep 2291715 = 3437573) B3437573
theorem B3867277 : Blo 2291435 3867277 := bbase (se 3 (by rfl) ⟨725114, by rfl⟩ : syracuseStep 3867277 = 1450229) (by norm_num)
theorem B5156369 : Blo 2291435 5156369 := bstep (se 2 (by rfl) ⟨1933638, by rfl⟩ : syracuseStep 5156369 = 3867277) B3867277
theorem B3437579 : Blo 2291435 3437579 := bstep (se 1 (by rfl) ⟨2578184, by rfl⟩ : syracuseStep 3437579 = 5156369) B5156369
theorem B2291719 : Blo 2291435 2291719 := bstep (se 1 (by rfl) ⟨1718789, by rfl⟩ : syracuseStep 2291719 = 3437579) B3437579
theorem B2578189 : Blo 2291435 2578189 := bbase (se 3 (by rfl) ⟨483410, by rfl⟩ : syracuseStep 2578189 = 966821) (by norm_num)
theorem B3437585 : Blo 2291435 3437585 := bstep (se 2 (by rfl) ⟨1289094, by rfl⟩ : syracuseStep 3437585 = 2578189) B2578189
theorem B2291723 : Blo 2291435 2291723 := bstep (se 1 (by rfl) ⟨1718792, by rfl⟩ : syracuseStep 2291723 = 3437585) B3437585
theorem B7734581 : Blo 2291435 7734581 := bbase (se 5 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 7734581 = 725117) (by norm_num)
theorem B5156387 : Blo 2291435 5156387 := bstep (se 1 (by rfl) ⟨3867290, by rfl⟩ : syracuseStep 5156387 = 7734581) B7734581
theorem B3437591 : Blo 2291435 3437591 := bstep (se 1 (by rfl) ⟨2578193, by rfl⟩ : syracuseStep 3437591 = 5156387) B5156387
theorem B2291727 : Blo 2291435 2291727 := bstep (se 1 (by rfl) ⟨1718795, by rfl⟩ : syracuseStep 2291727 = 3437591) B3437591
theorem B3437597 : Blo 2291435 3437597 := bbase (se 3 (by rfl) ⟨644549, by rfl⟩ : syracuseStep 3437597 = 1289099) (by norm_num)
theorem B2291731 : Blo 2291435 2291731 := bstep (se 1 (by rfl) ⟨1718798, by rfl⟩ : syracuseStep 2291731 = 3437597) B3437597
theorem B5156405 : Blo 2291435 5156405 := bbase (se 5 (by rfl) ⟨241706, by rfl⟩ : syracuseStep 5156405 = 483413) (by norm_num)
theorem B3437603 : Blo 2291435 3437603 := bstep (se 1 (by rfl) ⟨2578202, by rfl⟩ : syracuseStep 3437603 = 5156405) B5156405
theorem B2291735 : Blo 2291435 2291735 := bstep (se 1 (by rfl) ⟨1718801, by rfl⟩ : syracuseStep 2291735 = 3437603) B3437603
theorem B3670925 : Blo 2291435 3670925 := bbase (se 3 (by rfl) ⟨688298, by rfl⟩ : syracuseStep 3670925 = 1376597) (by norm_num)
theorem B9789133 : Blo 2291435 9789133 := bstep (se 3 (by rfl) ⟨1835462, by rfl⟩ : syracuseStep 9789133 = 3670925) B3670925
theorem B13052177 : Blo 2291435 13052177 := bstep (se 2 (by rfl) ⟨4894566, by rfl⟩ : syracuseStep 13052177 = 9789133) B9789133
theorem B8701451 : Blo 2291435 8701451 := bstep (se 1 (by rfl) ⟨6526088, by rfl⟩ : syracuseStep 8701451 = 13052177) B13052177
theorem B5800967 : Blo 2291435 5800967 := bstep (se 1 (by rfl) ⟨4350725, by rfl⟩ : syracuseStep 5800967 = 8701451) B8701451
theorem B3867311 : Blo 2291435 3867311 := bstep (se 1 (by rfl) ⟨2900483, by rfl⟩ : syracuseStep 3867311 = 5800967) B5800967
theorem B2578207 : Blo 2291435 2578207 := bstep (se 1 (by rfl) ⟨1933655, by rfl⟩ : syracuseStep 2578207 = 3867311) B3867311
theorem B3437609 : Blo 2291435 3437609 := bstep (se 2 (by rfl) ⟨1289103, by rfl⟩ : syracuseStep 3437609 = 2578207) B2578207
theorem B2291739 : Blo 2291435 2291739 := bstep (se 1 (by rfl) ⟨1718804, by rfl⟩ : syracuseStep 2291739 = 3437609) B3437609
theorem B5506397 : Blo 2291435 5506397 := bbase (se 3 (by rfl) ⟨1032449, by rfl⟩ : syracuseStep 5506397 = 2064899) (by norm_num)
theorem B3670931 : Blo 2291435 3670931 := bstep (se 1 (by rfl) ⟨2753198, by rfl⟩ : syracuseStep 3670931 = 5506397) B5506397
theorem B9789149 : Blo 2291435 9789149 := bstep (se 3 (by rfl) ⟨1835465, by rfl⟩ : syracuseStep 9789149 = 3670931) B3670931
theorem B6526099 : Blo 2291435 6526099 := bstep (se 1 (by rfl) ⟨4894574, by rfl⟩ : syracuseStep 6526099 = 9789149) B9789149
theorem B8701465 : Blo 2291435 8701465 := bstep (se 2 (by rfl) ⟨3263049, by rfl⟩ : syracuseStep 8701465 = 6526099) B6526099
theorem B11601953 : Blo 2291435 11601953 := bstep (se 2 (by rfl) ⟨4350732, by rfl⟩ : syracuseStep 11601953 = 8701465) B8701465
theorem B7734635 : Blo 2291435 7734635 := bstep (se 1 (by rfl) ⟨5800976, by rfl⟩ : syracuseStep 7734635 = 11601953) B11601953
theorem B5156423 : Blo 2291435 5156423 := bstep (se 1 (by rfl) ⟨3867317, by rfl⟩ : syracuseStep 5156423 = 7734635) B7734635
theorem B3437615 : Blo 2291435 3437615 := bstep (se 1 (by rfl) ⟨2578211, by rfl⟩ : syracuseStep 3437615 = 5156423) B5156423
theorem B2291743 : Blo 2291435 2291743 := bstep (se 1 (by rfl) ⟨1718807, by rfl⟩ : syracuseStep 2291743 = 3437615) B3437615
theorem B3437621 : Blo 2291435 3437621 := bbase (se 5 (by rfl) ⟨161138, by rfl⟩ : syracuseStep 3437621 = 322277) (by norm_num)
theorem B2291747 : Blo 2291435 2291747 := bstep (se 1 (by rfl) ⟨1718810, by rfl⟩ : syracuseStep 2291747 = 3437621) B3437621
theorem B5800997 : Blo 2291435 5800997 := bbase (se 4 (by rfl) ⟨543843, by rfl⟩ : syracuseStep 5800997 = 1087687) (by norm_num)
theorem B3867331 : Blo 2291435 3867331 := bstep (se 1 (by rfl) ⟨2900498, by rfl⟩ : syracuseStep 3867331 = 5800997) B5800997
theorem B5156441 : Blo 2291435 5156441 := bstep (se 2 (by rfl) ⟨1933665, by rfl⟩ : syracuseStep 5156441 = 3867331) B3867331
theorem B3437627 : Blo 2291435 3437627 := bstep (se 1 (by rfl) ⟨2578220, by rfl⟩ : syracuseStep 3437627 = 5156441) B5156441
theorem B2291751 : Blo 2291435 2291751 := bstep (se 1 (by rfl) ⟨1718813, by rfl⟩ : syracuseStep 2291751 = 3437627) B3437627
theorem B2578225 : Blo 2291435 2578225 := bbase (se 2 (by rfl) ⟨966834, by rfl⟩ : syracuseStep 2578225 = 1933669) (by norm_num)
theorem B3437633 : Blo 2291435 3437633 := bstep (se 2 (by rfl) ⟨1289112, by rfl⟩ : syracuseStep 3437633 = 2578225) B2578225
theorem B2291755 : Blo 2291435 2291755 := bstep (se 1 (by rfl) ⟨1718816, by rfl⟩ : syracuseStep 2291755 = 3437633) B3437633
theorem B3670957 : Blo 2291435 3670957 := bbase (se 3 (by rfl) ⟨688304, by rfl⟩ : syracuseStep 3670957 = 1376609) (by norm_num)
theorem B4894609 : Blo 2291435 4894609 := bstep (se 2 (by rfl) ⟨1835478, by rfl⟩ : syracuseStep 4894609 = 3670957) B3670957
theorem B6526145 : Blo 2291435 6526145 := bstep (se 2 (by rfl) ⟨2447304, by rfl⟩ : syracuseStep 6526145 = 4894609) B4894609
theorem B4350763 : Blo 2291435 4350763 := bstep (se 1 (by rfl) ⟨3263072, by rfl⟩ : syracuseStep 4350763 = 6526145) B6526145
theorem B5801017 : Blo 2291435 5801017 := bstep (se 2 (by rfl) ⟨2175381, by rfl⟩ : syracuseStep 5801017 = 4350763) B4350763
theorem B7734689 : Blo 2291435 7734689 := bstep (se 2 (by rfl) ⟨2900508, by rfl⟩ : syracuseStep 7734689 = 5801017) B5801017
theorem B5156459 : Blo 2291435 5156459 := bstep (se 1 (by rfl) ⟨3867344, by rfl⟩ : syracuseStep 5156459 = 7734689) B7734689
theorem B3437639 : Blo 2291435 3437639 := bstep (se 1 (by rfl) ⟨2578229, by rfl⟩ : syracuseStep 3437639 = 5156459) B5156459
theorem B2291759 : Blo 2291435 2291759 := bstep (se 1 (by rfl) ⟨1718819, by rfl⟩ : syracuseStep 2291759 = 3437639) B3437639
theorem B3437645 : Blo 2291435 3437645 := bbase (se 3 (by rfl) ⟨644558, by rfl⟩ : syracuseStep 3437645 = 1289117) (by norm_num)
theorem B2291763 : Blo 2291435 2291763 := bstep (se 1 (by rfl) ⟨1718822, by rfl⟩ : syracuseStep 2291763 = 3437645) B3437645
theorem B5156477 : Blo 2291435 5156477 := bbase (se 3 (by rfl) ⟨966839, by rfl⟩ : syracuseStep 5156477 = 1933679) (by norm_num)
theorem B3437651 : Blo 2291435 3437651 := bstep (se 1 (by rfl) ⟨2578238, by rfl⟩ : syracuseStep 3437651 = 5156477) B5156477
theorem B2291767 : Blo 2291435 2291767 := bstep (se 1 (by rfl) ⟨1718825, by rfl⟩ : syracuseStep 2291767 = 3437651) B3437651
theorem B3867365 : Blo 2291435 3867365 := bbase (se 4 (by rfl) ⟨362565, by rfl⟩ : syracuseStep 3867365 = 725131) (by norm_num)
theorem B2578243 : Blo 2291435 2578243 := bstep (se 1 (by rfl) ⟨1933682, by rfl⟩ : syracuseStep 2578243 = 3867365) B3867365
theorem B3437657 : Blo 2291435 3437657 := bstep (se 2 (by rfl) ⟨1289121, by rfl⟩ : syracuseStep 3437657 = 2578243) B2578243
theorem B2291771 : Blo 2291435 2291771 := bstep (se 1 (by rfl) ⟨1718828, by rfl⟩ : syracuseStep 2291771 = 3437657) B3437657
theorem B2753237 : Blo 2291435 2753237 := bbase (se 7 (by rfl) ⟨32264, by rfl⟩ : syracuseStep 2753237 = 64529) (by norm_num)
theorem B7341965 : Blo 2291435 7341965 := bstep (se 3 (by rfl) ⟨1376618, by rfl⟩ : syracuseStep 7341965 = 2753237) B2753237
theorem B4894643 : Blo 2291435 4894643 := bstep (se 1 (by rfl) ⟨3670982, by rfl⟩ : syracuseStep 4894643 = 7341965) B7341965
theorem B3263095 : Blo 2291435 3263095 := bstep (se 1 (by rfl) ⟨2447321, by rfl⟩ : syracuseStep 3263095 = 4894643) B4894643
theorem B17403173 : Blo 2291435 17403173 := bstep (se 4 (by rfl) ⟨1631547, by rfl⟩ : syracuseStep 17403173 = 3263095) B3263095
theorem B11602115 : Blo 2291435 11602115 := bstep (se 1 (by rfl) ⟨8701586, by rfl⟩ : syracuseStep 11602115 = 17403173) B17403173
theorem B7734743 : Blo 2291435 7734743 := bstep (se 1 (by rfl) ⟨5801057, by rfl⟩ : syracuseStep 7734743 = 11602115) B11602115
theorem B5156495 : Blo 2291435 5156495 := bstep (se 1 (by rfl) ⟨3867371, by rfl⟩ : syracuseStep 5156495 = 7734743) B7734743
theorem B3437663 : Blo 2291435 3437663 := bstep (se 1 (by rfl) ⟨2578247, by rfl⟩ : syracuseStep 3437663 = 5156495) B5156495
theorem B2291775 : Blo 2291435 2291775 := bstep (se 1 (by rfl) ⟨1718831, by rfl⟩ : syracuseStep 2291775 = 3437663) B3437663
theorem B3437669 : Blo 2291435 3437669 := bbase (se 4 (by rfl) ⟨322281, by rfl⟩ : syracuseStep 3437669 = 644563) (by norm_num)
theorem B2291779 : Blo 2291435 2291779 := bstep (se 1 (by rfl) ⟨1718834, by rfl⟩ : syracuseStep 2291779 = 3437669) B3437669
theorem B4894661 : Blo 2291435 4894661 := bbase (se 4 (by rfl) ⟨458874, by rfl⟩ : syracuseStep 4894661 = 917749) (by norm_num)
theorem B3263107 : Blo 2291435 3263107 := bstep (se 1 (by rfl) ⟨2447330, by rfl⟩ : syracuseStep 3263107 = 4894661) B4894661
theorem B4350809 : Blo 2291435 4350809 := bstep (se 2 (by rfl) ⟨1631553, by rfl⟩ : syracuseStep 4350809 = 3263107) B3263107
theorem B2900539 : Blo 2291435 2900539 := bstep (se 1 (by rfl) ⟨2175404, by rfl⟩ : syracuseStep 2900539 = 4350809) B4350809
theorem B3867385 : Blo 2291435 3867385 := bstep (se 2 (by rfl) ⟨1450269, by rfl⟩ : syracuseStep 3867385 = 2900539) B2900539
theorem B5156513 : Blo 2291435 5156513 := bstep (se 2 (by rfl) ⟨1933692, by rfl⟩ : syracuseStep 5156513 = 3867385) B3867385
theorem B3437675 : Blo 2291435 3437675 := bstep (se 1 (by rfl) ⟨2578256, by rfl⟩ : syracuseStep 3437675 = 5156513) B5156513
theorem B2291783 : Blo 2291435 2291783 := bstep (se 1 (by rfl) ⟨1718837, by rfl⟩ : syracuseStep 2291783 = 3437675) B3437675
theorem B2578261 : Blo 2291435 2578261 := bbase (se 9 (by rfl) ⟨7553, by rfl⟩ : syracuseStep 2578261 = 15107) (by norm_num)
theorem B3437681 : Blo 2291435 3437681 := bstep (se 2 (by rfl) ⟨1289130, by rfl⟩ : syracuseStep 3437681 = 2578261) B2578261
theorem B2291787 : Blo 2291435 2291787 := bstep (se 1 (by rfl) ⟨1718840, by rfl⟩ : syracuseStep 2291787 = 3437681) B3437681
theorem B2900549 : Blo 2291435 2900549 := bbase (se 4 (by rfl) ⟨271926, by rfl⟩ : syracuseStep 2900549 = 543853) (by norm_num)
theorem B7734797 : Blo 2291435 7734797 := bstep (se 3 (by rfl) ⟨1450274, by rfl⟩ : syracuseStep 7734797 = 2900549) B2900549
theorem B5156531 : Blo 2291435 5156531 := bstep (se 1 (by rfl) ⟨3867398, by rfl⟩ : syracuseStep 5156531 = 7734797) B7734797
theorem B3437687 : Blo 2291435 3437687 := bstep (se 1 (by rfl) ⟨2578265, by rfl⟩ : syracuseStep 3437687 = 5156531) B5156531
theorem B2291791 : Blo 2291435 2291791 := bstep (se 1 (by rfl) ⟨1718843, by rfl⟩ : syracuseStep 2291791 = 3437687) B3437687
theorem B3437693 : Blo 2291435 3437693 := bbase (se 3 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 3437693 = 1289135) (by norm_num)
theorem B2291795 : Blo 2291435 2291795 := bstep (se 1 (by rfl) ⟨1718846, by rfl⟩ : syracuseStep 2291795 = 3437693) B3437693
theorem B5156549 : Blo 2291435 5156549 := bbase (se 4 (by rfl) ⟨483426, by rfl⟩ : syracuseStep 5156549 = 966853) (by norm_num)
theorem B3437699 : Blo 2291435 3437699 := bstep (se 1 (by rfl) ⟨2578274, by rfl⟩ : syracuseStep 3437699 = 5156549) B5156549
theorem B2291799 : Blo 2291435 2291799 := bstep (se 1 (by rfl) ⟨1718849, by rfl⟩ : syracuseStep 2291799 = 3437699) B3437699
theorem B2386897 : Blo 2291435 2386897 := bbase (se 2 (by rfl) ⟨895086, by rfl⟩ : syracuseStep 2386897 = 1790173) (by norm_num)
theorem B12730117 : Blo 2291435 12730117 := bstep (se 4 (by rfl) ⟨1193448, by rfl⟩ : syracuseStep 12730117 = 2386897) B2386897
theorem B16973489 : Blo 2291435 16973489 := bstep (se 2 (by rfl) ⟨6365058, by rfl⟩ : syracuseStep 16973489 = 12730117) B12730117
theorem B11315659 : Blo 2291435 11315659 := bstep (se 1 (by rfl) ⟨8486744, by rfl⟩ : syracuseStep 11315659 = 16973489) B16973489
theorem B15087545 : Blo 2291435 15087545 := bstep (se 2 (by rfl) ⟨5657829, by rfl⟩ : syracuseStep 15087545 = 11315659) B11315659
theorem B10058363 : Blo 2291435 10058363 := bstep (se 1 (by rfl) ⟨7543772, by rfl⟩ : syracuseStep 10058363 = 15087545) B15087545
theorem B6705575 : Blo 2291435 6705575 := bstep (se 1 (by rfl) ⟨5029181, by rfl⟩ : syracuseStep 6705575 = 10058363) B10058363
theorem B4470383 : Blo 2291435 4470383 := bstep (se 1 (by rfl) ⟨3352787, by rfl⟩ : syracuseStep 4470383 = 6705575) B6705575
theorem B2980255 : Blo 2291435 2980255 := bstep (se 1 (by rfl) ⟨2235191, by rfl⟩ : syracuseStep 2980255 = 4470383) B4470383
theorem B3973673 : Blo 2291435 3973673 := bstep (se 2 (by rfl) ⟨1490127, by rfl⟩ : syracuseStep 3973673 = 2980255) B2980255
theorem B2649115 : Blo 2291435 2649115 := bstep (se 1 (by rfl) ⟨1986836, by rfl⟩ : syracuseStep 2649115 = 3973673) B3973673
theorem B14128613 : Blo 2291435 14128613 := bstep (se 4 (by rfl) ⟨1324557, by rfl⟩ : syracuseStep 14128613 = 2649115) B2649115
theorem B9419075 : Blo 2291435 9419075 := bstep (se 1 (by rfl) ⟨7064306, by rfl⟩ : syracuseStep 9419075 = 14128613) B14128613
theorem B6279383 : Blo 2291435 6279383 := bstep (se 1 (by rfl) ⟨4709537, by rfl⟩ : syracuseStep 6279383 = 9419075) B9419075
theorem B4186255 : Blo 2291435 4186255 := bstep (se 1 (by rfl) ⟨3139691, by rfl⟩ : syracuseStep 4186255 = 6279383) B6279383
theorem B5581673 : Blo 2291435 5581673 := bstep (se 2 (by rfl) ⟨2093127, by rfl⟩ : syracuseStep 5581673 = 4186255) B4186255
theorem B3721115 : Blo 2291435 3721115 := bstep (se 1 (by rfl) ⟨2790836, by rfl⟩ : syracuseStep 3721115 = 5581673) B5581673
theorem B2480743 : Blo 2291435 2480743 := bstep (se 1 (by rfl) ⟨1860557, by rfl⟩ : syracuseStep 2480743 = 3721115) B3721115
theorem B3307657 : Blo 2291435 3307657 := bstep (se 2 (by rfl) ⟨1240371, by rfl⟩ : syracuseStep 3307657 = 2480743) B2480743
theorem B4410209 : Blo 2291435 4410209 := bstep (se 2 (by rfl) ⟨1653828, by rfl⟩ : syracuseStep 4410209 = 3307657) B3307657
theorem B2940139 : Blo 2291435 2940139 := bstep (se 1 (by rfl) ⟨2205104, by rfl⟩ : syracuseStep 2940139 = 4410209) B4410209
theorem B3920185 : Blo 2291435 3920185 := bstep (se 2 (by rfl) ⟨1470069, by rfl⟩ : syracuseStep 3920185 = 2940139) B2940139
theorem B5226913 : Blo 2291435 5226913 := bstep (se 2 (by rfl) ⟨1960092, by rfl⟩ : syracuseStep 5226913 = 3920185) B3920185
theorem B27876869 : Blo 2291435 27876869 := bstep (se 4 (by rfl) ⟨2613456, by rfl⟩ : syracuseStep 27876869 = 5226913) B5226913
theorem B18584579 : Blo 2291435 18584579 := bstep (se 1 (by rfl) ⟨13938434, by rfl⟩ : syracuseStep 18584579 = 27876869) B27876869
theorem B49558877 : Blo 2291435 49558877 := bstep (se 3 (by rfl) ⟨9292289, by rfl⟩ : syracuseStep 49558877 = 18584579) B18584579
theorem B33039251 : Blo 2291435 33039251 := bstep (se 1 (by rfl) ⟨24779438, by rfl⟩ : syracuseStep 33039251 = 49558877) B49558877
theorem B22026167 : Blo 2291435 22026167 := bstep (se 1 (by rfl) ⟨16519625, by rfl⟩ : syracuseStep 22026167 = 33039251) B33039251
theorem B14684111 : Blo 2291435 14684111 := bstep (se 1 (by rfl) ⟨11013083, by rfl⟩ : syracuseStep 14684111 = 22026167) B22026167
theorem B9789407 : Blo 2291435 9789407 := bstep (se 1 (by rfl) ⟨7342055, by rfl⟩ : syracuseStep 9789407 = 14684111) B14684111
theorem B6526271 : Blo 2291435 6526271 := bstep (se 1 (by rfl) ⟨4894703, by rfl⟩ : syracuseStep 6526271 = 9789407) B9789407
theorem B4350847 : Blo 2291435 4350847 := bstep (se 1 (by rfl) ⟨3263135, by rfl⟩ : syracuseStep 4350847 = 6526271) B6526271
theorem B5801129 : Blo 2291435 5801129 := bstep (se 2 (by rfl) ⟨2175423, by rfl⟩ : syracuseStep 5801129 = 4350847) B4350847
theorem B3867419 : Blo 2291435 3867419 := bstep (se 1 (by rfl) ⟨2900564, by rfl⟩ : syracuseStep 3867419 = 5801129) B5801129
theorem B2578279 : Blo 2291435 2578279 := bstep (se 1 (by rfl) ⟨1933709, by rfl⟩ : syracuseStep 2578279 = 3867419) B3867419
theorem B3437705 : Blo 2291435 3437705 := bstep (se 2 (by rfl) ⟨1289139, by rfl⟩ : syracuseStep 3437705 = 2578279) B2578279
theorem B2291803 : Blo 2291435 2291803 := bstep (se 1 (by rfl) ⟨1718852, by rfl⟩ : syracuseStep 2291803 = 3437705) B3437705
theorem B11602277 : Blo 2291435 11602277 := bbase (se 4 (by rfl) ⟨1087713, by rfl⟩ : syracuseStep 11602277 = 2175427) (by norm_num)
theorem B7734851 : Blo 2291435 7734851 := bstep (se 1 (by rfl) ⟨5801138, by rfl⟩ : syracuseStep 7734851 = 11602277) B11602277
theorem B5156567 : Blo 2291435 5156567 := bstep (se 1 (by rfl) ⟨3867425, by rfl⟩ : syracuseStep 5156567 = 7734851) B7734851
theorem B3437711 : Blo 2291435 3437711 := bstep (se 1 (by rfl) ⟨2578283, by rfl⟩ : syracuseStep 3437711 = 5156567) B5156567
theorem B2291807 : Blo 2291435 2291807 := bstep (se 1 (by rfl) ⟨1718855, by rfl⟩ : syracuseStep 2291807 = 3437711) B3437711
theorem B3437717 : Blo 2291435 3437717 := bbase (se 6 (by rfl) ⟨80571, by rfl⟩ : syracuseStep 3437717 = 161143) (by norm_num)
theorem B2291811 : Blo 2291435 2291811 := bstep (se 1 (by rfl) ⟨1718858, by rfl⟩ : syracuseStep 2291811 = 3437717) B3437717
theorem B2753285 : Blo 2291435 2753285 := bbase (se 4 (by rfl) ⟨258120, by rfl⟩ : syracuseStep 2753285 = 516241) (by norm_num)
theorem B7342093 : Blo 2291435 7342093 := bstep (se 3 (by rfl) ⟨1376642, by rfl⟩ : syracuseStep 7342093 = 2753285) B2753285
theorem B9789457 : Blo 2291435 9789457 := bstep (se 2 (by rfl) ⟨3671046, by rfl⟩ : syracuseStep 9789457 = 7342093) B7342093
theorem B13052609 : Blo 2291435 13052609 := bstep (se 2 (by rfl) ⟨4894728, by rfl⟩ : syracuseStep 13052609 = 9789457) B9789457
theorem B8701739 : Blo 2291435 8701739 := bstep (se 1 (by rfl) ⟨6526304, by rfl⟩ : syracuseStep 8701739 = 13052609) B13052609
theorem B5801159 : Blo 2291435 5801159 := bstep (se 1 (by rfl) ⟨4350869, by rfl⟩ : syracuseStep 5801159 = 8701739) B8701739
theorem B3867439 : Blo 2291435 3867439 := bstep (se 1 (by rfl) ⟨2900579, by rfl⟩ : syracuseStep 3867439 = 5801159) B5801159
theorem B5156585 : Blo 2291435 5156585 := bstep (se 2 (by rfl) ⟨1933719, by rfl⟩ : syracuseStep 5156585 = 3867439) B3867439
theorem B3437723 : Blo 2291435 3437723 := bstep (se 1 (by rfl) ⟨2578292, by rfl⟩ : syracuseStep 3437723 = 5156585) B5156585
theorem B2291815 : Blo 2291435 2291815 := bstep (se 1 (by rfl) ⟨1718861, by rfl⟩ : syracuseStep 2291815 = 3437723) B3437723
theorem B2578297 : Blo 2291435 2578297 := bbase (se 2 (by rfl) ⟨966861, by rfl⟩ : syracuseStep 2578297 = 1933723) (by norm_num)
theorem B3437729 : Blo 2291435 3437729 := bstep (se 2 (by rfl) ⟨1289148, by rfl⟩ : syracuseStep 3437729 = 2578297) B2578297
theorem B2291819 : Blo 2291435 2291819 := bstep (se 1 (by rfl) ⟨1718864, by rfl⟩ : syracuseStep 2291819 = 3437729) B3437729
theorem B5506589 : Blo 2291435 5506589 := bbase (se 3 (by rfl) ⟨1032485, by rfl⟩ : syracuseStep 5506589 = 2064971) (by norm_num)
theorem B14684237 : Blo 2291435 14684237 := bstep (se 3 (by rfl) ⟨2753294, by rfl⟩ : syracuseStep 14684237 = 5506589) B5506589
theorem B9789491 : Blo 2291435 9789491 := bstep (se 1 (by rfl) ⟨7342118, by rfl⟩ : syracuseStep 9789491 = 14684237) B14684237
theorem B6526327 : Blo 2291435 6526327 := bstep (se 1 (by rfl) ⟨4894745, by rfl⟩ : syracuseStep 6526327 = 9789491) B9789491
theorem B8701769 : Blo 2291435 8701769 := bstep (se 2 (by rfl) ⟨3263163, by rfl⟩ : syracuseStep 8701769 = 6526327) B6526327
theorem B5801179 : Blo 2291435 5801179 := bstep (se 1 (by rfl) ⟨4350884, by rfl⟩ : syracuseStep 5801179 = 8701769) B8701769
theorem B7734905 : Blo 2291435 7734905 := bstep (se 2 (by rfl) ⟨2900589, by rfl⟩ : syracuseStep 7734905 = 5801179) B5801179
theorem B5156603 : Blo 2291435 5156603 := bstep (se 1 (by rfl) ⟨3867452, by rfl⟩ : syracuseStep 5156603 = 7734905) B7734905
theorem B3437735 : Blo 2291435 3437735 := bstep (se 1 (by rfl) ⟨2578301, by rfl⟩ : syracuseStep 3437735 = 5156603) B5156603
theorem B2291823 : Blo 2291435 2291823 := bstep (se 1 (by rfl) ⟨1718867, by rfl⟩ : syracuseStep 2291823 = 3437735) B3437735
theorem B3437741 : Blo 2291435 3437741 := bbase (se 3 (by rfl) ⟨644576, by rfl⟩ : syracuseStep 3437741 = 1289153) (by norm_num)
theorem B2291827 : Blo 2291435 2291827 := bstep (se 1 (by rfl) ⟨1718870, by rfl⟩ : syracuseStep 2291827 = 3437741) B3437741
theorem B5156621 : Blo 2291435 5156621 := bbase (se 3 (by rfl) ⟨966866, by rfl⟩ : syracuseStep 5156621 = 1933733) (by norm_num)
theorem B3437747 : Blo 2291435 3437747 := bstep (se 1 (by rfl) ⟨2578310, by rfl⟩ : syracuseStep 3437747 = 5156621) B5156621
theorem B2291831 : Blo 2291435 2291831 := bstep (se 1 (by rfl) ⟨1718873, by rfl⟩ : syracuseStep 2291831 = 3437747) B3437747
theorem B2900605 : Blo 2291435 2900605 := bbase (se 3 (by rfl) ⟨543863, by rfl⟩ : syracuseStep 2900605 = 1087727) (by norm_num)
theorem B3867473 : Blo 2291435 3867473 := bstep (se 2 (by rfl) ⟨1450302, by rfl⟩ : syracuseStep 3867473 = 2900605) B2900605
theorem B2578315 : Blo 2291435 2578315 := bstep (se 1 (by rfl) ⟨1933736, by rfl⟩ : syracuseStep 2578315 = 3867473) B3867473
theorem B3437753 : Blo 2291435 3437753 := bstep (se 2 (by rfl) ⟨1289157, by rfl⟩ : syracuseStep 3437753 = 2578315) B2578315
theorem B2291835 : Blo 2291435 2291835 := bstep (se 1 (by rfl) ⟨1718876, by rfl⟩ : syracuseStep 2291835 = 3437753) B3437753
theorem B8259941 : Blo 2291435 8259941 := bbase (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) (by norm_num)
theorem B5506627 : Blo 2291435 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B7342169 : Blo 2291435 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B19579117 : Blo 2291435 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B26105489 : Blo 2291435 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B17403659 : Blo 2291435 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B11602439 : Blo 2291435 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B7734959 : Blo 2291435 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B5156639 : Blo 2291435 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B3437759 : Blo 2291435 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B2291839 : Blo 2291435 2291839 := bstep (se 1 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 2291839 = 3437759) B3437759
theorem B3437765 : Blo 2291435 3437765 := bbase (se 4 (by rfl) ⟨322290, by rfl⟩ : syracuseStep 3437765 = 644581) (by norm_num)
theorem B2291843 : Blo 2291435 2291843 := bstep (se 1 (by rfl) ⟨1718882, by rfl⟩ : syracuseStep 2291843 = 3437765) B3437765
theorem B3867493 : Blo 2291435 3867493 := bbase (se 4 (by rfl) ⟨362577, by rfl⟩ : syracuseStep 3867493 = 725155) (by norm_num)
theorem B5156657 : Blo 2291435 5156657 := bstep (se 2 (by rfl) ⟨1933746, by rfl⟩ : syracuseStep 5156657 = 3867493) B3867493
theorem B3437771 : Blo 2291435 3437771 := bstep (se 1 (by rfl) ⟨2578328, by rfl⟩ : syracuseStep 3437771 = 5156657) B5156657
theorem B2291847 : Blo 2291435 2291847 := bstep (se 1 (by rfl) ⟨1718885, by rfl⟩ : syracuseStep 2291847 = 3437771) B3437771
theorem B2578333 : Blo 2291435 2578333 := bbase (se 3 (by rfl) ⟨483437, by rfl⟩ : syracuseStep 2578333 = 966875) (by norm_num)
theorem B3437777 : Blo 2291435 3437777 := bstep (se 2 (by rfl) ⟨1289166, by rfl⟩ : syracuseStep 3437777 = 2578333) B2578333
theorem B2291851 : Blo 2291435 2291851 := bstep (se 1 (by rfl) ⟨1718888, by rfl⟩ : syracuseStep 2291851 = 3437777) B3437777
theorem B7735013 : Blo 2291435 7735013 := bbase (se 4 (by rfl) ⟨725157, by rfl⟩ : syracuseStep 7735013 = 1450315) (by norm_num)
theorem B5156675 : Blo 2291435 5156675 := bstep (se 1 (by rfl) ⟨3867506, by rfl⟩ : syracuseStep 5156675 = 7735013) B7735013
theorem B3437783 : Blo 2291435 3437783 := bstep (se 1 (by rfl) ⟨2578337, by rfl⟩ : syracuseStep 3437783 = 5156675) B5156675
theorem B2291855 : Blo 2291435 2291855 := bstep (se 1 (by rfl) ⟨1718891, by rfl⟩ : syracuseStep 2291855 = 3437783) B3437783
theorem B3437789 : Blo 2291435 3437789 := bbase (se 3 (by rfl) ⟨644585, by rfl⟩ : syracuseStep 3437789 = 1289171) (by norm_num)
theorem B2291859 : Blo 2291435 2291859 := bstep (se 1 (by rfl) ⟨1718894, by rfl⟩ : syracuseStep 2291859 = 3437789) B3437789
theorem B5156693 : Blo 2291435 5156693 := bbase (se 9 (by rfl) ⟨15107, by rfl⟩ : syracuseStep 5156693 = 30215) (by norm_num)
theorem B3437795 : Blo 2291435 3437795 := bstep (se 1 (by rfl) ⟨2578346, by rfl⟩ : syracuseStep 3437795 = 5156693) B5156693
theorem B2291863 : Blo 2291435 2291863 := bstep (se 1 (by rfl) ⟨1718897, by rfl⟩ : syracuseStep 2291863 = 3437795) B3437795
theorem B6526453 : Blo 2291435 6526453 := bbase (se 5 (by rfl) ⟨305927, by rfl⟩ : syracuseStep 6526453 = 611855) (by norm_num)
theorem B8701937 : Blo 2291435 8701937 := bstep (se 2 (by rfl) ⟨3263226, by rfl⟩ : syracuseStep 8701937 = 6526453) B6526453
theorem B5801291 : Blo 2291435 5801291 := bstep (se 1 (by rfl) ⟨4350968, by rfl⟩ : syracuseStep 5801291 = 8701937) B8701937
theorem B3867527 : Blo 2291435 3867527 := bstep (se 1 (by rfl) ⟨2900645, by rfl⟩ : syracuseStep 3867527 = 5801291) B5801291
theorem B2578351 : Blo 2291435 2578351 := bstep (se 1 (by rfl) ⟨1933763, by rfl⟩ : syracuseStep 2578351 = 3867527) B3867527
theorem B3437801 : Blo 2291435 3437801 := bstep (se 2 (by rfl) ⟨1289175, by rfl⟩ : syracuseStep 3437801 = 2578351) B2578351
theorem B2291867 : Blo 2291435 2291867 := bstep (se 1 (by rfl) ⟨1718900, by rfl⟩ : syracuseStep 2291867 = 3437801) B3437801
theorem B200946005 : Blo 2291435 200946005 := bbase (se 10 (by rfl) ⟨294354, by rfl⟩ : syracuseStep 200946005 = 588709) (by norm_num)
theorem B133964003 : Blo 2291435 133964003 := bstep (se 1 (by rfl) ⟨100473002, by rfl⟩ : syracuseStep 133964003 = 200946005) B200946005
theorem B357237341 : Blo 2291435 357237341 := bstep (se 3 (by rfl) ⟨66982001, by rfl⟩ : syracuseStep 357237341 = 133964003) B133964003
theorem B238158227 : Blo 2291435 238158227 := bstep (se 1 (by rfl) ⟨178618670, by rfl⟩ : syracuseStep 238158227 = 357237341) B357237341
theorem B158772151 : Blo 2291435 158772151 := bstep (se 1 (by rfl) ⟨119079113, by rfl⟩ : syracuseStep 158772151 = 238158227) B238158227
theorem B211696201 : Blo 2291435 211696201 := bstep (se 2 (by rfl) ⟨79386075, by rfl⟩ : syracuseStep 211696201 = 158772151) B158772151
theorem B282261601 : Blo 2291435 282261601 := bstep (se 2 (by rfl) ⟨105848100, by rfl⟩ : syracuseStep 282261601 = 211696201) B211696201
theorem B376348801 : Blo 2291435 376348801 := bstep (se 2 (by rfl) ⟨141130800, by rfl⟩ : syracuseStep 376348801 = 282261601) B282261601
theorem B501798401 : Blo 2291435 501798401 := bstep (se 2 (by rfl) ⟨188174400, by rfl⟩ : syracuseStep 501798401 = 376348801) B376348801
theorem B334532267 : Blo 2291435 334532267 := bstep (se 1 (by rfl) ⟨250899200, by rfl⟩ : syracuseStep 334532267 = 501798401) B501798401
theorem B223021511 : Blo 2291435 223021511 := bstep (se 1 (by rfl) ⟨167266133, by rfl⟩ : syracuseStep 223021511 = 334532267) B334532267
theorem B148681007 : Blo 2291435 148681007 := bstep (se 1 (by rfl) ⟨111510755, by rfl⟩ : syracuseStep 148681007 = 223021511) B223021511
theorem B99120671 : Blo 2291435 99120671 := bstep (se 1 (by rfl) ⟨74340503, by rfl⟩ : syracuseStep 99120671 = 148681007) B148681007
theorem B66080447 : Blo 2291435 66080447 := bstep (se 1 (by rfl) ⟨49560335, by rfl⟩ : syracuseStep 66080447 = 99120671) B99120671
theorem B44053631 : Blo 2291435 44053631 := bstep (se 1 (by rfl) ⟨33040223, by rfl⟩ : syracuseStep 44053631 = 66080447) B66080447
theorem B29369087 : Blo 2291435 29369087 := bstep (se 1 (by rfl) ⟨22026815, by rfl⟩ : syracuseStep 29369087 = 44053631) B44053631
theorem B19579391 : Blo 2291435 19579391 := bstep (se 1 (by rfl) ⟨14684543, by rfl⟩ : syracuseStep 19579391 = 29369087) B29369087
theorem B13052927 : Blo 2291435 13052927 := bstep (se 1 (by rfl) ⟨9789695, by rfl⟩ : syracuseStep 13052927 = 19579391) B19579391
theorem B8701951 : Blo 2291435 8701951 := bstep (se 1 (by rfl) ⟨6526463, by rfl⟩ : syracuseStep 8701951 = 13052927) B13052927
theorem B11602601 : Blo 2291435 11602601 := bstep (se 2 (by rfl) ⟨4350975, by rfl⟩ : syracuseStep 11602601 = 8701951) B8701951
theorem B7735067 : Blo 2291435 7735067 := bstep (se 1 (by rfl) ⟨5801300, by rfl⟩ : syracuseStep 7735067 = 11602601) B11602601
theorem B5156711 : Blo 2291435 5156711 := bstep (se 1 (by rfl) ⟨3867533, by rfl⟩ : syracuseStep 5156711 = 7735067) B7735067
theorem B3437807 : Blo 2291435 3437807 := bstep (se 1 (by rfl) ⟨2578355, by rfl⟩ : syracuseStep 3437807 = 5156711) B5156711
theorem B2291871 : Blo 2291435 2291871 := bstep (se 1 (by rfl) ⟨1718903, by rfl⟩ : syracuseStep 2291871 = 3437807) B3437807
theorem B3437813 : Blo 2291435 3437813 := bbase (se 5 (by rfl) ⟨161147, by rfl⟩ : syracuseStep 3437813 = 322295) (by norm_num)
theorem B2291875 : Blo 2291435 2291875 := bstep (se 1 (by rfl) ⟨1718906, by rfl⟩ : syracuseStep 2291875 = 3437813) B3437813
theorem B14684597 : Blo 2291435 14684597 := bbase (se 5 (by rfl) ⟨688340, by rfl⟩ : syracuseStep 14684597 = 1376681) (by norm_num)
theorem B9789731 : Blo 2291435 9789731 := bstep (se 1 (by rfl) ⟨7342298, by rfl⟩ : syracuseStep 9789731 = 14684597) B14684597
theorem B6526487 : Blo 2291435 6526487 := bstep (se 1 (by rfl) ⟨4894865, by rfl⟩ : syracuseStep 6526487 = 9789731) B9789731
theorem B4350991 : Blo 2291435 4350991 := bstep (se 1 (by rfl) ⟨3263243, by rfl⟩ : syracuseStep 4350991 = 6526487) B6526487
theorem B5801321 : Blo 2291435 5801321 := bstep (se 2 (by rfl) ⟨2175495, by rfl⟩ : syracuseStep 5801321 = 4350991) B4350991
theorem B3867547 : Blo 2291435 3867547 := bstep (se 1 (by rfl) ⟨2900660, by rfl⟩ : syracuseStep 3867547 = 5801321) B5801321
theorem B5156729 : Blo 2291435 5156729 := bstep (se 2 (by rfl) ⟨1933773, by rfl⟩ : syracuseStep 5156729 = 3867547) B3867547
theorem B3437819 : Blo 2291435 3437819 := bstep (se 1 (by rfl) ⟨2578364, by rfl⟩ : syracuseStep 3437819 = 5156729) B5156729
theorem B2291879 : Blo 2291435 2291879 := bstep (se 1 (by rfl) ⟨1718909, by rfl⟩ : syracuseStep 2291879 = 3437819) B3437819
theorem B2578369 : Blo 2291435 2578369 := bbase (se 2 (by rfl) ⟨966888, by rfl⟩ : syracuseStep 2578369 = 1933777) (by norm_num)
theorem B3437825 : Blo 2291435 3437825 := bstep (se 2 (by rfl) ⟨1289184, by rfl⟩ : syracuseStep 3437825 = 2578369) B2578369
theorem B2291883 : Blo 2291435 2291883 := bstep (se 1 (by rfl) ⟨1718912, by rfl⟩ : syracuseStep 2291883 = 3437825) B3437825
theorem B5801341 : Blo 2291435 5801341 := bbase (se 3 (by rfl) ⟨1087751, by rfl⟩ : syracuseStep 5801341 = 2175503) (by norm_num)
theorem B7735121 : Blo 2291435 7735121 := bstep (se 2 (by rfl) ⟨2900670, by rfl⟩ : syracuseStep 7735121 = 5801341) B5801341
theorem B5156747 : Blo 2291435 5156747 := bstep (se 1 (by rfl) ⟨3867560, by rfl⟩ : syracuseStep 5156747 = 7735121) B7735121
theorem B3437831 : Blo 2291435 3437831 := bstep (se 1 (by rfl) ⟨2578373, by rfl⟩ : syracuseStep 3437831 = 5156747) B5156747
theorem B2291887 : Blo 2291435 2291887 := bstep (se 1 (by rfl) ⟨1718915, by rfl⟩ : syracuseStep 2291887 = 3437831) B3437831
theorem B3437837 : Blo 2291435 3437837 := bbase (se 3 (by rfl) ⟨644594, by rfl⟩ : syracuseStep 3437837 = 1289189) (by norm_num)
theorem B2291891 : Blo 2291435 2291891 := bstep (se 1 (by rfl) ⟨1718918, by rfl⟩ : syracuseStep 2291891 = 3437837) B3437837
theorem B5156765 : Blo 2291435 5156765 := bbase (se 3 (by rfl) ⟨966893, by rfl⟩ : syracuseStep 5156765 = 1933787) (by norm_num)
theorem B3437843 : Blo 2291435 3437843 := bstep (se 1 (by rfl) ⟨2578382, by rfl⟩ : syracuseStep 3437843 = 5156765) B5156765
theorem B2291895 : Blo 2291435 2291895 := bstep (se 1 (by rfl) ⟨1718921, by rfl⟩ : syracuseStep 2291895 = 3437843) B3437843
theorem B3867581 : Blo 2291435 3867581 := bbase (se 3 (by rfl) ⟨725171, by rfl⟩ : syracuseStep 3867581 = 1450343) (by norm_num)
theorem B2578387 : Blo 2291435 2578387 := bstep (se 1 (by rfl) ⟨1933790, by rfl⟩ : syracuseStep 2578387 = 3867581) B3867581
theorem B3437849 : Blo 2291435 3437849 := bstep (se 2 (by rfl) ⟨1289193, by rfl⟩ : syracuseStep 3437849 = 2578387) B2578387
theorem B2291899 : Blo 2291435 2291899 := bstep (se 1 (by rfl) ⟨1718924, by rfl⟩ : syracuseStep 2291899 = 3437849) B3437849
theorem B13053109 : Blo 2291435 13053109 := bbase (se 5 (by rfl) ⟨611864, by rfl⟩ : syracuseStep 13053109 = 1223729) (by norm_num)
theorem B17404145 : Blo 2291435 17404145 := bstep (se 2 (by rfl) ⟨6526554, by rfl⟩ : syracuseStep 17404145 = 13053109) B13053109
theorem B11602763 : Blo 2291435 11602763 := bstep (se 1 (by rfl) ⟨8702072, by rfl⟩ : syracuseStep 11602763 = 17404145) B17404145
theorem B7735175 : Blo 2291435 7735175 := bstep (se 1 (by rfl) ⟨5801381, by rfl⟩ : syracuseStep 7735175 = 11602763) B11602763
theorem B5156783 : Blo 2291435 5156783 := bstep (se 1 (by rfl) ⟨3867587, by rfl⟩ : syracuseStep 5156783 = 7735175) B7735175
theorem B3437855 : Blo 2291435 3437855 := bstep (se 1 (by rfl) ⟨2578391, by rfl⟩ : syracuseStep 3437855 = 5156783) B5156783
theorem B2291903 : Blo 2291435 2291903 := bstep (se 1 (by rfl) ⟨1718927, by rfl⟩ : syracuseStep 2291903 = 3437855) B3437855
theorem B3437861 : Blo 2291435 3437861 := bbase (se 4 (by rfl) ⟨322299, by rfl⟩ : syracuseStep 3437861 = 644599) (by norm_num)
theorem B2291907 : Blo 2291435 2291907 := bstep (se 1 (by rfl) ⟨1718930, by rfl⟩ : syracuseStep 2291907 = 3437861) B3437861
theorem B2900701 : Blo 2291435 2900701 := bbase (se 3 (by rfl) ⟨543881, by rfl⟩ : syracuseStep 2900701 = 1087763) (by norm_num)
theorem B3867601 : Blo 2291435 3867601 := bstep (se 2 (by rfl) ⟨1450350, by rfl⟩ : syracuseStep 3867601 = 2900701) B2900701
theorem B5156801 : Blo 2291435 5156801 := bstep (se 2 (by rfl) ⟨1933800, by rfl⟩ : syracuseStep 5156801 = 3867601) B3867601
theorem B3437867 : Blo 2291435 3437867 := bstep (se 1 (by rfl) ⟨2578400, by rfl⟩ : syracuseStep 3437867 = 5156801) B5156801
theorem B2291911 : Blo 2291435 2291911 := bstep (se 1 (by rfl) ⟨1718933, by rfl⟩ : syracuseStep 2291911 = 3437867) B3437867
theorem B2578405 : Blo 2291435 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B3437873 : Blo 2291435 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B2291915 : Blo 2291435 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B2613589 : Blo 2291435 2613589 := bbase (se 10 (by rfl) ⟨3828, by rfl⟩ : syracuseStep 2613589 = 7657) (by norm_num)
theorem B13939141 : Blo 2291435 13939141 := bstep (se 4 (by rfl) ⟨1306794, by rfl⟩ : syracuseStep 13939141 = 2613589) B2613589
theorem B18585521 : Blo 2291435 18585521 := bstep (se 2 (by rfl) ⟨6969570, by rfl⟩ : syracuseStep 18585521 = 13939141) B13939141
theorem B12390347 : Blo 2291435 12390347 := bstep (se 1 (by rfl) ⟨9292760, by rfl⟩ : syracuseStep 12390347 = 18585521) B18585521
theorem B8260231 : Blo 2291435 8260231 := bstep (se 1 (by rfl) ⟨6195173, by rfl⟩ : syracuseStep 8260231 = 12390347) B12390347
theorem B11013641 : Blo 2291435 11013641 := bstep (se 2 (by rfl) ⟨4130115, by rfl⟩ : syracuseStep 11013641 = 8260231) B8260231
theorem B7342427 : Blo 2291435 7342427 := bstep (se 1 (by rfl) ⟨5506820, by rfl⟩ : syracuseStep 7342427 = 11013641) B11013641
theorem B4894951 : Blo 2291435 4894951 := bstep (se 1 (by rfl) ⟨3671213, by rfl⟩ : syracuseStep 4894951 = 7342427) B7342427
theorem B6526601 : Blo 2291435 6526601 := bstep (se 2 (by rfl) ⟨2447475, by rfl⟩ : syracuseStep 6526601 = 4894951) B4894951
theorem B4351067 : Blo 2291435 4351067 := bstep (se 1 (by rfl) ⟨3263300, by rfl⟩ : syracuseStep 4351067 = 6526601) B6526601
theorem B2900711 : Blo 2291435 2900711 := bstep (se 1 (by rfl) ⟨2175533, by rfl⟩ : syracuseStep 2900711 = 4351067) B4351067
theorem B7735229 : Blo 2291435 7735229 := bstep (se 3 (by rfl) ⟨1450355, by rfl⟩ : syracuseStep 7735229 = 2900711) B2900711
theorem B5156819 : Blo 2291435 5156819 := bstep (se 1 (by rfl) ⟨3867614, by rfl⟩ : syracuseStep 5156819 = 7735229) B7735229
theorem B3437879 : Blo 2291435 3437879 := bstep (se 1 (by rfl) ⟨2578409, by rfl⟩ : syracuseStep 3437879 = 5156819) B5156819
theorem B2291919 : Blo 2291435 2291919 := bstep (se 1 (by rfl) ⟨1718939, by rfl⟩ : syracuseStep 2291919 = 3437879) B3437879
theorem B3437885 : Blo 2291435 3437885 := bbase (se 3 (by rfl) ⟨644603, by rfl⟩ : syracuseStep 3437885 = 1289207) (by norm_num)
theorem B2291923 : Blo 2291435 2291923 := bstep (se 1 (by rfl) ⟨1718942, by rfl⟩ : syracuseStep 2291923 = 3437885) B3437885
theorem B5156837 : Blo 2291435 5156837 := bbase (se 4 (by rfl) ⟨483453, by rfl⟩ : syracuseStep 5156837 = 966907) (by norm_num)
theorem B3437891 : Blo 2291435 3437891 := bstep (se 1 (by rfl) ⟨2578418, by rfl⟩ : syracuseStep 3437891 = 5156837) B5156837
theorem B2291927 : Blo 2291435 2291927 := bstep (se 1 (by rfl) ⟨1718945, by rfl⟩ : syracuseStep 2291927 = 3437891) B3437891
theorem B5801453 : Blo 2291435 5801453 := bbase (se 3 (by rfl) ⟨1087772, by rfl⟩ : syracuseStep 5801453 = 2175545) (by norm_num)
theorem B3867635 : Blo 2291435 3867635 := bstep (se 1 (by rfl) ⟨2900726, by rfl⟩ : syracuseStep 3867635 = 5801453) B5801453
theorem B2578423 : Blo 2291435 2578423 := bstep (se 1 (by rfl) ⟨1933817, by rfl⟩ : syracuseStep 2578423 = 3867635) B3867635
theorem B3437897 : Blo 2291435 3437897 := bstep (se 2 (by rfl) ⟨1289211, by rfl⟩ : syracuseStep 3437897 = 2578423) B2578423
theorem B2291931 : Blo 2291435 2291931 := bstep (se 1 (by rfl) ⟨1718948, by rfl⟩ : syracuseStep 2291931 = 3437897) B3437897
theorem B4646413 : Blo 2291435 4646413 := bbase (se 3 (by rfl) ⟨871202, by rfl⟩ : syracuseStep 4646413 = 1742405) (by norm_num)
theorem B6195217 : Blo 2291435 6195217 := bstep (se 2 (by rfl) ⟨2323206, by rfl⟩ : syracuseStep 6195217 = 4646413) B4646413
theorem B8260289 : Blo 2291435 8260289 := bstep (se 2 (by rfl) ⟨3097608, by rfl⟩ : syracuseStep 8260289 = 6195217) B6195217
theorem B5506859 : Blo 2291435 5506859 := bstep (se 1 (by rfl) ⟨4130144, by rfl⟩ : syracuseStep 5506859 = 8260289) B8260289
theorem B3671239 : Blo 2291435 3671239 := bstep (se 1 (by rfl) ⟨2753429, by rfl⟩ : syracuseStep 3671239 = 5506859) B5506859
theorem B4894985 : Blo 2291435 4894985 := bstep (se 2 (by rfl) ⟨1835619, by rfl⟩ : syracuseStep 4894985 = 3671239) B3671239
theorem B3263323 : Blo 2291435 3263323 := bstep (se 1 (by rfl) ⟨2447492, by rfl⟩ : syracuseStep 3263323 = 4894985) B4894985
theorem B4351097 : Blo 2291435 4351097 := bstep (se 2 (by rfl) ⟨1631661, by rfl⟩ : syracuseStep 4351097 = 3263323) B3263323
theorem B11602925 : Blo 2291435 11602925 := bstep (se 3 (by rfl) ⟨2175548, by rfl⟩ : syracuseStep 11602925 = 4351097) B4351097
theorem B7735283 : Blo 2291435 7735283 := bstep (se 1 (by rfl) ⟨5801462, by rfl⟩ : syracuseStep 7735283 = 11602925) B11602925
theorem B5156855 : Blo 2291435 5156855 := bstep (se 1 (by rfl) ⟨3867641, by rfl⟩ : syracuseStep 5156855 = 7735283) B7735283
theorem B3437903 : Blo 2291435 3437903 := bstep (se 1 (by rfl) ⟨2578427, by rfl⟩ : syracuseStep 3437903 = 5156855) B5156855
theorem B2291935 : Blo 2291435 2291935 := bstep (se 1 (by rfl) ⟨1718951, by rfl⟩ : syracuseStep 2291935 = 3437903) B3437903
theorem B3437909 : Blo 2291435 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B2291939 : Blo 2291435 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B2447501 : Blo 2291435 2447501 := bbase (se 3 (by rfl) ⟨458906, by rfl⟩ : syracuseStep 2447501 = 917813) (by norm_num)
theorem B6526669 : Blo 2291435 6526669 := bstep (se 3 (by rfl) ⟨1223750, by rfl⟩ : syracuseStep 6526669 = 2447501) B2447501
theorem B8702225 : Blo 2291435 8702225 := bstep (se 2 (by rfl) ⟨3263334, by rfl⟩ : syracuseStep 8702225 = 6526669) B6526669
theorem B5801483 : Blo 2291435 5801483 := bstep (se 1 (by rfl) ⟨4351112, by rfl⟩ : syracuseStep 5801483 = 8702225) B8702225
theorem B3867655 : Blo 2291435 3867655 := bstep (se 1 (by rfl) ⟨2900741, by rfl⟩ : syracuseStep 3867655 = 5801483) B5801483
theorem B5156873 : Blo 2291435 5156873 := bstep (se 2 (by rfl) ⟨1933827, by rfl⟩ : syracuseStep 5156873 = 3867655) B3867655
theorem B3437915 : Blo 2291435 3437915 := bstep (se 1 (by rfl) ⟨2578436, by rfl⟩ : syracuseStep 3437915 = 5156873) B5156873
theorem B2291943 : Blo 2291435 2291943 := bstep (se 1 (by rfl) ⟨1718957, by rfl⟩ : syracuseStep 2291943 = 3437915) B3437915
theorem B2578441 : Blo 2291435 2578441 := bbase (se 2 (by rfl) ⟨966915, by rfl⟩ : syracuseStep 2578441 = 1933831) (by norm_num)
theorem B3437921 : Blo 2291435 3437921 := bstep (se 2 (by rfl) ⟨1289220, by rfl⟩ : syracuseStep 3437921 = 2578441) B2578441
theorem B2291947 : Blo 2291435 2291947 := bstep (se 1 (by rfl) ⟨1718960, by rfl⟩ : syracuseStep 2291947 = 3437921) B3437921
theorem B12390517 : Blo 2291435 12390517 := bbase (se 5 (by rfl) ⟨580805, by rfl⟩ : syracuseStep 12390517 = 1161611) (by norm_num)
theorem B16520689 : Blo 2291435 16520689 := bstep (se 2 (by rfl) ⟨6195258, by rfl⟩ : syracuseStep 16520689 = 12390517) B12390517
theorem B22027585 : Blo 2291435 22027585 := bstep (se 2 (by rfl) ⟨8260344, by rfl⟩ : syracuseStep 22027585 = 16520689) B16520689
theorem B29370113 : Blo 2291435 29370113 := bstep (se 2 (by rfl) ⟨11013792, by rfl⟩ : syracuseStep 29370113 = 22027585) B22027585
theorem B19580075 : Blo 2291435 19580075 := bstep (se 1 (by rfl) ⟨14685056, by rfl⟩ : syracuseStep 19580075 = 29370113) B29370113
theorem B13053383 : Blo 2291435 13053383 := bstep (se 1 (by rfl) ⟨9790037, by rfl⟩ : syracuseStep 13053383 = 19580075) B19580075
theorem B8702255 : Blo 2291435 8702255 := bstep (se 1 (by rfl) ⟨6526691, by rfl⟩ : syracuseStep 8702255 = 13053383) B13053383
theorem B5801503 : Blo 2291435 5801503 := bstep (se 1 (by rfl) ⟨4351127, by rfl⟩ : syracuseStep 5801503 = 8702255) B8702255
theorem B7735337 : Blo 2291435 7735337 := bstep (se 2 (by rfl) ⟨2900751, by rfl⟩ : syracuseStep 7735337 = 5801503) B5801503
theorem B5156891 : Blo 2291435 5156891 := bstep (se 1 (by rfl) ⟨3867668, by rfl⟩ : syracuseStep 5156891 = 7735337) B7735337
theorem B3437927 : Blo 2291435 3437927 := bstep (se 1 (by rfl) ⟨2578445, by rfl⟩ : syracuseStep 3437927 = 5156891) B5156891
theorem B2291951 : Blo 2291435 2291951 := bstep (se 1 (by rfl) ⟨1718963, by rfl⟩ : syracuseStep 2291951 = 3437927) B3437927
theorem B3437933 : Blo 2291435 3437933 := bbase (se 3 (by rfl) ⟨644612, by rfl⟩ : syracuseStep 3437933 = 1289225) (by norm_num)
theorem B2291955 : Blo 2291435 2291955 := bstep (se 1 (by rfl) ⟨1718966, by rfl⟩ : syracuseStep 2291955 = 3437933) B3437933
theorem B5156909 : Blo 2291435 5156909 := bbase (se 3 (by rfl) ⟨966920, by rfl⟩ : syracuseStep 5156909 = 1933841) (by norm_num)
theorem B3437939 : Blo 2291435 3437939 := bstep (se 1 (by rfl) ⟨2578454, by rfl⟩ : syracuseStep 3437939 = 5156909) B5156909
theorem B2291959 : Blo 2291435 2291959 := bstep (se 1 (by rfl) ⟨1718969, by rfl⟩ : syracuseStep 2291959 = 3437939) B3437939
theorem B3484853 : Blo 2291435 3484853 := bbase (se 5 (by rfl) ⟨163352, by rfl⟩ : syracuseStep 3484853 = 326705) (by norm_num)
theorem B2323235 : Blo 2291435 2323235 := bstep (se 1 (by rfl) ⟨1742426, by rfl⟩ : syracuseStep 2323235 = 3484853) B3484853
theorem B6195293 : Blo 2291435 6195293 := bstep (se 3 (by rfl) ⟨1161617, by rfl⟩ : syracuseStep 6195293 = 2323235) B2323235
theorem B4130195 : Blo 2291435 4130195 := bstep (se 1 (by rfl) ⟨3097646, by rfl⟩ : syracuseStep 4130195 = 6195293) B6195293
theorem B11013853 : Blo 2291435 11013853 := bstep (se 3 (by rfl) ⟨2065097, by rfl⟩ : syracuseStep 11013853 = 4130195) B4130195
theorem B14685137 : Blo 2291435 14685137 := bstep (se 2 (by rfl) ⟨5506926, by rfl⟩ : syracuseStep 14685137 = 11013853) B11013853
theorem B9790091 : Blo 2291435 9790091 := bstep (se 1 (by rfl) ⟨7342568, by rfl⟩ : syracuseStep 9790091 = 14685137) B14685137
theorem B6526727 : Blo 2291435 6526727 := bstep (se 1 (by rfl) ⟨4895045, by rfl⟩ : syracuseStep 6526727 = 9790091) B9790091
theorem B4351151 : Blo 2291435 4351151 := bstep (se 1 (by rfl) ⟨3263363, by rfl⟩ : syracuseStep 4351151 = 6526727) B6526727
theorem B2900767 : Blo 2291435 2900767 := bstep (se 1 (by rfl) ⟨2175575, by rfl⟩ : syracuseStep 2900767 = 4351151) B4351151
theorem B3867689 : Blo 2291435 3867689 := bstep (se 2 (by rfl) ⟨1450383, by rfl⟩ : syracuseStep 3867689 = 2900767) B2900767
theorem B2578459 : Blo 2291435 2578459 := bstep (se 1 (by rfl) ⟨1933844, by rfl⟩ : syracuseStep 2578459 = 3867689) B3867689
theorem B3437945 : Blo 2291435 3437945 := bstep (se 2 (by rfl) ⟨1289229, by rfl⟩ : syracuseStep 3437945 = 2578459) B2578459
theorem B2291963 : Blo 2291435 2291963 := bstep (se 1 (by rfl) ⟨1718972, by rfl⟩ : syracuseStep 2291963 = 3437945) B3437945
theorem B4646477 : Blo 2291435 4646477 := bbase (se 3 (by rfl) ⟨871214, by rfl⟩ : syracuseStep 4646477 = 1742429) (by norm_num)
theorem B3097651 : Blo 2291435 3097651 := bstep (se 1 (by rfl) ⟨2323238, by rfl⟩ : syracuseStep 3097651 = 4646477) B4646477
theorem B4130201 : Blo 2291435 4130201 := bstep (se 2 (by rfl) ⟨1548825, by rfl⟩ : syracuseStep 4130201 = 3097651) B3097651
theorem B11013869 : Blo 2291435 11013869 := bstep (se 3 (by rfl) ⟨2065100, by rfl⟩ : syracuseStep 11013869 = 4130201) B4130201
theorem B7342579 : Blo 2291435 7342579 := bstep (se 1 (by rfl) ⟨5506934, by rfl⟩ : syracuseStep 7342579 = 11013869) B11013869
theorem B39160421 : Blo 2291435 39160421 := bstep (se 4 (by rfl) ⟨3671289, by rfl⟩ : syracuseStep 39160421 = 7342579) B7342579
theorem B26106947 : Blo 2291435 26106947 := bstep (se 1 (by rfl) ⟨19580210, by rfl⟩ : syracuseStep 26106947 = 39160421) B39160421
theorem B17404631 : Blo 2291435 17404631 := bstep (se 1 (by rfl) ⟨13053473, by rfl⟩ : syracuseStep 17404631 = 26106947) B26106947
theorem B11603087 : Blo 2291435 11603087 := bstep (se 1 (by rfl) ⟨8702315, by rfl⟩ : syracuseStep 11603087 = 17404631) B17404631
theorem B7735391 : Blo 2291435 7735391 := bstep (se 1 (by rfl) ⟨5801543, by rfl⟩ : syracuseStep 7735391 = 11603087) B11603087
theorem B5156927 : Blo 2291435 5156927 := bstep (se 1 (by rfl) ⟨3867695, by rfl⟩ : syracuseStep 5156927 = 7735391) B7735391
theorem B3437951 : Blo 2291435 3437951 := bstep (se 1 (by rfl) ⟨2578463, by rfl⟩ : syracuseStep 3437951 = 5156927) B5156927
theorem B2291967 : Blo 2291435 2291967 := bstep (se 1 (by rfl) ⟨1718975, by rfl⟩ : syracuseStep 2291967 = 3437951) B3437951
theorem B3437957 : Blo 2291435 3437957 := bbase (se 4 (by rfl) ⟨322308, by rfl⟩ : syracuseStep 3437957 = 644617) (by norm_num)
theorem B2291971 : Blo 2291435 2291971 := bstep (se 1 (by rfl) ⟨1718978, by rfl⟩ : syracuseStep 2291971 = 3437957) B3437957
theorem B3867709 : Blo 2291435 3867709 := bbase (se 3 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 3867709 = 1450391) (by norm_num)
theorem B5156945 : Blo 2291435 5156945 := bstep (se 2 (by rfl) ⟨1933854, by rfl⟩ : syracuseStep 5156945 = 3867709) B3867709
theorem B3437963 : Blo 2291435 3437963 := bstep (se 1 (by rfl) ⟨2578472, by rfl⟩ : syracuseStep 3437963 = 5156945) B5156945
theorem B2291975 : Blo 2291435 2291975 := bstep (se 1 (by rfl) ⟨1718981, by rfl⟩ : syracuseStep 2291975 = 3437963) B3437963
theorem B2578477 : Blo 2291435 2578477 := bbase (se 3 (by rfl) ⟨483464, by rfl⟩ : syracuseStep 2578477 = 966929) (by norm_num)
theorem B3437969 : Blo 2291435 3437969 := bstep (se 2 (by rfl) ⟨1289238, by rfl⟩ : syracuseStep 3437969 = 2578477) B2578477
theorem B2291979 : Blo 2291435 2291979 := bstep (se 1 (by rfl) ⟨1718984, by rfl⟩ : syracuseStep 2291979 = 3437969) B3437969
theorem B7735445 : Blo 2291435 7735445 := bbase (se 6 (by rfl) ⟨181299, by rfl⟩ : syracuseStep 7735445 = 362599) (by norm_num)
theorem B5156963 : Blo 2291435 5156963 := bstep (se 1 (by rfl) ⟨3867722, by rfl⟩ : syracuseStep 5156963 = 7735445) B7735445
theorem B3437975 : Blo 2291435 3437975 := bstep (se 1 (by rfl) ⟨2578481, by rfl⟩ : syracuseStep 3437975 = 5156963) B5156963
theorem B2291983 : Blo 2291435 2291983 := bstep (se 1 (by rfl) ⟨1718987, by rfl⟩ : syracuseStep 2291983 = 3437975) B3437975
theorem B3437981 : Blo 2291435 3437981 := bbase (se 3 (by rfl) ⟨644621, by rfl⟩ : syracuseStep 3437981 = 1289243) (by norm_num)
theorem B2291987 : Blo 2291435 2291987 := bstep (se 1 (by rfl) ⟨1718990, by rfl⟩ : syracuseStep 2291987 = 3437981) B3437981
theorem B5156981 : Blo 2291435 5156981 := bbase (se 5 (by rfl) ⟨241733, by rfl⟩ : syracuseStep 5156981 = 483467) (by norm_num)
theorem B3437987 : Blo 2291435 3437987 := bstep (se 1 (by rfl) ⟨2578490, by rfl⟩ : syracuseStep 3437987 = 5156981) B5156981
theorem B2291991 : Blo 2291435 2291991 := bstep (se 1 (by rfl) ⟨1718993, by rfl⟩ : syracuseStep 2291991 = 3437987) B3437987
theorem B3484901 : Blo 2291435 3484901 := bbase (se 4 (by rfl) ⟨326709, by rfl⟩ : syracuseStep 3484901 = 653419) (by norm_num)
theorem B9293069 : Blo 2291435 9293069 := bstep (se 3 (by rfl) ⟨1742450, by rfl⟩ : syracuseStep 9293069 = 3484901) B3484901
theorem B6195379 : Blo 2291435 6195379 := bstep (se 1 (by rfl) ⟨4646534, by rfl⟩ : syracuseStep 6195379 = 9293069) B9293069
theorem B8260505 : Blo 2291435 8260505 := bstep (se 2 (by rfl) ⟨3097689, by rfl⟩ : syracuseStep 8260505 = 6195379) B6195379
theorem B5507003 : Blo 2291435 5507003 := bstep (se 1 (by rfl) ⟨4130252, by rfl⟩ : syracuseStep 5507003 = 8260505) B8260505
theorem B3671335 : Blo 2291435 3671335 := bstep (se 1 (by rfl) ⟨2753501, by rfl⟩ : syracuseStep 3671335 = 5507003) B5507003
theorem B19580453 : Blo 2291435 19580453 := bstep (se 4 (by rfl) ⟨1835667, by rfl⟩ : syracuseStep 19580453 = 3671335) B3671335
theorem B13053635 : Blo 2291435 13053635 := bstep (se 1 (by rfl) ⟨9790226, by rfl⟩ : syracuseStep 13053635 = 19580453) B19580453
theorem B8702423 : Blo 2291435 8702423 := bstep (se 1 (by rfl) ⟨6526817, by rfl⟩ : syracuseStep 8702423 = 13053635) B13053635
theorem B5801615 : Blo 2291435 5801615 := bstep (se 1 (by rfl) ⟨4351211, by rfl⟩ : syracuseStep 5801615 = 8702423) B8702423
theorem B3867743 : Blo 2291435 3867743 := bstep (se 1 (by rfl) ⟨2900807, by rfl⟩ : syracuseStep 3867743 = 5801615) B5801615
theorem B2578495 : Blo 2291435 2578495 := bstep (se 1 (by rfl) ⟨1933871, by rfl⟩ : syracuseStep 2578495 = 3867743) B3867743
theorem B3437993 : Blo 2291435 3437993 := bstep (se 2 (by rfl) ⟨1289247, by rfl⟩ : syracuseStep 3437993 = 2578495) B2578495
theorem B2291995 : Blo 2291435 2291995 := bstep (se 1 (by rfl) ⟨1718996, by rfl⟩ : syracuseStep 2291995 = 3437993) B3437993
theorem B8702437 : Blo 2291435 8702437 := bbase (se 4 (by rfl) ⟨815853, by rfl⟩ : syracuseStep 8702437 = 1631707) (by norm_num)
theorem B11603249 : Blo 2291435 11603249 := bstep (se 2 (by rfl) ⟨4351218, by rfl⟩ : syracuseStep 11603249 = 8702437) B8702437
theorem B7735499 : Blo 2291435 7735499 := bstep (se 1 (by rfl) ⟨5801624, by rfl⟩ : syracuseStep 7735499 = 11603249) B11603249
theorem B5156999 : Blo 2291435 5156999 := bstep (se 1 (by rfl) ⟨3867749, by rfl⟩ : syracuseStep 5156999 = 7735499) B7735499
theorem B3437999 : Blo 2291435 3437999 := bstep (se 1 (by rfl) ⟨2578499, by rfl⟩ : syracuseStep 3437999 = 5156999) B5156999
theorem B2291999 : Blo 2291435 2291999 := bstep (se 1 (by rfl) ⟨1718999, by rfl⟩ : syracuseStep 2291999 = 3437999) B3437999
theorem B3438005 : Blo 2291435 3438005 := bbase (se 5 (by rfl) ⟨161156, by rfl⟩ : syracuseStep 3438005 = 322313) (by norm_num)
theorem B2292003 : Blo 2291435 2292003 := bstep (se 1 (by rfl) ⟨1719002, by rfl⟩ : syracuseStep 2292003 = 3438005) B3438005
theorem B5801645 : Blo 2291435 5801645 := bbase (se 3 (by rfl) ⟨1087808, by rfl⟩ : syracuseStep 5801645 = 2175617) (by norm_num)
theorem B3867763 : Blo 2291435 3867763 := bstep (se 1 (by rfl) ⟨2900822, by rfl⟩ : syracuseStep 3867763 = 5801645) B5801645
theorem B5157017 : Blo 2291435 5157017 := bstep (se 2 (by rfl) ⟨1933881, by rfl⟩ : syracuseStep 5157017 = 3867763) B3867763
theorem B3438011 : Blo 2291435 3438011 := bstep (se 1 (by rfl) ⟨2578508, by rfl⟩ : syracuseStep 3438011 = 5157017) B5157017
theorem B2292007 : Blo 2291435 2292007 := bstep (se 1 (by rfl) ⟨1719005, by rfl⟩ : syracuseStep 2292007 = 3438011) B3438011
theorem B2578513 : Blo 2291435 2578513 := bbase (se 2 (by rfl) ⟨966942, by rfl⟩ : syracuseStep 2578513 = 1933885) (by norm_num)
theorem B3438017 : Blo 2291435 3438017 := bstep (se 2 (by rfl) ⟨1289256, by rfl⟩ : syracuseStep 3438017 = 2578513) B2578513
theorem B2292011 : Blo 2291435 2292011 := bstep (se 1 (by rfl) ⟨1719008, by rfl⟩ : syracuseStep 2292011 = 3438017) B3438017
theorem B3263437 : Blo 2291435 3263437 := bbase (se 3 (by rfl) ⟨611894, by rfl⟩ : syracuseStep 3263437 = 1223789) (by norm_num)
theorem B4351249 : Blo 2291435 4351249 := bstep (se 2 (by rfl) ⟨1631718, by rfl⟩ : syracuseStep 4351249 = 3263437) B3263437
theorem B5801665 : Blo 2291435 5801665 := bstep (se 2 (by rfl) ⟨2175624, by rfl⟩ : syracuseStep 5801665 = 4351249) B4351249
theorem B7735553 : Blo 2291435 7735553 := bstep (se 2 (by rfl) ⟨2900832, by rfl⟩ : syracuseStep 7735553 = 5801665) B5801665
theorem B5157035 : Blo 2291435 5157035 := bstep (se 1 (by rfl) ⟨3867776, by rfl⟩ : syracuseStep 5157035 = 7735553) B7735553
theorem B3438023 : Blo 2291435 3438023 := bstep (se 1 (by rfl) ⟨2578517, by rfl⟩ : syracuseStep 3438023 = 5157035) B5157035
theorem B2292015 : Blo 2291435 2292015 := bstep (se 1 (by rfl) ⟨1719011, by rfl⟩ : syracuseStep 2292015 = 3438023) B3438023
theorem B3438029 : Blo 2291435 3438029 := bbase (se 3 (by rfl) ⟨644630, by rfl⟩ : syracuseStep 3438029 = 1289261) (by norm_num)
theorem B2292019 : Blo 2291435 2292019 := bstep (se 1 (by rfl) ⟨1719014, by rfl⟩ : syracuseStep 2292019 = 3438029) B3438029
theorem B5157053 : Blo 2291435 5157053 := bbase (se 3 (by rfl) ⟨966947, by rfl⟩ : syracuseStep 5157053 = 1933895) (by norm_num)
theorem B3438035 : Blo 2291435 3438035 := bstep (se 1 (by rfl) ⟨2578526, by rfl⟩ : syracuseStep 3438035 = 5157053) B5157053
theorem B2292023 : Blo 2291435 2292023 := bstep (se 1 (by rfl) ⟨1719017, by rfl⟩ : syracuseStep 2292023 = 3438035) B3438035
theorem B3867797 : Blo 2291435 3867797 := bbase (se 6 (by rfl) ⟨90651, by rfl⟩ : syracuseStep 3867797 = 181303) (by norm_num)
theorem B2578531 : Blo 2291435 2578531 := bstep (se 1 (by rfl) ⟨1933898, by rfl⟩ : syracuseStep 2578531 = 3867797) B3867797
theorem B3438041 : Blo 2291435 3438041 := bstep (se 2 (by rfl) ⟨1289265, by rfl⟩ : syracuseStep 3438041 = 2578531) B2578531
theorem B2292027 : Blo 2291435 2292027 := bstep (se 1 (by rfl) ⟨1719020, by rfl⟩ : syracuseStep 2292027 = 3438041) B3438041
theorem B20118709 : Blo 2291435 20118709 := bbase (se 5 (by rfl) ⟨943064, by rfl⟩ : syracuseStep 20118709 = 1886129) (by norm_num)
theorem B26824945 : Blo 2291435 26824945 := bstep (se 2 (by rfl) ⟨10059354, by rfl⟩ : syracuseStep 26824945 = 20118709) B20118709
theorem B35766593 : Blo 2291435 35766593 := bstep (se 2 (by rfl) ⟨13412472, by rfl⟩ : syracuseStep 35766593 = 26824945) B26824945
theorem B23844395 : Blo 2291435 23844395 := bstep (se 1 (by rfl) ⟨17883296, by rfl⟩ : syracuseStep 23844395 = 35766593) B35766593
theorem B15896263 : Blo 2291435 15896263 := bstep (se 1 (by rfl) ⟨11922197, by rfl⟩ : syracuseStep 15896263 = 23844395) B23844395
theorem B21195017 : Blo 2291435 21195017 := bstep (se 2 (by rfl) ⟨7948131, by rfl⟩ : syracuseStep 21195017 = 15896263) B15896263
theorem B14130011 : Blo 2291435 14130011 := bstep (se 1 (by rfl) ⟨10597508, by rfl⟩ : syracuseStep 14130011 = 21195017) B21195017
theorem B37680029 : Blo 2291435 37680029 := bstep (se 3 (by rfl) ⟨7065005, by rfl⟩ : syracuseStep 37680029 = 14130011) B14130011
theorem B25120019 : Blo 2291435 25120019 := bstep (se 1 (by rfl) ⟨18840014, by rfl⟩ : syracuseStep 25120019 = 37680029) B37680029
theorem B16746679 : Blo 2291435 16746679 := bstep (se 1 (by rfl) ⟨12560009, by rfl⟩ : syracuseStep 16746679 = 25120019) B25120019
theorem B22328905 : Blo 2291435 22328905 := bstep (se 2 (by rfl) ⟨8373339, by rfl⟩ : syracuseStep 22328905 = 16746679) B16746679
theorem B29771873 : Blo 2291435 29771873 := bstep (se 2 (by rfl) ⟨11164452, by rfl⟩ : syracuseStep 29771873 = 22328905) B22328905
theorem B19847915 : Blo 2291435 19847915 := bstep (se 1 (by rfl) ⟨14885936, by rfl⟩ : syracuseStep 19847915 = 29771873) B29771873
theorem B13231943 : Blo 2291435 13231943 := bstep (se 1 (by rfl) ⟨9923957, by rfl⟩ : syracuseStep 13231943 = 19847915) B19847915
theorem B8821295 : Blo 2291435 8821295 := bstep (se 1 (by rfl) ⟨6615971, by rfl⟩ : syracuseStep 8821295 = 13231943) B13231943
theorem B5880863 : Blo 2291435 5880863 := bstep (se 1 (by rfl) ⟨4410647, by rfl⟩ : syracuseStep 5880863 = 8821295) B8821295
theorem B3920575 : Blo 2291435 3920575 := bstep (se 1 (by rfl) ⟨2940431, by rfl⟩ : syracuseStep 3920575 = 5880863) B5880863
theorem B5227433 : Blo 2291435 5227433 := bstep (se 2 (by rfl) ⟨1960287, by rfl⟩ : syracuseStep 5227433 = 3920575) B3920575
theorem B3484955 : Blo 2291435 3484955 := bstep (se 1 (by rfl) ⟨2613716, by rfl⟩ : syracuseStep 3484955 = 5227433) B5227433
theorem B9293213 : Blo 2291435 9293213 := bstep (se 3 (by rfl) ⟨1742477, by rfl⟩ : syracuseStep 9293213 = 3484955) B3484955
theorem B6195475 : Blo 2291435 6195475 := bstep (se 1 (by rfl) ⟨4646606, by rfl⟩ : syracuseStep 6195475 = 9293213) B9293213
theorem B8260633 : Blo 2291435 8260633 := bstep (se 2 (by rfl) ⟨3097737, by rfl⟩ : syracuseStep 8260633 = 6195475) B6195475
theorem B11014177 : Blo 2291435 11014177 := bstep (se 2 (by rfl) ⟨4130316, by rfl⟩ : syracuseStep 11014177 = 8260633) B8260633
theorem B14685569 : Blo 2291435 14685569 := bstep (se 2 (by rfl) ⟨5507088, by rfl⟩ : syracuseStep 14685569 = 11014177) B11014177
theorem B9790379 : Blo 2291435 9790379 := bstep (se 1 (by rfl) ⟨7342784, by rfl⟩ : syracuseStep 9790379 = 14685569) B14685569
theorem B6526919 : Blo 2291435 6526919 := bstep (se 1 (by rfl) ⟨4895189, by rfl⟩ : syracuseStep 6526919 = 9790379) B9790379
theorem B17405117 : Blo 2291435 17405117 := bstep (se 3 (by rfl) ⟨3263459, by rfl⟩ : syracuseStep 17405117 = 6526919) B6526919
theorem B11603411 : Blo 2291435 11603411 := bstep (se 1 (by rfl) ⟨8702558, by rfl⟩ : syracuseStep 11603411 = 17405117) B17405117
theorem B7735607 : Blo 2291435 7735607 := bstep (se 1 (by rfl) ⟨5801705, by rfl⟩ : syracuseStep 7735607 = 11603411) B11603411
theorem B5157071 : Blo 2291435 5157071 := bstep (se 1 (by rfl) ⟨3867803, by rfl⟩ : syracuseStep 5157071 = 7735607) B7735607
theorem B3438047 : Blo 2291435 3438047 := bstep (se 1 (by rfl) ⟨2578535, by rfl⟩ : syracuseStep 3438047 = 5157071) B5157071
theorem B2292031 : Blo 2291435 2292031 := bstep (se 1 (by rfl) ⟨1719023, by rfl⟩ : syracuseStep 2292031 = 3438047) B3438047
theorem B3438053 : Blo 2291435 3438053 := bbase (se 4 (by rfl) ⟨322317, by rfl⟩ : syracuseStep 3438053 = 644635) (by norm_num)
theorem B2292035 : Blo 2291435 2292035 := bstep (se 1 (by rfl) ⟨1719026, by rfl⟩ : syracuseStep 2292035 = 3438053) B3438053
theorem B3307997 : Blo 2291435 3307997 := bbase (se 3 (by rfl) ⟨620249, by rfl⟩ : syracuseStep 3307997 = 1240499) (by norm_num)
theorem B8821325 : Blo 2291435 8821325 := bstep (se 3 (by rfl) ⟨1653998, by rfl⟩ : syracuseStep 8821325 = 3307997) B3307997
theorem B23523533 : Blo 2291435 23523533 := bstep (se 3 (by rfl) ⟨4410662, by rfl⟩ : syracuseStep 23523533 = 8821325) B8821325
theorem B15682355 : Blo 2291435 15682355 := bstep (se 1 (by rfl) ⟨11761766, by rfl⟩ : syracuseStep 15682355 = 23523533) B23523533
theorem B10454903 : Blo 2291435 10454903 := bstep (se 1 (by rfl) ⟨7841177, by rfl⟩ : syracuseStep 10454903 = 15682355) B15682355
theorem B6969935 : Blo 2291435 6969935 := bstep (se 1 (by rfl) ⟨5227451, by rfl⟩ : syracuseStep 6969935 = 10454903) B10454903
theorem B18586493 : Blo 2291435 18586493 := bstep (se 3 (by rfl) ⟨3484967, by rfl⟩ : syracuseStep 18586493 = 6969935) B6969935
theorem B12390995 : Blo 2291435 12390995 := bstep (se 1 (by rfl) ⟨9293246, by rfl⟩ : syracuseStep 12390995 = 18586493) B18586493
theorem B33042653 : Blo 2291435 33042653 := bstep (se 3 (by rfl) ⟨6195497, by rfl⟩ : syracuseStep 33042653 = 12390995) B12390995
theorem B22028435 : Blo 2291435 22028435 := bstep (se 1 (by rfl) ⟨16521326, by rfl⟩ : syracuseStep 22028435 = 33042653) B33042653
theorem B14685623 : Blo 2291435 14685623 := bstep (se 1 (by rfl) ⟨11014217, by rfl⟩ : syracuseStep 14685623 = 22028435) B22028435
theorem B9790415 : Blo 2291435 9790415 := bstep (se 1 (by rfl) ⟨7342811, by rfl⟩ : syracuseStep 9790415 = 14685623) B14685623
theorem B6526943 : Blo 2291435 6526943 := bstep (se 1 (by rfl) ⟨4895207, by rfl⟩ : syracuseStep 6526943 = 9790415) B9790415
theorem B4351295 : Blo 2291435 4351295 := bstep (se 1 (by rfl) ⟨3263471, by rfl⟩ : syracuseStep 4351295 = 6526943) B6526943
theorem B2900863 : Blo 2291435 2900863 := bstep (se 1 (by rfl) ⟨2175647, by rfl⟩ : syracuseStep 2900863 = 4351295) B4351295
theorem B3867817 : Blo 2291435 3867817 := bstep (se 2 (by rfl) ⟨1450431, by rfl⟩ : syracuseStep 3867817 = 2900863) B2900863
theorem B5157089 : Blo 2291435 5157089 := bstep (se 2 (by rfl) ⟨1933908, by rfl⟩ : syracuseStep 5157089 = 3867817) B3867817
theorem B3438059 : Blo 2291435 3438059 := bstep (se 1 (by rfl) ⟨2578544, by rfl⟩ : syracuseStep 3438059 = 5157089) B5157089
theorem B2292039 : Blo 2291435 2292039 := bstep (se 1 (by rfl) ⟨1719029, by rfl⟩ : syracuseStep 2292039 = 3438059) B3438059
theorem B2578549 : Blo 2291435 2578549 := bbase (se 5 (by rfl) ⟨120869, by rfl⟩ : syracuseStep 2578549 = 241739) (by norm_num)
theorem B3438065 : Blo 2291435 3438065 := bstep (se 2 (by rfl) ⟨1289274, by rfl⟩ : syracuseStep 3438065 = 2578549) B2578549
theorem B2292043 : Blo 2291435 2292043 := bstep (se 1 (by rfl) ⟨1719032, by rfl⟩ : syracuseStep 2292043 = 3438065) B3438065
theorem B2900873 : Blo 2291435 2900873 := bbase (se 2 (by rfl) ⟨1087827, by rfl⟩ : syracuseStep 2900873 = 2175655) (by norm_num)
theorem B7735661 : Blo 2291435 7735661 := bstep (se 3 (by rfl) ⟨1450436, by rfl⟩ : syracuseStep 7735661 = 2900873) B2900873
theorem B5157107 : Blo 2291435 5157107 := bstep (se 1 (by rfl) ⟨3867830, by rfl⟩ : syracuseStep 5157107 = 7735661) B7735661
theorem B3438071 : Blo 2291435 3438071 := bstep (se 1 (by rfl) ⟨2578553, by rfl⟩ : syracuseStep 3438071 = 5157107) B5157107
theorem B2292047 : Blo 2291435 2292047 := bstep (se 1 (by rfl) ⟨1719035, by rfl⟩ : syracuseStep 2292047 = 3438071) B3438071
theorem B3438077 : Blo 2291435 3438077 := bbase (se 3 (by rfl) ⟨644639, by rfl⟩ : syracuseStep 3438077 = 1289279) (by norm_num)
theorem B2292051 : Blo 2291435 2292051 := bstep (se 1 (by rfl) ⟨1719038, by rfl⟩ : syracuseStep 2292051 = 3438077) B3438077
theorem B5157125 : Blo 2291435 5157125 := bbase (se 4 (by rfl) ⟨483480, by rfl⟩ : syracuseStep 5157125 = 966961) (by norm_num)
theorem B3438083 : Blo 2291435 3438083 := bstep (se 1 (by rfl) ⟨2578562, by rfl⟩ : syracuseStep 3438083 = 5157125) B5157125
theorem B2292055 : Blo 2291435 2292055 := bstep (se 1 (by rfl) ⟨1719041, by rfl⟩ : syracuseStep 2292055 = 3438083) B3438083
theorem B4351333 : Blo 2291435 4351333 := bbase (se 4 (by rfl) ⟨407937, by rfl⟩ : syracuseStep 4351333 = 815875) (by norm_num)
theorem B5801777 : Blo 2291435 5801777 := bstep (se 2 (by rfl) ⟨2175666, by rfl⟩ : syracuseStep 5801777 = 4351333) B4351333
theorem B3867851 : Blo 2291435 3867851 := bstep (se 1 (by rfl) ⟨2900888, by rfl⟩ : syracuseStep 3867851 = 5801777) B5801777
theorem B2578567 : Blo 2291435 2578567 := bstep (se 1 (by rfl) ⟨1933925, by rfl⟩ : syracuseStep 2578567 = 3867851) B3867851
theorem B3438089 : Blo 2291435 3438089 := bstep (se 2 (by rfl) ⟨1289283, by rfl⟩ : syracuseStep 3438089 = 2578567) B2578567
theorem B2292059 : Blo 2291435 2292059 := bstep (se 1 (by rfl) ⟨1719044, by rfl⟩ : syracuseStep 2292059 = 3438089) B3438089
theorem B11603573 : Blo 2291435 11603573 := bbase (se 5 (by rfl) ⟨543917, by rfl⟩ : syracuseStep 11603573 = 1087835) (by norm_num)
theorem B7735715 : Blo 2291435 7735715 := bstep (se 1 (by rfl) ⟨5801786, by rfl⟩ : syracuseStep 7735715 = 11603573) B11603573
theorem B5157143 : Blo 2291435 5157143 := bstep (se 1 (by rfl) ⟨3867857, by rfl⟩ : syracuseStep 5157143 = 7735715) B7735715
theorem B3438095 : Blo 2291435 3438095 := bstep (se 1 (by rfl) ⟨2578571, by rfl⟩ : syracuseStep 3438095 = 5157143) B5157143
theorem B2292063 : Blo 2291435 2292063 := bstep (se 1 (by rfl) ⟨1719047, by rfl⟩ : syracuseStep 2292063 = 3438095) B3438095
theorem B3438101 : Blo 2291435 3438101 := bbase (se 6 (by rfl) ⟨80580, by rfl⟩ : syracuseStep 3438101 = 161161) (by norm_num)
theorem B2292067 : Blo 2291435 2292067 := bstep (se 1 (by rfl) ⟨1719050, by rfl⟩ : syracuseStep 2292067 = 3438101) B3438101
theorem B4130389 : Blo 2291435 4130389 := bbase (se 8 (by rfl) ⟨24201, by rfl⟩ : syracuseStep 4130389 = 48403) (by norm_num)
theorem B5507185 : Blo 2291435 5507185 := bstep (se 2 (by rfl) ⟨2065194, by rfl⟩ : syracuseStep 5507185 = 4130389) B4130389
theorem B7342913 : Blo 2291435 7342913 := bstep (se 2 (by rfl) ⟨2753592, by rfl⟩ : syracuseStep 7342913 = 5507185) B5507185
theorem B19581101 : Blo 2291435 19581101 := bstep (se 3 (by rfl) ⟨3671456, by rfl⟩ : syracuseStep 19581101 = 7342913) B7342913
theorem B13054067 : Blo 2291435 13054067 := bstep (se 1 (by rfl) ⟨9790550, by rfl⟩ : syracuseStep 13054067 = 19581101) B19581101
theorem B8702711 : Blo 2291435 8702711 := bstep (se 1 (by rfl) ⟨6527033, by rfl⟩ : syracuseStep 8702711 = 13054067) B13054067
theorem B5801807 : Blo 2291435 5801807 := bstep (se 1 (by rfl) ⟨4351355, by rfl⟩ : syracuseStep 5801807 = 8702711) B8702711
theorem B3867871 : Blo 2291435 3867871 := bstep (se 1 (by rfl) ⟨2900903, by rfl⟩ : syracuseStep 3867871 = 5801807) B5801807
theorem B5157161 : Blo 2291435 5157161 := bstep (se 2 (by rfl) ⟨1933935, by rfl⟩ : syracuseStep 5157161 = 3867871) B3867871
theorem B3438107 : Blo 2291435 3438107 := bstep (se 1 (by rfl) ⟨2578580, by rfl⟩ : syracuseStep 3438107 = 5157161) B5157161
theorem B2292071 : Blo 2291435 2292071 := bstep (se 1 (by rfl) ⟨1719053, by rfl⟩ : syracuseStep 2292071 = 3438107) B3438107
theorem B2578585 : Blo 2291435 2578585 := bbase (se 2 (by rfl) ⟨966969, by rfl⟩ : syracuseStep 2578585 = 1933939) (by norm_num)
theorem B3438113 : Blo 2291435 3438113 := bstep (se 2 (by rfl) ⟨1289292, by rfl⟩ : syracuseStep 3438113 = 2578585) B2578585
theorem B2292075 : Blo 2291435 2292075 := bstep (se 1 (by rfl) ⟨1719056, by rfl⟩ : syracuseStep 2292075 = 3438113) B3438113
theorem B8702741 : Blo 2291435 8702741 := bbase (se 6 (by rfl) ⟨203970, by rfl⟩ : syracuseStep 8702741 = 407941) (by norm_num)
theorem B5801827 : Blo 2291435 5801827 := bstep (se 1 (by rfl) ⟨4351370, by rfl⟩ : syracuseStep 5801827 = 8702741) B8702741
theorem B7735769 : Blo 2291435 7735769 := bstep (se 2 (by rfl) ⟨2900913, by rfl⟩ : syracuseStep 7735769 = 5801827) B5801827
theorem B5157179 : Blo 2291435 5157179 := bstep (se 1 (by rfl) ⟨3867884, by rfl⟩ : syracuseStep 5157179 = 7735769) B7735769
theorem B3438119 : Blo 2291435 3438119 := bstep (se 1 (by rfl) ⟨2578589, by rfl⟩ : syracuseStep 3438119 = 5157179) B5157179
theorem B2292079 : Blo 2291435 2292079 := bstep (se 1 (by rfl) ⟨1719059, by rfl⟩ : syracuseStep 2292079 = 3438119) B3438119
theorem B3438125 : Blo 2291435 3438125 := bbase (se 3 (by rfl) ⟨644648, by rfl⟩ : syracuseStep 3438125 = 1289297) (by norm_num)
theorem B2292083 : Blo 2291435 2292083 := bstep (se 1 (by rfl) ⟨1719062, by rfl⟩ : syracuseStep 2292083 = 3438125) B3438125
theorem B5157197 : Blo 2291435 5157197 := bbase (se 3 (by rfl) ⟨966974, by rfl⟩ : syracuseStep 5157197 = 1933949) (by norm_num)
theorem B3438131 : Blo 2291435 3438131 := bstep (se 1 (by rfl) ⟨2578598, by rfl⟩ : syracuseStep 3438131 = 5157197) B5157197
theorem B2292087 : Blo 2291435 2292087 := bstep (se 1 (by rfl) ⟨1719065, by rfl⟩ : syracuseStep 2292087 = 3438131) B3438131
theorem B2900929 : Blo 2291435 2900929 := bbase (se 2 (by rfl) ⟨1087848, by rfl⟩ : syracuseStep 2900929 = 2175697) (by norm_num)
theorem B3867905 : Blo 2291435 3867905 := bstep (se 2 (by rfl) ⟨1450464, by rfl⟩ : syracuseStep 3867905 = 2900929) B2900929
theorem B2578603 : Blo 2291435 2578603 := bstep (se 1 (by rfl) ⟨1933952, by rfl⟩ : syracuseStep 2578603 = 3867905) B3867905
theorem B3438137 : Blo 2291435 3438137 := bstep (se 2 (by rfl) ⟨1289301, by rfl⟩ : syracuseStep 3438137 = 2578603) B2578603
theorem B2292091 : Blo 2291435 2292091 := bstep (se 1 (by rfl) ⟨1719068, by rfl⟩ : syracuseStep 2292091 = 3438137) B3438137
theorem B3485053 : Blo 2291435 3485053 := bbase (se 3 (by rfl) ⟨653447, by rfl⟩ : syracuseStep 3485053 = 1306895) (by norm_num)
theorem B4646737 : Blo 2291435 4646737 := bstep (se 2 (by rfl) ⟨1742526, by rfl⟩ : syracuseStep 4646737 = 3485053) B3485053
theorem B6195649 : Blo 2291435 6195649 := bstep (se 2 (by rfl) ⟨2323368, by rfl⟩ : syracuseStep 6195649 = 4646737) B4646737
theorem B8260865 : Blo 2291435 8260865 := bstep (se 2 (by rfl) ⟨3097824, by rfl⟩ : syracuseStep 8260865 = 6195649) B6195649
theorem B5507243 : Blo 2291435 5507243 := bstep (se 1 (by rfl) ⟨4130432, by rfl⟩ : syracuseStep 5507243 = 8260865) B8260865
theorem B3671495 : Blo 2291435 3671495 := bstep (se 1 (by rfl) ⟨2753621, by rfl⟩ : syracuseStep 3671495 = 5507243) B5507243
theorem B2447663 : Blo 2291435 2447663 := bstep (se 1 (by rfl) ⟨1835747, by rfl⟩ : syracuseStep 2447663 = 3671495) B3671495
theorem B26108405 : Blo 2291435 26108405 := bstep (se 5 (by rfl) ⟨1223831, by rfl⟩ : syracuseStep 26108405 = 2447663) B2447663
theorem B17405603 : Blo 2291435 17405603 := bstep (se 1 (by rfl) ⟨13054202, by rfl⟩ : syracuseStep 17405603 = 26108405) B26108405
theorem B11603735 : Blo 2291435 11603735 := bstep (se 1 (by rfl) ⟨8702801, by rfl⟩ : syracuseStep 11603735 = 17405603) B17405603
theorem B7735823 : Blo 2291435 7735823 := bstep (se 1 (by rfl) ⟨5801867, by rfl⟩ : syracuseStep 7735823 = 11603735) B11603735
theorem B5157215 : Blo 2291435 5157215 := bstep (se 1 (by rfl) ⟨3867911, by rfl⟩ : syracuseStep 5157215 = 7735823) B7735823
theorem B3438143 : Blo 2291435 3438143 := bstep (se 1 (by rfl) ⟨2578607, by rfl⟩ : syracuseStep 3438143 = 5157215) B5157215
theorem B2292095 : Blo 2291435 2292095 := bstep (se 1 (by rfl) ⟨1719071, by rfl⟩ : syracuseStep 2292095 = 3438143) B3438143
theorem B3438149 : Blo 2291435 3438149 := bbase (se 4 (by rfl) ⟨322326, by rfl⟩ : syracuseStep 3438149 = 644653) (by norm_num)
theorem B2292099 : Blo 2291435 2292099 := bstep (se 1 (by rfl) ⟨1719074, by rfl⟩ : syracuseStep 2292099 = 3438149) B3438149
theorem B3867925 : Blo 2291435 3867925 := bbase (se 6 (by rfl) ⟨90654, by rfl⟩ : syracuseStep 3867925 = 181309) (by norm_num)
theorem B5157233 : Blo 2291435 5157233 := bstep (se 2 (by rfl) ⟨1933962, by rfl⟩ : syracuseStep 5157233 = 3867925) B3867925
theorem B3438155 : Blo 2291435 3438155 := bstep (se 1 (by rfl) ⟨2578616, by rfl⟩ : syracuseStep 3438155 = 5157233) B5157233
theorem B2292103 : Blo 2291435 2292103 := bstep (se 1 (by rfl) ⟨1719077, by rfl⟩ : syracuseStep 2292103 = 3438155) B3438155
theorem B2578621 : Blo 2291435 2578621 := bbase (se 3 (by rfl) ⟨483491, by rfl⟩ : syracuseStep 2578621 = 966983) (by norm_num)
theorem B3438161 : Blo 2291435 3438161 := bstep (se 2 (by rfl) ⟨1289310, by rfl⟩ : syracuseStep 3438161 = 2578621) B2578621
theorem B2292107 : Blo 2291435 2292107 := bstep (se 1 (by rfl) ⟨1719080, by rfl⟩ : syracuseStep 2292107 = 3438161) B3438161
theorem B7735877 : Blo 2291435 7735877 := bbase (se 4 (by rfl) ⟨725238, by rfl⟩ : syracuseStep 7735877 = 1450477) (by norm_num)
theorem B5157251 : Blo 2291435 5157251 := bstep (se 1 (by rfl) ⟨3867938, by rfl⟩ : syracuseStep 5157251 = 7735877) B7735877
theorem B3438167 : Blo 2291435 3438167 := bstep (se 1 (by rfl) ⟨2578625, by rfl⟩ : syracuseStep 3438167 = 5157251) B5157251
theorem B2292111 : Blo 2291435 2292111 := bstep (se 1 (by rfl) ⟨1719083, by rfl⟩ : syracuseStep 2292111 = 3438167) B3438167
theorem B3438173 : Blo 2291435 3438173 := bbase (se 3 (by rfl) ⟨644657, by rfl⟩ : syracuseStep 3438173 = 1289315) (by norm_num)
theorem B2292115 : Blo 2291435 2292115 := bstep (se 1 (by rfl) ⟨1719086, by rfl⟩ : syracuseStep 2292115 = 3438173) B3438173
theorem B5157269 : Blo 2291435 5157269 := bbase (se 6 (by rfl) ⟨120873, by rfl⟩ : syracuseStep 5157269 = 241747) (by norm_num)
theorem B3438179 : Blo 2291435 3438179 := bstep (se 1 (by rfl) ⟨2578634, by rfl⟩ : syracuseStep 3438179 = 5157269) B5157269
theorem B2292119 : Blo 2291435 2292119 := bstep (se 1 (by rfl) ⟨1719089, by rfl⟩ : syracuseStep 2292119 = 3438179) B3438179
theorem B3021337 : Blo 2291435 3021337 := bbase (se 2 (by rfl) ⟨1133001, by rfl⟩ : syracuseStep 3021337 = 2266003) (by norm_num)
theorem B4028449 : Blo 2291435 4028449 := bstep (se 2 (by rfl) ⟨1510668, by rfl⟩ : syracuseStep 4028449 = 3021337) B3021337
theorem B5371265 : Blo 2291435 5371265 := bstep (se 2 (by rfl) ⟨2014224, by rfl⟩ : syracuseStep 5371265 = 4028449) B4028449
theorem B3580843 : Blo 2291435 3580843 := bstep (se 1 (by rfl) ⟨2685632, by rfl⟩ : syracuseStep 3580843 = 5371265) B5371265
theorem B4774457 : Blo 2291435 4774457 := bstep (se 2 (by rfl) ⟨1790421, by rfl⟩ : syracuseStep 4774457 = 3580843) B3580843
theorem B3182971 : Blo 2291435 3182971 := bstep (se 1 (by rfl) ⟨2387228, by rfl⟩ : syracuseStep 3182971 = 4774457) B4774457
theorem B4243961 : Blo 2291435 4243961 := bstep (se 2 (by rfl) ⟨1591485, by rfl⟩ : syracuseStep 4243961 = 3182971) B3182971
theorem B11317229 : Blo 2291435 11317229 := bstep (se 3 (by rfl) ⟨2121980, by rfl⟩ : syracuseStep 11317229 = 4243961) B4243961
theorem B7544819 : Blo 2291435 7544819 := bstep (se 1 (by rfl) ⟨5658614, by rfl⟩ : syracuseStep 7544819 = 11317229) B11317229
theorem B5029879 : Blo 2291435 5029879 := bstep (se 1 (by rfl) ⟨3772409, by rfl⟩ : syracuseStep 5029879 = 7544819) B7544819
theorem B6706505 : Blo 2291435 6706505 := bstep (se 2 (by rfl) ⟨2514939, by rfl⟩ : syracuseStep 6706505 = 5029879) B5029879
theorem B4471003 : Blo 2291435 4471003 := bstep (se 1 (by rfl) ⟨3353252, by rfl⟩ : syracuseStep 4471003 = 6706505) B6706505
theorem B5961337 : Blo 2291435 5961337 := bstep (se 2 (by rfl) ⟨2235501, by rfl⟩ : syracuseStep 5961337 = 4471003) B4471003
theorem B127175189 : Blo 2291435 127175189 := bstep (se 6 (by rfl) ⟨2980668, by rfl⟩ : syracuseStep 127175189 = 5961337) B5961337
theorem B339133837 : Blo 2291435 339133837 := bstep (se 3 (by rfl) ⟨63587594, by rfl⟩ : syracuseStep 339133837 = 127175189) B127175189
theorem B452178449 : Blo 2291435 452178449 := bstep (se 2 (by rfl) ⟨169566918, by rfl⟩ : syracuseStep 452178449 = 339133837) B339133837
theorem B301452299 : Blo 2291435 301452299 := bstep (se 1 (by rfl) ⟨226089224, by rfl⟩ : syracuseStep 301452299 = 452178449) B452178449
theorem B200968199 : Blo 2291435 200968199 := bstep (se 1 (by rfl) ⟨150726149, by rfl⟩ : syracuseStep 200968199 = 301452299) B301452299
theorem B133978799 : Blo 2291435 133978799 := bstep (se 1 (by rfl) ⟨100484099, by rfl⟩ : syracuseStep 133978799 = 200968199) B200968199
theorem B89319199 : Blo 2291435 89319199 := bstep (se 1 (by rfl) ⟨66989399, by rfl⟩ : syracuseStep 89319199 = 133978799) B133978799
theorem B119092265 : Blo 2291435 119092265 := bstep (se 2 (by rfl) ⟨44659599, by rfl⟩ : syracuseStep 119092265 = 89319199) B89319199
theorem B79394843 : Blo 2291435 79394843 := bstep (se 1 (by rfl) ⟨59546132, by rfl⟩ : syracuseStep 79394843 = 119092265) B119092265
theorem B52929895 : Blo 2291435 52929895 := bstep (se 1 (by rfl) ⟨39697421, by rfl⟩ : syracuseStep 52929895 = 79394843) B79394843
theorem B70573193 : Blo 2291435 70573193 := bstep (se 2 (by rfl) ⟨26464947, by rfl⟩ : syracuseStep 70573193 = 52929895) B52929895
theorem B47048795 : Blo 2291435 47048795 := bstep (se 1 (by rfl) ⟨35286596, by rfl⟩ : syracuseStep 47048795 = 70573193) B70573193
theorem B31365863 : Blo 2291435 31365863 := bstep (se 1 (by rfl) ⟨23524397, by rfl⟩ : syracuseStep 31365863 = 47048795) B47048795
theorem B20910575 : Blo 2291435 20910575 := bstep (se 1 (by rfl) ⟨15682931, by rfl⟩ : syracuseStep 20910575 = 31365863) B31365863
theorem B13940383 : Blo 2291435 13940383 := bstep (se 1 (by rfl) ⟨10455287, by rfl⟩ : syracuseStep 13940383 = 20910575) B20910575
theorem B18587177 : Blo 2291435 18587177 := bstep (se 2 (by rfl) ⟨6970191, by rfl⟩ : syracuseStep 18587177 = 13940383) B13940383
theorem B12391451 : Blo 2291435 12391451 := bstep (se 1 (by rfl) ⟨9293588, by rfl⟩ : syracuseStep 12391451 = 18587177) B18587177
theorem B8260967 : Blo 2291435 8260967 := bstep (se 1 (by rfl) ⟨6195725, by rfl⟩ : syracuseStep 8260967 = 12391451) B12391451
theorem B5507311 : Blo 2291435 5507311 := bstep (se 1 (by rfl) ⟨4130483, by rfl⟩ : syracuseStep 5507311 = 8260967) B8260967
theorem B7343081 : Blo 2291435 7343081 := bstep (se 2 (by rfl) ⟨2753655, by rfl⟩ : syracuseStep 7343081 = 5507311) B5507311
theorem B4895387 : Blo 2291435 4895387 := bstep (se 1 (by rfl) ⟨3671540, by rfl⟩ : syracuseStep 4895387 = 7343081) B7343081
theorem B3263591 : Blo 2291435 3263591 := bstep (se 1 (by rfl) ⟨2447693, by rfl⟩ : syracuseStep 3263591 = 4895387) B4895387
theorem B8702909 : Blo 2291435 8702909 := bstep (se 3 (by rfl) ⟨1631795, by rfl⟩ : syracuseStep 8702909 = 3263591) B3263591
theorem B5801939 : Blo 2291435 5801939 := bstep (se 1 (by rfl) ⟨4351454, by rfl⟩ : syracuseStep 5801939 = 8702909) B8702909
theorem B3867959 : Blo 2291435 3867959 := bstep (se 1 (by rfl) ⟨2900969, by rfl⟩ : syracuseStep 3867959 = 5801939) B5801939
theorem B2578639 : Blo 2291435 2578639 := bstep (se 1 (by rfl) ⟨1933979, by rfl⟩ : syracuseStep 2578639 = 3867959) B3867959
theorem B3438185 : Blo 2291435 3438185 := bstep (se 2 (by rfl) ⟨1289319, by rfl⟩ : syracuseStep 3438185 = 2578639) B2578639
theorem B2292123 : Blo 2291435 2292123 := bstep (se 1 (by rfl) ⟨1719092, by rfl⟩ : syracuseStep 2292123 = 3438185) B3438185
theorem B9790789 : Blo 2291435 9790789 := bbase (se 4 (by rfl) ⟨917886, by rfl⟩ : syracuseStep 9790789 = 1835773) (by norm_num)
theorem B13054385 : Blo 2291435 13054385 := bstep (se 2 (by rfl) ⟨4895394, by rfl⟩ : syracuseStep 13054385 = 9790789) B9790789
theorem B8702923 : Blo 2291435 8702923 := bstep (se 1 (by rfl) ⟨6527192, by rfl⟩ : syracuseStep 8702923 = 13054385) B13054385
theorem B11603897 : Blo 2291435 11603897 := bstep (se 2 (by rfl) ⟨4351461, by rfl⟩ : syracuseStep 11603897 = 8702923) B8702923
theorem B7735931 : Blo 2291435 7735931 := bstep (se 1 (by rfl) ⟨5801948, by rfl⟩ : syracuseStep 7735931 = 11603897) B11603897
theorem B5157287 : Blo 2291435 5157287 := bstep (se 1 (by rfl) ⟨3867965, by rfl⟩ : syracuseStep 5157287 = 7735931) B7735931
theorem B3438191 : Blo 2291435 3438191 := bstep (se 1 (by rfl) ⟨2578643, by rfl⟩ : syracuseStep 3438191 = 5157287) B5157287
theorem B2292127 : Blo 2291435 2292127 := bstep (se 1 (by rfl) ⟨1719095, by rfl⟩ : syracuseStep 2292127 = 3438191) B3438191
theorem B3438197 : Blo 2291435 3438197 := bbase (se 5 (by rfl) ⟨161165, by rfl⟩ : syracuseStep 3438197 = 322331) (by norm_num)
theorem B2292131 : Blo 2291435 2292131 := bstep (se 1 (by rfl) ⟨1719098, by rfl⟩ : syracuseStep 2292131 = 3438197) B3438197
theorem B4351477 : Blo 2291435 4351477 := bbase (se 5 (by rfl) ⟨203975, by rfl⟩ : syracuseStep 4351477 = 407951) (by norm_num)
theorem B5801969 : Blo 2291435 5801969 := bstep (se 2 (by rfl) ⟨2175738, by rfl⟩ : syracuseStep 5801969 = 4351477) B4351477
theorem B3867979 : Blo 2291435 3867979 := bstep (se 1 (by rfl) ⟨2900984, by rfl⟩ : syracuseStep 3867979 = 5801969) B5801969
theorem B5157305 : Blo 2291435 5157305 := bstep (se 2 (by rfl) ⟨1933989, by rfl⟩ : syracuseStep 5157305 = 3867979) B3867979
theorem B3438203 : Blo 2291435 3438203 := bstep (se 1 (by rfl) ⟨2578652, by rfl⟩ : syracuseStep 3438203 = 5157305) B5157305
theorem B2292135 : Blo 2291435 2292135 := bstep (se 1 (by rfl) ⟨1719101, by rfl⟩ : syracuseStep 2292135 = 3438203) B3438203
theorem B2578657 : Blo 2291435 2578657 := bbase (se 2 (by rfl) ⟨966996, by rfl⟩ : syracuseStep 2578657 = 1933993) (by norm_num)
theorem B3438209 : Blo 2291435 3438209 := bstep (se 2 (by rfl) ⟨1289328, by rfl⟩ : syracuseStep 3438209 = 2578657) B2578657
theorem B2292139 : Blo 2291435 2292139 := bstep (se 1 (by rfl) ⟨1719104, by rfl⟩ : syracuseStep 2292139 = 3438209) B3438209
theorem B5801989 : Blo 2291435 5801989 := bbase (se 4 (by rfl) ⟨543936, by rfl⟩ : syracuseStep 5801989 = 1087873) (by norm_num)
theorem B7735985 : Blo 2291435 7735985 := bstep (se 2 (by rfl) ⟨2900994, by rfl⟩ : syracuseStep 7735985 = 5801989) B5801989
theorem B5157323 : Blo 2291435 5157323 := bstep (se 1 (by rfl) ⟨3867992, by rfl⟩ : syracuseStep 5157323 = 7735985) B7735985
theorem B3438215 : Blo 2291435 3438215 := bstep (se 1 (by rfl) ⟨2578661, by rfl⟩ : syracuseStep 3438215 = 5157323) B5157323
theorem B2292143 : Blo 2291435 2292143 := bstep (se 1 (by rfl) ⟨1719107, by rfl⟩ : syracuseStep 2292143 = 3438215) B3438215
theorem B3438221 : Blo 2291435 3438221 := bbase (se 3 (by rfl) ⟨644666, by rfl⟩ : syracuseStep 3438221 = 1289333) (by norm_num)
theorem B2292147 : Blo 2291435 2292147 := bstep (se 1 (by rfl) ⟨1719110, by rfl⟩ : syracuseStep 2292147 = 3438221) B3438221
theorem B5157341 : Blo 2291435 5157341 := bbase (se 3 (by rfl) ⟨967001, by rfl⟩ : syracuseStep 5157341 = 1934003) (by norm_num)
theorem B3438227 : Blo 2291435 3438227 := bstep (se 1 (by rfl) ⟨2578670, by rfl⟩ : syracuseStep 3438227 = 5157341) B5157341
theorem B2292151 : Blo 2291435 2292151 := bstep (se 1 (by rfl) ⟨1719113, by rfl⟩ : syracuseStep 2292151 = 3438227) B3438227
theorem B3868013 : Blo 2291435 3868013 := bbase (se 3 (by rfl) ⟨725252, by rfl⟩ : syracuseStep 3868013 = 1450505) (by norm_num)
theorem B2578675 : Blo 2291435 2578675 := bstep (se 1 (by rfl) ⟨1934006, by rfl⟩ : syracuseStep 2578675 = 3868013) B3868013
theorem B3438233 : Blo 2291435 3438233 := bstep (se 2 (by rfl) ⟨1289337, by rfl⟩ : syracuseStep 3438233 = 2578675) B2578675
theorem B2292155 : Blo 2291435 2292155 := bstep (se 1 (by rfl) ⟨1719116, by rfl⟩ : syracuseStep 2292155 = 3438233) B3438233
theorem B3485149 : Blo 2291435 3485149 := bbase (se 3 (by rfl) ⟨653465, by rfl⟩ : syracuseStep 3485149 = 1306931) (by norm_num)
theorem B74349845 : Blo 2291435 74349845 := bstep (se 6 (by rfl) ⟨1742574, by rfl⟩ : syracuseStep 74349845 = 3485149) B3485149
theorem B49566563 : Blo 2291435 49566563 := bstep (se 1 (by rfl) ⟨37174922, by rfl⟩ : syracuseStep 49566563 = 74349845) B74349845
theorem B33044375 : Blo 2291435 33044375 := bstep (se 1 (by rfl) ⟨24783281, by rfl⟩ : syracuseStep 33044375 = 49566563) B49566563
theorem B22029583 : Blo 2291435 22029583 := bstep (se 1 (by rfl) ⟨16522187, by rfl⟩ : syracuseStep 22029583 = 33044375) B33044375
theorem B29372777 : Blo 2291435 29372777 := bstep (se 2 (by rfl) ⟨11014791, by rfl⟩ : syracuseStep 29372777 = 22029583) B22029583
theorem B19581851 : Blo 2291435 19581851 := bstep (se 1 (by rfl) ⟨14686388, by rfl⟩ : syracuseStep 19581851 = 29372777) B29372777
theorem B13054567 : Blo 2291435 13054567 := bstep (se 1 (by rfl) ⟨9790925, by rfl⟩ : syracuseStep 13054567 = 19581851) B19581851
theorem B17406089 : Blo 2291435 17406089 := bstep (se 2 (by rfl) ⟨6527283, by rfl⟩ : syracuseStep 17406089 = 13054567) B13054567
theorem B11604059 : Blo 2291435 11604059 := bstep (se 1 (by rfl) ⟨8703044, by rfl⟩ : syracuseStep 11604059 = 17406089) B17406089
theorem B7736039 : Blo 2291435 7736039 := bstep (se 1 (by rfl) ⟨5802029, by rfl⟩ : syracuseStep 7736039 = 11604059) B11604059
theorem B5157359 : Blo 2291435 5157359 := bstep (se 1 (by rfl) ⟨3868019, by rfl⟩ : syracuseStep 5157359 = 7736039) B7736039
theorem B3438239 : Blo 2291435 3438239 := bstep (se 1 (by rfl) ⟨2578679, by rfl⟩ : syracuseStep 3438239 = 5157359) B5157359
theorem B2292159 : Blo 2291435 2292159 := bstep (se 1 (by rfl) ⟨1719119, by rfl⟩ : syracuseStep 2292159 = 3438239) B3438239
theorem B3438245 : Blo 2291435 3438245 := bbase (se 4 (by rfl) ⟨322335, by rfl⟩ : syracuseStep 3438245 = 644671) (by norm_num)
theorem B2292163 : Blo 2291435 2292163 := bstep (se 1 (by rfl) ⟨1719122, by rfl⟩ : syracuseStep 2292163 = 3438245) B3438245
theorem B2901025 : Blo 2291435 2901025 := bbase (se 2 (by rfl) ⟨1087884, by rfl⟩ : syracuseStep 2901025 = 2175769) (by norm_num)
theorem B3868033 : Blo 2291435 3868033 := bstep (se 2 (by rfl) ⟨1450512, by rfl⟩ : syracuseStep 3868033 = 2901025) B2901025
theorem B5157377 : Blo 2291435 5157377 := bstep (se 2 (by rfl) ⟨1934016, by rfl⟩ : syracuseStep 5157377 = 3868033) B3868033
theorem B3438251 : Blo 2291435 3438251 := bstep (se 1 (by rfl) ⟨2578688, by rfl⟩ : syracuseStep 3438251 = 5157377) B5157377
theorem B2292167 : Blo 2291435 2292167 := bstep (se 1 (by rfl) ⟨1719125, by rfl⟩ : syracuseStep 2292167 = 3438251) B3438251
theorem B2578693 : Blo 2291435 2578693 := bbase (se 4 (by rfl) ⟨241752, by rfl⟩ : syracuseStep 2578693 = 483505) (by norm_num)
theorem B3438257 : Blo 2291435 3438257 := bstep (se 2 (by rfl) ⟨1289346, by rfl⟩ : syracuseStep 3438257 = 2578693) B2578693
theorem B2292171 : Blo 2291435 2292171 := bstep (se 1 (by rfl) ⟨1719128, by rfl⟩ : syracuseStep 2292171 = 3438257) B3438257
theorem B2447749 : Blo 2291435 2447749 := bbase (se 4 (by rfl) ⟨229476, by rfl⟩ : syracuseStep 2447749 = 458953) (by norm_num)
theorem B3263665 : Blo 2291435 3263665 := bstep (se 2 (by rfl) ⟨1223874, by rfl⟩ : syracuseStep 3263665 = 2447749) B2447749
theorem B4351553 : Blo 2291435 4351553 := bstep (se 2 (by rfl) ⟨1631832, by rfl⟩ : syracuseStep 4351553 = 3263665) B3263665
theorem B2901035 : Blo 2291435 2901035 := bstep (se 1 (by rfl) ⟨2175776, by rfl⟩ : syracuseStep 2901035 = 4351553) B4351553
theorem B7736093 : Blo 2291435 7736093 := bstep (se 3 (by rfl) ⟨1450517, by rfl⟩ : syracuseStep 7736093 = 2901035) B2901035
theorem B5157395 : Blo 2291435 5157395 := bstep (se 1 (by rfl) ⟨3868046, by rfl⟩ : syracuseStep 5157395 = 7736093) B7736093
theorem B3438263 : Blo 2291435 3438263 := bstep (se 1 (by rfl) ⟨2578697, by rfl⟩ : syracuseStep 3438263 = 5157395) B5157395
theorem B2292175 : Blo 2291435 2292175 := bstep (se 1 (by rfl) ⟨1719131, by rfl⟩ : syracuseStep 2292175 = 3438263) B3438263
theorem B3438269 : Blo 2291435 3438269 := bbase (se 3 (by rfl) ⟨644675, by rfl⟩ : syracuseStep 3438269 = 1289351) (by norm_num)
theorem B2292179 : Blo 2291435 2292179 := bstep (se 1 (by rfl) ⟨1719134, by rfl⟩ : syracuseStep 2292179 = 3438269) B3438269
theorem B5157413 : Blo 2291435 5157413 := bbase (se 4 (by rfl) ⟨483507, by rfl⟩ : syracuseStep 5157413 = 967015) (by norm_num)
theorem B3438275 : Blo 2291435 3438275 := bstep (se 1 (by rfl) ⟨2578706, by rfl⟩ : syracuseStep 3438275 = 5157413) B5157413
theorem B2292183 : Blo 2291435 2292183 := bstep (se 1 (by rfl) ⟨1719137, by rfl⟩ : syracuseStep 2292183 = 3438275) B3438275
theorem B5802101 : Blo 2291435 5802101 := bbase (se 5 (by rfl) ⟨271973, by rfl⟩ : syracuseStep 5802101 = 543947) (by norm_num)
theorem B3868067 : Blo 2291435 3868067 := bstep (se 1 (by rfl) ⟨2901050, by rfl⟩ : syracuseStep 3868067 = 5802101) B5802101
theorem B2578711 : Blo 2291435 2578711 := bstep (se 1 (by rfl) ⟨1934033, by rfl⟩ : syracuseStep 2578711 = 3868067) B3868067
theorem B3438281 : Blo 2291435 3438281 := bstep (se 2 (by rfl) ⟨1289355, by rfl⟩ : syracuseStep 3438281 = 2578711) B2578711
theorem B2292187 : Blo 2291435 2292187 := bstep (se 1 (by rfl) ⟨1719140, by rfl⟩ : syracuseStep 2292187 = 3438281) B3438281
theorem B4130605 : Blo 2291435 4130605 := bbase (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) (by norm_num)
theorem B22029893 : Blo 2291435 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B14686595 : Blo 2291435 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B9791063 : Blo 2291435 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B6527375 : Blo 2291435 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B4351583 : Blo 2291435 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B11604221 : Blo 2291435 11604221 := bstep (se 3 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 11604221 = 4351583) B4351583
theorem B7736147 : Blo 2291435 7736147 := bstep (se 1 (by rfl) ⟨5802110, by rfl⟩ : syracuseStep 7736147 = 11604221) B11604221
theorem B5157431 : Blo 2291435 5157431 := bstep (se 1 (by rfl) ⟨3868073, by rfl⟩ : syracuseStep 5157431 = 7736147) B7736147
theorem B3438287 : Blo 2291435 3438287 := bstep (se 1 (by rfl) ⟨2578715, by rfl⟩ : syracuseStep 3438287 = 5157431) B5157431
theorem B2292191 : Blo 2291435 2292191 := bstep (se 1 (by rfl) ⟨1719143, by rfl⟩ : syracuseStep 2292191 = 3438287) B3438287
theorem B3438293 : Blo 2291435 3438293 := bbase (se 7 (by rfl) ⟨40292, by rfl⟩ : syracuseStep 3438293 = 80585) (by norm_num)
theorem B2292195 : Blo 2291435 2292195 := bstep (se 1 (by rfl) ⟨1719146, by rfl⟩ : syracuseStep 2292195 = 3438293) B3438293
theorem B4895549 : Blo 2291435 4895549 := bbase (se 3 (by rfl) ⟨917915, by rfl⟩ : syracuseStep 4895549 = 1835831) (by norm_num)
theorem B3263699 : Blo 2291435 3263699 := bstep (se 1 (by rfl) ⟨2447774, by rfl⟩ : syracuseStep 3263699 = 4895549) B4895549
theorem B8703197 : Blo 2291435 8703197 := bstep (se 3 (by rfl) ⟨1631849, by rfl⟩ : syracuseStep 8703197 = 3263699) B3263699
theorem B5802131 : Blo 2291435 5802131 := bstep (se 1 (by rfl) ⟨4351598, by rfl⟩ : syracuseStep 5802131 = 8703197) B8703197
theorem B3868087 : Blo 2291435 3868087 := bstep (se 1 (by rfl) ⟨2901065, by rfl⟩ : syracuseStep 3868087 = 5802131) B5802131
theorem B5157449 : Blo 2291435 5157449 := bstep (se 2 (by rfl) ⟨1934043, by rfl⟩ : syracuseStep 5157449 = 3868087) B3868087
theorem B3438299 : Blo 2291435 3438299 := bstep (se 1 (by rfl) ⟨2578724, by rfl⟩ : syracuseStep 3438299 = 5157449) B5157449
theorem B2292199 : Blo 2291435 2292199 := bstep (se 1 (by rfl) ⟨1719149, by rfl⟩ : syracuseStep 2292199 = 3438299) B3438299
theorem B2578729 : Blo 2291435 2578729 := bbase (se 2 (by rfl) ⟨967023, by rfl⟩ : syracuseStep 2578729 = 1934047) (by norm_num)
theorem B3438305 : Blo 2291435 3438305 := bstep (se 2 (by rfl) ⟨1289364, by rfl⟩ : syracuseStep 3438305 = 2578729) B2578729
theorem B2292203 : Blo 2291435 2292203 := bstep (se 1 (by rfl) ⟨1719152, by rfl⟩ : syracuseStep 2292203 = 3438305) B3438305
theorem B5961557 : Blo 2291435 5961557 := bbase (se 9 (by rfl) ⟨17465, by rfl⟩ : syracuseStep 5961557 = 34931) (by norm_num)
theorem B15897485 : Blo 2291435 15897485 := bstep (se 3 (by rfl) ⟨2980778, by rfl⟩ : syracuseStep 15897485 = 5961557) B5961557
theorem B10598323 : Blo 2291435 10598323 := bstep (se 1 (by rfl) ⟨7948742, by rfl⟩ : syracuseStep 10598323 = 15897485) B15897485
theorem B14131097 : Blo 2291435 14131097 := bstep (se 2 (by rfl) ⟨5299161, by rfl⟩ : syracuseStep 14131097 = 10598323) B10598323
theorem B9420731 : Blo 2291435 9420731 := bstep (se 1 (by rfl) ⟨7065548, by rfl⟩ : syracuseStep 9420731 = 14131097) B14131097
theorem B6280487 : Blo 2291435 6280487 := bstep (se 1 (by rfl) ⟨4710365, by rfl⟩ : syracuseStep 6280487 = 9420731) B9420731
theorem B4186991 : Blo 2291435 4186991 := bstep (se 1 (by rfl) ⟨3140243, by rfl⟩ : syracuseStep 4186991 = 6280487) B6280487
theorem B11165309 : Blo 2291435 11165309 := bstep (se 3 (by rfl) ⟨2093495, by rfl⟩ : syracuseStep 11165309 = 4186991) B4186991
theorem B7443539 : Blo 2291435 7443539 := bstep (se 1 (by rfl) ⟨5582654, by rfl⟩ : syracuseStep 7443539 = 11165309) B11165309
theorem B4962359 : Blo 2291435 4962359 := bstep (se 1 (by rfl) ⟨3721769, by rfl⟩ : syracuseStep 4962359 = 7443539) B7443539
theorem B3308239 : Blo 2291435 3308239 := bstep (se 1 (by rfl) ⟨2481179, by rfl⟩ : syracuseStep 3308239 = 4962359) B4962359
theorem B4410985 : Blo 2291435 4410985 := bstep (se 2 (by rfl) ⟨1654119, by rfl⟩ : syracuseStep 4410985 = 3308239) B3308239
theorem B5881313 : Blo 2291435 5881313 := bstep (se 2 (by rfl) ⟨2205492, by rfl⟩ : syracuseStep 5881313 = 4410985) B4410985
theorem B15683501 : Blo 2291435 15683501 := bstep (se 3 (by rfl) ⟨2940656, by rfl⟩ : syracuseStep 15683501 = 5881313) B5881313
theorem B41822669 : Blo 2291435 41822669 := bstep (se 3 (by rfl) ⟨7841750, by rfl⟩ : syracuseStep 41822669 = 15683501) B15683501
theorem B27881779 : Blo 2291435 27881779 := bstep (se 1 (by rfl) ⟨20911334, by rfl⟩ : syracuseStep 27881779 = 41822669) B41822669
theorem B37175705 : Blo 2291435 37175705 := bstep (se 2 (by rfl) ⟨13940889, by rfl⟩ : syracuseStep 37175705 = 27881779) B27881779
theorem B24783803 : Blo 2291435 24783803 := bstep (se 1 (by rfl) ⟨18587852, by rfl⟩ : syracuseStep 24783803 = 37175705) B37175705
theorem B16522535 : Blo 2291435 16522535 := bstep (se 1 (by rfl) ⟨12391901, by rfl⟩ : syracuseStep 16522535 = 24783803) B24783803
theorem B11015023 : Blo 2291435 11015023 := bstep (se 1 (by rfl) ⟨8261267, by rfl⟩ : syracuseStep 11015023 = 16522535) B16522535
theorem B14686697 : Blo 2291435 14686697 := bstep (se 2 (by rfl) ⟨5507511, by rfl⟩ : syracuseStep 14686697 = 11015023) B11015023
theorem B9791131 : Blo 2291435 9791131 := bstep (se 1 (by rfl) ⟨7343348, by rfl⟩ : syracuseStep 9791131 = 14686697) B14686697
theorem B13054841 : Blo 2291435 13054841 := bstep (se 2 (by rfl) ⟨4895565, by rfl⟩ : syracuseStep 13054841 = 9791131) B9791131
theorem B8703227 : Blo 2291435 8703227 := bstep (se 1 (by rfl) ⟨6527420, by rfl⟩ : syracuseStep 8703227 = 13054841) B13054841
theorem B5802151 : Blo 2291435 5802151 := bstep (se 1 (by rfl) ⟨4351613, by rfl⟩ : syracuseStep 5802151 = 8703227) B8703227
theorem B7736201 : Blo 2291435 7736201 := bstep (se 2 (by rfl) ⟨2901075, by rfl⟩ : syracuseStep 7736201 = 5802151) B5802151
theorem B5157467 : Blo 2291435 5157467 := bstep (se 1 (by rfl) ⟨3868100, by rfl⟩ : syracuseStep 5157467 = 7736201) B7736201
theorem B3438311 : Blo 2291435 3438311 := bstep (se 1 (by rfl) ⟨2578733, by rfl⟩ : syracuseStep 3438311 = 5157467) B5157467
theorem B2292207 : Blo 2291435 2292207 := bstep (se 1 (by rfl) ⟨1719155, by rfl⟩ : syracuseStep 2292207 = 3438311) B3438311
theorem B3438317 : Blo 2291435 3438317 := bbase (se 3 (by rfl) ⟨644684, by rfl⟩ : syracuseStep 3438317 = 1289369) (by norm_num)
theorem B2292211 : Blo 2291435 2292211 := bstep (se 1 (by rfl) ⟨1719158, by rfl⟩ : syracuseStep 2292211 = 3438317) B3438317
theorem B5157485 : Blo 2291435 5157485 := bbase (se 3 (by rfl) ⟨967028, by rfl⟩ : syracuseStep 5157485 = 1934057) (by norm_num)
theorem B3438323 : Blo 2291435 3438323 := bstep (se 1 (by rfl) ⟨2578742, by rfl⟩ : syracuseStep 3438323 = 5157485) B5157485
theorem B2292215 : Blo 2291435 2292215 := bstep (se 1 (by rfl) ⟨1719161, by rfl⟩ : syracuseStep 2292215 = 3438323) B3438323
theorem B4351637 : Blo 2291435 4351637 := bbase (se 6 (by rfl) ⟨101991, by rfl⟩ : syracuseStep 4351637 = 203983) (by norm_num)
theorem B2901091 : Blo 2291435 2901091 := bstep (se 1 (by rfl) ⟨2175818, by rfl⟩ : syracuseStep 2901091 = 4351637) B4351637
theorem B3868121 : Blo 2291435 3868121 := bstep (se 2 (by rfl) ⟨1450545, by rfl⟩ : syracuseStep 3868121 = 2901091) B2901091
theorem B2578747 : Blo 2291435 2578747 := bstep (se 1 (by rfl) ⟨1934060, by rfl⟩ : syracuseStep 2578747 = 3868121) B3868121
theorem B3438329 : Blo 2291435 3438329 := bstep (se 2 (by rfl) ⟨1289373, by rfl⟩ : syracuseStep 3438329 = 2578747) B2578747
theorem B2292219 : Blo 2291435 2292219 := bstep (se 1 (by rfl) ⟨1719164, by rfl⟩ : syracuseStep 2292219 = 3438329) B3438329
theorem B83645909 : Blo 2291435 83645909 := bbase (se 7 (by rfl) ⟨980225, by rfl⟩ : syracuseStep 83645909 = 1960451) (by norm_num)
theorem B55763939 : Blo 2291435 55763939 := bstep (se 1 (by rfl) ⟨41822954, by rfl⟩ : syracuseStep 55763939 = 83645909) B83645909
theorem B37175959 : Blo 2291435 37175959 := bstep (se 1 (by rfl) ⟨27881969, by rfl⟩ : syracuseStep 37175959 = 55763939) B55763939
theorem B49567945 : Blo 2291435 49567945 := bstep (se 2 (by rfl) ⟨18587979, by rfl⟩ : syracuseStep 49567945 = 37175959) B37175959
theorem B66090593 : Blo 2291435 66090593 := bstep (se 2 (by rfl) ⟨24783972, by rfl⟩ : syracuseStep 66090593 = 49567945) B49567945
theorem B44060395 : Blo 2291435 44060395 := bstep (se 1 (by rfl) ⟨33045296, by rfl⟩ : syracuseStep 44060395 = 66090593) B66090593
theorem B58747193 : Blo 2291435 58747193 := bstep (se 2 (by rfl) ⟨22030197, by rfl⟩ : syracuseStep 58747193 = 44060395) B44060395
theorem B39164795 : Blo 2291435 39164795 := bstep (se 1 (by rfl) ⟨29373596, by rfl⟩ : syracuseStep 39164795 = 58747193) B58747193
theorem B26109863 : Blo 2291435 26109863 := bstep (se 1 (by rfl) ⟨19582397, by rfl⟩ : syracuseStep 26109863 = 39164795) B39164795
theorem B17406575 : Blo 2291435 17406575 := bstep (se 1 (by rfl) ⟨13054931, by rfl⟩ : syracuseStep 17406575 = 26109863) B26109863
theorem B11604383 : Blo 2291435 11604383 := bstep (se 1 (by rfl) ⟨8703287, by rfl⟩ : syracuseStep 11604383 = 17406575) B17406575
theorem B7736255 : Blo 2291435 7736255 := bstep (se 1 (by rfl) ⟨5802191, by rfl⟩ : syracuseStep 7736255 = 11604383) B11604383
theorem B5157503 : Blo 2291435 5157503 := bstep (se 1 (by rfl) ⟨3868127, by rfl⟩ : syracuseStep 5157503 = 7736255) B7736255
theorem B3438335 : Blo 2291435 3438335 := bstep (se 1 (by rfl) ⟨2578751, by rfl⟩ : syracuseStep 3438335 = 5157503) B5157503
theorem B2292223 : Blo 2291435 2292223 := bstep (se 1 (by rfl) ⟨1719167, by rfl⟩ : syracuseStep 2292223 = 3438335) B3438335
theorem B3438341 : Blo 2291435 3438341 := bbase (se 4 (by rfl) ⟨322344, by rfl⟩ : syracuseStep 3438341 = 644689) (by norm_num)
theorem B2292227 : Blo 2291435 2292227 := bstep (se 1 (by rfl) ⟨1719170, by rfl⟩ : syracuseStep 2292227 = 3438341) B3438341
theorem B3868141 : Blo 2291435 3868141 := bbase (se 3 (by rfl) ⟨725276, by rfl⟩ : syracuseStep 3868141 = 1450553) (by norm_num)
theorem B5157521 : Blo 2291435 5157521 := bstep (se 2 (by rfl) ⟨1934070, by rfl⟩ : syracuseStep 5157521 = 3868141) B3868141
theorem B3438347 : Blo 2291435 3438347 := bstep (se 1 (by rfl) ⟨2578760, by rfl⟩ : syracuseStep 3438347 = 5157521) B5157521
theorem B2292231 : Blo 2291435 2292231 := bstep (se 1 (by rfl) ⟨1719173, by rfl⟩ : syracuseStep 2292231 = 3438347) B3438347
theorem B2578765 : Blo 2291435 2578765 := bbase (se 3 (by rfl) ⟨483518, by rfl⟩ : syracuseStep 2578765 = 967037) (by norm_num)
theorem B3438353 : Blo 2291435 3438353 := bstep (se 2 (by rfl) ⟨1289382, by rfl⟩ : syracuseStep 3438353 = 2578765) B2578765
theorem B2292235 : Blo 2291435 2292235 := bstep (se 1 (by rfl) ⟨1719176, by rfl⟩ : syracuseStep 2292235 = 3438353) B3438353
theorem B7736309 : Blo 2291435 7736309 := bbase (se 5 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 7736309 = 725279) (by norm_num)
theorem B5157539 : Blo 2291435 5157539 := bstep (se 1 (by rfl) ⟨3868154, by rfl⟩ : syracuseStep 5157539 = 7736309) B7736309
theorem B3438359 : Blo 2291435 3438359 := bstep (se 1 (by rfl) ⟨2578769, by rfl⟩ : syracuseStep 3438359 = 5157539) B5157539
theorem B2292239 : Blo 2291435 2292239 := bstep (se 1 (by rfl) ⟨1719179, by rfl⟩ : syracuseStep 2292239 = 3438359) B3438359
theorem B3438365 : Blo 2291435 3438365 := bbase (se 3 (by rfl) ⟨644693, by rfl⟩ : syracuseStep 3438365 = 1289387) (by norm_num)
theorem B2292243 : Blo 2291435 2292243 := bstep (se 1 (by rfl) ⟨1719182, by rfl⟩ : syracuseStep 2292243 = 3438365) B3438365
theorem B5157557 : Blo 2291435 5157557 := bbase (se 5 (by rfl) ⟨241760, by rfl⟩ : syracuseStep 5157557 = 483521) (by norm_num)
theorem B3438371 : Blo 2291435 3438371 := bstep (se 1 (by rfl) ⟨2578778, by rfl⟩ : syracuseStep 3438371 = 5157557) B5157557
theorem B2292247 : Blo 2291435 2292247 := bstep (se 1 (by rfl) ⟨1719185, by rfl⟩ : syracuseStep 2292247 = 3438371) B3438371
theorem B13055093 : Blo 2291435 13055093 := bbase (se 5 (by rfl) ⟨611957, by rfl⟩ : syracuseStep 13055093 = 1223915) (by norm_num)
theorem B8703395 : Blo 2291435 8703395 := bstep (se 1 (by rfl) ⟨6527546, by rfl⟩ : syracuseStep 8703395 = 13055093) B13055093
theorem B5802263 : Blo 2291435 5802263 := bstep (se 1 (by rfl) ⟨4351697, by rfl⟩ : syracuseStep 5802263 = 8703395) B8703395
theorem B3868175 : Blo 2291435 3868175 := bstep (se 1 (by rfl) ⟨2901131, by rfl⟩ : syracuseStep 3868175 = 5802263) B5802263
theorem B2578783 : Blo 2291435 2578783 := bstep (se 1 (by rfl) ⟨1934087, by rfl⟩ : syracuseStep 2578783 = 3868175) B3868175
theorem B3438377 : Blo 2291435 3438377 := bstep (se 2 (by rfl) ⟨1289391, by rfl⟩ : syracuseStep 3438377 = 2578783) B2578783
theorem B2292251 : Blo 2291435 2292251 := bstep (se 1 (by rfl) ⟨1719188, by rfl⟩ : syracuseStep 2292251 = 3438377) B3438377
theorem B6527557 : Blo 2291435 6527557 := bbase (se 4 (by rfl) ⟨611958, by rfl⟩ : syracuseStep 6527557 = 1223917) (by norm_num)
theorem B8703409 : Blo 2291435 8703409 := bstep (se 2 (by rfl) ⟨3263778, by rfl⟩ : syracuseStep 8703409 = 6527557) B6527557
theorem B11604545 : Blo 2291435 11604545 := bstep (se 2 (by rfl) ⟨4351704, by rfl⟩ : syracuseStep 11604545 = 8703409) B8703409
theorem B7736363 : Blo 2291435 7736363 := bstep (se 1 (by rfl) ⟨5802272, by rfl⟩ : syracuseStep 7736363 = 11604545) B11604545
theorem B5157575 : Blo 2291435 5157575 := bstep (se 1 (by rfl) ⟨3868181, by rfl⟩ : syracuseStep 5157575 = 7736363) B7736363
theorem B3438383 : Blo 2291435 3438383 := bstep (se 1 (by rfl) ⟨2578787, by rfl⟩ : syracuseStep 3438383 = 5157575) B5157575
theorem B2292255 : Blo 2291435 2292255 := bstep (se 1 (by rfl) ⟨1719191, by rfl⟩ : syracuseStep 2292255 = 3438383) B3438383
theorem B3438389 : Blo 2291435 3438389 := bbase (se 5 (by rfl) ⟨161174, by rfl⟩ : syracuseStep 3438389 = 322349) (by norm_num)
theorem B2292259 : Blo 2291435 2292259 := bstep (se 1 (by rfl) ⟨1719194, by rfl⟩ : syracuseStep 2292259 = 3438389) B3438389
theorem B5802293 : Blo 2291435 5802293 := bbase (se 5 (by rfl) ⟨271982, by rfl⟩ : syracuseStep 5802293 = 543965) (by norm_num)
theorem B3868195 : Blo 2291435 3868195 := bstep (se 1 (by rfl) ⟨2901146, by rfl⟩ : syracuseStep 3868195 = 5802293) B5802293
theorem B5157593 : Blo 2291435 5157593 := bstep (se 2 (by rfl) ⟨1934097, by rfl⟩ : syracuseStep 5157593 = 3868195) B3868195
theorem B3438395 : Blo 2291435 3438395 := bstep (se 1 (by rfl) ⟨2578796, by rfl⟩ : syracuseStep 3438395 = 5157593) B5157593
theorem B2292263 : Blo 2291435 2292263 := bstep (se 1 (by rfl) ⟨1719197, by rfl⟩ : syracuseStep 2292263 = 3438395) B3438395
theorem B2578801 : Blo 2291435 2578801 := bbase (se 2 (by rfl) ⟨967050, by rfl⟩ : syracuseStep 2578801 = 1934101) (by norm_num)
theorem B3438401 : Blo 2291435 3438401 := bstep (se 2 (by rfl) ⟨1289400, by rfl⟩ : syracuseStep 3438401 = 2578801) B2578801
theorem B2292267 : Blo 2291435 2292267 := bstep (se 1 (by rfl) ⟨1719200, by rfl⟩ : syracuseStep 2292267 = 3438401) B3438401
theorem B2753833 : Blo 2291435 2753833 := bbase (se 2 (by rfl) ⟨1032687, by rfl⟩ : syracuseStep 2753833 = 2065375) (by norm_num)
theorem B3671777 : Blo 2291435 3671777 := bstep (se 2 (by rfl) ⟨1376916, by rfl⟩ : syracuseStep 3671777 = 2753833) B2753833
theorem B9791405 : Blo 2291435 9791405 := bstep (se 3 (by rfl) ⟨1835888, by rfl⟩ : syracuseStep 9791405 = 3671777) B3671777
theorem B6527603 : Blo 2291435 6527603 := bstep (se 1 (by rfl) ⟨4895702, by rfl⟩ : syracuseStep 6527603 = 9791405) B9791405
theorem B4351735 : Blo 2291435 4351735 := bstep (se 1 (by rfl) ⟨3263801, by rfl⟩ : syracuseStep 4351735 = 6527603) B6527603
theorem B5802313 : Blo 2291435 5802313 := bstep (se 2 (by rfl) ⟨2175867, by rfl⟩ : syracuseStep 5802313 = 4351735) B4351735
theorem B7736417 : Blo 2291435 7736417 := bstep (se 2 (by rfl) ⟨2901156, by rfl⟩ : syracuseStep 7736417 = 5802313) B5802313
theorem B5157611 : Blo 2291435 5157611 := bstep (se 1 (by rfl) ⟨3868208, by rfl⟩ : syracuseStep 5157611 = 7736417) B7736417
theorem B3438407 : Blo 2291435 3438407 := bstep (se 1 (by rfl) ⟨2578805, by rfl⟩ : syracuseStep 3438407 = 5157611) B5157611
theorem B2292271 : Blo 2291435 2292271 := bstep (se 1 (by rfl) ⟨1719203, by rfl⟩ : syracuseStep 2292271 = 3438407) B3438407
theorem B3438413 : Blo 2291435 3438413 := bbase (se 3 (by rfl) ⟨644702, by rfl⟩ : syracuseStep 3438413 = 1289405) (by norm_num)
theorem B2292275 : Blo 2291435 2292275 := bstep (se 1 (by rfl) ⟨1719206, by rfl⟩ : syracuseStep 2292275 = 3438413) B3438413
theorem B5157629 : Blo 2291435 5157629 := bbase (se 3 (by rfl) ⟨967055, by rfl⟩ : syracuseStep 5157629 = 1934111) (by norm_num)
theorem B3438419 : Blo 2291435 3438419 := bstep (se 1 (by rfl) ⟨2578814, by rfl⟩ : syracuseStep 3438419 = 5157629) B5157629
theorem B2292279 : Blo 2291435 2292279 := bstep (se 1 (by rfl) ⟨1719209, by rfl⟩ : syracuseStep 2292279 = 3438419) B3438419
theorem B3868229 : Blo 2291435 3868229 := bbase (se 4 (by rfl) ⟨362646, by rfl⟩ : syracuseStep 3868229 = 725293) (by norm_num)
theorem B2578819 : Blo 2291435 2578819 := bstep (se 1 (by rfl) ⟨1934114, by rfl⟩ : syracuseStep 2578819 = 3868229) B3868229
theorem B3438425 : Blo 2291435 3438425 := bstep (se 2 (by rfl) ⟨1289409, by rfl⟩ : syracuseStep 3438425 = 2578819) B2578819
theorem B2292283 : Blo 2291435 2292283 := bstep (se 1 (by rfl) ⟨1719212, by rfl⟩ : syracuseStep 2292283 = 3438425) B3438425
theorem B17407061 : Blo 2291435 17407061 := bbase (se 8 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 17407061 = 203989) (by norm_num)
theorem B11604707 : Blo 2291435 11604707 := bstep (se 1 (by rfl) ⟨8703530, by rfl⟩ : syracuseStep 11604707 = 17407061) B17407061
theorem B7736471 : Blo 2291435 7736471 := bstep (se 1 (by rfl) ⟨5802353, by rfl⟩ : syracuseStep 7736471 = 11604707) B11604707
theorem B5157647 : Blo 2291435 5157647 := bstep (se 1 (by rfl) ⟨3868235, by rfl⟩ : syracuseStep 5157647 = 7736471) B7736471
theorem B3438431 : Blo 2291435 3438431 := bstep (se 1 (by rfl) ⟨2578823, by rfl⟩ : syracuseStep 3438431 = 5157647) B5157647
theorem B2292287 : Blo 2291435 2292287 := bstep (se 1 (by rfl) ⟨1719215, by rfl⟩ : syracuseStep 2292287 = 3438431) B3438431
theorem B3438437 : Blo 2291435 3438437 := bbase (se 4 (by rfl) ⟨322353, by rfl⟩ : syracuseStep 3438437 = 644707) (by norm_num)
theorem B2292291 : Blo 2291435 2292291 := bstep (se 1 (by rfl) ⟨1719218, by rfl⟩ : syracuseStep 2292291 = 3438437) B3438437
theorem B4351781 : Blo 2291435 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B2901187 : Blo 2291435 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B3868249 : Blo 2291435 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B5157665 : Blo 2291435 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B3438443 : Blo 2291435 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B2292295 : Blo 2291435 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B2578837 : Blo 2291435 2578837 := bbase (se 6 (by rfl) ⟨60441, by rfl⟩ : syracuseStep 2578837 = 120883) (by norm_num)
theorem B3438449 : Blo 2291435 3438449 := bstep (se 2 (by rfl) ⟨1289418, by rfl⟩ : syracuseStep 3438449 = 2578837) B2578837
theorem B2292299 : Blo 2291435 2292299 := bstep (se 1 (by rfl) ⟨1719224, by rfl⟩ : syracuseStep 2292299 = 3438449) B3438449
theorem B2901197 : Blo 2291435 2901197 := bbase (se 3 (by rfl) ⟨543974, by rfl⟩ : syracuseStep 2901197 = 1087949) (by norm_num)
theorem B7736525 : Blo 2291435 7736525 := bstep (se 3 (by rfl) ⟨1450598, by rfl⟩ : syracuseStep 7736525 = 2901197) B2901197
theorem B5157683 : Blo 2291435 5157683 := bstep (se 1 (by rfl) ⟨3868262, by rfl⟩ : syracuseStep 5157683 = 7736525) B7736525
theorem B3438455 : Blo 2291435 3438455 := bstep (se 1 (by rfl) ⟨2578841, by rfl⟩ : syracuseStep 3438455 = 5157683) B5157683
theorem B2292303 : Blo 2291435 2292303 := bstep (se 1 (by rfl) ⟨1719227, by rfl⟩ : syracuseStep 2292303 = 3438455) B3438455
theorem B3438461 : Blo 2291435 3438461 := bbase (se 3 (by rfl) ⟨644711, by rfl⟩ : syracuseStep 3438461 = 1289423) (by norm_num)
theorem B2292307 : Blo 2291435 2292307 := bstep (se 1 (by rfl) ⟨1719230, by rfl⟩ : syracuseStep 2292307 = 3438461) B3438461
theorem B5157701 : Blo 2291435 5157701 := bbase (se 4 (by rfl) ⟨483534, by rfl⟩ : syracuseStep 5157701 = 967069) (by norm_num)
theorem B3438467 : Blo 2291435 3438467 := bstep (se 1 (by rfl) ⟨2578850, by rfl⟩ : syracuseStep 3438467 = 5157701) B5157701
theorem B2292311 : Blo 2291435 2292311 := bstep (se 1 (by rfl) ⟨1719233, by rfl⟩ : syracuseStep 2292311 = 3438467) B3438467
theorem B4895797 : Blo 2291435 4895797 := bbase (se 5 (by rfl) ⟨229490, by rfl⟩ : syracuseStep 4895797 = 458981) (by norm_num)
theorem B6527729 : Blo 2291435 6527729 := bstep (se 2 (by rfl) ⟨2447898, by rfl⟩ : syracuseStep 6527729 = 4895797) B4895797
theorem B4351819 : Blo 2291435 4351819 := bstep (se 1 (by rfl) ⟨3263864, by rfl⟩ : syracuseStep 4351819 = 6527729) B6527729
theorem B5802425 : Blo 2291435 5802425 := bstep (se 2 (by rfl) ⟨2175909, by rfl⟩ : syracuseStep 5802425 = 4351819) B4351819
theorem B3868283 : Blo 2291435 3868283 := bstep (se 1 (by rfl) ⟨2901212, by rfl⟩ : syracuseStep 3868283 = 5802425) B5802425
theorem B2578855 : Blo 2291435 2578855 := bstep (se 1 (by rfl) ⟨1934141, by rfl⟩ : syracuseStep 2578855 = 3868283) B3868283
theorem B3438473 : Blo 2291435 3438473 := bstep (se 2 (by rfl) ⟨1289427, by rfl⟩ : syracuseStep 3438473 = 2578855) B2578855
theorem B2292315 : Blo 2291435 2292315 := bstep (se 1 (by rfl) ⟨1719236, by rfl⟩ : syracuseStep 2292315 = 3438473) B3438473
theorem B11604869 : Blo 2291435 11604869 := bbase (se 4 (by rfl) ⟨1087956, by rfl⟩ : syracuseStep 11604869 = 2175913) (by norm_num)
theorem B7736579 : Blo 2291435 7736579 := bstep (se 1 (by rfl) ⟨5802434, by rfl⟩ : syracuseStep 7736579 = 11604869) B11604869
theorem B5157719 : Blo 2291435 5157719 := bstep (se 1 (by rfl) ⟨3868289, by rfl⟩ : syracuseStep 5157719 = 7736579) B7736579
theorem B3438479 : Blo 2291435 3438479 := bstep (se 1 (by rfl) ⟨2578859, by rfl⟩ : syracuseStep 3438479 = 5157719) B5157719
theorem B2292319 : Blo 2291435 2292319 := bstep (se 1 (by rfl) ⟨1719239, by rfl⟩ : syracuseStep 2292319 = 3438479) B3438479
theorem B3438485 : Blo 2291435 3438485 := bbase (se 6 (by rfl) ⟨80589, by rfl⟩ : syracuseStep 3438485 = 161179) (by norm_num)
theorem B2292323 : Blo 2291435 2292323 := bstep (se 1 (by rfl) ⟨1719242, by rfl⟩ : syracuseStep 2292323 = 3438485) B3438485
theorem B6196277 : Blo 2291435 6196277 := bbase (se 5 (by rfl) ⟨290450, by rfl⟩ : syracuseStep 6196277 = 580901) (by norm_num)
theorem B4130851 : Blo 2291435 4130851 := bstep (se 1 (by rfl) ⟨3098138, by rfl⟩ : syracuseStep 4130851 = 6196277) B6196277
theorem B5507801 : Blo 2291435 5507801 := bstep (se 2 (by rfl) ⟨2065425, by rfl⟩ : syracuseStep 5507801 = 4130851) B4130851
theorem B3671867 : Blo 2291435 3671867 := bstep (se 1 (by rfl) ⟨2753900, by rfl⟩ : syracuseStep 3671867 = 5507801) B5507801
theorem B2447911 : Blo 2291435 2447911 := bstep (se 1 (by rfl) ⟨1835933, by rfl⟩ : syracuseStep 2447911 = 3671867) B3671867
theorem B13055525 : Blo 2291435 13055525 := bstep (se 4 (by rfl) ⟨1223955, by rfl⟩ : syracuseStep 13055525 = 2447911) B2447911
theorem B8703683 : Blo 2291435 8703683 := bstep (se 1 (by rfl) ⟨6527762, by rfl⟩ : syracuseStep 8703683 = 13055525) B13055525
theorem B5802455 : Blo 2291435 5802455 := bstep (se 1 (by rfl) ⟨4351841, by rfl⟩ : syracuseStep 5802455 = 8703683) B8703683
theorem B3868303 : Blo 2291435 3868303 := bstep (se 1 (by rfl) ⟨2901227, by rfl⟩ : syracuseStep 3868303 = 5802455) B5802455
theorem B5157737 : Blo 2291435 5157737 := bstep (se 2 (by rfl) ⟨1934151, by rfl⟩ : syracuseStep 5157737 = 3868303) B3868303
theorem B3438491 : Blo 2291435 3438491 := bstep (se 1 (by rfl) ⟨2578868, by rfl⟩ : syracuseStep 3438491 = 5157737) B5157737
theorem B2292327 : Blo 2291435 2292327 := bstep (se 1 (by rfl) ⟨1719245, by rfl⟩ : syracuseStep 2292327 = 3438491) B3438491
theorem B2578873 : Blo 2291435 2578873 := bbase (se 2 (by rfl) ⟨967077, by rfl⟩ : syracuseStep 2578873 = 1934155) (by norm_num)
theorem B3438497 : Blo 2291435 3438497 := bstep (se 2 (by rfl) ⟨1289436, by rfl⟩ : syracuseStep 3438497 = 2578873) B2578873
theorem B2292331 : Blo 2291435 2292331 := bstep (se 1 (by rfl) ⟨1719248, by rfl⟩ : syracuseStep 2292331 = 3438497) B3438497
theorem B4962637 : Blo 2291435 4962637 := bbase (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) (by norm_num)
theorem B6616849 : Blo 2291435 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B8822465 : Blo 2291435 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B5881643 : Blo 2291435 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B3921095 : Blo 2291435 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B10456253 : Blo 2291435 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B6970835 : Blo 2291435 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B4647223 : Blo 2291435 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B24785189 : Blo 2291435 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B16523459 : Blo 2291435 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B11015639 : Blo 2291435 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B7343759 : Blo 2291435 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B4895839 : Blo 2291435 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B6527785 : Blo 2291435 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B8703713 : Blo 2291435 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B5802475 : Blo 2291435 5802475 := bstep (se 1 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 5802475 = 8703713) B8703713
theorem B7736633 : Blo 2291435 7736633 := bstep (se 2 (by rfl) ⟨2901237, by rfl⟩ : syracuseStep 7736633 = 5802475) B5802475
theorem B5157755 : Blo 2291435 5157755 := bstep (se 1 (by rfl) ⟨3868316, by rfl⟩ : syracuseStep 5157755 = 7736633) B7736633
theorem B3438503 : Blo 2291435 3438503 := bstep (se 1 (by rfl) ⟨2578877, by rfl⟩ : syracuseStep 3438503 = 5157755) B5157755
theorem B2292335 : Blo 2291435 2292335 := bstep (se 1 (by rfl) ⟨1719251, by rfl⟩ : syracuseStep 2292335 = 3438503) B3438503
theorem B3438509 : Blo 2291435 3438509 := bbase (se 3 (by rfl) ⟨644720, by rfl⟩ : syracuseStep 3438509 = 1289441) (by norm_num)
theorem B2292339 : Blo 2291435 2292339 := bstep (se 1 (by rfl) ⟨1719254, by rfl⟩ : syracuseStep 2292339 = 3438509) B3438509
theorem B5157773 : Blo 2291435 5157773 := bbase (se 3 (by rfl) ⟨967082, by rfl⟩ : syracuseStep 5157773 = 1934165) (by norm_num)
theorem B3438515 : Blo 2291435 3438515 := bstep (se 1 (by rfl) ⟨2578886, by rfl⟩ : syracuseStep 3438515 = 5157773) B5157773
theorem B2292343 : Blo 2291435 2292343 := bstep (se 1 (by rfl) ⟨1719257, by rfl⟩ : syracuseStep 2292343 = 3438515) B3438515
theorem B2901253 : Blo 2291435 2901253 := bbase (se 4 (by rfl) ⟨271992, by rfl⟩ : syracuseStep 2901253 = 543985) (by norm_num)
theorem B3868337 : Blo 2291435 3868337 := bstep (se 2 (by rfl) ⟨1450626, by rfl⟩ : syracuseStep 3868337 = 2901253) B2901253
theorem B2578891 : Blo 2291435 2578891 := bstep (se 1 (by rfl) ⟨1934168, by rfl⟩ : syracuseStep 2578891 = 3868337) B3868337
theorem B3438521 : Blo 2291435 3438521 := bstep (se 2 (by rfl) ⟨1289445, by rfl⟩ : syracuseStep 3438521 = 2578891) B2578891
theorem B2292347 : Blo 2291435 2292347 := bstep (se 1 (by rfl) ⟨1719260, by rfl⟩ : syracuseStep 2292347 = 3438521) B3438521
theorem B4130893 : Blo 2291435 4130893 := bbase (se 3 (by rfl) ⟨774542, by rfl⟩ : syracuseStep 4130893 = 1549085) (by norm_num)
theorem B5507857 : Blo 2291435 5507857 := bstep (se 2 (by rfl) ⟨2065446, by rfl⟩ : syracuseStep 5507857 = 4130893) B4130893
theorem B29375237 : Blo 2291435 29375237 := bstep (se 4 (by rfl) ⟨2753928, by rfl⟩ : syracuseStep 29375237 = 5507857) B5507857
theorem B19583491 : Blo 2291435 19583491 := bstep (se 1 (by rfl) ⟨14687618, by rfl⟩ : syracuseStep 19583491 = 29375237) B29375237
theorem B26111321 : Blo 2291435 26111321 := bstep (se 2 (by rfl) ⟨9791745, by rfl⟩ : syracuseStep 26111321 = 19583491) B19583491
theorem B17407547 : Blo 2291435 17407547 := bstep (se 1 (by rfl) ⟨13055660, by rfl⟩ : syracuseStep 17407547 = 26111321) B26111321
theorem B11605031 : Blo 2291435 11605031 := bstep (se 1 (by rfl) ⟨8703773, by rfl⟩ : syracuseStep 11605031 = 17407547) B17407547
theorem B7736687 : Blo 2291435 7736687 := bstep (se 1 (by rfl) ⟨5802515, by rfl⟩ : syracuseStep 7736687 = 11605031) B11605031
theorem B5157791 : Blo 2291435 5157791 := bstep (se 1 (by rfl) ⟨3868343, by rfl⟩ : syracuseStep 5157791 = 7736687) B7736687
theorem B3438527 : Blo 2291435 3438527 := bstep (se 1 (by rfl) ⟨2578895, by rfl⟩ : syracuseStep 3438527 = 5157791) B5157791
theorem B2292351 : Blo 2291435 2292351 := bstep (se 1 (by rfl) ⟨1719263, by rfl⟩ : syracuseStep 2292351 = 3438527) B3438527
theorem B3438533 : Blo 2291435 3438533 := bbase (se 4 (by rfl) ⟨322362, by rfl⟩ : syracuseStep 3438533 = 644725) (by norm_num)
theorem B2292355 : Blo 2291435 2292355 := bstep (se 1 (by rfl) ⟨1719266, by rfl⟩ : syracuseStep 2292355 = 3438533) B3438533
theorem B3868357 : Blo 2291435 3868357 := bbase (se 4 (by rfl) ⟨362658, by rfl⟩ : syracuseStep 3868357 = 725317) (by norm_num)
theorem B5157809 : Blo 2291435 5157809 := bstep (se 2 (by rfl) ⟨1934178, by rfl⟩ : syracuseStep 5157809 = 3868357) B3868357
theorem B3438539 : Blo 2291435 3438539 := bstep (se 1 (by rfl) ⟨2578904, by rfl⟩ : syracuseStep 3438539 = 5157809) B5157809
theorem B2292359 : Blo 2291435 2292359 := bstep (se 1 (by rfl) ⟨1719269, by rfl⟩ : syracuseStep 2292359 = 3438539) B3438539
theorem B2578909 : Blo 2291435 2578909 := bbase (se 3 (by rfl) ⟨483545, by rfl⟩ : syracuseStep 2578909 = 967091) (by norm_num)
theorem B3438545 : Blo 2291435 3438545 := bstep (se 2 (by rfl) ⟨1289454, by rfl⟩ : syracuseStep 3438545 = 2578909) B2578909
theorem B2292363 : Blo 2291435 2292363 := bstep (se 1 (by rfl) ⟨1719272, by rfl⟩ : syracuseStep 2292363 = 3438545) B3438545
theorem B7736741 : Blo 2291435 7736741 := bbase (se 4 (by rfl) ⟨725319, by rfl⟩ : syracuseStep 7736741 = 1450639) (by norm_num)
theorem B5157827 : Blo 2291435 5157827 := bstep (se 1 (by rfl) ⟨3868370, by rfl⟩ : syracuseStep 5157827 = 7736741) B7736741
theorem B3438551 : Blo 2291435 3438551 := bstep (se 1 (by rfl) ⟨2578913, by rfl⟩ : syracuseStep 3438551 = 5157827) B5157827
theorem B2292367 : Blo 2291435 2292367 := bstep (se 1 (by rfl) ⟨1719275, by rfl⟩ : syracuseStep 2292367 = 3438551) B3438551
theorem B3438557 : Blo 2291435 3438557 := bbase (se 3 (by rfl) ⟨644729, by rfl⟩ : syracuseStep 3438557 = 1289459) (by norm_num)
theorem B2292371 : Blo 2291435 2292371 := bstep (se 1 (by rfl) ⟨1719278, by rfl⟩ : syracuseStep 2292371 = 3438557) B3438557
theorem B5157845 : Blo 2291435 5157845 := bbase (se 7 (by rfl) ⟨60443, by rfl⟩ : syracuseStep 5157845 = 120887) (by norm_num)
theorem B3438563 : Blo 2291435 3438563 := bstep (se 1 (by rfl) ⟨2578922, by rfl⟩ : syracuseStep 3438563 = 5157845) B5157845
theorem B2292375 : Blo 2291435 2292375 := bstep (se 1 (by rfl) ⟨1719281, by rfl⟩ : syracuseStep 2292375 = 3438563) B3438563
theorem B7842341 : Blo 2291435 7842341 := bbase (se 4 (by rfl) ⟨735219, by rfl⟩ : syracuseStep 7842341 = 1470439) (by norm_num)
theorem B5228227 : Blo 2291435 5228227 := bstep (se 1 (by rfl) ⟨3921170, by rfl⟩ : syracuseStep 5228227 = 7842341) B7842341
theorem B6970969 : Blo 2291435 6970969 := bstep (se 2 (by rfl) ⟨2614113, by rfl⟩ : syracuseStep 6970969 = 5228227) B5228227
theorem B9294625 : Blo 2291435 9294625 := bstep (se 2 (by rfl) ⟨3485484, by rfl⟩ : syracuseStep 9294625 = 6970969) B6970969
theorem B12392833 : Blo 2291435 12392833 := bstep (se 2 (by rfl) ⟨4647312, by rfl⟩ : syracuseStep 12392833 = 9294625) B9294625
theorem B16523777 : Blo 2291435 16523777 := bstep (se 2 (by rfl) ⟨6196416, by rfl⟩ : syracuseStep 16523777 = 12392833) B12392833
theorem B11015851 : Blo 2291435 11015851 := bstep (se 1 (by rfl) ⟨8261888, by rfl⟩ : syracuseStep 11015851 = 16523777) B16523777
theorem B14687801 : Blo 2291435 14687801 := bstep (se 2 (by rfl) ⟨5507925, by rfl⟩ : syracuseStep 14687801 = 11015851) B11015851
theorem B9791867 : Blo 2291435 9791867 := bstep (se 1 (by rfl) ⟨7343900, by rfl⟩ : syracuseStep 9791867 = 14687801) B14687801
theorem B6527911 : Blo 2291435 6527911 := bstep (se 1 (by rfl) ⟨4895933, by rfl⟩ : syracuseStep 6527911 = 9791867) B9791867
theorem B8703881 : Blo 2291435 8703881 := bstep (se 2 (by rfl) ⟨3263955, by rfl⟩ : syracuseStep 8703881 = 6527911) B6527911
theorem B5802587 : Blo 2291435 5802587 := bstep (se 1 (by rfl) ⟨4351940, by rfl⟩ : syracuseStep 5802587 = 8703881) B8703881
theorem B3868391 : Blo 2291435 3868391 := bstep (se 1 (by rfl) ⟨2901293, by rfl⟩ : syracuseStep 3868391 = 5802587) B5802587
theorem B2578927 : Blo 2291435 2578927 := bstep (se 1 (by rfl) ⟨1934195, by rfl⟩ : syracuseStep 2578927 = 3868391) B3868391
theorem B3438569 : Blo 2291435 3438569 := bstep (se 2 (by rfl) ⟨1289463, by rfl⟩ : syracuseStep 3438569 = 2578927) B2578927
theorem B2292379 : Blo 2291435 2292379 := bstep (se 1 (by rfl) ⟨1719284, by rfl⟩ : syracuseStep 2292379 = 3438569) B3438569
theorem B19583765 : Blo 2291435 19583765 := bbase (se 6 (by rfl) ⟨458994, by rfl⟩ : syracuseStep 19583765 = 917989) (by norm_num)
theorem B13055843 : Blo 2291435 13055843 := bstep (se 1 (by rfl) ⟨9791882, by rfl⟩ : syracuseStep 13055843 = 19583765) B19583765
theorem B8703895 : Blo 2291435 8703895 := bstep (se 1 (by rfl) ⟨6527921, by rfl⟩ : syracuseStep 8703895 = 13055843) B13055843
theorem B11605193 : Blo 2291435 11605193 := bstep (se 2 (by rfl) ⟨4351947, by rfl⟩ : syracuseStep 11605193 = 8703895) B8703895
theorem B7736795 : Blo 2291435 7736795 := bstep (se 1 (by rfl) ⟨5802596, by rfl⟩ : syracuseStep 7736795 = 11605193) B11605193
theorem B5157863 : Blo 2291435 5157863 := bstep (se 1 (by rfl) ⟨3868397, by rfl⟩ : syracuseStep 5157863 = 7736795) B7736795
theorem B3438575 : Blo 2291435 3438575 := bstep (se 1 (by rfl) ⟨2578931, by rfl⟩ : syracuseStep 3438575 = 5157863) B5157863
theorem B2292383 : Blo 2291435 2292383 := bstep (se 1 (by rfl) ⟨1719287, by rfl⟩ : syracuseStep 2292383 = 3438575) B3438575
theorem B3438581 : Blo 2291435 3438581 := bbase (se 5 (by rfl) ⟨161183, by rfl⟩ : syracuseStep 3438581 = 322367) (by norm_num)
theorem B2292387 : Blo 2291435 2292387 := bstep (se 1 (by rfl) ⟨1719290, by rfl⟩ : syracuseStep 2292387 = 3438581) B3438581
theorem B11015909 : Blo 2291435 11015909 := bbase (se 4 (by rfl) ⟨1032741, by rfl⟩ : syracuseStep 11015909 = 2065483) (by norm_num)
theorem B7343939 : Blo 2291435 7343939 := bstep (se 1 (by rfl) ⟨5507954, by rfl⟩ : syracuseStep 7343939 = 11015909) B11015909
theorem B4895959 : Blo 2291435 4895959 := bstep (se 1 (by rfl) ⟨3671969, by rfl⟩ : syracuseStep 4895959 = 7343939) B7343939
theorem B6527945 : Blo 2291435 6527945 := bstep (se 2 (by rfl) ⟨2447979, by rfl⟩ : syracuseStep 6527945 = 4895959) B4895959
theorem B4351963 : Blo 2291435 4351963 := bstep (se 1 (by rfl) ⟨3263972, by rfl⟩ : syracuseStep 4351963 = 6527945) B6527945
theorem B5802617 : Blo 2291435 5802617 := bstep (se 2 (by rfl) ⟨2175981, by rfl⟩ : syracuseStep 5802617 = 4351963) B4351963
theorem B3868411 : Blo 2291435 3868411 := bstep (se 1 (by rfl) ⟨2901308, by rfl⟩ : syracuseStep 3868411 = 5802617) B5802617
theorem B5157881 : Blo 2291435 5157881 := bstep (se 2 (by rfl) ⟨1934205, by rfl⟩ : syracuseStep 5157881 = 3868411) B3868411
theorem B3438587 : Blo 2291435 3438587 := bstep (se 1 (by rfl) ⟨2578940, by rfl⟩ : syracuseStep 3438587 = 5157881) B5157881
theorem B2292391 : Blo 2291435 2292391 := bstep (se 1 (by rfl) ⟨1719293, by rfl⟩ : syracuseStep 2292391 = 3438587) B3438587
theorem B2578945 : Blo 2291435 2578945 := bbase (se 2 (by rfl) ⟨967104, by rfl⟩ : syracuseStep 2578945 = 1934209) (by norm_num)
theorem B3438593 : Blo 2291435 3438593 := bstep (se 2 (by rfl) ⟨1289472, by rfl⟩ : syracuseStep 3438593 = 2578945) B2578945
theorem B2292395 : Blo 2291435 2292395 := bstep (se 1 (by rfl) ⟨1719296, by rfl⟩ : syracuseStep 2292395 = 3438593) B3438593
theorem B5802637 : Blo 2291435 5802637 := bbase (se 3 (by rfl) ⟨1087994, by rfl⟩ : syracuseStep 5802637 = 2175989) (by norm_num)
theorem B7736849 : Blo 2291435 7736849 := bstep (se 2 (by rfl) ⟨2901318, by rfl⟩ : syracuseStep 7736849 = 5802637) B5802637
theorem B5157899 : Blo 2291435 5157899 := bstep (se 1 (by rfl) ⟨3868424, by rfl⟩ : syracuseStep 5157899 = 7736849) B7736849
theorem B3438599 : Blo 2291435 3438599 := bstep (se 1 (by rfl) ⟨2578949, by rfl⟩ : syracuseStep 3438599 = 5157899) B5157899
theorem B2292399 : Blo 2291435 2292399 := bstep (se 1 (by rfl) ⟨1719299, by rfl⟩ : syracuseStep 2292399 = 3438599) B3438599
theorem B3438605 : Blo 2291435 3438605 := bbase (se 3 (by rfl) ⟨644738, by rfl⟩ : syracuseStep 3438605 = 1289477) (by norm_num)
theorem B2292403 : Blo 2291435 2292403 := bstep (se 1 (by rfl) ⟨1719302, by rfl⟩ : syracuseStep 2292403 = 3438605) B3438605
theorem B5157917 : Blo 2291435 5157917 := bbase (se 3 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 5157917 = 1934219) (by norm_num)
theorem B3438611 : Blo 2291435 3438611 := bstep (se 1 (by rfl) ⟨2578958, by rfl⟩ : syracuseStep 3438611 = 5157917) B5157917
theorem B2292407 : Blo 2291435 2292407 := bstep (se 1 (by rfl) ⟨1719305, by rfl⟩ : syracuseStep 2292407 = 3438611) B3438611
theorem B3868445 : Blo 2291435 3868445 := bbase (se 3 (by rfl) ⟨725333, by rfl⟩ : syracuseStep 3868445 = 1450667) (by norm_num)
theorem B2578963 : Blo 2291435 2578963 := bstep (se 1 (by rfl) ⟨1934222, by rfl⟩ : syracuseStep 2578963 = 3868445) B3868445
theorem B3438617 : Blo 2291435 3438617 := bstep (se 2 (by rfl) ⟨1289481, by rfl⟩ : syracuseStep 3438617 = 2578963) B2578963
theorem B2292411 : Blo 2291435 2292411 := bstep (se 1 (by rfl) ⟨1719308, by rfl⟩ : syracuseStep 2292411 = 3438617) B3438617
theorem B5228309 : Blo 2291435 5228309 := bbase (se 6 (by rfl) ⟨122538, by rfl⟩ : syracuseStep 5228309 = 245077) (by norm_num)
theorem B3485539 : Blo 2291435 3485539 := bstep (se 1 (by rfl) ⟨2614154, by rfl⟩ : syracuseStep 3485539 = 5228309) B5228309
theorem B4647385 : Blo 2291435 4647385 := bstep (se 2 (by rfl) ⟨1742769, by rfl⟩ : syracuseStep 4647385 = 3485539) B3485539
theorem B6196513 : Blo 2291435 6196513 := bstep (se 2 (by rfl) ⟨2323692, by rfl⟩ : syracuseStep 6196513 = 4647385) B4647385
theorem B8262017 : Blo 2291435 8262017 := bstep (se 2 (by rfl) ⟨3098256, by rfl⟩ : syracuseStep 8262017 = 6196513) B6196513
theorem B5508011 : Blo 2291435 5508011 := bstep (se 1 (by rfl) ⟨4131008, by rfl⟩ : syracuseStep 5508011 = 8262017) B8262017
theorem B14688029 : Blo 2291435 14688029 := bstep (se 3 (by rfl) ⟨2754005, by rfl⟩ : syracuseStep 14688029 = 5508011) B5508011
theorem B9792019 : Blo 2291435 9792019 := bstep (se 1 (by rfl) ⟨7344014, by rfl⟩ : syracuseStep 9792019 = 14688029) B14688029
theorem B13056025 : Blo 2291435 13056025 := bstep (se 2 (by rfl) ⟨4896009, by rfl⟩ : syracuseStep 13056025 = 9792019) B9792019
theorem B17408033 : Blo 2291435 17408033 := bstep (se 2 (by rfl) ⟨6528012, by rfl⟩ : syracuseStep 17408033 = 13056025) B13056025
theorem B11605355 : Blo 2291435 11605355 := bstep (se 1 (by rfl) ⟨8704016, by rfl⟩ : syracuseStep 11605355 = 17408033) B17408033
theorem B7736903 : Blo 2291435 7736903 := bstep (se 1 (by rfl) ⟨5802677, by rfl⟩ : syracuseStep 7736903 = 11605355) B11605355
theorem B5157935 : Blo 2291435 5157935 := bstep (se 1 (by rfl) ⟨3868451, by rfl⟩ : syracuseStep 5157935 = 7736903) B7736903
theorem B3438623 : Blo 2291435 3438623 := bstep (se 1 (by rfl) ⟨2578967, by rfl⟩ : syracuseStep 3438623 = 5157935) B5157935
theorem B2292415 : Blo 2291435 2292415 := bstep (se 1 (by rfl) ⟨1719311, by rfl⟩ : syracuseStep 2292415 = 3438623) B3438623
theorem B3438629 : Blo 2291435 3438629 := bbase (se 4 (by rfl) ⟨322371, by rfl⟩ : syracuseStep 3438629 = 644743) (by norm_num)
theorem B2292419 : Blo 2291435 2292419 := bstep (se 1 (by rfl) ⟨1719314, by rfl⟩ : syracuseStep 2292419 = 3438629) B3438629
theorem B2901349 : Blo 2291435 2901349 := bbase (se 4 (by rfl) ⟨272001, by rfl⟩ : syracuseStep 2901349 = 544003) (by norm_num)
theorem B3868465 : Blo 2291435 3868465 := bstep (se 2 (by rfl) ⟨1450674, by rfl⟩ : syracuseStep 3868465 = 2901349) B2901349
theorem B5157953 : Blo 2291435 5157953 := bstep (se 2 (by rfl) ⟨1934232, by rfl⟩ : syracuseStep 5157953 = 3868465) B3868465
theorem B3438635 : Blo 2291435 3438635 := bstep (se 1 (by rfl) ⟨2578976, by rfl⟩ : syracuseStep 3438635 = 5157953) B5157953
theorem B2292423 : Blo 2291435 2292423 := bstep (se 1 (by rfl) ⟨1719317, by rfl⟩ : syracuseStep 2292423 = 3438635) B3438635
theorem B2578981 : Blo 2291435 2578981 := bbase (se 4 (by rfl) ⟨241779, by rfl⟩ : syracuseStep 2578981 = 483559) (by norm_num)
theorem B3438641 : Blo 2291435 3438641 := bstep (se 2 (by rfl) ⟨1289490, by rfl⟩ : syracuseStep 3438641 = 2578981) B2578981
theorem B2292427 : Blo 2291435 2292427 := bstep (se 1 (by rfl) ⟨1719320, by rfl⟩ : syracuseStep 2292427 = 3438641) B3438641
theorem B11016101 : Blo 2291435 11016101 := bbase (se 4 (by rfl) ⟨1032759, by rfl⟩ : syracuseStep 11016101 = 2065519) (by norm_num)
theorem B7344067 : Blo 2291435 7344067 := bstep (se 1 (by rfl) ⟨5508050, by rfl⟩ : syracuseStep 7344067 = 11016101) B11016101
theorem B9792089 : Blo 2291435 9792089 := bstep (se 2 (by rfl) ⟨3672033, by rfl⟩ : syracuseStep 9792089 = 7344067) B7344067
theorem B6528059 : Blo 2291435 6528059 := bstep (se 1 (by rfl) ⟨4896044, by rfl⟩ : syracuseStep 6528059 = 9792089) B9792089
theorem B4352039 : Blo 2291435 4352039 := bstep (se 1 (by rfl) ⟨3264029, by rfl⟩ : syracuseStep 4352039 = 6528059) B6528059
theorem B2901359 : Blo 2291435 2901359 := bstep (se 1 (by rfl) ⟨2176019, by rfl⟩ : syracuseStep 2901359 = 4352039) B4352039
theorem B7736957 : Blo 2291435 7736957 := bstep (se 3 (by rfl) ⟨1450679, by rfl⟩ : syracuseStep 7736957 = 2901359) B2901359
theorem B5157971 : Blo 2291435 5157971 := bstep (se 1 (by rfl) ⟨3868478, by rfl⟩ : syracuseStep 5157971 = 7736957) B7736957
theorem B3438647 : Blo 2291435 3438647 := bstep (se 1 (by rfl) ⟨2578985, by rfl⟩ : syracuseStep 3438647 = 5157971) B5157971
theorem B2292431 : Blo 2291435 2292431 := bstep (se 1 (by rfl) ⟨1719323, by rfl⟩ : syracuseStep 2292431 = 3438647) B3438647
theorem B3438653 : Blo 2291435 3438653 := bbase (se 3 (by rfl) ⟨644747, by rfl⟩ : syracuseStep 3438653 = 1289495) (by norm_num)
theorem B2292435 : Blo 2291435 2292435 := bstep (se 1 (by rfl) ⟨1719326, by rfl⟩ : syracuseStep 2292435 = 3438653) B3438653
theorem B5157989 : Blo 2291435 5157989 := bbase (se 4 (by rfl) ⟨483561, by rfl⟩ : syracuseStep 5157989 = 967123) (by norm_num)
theorem B3438659 : Blo 2291435 3438659 := bstep (se 1 (by rfl) ⟨2578994, by rfl⟩ : syracuseStep 3438659 = 5157989) B5157989
theorem B2292439 : Blo 2291435 2292439 := bstep (se 1 (by rfl) ⟨1719329, by rfl⟩ : syracuseStep 2292439 = 3438659) B3438659
theorem B5802749 : Blo 2291435 5802749 := bbase (se 3 (by rfl) ⟨1088015, by rfl⟩ : syracuseStep 5802749 = 2176031) (by norm_num)
theorem B3868499 : Blo 2291435 3868499 := bstep (se 1 (by rfl) ⟨2901374, by rfl⟩ : syracuseStep 3868499 = 5802749) B5802749
theorem B2578999 : Blo 2291435 2578999 := bstep (se 1 (by rfl) ⟨1934249, by rfl⟩ : syracuseStep 2578999 = 3868499) B3868499
theorem B3438665 : Blo 2291435 3438665 := bstep (se 2 (by rfl) ⟨1289499, by rfl⟩ : syracuseStep 3438665 = 2578999) B2578999
theorem B2292443 : Blo 2291435 2292443 := bstep (se 1 (by rfl) ⟨1719332, by rfl⟩ : syracuseStep 2292443 = 3438665) B3438665
theorem B4352069 : Blo 2291435 4352069 := bbase (se 4 (by rfl) ⟨408006, by rfl⟩ : syracuseStep 4352069 = 816013) (by norm_num)
theorem B11605517 : Blo 2291435 11605517 := bstep (se 3 (by rfl) ⟨2176034, by rfl⟩ : syracuseStep 11605517 = 4352069) B4352069
theorem B7737011 : Blo 2291435 7737011 := bstep (se 1 (by rfl) ⟨5802758, by rfl⟩ : syracuseStep 7737011 = 11605517) B11605517
theorem B5158007 : Blo 2291435 5158007 := bstep (se 1 (by rfl) ⟨3868505, by rfl⟩ : syracuseStep 5158007 = 7737011) B7737011
theorem B3438671 : Blo 2291435 3438671 := bstep (se 1 (by rfl) ⟨2579003, by rfl⟩ : syracuseStep 3438671 = 5158007) B5158007
theorem B2292447 : Blo 2291435 2292447 := bstep (se 1 (by rfl) ⟨1719335, by rfl⟩ : syracuseStep 2292447 = 3438671) B3438671
theorem B3438677 : Blo 2291435 3438677 := bbase (se 8 (by rfl) ⟨20148, by rfl⟩ : syracuseStep 3438677 = 40297) (by norm_num)
theorem B2292451 : Blo 2291435 2292451 := bstep (se 1 (by rfl) ⟨1719338, by rfl⟩ : syracuseStep 2292451 = 3438677) B3438677
theorem B33499541 : Blo 2291435 33499541 := bbase (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) (by norm_num)
theorem B89332109 : Blo 2291435 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B59554739 : Blo 2291435 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B39703159 : Blo 2291435 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B52937545 : Blo 2291435 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B70583393 : Blo 2291435 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B47055595 : Blo 2291435 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B62740793 : Blo 2291435 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B41827195 : Blo 2291435 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B55769593 : Blo 2291435 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B74359457 : Blo 2291435 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B49572971 : Blo 2291435 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B33048647 : Blo 2291435 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B22032431 : Blo 2291435 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B14688287 : Blo 2291435 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B9792191 : Blo 2291435 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B6528127 : Blo 2291435 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B8704169 : Blo 2291435 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B5802779 : Blo 2291435 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B3868519 : Blo 2291435 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B5158025 : Blo 2291435 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B3438683 : Blo 2291435 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B2292455 : Blo 2291435 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B2579017 : Blo 2291435 2579017 := bbase (se 2 (by rfl) ⟨967131, by rfl⟩ : syracuseStep 2579017 = 1934263) (by norm_num)
theorem B3438689 : Blo 2291435 3438689 := bstep (se 2 (by rfl) ⟨1289508, by rfl⟩ : syracuseStep 3438689 = 2579017) B2579017
theorem B2292459 : Blo 2291435 2292459 := bstep (se 1 (by rfl) ⟨1719344, by rfl⟩ : syracuseStep 2292459 = 3438689) B3438689
theorem B9294965 : Blo 2291435 9294965 := bbase (se 5 (by rfl) ⟨435701, by rfl⟩ : syracuseStep 9294965 = 871403) (by norm_num)
theorem B6196643 : Blo 2291435 6196643 := bstep (se 1 (by rfl) ⟨4647482, by rfl⟩ : syracuseStep 6196643 = 9294965) B9294965
theorem B4131095 : Blo 2291435 4131095 := bstep (se 1 (by rfl) ⟨3098321, by rfl⟩ : syracuseStep 4131095 = 6196643) B6196643
theorem B11016253 : Blo 2291435 11016253 := bstep (se 3 (by rfl) ⟨2065547, by rfl⟩ : syracuseStep 11016253 = 4131095) B4131095
theorem B14688337 : Blo 2291435 14688337 := bstep (se 2 (by rfl) ⟨5508126, by rfl⟩ : syracuseStep 14688337 = 11016253) B11016253
theorem B19584449 : Blo 2291435 19584449 := bstep (se 2 (by rfl) ⟨7344168, by rfl⟩ : syracuseStep 19584449 = 14688337) B14688337
theorem B13056299 : Blo 2291435 13056299 := bstep (se 1 (by rfl) ⟨9792224, by rfl⟩ : syracuseStep 13056299 = 19584449) B19584449
theorem B8704199 : Blo 2291435 8704199 := bstep (se 1 (by rfl) ⟨6528149, by rfl⟩ : syracuseStep 8704199 = 13056299) B13056299
theorem B5802799 : Blo 2291435 5802799 := bstep (se 1 (by rfl) ⟨4352099, by rfl⟩ : syracuseStep 5802799 = 8704199) B8704199
theorem B7737065 : Blo 2291435 7737065 := bstep (se 2 (by rfl) ⟨2901399, by rfl⟩ : syracuseStep 7737065 = 5802799) B5802799
theorem B5158043 : Blo 2291435 5158043 := bstep (se 1 (by rfl) ⟨3868532, by rfl⟩ : syracuseStep 5158043 = 7737065) B7737065
theorem B3438695 : Blo 2291435 3438695 := bstep (se 1 (by rfl) ⟨2579021, by rfl⟩ : syracuseStep 3438695 = 5158043) B5158043
theorem B2292463 : Blo 2291435 2292463 := bstep (se 1 (by rfl) ⟨1719347, by rfl⟩ : syracuseStep 2292463 = 3438695) B3438695
theorem B3438701 : Blo 2291435 3438701 := bbase (se 3 (by rfl) ⟨644756, by rfl⟩ : syracuseStep 3438701 = 1289513) (by norm_num)
theorem B2292467 : Blo 2291435 2292467 := bstep (se 1 (by rfl) ⟨1719350, by rfl⟩ : syracuseStep 2292467 = 3438701) B3438701
theorem B5158061 : Blo 2291435 5158061 := bbase (se 3 (by rfl) ⟨967136, by rfl⟩ : syracuseStep 5158061 = 1934273) (by norm_num)
theorem B3438707 : Blo 2291435 3438707 := bstep (se 1 (by rfl) ⟨2579030, by rfl⟩ : syracuseStep 3438707 = 5158061) B5158061
theorem B2292471 : Blo 2291435 2292471 := bstep (se 1 (by rfl) ⟨1719353, by rfl⟩ : syracuseStep 2292471 = 3438707) B3438707
theorem B5508157 : Blo 2291435 5508157 := bbase (se 3 (by rfl) ⟨1032779, by rfl⟩ : syracuseStep 5508157 = 2065559) (by norm_num)
theorem B7344209 : Blo 2291435 7344209 := bstep (se 2 (by rfl) ⟨2754078, by rfl⟩ : syracuseStep 7344209 = 5508157) B5508157
theorem B4896139 : Blo 2291435 4896139 := bstep (se 1 (by rfl) ⟨3672104, by rfl⟩ : syracuseStep 4896139 = 7344209) B7344209
theorem B6528185 : Blo 2291435 6528185 := bstep (se 2 (by rfl) ⟨2448069, by rfl⟩ : syracuseStep 6528185 = 4896139) B4896139
theorem B4352123 : Blo 2291435 4352123 := bstep (se 1 (by rfl) ⟨3264092, by rfl⟩ : syracuseStep 4352123 = 6528185) B6528185
theorem B2901415 : Blo 2291435 2901415 := bstep (se 1 (by rfl) ⟨2176061, by rfl⟩ : syracuseStep 2901415 = 4352123) B4352123
theorem B3868553 : Blo 2291435 3868553 := bstep (se 2 (by rfl) ⟨1450707, by rfl⟩ : syracuseStep 3868553 = 2901415) B2901415
theorem B2579035 : Blo 2291435 2579035 := bstep (se 1 (by rfl) ⟨1934276, by rfl⟩ : syracuseStep 2579035 = 3868553) B3868553
theorem B3438713 : Blo 2291435 3438713 := bstep (se 2 (by rfl) ⟨1289517, by rfl⟩ : syracuseStep 3438713 = 2579035) B2579035
theorem B2292475 : Blo 2291435 2292475 := bstep (se 1 (by rfl) ⟨1719356, by rfl⟩ : syracuseStep 2292475 = 3438713) B3438713
theorem B47056085 : Blo 2291435 47056085 := bbase (se 7 (by rfl) ⟨551438, by rfl⟩ : syracuseStep 47056085 = 1102877) (by norm_num)
theorem B31370723 : Blo 2291435 31370723 := bstep (se 1 (by rfl) ⟨23528042, by rfl⟩ : syracuseStep 31370723 = 47056085) B47056085
theorem B20913815 : Blo 2291435 20913815 := bstep (se 1 (by rfl) ⟨15685361, by rfl⟩ : syracuseStep 20913815 = 31370723) B31370723
theorem B13942543 : Blo 2291435 13942543 := bstep (se 1 (by rfl) ⟨10456907, by rfl⟩ : syracuseStep 13942543 = 20913815) B20913815
theorem B18590057 : Blo 2291435 18590057 := bstep (se 2 (by rfl) ⟨6971271, by rfl⟩ : syracuseStep 18590057 = 13942543) B13942543
theorem B12393371 : Blo 2291435 12393371 := bstep (se 1 (by rfl) ⟨9295028, by rfl⟩ : syracuseStep 12393371 = 18590057) B18590057
theorem B8262247 : Blo 2291435 8262247 := bstep (se 1 (by rfl) ⟨6196685, by rfl⟩ : syracuseStep 8262247 = 12393371) B12393371
theorem B11016329 : Blo 2291435 11016329 := bstep (se 2 (by rfl) ⟨4131123, by rfl⟩ : syracuseStep 11016329 = 8262247) B8262247
theorem B29376877 : Blo 2291435 29376877 := bstep (se 3 (by rfl) ⟨5508164, by rfl⟩ : syracuseStep 29376877 = 11016329) B11016329
theorem B39169169 : Blo 2291435 39169169 := bstep (se 2 (by rfl) ⟨14688438, by rfl⟩ : syracuseStep 39169169 = 29376877) B29376877
theorem B26112779 : Blo 2291435 26112779 := bstep (se 1 (by rfl) ⟨19584584, by rfl⟩ : syracuseStep 26112779 = 39169169) B39169169
theorem B17408519 : Blo 2291435 17408519 := bstep (se 1 (by rfl) ⟨13056389, by rfl⟩ : syracuseStep 17408519 = 26112779) B26112779
theorem B11605679 : Blo 2291435 11605679 := bstep (se 1 (by rfl) ⟨8704259, by rfl⟩ : syracuseStep 11605679 = 17408519) B17408519
theorem B7737119 : Blo 2291435 7737119 := bstep (se 1 (by rfl) ⟨5802839, by rfl⟩ : syracuseStep 7737119 = 11605679) B11605679
theorem B5158079 : Blo 2291435 5158079 := bstep (se 1 (by rfl) ⟨3868559, by rfl⟩ : syracuseStep 5158079 = 7737119) B7737119
theorem B3438719 : Blo 2291435 3438719 := bstep (se 1 (by rfl) ⟨2579039, by rfl⟩ : syracuseStep 3438719 = 5158079) B5158079
theorem B2292479 : Blo 2291435 2292479 := bstep (se 1 (by rfl) ⟨1719359, by rfl⟩ : syracuseStep 2292479 = 3438719) B3438719
theorem B3438725 : Blo 2291435 3438725 := bbase (se 4 (by rfl) ⟨322380, by rfl⟩ : syracuseStep 3438725 = 644761) (by norm_num)
theorem B2292483 : Blo 2291435 2292483 := bstep (se 1 (by rfl) ⟨1719362, by rfl⟩ : syracuseStep 2292483 = 3438725) B3438725
theorem B3868573 : Blo 2291435 3868573 := bbase (se 3 (by rfl) ⟨725357, by rfl⟩ : syracuseStep 3868573 = 1450715) (by norm_num)
theorem B5158097 : Blo 2291435 5158097 := bstep (se 2 (by rfl) ⟨1934286, by rfl⟩ : syracuseStep 5158097 = 3868573) B3868573
theorem B3438731 : Blo 2291435 3438731 := bstep (se 1 (by rfl) ⟨2579048, by rfl⟩ : syracuseStep 3438731 = 5158097) B5158097
theorem B2292487 : Blo 2291435 2292487 := bstep (se 1 (by rfl) ⟨1719365, by rfl⟩ : syracuseStep 2292487 = 3438731) B3438731
theorem B2579053 : Blo 2291435 2579053 := bbase (se 3 (by rfl) ⟨483572, by rfl⟩ : syracuseStep 2579053 = 967145) (by norm_num)
theorem B3438737 : Blo 2291435 3438737 := bstep (se 2 (by rfl) ⟨1289526, by rfl⟩ : syracuseStep 3438737 = 2579053) B2579053
theorem B2292491 : Blo 2291435 2292491 := bstep (se 1 (by rfl) ⟨1719368, by rfl⟩ : syracuseStep 2292491 = 3438737) B3438737
theorem B7737173 : Blo 2291435 7737173 := bbase (se 9 (by rfl) ⟨22667, by rfl⟩ : syracuseStep 7737173 = 45335) (by norm_num)
theorem B5158115 : Blo 2291435 5158115 := bstep (se 1 (by rfl) ⟨3868586, by rfl⟩ : syracuseStep 5158115 = 7737173) B7737173
theorem B3438743 : Blo 2291435 3438743 := bstep (se 1 (by rfl) ⟨2579057, by rfl⟩ : syracuseStep 3438743 = 5158115) B5158115
theorem B2292495 : Blo 2291435 2292495 := bstep (se 1 (by rfl) ⟨1719371, by rfl⟩ : syracuseStep 2292495 = 3438743) B3438743
theorem B3438749 : Blo 2291435 3438749 := bbase (se 3 (by rfl) ⟨644765, by rfl⟩ : syracuseStep 3438749 = 1289531) (by norm_num)
theorem B2292499 : Blo 2291435 2292499 := bstep (se 1 (by rfl) ⟨1719374, by rfl⟩ : syracuseStep 2292499 = 3438749) B3438749
theorem B5158133 : Blo 2291435 5158133 := bbase (se 5 (by rfl) ⟨241787, by rfl⟩ : syracuseStep 5158133 = 483575) (by norm_num)
theorem B3438755 : Blo 2291435 3438755 := bstep (se 1 (by rfl) ⟨2579066, by rfl⟩ : syracuseStep 3438755 = 5158133) B5158133
theorem B2292503 : Blo 2291435 2292503 := bstep (se 1 (by rfl) ⟨1719377, by rfl⟩ : syracuseStep 2292503 = 3438755) B3438755
theorem B3098381 : Blo 2291435 3098381 := bbase (se 3 (by rfl) ⟨580946, by rfl⟩ : syracuseStep 3098381 = 1161893) (by norm_num)
theorem B33049397 : Blo 2291435 33049397 := bstep (se 5 (by rfl) ⟨1549190, by rfl⟩ : syracuseStep 33049397 = 3098381) B3098381
theorem B22032931 : Blo 2291435 22032931 := bstep (se 1 (by rfl) ⟨16524698, by rfl⟩ : syracuseStep 22032931 = 33049397) B33049397
theorem B29377241 : Blo 2291435 29377241 := bstep (se 2 (by rfl) ⟨11016465, by rfl⟩ : syracuseStep 29377241 = 22032931) B22032931
theorem B19584827 : Blo 2291435 19584827 := bstep (se 1 (by rfl) ⟨14688620, by rfl⟩ : syracuseStep 19584827 = 29377241) B29377241
theorem B13056551 : Blo 2291435 13056551 := bstep (se 1 (by rfl) ⟨9792413, by rfl⟩ : syracuseStep 13056551 = 19584827) B19584827
theorem B8704367 : Blo 2291435 8704367 := bstep (se 1 (by rfl) ⟨6528275, by rfl⟩ : syracuseStep 8704367 = 13056551) B13056551
theorem B5802911 : Blo 2291435 5802911 := bstep (se 1 (by rfl) ⟨4352183, by rfl⟩ : syracuseStep 5802911 = 8704367) B8704367
theorem B3868607 : Blo 2291435 3868607 := bstep (se 1 (by rfl) ⟨2901455, by rfl⟩ : syracuseStep 3868607 = 5802911) B5802911
theorem B2579071 : Blo 2291435 2579071 := bstep (se 1 (by rfl) ⟨1934303, by rfl⟩ : syracuseStep 2579071 = 3868607) B3868607
theorem B3438761 : Blo 2291435 3438761 := bstep (se 2 (by rfl) ⟨1289535, by rfl⟩ : syracuseStep 3438761 = 2579071) B2579071
theorem B2292507 : Blo 2291435 2292507 := bstep (se 1 (by rfl) ⟨1719380, by rfl⟩ : syracuseStep 2292507 = 3438761) B3438761
theorem B11016485 : Blo 2291435 11016485 := bbase (se 4 (by rfl) ⟨1032795, by rfl⟩ : syracuseStep 11016485 = 2065591) (by norm_num)
theorem B7344323 : Blo 2291435 7344323 := bstep (se 1 (by rfl) ⟨5508242, by rfl⟩ : syracuseStep 7344323 = 11016485) B11016485
theorem B4896215 : Blo 2291435 4896215 := bstep (se 1 (by rfl) ⟨3672161, by rfl⟩ : syracuseStep 4896215 = 7344323) B7344323
theorem B3264143 : Blo 2291435 3264143 := bstep (se 1 (by rfl) ⟨2448107, by rfl⟩ : syracuseStep 3264143 = 4896215) B4896215
theorem B8704381 : Blo 2291435 8704381 := bstep (se 3 (by rfl) ⟨1632071, by rfl⟩ : syracuseStep 8704381 = 3264143) B3264143
theorem B11605841 : Blo 2291435 11605841 := bstep (se 2 (by rfl) ⟨4352190, by rfl⟩ : syracuseStep 11605841 = 8704381) B8704381
theorem B7737227 : Blo 2291435 7737227 := bstep (se 1 (by rfl) ⟨5802920, by rfl⟩ : syracuseStep 7737227 = 11605841) B11605841
theorem B5158151 : Blo 2291435 5158151 := bstep (se 1 (by rfl) ⟨3868613, by rfl⟩ : syracuseStep 5158151 = 7737227) B7737227
theorem B3438767 : Blo 2291435 3438767 := bstep (se 1 (by rfl) ⟨2579075, by rfl⟩ : syracuseStep 3438767 = 5158151) B5158151
theorem B2292511 : Blo 2291435 2292511 := bstep (se 1 (by rfl) ⟨1719383, by rfl⟩ : syracuseStep 2292511 = 3438767) B3438767
theorem B3438773 : Blo 2291435 3438773 := bbase (se 5 (by rfl) ⟨161192, by rfl⟩ : syracuseStep 3438773 = 322385) (by norm_num)
theorem B2292515 : Blo 2291435 2292515 := bstep (se 1 (by rfl) ⟨1719386, by rfl⟩ : syracuseStep 2292515 = 3438773) B3438773
theorem B5802941 : Blo 2291435 5802941 := bbase (se 3 (by rfl) ⟨1088051, by rfl⟩ : syracuseStep 5802941 = 2176103) (by norm_num)
theorem B3868627 : Blo 2291435 3868627 := bstep (se 1 (by rfl) ⟨2901470, by rfl⟩ : syracuseStep 3868627 = 5802941) B5802941
theorem B5158169 : Blo 2291435 5158169 := bstep (se 2 (by rfl) ⟨1934313, by rfl⟩ : syracuseStep 5158169 = 3868627) B3868627
theorem B3438779 : Blo 2291435 3438779 := bstep (se 1 (by rfl) ⟨2579084, by rfl⟩ : syracuseStep 3438779 = 5158169) B5158169
theorem B2292519 : Blo 2291435 2292519 := bstep (se 1 (by rfl) ⟨1719389, by rfl⟩ : syracuseStep 2292519 = 3438779) B3438779
theorem B2579089 : Blo 2291435 2579089 := bbase (se 2 (by rfl) ⟨967158, by rfl⟩ : syracuseStep 2579089 = 1934317) (by norm_num)
theorem B3438785 : Blo 2291435 3438785 := bstep (se 2 (by rfl) ⟨1289544, by rfl⟩ : syracuseStep 3438785 = 2579089) B2579089
theorem B2292523 : Blo 2291435 2292523 := bstep (se 1 (by rfl) ⟨1719392, by rfl⟩ : syracuseStep 2292523 = 3438785) B3438785
theorem B4352221 : Blo 2291435 4352221 := bbase (se 3 (by rfl) ⟨816041, by rfl⟩ : syracuseStep 4352221 = 1632083) (by norm_num)
theorem B5802961 : Blo 2291435 5802961 := bstep (se 2 (by rfl) ⟨2176110, by rfl⟩ : syracuseStep 5802961 = 4352221) B4352221
theorem B7737281 : Blo 2291435 7737281 := bstep (se 2 (by rfl) ⟨2901480, by rfl⟩ : syracuseStep 7737281 = 5802961) B5802961
theorem B5158187 : Blo 2291435 5158187 := bstep (se 1 (by rfl) ⟨3868640, by rfl⟩ : syracuseStep 5158187 = 7737281) B7737281
theorem B3438791 : Blo 2291435 3438791 := bstep (se 1 (by rfl) ⟨2579093, by rfl⟩ : syracuseStep 3438791 = 5158187) B5158187
theorem B2292527 : Blo 2291435 2292527 := bstep (se 1 (by rfl) ⟨1719395, by rfl⟩ : syracuseStep 2292527 = 3438791) B3438791
theorem B3438797 : Blo 2291435 3438797 := bbase (se 3 (by rfl) ⟨644774, by rfl⟩ : syracuseStep 3438797 = 1289549) (by norm_num)
theorem B2292531 : Blo 2291435 2292531 := bstep (se 1 (by rfl) ⟨1719398, by rfl⟩ : syracuseStep 2292531 = 3438797) B3438797
theorem B5158205 : Blo 2291435 5158205 := bbase (se 3 (by rfl) ⟨967163, by rfl⟩ : syracuseStep 5158205 = 1934327) (by norm_num)
theorem B3438803 : Blo 2291435 3438803 := bstep (se 1 (by rfl) ⟨2579102, by rfl⟩ : syracuseStep 3438803 = 5158205) B5158205
theorem B2292535 : Blo 2291435 2292535 := bstep (se 1 (by rfl) ⟨1719401, by rfl⟩ : syracuseStep 2292535 = 3438803) B3438803
theorem B3868661 : Blo 2291435 3868661 := bbase (se 5 (by rfl) ⟨181343, by rfl⟩ : syracuseStep 3868661 = 362687) (by norm_num)
theorem B2579107 : Blo 2291435 2579107 := bstep (se 1 (by rfl) ⟨1934330, by rfl⟩ : syracuseStep 2579107 = 3868661) B3868661
theorem B3438809 : Blo 2291435 3438809 := bstep (se 2 (by rfl) ⟨1289553, by rfl⟩ : syracuseStep 3438809 = 2579107) B2579107
theorem B2292539 : Blo 2291435 2292539 := bstep (se 1 (by rfl) ⟨1719404, by rfl⟩ : syracuseStep 2292539 = 3438809) B3438809
theorem B7842901 : Blo 2291435 7842901 := bbase (se 8 (by rfl) ⟨45954, by rfl⟩ : syracuseStep 7842901 = 91909) (by norm_num)
theorem B10457201 : Blo 2291435 10457201 := bstep (se 2 (by rfl) ⟨3921450, by rfl⟩ : syracuseStep 10457201 = 7842901) B7842901
theorem B27885869 : Blo 2291435 27885869 := bstep (se 3 (by rfl) ⟨5228600, by rfl⟩ : syracuseStep 27885869 = 10457201) B10457201
theorem B18590579 : Blo 2291435 18590579 := bstep (se 1 (by rfl) ⟨13942934, by rfl⟩ : syracuseStep 18590579 = 27885869) B27885869
theorem B12393719 : Blo 2291435 12393719 := bstep (se 1 (by rfl) ⟨9295289, by rfl⟩ : syracuseStep 12393719 = 18590579) B18590579
theorem B8262479 : Blo 2291435 8262479 := bstep (se 1 (by rfl) ⟨6196859, by rfl⟩ : syracuseStep 8262479 = 12393719) B12393719
theorem B5508319 : Blo 2291435 5508319 := bstep (se 1 (by rfl) ⟨4131239, by rfl⟩ : syracuseStep 5508319 = 8262479) B8262479
theorem B7344425 : Blo 2291435 7344425 := bstep (se 2 (by rfl) ⟨2754159, by rfl⟩ : syracuseStep 7344425 = 5508319) B5508319
theorem B4896283 : Blo 2291435 4896283 := bstep (se 1 (by rfl) ⟨3672212, by rfl⟩ : syracuseStep 4896283 = 7344425) B7344425
theorem B6528377 : Blo 2291435 6528377 := bstep (se 2 (by rfl) ⟨2448141, by rfl⟩ : syracuseStep 6528377 = 4896283) B4896283
theorem B17409005 : Blo 2291435 17409005 := bstep (se 3 (by rfl) ⟨3264188, by rfl⟩ : syracuseStep 17409005 = 6528377) B6528377
theorem B11606003 : Blo 2291435 11606003 := bstep (se 1 (by rfl) ⟨8704502, by rfl⟩ : syracuseStep 11606003 = 17409005) B17409005
theorem B7737335 : Blo 2291435 7737335 := bstep (se 1 (by rfl) ⟨5803001, by rfl⟩ : syracuseStep 7737335 = 11606003) B11606003
theorem B5158223 : Blo 2291435 5158223 := bstep (se 1 (by rfl) ⟨3868667, by rfl⟩ : syracuseStep 5158223 = 7737335) B7737335
theorem B3438815 : Blo 2291435 3438815 := bstep (se 1 (by rfl) ⟨2579111, by rfl⟩ : syracuseStep 3438815 = 5158223) B5158223
theorem B2292543 : Blo 2291435 2292543 := bstep (se 1 (by rfl) ⟨1719407, by rfl⟩ : syracuseStep 2292543 = 3438815) B3438815
theorem B3438821 : Blo 2291435 3438821 := bbase (se 4 (by rfl) ⟨322389, by rfl⟩ : syracuseStep 3438821 = 644779) (by norm_num)
theorem B2292547 : Blo 2291435 2292547 := bstep (se 1 (by rfl) ⟨1719410, by rfl⟩ : syracuseStep 2292547 = 3438821) B3438821
theorem B4896301 : Blo 2291435 4896301 := bbase (se 3 (by rfl) ⟨918056, by rfl⟩ : syracuseStep 4896301 = 1836113) (by norm_num)
theorem B6528401 : Blo 2291435 6528401 := bstep (se 2 (by rfl) ⟨2448150, by rfl⟩ : syracuseStep 6528401 = 4896301) B4896301
theorem B4352267 : Blo 2291435 4352267 := bstep (se 1 (by rfl) ⟨3264200, by rfl⟩ : syracuseStep 4352267 = 6528401) B6528401
theorem B2901511 : Blo 2291435 2901511 := bstep (se 1 (by rfl) ⟨2176133, by rfl⟩ : syracuseStep 2901511 = 4352267) B4352267
theorem B3868681 : Blo 2291435 3868681 := bstep (se 2 (by rfl) ⟨1450755, by rfl⟩ : syracuseStep 3868681 = 2901511) B2901511
theorem B5158241 : Blo 2291435 5158241 := bstep (se 2 (by rfl) ⟨1934340, by rfl⟩ : syracuseStep 5158241 = 3868681) B3868681
theorem B3438827 : Blo 2291435 3438827 := bstep (se 1 (by rfl) ⟨2579120, by rfl⟩ : syracuseStep 3438827 = 5158241) B5158241
theorem B2292551 : Blo 2291435 2292551 := bstep (se 1 (by rfl) ⟨1719413, by rfl⟩ : syracuseStep 2292551 = 3438827) B3438827
theorem B2579125 : Blo 2291435 2579125 := bbase (se 5 (by rfl) ⟨120896, by rfl⟩ : syracuseStep 2579125 = 241793) (by norm_num)
theorem B3438833 : Blo 2291435 3438833 := bstep (se 2 (by rfl) ⟨1289562, by rfl⟩ : syracuseStep 3438833 = 2579125) B2579125
theorem B2292555 : Blo 2291435 2292555 := bstep (se 1 (by rfl) ⟨1719416, by rfl⟩ : syracuseStep 2292555 = 3438833) B3438833
theorem B2901521 : Blo 2291435 2901521 := bbase (se 2 (by rfl) ⟨1088070, by rfl⟩ : syracuseStep 2901521 = 2176141) (by norm_num)
theorem B7737389 : Blo 2291435 7737389 := bstep (se 3 (by rfl) ⟨1450760, by rfl⟩ : syracuseStep 7737389 = 2901521) B2901521
theorem B5158259 : Blo 2291435 5158259 := bstep (se 1 (by rfl) ⟨3868694, by rfl⟩ : syracuseStep 5158259 = 7737389) B7737389
theorem B3438839 : Blo 2291435 3438839 := bstep (se 1 (by rfl) ⟨2579129, by rfl⟩ : syracuseStep 3438839 = 5158259) B5158259
theorem B2292559 : Blo 2291435 2292559 := bstep (se 1 (by rfl) ⟨1719419, by rfl⟩ : syracuseStep 2292559 = 3438839) B3438839
theorem B3438845 : Blo 2291435 3438845 := bbase (se 3 (by rfl) ⟨644783, by rfl⟩ : syracuseStep 3438845 = 1289567) (by norm_num)
theorem B2292563 : Blo 2291435 2292563 := bstep (se 1 (by rfl) ⟨1719422, by rfl⟩ : syracuseStep 2292563 = 3438845) B3438845
theorem B5158277 : Blo 2291435 5158277 := bbase (se 4 (by rfl) ⟨483588, by rfl⟩ : syracuseStep 5158277 = 967177) (by norm_num)
theorem B3438851 : Blo 2291435 3438851 := bstep (se 1 (by rfl) ⟨2579138, by rfl⟩ : syracuseStep 3438851 = 5158277) B5158277
theorem B2292567 : Blo 2291435 2292567 := bstep (se 1 (by rfl) ⟨1719425, by rfl⟩ : syracuseStep 2292567 = 3438851) B3438851
theorem B3264229 : Blo 2291435 3264229 := bbase (se 4 (by rfl) ⟨306021, by rfl⟩ : syracuseStep 3264229 = 612043) (by norm_num)
theorem B4352305 : Blo 2291435 4352305 := bstep (se 2 (by rfl) ⟨1632114, by rfl⟩ : syracuseStep 4352305 = 3264229) B3264229
theorem B5803073 : Blo 2291435 5803073 := bstep (se 2 (by rfl) ⟨2176152, by rfl⟩ : syracuseStep 5803073 = 4352305) B4352305
theorem B3868715 : Blo 2291435 3868715 := bstep (se 1 (by rfl) ⟨2901536, by rfl⟩ : syracuseStep 3868715 = 5803073) B5803073
theorem B2579143 : Blo 2291435 2579143 := bstep (se 1 (by rfl) ⟨1934357, by rfl⟩ : syracuseStep 2579143 = 3868715) B3868715
theorem B3438857 : Blo 2291435 3438857 := bstep (se 2 (by rfl) ⟨1289571, by rfl⟩ : syracuseStep 3438857 = 2579143) B2579143
theorem B2292571 : Blo 2291435 2292571 := bstep (se 1 (by rfl) ⟨1719428, by rfl⟩ : syracuseStep 2292571 = 3438857) B3438857
theorem B11606165 : Blo 2291435 11606165 := bbase (se 6 (by rfl) ⟨272019, by rfl⟩ : syracuseStep 11606165 = 544039) (by norm_num)
theorem B7737443 : Blo 2291435 7737443 := bstep (se 1 (by rfl) ⟨5803082, by rfl⟩ : syracuseStep 7737443 = 11606165) B11606165
theorem B5158295 : Blo 2291435 5158295 := bstep (se 1 (by rfl) ⟨3868721, by rfl⟩ : syracuseStep 5158295 = 7737443) B7737443
theorem B3438863 : Blo 2291435 3438863 := bstep (se 1 (by rfl) ⟨2579147, by rfl⟩ : syracuseStep 3438863 = 5158295) B5158295
theorem B2292575 : Blo 2291435 2292575 := bstep (se 1 (by rfl) ⟨1719431, by rfl⟩ : syracuseStep 2292575 = 3438863) B3438863
theorem B3438869 : Blo 2291435 3438869 := bbase (se 6 (by rfl) ⟨80598, by rfl⟩ : syracuseStep 3438869 = 161197) (by norm_num)
theorem B2292579 : Blo 2291435 2292579 := bstep (se 1 (by rfl) ⟨1719434, by rfl⟩ : syracuseStep 2292579 = 3438869) B3438869
theorem B16750709 : Blo 2291435 16750709 := bbase (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) (by norm_num)
theorem B11167139 : Blo 2291435 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B7444759 : Blo 2291435 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B9926345 : Blo 2291435 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B26470253 : Blo 2291435 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B17646835 : Blo 2291435 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B23529113 : Blo 2291435 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B15686075 : Blo 2291435 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B41829533 : Blo 2291435 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B27886355 : Blo 2291435 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B18590903 : Blo 2291435 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B12393935 : Blo 2291435 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B8262623 : Blo 2291435 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B5508415 : Blo 2291435 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B29378213 : Blo 2291435 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B19585475 : Blo 2291435 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B13056983 : Blo 2291435 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B8704655 : Blo 2291435 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B5803103 : Blo 2291435 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B3868735 : Blo 2291435 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B5158313 : Blo 2291435 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B3438875 : Blo 2291435 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B2292583 : Blo 2291435 2292583 := bstep (se 1 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 2292583 = 3438875) B3438875
theorem B2579161 : Blo 2291435 2579161 := bbase (se 2 (by rfl) ⟨967185, by rfl⟩ : syracuseStep 2579161 = 1934371) (by norm_num)
theorem B3438881 : Blo 2291435 3438881 := bstep (se 2 (by rfl) ⟨1289580, by rfl⟩ : syracuseStep 3438881 = 2579161) B2579161
theorem B2292587 : Blo 2291435 2292587 := bstep (se 1 (by rfl) ⟨1719440, by rfl⟩ : syracuseStep 2292587 = 3438881) B3438881
theorem B2448193 : Blo 2291435 2448193 := bbase (se 2 (by rfl) ⟨918072, by rfl⟩ : syracuseStep 2448193 = 1836145) (by norm_num)
theorem B3264257 : Blo 2291435 3264257 := bstep (se 2 (by rfl) ⟨1224096, by rfl⟩ : syracuseStep 3264257 = 2448193) B2448193
theorem B8704685 : Blo 2291435 8704685 := bstep (se 3 (by rfl) ⟨1632128, by rfl⟩ : syracuseStep 8704685 = 3264257) B3264257
theorem B5803123 : Blo 2291435 5803123 := bstep (se 1 (by rfl) ⟨4352342, by rfl⟩ : syracuseStep 5803123 = 8704685) B8704685
theorem B7737497 : Blo 2291435 7737497 := bstep (se 2 (by rfl) ⟨2901561, by rfl⟩ : syracuseStep 7737497 = 5803123) B5803123
theorem B5158331 : Blo 2291435 5158331 := bstep (se 1 (by rfl) ⟨3868748, by rfl⟩ : syracuseStep 5158331 = 7737497) B7737497
theorem B3438887 : Blo 2291435 3438887 := bstep (se 1 (by rfl) ⟨2579165, by rfl⟩ : syracuseStep 3438887 = 5158331) B5158331
theorem B2292591 : Blo 2291435 2292591 := bstep (se 1 (by rfl) ⟨1719443, by rfl⟩ : syracuseStep 2292591 = 3438887) B3438887
theorem B3438893 : Blo 2291435 3438893 := bbase (se 3 (by rfl) ⟨644792, by rfl⟩ : syracuseStep 3438893 = 1289585) (by norm_num)
theorem B2292595 : Blo 2291435 2292595 := bstep (se 1 (by rfl) ⟨1719446, by rfl⟩ : syracuseStep 2292595 = 3438893) B3438893
theorem B5158349 : Blo 2291435 5158349 := bbase (se 3 (by rfl) ⟨967190, by rfl⟩ : syracuseStep 5158349 = 1934381) (by norm_num)
theorem B3438899 : Blo 2291435 3438899 := bstep (se 1 (by rfl) ⟨2579174, by rfl⟩ : syracuseStep 3438899 = 5158349) B5158349
theorem B2292599 : Blo 2291435 2292599 := bstep (se 1 (by rfl) ⟨1719449, by rfl⟩ : syracuseStep 2292599 = 3438899) B3438899
theorem B2901577 : Blo 2291435 2901577 := bbase (se 2 (by rfl) ⟨1088091, by rfl⟩ : syracuseStep 2901577 = 2176183) (by norm_num)
theorem B3868769 : Blo 2291435 3868769 := bstep (se 2 (by rfl) ⟨1450788, by rfl⟩ : syracuseStep 3868769 = 2901577) B2901577
theorem B2579179 : Blo 2291435 2579179 := bstep (se 1 (by rfl) ⟨1934384, by rfl⟩ : syracuseStep 2579179 = 3868769) B3868769
theorem B3438905 : Blo 2291435 3438905 := bstep (se 2 (by rfl) ⟨1289589, by rfl⟩ : syracuseStep 3438905 = 2579179) B2579179
theorem B2292603 : Blo 2291435 2292603 := bstep (se 1 (by rfl) ⟨1719452, by rfl⟩ : syracuseStep 2292603 = 3438905) B3438905
theorem B8823509 : Blo 2291435 8823509 := bbase (se 7 (by rfl) ⟨103400, by rfl⟩ : syracuseStep 8823509 = 206801) (by norm_num)
theorem B5882339 : Blo 2291435 5882339 := bstep (se 1 (by rfl) ⟨4411754, by rfl⟩ : syracuseStep 5882339 = 8823509) B8823509
theorem B15686237 : Blo 2291435 15686237 := bstep (se 3 (by rfl) ⟨2941169, by rfl⟩ : syracuseStep 15686237 = 5882339) B5882339
theorem B41829965 : Blo 2291435 41829965 := bstep (se 3 (by rfl) ⟨7843118, by rfl⟩ : syracuseStep 41829965 = 15686237) B15686237
theorem B27886643 : Blo 2291435 27886643 := bstep (se 1 (by rfl) ⟨20914982, by rfl⟩ : syracuseStep 27886643 = 41829965) B41829965
theorem B18591095 : Blo 2291435 18591095 := bstep (se 1 (by rfl) ⟨13943321, by rfl⟩ : syracuseStep 18591095 = 27886643) B27886643
theorem B12394063 : Blo 2291435 12394063 := bstep (se 1 (by rfl) ⟨9295547, by rfl⟩ : syracuseStep 12394063 = 18591095) B18591095
theorem B16525417 : Blo 2291435 16525417 := bstep (se 2 (by rfl) ⟨6197031, by rfl⟩ : syracuseStep 16525417 = 12394063) B12394063
theorem B22033889 : Blo 2291435 22033889 := bstep (se 2 (by rfl) ⟨8262708, by rfl⟩ : syracuseStep 22033889 = 16525417) B16525417
theorem B14689259 : Blo 2291435 14689259 := bstep (se 1 (by rfl) ⟨11016944, by rfl⟩ : syracuseStep 14689259 = 22033889) B22033889
theorem B9792839 : Blo 2291435 9792839 := bstep (se 1 (by rfl) ⟨7344629, by rfl⟩ : syracuseStep 9792839 = 14689259) B14689259
theorem B26114237 : Blo 2291435 26114237 := bstep (se 3 (by rfl) ⟨4896419, by rfl⟩ : syracuseStep 26114237 = 9792839) B9792839
theorem B17409491 : Blo 2291435 17409491 := bstep (se 1 (by rfl) ⟨13057118, by rfl⟩ : syracuseStep 17409491 = 26114237) B26114237
theorem B11606327 : Blo 2291435 11606327 := bstep (se 1 (by rfl) ⟨8704745, by rfl⟩ : syracuseStep 11606327 = 17409491) B17409491
theorem B7737551 : Blo 2291435 7737551 := bstep (se 1 (by rfl) ⟨5803163, by rfl⟩ : syracuseStep 7737551 = 11606327) B11606327
theorem B5158367 : Blo 2291435 5158367 := bstep (se 1 (by rfl) ⟨3868775, by rfl⟩ : syracuseStep 5158367 = 7737551) B7737551
theorem B3438911 : Blo 2291435 3438911 := bstep (se 1 (by rfl) ⟨2579183, by rfl⟩ : syracuseStep 3438911 = 5158367) B5158367
theorem B2292607 : Blo 2291435 2292607 := bstep (se 1 (by rfl) ⟨1719455, by rfl⟩ : syracuseStep 2292607 = 3438911) B3438911
theorem B3438917 : Blo 2291435 3438917 := bbase (se 4 (by rfl) ⟨322398, by rfl⟩ : syracuseStep 3438917 = 644797) (by norm_num)
theorem B2292611 : Blo 2291435 2292611 := bstep (se 1 (by rfl) ⟨1719458, by rfl⟩ : syracuseStep 2292611 = 3438917) B3438917
theorem B3868789 : Blo 2291435 3868789 := bbase (se 5 (by rfl) ⟨181349, by rfl⟩ : syracuseStep 3868789 = 362699) (by norm_num)
theorem B5158385 : Blo 2291435 5158385 := bstep (se 2 (by rfl) ⟨1934394, by rfl⟩ : syracuseStep 5158385 = 3868789) B3868789
theorem B3438923 : Blo 2291435 3438923 := bstep (se 1 (by rfl) ⟨2579192, by rfl⟩ : syracuseStep 3438923 = 5158385) B5158385
theorem B2292615 : Blo 2291435 2292615 := bstep (se 1 (by rfl) ⟨1719461, by rfl⟩ : syracuseStep 2292615 = 3438923) B3438923
theorem B2579197 : Blo 2291435 2579197 := bbase (se 3 (by rfl) ⟨483599, by rfl⟩ : syracuseStep 2579197 = 967199) (by norm_num)
theorem B3438929 : Blo 2291435 3438929 := bstep (se 2 (by rfl) ⟨1289598, by rfl⟩ : syracuseStep 3438929 = 2579197) B2579197
theorem B2292619 : Blo 2291435 2292619 := bstep (se 1 (by rfl) ⟨1719464, by rfl⟩ : syracuseStep 2292619 = 3438929) B3438929
theorem B7737605 : Blo 2291435 7737605 := bbase (se 4 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 7737605 = 1450801) (by norm_num)
theorem B5158403 : Blo 2291435 5158403 := bstep (se 1 (by rfl) ⟨3868802, by rfl⟩ : syracuseStep 5158403 = 7737605) B7737605
theorem B3438935 : Blo 2291435 3438935 := bstep (se 1 (by rfl) ⟨2579201, by rfl⟩ : syracuseStep 3438935 = 5158403) B5158403
theorem B2292623 : Blo 2291435 2292623 := bstep (se 1 (by rfl) ⟨1719467, by rfl⟩ : syracuseStep 2292623 = 3438935) B3438935
theorem B3438941 : Blo 2291435 3438941 := bbase (se 3 (by rfl) ⟨644801, by rfl⟩ : syracuseStep 3438941 = 1289603) (by norm_num)
theorem B2292627 : Blo 2291435 2292627 := bstep (se 1 (by rfl) ⟨1719470, by rfl⟩ : syracuseStep 2292627 = 3438941) B3438941
theorem B5158421 : Blo 2291435 5158421 := bbase (se 6 (by rfl) ⟨120900, by rfl⟩ : syracuseStep 5158421 = 241801) (by norm_num)
theorem B3438947 : Blo 2291435 3438947 := bstep (se 1 (by rfl) ⟨2579210, by rfl⟩ : syracuseStep 3438947 = 5158421) B5158421
theorem B2292631 : Blo 2291435 2292631 := bstep (se 1 (by rfl) ⟨1719473, by rfl⟩ : syracuseStep 2292631 = 3438947) B3438947
theorem B8704853 : Blo 2291435 8704853 := bbase (se 9 (by rfl) ⟨25502, by rfl⟩ : syracuseStep 8704853 = 51005) (by norm_num)
theorem B5803235 : Blo 2291435 5803235 := bstep (se 1 (by rfl) ⟨4352426, by rfl⟩ : syracuseStep 5803235 = 8704853) B8704853
theorem B3868823 : Blo 2291435 3868823 := bstep (se 1 (by rfl) ⟨2901617, by rfl⟩ : syracuseStep 3868823 = 5803235) B5803235
theorem B2579215 : Blo 2291435 2579215 := bstep (se 1 (by rfl) ⟨1934411, by rfl⟩ : syracuseStep 2579215 = 3868823) B3868823
theorem B3438953 : Blo 2291435 3438953 := bstep (se 2 (by rfl) ⟨1289607, by rfl⟩ : syracuseStep 3438953 = 2579215) B2579215
theorem B2292635 : Blo 2291435 2292635 := bstep (se 1 (by rfl) ⟨1719476, by rfl⟩ : syracuseStep 2292635 = 3438953) B3438953
theorem B13057301 : Blo 2291435 13057301 := bbase (se 6 (by rfl) ⟨306030, by rfl⟩ : syracuseStep 13057301 = 612061) (by norm_num)
theorem B8704867 : Blo 2291435 8704867 := bstep (se 1 (by rfl) ⟨6528650, by rfl⟩ : syracuseStep 8704867 = 13057301) B13057301
theorem B11606489 : Blo 2291435 11606489 := bstep (se 2 (by rfl) ⟨4352433, by rfl⟩ : syracuseStep 11606489 = 8704867) B8704867
theorem B7737659 : Blo 2291435 7737659 := bstep (se 1 (by rfl) ⟨5803244, by rfl⟩ : syracuseStep 7737659 = 11606489) B11606489
theorem B5158439 : Blo 2291435 5158439 := bstep (se 1 (by rfl) ⟨3868829, by rfl⟩ : syracuseStep 5158439 = 7737659) B7737659
theorem B3438959 : Blo 2291435 3438959 := bstep (se 1 (by rfl) ⟨2579219, by rfl⟩ : syracuseStep 3438959 = 5158439) B5158439
theorem B2292639 : Blo 2291435 2292639 := bstep (se 1 (by rfl) ⟨1719479, by rfl⟩ : syracuseStep 2292639 = 3438959) B3438959
theorem B3438965 : Blo 2291435 3438965 := bbase (se 5 (by rfl) ⟨161201, by rfl⟩ : syracuseStep 3438965 = 322403) (by norm_num)
theorem B2292643 : Blo 2291435 2292643 := bstep (se 1 (by rfl) ⟨1719482, by rfl⟩ : syracuseStep 2292643 = 3438965) B3438965
theorem B2448253 : Blo 2291435 2448253 := bbase (se 3 (by rfl) ⟨459047, by rfl⟩ : syracuseStep 2448253 = 918095) (by norm_num)
theorem B3264337 : Blo 2291435 3264337 := bstep (se 2 (by rfl) ⟨1224126, by rfl⟩ : syracuseStep 3264337 = 2448253) B2448253
theorem B4352449 : Blo 2291435 4352449 := bstep (se 2 (by rfl) ⟨1632168, by rfl⟩ : syracuseStep 4352449 = 3264337) B3264337
theorem B5803265 : Blo 2291435 5803265 := bstep (se 2 (by rfl) ⟨2176224, by rfl⟩ : syracuseStep 5803265 = 4352449) B4352449
theorem B3868843 : Blo 2291435 3868843 := bstep (se 1 (by rfl) ⟨2901632, by rfl⟩ : syracuseStep 3868843 = 5803265) B5803265
theorem B5158457 : Blo 2291435 5158457 := bstep (se 2 (by rfl) ⟨1934421, by rfl⟩ : syracuseStep 5158457 = 3868843) B3868843
theorem B3438971 : Blo 2291435 3438971 := bstep (se 1 (by rfl) ⟨2579228, by rfl⟩ : syracuseStep 3438971 = 5158457) B5158457
theorem B2292647 : Blo 2291435 2292647 := bstep (se 1 (by rfl) ⟨1719485, by rfl⟩ : syracuseStep 2292647 = 3438971) B3438971
theorem B2579233 : Blo 2291435 2579233 := bbase (se 2 (by rfl) ⟨967212, by rfl⟩ : syracuseStep 2579233 = 1934425) (by norm_num)
theorem B3438977 : Blo 2291435 3438977 := bstep (se 2 (by rfl) ⟨1289616, by rfl⟩ : syracuseStep 3438977 = 2579233) B2579233
theorem B2292651 : Blo 2291435 2292651 := bstep (se 1 (by rfl) ⟨1719488, by rfl⟩ : syracuseStep 2292651 = 3438977) B3438977
theorem B5803285 : Blo 2291435 5803285 := bbase (se 6 (by rfl) ⟨136014, by rfl⟩ : syracuseStep 5803285 = 272029) (by norm_num)
theorem B7737713 : Blo 2291435 7737713 := bstep (se 2 (by rfl) ⟨2901642, by rfl⟩ : syracuseStep 7737713 = 5803285) B5803285
theorem B5158475 : Blo 2291435 5158475 := bstep (se 1 (by rfl) ⟨3868856, by rfl⟩ : syracuseStep 5158475 = 7737713) B7737713
theorem B3438983 : Blo 2291435 3438983 := bstep (se 1 (by rfl) ⟨2579237, by rfl⟩ : syracuseStep 3438983 = 5158475) B5158475
theorem B2292655 : Blo 2291435 2292655 := bstep (se 1 (by rfl) ⟨1719491, by rfl⟩ : syracuseStep 2292655 = 3438983) B3438983
theorem B3438989 : Blo 2291435 3438989 := bbase (se 3 (by rfl) ⟨644810, by rfl⟩ : syracuseStep 3438989 = 1289621) (by norm_num)
theorem B2292659 : Blo 2291435 2292659 := bstep (se 1 (by rfl) ⟨1719494, by rfl⟩ : syracuseStep 2292659 = 3438989) B3438989
theorem B5158493 : Blo 2291435 5158493 := bbase (se 3 (by rfl) ⟨967217, by rfl⟩ : syracuseStep 5158493 = 1934435) (by norm_num)
theorem B3438995 : Blo 2291435 3438995 := bstep (se 1 (by rfl) ⟨2579246, by rfl⟩ : syracuseStep 3438995 = 5158493) B5158493
theorem B2292663 : Blo 2291435 2292663 := bstep (se 1 (by rfl) ⟨1719497, by rfl⟩ : syracuseStep 2292663 = 3438995) B3438995
theorem B3868877 : Blo 2291435 3868877 := bbase (se 3 (by rfl) ⟨725414, by rfl⟩ : syracuseStep 3868877 = 1450829) (by norm_num)
theorem B2579251 : Blo 2291435 2579251 := bstep (se 1 (by rfl) ⟨1934438, by rfl⟩ : syracuseStep 2579251 = 3868877) B3868877
theorem B3439001 : Blo 2291435 3439001 := bstep (se 2 (by rfl) ⟨1289625, by rfl⟩ : syracuseStep 3439001 = 2579251) B2579251
theorem B2292667 : Blo 2291435 2292667 := bstep (se 1 (by rfl) ⟨1719500, by rfl⟩ : syracuseStep 2292667 = 3439001) B3439001
theorem B2754313 : Blo 2291435 2754313 := bbase (se 2 (by rfl) ⟨1032867, by rfl⟩ : syracuseStep 2754313 = 2065735) (by norm_num)
theorem B14689669 : Blo 2291435 14689669 := bstep (se 4 (by rfl) ⟨1377156, by rfl⟩ : syracuseStep 14689669 = 2754313) B2754313
theorem B19586225 : Blo 2291435 19586225 := bstep (se 2 (by rfl) ⟨7344834, by rfl⟩ : syracuseStep 19586225 = 14689669) B14689669
theorem B13057483 : Blo 2291435 13057483 := bstep (se 1 (by rfl) ⟨9793112, by rfl⟩ : syracuseStep 13057483 = 19586225) B19586225
theorem B17409977 : Blo 2291435 17409977 := bstep (se 2 (by rfl) ⟨6528741, by rfl⟩ : syracuseStep 17409977 = 13057483) B13057483
theorem B11606651 : Blo 2291435 11606651 := bstep (se 1 (by rfl) ⟨8704988, by rfl⟩ : syracuseStep 11606651 = 17409977) B17409977
theorem B7737767 : Blo 2291435 7737767 := bstep (se 1 (by rfl) ⟨5803325, by rfl⟩ : syracuseStep 7737767 = 11606651) B11606651
theorem B5158511 : Blo 2291435 5158511 := bstep (se 1 (by rfl) ⟨3868883, by rfl⟩ : syracuseStep 5158511 = 7737767) B7737767
theorem B3439007 : Blo 2291435 3439007 := bstep (se 1 (by rfl) ⟨2579255, by rfl⟩ : syracuseStep 3439007 = 5158511) B5158511
theorem B2292671 : Blo 2291435 2292671 := bstep (se 1 (by rfl) ⟨1719503, by rfl⟩ : syracuseStep 2292671 = 3439007) B3439007
theorem B3439013 : Blo 2291435 3439013 := bbase (se 4 (by rfl) ⟨322407, by rfl⟩ : syracuseStep 3439013 = 644815) (by norm_num)
theorem B2292675 : Blo 2291435 2292675 := bstep (se 1 (by rfl) ⟨1719506, by rfl⟩ : syracuseStep 2292675 = 3439013) B3439013
theorem B2901673 : Blo 2291435 2901673 := bbase (se 2 (by rfl) ⟨1088127, by rfl⟩ : syracuseStep 2901673 = 2176255) (by norm_num)
theorem B3868897 : Blo 2291435 3868897 := bstep (se 2 (by rfl) ⟨1450836, by rfl⟩ : syracuseStep 3868897 = 2901673) B2901673
theorem B5158529 : Blo 2291435 5158529 := bstep (se 2 (by rfl) ⟨1934448, by rfl⟩ : syracuseStep 5158529 = 3868897) B3868897
theorem B3439019 : Blo 2291435 3439019 := bstep (se 1 (by rfl) ⟨2579264, by rfl⟩ : syracuseStep 3439019 = 5158529) B5158529
theorem B2292679 : Blo 2291435 2292679 := bstep (se 1 (by rfl) ⟨1719509, by rfl⟩ : syracuseStep 2292679 = 3439019) B3439019
theorem B2579269 : Blo 2291435 2579269 := bbase (se 4 (by rfl) ⟨241806, by rfl⟩ : syracuseStep 2579269 = 483613) (by norm_num)
theorem B3439025 : Blo 2291435 3439025 := bstep (se 2 (by rfl) ⟨1289634, by rfl⟩ : syracuseStep 3439025 = 2579269) B2579269
theorem B2292683 : Blo 2291435 2292683 := bstep (se 1 (by rfl) ⟨1719512, by rfl⟩ : syracuseStep 2292683 = 3439025) B3439025
theorem B4352525 : Blo 2291435 4352525 := bbase (se 3 (by rfl) ⟨816098, by rfl⟩ : syracuseStep 4352525 = 1632197) (by norm_num)
theorem B2901683 : Blo 2291435 2901683 := bstep (se 1 (by rfl) ⟨2176262, by rfl⟩ : syracuseStep 2901683 = 4352525) B4352525
theorem B7737821 : Blo 2291435 7737821 := bstep (se 3 (by rfl) ⟨1450841, by rfl⟩ : syracuseStep 7737821 = 2901683) B2901683
theorem B5158547 : Blo 2291435 5158547 := bstep (se 1 (by rfl) ⟨3868910, by rfl⟩ : syracuseStep 5158547 = 7737821) B7737821
theorem B3439031 : Blo 2291435 3439031 := bstep (se 1 (by rfl) ⟨2579273, by rfl⟩ : syracuseStep 3439031 = 5158547) B5158547
theorem B2292687 : Blo 2291435 2292687 := bstep (se 1 (by rfl) ⟨1719515, by rfl⟩ : syracuseStep 2292687 = 3439031) B3439031
theorem B3439037 : Blo 2291435 3439037 := bbase (se 3 (by rfl) ⟨644819, by rfl⟩ : syracuseStep 3439037 = 1289639) (by norm_num)
theorem B2292691 : Blo 2291435 2292691 := bstep (se 1 (by rfl) ⟨1719518, by rfl⟩ : syracuseStep 2292691 = 3439037) B3439037
theorem B5158565 : Blo 2291435 5158565 := bbase (se 4 (by rfl) ⟨483615, by rfl⟩ : syracuseStep 5158565 = 967231) (by norm_num)
theorem B3439043 : Blo 2291435 3439043 := bstep (se 1 (by rfl) ⟨2579282, by rfl⟩ : syracuseStep 3439043 = 5158565) B5158565
theorem B2292695 : Blo 2291435 2292695 := bstep (se 1 (by rfl) ⟨1719521, by rfl⟩ : syracuseStep 2292695 = 3439043) B3439043
theorem B5803397 : Blo 2291435 5803397 := bbase (se 4 (by rfl) ⟨544068, by rfl⟩ : syracuseStep 5803397 = 1088137) (by norm_num)
theorem B3868931 : Blo 2291435 3868931 := bstep (se 1 (by rfl) ⟨2901698, by rfl⟩ : syracuseStep 3868931 = 5803397) B5803397
theorem B2579287 : Blo 2291435 2579287 := bstep (se 1 (by rfl) ⟨1934465, by rfl⟩ : syracuseStep 2579287 = 3868931) B3868931
theorem B3439049 : Blo 2291435 3439049 := bstep (se 2 (by rfl) ⟨1289643, by rfl⟩ : syracuseStep 3439049 = 2579287) B2579287
theorem B2292699 : Blo 2291435 2292699 := bstep (se 1 (by rfl) ⟨1719524, by rfl⟩ : syracuseStep 2292699 = 3439049) B3439049
theorem B3672469 : Blo 2291435 3672469 := bbase (se 6 (by rfl) ⟨86073, by rfl⟩ : syracuseStep 3672469 = 172147) (by norm_num)
theorem B4896625 : Blo 2291435 4896625 := bstep (se 2 (by rfl) ⟨1836234, by rfl⟩ : syracuseStep 4896625 = 3672469) B3672469
theorem B6528833 : Blo 2291435 6528833 := bstep (se 2 (by rfl) ⟨2448312, by rfl⟩ : syracuseStep 6528833 = 4896625) B4896625
theorem B4352555 : Blo 2291435 4352555 := bstep (se 1 (by rfl) ⟨3264416, by rfl⟩ : syracuseStep 4352555 = 6528833) B6528833
theorem B11606813 : Blo 2291435 11606813 := bstep (se 3 (by rfl) ⟨2176277, by rfl⟩ : syracuseStep 11606813 = 4352555) B4352555
theorem B7737875 : Blo 2291435 7737875 := bstep (se 1 (by rfl) ⟨5803406, by rfl⟩ : syracuseStep 7737875 = 11606813) B11606813
theorem B5158583 : Blo 2291435 5158583 := bstep (se 1 (by rfl) ⟨3868937, by rfl⟩ : syracuseStep 5158583 = 7737875) B7737875
theorem B3439055 : Blo 2291435 3439055 := bstep (se 1 (by rfl) ⟨2579291, by rfl⟩ : syracuseStep 3439055 = 5158583) B5158583
theorem B2292703 : Blo 2291435 2292703 := bstep (se 1 (by rfl) ⟨1719527, by rfl⟩ : syracuseStep 2292703 = 3439055) B3439055
theorem B3439061 : Blo 2291435 3439061 := bbase (se 7 (by rfl) ⟨40301, by rfl⟩ : syracuseStep 3439061 = 80603) (by norm_num)
theorem B2292707 : Blo 2291435 2292707 := bstep (se 1 (by rfl) ⟨1719530, by rfl⟩ : syracuseStep 2292707 = 3439061) B3439061
theorem B8705141 : Blo 2291435 8705141 := bbase (se 5 (by rfl) ⟨408053, by rfl⟩ : syracuseStep 8705141 = 816107) (by norm_num)
theorem B5803427 : Blo 2291435 5803427 := bstep (se 1 (by rfl) ⟨4352570, by rfl⟩ : syracuseStep 5803427 = 8705141) B8705141
theorem B3868951 : Blo 2291435 3868951 := bstep (se 1 (by rfl) ⟨2901713, by rfl⟩ : syracuseStep 3868951 = 5803427) B5803427
theorem B5158601 : Blo 2291435 5158601 := bstep (se 2 (by rfl) ⟨1934475, by rfl⟩ : syracuseStep 5158601 = 3868951) B3868951
theorem B3439067 : Blo 2291435 3439067 := bstep (se 1 (by rfl) ⟨2579300, by rfl⟩ : syracuseStep 3439067 = 5158601) B5158601
theorem B2292711 : Blo 2291435 2292711 := bstep (se 1 (by rfl) ⟨1719533, by rfl⟩ : syracuseStep 2292711 = 3439067) B3439067
theorem B2579305 : Blo 2291435 2579305 := bbase (se 2 (by rfl) ⟨967239, by rfl⟩ : syracuseStep 2579305 = 1934479) (by norm_num)
theorem B3439073 : Blo 2291435 3439073 := bstep (se 2 (by rfl) ⟨1289652, by rfl⟩ : syracuseStep 3439073 = 2579305) B2579305
theorem B2292715 : Blo 2291435 2292715 := bstep (se 1 (by rfl) ⟨1719536, by rfl⟩ : syracuseStep 2292715 = 3439073) B3439073
theorem B4131557 : Blo 2291435 4131557 := bbase (se 4 (by rfl) ⟨387333, by rfl⟩ : syracuseStep 4131557 = 774667) (by norm_num)
theorem B2754371 : Blo 2291435 2754371 := bstep (se 1 (by rfl) ⟨2065778, by rfl⟩ : syracuseStep 2754371 = 4131557) B4131557
theorem B7344989 : Blo 2291435 7344989 := bstep (se 3 (by rfl) ⟨1377185, by rfl⟩ : syracuseStep 7344989 = 2754371) B2754371
theorem B4896659 : Blo 2291435 4896659 := bstep (se 1 (by rfl) ⟨3672494, by rfl⟩ : syracuseStep 4896659 = 7344989) B7344989
theorem B13057757 : Blo 2291435 13057757 := bstep (se 3 (by rfl) ⟨2448329, by rfl⟩ : syracuseStep 13057757 = 4896659) B4896659
theorem B8705171 : Blo 2291435 8705171 := bstep (se 1 (by rfl) ⟨6528878, by rfl⟩ : syracuseStep 8705171 = 13057757) B13057757
theorem B5803447 : Blo 2291435 5803447 := bstep (se 1 (by rfl) ⟨4352585, by rfl⟩ : syracuseStep 5803447 = 8705171) B8705171
theorem B7737929 : Blo 2291435 7737929 := bstep (se 2 (by rfl) ⟨2901723, by rfl⟩ : syracuseStep 7737929 = 5803447) B5803447
theorem B5158619 : Blo 2291435 5158619 := bstep (se 1 (by rfl) ⟨3868964, by rfl⟩ : syracuseStep 5158619 = 7737929) B7737929
theorem B3439079 : Blo 2291435 3439079 := bstep (se 1 (by rfl) ⟨2579309, by rfl⟩ : syracuseStep 3439079 = 5158619) B5158619
theorem B2292719 : Blo 2291435 2292719 := bstep (se 1 (by rfl) ⟨1719539, by rfl⟩ : syracuseStep 2292719 = 3439079) B3439079
theorem B3439085 : Blo 2291435 3439085 := bbase (se 3 (by rfl) ⟨644828, by rfl⟩ : syracuseStep 3439085 = 1289657) (by norm_num)
theorem B2292723 : Blo 2291435 2292723 := bstep (se 1 (by rfl) ⟨1719542, by rfl⟩ : syracuseStep 2292723 = 3439085) B3439085
theorem B5158637 : Blo 2291435 5158637 := bbase (se 3 (by rfl) ⟨967244, by rfl⟩ : syracuseStep 5158637 = 1934489) (by norm_num)
theorem B3439091 : Blo 2291435 3439091 := bstep (se 1 (by rfl) ⟨2579318, by rfl⟩ : syracuseStep 3439091 = 5158637) B5158637
theorem B2292727 : Blo 2291435 2292727 := bstep (se 1 (by rfl) ⟨1719545, by rfl⟩ : syracuseStep 2292727 = 3439091) B3439091
theorem B5508773 : Blo 2291435 5508773 := bbase (se 4 (by rfl) ⟨516447, by rfl⟩ : syracuseStep 5508773 = 1032895) (by norm_num)
theorem B3672515 : Blo 2291435 3672515 := bstep (se 1 (by rfl) ⟨2754386, by rfl⟩ : syracuseStep 3672515 = 5508773) B5508773
theorem B2448343 : Blo 2291435 2448343 := bstep (se 1 (by rfl) ⟨1836257, by rfl⟩ : syracuseStep 2448343 = 3672515) B3672515
theorem B3264457 : Blo 2291435 3264457 := bstep (se 2 (by rfl) ⟨1224171, by rfl⟩ : syracuseStep 3264457 = 2448343) B2448343
theorem B4352609 : Blo 2291435 4352609 := bstep (se 2 (by rfl) ⟨1632228, by rfl⟩ : syracuseStep 4352609 = 3264457) B3264457
theorem B2901739 : Blo 2291435 2901739 := bstep (se 1 (by rfl) ⟨2176304, by rfl⟩ : syracuseStep 2901739 = 4352609) B4352609
theorem B3868985 : Blo 2291435 3868985 := bstep (se 2 (by rfl) ⟨1450869, by rfl⟩ : syracuseStep 3868985 = 2901739) B2901739
theorem B2579323 : Blo 2291435 2579323 := bstep (se 1 (by rfl) ⟨1934492, by rfl⟩ : syracuseStep 2579323 = 3868985) B3868985
theorem B3439097 : Blo 2291435 3439097 := bstep (se 2 (by rfl) ⟨1289661, by rfl⟩ : syracuseStep 3439097 = 2579323) B2579323
theorem B2292731 : Blo 2291435 2292731 := bstep (se 1 (by rfl) ⟨1719548, by rfl⟩ : syracuseStep 2292731 = 3439097) B3439097
theorem B5229037 : Blo 2291435 5229037 := bbase (se 3 (by rfl) ⟨980444, by rfl⟩ : syracuseStep 5229037 = 1960889) (by norm_num)
theorem B27888197 : Blo 2291435 27888197 := bstep (se 4 (by rfl) ⟨2614518, by rfl⟩ : syracuseStep 27888197 = 5229037) B5229037
theorem B74368525 : Blo 2291435 74368525 := bstep (se 3 (by rfl) ⟨13944098, by rfl⟩ : syracuseStep 74368525 = 27888197) B27888197
theorem B99158033 : Blo 2291435 99158033 := bstep (se 2 (by rfl) ⟨37184262, by rfl⟩ : syracuseStep 99158033 = 74368525) B74368525
theorem B66105355 : Blo 2291435 66105355 := bstep (se 1 (by rfl) ⟨49579016, by rfl⟩ : syracuseStep 66105355 = 99158033) B99158033
theorem B88140473 : Blo 2291435 88140473 := bstep (se 2 (by rfl) ⟨33052677, by rfl⟩ : syracuseStep 88140473 = 66105355) B66105355
theorem B58760315 : Blo 2291435 58760315 := bstep (se 1 (by rfl) ⟨44070236, by rfl⟩ : syracuseStep 58760315 = 88140473) B88140473
theorem B39173543 : Blo 2291435 39173543 := bstep (se 1 (by rfl) ⟨29380157, by rfl⟩ : syracuseStep 39173543 = 58760315) B58760315
theorem B26115695 : Blo 2291435 26115695 := bstep (se 1 (by rfl) ⟨19586771, by rfl⟩ : syracuseStep 26115695 = 39173543) B39173543
theorem B17410463 : Blo 2291435 17410463 := bstep (se 1 (by rfl) ⟨13057847, by rfl⟩ : syracuseStep 17410463 = 26115695) B26115695
theorem B11606975 : Blo 2291435 11606975 := bstep (se 1 (by rfl) ⟨8705231, by rfl⟩ : syracuseStep 11606975 = 17410463) B17410463
theorem B7737983 : Blo 2291435 7737983 := bstep (se 1 (by rfl) ⟨5803487, by rfl⟩ : syracuseStep 7737983 = 11606975) B11606975
theorem B5158655 : Blo 2291435 5158655 := bstep (se 1 (by rfl) ⟨3868991, by rfl⟩ : syracuseStep 5158655 = 7737983) B7737983
theorem B3439103 : Blo 2291435 3439103 := bstep (se 1 (by rfl) ⟨2579327, by rfl⟩ : syracuseStep 3439103 = 5158655) B5158655
theorem B2292735 : Blo 2291435 2292735 := bstep (se 1 (by rfl) ⟨1719551, by rfl⟩ : syracuseStep 2292735 = 3439103) B3439103
theorem B3439109 : Blo 2291435 3439109 := bbase (se 4 (by rfl) ⟨322416, by rfl⟩ : syracuseStep 3439109 = 644833) (by norm_num)
theorem B2292739 : Blo 2291435 2292739 := bstep (se 1 (by rfl) ⟨1719554, by rfl⟩ : syracuseStep 2292739 = 3439109) B3439109
theorem B3869005 : Blo 2291435 3869005 := bbase (se 3 (by rfl) ⟨725438, by rfl⟩ : syracuseStep 3869005 = 1450877) (by norm_num)
theorem B5158673 : Blo 2291435 5158673 := bstep (se 2 (by rfl) ⟨1934502, by rfl⟩ : syracuseStep 5158673 = 3869005) B3869005
theorem B3439115 : Blo 2291435 3439115 := bstep (se 1 (by rfl) ⟨2579336, by rfl⟩ : syracuseStep 3439115 = 5158673) B5158673
theorem B2292743 : Blo 2291435 2292743 := bstep (se 1 (by rfl) ⟨1719557, by rfl⟩ : syracuseStep 2292743 = 3439115) B3439115
theorem B2579341 : Blo 2291435 2579341 := bbase (se 3 (by rfl) ⟨483626, by rfl⟩ : syracuseStep 2579341 = 967253) (by norm_num)
theorem B3439121 : Blo 2291435 3439121 := bstep (se 2 (by rfl) ⟨1289670, by rfl⟩ : syracuseStep 3439121 = 2579341) B2579341
theorem B2292747 : Blo 2291435 2292747 := bstep (se 1 (by rfl) ⟨1719560, by rfl⟩ : syracuseStep 2292747 = 3439121) B3439121
theorem B7738037 : Blo 2291435 7738037 := bbase (se 5 (by rfl) ⟨362720, by rfl⟩ : syracuseStep 7738037 = 725441) (by norm_num)
theorem B5158691 : Blo 2291435 5158691 := bstep (se 1 (by rfl) ⟨3869018, by rfl⟩ : syracuseStep 5158691 = 7738037) B7738037
theorem B3439127 : Blo 2291435 3439127 := bstep (se 1 (by rfl) ⟨2579345, by rfl⟩ : syracuseStep 3439127 = 5158691) B5158691
theorem B2292751 : Blo 2291435 2292751 := bstep (se 1 (by rfl) ⟨1719563, by rfl⟩ : syracuseStep 2292751 = 3439127) B3439127
theorem B3439133 : Blo 2291435 3439133 := bbase (se 3 (by rfl) ⟨644837, by rfl⟩ : syracuseStep 3439133 = 1289675) (by norm_num)
theorem B2292755 : Blo 2291435 2292755 := bstep (se 1 (by rfl) ⟨1719566, by rfl⟩ : syracuseStep 2292755 = 3439133) B3439133
theorem B5158709 : Blo 2291435 5158709 := bbase (se 5 (by rfl) ⟨241814, by rfl⟩ : syracuseStep 5158709 = 483629) (by norm_num)
theorem B3439139 : Blo 2291435 3439139 := bstep (se 1 (by rfl) ⟨2579354, by rfl⟩ : syracuseStep 3439139 = 5158709) B5158709
theorem B2292759 : Blo 2291435 2292759 := bstep (se 1 (by rfl) ⟨1719569, by rfl⟩ : syracuseStep 2292759 = 3439139) B3439139
theorem B14690261 : Blo 2291435 14690261 := bbase (se 7 (by rfl) ⟨172151, by rfl⟩ : syracuseStep 14690261 = 344303) (by norm_num)
theorem B9793507 : Blo 2291435 9793507 := bstep (se 1 (by rfl) ⟨7345130, by rfl⟩ : syracuseStep 9793507 = 14690261) B14690261
theorem B13058009 : Blo 2291435 13058009 := bstep (se 2 (by rfl) ⟨4896753, by rfl⟩ : syracuseStep 13058009 = 9793507) B9793507
theorem B8705339 : Blo 2291435 8705339 := bstep (se 1 (by rfl) ⟨6529004, by rfl⟩ : syracuseStep 8705339 = 13058009) B13058009
theorem B5803559 : Blo 2291435 5803559 := bstep (se 1 (by rfl) ⟨4352669, by rfl⟩ : syracuseStep 5803559 = 8705339) B8705339
theorem B3869039 : Blo 2291435 3869039 := bstep (se 1 (by rfl) ⟨2901779, by rfl⟩ : syracuseStep 3869039 = 5803559) B5803559
theorem B2579359 : Blo 2291435 2579359 := bstep (se 1 (by rfl) ⟨1934519, by rfl⟩ : syracuseStep 2579359 = 3869039) B3869039
theorem B3439145 : Blo 2291435 3439145 := bstep (se 2 (by rfl) ⟨1289679, by rfl⟩ : syracuseStep 3439145 = 2579359) B2579359
theorem B2292763 : Blo 2291435 2292763 := bstep (se 1 (by rfl) ⟨1719572, by rfl⟩ : syracuseStep 2292763 = 3439145) B3439145
theorem B6972149 : Blo 2291435 6972149 := bbase (se 5 (by rfl) ⟨326819, by rfl⟩ : syracuseStep 6972149 = 653639) (by norm_num)
theorem B4648099 : Blo 2291435 4648099 := bstep (se 1 (by rfl) ⟨3486074, by rfl⟩ : syracuseStep 4648099 = 6972149) B6972149
theorem B6197465 : Blo 2291435 6197465 := bstep (se 2 (by rfl) ⟨2324049, by rfl⟩ : syracuseStep 6197465 = 4648099) B4648099
theorem B4131643 : Blo 2291435 4131643 := bstep (se 1 (by rfl) ⟨3098732, by rfl⟩ : syracuseStep 4131643 = 6197465) B6197465
theorem B5508857 : Blo 2291435 5508857 := bstep (se 2 (by rfl) ⟨2065821, by rfl⟩ : syracuseStep 5508857 = 4131643) B4131643
theorem B14690285 : Blo 2291435 14690285 := bstep (se 3 (by rfl) ⟨2754428, by rfl⟩ : syracuseStep 14690285 = 5508857) B5508857
theorem B9793523 : Blo 2291435 9793523 := bstep (se 1 (by rfl) ⟨7345142, by rfl⟩ : syracuseStep 9793523 = 14690285) B14690285
theorem B6529015 : Blo 2291435 6529015 := bstep (se 1 (by rfl) ⟨4896761, by rfl⟩ : syracuseStep 6529015 = 9793523) B9793523
theorem B8705353 : Blo 2291435 8705353 := bstep (se 2 (by rfl) ⟨3264507, by rfl⟩ : syracuseStep 8705353 = 6529015) B6529015
theorem B11607137 : Blo 2291435 11607137 := bstep (se 2 (by rfl) ⟨4352676, by rfl⟩ : syracuseStep 11607137 = 8705353) B8705353
theorem B7738091 : Blo 2291435 7738091 := bstep (se 1 (by rfl) ⟨5803568, by rfl⟩ : syracuseStep 7738091 = 11607137) B11607137
theorem B5158727 : Blo 2291435 5158727 := bstep (se 1 (by rfl) ⟨3869045, by rfl⟩ : syracuseStep 5158727 = 7738091) B7738091
theorem B3439151 : Blo 2291435 3439151 := bstep (se 1 (by rfl) ⟨2579363, by rfl⟩ : syracuseStep 3439151 = 5158727) B5158727
theorem B2292767 : Blo 2291435 2292767 := bstep (se 1 (by rfl) ⟨1719575, by rfl⟩ : syracuseStep 2292767 = 3439151) B3439151
theorem B3439157 : Blo 2291435 3439157 := bbase (se 5 (by rfl) ⟨161210, by rfl⟩ : syracuseStep 3439157 = 322421) (by norm_num)
theorem B2292771 : Blo 2291435 2292771 := bstep (se 1 (by rfl) ⟨1719578, by rfl⟩ : syracuseStep 2292771 = 3439157) B3439157
theorem B5803589 : Blo 2291435 5803589 := bbase (se 4 (by rfl) ⟨544086, by rfl⟩ : syracuseStep 5803589 = 1088173) (by norm_num)
theorem B3869059 : Blo 2291435 3869059 := bstep (se 1 (by rfl) ⟨2901794, by rfl⟩ : syracuseStep 3869059 = 5803589) B5803589
theorem B5158745 : Blo 2291435 5158745 := bstep (se 2 (by rfl) ⟨1934529, by rfl⟩ : syracuseStep 5158745 = 3869059) B3869059
theorem B3439163 : Blo 2291435 3439163 := bstep (se 1 (by rfl) ⟨2579372, by rfl⟩ : syracuseStep 3439163 = 5158745) B5158745
theorem B2292775 : Blo 2291435 2292775 := bstep (se 1 (by rfl) ⟨1719581, by rfl⟩ : syracuseStep 2292775 = 3439163) B3439163
theorem B2579377 : Blo 2291435 2579377 := bbase (se 2 (by rfl) ⟨967266, by rfl⟩ : syracuseStep 2579377 = 1934533) (by norm_num)
theorem B3439169 : Blo 2291435 3439169 := bstep (se 2 (by rfl) ⟨1289688, by rfl⟩ : syracuseStep 3439169 = 2579377) B2579377
theorem B2292779 : Blo 2291435 2292779 := bstep (se 1 (by rfl) ⟨1719584, by rfl⟩ : syracuseStep 2292779 = 3439169) B3439169
theorem B6529061 : Blo 2291435 6529061 := bbase (se 4 (by rfl) ⟨612099, by rfl⟩ : syracuseStep 6529061 = 1224199) (by norm_num)
theorem B4352707 : Blo 2291435 4352707 := bstep (se 1 (by rfl) ⟨3264530, by rfl⟩ : syracuseStep 4352707 = 6529061) B6529061
theorem B5803609 : Blo 2291435 5803609 := bstep (se 2 (by rfl) ⟨2176353, by rfl⟩ : syracuseStep 5803609 = 4352707) B4352707
theorem B7738145 : Blo 2291435 7738145 := bstep (se 2 (by rfl) ⟨2901804, by rfl⟩ : syracuseStep 7738145 = 5803609) B5803609
theorem B5158763 : Blo 2291435 5158763 := bstep (se 1 (by rfl) ⟨3869072, by rfl⟩ : syracuseStep 5158763 = 7738145) B7738145
theorem B3439175 : Blo 2291435 3439175 := bstep (se 1 (by rfl) ⟨2579381, by rfl⟩ : syracuseStep 3439175 = 5158763) B5158763
theorem B2292783 : Blo 2291435 2292783 := bstep (se 1 (by rfl) ⟨1719587, by rfl⟩ : syracuseStep 2292783 = 3439175) B3439175
theorem B3439181 : Blo 2291435 3439181 := bbase (se 3 (by rfl) ⟨644846, by rfl⟩ : syracuseStep 3439181 = 1289693) (by norm_num)
theorem B2292787 : Blo 2291435 2292787 := bstep (se 1 (by rfl) ⟨1719590, by rfl⟩ : syracuseStep 2292787 = 3439181) B3439181
theorem B5158781 : Blo 2291435 5158781 := bbase (se 3 (by rfl) ⟨967271, by rfl⟩ : syracuseStep 5158781 = 1934543) (by norm_num)
theorem B3439187 : Blo 2291435 3439187 := bstep (se 1 (by rfl) ⟨2579390, by rfl⟩ : syracuseStep 3439187 = 5158781) B5158781
theorem B2292791 : Blo 2291435 2292791 := bstep (se 1 (by rfl) ⟨1719593, by rfl⟩ : syracuseStep 2292791 = 3439187) B3439187
theorem B3869093 : Blo 2291435 3869093 := bbase (se 4 (by rfl) ⟨362727, by rfl⟩ : syracuseStep 3869093 = 725455) (by norm_num)
theorem B2579395 : Blo 2291435 2579395 := bstep (se 1 (by rfl) ⟨1934546, by rfl⟩ : syracuseStep 2579395 = 3869093) B3869093
theorem B3439193 : Blo 2291435 3439193 := bstep (se 2 (by rfl) ⟨1289697, by rfl⟩ : syracuseStep 3439193 = 2579395) B2579395
theorem B2292795 : Blo 2291435 2292795 := bstep (se 1 (by rfl) ⟨1719596, by rfl⟩ : syracuseStep 2292795 = 3439193) B3439193
theorem B2941417 : Blo 2291435 2941417 := bbase (se 2 (by rfl) ⟨1103031, by rfl⟩ : syracuseStep 2941417 = 2206063) (by norm_num)
theorem B15687557 : Blo 2291435 15687557 := bstep (se 4 (by rfl) ⟨1470708, by rfl⟩ : syracuseStep 15687557 = 2941417) B2941417
theorem B10458371 : Blo 2291435 10458371 := bstep (se 1 (by rfl) ⟨7843778, by rfl⟩ : syracuseStep 10458371 = 15687557) B15687557
theorem B6972247 : Blo 2291435 6972247 := bstep (se 1 (by rfl) ⟨5229185, by rfl⟩ : syracuseStep 6972247 = 10458371) B10458371
theorem B9296329 : Blo 2291435 9296329 := bstep (se 2 (by rfl) ⟨3486123, by rfl⟩ : syracuseStep 9296329 = 6972247) B6972247
theorem B12395105 : Blo 2291435 12395105 := bstep (se 2 (by rfl) ⟨4648164, by rfl⟩ : syracuseStep 12395105 = 9296329) B9296329
theorem B8263403 : Blo 2291435 8263403 := bstep (se 1 (by rfl) ⟨6197552, by rfl⟩ : syracuseStep 8263403 = 12395105) B12395105
theorem B5508935 : Blo 2291435 5508935 := bstep (se 1 (by rfl) ⟨4131701, by rfl⟩ : syracuseStep 5508935 = 8263403) B8263403
theorem B3672623 : Blo 2291435 3672623 := bstep (se 1 (by rfl) ⟨2754467, by rfl⟩ : syracuseStep 3672623 = 5508935) B5508935
theorem B2448415 : Blo 2291435 2448415 := bstep (se 1 (by rfl) ⟨1836311, by rfl⟩ : syracuseStep 2448415 = 3672623) B3672623
theorem B3264553 : Blo 2291435 3264553 := bstep (se 2 (by rfl) ⟨1224207, by rfl⟩ : syracuseStep 3264553 = 2448415) B2448415
theorem B17410949 : Blo 2291435 17410949 := bstep (se 4 (by rfl) ⟨1632276, by rfl⟩ : syracuseStep 17410949 = 3264553) B3264553
theorem B11607299 : Blo 2291435 11607299 := bstep (se 1 (by rfl) ⟨8705474, by rfl⟩ : syracuseStep 11607299 = 17410949) B17410949
theorem B7738199 : Blo 2291435 7738199 := bstep (se 1 (by rfl) ⟨5803649, by rfl⟩ : syracuseStep 7738199 = 11607299) B11607299
theorem B5158799 : Blo 2291435 5158799 := bstep (se 1 (by rfl) ⟨3869099, by rfl⟩ : syracuseStep 5158799 = 7738199) B7738199
theorem B3439199 : Blo 2291435 3439199 := bstep (se 1 (by rfl) ⟨2579399, by rfl⟩ : syracuseStep 3439199 = 5158799) B5158799
theorem B2292799 : Blo 2291435 2292799 := bstep (se 1 (by rfl) ⟨1719599, by rfl⟩ : syracuseStep 2292799 = 3439199) B3439199
theorem B3439205 : Blo 2291435 3439205 := bbase (se 4 (by rfl) ⟨322425, by rfl⟩ : syracuseStep 3439205 = 644851) (by norm_num)
theorem B2292803 : Blo 2291435 2292803 := bstep (se 1 (by rfl) ⟨1719602, by rfl⟩ : syracuseStep 2292803 = 3439205) B3439205
theorem B3264565 : Blo 2291435 3264565 := bbase (se 5 (by rfl) ⟨153026, by rfl⟩ : syracuseStep 3264565 = 306053) (by norm_num)
theorem B4352753 : Blo 2291435 4352753 := bstep (se 2 (by rfl) ⟨1632282, by rfl⟩ : syracuseStep 4352753 = 3264565) B3264565
theorem B2901835 : Blo 2291435 2901835 := bstep (se 1 (by rfl) ⟨2176376, by rfl⟩ : syracuseStep 2901835 = 4352753) B4352753
theorem B3869113 : Blo 2291435 3869113 := bstep (se 2 (by rfl) ⟨1450917, by rfl⟩ : syracuseStep 3869113 = 2901835) B2901835
theorem B5158817 : Blo 2291435 5158817 := bstep (se 2 (by rfl) ⟨1934556, by rfl⟩ : syracuseStep 5158817 = 3869113) B3869113
theorem B3439211 : Blo 2291435 3439211 := bstep (se 1 (by rfl) ⟨2579408, by rfl⟩ : syracuseStep 3439211 = 5158817) B5158817
theorem B2292807 : Blo 2291435 2292807 := bstep (se 1 (by rfl) ⟨1719605, by rfl⟩ : syracuseStep 2292807 = 3439211) B3439211
theorem B2579413 : Blo 2291435 2579413 := bbase (se 7 (by rfl) ⟨30227, by rfl⟩ : syracuseStep 2579413 = 60455) (by norm_num)
theorem B3439217 : Blo 2291435 3439217 := bstep (se 2 (by rfl) ⟨1289706, by rfl⟩ : syracuseStep 3439217 = 2579413) B2579413
theorem B2292811 : Blo 2291435 2292811 := bstep (se 1 (by rfl) ⟨1719608, by rfl⟩ : syracuseStep 2292811 = 3439217) B3439217
theorem B2901845 : Blo 2291435 2901845 := bbase (se 9 (by rfl) ⟨8501, by rfl⟩ : syracuseStep 2901845 = 17003) (by norm_num)
theorem B7738253 : Blo 2291435 7738253 := bstep (se 3 (by rfl) ⟨1450922, by rfl⟩ : syracuseStep 7738253 = 2901845) B2901845
theorem B5158835 : Blo 2291435 5158835 := bstep (se 1 (by rfl) ⟨3869126, by rfl⟩ : syracuseStep 5158835 = 7738253) B7738253
theorem B3439223 : Blo 2291435 3439223 := bstep (se 1 (by rfl) ⟨2579417, by rfl⟩ : syracuseStep 3439223 = 5158835) B5158835
theorem B2292815 : Blo 2291435 2292815 := bstep (se 1 (by rfl) ⟨1719611, by rfl⟩ : syracuseStep 2292815 = 3439223) B3439223
theorem B3439229 : Blo 2291435 3439229 := bbase (se 3 (by rfl) ⟨644855, by rfl⟩ : syracuseStep 3439229 = 1289711) (by norm_num)
theorem B2292819 : Blo 2291435 2292819 := bstep (se 1 (by rfl) ⟨1719614, by rfl⟩ : syracuseStep 2292819 = 3439229) B3439229
theorem B5158853 : Blo 2291435 5158853 := bbase (se 4 (by rfl) ⟨483642, by rfl⟩ : syracuseStep 5158853 = 967285) (by norm_num)
theorem B3439235 : Blo 2291435 3439235 := bstep (se 1 (by rfl) ⟨2579426, by rfl⟩ : syracuseStep 3439235 = 5158853) B5158853
theorem B2292823 : Blo 2291435 2292823 := bstep (se 1 (by rfl) ⟨1719617, by rfl⟩ : syracuseStep 2292823 = 3439235) B3439235
theorem B9793781 : Blo 2291435 9793781 := bbase (se 5 (by rfl) ⟨459083, by rfl⟩ : syracuseStep 9793781 = 918167) (by norm_num)
theorem B6529187 : Blo 2291435 6529187 := bstep (se 1 (by rfl) ⟨4896890, by rfl⟩ : syracuseStep 6529187 = 9793781) B9793781
theorem B4352791 : Blo 2291435 4352791 := bstep (se 1 (by rfl) ⟨3264593, by rfl⟩ : syracuseStep 4352791 = 6529187) B6529187
theorem B5803721 : Blo 2291435 5803721 := bstep (se 2 (by rfl) ⟨2176395, by rfl⟩ : syracuseStep 5803721 = 4352791) B4352791
theorem B3869147 : Blo 2291435 3869147 := bstep (se 1 (by rfl) ⟨2901860, by rfl⟩ : syracuseStep 3869147 = 5803721) B5803721
theorem B2579431 : Blo 2291435 2579431 := bstep (se 1 (by rfl) ⟨1934573, by rfl⟩ : syracuseStep 2579431 = 3869147) B3869147
theorem B3439241 : Blo 2291435 3439241 := bstep (se 2 (by rfl) ⟨1289715, by rfl⟩ : syracuseStep 3439241 = 2579431) B2579431
theorem B2292827 : Blo 2291435 2292827 := bstep (se 1 (by rfl) ⟨1719620, by rfl⟩ : syracuseStep 2292827 = 3439241) B3439241
theorem B11607461 : Blo 2291435 11607461 := bbase (se 4 (by rfl) ⟨1088199, by rfl⟩ : syracuseStep 11607461 = 2176399) (by norm_num)
theorem B7738307 : Blo 2291435 7738307 := bstep (se 1 (by rfl) ⟨5803730, by rfl⟩ : syracuseStep 7738307 = 11607461) B11607461
theorem B5158871 : Blo 2291435 5158871 := bstep (se 1 (by rfl) ⟨3869153, by rfl⟩ : syracuseStep 5158871 = 7738307) B7738307
theorem B3439247 : Blo 2291435 3439247 := bstep (se 1 (by rfl) ⟨2579435, by rfl⟩ : syracuseStep 3439247 = 5158871) B5158871
theorem B2292831 : Blo 2291435 2292831 := bstep (se 1 (by rfl) ⟨1719623, by rfl⟩ : syracuseStep 2292831 = 3439247) B3439247
theorem B3439253 : Blo 2291435 3439253 := bbase (se 6 (by rfl) ⟨80607, by rfl⟩ : syracuseStep 3439253 = 161215) (by norm_num)
theorem B2292835 : Blo 2291435 2292835 := bstep (se 1 (by rfl) ⟨1719626, by rfl⟩ : syracuseStep 2292835 = 3439253) B3439253
theorem B3141109 : Blo 2291435 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B16752581 : Blo 2291435 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B11168387 : Blo 2291435 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B7445591 : Blo 2291435 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B4963727 : Blo 2291435 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B13236605 : Blo 2291435 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B8824403 : Blo 2291435 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B23531741 : Blo 2291435 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B15687827 : Blo 2291435 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B10458551 : Blo 2291435 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B6972367 : Blo 2291435 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B9296489 : Blo 2291435 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B24790637 : Blo 2291435 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B16527091 : Blo 2291435 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B22036121 : Blo 2291435 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B14690747 : Blo 2291435 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B9793831 : Blo 2291435 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B13058441 : Blo 2291435 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B8705627 : Blo 2291435 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B5803751 : Blo 2291435 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B3869167 : Blo 2291435 3869167 := bstep (se 1 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 3869167 = 5803751) B5803751
theorem B5158889 : Blo 2291435 5158889 := bstep (se 2 (by rfl) ⟨1934583, by rfl⟩ : syracuseStep 5158889 = 3869167) B3869167
theorem B3439259 : Blo 2291435 3439259 := bstep (se 1 (by rfl) ⟨2579444, by rfl⟩ : syracuseStep 3439259 = 5158889) B5158889
theorem B2292839 : Blo 2291435 2292839 := bstep (se 1 (by rfl) ⟨1719629, by rfl⟩ : syracuseStep 2292839 = 3439259) B3439259
theorem B2579449 : Blo 2291435 2579449 := bbase (se 2 (by rfl) ⟨967293, by rfl⟩ : syracuseStep 2579449 = 1934587) (by norm_num)
theorem B3439265 : Blo 2291435 3439265 := bstep (se 2 (by rfl) ⟨1289724, by rfl⟩ : syracuseStep 3439265 = 2579449) B2579449
theorem B2292843 : Blo 2291435 2292843 := bstep (se 1 (by rfl) ⟨1719632, by rfl⟩ : syracuseStep 2292843 = 3439265) B3439265
theorem B4648261 : Blo 2291435 4648261 := bbase (se 4 (by rfl) ⟨435774, by rfl⟩ : syracuseStep 4648261 = 871549) (by norm_num)
theorem B6197681 : Blo 2291435 6197681 := bstep (se 2 (by rfl) ⟨2324130, by rfl⟩ : syracuseStep 6197681 = 4648261) B4648261
theorem B16527149 : Blo 2291435 16527149 := bstep (se 3 (by rfl) ⟨3098840, by rfl⟩ : syracuseStep 16527149 = 6197681) B6197681
theorem B11018099 : Blo 2291435 11018099 := bstep (se 1 (by rfl) ⟨8263574, by rfl⟩ : syracuseStep 11018099 = 16527149) B16527149
theorem B7345399 : Blo 2291435 7345399 := bstep (se 1 (by rfl) ⟨5509049, by rfl⟩ : syracuseStep 7345399 = 11018099) B11018099
theorem B9793865 : Blo 2291435 9793865 := bstep (se 2 (by rfl) ⟨3672699, by rfl⟩ : syracuseStep 9793865 = 7345399) B7345399
theorem B6529243 : Blo 2291435 6529243 := bstep (se 1 (by rfl) ⟨4896932, by rfl⟩ : syracuseStep 6529243 = 9793865) B9793865
theorem B8705657 : Blo 2291435 8705657 := bstep (se 2 (by rfl) ⟨3264621, by rfl⟩ : syracuseStep 8705657 = 6529243) B6529243
theorem B5803771 : Blo 2291435 5803771 := bstep (se 1 (by rfl) ⟨4352828, by rfl⟩ : syracuseStep 5803771 = 8705657) B8705657
theorem B7738361 : Blo 2291435 7738361 := bstep (se 2 (by rfl) ⟨2901885, by rfl⟩ : syracuseStep 7738361 = 5803771) B5803771
theorem B5158907 : Blo 2291435 5158907 := bstep (se 1 (by rfl) ⟨3869180, by rfl⟩ : syracuseStep 5158907 = 7738361) B7738361
theorem B3439271 : Blo 2291435 3439271 := bstep (se 1 (by rfl) ⟨2579453, by rfl⟩ : syracuseStep 3439271 = 5158907) B5158907
theorem B2292847 : Blo 2291435 2292847 := bstep (se 1 (by rfl) ⟨1719635, by rfl⟩ : syracuseStep 2292847 = 3439271) B3439271
theorem B3439277 : Blo 2291435 3439277 := bbase (se 3 (by rfl) ⟨644864, by rfl⟩ : syracuseStep 3439277 = 1289729) (by norm_num)
theorem B2292851 : Blo 2291435 2292851 := bstep (se 1 (by rfl) ⟨1719638, by rfl⟩ : syracuseStep 2292851 = 3439277) B3439277
theorem B5158925 : Blo 2291435 5158925 := bbase (se 3 (by rfl) ⟨967298, by rfl⟩ : syracuseStep 5158925 = 1934597) (by norm_num)
theorem B3439283 : Blo 2291435 3439283 := bstep (se 1 (by rfl) ⟨2579462, by rfl⟩ : syracuseStep 3439283 = 5158925) B5158925
theorem B2292855 : Blo 2291435 2292855 := bstep (se 1 (by rfl) ⟨1719641, by rfl⟩ : syracuseStep 2292855 = 3439283) B3439283
theorem B2901901 : Blo 2291435 2901901 := bbase (se 3 (by rfl) ⟨544106, by rfl⟩ : syracuseStep 2901901 = 1088213) (by norm_num)
theorem B3869201 : Blo 2291435 3869201 := bstep (se 2 (by rfl) ⟨1450950, by rfl⟩ : syracuseStep 3869201 = 2901901) B2901901
theorem B2579467 : Blo 2291435 2579467 := bstep (se 1 (by rfl) ⟨1934600, by rfl⟩ : syracuseStep 2579467 = 3869201) B3869201
theorem B3439289 : Blo 2291435 3439289 := bstep (se 2 (by rfl) ⟨1289733, by rfl⟩ : syracuseStep 3439289 = 2579467) B2579467
theorem B2292859 : Blo 2291435 2292859 := bstep (se 1 (by rfl) ⟨1719644, by rfl⟩ : syracuseStep 2292859 = 3439289) B3439289
theorem B15687989 : Blo 2291435 15687989 := bbase (se 5 (by rfl) ⟨735374, by rfl⟩ : syracuseStep 15687989 = 1470749) (by norm_num)
theorem B10458659 : Blo 2291435 10458659 := bstep (se 1 (by rfl) ⟨7843994, by rfl⟩ : syracuseStep 10458659 = 15687989) B15687989
theorem B27889757 : Blo 2291435 27889757 := bstep (se 3 (by rfl) ⟨5229329, by rfl⟩ : syracuseStep 27889757 = 10458659) B10458659
theorem B18593171 : Blo 2291435 18593171 := bstep (se 1 (by rfl) ⟨13944878, by rfl⟩ : syracuseStep 18593171 = 27889757) B27889757
theorem B12395447 : Blo 2291435 12395447 := bstep (se 1 (by rfl) ⟨9296585, by rfl⟩ : syracuseStep 12395447 = 18593171) B18593171
theorem B8263631 : Blo 2291435 8263631 := bstep (se 1 (by rfl) ⟨6197723, by rfl⟩ : syracuseStep 8263631 = 12395447) B12395447
theorem B22036349 : Blo 2291435 22036349 := bstep (se 3 (by rfl) ⟨4131815, by rfl⟩ : syracuseStep 22036349 = 8263631) B8263631
theorem B14690899 : Blo 2291435 14690899 := bstep (se 1 (by rfl) ⟨11018174, by rfl⟩ : syracuseStep 14690899 = 22036349) B22036349
theorem B19587865 : Blo 2291435 19587865 := bstep (se 2 (by rfl) ⟨7345449, by rfl⟩ : syracuseStep 19587865 = 14690899) B14690899
theorem B26117153 : Blo 2291435 26117153 := bstep (se 2 (by rfl) ⟨9793932, by rfl⟩ : syracuseStep 26117153 = 19587865) B19587865
theorem B17411435 : Blo 2291435 17411435 := bstep (se 1 (by rfl) ⟨13058576, by rfl⟩ : syracuseStep 17411435 = 26117153) B26117153
theorem B11607623 : Blo 2291435 11607623 := bstep (se 1 (by rfl) ⟨8705717, by rfl⟩ : syracuseStep 11607623 = 17411435) B17411435
theorem B7738415 : Blo 2291435 7738415 := bstep (se 1 (by rfl) ⟨5803811, by rfl⟩ : syracuseStep 7738415 = 11607623) B11607623
theorem B5158943 : Blo 2291435 5158943 := bstep (se 1 (by rfl) ⟨3869207, by rfl⟩ : syracuseStep 5158943 = 7738415) B7738415
theorem B3439295 : Blo 2291435 3439295 := bstep (se 1 (by rfl) ⟨2579471, by rfl⟩ : syracuseStep 3439295 = 5158943) B5158943
theorem B2292863 : Blo 2291435 2292863 := bstep (se 1 (by rfl) ⟨1719647, by rfl⟩ : syracuseStep 2292863 = 3439295) B3439295
theorem B3439301 : Blo 2291435 3439301 := bbase (se 4 (by rfl) ⟨322434, by rfl⟩ : syracuseStep 3439301 = 644869) (by norm_num)
theorem B2292867 : Blo 2291435 2292867 := bstep (se 1 (by rfl) ⟨1719650, by rfl⟩ : syracuseStep 2292867 = 3439301) B3439301
theorem B3869221 : Blo 2291435 3869221 := bbase (se 4 (by rfl) ⟨362739, by rfl⟩ : syracuseStep 3869221 = 725479) (by norm_num)
theorem B5158961 : Blo 2291435 5158961 := bstep (se 2 (by rfl) ⟨1934610, by rfl⟩ : syracuseStep 5158961 = 3869221) B3869221
theorem B3439307 : Blo 2291435 3439307 := bstep (se 1 (by rfl) ⟨2579480, by rfl⟩ : syracuseStep 3439307 = 5158961) B5158961
theorem B2292871 : Blo 2291435 2292871 := bstep (se 1 (by rfl) ⟨1719653, by rfl⟩ : syracuseStep 2292871 = 3439307) B3439307
theorem B2579485 : Blo 2291435 2579485 := bbase (se 3 (by rfl) ⟨483653, by rfl⟩ : syracuseStep 2579485 = 967307) (by norm_num)
theorem B3439313 : Blo 2291435 3439313 := bstep (se 2 (by rfl) ⟨1289742, by rfl⟩ : syracuseStep 3439313 = 2579485) B2579485
theorem B2292875 : Blo 2291435 2292875 := bstep (se 1 (by rfl) ⟨1719656, by rfl⟩ : syracuseStep 2292875 = 3439313) B3439313
theorem B7738469 : Blo 2291435 7738469 := bbase (se 4 (by rfl) ⟨725481, by rfl⟩ : syracuseStep 7738469 = 1450963) (by norm_num)
theorem B5158979 : Blo 2291435 5158979 := bstep (se 1 (by rfl) ⟨3869234, by rfl⟩ : syracuseStep 5158979 = 7738469) B7738469
theorem B3439319 : Blo 2291435 3439319 := bstep (se 1 (by rfl) ⟨2579489, by rfl⟩ : syracuseStep 3439319 = 5158979) B5158979
theorem B2292879 : Blo 2291435 2292879 := bstep (se 1 (by rfl) ⟨1719659, by rfl⟩ : syracuseStep 2292879 = 3439319) B3439319
theorem B3439325 : Blo 2291435 3439325 := bbase (se 3 (by rfl) ⟨644873, by rfl⟩ : syracuseStep 3439325 = 1289747) (by norm_num)
theorem B2292883 : Blo 2291435 2292883 := bstep (se 1 (by rfl) ⟨1719662, by rfl⟩ : syracuseStep 2292883 = 3439325) B3439325
theorem B5158997 : Blo 2291435 5158997 := bbase (se 8 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 5158997 = 60457) (by norm_num)
theorem B3439331 : Blo 2291435 3439331 := bstep (se 1 (by rfl) ⟨2579498, by rfl⟩ : syracuseStep 3439331 = 5158997) B5158997
theorem B2292887 : Blo 2291435 2292887 := bstep (se 1 (by rfl) ⟨1719665, by rfl⟩ : syracuseStep 2292887 = 3439331) B3439331
theorem B7345541 : Blo 2291435 7345541 := bbase (se 4 (by rfl) ⟨688644, by rfl⟩ : syracuseStep 7345541 = 1377289) (by norm_num)
theorem B4897027 : Blo 2291435 4897027 := bstep (se 1 (by rfl) ⟨3672770, by rfl⟩ : syracuseStep 4897027 = 7345541) B7345541
theorem B6529369 : Blo 2291435 6529369 := bstep (se 2 (by rfl) ⟨2448513, by rfl⟩ : syracuseStep 6529369 = 4897027) B4897027
theorem B8705825 : Blo 2291435 8705825 := bstep (se 2 (by rfl) ⟨3264684, by rfl⟩ : syracuseStep 8705825 = 6529369) B6529369
theorem B5803883 : Blo 2291435 5803883 := bstep (se 1 (by rfl) ⟨4352912, by rfl⟩ : syracuseStep 5803883 = 8705825) B8705825
theorem B3869255 : Blo 2291435 3869255 := bstep (se 1 (by rfl) ⟨2901941, by rfl⟩ : syracuseStep 3869255 = 5803883) B5803883
theorem B2579503 : Blo 2291435 2579503 := bstep (se 1 (by rfl) ⟨1934627, by rfl⟩ : syracuseStep 2579503 = 3869255) B3869255
theorem B3439337 : Blo 2291435 3439337 := bstep (se 2 (by rfl) ⟨1289751, by rfl⟩ : syracuseStep 3439337 = 2579503) B2579503
theorem B2292891 : Blo 2291435 2292891 := bstep (se 1 (by rfl) ⟨1719668, by rfl⟩ : syracuseStep 2292891 = 3439337) B3439337
theorem B3486269 : Blo 2291435 3486269 := bbase (se 3 (by rfl) ⟨653675, by rfl⟩ : syracuseStep 3486269 = 1307351) (by norm_num)
theorem B2324179 : Blo 2291435 2324179 := bstep (se 1 (by rfl) ⟨1743134, by rfl⟩ : syracuseStep 2324179 = 3486269) B3486269
theorem B3098905 : Blo 2291435 3098905 := bstep (se 2 (by rfl) ⟨1162089, by rfl⟩ : syracuseStep 3098905 = 2324179) B2324179
theorem B16527493 : Blo 2291435 16527493 := bstep (se 4 (by rfl) ⟨1549452, by rfl⟩ : syracuseStep 16527493 = 3098905) B3098905
theorem B22036657 : Blo 2291435 22036657 := bstep (se 2 (by rfl) ⟨8263746, by rfl⟩ : syracuseStep 22036657 = 16527493) B16527493
theorem B29382209 : Blo 2291435 29382209 := bstep (se 2 (by rfl) ⟨11018328, by rfl⟩ : syracuseStep 29382209 = 22036657) B22036657
theorem B19588139 : Blo 2291435 19588139 := bstep (se 1 (by rfl) ⟨14691104, by rfl⟩ : syracuseStep 19588139 = 29382209) B29382209
theorem B13058759 : Blo 2291435 13058759 := bstep (se 1 (by rfl) ⟨9794069, by rfl⟩ : syracuseStep 13058759 = 19588139) B19588139
theorem B8705839 : Blo 2291435 8705839 := bstep (se 1 (by rfl) ⟨6529379, by rfl⟩ : syracuseStep 8705839 = 13058759) B13058759
theorem B11607785 : Blo 2291435 11607785 := bstep (se 2 (by rfl) ⟨4352919, by rfl⟩ : syracuseStep 11607785 = 8705839) B8705839
theorem B7738523 : Blo 2291435 7738523 := bstep (se 1 (by rfl) ⟨5803892, by rfl⟩ : syracuseStep 7738523 = 11607785) B11607785
theorem B5159015 : Blo 2291435 5159015 := bstep (se 1 (by rfl) ⟨3869261, by rfl⟩ : syracuseStep 5159015 = 7738523) B7738523
theorem B3439343 : Blo 2291435 3439343 := bstep (se 1 (by rfl) ⟨2579507, by rfl⟩ : syracuseStep 3439343 = 5159015) B5159015
theorem B2292895 : Blo 2291435 2292895 := bstep (se 1 (by rfl) ⟨1719671, by rfl⟩ : syracuseStep 2292895 = 3439343) B3439343
theorem B3439349 : Blo 2291435 3439349 := bbase (se 5 (by rfl) ⟨161219, by rfl⟩ : syracuseStep 3439349 = 322439) (by norm_num)
theorem B2292899 : Blo 2291435 2292899 := bstep (se 1 (by rfl) ⟨1719674, by rfl⟩ : syracuseStep 2292899 = 3439349) B3439349
theorem B5883101 : Blo 2291435 5883101 := bbase (se 3 (by rfl) ⟨1103081, by rfl⟩ : syracuseStep 5883101 = 2206163) (by norm_num)
theorem B3922067 : Blo 2291435 3922067 := bstep (se 1 (by rfl) ⟨2941550, by rfl⟩ : syracuseStep 3922067 = 5883101) B5883101
theorem B10458845 : Blo 2291435 10458845 := bstep (se 3 (by rfl) ⟨1961033, by rfl⟩ : syracuseStep 10458845 = 3922067) B3922067
theorem B6972563 : Blo 2291435 6972563 := bstep (se 1 (by rfl) ⟨5229422, by rfl⟩ : syracuseStep 6972563 = 10458845) B10458845
theorem B4648375 : Blo 2291435 4648375 := bstep (se 1 (by rfl) ⟨3486281, by rfl⟩ : syracuseStep 4648375 = 6972563) B6972563
theorem B6197833 : Blo 2291435 6197833 := bstep (se 2 (by rfl) ⟨2324187, by rfl⟩ : syracuseStep 6197833 = 4648375) B4648375
theorem B8263777 : Blo 2291435 8263777 := bstep (se 2 (by rfl) ⟨3098916, by rfl⟩ : syracuseStep 8263777 = 6197833) B6197833
theorem B11018369 : Blo 2291435 11018369 := bstep (se 2 (by rfl) ⟨4131888, by rfl⟩ : syracuseStep 11018369 = 8263777) B8263777
theorem B7345579 : Blo 2291435 7345579 := bstep (se 1 (by rfl) ⟨5509184, by rfl⟩ : syracuseStep 7345579 = 11018369) B11018369
theorem B9794105 : Blo 2291435 9794105 := bstep (se 2 (by rfl) ⟨3672789, by rfl⟩ : syracuseStep 9794105 = 7345579) B7345579
theorem B6529403 : Blo 2291435 6529403 := bstep (se 1 (by rfl) ⟨4897052, by rfl⟩ : syracuseStep 6529403 = 9794105) B9794105
theorem B4352935 : Blo 2291435 4352935 := bstep (se 1 (by rfl) ⟨3264701, by rfl⟩ : syracuseStep 4352935 = 6529403) B6529403
theorem B5803913 : Blo 2291435 5803913 := bstep (se 2 (by rfl) ⟨2176467, by rfl⟩ : syracuseStep 5803913 = 4352935) B4352935
theorem B3869275 : Blo 2291435 3869275 := bstep (se 1 (by rfl) ⟨2901956, by rfl⟩ : syracuseStep 3869275 = 5803913) B5803913
theorem B5159033 : Blo 2291435 5159033 := bstep (se 2 (by rfl) ⟨1934637, by rfl⟩ : syracuseStep 5159033 = 3869275) B3869275
theorem B3439355 : Blo 2291435 3439355 := bstep (se 1 (by rfl) ⟨2579516, by rfl⟩ : syracuseStep 3439355 = 5159033) B5159033
theorem B2292903 : Blo 2291435 2292903 := bstep (se 1 (by rfl) ⟨1719677, by rfl⟩ : syracuseStep 2292903 = 3439355) B3439355
theorem B2579521 : Blo 2291435 2579521 := bbase (se 2 (by rfl) ⟨967320, by rfl⟩ : syracuseStep 2579521 = 1934641) (by norm_num)
theorem B3439361 : Blo 2291435 3439361 := bstep (se 2 (by rfl) ⟨1289760, by rfl⟩ : syracuseStep 3439361 = 2579521) B2579521
theorem B2292907 : Blo 2291435 2292907 := bstep (se 1 (by rfl) ⟨1719680, by rfl⟩ : syracuseStep 2292907 = 3439361) B3439361
theorem B5803933 : Blo 2291435 5803933 := bbase (se 3 (by rfl) ⟨1088237, by rfl⟩ : syracuseStep 5803933 = 2176475) (by norm_num)
theorem B7738577 : Blo 2291435 7738577 := bstep (se 2 (by rfl) ⟨2901966, by rfl⟩ : syracuseStep 7738577 = 5803933) B5803933
theorem B5159051 : Blo 2291435 5159051 := bstep (se 1 (by rfl) ⟨3869288, by rfl⟩ : syracuseStep 5159051 = 7738577) B7738577
theorem B3439367 : Blo 2291435 3439367 := bstep (se 1 (by rfl) ⟨2579525, by rfl⟩ : syracuseStep 3439367 = 5159051) B5159051
theorem B2292911 : Blo 2291435 2292911 := bstep (se 1 (by rfl) ⟨1719683, by rfl⟩ : syracuseStep 2292911 = 3439367) B3439367
theorem B3439373 : Blo 2291435 3439373 := bbase (se 3 (by rfl) ⟨644882, by rfl⟩ : syracuseStep 3439373 = 1289765) (by norm_num)
theorem B2292915 : Blo 2291435 2292915 := bstep (se 1 (by rfl) ⟨1719686, by rfl⟩ : syracuseStep 2292915 = 3439373) B3439373
theorem B5159069 : Blo 2291435 5159069 := bbase (se 3 (by rfl) ⟨967325, by rfl⟩ : syracuseStep 5159069 = 1934651) (by norm_num)
theorem B3439379 : Blo 2291435 3439379 := bstep (se 1 (by rfl) ⟨2579534, by rfl⟩ : syracuseStep 3439379 = 5159069) B5159069
theorem B2292919 : Blo 2291435 2292919 := bstep (se 1 (by rfl) ⟨1719689, by rfl⟩ : syracuseStep 2292919 = 3439379) B3439379
theorem B3869309 : Blo 2291435 3869309 := bbase (se 3 (by rfl) ⟨725495, by rfl⟩ : syracuseStep 3869309 = 1450991) (by norm_num)
theorem B2579539 : Blo 2291435 2579539 := bstep (se 1 (by rfl) ⟨1934654, by rfl⟩ : syracuseStep 2579539 = 3869309) B3869309
theorem B3439385 : Blo 2291435 3439385 := bstep (se 2 (by rfl) ⟨1289769, by rfl⟩ : syracuseStep 3439385 = 2579539) B2579539
theorem B2292923 : Blo 2291435 2292923 := bstep (se 1 (by rfl) ⟨1719692, by rfl⟩ : syracuseStep 2292923 = 3439385) B3439385
theorem B3533885 : Blo 2291435 3533885 := bbase (se 3 (by rfl) ⟨662603, by rfl⟩ : syracuseStep 3533885 = 1325207) (by norm_num)
theorem B2355923 : Blo 2291435 2355923 := bstep (se 1 (by rfl) ⟨1766942, by rfl⟩ : syracuseStep 2355923 = 3533885) B3533885
theorem B6282461 : Blo 2291435 6282461 := bstep (se 3 (by rfl) ⟨1177961, by rfl⟩ : syracuseStep 6282461 = 2355923) B2355923
theorem B4188307 : Blo 2291435 4188307 := bstep (se 1 (by rfl) ⟨3141230, by rfl⟩ : syracuseStep 4188307 = 6282461) B6282461
theorem B5584409 : Blo 2291435 5584409 := bstep (se 2 (by rfl) ⟨2094153, by rfl⟩ : syracuseStep 5584409 = 4188307) B4188307
theorem B3722939 : Blo 2291435 3722939 := bstep (se 1 (by rfl) ⟨2792204, by rfl⟩ : syracuseStep 3722939 = 5584409) B5584409
theorem B2481959 : Blo 2291435 2481959 := bstep (se 1 (by rfl) ⟨1861469, by rfl⟩ : syracuseStep 2481959 = 3722939) B3722939
theorem B6618557 : Blo 2291435 6618557 := bstep (se 3 (by rfl) ⟨1240979, by rfl⟩ : syracuseStep 6618557 = 2481959) B2481959
theorem B17649485 : Blo 2291435 17649485 := bstep (se 3 (by rfl) ⟨3309278, by rfl⟩ : syracuseStep 17649485 = 6618557) B6618557
theorem B11766323 : Blo 2291435 11766323 := bstep (se 1 (by rfl) ⟨8824742, by rfl⟩ : syracuseStep 11766323 = 17649485) B17649485
theorem B7844215 : Blo 2291435 7844215 := bstep (se 1 (by rfl) ⟨5883161, by rfl⟩ : syracuseStep 7844215 = 11766323) B11766323
theorem B10458953 : Blo 2291435 10458953 := bstep (se 2 (by rfl) ⟨3922107, by rfl⟩ : syracuseStep 10458953 = 7844215) B7844215
theorem B6972635 : Blo 2291435 6972635 := bstep (se 1 (by rfl) ⟨5229476, by rfl⟩ : syracuseStep 6972635 = 10458953) B10458953
theorem B4648423 : Blo 2291435 4648423 := bstep (se 1 (by rfl) ⟨3486317, by rfl⟩ : syracuseStep 4648423 = 6972635) B6972635
theorem B6197897 : Blo 2291435 6197897 := bstep (se 2 (by rfl) ⟨2324211, by rfl⟩ : syracuseStep 6197897 = 4648423) B4648423
theorem B16527725 : Blo 2291435 16527725 := bstep (se 3 (by rfl) ⟨3098948, by rfl⟩ : syracuseStep 16527725 = 6197897) B6197897
theorem B11018483 : Blo 2291435 11018483 := bstep (se 1 (by rfl) ⟨8263862, by rfl⟩ : syracuseStep 11018483 = 16527725) B16527725
theorem B7345655 : Blo 2291435 7345655 := bstep (se 1 (by rfl) ⟨5509241, by rfl⟩ : syracuseStep 7345655 = 11018483) B11018483
theorem B4897103 : Blo 2291435 4897103 := bstep (se 1 (by rfl) ⟨3672827, by rfl⟩ : syracuseStep 4897103 = 7345655) B7345655
theorem B13058941 : Blo 2291435 13058941 := bstep (se 3 (by rfl) ⟨2448551, by rfl⟩ : syracuseStep 13058941 = 4897103) B4897103
theorem B17411921 : Blo 2291435 17411921 := bstep (se 2 (by rfl) ⟨6529470, by rfl⟩ : syracuseStep 17411921 = 13058941) B13058941
theorem B11607947 : Blo 2291435 11607947 := bstep (se 1 (by rfl) ⟨8705960, by rfl⟩ : syracuseStep 11607947 = 17411921) B17411921
theorem B7738631 : Blo 2291435 7738631 := bstep (se 1 (by rfl) ⟨5803973, by rfl⟩ : syracuseStep 7738631 = 11607947) B11607947
theorem B5159087 : Blo 2291435 5159087 := bstep (se 1 (by rfl) ⟨3869315, by rfl⟩ : syracuseStep 5159087 = 7738631) B7738631
theorem B3439391 : Blo 2291435 3439391 := bstep (se 1 (by rfl) ⟨2579543, by rfl⟩ : syracuseStep 3439391 = 5159087) B5159087
theorem B2292927 : Blo 2291435 2292927 := bstep (se 1 (by rfl) ⟨1719695, by rfl⟩ : syracuseStep 2292927 = 3439391) B3439391
theorem B3439397 : Blo 2291435 3439397 := bbase (se 4 (by rfl) ⟨322443, by rfl⟩ : syracuseStep 3439397 = 644887) (by norm_num)
theorem B2292931 : Blo 2291435 2292931 := bstep (se 1 (by rfl) ⟨1719698, by rfl⟩ : syracuseStep 2292931 = 3439397) B3439397
theorem B2901997 : Blo 2291435 2901997 := bbase (se 3 (by rfl) ⟨544124, by rfl⟩ : syracuseStep 2901997 = 1088249) (by norm_num)
theorem B3869329 : Blo 2291435 3869329 := bstep (se 2 (by rfl) ⟨1450998, by rfl⟩ : syracuseStep 3869329 = 2901997) B2901997
theorem B5159105 : Blo 2291435 5159105 := bstep (se 2 (by rfl) ⟨1934664, by rfl⟩ : syracuseStep 5159105 = 3869329) B3869329
theorem B3439403 : Blo 2291435 3439403 := bstep (se 1 (by rfl) ⟨2579552, by rfl⟩ : syracuseStep 3439403 = 5159105) B5159105
theorem B2292935 : Blo 2291435 2292935 := bstep (se 1 (by rfl) ⟨1719701, by rfl⟩ : syracuseStep 2292935 = 3439403) B3439403
theorem B2579557 : Blo 2291435 2579557 := bbase (se 4 (by rfl) ⟨241833, by rfl⟩ : syracuseStep 2579557 = 483667) (by norm_num)
theorem B3439409 : Blo 2291435 3439409 := bstep (se 2 (by rfl) ⟨1289778, by rfl⟩ : syracuseStep 3439409 = 2579557) B2579557
theorem B2292939 : Blo 2291435 2292939 := bstep (se 1 (by rfl) ⟨1719704, by rfl⟩ : syracuseStep 2292939 = 3439409) B3439409
theorem B2448569 : Blo 2291435 2448569 := bbase (se 2 (by rfl) ⟨918213, by rfl⟩ : syracuseStep 2448569 = 1836427) (by norm_num)
theorem B6529517 : Blo 2291435 6529517 := bstep (se 3 (by rfl) ⟨1224284, by rfl⟩ : syracuseStep 6529517 = 2448569) B2448569
theorem B4353011 : Blo 2291435 4353011 := bstep (se 1 (by rfl) ⟨3264758, by rfl⟩ : syracuseStep 4353011 = 6529517) B6529517
theorem B2902007 : Blo 2291435 2902007 := bstep (se 1 (by rfl) ⟨2176505, by rfl⟩ : syracuseStep 2902007 = 4353011) B4353011
theorem B7738685 : Blo 2291435 7738685 := bstep (se 3 (by rfl) ⟨1451003, by rfl⟩ : syracuseStep 7738685 = 2902007) B2902007
theorem B5159123 : Blo 2291435 5159123 := bstep (se 1 (by rfl) ⟨3869342, by rfl⟩ : syracuseStep 5159123 = 7738685) B7738685
theorem B3439415 : Blo 2291435 3439415 := bstep (se 1 (by rfl) ⟨2579561, by rfl⟩ : syracuseStep 3439415 = 5159123) B5159123
theorem B2292943 : Blo 2291435 2292943 := bstep (se 1 (by rfl) ⟨1719707, by rfl⟩ : syracuseStep 2292943 = 3439415) B3439415
theorem B3439421 : Blo 2291435 3439421 := bbase (se 3 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 3439421 = 1289783) (by norm_num)
theorem B2292947 : Blo 2291435 2292947 := bstep (se 1 (by rfl) ⟨1719710, by rfl⟩ : syracuseStep 2292947 = 3439421) B3439421
theorem B5159141 : Blo 2291435 5159141 := bbase (se 4 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 5159141 = 967339) (by norm_num)
theorem B3439427 : Blo 2291435 3439427 := bstep (se 1 (by rfl) ⟨2579570, by rfl⟩ : syracuseStep 3439427 = 5159141) B5159141
theorem B2292951 : Blo 2291435 2292951 := bstep (se 1 (by rfl) ⟨1719713, by rfl⟩ : syracuseStep 2292951 = 3439427) B3439427
theorem B5804045 : Blo 2291435 5804045 := bbase (se 3 (by rfl) ⟨1088258, by rfl⟩ : syracuseStep 5804045 = 2176517) (by norm_num)
theorem B3869363 : Blo 2291435 3869363 := bstep (se 1 (by rfl) ⟨2902022, by rfl⟩ : syracuseStep 3869363 = 5804045) B5804045
theorem B2579575 : Blo 2291435 2579575 := bstep (se 1 (by rfl) ⟨1934681, by rfl⟩ : syracuseStep 2579575 = 3869363) B3869363
theorem B3439433 : Blo 2291435 3439433 := bstep (se 2 (by rfl) ⟨1289787, by rfl⟩ : syracuseStep 3439433 = 2579575) B2579575
theorem B2292955 : Blo 2291435 2292955 := bstep (se 1 (by rfl) ⟨1719716, by rfl⟩ : syracuseStep 2292955 = 3439433) B3439433
theorem B3264781 : Blo 2291435 3264781 := bbase (se 3 (by rfl) ⟨612146, by rfl⟩ : syracuseStep 3264781 = 1224293) (by norm_num)
theorem B4353041 : Blo 2291435 4353041 := bstep (se 2 (by rfl) ⟨1632390, by rfl⟩ : syracuseStep 4353041 = 3264781) B3264781
theorem B11608109 : Blo 2291435 11608109 := bstep (se 3 (by rfl) ⟨2176520, by rfl⟩ : syracuseStep 11608109 = 4353041) B4353041
theorem B7738739 : Blo 2291435 7738739 := bstep (se 1 (by rfl) ⟨5804054, by rfl⟩ : syracuseStep 7738739 = 11608109) B11608109
theorem B5159159 : Blo 2291435 5159159 := bstep (se 1 (by rfl) ⟨3869369, by rfl⟩ : syracuseStep 5159159 = 7738739) B7738739
theorem B3439439 : Blo 2291435 3439439 := bstep (se 1 (by rfl) ⟨2579579, by rfl⟩ : syracuseStep 3439439 = 5159159) B5159159
theorem B2292959 : Blo 2291435 2292959 := bstep (se 1 (by rfl) ⟨1719719, by rfl⟩ : syracuseStep 2292959 = 3439439) B3439439
theorem B3439445 : Blo 2291435 3439445 := bbase (se 9 (by rfl) ⟨10076, by rfl⟩ : syracuseStep 3439445 = 20153) (by norm_num)
theorem B2292963 : Blo 2291435 2292963 := bstep (se 1 (by rfl) ⟨1719722, by rfl⟩ : syracuseStep 2292963 = 3439445) B3439445
theorem B4897189 : Blo 2291435 4897189 := bbase (se 4 (by rfl) ⟨459111, by rfl⟩ : syracuseStep 4897189 = 918223) (by norm_num)
theorem B6529585 : Blo 2291435 6529585 := bstep (se 2 (by rfl) ⟨2448594, by rfl⟩ : syracuseStep 6529585 = 4897189) B4897189
theorem B8706113 : Blo 2291435 8706113 := bstep (se 2 (by rfl) ⟨3264792, by rfl⟩ : syracuseStep 8706113 = 6529585) B6529585
theorem B5804075 : Blo 2291435 5804075 := bstep (se 1 (by rfl) ⟨4353056, by rfl⟩ : syracuseStep 5804075 = 8706113) B8706113
theorem B3869383 : Blo 2291435 3869383 := bstep (se 1 (by rfl) ⟨2902037, by rfl⟩ : syracuseStep 3869383 = 5804075) B5804075
theorem B5159177 : Blo 2291435 5159177 := bstep (se 2 (by rfl) ⟨1934691, by rfl⟩ : syracuseStep 5159177 = 3869383) B3869383
theorem B3439451 : Blo 2291435 3439451 := bstep (se 1 (by rfl) ⟨2579588, by rfl⟩ : syracuseStep 3439451 = 5159177) B5159177
theorem B2292967 : Blo 2291435 2292967 := bstep (se 1 (by rfl) ⟨1719725, by rfl⟩ : syracuseStep 2292967 = 3439451) B3439451
theorem B2579593 : Blo 2291435 2579593 := bbase (se 2 (by rfl) ⟨967347, by rfl⟩ : syracuseStep 2579593 = 1934695) (by norm_num)
theorem B3439457 : Blo 2291435 3439457 := bstep (se 2 (by rfl) ⟨1289796, by rfl⟩ : syracuseStep 3439457 = 2579593) B2579593
theorem B2292971 : Blo 2291435 2292971 := bstep (se 1 (by rfl) ⟨1719728, by rfl⟩ : syracuseStep 2292971 = 3439457) B3439457
theorem B12396053 : Blo 2291435 12396053 := bbase (se 6 (by rfl) ⟨290532, by rfl⟩ : syracuseStep 12396053 = 581065) (by norm_num)
theorem B8264035 : Blo 2291435 8264035 := bstep (se 1 (by rfl) ⟨6198026, by rfl⟩ : syracuseStep 8264035 = 12396053) B12396053
theorem B44074853 : Blo 2291435 44074853 := bstep (se 4 (by rfl) ⟨4132017, by rfl⟩ : syracuseStep 44074853 = 8264035) B8264035
theorem B29383235 : Blo 2291435 29383235 := bstep (se 1 (by rfl) ⟨22037426, by rfl⟩ : syracuseStep 29383235 = 44074853) B44074853
theorem B19588823 : Blo 2291435 19588823 := bstep (se 1 (by rfl) ⟨14691617, by rfl⟩ : syracuseStep 19588823 = 29383235) B29383235
theorem B13059215 : Blo 2291435 13059215 := bstep (se 1 (by rfl) ⟨9794411, by rfl⟩ : syracuseStep 13059215 = 19588823) B19588823
theorem B8706143 : Blo 2291435 8706143 := bstep (se 1 (by rfl) ⟨6529607, by rfl⟩ : syracuseStep 8706143 = 13059215) B13059215
theorem B5804095 : Blo 2291435 5804095 := bstep (se 1 (by rfl) ⟨4353071, by rfl⟩ : syracuseStep 5804095 = 8706143) B8706143
theorem B7738793 : Blo 2291435 7738793 := bstep (se 2 (by rfl) ⟨2902047, by rfl⟩ : syracuseStep 7738793 = 5804095) B5804095
theorem B5159195 : Blo 2291435 5159195 := bstep (se 1 (by rfl) ⟨3869396, by rfl⟩ : syracuseStep 5159195 = 7738793) B7738793
theorem B3439463 : Blo 2291435 3439463 := bstep (se 1 (by rfl) ⟨2579597, by rfl⟩ : syracuseStep 3439463 = 5159195) B5159195
theorem B2292975 : Blo 2291435 2292975 := bstep (se 1 (by rfl) ⟨1719731, by rfl⟩ : syracuseStep 2292975 = 3439463) B3439463
theorem B3439469 : Blo 2291435 3439469 := bbase (se 3 (by rfl) ⟨644900, by rfl⟩ : syracuseStep 3439469 = 1289801) (by norm_num)
theorem B2292979 : Blo 2291435 2292979 := bstep (se 1 (by rfl) ⟨1719734, by rfl⟩ : syracuseStep 2292979 = 3439469) B3439469
theorem B5159213 : Blo 2291435 5159213 := bbase (se 3 (by rfl) ⟨967352, by rfl⟩ : syracuseStep 5159213 = 1934705) (by norm_num)
theorem B3439475 : Blo 2291435 3439475 := bstep (se 1 (by rfl) ⟨2579606, by rfl⟩ : syracuseStep 3439475 = 5159213) B5159213
theorem B2292983 : Blo 2291435 2292983 := bstep (se 1 (by rfl) ⟨1719737, by rfl⟩ : syracuseStep 2292983 = 3439475) B3439475
theorem B2324273 : Blo 2291435 2324273 := bbase (se 2 (by rfl) ⟨871602, by rfl⟩ : syracuseStep 2324273 = 1743205) (by norm_num)
theorem B6198061 : Blo 2291435 6198061 := bstep (se 3 (by rfl) ⟨1162136, by rfl⟩ : syracuseStep 6198061 = 2324273) B2324273
theorem B8264081 : Blo 2291435 8264081 := bstep (se 2 (by rfl) ⟨3099030, by rfl⟩ : syracuseStep 8264081 = 6198061) B6198061
theorem B5509387 : Blo 2291435 5509387 := bstep (se 1 (by rfl) ⟨4132040, by rfl⟩ : syracuseStep 5509387 = 8264081) B8264081
theorem B7345849 : Blo 2291435 7345849 := bstep (se 2 (by rfl) ⟨2754693, by rfl⟩ : syracuseStep 7345849 = 5509387) B5509387
theorem B9794465 : Blo 2291435 9794465 := bstep (se 2 (by rfl) ⟨3672924, by rfl⟩ : syracuseStep 9794465 = 7345849) B7345849
theorem B6529643 : Blo 2291435 6529643 := bstep (se 1 (by rfl) ⟨4897232, by rfl⟩ : syracuseStep 6529643 = 9794465) B9794465
theorem B4353095 : Blo 2291435 4353095 := bstep (se 1 (by rfl) ⟨3264821, by rfl⟩ : syracuseStep 4353095 = 6529643) B6529643
theorem B2902063 : Blo 2291435 2902063 := bstep (se 1 (by rfl) ⟨2176547, by rfl⟩ : syracuseStep 2902063 = 4353095) B4353095
theorem B3869417 : Blo 2291435 3869417 := bstep (se 2 (by rfl) ⟨1451031, by rfl⟩ : syracuseStep 3869417 = 2902063) B2902063
theorem B2579611 : Blo 2291435 2579611 := bstep (se 1 (by rfl) ⟨1934708, by rfl⟩ : syracuseStep 2579611 = 3869417) B3869417
theorem B3439481 : Blo 2291435 3439481 := bstep (se 2 (by rfl) ⟨1289805, by rfl⟩ : syracuseStep 3439481 = 2579611) B2579611
theorem B2292987 : Blo 2291435 2292987 := bstep (se 1 (by rfl) ⟨1719740, by rfl⟩ : syracuseStep 2292987 = 3439481) B3439481
theorem B24792277 : Blo 2291435 24792277 := bbase (se 7 (by rfl) ⟨290534, by rfl⟩ : syracuseStep 24792277 = 581069) (by norm_num)
theorem B33056369 : Blo 2291435 33056369 := bstep (se 2 (by rfl) ⟨12396138, by rfl⟩ : syracuseStep 33056369 = 24792277) B24792277
theorem B22037579 : Blo 2291435 22037579 := bstep (se 1 (by rfl) ⟨16528184, by rfl⟩ : syracuseStep 22037579 = 33056369) B33056369
theorem B14691719 : Blo 2291435 14691719 := bstep (se 1 (by rfl) ⟨11018789, by rfl⟩ : syracuseStep 14691719 = 22037579) B22037579
theorem B39177917 : Blo 2291435 39177917 := bstep (se 3 (by rfl) ⟨7345859, by rfl⟩ : syracuseStep 39177917 = 14691719) B14691719
theorem B26118611 : Blo 2291435 26118611 := bstep (se 1 (by rfl) ⟨19588958, by rfl⟩ : syracuseStep 26118611 = 39177917) B39177917
theorem B17412407 : Blo 2291435 17412407 := bstep (se 1 (by rfl) ⟨13059305, by rfl⟩ : syracuseStep 17412407 = 26118611) B26118611
theorem B11608271 : Blo 2291435 11608271 := bstep (se 1 (by rfl) ⟨8706203, by rfl⟩ : syracuseStep 11608271 = 17412407) B17412407
theorem B7738847 : Blo 2291435 7738847 := bstep (se 1 (by rfl) ⟨5804135, by rfl⟩ : syracuseStep 7738847 = 11608271) B11608271
theorem B5159231 : Blo 2291435 5159231 := bstep (se 1 (by rfl) ⟨3869423, by rfl⟩ : syracuseStep 5159231 = 7738847) B7738847
theorem B3439487 : Blo 2291435 3439487 := bstep (se 1 (by rfl) ⟨2579615, by rfl⟩ : syracuseStep 3439487 = 5159231) B5159231
theorem B2292991 : Blo 2291435 2292991 := bstep (se 1 (by rfl) ⟨1719743, by rfl⟩ : syracuseStep 2292991 = 3439487) B3439487
theorem B3439493 : Blo 2291435 3439493 := bbase (se 4 (by rfl) ⟨322452, by rfl⟩ : syracuseStep 3439493 = 644905) (by norm_num)
theorem B2292995 : Blo 2291435 2292995 := bstep (se 1 (by rfl) ⟨1719746, by rfl⟩ : syracuseStep 2292995 = 3439493) B3439493
theorem B3869437 : Blo 2291435 3869437 := bbase (se 3 (by rfl) ⟨725519, by rfl⟩ : syracuseStep 3869437 = 1451039) (by norm_num)
theorem B5159249 : Blo 2291435 5159249 := bstep (se 2 (by rfl) ⟨1934718, by rfl⟩ : syracuseStep 5159249 = 3869437) B3869437
theorem B3439499 : Blo 2291435 3439499 := bstep (se 1 (by rfl) ⟨2579624, by rfl⟩ : syracuseStep 3439499 = 5159249) B5159249
theorem B2292999 : Blo 2291435 2292999 := bstep (se 1 (by rfl) ⟨1719749, by rfl⟩ : syracuseStep 2292999 = 3439499) B3439499
theorem B2579629 : Blo 2291435 2579629 := bbase (se 3 (by rfl) ⟨483680, by rfl⟩ : syracuseStep 2579629 = 967361) (by norm_num)
theorem B3439505 : Blo 2291435 3439505 := bstep (se 2 (by rfl) ⟨1289814, by rfl⟩ : syracuseStep 3439505 = 2579629) B2579629
theorem B2293003 : Blo 2291435 2293003 := bstep (se 1 (by rfl) ⟨1719752, by rfl⟩ : syracuseStep 2293003 = 3439505) B3439505
theorem B7738901 : Blo 2291435 7738901 := bbase (se 6 (by rfl) ⟨181380, by rfl⟩ : syracuseStep 7738901 = 362761) (by norm_num)
theorem B5159267 : Blo 2291435 5159267 := bstep (se 1 (by rfl) ⟨3869450, by rfl⟩ : syracuseStep 5159267 = 7738901) B7738901
theorem B3439511 : Blo 2291435 3439511 := bstep (se 1 (by rfl) ⟨2579633, by rfl⟩ : syracuseStep 3439511 = 5159267) B5159267
theorem B2293007 : Blo 2291435 2293007 := bstep (se 1 (by rfl) ⟨1719755, by rfl⟩ : syracuseStep 2293007 = 3439511) B3439511
theorem B3439517 : Blo 2291435 3439517 := bbase (se 3 (by rfl) ⟨644909, by rfl⟩ : syracuseStep 3439517 = 1289819) (by norm_num)
theorem B2293011 : Blo 2291435 2293011 := bstep (se 1 (by rfl) ⟨1719758, by rfl⟩ : syracuseStep 2293011 = 3439517) B3439517
theorem B5159285 : Blo 2291435 5159285 := bbase (se 5 (by rfl) ⟨241841, by rfl⟩ : syracuseStep 5159285 = 483683) (by norm_num)
theorem B3439523 : Blo 2291435 3439523 := bstep (se 1 (by rfl) ⟨2579642, by rfl⟩ : syracuseStep 3439523 = 5159285) B5159285
theorem B2293015 : Blo 2291435 2293015 := bstep (se 1 (by rfl) ⟨1719761, by rfl⟩ : syracuseStep 2293015 = 3439523) B3439523
theorem B2324305 : Blo 2291435 2324305 := bbase (se 2 (by rfl) ⟨871614, by rfl⟩ : syracuseStep 2324305 = 1743229) (by norm_num)
theorem B12396293 : Blo 2291435 12396293 := bstep (se 4 (by rfl) ⟨1162152, by rfl⟩ : syracuseStep 12396293 = 2324305) B2324305
theorem B8264195 : Blo 2291435 8264195 := bstep (se 1 (by rfl) ⟨6198146, by rfl⟩ : syracuseStep 8264195 = 12396293) B12396293
theorem B5509463 : Blo 2291435 5509463 := bstep (se 1 (by rfl) ⟨4132097, by rfl⟩ : syracuseStep 5509463 = 8264195) B8264195
theorem B14691901 : Blo 2291435 14691901 := bstep (se 3 (by rfl) ⟨2754731, by rfl⟩ : syracuseStep 14691901 = 5509463) B5509463
theorem B19589201 : Blo 2291435 19589201 := bstep (se 2 (by rfl) ⟨7345950, by rfl⟩ : syracuseStep 19589201 = 14691901) B14691901
theorem B13059467 : Blo 2291435 13059467 := bstep (se 1 (by rfl) ⟨9794600, by rfl⟩ : syracuseStep 13059467 = 19589201) B19589201
theorem B8706311 : Blo 2291435 8706311 := bstep (se 1 (by rfl) ⟨6529733, by rfl⟩ : syracuseStep 8706311 = 13059467) B13059467
theorem B5804207 : Blo 2291435 5804207 := bstep (se 1 (by rfl) ⟨4353155, by rfl⟩ : syracuseStep 5804207 = 8706311) B8706311
theorem B3869471 : Blo 2291435 3869471 := bstep (se 1 (by rfl) ⟨2902103, by rfl⟩ : syracuseStep 3869471 = 5804207) B5804207
theorem B2579647 : Blo 2291435 2579647 := bstep (se 1 (by rfl) ⟨1934735, by rfl⟩ : syracuseStep 2579647 = 3869471) B3869471
theorem B3439529 : Blo 2291435 3439529 := bstep (se 2 (by rfl) ⟨1289823, by rfl⟩ : syracuseStep 3439529 = 2579647) B2579647
theorem B2293019 : Blo 2291435 2293019 := bstep (se 1 (by rfl) ⟨1719764, by rfl⟩ : syracuseStep 2293019 = 3439529) B3439529
theorem B8706325 : Blo 2291435 8706325 := bbase (se 6 (by rfl) ⟨204054, by rfl⟩ : syracuseStep 8706325 = 408109) (by norm_num)
theorem B11608433 : Blo 2291435 11608433 := bstep (se 2 (by rfl) ⟨4353162, by rfl⟩ : syracuseStep 11608433 = 8706325) B8706325
theorem B7738955 : Blo 2291435 7738955 := bstep (se 1 (by rfl) ⟨5804216, by rfl⟩ : syracuseStep 7738955 = 11608433) B11608433
theorem B5159303 : Blo 2291435 5159303 := bstep (se 1 (by rfl) ⟨3869477, by rfl⟩ : syracuseStep 5159303 = 7738955) B7738955
theorem B3439535 : Blo 2291435 3439535 := bstep (se 1 (by rfl) ⟨2579651, by rfl⟩ : syracuseStep 3439535 = 5159303) B5159303
theorem B2293023 : Blo 2291435 2293023 := bstep (se 1 (by rfl) ⟨1719767, by rfl⟩ : syracuseStep 2293023 = 3439535) B3439535
theorem B3439541 : Blo 2291435 3439541 := bbase (se 5 (by rfl) ⟨161228, by rfl⟩ : syracuseStep 3439541 = 322457) (by norm_num)
theorem B2293027 : Blo 2291435 2293027 := bstep (se 1 (by rfl) ⟨1719770, by rfl⟩ : syracuseStep 2293027 = 3439541) B3439541
theorem B5804237 : Blo 2291435 5804237 := bbase (se 3 (by rfl) ⟨1088294, by rfl⟩ : syracuseStep 5804237 = 2176589) (by norm_num)
theorem B3869491 : Blo 2291435 3869491 := bstep (se 1 (by rfl) ⟨2902118, by rfl⟩ : syracuseStep 3869491 = 5804237) B5804237
theorem B5159321 : Blo 2291435 5159321 := bstep (se 2 (by rfl) ⟨1934745, by rfl⟩ : syracuseStep 5159321 = 3869491) B3869491
theorem B3439547 : Blo 2291435 3439547 := bstep (se 1 (by rfl) ⟨2579660, by rfl⟩ : syracuseStep 3439547 = 5159321) B5159321
theorem B2293031 : Blo 2291435 2293031 := bstep (se 1 (by rfl) ⟨1719773, by rfl⟩ : syracuseStep 2293031 = 3439547) B3439547
theorem B2579665 : Blo 2291435 2579665 := bbase (se 2 (by rfl) ⟨967374, by rfl⟩ : syracuseStep 2579665 = 1934749) (by norm_num)
theorem B3439553 : Blo 2291435 3439553 := bstep (se 2 (by rfl) ⟨1289832, by rfl⟩ : syracuseStep 3439553 = 2579665) B2579665
theorem B2293035 : Blo 2291435 2293035 := bstep (se 1 (by rfl) ⟨1719776, by rfl⟩ : syracuseStep 2293035 = 3439553) B3439553
theorem B37189205 : Blo 2291435 37189205 := bbase (se 8 (by rfl) ⟨217905, by rfl⟩ : syracuseStep 37189205 = 435811) (by norm_num)
theorem B24792803 : Blo 2291435 24792803 := bstep (se 1 (by rfl) ⟨18594602, by rfl⟩ : syracuseStep 24792803 = 37189205) B37189205
theorem B16528535 : Blo 2291435 16528535 := bstep (se 1 (by rfl) ⟨12396401, by rfl⟩ : syracuseStep 16528535 = 24792803) B24792803
theorem B11019023 : Blo 2291435 11019023 := bstep (se 1 (by rfl) ⟨8264267, by rfl⟩ : syracuseStep 11019023 = 16528535) B16528535
theorem B7346015 : Blo 2291435 7346015 := bstep (se 1 (by rfl) ⟨5509511, by rfl⟩ : syracuseStep 7346015 = 11019023) B11019023
theorem B4897343 : Blo 2291435 4897343 := bstep (se 1 (by rfl) ⟨3673007, by rfl⟩ : syracuseStep 4897343 = 7346015) B7346015
theorem B3264895 : Blo 2291435 3264895 := bstep (se 1 (by rfl) ⟨2448671, by rfl⟩ : syracuseStep 3264895 = 4897343) B4897343
theorem B4353193 : Blo 2291435 4353193 := bstep (se 2 (by rfl) ⟨1632447, by rfl⟩ : syracuseStep 4353193 = 3264895) B3264895
theorem B5804257 : Blo 2291435 5804257 := bstep (se 2 (by rfl) ⟨2176596, by rfl⟩ : syracuseStep 5804257 = 4353193) B4353193
theorem B7739009 : Blo 2291435 7739009 := bstep (se 2 (by rfl) ⟨2902128, by rfl⟩ : syracuseStep 7739009 = 5804257) B5804257
theorem B5159339 : Blo 2291435 5159339 := bstep (se 1 (by rfl) ⟨3869504, by rfl⟩ : syracuseStep 5159339 = 7739009) B7739009
theorem B3439559 : Blo 2291435 3439559 := bstep (se 1 (by rfl) ⟨2579669, by rfl⟩ : syracuseStep 3439559 = 5159339) B5159339
theorem B2293039 : Blo 2291435 2293039 := bstep (se 1 (by rfl) ⟨1719779, by rfl⟩ : syracuseStep 2293039 = 3439559) B3439559
theorem B3439565 : Blo 2291435 3439565 := bbase (se 3 (by rfl) ⟨644918, by rfl⟩ : syracuseStep 3439565 = 1289837) (by norm_num)
theorem B2293043 : Blo 2291435 2293043 := bstep (se 1 (by rfl) ⟨1719782, by rfl⟩ : syracuseStep 2293043 = 3439565) B3439565
theorem B5159357 : Blo 2291435 5159357 := bbase (se 3 (by rfl) ⟨967379, by rfl⟩ : syracuseStep 5159357 = 1934759) (by norm_num)
theorem B3439571 : Blo 2291435 3439571 := bstep (se 1 (by rfl) ⟨2579678, by rfl⟩ : syracuseStep 3439571 = 5159357) B5159357
theorem B2293047 : Blo 2291435 2293047 := bstep (se 1 (by rfl) ⟨1719785, by rfl⟩ : syracuseStep 2293047 = 3439571) B3439571
theorem B3869525 : Blo 2291435 3869525 := bbase (se 9 (by rfl) ⟨11336, by rfl⟩ : syracuseStep 3869525 = 22673) (by norm_num)
theorem B2579683 : Blo 2291435 2579683 := bstep (se 1 (by rfl) ⟨1934762, by rfl⟩ : syracuseStep 2579683 = 3869525) B3869525
theorem B3439577 : Blo 2291435 3439577 := bstep (se 2 (by rfl) ⟨1289841, by rfl⟩ : syracuseStep 3439577 = 2579683) B2579683
theorem B2293051 : Blo 2291435 2293051 := bstep (se 1 (by rfl) ⟨1719788, by rfl⟩ : syracuseStep 2293051 = 3439577) B3439577
theorem B5509549 : Blo 2291435 5509549 := bbase (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) (by norm_num)
theorem B7346065 : Blo 2291435 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B9794753 : Blo 2291435 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B6529835 : Blo 2291435 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B17412893 : Blo 2291435 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B11608595 : Blo 2291435 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B7739063 : Blo 2291435 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B5159375 : Blo 2291435 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B3439583 : Blo 2291435 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B2293055 : Blo 2291435 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B3439589 : Blo 2291435 3439589 := bbase (se 4 (by rfl) ⟨322461, by rfl⟩ : syracuseStep 3439589 = 644923) (by norm_num)
theorem B2293059 : Blo 2291435 2293059 := bstep (se 1 (by rfl) ⟨1719794, by rfl⟩ : syracuseStep 2293059 = 3439589) B3439589
theorem B9794789 : Blo 2291435 9794789 := bbase (se 4 (by rfl) ⟨918261, by rfl⟩ : syracuseStep 9794789 = 1836523) (by norm_num)
theorem B6529859 : Blo 2291435 6529859 := bstep (se 1 (by rfl) ⟨4897394, by rfl⟩ : syracuseStep 6529859 = 9794789) B9794789
theorem B4353239 : Blo 2291435 4353239 := bstep (se 1 (by rfl) ⟨3264929, by rfl⟩ : syracuseStep 4353239 = 6529859) B6529859
theorem B2902159 : Blo 2291435 2902159 := bstep (se 1 (by rfl) ⟨2176619, by rfl⟩ : syracuseStep 2902159 = 4353239) B4353239
theorem B3869545 : Blo 2291435 3869545 := bstep (se 2 (by rfl) ⟨1451079, by rfl⟩ : syracuseStep 3869545 = 2902159) B2902159
theorem B5159393 : Blo 2291435 5159393 := bstep (se 2 (by rfl) ⟨1934772, by rfl⟩ : syracuseStep 5159393 = 3869545) B3869545
theorem B3439595 : Blo 2291435 3439595 := bstep (se 1 (by rfl) ⟨2579696, by rfl⟩ : syracuseStep 3439595 = 5159393) B5159393
theorem B2293063 : Blo 2291435 2293063 := bstep (se 1 (by rfl) ⟨1719797, by rfl⟩ : syracuseStep 2293063 = 3439595) B3439595
theorem B2579701 : Blo 2291435 2579701 := bbase (se 5 (by rfl) ⟨120923, by rfl⟩ : syracuseStep 2579701 = 241847) (by norm_num)
theorem B3439601 : Blo 2291435 3439601 := bstep (se 2 (by rfl) ⟨1289850, by rfl⟩ : syracuseStep 3439601 = 2579701) B2579701
theorem B2293067 : Blo 2291435 2293067 := bstep (se 1 (by rfl) ⟨1719800, by rfl⟩ : syracuseStep 2293067 = 3439601) B3439601
theorem B2902169 : Blo 2291435 2902169 := bbase (se 2 (by rfl) ⟨1088313, by rfl⟩ : syracuseStep 2902169 = 2176627) (by norm_num)
theorem B7739117 : Blo 2291435 7739117 := bstep (se 3 (by rfl) ⟨1451084, by rfl⟩ : syracuseStep 7739117 = 2902169) B2902169
theorem B5159411 : Blo 2291435 5159411 := bstep (se 1 (by rfl) ⟨3869558, by rfl⟩ : syracuseStep 5159411 = 7739117) B7739117
theorem B3439607 : Blo 2291435 3439607 := bstep (se 1 (by rfl) ⟨2579705, by rfl⟩ : syracuseStep 3439607 = 5159411) B5159411
theorem B2293071 : Blo 2291435 2293071 := bstep (se 1 (by rfl) ⟨1719803, by rfl⟩ : syracuseStep 2293071 = 3439607) B3439607
theorem B3439613 : Blo 2291435 3439613 := bbase (se 3 (by rfl) ⟨644927, by rfl⟩ : syracuseStep 3439613 = 1289855) (by norm_num)
theorem B2293075 : Blo 2291435 2293075 := bstep (se 1 (by rfl) ⟨1719806, by rfl⟩ : syracuseStep 2293075 = 3439613) B3439613
theorem B5159429 : Blo 2291435 5159429 := bbase (se 4 (by rfl) ⟨483696, by rfl⟩ : syracuseStep 5159429 = 967393) (by norm_num)
theorem B3439619 : Blo 2291435 3439619 := bstep (se 1 (by rfl) ⟨2579714, by rfl⟩ : syracuseStep 3439619 = 5159429) B5159429
theorem B2293079 : Blo 2291435 2293079 := bstep (se 1 (by rfl) ⟨1719809, by rfl⟩ : syracuseStep 2293079 = 3439619) B3439619
theorem B4353277 : Blo 2291435 4353277 := bbase (se 3 (by rfl) ⟨816239, by rfl⟩ : syracuseStep 4353277 = 1632479) (by norm_num)
theorem B5804369 : Blo 2291435 5804369 := bstep (se 2 (by rfl) ⟨2176638, by rfl⟩ : syracuseStep 5804369 = 4353277) B4353277
theorem B3869579 : Blo 2291435 3869579 := bstep (se 1 (by rfl) ⟨2902184, by rfl⟩ : syracuseStep 3869579 = 5804369) B5804369
theorem B2579719 : Blo 2291435 2579719 := bstep (se 1 (by rfl) ⟨1934789, by rfl⟩ : syracuseStep 2579719 = 3869579) B3869579
theorem B3439625 : Blo 2291435 3439625 := bstep (se 2 (by rfl) ⟨1289859, by rfl⟩ : syracuseStep 3439625 = 2579719) B2579719
theorem B2293083 : Blo 2291435 2293083 := bstep (se 1 (by rfl) ⟨1719812, by rfl⟩ : syracuseStep 2293083 = 3439625) B3439625
theorem B11608757 : Blo 2291435 11608757 := bbase (se 5 (by rfl) ⟨544160, by rfl⟩ : syracuseStep 11608757 = 1088321) (by norm_num)
theorem B7739171 : Blo 2291435 7739171 := bstep (se 1 (by rfl) ⟨5804378, by rfl⟩ : syracuseStep 7739171 = 11608757) B11608757
theorem B5159447 : Blo 2291435 5159447 := bstep (se 1 (by rfl) ⟨3869585, by rfl⟩ : syracuseStep 5159447 = 7739171) B7739171
theorem B3439631 : Blo 2291435 3439631 := bstep (se 1 (by rfl) ⟨2579723, by rfl⟩ : syracuseStep 3439631 = 5159447) B5159447
theorem B2293087 : Blo 2291435 2293087 := bstep (se 1 (by rfl) ⟨1719815, by rfl⟩ : syracuseStep 2293087 = 3439631) B3439631
theorem B3439637 : Blo 2291435 3439637 := bbase (se 6 (by rfl) ⟨80616, by rfl⟩ : syracuseStep 3439637 = 161233) (by norm_num)
theorem B2293091 : Blo 2291435 2293091 := bstep (se 1 (by rfl) ⟨1719818, by rfl⟩ : syracuseStep 2293091 = 3439637) B3439637
theorem B22038581 : Blo 2291435 22038581 := bbase (se 5 (by rfl) ⟨1033058, by rfl⟩ : syracuseStep 22038581 = 2066117) (by norm_num)
theorem B14692387 : Blo 2291435 14692387 := bstep (se 1 (by rfl) ⟨11019290, by rfl⟩ : syracuseStep 14692387 = 22038581) B22038581
theorem B19589849 : Blo 2291435 19589849 := bstep (se 2 (by rfl) ⟨7346193, by rfl⟩ : syracuseStep 19589849 = 14692387) B14692387
theorem B13059899 : Blo 2291435 13059899 := bstep (se 1 (by rfl) ⟨9794924, by rfl⟩ : syracuseStep 13059899 = 19589849) B19589849
theorem B8706599 : Blo 2291435 8706599 := bstep (se 1 (by rfl) ⟨6529949, by rfl⟩ : syracuseStep 8706599 = 13059899) B13059899
theorem B5804399 : Blo 2291435 5804399 := bstep (se 1 (by rfl) ⟨4353299, by rfl⟩ : syracuseStep 5804399 = 8706599) B8706599
theorem B3869599 : Blo 2291435 3869599 := bstep (se 1 (by rfl) ⟨2902199, by rfl⟩ : syracuseStep 3869599 = 5804399) B5804399
theorem B5159465 : Blo 2291435 5159465 := bstep (se 2 (by rfl) ⟨1934799, by rfl⟩ : syracuseStep 5159465 = 3869599) B3869599
theorem B3439643 : Blo 2291435 3439643 := bstep (se 1 (by rfl) ⟨2579732, by rfl⟩ : syracuseStep 3439643 = 5159465) B5159465
theorem B2293095 : Blo 2291435 2293095 := bstep (se 1 (by rfl) ⟨1719821, by rfl⟩ : syracuseStep 2293095 = 3439643) B3439643
theorem B2579737 : Blo 2291435 2579737 := bbase (se 2 (by rfl) ⟨967401, by rfl⟩ : syracuseStep 2579737 = 1934803) (by norm_num)
theorem B3439649 : Blo 2291435 3439649 := bstep (se 2 (by rfl) ⟨1289868, by rfl⟩ : syracuseStep 3439649 = 2579737) B2579737
theorem B2293099 : Blo 2291435 2293099 := bstep (se 1 (by rfl) ⟨1719824, by rfl⟩ : syracuseStep 2293099 = 3439649) B3439649
theorem B8706629 : Blo 2291435 8706629 := bbase (se 4 (by rfl) ⟨816246, by rfl⟩ : syracuseStep 8706629 = 1632493) (by norm_num)
theorem B5804419 : Blo 2291435 5804419 := bstep (se 1 (by rfl) ⟨4353314, by rfl⟩ : syracuseStep 5804419 = 8706629) B8706629
theorem B7739225 : Blo 2291435 7739225 := bstep (se 2 (by rfl) ⟨2902209, by rfl⟩ : syracuseStep 7739225 = 5804419) B5804419
theorem B5159483 : Blo 2291435 5159483 := bstep (se 1 (by rfl) ⟨3869612, by rfl⟩ : syracuseStep 5159483 = 7739225) B7739225
theorem B3439655 : Blo 2291435 3439655 := bstep (se 1 (by rfl) ⟨2579741, by rfl⟩ : syracuseStep 3439655 = 5159483) B5159483
theorem B2293103 : Blo 2291435 2293103 := bstep (se 1 (by rfl) ⟨1719827, by rfl⟩ : syracuseStep 2293103 = 3439655) B3439655
theorem B3439661 : Blo 2291435 3439661 := bbase (se 3 (by rfl) ⟨644936, by rfl⟩ : syracuseStep 3439661 = 1289873) (by norm_num)
theorem B2293107 : Blo 2291435 2293107 := bstep (se 1 (by rfl) ⟨1719830, by rfl⟩ : syracuseStep 2293107 = 3439661) B3439661
theorem B5159501 : Blo 2291435 5159501 := bbase (se 3 (by rfl) ⟨967406, by rfl⟩ : syracuseStep 5159501 = 1934813) (by norm_num)
theorem B3439667 : Blo 2291435 3439667 := bstep (se 1 (by rfl) ⟨2579750, by rfl⟩ : syracuseStep 3439667 = 5159501) B5159501
theorem B2293111 : Blo 2291435 2293111 := bstep (se 1 (by rfl) ⟨1719833, by rfl⟩ : syracuseStep 2293111 = 3439667) B3439667
theorem B2902225 : Blo 2291435 2902225 := bbase (se 2 (by rfl) ⟨1088334, by rfl⟩ : syracuseStep 2902225 = 2176669) (by norm_num)
theorem B3869633 : Blo 2291435 3869633 := bstep (se 2 (by rfl) ⟨1451112, by rfl⟩ : syracuseStep 3869633 = 2902225) B2902225
theorem B2579755 : Blo 2291435 2579755 := bstep (se 1 (by rfl) ⟨1934816, by rfl⟩ : syracuseStep 2579755 = 3869633) B3869633
theorem B3439673 : Blo 2291435 3439673 := bstep (se 2 (by rfl) ⟨1289877, by rfl⟩ : syracuseStep 3439673 = 2579755) B2579755
theorem B2293115 : Blo 2291435 2293115 := bstep (se 1 (by rfl) ⟨1719836, by rfl⟩ : syracuseStep 2293115 = 3439673) B3439673
theorem B10459829 : Blo 2291435 10459829 := bbase (se 5 (by rfl) ⟨490304, by rfl⟩ : syracuseStep 10459829 = 980609) (by norm_num)
theorem B6973219 : Blo 2291435 6973219 := bstep (se 1 (by rfl) ⟨5229914, by rfl⟩ : syracuseStep 6973219 = 10459829) B10459829
theorem B9297625 : Blo 2291435 9297625 := bstep (se 2 (by rfl) ⟨3486609, by rfl⟩ : syracuseStep 9297625 = 6973219) B6973219
theorem B12396833 : Blo 2291435 12396833 := bstep (se 2 (by rfl) ⟨4648812, by rfl⟩ : syracuseStep 12396833 = 9297625) B9297625
theorem B8264555 : Blo 2291435 8264555 := bstep (se 1 (by rfl) ⟨6198416, by rfl⟩ : syracuseStep 8264555 = 12396833) B12396833
theorem B5509703 : Blo 2291435 5509703 := bstep (se 1 (by rfl) ⟨4132277, by rfl⟩ : syracuseStep 5509703 = 8264555) B8264555
theorem B3673135 : Blo 2291435 3673135 := bstep (se 1 (by rfl) ⟨2754851, by rfl⟩ : syracuseStep 3673135 = 5509703) B5509703
theorem B4897513 : Blo 2291435 4897513 := bstep (se 2 (by rfl) ⟨1836567, by rfl⟩ : syracuseStep 4897513 = 3673135) B3673135
theorem B26120069 : Blo 2291435 26120069 := bstep (se 4 (by rfl) ⟨2448756, by rfl⟩ : syracuseStep 26120069 = 4897513) B4897513
theorem B17413379 : Blo 2291435 17413379 := bstep (se 1 (by rfl) ⟨13060034, by rfl⟩ : syracuseStep 17413379 = 26120069) B26120069
theorem B11608919 : Blo 2291435 11608919 := bstep (se 1 (by rfl) ⟨8706689, by rfl⟩ : syracuseStep 11608919 = 17413379) B17413379
theorem B7739279 : Blo 2291435 7739279 := bstep (se 1 (by rfl) ⟨5804459, by rfl⟩ : syracuseStep 7739279 = 11608919) B11608919
theorem B5159519 : Blo 2291435 5159519 := bstep (se 1 (by rfl) ⟨3869639, by rfl⟩ : syracuseStep 5159519 = 7739279) B7739279
theorem B3439679 : Blo 2291435 3439679 := bstep (se 1 (by rfl) ⟨2579759, by rfl⟩ : syracuseStep 3439679 = 5159519) B5159519
theorem B2293119 : Blo 2291435 2293119 := bstep (se 1 (by rfl) ⟨1719839, by rfl⟩ : syracuseStep 2293119 = 3439679) B3439679
theorem B3439685 : Blo 2291435 3439685 := bbase (se 4 (by rfl) ⟨322470, by rfl⟩ : syracuseStep 3439685 = 644941) (by norm_num)
theorem B2293123 : Blo 2291435 2293123 := bstep (se 1 (by rfl) ⟨1719842, by rfl⟩ : syracuseStep 2293123 = 3439685) B3439685
theorem B3869653 : Blo 2291435 3869653 := bbase (se 7 (by rfl) ⟨45347, by rfl⟩ : syracuseStep 3869653 = 90695) (by norm_num)
theorem B5159537 : Blo 2291435 5159537 := bstep (se 2 (by rfl) ⟨1934826, by rfl⟩ : syracuseStep 5159537 = 3869653) B3869653
theorem B3439691 : Blo 2291435 3439691 := bstep (se 1 (by rfl) ⟨2579768, by rfl⟩ : syracuseStep 3439691 = 5159537) B5159537
theorem B2293127 : Blo 2291435 2293127 := bstep (se 1 (by rfl) ⟨1719845, by rfl⟩ : syracuseStep 2293127 = 3439691) B3439691
theorem B2579773 : Blo 2291435 2579773 := bbase (se 3 (by rfl) ⟨483707, by rfl⟩ : syracuseStep 2579773 = 967415) (by norm_num)
theorem B3439697 : Blo 2291435 3439697 := bstep (se 2 (by rfl) ⟨1289886, by rfl⟩ : syracuseStep 3439697 = 2579773) B2579773
theorem B2293131 : Blo 2291435 2293131 := bstep (se 1 (by rfl) ⟨1719848, by rfl⟩ : syracuseStep 2293131 = 3439697) B3439697
theorem B7739333 : Blo 2291435 7739333 := bbase (se 4 (by rfl) ⟨725562, by rfl⟩ : syracuseStep 7739333 = 1451125) (by norm_num)
theorem B5159555 : Blo 2291435 5159555 := bstep (se 1 (by rfl) ⟨3869666, by rfl⟩ : syracuseStep 5159555 = 7739333) B7739333
theorem B3439703 : Blo 2291435 3439703 := bstep (se 1 (by rfl) ⟨2579777, by rfl⟩ : syracuseStep 3439703 = 5159555) B5159555
theorem B2293135 : Blo 2291435 2293135 := bstep (se 1 (by rfl) ⟨1719851, by rfl⟩ : syracuseStep 2293135 = 3439703) B3439703
theorem B3439709 : Blo 2291435 3439709 := bbase (se 3 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 3439709 = 1289891) (by norm_num)
theorem B2293139 : Blo 2291435 2293139 := bstep (se 1 (by rfl) ⟨1719854, by rfl⟩ : syracuseStep 2293139 = 3439709) B3439709
theorem B5159573 : Blo 2291435 5159573 := bbase (se 6 (by rfl) ⟨120927, by rfl⟩ : syracuseStep 5159573 = 241855) (by norm_num)
theorem B3439715 : Blo 2291435 3439715 := bstep (se 1 (by rfl) ⟨2579786, by rfl⟩ : syracuseStep 3439715 = 5159573) B5159573
theorem B2293143 : Blo 2291435 2293143 := bstep (se 1 (by rfl) ⟨1719857, by rfl⟩ : syracuseStep 2293143 = 3439715) B3439715
theorem B3673181 : Blo 2291435 3673181 := bbase (se 3 (by rfl) ⟨688721, by rfl⟩ : syracuseStep 3673181 = 1377443) (by norm_num)
theorem B2448787 : Blo 2291435 2448787 := bstep (se 1 (by rfl) ⟨1836590, by rfl⟩ : syracuseStep 2448787 = 3673181) B3673181
theorem B3265049 : Blo 2291435 3265049 := bstep (se 2 (by rfl) ⟨1224393, by rfl⟩ : syracuseStep 3265049 = 2448787) B2448787
theorem B8706797 : Blo 2291435 8706797 := bstep (se 3 (by rfl) ⟨1632524, by rfl⟩ : syracuseStep 8706797 = 3265049) B3265049
theorem B5804531 : Blo 2291435 5804531 := bstep (se 1 (by rfl) ⟨4353398, by rfl⟩ : syracuseStep 5804531 = 8706797) B8706797
theorem B3869687 : Blo 2291435 3869687 := bstep (se 1 (by rfl) ⟨2902265, by rfl⟩ : syracuseStep 3869687 = 5804531) B5804531
theorem B2579791 : Blo 2291435 2579791 := bstep (se 1 (by rfl) ⟨1934843, by rfl⟩ : syracuseStep 2579791 = 3869687) B3869687
theorem B3439721 : Blo 2291435 3439721 := bstep (se 2 (by rfl) ⟨1289895, by rfl⟩ : syracuseStep 3439721 = 2579791) B2579791
theorem B2293147 : Blo 2291435 2293147 := bstep (se 1 (by rfl) ⟨1719860, by rfl⟩ : syracuseStep 2293147 = 3439721) B3439721
theorem B10459973 : Blo 2291435 10459973 := bbase (se 4 (by rfl) ⟨980622, by rfl⟩ : syracuseStep 10459973 = 1961245) (by norm_num)
theorem B27893261 : Blo 2291435 27893261 := bstep (se 3 (by rfl) ⟨5229986, by rfl⟩ : syracuseStep 27893261 = 10459973) B10459973
theorem B18595507 : Blo 2291435 18595507 := bstep (se 1 (by rfl) ⟨13946630, by rfl⟩ : syracuseStep 18595507 = 27893261) B27893261
theorem B24794009 : Blo 2291435 24794009 := bstep (se 2 (by rfl) ⟨9297753, by rfl⟩ : syracuseStep 24794009 = 18595507) B18595507
theorem B16529339 : Blo 2291435 16529339 := bstep (se 1 (by rfl) ⟨12397004, by rfl⟩ : syracuseStep 16529339 = 24794009) B24794009
theorem B11019559 : Blo 2291435 11019559 := bstep (se 1 (by rfl) ⟨8264669, by rfl⟩ : syracuseStep 11019559 = 16529339) B16529339
theorem B14692745 : Blo 2291435 14692745 := bstep (se 2 (by rfl) ⟨5509779, by rfl⟩ : syracuseStep 14692745 = 11019559) B11019559
theorem B9795163 : Blo 2291435 9795163 := bstep (se 1 (by rfl) ⟨7346372, by rfl⟩ : syracuseStep 9795163 = 14692745) B14692745
theorem B13060217 : Blo 2291435 13060217 := bstep (se 2 (by rfl) ⟨4897581, by rfl⟩ : syracuseStep 13060217 = 9795163) B9795163
theorem B8706811 : Blo 2291435 8706811 := bstep (se 1 (by rfl) ⟨6530108, by rfl⟩ : syracuseStep 8706811 = 13060217) B13060217
theorem B11609081 : Blo 2291435 11609081 := bstep (se 2 (by rfl) ⟨4353405, by rfl⟩ : syracuseStep 11609081 = 8706811) B8706811
theorem B7739387 : Blo 2291435 7739387 := bstep (se 1 (by rfl) ⟨5804540, by rfl⟩ : syracuseStep 7739387 = 11609081) B11609081
theorem B5159591 : Blo 2291435 5159591 := bstep (se 1 (by rfl) ⟨3869693, by rfl⟩ : syracuseStep 5159591 = 7739387) B7739387
theorem B3439727 : Blo 2291435 3439727 := bstep (se 1 (by rfl) ⟨2579795, by rfl⟩ : syracuseStep 3439727 = 5159591) B5159591
theorem B2293151 : Blo 2291435 2293151 := bstep (se 1 (by rfl) ⟨1719863, by rfl⟩ : syracuseStep 2293151 = 3439727) B3439727
theorem B3439733 : Blo 2291435 3439733 := bbase (se 5 (by rfl) ⟨161237, by rfl⟩ : syracuseStep 3439733 = 322475) (by norm_num)
theorem B2293155 : Blo 2291435 2293155 := bstep (se 1 (by rfl) ⟨1719866, by rfl⟩ : syracuseStep 2293155 = 3439733) B3439733
theorem B4353421 : Blo 2291435 4353421 := bbase (se 3 (by rfl) ⟨816266, by rfl⟩ : syracuseStep 4353421 = 1632533) (by norm_num)
theorem B5804561 : Blo 2291435 5804561 := bstep (se 2 (by rfl) ⟨2176710, by rfl⟩ : syracuseStep 5804561 = 4353421) B4353421
theorem B3869707 : Blo 2291435 3869707 := bstep (se 1 (by rfl) ⟨2902280, by rfl⟩ : syracuseStep 3869707 = 5804561) B5804561
theorem B5159609 : Blo 2291435 5159609 := bstep (se 2 (by rfl) ⟨1934853, by rfl⟩ : syracuseStep 5159609 = 3869707) B3869707
theorem B3439739 : Blo 2291435 3439739 := bstep (se 1 (by rfl) ⟨2579804, by rfl⟩ : syracuseStep 3439739 = 5159609) B5159609
theorem B2293159 : Blo 2291435 2293159 := bstep (se 1 (by rfl) ⟨1719869, by rfl⟩ : syracuseStep 2293159 = 3439739) B3439739
theorem B2579809 : Blo 2291435 2579809 := bbase (se 2 (by rfl) ⟨967428, by rfl⟩ : syracuseStep 2579809 = 1934857) (by norm_num)
theorem B3439745 : Blo 2291435 3439745 := bstep (se 2 (by rfl) ⟨1289904, by rfl⟩ : syracuseStep 3439745 = 2579809) B2579809
theorem B2293163 : Blo 2291435 2293163 := bstep (se 1 (by rfl) ⟨1719872, by rfl⟩ : syracuseStep 2293163 = 3439745) B3439745
theorem B5804581 : Blo 2291435 5804581 := bbase (se 4 (by rfl) ⟨544179, by rfl⟩ : syracuseStep 5804581 = 1088359) (by norm_num)
theorem B7739441 : Blo 2291435 7739441 := bstep (se 2 (by rfl) ⟨2902290, by rfl⟩ : syracuseStep 7739441 = 5804581) B5804581
theorem B5159627 : Blo 2291435 5159627 := bstep (se 1 (by rfl) ⟨3869720, by rfl⟩ : syracuseStep 5159627 = 7739441) B7739441
theorem B3439751 : Blo 2291435 3439751 := bstep (se 1 (by rfl) ⟨2579813, by rfl⟩ : syracuseStep 3439751 = 5159627) B5159627
theorem B2293167 : Blo 2291435 2293167 := bstep (se 1 (by rfl) ⟨1719875, by rfl⟩ : syracuseStep 2293167 = 3439751) B3439751
theorem B3439757 : Blo 2291435 3439757 := bbase (se 3 (by rfl) ⟨644954, by rfl⟩ : syracuseStep 3439757 = 1289909) (by norm_num)
theorem B2293171 : Blo 2291435 2293171 := bstep (se 1 (by rfl) ⟨1719878, by rfl⟩ : syracuseStep 2293171 = 3439757) B3439757
theorem B5159645 : Blo 2291435 5159645 := bbase (se 3 (by rfl) ⟨967433, by rfl⟩ : syracuseStep 5159645 = 1934867) (by norm_num)
theorem B3439763 : Blo 2291435 3439763 := bstep (se 1 (by rfl) ⟨2579822, by rfl⟩ : syracuseStep 3439763 = 5159645) B5159645
theorem B2293175 : Blo 2291435 2293175 := bstep (se 1 (by rfl) ⟨1719881, by rfl⟩ : syracuseStep 2293175 = 3439763) B3439763
theorem B3869741 : Blo 2291435 3869741 := bbase (se 3 (by rfl) ⟨725576, by rfl⟩ : syracuseStep 3869741 = 1451153) (by norm_num)
theorem B2579827 : Blo 2291435 2579827 := bstep (se 1 (by rfl) ⟨1934870, by rfl⟩ : syracuseStep 2579827 = 3869741) B3869741
theorem B3439769 : Blo 2291435 3439769 := bstep (se 2 (by rfl) ⟨1289913, by rfl⟩ : syracuseStep 3439769 = 2579827) B2579827
theorem B2293179 : Blo 2291435 2293179 := bstep (se 1 (by rfl) ⟨1719884, by rfl⟩ : syracuseStep 2293179 = 3439769) B3439769
theorem B18595765 : Blo 2291435 18595765 := bbase (se 5 (by rfl) ⟨871676, by rfl⟩ : syracuseStep 18595765 = 1743353) (by norm_num)
theorem B24794353 : Blo 2291435 24794353 := bstep (se 2 (by rfl) ⟨9297882, by rfl⟩ : syracuseStep 24794353 = 18595765) B18595765
theorem B33059137 : Blo 2291435 33059137 := bstep (se 2 (by rfl) ⟨12397176, by rfl⟩ : syracuseStep 33059137 = 24794353) B24794353
theorem B44078849 : Blo 2291435 44078849 := bstep (se 2 (by rfl) ⟨16529568, by rfl⟩ : syracuseStep 44078849 = 33059137) B33059137
theorem B29385899 : Blo 2291435 29385899 := bstep (se 1 (by rfl) ⟨22039424, by rfl⟩ : syracuseStep 29385899 = 44078849) B44078849
theorem B19590599 : Blo 2291435 19590599 := bstep (se 1 (by rfl) ⟨14692949, by rfl⟩ : syracuseStep 19590599 = 29385899) B29385899
theorem B13060399 : Blo 2291435 13060399 := bstep (se 1 (by rfl) ⟨9795299, by rfl⟩ : syracuseStep 13060399 = 19590599) B19590599
theorem B17413865 : Blo 2291435 17413865 := bstep (se 2 (by rfl) ⟨6530199, by rfl⟩ : syracuseStep 17413865 = 13060399) B13060399
theorem B11609243 : Blo 2291435 11609243 := bstep (se 1 (by rfl) ⟨8706932, by rfl⟩ : syracuseStep 11609243 = 17413865) B17413865
theorem B7739495 : Blo 2291435 7739495 := bstep (se 1 (by rfl) ⟨5804621, by rfl⟩ : syracuseStep 7739495 = 11609243) B11609243
theorem B5159663 : Blo 2291435 5159663 := bstep (se 1 (by rfl) ⟨3869747, by rfl⟩ : syracuseStep 5159663 = 7739495) B7739495
theorem B3439775 : Blo 2291435 3439775 := bstep (se 1 (by rfl) ⟨2579831, by rfl⟩ : syracuseStep 3439775 = 5159663) B5159663
theorem B2293183 : Blo 2291435 2293183 := bstep (se 1 (by rfl) ⟨1719887, by rfl⟩ : syracuseStep 2293183 = 3439775) B3439775
theorem B3439781 : Blo 2291435 3439781 := bbase (se 4 (by rfl) ⟨322479, by rfl⟩ : syracuseStep 3439781 = 644959) (by norm_num)
theorem B2293187 : Blo 2291435 2293187 := bstep (se 1 (by rfl) ⟨1719890, by rfl⟩ : syracuseStep 2293187 = 3439781) B3439781
theorem B2902321 : Blo 2291435 2902321 := bbase (se 2 (by rfl) ⟨1088370, by rfl⟩ : syracuseStep 2902321 = 2176741) (by norm_num)
theorem B3869761 : Blo 2291435 3869761 := bstep (se 2 (by rfl) ⟨1451160, by rfl⟩ : syracuseStep 3869761 = 2902321) B2902321
theorem B5159681 : Blo 2291435 5159681 := bstep (se 2 (by rfl) ⟨1934880, by rfl⟩ : syracuseStep 5159681 = 3869761) B3869761
theorem B3439787 : Blo 2291435 3439787 := bstep (se 1 (by rfl) ⟨2579840, by rfl⟩ : syracuseStep 3439787 = 5159681) B5159681
theorem B2293191 : Blo 2291435 2293191 := bstep (se 1 (by rfl) ⟨1719893, by rfl⟩ : syracuseStep 2293191 = 3439787) B3439787
theorem B2579845 : Blo 2291435 2579845 := bbase (se 4 (by rfl) ⟨241860, by rfl⟩ : syracuseStep 2579845 = 483721) (by norm_num)
theorem B3439793 : Blo 2291435 3439793 := bstep (se 2 (by rfl) ⟨1289922, by rfl⟩ : syracuseStep 3439793 = 2579845) B2579845
theorem B2293195 : Blo 2291435 2293195 := bstep (se 1 (by rfl) ⟨1719896, by rfl⟩ : syracuseStep 2293195 = 3439793) B3439793
theorem B4897685 : Blo 2291435 4897685 := bbase (se 6 (by rfl) ⟨114789, by rfl⟩ : syracuseStep 4897685 = 229579) (by norm_num)
theorem B3265123 : Blo 2291435 3265123 := bstep (se 1 (by rfl) ⟨2448842, by rfl⟩ : syracuseStep 3265123 = 4897685) B4897685
theorem B4353497 : Blo 2291435 4353497 := bstep (se 2 (by rfl) ⟨1632561, by rfl⟩ : syracuseStep 4353497 = 3265123) B3265123
theorem B2902331 : Blo 2291435 2902331 := bstep (se 1 (by rfl) ⟨2176748, by rfl⟩ : syracuseStep 2902331 = 4353497) B4353497
theorem B7739549 : Blo 2291435 7739549 := bstep (se 3 (by rfl) ⟨1451165, by rfl⟩ : syracuseStep 7739549 = 2902331) B2902331
theorem B5159699 : Blo 2291435 5159699 := bstep (se 1 (by rfl) ⟨3869774, by rfl⟩ : syracuseStep 5159699 = 7739549) B7739549
theorem B3439799 : Blo 2291435 3439799 := bstep (se 1 (by rfl) ⟨2579849, by rfl⟩ : syracuseStep 3439799 = 5159699) B5159699
theorem B2293199 : Blo 2291435 2293199 := bstep (se 1 (by rfl) ⟨1719899, by rfl⟩ : syracuseStep 2293199 = 3439799) B3439799
theorem B3439805 : Blo 2291435 3439805 := bbase (se 3 (by rfl) ⟨644963, by rfl⟩ : syracuseStep 3439805 = 1289927) (by norm_num)
theorem B2293203 : Blo 2291435 2293203 := bstep (se 1 (by rfl) ⟨1719902, by rfl⟩ : syracuseStep 2293203 = 3439805) B3439805
theorem B5159717 : Blo 2291435 5159717 := bbase (se 4 (by rfl) ⟨483723, by rfl⟩ : syracuseStep 5159717 = 967447) (by norm_num)
theorem B3439811 : Blo 2291435 3439811 := bstep (se 1 (by rfl) ⟨2579858, by rfl⟩ : syracuseStep 3439811 = 5159717) B5159717
theorem B2293207 : Blo 2291435 2293207 := bstep (se 1 (by rfl) ⟨1719905, by rfl⟩ : syracuseStep 2293207 = 3439811) B3439811
theorem B5804693 : Blo 2291435 5804693 := bbase (se 6 (by rfl) ⟨136047, by rfl⟩ : syracuseStep 5804693 = 272095) (by norm_num)
theorem B3869795 : Blo 2291435 3869795 := bstep (se 1 (by rfl) ⟨2902346, by rfl⟩ : syracuseStep 3869795 = 5804693) B5804693
theorem B2579863 : Blo 2291435 2579863 := bstep (se 1 (by rfl) ⟨1934897, by rfl⟩ : syracuseStep 2579863 = 3869795) B3869795
theorem B3439817 : Blo 2291435 3439817 := bstep (se 2 (by rfl) ⟨1289931, by rfl⟩ : syracuseStep 3439817 = 2579863) B2579863
theorem B2293211 : Blo 2291435 2293211 := bstep (se 1 (by rfl) ⟨1719908, by rfl⟩ : syracuseStep 2293211 = 3439817) B3439817
theorem B6198677 : Blo 2291435 6198677 := bbase (se 6 (by rfl) ⟨145281, by rfl⟩ : syracuseStep 6198677 = 290563) (by norm_num)
theorem B4132451 : Blo 2291435 4132451 := bstep (se 1 (by rfl) ⟨3099338, by rfl⟩ : syracuseStep 4132451 = 6198677) B6198677
theorem B2754967 : Blo 2291435 2754967 := bstep (se 1 (by rfl) ⟨2066225, by rfl⟩ : syracuseStep 2754967 = 4132451) B4132451
theorem B3673289 : Blo 2291435 3673289 := bstep (se 2 (by rfl) ⟨1377483, by rfl⟩ : syracuseStep 3673289 = 2754967) B2754967
theorem B9795437 : Blo 2291435 9795437 := bstep (se 3 (by rfl) ⟨1836644, by rfl⟩ : syracuseStep 9795437 = 3673289) B3673289
theorem B6530291 : Blo 2291435 6530291 := bstep (se 1 (by rfl) ⟨4897718, by rfl⟩ : syracuseStep 6530291 = 9795437) B9795437
theorem B4353527 : Blo 2291435 4353527 := bstep (se 1 (by rfl) ⟨3265145, by rfl⟩ : syracuseStep 4353527 = 6530291) B6530291
theorem B11609405 : Blo 2291435 11609405 := bstep (se 3 (by rfl) ⟨2176763, by rfl⟩ : syracuseStep 11609405 = 4353527) B4353527
theorem B7739603 : Blo 2291435 7739603 := bstep (se 1 (by rfl) ⟨5804702, by rfl⟩ : syracuseStep 7739603 = 11609405) B11609405
theorem B5159735 : Blo 2291435 5159735 := bstep (se 1 (by rfl) ⟨3869801, by rfl⟩ : syracuseStep 5159735 = 7739603) B7739603
theorem B3439823 : Blo 2291435 3439823 := bstep (se 1 (by rfl) ⟨2579867, by rfl⟩ : syracuseStep 3439823 = 5159735) B5159735
theorem B2293215 : Blo 2291435 2293215 := bstep (se 1 (by rfl) ⟨1719911, by rfl⟩ : syracuseStep 2293215 = 3439823) B3439823
theorem B3439829 : Blo 2291435 3439829 := bbase (se 7 (by rfl) ⟨40310, by rfl⟩ : syracuseStep 3439829 = 80621) (by norm_num)
theorem B2293219 : Blo 2291435 2293219 := bstep (se 1 (by rfl) ⟨1719914, by rfl⟩ : syracuseStep 2293219 = 3439829) B3439829
theorem B3265157 : Blo 2291435 3265157 := bbase (se 4 (by rfl) ⟨306108, by rfl⟩ : syracuseStep 3265157 = 612217) (by norm_num)
theorem B8707085 : Blo 2291435 8707085 := bstep (se 3 (by rfl) ⟨1632578, by rfl⟩ : syracuseStep 8707085 = 3265157) B3265157
theorem B5804723 : Blo 2291435 5804723 := bstep (se 1 (by rfl) ⟨4353542, by rfl⟩ : syracuseStep 5804723 = 8707085) B8707085
theorem B3869815 : Blo 2291435 3869815 := bstep (se 1 (by rfl) ⟨2902361, by rfl⟩ : syracuseStep 3869815 = 5804723) B5804723
theorem B5159753 : Blo 2291435 5159753 := bstep (se 2 (by rfl) ⟨1934907, by rfl⟩ : syracuseStep 5159753 = 3869815) B3869815
theorem B3439835 : Blo 2291435 3439835 := bstep (se 1 (by rfl) ⟨2579876, by rfl⟩ : syracuseStep 3439835 = 5159753) B5159753
theorem B2293223 : Blo 2291435 2293223 := bstep (se 1 (by rfl) ⟨1719917, by rfl⟩ : syracuseStep 2293223 = 3439835) B3439835
theorem B2579881 : Blo 2291435 2579881 := bbase (se 2 (by rfl) ⟨967455, by rfl⟩ : syracuseStep 2579881 = 1934911) (by norm_num)
theorem B3439841 : Blo 2291435 3439841 := bstep (se 2 (by rfl) ⟨1289940, by rfl⟩ : syracuseStep 3439841 = 2579881) B2579881
theorem B2293227 : Blo 2291435 2293227 := bstep (se 1 (by rfl) ⟨1719920, by rfl⟩ : syracuseStep 2293227 = 3439841) B3439841
theorem B7346629 : Blo 2291435 7346629 := bbase (se 4 (by rfl) ⟨688746, by rfl⟩ : syracuseStep 7346629 = 1377493) (by norm_num)
theorem B9795505 : Blo 2291435 9795505 := bstep (se 2 (by rfl) ⟨3673314, by rfl⟩ : syracuseStep 9795505 = 7346629) B7346629
theorem B13060673 : Blo 2291435 13060673 := bstep (se 2 (by rfl) ⟨4897752, by rfl⟩ : syracuseStep 13060673 = 9795505) B9795505
theorem B8707115 : Blo 2291435 8707115 := bstep (se 1 (by rfl) ⟨6530336, by rfl⟩ : syracuseStep 8707115 = 13060673) B13060673
theorem B5804743 : Blo 2291435 5804743 := bstep (se 1 (by rfl) ⟨4353557, by rfl⟩ : syracuseStep 5804743 = 8707115) B8707115
theorem B7739657 : Blo 2291435 7739657 := bstep (se 2 (by rfl) ⟨2902371, by rfl⟩ : syracuseStep 7739657 = 5804743) B5804743
theorem B5159771 : Blo 2291435 5159771 := bstep (se 1 (by rfl) ⟨3869828, by rfl⟩ : syracuseStep 5159771 = 7739657) B7739657
theorem B3439847 : Blo 2291435 3439847 := bstep (se 1 (by rfl) ⟨2579885, by rfl⟩ : syracuseStep 3439847 = 5159771) B5159771
theorem B2293231 : Blo 2291435 2293231 := bstep (se 1 (by rfl) ⟨1719923, by rfl⟩ : syracuseStep 2293231 = 3439847) B3439847
theorem B3439853 : Blo 2291435 3439853 := bbase (se 3 (by rfl) ⟨644972, by rfl⟩ : syracuseStep 3439853 = 1289945) (by norm_num)
theorem B2293235 : Blo 2291435 2293235 := bstep (se 1 (by rfl) ⟨1719926, by rfl⟩ : syracuseStep 2293235 = 3439853) B3439853
theorem B5159789 : Blo 2291435 5159789 := bbase (se 3 (by rfl) ⟨967460, by rfl⟩ : syracuseStep 5159789 = 1934921) (by norm_num)
theorem B3439859 : Blo 2291435 3439859 := bstep (se 1 (by rfl) ⟨2579894, by rfl⟩ : syracuseStep 3439859 = 5159789) B5159789
theorem B2293239 : Blo 2291435 2293239 := bstep (se 1 (by rfl) ⟨1719929, by rfl⟩ : syracuseStep 2293239 = 3439859) B3439859
theorem B4353581 : Blo 2291435 4353581 := bbase (se 3 (by rfl) ⟨816296, by rfl⟩ : syracuseStep 4353581 = 1632593) (by norm_num)
theorem B2902387 : Blo 2291435 2902387 := bstep (se 1 (by rfl) ⟨2176790, by rfl⟩ : syracuseStep 2902387 = 4353581) B4353581
theorem B3869849 : Blo 2291435 3869849 := bstep (se 2 (by rfl) ⟨1451193, by rfl⟩ : syracuseStep 3869849 = 2902387) B2902387
theorem B2579899 : Blo 2291435 2579899 := bstep (se 1 (by rfl) ⟨1934924, by rfl⟩ : syracuseStep 2579899 = 3869849) B3869849
theorem B3439865 : Blo 2291435 3439865 := bstep (se 2 (by rfl) ⟨1289949, by rfl⟩ : syracuseStep 3439865 = 2579899) B2579899
theorem B2293243 : Blo 2291435 2293243 := bstep (se 1 (by rfl) ⟨1719932, by rfl⟩ : syracuseStep 2293243 = 3439865) B3439865
theorem B2792593 : Blo 2291435 2792593 := bbase (se 2 (by rfl) ⟨1047222, by rfl⟩ : syracuseStep 2792593 = 2094445) (by norm_num)
theorem B3723457 : Blo 2291435 3723457 := bstep (se 2 (by rfl) ⟨1396296, by rfl⟩ : syracuseStep 3723457 = 2792593) B2792593
theorem B4964609 : Blo 2291435 4964609 := bstep (se 2 (by rfl) ⟨1861728, by rfl⟩ : syracuseStep 4964609 = 3723457) B3723457
theorem B13238957 : Blo 2291435 13238957 := bstep (se 3 (by rfl) ⟨2482304, by rfl⟩ : syracuseStep 13238957 = 4964609) B4964609
theorem B8825971 : Blo 2291435 8825971 := bstep (se 1 (by rfl) ⟨6619478, by rfl⟩ : syracuseStep 8825971 = 13238957) B13238957
theorem B11767961 : Blo 2291435 11767961 := bstep (se 2 (by rfl) ⟨4412985, by rfl⟩ : syracuseStep 11767961 = 8825971) B8825971
theorem B31381229 : Blo 2291435 31381229 := bstep (se 3 (by rfl) ⟨5883980, by rfl⟩ : syracuseStep 31381229 = 11767961) B11767961
theorem B83683277 : Blo 2291435 83683277 := bstep (se 3 (by rfl) ⟨15690614, by rfl⟩ : syracuseStep 83683277 = 31381229) B31381229
theorem B55788851 : Blo 2291435 55788851 := bstep (se 1 (by rfl) ⟨41841638, by rfl⟩ : syracuseStep 55788851 = 83683277) B83683277
theorem B37192567 : Blo 2291435 37192567 := bstep (se 1 (by rfl) ⟨27894425, by rfl⟩ : syracuseStep 37192567 = 55788851) B55788851
theorem B49590089 : Blo 2291435 49590089 := bstep (se 2 (by rfl) ⟨18596283, by rfl⟩ : syracuseStep 49590089 = 37192567) B37192567
theorem B33060059 : Blo 2291435 33060059 := bstep (se 1 (by rfl) ⟨24795044, by rfl⟩ : syracuseStep 33060059 = 49590089) B49590089
theorem B22040039 : Blo 2291435 22040039 := bstep (se 1 (by rfl) ⟨16530029, by rfl⟩ : syracuseStep 22040039 = 33060059) B33060059
theorem B58773437 : Blo 2291435 58773437 := bstep (se 3 (by rfl) ⟨11020019, by rfl⟩ : syracuseStep 58773437 = 22040039) B22040039
theorem B39182291 : Blo 2291435 39182291 := bstep (se 1 (by rfl) ⟨29386718, by rfl⟩ : syracuseStep 39182291 = 58773437) B58773437
theorem B26121527 : Blo 2291435 26121527 := bstep (se 1 (by rfl) ⟨19591145, by rfl⟩ : syracuseStep 26121527 = 39182291) B39182291
theorem B17414351 : Blo 2291435 17414351 := bstep (se 1 (by rfl) ⟨13060763, by rfl⟩ : syracuseStep 17414351 = 26121527) B26121527
theorem B11609567 : Blo 2291435 11609567 := bstep (se 1 (by rfl) ⟨8707175, by rfl⟩ : syracuseStep 11609567 = 17414351) B17414351
theorem B7739711 : Blo 2291435 7739711 := bstep (se 1 (by rfl) ⟨5804783, by rfl⟩ : syracuseStep 7739711 = 11609567) B11609567
theorem B5159807 : Blo 2291435 5159807 := bstep (se 1 (by rfl) ⟨3869855, by rfl⟩ : syracuseStep 5159807 = 7739711) B7739711
theorem B3439871 : Blo 2291435 3439871 := bstep (se 1 (by rfl) ⟨2579903, by rfl⟩ : syracuseStep 3439871 = 5159807) B5159807
theorem B2293247 : Blo 2291435 2293247 := bstep (se 1 (by rfl) ⟨1719935, by rfl⟩ : syracuseStep 2293247 = 3439871) B3439871
theorem B3439877 : Blo 2291435 3439877 := bbase (se 4 (by rfl) ⟨322488, by rfl⟩ : syracuseStep 3439877 = 644977) (by norm_num)
theorem B2293251 : Blo 2291435 2293251 := bstep (se 1 (by rfl) ⟨1719938, by rfl⟩ : syracuseStep 2293251 = 3439877) B3439877
theorem B3869869 : Blo 2291435 3869869 := bbase (se 3 (by rfl) ⟨725600, by rfl⟩ : syracuseStep 3869869 = 1451201) (by norm_num)
theorem B5159825 : Blo 2291435 5159825 := bstep (se 2 (by rfl) ⟨1934934, by rfl⟩ : syracuseStep 5159825 = 3869869) B3869869
theorem B3439883 : Blo 2291435 3439883 := bstep (se 1 (by rfl) ⟨2579912, by rfl⟩ : syracuseStep 3439883 = 5159825) B5159825
theorem B2293255 : Blo 2291435 2293255 := bstep (se 1 (by rfl) ⟨1719941, by rfl⟩ : syracuseStep 2293255 = 3439883) B3439883
theorem B2579917 : Blo 2291435 2579917 := bbase (se 3 (by rfl) ⟨483734, by rfl⟩ : syracuseStep 2579917 = 967469) (by norm_num)
theorem B3439889 : Blo 2291435 3439889 := bstep (se 2 (by rfl) ⟨1289958, by rfl⟩ : syracuseStep 3439889 = 2579917) B2579917
theorem B2293259 : Blo 2291435 2293259 := bstep (se 1 (by rfl) ⟨1719944, by rfl⟩ : syracuseStep 2293259 = 3439889) B3439889
theorem B7739765 : Blo 2291435 7739765 := bbase (se 5 (by rfl) ⟨362801, by rfl⟩ : syracuseStep 7739765 = 725603) (by norm_num)
theorem B5159843 : Blo 2291435 5159843 := bstep (se 1 (by rfl) ⟨3869882, by rfl⟩ : syracuseStep 5159843 = 7739765) B7739765
theorem B3439895 : Blo 2291435 3439895 := bstep (se 1 (by rfl) ⟨2579921, by rfl⟩ : syracuseStep 3439895 = 5159843) B5159843
theorem B2293263 : Blo 2291435 2293263 := bstep (se 1 (by rfl) ⟨1719947, by rfl⟩ : syracuseStep 2293263 = 3439895) B3439895
theorem B3439901 : Blo 2291435 3439901 := bbase (se 3 (by rfl) ⟨644981, by rfl⟩ : syracuseStep 3439901 = 1289963) (by norm_num)
theorem B2293267 : Blo 2291435 2293267 := bstep (se 1 (by rfl) ⟨1719950, by rfl⟩ : syracuseStep 2293267 = 3439901) B3439901
theorem B5159861 : Blo 2291435 5159861 := bbase (se 5 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 5159861 = 483737) (by norm_num)
theorem B3439907 : Blo 2291435 3439907 := bstep (se 1 (by rfl) ⟨2579930, by rfl⟩ : syracuseStep 3439907 = 5159861) B5159861
theorem B2293271 : Blo 2291435 2293271 := bstep (se 1 (by rfl) ⟨1719953, by rfl⟩ : syracuseStep 2293271 = 3439907) B3439907
theorem B28661141 : Blo 2291435 28661141 := bbase (se 6 (by rfl) ⟨671745, by rfl⟩ : syracuseStep 28661141 = 1343491) (by norm_num)
theorem B19107427 : Blo 2291435 19107427 := bstep (se 1 (by rfl) ⟨14330570, by rfl⟩ : syracuseStep 19107427 = 28661141) B28661141
theorem B25476569 : Blo 2291435 25476569 := bstep (se 2 (by rfl) ⟨9553713, by rfl⟩ : syracuseStep 25476569 = 19107427) B19107427
theorem B16984379 : Blo 2291435 16984379 := bstep (se 1 (by rfl) ⟨12738284, by rfl⟩ : syracuseStep 16984379 = 25476569) B25476569
theorem B11322919 : Blo 2291435 11322919 := bstep (se 1 (by rfl) ⟨8492189, by rfl⟩ : syracuseStep 11322919 = 16984379) B16984379
theorem B15097225 : Blo 2291435 15097225 := bstep (se 2 (by rfl) ⟨5661459, by rfl⟩ : syracuseStep 15097225 = 11322919) B11322919
theorem B20129633 : Blo 2291435 20129633 := bstep (se 2 (by rfl) ⟨7548612, by rfl⟩ : syracuseStep 20129633 = 15097225) B15097225
theorem B13419755 : Blo 2291435 13419755 := bstep (se 1 (by rfl) ⟨10064816, by rfl⟩ : syracuseStep 13419755 = 20129633) B20129633
theorem B8946503 : Blo 2291435 8946503 := bstep (se 1 (by rfl) ⟨6709877, by rfl⟩ : syracuseStep 8946503 = 13419755) B13419755
theorem B5964335 : Blo 2291435 5964335 := bstep (se 1 (by rfl) ⟨4473251, by rfl⟩ : syracuseStep 5964335 = 8946503) B8946503
theorem B3976223 : Blo 2291435 3976223 := bstep (se 1 (by rfl) ⟨2982167, by rfl⟩ : syracuseStep 3976223 = 5964335) B5964335
theorem B10603261 : Blo 2291435 10603261 := bstep (se 3 (by rfl) ⟨1988111, by rfl⟩ : syracuseStep 10603261 = 3976223) B3976223
theorem B14137681 : Blo 2291435 14137681 := bstep (se 2 (by rfl) ⟨5301630, by rfl⟩ : syracuseStep 14137681 = 10603261) B10603261
theorem B18850241 : Blo 2291435 18850241 := bstep (se 2 (by rfl) ⟨7068840, by rfl⟩ : syracuseStep 18850241 = 14137681) B14137681
theorem B12566827 : Blo 2291435 12566827 := bstep (se 1 (by rfl) ⟨9425120, by rfl⟩ : syracuseStep 12566827 = 18850241) B18850241
theorem B16755769 : Blo 2291435 16755769 := bstep (se 2 (by rfl) ⟨6283413, by rfl⟩ : syracuseStep 16755769 = 12566827) B12566827
theorem B22341025 : Blo 2291435 22341025 := bstep (se 2 (by rfl) ⟨8377884, by rfl⟩ : syracuseStep 22341025 = 16755769) B16755769
theorem B29788033 : Blo 2291435 29788033 := bstep (se 2 (by rfl) ⟨11170512, by rfl⟩ : syracuseStep 29788033 = 22341025) B22341025
theorem B39717377 : Blo 2291435 39717377 := bstep (se 2 (by rfl) ⟨14894016, by rfl⟩ : syracuseStep 39717377 = 29788033) B29788033
theorem B26478251 : Blo 2291435 26478251 := bstep (se 1 (by rfl) ⟨19858688, by rfl⟩ : syracuseStep 26478251 = 39717377) B39717377
theorem B17652167 : Blo 2291435 17652167 := bstep (se 1 (by rfl) ⟨13239125, by rfl⟩ : syracuseStep 17652167 = 26478251) B26478251
theorem B11768111 : Blo 2291435 11768111 := bstep (se 1 (by rfl) ⟨8826083, by rfl⟩ : syracuseStep 11768111 = 17652167) B17652167
theorem B7845407 : Blo 2291435 7845407 := bstep (se 1 (by rfl) ⟨5884055, by rfl⟩ : syracuseStep 7845407 = 11768111) B11768111
theorem B5230271 : Blo 2291435 5230271 := bstep (se 1 (by rfl) ⟨3922703, by rfl⟩ : syracuseStep 5230271 = 7845407) B7845407
theorem B13947389 : Blo 2291435 13947389 := bstep (se 3 (by rfl) ⟨2615135, by rfl⟩ : syracuseStep 13947389 = 5230271) B5230271
theorem B9298259 : Blo 2291435 9298259 := bstep (se 1 (by rfl) ⟨6973694, by rfl⟩ : syracuseStep 9298259 = 13947389) B13947389
theorem B6198839 : Blo 2291435 6198839 := bstep (se 1 (by rfl) ⟨4649129, by rfl⟩ : syracuseStep 6198839 = 9298259) B9298259
theorem B4132559 : Blo 2291435 4132559 := bstep (se 1 (by rfl) ⟨3099419, by rfl⟩ : syracuseStep 4132559 = 6198839) B6198839
theorem B11020157 : Blo 2291435 11020157 := bstep (se 3 (by rfl) ⟨2066279, by rfl⟩ : syracuseStep 11020157 = 4132559) B4132559
theorem B7346771 : Blo 2291435 7346771 := bstep (se 1 (by rfl) ⟨5510078, by rfl⟩ : syracuseStep 7346771 = 11020157) B11020157
theorem B4897847 : Blo 2291435 4897847 := bstep (se 1 (by rfl) ⟨3673385, by rfl⟩ : syracuseStep 4897847 = 7346771) B7346771
theorem B13060925 : Blo 2291435 13060925 := bstep (se 3 (by rfl) ⟨2448923, by rfl⟩ : syracuseStep 13060925 = 4897847) B4897847
theorem B8707283 : Blo 2291435 8707283 := bstep (se 1 (by rfl) ⟨6530462, by rfl⟩ : syracuseStep 8707283 = 13060925) B13060925
theorem B5804855 : Blo 2291435 5804855 := bstep (se 1 (by rfl) ⟨4353641, by rfl⟩ : syracuseStep 5804855 = 8707283) B8707283
theorem B3869903 : Blo 2291435 3869903 := bstep (se 1 (by rfl) ⟨2902427, by rfl⟩ : syracuseStep 3869903 = 5804855) B5804855
theorem B2579935 : Blo 2291435 2579935 := bstep (se 1 (by rfl) ⟨1934951, by rfl⟩ : syracuseStep 2579935 = 3869903) B3869903
theorem B3439913 : Blo 2291435 3439913 := bstep (se 2 (by rfl) ⟨1289967, by rfl⟩ : syracuseStep 3439913 = 2579935) B2579935
theorem B2293275 : Blo 2291435 2293275 := bstep (se 1 (by rfl) ⟨1719956, by rfl⟩ : syracuseStep 2293275 = 3439913) B3439913
theorem B6619573 : Blo 2291435 6619573 := bbase (se 5 (by rfl) ⟨310292, by rfl⟩ : syracuseStep 6619573 = 620585) (by norm_num)
theorem B8826097 : Blo 2291435 8826097 := bstep (se 2 (by rfl) ⟨3309786, by rfl⟩ : syracuseStep 8826097 = 6619573) B6619573
theorem B11768129 : Blo 2291435 11768129 := bstep (se 2 (by rfl) ⟨4413048, by rfl⟩ : syracuseStep 11768129 = 8826097) B8826097
theorem B7845419 : Blo 2291435 7845419 := bstep (se 1 (by rfl) ⟨5884064, by rfl⟩ : syracuseStep 7845419 = 11768129) B11768129
theorem B5230279 : Blo 2291435 5230279 := bstep (se 1 (by rfl) ⟨3922709, by rfl⟩ : syracuseStep 5230279 = 7845419) B7845419
theorem B6973705 : Blo 2291435 6973705 := bstep (se 2 (by rfl) ⟨2615139, by rfl⟩ : syracuseStep 6973705 = 5230279) B5230279
theorem B37193093 : Blo 2291435 37193093 := bstep (se 4 (by rfl) ⟨3486852, by rfl⟩ : syracuseStep 37193093 = 6973705) B6973705
theorem B24795395 : Blo 2291435 24795395 := bstep (se 1 (by rfl) ⟨18596546, by rfl⟩ : syracuseStep 24795395 = 37193093) B37193093
theorem B16530263 : Blo 2291435 16530263 := bstep (se 1 (by rfl) ⟨12397697, by rfl⟩ : syracuseStep 16530263 = 24795395) B24795395
theorem B11020175 : Blo 2291435 11020175 := bstep (se 1 (by rfl) ⟨8265131, by rfl⟩ : syracuseStep 11020175 = 16530263) B16530263
theorem B7346783 : Blo 2291435 7346783 := bstep (se 1 (by rfl) ⟨5510087, by rfl⟩ : syracuseStep 7346783 = 11020175) B11020175
theorem B4897855 : Blo 2291435 4897855 := bstep (se 1 (by rfl) ⟨3673391, by rfl⟩ : syracuseStep 4897855 = 7346783) B7346783
theorem B6530473 : Blo 2291435 6530473 := bstep (se 2 (by rfl) ⟨2448927, by rfl⟩ : syracuseStep 6530473 = 4897855) B4897855
theorem B8707297 : Blo 2291435 8707297 := bstep (se 2 (by rfl) ⟨3265236, by rfl⟩ : syracuseStep 8707297 = 6530473) B6530473
theorem B11609729 : Blo 2291435 11609729 := bstep (se 2 (by rfl) ⟨4353648, by rfl⟩ : syracuseStep 11609729 = 8707297) B8707297
theorem B7739819 : Blo 2291435 7739819 := bstep (se 1 (by rfl) ⟨5804864, by rfl⟩ : syracuseStep 7739819 = 11609729) B11609729
theorem B5159879 : Blo 2291435 5159879 := bstep (se 1 (by rfl) ⟨3869909, by rfl⟩ : syracuseStep 5159879 = 7739819) B7739819
theorem B3439919 : Blo 2291435 3439919 := bstep (se 1 (by rfl) ⟨2579939, by rfl⟩ : syracuseStep 3439919 = 5159879) B5159879
theorem B2293279 : Blo 2291435 2293279 := bstep (se 1 (by rfl) ⟨1719959, by rfl⟩ : syracuseStep 2293279 = 3439919) B3439919
theorem B3439925 : Blo 2291435 3439925 := bbase (se 5 (by rfl) ⟨161246, by rfl⟩ : syracuseStep 3439925 = 322493) (by norm_num)
theorem B2293283 : Blo 2291435 2293283 := bstep (se 1 (by rfl) ⟨1719962, by rfl⟩ : syracuseStep 2293283 = 3439925) B3439925
theorem B5804885 : Blo 2291435 5804885 := bbase (se 9 (by rfl) ⟨17006, by rfl⟩ : syracuseStep 5804885 = 34013) (by norm_num)
theorem B3869923 : Blo 2291435 3869923 := bstep (se 1 (by rfl) ⟨2902442, by rfl⟩ : syracuseStep 3869923 = 5804885) B5804885
theorem B5159897 : Blo 2291435 5159897 := bstep (se 2 (by rfl) ⟨1934961, by rfl⟩ : syracuseStep 5159897 = 3869923) B3869923
theorem B3439931 : Blo 2291435 3439931 := bstep (se 1 (by rfl) ⟨2579948, by rfl⟩ : syracuseStep 3439931 = 5159897) B5159897
theorem B2293287 : Blo 2291435 2293287 := bstep (se 1 (by rfl) ⟨1719965, by rfl⟩ : syracuseStep 2293287 = 3439931) B3439931
theorem B2579953 : Blo 2291435 2579953 := bbase (se 2 (by rfl) ⟨967482, by rfl⟩ : syracuseStep 2579953 = 1934965) (by norm_num)
theorem B3439937 : Blo 2291435 3439937 := bstep (se 2 (by rfl) ⟨1289976, by rfl⟩ : syracuseStep 3439937 = 2579953) B2579953
theorem B2293291 : Blo 2291435 2293291 := bstep (se 1 (by rfl) ⟨1719968, by rfl⟩ : syracuseStep 2293291 = 3439937) B3439937
theorem B2324585 : Blo 2291435 2324585 := bbase (se 2 (by rfl) ⟨871719, by rfl⟩ : syracuseStep 2324585 = 1743439) (by norm_num)
theorem B6198893 : Blo 2291435 6198893 := bstep (se 3 (by rfl) ⟨1162292, by rfl⟩ : syracuseStep 6198893 = 2324585) B2324585
theorem B4132595 : Blo 2291435 4132595 := bstep (se 1 (by rfl) ⟨3099446, by rfl⟩ : syracuseStep 4132595 = 6198893) B6198893
theorem B2755063 : Blo 2291435 2755063 := bstep (se 1 (by rfl) ⟨2066297, by rfl⟩ : syracuseStep 2755063 = 4132595) B4132595
theorem B14693669 : Blo 2291435 14693669 := bstep (se 4 (by rfl) ⟨1377531, by rfl⟩ : syracuseStep 14693669 = 2755063) B2755063
theorem B9795779 : Blo 2291435 9795779 := bstep (se 1 (by rfl) ⟨7346834, by rfl⟩ : syracuseStep 9795779 = 14693669) B14693669
theorem B6530519 : Blo 2291435 6530519 := bstep (se 1 (by rfl) ⟨4897889, by rfl⟩ : syracuseStep 6530519 = 9795779) B9795779
theorem B4353679 : Blo 2291435 4353679 := bstep (se 1 (by rfl) ⟨3265259, by rfl⟩ : syracuseStep 4353679 = 6530519) B6530519
theorem B5804905 : Blo 2291435 5804905 := bstep (se 2 (by rfl) ⟨2176839, by rfl⟩ : syracuseStep 5804905 = 4353679) B4353679
theorem B7739873 : Blo 2291435 7739873 := bstep (se 2 (by rfl) ⟨2902452, by rfl⟩ : syracuseStep 7739873 = 5804905) B5804905
theorem B5159915 : Blo 2291435 5159915 := bstep (se 1 (by rfl) ⟨3869936, by rfl⟩ : syracuseStep 5159915 = 7739873) B7739873
theorem B3439943 : Blo 2291435 3439943 := bstep (se 1 (by rfl) ⟨2579957, by rfl⟩ : syracuseStep 3439943 = 5159915) B5159915
theorem B2293295 : Blo 2291435 2293295 := bstep (se 1 (by rfl) ⟨1719971, by rfl⟩ : syracuseStep 2293295 = 3439943) B3439943
theorem B3439949 : Blo 2291435 3439949 := bbase (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) (by norm_num)
theorem B2293299 : Blo 2291435 2293299 := bstep (se 1 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 2293299 = 3439949) B3439949
theorem B5159933 : Blo 2291435 5159933 := bbase (se 3 (by rfl) ⟨967487, by rfl⟩ : syracuseStep 5159933 = 1934975) (by norm_num)
theorem B3439955 : Blo 2291435 3439955 := bstep (se 1 (by rfl) ⟨2579966, by rfl⟩ : syracuseStep 3439955 = 5159933) B5159933
theorem B2293303 : Blo 2291435 2293303 := bstep (se 1 (by rfl) ⟨1719977, by rfl⟩ : syracuseStep 2293303 = 3439955) B3439955
theorem B3869957 : Blo 2291435 3869957 := bbase (se 4 (by rfl) ⟨362808, by rfl⟩ : syracuseStep 3869957 = 725617) (by norm_num)
theorem B2579971 : Blo 2291435 2579971 := bstep (se 1 (by rfl) ⟨1934978, by rfl⟩ : syracuseStep 2579971 = 3869957) B3869957
theorem B3439961 : Blo 2291435 3439961 := bstep (se 2 (by rfl) ⟨1289985, by rfl⟩ : syracuseStep 3439961 = 2579971) B2579971
theorem B2293307 : Blo 2291435 2293307 := bstep (se 1 (by rfl) ⟨1719980, by rfl⟩ : syracuseStep 2293307 = 3439961) B3439961
theorem B17414837 : Blo 2291435 17414837 := bbase (se 5 (by rfl) ⟨816320, by rfl⟩ : syracuseStep 17414837 = 1632641) (by norm_num)
theorem B11609891 : Blo 2291435 11609891 := bstep (se 1 (by rfl) ⟨8707418, by rfl⟩ : syracuseStep 11609891 = 17414837) B17414837
theorem B7739927 : Blo 2291435 7739927 := bstep (se 1 (by rfl) ⟨5804945, by rfl⟩ : syracuseStep 7739927 = 11609891) B11609891
theorem B5159951 : Blo 2291435 5159951 := bstep (se 1 (by rfl) ⟨3869963, by rfl⟩ : syracuseStep 5159951 = 7739927) B7739927
theorem B3439967 : Blo 2291435 3439967 := bstep (se 1 (by rfl) ⟨2579975, by rfl⟩ : syracuseStep 3439967 = 5159951) B5159951
theorem B2293311 : Blo 2291435 2293311 := bstep (se 1 (by rfl) ⟨1719983, by rfl⟩ : syracuseStep 2293311 = 3439967) B3439967
theorem B3439973 : Blo 2291435 3439973 := bbase (se 4 (by rfl) ⟨322497, by rfl⟩ : syracuseStep 3439973 = 644995) (by norm_num)
theorem B2293315 : Blo 2291435 2293315 := bstep (se 1 (by rfl) ⟨1719986, by rfl⟩ : syracuseStep 2293315 = 3439973) B3439973
theorem B4353725 : Blo 2291435 4353725 := bbase (se 3 (by rfl) ⟨816323, by rfl⟩ : syracuseStep 4353725 = 1632647) (by norm_num)
theorem B2902483 : Blo 2291435 2902483 := bstep (se 1 (by rfl) ⟨2176862, by rfl⟩ : syracuseStep 2902483 = 4353725) B4353725
theorem B3869977 : Blo 2291435 3869977 := bstep (se 2 (by rfl) ⟨1451241, by rfl⟩ : syracuseStep 3869977 = 2902483) B2902483
theorem B5159969 : Blo 2291435 5159969 := bstep (se 2 (by rfl) ⟨1934988, by rfl⟩ : syracuseStep 5159969 = 3869977) B3869977
theorem B3439979 : Blo 2291435 3439979 := bstep (se 1 (by rfl) ⟨2579984, by rfl⟩ : syracuseStep 3439979 = 5159969) B5159969
theorem B2293319 : Blo 2291435 2293319 := bstep (se 1 (by rfl) ⟨1719989, by rfl⟩ : syracuseStep 2293319 = 3439979) B3439979
theorem B2579989 : Blo 2291435 2579989 := bbase (se 6 (by rfl) ⟨60468, by rfl⟩ : syracuseStep 2579989 = 120937) (by norm_num)
theorem B3439985 : Blo 2291435 3439985 := bstep (se 2 (by rfl) ⟨1289994, by rfl⟩ : syracuseStep 3439985 = 2579989) B2579989
theorem B2293323 : Blo 2291435 2293323 := bstep (se 1 (by rfl) ⟨1719992, by rfl⟩ : syracuseStep 2293323 = 3439985) B3439985
theorem B2902493 : Blo 2291435 2902493 := bbase (se 3 (by rfl) ⟨544217, by rfl⟩ : syracuseStep 2902493 = 1088435) (by norm_num)
theorem B7739981 : Blo 2291435 7739981 := bstep (se 3 (by rfl) ⟨1451246, by rfl⟩ : syracuseStep 7739981 = 2902493) B2902493
theorem B5159987 : Blo 2291435 5159987 := bstep (se 1 (by rfl) ⟨3869990, by rfl⟩ : syracuseStep 5159987 = 7739981) B7739981
theorem B3439991 : Blo 2291435 3439991 := bstep (se 1 (by rfl) ⟨2579993, by rfl⟩ : syracuseStep 3439991 = 5159987) B5159987
theorem B2293327 : Blo 2291435 2293327 := bstep (se 1 (by rfl) ⟨1719995, by rfl⟩ : syracuseStep 2293327 = 3439991) B3439991
theorem B3439997 : Blo 2291435 3439997 := bbase (se 3 (by rfl) ⟨644999, by rfl⟩ : syracuseStep 3439997 = 1289999) (by norm_num)
theorem B2293331 : Blo 2291435 2293331 := bstep (se 1 (by rfl) ⟨1719998, by rfl⟩ : syracuseStep 2293331 = 3439997) B3439997
theorem B5160005 : Blo 2291435 5160005 := bbase (se 4 (by rfl) ⟨483750, by rfl⟩ : syracuseStep 5160005 = 967501) (by norm_num)
theorem B3440003 : Blo 2291435 3440003 := bstep (se 1 (by rfl) ⟨2580002, by rfl⟩ : syracuseStep 3440003 = 5160005) B5160005
theorem B2293335 : Blo 2291435 2293335 := bstep (se 1 (by rfl) ⟨1720001, by rfl⟩ : syracuseStep 2293335 = 3440003) B3440003
theorem B6530645 : Blo 2291435 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B4353763 : Blo 2291435 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B5805017 : Blo 2291435 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B3870011 : Blo 2291435 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B2580007 : Blo 2291435 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B3440009 : Blo 2291435 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B2293339 : Blo 2291435 2293339 := bstep (se 1 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 2293339 = 3440009) B3440009
theorem B11610053 : Blo 2291435 11610053 := bbase (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) (by norm_num)
theorem B7740035 : Blo 2291435 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B5160023 : Blo 2291435 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B3440015 : Blo 2291435 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B2293343 : Blo 2291435 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B3440021 : Blo 2291435 3440021 := bbase (se 6 (by rfl) ⟨80625, by rfl⟩ : syracuseStep 3440021 = 161251) (by norm_num)
theorem B2293347 : Blo 2291435 2293347 := bstep (se 1 (by rfl) ⟨1720010, by rfl⟩ : syracuseStep 2293347 = 3440021) B3440021
theorem B5510261 : Blo 2291435 5510261 := bbase (se 5 (by rfl) ⟨258293, by rfl⟩ : syracuseStep 5510261 = 516587) (by norm_num)
theorem B3673507 : Blo 2291435 3673507 := bstep (se 1 (by rfl) ⟨2755130, by rfl⟩ : syracuseStep 3673507 = 5510261) B5510261
theorem B4898009 : Blo 2291435 4898009 := bstep (se 2 (by rfl) ⟨1836753, by rfl⟩ : syracuseStep 4898009 = 3673507) B3673507
theorem B13061357 : Blo 2291435 13061357 := bstep (se 3 (by rfl) ⟨2449004, by rfl⟩ : syracuseStep 13061357 = 4898009) B4898009
theorem B8707571 : Blo 2291435 8707571 := bstep (se 1 (by rfl) ⟨6530678, by rfl⟩ : syracuseStep 8707571 = 13061357) B13061357
theorem B5805047 : Blo 2291435 5805047 := bstep (se 1 (by rfl) ⟨4353785, by rfl⟩ : syracuseStep 5805047 = 8707571) B8707571
theorem B3870031 : Blo 2291435 3870031 := bstep (se 1 (by rfl) ⟨2902523, by rfl⟩ : syracuseStep 3870031 = 5805047) B5805047
theorem B5160041 : Blo 2291435 5160041 := bstep (se 2 (by rfl) ⟨1935015, by rfl⟩ : syracuseStep 5160041 = 3870031) B3870031
theorem B3440027 : Blo 2291435 3440027 := bstep (se 1 (by rfl) ⟨2580020, by rfl⟩ : syracuseStep 3440027 = 5160041) B5160041
theorem B2293351 : Blo 2291435 2293351 := bstep (se 1 (by rfl) ⟨1720013, by rfl⟩ : syracuseStep 2293351 = 3440027) B3440027
theorem B2580025 : Blo 2291435 2580025 := bbase (se 2 (by rfl) ⟨967509, by rfl⟩ : syracuseStep 2580025 = 1935019) (by norm_num)
theorem B3440033 : Blo 2291435 3440033 := bstep (se 2 (by rfl) ⟨1290012, by rfl⟩ : syracuseStep 3440033 = 2580025) B2580025
theorem B2293355 : Blo 2291435 2293355 := bstep (se 1 (by rfl) ⟨1720016, by rfl⟩ : syracuseStep 2293355 = 3440033) B3440033
theorem B2449013 : Blo 2291435 2449013 := bbase (se 5 (by rfl) ⟨114797, by rfl⟩ : syracuseStep 2449013 = 229595) (by norm_num)
theorem B6530701 : Blo 2291435 6530701 := bstep (se 3 (by rfl) ⟨1224506, by rfl⟩ : syracuseStep 6530701 = 2449013) B2449013
theorem B8707601 : Blo 2291435 8707601 := bstep (se 2 (by rfl) ⟨3265350, by rfl⟩ : syracuseStep 8707601 = 6530701) B6530701
theorem B5805067 : Blo 2291435 5805067 := bstep (se 1 (by rfl) ⟨4353800, by rfl⟩ : syracuseStep 5805067 = 8707601) B8707601
theorem B7740089 : Blo 2291435 7740089 := bstep (se 2 (by rfl) ⟨2902533, by rfl⟩ : syracuseStep 7740089 = 5805067) B5805067
theorem B5160059 : Blo 2291435 5160059 := bstep (se 1 (by rfl) ⟨3870044, by rfl⟩ : syracuseStep 5160059 = 7740089) B7740089
theorem B3440039 : Blo 2291435 3440039 := bstep (se 1 (by rfl) ⟨2580029, by rfl⟩ : syracuseStep 3440039 = 5160059) B5160059
theorem B2293359 : Blo 2291435 2293359 := bstep (se 1 (by rfl) ⟨1720019, by rfl⟩ : syracuseStep 2293359 = 3440039) B3440039
theorem B3440045 : Blo 2291435 3440045 := bbase (se 3 (by rfl) ⟨645008, by rfl⟩ : syracuseStep 3440045 = 1290017) (by norm_num)
theorem B2293363 : Blo 2291435 2293363 := bstep (se 1 (by rfl) ⟨1720022, by rfl⟩ : syracuseStep 2293363 = 3440045) B3440045
theorem B5160077 : Blo 2291435 5160077 := bbase (se 3 (by rfl) ⟨967514, by rfl⟩ : syracuseStep 5160077 = 1935029) (by norm_num)
theorem B3440051 : Blo 2291435 3440051 := bstep (se 1 (by rfl) ⟨2580038, by rfl⟩ : syracuseStep 3440051 = 5160077) B5160077
theorem B2293367 : Blo 2291435 2293367 := bstep (se 1 (by rfl) ⟨1720025, by rfl⟩ : syracuseStep 2293367 = 3440051) B3440051
theorem B2902549 : Blo 2291435 2902549 := bbase (se 6 (by rfl) ⟨68028, by rfl⟩ : syracuseStep 2902549 = 136057) (by norm_num)
theorem B3870065 : Blo 2291435 3870065 := bstep (se 2 (by rfl) ⟨1451274, by rfl⟩ : syracuseStep 3870065 = 2902549) B2902549
theorem B2580043 : Blo 2291435 2580043 := bstep (se 1 (by rfl) ⟨1935032, by rfl⟩ : syracuseStep 2580043 = 3870065) B3870065
theorem B3440057 : Blo 2291435 3440057 := bstep (se 2 (by rfl) ⟨1290021, by rfl⟩ : syracuseStep 3440057 = 2580043) B2580043
theorem B2293371 : Blo 2291435 2293371 := bstep (se 1 (by rfl) ⟨1720028, by rfl⟩ : syracuseStep 2293371 = 3440057) B3440057
theorem B5884309 : Blo 2291435 5884309 := bbase (se 6 (by rfl) ⟨137913, by rfl⟩ : syracuseStep 5884309 = 275827) (by norm_num)
theorem B31382981 : Blo 2291435 31382981 := bstep (se 4 (by rfl) ⟨2942154, by rfl⟩ : syracuseStep 31382981 = 5884309) B5884309
theorem B20921987 : Blo 2291435 20921987 := bstep (se 1 (by rfl) ⟨15691490, by rfl⟩ : syracuseStep 20921987 = 31382981) B31382981
theorem B55791965 : Blo 2291435 55791965 := bstep (se 3 (by rfl) ⟨10460993, by rfl⟩ : syracuseStep 55791965 = 20921987) B20921987
theorem B37194643 : Blo 2291435 37194643 := bstep (se 1 (by rfl) ⟨27895982, by rfl⟩ : syracuseStep 37194643 = 55791965) B55791965
theorem B49592857 : Blo 2291435 49592857 := bstep (se 2 (by rfl) ⟨18597321, by rfl⟩ : syracuseStep 49592857 = 37194643) B37194643
theorem B66123809 : Blo 2291435 66123809 := bstep (se 2 (by rfl) ⟨24796428, by rfl⟩ : syracuseStep 66123809 = 49592857) B49592857
theorem B44082539 : Blo 2291435 44082539 := bstep (se 1 (by rfl) ⟨33061904, by rfl⟩ : syracuseStep 44082539 = 66123809) B66123809
theorem B29388359 : Blo 2291435 29388359 := bstep (se 1 (by rfl) ⟨22041269, by rfl⟩ : syracuseStep 29388359 = 44082539) B44082539
theorem B19592239 : Blo 2291435 19592239 := bstep (se 1 (by rfl) ⟨14694179, by rfl⟩ : syracuseStep 19592239 = 29388359) B29388359
theorem B26122985 : Blo 2291435 26122985 := bstep (se 2 (by rfl) ⟨9796119, by rfl⟩ : syracuseStep 26122985 = 19592239) B19592239
theorem B17415323 : Blo 2291435 17415323 := bstep (se 1 (by rfl) ⟨13061492, by rfl⟩ : syracuseStep 17415323 = 26122985) B26122985
theorem B11610215 : Blo 2291435 11610215 := bstep (se 1 (by rfl) ⟨8707661, by rfl⟩ : syracuseStep 11610215 = 17415323) B17415323
theorem B7740143 : Blo 2291435 7740143 := bstep (se 1 (by rfl) ⟨5805107, by rfl⟩ : syracuseStep 7740143 = 11610215) B11610215
theorem B5160095 : Blo 2291435 5160095 := bstep (se 1 (by rfl) ⟨3870071, by rfl⟩ : syracuseStep 5160095 = 7740143) B7740143
theorem B3440063 : Blo 2291435 3440063 := bstep (se 1 (by rfl) ⟨2580047, by rfl⟩ : syracuseStep 3440063 = 5160095) B5160095
theorem B2293375 : Blo 2291435 2293375 := bstep (se 1 (by rfl) ⟨1720031, by rfl⟩ : syracuseStep 2293375 = 3440063) B3440063
theorem B3440069 : Blo 2291435 3440069 := bbase (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) (by norm_num)
theorem B2293379 : Blo 2291435 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B3870085 : Blo 2291435 3870085 := bbase (se 4 (by rfl) ⟨362820, by rfl⟩ : syracuseStep 3870085 = 725641) (by norm_num)
theorem B5160113 : Blo 2291435 5160113 := bstep (se 2 (by rfl) ⟨1935042, by rfl⟩ : syracuseStep 5160113 = 3870085) B3870085
theorem B3440075 : Blo 2291435 3440075 := bstep (se 1 (by rfl) ⟨2580056, by rfl⟩ : syracuseStep 3440075 = 5160113) B5160113
theorem B2293383 : Blo 2291435 2293383 := bstep (se 1 (by rfl) ⟨1720037, by rfl⟩ : syracuseStep 2293383 = 3440075) B3440075
theorem B2580061 : Blo 2291435 2580061 := bbase (se 3 (by rfl) ⟨483761, by rfl⟩ : syracuseStep 2580061 = 967523) (by norm_num)
theorem B3440081 : Blo 2291435 3440081 := bstep (se 2 (by rfl) ⟨1290030, by rfl⟩ : syracuseStep 3440081 = 2580061) B2580061
theorem B2293387 : Blo 2291435 2293387 := bstep (se 1 (by rfl) ⟨1720040, by rfl⟩ : syracuseStep 2293387 = 3440081) B3440081
theorem B7740197 : Blo 2291435 7740197 := bbase (se 4 (by rfl) ⟨725643, by rfl⟩ : syracuseStep 7740197 = 1451287) (by norm_num)
theorem B5160131 : Blo 2291435 5160131 := bstep (se 1 (by rfl) ⟨3870098, by rfl⟩ : syracuseStep 5160131 = 7740197) B7740197
theorem B3440087 : Blo 2291435 3440087 := bstep (se 1 (by rfl) ⟨2580065, by rfl⟩ : syracuseStep 3440087 = 5160131) B5160131
theorem B2293391 : Blo 2291435 2293391 := bstep (se 1 (by rfl) ⟨1720043, by rfl⟩ : syracuseStep 2293391 = 3440087) B3440087
theorem B3440093 : Blo 2291435 3440093 := bbase (se 3 (by rfl) ⟨645017, by rfl⟩ : syracuseStep 3440093 = 1290035) (by norm_num)
theorem B2293395 : Blo 2291435 2293395 := bstep (se 1 (by rfl) ⟨1720046, by rfl⟩ : syracuseStep 2293395 = 3440093) B3440093
theorem B5160149 : Blo 2291435 5160149 := bbase (se 7 (by rfl) ⟨60470, by rfl⟩ : syracuseStep 5160149 = 120941) (by norm_num)
theorem B3440099 : Blo 2291435 3440099 := bstep (se 1 (by rfl) ⟨2580074, by rfl⟩ : syracuseStep 3440099 = 5160149) B5160149
theorem B2293399 : Blo 2291435 2293399 := bstep (se 1 (by rfl) ⟨1720049, by rfl⟩ : syracuseStep 2293399 = 3440099) B3440099
theorem B2755193 : Blo 2291435 2755193 := bbase (se 2 (by rfl) ⟨1033197, by rfl⟩ : syracuseStep 2755193 = 2066395) (by norm_num)
theorem B7347181 : Blo 2291435 7347181 := bstep (se 3 (by rfl) ⟨1377596, by rfl⟩ : syracuseStep 7347181 = 2755193) B2755193
theorem B9796241 : Blo 2291435 9796241 := bstep (se 2 (by rfl) ⟨3673590, by rfl⟩ : syracuseStep 9796241 = 7347181) B7347181
theorem B6530827 : Blo 2291435 6530827 := bstep (se 1 (by rfl) ⟨4898120, by rfl⟩ : syracuseStep 6530827 = 9796241) B9796241
theorem B8707769 : Blo 2291435 8707769 := bstep (se 2 (by rfl) ⟨3265413, by rfl⟩ : syracuseStep 8707769 = 6530827) B6530827
theorem B5805179 : Blo 2291435 5805179 := bstep (se 1 (by rfl) ⟨4353884, by rfl⟩ : syracuseStep 5805179 = 8707769) B8707769
theorem B3870119 : Blo 2291435 3870119 := bstep (se 1 (by rfl) ⟨2902589, by rfl⟩ : syracuseStep 3870119 = 5805179) B5805179
theorem B2580079 : Blo 2291435 2580079 := bstep (se 1 (by rfl) ⟨1935059, by rfl⟩ : syracuseStep 2580079 = 3870119) B3870119
theorem B3440105 : Blo 2291435 3440105 := bstep (se 2 (by rfl) ⟨1290039, by rfl⟩ : syracuseStep 3440105 = 2580079) B2580079
theorem B2293403 : Blo 2291435 2293403 := bstep (se 1 (by rfl) ⟨1720052, by rfl⟩ : syracuseStep 2293403 = 3440105) B3440105
theorem B11020789 : Blo 2291435 11020789 := bbase (se 5 (by rfl) ⟨516599, by rfl⟩ : syracuseStep 11020789 = 1033199) (by norm_num)
theorem B14694385 : Blo 2291435 14694385 := bstep (se 2 (by rfl) ⟨5510394, by rfl⟩ : syracuseStep 14694385 = 11020789) B11020789
theorem B19592513 : Blo 2291435 19592513 := bstep (se 2 (by rfl) ⟨7347192, by rfl⟩ : syracuseStep 19592513 = 14694385) B14694385
theorem B13061675 : Blo 2291435 13061675 := bstep (se 1 (by rfl) ⟨9796256, by rfl⟩ : syracuseStep 13061675 = 19592513) B19592513
theorem B8707783 : Blo 2291435 8707783 := bstep (se 1 (by rfl) ⟨6530837, by rfl⟩ : syracuseStep 8707783 = 13061675) B13061675
theorem B11610377 : Blo 2291435 11610377 := bstep (se 2 (by rfl) ⟨4353891, by rfl⟩ : syracuseStep 11610377 = 8707783) B8707783
theorem B7740251 : Blo 2291435 7740251 := bstep (se 1 (by rfl) ⟨5805188, by rfl⟩ : syracuseStep 7740251 = 11610377) B11610377
theorem B5160167 : Blo 2291435 5160167 := bstep (se 1 (by rfl) ⟨3870125, by rfl⟩ : syracuseStep 5160167 = 7740251) B7740251
theorem B3440111 : Blo 2291435 3440111 := bstep (se 1 (by rfl) ⟨2580083, by rfl⟩ : syracuseStep 3440111 = 5160167) B5160167
theorem B2293407 : Blo 2291435 2293407 := bstep (se 1 (by rfl) ⟨1720055, by rfl⟩ : syracuseStep 2293407 = 3440111) B3440111
theorem B3440117 : Blo 2291435 3440117 := bbase (se 5 (by rfl) ⟨161255, by rfl⟩ : syracuseStep 3440117 = 322511) (by norm_num)
theorem B2293411 : Blo 2291435 2293411 := bstep (se 1 (by rfl) ⟨1720058, by rfl⟩ : syracuseStep 2293411 = 3440117) B3440117
theorem B2449073 : Blo 2291435 2449073 := bbase (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) (by norm_num)
theorem B6530861 : Blo 2291435 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B4353907 : Blo 2291435 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B5805209 : Blo 2291435 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B3870139 : Blo 2291435 3870139 := bstep (se 1 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 3870139 = 5805209) B5805209
theorem B5160185 : Blo 2291435 5160185 := bstep (se 2 (by rfl) ⟨1935069, by rfl⟩ : syracuseStep 5160185 = 3870139) B3870139
theorem B3440123 : Blo 2291435 3440123 := bstep (se 1 (by rfl) ⟨2580092, by rfl⟩ : syracuseStep 3440123 = 5160185) B5160185
theorem B2293415 : Blo 2291435 2293415 := bstep (se 1 (by rfl) ⟨1720061, by rfl⟩ : syracuseStep 2293415 = 3440123) B3440123
theorem B2580097 : Blo 2291435 2580097 := bbase (se 2 (by rfl) ⟨967536, by rfl⟩ : syracuseStep 2580097 = 1935073) (by norm_num)
theorem B3440129 : Blo 2291435 3440129 := bstep (se 2 (by rfl) ⟨1290048, by rfl⟩ : syracuseStep 3440129 = 2580097) B2580097
theorem B2293419 : Blo 2291435 2293419 := bstep (se 1 (by rfl) ⟨1720064, by rfl⟩ : syracuseStep 2293419 = 3440129) B3440129
theorem B5805229 : Blo 2291435 5805229 := bbase (se 3 (by rfl) ⟨1088480, by rfl⟩ : syracuseStep 5805229 = 2176961) (by norm_num)
theorem B7740305 : Blo 2291435 7740305 := bstep (se 2 (by rfl) ⟨2902614, by rfl⟩ : syracuseStep 7740305 = 5805229) B5805229
theorem B5160203 : Blo 2291435 5160203 := bstep (se 1 (by rfl) ⟨3870152, by rfl⟩ : syracuseStep 5160203 = 7740305) B7740305
theorem B3440135 : Blo 2291435 3440135 := bstep (se 1 (by rfl) ⟨2580101, by rfl⟩ : syracuseStep 3440135 = 5160203) B5160203
theorem B2293423 : Blo 2291435 2293423 := bstep (se 1 (by rfl) ⟨1720067, by rfl⟩ : syracuseStep 2293423 = 3440135) B3440135
theorem B3440141 : Blo 2291435 3440141 := bbase (se 3 (by rfl) ⟨645026, by rfl⟩ : syracuseStep 3440141 = 1290053) (by norm_num)
theorem B2293427 : Blo 2291435 2293427 := bstep (se 1 (by rfl) ⟨1720070, by rfl⟩ : syracuseStep 2293427 = 3440141) B3440141
theorem B5160221 : Blo 2291435 5160221 := bbase (se 3 (by rfl) ⟨967541, by rfl⟩ : syracuseStep 5160221 = 1935083) (by norm_num)
theorem B3440147 : Blo 2291435 3440147 := bstep (se 1 (by rfl) ⟨2580110, by rfl⟩ : syracuseStep 3440147 = 5160221) B5160221
theorem B2293431 : Blo 2291435 2293431 := bstep (se 1 (by rfl) ⟨1720073, by rfl⟩ : syracuseStep 2293431 = 3440147) B3440147
theorem B3870173 : Blo 2291435 3870173 := bbase (se 3 (by rfl) ⟨725657, by rfl⟩ : syracuseStep 3870173 = 1451315) (by norm_num)
theorem B2580115 : Blo 2291435 2580115 := bstep (se 1 (by rfl) ⟨1935086, by rfl⟩ : syracuseStep 2580115 = 3870173) B3870173
theorem B3440153 : Blo 2291435 3440153 := bstep (se 2 (by rfl) ⟨1290057, by rfl⟩ : syracuseStep 3440153 = 2580115) B2580115
theorem B2293435 : Blo 2291435 2293435 := bstep (se 1 (by rfl) ⟨1720076, by rfl⟩ : syracuseStep 2293435 = 3440153) B3440153
theorem C0 (j : ℕ) (h1 : 572858 ≤ j) (h2 : j ≤ 573358) : Blo 2291435 (4 * j + 3) := by
  interval_cases j
  · exact B2291435
  · exact B2291439
  · exact B2291443
  · exact B2291447
  · exact B2291451
  · exact B2291455
  · exact B2291459
  · exact B2291463
  · exact B2291467
  · exact B2291471
  · exact B2291475
  · exact B2291479
  · exact B2291483
  · exact B2291487
  · exact B2291491
  · exact B2291495
  · exact B2291499
  · exact B2291503
  · exact B2291507
  · exact B2291511
  · exact B2291515
  · exact B2291519
  · exact B2291523
  · exact B2291527
  · exact B2291531
  · exact B2291535
  · exact B2291539
  · exact B2291543
  · exact B2291547
  · exact B2291551
  · exact B2291555
  · exact B2291559
  · exact B2291563
  · exact B2291567
  · exact B2291571
  · exact B2291575
  · exact B2291579
  · exact B2291583
  · exact B2291587
  · exact B2291591
  · exact B2291595
  · exact B2291599
  · exact B2291603
  · exact B2291607
  · exact B2291611
  · exact B2291615
  · exact B2291619
  · exact B2291623
  · exact B2291627
  · exact B2291631
  · exact B2291635
  · exact B2291639
  · exact B2291643
  · exact B2291647
  · exact B2291651
  · exact B2291655
  · exact B2291659
  · exact B2291663
  · exact B2291667
  · exact B2291671
  · exact B2291675
  · exact B2291679
  · exact B2291683
  · exact B2291687
  · exact B2291691
  · exact B2291695
  · exact B2291699
  · exact B2291703
  · exact B2291707
  · exact B2291711
  · exact B2291715
  · exact B2291719
  · exact B2291723
  · exact B2291727
  · exact B2291731
  · exact B2291735
  · exact B2291739
  · exact B2291743
  · exact B2291747
  · exact B2291751
  · exact B2291755
  · exact B2291759
  · exact B2291763
  · exact B2291767
  · exact B2291771
  · exact B2291775
  · exact B2291779
  · exact B2291783
  · exact B2291787
  · exact B2291791
  · exact B2291795
  · exact B2291799
  · exact B2291803
  · exact B2291807
  · exact B2291811
  · exact B2291815
  · exact B2291819
  · exact B2291823
  · exact B2291827
  · exact B2291831
  · exact B2291835
  · exact B2291839
  · exact B2291843
  · exact B2291847
  · exact B2291851
  · exact B2291855
  · exact B2291859
  · exact B2291863
  · exact B2291867
  · exact B2291871
  · exact B2291875
  · exact B2291879
  · exact B2291883
  · exact B2291887
  · exact B2291891
  · exact B2291895
  · exact B2291899
  · exact B2291903
  · exact B2291907
  · exact B2291911
  · exact B2291915
  · exact B2291919
  · exact B2291923
  · exact B2291927
  · exact B2291931
  · exact B2291935
  · exact B2291939
  · exact B2291943
  · exact B2291947
  · exact B2291951
  · exact B2291955
  · exact B2291959
  · exact B2291963
  · exact B2291967
  · exact B2291971
  · exact B2291975
  · exact B2291979
  · exact B2291983
  · exact B2291987
  · exact B2291991
  · exact B2291995
  · exact B2291999
  · exact B2292003
  · exact B2292007
  · exact B2292011
  · exact B2292015
  · exact B2292019
  · exact B2292023
  · exact B2292027
  · exact B2292031
  · exact B2292035
  · exact B2292039
  · exact B2292043
  · exact B2292047
  · exact B2292051
  · exact B2292055
  · exact B2292059
  · exact B2292063
  · exact B2292067
  · exact B2292071
  · exact B2292075
  · exact B2292079
  · exact B2292083
  · exact B2292087
  · exact B2292091
  · exact B2292095
  · exact B2292099
  · exact B2292103
  · exact B2292107
  · exact B2292111
  · exact B2292115
  · exact B2292119
  · exact B2292123
  · exact B2292127
  · exact B2292131
  · exact B2292135
  · exact B2292139
  · exact B2292143
  · exact B2292147
  · exact B2292151
  · exact B2292155
  · exact B2292159
  · exact B2292163
  · exact B2292167
  · exact B2292171
  · exact B2292175
  · exact B2292179
  · exact B2292183
  · exact B2292187
  · exact B2292191
  · exact B2292195
  · exact B2292199
  · exact B2292203
  · exact B2292207
  · exact B2292211
  · exact B2292215
  · exact B2292219
  · exact B2292223
  · exact B2292227
  · exact B2292231
  · exact B2292235
  · exact B2292239
  · exact B2292243
  · exact B2292247
  · exact B2292251
  · exact B2292255
  · exact B2292259
  · exact B2292263
  · exact B2292267
  · exact B2292271
  · exact B2292275
  · exact B2292279
  · exact B2292283
  · exact B2292287
  · exact B2292291
  · exact B2292295
  · exact B2292299
  · exact B2292303
  · exact B2292307
  · exact B2292311
  · exact B2292315
  · exact B2292319
  · exact B2292323
  · exact B2292327
  · exact B2292331
  · exact B2292335
  · exact B2292339
  · exact B2292343
  · exact B2292347
  · exact B2292351
  · exact B2292355
  · exact B2292359
  · exact B2292363
  · exact B2292367
  · exact B2292371
  · exact B2292375
  · exact B2292379
  · exact B2292383
  · exact B2292387
  · exact B2292391
  · exact B2292395
  · exact B2292399
  · exact B2292403
  · exact B2292407
  · exact B2292411
  · exact B2292415
  · exact B2292419
  · exact B2292423
  · exact B2292427
  · exact B2292431
  · exact B2292435
  · exact B2292439
  · exact B2292443
  · exact B2292447
  · exact B2292451
  · exact B2292455
  · exact B2292459
  · exact B2292463
  · exact B2292467
  · exact B2292471
  · exact B2292475
  · exact B2292479
  · exact B2292483
  · exact B2292487
  · exact B2292491
  · exact B2292495
  · exact B2292499
  · exact B2292503
  · exact B2292507
  · exact B2292511
  · exact B2292515
  · exact B2292519
  · exact B2292523
  · exact B2292527
  · exact B2292531
  · exact B2292535
  · exact B2292539
  · exact B2292543
  · exact B2292547
  · exact B2292551
  · exact B2292555
  · exact B2292559
  · exact B2292563
  · exact B2292567
  · exact B2292571
  · exact B2292575
  · exact B2292579
  · exact B2292583
  · exact B2292587
  · exact B2292591
  · exact B2292595
  · exact B2292599
  · exact B2292603
  · exact B2292607
  · exact B2292611
  · exact B2292615
  · exact B2292619
  · exact B2292623
  · exact B2292627
  · exact B2292631
  · exact B2292635
  · exact B2292639
  · exact B2292643
  · exact B2292647
  · exact B2292651
  · exact B2292655
  · exact B2292659
  · exact B2292663
  · exact B2292667
  · exact B2292671
  · exact B2292675
  · exact B2292679
  · exact B2292683
  · exact B2292687
  · exact B2292691
  · exact B2292695
  · exact B2292699
  · exact B2292703
  · exact B2292707
  · exact B2292711
  · exact B2292715
  · exact B2292719
  · exact B2292723
  · exact B2292727
  · exact B2292731
  · exact B2292735
  · exact B2292739
  · exact B2292743
  · exact B2292747
  · exact B2292751
  · exact B2292755
  · exact B2292759
  · exact B2292763
  · exact B2292767
  · exact B2292771
  · exact B2292775
  · exact B2292779
  · exact B2292783
  · exact B2292787
  · exact B2292791
  · exact B2292795
  · exact B2292799
  · exact B2292803
  · exact B2292807
  · exact B2292811
  · exact B2292815
  · exact B2292819
  · exact B2292823
  · exact B2292827
  · exact B2292831
  · exact B2292835
  · exact B2292839
  · exact B2292843
  · exact B2292847
  · exact B2292851
  · exact B2292855
  · exact B2292859
  · exact B2292863
  · exact B2292867
  · exact B2292871
  · exact B2292875
  · exact B2292879
  · exact B2292883
  · exact B2292887
  · exact B2292891
  · exact B2292895
  · exact B2292899
  · exact B2292903
  · exact B2292907
  · exact B2292911
  · exact B2292915
  · exact B2292919
  · exact B2292923
  · exact B2292927
  · exact B2292931
  · exact B2292935
  · exact B2292939
  · exact B2292943
  · exact B2292947
  · exact B2292951
  · exact B2292955
  · exact B2292959
  · exact B2292963
  · exact B2292967
  · exact B2292971
  · exact B2292975
  · exact B2292979
  · exact B2292983
  · exact B2292987
  · exact B2292991
  · exact B2292995
  · exact B2292999
  · exact B2293003
  · exact B2293007
  · exact B2293011
  · exact B2293015
  · exact B2293019
  · exact B2293023
  · exact B2293027
  · exact B2293031
  · exact B2293035
  · exact B2293039
  · exact B2293043
  · exact B2293047
  · exact B2293051
  · exact B2293055
  · exact B2293059
  · exact B2293063
  · exact B2293067
  · exact B2293071
  · exact B2293075
  · exact B2293079
  · exact B2293083
  · exact B2293087
  · exact B2293091
  · exact B2293095
  · exact B2293099
  · exact B2293103
  · exact B2293107
  · exact B2293111
  · exact B2293115
  · exact B2293119
  · exact B2293123
  · exact B2293127
  · exact B2293131
  · exact B2293135
  · exact B2293139
  · exact B2293143
  · exact B2293147
  · exact B2293151
  · exact B2293155
  · exact B2293159
  · exact B2293163
  · exact B2293167
  · exact B2293171
  · exact B2293175
  · exact B2293179
  · exact B2293183
  · exact B2293187
  · exact B2293191
  · exact B2293195
  · exact B2293199
  · exact B2293203
  · exact B2293207
  · exact B2293211
  · exact B2293215
  · exact B2293219
  · exact B2293223
  · exact B2293227
  · exact B2293231
  · exact B2293235
  · exact B2293239
  · exact B2293243
  · exact B2293247
  · exact B2293251
  · exact B2293255
  · exact B2293259
  · exact B2293263
  · exact B2293267
  · exact B2293271
  · exact B2293275
  · exact B2293279
  · exact B2293283
  · exact B2293287
  · exact B2293291
  · exact B2293295
  · exact B2293299
  · exact B2293303
  · exact B2293307
  · exact B2293311
  · exact B2293315
  · exact B2293319
  · exact B2293323
  · exact B2293327
  · exact B2293331
  · exact B2293335
  · exact B2293339
  · exact B2293343
  · exact B2293347
  · exact B2293351
  · exact B2293355
  · exact B2293359
  · exact B2293363
  · exact B2293367
  · exact B2293371
  · exact B2293375
  · exact B2293379
  · exact B2293383
  · exact B2293387
  · exact B2293391
  · exact B2293395
  · exact B2293399
  · exact B2293403
  · exact B2293407
  · exact B2293411
  · exact B2293415
  · exact B2293419
  · exact B2293423
  · exact B2293427
  · exact B2293431
  · exact B2293435
theorem solution (m : ℕ) (hlo : 2291435 ≤ m) (hhi : m ≤ 2293435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 572858 ≤ j := by omega
    have hj2 : j ≤ 573358 := by omega
    have hb : Blo 2291435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
