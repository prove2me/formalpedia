-- Prove2me | solution 1 for syracuse_descends_range_2279435_2281435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:35.581926+00:00
-- url     : https://prove2.me/submissions/5d1f2c17-e2fd-49a0-a31c-c7040b0499f9

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

theorem B2564365 : Blo 2279435 2564365 := bbase (se 3 (by rfl) ⟨480818, by rfl⟩ : syracuseStep 2564365 = 961637) (by norm_num)
theorem B3419153 : Blo 2279435 3419153 := bstep (se 2 (by rfl) ⟨1282182, by rfl⟩ : syracuseStep 3419153 = 2564365) B2564365
theorem B2279435 : Blo 2279435 2279435 := bstep (se 1 (by rfl) ⟨1709576, by rfl⟩ : syracuseStep 2279435 = 3419153) B3419153
theorem B7693109 : Blo 2279435 7693109 := bbase (se 5 (by rfl) ⟨360614, by rfl⟩ : syracuseStep 7693109 = 721229) (by norm_num)
theorem B5128739 : Blo 2279435 5128739 := bstep (se 1 (by rfl) ⟨3846554, by rfl⟩ : syracuseStep 5128739 = 7693109) B7693109
theorem B3419159 : Blo 2279435 3419159 := bstep (se 1 (by rfl) ⟨2564369, by rfl⟩ : syracuseStep 3419159 = 5128739) B5128739
theorem B2279439 : Blo 2279435 2279439 := bstep (se 1 (by rfl) ⟨1709579, by rfl⟩ : syracuseStep 2279439 = 3419159) B3419159
theorem B3419165 : Blo 2279435 3419165 := bbase (se 3 (by rfl) ⟨641093, by rfl⟩ : syracuseStep 3419165 = 1282187) (by norm_num)
theorem B2279443 : Blo 2279435 2279443 := bstep (se 1 (by rfl) ⟨1709582, by rfl⟩ : syracuseStep 2279443 = 3419165) B3419165
theorem B5128757 : Blo 2279435 5128757 := bbase (se 5 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 5128757 = 480821) (by norm_num)
theorem B3419171 : Blo 2279435 3419171 := bstep (se 1 (by rfl) ⟨2564378, by rfl⟩ : syracuseStep 3419171 = 5128757) B5128757
theorem B2279447 : Blo 2279435 2279447 := bstep (se 1 (by rfl) ⟨1709585, by rfl⟩ : syracuseStep 2279447 = 3419171) B3419171
theorem B9736645 : Blo 2279435 9736645 := bbase (se 4 (by rfl) ⟨912810, by rfl⟩ : syracuseStep 9736645 = 1825621) (by norm_num)
theorem B12982193 : Blo 2279435 12982193 := bstep (se 2 (by rfl) ⟨4868322, by rfl⟩ : syracuseStep 12982193 = 9736645) B9736645
theorem B8654795 : Blo 2279435 8654795 := bstep (se 1 (by rfl) ⟨6491096, by rfl⟩ : syracuseStep 8654795 = 12982193) B12982193
theorem B5769863 : Blo 2279435 5769863 := bstep (se 1 (by rfl) ⟨4327397, by rfl⟩ : syracuseStep 5769863 = 8654795) B8654795
theorem B3846575 : Blo 2279435 3846575 := bstep (se 1 (by rfl) ⟨2884931, by rfl⟩ : syracuseStep 3846575 = 5769863) B5769863
theorem B2564383 : Blo 2279435 2564383 := bstep (se 1 (by rfl) ⟨1923287, by rfl⟩ : syracuseStep 2564383 = 3846575) B3846575
theorem B3419177 : Blo 2279435 3419177 := bstep (se 2 (by rfl) ⟨1282191, by rfl⟩ : syracuseStep 3419177 = 2564383) B2564383
theorem B2279451 : Blo 2279435 2279451 := bstep (se 1 (by rfl) ⟨1709588, by rfl⟩ : syracuseStep 2279451 = 3419177) B3419177
theorem B9736661 : Blo 2279435 9736661 := bbase (se 7 (by rfl) ⟨114101, by rfl⟩ : syracuseStep 9736661 = 228203) (by norm_num)
theorem B6491107 : Blo 2279435 6491107 := bstep (se 1 (by rfl) ⟨4868330, by rfl⟩ : syracuseStep 6491107 = 9736661) B9736661
theorem B8654809 : Blo 2279435 8654809 := bstep (se 2 (by rfl) ⟨3245553, by rfl⟩ : syracuseStep 8654809 = 6491107) B6491107
theorem B11539745 : Blo 2279435 11539745 := bstep (se 2 (by rfl) ⟨4327404, by rfl⟩ : syracuseStep 11539745 = 8654809) B8654809
theorem B7693163 : Blo 2279435 7693163 := bstep (se 1 (by rfl) ⟨5769872, by rfl⟩ : syracuseStep 7693163 = 11539745) B11539745
theorem B5128775 : Blo 2279435 5128775 := bstep (se 1 (by rfl) ⟨3846581, by rfl⟩ : syracuseStep 5128775 = 7693163) B7693163
theorem B3419183 : Blo 2279435 3419183 := bstep (se 1 (by rfl) ⟨2564387, by rfl⟩ : syracuseStep 3419183 = 5128775) B5128775
theorem B2279455 : Blo 2279435 2279455 := bstep (se 1 (by rfl) ⟨1709591, by rfl⟩ : syracuseStep 2279455 = 3419183) B3419183
theorem B3419189 : Blo 2279435 3419189 := bbase (se 5 (by rfl) ⟨160274, by rfl⟩ : syracuseStep 3419189 = 320549) (by norm_num)
theorem B2279459 : Blo 2279435 2279459 := bstep (se 1 (by rfl) ⟨1709594, by rfl⟩ : syracuseStep 2279459 = 3419189) B3419189
theorem B5769893 : Blo 2279435 5769893 := bbase (se 4 (by rfl) ⟨540927, by rfl⟩ : syracuseStep 5769893 = 1081855) (by norm_num)
theorem B3846595 : Blo 2279435 3846595 := bstep (se 1 (by rfl) ⟨2884946, by rfl⟩ : syracuseStep 3846595 = 5769893) B5769893
theorem B5128793 : Blo 2279435 5128793 := bstep (se 2 (by rfl) ⟨1923297, by rfl⟩ : syracuseStep 5128793 = 3846595) B3846595
theorem B3419195 : Blo 2279435 3419195 := bstep (se 1 (by rfl) ⟨2564396, by rfl⟩ : syracuseStep 3419195 = 5128793) B5128793
theorem B2279463 : Blo 2279435 2279463 := bstep (se 1 (by rfl) ⟨1709597, by rfl⟩ : syracuseStep 2279463 = 3419195) B3419195
theorem B2564401 : Blo 2279435 2564401 := bbase (se 2 (by rfl) ⟨961650, by rfl⟩ : syracuseStep 2564401 = 1923301) (by norm_num)
theorem B3419201 : Blo 2279435 3419201 := bstep (se 2 (by rfl) ⟨1282200, by rfl⟩ : syracuseStep 3419201 = 2564401) B2564401
theorem B2279467 : Blo 2279435 2279467 := bstep (se 1 (by rfl) ⟨1709600, by rfl⟩ : syracuseStep 2279467 = 3419201) B3419201
theorem B4868365 : Blo 2279435 4868365 := bbase (se 3 (by rfl) ⟨912818, by rfl⟩ : syracuseStep 4868365 = 1825637) (by norm_num)
theorem B6491153 : Blo 2279435 6491153 := bstep (se 2 (by rfl) ⟨2434182, by rfl⟩ : syracuseStep 6491153 = 4868365) B4868365
theorem B4327435 : Blo 2279435 4327435 := bstep (se 1 (by rfl) ⟨3245576, by rfl⟩ : syracuseStep 4327435 = 6491153) B6491153
theorem B5769913 : Blo 2279435 5769913 := bstep (se 2 (by rfl) ⟨2163717, by rfl⟩ : syracuseStep 5769913 = 4327435) B4327435
theorem B7693217 : Blo 2279435 7693217 := bstep (se 2 (by rfl) ⟨2884956, by rfl⟩ : syracuseStep 7693217 = 5769913) B5769913
theorem B5128811 : Blo 2279435 5128811 := bstep (se 1 (by rfl) ⟨3846608, by rfl⟩ : syracuseStep 5128811 = 7693217) B7693217
theorem B3419207 : Blo 2279435 3419207 := bstep (se 1 (by rfl) ⟨2564405, by rfl⟩ : syracuseStep 3419207 = 5128811) B5128811
theorem B2279471 : Blo 2279435 2279471 := bstep (se 1 (by rfl) ⟨1709603, by rfl⟩ : syracuseStep 2279471 = 3419207) B3419207
theorem B3419213 : Blo 2279435 3419213 := bbase (se 3 (by rfl) ⟨641102, by rfl⟩ : syracuseStep 3419213 = 1282205) (by norm_num)
theorem B2279475 : Blo 2279435 2279475 := bstep (se 1 (by rfl) ⟨1709606, by rfl⟩ : syracuseStep 2279475 = 3419213) B3419213
theorem B5128829 : Blo 2279435 5128829 := bbase (se 3 (by rfl) ⟨961655, by rfl⟩ : syracuseStep 5128829 = 1923311) (by norm_num)
theorem B3419219 : Blo 2279435 3419219 := bstep (se 1 (by rfl) ⟨2564414, by rfl⟩ : syracuseStep 3419219 = 5128829) B5128829
theorem B2279479 : Blo 2279435 2279479 := bstep (se 1 (by rfl) ⟨1709609, by rfl⟩ : syracuseStep 2279479 = 3419219) B3419219
theorem B3846629 : Blo 2279435 3846629 := bbase (se 4 (by rfl) ⟨360621, by rfl⟩ : syracuseStep 3846629 = 721243) (by norm_num)
theorem B2564419 : Blo 2279435 2564419 := bstep (se 1 (by rfl) ⟨1923314, by rfl⟩ : syracuseStep 2564419 = 3846629) B3846629
theorem B3419225 : Blo 2279435 3419225 := bstep (se 2 (by rfl) ⟨1282209, by rfl⟩ : syracuseStep 3419225 = 2564419) B2564419
theorem B2279483 : Blo 2279435 2279483 := bstep (se 1 (by rfl) ⟨1709612, by rfl⟩ : syracuseStep 2279483 = 3419225) B3419225
theorem B6931765 : Blo 2279435 6931765 := bbase (se 5 (by rfl) ⟨324926, by rfl⟩ : syracuseStep 6931765 = 649853) (by norm_num)
theorem B9242353 : Blo 2279435 9242353 := bstep (se 2 (by rfl) ⟨3465882, by rfl⟩ : syracuseStep 9242353 = 6931765) B6931765
theorem B12323137 : Blo 2279435 12323137 := bstep (se 2 (by rfl) ⟨4621176, by rfl⟩ : syracuseStep 12323137 = 9242353) B9242353
theorem B16430849 : Blo 2279435 16430849 := bstep (se 2 (by rfl) ⟨6161568, by rfl⟩ : syracuseStep 16430849 = 12323137) B12323137
theorem B10953899 : Blo 2279435 10953899 := bstep (se 1 (by rfl) ⟨8215424, by rfl⟩ : syracuseStep 10953899 = 16430849) B16430849
theorem B7302599 : Blo 2279435 7302599 := bstep (se 1 (by rfl) ⟨5476949, by rfl⟩ : syracuseStep 7302599 = 10953899) B10953899
theorem B4868399 : Blo 2279435 4868399 := bstep (se 1 (by rfl) ⟨3651299, by rfl⟩ : syracuseStep 4868399 = 7302599) B7302599
theorem B3245599 : Blo 2279435 3245599 := bstep (se 1 (by rfl) ⟨2434199, by rfl⟩ : syracuseStep 3245599 = 4868399) B4868399
theorem B17309861 : Blo 2279435 17309861 := bstep (se 4 (by rfl) ⟨1622799, by rfl⟩ : syracuseStep 17309861 = 3245599) B3245599
theorem B11539907 : Blo 2279435 11539907 := bstep (se 1 (by rfl) ⟨8654930, by rfl⟩ : syracuseStep 11539907 = 17309861) B17309861
theorem B7693271 : Blo 2279435 7693271 := bstep (se 1 (by rfl) ⟨5769953, by rfl⟩ : syracuseStep 7693271 = 11539907) B11539907
theorem B5128847 : Blo 2279435 5128847 := bstep (se 1 (by rfl) ⟨3846635, by rfl⟩ : syracuseStep 5128847 = 7693271) B7693271
theorem B3419231 : Blo 2279435 3419231 := bstep (se 1 (by rfl) ⟨2564423, by rfl⟩ : syracuseStep 3419231 = 5128847) B5128847
theorem B2279487 : Blo 2279435 2279487 := bstep (se 1 (by rfl) ⟨1709615, by rfl⟩ : syracuseStep 2279487 = 3419231) B3419231
theorem B3419237 : Blo 2279435 3419237 := bbase (se 4 (by rfl) ⟨320553, by rfl⟩ : syracuseStep 3419237 = 641107) (by norm_num)
theorem B2279491 : Blo 2279435 2279491 := bstep (se 1 (by rfl) ⟨1709618, by rfl⟩ : syracuseStep 2279491 = 3419237) B3419237
theorem B2738485 : Blo 2279435 2738485 := bbase (se 5 (by rfl) ⟨128366, by rfl⟩ : syracuseStep 2738485 = 256733) (by norm_num)
theorem B3651313 : Blo 2279435 3651313 := bstep (se 2 (by rfl) ⟨1369242, by rfl⟩ : syracuseStep 3651313 = 2738485) B2738485
theorem B4868417 : Blo 2279435 4868417 := bstep (se 2 (by rfl) ⟨1825656, by rfl⟩ : syracuseStep 4868417 = 3651313) B3651313
theorem B3245611 : Blo 2279435 3245611 := bstep (se 1 (by rfl) ⟨2434208, by rfl⟩ : syracuseStep 3245611 = 4868417) B4868417
theorem B4327481 : Blo 2279435 4327481 := bstep (se 2 (by rfl) ⟨1622805, by rfl⟩ : syracuseStep 4327481 = 3245611) B3245611
theorem B2884987 : Blo 2279435 2884987 := bstep (se 1 (by rfl) ⟨2163740, by rfl⟩ : syracuseStep 2884987 = 4327481) B4327481
theorem B3846649 : Blo 2279435 3846649 := bstep (se 2 (by rfl) ⟨1442493, by rfl⟩ : syracuseStep 3846649 = 2884987) B2884987
theorem B5128865 : Blo 2279435 5128865 := bstep (se 2 (by rfl) ⟨1923324, by rfl⟩ : syracuseStep 5128865 = 3846649) B3846649
theorem B3419243 : Blo 2279435 3419243 := bstep (se 1 (by rfl) ⟨2564432, by rfl⟩ : syracuseStep 3419243 = 5128865) B5128865
theorem B2279495 : Blo 2279435 2279495 := bstep (se 1 (by rfl) ⟨1709621, by rfl⟩ : syracuseStep 2279495 = 3419243) B3419243
theorem B2564437 : Blo 2279435 2564437 := bbase (se 10 (by rfl) ⟨3756, by rfl⟩ : syracuseStep 2564437 = 7513) (by norm_num)
theorem B3419249 : Blo 2279435 3419249 := bstep (se 2 (by rfl) ⟨1282218, by rfl⟩ : syracuseStep 3419249 = 2564437) B2564437
theorem B2279499 : Blo 2279435 2279499 := bstep (se 1 (by rfl) ⟨1709624, by rfl⟩ : syracuseStep 2279499 = 3419249) B3419249
theorem B2884997 : Blo 2279435 2884997 := bbase (se 4 (by rfl) ⟨270468, by rfl⟩ : syracuseStep 2884997 = 540937) (by norm_num)
theorem B7693325 : Blo 2279435 7693325 := bstep (se 3 (by rfl) ⟨1442498, by rfl⟩ : syracuseStep 7693325 = 2884997) B2884997
theorem B5128883 : Blo 2279435 5128883 := bstep (se 1 (by rfl) ⟨3846662, by rfl⟩ : syracuseStep 5128883 = 7693325) B7693325
theorem B3419255 : Blo 2279435 3419255 := bstep (se 1 (by rfl) ⟨2564441, by rfl⟩ : syracuseStep 3419255 = 5128883) B5128883
theorem B2279503 : Blo 2279435 2279503 := bstep (se 1 (by rfl) ⟨1709627, by rfl⟩ : syracuseStep 2279503 = 3419255) B3419255
theorem B3419261 : Blo 2279435 3419261 := bbase (se 3 (by rfl) ⟨641111, by rfl⟩ : syracuseStep 3419261 = 1282223) (by norm_num)
theorem B2279507 : Blo 2279435 2279507 := bstep (se 1 (by rfl) ⟨1709630, by rfl⟩ : syracuseStep 2279507 = 3419261) B3419261
theorem B5128901 : Blo 2279435 5128901 := bbase (se 4 (by rfl) ⟨480834, by rfl⟩ : syracuseStep 5128901 = 961669) (by norm_num)
theorem B3419267 : Blo 2279435 3419267 := bstep (se 1 (by rfl) ⟨2564450, by rfl⟩ : syracuseStep 3419267 = 5128901) B5128901
theorem B2279511 : Blo 2279435 2279511 := bstep (se 1 (by rfl) ⟨1709633, by rfl⟩ : syracuseStep 2279511 = 3419267) B3419267
theorem B2310617 : Blo 2279435 2310617 := bbase (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) (by norm_num)
theorem B6161645 : Blo 2279435 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B4107763 : Blo 2279435 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B21908069 : Blo 2279435 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B14605379 : Blo 2279435 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B9736919 : Blo 2279435 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B6491279 : Blo 2279435 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B4327519 : Blo 2279435 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B5770025 : Blo 2279435 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B3846683 : Blo 2279435 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B2564455 : Blo 2279435 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B3419273 : Blo 2279435 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B2279515 : Blo 2279435 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B11540069 : Blo 2279435 11540069 := bbase (se 4 (by rfl) ⟨1081881, by rfl⟩ : syracuseStep 11540069 = 2163763) (by norm_num)
theorem B7693379 : Blo 2279435 7693379 := bstep (se 1 (by rfl) ⟨5770034, by rfl⟩ : syracuseStep 7693379 = 11540069) B11540069
theorem B5128919 : Blo 2279435 5128919 := bstep (se 1 (by rfl) ⟨3846689, by rfl⟩ : syracuseStep 5128919 = 7693379) B7693379
theorem B3419279 : Blo 2279435 3419279 := bstep (se 1 (by rfl) ⟨2564459, by rfl⟩ : syracuseStep 3419279 = 5128919) B5128919
theorem B2279519 : Blo 2279435 2279519 := bstep (se 1 (by rfl) ⟨1709639, by rfl⟩ : syracuseStep 2279519 = 3419279) B3419279
theorem B3419285 : Blo 2279435 3419285 := bbase (se 6 (by rfl) ⟨80139, by rfl⟩ : syracuseStep 3419285 = 160279) (by norm_num)
theorem B2279523 : Blo 2279435 2279523 := bstep (se 1 (by rfl) ⟨1709642, by rfl⟩ : syracuseStep 2279523 = 3419285) B3419285
theorem B7798373 : Blo 2279435 7798373 := bbase (se 4 (by rfl) ⟨731097, by rfl⟩ : syracuseStep 7798373 = 1462195) (by norm_num)
theorem B5198915 : Blo 2279435 5198915 := bstep (se 1 (by rfl) ⟨3899186, by rfl⟩ : syracuseStep 5198915 = 7798373) B7798373
theorem B13863773 : Blo 2279435 13863773 := bstep (se 3 (by rfl) ⟨2599457, by rfl⟩ : syracuseStep 13863773 = 5198915) B5198915
theorem B9242515 : Blo 2279435 9242515 := bstep (se 1 (by rfl) ⟨6931886, by rfl⟩ : syracuseStep 9242515 = 13863773) B13863773
theorem B12323353 : Blo 2279435 12323353 := bstep (se 2 (by rfl) ⟨4621257, by rfl⟩ : syracuseStep 12323353 = 9242515) B9242515
theorem B16431137 : Blo 2279435 16431137 := bstep (se 2 (by rfl) ⟨6161676, by rfl⟩ : syracuseStep 16431137 = 12323353) B12323353
theorem B10954091 : Blo 2279435 10954091 := bstep (se 1 (by rfl) ⟨8215568, by rfl⟩ : syracuseStep 10954091 = 16431137) B16431137
theorem B7302727 : Blo 2279435 7302727 := bstep (se 1 (by rfl) ⟨5477045, by rfl⟩ : syracuseStep 7302727 = 10954091) B10954091
theorem B9736969 : Blo 2279435 9736969 := bstep (se 2 (by rfl) ⟨3651363, by rfl⟩ : syracuseStep 9736969 = 7302727) B7302727
theorem B12982625 : Blo 2279435 12982625 := bstep (se 2 (by rfl) ⟨4868484, by rfl⟩ : syracuseStep 12982625 = 9736969) B9736969
theorem B8655083 : Blo 2279435 8655083 := bstep (se 1 (by rfl) ⟨6491312, by rfl⟩ : syracuseStep 8655083 = 12982625) B12982625
theorem B5770055 : Blo 2279435 5770055 := bstep (se 1 (by rfl) ⟨4327541, by rfl⟩ : syracuseStep 5770055 = 8655083) B8655083
theorem B3846703 : Blo 2279435 3846703 := bstep (se 1 (by rfl) ⟨2885027, by rfl⟩ : syracuseStep 3846703 = 5770055) B5770055
theorem B5128937 : Blo 2279435 5128937 := bstep (se 2 (by rfl) ⟨1923351, by rfl⟩ : syracuseStep 5128937 = 3846703) B3846703
theorem B3419291 : Blo 2279435 3419291 := bstep (se 1 (by rfl) ⟨2564468, by rfl⟩ : syracuseStep 3419291 = 5128937) B5128937
theorem B2279527 : Blo 2279435 2279527 := bstep (se 1 (by rfl) ⟨1709645, by rfl⟩ : syracuseStep 2279527 = 3419291) B3419291
theorem B2564473 : Blo 2279435 2564473 := bbase (se 2 (by rfl) ⟨961677, by rfl⟩ : syracuseStep 2564473 = 1923355) (by norm_num)
theorem B3419297 : Blo 2279435 3419297 := bstep (se 2 (by rfl) ⟨1282236, by rfl⟩ : syracuseStep 3419297 = 2564473) B2564473
theorem B2279531 : Blo 2279435 2279531 := bstep (se 1 (by rfl) ⟨1709648, by rfl⟩ : syracuseStep 2279531 = 3419297) B3419297
theorem B2310637 : Blo 2279435 2310637 := bbase (se 3 (by rfl) ⟨433244, by rfl⟩ : syracuseStep 2310637 = 866489) (by norm_num)
theorem B3080849 : Blo 2279435 3080849 := bstep (se 2 (by rfl) ⟨1155318, by rfl⟩ : syracuseStep 3080849 = 2310637) B2310637
theorem B8215597 : Blo 2279435 8215597 := bstep (se 3 (by rfl) ⟨1540424, by rfl⟩ : syracuseStep 8215597 = 3080849) B3080849
theorem B10954129 : Blo 2279435 10954129 := bstep (se 2 (by rfl) ⟨4107798, by rfl⟩ : syracuseStep 10954129 = 8215597) B8215597
theorem B14605505 : Blo 2279435 14605505 := bstep (se 2 (by rfl) ⟨5477064, by rfl⟩ : syracuseStep 14605505 = 10954129) B10954129
theorem B9737003 : Blo 2279435 9737003 := bstep (se 1 (by rfl) ⟨7302752, by rfl⟩ : syracuseStep 9737003 = 14605505) B14605505
theorem B6491335 : Blo 2279435 6491335 := bstep (se 1 (by rfl) ⟨4868501, by rfl⟩ : syracuseStep 6491335 = 9737003) B9737003
theorem B8655113 : Blo 2279435 8655113 := bstep (se 2 (by rfl) ⟨3245667, by rfl⟩ : syracuseStep 8655113 = 6491335) B6491335
theorem B5770075 : Blo 2279435 5770075 := bstep (se 1 (by rfl) ⟨4327556, by rfl⟩ : syracuseStep 5770075 = 8655113) B8655113
theorem B7693433 : Blo 2279435 7693433 := bstep (se 2 (by rfl) ⟨2885037, by rfl⟩ : syracuseStep 7693433 = 5770075) B5770075
theorem B5128955 : Blo 2279435 5128955 := bstep (se 1 (by rfl) ⟨3846716, by rfl⟩ : syracuseStep 5128955 = 7693433) B7693433
theorem B3419303 : Blo 2279435 3419303 := bstep (se 1 (by rfl) ⟨2564477, by rfl⟩ : syracuseStep 3419303 = 5128955) B5128955
theorem B2279535 : Blo 2279435 2279535 := bstep (se 1 (by rfl) ⟨1709651, by rfl⟩ : syracuseStep 2279535 = 3419303) B3419303
theorem B3419309 : Blo 2279435 3419309 := bbase (se 3 (by rfl) ⟨641120, by rfl⟩ : syracuseStep 3419309 = 1282241) (by norm_num)
theorem B2279539 : Blo 2279435 2279539 := bstep (se 1 (by rfl) ⟨1709654, by rfl⟩ : syracuseStep 2279539 = 3419309) B3419309
theorem B5128973 : Blo 2279435 5128973 := bbase (se 3 (by rfl) ⟨961682, by rfl⟩ : syracuseStep 5128973 = 1923365) (by norm_num)
theorem B3419315 : Blo 2279435 3419315 := bstep (se 1 (by rfl) ⟨2564486, by rfl⟩ : syracuseStep 3419315 = 5128973) B5128973
theorem B2279543 : Blo 2279435 2279543 := bstep (se 1 (by rfl) ⟨1709657, by rfl⟩ : syracuseStep 2279543 = 3419315) B3419315
theorem B2885053 : Blo 2279435 2885053 := bbase (se 3 (by rfl) ⟨540947, by rfl⟩ : syracuseStep 2885053 = 1081895) (by norm_num)
theorem B3846737 : Blo 2279435 3846737 := bstep (se 2 (by rfl) ⟨1442526, by rfl⟩ : syracuseStep 3846737 = 2885053) B2885053
theorem B2564491 : Blo 2279435 2564491 := bstep (se 1 (by rfl) ⟨1923368, by rfl⟩ : syracuseStep 2564491 = 3846737) B3846737
theorem B3419321 : Blo 2279435 3419321 := bstep (se 2 (by rfl) ⟨1282245, by rfl⟩ : syracuseStep 3419321 = 2564491) B2564491
theorem B2279547 : Blo 2279435 2279547 := bstep (se 1 (by rfl) ⟨1709660, by rfl⟩ : syracuseStep 2279547 = 3419321) B3419321
theorem B2310653 : Blo 2279435 2310653 := bbase (se 3 (by rfl) ⟨433247, by rfl⟩ : syracuseStep 2310653 = 866495) (by norm_num)
theorem B6161741 : Blo 2279435 6161741 := bstep (se 3 (by rfl) ⟨1155326, by rfl⟩ : syracuseStep 6161741 = 2310653) B2310653
theorem B4107827 : Blo 2279435 4107827 := bstep (se 1 (by rfl) ⟨3080870, by rfl⟩ : syracuseStep 4107827 = 6161741) B6161741
theorem B10954205 : Blo 2279435 10954205 := bstep (se 3 (by rfl) ⟨2053913, by rfl⟩ : syracuseStep 10954205 = 4107827) B4107827
theorem B7302803 : Blo 2279435 7302803 := bstep (se 1 (by rfl) ⟨5477102, by rfl⟩ : syracuseStep 7302803 = 10954205) B10954205
theorem B19474141 : Blo 2279435 19474141 := bstep (se 3 (by rfl) ⟨3651401, by rfl⟩ : syracuseStep 19474141 = 7302803) B7302803
theorem B25965521 : Blo 2279435 25965521 := bstep (se 2 (by rfl) ⟨9737070, by rfl⟩ : syracuseStep 25965521 = 19474141) B19474141
theorem B17310347 : Blo 2279435 17310347 := bstep (se 1 (by rfl) ⟨12982760, by rfl⟩ : syracuseStep 17310347 = 25965521) B25965521
theorem B11540231 : Blo 2279435 11540231 := bstep (se 1 (by rfl) ⟨8655173, by rfl⟩ : syracuseStep 11540231 = 17310347) B17310347
theorem B7693487 : Blo 2279435 7693487 := bstep (se 1 (by rfl) ⟨5770115, by rfl⟩ : syracuseStep 7693487 = 11540231) B11540231
theorem B5128991 : Blo 2279435 5128991 := bstep (se 1 (by rfl) ⟨3846743, by rfl⟩ : syracuseStep 5128991 = 7693487) B7693487
theorem B3419327 : Blo 2279435 3419327 := bstep (se 1 (by rfl) ⟨2564495, by rfl⟩ : syracuseStep 3419327 = 5128991) B5128991
theorem B2279551 : Blo 2279435 2279551 := bstep (se 1 (by rfl) ⟨1709663, by rfl⟩ : syracuseStep 2279551 = 3419327) B3419327
theorem B3419333 : Blo 2279435 3419333 := bbase (se 4 (by rfl) ⟨320562, by rfl⟩ : syracuseStep 3419333 = 641125) (by norm_num)
theorem B2279555 : Blo 2279435 2279555 := bstep (se 1 (by rfl) ⟨1709666, by rfl⟩ : syracuseStep 2279555 = 3419333) B3419333
theorem B3846757 : Blo 2279435 3846757 := bbase (se 4 (by rfl) ⟨360633, by rfl⟩ : syracuseStep 3846757 = 721267) (by norm_num)
theorem B5129009 : Blo 2279435 5129009 := bstep (se 2 (by rfl) ⟨1923378, by rfl⟩ : syracuseStep 5129009 = 3846757) B3846757
theorem B3419339 : Blo 2279435 3419339 := bstep (se 1 (by rfl) ⟨2564504, by rfl⟩ : syracuseStep 3419339 = 5129009) B5129009
theorem B2279559 : Blo 2279435 2279559 := bstep (se 1 (by rfl) ⟨1709669, by rfl⟩ : syracuseStep 2279559 = 3419339) B3419339
theorem B2564509 : Blo 2279435 2564509 := bbase (se 3 (by rfl) ⟨480845, by rfl⟩ : syracuseStep 2564509 = 961691) (by norm_num)
theorem B3419345 : Blo 2279435 3419345 := bstep (se 2 (by rfl) ⟨1282254, by rfl⟩ : syracuseStep 3419345 = 2564509) B2564509
theorem B2279563 : Blo 2279435 2279563 := bstep (se 1 (by rfl) ⟨1709672, by rfl⟩ : syracuseStep 2279563 = 3419345) B3419345
theorem B7693541 : Blo 2279435 7693541 := bbase (se 4 (by rfl) ⟨721269, by rfl⟩ : syracuseStep 7693541 = 1442539) (by norm_num)
theorem B5129027 : Blo 2279435 5129027 := bstep (se 1 (by rfl) ⟨3846770, by rfl⟩ : syracuseStep 5129027 = 7693541) B7693541
theorem B3419351 : Blo 2279435 3419351 := bstep (se 1 (by rfl) ⟨2564513, by rfl⟩ : syracuseStep 3419351 = 5129027) B5129027
theorem B2279567 : Blo 2279435 2279567 := bstep (se 1 (by rfl) ⟨1709675, by rfl⟩ : syracuseStep 2279567 = 3419351) B3419351
theorem B3419357 : Blo 2279435 3419357 := bbase (se 3 (by rfl) ⟨641129, by rfl⟩ : syracuseStep 3419357 = 1282259) (by norm_num)
theorem B2279571 : Blo 2279435 2279571 := bstep (se 1 (by rfl) ⟨1709678, by rfl⟩ : syracuseStep 2279571 = 3419357) B3419357
theorem B5129045 : Blo 2279435 5129045 := bbase (se 9 (by rfl) ⟨15026, by rfl⟩ : syracuseStep 5129045 = 30053) (by norm_num)
theorem B3419363 : Blo 2279435 3419363 := bstep (se 1 (by rfl) ⟨2564522, by rfl⟩ : syracuseStep 3419363 = 5129045) B5129045
theorem B2279575 : Blo 2279435 2279575 := bstep (se 1 (by rfl) ⟨1709681, by rfl⟩ : syracuseStep 2279575 = 3419363) B3419363
theorem B6491461 : Blo 2279435 6491461 := bbase (se 4 (by rfl) ⟨608574, by rfl⟩ : syracuseStep 6491461 = 1217149) (by norm_num)
theorem B8655281 : Blo 2279435 8655281 := bstep (se 2 (by rfl) ⟨3245730, by rfl⟩ : syracuseStep 8655281 = 6491461) B6491461
theorem B5770187 : Blo 2279435 5770187 := bstep (se 1 (by rfl) ⟨4327640, by rfl⟩ : syracuseStep 5770187 = 8655281) B8655281
theorem B3846791 : Blo 2279435 3846791 := bstep (se 1 (by rfl) ⟨2885093, by rfl⟩ : syracuseStep 3846791 = 5770187) B5770187
theorem B2564527 : Blo 2279435 2564527 := bstep (se 1 (by rfl) ⟨1923395, by rfl⟩ : syracuseStep 2564527 = 3846791) B3846791
theorem B3419369 : Blo 2279435 3419369 := bstep (se 2 (by rfl) ⟨1282263, by rfl⟩ : syracuseStep 3419369 = 2564527) B2564527
theorem B2279579 : Blo 2279435 2279579 := bstep (se 1 (by rfl) ⟨1709684, by rfl⟩ : syracuseStep 2279579 = 3419369) B3419369
theorem B2924461 : Blo 2279435 2924461 := bbase (se 3 (by rfl) ⟨548336, by rfl⟩ : syracuseStep 2924461 = 1096673) (by norm_num)
theorem B15597125 : Blo 2279435 15597125 := bstep (se 4 (by rfl) ⟨1462230, by rfl⟩ : syracuseStep 15597125 = 2924461) B2924461
theorem B10398083 : Blo 2279435 10398083 := bstep (se 1 (by rfl) ⟨7798562, by rfl⟩ : syracuseStep 10398083 = 15597125) B15597125
theorem B110912885 : Blo 2279435 110912885 := bstep (se 5 (by rfl) ⟨5199041, by rfl⟩ : syracuseStep 110912885 = 10398083) B10398083
theorem B73941923 : Blo 2279435 73941923 := bstep (se 1 (by rfl) ⟨55456442, by rfl⟩ : syracuseStep 73941923 = 110912885) B110912885
theorem B49294615 : Blo 2279435 49294615 := bstep (se 1 (by rfl) ⟨36970961, by rfl⟩ : syracuseStep 49294615 = 73941923) B73941923
theorem B65726153 : Blo 2279435 65726153 := bstep (se 2 (by rfl) ⟨24647307, by rfl⟩ : syracuseStep 65726153 = 49294615) B49294615
theorem B43817435 : Blo 2279435 43817435 := bstep (se 1 (by rfl) ⟨32863076, by rfl⟩ : syracuseStep 43817435 = 65726153) B65726153
theorem B29211623 : Blo 2279435 29211623 := bstep (se 1 (by rfl) ⟨21908717, by rfl⟩ : syracuseStep 29211623 = 43817435) B43817435
theorem B19474415 : Blo 2279435 19474415 := bstep (se 1 (by rfl) ⟨14605811, by rfl⟩ : syracuseStep 19474415 = 29211623) B29211623
theorem B12982943 : Blo 2279435 12982943 := bstep (se 1 (by rfl) ⟨9737207, by rfl⟩ : syracuseStep 12982943 = 19474415) B19474415
theorem B8655295 : Blo 2279435 8655295 := bstep (se 1 (by rfl) ⟨6491471, by rfl⟩ : syracuseStep 8655295 = 12982943) B12982943
theorem B11540393 : Blo 2279435 11540393 := bstep (se 2 (by rfl) ⟨4327647, by rfl⟩ : syracuseStep 11540393 = 8655295) B8655295
theorem B7693595 : Blo 2279435 7693595 := bstep (se 1 (by rfl) ⟨5770196, by rfl⟩ : syracuseStep 7693595 = 11540393) B11540393
theorem B5129063 : Blo 2279435 5129063 := bstep (se 1 (by rfl) ⟨3846797, by rfl⟩ : syracuseStep 5129063 = 7693595) B7693595
theorem B3419375 : Blo 2279435 3419375 := bstep (se 1 (by rfl) ⟨2564531, by rfl⟩ : syracuseStep 3419375 = 5129063) B5129063
theorem B2279583 : Blo 2279435 2279583 := bstep (se 1 (by rfl) ⟨1709687, by rfl⟩ : syracuseStep 2279583 = 3419375) B3419375
theorem B3419381 : Blo 2279435 3419381 := bbase (se 5 (by rfl) ⟨160283, by rfl⟩ : syracuseStep 3419381 = 320567) (by norm_num)
theorem B2279587 : Blo 2279435 2279587 := bstep (se 1 (by rfl) ⟨1709690, by rfl⟩ : syracuseStep 2279587 = 3419381) B3419381
theorem B10539989 : Blo 2279435 10539989 := bbase (se 7 (by rfl) ⟨123515, by rfl⟩ : syracuseStep 10539989 = 247031) (by norm_num)
theorem B7026659 : Blo 2279435 7026659 := bstep (se 1 (by rfl) ⟨5269994, by rfl⟩ : syracuseStep 7026659 = 10539989) B10539989
theorem B4684439 : Blo 2279435 4684439 := bstep (se 1 (by rfl) ⟨3513329, by rfl⟩ : syracuseStep 4684439 = 7026659) B7026659
theorem B12491837 : Blo 2279435 12491837 := bstep (se 3 (by rfl) ⟨2342219, by rfl⟩ : syracuseStep 12491837 = 4684439) B4684439
theorem B8327891 : Blo 2279435 8327891 := bstep (se 1 (by rfl) ⟨6245918, by rfl⟩ : syracuseStep 8327891 = 12491837) B12491837
theorem B5551927 : Blo 2279435 5551927 := bstep (se 1 (by rfl) ⟨4163945, by rfl⟩ : syracuseStep 5551927 = 8327891) B8327891
theorem B118441109 : Blo 2279435 118441109 := bstep (se 6 (by rfl) ⟨2775963, by rfl⟩ : syracuseStep 118441109 = 5551927) B5551927
theorem B78960739 : Blo 2279435 78960739 := bstep (se 1 (by rfl) ⟨59220554, by rfl⟩ : syracuseStep 78960739 = 118441109) B118441109
theorem B105280985 : Blo 2279435 105280985 := bstep (se 2 (by rfl) ⟨39480369, by rfl⟩ : syracuseStep 105280985 = 78960739) B78960739
theorem B70187323 : Blo 2279435 70187323 := bstep (se 1 (by rfl) ⟨52640492, by rfl⟩ : syracuseStep 70187323 = 105280985) B105280985
theorem B93583097 : Blo 2279435 93583097 := bstep (se 2 (by rfl) ⟨35093661, by rfl⟩ : syracuseStep 93583097 = 70187323) B70187323
theorem B62388731 : Blo 2279435 62388731 := bstep (se 1 (by rfl) ⟨46791548, by rfl⟩ : syracuseStep 62388731 = 93583097) B93583097
theorem B41592487 : Blo 2279435 41592487 := bstep (se 1 (by rfl) ⟨31194365, by rfl⟩ : syracuseStep 41592487 = 62388731) B62388731
theorem B55456649 : Blo 2279435 55456649 := bstep (se 2 (by rfl) ⟨20796243, by rfl⟩ : syracuseStep 55456649 = 41592487) B41592487
theorem B36971099 : Blo 2279435 36971099 := bstep (se 1 (by rfl) ⟨27728324, by rfl⟩ : syracuseStep 36971099 = 55456649) B55456649
theorem B24647399 : Blo 2279435 24647399 := bstep (se 1 (by rfl) ⟨18485549, by rfl⟩ : syracuseStep 24647399 = 36971099) B36971099
theorem B16431599 : Blo 2279435 16431599 := bstep (se 1 (by rfl) ⟨12323699, by rfl⟩ : syracuseStep 16431599 = 24647399) B24647399
theorem B10954399 : Blo 2279435 10954399 := bstep (se 1 (by rfl) ⟨8215799, by rfl⟩ : syracuseStep 10954399 = 16431599) B16431599
theorem B14605865 : Blo 2279435 14605865 := bstep (se 2 (by rfl) ⟨5477199, by rfl⟩ : syracuseStep 14605865 = 10954399) B10954399
theorem B9737243 : Blo 2279435 9737243 := bstep (se 1 (by rfl) ⟨7302932, by rfl⟩ : syracuseStep 9737243 = 14605865) B14605865
theorem B6491495 : Blo 2279435 6491495 := bstep (se 1 (by rfl) ⟨4868621, by rfl⟩ : syracuseStep 6491495 = 9737243) B9737243
theorem B4327663 : Blo 2279435 4327663 := bstep (se 1 (by rfl) ⟨3245747, by rfl⟩ : syracuseStep 4327663 = 6491495) B6491495
theorem B5770217 : Blo 2279435 5770217 := bstep (se 2 (by rfl) ⟨2163831, by rfl⟩ : syracuseStep 5770217 = 4327663) B4327663
theorem B3846811 : Blo 2279435 3846811 := bstep (se 1 (by rfl) ⟨2885108, by rfl⟩ : syracuseStep 3846811 = 5770217) B5770217
theorem B5129081 : Blo 2279435 5129081 := bstep (se 2 (by rfl) ⟨1923405, by rfl⟩ : syracuseStep 5129081 = 3846811) B3846811
theorem B3419387 : Blo 2279435 3419387 := bstep (se 1 (by rfl) ⟨2564540, by rfl⟩ : syracuseStep 3419387 = 5129081) B5129081
theorem B2279591 : Blo 2279435 2279591 := bstep (se 1 (by rfl) ⟨1709693, by rfl⟩ : syracuseStep 2279591 = 3419387) B3419387
theorem B2564545 : Blo 2279435 2564545 := bbase (se 2 (by rfl) ⟨961704, by rfl⟩ : syracuseStep 2564545 = 1923409) (by norm_num)
theorem B3419393 : Blo 2279435 3419393 := bstep (se 2 (by rfl) ⟨1282272, by rfl⟩ : syracuseStep 3419393 = 2564545) B2564545
theorem B2279595 : Blo 2279435 2279595 := bstep (se 1 (by rfl) ⟨1709696, by rfl⟩ : syracuseStep 2279595 = 3419393) B3419393
theorem B5770237 : Blo 2279435 5770237 := bbase (se 3 (by rfl) ⟨1081919, by rfl⟩ : syracuseStep 5770237 = 2163839) (by norm_num)
theorem B7693649 : Blo 2279435 7693649 := bstep (se 2 (by rfl) ⟨2885118, by rfl⟩ : syracuseStep 7693649 = 5770237) B5770237
theorem B5129099 : Blo 2279435 5129099 := bstep (se 1 (by rfl) ⟨3846824, by rfl⟩ : syracuseStep 5129099 = 7693649) B7693649
theorem B3419399 : Blo 2279435 3419399 := bstep (se 1 (by rfl) ⟨2564549, by rfl⟩ : syracuseStep 3419399 = 5129099) B5129099
theorem B2279599 : Blo 2279435 2279599 := bstep (se 1 (by rfl) ⟨1709699, by rfl⟩ : syracuseStep 2279599 = 3419399) B3419399
theorem B3419405 : Blo 2279435 3419405 := bbase (se 3 (by rfl) ⟨641138, by rfl⟩ : syracuseStep 3419405 = 1282277) (by norm_num)
theorem B2279603 : Blo 2279435 2279603 := bstep (se 1 (by rfl) ⟨1709702, by rfl⟩ : syracuseStep 2279603 = 3419405) B3419405
theorem B5129117 : Blo 2279435 5129117 := bbase (se 3 (by rfl) ⟨961709, by rfl⟩ : syracuseStep 5129117 = 1923419) (by norm_num)
theorem B3419411 : Blo 2279435 3419411 := bstep (se 1 (by rfl) ⟨2564558, by rfl⟩ : syracuseStep 3419411 = 5129117) B5129117
theorem B2279607 : Blo 2279435 2279607 := bstep (se 1 (by rfl) ⟨1709705, by rfl⟩ : syracuseStep 2279607 = 3419411) B3419411
theorem B3846845 : Blo 2279435 3846845 := bbase (se 3 (by rfl) ⟨721283, by rfl⟩ : syracuseStep 3846845 = 1442567) (by norm_num)
theorem B2564563 : Blo 2279435 2564563 := bstep (se 1 (by rfl) ⟨1923422, by rfl⟩ : syracuseStep 2564563 = 3846845) B3846845
theorem B3419417 : Blo 2279435 3419417 := bstep (se 2 (by rfl) ⟨1282281, by rfl⟩ : syracuseStep 3419417 = 2564563) B2564563
theorem B2279611 : Blo 2279435 2279611 := bstep (se 1 (by rfl) ⟨1709708, by rfl⟩ : syracuseStep 2279611 = 3419417) B3419417
theorem B12983125 : Blo 2279435 12983125 := bbase (se 9 (by rfl) ⟨38036, by rfl⟩ : syracuseStep 12983125 = 76073) (by norm_num)
theorem B17310833 : Blo 2279435 17310833 := bstep (se 2 (by rfl) ⟨6491562, by rfl⟩ : syracuseStep 17310833 = 12983125) B12983125
theorem B11540555 : Blo 2279435 11540555 := bstep (se 1 (by rfl) ⟨8655416, by rfl⟩ : syracuseStep 11540555 = 17310833) B17310833
theorem B7693703 : Blo 2279435 7693703 := bstep (se 1 (by rfl) ⟨5770277, by rfl⟩ : syracuseStep 7693703 = 11540555) B11540555
theorem B5129135 : Blo 2279435 5129135 := bstep (se 1 (by rfl) ⟨3846851, by rfl⟩ : syracuseStep 5129135 = 7693703) B7693703
theorem B3419423 : Blo 2279435 3419423 := bstep (se 1 (by rfl) ⟨2564567, by rfl⟩ : syracuseStep 3419423 = 5129135) B5129135
theorem B2279615 : Blo 2279435 2279615 := bstep (se 1 (by rfl) ⟨1709711, by rfl⟩ : syracuseStep 2279615 = 3419423) B3419423
theorem B3419429 : Blo 2279435 3419429 := bbase (se 4 (by rfl) ⟨320571, by rfl⟩ : syracuseStep 3419429 = 641143) (by norm_num)
theorem B2279619 : Blo 2279435 2279619 := bstep (se 1 (by rfl) ⟨1709714, by rfl⟩ : syracuseStep 2279619 = 3419429) B3419429
theorem B2885149 : Blo 2279435 2885149 := bbase (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) (by norm_num)
theorem B3846865 : Blo 2279435 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B5129153 : Blo 2279435 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B3419435 : Blo 2279435 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B2279623 : Blo 2279435 2279623 := bstep (se 1 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 2279623 = 3419435) B3419435
theorem B2564581 : Blo 2279435 2564581 := bbase (se 4 (by rfl) ⟨240429, by rfl⟩ : syracuseStep 2564581 = 480859) (by norm_num)
theorem B3419441 : Blo 2279435 3419441 := bstep (se 2 (by rfl) ⟨1282290, by rfl⟩ : syracuseStep 3419441 = 2564581) B2564581
theorem B2279627 : Blo 2279435 2279627 := bstep (se 1 (by rfl) ⟨1709720, by rfl⟩ : syracuseStep 2279627 = 3419441) B3419441
theorem B7303061 : Blo 2279435 7303061 := bbase (se 6 (by rfl) ⟨171165, by rfl⟩ : syracuseStep 7303061 = 342331) (by norm_num)
theorem B4868707 : Blo 2279435 4868707 := bstep (se 1 (by rfl) ⟨3651530, by rfl⟩ : syracuseStep 4868707 = 7303061) B7303061
theorem B6491609 : Blo 2279435 6491609 := bstep (se 2 (by rfl) ⟨2434353, by rfl⟩ : syracuseStep 6491609 = 4868707) B4868707
theorem B4327739 : Blo 2279435 4327739 := bstep (se 1 (by rfl) ⟨3245804, by rfl⟩ : syracuseStep 4327739 = 6491609) B6491609
theorem B2885159 : Blo 2279435 2885159 := bstep (se 1 (by rfl) ⟨2163869, by rfl⟩ : syracuseStep 2885159 = 4327739) B4327739
theorem B7693757 : Blo 2279435 7693757 := bstep (se 3 (by rfl) ⟨1442579, by rfl⟩ : syracuseStep 7693757 = 2885159) B2885159
theorem B5129171 : Blo 2279435 5129171 := bstep (se 1 (by rfl) ⟨3846878, by rfl⟩ : syracuseStep 5129171 = 7693757) B7693757
theorem B3419447 : Blo 2279435 3419447 := bstep (se 1 (by rfl) ⟨2564585, by rfl⟩ : syracuseStep 3419447 = 5129171) B5129171
theorem B2279631 : Blo 2279435 2279631 := bstep (se 1 (by rfl) ⟨1709723, by rfl⟩ : syracuseStep 2279631 = 3419447) B3419447
theorem B3419453 : Blo 2279435 3419453 := bbase (se 3 (by rfl) ⟨641147, by rfl⟩ : syracuseStep 3419453 = 1282295) (by norm_num)
theorem B2279635 : Blo 2279435 2279635 := bstep (se 1 (by rfl) ⟨1709726, by rfl⟩ : syracuseStep 2279635 = 3419453) B3419453
theorem B5129189 : Blo 2279435 5129189 := bbase (se 4 (by rfl) ⟨480861, by rfl⟩ : syracuseStep 5129189 = 961723) (by norm_num)
theorem B3419459 : Blo 2279435 3419459 := bstep (se 1 (by rfl) ⟨2564594, by rfl⟩ : syracuseStep 3419459 = 5129189) B5129189
theorem B2279639 : Blo 2279435 2279639 := bstep (se 1 (by rfl) ⟨1709729, by rfl⟩ : syracuseStep 2279639 = 3419459) B3419459
theorem B5770349 : Blo 2279435 5770349 := bbase (se 3 (by rfl) ⟨1081940, by rfl⟩ : syracuseStep 5770349 = 2163881) (by norm_num)
theorem B3846899 : Blo 2279435 3846899 := bstep (se 1 (by rfl) ⟨2885174, by rfl⟩ : syracuseStep 3846899 = 5770349) B5770349
theorem B2564599 : Blo 2279435 2564599 := bstep (se 1 (by rfl) ⟨1923449, by rfl⟩ : syracuseStep 2564599 = 3846899) B3846899
theorem B3419465 : Blo 2279435 3419465 := bstep (se 2 (by rfl) ⟨1282299, by rfl⟩ : syracuseStep 3419465 = 2564599) B2564599
theorem B2279643 : Blo 2279435 2279643 := bstep (se 1 (by rfl) ⟨1709732, by rfl⟩ : syracuseStep 2279643 = 3419465) B3419465
theorem B4868741 : Blo 2279435 4868741 := bbase (se 4 (by rfl) ⟨456444, by rfl⟩ : syracuseStep 4868741 = 912889) (by norm_num)
theorem B3245827 : Blo 2279435 3245827 := bstep (se 1 (by rfl) ⟨2434370, by rfl⟩ : syracuseStep 3245827 = 4868741) B4868741
theorem B4327769 : Blo 2279435 4327769 := bstep (se 2 (by rfl) ⟨1622913, by rfl⟩ : syracuseStep 4327769 = 3245827) B3245827
theorem B11540717 : Blo 2279435 11540717 := bstep (se 3 (by rfl) ⟨2163884, by rfl⟩ : syracuseStep 11540717 = 4327769) B4327769
theorem B7693811 : Blo 2279435 7693811 := bstep (se 1 (by rfl) ⟨5770358, by rfl⟩ : syracuseStep 7693811 = 11540717) B11540717
theorem B5129207 : Blo 2279435 5129207 := bstep (se 1 (by rfl) ⟨3846905, by rfl⟩ : syracuseStep 5129207 = 7693811) B7693811
theorem B3419471 : Blo 2279435 3419471 := bstep (se 1 (by rfl) ⟨2564603, by rfl⟩ : syracuseStep 3419471 = 5129207) B5129207
theorem B2279647 : Blo 2279435 2279647 := bstep (se 1 (by rfl) ⟨1709735, by rfl⟩ : syracuseStep 2279647 = 3419471) B3419471
theorem B3419477 : Blo 2279435 3419477 := bbase (se 11 (by rfl) ⟨2504, by rfl⟩ : syracuseStep 3419477 = 5009) (by norm_num)
theorem B2279651 : Blo 2279435 2279651 := bstep (se 1 (by rfl) ⟨1709738, by rfl⟩ : syracuseStep 2279651 = 3419477) B3419477
theorem B2738677 : Blo 2279435 2738677 := bbase (se 5 (by rfl) ⟨128375, by rfl⟩ : syracuseStep 2738677 = 256751) (by norm_num)
theorem B3651569 : Blo 2279435 3651569 := bstep (se 2 (by rfl) ⟨1369338, by rfl⟩ : syracuseStep 3651569 = 2738677) B2738677
theorem B2434379 : Blo 2279435 2434379 := bstep (se 1 (by rfl) ⟨1825784, by rfl⟩ : syracuseStep 2434379 = 3651569) B3651569
theorem B6491677 : Blo 2279435 6491677 := bstep (se 3 (by rfl) ⟨1217189, by rfl⟩ : syracuseStep 6491677 = 2434379) B2434379
theorem B8655569 : Blo 2279435 8655569 := bstep (se 2 (by rfl) ⟨3245838, by rfl⟩ : syracuseStep 8655569 = 6491677) B6491677
theorem B5770379 : Blo 2279435 5770379 := bstep (se 1 (by rfl) ⟨4327784, by rfl⟩ : syracuseStep 5770379 = 8655569) B8655569
theorem B3846919 : Blo 2279435 3846919 := bstep (se 1 (by rfl) ⟨2885189, by rfl⟩ : syracuseStep 3846919 = 5770379) B5770379
theorem B5129225 : Blo 2279435 5129225 := bstep (se 2 (by rfl) ⟨1923459, by rfl⟩ : syracuseStep 5129225 = 3846919) B3846919
theorem B3419483 : Blo 2279435 3419483 := bstep (se 1 (by rfl) ⟨2564612, by rfl⟩ : syracuseStep 3419483 = 5129225) B5129225
theorem B2279655 : Blo 2279435 2279655 := bstep (se 1 (by rfl) ⟨1709741, by rfl⟩ : syracuseStep 2279655 = 3419483) B3419483
theorem B2564617 : Blo 2279435 2564617 := bbase (se 2 (by rfl) ⟨961731, by rfl⟩ : syracuseStep 2564617 = 1923463) (by norm_num)
theorem B3419489 : Blo 2279435 3419489 := bstep (se 2 (by rfl) ⟨1282308, by rfl⟩ : syracuseStep 3419489 = 2564617) B2564617
theorem B2279659 : Blo 2279435 2279659 := bstep (se 1 (by rfl) ⟨1709744, by rfl⟩ : syracuseStep 2279659 = 3419489) B3419489
theorem B4164077 : Blo 2279435 4164077 := bbase (se 3 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 4164077 = 1561529) (by norm_num)
theorem B2776051 : Blo 2279435 2776051 := bstep (se 1 (by rfl) ⟨2082038, by rfl⟩ : syracuseStep 2776051 = 4164077) B4164077
theorem B14805605 : Blo 2279435 14805605 := bstep (se 4 (by rfl) ⟨1388025, by rfl⟩ : syracuseStep 14805605 = 2776051) B2776051
theorem B9870403 : Blo 2279435 9870403 := bstep (se 1 (by rfl) ⟨7402802, by rfl⟩ : syracuseStep 9870403 = 14805605) B14805605
theorem B13160537 : Blo 2279435 13160537 := bstep (se 2 (by rfl) ⟨4935201, by rfl⟩ : syracuseStep 13160537 = 9870403) B9870403
theorem B8773691 : Blo 2279435 8773691 := bstep (se 1 (by rfl) ⟨6580268, by rfl⟩ : syracuseStep 8773691 = 13160537) B13160537
theorem B23396509 : Blo 2279435 23396509 := bstep (se 3 (by rfl) ⟨4386845, by rfl⟩ : syracuseStep 23396509 = 8773691) B8773691
theorem B124781381 : Blo 2279435 124781381 := bstep (se 4 (by rfl) ⟨11698254, by rfl⟩ : syracuseStep 124781381 = 23396509) B23396509
theorem B83187587 : Blo 2279435 83187587 := bstep (se 1 (by rfl) ⟨62390690, by rfl⟩ : syracuseStep 83187587 = 124781381) B124781381
theorem B55458391 : Blo 2279435 55458391 := bstep (se 1 (by rfl) ⟨41593793, by rfl⟩ : syracuseStep 55458391 = 83187587) B83187587
theorem B73944521 : Blo 2279435 73944521 := bstep (se 2 (by rfl) ⟨27729195, by rfl⟩ : syracuseStep 73944521 = 55458391) B55458391
theorem B49296347 : Blo 2279435 49296347 := bstep (se 1 (by rfl) ⟨36972260, by rfl⟩ : syracuseStep 49296347 = 73944521) B73944521
theorem B32864231 : Blo 2279435 32864231 := bstep (se 1 (by rfl) ⟨24648173, by rfl⟩ : syracuseStep 32864231 = 49296347) B49296347
theorem B21909487 : Blo 2279435 21909487 := bstep (se 1 (by rfl) ⟨16432115, by rfl⟩ : syracuseStep 21909487 = 32864231) B32864231
theorem B29212649 : Blo 2279435 29212649 := bstep (se 2 (by rfl) ⟨10954743, by rfl⟩ : syracuseStep 29212649 = 21909487) B21909487
theorem B19475099 : Blo 2279435 19475099 := bstep (se 1 (by rfl) ⟨14606324, by rfl⟩ : syracuseStep 19475099 = 29212649) B29212649
theorem B12983399 : Blo 2279435 12983399 := bstep (se 1 (by rfl) ⟨9737549, by rfl⟩ : syracuseStep 12983399 = 19475099) B19475099
theorem B8655599 : Blo 2279435 8655599 := bstep (se 1 (by rfl) ⟨6491699, by rfl⟩ : syracuseStep 8655599 = 12983399) B12983399
theorem B5770399 : Blo 2279435 5770399 := bstep (se 1 (by rfl) ⟨4327799, by rfl⟩ : syracuseStep 5770399 = 8655599) B8655599
theorem B7693865 : Blo 2279435 7693865 := bstep (se 2 (by rfl) ⟨2885199, by rfl⟩ : syracuseStep 7693865 = 5770399) B5770399
theorem B5129243 : Blo 2279435 5129243 := bstep (se 1 (by rfl) ⟨3846932, by rfl⟩ : syracuseStep 5129243 = 7693865) B7693865
theorem B3419495 : Blo 2279435 3419495 := bstep (se 1 (by rfl) ⟨2564621, by rfl⟩ : syracuseStep 3419495 = 5129243) B5129243
theorem B2279663 : Blo 2279435 2279663 := bstep (se 1 (by rfl) ⟨1709747, by rfl⟩ : syracuseStep 2279663 = 3419495) B3419495
theorem B3419501 : Blo 2279435 3419501 := bbase (se 3 (by rfl) ⟨641156, by rfl⟩ : syracuseStep 3419501 = 1282313) (by norm_num)
theorem B2279667 : Blo 2279435 2279667 := bstep (se 1 (by rfl) ⟨1709750, by rfl⟩ : syracuseStep 2279667 = 3419501) B3419501
theorem B5129261 : Blo 2279435 5129261 := bbase (se 3 (by rfl) ⟨961736, by rfl⟩ : syracuseStep 5129261 = 1923473) (by norm_num)
theorem B3419507 : Blo 2279435 3419507 := bstep (se 1 (by rfl) ⟨2564630, by rfl⟩ : syracuseStep 3419507 = 5129261) B5129261
theorem B2279671 : Blo 2279435 2279671 := bstep (se 1 (by rfl) ⟨1709753, by rfl⟩ : syracuseStep 2279671 = 3419507) B3419507
theorem B2738701 : Blo 2279435 2738701 := bbase (se 3 (by rfl) ⟨513506, by rfl⟩ : syracuseStep 2738701 = 1027013) (by norm_num)
theorem B14606405 : Blo 2279435 14606405 := bstep (se 4 (by rfl) ⟨1369350, by rfl⟩ : syracuseStep 14606405 = 2738701) B2738701
theorem B9737603 : Blo 2279435 9737603 := bstep (se 1 (by rfl) ⟨7303202, by rfl⟩ : syracuseStep 9737603 = 14606405) B14606405
theorem B6491735 : Blo 2279435 6491735 := bstep (se 1 (by rfl) ⟨4868801, by rfl⟩ : syracuseStep 6491735 = 9737603) B9737603
theorem B4327823 : Blo 2279435 4327823 := bstep (se 1 (by rfl) ⟨3245867, by rfl⟩ : syracuseStep 4327823 = 6491735) B6491735
theorem B2885215 : Blo 2279435 2885215 := bstep (se 1 (by rfl) ⟨2163911, by rfl⟩ : syracuseStep 2885215 = 4327823) B4327823
theorem B3846953 : Blo 2279435 3846953 := bstep (se 2 (by rfl) ⟨1442607, by rfl⟩ : syracuseStep 3846953 = 2885215) B2885215
theorem B2564635 : Blo 2279435 2564635 := bstep (se 1 (by rfl) ⟨1923476, by rfl⟩ : syracuseStep 2564635 = 3846953) B3846953
theorem B3419513 : Blo 2279435 3419513 := bstep (se 2 (by rfl) ⟨1282317, by rfl⟩ : syracuseStep 3419513 = 2564635) B2564635
theorem B2279675 : Blo 2279435 2279675 := bstep (se 1 (by rfl) ⟨1709756, by rfl⟩ : syracuseStep 2279675 = 3419513) B3419513
theorem B2738705 : Blo 2279435 2738705 := bbase (se 2 (by rfl) ⟨1027014, by rfl⟩ : syracuseStep 2738705 = 2054029) (by norm_num)
theorem B7303213 : Blo 2279435 7303213 := bstep (se 3 (by rfl) ⟨1369352, by rfl⟩ : syracuseStep 7303213 = 2738705) B2738705
theorem B38950469 : Blo 2279435 38950469 := bstep (se 4 (by rfl) ⟨3651606, by rfl⟩ : syracuseStep 38950469 = 7303213) B7303213
theorem B25966979 : Blo 2279435 25966979 := bstep (se 1 (by rfl) ⟨19475234, by rfl⟩ : syracuseStep 25966979 = 38950469) B38950469
theorem B17311319 : Blo 2279435 17311319 := bstep (se 1 (by rfl) ⟨12983489, by rfl⟩ : syracuseStep 17311319 = 25966979) B25966979
theorem B11540879 : Blo 2279435 11540879 := bstep (se 1 (by rfl) ⟨8655659, by rfl⟩ : syracuseStep 11540879 = 17311319) B17311319
theorem B7693919 : Blo 2279435 7693919 := bstep (se 1 (by rfl) ⟨5770439, by rfl⟩ : syracuseStep 7693919 = 11540879) B11540879
theorem B5129279 : Blo 2279435 5129279 := bstep (se 1 (by rfl) ⟨3846959, by rfl⟩ : syracuseStep 5129279 = 7693919) B7693919
theorem B3419519 : Blo 2279435 3419519 := bstep (se 1 (by rfl) ⟨2564639, by rfl⟩ : syracuseStep 3419519 = 5129279) B5129279
theorem B2279679 : Blo 2279435 2279679 := bstep (se 1 (by rfl) ⟨1709759, by rfl⟩ : syracuseStep 2279679 = 3419519) B3419519
theorem B3419525 : Blo 2279435 3419525 := bbase (se 4 (by rfl) ⟨320580, by rfl⟩ : syracuseStep 3419525 = 641161) (by norm_num)
theorem B2279683 : Blo 2279435 2279683 := bstep (se 1 (by rfl) ⟨1709762, by rfl⟩ : syracuseStep 2279683 = 3419525) B3419525
theorem B3846973 : Blo 2279435 3846973 := bbase (se 3 (by rfl) ⟨721307, by rfl⟩ : syracuseStep 3846973 = 1442615) (by norm_num)
theorem B5129297 : Blo 2279435 5129297 := bstep (se 2 (by rfl) ⟨1923486, by rfl⟩ : syracuseStep 5129297 = 3846973) B3846973
theorem B3419531 : Blo 2279435 3419531 := bstep (se 1 (by rfl) ⟨2564648, by rfl⟩ : syracuseStep 3419531 = 5129297) B5129297
theorem B2279687 : Blo 2279435 2279687 := bstep (se 1 (by rfl) ⟨1709765, by rfl⟩ : syracuseStep 2279687 = 3419531) B3419531
theorem B2564653 : Blo 2279435 2564653 := bbase (se 3 (by rfl) ⟨480872, by rfl⟩ : syracuseStep 2564653 = 961745) (by norm_num)
theorem B3419537 : Blo 2279435 3419537 := bstep (se 2 (by rfl) ⟨1282326, by rfl⟩ : syracuseStep 3419537 = 2564653) B2564653
theorem B2279691 : Blo 2279435 2279691 := bstep (se 1 (by rfl) ⟨1709768, by rfl⟩ : syracuseStep 2279691 = 3419537) B3419537
theorem B7693973 : Blo 2279435 7693973 := bbase (se 6 (by rfl) ⟨180327, by rfl⟩ : syracuseStep 7693973 = 360655) (by norm_num)
theorem B5129315 : Blo 2279435 5129315 := bstep (se 1 (by rfl) ⟨3846986, by rfl⟩ : syracuseStep 5129315 = 7693973) B7693973
theorem B3419543 : Blo 2279435 3419543 := bstep (se 1 (by rfl) ⟨2564657, by rfl⟩ : syracuseStep 3419543 = 5129315) B5129315
theorem B2279695 : Blo 2279435 2279695 := bstep (se 1 (by rfl) ⟨1709771, by rfl⟩ : syracuseStep 2279695 = 3419543) B3419543
theorem B3419549 : Blo 2279435 3419549 := bbase (se 3 (by rfl) ⟨641165, by rfl⟩ : syracuseStep 3419549 = 1282331) (by norm_num)
theorem B2279699 : Blo 2279435 2279699 := bstep (se 1 (by rfl) ⟨1709774, by rfl⟩ : syracuseStep 2279699 = 3419549) B3419549
theorem B5129333 : Blo 2279435 5129333 := bbase (se 5 (by rfl) ⟨240437, by rfl⟩ : syracuseStep 5129333 = 480875) (by norm_num)
theorem B3419555 : Blo 2279435 3419555 := bstep (se 1 (by rfl) ⟨2564666, by rfl⟩ : syracuseStep 3419555 = 5129333) B5129333
theorem B2279703 : Blo 2279435 2279703 := bstep (se 1 (by rfl) ⟨1709777, by rfl⟩ : syracuseStep 2279703 = 3419555) B3419555
theorem B19475477 : Blo 2279435 19475477 := bbase (se 6 (by rfl) ⟨456456, by rfl⟩ : syracuseStep 19475477 = 912913) (by norm_num)
theorem B12983651 : Blo 2279435 12983651 := bstep (se 1 (by rfl) ⟨9737738, by rfl⟩ : syracuseStep 12983651 = 19475477) B19475477
theorem B8655767 : Blo 2279435 8655767 := bstep (se 1 (by rfl) ⟨6491825, by rfl⟩ : syracuseStep 8655767 = 12983651) B12983651
theorem B5770511 : Blo 2279435 5770511 := bstep (se 1 (by rfl) ⟨4327883, by rfl⟩ : syracuseStep 5770511 = 8655767) B8655767
theorem B3847007 : Blo 2279435 3847007 := bstep (se 1 (by rfl) ⟨2885255, by rfl⟩ : syracuseStep 3847007 = 5770511) B5770511
theorem B2564671 : Blo 2279435 2564671 := bstep (se 1 (by rfl) ⟨1923503, by rfl⟩ : syracuseStep 2564671 = 3847007) B3847007
theorem B3419561 : Blo 2279435 3419561 := bstep (se 2 (by rfl) ⟨1282335, by rfl⟩ : syracuseStep 3419561 = 2564671) B2564671
theorem B2279707 : Blo 2279435 2279707 := bstep (se 1 (by rfl) ⟨1709780, by rfl⟩ : syracuseStep 2279707 = 3419561) B3419561
theorem B8655781 : Blo 2279435 8655781 := bbase (se 4 (by rfl) ⟨811479, by rfl⟩ : syracuseStep 8655781 = 1622959) (by norm_num)
theorem B11541041 : Blo 2279435 11541041 := bstep (se 2 (by rfl) ⟨4327890, by rfl⟩ : syracuseStep 11541041 = 8655781) B8655781
theorem B7694027 : Blo 2279435 7694027 := bstep (se 1 (by rfl) ⟨5770520, by rfl⟩ : syracuseStep 7694027 = 11541041) B11541041
theorem B5129351 : Blo 2279435 5129351 := bstep (se 1 (by rfl) ⟨3847013, by rfl⟩ : syracuseStep 5129351 = 7694027) B7694027
theorem B3419567 : Blo 2279435 3419567 := bstep (se 1 (by rfl) ⟨2564675, by rfl⟩ : syracuseStep 3419567 = 5129351) B5129351
theorem B2279711 : Blo 2279435 2279711 := bstep (se 1 (by rfl) ⟨1709783, by rfl⟩ : syracuseStep 2279711 = 3419567) B3419567
theorem B3419573 : Blo 2279435 3419573 := bbase (se 5 (by rfl) ⟨160292, by rfl⟩ : syracuseStep 3419573 = 320585) (by norm_num)
theorem B2279715 : Blo 2279435 2279715 := bstep (se 1 (by rfl) ⟨1709786, by rfl⟩ : syracuseStep 2279715 = 3419573) B3419573
theorem B5770541 : Blo 2279435 5770541 := bbase (se 3 (by rfl) ⟨1081976, by rfl⟩ : syracuseStep 5770541 = 2163953) (by norm_num)
theorem B3847027 : Blo 2279435 3847027 := bstep (se 1 (by rfl) ⟨2885270, by rfl⟩ : syracuseStep 3847027 = 5770541) B5770541
theorem B5129369 : Blo 2279435 5129369 := bstep (se 2 (by rfl) ⟨1923513, by rfl⟩ : syracuseStep 5129369 = 3847027) B3847027
theorem B3419579 : Blo 2279435 3419579 := bstep (se 1 (by rfl) ⟨2564684, by rfl⟩ : syracuseStep 3419579 = 5129369) B5129369
theorem B2279719 : Blo 2279435 2279719 := bstep (se 1 (by rfl) ⟨1709789, by rfl⟩ : syracuseStep 2279719 = 3419579) B3419579
theorem B2564689 : Blo 2279435 2564689 := bbase (se 2 (by rfl) ⟨961758, by rfl⟩ : syracuseStep 2564689 = 1923517) (by norm_num)
theorem B3419585 : Blo 2279435 3419585 := bstep (se 2 (by rfl) ⟨1282344, by rfl⟩ : syracuseStep 3419585 = 2564689) B2564689
theorem B2279723 : Blo 2279435 2279723 := bstep (se 1 (by rfl) ⟨1709792, by rfl⟩ : syracuseStep 2279723 = 3419585) B3419585
theorem B3245941 : Blo 2279435 3245941 := bbase (se 5 (by rfl) ⟨152153, by rfl⟩ : syracuseStep 3245941 = 304307) (by norm_num)
theorem B4327921 : Blo 2279435 4327921 := bstep (se 2 (by rfl) ⟨1622970, by rfl⟩ : syracuseStep 4327921 = 3245941) B3245941
theorem B5770561 : Blo 2279435 5770561 := bstep (se 2 (by rfl) ⟨2163960, by rfl⟩ : syracuseStep 5770561 = 4327921) B4327921
theorem B7694081 : Blo 2279435 7694081 := bstep (se 2 (by rfl) ⟨2885280, by rfl⟩ : syracuseStep 7694081 = 5770561) B5770561
theorem B5129387 : Blo 2279435 5129387 := bstep (se 1 (by rfl) ⟨3847040, by rfl⟩ : syracuseStep 5129387 = 7694081) B7694081
theorem B3419591 : Blo 2279435 3419591 := bstep (se 1 (by rfl) ⟨2564693, by rfl⟩ : syracuseStep 3419591 = 5129387) B5129387
theorem B2279727 : Blo 2279435 2279727 := bstep (se 1 (by rfl) ⟨1709795, by rfl⟩ : syracuseStep 2279727 = 3419591) B3419591
theorem B3419597 : Blo 2279435 3419597 := bbase (se 3 (by rfl) ⟨641174, by rfl⟩ : syracuseStep 3419597 = 1282349) (by norm_num)
theorem B2279731 : Blo 2279435 2279731 := bstep (se 1 (by rfl) ⟨1709798, by rfl⟩ : syracuseStep 2279731 = 3419597) B3419597
theorem B5129405 : Blo 2279435 5129405 := bbase (se 3 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 5129405 = 1923527) (by norm_num)
theorem B3419603 : Blo 2279435 3419603 := bstep (se 1 (by rfl) ⟨2564702, by rfl⟩ : syracuseStep 3419603 = 5129405) B5129405
theorem B2279735 : Blo 2279435 2279735 := bstep (se 1 (by rfl) ⟨1709801, by rfl⟩ : syracuseStep 2279735 = 3419603) B3419603
theorem B3847061 : Blo 2279435 3847061 := bbase (se 6 (by rfl) ⟨90165, by rfl⟩ : syracuseStep 3847061 = 180331) (by norm_num)
theorem B2564707 : Blo 2279435 2564707 := bstep (se 1 (by rfl) ⟨1923530, by rfl⟩ : syracuseStep 2564707 = 3847061) B3847061
theorem B3419609 : Blo 2279435 3419609 := bstep (se 2 (by rfl) ⟨1282353, by rfl⟩ : syracuseStep 3419609 = 2564707) B2564707
theorem B2279739 : Blo 2279435 2279739 := bstep (se 1 (by rfl) ⟨1709804, by rfl⟩ : syracuseStep 2279739 = 3419609) B3419609
theorem B14606837 : Blo 2279435 14606837 := bbase (se 5 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 14606837 = 1369391) (by norm_num)
theorem B9737891 : Blo 2279435 9737891 := bstep (se 1 (by rfl) ⟨7303418, by rfl⟩ : syracuseStep 9737891 = 14606837) B14606837
theorem B6491927 : Blo 2279435 6491927 := bstep (se 1 (by rfl) ⟨4868945, by rfl⟩ : syracuseStep 6491927 = 9737891) B9737891
theorem B17311805 : Blo 2279435 17311805 := bstep (se 3 (by rfl) ⟨3245963, by rfl⟩ : syracuseStep 17311805 = 6491927) B6491927
theorem B11541203 : Blo 2279435 11541203 := bstep (se 1 (by rfl) ⟨8655902, by rfl⟩ : syracuseStep 11541203 = 17311805) B17311805
theorem B7694135 : Blo 2279435 7694135 := bstep (se 1 (by rfl) ⟨5770601, by rfl⟩ : syracuseStep 7694135 = 11541203) B11541203
theorem B5129423 : Blo 2279435 5129423 := bstep (se 1 (by rfl) ⟨3847067, by rfl⟩ : syracuseStep 5129423 = 7694135) B7694135
theorem B3419615 : Blo 2279435 3419615 := bstep (se 1 (by rfl) ⟨2564711, by rfl⟩ : syracuseStep 3419615 = 5129423) B5129423
theorem B2279743 : Blo 2279435 2279743 := bstep (se 1 (by rfl) ⟨1709807, by rfl⟩ : syracuseStep 2279743 = 3419615) B3419615
theorem B3419621 : Blo 2279435 3419621 := bbase (se 4 (by rfl) ⟨320589, by rfl⟩ : syracuseStep 3419621 = 641179) (by norm_num)
theorem B2279747 : Blo 2279435 2279747 := bstep (se 1 (by rfl) ⟨1709810, by rfl⟩ : syracuseStep 2279747 = 3419621) B3419621
theorem B12324565 : Blo 2279435 12324565 := bbase (se 7 (by rfl) ⟨144428, by rfl⟩ : syracuseStep 12324565 = 288857) (by norm_num)
theorem B16432753 : Blo 2279435 16432753 := bstep (se 2 (by rfl) ⟨6162282, by rfl⟩ : syracuseStep 16432753 = 12324565) B12324565
theorem B21910337 : Blo 2279435 21910337 := bstep (se 2 (by rfl) ⟨8216376, by rfl⟩ : syracuseStep 21910337 = 16432753) B16432753
theorem B14606891 : Blo 2279435 14606891 := bstep (se 1 (by rfl) ⟨10955168, by rfl⟩ : syracuseStep 14606891 = 21910337) B21910337
theorem B9737927 : Blo 2279435 9737927 := bstep (se 1 (by rfl) ⟨7303445, by rfl⟩ : syracuseStep 9737927 = 14606891) B14606891
theorem B6491951 : Blo 2279435 6491951 := bstep (se 1 (by rfl) ⟨4868963, by rfl⟩ : syracuseStep 6491951 = 9737927) B9737927
theorem B4327967 : Blo 2279435 4327967 := bstep (se 1 (by rfl) ⟨3245975, by rfl⟩ : syracuseStep 4327967 = 6491951) B6491951
theorem B2885311 : Blo 2279435 2885311 := bstep (se 1 (by rfl) ⟨2163983, by rfl⟩ : syracuseStep 2885311 = 4327967) B4327967
theorem B3847081 : Blo 2279435 3847081 := bstep (se 2 (by rfl) ⟨1442655, by rfl⟩ : syracuseStep 3847081 = 2885311) B2885311
theorem B5129441 : Blo 2279435 5129441 := bstep (se 2 (by rfl) ⟨1923540, by rfl⟩ : syracuseStep 5129441 = 3847081) B3847081
theorem B3419627 : Blo 2279435 3419627 := bstep (se 1 (by rfl) ⟨2564720, by rfl⟩ : syracuseStep 3419627 = 5129441) B5129441
theorem B2279751 : Blo 2279435 2279751 := bstep (se 1 (by rfl) ⟨1709813, by rfl⟩ : syracuseStep 2279751 = 3419627) B3419627
theorem B2564725 : Blo 2279435 2564725 := bbase (se 5 (by rfl) ⟨120221, by rfl⟩ : syracuseStep 2564725 = 240443) (by norm_num)
theorem B3419633 : Blo 2279435 3419633 := bstep (se 2 (by rfl) ⟨1282362, by rfl⟩ : syracuseStep 3419633 = 2564725) B2564725
theorem B2279755 : Blo 2279435 2279755 := bstep (se 1 (by rfl) ⟨1709816, by rfl⟩ : syracuseStep 2279755 = 3419633) B3419633
theorem B2885321 : Blo 2279435 2885321 := bbase (se 2 (by rfl) ⟨1081995, by rfl⟩ : syracuseStep 2885321 = 2163991) (by norm_num)
theorem B7694189 : Blo 2279435 7694189 := bstep (se 3 (by rfl) ⟨1442660, by rfl⟩ : syracuseStep 7694189 = 2885321) B2885321
theorem B5129459 : Blo 2279435 5129459 := bstep (se 1 (by rfl) ⟨3847094, by rfl⟩ : syracuseStep 5129459 = 7694189) B7694189
theorem B3419639 : Blo 2279435 3419639 := bstep (se 1 (by rfl) ⟨2564729, by rfl⟩ : syracuseStep 3419639 = 5129459) B5129459
theorem B2279759 : Blo 2279435 2279759 := bstep (se 1 (by rfl) ⟨1709819, by rfl⟩ : syracuseStep 2279759 = 3419639) B3419639
theorem B3419645 : Blo 2279435 3419645 := bbase (se 3 (by rfl) ⟨641183, by rfl⟩ : syracuseStep 3419645 = 1282367) (by norm_num)
theorem B2279763 : Blo 2279435 2279763 := bstep (se 1 (by rfl) ⟨1709822, by rfl⟩ : syracuseStep 2279763 = 3419645) B3419645
theorem B5129477 : Blo 2279435 5129477 := bbase (se 4 (by rfl) ⟨480888, by rfl⟩ : syracuseStep 5129477 = 961777) (by norm_num)
theorem B3419651 : Blo 2279435 3419651 := bstep (se 1 (by rfl) ⟨2564738, by rfl⟩ : syracuseStep 3419651 = 5129477) B5129477
theorem B2279767 : Blo 2279435 2279767 := bstep (se 1 (by rfl) ⟨1709825, by rfl⟩ : syracuseStep 2279767 = 3419651) B3419651
theorem B4328005 : Blo 2279435 4328005 := bbase (se 4 (by rfl) ⟨405750, by rfl⟩ : syracuseStep 4328005 = 811501) (by norm_num)
theorem B5770673 : Blo 2279435 5770673 := bstep (se 2 (by rfl) ⟨2164002, by rfl⟩ : syracuseStep 5770673 = 4328005) B4328005
theorem B3847115 : Blo 2279435 3847115 := bstep (se 1 (by rfl) ⟨2885336, by rfl⟩ : syracuseStep 3847115 = 5770673) B5770673
theorem B2564743 : Blo 2279435 2564743 := bstep (se 1 (by rfl) ⟨1923557, by rfl⟩ : syracuseStep 2564743 = 3847115) B3847115
theorem B3419657 : Blo 2279435 3419657 := bstep (se 2 (by rfl) ⟨1282371, by rfl⟩ : syracuseStep 3419657 = 2564743) B2564743
theorem B2279771 : Blo 2279435 2279771 := bstep (se 1 (by rfl) ⟨1709828, by rfl⟩ : syracuseStep 2279771 = 3419657) B3419657
theorem B11541365 : Blo 2279435 11541365 := bbase (se 5 (by rfl) ⟨541001, by rfl⟩ : syracuseStep 11541365 = 1082003) (by norm_num)
theorem B7694243 : Blo 2279435 7694243 := bstep (se 1 (by rfl) ⟨5770682, by rfl⟩ : syracuseStep 7694243 = 11541365) B11541365
theorem B5129495 : Blo 2279435 5129495 := bstep (se 1 (by rfl) ⟨3847121, by rfl⟩ : syracuseStep 5129495 = 7694243) B7694243
theorem B3419663 : Blo 2279435 3419663 := bstep (se 1 (by rfl) ⟨2564747, by rfl⟩ : syracuseStep 3419663 = 5129495) B5129495
theorem B2279775 : Blo 2279435 2279775 := bstep (se 1 (by rfl) ⟨1709831, by rfl⟩ : syracuseStep 2279775 = 3419663) B3419663
theorem B3419669 : Blo 2279435 3419669 := bbase (se 6 (by rfl) ⟨80148, by rfl⟩ : syracuseStep 3419669 = 160297) (by norm_num)
theorem B2279779 : Blo 2279435 2279779 := bstep (se 1 (by rfl) ⟨1709834, by rfl⟩ : syracuseStep 2279779 = 3419669) B3419669
theorem B5849437 : Blo 2279435 5849437 := bbase (se 3 (by rfl) ⟨1096769, by rfl⟩ : syracuseStep 5849437 = 2193539) (by norm_num)
theorem B7799249 : Blo 2279435 7799249 := bstep (se 2 (by rfl) ⟨2924718, by rfl⟩ : syracuseStep 7799249 = 5849437) B5849437
theorem B5199499 : Blo 2279435 5199499 := bstep (se 1 (by rfl) ⟨3899624, by rfl⟩ : syracuseStep 5199499 = 7799249) B7799249
theorem B6932665 : Blo 2279435 6932665 := bstep (se 2 (by rfl) ⟨2599749, by rfl⟩ : syracuseStep 6932665 = 5199499) B5199499
theorem B9243553 : Blo 2279435 9243553 := bstep (se 2 (by rfl) ⟨3466332, by rfl⟩ : syracuseStep 9243553 = 6932665) B6932665
theorem B12324737 : Blo 2279435 12324737 := bstep (se 2 (by rfl) ⟨4621776, by rfl⟩ : syracuseStep 12324737 = 9243553) B9243553
theorem B8216491 : Blo 2279435 8216491 := bstep (se 1 (by rfl) ⟨6162368, by rfl⟩ : syracuseStep 8216491 = 12324737) B12324737
theorem B10955321 : Blo 2279435 10955321 := bstep (se 2 (by rfl) ⟨4108245, by rfl⟩ : syracuseStep 10955321 = 8216491) B8216491
theorem B7303547 : Blo 2279435 7303547 := bstep (se 1 (by rfl) ⟨5477660, by rfl⟩ : syracuseStep 7303547 = 10955321) B10955321
theorem B19476125 : Blo 2279435 19476125 := bstep (se 3 (by rfl) ⟨3651773, by rfl⟩ : syracuseStep 19476125 = 7303547) B7303547
theorem B12984083 : Blo 2279435 12984083 := bstep (se 1 (by rfl) ⟨9738062, by rfl⟩ : syracuseStep 12984083 = 19476125) B19476125
theorem B8656055 : Blo 2279435 8656055 := bstep (se 1 (by rfl) ⟨6492041, by rfl⟩ : syracuseStep 8656055 = 12984083) B12984083
theorem B5770703 : Blo 2279435 5770703 := bstep (se 1 (by rfl) ⟨4328027, by rfl⟩ : syracuseStep 5770703 = 8656055) B8656055
theorem B3847135 : Blo 2279435 3847135 := bstep (se 1 (by rfl) ⟨2885351, by rfl⟩ : syracuseStep 3847135 = 5770703) B5770703
theorem B5129513 : Blo 2279435 5129513 := bstep (se 2 (by rfl) ⟨1923567, by rfl⟩ : syracuseStep 5129513 = 3847135) B3847135
theorem B3419675 : Blo 2279435 3419675 := bstep (se 1 (by rfl) ⟨2564756, by rfl⟩ : syracuseStep 3419675 = 5129513) B5129513
theorem B2279783 : Blo 2279435 2279783 := bstep (se 1 (by rfl) ⟨1709837, by rfl⟩ : syracuseStep 2279783 = 3419675) B3419675
theorem B2564761 : Blo 2279435 2564761 := bbase (se 2 (by rfl) ⟨961785, by rfl⟩ : syracuseStep 2564761 = 1923571) (by norm_num)
theorem B3419681 : Blo 2279435 3419681 := bstep (se 2 (by rfl) ⟨1282380, by rfl⟩ : syracuseStep 3419681 = 2564761) B2564761
theorem B2279787 : Blo 2279435 2279787 := bstep (se 1 (by rfl) ⟨1709840, by rfl⟩ : syracuseStep 2279787 = 3419681) B3419681
theorem B8656085 : Blo 2279435 8656085 := bbase (se 7 (by rfl) ⟨101438, by rfl⟩ : syracuseStep 8656085 = 202877) (by norm_num)
theorem B5770723 : Blo 2279435 5770723 := bstep (se 1 (by rfl) ⟨4328042, by rfl⟩ : syracuseStep 5770723 = 8656085) B8656085
theorem B7694297 : Blo 2279435 7694297 := bstep (se 2 (by rfl) ⟨2885361, by rfl⟩ : syracuseStep 7694297 = 5770723) B5770723
theorem B5129531 : Blo 2279435 5129531 := bstep (se 1 (by rfl) ⟨3847148, by rfl⟩ : syracuseStep 5129531 = 7694297) B7694297
theorem B3419687 : Blo 2279435 3419687 := bstep (se 1 (by rfl) ⟨2564765, by rfl⟩ : syracuseStep 3419687 = 5129531) B5129531
theorem B2279791 : Blo 2279435 2279791 := bstep (se 1 (by rfl) ⟨1709843, by rfl⟩ : syracuseStep 2279791 = 3419687) B3419687
theorem B3419693 : Blo 2279435 3419693 := bbase (se 3 (by rfl) ⟨641192, by rfl⟩ : syracuseStep 3419693 = 1282385) (by norm_num)
theorem B2279795 : Blo 2279435 2279795 := bstep (se 1 (by rfl) ⟨1709846, by rfl⟩ : syracuseStep 2279795 = 3419693) B3419693
theorem B5129549 : Blo 2279435 5129549 := bbase (se 3 (by rfl) ⟨961790, by rfl⟩ : syracuseStep 5129549 = 1923581) (by norm_num)
theorem B3419699 : Blo 2279435 3419699 := bstep (se 1 (by rfl) ⟨2564774, by rfl⟩ : syracuseStep 3419699 = 5129549) B5129549
theorem B2279799 : Blo 2279435 2279799 := bstep (se 1 (by rfl) ⟨1709849, by rfl⟩ : syracuseStep 2279799 = 3419699) B3419699
theorem B2885377 : Blo 2279435 2885377 := bbase (se 2 (by rfl) ⟨1082016, by rfl⟩ : syracuseStep 2885377 = 2164033) (by norm_num)
theorem B3847169 : Blo 2279435 3847169 := bstep (se 2 (by rfl) ⟨1442688, by rfl⟩ : syracuseStep 3847169 = 2885377) B2885377
theorem B2564779 : Blo 2279435 2564779 := bstep (se 1 (by rfl) ⟨1923584, by rfl⟩ : syracuseStep 2564779 = 3847169) B3847169
theorem B3419705 : Blo 2279435 3419705 := bstep (se 2 (by rfl) ⟨1282389, by rfl⟩ : syracuseStep 3419705 = 2564779) B2564779
theorem B2279803 : Blo 2279435 2279803 := bstep (se 1 (by rfl) ⟨1709852, by rfl⟩ : syracuseStep 2279803 = 3419705) B3419705
theorem B2434541 : Blo 2279435 2434541 := bbase (se 3 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 2434541 = 912953) (by norm_num)
theorem B25968437 : Blo 2279435 25968437 := bstep (se 5 (by rfl) ⟨1217270, by rfl⟩ : syracuseStep 25968437 = 2434541) B2434541
theorem B17312291 : Blo 2279435 17312291 := bstep (se 1 (by rfl) ⟨12984218, by rfl⟩ : syracuseStep 17312291 = 25968437) B25968437
theorem B11541527 : Blo 2279435 11541527 := bstep (se 1 (by rfl) ⟨8656145, by rfl⟩ : syracuseStep 11541527 = 17312291) B17312291
theorem B7694351 : Blo 2279435 7694351 := bstep (se 1 (by rfl) ⟨5770763, by rfl⟩ : syracuseStep 7694351 = 11541527) B11541527
theorem B5129567 : Blo 2279435 5129567 := bstep (se 1 (by rfl) ⟨3847175, by rfl⟩ : syracuseStep 5129567 = 7694351) B7694351
theorem B3419711 : Blo 2279435 3419711 := bstep (se 1 (by rfl) ⟨2564783, by rfl⟩ : syracuseStep 3419711 = 5129567) B5129567
theorem B2279807 : Blo 2279435 2279807 := bstep (se 1 (by rfl) ⟨1709855, by rfl⟩ : syracuseStep 2279807 = 3419711) B3419711
theorem B3419717 : Blo 2279435 3419717 := bbase (se 4 (by rfl) ⟨320598, by rfl⟩ : syracuseStep 3419717 = 641197) (by norm_num)
theorem B2279811 : Blo 2279435 2279811 := bstep (se 1 (by rfl) ⟨1709858, by rfl⟩ : syracuseStep 2279811 = 3419717) B3419717
theorem B3847189 : Blo 2279435 3847189 := bbase (se 6 (by rfl) ⟨90168, by rfl⟩ : syracuseStep 3847189 = 180337) (by norm_num)
theorem B5129585 : Blo 2279435 5129585 := bstep (se 2 (by rfl) ⟨1923594, by rfl⟩ : syracuseStep 5129585 = 3847189) B3847189
theorem B3419723 : Blo 2279435 3419723 := bstep (se 1 (by rfl) ⟨2564792, by rfl⟩ : syracuseStep 3419723 = 5129585) B5129585
theorem B2279815 : Blo 2279435 2279815 := bstep (se 1 (by rfl) ⟨1709861, by rfl⟩ : syracuseStep 2279815 = 3419723) B3419723
theorem B2564797 : Blo 2279435 2564797 := bbase (se 3 (by rfl) ⟨480899, by rfl⟩ : syracuseStep 2564797 = 961799) (by norm_num)
theorem B3419729 : Blo 2279435 3419729 := bstep (se 2 (by rfl) ⟨1282398, by rfl⟩ : syracuseStep 3419729 = 2564797) B2564797
theorem B2279819 : Blo 2279435 2279819 := bstep (se 1 (by rfl) ⟨1709864, by rfl⟩ : syracuseStep 2279819 = 3419729) B3419729
theorem B7694405 : Blo 2279435 7694405 := bbase (se 4 (by rfl) ⟨721350, by rfl⟩ : syracuseStep 7694405 = 1442701) (by norm_num)
theorem B5129603 : Blo 2279435 5129603 := bstep (se 1 (by rfl) ⟨3847202, by rfl⟩ : syracuseStep 5129603 = 7694405) B7694405
theorem B3419735 : Blo 2279435 3419735 := bstep (se 1 (by rfl) ⟨2564801, by rfl⟩ : syracuseStep 3419735 = 5129603) B5129603
theorem B2279823 : Blo 2279435 2279823 := bstep (se 1 (by rfl) ⟨1709867, by rfl⟩ : syracuseStep 2279823 = 3419735) B3419735
theorem B3419741 : Blo 2279435 3419741 := bbase (se 3 (by rfl) ⟨641201, by rfl⟩ : syracuseStep 3419741 = 1282403) (by norm_num)
theorem B2279827 : Blo 2279435 2279827 := bstep (se 1 (by rfl) ⟨1709870, by rfl⟩ : syracuseStep 2279827 = 3419741) B3419741
theorem B5129621 : Blo 2279435 5129621 := bbase (se 6 (by rfl) ⟨120225, by rfl⟩ : syracuseStep 5129621 = 240451) (by norm_num)
theorem B3419747 : Blo 2279435 3419747 := bstep (se 1 (by rfl) ⟨2564810, by rfl⟩ : syracuseStep 3419747 = 5129621) B5129621
theorem B2279831 : Blo 2279435 2279831 := bstep (se 1 (by rfl) ⟨1709873, by rfl⟩ : syracuseStep 2279831 = 3419747) B3419747
theorem B10955573 : Blo 2279435 10955573 := bbase (se 5 (by rfl) ⟨513542, by rfl⟩ : syracuseStep 10955573 = 1027085) (by norm_num)
theorem B7303715 : Blo 2279435 7303715 := bstep (se 1 (by rfl) ⟨5477786, by rfl⟩ : syracuseStep 7303715 = 10955573) B10955573
theorem B4869143 : Blo 2279435 4869143 := bstep (se 1 (by rfl) ⟨3651857, by rfl⟩ : syracuseStep 4869143 = 7303715) B7303715
theorem B3246095 : Blo 2279435 3246095 := bstep (se 1 (by rfl) ⟨2434571, by rfl⟩ : syracuseStep 3246095 = 4869143) B4869143
theorem B8656253 : Blo 2279435 8656253 := bstep (se 3 (by rfl) ⟨1623047, by rfl⟩ : syracuseStep 8656253 = 3246095) B3246095
theorem B5770835 : Blo 2279435 5770835 := bstep (se 1 (by rfl) ⟨4328126, by rfl⟩ : syracuseStep 5770835 = 8656253) B8656253
theorem B3847223 : Blo 2279435 3847223 := bstep (se 1 (by rfl) ⟨2885417, by rfl⟩ : syracuseStep 3847223 = 5770835) B5770835
theorem B2564815 : Blo 2279435 2564815 := bstep (se 1 (by rfl) ⟨1923611, by rfl⟩ : syracuseStep 2564815 = 3847223) B3847223
theorem B3419753 : Blo 2279435 3419753 := bstep (se 2 (by rfl) ⟨1282407, by rfl⟩ : syracuseStep 3419753 = 2564815) B2564815
theorem B2279835 : Blo 2279435 2279835 := bstep (se 1 (by rfl) ⟨1709876, by rfl⟩ : syracuseStep 2279835 = 3419753) B3419753
theorem B8216693 : Blo 2279435 8216693 := bbase (se 5 (by rfl) ⟨385157, by rfl⟩ : syracuseStep 8216693 = 770315) (by norm_num)
theorem B5477795 : Blo 2279435 5477795 := bstep (se 1 (by rfl) ⟨4108346, by rfl⟩ : syracuseStep 5477795 = 8216693) B8216693
theorem B3651863 : Blo 2279435 3651863 := bstep (se 1 (by rfl) ⟨2738897, by rfl⟩ : syracuseStep 3651863 = 5477795) B5477795
theorem B9738301 : Blo 2279435 9738301 := bstep (se 3 (by rfl) ⟨1825931, by rfl⟩ : syracuseStep 9738301 = 3651863) B3651863
theorem B12984401 : Blo 2279435 12984401 := bstep (se 2 (by rfl) ⟨4869150, by rfl⟩ : syracuseStep 12984401 = 9738301) B9738301
theorem B8656267 : Blo 2279435 8656267 := bstep (se 1 (by rfl) ⟨6492200, by rfl⟩ : syracuseStep 8656267 = 12984401) B12984401
theorem B11541689 : Blo 2279435 11541689 := bstep (se 2 (by rfl) ⟨4328133, by rfl⟩ : syracuseStep 11541689 = 8656267) B8656267
theorem B7694459 : Blo 2279435 7694459 := bstep (se 1 (by rfl) ⟨5770844, by rfl⟩ : syracuseStep 7694459 = 11541689) B11541689
theorem B5129639 : Blo 2279435 5129639 := bstep (se 1 (by rfl) ⟨3847229, by rfl⟩ : syracuseStep 5129639 = 7694459) B7694459
theorem B3419759 : Blo 2279435 3419759 := bstep (se 1 (by rfl) ⟨2564819, by rfl⟩ : syracuseStep 3419759 = 5129639) B5129639
theorem B2279839 : Blo 2279435 2279839 := bstep (se 1 (by rfl) ⟨1709879, by rfl⟩ : syracuseStep 2279839 = 3419759) B3419759
theorem B3419765 : Blo 2279435 3419765 := bbase (se 5 (by rfl) ⟨160301, by rfl⟩ : syracuseStep 3419765 = 320603) (by norm_num)
theorem B2279843 : Blo 2279435 2279843 := bstep (se 1 (by rfl) ⟨1709882, by rfl⟩ : syracuseStep 2279843 = 3419765) B3419765
theorem B4328149 : Blo 2279435 4328149 := bbase (se 7 (by rfl) ⟨50720, by rfl⟩ : syracuseStep 4328149 = 101441) (by norm_num)
theorem B5770865 : Blo 2279435 5770865 := bstep (se 2 (by rfl) ⟨2164074, by rfl⟩ : syracuseStep 5770865 = 4328149) B4328149
theorem B3847243 : Blo 2279435 3847243 := bstep (se 1 (by rfl) ⟨2885432, by rfl⟩ : syracuseStep 3847243 = 5770865) B5770865
theorem B5129657 : Blo 2279435 5129657 := bstep (se 2 (by rfl) ⟨1923621, by rfl⟩ : syracuseStep 5129657 = 3847243) B3847243
theorem B3419771 : Blo 2279435 3419771 := bstep (se 1 (by rfl) ⟨2564828, by rfl⟩ : syracuseStep 3419771 = 5129657) B5129657
theorem B2279847 : Blo 2279435 2279847 := bstep (se 1 (by rfl) ⟨1709885, by rfl⟩ : syracuseStep 2279847 = 3419771) B3419771
theorem B2564833 : Blo 2279435 2564833 := bbase (se 2 (by rfl) ⟨961812, by rfl⟩ : syracuseStep 2564833 = 1923625) (by norm_num)
theorem B3419777 : Blo 2279435 3419777 := bstep (se 2 (by rfl) ⟨1282416, by rfl⟩ : syracuseStep 3419777 = 2564833) B2564833
theorem B2279851 : Blo 2279435 2279851 := bstep (se 1 (by rfl) ⟨1709888, by rfl⟩ : syracuseStep 2279851 = 3419777) B3419777
theorem B5770885 : Blo 2279435 5770885 := bbase (se 4 (by rfl) ⟨541020, by rfl⟩ : syracuseStep 5770885 = 1082041) (by norm_num)
theorem B7694513 : Blo 2279435 7694513 := bstep (se 2 (by rfl) ⟨2885442, by rfl⟩ : syracuseStep 7694513 = 5770885) B5770885
theorem B5129675 : Blo 2279435 5129675 := bstep (se 1 (by rfl) ⟨3847256, by rfl⟩ : syracuseStep 5129675 = 7694513) B7694513
theorem B3419783 : Blo 2279435 3419783 := bstep (se 1 (by rfl) ⟨2564837, by rfl⟩ : syracuseStep 3419783 = 5129675) B5129675
theorem B2279855 : Blo 2279435 2279855 := bstep (se 1 (by rfl) ⟨1709891, by rfl⟩ : syracuseStep 2279855 = 3419783) B3419783
theorem B3419789 : Blo 2279435 3419789 := bbase (se 3 (by rfl) ⟨641210, by rfl⟩ : syracuseStep 3419789 = 1282421) (by norm_num)
theorem B2279859 : Blo 2279435 2279859 := bstep (se 1 (by rfl) ⟨1709894, by rfl⟩ : syracuseStep 2279859 = 3419789) B3419789
theorem B5129693 : Blo 2279435 5129693 := bbase (se 3 (by rfl) ⟨961817, by rfl⟩ : syracuseStep 5129693 = 1923635) (by norm_num)
theorem B3419795 : Blo 2279435 3419795 := bstep (se 1 (by rfl) ⟨2564846, by rfl⟩ : syracuseStep 3419795 = 5129693) B5129693
theorem B2279863 : Blo 2279435 2279863 := bstep (se 1 (by rfl) ⟨1709897, by rfl⟩ : syracuseStep 2279863 = 3419795) B3419795
theorem B3847277 : Blo 2279435 3847277 := bbase (se 3 (by rfl) ⟨721364, by rfl⟩ : syracuseStep 3847277 = 1442729) (by norm_num)
theorem B2564851 : Blo 2279435 2564851 := bstep (se 1 (by rfl) ⟨1923638, by rfl⟩ : syracuseStep 2564851 = 3847277) B3847277
theorem B3419801 : Blo 2279435 3419801 := bstep (se 2 (by rfl) ⟨1282425, by rfl⟩ : syracuseStep 3419801 = 2564851) B2564851
theorem B2279867 : Blo 2279435 2279867 := bstep (se 1 (by rfl) ⟨1709900, by rfl⟩ : syracuseStep 2279867 = 3419801) B3419801
theorem B23398645 : Blo 2279435 23398645 := bbase (se 5 (by rfl) ⟨1096811, by rfl⟩ : syracuseStep 23398645 = 2193623) (by norm_num)
theorem B31198193 : Blo 2279435 31198193 := bstep (se 2 (by rfl) ⟨11699322, by rfl⟩ : syracuseStep 31198193 = 23398645) B23398645
theorem B20798795 : Blo 2279435 20798795 := bstep (se 1 (by rfl) ⟨15599096, by rfl⟩ : syracuseStep 20798795 = 31198193) B31198193
theorem B13865863 : Blo 2279435 13865863 := bstep (se 1 (by rfl) ⟨10399397, by rfl⟩ : syracuseStep 13865863 = 20798795) B20798795
theorem B18487817 : Blo 2279435 18487817 := bstep (se 2 (by rfl) ⟨6932931, by rfl⟩ : syracuseStep 18487817 = 13865863) B13865863
theorem B12325211 : Blo 2279435 12325211 := bstep (se 1 (by rfl) ⟨9243908, by rfl⟩ : syracuseStep 12325211 = 18487817) B18487817
theorem B8216807 : Blo 2279435 8216807 := bstep (se 1 (by rfl) ⟨6162605, by rfl⟩ : syracuseStep 8216807 = 12325211) B12325211
theorem B21911485 : Blo 2279435 21911485 := bstep (se 3 (by rfl) ⟨4108403, by rfl⟩ : syracuseStep 21911485 = 8216807) B8216807
theorem B29215313 : Blo 2279435 29215313 := bstep (se 2 (by rfl) ⟨10955742, by rfl⟩ : syracuseStep 29215313 = 21911485) B21911485
theorem B19476875 : Blo 2279435 19476875 := bstep (se 1 (by rfl) ⟨14607656, by rfl⟩ : syracuseStep 19476875 = 29215313) B29215313
theorem B12984583 : Blo 2279435 12984583 := bstep (se 1 (by rfl) ⟨9738437, by rfl⟩ : syracuseStep 12984583 = 19476875) B19476875
theorem B17312777 : Blo 2279435 17312777 := bstep (se 2 (by rfl) ⟨6492291, by rfl⟩ : syracuseStep 17312777 = 12984583) B12984583
theorem B11541851 : Blo 2279435 11541851 := bstep (se 1 (by rfl) ⟨8656388, by rfl⟩ : syracuseStep 11541851 = 17312777) B17312777
theorem B7694567 : Blo 2279435 7694567 := bstep (se 1 (by rfl) ⟨5770925, by rfl⟩ : syracuseStep 7694567 = 11541851) B11541851
theorem B5129711 : Blo 2279435 5129711 := bstep (se 1 (by rfl) ⟨3847283, by rfl⟩ : syracuseStep 5129711 = 7694567) B7694567
theorem B3419807 : Blo 2279435 3419807 := bstep (se 1 (by rfl) ⟨2564855, by rfl⟩ : syracuseStep 3419807 = 5129711) B5129711
theorem B2279871 : Blo 2279435 2279871 := bstep (se 1 (by rfl) ⟨1709903, by rfl⟩ : syracuseStep 2279871 = 3419807) B3419807
theorem B3419813 : Blo 2279435 3419813 := bbase (se 4 (by rfl) ⟨320607, by rfl⟩ : syracuseStep 3419813 = 641215) (by norm_num)
theorem B2279875 : Blo 2279435 2279875 := bstep (se 1 (by rfl) ⟨1709906, by rfl⟩ : syracuseStep 2279875 = 3419813) B3419813
theorem B2885473 : Blo 2279435 2885473 := bbase (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) (by norm_num)
theorem B3847297 : Blo 2279435 3847297 := bstep (se 2 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 3847297 = 2885473) B2885473
theorem B5129729 : Blo 2279435 5129729 := bstep (se 2 (by rfl) ⟨1923648, by rfl⟩ : syracuseStep 5129729 = 3847297) B3847297
theorem B3419819 : Blo 2279435 3419819 := bstep (se 1 (by rfl) ⟨2564864, by rfl⟩ : syracuseStep 3419819 = 5129729) B5129729
theorem B2279879 : Blo 2279435 2279879 := bstep (se 1 (by rfl) ⟨1709909, by rfl⟩ : syracuseStep 2279879 = 3419819) B3419819
theorem B2564869 : Blo 2279435 2564869 := bbase (se 4 (by rfl) ⟨240456, by rfl⟩ : syracuseStep 2564869 = 480913) (by norm_num)
theorem B3419825 : Blo 2279435 3419825 := bstep (se 2 (by rfl) ⟨1282434, by rfl⟩ : syracuseStep 3419825 = 2564869) B2564869
theorem B2279883 : Blo 2279435 2279883 := bstep (se 1 (by rfl) ⟨1709912, by rfl⟩ : syracuseStep 2279883 = 3419825) B3419825
theorem B3651941 : Blo 2279435 3651941 := bbase (se 4 (by rfl) ⟨342369, by rfl⟩ : syracuseStep 3651941 = 684739) (by norm_num)
theorem B2434627 : Blo 2279435 2434627 := bstep (se 1 (by rfl) ⟨1825970, by rfl⟩ : syracuseStep 2434627 = 3651941) B3651941
theorem B3246169 : Blo 2279435 3246169 := bstep (se 2 (by rfl) ⟨1217313, by rfl⟩ : syracuseStep 3246169 = 2434627) B2434627
theorem B4328225 : Blo 2279435 4328225 := bstep (se 2 (by rfl) ⟨1623084, by rfl⟩ : syracuseStep 4328225 = 3246169) B3246169
theorem B2885483 : Blo 2279435 2885483 := bstep (se 1 (by rfl) ⟨2164112, by rfl⟩ : syracuseStep 2885483 = 4328225) B4328225
theorem B7694621 : Blo 2279435 7694621 := bstep (se 3 (by rfl) ⟨1442741, by rfl⟩ : syracuseStep 7694621 = 2885483) B2885483
theorem B5129747 : Blo 2279435 5129747 := bstep (se 1 (by rfl) ⟨3847310, by rfl⟩ : syracuseStep 5129747 = 7694621) B7694621
theorem B3419831 : Blo 2279435 3419831 := bstep (se 1 (by rfl) ⟨2564873, by rfl⟩ : syracuseStep 3419831 = 5129747) B5129747
theorem B2279887 : Blo 2279435 2279887 := bstep (se 1 (by rfl) ⟨1709915, by rfl⟩ : syracuseStep 2279887 = 3419831) B3419831
theorem B3419837 : Blo 2279435 3419837 := bbase (se 3 (by rfl) ⟨641219, by rfl⟩ : syracuseStep 3419837 = 1282439) (by norm_num)
theorem B2279891 : Blo 2279435 2279891 := bstep (se 1 (by rfl) ⟨1709918, by rfl⟩ : syracuseStep 2279891 = 3419837) B3419837
theorem B5129765 : Blo 2279435 5129765 := bbase (se 4 (by rfl) ⟨480915, by rfl⟩ : syracuseStep 5129765 = 961831) (by norm_num)
theorem B3419843 : Blo 2279435 3419843 := bstep (se 1 (by rfl) ⟨2564882, by rfl⟩ : syracuseStep 3419843 = 5129765) B5129765
theorem B2279895 : Blo 2279435 2279895 := bstep (se 1 (by rfl) ⟨1709921, by rfl⟩ : syracuseStep 2279895 = 3419843) B3419843
theorem B5770997 : Blo 2279435 5770997 := bbase (se 5 (by rfl) ⟨270515, by rfl⟩ : syracuseStep 5770997 = 541031) (by norm_num)
theorem B3847331 : Blo 2279435 3847331 := bstep (se 1 (by rfl) ⟨2885498, by rfl⟩ : syracuseStep 3847331 = 5770997) B5770997
theorem B2564887 : Blo 2279435 2564887 := bstep (se 1 (by rfl) ⟨1923665, by rfl⟩ : syracuseStep 2564887 = 3847331) B3847331
theorem B3419849 : Blo 2279435 3419849 := bstep (se 2 (by rfl) ⟨1282443, by rfl⟩ : syracuseStep 3419849 = 2564887) B2564887
theorem B2279899 : Blo 2279435 2279899 := bstep (se 1 (by rfl) ⟨1709924, by rfl⟩ : syracuseStep 2279899 = 3419849) B3419849
theorem B15599317 : Blo 2279435 15599317 := bbase (se 7 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 15599317 = 365609) (by norm_num)
theorem B20799089 : Blo 2279435 20799089 := bstep (se 2 (by rfl) ⟨7799658, by rfl⟩ : syracuseStep 20799089 = 15599317) B15599317
theorem B13866059 : Blo 2279435 13866059 := bstep (se 1 (by rfl) ⟨10399544, by rfl⟩ : syracuseStep 13866059 = 20799089) B20799089
theorem B9244039 : Blo 2279435 9244039 := bstep (se 1 (by rfl) ⟨6933029, by rfl⟩ : syracuseStep 9244039 = 13866059) B13866059
theorem B12325385 : Blo 2279435 12325385 := bstep (se 2 (by rfl) ⟨4622019, by rfl⟩ : syracuseStep 12325385 = 9244039) B9244039
theorem B32867693 : Blo 2279435 32867693 := bstep (se 3 (by rfl) ⟨6162692, by rfl⟩ : syracuseStep 32867693 = 12325385) B12325385
theorem B21911795 : Blo 2279435 21911795 := bstep (se 1 (by rfl) ⟨16433846, by rfl⟩ : syracuseStep 21911795 = 32867693) B32867693
theorem B14607863 : Blo 2279435 14607863 := bstep (se 1 (by rfl) ⟨10955897, by rfl⟩ : syracuseStep 14607863 = 21911795) B21911795
theorem B9738575 : Blo 2279435 9738575 := bstep (se 1 (by rfl) ⟨7303931, by rfl⟩ : syracuseStep 9738575 = 14607863) B14607863
theorem B6492383 : Blo 2279435 6492383 := bstep (se 1 (by rfl) ⟨4869287, by rfl⟩ : syracuseStep 6492383 = 9738575) B9738575
theorem B4328255 : Blo 2279435 4328255 := bstep (se 1 (by rfl) ⟨3246191, by rfl⟩ : syracuseStep 4328255 = 6492383) B6492383
theorem B11542013 : Blo 2279435 11542013 := bstep (se 3 (by rfl) ⟨2164127, by rfl⟩ : syracuseStep 11542013 = 4328255) B4328255
theorem B7694675 : Blo 2279435 7694675 := bstep (se 1 (by rfl) ⟨5771006, by rfl⟩ : syracuseStep 7694675 = 11542013) B11542013
theorem B5129783 : Blo 2279435 5129783 := bstep (se 1 (by rfl) ⟨3847337, by rfl⟩ : syracuseStep 5129783 = 7694675) B7694675
theorem B3419855 : Blo 2279435 3419855 := bstep (se 1 (by rfl) ⟨2564891, by rfl⟩ : syracuseStep 3419855 = 5129783) B5129783
theorem B2279903 : Blo 2279435 2279903 := bstep (se 1 (by rfl) ⟨1709927, by rfl⟩ : syracuseStep 2279903 = 3419855) B3419855
theorem B3419861 : Blo 2279435 3419861 := bbase (se 7 (by rfl) ⟨40076, by rfl⟩ : syracuseStep 3419861 = 80153) (by norm_num)
theorem B2279907 : Blo 2279435 2279907 := bstep (se 1 (by rfl) ⟨1709930, by rfl⟩ : syracuseStep 2279907 = 3419861) B3419861
theorem B4108477 : Blo 2279435 4108477 := bbase (se 3 (by rfl) ⟨770339, by rfl⟩ : syracuseStep 4108477 = 1540679) (by norm_num)
theorem B5477969 : Blo 2279435 5477969 := bstep (se 2 (by rfl) ⟨2054238, by rfl⟩ : syracuseStep 5477969 = 4108477) B4108477
theorem B3651979 : Blo 2279435 3651979 := bstep (se 1 (by rfl) ⟨2738984, by rfl⟩ : syracuseStep 3651979 = 5477969) B5477969
theorem B4869305 : Blo 2279435 4869305 := bstep (se 2 (by rfl) ⟨1825989, by rfl⟩ : syracuseStep 4869305 = 3651979) B3651979
theorem B3246203 : Blo 2279435 3246203 := bstep (se 1 (by rfl) ⟨2434652, by rfl⟩ : syracuseStep 3246203 = 4869305) B4869305
theorem B8656541 : Blo 2279435 8656541 := bstep (se 3 (by rfl) ⟨1623101, by rfl⟩ : syracuseStep 8656541 = 3246203) B3246203
theorem B5771027 : Blo 2279435 5771027 := bstep (se 1 (by rfl) ⟨4328270, by rfl⟩ : syracuseStep 5771027 = 8656541) B8656541
theorem B3847351 : Blo 2279435 3847351 := bstep (se 1 (by rfl) ⟨2885513, by rfl⟩ : syracuseStep 3847351 = 5771027) B5771027
theorem B5129801 : Blo 2279435 5129801 := bstep (se 2 (by rfl) ⟨1923675, by rfl⟩ : syracuseStep 5129801 = 3847351) B3847351
theorem B3419867 : Blo 2279435 3419867 := bstep (se 1 (by rfl) ⟨2564900, by rfl⟩ : syracuseStep 3419867 = 5129801) B5129801
theorem B2279911 : Blo 2279435 2279911 := bstep (se 1 (by rfl) ⟨1709933, by rfl⟩ : syracuseStep 2279911 = 3419867) B3419867
theorem B2564905 : Blo 2279435 2564905 := bbase (se 2 (by rfl) ⟨961839, by rfl⟩ : syracuseStep 2564905 = 1923679) (by norm_num)
theorem B3419873 : Blo 2279435 3419873 := bstep (se 2 (by rfl) ⟨1282452, by rfl⟩ : syracuseStep 3419873 = 2564905) B2564905
theorem B2279915 : Blo 2279435 2279915 := bstep (se 1 (by rfl) ⟨1709936, by rfl⟩ : syracuseStep 2279915 = 3419873) B3419873
theorem B8216981 : Blo 2279435 8216981 := bbase (se 6 (by rfl) ⟨192585, by rfl⟩ : syracuseStep 8216981 = 385171) (by norm_num)
theorem B5477987 : Blo 2279435 5477987 := bstep (se 1 (by rfl) ⟨4108490, by rfl⟩ : syracuseStep 5477987 = 8216981) B8216981
theorem B14607965 : Blo 2279435 14607965 := bstep (se 3 (by rfl) ⟨2738993, by rfl⟩ : syracuseStep 14607965 = 5477987) B5477987
theorem B9738643 : Blo 2279435 9738643 := bstep (se 1 (by rfl) ⟨7303982, by rfl⟩ : syracuseStep 9738643 = 14607965) B14607965
theorem B12984857 : Blo 2279435 12984857 := bstep (se 2 (by rfl) ⟨4869321, by rfl⟩ : syracuseStep 12984857 = 9738643) B9738643
theorem B8656571 : Blo 2279435 8656571 := bstep (se 1 (by rfl) ⟨6492428, by rfl⟩ : syracuseStep 8656571 = 12984857) B12984857
theorem B5771047 : Blo 2279435 5771047 := bstep (se 1 (by rfl) ⟨4328285, by rfl⟩ : syracuseStep 5771047 = 8656571) B8656571
theorem B7694729 : Blo 2279435 7694729 := bstep (se 2 (by rfl) ⟨2885523, by rfl⟩ : syracuseStep 7694729 = 5771047) B5771047
theorem B5129819 : Blo 2279435 5129819 := bstep (se 1 (by rfl) ⟨3847364, by rfl⟩ : syracuseStep 5129819 = 7694729) B7694729
theorem B3419879 : Blo 2279435 3419879 := bstep (se 1 (by rfl) ⟨2564909, by rfl⟩ : syracuseStep 3419879 = 5129819) B5129819
theorem B2279919 : Blo 2279435 2279919 := bstep (se 1 (by rfl) ⟨1709939, by rfl⟩ : syracuseStep 2279919 = 3419879) B3419879
theorem B3419885 : Blo 2279435 3419885 := bbase (se 3 (by rfl) ⟨641228, by rfl⟩ : syracuseStep 3419885 = 1282457) (by norm_num)
theorem B2279923 : Blo 2279435 2279923 := bstep (se 1 (by rfl) ⟨1709942, by rfl⟩ : syracuseStep 2279923 = 3419885) B3419885
theorem B5129837 : Blo 2279435 5129837 := bbase (se 3 (by rfl) ⟨961844, by rfl⟩ : syracuseStep 5129837 = 1923689) (by norm_num)
theorem B3419891 : Blo 2279435 3419891 := bstep (se 1 (by rfl) ⟨2564918, by rfl⟩ : syracuseStep 3419891 = 5129837) B5129837
theorem B2279927 : Blo 2279435 2279927 := bstep (se 1 (by rfl) ⟨1709945, by rfl⟩ : syracuseStep 2279927 = 3419891) B3419891
theorem B4328309 : Blo 2279435 4328309 := bbase (se 5 (by rfl) ⟨202889, by rfl⟩ : syracuseStep 4328309 = 405779) (by norm_num)
theorem B2885539 : Blo 2279435 2885539 := bstep (se 1 (by rfl) ⟨2164154, by rfl⟩ : syracuseStep 2885539 = 4328309) B4328309
theorem B3847385 : Blo 2279435 3847385 := bstep (se 2 (by rfl) ⟨1442769, by rfl⟩ : syracuseStep 3847385 = 2885539) B2885539
theorem B2564923 : Blo 2279435 2564923 := bstep (se 1 (by rfl) ⟨1923692, by rfl⟩ : syracuseStep 2564923 = 3847385) B3847385
theorem B3419897 : Blo 2279435 3419897 := bstep (se 2 (by rfl) ⟨1282461, by rfl⟩ : syracuseStep 3419897 = 2564923) B2564923
theorem B2279931 : Blo 2279435 2279931 := bstep (se 1 (by rfl) ⟨1709948, by rfl⟩ : syracuseStep 2279931 = 3419897) B3419897
theorem B5552765 : Blo 2279435 5552765 := bbase (se 3 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 5552765 = 2082287) (by norm_num)
theorem B3701843 : Blo 2279435 3701843 := bstep (se 1 (by rfl) ⟨2776382, by rfl⟩ : syracuseStep 3701843 = 5552765) B5552765
theorem B2467895 : Blo 2279435 2467895 := bstep (se 1 (by rfl) ⟨1850921, by rfl⟩ : syracuseStep 2467895 = 3701843) B3701843
theorem B6581053 : Blo 2279435 6581053 := bstep (se 3 (by rfl) ⟨1233947, by rfl⟩ : syracuseStep 6581053 = 2467895) B2467895
theorem B8774737 : Blo 2279435 8774737 := bstep (se 2 (by rfl) ⟨3290526, by rfl⟩ : syracuseStep 8774737 = 6581053) B6581053
theorem B46798597 : Blo 2279435 46798597 := bstep (se 4 (by rfl) ⟨4387368, by rfl⟩ : syracuseStep 46798597 = 8774737) B8774737
theorem B62398129 : Blo 2279435 62398129 := bstep (se 2 (by rfl) ⟨23399298, by rfl⟩ : syracuseStep 62398129 = 46798597) B46798597
theorem B83197505 : Blo 2279435 83197505 := bstep (se 2 (by rfl) ⟨31199064, by rfl⟩ : syracuseStep 83197505 = 62398129) B62398129
theorem B55465003 : Blo 2279435 55465003 := bstep (se 1 (by rfl) ⟨41598752, by rfl⟩ : syracuseStep 55465003 = 83197505) B83197505
theorem B73953337 : Blo 2279435 73953337 := bstep (se 2 (by rfl) ⟨27732501, by rfl⟩ : syracuseStep 73953337 = 55465003) B55465003
theorem B98604449 : Blo 2279435 98604449 := bstep (se 2 (by rfl) ⟨36976668, by rfl⟩ : syracuseStep 98604449 = 73953337) B73953337
theorem B65736299 : Blo 2279435 65736299 := bstep (se 1 (by rfl) ⟨49302224, by rfl⟩ : syracuseStep 65736299 = 98604449) B98604449
theorem B43824199 : Blo 2279435 43824199 := bstep (se 1 (by rfl) ⟨32868149, by rfl⟩ : syracuseStep 43824199 = 65736299) B65736299
theorem B58432265 : Blo 2279435 58432265 := bstep (se 2 (by rfl) ⟨21912099, by rfl⟩ : syracuseStep 58432265 = 43824199) B43824199
theorem B38954843 : Blo 2279435 38954843 := bstep (se 1 (by rfl) ⟨29216132, by rfl⟩ : syracuseStep 38954843 = 58432265) B58432265
theorem B25969895 : Blo 2279435 25969895 := bstep (se 1 (by rfl) ⟨19477421, by rfl⟩ : syracuseStep 25969895 = 38954843) B38954843
theorem B17313263 : Blo 2279435 17313263 := bstep (se 1 (by rfl) ⟨12984947, by rfl⟩ : syracuseStep 17313263 = 25969895) B25969895
theorem B11542175 : Blo 2279435 11542175 := bstep (se 1 (by rfl) ⟨8656631, by rfl⟩ : syracuseStep 11542175 = 17313263) B17313263
theorem B7694783 : Blo 2279435 7694783 := bstep (se 1 (by rfl) ⟨5771087, by rfl⟩ : syracuseStep 7694783 = 11542175) B11542175
theorem B5129855 : Blo 2279435 5129855 := bstep (se 1 (by rfl) ⟨3847391, by rfl⟩ : syracuseStep 5129855 = 7694783) B7694783
theorem B3419903 : Blo 2279435 3419903 := bstep (se 1 (by rfl) ⟨2564927, by rfl⟩ : syracuseStep 3419903 = 5129855) B5129855
theorem B2279935 : Blo 2279435 2279935 := bstep (se 1 (by rfl) ⟨1709951, by rfl⟩ : syracuseStep 2279935 = 3419903) B3419903
theorem B3419909 : Blo 2279435 3419909 := bbase (se 4 (by rfl) ⟨320616, by rfl⟩ : syracuseStep 3419909 = 641233) (by norm_num)
theorem B2279939 : Blo 2279435 2279939 := bstep (se 1 (by rfl) ⟨1709954, by rfl⟩ : syracuseStep 2279939 = 3419909) B3419909
theorem B3847405 : Blo 2279435 3847405 := bbase (se 3 (by rfl) ⟨721388, by rfl⟩ : syracuseStep 3847405 = 1442777) (by norm_num)
theorem B5129873 : Blo 2279435 5129873 := bstep (se 2 (by rfl) ⟨1923702, by rfl⟩ : syracuseStep 5129873 = 3847405) B3847405
theorem B3419915 : Blo 2279435 3419915 := bstep (se 1 (by rfl) ⟨2564936, by rfl⟩ : syracuseStep 3419915 = 5129873) B5129873
theorem B2279943 : Blo 2279435 2279943 := bstep (se 1 (by rfl) ⟨1709957, by rfl⟩ : syracuseStep 2279943 = 3419915) B3419915
theorem B2564941 : Blo 2279435 2564941 := bbase (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) (by norm_num)
theorem B3419921 : Blo 2279435 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B2279947 : Blo 2279435 2279947 := bstep (se 1 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 2279947 = 3419921) B3419921
theorem B7694837 : Blo 2279435 7694837 := bbase (se 5 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 7694837 = 721391) (by norm_num)
theorem B5129891 : Blo 2279435 5129891 := bstep (se 1 (by rfl) ⟨3847418, by rfl⟩ : syracuseStep 5129891 = 7694837) B7694837
theorem B3419927 : Blo 2279435 3419927 := bstep (se 1 (by rfl) ⟨2564945, by rfl⟩ : syracuseStep 3419927 = 5129891) B5129891
theorem B2279951 : Blo 2279435 2279951 := bstep (se 1 (by rfl) ⟨1709963, by rfl⟩ : syracuseStep 2279951 = 3419927) B3419927
theorem B3419933 : Blo 2279435 3419933 := bbase (se 3 (by rfl) ⟨641237, by rfl⟩ : syracuseStep 3419933 = 1282475) (by norm_num)
theorem B2279955 : Blo 2279435 2279955 := bstep (se 1 (by rfl) ⟨1709966, by rfl⟩ : syracuseStep 2279955 = 3419933) B3419933
theorem B5129909 : Blo 2279435 5129909 := bbase (se 5 (by rfl) ⟨240464, by rfl⟩ : syracuseStep 5129909 = 480929) (by norm_num)
theorem B3419939 : Blo 2279435 3419939 := bstep (se 1 (by rfl) ⟨2564954, by rfl⟩ : syracuseStep 3419939 = 5129909) B5129909
theorem B2279959 : Blo 2279435 2279959 := bstep (se 1 (by rfl) ⟨1709969, by rfl⟩ : syracuseStep 2279959 = 3419939) B3419939
theorem B12985109 : Blo 2279435 12985109 := bbase (se 6 (by rfl) ⟨304338, by rfl⟩ : syracuseStep 12985109 = 608677) (by norm_num)
theorem B8656739 : Blo 2279435 8656739 := bstep (se 1 (by rfl) ⟨6492554, by rfl⟩ : syracuseStep 8656739 = 12985109) B12985109
theorem B5771159 : Blo 2279435 5771159 := bstep (se 1 (by rfl) ⟨4328369, by rfl⟩ : syracuseStep 5771159 = 8656739) B8656739
theorem B3847439 : Blo 2279435 3847439 := bstep (se 1 (by rfl) ⟨2885579, by rfl⟩ : syracuseStep 3847439 = 5771159) B5771159
theorem B2564959 : Blo 2279435 2564959 := bstep (se 1 (by rfl) ⟨1923719, by rfl⟩ : syracuseStep 2564959 = 3847439) B3847439
theorem B3419945 : Blo 2279435 3419945 := bstep (se 2 (by rfl) ⟨1282479, by rfl⟩ : syracuseStep 3419945 = 2564959) B2564959
theorem B2279963 : Blo 2279435 2279963 := bstep (se 1 (by rfl) ⟨1709972, by rfl⟩ : syracuseStep 2279963 = 3419945) B3419945
theorem B6492565 : Blo 2279435 6492565 := bbase (se 6 (by rfl) ⟨152169, by rfl⟩ : syracuseStep 6492565 = 304339) (by norm_num)
theorem B8656753 : Blo 2279435 8656753 := bstep (se 2 (by rfl) ⟨3246282, by rfl⟩ : syracuseStep 8656753 = 6492565) B6492565
theorem B11542337 : Blo 2279435 11542337 := bstep (se 2 (by rfl) ⟨4328376, by rfl⟩ : syracuseStep 11542337 = 8656753) B8656753
theorem B7694891 : Blo 2279435 7694891 := bstep (se 1 (by rfl) ⟨5771168, by rfl⟩ : syracuseStep 7694891 = 11542337) B11542337
theorem B5129927 : Blo 2279435 5129927 := bstep (se 1 (by rfl) ⟨3847445, by rfl⟩ : syracuseStep 5129927 = 7694891) B7694891
theorem B3419951 : Blo 2279435 3419951 := bstep (se 1 (by rfl) ⟨2564963, by rfl⟩ : syracuseStep 3419951 = 5129927) B5129927
theorem B2279967 : Blo 2279435 2279967 := bstep (se 1 (by rfl) ⟨1709975, by rfl⟩ : syracuseStep 2279967 = 3419951) B3419951
theorem B3419957 : Blo 2279435 3419957 := bbase (se 5 (by rfl) ⟨160310, by rfl⟩ : syracuseStep 3419957 = 320621) (by norm_num)
theorem B2279971 : Blo 2279435 2279971 := bstep (se 1 (by rfl) ⟨1709978, by rfl⟩ : syracuseStep 2279971 = 3419957) B3419957
theorem B5771189 : Blo 2279435 5771189 := bbase (se 5 (by rfl) ⟨270524, by rfl⟩ : syracuseStep 5771189 = 541049) (by norm_num)
theorem B3847459 : Blo 2279435 3847459 := bstep (se 1 (by rfl) ⟨2885594, by rfl⟩ : syracuseStep 3847459 = 5771189) B5771189
theorem B5129945 : Blo 2279435 5129945 := bstep (se 2 (by rfl) ⟨1923729, by rfl⟩ : syracuseStep 5129945 = 3847459) B3847459
theorem B3419963 : Blo 2279435 3419963 := bstep (se 1 (by rfl) ⟨2564972, by rfl⟩ : syracuseStep 3419963 = 5129945) B5129945
theorem B2279975 : Blo 2279435 2279975 := bstep (se 1 (by rfl) ⟨1709981, by rfl⟩ : syracuseStep 2279975 = 3419963) B3419963
theorem B2564977 : Blo 2279435 2564977 := bbase (se 2 (by rfl) ⟨961866, by rfl⟩ : syracuseStep 2564977 = 1923733) (by norm_num)
theorem B3419969 : Blo 2279435 3419969 := bstep (se 2 (by rfl) ⟨1282488, by rfl⟩ : syracuseStep 3419969 = 2564977) B2564977
theorem B2279979 : Blo 2279435 2279979 := bstep (se 1 (by rfl) ⟨1709984, by rfl⟩ : syracuseStep 2279979 = 3419969) B3419969
theorem B9738917 : Blo 2279435 9738917 := bbase (se 4 (by rfl) ⟨913023, by rfl⟩ : syracuseStep 9738917 = 1826047) (by norm_num)
theorem B6492611 : Blo 2279435 6492611 := bstep (se 1 (by rfl) ⟨4869458, by rfl⟩ : syracuseStep 6492611 = 9738917) B9738917
theorem B4328407 : Blo 2279435 4328407 := bstep (se 1 (by rfl) ⟨3246305, by rfl⟩ : syracuseStep 4328407 = 6492611) B6492611
theorem B5771209 : Blo 2279435 5771209 := bstep (se 2 (by rfl) ⟨2164203, by rfl⟩ : syracuseStep 5771209 = 4328407) B4328407
theorem B7694945 : Blo 2279435 7694945 := bstep (se 2 (by rfl) ⟨2885604, by rfl⟩ : syracuseStep 7694945 = 5771209) B5771209
theorem B5129963 : Blo 2279435 5129963 := bstep (se 1 (by rfl) ⟨3847472, by rfl⟩ : syracuseStep 5129963 = 7694945) B7694945
theorem B3419975 : Blo 2279435 3419975 := bstep (se 1 (by rfl) ⟨2564981, by rfl⟩ : syracuseStep 3419975 = 5129963) B5129963
theorem B2279983 : Blo 2279435 2279983 := bstep (se 1 (by rfl) ⟨1709987, by rfl⟩ : syracuseStep 2279983 = 3419975) B3419975
theorem B3419981 : Blo 2279435 3419981 := bbase (se 3 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 3419981 = 1282493) (by norm_num)
theorem B2279987 : Blo 2279435 2279987 := bstep (se 1 (by rfl) ⟨1709990, by rfl⟩ : syracuseStep 2279987 = 3419981) B3419981
theorem B5129981 : Blo 2279435 5129981 := bbase (se 3 (by rfl) ⟨961871, by rfl⟩ : syracuseStep 5129981 = 1923743) (by norm_num)
theorem B3419987 : Blo 2279435 3419987 := bstep (se 1 (by rfl) ⟨2564990, by rfl⟩ : syracuseStep 3419987 = 5129981) B5129981
theorem B2279991 : Blo 2279435 2279991 := bstep (se 1 (by rfl) ⟨1709993, by rfl⟩ : syracuseStep 2279991 = 3419987) B3419987
theorem B3847493 : Blo 2279435 3847493 := bbase (se 4 (by rfl) ⟨360702, by rfl⟩ : syracuseStep 3847493 = 721405) (by norm_num)
theorem B2564995 : Blo 2279435 2564995 := bstep (se 1 (by rfl) ⟨1923746, by rfl⟩ : syracuseStep 2564995 = 3847493) B3847493
theorem B3419993 : Blo 2279435 3419993 := bstep (se 2 (by rfl) ⟨1282497, by rfl⟩ : syracuseStep 3419993 = 2564995) B2564995
theorem B2279995 : Blo 2279435 2279995 := bstep (se 1 (by rfl) ⟨1709996, by rfl⟩ : syracuseStep 2279995 = 3419993) B3419993
theorem B17313749 : Blo 2279435 17313749 := bbase (se 7 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 17313749 = 405791) (by norm_num)
theorem B11542499 : Blo 2279435 11542499 := bstep (se 1 (by rfl) ⟨8656874, by rfl⟩ : syracuseStep 11542499 = 17313749) B17313749
theorem B7694999 : Blo 2279435 7694999 := bstep (se 1 (by rfl) ⟨5771249, by rfl⟩ : syracuseStep 7694999 = 11542499) B11542499
theorem B5129999 : Blo 2279435 5129999 := bstep (se 1 (by rfl) ⟨3847499, by rfl⟩ : syracuseStep 5129999 = 7694999) B7694999
theorem B3419999 : Blo 2279435 3419999 := bstep (se 1 (by rfl) ⟨2564999, by rfl⟩ : syracuseStep 3419999 = 5129999) B5129999
theorem B2279999 : Blo 2279435 2279999 := bstep (se 1 (by rfl) ⟨1709999, by rfl⟩ : syracuseStep 2279999 = 3419999) B3419999
theorem B3420005 : Blo 2279435 3420005 := bbase (se 4 (by rfl) ⟨320625, by rfl⟩ : syracuseStep 3420005 = 641251) (by norm_num)
theorem B2280003 : Blo 2279435 2280003 := bstep (se 1 (by rfl) ⟨1710002, by rfl⟩ : syracuseStep 2280003 = 3420005) B3420005
theorem B4328453 : Blo 2279435 4328453 := bbase (se 4 (by rfl) ⟨405792, by rfl⟩ : syracuseStep 4328453 = 811585) (by norm_num)
theorem B2885635 : Blo 2279435 2885635 := bstep (se 1 (by rfl) ⟨2164226, by rfl⟩ : syracuseStep 2885635 = 4328453) B4328453
theorem B3847513 : Blo 2279435 3847513 := bstep (se 2 (by rfl) ⟨1442817, by rfl⟩ : syracuseStep 3847513 = 2885635) B2885635
theorem B5130017 : Blo 2279435 5130017 := bstep (se 2 (by rfl) ⟨1923756, by rfl⟩ : syracuseStep 5130017 = 3847513) B3847513
theorem B3420011 : Blo 2279435 3420011 := bstep (se 1 (by rfl) ⟨2565008, by rfl⟩ : syracuseStep 3420011 = 5130017) B5130017
theorem B2280007 : Blo 2279435 2280007 := bstep (se 1 (by rfl) ⟨1710005, by rfl⟩ : syracuseStep 2280007 = 3420011) B3420011
theorem B2565013 : Blo 2279435 2565013 := bbase (se 6 (by rfl) ⟨60117, by rfl⟩ : syracuseStep 2565013 = 120235) (by norm_num)
theorem B3420017 : Blo 2279435 3420017 := bstep (se 2 (by rfl) ⟨1282506, by rfl⟩ : syracuseStep 3420017 = 2565013) B2565013
theorem B2280011 : Blo 2279435 2280011 := bstep (se 1 (by rfl) ⟨1710008, by rfl⟩ : syracuseStep 2280011 = 3420017) B3420017
theorem B2885645 : Blo 2279435 2885645 := bbase (se 3 (by rfl) ⟨541058, by rfl⟩ : syracuseStep 2885645 = 1082117) (by norm_num)
theorem B7695053 : Blo 2279435 7695053 := bstep (se 3 (by rfl) ⟨1442822, by rfl⟩ : syracuseStep 7695053 = 2885645) B2885645
theorem B5130035 : Blo 2279435 5130035 := bstep (se 1 (by rfl) ⟨3847526, by rfl⟩ : syracuseStep 5130035 = 7695053) B7695053
theorem B3420023 : Blo 2279435 3420023 := bstep (se 1 (by rfl) ⟨2565017, by rfl⟩ : syracuseStep 3420023 = 5130035) B5130035
theorem B2280015 : Blo 2279435 2280015 := bstep (se 1 (by rfl) ⟨1710011, by rfl⟩ : syracuseStep 2280015 = 3420023) B3420023
theorem B3420029 : Blo 2279435 3420029 := bbase (se 3 (by rfl) ⟨641255, by rfl⟩ : syracuseStep 3420029 = 1282511) (by norm_num)
theorem B2280019 : Blo 2279435 2280019 := bstep (se 1 (by rfl) ⟨1710014, by rfl⟩ : syracuseStep 2280019 = 3420029) B3420029
theorem B5130053 : Blo 2279435 5130053 := bbase (se 4 (by rfl) ⟨480942, by rfl⟩ : syracuseStep 5130053 = 961885) (by norm_num)
theorem B3420035 : Blo 2279435 3420035 := bstep (se 1 (by rfl) ⟨2565026, by rfl⟩ : syracuseStep 3420035 = 5130053) B5130053
theorem B2280023 : Blo 2279435 2280023 := bstep (se 1 (by rfl) ⟨1710017, by rfl⟩ : syracuseStep 2280023 = 3420035) B3420035
theorem B3652165 : Blo 2279435 3652165 := bbase (se 4 (by rfl) ⟨342390, by rfl⟩ : syracuseStep 3652165 = 684781) (by norm_num)
theorem B4869553 : Blo 2279435 4869553 := bstep (se 2 (by rfl) ⟨1826082, by rfl⟩ : syracuseStep 4869553 = 3652165) B3652165
theorem B6492737 : Blo 2279435 6492737 := bstep (se 2 (by rfl) ⟨2434776, by rfl⟩ : syracuseStep 6492737 = 4869553) B4869553
theorem B4328491 : Blo 2279435 4328491 := bstep (se 1 (by rfl) ⟨3246368, by rfl⟩ : syracuseStep 4328491 = 6492737) B6492737
theorem B5771321 : Blo 2279435 5771321 := bstep (se 2 (by rfl) ⟨2164245, by rfl⟩ : syracuseStep 5771321 = 4328491) B4328491
theorem B3847547 : Blo 2279435 3847547 := bstep (se 1 (by rfl) ⟨2885660, by rfl⟩ : syracuseStep 3847547 = 5771321) B5771321
theorem B2565031 : Blo 2279435 2565031 := bstep (se 1 (by rfl) ⟨1923773, by rfl⟩ : syracuseStep 2565031 = 3847547) B3847547
theorem B3420041 : Blo 2279435 3420041 := bstep (se 2 (by rfl) ⟨1282515, by rfl⟩ : syracuseStep 3420041 = 2565031) B2565031
theorem B2280027 : Blo 2279435 2280027 := bstep (se 1 (by rfl) ⟨1710020, by rfl⟩ : syracuseStep 2280027 = 3420041) B3420041
theorem B11542661 : Blo 2279435 11542661 := bbase (se 4 (by rfl) ⟨1082124, by rfl⟩ : syracuseStep 11542661 = 2164249) (by norm_num)
theorem B7695107 : Blo 2279435 7695107 := bstep (se 1 (by rfl) ⟨5771330, by rfl⟩ : syracuseStep 7695107 = 11542661) B11542661
theorem B5130071 : Blo 2279435 5130071 := bstep (se 1 (by rfl) ⟨3847553, by rfl⟩ : syracuseStep 5130071 = 7695107) B7695107
theorem B3420047 : Blo 2279435 3420047 := bstep (se 1 (by rfl) ⟨2565035, by rfl⟩ : syracuseStep 3420047 = 5130071) B5130071
theorem B2280031 : Blo 2279435 2280031 := bstep (se 1 (by rfl) ⟨1710023, by rfl⟩ : syracuseStep 2280031 = 3420047) B3420047
theorem B3420053 : Blo 2279435 3420053 := bbase (se 6 (by rfl) ⟨80157, by rfl⟩ : syracuseStep 3420053 = 160315) (by norm_num)
theorem B2280035 : Blo 2279435 2280035 := bstep (se 1 (by rfl) ⟨1710026, by rfl⟩ : syracuseStep 2280035 = 3420053) B3420053
theorem B2434789 : Blo 2279435 2434789 := bbase (se 4 (by rfl) ⟨228261, by rfl⟩ : syracuseStep 2434789 = 456523) (by norm_num)
theorem B12985541 : Blo 2279435 12985541 := bstep (se 4 (by rfl) ⟨1217394, by rfl⟩ : syracuseStep 12985541 = 2434789) B2434789
theorem B8657027 : Blo 2279435 8657027 := bstep (se 1 (by rfl) ⟨6492770, by rfl⟩ : syracuseStep 8657027 = 12985541) B12985541
theorem B5771351 : Blo 2279435 5771351 := bstep (se 1 (by rfl) ⟨4328513, by rfl⟩ : syracuseStep 5771351 = 8657027) B8657027
theorem B3847567 : Blo 2279435 3847567 := bstep (se 1 (by rfl) ⟨2885675, by rfl⟩ : syracuseStep 3847567 = 5771351) B5771351
theorem B5130089 : Blo 2279435 5130089 := bstep (se 2 (by rfl) ⟨1923783, by rfl⟩ : syracuseStep 5130089 = 3847567) B3847567
theorem B3420059 : Blo 2279435 3420059 := bstep (se 1 (by rfl) ⟨2565044, by rfl⟩ : syracuseStep 3420059 = 5130089) B5130089
theorem B2280039 : Blo 2279435 2280039 := bstep (se 1 (by rfl) ⟨1710029, by rfl⟩ : syracuseStep 2280039 = 3420059) B3420059
theorem B2565049 : Blo 2279435 2565049 := bbase (se 2 (by rfl) ⟨961893, by rfl⟩ : syracuseStep 2565049 = 1923787) (by norm_num)
theorem B3420065 : Blo 2279435 3420065 := bstep (se 2 (by rfl) ⟨1282524, by rfl⟩ : syracuseStep 3420065 = 2565049) B2565049
theorem B2280043 : Blo 2279435 2280043 := bstep (se 1 (by rfl) ⟨1710032, by rfl⟩ : syracuseStep 2280043 = 3420065) B3420065
theorem B12326165 : Blo 2279435 12326165 := bbase (se 6 (by rfl) ⟨288894, by rfl⟩ : syracuseStep 12326165 = 577789) (by norm_num)
theorem B8217443 : Blo 2279435 8217443 := bstep (se 1 (by rfl) ⟨6163082, by rfl⟩ : syracuseStep 8217443 = 12326165) B12326165
theorem B5478295 : Blo 2279435 5478295 := bstep (se 1 (by rfl) ⟨4108721, by rfl⟩ : syracuseStep 5478295 = 8217443) B8217443
theorem B7304393 : Blo 2279435 7304393 := bstep (se 2 (by rfl) ⟨2739147, by rfl⟩ : syracuseStep 7304393 = 5478295) B5478295
theorem B4869595 : Blo 2279435 4869595 := bstep (se 1 (by rfl) ⟨3652196, by rfl⟩ : syracuseStep 4869595 = 7304393) B7304393
theorem B6492793 : Blo 2279435 6492793 := bstep (se 2 (by rfl) ⟨2434797, by rfl⟩ : syracuseStep 6492793 = 4869595) B4869595
theorem B8657057 : Blo 2279435 8657057 := bstep (se 2 (by rfl) ⟨3246396, by rfl⟩ : syracuseStep 8657057 = 6492793) B6492793
theorem B5771371 : Blo 2279435 5771371 := bstep (se 1 (by rfl) ⟨4328528, by rfl⟩ : syracuseStep 5771371 = 8657057) B8657057
theorem B7695161 : Blo 2279435 7695161 := bstep (se 2 (by rfl) ⟨2885685, by rfl⟩ : syracuseStep 7695161 = 5771371) B5771371
theorem B5130107 : Blo 2279435 5130107 := bstep (se 1 (by rfl) ⟨3847580, by rfl⟩ : syracuseStep 5130107 = 7695161) B7695161
theorem B3420071 : Blo 2279435 3420071 := bstep (se 1 (by rfl) ⟨2565053, by rfl⟩ : syracuseStep 3420071 = 5130107) B5130107
theorem B2280047 : Blo 2279435 2280047 := bstep (se 1 (by rfl) ⟨1710035, by rfl⟩ : syracuseStep 2280047 = 3420071) B3420071
theorem B3420077 : Blo 2279435 3420077 := bbase (se 3 (by rfl) ⟨641264, by rfl⟩ : syracuseStep 3420077 = 1282529) (by norm_num)
theorem B2280051 : Blo 2279435 2280051 := bstep (se 1 (by rfl) ⟨1710038, by rfl⟩ : syracuseStep 2280051 = 3420077) B3420077
theorem B5130125 : Blo 2279435 5130125 := bbase (se 3 (by rfl) ⟨961898, by rfl⟩ : syracuseStep 5130125 = 1923797) (by norm_num)
theorem B3420083 : Blo 2279435 3420083 := bstep (se 1 (by rfl) ⟨2565062, by rfl⟩ : syracuseStep 3420083 = 5130125) B5130125
theorem B2280055 : Blo 2279435 2280055 := bstep (se 1 (by rfl) ⟨1710041, by rfl⟩ : syracuseStep 2280055 = 3420083) B3420083
theorem B2885701 : Blo 2279435 2885701 := bbase (se 4 (by rfl) ⟨270534, by rfl⟩ : syracuseStep 2885701 = 541069) (by norm_num)
theorem B3847601 : Blo 2279435 3847601 := bstep (se 2 (by rfl) ⟨1442850, by rfl⟩ : syracuseStep 3847601 = 2885701) B2885701
theorem B2565067 : Blo 2279435 2565067 := bstep (se 1 (by rfl) ⟨1923800, by rfl⟩ : syracuseStep 2565067 = 3847601) B3847601
theorem B3420089 : Blo 2279435 3420089 := bstep (se 2 (by rfl) ⟨1282533, by rfl⟩ : syracuseStep 3420089 = 2565067) B2565067
theorem B2280059 : Blo 2279435 2280059 := bstep (se 1 (by rfl) ⟨1710044, by rfl⟩ : syracuseStep 2280059 = 3420089) B3420089
theorem B2925077 : Blo 2279435 2925077 := bbase (se 6 (by rfl) ⟨68556, by rfl⟩ : syracuseStep 2925077 = 137113) (by norm_num)
theorem B31200821 : Blo 2279435 31200821 := bstep (se 5 (by rfl) ⟨1462538, by rfl⟩ : syracuseStep 31200821 = 2925077) B2925077
theorem B20800547 : Blo 2279435 20800547 := bstep (se 1 (by rfl) ⟨15600410, by rfl⟩ : syracuseStep 20800547 = 31200821) B31200821
theorem B13867031 : Blo 2279435 13867031 := bstep (se 1 (by rfl) ⟨10400273, by rfl⟩ : syracuseStep 13867031 = 20800547) B20800547
theorem B9244687 : Blo 2279435 9244687 := bstep (se 1 (by rfl) ⟨6933515, by rfl⟩ : syracuseStep 9244687 = 13867031) B13867031
theorem B12326249 : Blo 2279435 12326249 := bstep (se 2 (by rfl) ⟨4622343, by rfl⟩ : syracuseStep 12326249 = 9244687) B9244687
theorem B8217499 : Blo 2279435 8217499 := bstep (se 1 (by rfl) ⟨6163124, by rfl⟩ : syracuseStep 8217499 = 12326249) B12326249
theorem B10956665 : Blo 2279435 10956665 := bstep (se 2 (by rfl) ⟨4108749, by rfl⟩ : syracuseStep 10956665 = 8217499) B8217499
theorem B29217773 : Blo 2279435 29217773 := bstep (se 3 (by rfl) ⟨5478332, by rfl⟩ : syracuseStep 29217773 = 10956665) B10956665
theorem B19478515 : Blo 2279435 19478515 := bstep (se 1 (by rfl) ⟨14608886, by rfl⟩ : syracuseStep 19478515 = 29217773) B29217773
theorem B25971353 : Blo 2279435 25971353 := bstep (se 2 (by rfl) ⟨9739257, by rfl⟩ : syracuseStep 25971353 = 19478515) B19478515
theorem B17314235 : Blo 2279435 17314235 := bstep (se 1 (by rfl) ⟨12985676, by rfl⟩ : syracuseStep 17314235 = 25971353) B25971353
theorem B11542823 : Blo 2279435 11542823 := bstep (se 1 (by rfl) ⟨8657117, by rfl⟩ : syracuseStep 11542823 = 17314235) B17314235
theorem B7695215 : Blo 2279435 7695215 := bstep (se 1 (by rfl) ⟨5771411, by rfl⟩ : syracuseStep 7695215 = 11542823) B11542823
theorem B5130143 : Blo 2279435 5130143 := bstep (se 1 (by rfl) ⟨3847607, by rfl⟩ : syracuseStep 5130143 = 7695215) B7695215
theorem B3420095 : Blo 2279435 3420095 := bstep (se 1 (by rfl) ⟨2565071, by rfl⟩ : syracuseStep 3420095 = 5130143) B5130143
theorem B2280063 : Blo 2279435 2280063 := bstep (se 1 (by rfl) ⟨1710047, by rfl⟩ : syracuseStep 2280063 = 3420095) B3420095
theorem B3420101 : Blo 2279435 3420101 := bbase (se 4 (by rfl) ⟨320634, by rfl⟩ : syracuseStep 3420101 = 641269) (by norm_num)
theorem B2280067 : Blo 2279435 2280067 := bstep (se 1 (by rfl) ⟨1710050, by rfl⟩ : syracuseStep 2280067 = 3420101) B3420101
theorem B3847621 : Blo 2279435 3847621 := bbase (se 4 (by rfl) ⟨360714, by rfl⟩ : syracuseStep 3847621 = 721429) (by norm_num)
theorem B5130161 : Blo 2279435 5130161 := bstep (se 2 (by rfl) ⟨1923810, by rfl⟩ : syracuseStep 5130161 = 3847621) B3847621
theorem B3420107 : Blo 2279435 3420107 := bstep (se 1 (by rfl) ⟨2565080, by rfl⟩ : syracuseStep 3420107 = 5130161) B5130161
theorem B2280071 : Blo 2279435 2280071 := bstep (se 1 (by rfl) ⟨1710053, by rfl⟩ : syracuseStep 2280071 = 3420107) B3420107
theorem B2565085 : Blo 2279435 2565085 := bbase (se 3 (by rfl) ⟨480953, by rfl⟩ : syracuseStep 2565085 = 961907) (by norm_num)
theorem B3420113 : Blo 2279435 3420113 := bstep (se 2 (by rfl) ⟨1282542, by rfl⟩ : syracuseStep 3420113 = 2565085) B2565085
theorem B2280075 : Blo 2279435 2280075 := bstep (se 1 (by rfl) ⟨1710056, by rfl⟩ : syracuseStep 2280075 = 3420113) B3420113
theorem B7695269 : Blo 2279435 7695269 := bbase (se 4 (by rfl) ⟨721431, by rfl⟩ : syracuseStep 7695269 = 1442863) (by norm_num)
theorem B5130179 : Blo 2279435 5130179 := bstep (se 1 (by rfl) ⟨3847634, by rfl⟩ : syracuseStep 5130179 = 7695269) B7695269
theorem B3420119 : Blo 2279435 3420119 := bstep (se 1 (by rfl) ⟨2565089, by rfl⟩ : syracuseStep 3420119 = 5130179) B5130179
theorem B2280079 : Blo 2279435 2280079 := bstep (se 1 (by rfl) ⟨1710059, by rfl⟩ : syracuseStep 2280079 = 3420119) B3420119
theorem B3420125 : Blo 2279435 3420125 := bbase (se 3 (by rfl) ⟨641273, by rfl⟩ : syracuseStep 3420125 = 1282547) (by norm_num)
theorem B2280083 : Blo 2279435 2280083 := bstep (se 1 (by rfl) ⟨1710062, by rfl⟩ : syracuseStep 2280083 = 3420125) B3420125
theorem B5130197 : Blo 2279435 5130197 := bbase (se 7 (by rfl) ⟨60119, by rfl⟩ : syracuseStep 5130197 = 120239) (by norm_num)
theorem B3420131 : Blo 2279435 3420131 := bstep (se 1 (by rfl) ⟨2565098, by rfl⟩ : syracuseStep 3420131 = 5130197) B5130197
theorem B2280087 : Blo 2279435 2280087 := bstep (se 1 (by rfl) ⟨1710065, by rfl⟩ : syracuseStep 2280087 = 3420131) B3420131
theorem B2311201 : Blo 2279435 2311201 := bbase (se 2 (by rfl) ⟨866700, by rfl⟩ : syracuseStep 2311201 = 1733401) (by norm_num)
theorem B3081601 : Blo 2279435 3081601 := bstep (se 2 (by rfl) ⟨1155600, by rfl⟩ : syracuseStep 3081601 = 2311201) B2311201
theorem B4108801 : Blo 2279435 4108801 := bstep (se 2 (by rfl) ⟨1540800, by rfl⟩ : syracuseStep 4108801 = 3081601) B3081601
theorem B5478401 : Blo 2279435 5478401 := bstep (se 2 (by rfl) ⟨2054400, by rfl⟩ : syracuseStep 5478401 = 4108801) B4108801
theorem B14609069 : Blo 2279435 14609069 := bstep (se 3 (by rfl) ⟨2739200, by rfl⟩ : syracuseStep 14609069 = 5478401) B5478401
theorem B9739379 : Blo 2279435 9739379 := bstep (se 1 (by rfl) ⟨7304534, by rfl⟩ : syracuseStep 9739379 = 14609069) B14609069
theorem B6492919 : Blo 2279435 6492919 := bstep (se 1 (by rfl) ⟨4869689, by rfl⟩ : syracuseStep 6492919 = 9739379) B9739379
theorem B8657225 : Blo 2279435 8657225 := bstep (se 2 (by rfl) ⟨3246459, by rfl⟩ : syracuseStep 8657225 = 6492919) B6492919
theorem B5771483 : Blo 2279435 5771483 := bstep (se 1 (by rfl) ⟨4328612, by rfl⟩ : syracuseStep 5771483 = 8657225) B8657225
theorem B3847655 : Blo 2279435 3847655 := bstep (se 1 (by rfl) ⟨2885741, by rfl⟩ : syracuseStep 3847655 = 5771483) B5771483
theorem B2565103 : Blo 2279435 2565103 := bstep (se 1 (by rfl) ⟨1923827, by rfl⟩ : syracuseStep 2565103 = 3847655) B3847655
theorem B3420137 : Blo 2279435 3420137 := bstep (se 2 (by rfl) ⟨1282551, by rfl⟩ : syracuseStep 3420137 = 2565103) B2565103
theorem B2280091 : Blo 2279435 2280091 := bstep (se 1 (by rfl) ⟨1710068, by rfl⟩ : syracuseStep 2280091 = 3420137) B3420137
theorem B2739205 : Blo 2279435 2739205 := bbase (se 4 (by rfl) ⟨256800, by rfl⟩ : syracuseStep 2739205 = 513601) (by norm_num)
theorem B3652273 : Blo 2279435 3652273 := bstep (se 2 (by rfl) ⟨1369602, by rfl⟩ : syracuseStep 3652273 = 2739205) B2739205
theorem B19478789 : Blo 2279435 19478789 := bstep (se 4 (by rfl) ⟨1826136, by rfl⟩ : syracuseStep 19478789 = 3652273) B3652273
theorem B12985859 : Blo 2279435 12985859 := bstep (se 1 (by rfl) ⟨9739394, by rfl⟩ : syracuseStep 12985859 = 19478789) B19478789
theorem B8657239 : Blo 2279435 8657239 := bstep (se 1 (by rfl) ⟨6492929, by rfl⟩ : syracuseStep 8657239 = 12985859) B12985859
theorem B11542985 : Blo 2279435 11542985 := bstep (se 2 (by rfl) ⟨4328619, by rfl⟩ : syracuseStep 11542985 = 8657239) B8657239
theorem B7695323 : Blo 2279435 7695323 := bstep (se 1 (by rfl) ⟨5771492, by rfl⟩ : syracuseStep 7695323 = 11542985) B11542985
theorem B5130215 : Blo 2279435 5130215 := bstep (se 1 (by rfl) ⟨3847661, by rfl⟩ : syracuseStep 5130215 = 7695323) B7695323
theorem B3420143 : Blo 2279435 3420143 := bstep (se 1 (by rfl) ⟨2565107, by rfl⟩ : syracuseStep 3420143 = 5130215) B5130215
theorem B2280095 : Blo 2279435 2280095 := bstep (se 1 (by rfl) ⟨1710071, by rfl⟩ : syracuseStep 2280095 = 3420143) B3420143
theorem B3420149 : Blo 2279435 3420149 := bbase (se 5 (by rfl) ⟨160319, by rfl⟩ : syracuseStep 3420149 = 320639) (by norm_num)
theorem B2280099 : Blo 2279435 2280099 := bstep (se 1 (by rfl) ⟨1710074, by rfl⟩ : syracuseStep 2280099 = 3420149) B3420149
theorem B9244853 : Blo 2279435 9244853 := bbase (se 5 (by rfl) ⟨433352, by rfl⟩ : syracuseStep 9244853 = 866705) (by norm_num)
theorem B6163235 : Blo 2279435 6163235 := bstep (se 1 (by rfl) ⟨4622426, by rfl⟩ : syracuseStep 6163235 = 9244853) B9244853
theorem B4108823 : Blo 2279435 4108823 := bstep (se 1 (by rfl) ⟨3081617, by rfl⟩ : syracuseStep 4108823 = 6163235) B6163235
theorem B2739215 : Blo 2279435 2739215 := bstep (se 1 (by rfl) ⟨2054411, by rfl⟩ : syracuseStep 2739215 = 4108823) B4108823
theorem B7304573 : Blo 2279435 7304573 := bstep (se 3 (by rfl) ⟨1369607, by rfl⟩ : syracuseStep 7304573 = 2739215) B2739215
theorem B4869715 : Blo 2279435 4869715 := bstep (se 1 (by rfl) ⟨3652286, by rfl⟩ : syracuseStep 4869715 = 7304573) B7304573
theorem B6492953 : Blo 2279435 6492953 := bstep (se 2 (by rfl) ⟨2434857, by rfl⟩ : syracuseStep 6492953 = 4869715) B4869715
theorem B4328635 : Blo 2279435 4328635 := bstep (se 1 (by rfl) ⟨3246476, by rfl⟩ : syracuseStep 4328635 = 6492953) B6492953
theorem B5771513 : Blo 2279435 5771513 := bstep (se 2 (by rfl) ⟨2164317, by rfl⟩ : syracuseStep 5771513 = 4328635) B4328635
theorem B3847675 : Blo 2279435 3847675 := bstep (se 1 (by rfl) ⟨2885756, by rfl⟩ : syracuseStep 3847675 = 5771513) B5771513
theorem B5130233 : Blo 2279435 5130233 := bstep (se 2 (by rfl) ⟨1923837, by rfl⟩ : syracuseStep 5130233 = 3847675) B3847675
theorem B3420155 : Blo 2279435 3420155 := bstep (se 1 (by rfl) ⟨2565116, by rfl⟩ : syracuseStep 3420155 = 5130233) B5130233
theorem B2280103 : Blo 2279435 2280103 := bstep (se 1 (by rfl) ⟨1710077, by rfl⟩ : syracuseStep 2280103 = 3420155) B3420155
theorem B2565121 : Blo 2279435 2565121 := bbase (se 2 (by rfl) ⟨961920, by rfl⟩ : syracuseStep 2565121 = 1923841) (by norm_num)
theorem B3420161 : Blo 2279435 3420161 := bstep (se 2 (by rfl) ⟨1282560, by rfl⟩ : syracuseStep 3420161 = 2565121) B2565121
theorem B2280107 : Blo 2279435 2280107 := bstep (se 1 (by rfl) ⟨1710080, by rfl⟩ : syracuseStep 2280107 = 3420161) B3420161
theorem B5771533 : Blo 2279435 5771533 := bbase (se 3 (by rfl) ⟨1082162, by rfl⟩ : syracuseStep 5771533 = 2164325) (by norm_num)
theorem B7695377 : Blo 2279435 7695377 := bstep (se 2 (by rfl) ⟨2885766, by rfl⟩ : syracuseStep 7695377 = 5771533) B5771533
theorem B5130251 : Blo 2279435 5130251 := bstep (se 1 (by rfl) ⟨3847688, by rfl⟩ : syracuseStep 5130251 = 7695377) B7695377
theorem B3420167 : Blo 2279435 3420167 := bstep (se 1 (by rfl) ⟨2565125, by rfl⟩ : syracuseStep 3420167 = 5130251) B5130251
theorem B2280111 : Blo 2279435 2280111 := bstep (se 1 (by rfl) ⟨1710083, by rfl⟩ : syracuseStep 2280111 = 3420167) B3420167
theorem B3420173 : Blo 2279435 3420173 := bbase (se 3 (by rfl) ⟨641282, by rfl⟩ : syracuseStep 3420173 = 1282565) (by norm_num)
theorem B2280115 : Blo 2279435 2280115 := bstep (se 1 (by rfl) ⟨1710086, by rfl⟩ : syracuseStep 2280115 = 3420173) B3420173
theorem B5130269 : Blo 2279435 5130269 := bbase (se 3 (by rfl) ⟨961925, by rfl⟩ : syracuseStep 5130269 = 1923851) (by norm_num)
theorem B3420179 : Blo 2279435 3420179 := bstep (se 1 (by rfl) ⟨2565134, by rfl⟩ : syracuseStep 3420179 = 5130269) B5130269
theorem B2280119 : Blo 2279435 2280119 := bstep (se 1 (by rfl) ⟨1710089, by rfl⟩ : syracuseStep 2280119 = 3420179) B3420179
theorem B3847709 : Blo 2279435 3847709 := bbase (se 3 (by rfl) ⟨721445, by rfl⟩ : syracuseStep 3847709 = 1442891) (by norm_num)
theorem B2565139 : Blo 2279435 2565139 := bstep (se 1 (by rfl) ⟨1923854, by rfl⟩ : syracuseStep 2565139 = 3847709) B3847709
theorem B3420185 : Blo 2279435 3420185 := bstep (se 2 (by rfl) ⟨1282569, by rfl⟩ : syracuseStep 3420185 = 2565139) B2565139
theorem B2280123 : Blo 2279435 2280123 := bstep (se 1 (by rfl) ⟨1710092, by rfl⟩ : syracuseStep 2280123 = 3420185) B3420185
theorem B2311237 : Blo 2279435 2311237 := bbase (se 4 (by rfl) ⟨216678, by rfl⟩ : syracuseStep 2311237 = 433357) (by norm_num)
theorem B3081649 : Blo 2279435 3081649 := bstep (se 2 (by rfl) ⟨1155618, by rfl⟩ : syracuseStep 3081649 = 2311237) B2311237
theorem B4108865 : Blo 2279435 4108865 := bstep (se 2 (by rfl) ⟨1540824, by rfl⟩ : syracuseStep 4108865 = 3081649) B3081649
theorem B10956973 : Blo 2279435 10956973 := bstep (se 3 (by rfl) ⟨2054432, by rfl⟩ : syracuseStep 10956973 = 4108865) B4108865
theorem B14609297 : Blo 2279435 14609297 := bstep (se 2 (by rfl) ⟨5478486, by rfl⟩ : syracuseStep 14609297 = 10956973) B10956973
theorem B9739531 : Blo 2279435 9739531 := bstep (se 1 (by rfl) ⟨7304648, by rfl⟩ : syracuseStep 9739531 = 14609297) B14609297
theorem B12986041 : Blo 2279435 12986041 := bstep (se 2 (by rfl) ⟨4869765, by rfl⟩ : syracuseStep 12986041 = 9739531) B9739531
theorem B17314721 : Blo 2279435 17314721 := bstep (se 2 (by rfl) ⟨6493020, by rfl⟩ : syracuseStep 17314721 = 12986041) B12986041
theorem B11543147 : Blo 2279435 11543147 := bstep (se 1 (by rfl) ⟨8657360, by rfl⟩ : syracuseStep 11543147 = 17314721) B17314721
theorem B7695431 : Blo 2279435 7695431 := bstep (se 1 (by rfl) ⟨5771573, by rfl⟩ : syracuseStep 7695431 = 11543147) B11543147
theorem B5130287 : Blo 2279435 5130287 := bstep (se 1 (by rfl) ⟨3847715, by rfl⟩ : syracuseStep 5130287 = 7695431) B7695431
theorem B3420191 : Blo 2279435 3420191 := bstep (se 1 (by rfl) ⟨2565143, by rfl⟩ : syracuseStep 3420191 = 5130287) B5130287
theorem B2280127 : Blo 2279435 2280127 := bstep (se 1 (by rfl) ⟨1710095, by rfl⟩ : syracuseStep 2280127 = 3420191) B3420191
theorem B3420197 : Blo 2279435 3420197 := bbase (se 4 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 3420197 = 641287) (by norm_num)
theorem B2280131 : Blo 2279435 2280131 := bstep (se 1 (by rfl) ⟨1710098, by rfl⟩ : syracuseStep 2280131 = 3420197) B3420197
theorem B2885797 : Blo 2279435 2885797 := bbase (se 4 (by rfl) ⟨270543, by rfl⟩ : syracuseStep 2885797 = 541087) (by norm_num)
theorem B3847729 : Blo 2279435 3847729 := bstep (se 2 (by rfl) ⟨1442898, by rfl⟩ : syracuseStep 3847729 = 2885797) B2885797
theorem B5130305 : Blo 2279435 5130305 := bstep (se 2 (by rfl) ⟨1923864, by rfl⟩ : syracuseStep 5130305 = 3847729) B3847729
theorem B3420203 : Blo 2279435 3420203 := bstep (se 1 (by rfl) ⟨2565152, by rfl⟩ : syracuseStep 3420203 = 5130305) B5130305
theorem B2280135 : Blo 2279435 2280135 := bstep (se 1 (by rfl) ⟨1710101, by rfl⟩ : syracuseStep 2280135 = 3420203) B3420203
theorem B2565157 : Blo 2279435 2565157 := bbase (se 4 (by rfl) ⟨240483, by rfl⟩ : syracuseStep 2565157 = 480967) (by norm_num)
theorem B3420209 : Blo 2279435 3420209 := bstep (se 2 (by rfl) ⟨1282578, by rfl⟩ : syracuseStep 3420209 = 2565157) B2565157
theorem B2280139 : Blo 2279435 2280139 := bstep (se 1 (by rfl) ⟨1710104, by rfl⟩ : syracuseStep 2280139 = 3420209) B3420209
theorem B2925181 : Blo 2279435 2925181 := bbase (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) (by norm_num)
theorem B3900241 : Blo 2279435 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B20801285 : Blo 2279435 20801285 := bstep (se 4 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 20801285 = 3900241) B3900241
theorem B13867523 : Blo 2279435 13867523 := bstep (se 1 (by rfl) ⟨10400642, by rfl⟩ : syracuseStep 13867523 = 20801285) B20801285
theorem B9245015 : Blo 2279435 9245015 := bstep (se 1 (by rfl) ⟨6933761, by rfl⟩ : syracuseStep 9245015 = 13867523) B13867523
theorem B6163343 : Blo 2279435 6163343 := bstep (se 1 (by rfl) ⟨4622507, by rfl⟩ : syracuseStep 6163343 = 9245015) B9245015
theorem B4108895 : Blo 2279435 4108895 := bstep (se 1 (by rfl) ⟨3081671, by rfl⟩ : syracuseStep 4108895 = 6163343) B6163343
theorem B2739263 : Blo 2279435 2739263 := bstep (se 1 (by rfl) ⟨2054447, by rfl⟩ : syracuseStep 2739263 = 4108895) B4108895
theorem B7304701 : Blo 2279435 7304701 := bstep (se 3 (by rfl) ⟨1369631, by rfl⟩ : syracuseStep 7304701 = 2739263) B2739263
theorem B9739601 : Blo 2279435 9739601 := bstep (se 2 (by rfl) ⟨3652350, by rfl⟩ : syracuseStep 9739601 = 7304701) B7304701
theorem B6493067 : Blo 2279435 6493067 := bstep (se 1 (by rfl) ⟨4869800, by rfl⟩ : syracuseStep 6493067 = 9739601) B9739601
theorem B4328711 : Blo 2279435 4328711 := bstep (se 1 (by rfl) ⟨3246533, by rfl⟩ : syracuseStep 4328711 = 6493067) B6493067
theorem B2885807 : Blo 2279435 2885807 := bstep (se 1 (by rfl) ⟨2164355, by rfl⟩ : syracuseStep 2885807 = 4328711) B4328711
theorem B7695485 : Blo 2279435 7695485 := bstep (se 3 (by rfl) ⟨1442903, by rfl⟩ : syracuseStep 7695485 = 2885807) B2885807
theorem B5130323 : Blo 2279435 5130323 := bstep (se 1 (by rfl) ⟨3847742, by rfl⟩ : syracuseStep 5130323 = 7695485) B7695485
theorem B3420215 : Blo 2279435 3420215 := bstep (se 1 (by rfl) ⟨2565161, by rfl⟩ : syracuseStep 3420215 = 5130323) B5130323
theorem B2280143 : Blo 2279435 2280143 := bstep (se 1 (by rfl) ⟨1710107, by rfl⟩ : syracuseStep 2280143 = 3420215) B3420215
theorem B3420221 : Blo 2279435 3420221 := bbase (se 3 (by rfl) ⟨641291, by rfl⟩ : syracuseStep 3420221 = 1282583) (by norm_num)
theorem B2280147 : Blo 2279435 2280147 := bstep (se 1 (by rfl) ⟨1710110, by rfl⟩ : syracuseStep 2280147 = 3420221) B3420221
theorem B5130341 : Blo 2279435 5130341 := bbase (se 4 (by rfl) ⟨480969, by rfl⟩ : syracuseStep 5130341 = 961939) (by norm_num)
theorem B3420227 : Blo 2279435 3420227 := bstep (se 1 (by rfl) ⟨2565170, by rfl⟩ : syracuseStep 3420227 = 5130341) B5130341
theorem B2280151 : Blo 2279435 2280151 := bstep (se 1 (by rfl) ⟨1710113, by rfl⟩ : syracuseStep 2280151 = 3420227) B3420227
theorem B5771645 : Blo 2279435 5771645 := bbase (se 3 (by rfl) ⟨1082183, by rfl⟩ : syracuseStep 5771645 = 2164367) (by norm_num)
theorem B3847763 : Blo 2279435 3847763 := bstep (se 1 (by rfl) ⟨2885822, by rfl⟩ : syracuseStep 3847763 = 5771645) B5771645
theorem B2565175 : Blo 2279435 2565175 := bstep (se 1 (by rfl) ⟨1923881, by rfl⟩ : syracuseStep 2565175 = 3847763) B3847763
theorem B3420233 : Blo 2279435 3420233 := bstep (se 2 (by rfl) ⟨1282587, by rfl⟩ : syracuseStep 3420233 = 2565175) B2565175
theorem B2280155 : Blo 2279435 2280155 := bstep (se 1 (by rfl) ⟨1710116, by rfl⟩ : syracuseStep 2280155 = 3420233) B3420233
theorem B4328741 : Blo 2279435 4328741 := bbase (se 4 (by rfl) ⟨405819, by rfl⟩ : syracuseStep 4328741 = 811639) (by norm_num)
theorem B11543309 : Blo 2279435 11543309 := bstep (se 3 (by rfl) ⟨2164370, by rfl⟩ : syracuseStep 11543309 = 4328741) B4328741
theorem B7695539 : Blo 2279435 7695539 := bstep (se 1 (by rfl) ⟨5771654, by rfl⟩ : syracuseStep 7695539 = 11543309) B11543309
theorem B5130359 : Blo 2279435 5130359 := bstep (se 1 (by rfl) ⟨3847769, by rfl⟩ : syracuseStep 5130359 = 7695539) B7695539
theorem B3420239 : Blo 2279435 3420239 := bstep (se 1 (by rfl) ⟨2565179, by rfl⟩ : syracuseStep 3420239 = 5130359) B5130359
theorem B2280159 : Blo 2279435 2280159 := bstep (se 1 (by rfl) ⟨1710119, by rfl⟩ : syracuseStep 2280159 = 3420239) B3420239
theorem B3420245 : Blo 2279435 3420245 := bbase (se 8 (by rfl) ⟨20040, by rfl⟩ : syracuseStep 3420245 = 40081) (by norm_num)
theorem B2280163 : Blo 2279435 2280163 := bstep (se 1 (by rfl) ⟨1710122, by rfl⟩ : syracuseStep 2280163 = 3420245) B3420245
theorem B28113749 : Blo 2279435 28113749 := bbase (se 9 (by rfl) ⟨82364, by rfl⟩ : syracuseStep 28113749 = 164729) (by norm_num)
theorem B18742499 : Blo 2279435 18742499 := bstep (se 1 (by rfl) ⟨14056874, by rfl⟩ : syracuseStep 18742499 = 28113749) B28113749
theorem B12494999 : Blo 2279435 12494999 := bstep (se 1 (by rfl) ⟨9371249, by rfl⟩ : syracuseStep 12494999 = 18742499) B18742499
theorem B8329999 : Blo 2279435 8329999 := bstep (se 1 (by rfl) ⟨6247499, by rfl⟩ : syracuseStep 8329999 = 12494999) B12494999
theorem B11106665 : Blo 2279435 11106665 := bstep (se 2 (by rfl) ⟨4164999, by rfl⟩ : syracuseStep 11106665 = 8329999) B8329999
theorem B7404443 : Blo 2279435 7404443 := bstep (se 1 (by rfl) ⟨5553332, by rfl⟩ : syracuseStep 7404443 = 11106665) B11106665
theorem B4936295 : Blo 2279435 4936295 := bstep (se 1 (by rfl) ⟨3702221, by rfl⟩ : syracuseStep 4936295 = 7404443) B7404443
theorem B3290863 : Blo 2279435 3290863 := bstep (se 1 (by rfl) ⟨2468147, by rfl⟩ : syracuseStep 3290863 = 4936295) B4936295
theorem B4387817 : Blo 2279435 4387817 := bstep (se 2 (by rfl) ⟨1645431, by rfl⟩ : syracuseStep 4387817 = 3290863) B3290863
theorem B11700845 : Blo 2279435 11700845 := bstep (se 3 (by rfl) ⟨2193908, by rfl⟩ : syracuseStep 11700845 = 4387817) B4387817
theorem B7800563 : Blo 2279435 7800563 := bstep (se 1 (by rfl) ⟨5850422, by rfl⟩ : syracuseStep 7800563 = 11700845) B11700845
theorem B5200375 : Blo 2279435 5200375 := bstep (se 1 (by rfl) ⟨3900281, by rfl⟩ : syracuseStep 5200375 = 7800563) B7800563
theorem B6933833 : Blo 2279435 6933833 := bstep (se 2 (by rfl) ⟨2600187, by rfl⟩ : syracuseStep 6933833 = 5200375) B5200375
theorem B4622555 : Blo 2279435 4622555 := bstep (se 1 (by rfl) ⟨3466916, by rfl⟩ : syracuseStep 4622555 = 6933833) B6933833
theorem B12326813 : Blo 2279435 12326813 := bstep (se 3 (by rfl) ⟨2311277, by rfl⟩ : syracuseStep 12326813 = 4622555) B4622555
theorem B8217875 : Blo 2279435 8217875 := bstep (se 1 (by rfl) ⟨6163406, by rfl⟩ : syracuseStep 8217875 = 12326813) B12326813
theorem B21914333 : Blo 2279435 21914333 := bstep (se 3 (by rfl) ⟨4108937, by rfl⟩ : syracuseStep 21914333 = 8217875) B8217875
theorem B14609555 : Blo 2279435 14609555 := bstep (se 1 (by rfl) ⟨10957166, by rfl⟩ : syracuseStep 14609555 = 21914333) B21914333
theorem B9739703 : Blo 2279435 9739703 := bstep (se 1 (by rfl) ⟨7304777, by rfl⟩ : syracuseStep 9739703 = 14609555) B14609555
theorem B6493135 : Blo 2279435 6493135 := bstep (se 1 (by rfl) ⟨4869851, by rfl⟩ : syracuseStep 6493135 = 9739703) B9739703
theorem B8657513 : Blo 2279435 8657513 := bstep (se 2 (by rfl) ⟨3246567, by rfl⟩ : syracuseStep 8657513 = 6493135) B6493135
theorem B5771675 : Blo 2279435 5771675 := bstep (se 1 (by rfl) ⟨4328756, by rfl⟩ : syracuseStep 5771675 = 8657513) B8657513
theorem B3847783 : Blo 2279435 3847783 := bstep (se 1 (by rfl) ⟨2885837, by rfl⟩ : syracuseStep 3847783 = 5771675) B5771675
theorem B5130377 : Blo 2279435 5130377 := bstep (se 2 (by rfl) ⟨1923891, by rfl⟩ : syracuseStep 5130377 = 3847783) B3847783
theorem B3420251 : Blo 2279435 3420251 := bstep (se 1 (by rfl) ⟨2565188, by rfl⟩ : syracuseStep 3420251 = 5130377) B5130377
theorem B2280167 : Blo 2279435 2280167 := bstep (se 1 (by rfl) ⟨1710125, by rfl⟩ : syracuseStep 2280167 = 3420251) B3420251
theorem B2565193 : Blo 2279435 2565193 := bbase (se 2 (by rfl) ⟨961947, by rfl⟩ : syracuseStep 2565193 = 1923895) (by norm_num)
theorem B3420257 : Blo 2279435 3420257 := bstep (se 2 (by rfl) ⟨1282596, by rfl⟩ : syracuseStep 3420257 = 2565193) B2565193
theorem B2280171 : Blo 2279435 2280171 := bstep (se 1 (by rfl) ⟨1710128, by rfl⟩ : syracuseStep 2280171 = 3420257) B3420257
theorem B2739301 : Blo 2279435 2739301 := bbase (se 4 (by rfl) ⟨256809, by rfl⟩ : syracuseStep 2739301 = 513619) (by norm_num)
theorem B14609605 : Blo 2279435 14609605 := bstep (se 4 (by rfl) ⟨1369650, by rfl⟩ : syracuseStep 14609605 = 2739301) B2739301
theorem B19479473 : Blo 2279435 19479473 := bstep (se 2 (by rfl) ⟨7304802, by rfl⟩ : syracuseStep 19479473 = 14609605) B14609605
theorem B12986315 : Blo 2279435 12986315 := bstep (se 1 (by rfl) ⟨9739736, by rfl⟩ : syracuseStep 12986315 = 19479473) B19479473
theorem B8657543 : Blo 2279435 8657543 := bstep (se 1 (by rfl) ⟨6493157, by rfl⟩ : syracuseStep 8657543 = 12986315) B12986315
theorem B5771695 : Blo 2279435 5771695 := bstep (se 1 (by rfl) ⟨4328771, by rfl⟩ : syracuseStep 5771695 = 8657543) B8657543
theorem B7695593 : Blo 2279435 7695593 := bstep (se 2 (by rfl) ⟨2885847, by rfl⟩ : syracuseStep 7695593 = 5771695) B5771695
theorem B5130395 : Blo 2279435 5130395 := bstep (se 1 (by rfl) ⟨3847796, by rfl⟩ : syracuseStep 5130395 = 7695593) B7695593
theorem B3420263 : Blo 2279435 3420263 := bstep (se 1 (by rfl) ⟨2565197, by rfl⟩ : syracuseStep 3420263 = 5130395) B5130395
theorem B2280175 : Blo 2279435 2280175 := bstep (se 1 (by rfl) ⟨1710131, by rfl⟩ : syracuseStep 2280175 = 3420263) B3420263
theorem B3420269 : Blo 2279435 3420269 := bbase (se 3 (by rfl) ⟨641300, by rfl⟩ : syracuseStep 3420269 = 1282601) (by norm_num)
theorem B2280179 : Blo 2279435 2280179 := bstep (se 1 (by rfl) ⟨1710134, by rfl⟩ : syracuseStep 2280179 = 3420269) B3420269
theorem B5130413 : Blo 2279435 5130413 := bbase (se 3 (by rfl) ⟨961952, by rfl⟩ : syracuseStep 5130413 = 1923905) (by norm_num)
theorem B3420275 : Blo 2279435 3420275 := bstep (se 1 (by rfl) ⟨2565206, by rfl⟩ : syracuseStep 3420275 = 5130413) B5130413
theorem B2280183 : Blo 2279435 2280183 := bstep (se 1 (by rfl) ⟨1710137, by rfl⟩ : syracuseStep 2280183 = 3420275) B3420275
theorem B4622597 : Blo 2279435 4622597 := bbase (se 4 (by rfl) ⟨433368, by rfl⟩ : syracuseStep 4622597 = 866737) (by norm_num)
theorem B3081731 : Blo 2279435 3081731 := bstep (se 1 (by rfl) ⟨2311298, by rfl⟩ : syracuseStep 3081731 = 4622597) B4622597
theorem B8217949 : Blo 2279435 8217949 := bstep (se 3 (by rfl) ⟨1540865, by rfl⟩ : syracuseStep 8217949 = 3081731) B3081731
theorem B10957265 : Blo 2279435 10957265 := bstep (se 2 (by rfl) ⟨4108974, by rfl⟩ : syracuseStep 10957265 = 8217949) B8217949
theorem B7304843 : Blo 2279435 7304843 := bstep (se 1 (by rfl) ⟨5478632, by rfl⟩ : syracuseStep 7304843 = 10957265) B10957265
theorem B4869895 : Blo 2279435 4869895 := bstep (se 1 (by rfl) ⟨3652421, by rfl⟩ : syracuseStep 4869895 = 7304843) B7304843
theorem B6493193 : Blo 2279435 6493193 := bstep (se 2 (by rfl) ⟨2434947, by rfl⟩ : syracuseStep 6493193 = 4869895) B4869895
theorem B4328795 : Blo 2279435 4328795 := bstep (se 1 (by rfl) ⟨3246596, by rfl⟩ : syracuseStep 4328795 = 6493193) B6493193
theorem B2885863 : Blo 2279435 2885863 := bstep (se 1 (by rfl) ⟨2164397, by rfl⟩ : syracuseStep 2885863 = 4328795) B4328795
theorem B3847817 : Blo 2279435 3847817 := bstep (se 2 (by rfl) ⟨1442931, by rfl⟩ : syracuseStep 3847817 = 2885863) B2885863
theorem B2565211 : Blo 2279435 2565211 := bstep (se 1 (by rfl) ⟨1923908, by rfl⟩ : syracuseStep 2565211 = 3847817) B3847817
theorem B3420281 : Blo 2279435 3420281 := bstep (se 2 (by rfl) ⟨1282605, by rfl⟩ : syracuseStep 3420281 = 2565211) B2565211
theorem B2280187 : Blo 2279435 2280187 := bstep (se 1 (by rfl) ⟨1710140, by rfl⟩ : syracuseStep 2280187 = 3420281) B3420281
theorem B29219413 : Blo 2279435 29219413 := bbase (se 8 (by rfl) ⟨171207, by rfl⟩ : syracuseStep 29219413 = 342415) (by norm_num)
theorem B38959217 : Blo 2279435 38959217 := bstep (se 2 (by rfl) ⟨14609706, by rfl⟩ : syracuseStep 38959217 = 29219413) B29219413
theorem B25972811 : Blo 2279435 25972811 := bstep (se 1 (by rfl) ⟨19479608, by rfl⟩ : syracuseStep 25972811 = 38959217) B38959217
theorem B17315207 : Blo 2279435 17315207 := bstep (se 1 (by rfl) ⟨12986405, by rfl⟩ : syracuseStep 17315207 = 25972811) B25972811
theorem B11543471 : Blo 2279435 11543471 := bstep (se 1 (by rfl) ⟨8657603, by rfl⟩ : syracuseStep 11543471 = 17315207) B17315207
theorem B7695647 : Blo 2279435 7695647 := bstep (se 1 (by rfl) ⟨5771735, by rfl⟩ : syracuseStep 7695647 = 11543471) B11543471
theorem B5130431 : Blo 2279435 5130431 := bstep (se 1 (by rfl) ⟨3847823, by rfl⟩ : syracuseStep 5130431 = 7695647) B7695647
theorem B3420287 : Blo 2279435 3420287 := bstep (se 1 (by rfl) ⟨2565215, by rfl⟩ : syracuseStep 3420287 = 5130431) B5130431
theorem B2280191 : Blo 2279435 2280191 := bstep (se 1 (by rfl) ⟨1710143, by rfl⟩ : syracuseStep 2280191 = 3420287) B3420287
theorem B3420293 : Blo 2279435 3420293 := bbase (se 4 (by rfl) ⟨320652, by rfl⟩ : syracuseStep 3420293 = 641305) (by norm_num)
theorem B2280195 : Blo 2279435 2280195 := bstep (se 1 (by rfl) ⟨1710146, by rfl⟩ : syracuseStep 2280195 = 3420293) B3420293
theorem B3847837 : Blo 2279435 3847837 := bbase (se 3 (by rfl) ⟨721469, by rfl⟩ : syracuseStep 3847837 = 1442939) (by norm_num)
theorem B5130449 : Blo 2279435 5130449 := bstep (se 2 (by rfl) ⟨1923918, by rfl⟩ : syracuseStep 5130449 = 3847837) B3847837
theorem B3420299 : Blo 2279435 3420299 := bstep (se 1 (by rfl) ⟨2565224, by rfl⟩ : syracuseStep 3420299 = 5130449) B5130449
theorem B2280199 : Blo 2279435 2280199 := bstep (se 1 (by rfl) ⟨1710149, by rfl⟩ : syracuseStep 2280199 = 3420299) B3420299
theorem B2565229 : Blo 2279435 2565229 := bbase (se 3 (by rfl) ⟨480980, by rfl⟩ : syracuseStep 2565229 = 961961) (by norm_num)
theorem B3420305 : Blo 2279435 3420305 := bstep (se 2 (by rfl) ⟨1282614, by rfl⟩ : syracuseStep 3420305 = 2565229) B2565229
theorem B2280203 : Blo 2279435 2280203 := bstep (se 1 (by rfl) ⟨1710152, by rfl⟩ : syracuseStep 2280203 = 3420305) B3420305
theorem B7695701 : Blo 2279435 7695701 := bbase (se 11 (by rfl) ⟨5636, by rfl⟩ : syracuseStep 7695701 = 11273) (by norm_num)
theorem B5130467 : Blo 2279435 5130467 := bstep (se 1 (by rfl) ⟨3847850, by rfl⟩ : syracuseStep 5130467 = 7695701) B7695701
theorem B3420311 : Blo 2279435 3420311 := bstep (se 1 (by rfl) ⟨2565233, by rfl⟩ : syracuseStep 3420311 = 5130467) B5130467
theorem B2280207 : Blo 2279435 2280207 := bstep (se 1 (by rfl) ⟨1710155, by rfl⟩ : syracuseStep 2280207 = 3420311) B3420311
theorem B3420317 : Blo 2279435 3420317 := bbase (se 3 (by rfl) ⟨641309, by rfl⟩ : syracuseStep 3420317 = 1282619) (by norm_num)
theorem B2280211 : Blo 2279435 2280211 := bstep (se 1 (by rfl) ⟨1710158, by rfl⟩ : syracuseStep 2280211 = 3420317) B3420317
theorem B5130485 : Blo 2279435 5130485 := bbase (se 5 (by rfl) ⟨240491, by rfl⟩ : syracuseStep 5130485 = 480983) (by norm_num)
theorem B3420323 : Blo 2279435 3420323 := bstep (se 1 (by rfl) ⟨2565242, by rfl⟩ : syracuseStep 3420323 = 5130485) B5130485
theorem B2280215 : Blo 2279435 2280215 := bstep (se 1 (by rfl) ⟨1710161, by rfl⟩ : syracuseStep 2280215 = 3420323) B3420323
theorem B2776729 : Blo 2279435 2776729 := bbase (se 2 (by rfl) ⟨1041273, by rfl⟩ : syracuseStep 2776729 = 2082547) (by norm_num)
theorem B3702305 : Blo 2279435 3702305 := bstep (se 2 (by rfl) ⟨1388364, by rfl⟩ : syracuseStep 3702305 = 2776729) B2776729
theorem B9872813 : Blo 2279435 9872813 := bstep (se 3 (by rfl) ⟨1851152, by rfl⟩ : syracuseStep 9872813 = 3702305) B3702305
theorem B26327501 : Blo 2279435 26327501 := bstep (se 3 (by rfl) ⟨4936406, by rfl⟩ : syracuseStep 26327501 = 9872813) B9872813
theorem B17551667 : Blo 2279435 17551667 := bstep (se 1 (by rfl) ⟨13163750, by rfl⟩ : syracuseStep 17551667 = 26327501) B26327501
theorem B11701111 : Blo 2279435 11701111 := bstep (se 1 (by rfl) ⟨8775833, by rfl⟩ : syracuseStep 11701111 = 17551667) B17551667
theorem B15601481 : Blo 2279435 15601481 := bstep (se 2 (by rfl) ⟨5850555, by rfl⟩ : syracuseStep 15601481 = 11701111) B11701111
theorem B10400987 : Blo 2279435 10400987 := bstep (se 1 (by rfl) ⟨7800740, by rfl⟩ : syracuseStep 10400987 = 15601481) B15601481
theorem B6933991 : Blo 2279435 6933991 := bstep (se 1 (by rfl) ⟨5200493, by rfl⟩ : syracuseStep 6933991 = 10400987) B10400987
theorem B9245321 : Blo 2279435 9245321 := bstep (se 2 (by rfl) ⟨3466995, by rfl⟩ : syracuseStep 9245321 = 6933991) B6933991
theorem B6163547 : Blo 2279435 6163547 := bstep (se 1 (by rfl) ⟨4622660, by rfl⟩ : syracuseStep 6163547 = 9245321) B9245321
theorem B16436125 : Blo 2279435 16436125 := bstep (se 3 (by rfl) ⟨3081773, by rfl⟩ : syracuseStep 16436125 = 6163547) B6163547
theorem B21914833 : Blo 2279435 21914833 := bstep (se 2 (by rfl) ⟨8218062, by rfl⟩ : syracuseStep 21914833 = 16436125) B16436125
theorem B29219777 : Blo 2279435 29219777 := bstep (se 2 (by rfl) ⟨10957416, by rfl⟩ : syracuseStep 29219777 = 21914833) B21914833
theorem B19479851 : Blo 2279435 19479851 := bstep (se 1 (by rfl) ⟨14609888, by rfl⟩ : syracuseStep 19479851 = 29219777) B29219777
theorem B12986567 : Blo 2279435 12986567 := bstep (se 1 (by rfl) ⟨9739925, by rfl⟩ : syracuseStep 12986567 = 19479851) B19479851
theorem B8657711 : Blo 2279435 8657711 := bstep (se 1 (by rfl) ⟨6493283, by rfl⟩ : syracuseStep 8657711 = 12986567) B12986567
theorem B5771807 : Blo 2279435 5771807 := bstep (se 1 (by rfl) ⟨4328855, by rfl⟩ : syracuseStep 5771807 = 8657711) B8657711
theorem B3847871 : Blo 2279435 3847871 := bstep (se 1 (by rfl) ⟨2885903, by rfl⟩ : syracuseStep 3847871 = 5771807) B5771807
theorem B2565247 : Blo 2279435 2565247 := bstep (se 1 (by rfl) ⟨1923935, by rfl⟩ : syracuseStep 2565247 = 3847871) B3847871
theorem B3420329 : Blo 2279435 3420329 := bstep (se 2 (by rfl) ⟨1282623, by rfl⟩ : syracuseStep 3420329 = 2565247) B2565247
theorem B2280219 : Blo 2279435 2280219 := bstep (se 1 (by rfl) ⟨1710164, by rfl⟩ : syracuseStep 2280219 = 3420329) B3420329
theorem B4759597 : Blo 2279435 4759597 := bbase (se 3 (by rfl) ⟨892424, by rfl⟩ : syracuseStep 4759597 = 1784849) (by norm_num)
theorem B6346129 : Blo 2279435 6346129 := bstep (se 2 (by rfl) ⟨2379798, by rfl⟩ : syracuseStep 6346129 = 4759597) B4759597
theorem B8461505 : Blo 2279435 8461505 := bstep (se 2 (by rfl) ⟨3173064, by rfl⟩ : syracuseStep 8461505 = 6346129) B6346129
theorem B22564013 : Blo 2279435 22564013 := bstep (se 3 (by rfl) ⟨4230752, by rfl⟩ : syracuseStep 22564013 = 8461505) B8461505
theorem B60170701 : Blo 2279435 60170701 := bstep (se 3 (by rfl) ⟨11282006, by rfl⟩ : syracuseStep 60170701 = 22564013) B22564013
theorem B80227601 : Blo 2279435 80227601 := bstep (se 2 (by rfl) ⟨30085350, by rfl⟩ : syracuseStep 80227601 = 60170701) B60170701
theorem B53485067 : Blo 2279435 53485067 := bstep (se 1 (by rfl) ⟨40113800, by rfl⟩ : syracuseStep 53485067 = 80227601) B80227601
theorem B142626845 : Blo 2279435 142626845 := bstep (se 3 (by rfl) ⟨26742533, by rfl⟩ : syracuseStep 142626845 = 53485067) B53485067
theorem B380338253 : Blo 2279435 380338253 := bstep (se 3 (by rfl) ⟨71313422, by rfl⟩ : syracuseStep 380338253 = 142626845) B142626845
theorem B253558835 : Blo 2279435 253558835 := bstep (se 1 (by rfl) ⟨190169126, by rfl⟩ : syracuseStep 253558835 = 380338253) B380338253
theorem B169039223 : Blo 2279435 169039223 := bstep (se 1 (by rfl) ⟨126779417, by rfl⟩ : syracuseStep 169039223 = 253558835) B253558835
theorem B112692815 : Blo 2279435 112692815 := bstep (se 1 (by rfl) ⟨84519611, by rfl⟩ : syracuseStep 112692815 = 169039223) B169039223
theorem B75128543 : Blo 2279435 75128543 := bstep (se 1 (by rfl) ⟨56346407, by rfl⟩ : syracuseStep 75128543 = 112692815) B112692815
theorem B50085695 : Blo 2279435 50085695 := bstep (se 1 (by rfl) ⟨37564271, by rfl⟩ : syracuseStep 50085695 = 75128543) B75128543
theorem B33390463 : Blo 2279435 33390463 := bstep (se 1 (by rfl) ⟨25042847, by rfl⟩ : syracuseStep 33390463 = 50085695) B50085695
theorem B44520617 : Blo 2279435 44520617 := bstep (se 2 (by rfl) ⟨16695231, by rfl⟩ : syracuseStep 44520617 = 33390463) B33390463
theorem B29680411 : Blo 2279435 29680411 := bstep (se 1 (by rfl) ⟨22260308, by rfl⟩ : syracuseStep 29680411 = 44520617) B44520617
theorem B39573881 : Blo 2279435 39573881 := bstep (se 2 (by rfl) ⟨14840205, by rfl⟩ : syracuseStep 39573881 = 29680411) B29680411
theorem B26382587 : Blo 2279435 26382587 := bstep (se 1 (by rfl) ⟨19786940, by rfl⟩ : syracuseStep 26382587 = 39573881) B39573881
theorem B281414261 : Blo 2279435 281414261 := bstep (se 5 (by rfl) ⟨13191293, by rfl⟩ : syracuseStep 281414261 = 26382587) B26382587
theorem B187609507 : Blo 2279435 187609507 := bstep (se 1 (by rfl) ⟨140707130, by rfl⟩ : syracuseStep 187609507 = 281414261) B281414261
theorem B1000584037 : Blo 2279435 1000584037 := bstep (se 4 (by rfl) ⟨93804753, by rfl⟩ : syracuseStep 1000584037 = 187609507) B187609507
theorem B1334112049 : Blo 2279435 1334112049 := bstep (se 2 (by rfl) ⟨500292018, by rfl⟩ : syracuseStep 1334112049 = 1000584037) B1000584037
theorem B1778816065 : Blo 2279435 1778816065 := bstep (se 2 (by rfl) ⟨667056024, by rfl⟩ : syracuseStep 1778816065 = 1334112049) B1334112049
theorem B2371754753 : Blo 2279435 2371754753 := bstep (se 2 (by rfl) ⟨889408032, by rfl⟩ : syracuseStep 2371754753 = 1778816065) B1778816065
theorem B1581169835 : Blo 2279435 1581169835 := bstep (se 1 (by rfl) ⟨1185877376, by rfl⟩ : syracuseStep 1581169835 = 2371754753) B2371754753
theorem B4216452893 : Blo 2279435 4216452893 := bstep (se 3 (by rfl) ⟨790584917, by rfl⟩ : syracuseStep 4216452893 = 1581169835) B1581169835
theorem B2810968595 : Blo 2279435 2810968595 := bstep (se 1 (by rfl) ⟨2108226446, by rfl⟩ : syracuseStep 2810968595 = 4216452893) B4216452893
theorem B1873979063 : Blo 2279435 1873979063 := bstep (se 1 (by rfl) ⟨1405484297, by rfl⟩ : syracuseStep 1873979063 = 2810968595) B2810968595
theorem B1249319375 : Blo 2279435 1249319375 := bstep (se 1 (by rfl) ⟨936989531, by rfl⟩ : syracuseStep 1249319375 = 1873979063) B1873979063
theorem B832879583 : Blo 2279435 832879583 := bstep (se 1 (by rfl) ⟨624659687, by rfl⟩ : syracuseStep 832879583 = 1249319375) B1249319375
theorem B555253055 : Blo 2279435 555253055 := bstep (se 1 (by rfl) ⟨416439791, by rfl⟩ : syracuseStep 555253055 = 832879583) B832879583
theorem B370168703 : Blo 2279435 370168703 := bstep (se 1 (by rfl) ⟨277626527, by rfl⟩ : syracuseStep 370168703 = 555253055) B555253055
theorem B246779135 : Blo 2279435 246779135 := bstep (se 1 (by rfl) ⟨185084351, by rfl⟩ : syracuseStep 246779135 = 370168703) B370168703
theorem B164519423 : Blo 2279435 164519423 := bstep (se 1 (by rfl) ⟨123389567, by rfl⟩ : syracuseStep 164519423 = 246779135) B246779135
theorem B109679615 : Blo 2279435 109679615 := bstep (se 1 (by rfl) ⟨82259711, by rfl⟩ : syracuseStep 109679615 = 164519423) B164519423
theorem B73119743 : Blo 2279435 73119743 := bstep (se 1 (by rfl) ⟨54839807, by rfl⟩ : syracuseStep 73119743 = 109679615) B109679615
theorem B48746495 : Blo 2279435 48746495 := bstep (se 1 (by rfl) ⟨36559871, by rfl⟩ : syracuseStep 48746495 = 73119743) B73119743
theorem B129990653 : Blo 2279435 129990653 := bstep (se 3 (by rfl) ⟨24373247, by rfl⟩ : syracuseStep 129990653 = 48746495) B48746495
theorem B86660435 : Blo 2279435 86660435 := bstep (se 1 (by rfl) ⟨64995326, by rfl⟩ : syracuseStep 86660435 = 129990653) B129990653
theorem B57773623 : Blo 2279435 57773623 := bstep (se 1 (by rfl) ⟨43330217, by rfl⟩ : syracuseStep 57773623 = 86660435) B86660435
theorem B77031497 : Blo 2279435 77031497 := bstep (se 2 (by rfl) ⟨28886811, by rfl⟩ : syracuseStep 77031497 = 57773623) B57773623
theorem B51354331 : Blo 2279435 51354331 := bstep (se 1 (by rfl) ⟨38515748, by rfl⟩ : syracuseStep 51354331 = 77031497) B77031497
theorem B273889765 : Blo 2279435 273889765 := bstep (se 4 (by rfl) ⟨25677165, by rfl⟩ : syracuseStep 273889765 = 51354331) B51354331
theorem B365186353 : Blo 2279435 365186353 := bstep (se 2 (by rfl) ⟨136944882, by rfl⟩ : syracuseStep 365186353 = 273889765) B273889765
theorem B486915137 : Blo 2279435 486915137 := bstep (se 2 (by rfl) ⟨182593176, by rfl⟩ : syracuseStep 486915137 = 365186353) B365186353
theorem B324610091 : Blo 2279435 324610091 := bstep (se 1 (by rfl) ⟨243457568, by rfl⟩ : syracuseStep 324610091 = 486915137) B486915137
theorem B216406727 : Blo 2279435 216406727 := bstep (se 1 (by rfl) ⟨162305045, by rfl⟩ : syracuseStep 216406727 = 324610091) B324610091
theorem B144271151 : Blo 2279435 144271151 := bstep (se 1 (by rfl) ⟨108203363, by rfl⟩ : syracuseStep 144271151 = 216406727) B216406727
theorem B96180767 : Blo 2279435 96180767 := bstep (se 1 (by rfl) ⟨72135575, by rfl⟩ : syracuseStep 96180767 = 144271151) B144271151
theorem B64120511 : Blo 2279435 64120511 := bstep (se 1 (by rfl) ⟨48090383, by rfl⟩ : syracuseStep 64120511 = 96180767) B96180767
theorem B42747007 : Blo 2279435 42747007 := bstep (se 1 (by rfl) ⟨32060255, by rfl⟩ : syracuseStep 42747007 = 64120511) B64120511
theorem B56996009 : Blo 2279435 56996009 := bstep (se 2 (by rfl) ⟨21373503, by rfl⟩ : syracuseStep 56996009 = 42747007) B42747007
theorem B607957429 : Blo 2279435 607957429 := bstep (se 5 (by rfl) ⟨28498004, by rfl⟩ : syracuseStep 607957429 = 56996009) B56996009
theorem B810609905 : Blo 2279435 810609905 := bstep (se 2 (by rfl) ⟨303978714, by rfl⟩ : syracuseStep 810609905 = 607957429) B607957429
theorem B540406603 : Blo 2279435 540406603 := bstep (se 1 (by rfl) ⟨405304952, by rfl⟩ : syracuseStep 540406603 = 810609905) B810609905
theorem B720542137 : Blo 2279435 720542137 := bstep (se 2 (by rfl) ⟨270203301, by rfl⟩ : syracuseStep 720542137 = 540406603) B540406603
theorem B960722849 : Blo 2279435 960722849 := bstep (se 2 (by rfl) ⟨360271068, by rfl⟩ : syracuseStep 960722849 = 720542137) B720542137
theorem B640481899 : Blo 2279435 640481899 := bstep (se 1 (by rfl) ⟨480361424, by rfl⟩ : syracuseStep 640481899 = 960722849) B960722849
theorem B853975865 : Blo 2279435 853975865 := bstep (se 2 (by rfl) ⟨320240949, by rfl⟩ : syracuseStep 853975865 = 640481899) B640481899
theorem B569317243 : Blo 2279435 569317243 := bstep (se 1 (by rfl) ⟨426987932, by rfl⟩ : syracuseStep 569317243 = 853975865) B853975865
theorem B759089657 : Blo 2279435 759089657 := bstep (se 2 (by rfl) ⟨284658621, by rfl⟩ : syracuseStep 759089657 = 569317243) B569317243
theorem B506059771 : Blo 2279435 506059771 := bstep (se 1 (by rfl) ⟨379544828, by rfl⟩ : syracuseStep 506059771 = 759089657) B759089657
theorem B674746361 : Blo 2279435 674746361 := bstep (se 2 (by rfl) ⟨253029885, by rfl⟩ : syracuseStep 674746361 = 506059771) B506059771
theorem B449830907 : Blo 2279435 449830907 := bstep (se 1 (by rfl) ⟨337373180, by rfl⟩ : syracuseStep 449830907 = 674746361) B674746361
theorem B299887271 : Blo 2279435 299887271 := bstep (se 1 (by rfl) ⟨224915453, by rfl⟩ : syracuseStep 299887271 = 449830907) B449830907
theorem B199924847 : Blo 2279435 199924847 := bstep (se 1 (by rfl) ⟨149943635, by rfl⟩ : syracuseStep 199924847 = 299887271) B299887271
theorem B133283231 : Blo 2279435 133283231 := bstep (se 1 (by rfl) ⟨99962423, by rfl⟩ : syracuseStep 133283231 = 199924847) B199924847
theorem B88855487 : Blo 2279435 88855487 := bstep (se 1 (by rfl) ⟨66641615, by rfl⟩ : syracuseStep 88855487 = 133283231) B133283231
theorem B59236991 : Blo 2279435 59236991 := bstep (se 1 (by rfl) ⟨44427743, by rfl⟩ : syracuseStep 59236991 = 88855487) B88855487
theorem B39491327 : Blo 2279435 39491327 := bstep (se 1 (by rfl) ⟨29618495, by rfl⟩ : syracuseStep 39491327 = 59236991) B59236991
theorem B26327551 : Blo 2279435 26327551 := bstep (se 1 (by rfl) ⟨19745663, by rfl⟩ : syracuseStep 26327551 = 39491327) B39491327
theorem B35103401 : Blo 2279435 35103401 := bstep (se 2 (by rfl) ⟨13163775, by rfl⟩ : syracuseStep 35103401 = 26327551) B26327551
theorem B23402267 : Blo 2279435 23402267 := bstep (se 1 (by rfl) ⟨17551700, by rfl⟩ : syracuseStep 23402267 = 35103401) B35103401
theorem B15601511 : Blo 2279435 15601511 := bstep (se 1 (by rfl) ⟨11701133, by rfl⟩ : syracuseStep 15601511 = 23402267) B23402267
theorem B10401007 : Blo 2279435 10401007 := bstep (se 1 (by rfl) ⟨7800755, by rfl⟩ : syracuseStep 10401007 = 15601511) B15601511
theorem B13868009 : Blo 2279435 13868009 := bstep (se 2 (by rfl) ⟨5200503, by rfl⟩ : syracuseStep 13868009 = 10401007) B10401007
theorem B9245339 : Blo 2279435 9245339 := bstep (se 1 (by rfl) ⟨6934004, by rfl⟩ : syracuseStep 9245339 = 13868009) B13868009
theorem B6163559 : Blo 2279435 6163559 := bstep (se 1 (by rfl) ⟨4622669, by rfl⟩ : syracuseStep 6163559 = 9245339) B9245339
theorem B4109039 : Blo 2279435 4109039 := bstep (se 1 (by rfl) ⟨3081779, by rfl⟩ : syracuseStep 4109039 = 6163559) B6163559
theorem B2739359 : Blo 2279435 2739359 := bstep (se 1 (by rfl) ⟨2054519, by rfl⟩ : syracuseStep 2739359 = 4109039) B4109039
theorem B7304957 : Blo 2279435 7304957 := bstep (se 3 (by rfl) ⟨1369679, by rfl⟩ : syracuseStep 7304957 = 2739359) B2739359
theorem B4869971 : Blo 2279435 4869971 := bstep (se 1 (by rfl) ⟨3652478, by rfl⟩ : syracuseStep 4869971 = 7304957) B7304957
theorem B3246647 : Blo 2279435 3246647 := bstep (se 1 (by rfl) ⟨2434985, by rfl⟩ : syracuseStep 3246647 = 4869971) B4869971
theorem B8657725 : Blo 2279435 8657725 := bstep (se 3 (by rfl) ⟨1623323, by rfl⟩ : syracuseStep 8657725 = 3246647) B3246647
theorem B11543633 : Blo 2279435 11543633 := bstep (se 2 (by rfl) ⟨4328862, by rfl⟩ : syracuseStep 11543633 = 8657725) B8657725
theorem B7695755 : Blo 2279435 7695755 := bstep (se 1 (by rfl) ⟨5771816, by rfl⟩ : syracuseStep 7695755 = 11543633) B11543633
theorem B5130503 : Blo 2279435 5130503 := bstep (se 1 (by rfl) ⟨3847877, by rfl⟩ : syracuseStep 5130503 = 7695755) B7695755
theorem B3420335 : Blo 2279435 3420335 := bstep (se 1 (by rfl) ⟨2565251, by rfl⟩ : syracuseStep 3420335 = 5130503) B5130503
theorem B2280223 : Blo 2279435 2280223 := bstep (se 1 (by rfl) ⟨1710167, by rfl⟩ : syracuseStep 2280223 = 3420335) B3420335
theorem B3420341 : Blo 2279435 3420341 := bbase (se 5 (by rfl) ⟨160328, by rfl⟩ : syracuseStep 3420341 = 320657) (by norm_num)
theorem B2280227 : Blo 2279435 2280227 := bstep (se 1 (by rfl) ⟨1710170, by rfl⟩ : syracuseStep 2280227 = 3420341) B3420341
theorem B5771837 : Blo 2279435 5771837 := bbase (se 3 (by rfl) ⟨1082219, by rfl⟩ : syracuseStep 5771837 = 2164439) (by norm_num)
theorem B3847891 : Blo 2279435 3847891 := bstep (se 1 (by rfl) ⟨2885918, by rfl⟩ : syracuseStep 3847891 = 5771837) B5771837
theorem B5130521 : Blo 2279435 5130521 := bstep (se 2 (by rfl) ⟨1923945, by rfl⟩ : syracuseStep 5130521 = 3847891) B3847891
theorem B3420347 : Blo 2279435 3420347 := bstep (se 1 (by rfl) ⟨2565260, by rfl⟩ : syracuseStep 3420347 = 5130521) B5130521
theorem B2280231 : Blo 2279435 2280231 := bstep (se 1 (by rfl) ⟨1710173, by rfl⟩ : syracuseStep 2280231 = 3420347) B3420347
theorem B2565265 : Blo 2279435 2565265 := bbase (se 2 (by rfl) ⟨961974, by rfl⟩ : syracuseStep 2565265 = 1923949) (by norm_num)
theorem B3420353 : Blo 2279435 3420353 := bstep (se 2 (by rfl) ⟨1282632, by rfl⟩ : syracuseStep 3420353 = 2565265) B2565265
theorem B2280235 : Blo 2279435 2280235 := bstep (se 1 (by rfl) ⟨1710176, by rfl⟩ : syracuseStep 2280235 = 3420353) B3420353
theorem B4328893 : Blo 2279435 4328893 := bbase (se 3 (by rfl) ⟨811667, by rfl⟩ : syracuseStep 4328893 = 1623335) (by norm_num)
theorem B5771857 : Blo 2279435 5771857 := bstep (se 2 (by rfl) ⟨2164446, by rfl⟩ : syracuseStep 5771857 = 4328893) B4328893
theorem B7695809 : Blo 2279435 7695809 := bstep (se 2 (by rfl) ⟨2885928, by rfl⟩ : syracuseStep 7695809 = 5771857) B5771857
theorem B5130539 : Blo 2279435 5130539 := bstep (se 1 (by rfl) ⟨3847904, by rfl⟩ : syracuseStep 5130539 = 7695809) B7695809
theorem B3420359 : Blo 2279435 3420359 := bstep (se 1 (by rfl) ⟨2565269, by rfl⟩ : syracuseStep 3420359 = 5130539) B5130539
theorem B2280239 : Blo 2279435 2280239 := bstep (se 1 (by rfl) ⟨1710179, by rfl⟩ : syracuseStep 2280239 = 3420359) B3420359
theorem B3420365 : Blo 2279435 3420365 := bbase (se 3 (by rfl) ⟨641318, by rfl⟩ : syracuseStep 3420365 = 1282637) (by norm_num)
theorem B2280243 : Blo 2279435 2280243 := bstep (se 1 (by rfl) ⟨1710182, by rfl⟩ : syracuseStep 2280243 = 3420365) B3420365
theorem B5130557 : Blo 2279435 5130557 := bbase (se 3 (by rfl) ⟨961979, by rfl⟩ : syracuseStep 5130557 = 1923959) (by norm_num)
theorem B3420371 : Blo 2279435 3420371 := bstep (se 1 (by rfl) ⟨2565278, by rfl⟩ : syracuseStep 3420371 = 5130557) B5130557
theorem B2280247 : Blo 2279435 2280247 := bstep (se 1 (by rfl) ⟨1710185, by rfl⟩ : syracuseStep 2280247 = 3420371) B3420371
theorem B3847925 : Blo 2279435 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B2565283 : Blo 2279435 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B3420377 : Blo 2279435 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B2280251 : Blo 2279435 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B10957589 : Blo 2279435 10957589 := bbase (se 6 (by rfl) ⟨256818, by rfl⟩ : syracuseStep 10957589 = 513637) (by norm_num)
theorem B7305059 : Blo 2279435 7305059 := bstep (se 1 (by rfl) ⟨5478794, by rfl⟩ : syracuseStep 7305059 = 10957589) B10957589
theorem B4870039 : Blo 2279435 4870039 := bstep (se 1 (by rfl) ⟨3652529, by rfl⟩ : syracuseStep 4870039 = 7305059) B7305059
theorem B6493385 : Blo 2279435 6493385 := bstep (se 2 (by rfl) ⟨2435019, by rfl⟩ : syracuseStep 6493385 = 4870039) B4870039
theorem B17315693 : Blo 2279435 17315693 := bstep (se 3 (by rfl) ⟨3246692, by rfl⟩ : syracuseStep 17315693 = 6493385) B6493385
theorem B11543795 : Blo 2279435 11543795 := bstep (se 1 (by rfl) ⟨8657846, by rfl⟩ : syracuseStep 11543795 = 17315693) B17315693
theorem B7695863 : Blo 2279435 7695863 := bstep (se 1 (by rfl) ⟨5771897, by rfl⟩ : syracuseStep 7695863 = 11543795) B11543795
theorem B5130575 : Blo 2279435 5130575 := bstep (se 1 (by rfl) ⟨3847931, by rfl⟩ : syracuseStep 5130575 = 7695863) B7695863
theorem B3420383 : Blo 2279435 3420383 := bstep (se 1 (by rfl) ⟨2565287, by rfl⟩ : syracuseStep 3420383 = 5130575) B5130575
theorem B2280255 : Blo 2279435 2280255 := bstep (se 1 (by rfl) ⟨1710191, by rfl⟩ : syracuseStep 2280255 = 3420383) B3420383
theorem B3420389 : Blo 2279435 3420389 := bbase (se 4 (by rfl) ⟨320661, by rfl⟩ : syracuseStep 3420389 = 641323) (by norm_num)
theorem B2280259 : Blo 2279435 2280259 := bstep (se 1 (by rfl) ⟨1710194, by rfl⟩ : syracuseStep 2280259 = 3420389) B3420389
theorem B23402677 : Blo 2279435 23402677 := bbase (se 5 (by rfl) ⟨1097000, by rfl⟩ : syracuseStep 23402677 = 2194001) (by norm_num)
theorem B31203569 : Blo 2279435 31203569 := bstep (se 2 (by rfl) ⟨11701338, by rfl⟩ : syracuseStep 31203569 = 23402677) B23402677
theorem B20802379 : Blo 2279435 20802379 := bstep (se 1 (by rfl) ⟨15601784, by rfl⟩ : syracuseStep 20802379 = 31203569) B31203569
theorem B27736505 : Blo 2279435 27736505 := bstep (se 2 (by rfl) ⟨10401189, by rfl⟩ : syracuseStep 27736505 = 20802379) B20802379
theorem B18491003 : Blo 2279435 18491003 := bstep (se 1 (by rfl) ⟨13868252, by rfl⟩ : syracuseStep 18491003 = 27736505) B27736505
theorem B12327335 : Blo 2279435 12327335 := bstep (se 1 (by rfl) ⟨9245501, by rfl⟩ : syracuseStep 12327335 = 18491003) B18491003
theorem B8218223 : Blo 2279435 8218223 := bstep (se 1 (by rfl) ⟨6163667, by rfl⟩ : syracuseStep 8218223 = 12327335) B12327335
theorem B5478815 : Blo 2279435 5478815 := bstep (se 1 (by rfl) ⟨4109111, by rfl⟩ : syracuseStep 5478815 = 8218223) B8218223
theorem B3652543 : Blo 2279435 3652543 := bstep (se 1 (by rfl) ⟨2739407, by rfl⟩ : syracuseStep 3652543 = 5478815) B5478815
theorem B4870057 : Blo 2279435 4870057 := bstep (se 2 (by rfl) ⟨1826271, by rfl⟩ : syracuseStep 4870057 = 3652543) B3652543
theorem B6493409 : Blo 2279435 6493409 := bstep (se 2 (by rfl) ⟨2435028, by rfl⟩ : syracuseStep 6493409 = 4870057) B4870057
theorem B4328939 : Blo 2279435 4328939 := bstep (se 1 (by rfl) ⟨3246704, by rfl⟩ : syracuseStep 4328939 = 6493409) B6493409
theorem B2885959 : Blo 2279435 2885959 := bstep (se 1 (by rfl) ⟨2164469, by rfl⟩ : syracuseStep 2885959 = 4328939) B4328939
theorem B3847945 : Blo 2279435 3847945 := bstep (se 2 (by rfl) ⟨1442979, by rfl⟩ : syracuseStep 3847945 = 2885959) B2885959
theorem B5130593 : Blo 2279435 5130593 := bstep (se 2 (by rfl) ⟨1923972, by rfl⟩ : syracuseStep 5130593 = 3847945) B3847945
theorem B3420395 : Blo 2279435 3420395 := bstep (se 1 (by rfl) ⟨2565296, by rfl⟩ : syracuseStep 3420395 = 5130593) B5130593
theorem B2280263 : Blo 2279435 2280263 := bstep (se 1 (by rfl) ⟨1710197, by rfl⟩ : syracuseStep 2280263 = 3420395) B3420395
theorem B2565301 : Blo 2279435 2565301 := bbase (se 5 (by rfl) ⟨120248, by rfl⟩ : syracuseStep 2565301 = 240497) (by norm_num)
theorem B3420401 : Blo 2279435 3420401 := bstep (se 2 (by rfl) ⟨1282650, by rfl⟩ : syracuseStep 3420401 = 2565301) B2565301
theorem B2280267 : Blo 2279435 2280267 := bstep (se 1 (by rfl) ⟨1710200, by rfl⟩ : syracuseStep 2280267 = 3420401) B3420401
theorem B2885969 : Blo 2279435 2885969 := bbase (se 2 (by rfl) ⟨1082238, by rfl⟩ : syracuseStep 2885969 = 2164477) (by norm_num)
theorem B7695917 : Blo 2279435 7695917 := bstep (se 3 (by rfl) ⟨1442984, by rfl⟩ : syracuseStep 7695917 = 2885969) B2885969
theorem B5130611 : Blo 2279435 5130611 := bstep (se 1 (by rfl) ⟨3847958, by rfl⟩ : syracuseStep 5130611 = 7695917) B7695917
theorem B3420407 : Blo 2279435 3420407 := bstep (se 1 (by rfl) ⟨2565305, by rfl⟩ : syracuseStep 3420407 = 5130611) B5130611
theorem B2280271 : Blo 2279435 2280271 := bstep (se 1 (by rfl) ⟨1710203, by rfl⟩ : syracuseStep 2280271 = 3420407) B3420407
theorem B3420413 : Blo 2279435 3420413 := bbase (se 3 (by rfl) ⟨641327, by rfl⟩ : syracuseStep 3420413 = 1282655) (by norm_num)
theorem B2280275 : Blo 2279435 2280275 := bstep (se 1 (by rfl) ⟨1710206, by rfl⟩ : syracuseStep 2280275 = 3420413) B3420413
theorem B5130629 : Blo 2279435 5130629 := bbase (se 4 (by rfl) ⟨480996, by rfl⟩ : syracuseStep 5130629 = 961993) (by norm_num)
theorem B3420419 : Blo 2279435 3420419 := bstep (se 1 (by rfl) ⟨2565314, by rfl⟩ : syracuseStep 3420419 = 5130629) B5130629
theorem B2280279 : Blo 2279435 2280279 := bstep (se 1 (by rfl) ⟨1710209, by rfl⟩ : syracuseStep 2280279 = 3420419) B3420419
theorem B3246733 : Blo 2279435 3246733 := bbase (se 3 (by rfl) ⟨608762, by rfl⟩ : syracuseStep 3246733 = 1217525) (by norm_num)
theorem B4328977 : Blo 2279435 4328977 := bstep (se 2 (by rfl) ⟨1623366, by rfl⟩ : syracuseStep 4328977 = 3246733) B3246733
theorem B5771969 : Blo 2279435 5771969 := bstep (se 2 (by rfl) ⟨2164488, by rfl⟩ : syracuseStep 5771969 = 4328977) B4328977
theorem B3847979 : Blo 2279435 3847979 := bstep (se 1 (by rfl) ⟨2885984, by rfl⟩ : syracuseStep 3847979 = 5771969) B5771969
theorem B2565319 : Blo 2279435 2565319 := bstep (se 1 (by rfl) ⟨1923989, by rfl⟩ : syracuseStep 2565319 = 3847979) B3847979
theorem B3420425 : Blo 2279435 3420425 := bstep (se 2 (by rfl) ⟨1282659, by rfl⟩ : syracuseStep 3420425 = 2565319) B2565319
theorem B2280283 : Blo 2279435 2280283 := bstep (se 1 (by rfl) ⟨1710212, by rfl⟩ : syracuseStep 2280283 = 3420425) B3420425
theorem B11543957 : Blo 2279435 11543957 := bbase (se 6 (by rfl) ⟨270561, by rfl⟩ : syracuseStep 11543957 = 541123) (by norm_num)
theorem B7695971 : Blo 2279435 7695971 := bstep (se 1 (by rfl) ⟨5771978, by rfl⟩ : syracuseStep 7695971 = 11543957) B11543957
theorem B5130647 : Blo 2279435 5130647 := bstep (se 1 (by rfl) ⟨3847985, by rfl⟩ : syracuseStep 5130647 = 7695971) B7695971
theorem B3420431 : Blo 2279435 3420431 := bstep (se 1 (by rfl) ⟨2565323, by rfl⟩ : syracuseStep 3420431 = 5130647) B5130647
theorem B2280287 : Blo 2279435 2280287 := bstep (se 1 (by rfl) ⟨1710215, by rfl⟩ : syracuseStep 2280287 = 3420431) B3420431
theorem B3420437 : Blo 2279435 3420437 := bbase (se 6 (by rfl) ⟨80166, by rfl⟩ : syracuseStep 3420437 = 160333) (by norm_num)
theorem B2280291 : Blo 2279435 2280291 := bstep (se 1 (by rfl) ⟨1710218, by rfl⟩ : syracuseStep 2280291 = 3420437) B3420437
theorem B10957781 : Blo 2279435 10957781 := bbase (se 7 (by rfl) ⟨128411, by rfl⟩ : syracuseStep 10957781 = 256823) (by norm_num)
theorem B29220749 : Blo 2279435 29220749 := bstep (se 3 (by rfl) ⟨5478890, by rfl⟩ : syracuseStep 29220749 = 10957781) B10957781
theorem B19480499 : Blo 2279435 19480499 := bstep (se 1 (by rfl) ⟨14610374, by rfl⟩ : syracuseStep 19480499 = 29220749) B29220749
theorem B12986999 : Blo 2279435 12986999 := bstep (se 1 (by rfl) ⟨9740249, by rfl⟩ : syracuseStep 12986999 = 19480499) B19480499
theorem B8657999 : Blo 2279435 8657999 := bstep (se 1 (by rfl) ⟨6493499, by rfl⟩ : syracuseStep 8657999 = 12986999) B12986999
theorem B5771999 : Blo 2279435 5771999 := bstep (se 1 (by rfl) ⟨4328999, by rfl⟩ : syracuseStep 5771999 = 8657999) B8657999
theorem B3847999 : Blo 2279435 3847999 := bstep (se 1 (by rfl) ⟨2885999, by rfl⟩ : syracuseStep 3847999 = 5771999) B5771999
theorem B5130665 : Blo 2279435 5130665 := bstep (se 2 (by rfl) ⟨1923999, by rfl⟩ : syracuseStep 5130665 = 3847999) B3847999
theorem B3420443 : Blo 2279435 3420443 := bstep (se 1 (by rfl) ⟨2565332, by rfl⟩ : syracuseStep 3420443 = 5130665) B5130665
theorem B2280295 : Blo 2279435 2280295 := bstep (se 1 (by rfl) ⟨1710221, by rfl⟩ : syracuseStep 2280295 = 3420443) B3420443
theorem B2565337 : Blo 2279435 2565337 := bbase (se 2 (by rfl) ⟨962001, by rfl⟩ : syracuseStep 2565337 = 1924003) (by norm_num)
theorem B3420449 : Blo 2279435 3420449 := bstep (se 2 (by rfl) ⟨1282668, by rfl⟩ : syracuseStep 3420449 = 2565337) B2565337
theorem B2280299 : Blo 2279435 2280299 := bstep (se 1 (by rfl) ⟨1710224, by rfl⟩ : syracuseStep 2280299 = 3420449) B3420449
theorem B5343565 : Blo 2279435 5343565 := bbase (se 3 (by rfl) ⟨1001918, by rfl⟩ : syracuseStep 5343565 = 2003837) (by norm_num)
theorem B7124753 : Blo 2279435 7124753 := bstep (se 2 (by rfl) ⟨2671782, by rfl⟩ : syracuseStep 7124753 = 5343565) B5343565
theorem B18999341 : Blo 2279435 18999341 := bstep (se 3 (by rfl) ⟨3562376, by rfl⟩ : syracuseStep 18999341 = 7124753) B7124753
theorem B12666227 : Blo 2279435 12666227 := bstep (se 1 (by rfl) ⟨9499670, by rfl⟩ : syracuseStep 12666227 = 18999341) B18999341
theorem B33776605 : Blo 2279435 33776605 := bstep (se 3 (by rfl) ⟨6333113, by rfl⟩ : syracuseStep 33776605 = 12666227) B12666227
theorem B180141893 : Blo 2279435 180141893 := bstep (se 4 (by rfl) ⟨16888302, by rfl⟩ : syracuseStep 180141893 = 33776605) B33776605
theorem B120094595 : Blo 2279435 120094595 := bstep (se 1 (by rfl) ⟨90070946, by rfl⟩ : syracuseStep 120094595 = 180141893) B180141893
theorem B80063063 : Blo 2279435 80063063 := bstep (se 1 (by rfl) ⟨60047297, by rfl⟩ : syracuseStep 80063063 = 120094595) B120094595
theorem B53375375 : Blo 2279435 53375375 := bstep (se 1 (by rfl) ⟨40031531, by rfl⟩ : syracuseStep 53375375 = 80063063) B80063063
theorem B35583583 : Blo 2279435 35583583 := bstep (se 1 (by rfl) ⟨26687687, by rfl⟩ : syracuseStep 35583583 = 53375375) B53375375
theorem B47444777 : Blo 2279435 47444777 := bstep (se 2 (by rfl) ⟨17791791, by rfl⟩ : syracuseStep 47444777 = 35583583) B35583583
theorem B31629851 : Blo 2279435 31629851 := bstep (se 1 (by rfl) ⟨23722388, by rfl⟩ : syracuseStep 31629851 = 47444777) B47444777
theorem B21086567 : Blo 2279435 21086567 := bstep (se 1 (by rfl) ⟨15814925, by rfl⟩ : syracuseStep 21086567 = 31629851) B31629851
theorem B14057711 : Blo 2279435 14057711 := bstep (se 1 (by rfl) ⟨10543283, by rfl⟩ : syracuseStep 14057711 = 21086567) B21086567
theorem B9371807 : Blo 2279435 9371807 := bstep (se 1 (by rfl) ⟨7028855, by rfl⟩ : syracuseStep 9371807 = 14057711) B14057711
theorem B6247871 : Blo 2279435 6247871 := bstep (se 1 (by rfl) ⟨4685903, by rfl⟩ : syracuseStep 6247871 = 9371807) B9371807
theorem B4165247 : Blo 2279435 4165247 := bstep (se 1 (by rfl) ⟨3123935, by rfl⟩ : syracuseStep 4165247 = 6247871) B6247871
theorem B11107325 : Blo 2279435 11107325 := bstep (se 3 (by rfl) ⟨2082623, by rfl⟩ : syracuseStep 11107325 = 4165247) B4165247
theorem B7404883 : Blo 2279435 7404883 := bstep (se 1 (by rfl) ⟨5553662, by rfl⟩ : syracuseStep 7404883 = 11107325) B11107325
theorem B157970837 : Blo 2279435 157970837 := bstep (se 6 (by rfl) ⟨3702441, by rfl⟩ : syracuseStep 157970837 = 7404883) B7404883
theorem B105313891 : Blo 2279435 105313891 := bstep (se 1 (by rfl) ⟨78985418, by rfl⟩ : syracuseStep 105313891 = 157970837) B157970837
theorem B140418521 : Blo 2279435 140418521 := bstep (se 2 (by rfl) ⟨52656945, by rfl⟩ : syracuseStep 140418521 = 105313891) B105313891
theorem B93612347 : Blo 2279435 93612347 := bstep (se 1 (by rfl) ⟨70209260, by rfl⟩ : syracuseStep 93612347 = 140418521) B140418521
theorem B62408231 : Blo 2279435 62408231 := bstep (se 1 (by rfl) ⟨46806173, by rfl⟩ : syracuseStep 62408231 = 93612347) B93612347
theorem B41605487 : Blo 2279435 41605487 := bstep (se 1 (by rfl) ⟨31204115, by rfl⟩ : syracuseStep 41605487 = 62408231) B62408231
theorem B27736991 : Blo 2279435 27736991 := bstep (se 1 (by rfl) ⟨20802743, by rfl⟩ : syracuseStep 27736991 = 41605487) B41605487
theorem B18491327 : Blo 2279435 18491327 := bstep (se 1 (by rfl) ⟨13868495, by rfl⟩ : syracuseStep 18491327 = 27736991) B27736991
theorem B12327551 : Blo 2279435 12327551 := bstep (se 1 (by rfl) ⟨9245663, by rfl⟩ : syracuseStep 12327551 = 18491327) B18491327
theorem B8218367 : Blo 2279435 8218367 := bstep (se 1 (by rfl) ⟨6163775, by rfl⟩ : syracuseStep 8218367 = 12327551) B12327551
theorem B5478911 : Blo 2279435 5478911 := bstep (se 1 (by rfl) ⟨4109183, by rfl⟩ : syracuseStep 5478911 = 8218367) B8218367
theorem B3652607 : Blo 2279435 3652607 := bstep (se 1 (by rfl) ⟨2739455, by rfl⟩ : syracuseStep 3652607 = 5478911) B5478911
theorem B2435071 : Blo 2279435 2435071 := bstep (se 1 (by rfl) ⟨1826303, by rfl⟩ : syracuseStep 2435071 = 3652607) B3652607
theorem B3246761 : Blo 2279435 3246761 := bstep (se 2 (by rfl) ⟨1217535, by rfl⟩ : syracuseStep 3246761 = 2435071) B2435071
theorem B8658029 : Blo 2279435 8658029 := bstep (se 3 (by rfl) ⟨1623380, by rfl⟩ : syracuseStep 8658029 = 3246761) B3246761
theorem B5772019 : Blo 2279435 5772019 := bstep (se 1 (by rfl) ⟨4329014, by rfl⟩ : syracuseStep 5772019 = 8658029) B8658029
theorem B7696025 : Blo 2279435 7696025 := bstep (se 2 (by rfl) ⟨2886009, by rfl⟩ : syracuseStep 7696025 = 5772019) B5772019
theorem B5130683 : Blo 2279435 5130683 := bstep (se 1 (by rfl) ⟨3848012, by rfl⟩ : syracuseStep 5130683 = 7696025) B7696025
theorem B3420455 : Blo 2279435 3420455 := bstep (se 1 (by rfl) ⟨2565341, by rfl⟩ : syracuseStep 3420455 = 5130683) B5130683
theorem B2280303 : Blo 2279435 2280303 := bstep (se 1 (by rfl) ⟨1710227, by rfl⟩ : syracuseStep 2280303 = 3420455) B3420455
theorem B3420461 : Blo 2279435 3420461 := bbase (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) (by norm_num)
theorem B2280307 : Blo 2279435 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B5130701 : Blo 2279435 5130701 := bbase (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) (by norm_num)
theorem B3420467 : Blo 2279435 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B2280311 : Blo 2279435 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B2886025 : Blo 2279435 2886025 := bbase (se 2 (by rfl) ⟨1082259, by rfl⟩ : syracuseStep 2886025 = 2164519) (by norm_num)
theorem B3848033 : Blo 2279435 3848033 := bstep (se 2 (by rfl) ⟨1443012, by rfl⟩ : syracuseStep 3848033 = 2886025) B2886025
theorem B2565355 : Blo 2279435 2565355 := bstep (se 1 (by rfl) ⟨1924016, by rfl⟩ : syracuseStep 2565355 = 3848033) B3848033
theorem B3420473 : Blo 2279435 3420473 := bstep (se 2 (by rfl) ⟨1282677, by rfl⟩ : syracuseStep 3420473 = 2565355) B2565355
theorem B2280315 : Blo 2279435 2280315 := bstep (se 1 (by rfl) ⟨1710236, by rfl⟩ : syracuseStep 2280315 = 3420473) B3420473
theorem B11701621 : Blo 2279435 11701621 := bbase (se 5 (by rfl) ⟨548513, by rfl⟩ : syracuseStep 11701621 = 1097027) (by norm_num)
theorem B15602161 : Blo 2279435 15602161 := bstep (se 2 (by rfl) ⟨5850810, by rfl⟩ : syracuseStep 15602161 = 11701621) B11701621
theorem B20802881 : Blo 2279435 20802881 := bstep (se 2 (by rfl) ⟨7801080, by rfl⟩ : syracuseStep 20802881 = 15602161) B15602161
theorem B13868587 : Blo 2279435 13868587 := bstep (se 1 (by rfl) ⟨10401440, by rfl⟩ : syracuseStep 13868587 = 20802881) B20802881
theorem B73965797 : Blo 2279435 73965797 := bstep (se 4 (by rfl) ⟨6934293, by rfl⟩ : syracuseStep 73965797 = 13868587) B13868587
theorem B49310531 : Blo 2279435 49310531 := bstep (se 1 (by rfl) ⟨36982898, by rfl⟩ : syracuseStep 49310531 = 73965797) B73965797
theorem B32873687 : Blo 2279435 32873687 := bstep (se 1 (by rfl) ⟨24655265, by rfl⟩ : syracuseStep 32873687 = 49310531) B49310531
theorem B21915791 : Blo 2279435 21915791 := bstep (se 1 (by rfl) ⟨16436843, by rfl⟩ : syracuseStep 21915791 = 32873687) B32873687
theorem B14610527 : Blo 2279435 14610527 := bstep (se 1 (by rfl) ⟨10957895, by rfl⟩ : syracuseStep 14610527 = 21915791) B21915791
theorem B9740351 : Blo 2279435 9740351 := bstep (se 1 (by rfl) ⟨7305263, by rfl⟩ : syracuseStep 9740351 = 14610527) B14610527
theorem B25974269 : Blo 2279435 25974269 := bstep (se 3 (by rfl) ⟨4870175, by rfl⟩ : syracuseStep 25974269 = 9740351) B9740351
theorem B17316179 : Blo 2279435 17316179 := bstep (se 1 (by rfl) ⟨12987134, by rfl⟩ : syracuseStep 17316179 = 25974269) B25974269
theorem B11544119 : Blo 2279435 11544119 := bstep (se 1 (by rfl) ⟨8658089, by rfl⟩ : syracuseStep 11544119 = 17316179) B17316179
theorem B7696079 : Blo 2279435 7696079 := bstep (se 1 (by rfl) ⟨5772059, by rfl⟩ : syracuseStep 7696079 = 11544119) B11544119
theorem B5130719 : Blo 2279435 5130719 := bstep (se 1 (by rfl) ⟨3848039, by rfl⟩ : syracuseStep 5130719 = 7696079) B7696079
theorem B3420479 : Blo 2279435 3420479 := bstep (se 1 (by rfl) ⟨2565359, by rfl⟩ : syracuseStep 3420479 = 5130719) B5130719
theorem B2280319 : Blo 2279435 2280319 := bstep (se 1 (by rfl) ⟨1710239, by rfl⟩ : syracuseStep 2280319 = 3420479) B3420479
theorem B3420485 : Blo 2279435 3420485 := bbase (se 4 (by rfl) ⟨320670, by rfl⟩ : syracuseStep 3420485 = 641341) (by norm_num)
theorem B2280323 : Blo 2279435 2280323 := bstep (se 1 (by rfl) ⟨1710242, by rfl⟩ : syracuseStep 2280323 = 3420485) B3420485
theorem B3848053 : Blo 2279435 3848053 := bbase (se 5 (by rfl) ⟨180377, by rfl⟩ : syracuseStep 3848053 = 360755) (by norm_num)
theorem B5130737 : Blo 2279435 5130737 := bstep (se 2 (by rfl) ⟨1924026, by rfl⟩ : syracuseStep 5130737 = 3848053) B3848053
theorem B3420491 : Blo 2279435 3420491 := bstep (se 1 (by rfl) ⟨2565368, by rfl⟩ : syracuseStep 3420491 = 5130737) B5130737
theorem B2280327 : Blo 2279435 2280327 := bstep (se 1 (by rfl) ⟨1710245, by rfl⟩ : syracuseStep 2280327 = 3420491) B3420491
theorem B2565373 : Blo 2279435 2565373 := bbase (se 3 (by rfl) ⟨481007, by rfl⟩ : syracuseStep 2565373 = 962015) (by norm_num)
theorem B3420497 : Blo 2279435 3420497 := bstep (se 2 (by rfl) ⟨1282686, by rfl⟩ : syracuseStep 3420497 = 2565373) B2565373
theorem B2280331 : Blo 2279435 2280331 := bstep (se 1 (by rfl) ⟨1710248, by rfl⟩ : syracuseStep 2280331 = 3420497) B3420497
theorem B7696133 : Blo 2279435 7696133 := bbase (se 4 (by rfl) ⟨721512, by rfl⟩ : syracuseStep 7696133 = 1443025) (by norm_num)
theorem B5130755 : Blo 2279435 5130755 := bstep (se 1 (by rfl) ⟨3848066, by rfl⟩ : syracuseStep 5130755 = 7696133) B7696133
theorem B3420503 : Blo 2279435 3420503 := bstep (se 1 (by rfl) ⟨2565377, by rfl⟩ : syracuseStep 3420503 = 5130755) B5130755
theorem B2280335 : Blo 2279435 2280335 := bstep (se 1 (by rfl) ⟨1710251, by rfl⟩ : syracuseStep 2280335 = 3420503) B3420503
theorem B3420509 : Blo 2279435 3420509 := bbase (se 3 (by rfl) ⟨641345, by rfl⟩ : syracuseStep 3420509 = 1282691) (by norm_num)
theorem B2280339 : Blo 2279435 2280339 := bstep (se 1 (by rfl) ⟨1710254, by rfl⟩ : syracuseStep 2280339 = 3420509) B3420509
theorem B5130773 : Blo 2279435 5130773 := bbase (se 6 (by rfl) ⟨120252, by rfl⟩ : syracuseStep 5130773 = 240505) (by norm_num)
theorem B3420515 : Blo 2279435 3420515 := bstep (se 1 (by rfl) ⟨2565386, by rfl⟩ : syracuseStep 3420515 = 5130773) B5130773
theorem B2280343 : Blo 2279435 2280343 := bstep (se 1 (by rfl) ⟨1710257, by rfl⟩ : syracuseStep 2280343 = 3420515) B3420515
theorem B8658197 : Blo 2279435 8658197 := bbase (se 6 (by rfl) ⟨202926, by rfl⟩ : syracuseStep 8658197 = 405853) (by norm_num)
theorem B5772131 : Blo 2279435 5772131 := bstep (se 1 (by rfl) ⟨4329098, by rfl⟩ : syracuseStep 5772131 = 8658197) B8658197
theorem B3848087 : Blo 2279435 3848087 := bstep (se 1 (by rfl) ⟨2886065, by rfl⟩ : syracuseStep 3848087 = 5772131) B5772131
theorem B2565391 : Blo 2279435 2565391 := bstep (se 1 (by rfl) ⟨1924043, by rfl⟩ : syracuseStep 2565391 = 3848087) B3848087
theorem B3420521 : Blo 2279435 3420521 := bstep (se 2 (by rfl) ⟨1282695, by rfl⟩ : syracuseStep 3420521 = 2565391) B2565391
theorem B2280347 : Blo 2279435 2280347 := bstep (se 1 (by rfl) ⟨1710260, by rfl⟩ : syracuseStep 2280347 = 3420521) B3420521
theorem B12987317 : Blo 2279435 12987317 := bbase (se 5 (by rfl) ⟨608780, by rfl⟩ : syracuseStep 12987317 = 1217561) (by norm_num)
theorem B8658211 : Blo 2279435 8658211 := bstep (se 1 (by rfl) ⟨6493658, by rfl⟩ : syracuseStep 8658211 = 12987317) B12987317
theorem B11544281 : Blo 2279435 11544281 := bstep (se 2 (by rfl) ⟨4329105, by rfl⟩ : syracuseStep 11544281 = 8658211) B8658211
theorem B7696187 : Blo 2279435 7696187 := bstep (se 1 (by rfl) ⟨5772140, by rfl⟩ : syracuseStep 7696187 = 11544281) B11544281
theorem B5130791 : Blo 2279435 5130791 := bstep (se 1 (by rfl) ⟨3848093, by rfl⟩ : syracuseStep 5130791 = 7696187) B7696187
theorem B3420527 : Blo 2279435 3420527 := bstep (se 1 (by rfl) ⟨2565395, by rfl⟩ : syracuseStep 3420527 = 5130791) B5130791
theorem B2280351 : Blo 2279435 2280351 := bstep (se 1 (by rfl) ⟨1710263, by rfl⟩ : syracuseStep 2280351 = 3420527) B3420527
theorem B3420533 : Blo 2279435 3420533 := bbase (se 5 (by rfl) ⟨160337, by rfl⟩ : syracuseStep 3420533 = 320675) (by norm_num)
theorem B2280355 : Blo 2279435 2280355 := bstep (se 1 (by rfl) ⟨1710266, by rfl⟩ : syracuseStep 2280355 = 3420533) B3420533
theorem B4109285 : Blo 2279435 4109285 := bbase (se 4 (by rfl) ⟨385245, by rfl⟩ : syracuseStep 4109285 = 770491) (by norm_num)
theorem B2739523 : Blo 2279435 2739523 := bstep (se 1 (by rfl) ⟨2054642, by rfl⟩ : syracuseStep 2739523 = 4109285) B4109285
theorem B3652697 : Blo 2279435 3652697 := bstep (se 2 (by rfl) ⟨1369761, by rfl⟩ : syracuseStep 3652697 = 2739523) B2739523
theorem B2435131 : Blo 2279435 2435131 := bstep (se 1 (by rfl) ⟨1826348, by rfl⟩ : syracuseStep 2435131 = 3652697) B3652697
theorem B3246841 : Blo 2279435 3246841 := bstep (se 2 (by rfl) ⟨1217565, by rfl⟩ : syracuseStep 3246841 = 2435131) B2435131
theorem B4329121 : Blo 2279435 4329121 := bstep (se 2 (by rfl) ⟨1623420, by rfl⟩ : syracuseStep 4329121 = 3246841) B3246841
theorem B5772161 : Blo 2279435 5772161 := bstep (se 2 (by rfl) ⟨2164560, by rfl⟩ : syracuseStep 5772161 = 4329121) B4329121
theorem B3848107 : Blo 2279435 3848107 := bstep (se 1 (by rfl) ⟨2886080, by rfl⟩ : syracuseStep 3848107 = 5772161) B5772161
theorem B5130809 : Blo 2279435 5130809 := bstep (se 2 (by rfl) ⟨1924053, by rfl⟩ : syracuseStep 5130809 = 3848107) B3848107
theorem B3420539 : Blo 2279435 3420539 := bstep (se 1 (by rfl) ⟨2565404, by rfl⟩ : syracuseStep 3420539 = 5130809) B5130809
theorem B2280359 : Blo 2279435 2280359 := bstep (se 1 (by rfl) ⟨1710269, by rfl⟩ : syracuseStep 2280359 = 3420539) B3420539
theorem B2565409 : Blo 2279435 2565409 := bbase (se 2 (by rfl) ⟨962028, by rfl⟩ : syracuseStep 2565409 = 1924057) (by norm_num)
theorem B3420545 : Blo 2279435 3420545 := bstep (se 2 (by rfl) ⟨1282704, by rfl⟩ : syracuseStep 3420545 = 2565409) B2565409
theorem B2280363 : Blo 2279435 2280363 := bstep (se 1 (by rfl) ⟨1710272, by rfl⟩ : syracuseStep 2280363 = 3420545) B3420545
theorem B5772181 : Blo 2279435 5772181 := bbase (se 6 (by rfl) ⟨135285, by rfl⟩ : syracuseStep 5772181 = 270571) (by norm_num)
theorem B7696241 : Blo 2279435 7696241 := bstep (se 2 (by rfl) ⟨2886090, by rfl⟩ : syracuseStep 7696241 = 5772181) B5772181
theorem B5130827 : Blo 2279435 5130827 := bstep (se 1 (by rfl) ⟨3848120, by rfl⟩ : syracuseStep 5130827 = 7696241) B7696241
theorem B3420551 : Blo 2279435 3420551 := bstep (se 1 (by rfl) ⟨2565413, by rfl⟩ : syracuseStep 3420551 = 5130827) B5130827
theorem B2280367 : Blo 2279435 2280367 := bstep (se 1 (by rfl) ⟨1710275, by rfl⟩ : syracuseStep 2280367 = 3420551) B3420551
theorem B3420557 : Blo 2279435 3420557 := bbase (se 3 (by rfl) ⟨641354, by rfl⟩ : syracuseStep 3420557 = 1282709) (by norm_num)
theorem B2280371 : Blo 2279435 2280371 := bstep (se 1 (by rfl) ⟨1710278, by rfl⟩ : syracuseStep 2280371 = 3420557) B3420557
theorem B5130845 : Blo 2279435 5130845 := bbase (se 3 (by rfl) ⟨962033, by rfl⟩ : syracuseStep 5130845 = 1924067) (by norm_num)
theorem B3420563 : Blo 2279435 3420563 := bstep (se 1 (by rfl) ⟨2565422, by rfl⟩ : syracuseStep 3420563 = 5130845) B5130845
theorem B2280375 : Blo 2279435 2280375 := bstep (se 1 (by rfl) ⟨1710281, by rfl⟩ : syracuseStep 2280375 = 3420563) B3420563
theorem B3848141 : Blo 2279435 3848141 := bbase (se 3 (by rfl) ⟨721526, by rfl⟩ : syracuseStep 3848141 = 1443053) (by norm_num)
theorem B2565427 : Blo 2279435 2565427 := bstep (se 1 (by rfl) ⟨1924070, by rfl⟩ : syracuseStep 2565427 = 3848141) B3848141
theorem B3420569 : Blo 2279435 3420569 := bstep (se 2 (by rfl) ⟨1282713, by rfl⟩ : syracuseStep 3420569 = 2565427) B2565427
theorem B2280379 : Blo 2279435 2280379 := bstep (se 1 (by rfl) ⟨1710284, by rfl⟩ : syracuseStep 2280379 = 3420569) B3420569
theorem B10401733 : Blo 2279435 10401733 := bbase (se 4 (by rfl) ⟨975162, by rfl⟩ : syracuseStep 10401733 = 1950325) (by norm_num)
theorem B13868977 : Blo 2279435 13868977 := bstep (se 2 (by rfl) ⟨5200866, by rfl⟩ : syracuseStep 13868977 = 10401733) B10401733
theorem B18491969 : Blo 2279435 18491969 := bstep (se 2 (by rfl) ⟨6934488, by rfl⟩ : syracuseStep 18491969 = 13868977) B13868977
theorem B12327979 : Blo 2279435 12327979 := bstep (se 1 (by rfl) ⟨9245984, by rfl⟩ : syracuseStep 12327979 = 18491969) B18491969
theorem B16437305 : Blo 2279435 16437305 := bstep (se 2 (by rfl) ⟨6163989, by rfl⟩ : syracuseStep 16437305 = 12327979) B12327979
theorem B10958203 : Blo 2279435 10958203 := bstep (se 1 (by rfl) ⟨8218652, by rfl⟩ : syracuseStep 10958203 = 16437305) B16437305
theorem B14610937 : Blo 2279435 14610937 := bstep (se 2 (by rfl) ⟨5479101, by rfl⟩ : syracuseStep 14610937 = 10958203) B10958203
theorem B19481249 : Blo 2279435 19481249 := bstep (se 2 (by rfl) ⟨7305468, by rfl⟩ : syracuseStep 19481249 = 14610937) B14610937
theorem B12987499 : Blo 2279435 12987499 := bstep (se 1 (by rfl) ⟨9740624, by rfl⟩ : syracuseStep 12987499 = 19481249) B19481249
theorem B17316665 : Blo 2279435 17316665 := bstep (se 2 (by rfl) ⟨6493749, by rfl⟩ : syracuseStep 17316665 = 12987499) B12987499
theorem B11544443 : Blo 2279435 11544443 := bstep (se 1 (by rfl) ⟨8658332, by rfl⟩ : syracuseStep 11544443 = 17316665) B17316665
theorem B7696295 : Blo 2279435 7696295 := bstep (se 1 (by rfl) ⟨5772221, by rfl⟩ : syracuseStep 7696295 = 11544443) B11544443
theorem B5130863 : Blo 2279435 5130863 := bstep (se 1 (by rfl) ⟨3848147, by rfl⟩ : syracuseStep 5130863 = 7696295) B7696295
theorem B3420575 : Blo 2279435 3420575 := bstep (se 1 (by rfl) ⟨2565431, by rfl⟩ : syracuseStep 3420575 = 5130863) B5130863
theorem B2280383 : Blo 2279435 2280383 := bstep (se 1 (by rfl) ⟨1710287, by rfl⟩ : syracuseStep 2280383 = 3420575) B3420575
theorem B3420581 : Blo 2279435 3420581 := bbase (se 4 (by rfl) ⟨320679, by rfl⟩ : syracuseStep 3420581 = 641359) (by norm_num)
theorem B2280387 : Blo 2279435 2280387 := bstep (se 1 (by rfl) ⟨1710290, by rfl⟩ : syracuseStep 2280387 = 3420581) B3420581
theorem B2886121 : Blo 2279435 2886121 := bbase (se 2 (by rfl) ⟨1082295, by rfl⟩ : syracuseStep 2886121 = 2164591) (by norm_num)
theorem B3848161 : Blo 2279435 3848161 := bstep (se 2 (by rfl) ⟨1443060, by rfl⟩ : syracuseStep 3848161 = 2886121) B2886121
theorem B5130881 : Blo 2279435 5130881 := bstep (se 2 (by rfl) ⟨1924080, by rfl⟩ : syracuseStep 5130881 = 3848161) B3848161
theorem B3420587 : Blo 2279435 3420587 := bstep (se 1 (by rfl) ⟨2565440, by rfl⟩ : syracuseStep 3420587 = 5130881) B5130881
theorem B2280391 : Blo 2279435 2280391 := bstep (se 1 (by rfl) ⟨1710293, by rfl⟩ : syracuseStep 2280391 = 3420587) B3420587
theorem B2565445 : Blo 2279435 2565445 := bbase (se 4 (by rfl) ⟨240510, by rfl⟩ : syracuseStep 2565445 = 481021) (by norm_num)
theorem B3420593 : Blo 2279435 3420593 := bstep (se 2 (by rfl) ⟨1282722, by rfl⟩ : syracuseStep 3420593 = 2565445) B2565445
theorem B2280395 : Blo 2279435 2280395 := bstep (se 1 (by rfl) ⟨1710296, by rfl⟩ : syracuseStep 2280395 = 3420593) B3420593
theorem B4329197 : Blo 2279435 4329197 := bbase (se 3 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 4329197 = 1623449) (by norm_num)
theorem B2886131 : Blo 2279435 2886131 := bstep (se 1 (by rfl) ⟨2164598, by rfl⟩ : syracuseStep 2886131 = 4329197) B4329197
theorem B7696349 : Blo 2279435 7696349 := bstep (se 3 (by rfl) ⟨1443065, by rfl⟩ : syracuseStep 7696349 = 2886131) B2886131
theorem B5130899 : Blo 2279435 5130899 := bstep (se 1 (by rfl) ⟨3848174, by rfl⟩ : syracuseStep 5130899 = 7696349) B7696349
theorem B3420599 : Blo 2279435 3420599 := bstep (se 1 (by rfl) ⟨2565449, by rfl⟩ : syracuseStep 3420599 = 5130899) B5130899
theorem B2280399 : Blo 2279435 2280399 := bstep (se 1 (by rfl) ⟨1710299, by rfl⟩ : syracuseStep 2280399 = 3420599) B3420599
theorem B3420605 : Blo 2279435 3420605 := bbase (se 3 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 3420605 = 1282727) (by norm_num)
theorem B2280403 : Blo 2279435 2280403 := bstep (se 1 (by rfl) ⟨1710302, by rfl⟩ : syracuseStep 2280403 = 3420605) B3420605
theorem B5130917 : Blo 2279435 5130917 := bbase (se 4 (by rfl) ⟨481023, by rfl⟩ : syracuseStep 5130917 = 962047) (by norm_num)
theorem B3420611 : Blo 2279435 3420611 := bstep (se 1 (by rfl) ⟨2565458, by rfl⟩ : syracuseStep 3420611 = 5130917) B5130917
theorem B2280407 : Blo 2279435 2280407 := bstep (se 1 (by rfl) ⟨1710305, by rfl⟩ : syracuseStep 2280407 = 3420611) B3420611
theorem B5772293 : Blo 2279435 5772293 := bbase (se 4 (by rfl) ⟨541152, by rfl⟩ : syracuseStep 5772293 = 1082305) (by norm_num)
theorem B3848195 : Blo 2279435 3848195 := bstep (se 1 (by rfl) ⟨2886146, by rfl⟩ : syracuseStep 3848195 = 5772293) B5772293
theorem B2565463 : Blo 2279435 2565463 := bstep (se 1 (by rfl) ⟨1924097, by rfl⟩ : syracuseStep 2565463 = 3848195) B3848195
theorem B3420617 : Blo 2279435 3420617 := bstep (se 2 (by rfl) ⟨1282731, by rfl⟩ : syracuseStep 3420617 = 2565463) B2565463
theorem B2280411 : Blo 2279435 2280411 := bstep (se 1 (by rfl) ⟨1710308, by rfl⟩ : syracuseStep 2280411 = 3420617) B3420617
theorem B4870381 : Blo 2279435 4870381 := bbase (se 3 (by rfl) ⟨913196, by rfl⟩ : syracuseStep 4870381 = 1826393) (by norm_num)
theorem B6493841 : Blo 2279435 6493841 := bstep (se 2 (by rfl) ⟨2435190, by rfl⟩ : syracuseStep 6493841 = 4870381) B4870381
theorem B4329227 : Blo 2279435 4329227 := bstep (se 1 (by rfl) ⟨3246920, by rfl⟩ : syracuseStep 4329227 = 6493841) B6493841
theorem B11544605 : Blo 2279435 11544605 := bstep (se 3 (by rfl) ⟨2164613, by rfl⟩ : syracuseStep 11544605 = 4329227) B4329227
theorem B7696403 : Blo 2279435 7696403 := bstep (se 1 (by rfl) ⟨5772302, by rfl⟩ : syracuseStep 7696403 = 11544605) B11544605
theorem B5130935 : Blo 2279435 5130935 := bstep (se 1 (by rfl) ⟨3848201, by rfl⟩ : syracuseStep 5130935 = 7696403) B7696403
theorem B3420623 : Blo 2279435 3420623 := bstep (se 1 (by rfl) ⟨2565467, by rfl⟩ : syracuseStep 3420623 = 5130935) B5130935
theorem B2280415 : Blo 2279435 2280415 := bstep (se 1 (by rfl) ⟨1710311, by rfl⟩ : syracuseStep 2280415 = 3420623) B3420623
theorem B3420629 : Blo 2279435 3420629 := bbase (se 7 (by rfl) ⟨40085, by rfl⟩ : syracuseStep 3420629 = 80171) (by norm_num)
theorem B2280419 : Blo 2279435 2280419 := bstep (se 1 (by rfl) ⟨1710314, by rfl⟩ : syracuseStep 2280419 = 3420629) B3420629
theorem B8658485 : Blo 2279435 8658485 := bbase (se 5 (by rfl) ⟨405866, by rfl⟩ : syracuseStep 8658485 = 811733) (by norm_num)
theorem B5772323 : Blo 2279435 5772323 := bstep (se 1 (by rfl) ⟨4329242, by rfl⟩ : syracuseStep 5772323 = 8658485) B8658485
theorem B3848215 : Blo 2279435 3848215 := bstep (se 1 (by rfl) ⟨2886161, by rfl⟩ : syracuseStep 3848215 = 5772323) B5772323
theorem B5130953 : Blo 2279435 5130953 := bstep (se 2 (by rfl) ⟨1924107, by rfl⟩ : syracuseStep 5130953 = 3848215) B3848215
theorem B3420635 : Blo 2279435 3420635 := bstep (se 1 (by rfl) ⟨2565476, by rfl⟩ : syracuseStep 3420635 = 5130953) B5130953
theorem B2280423 : Blo 2279435 2280423 := bstep (se 1 (by rfl) ⟨1710317, by rfl⟩ : syracuseStep 2280423 = 3420635) B3420635
theorem B2565481 : Blo 2279435 2565481 := bbase (se 2 (by rfl) ⟨962055, by rfl⟩ : syracuseStep 2565481 = 1924111) (by norm_num)
theorem B3420641 : Blo 2279435 3420641 := bstep (se 2 (by rfl) ⟨1282740, by rfl⟩ : syracuseStep 3420641 = 2565481) B2565481
theorem B2280427 : Blo 2279435 2280427 := bstep (se 1 (by rfl) ⟨1710320, by rfl⟩ : syracuseStep 2280427 = 3420641) B3420641
theorem B16437653 : Blo 2279435 16437653 := bbase (se 6 (by rfl) ⟨385257, by rfl⟩ : syracuseStep 16437653 = 770515) (by norm_num)
theorem B10958435 : Blo 2279435 10958435 := bstep (se 1 (by rfl) ⟨8218826, by rfl⟩ : syracuseStep 10958435 = 16437653) B16437653
theorem B7305623 : Blo 2279435 7305623 := bstep (se 1 (by rfl) ⟨5479217, by rfl⟩ : syracuseStep 7305623 = 10958435) B10958435
theorem B4870415 : Blo 2279435 4870415 := bstep (se 1 (by rfl) ⟨3652811, by rfl⟩ : syracuseStep 4870415 = 7305623) B7305623
theorem B12987773 : Blo 2279435 12987773 := bstep (se 3 (by rfl) ⟨2435207, by rfl⟩ : syracuseStep 12987773 = 4870415) B4870415
theorem B8658515 : Blo 2279435 8658515 := bstep (se 1 (by rfl) ⟨6493886, by rfl⟩ : syracuseStep 8658515 = 12987773) B12987773
theorem B5772343 : Blo 2279435 5772343 := bstep (se 1 (by rfl) ⟨4329257, by rfl⟩ : syracuseStep 5772343 = 8658515) B8658515
theorem B7696457 : Blo 2279435 7696457 := bstep (se 2 (by rfl) ⟨2886171, by rfl⟩ : syracuseStep 7696457 = 5772343) B5772343
theorem B5130971 : Blo 2279435 5130971 := bstep (se 1 (by rfl) ⟨3848228, by rfl⟩ : syracuseStep 5130971 = 7696457) B7696457
theorem B3420647 : Blo 2279435 3420647 := bstep (se 1 (by rfl) ⟨2565485, by rfl⟩ : syracuseStep 3420647 = 5130971) B5130971
theorem B2280431 : Blo 2279435 2280431 := bstep (se 1 (by rfl) ⟨1710323, by rfl⟩ : syracuseStep 2280431 = 3420647) B3420647
theorem B3420653 : Blo 2279435 3420653 := bbase (se 3 (by rfl) ⟨641372, by rfl⟩ : syracuseStep 3420653 = 1282745) (by norm_num)
theorem B2280435 : Blo 2279435 2280435 := bstep (se 1 (by rfl) ⟨1710326, by rfl⟩ : syracuseStep 2280435 = 3420653) B3420653
theorem B5130989 : Blo 2279435 5130989 := bbase (se 3 (by rfl) ⟨962060, by rfl⟩ : syracuseStep 5130989 = 1924121) (by norm_num)
theorem B3420659 : Blo 2279435 3420659 := bstep (se 1 (by rfl) ⟨2565494, by rfl⟩ : syracuseStep 3420659 = 5130989) B5130989
theorem B2280439 : Blo 2279435 2280439 := bstep (se 1 (by rfl) ⟨1710329, by rfl⟩ : syracuseStep 2280439 = 3420659) B3420659
theorem B2435221 : Blo 2279435 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B3246961 : Blo 2279435 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B4329281 : Blo 2279435 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B2886187 : Blo 2279435 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B3848249 : Blo 2279435 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B2565499 : Blo 2279435 2565499 := bstep (se 1 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 2565499 = 3848249) B3848249
theorem B3420665 : Blo 2279435 3420665 := bstep (se 2 (by rfl) ⟨1282749, by rfl⟩ : syracuseStep 3420665 = 2565499) B2565499
theorem B2280443 : Blo 2279435 2280443 := bstep (se 1 (by rfl) ⟨1710332, by rfl⟩ : syracuseStep 2280443 = 3420665) B3420665
theorem B2311561 : Blo 2279435 2311561 := bbase (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) (by norm_num)
theorem B3082081 : Blo 2279435 3082081 := bstep (se 2 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 3082081 = 2311561) B2311561
theorem B65751061 : Blo 2279435 65751061 := bstep (se 6 (by rfl) ⟨1541040, by rfl⟩ : syracuseStep 65751061 = 3082081) B3082081
theorem B87668081 : Blo 2279435 87668081 := bstep (se 2 (by rfl) ⟨32875530, by rfl⟩ : syracuseStep 87668081 = 65751061) B65751061
theorem B58445387 : Blo 2279435 58445387 := bstep (se 1 (by rfl) ⟨43834040, by rfl⟩ : syracuseStep 58445387 = 87668081) B87668081
theorem B38963591 : Blo 2279435 38963591 := bstep (se 1 (by rfl) ⟨29222693, by rfl⟩ : syracuseStep 38963591 = 58445387) B58445387
theorem B25975727 : Blo 2279435 25975727 := bstep (se 1 (by rfl) ⟨19481795, by rfl⟩ : syracuseStep 25975727 = 38963591) B38963591
theorem B17317151 : Blo 2279435 17317151 := bstep (se 1 (by rfl) ⟨12987863, by rfl⟩ : syracuseStep 17317151 = 25975727) B25975727
theorem B11544767 : Blo 2279435 11544767 := bstep (se 1 (by rfl) ⟨8658575, by rfl⟩ : syracuseStep 11544767 = 17317151) B17317151
theorem B7696511 : Blo 2279435 7696511 := bstep (se 1 (by rfl) ⟨5772383, by rfl⟩ : syracuseStep 7696511 = 11544767) B11544767
theorem B5131007 : Blo 2279435 5131007 := bstep (se 1 (by rfl) ⟨3848255, by rfl⟩ : syracuseStep 5131007 = 7696511) B7696511
theorem B3420671 : Blo 2279435 3420671 := bstep (se 1 (by rfl) ⟨2565503, by rfl⟩ : syracuseStep 3420671 = 5131007) B5131007
theorem B2280447 : Blo 2279435 2280447 := bstep (se 1 (by rfl) ⟨1710335, by rfl⟩ : syracuseStep 2280447 = 3420671) B3420671
theorem B3420677 : Blo 2279435 3420677 := bbase (se 4 (by rfl) ⟨320688, by rfl⟩ : syracuseStep 3420677 = 641377) (by norm_num)
theorem B2280451 : Blo 2279435 2280451 := bstep (se 1 (by rfl) ⟨1710338, by rfl⟩ : syracuseStep 2280451 = 3420677) B3420677
theorem B3848269 : Blo 2279435 3848269 := bbase (se 3 (by rfl) ⟨721550, by rfl⟩ : syracuseStep 3848269 = 1443101) (by norm_num)
theorem B5131025 : Blo 2279435 5131025 := bstep (se 2 (by rfl) ⟨1924134, by rfl⟩ : syracuseStep 5131025 = 3848269) B3848269
theorem B3420683 : Blo 2279435 3420683 := bstep (se 1 (by rfl) ⟨2565512, by rfl⟩ : syracuseStep 3420683 = 5131025) B5131025
theorem B2280455 : Blo 2279435 2280455 := bstep (se 1 (by rfl) ⟨1710341, by rfl⟩ : syracuseStep 2280455 = 3420683) B3420683
theorem B2565517 : Blo 2279435 2565517 := bbase (se 3 (by rfl) ⟨481034, by rfl⟩ : syracuseStep 2565517 = 962069) (by norm_num)
theorem B3420689 : Blo 2279435 3420689 := bstep (se 2 (by rfl) ⟨1282758, by rfl⟩ : syracuseStep 3420689 = 2565517) B2565517
theorem B2280459 : Blo 2279435 2280459 := bstep (se 1 (by rfl) ⟨1710344, by rfl⟩ : syracuseStep 2280459 = 3420689) B3420689
theorem B7696565 : Blo 2279435 7696565 := bbase (se 5 (by rfl) ⟨360776, by rfl⟩ : syracuseStep 7696565 = 721553) (by norm_num)
theorem B5131043 : Blo 2279435 5131043 := bstep (se 1 (by rfl) ⟨3848282, by rfl⟩ : syracuseStep 5131043 = 7696565) B7696565
theorem B3420695 : Blo 2279435 3420695 := bstep (se 1 (by rfl) ⟨2565521, by rfl⟩ : syracuseStep 3420695 = 5131043) B5131043
theorem B2280463 : Blo 2279435 2280463 := bstep (se 1 (by rfl) ⟨1710347, by rfl⟩ : syracuseStep 2280463 = 3420695) B3420695
theorem B3420701 : Blo 2279435 3420701 := bbase (se 3 (by rfl) ⟨641381, by rfl⟩ : syracuseStep 3420701 = 1282763) (by norm_num)
theorem B2280467 : Blo 2279435 2280467 := bstep (se 1 (by rfl) ⟨1710350, by rfl⟩ : syracuseStep 2280467 = 3420701) B3420701
theorem B5131061 : Blo 2279435 5131061 := bbase (se 5 (by rfl) ⟨240518, by rfl⟩ : syracuseStep 5131061 = 481037) (by norm_num)
theorem B3420707 : Blo 2279435 3420707 := bstep (se 1 (by rfl) ⟨2565530, by rfl⟩ : syracuseStep 3420707 = 5131061) B5131061
theorem B2280471 : Blo 2279435 2280471 := bstep (se 1 (by rfl) ⟨1710353, by rfl⟩ : syracuseStep 2280471 = 3420707) B3420707
theorem B20804309 : Blo 2279435 20804309 := bbase (se 7 (by rfl) ⟨243800, by rfl⟩ : syracuseStep 20804309 = 487601) (by norm_num)
theorem B13869539 : Blo 2279435 13869539 := bstep (se 1 (by rfl) ⟨10402154, by rfl⟩ : syracuseStep 13869539 = 20804309) B20804309
theorem B9246359 : Blo 2279435 9246359 := bstep (se 1 (by rfl) ⟨6934769, by rfl⟩ : syracuseStep 9246359 = 13869539) B13869539
theorem B24656957 : Blo 2279435 24656957 := bstep (se 3 (by rfl) ⟨4623179, by rfl⟩ : syracuseStep 24656957 = 9246359) B9246359
theorem B16437971 : Blo 2279435 16437971 := bstep (se 1 (by rfl) ⟨12328478, by rfl⟩ : syracuseStep 16437971 = 24656957) B24656957
theorem B10958647 : Blo 2279435 10958647 := bstep (se 1 (by rfl) ⟨8218985, by rfl⟩ : syracuseStep 10958647 = 16437971) B16437971
theorem B14611529 : Blo 2279435 14611529 := bstep (se 2 (by rfl) ⟨5479323, by rfl⟩ : syracuseStep 14611529 = 10958647) B10958647
theorem B9741019 : Blo 2279435 9741019 := bstep (se 1 (by rfl) ⟨7305764, by rfl⟩ : syracuseStep 9741019 = 14611529) B14611529
theorem B12988025 : Blo 2279435 12988025 := bstep (se 2 (by rfl) ⟨4870509, by rfl⟩ : syracuseStep 12988025 = 9741019) B9741019
theorem B8658683 : Blo 2279435 8658683 := bstep (se 1 (by rfl) ⟨6494012, by rfl⟩ : syracuseStep 8658683 = 12988025) B12988025
theorem B5772455 : Blo 2279435 5772455 := bstep (se 1 (by rfl) ⟨4329341, by rfl⟩ : syracuseStep 5772455 = 8658683) B8658683
theorem B3848303 : Blo 2279435 3848303 := bstep (se 1 (by rfl) ⟨2886227, by rfl⟩ : syracuseStep 3848303 = 5772455) B5772455
theorem B2565535 : Blo 2279435 2565535 := bstep (se 1 (by rfl) ⟨1924151, by rfl⟩ : syracuseStep 2565535 = 3848303) B3848303
theorem B3420713 : Blo 2279435 3420713 := bstep (se 2 (by rfl) ⟨1282767, by rfl⟩ : syracuseStep 3420713 = 2565535) B2565535
theorem B2280475 : Blo 2279435 2280475 := bstep (se 1 (by rfl) ⟨1710356, by rfl⟩ : syracuseStep 2280475 = 3420713) B3420713
theorem B2468485 : Blo 2279435 2468485 := bbase (se 4 (by rfl) ⟨231420, by rfl⟩ : syracuseStep 2468485 = 462841) (by norm_num)
theorem B13165253 : Blo 2279435 13165253 := bstep (se 4 (by rfl) ⟨1234242, by rfl⟩ : syracuseStep 13165253 = 2468485) B2468485
theorem B8776835 : Blo 2279435 8776835 := bstep (se 1 (by rfl) ⟨6582626, by rfl⟩ : syracuseStep 8776835 = 13165253) B13165253
theorem B5851223 : Blo 2279435 5851223 := bstep (se 1 (by rfl) ⟨4388417, by rfl⟩ : syracuseStep 5851223 = 8776835) B8776835
theorem B3900815 : Blo 2279435 3900815 := bstep (se 1 (by rfl) ⟨2925611, by rfl⟩ : syracuseStep 3900815 = 5851223) B5851223
theorem B2600543 : Blo 2279435 2600543 := bstep (se 1 (by rfl) ⟨1950407, by rfl⟩ : syracuseStep 2600543 = 3900815) B3900815
theorem B6934781 : Blo 2279435 6934781 := bstep (se 3 (by rfl) ⟨1300271, by rfl⟩ : syracuseStep 6934781 = 2600543) B2600543
theorem B18492749 : Blo 2279435 18492749 := bstep (se 3 (by rfl) ⟨3467390, by rfl⟩ : syracuseStep 18492749 = 6934781) B6934781
theorem B12328499 : Blo 2279435 12328499 := bstep (se 1 (by rfl) ⟨9246374, by rfl⟩ : syracuseStep 12328499 = 18492749) B18492749
theorem B8218999 : Blo 2279435 8218999 := bstep (se 1 (by rfl) ⟨6164249, by rfl⟩ : syracuseStep 8218999 = 12328499) B12328499
theorem B10958665 : Blo 2279435 10958665 := bstep (se 2 (by rfl) ⟨4109499, by rfl⟩ : syracuseStep 10958665 = 8218999) B8218999
theorem B14611553 : Blo 2279435 14611553 := bstep (se 2 (by rfl) ⟨5479332, by rfl⟩ : syracuseStep 14611553 = 10958665) B10958665
theorem B9741035 : Blo 2279435 9741035 := bstep (se 1 (by rfl) ⟨7305776, by rfl⟩ : syracuseStep 9741035 = 14611553) B14611553
theorem B6494023 : Blo 2279435 6494023 := bstep (se 1 (by rfl) ⟨4870517, by rfl⟩ : syracuseStep 6494023 = 9741035) B9741035
theorem B8658697 : Blo 2279435 8658697 := bstep (se 2 (by rfl) ⟨3247011, by rfl⟩ : syracuseStep 8658697 = 6494023) B6494023
theorem B11544929 : Blo 2279435 11544929 := bstep (se 2 (by rfl) ⟨4329348, by rfl⟩ : syracuseStep 11544929 = 8658697) B8658697
theorem B7696619 : Blo 2279435 7696619 := bstep (se 1 (by rfl) ⟨5772464, by rfl⟩ : syracuseStep 7696619 = 11544929) B11544929
theorem B5131079 : Blo 2279435 5131079 := bstep (se 1 (by rfl) ⟨3848309, by rfl⟩ : syracuseStep 5131079 = 7696619) B7696619
theorem B3420719 : Blo 2279435 3420719 := bstep (se 1 (by rfl) ⟨2565539, by rfl⟩ : syracuseStep 3420719 = 5131079) B5131079
theorem B2280479 : Blo 2279435 2280479 := bstep (se 1 (by rfl) ⟨1710359, by rfl⟩ : syracuseStep 2280479 = 3420719) B3420719
theorem B3420725 : Blo 2279435 3420725 := bbase (se 5 (by rfl) ⟨160346, by rfl⟩ : syracuseStep 3420725 = 320693) (by norm_num)
theorem B2280483 : Blo 2279435 2280483 := bstep (se 1 (by rfl) ⟨1710362, by rfl⟩ : syracuseStep 2280483 = 3420725) B3420725
theorem B5772485 : Blo 2279435 5772485 := bbase (se 4 (by rfl) ⟨541170, by rfl⟩ : syracuseStep 5772485 = 1082341) (by norm_num)
theorem B3848323 : Blo 2279435 3848323 := bstep (se 1 (by rfl) ⟨2886242, by rfl⟩ : syracuseStep 3848323 = 5772485) B5772485
theorem B5131097 : Blo 2279435 5131097 := bstep (se 2 (by rfl) ⟨1924161, by rfl⟩ : syracuseStep 5131097 = 3848323) B3848323
theorem B3420731 : Blo 2279435 3420731 := bstep (se 1 (by rfl) ⟨2565548, by rfl⟩ : syracuseStep 3420731 = 5131097) B5131097
theorem B2280487 : Blo 2279435 2280487 := bstep (se 1 (by rfl) ⟨1710365, by rfl⟩ : syracuseStep 2280487 = 3420731) B3420731
theorem B2565553 : Blo 2279435 2565553 := bbase (se 2 (by rfl) ⟨962082, by rfl⟩ : syracuseStep 2565553 = 1924165) (by norm_num)
theorem B3420737 : Blo 2279435 3420737 := bstep (se 2 (by rfl) ⟨1282776, by rfl⟩ : syracuseStep 3420737 = 2565553) B2565553
theorem B2280491 : Blo 2279435 2280491 := bstep (se 1 (by rfl) ⟨1710368, by rfl⟩ : syracuseStep 2280491 = 3420737) B3420737
theorem B6494069 : Blo 2279435 6494069 := bbase (se 5 (by rfl) ⟨304409, by rfl⟩ : syracuseStep 6494069 = 608819) (by norm_num)
theorem B4329379 : Blo 2279435 4329379 := bstep (se 1 (by rfl) ⟨3247034, by rfl⟩ : syracuseStep 4329379 = 6494069) B6494069
theorem B5772505 : Blo 2279435 5772505 := bstep (se 2 (by rfl) ⟨2164689, by rfl⟩ : syracuseStep 5772505 = 4329379) B4329379
theorem B7696673 : Blo 2279435 7696673 := bstep (se 2 (by rfl) ⟨2886252, by rfl⟩ : syracuseStep 7696673 = 5772505) B5772505
theorem B5131115 : Blo 2279435 5131115 := bstep (se 1 (by rfl) ⟨3848336, by rfl⟩ : syracuseStep 5131115 = 7696673) B7696673
theorem B3420743 : Blo 2279435 3420743 := bstep (se 1 (by rfl) ⟨2565557, by rfl⟩ : syracuseStep 3420743 = 5131115) B5131115
theorem B2280495 : Blo 2279435 2280495 := bstep (se 1 (by rfl) ⟨1710371, by rfl⟩ : syracuseStep 2280495 = 3420743) B3420743
theorem B3420749 : Blo 2279435 3420749 := bbase (se 3 (by rfl) ⟨641390, by rfl⟩ : syracuseStep 3420749 = 1282781) (by norm_num)
theorem B2280499 : Blo 2279435 2280499 := bstep (se 1 (by rfl) ⟨1710374, by rfl⟩ : syracuseStep 2280499 = 3420749) B3420749
theorem B5131133 : Blo 2279435 5131133 := bbase (se 3 (by rfl) ⟨962087, by rfl⟩ : syracuseStep 5131133 = 1924175) (by norm_num)
theorem B3420755 : Blo 2279435 3420755 := bstep (se 1 (by rfl) ⟨2565566, by rfl⟩ : syracuseStep 3420755 = 5131133) B5131133
theorem B2280503 : Blo 2279435 2280503 := bstep (se 1 (by rfl) ⟨1710377, by rfl⟩ : syracuseStep 2280503 = 3420755) B3420755
theorem B3848357 : Blo 2279435 3848357 := bbase (se 4 (by rfl) ⟨360783, by rfl⟩ : syracuseStep 3848357 = 721567) (by norm_num)
theorem B2565571 : Blo 2279435 2565571 := bstep (se 1 (by rfl) ⟨1924178, by rfl⟩ : syracuseStep 2565571 = 3848357) B3848357
theorem B3420761 : Blo 2279435 3420761 := bstep (se 2 (by rfl) ⟨1282785, by rfl⟩ : syracuseStep 3420761 = 2565571) B2565571
theorem B2280507 : Blo 2279435 2280507 := bstep (se 1 (by rfl) ⟨1710380, by rfl⟩ : syracuseStep 2280507 = 3420761) B3420761
theorem B2435293 : Blo 2279435 2435293 := bbase (se 3 (by rfl) ⟨456617, by rfl⟩ : syracuseStep 2435293 = 913235) (by norm_num)
theorem B3247057 : Blo 2279435 3247057 := bstep (se 2 (by rfl) ⟨1217646, by rfl⟩ : syracuseStep 3247057 = 2435293) B2435293
theorem B17317637 : Blo 2279435 17317637 := bstep (se 4 (by rfl) ⟨1623528, by rfl⟩ : syracuseStep 17317637 = 3247057) B3247057
theorem B11545091 : Blo 2279435 11545091 := bstep (se 1 (by rfl) ⟨8658818, by rfl⟩ : syracuseStep 11545091 = 17317637) B17317637
theorem B7696727 : Blo 2279435 7696727 := bstep (se 1 (by rfl) ⟨5772545, by rfl⟩ : syracuseStep 7696727 = 11545091) B11545091
theorem B5131151 : Blo 2279435 5131151 := bstep (se 1 (by rfl) ⟨3848363, by rfl⟩ : syracuseStep 5131151 = 7696727) B7696727
theorem B3420767 : Blo 2279435 3420767 := bstep (se 1 (by rfl) ⟨2565575, by rfl⟩ : syracuseStep 3420767 = 5131151) B5131151
theorem B2280511 : Blo 2279435 2280511 := bstep (se 1 (by rfl) ⟨1710383, by rfl⟩ : syracuseStep 2280511 = 3420767) B3420767
theorem B3420773 : Blo 2279435 3420773 := bbase (se 4 (by rfl) ⟨320697, by rfl⟩ : syracuseStep 3420773 = 641395) (by norm_num)
theorem B2280515 : Blo 2279435 2280515 := bstep (se 1 (by rfl) ⟨1710386, by rfl⟩ : syracuseStep 2280515 = 3420773) B3420773
theorem B3247069 : Blo 2279435 3247069 := bbase (se 3 (by rfl) ⟨608825, by rfl⟩ : syracuseStep 3247069 = 1217651) (by norm_num)
theorem B4329425 : Blo 2279435 4329425 := bstep (se 2 (by rfl) ⟨1623534, by rfl⟩ : syracuseStep 4329425 = 3247069) B3247069
theorem B2886283 : Blo 2279435 2886283 := bstep (se 1 (by rfl) ⟨2164712, by rfl⟩ : syracuseStep 2886283 = 4329425) B4329425
theorem B3848377 : Blo 2279435 3848377 := bstep (se 2 (by rfl) ⟨1443141, by rfl⟩ : syracuseStep 3848377 = 2886283) B2886283
theorem B5131169 : Blo 2279435 5131169 := bstep (se 2 (by rfl) ⟨1924188, by rfl⟩ : syracuseStep 5131169 = 3848377) B3848377
theorem B3420779 : Blo 2279435 3420779 := bstep (se 1 (by rfl) ⟨2565584, by rfl⟩ : syracuseStep 3420779 = 5131169) B5131169
theorem B2280519 : Blo 2279435 2280519 := bstep (se 1 (by rfl) ⟨1710389, by rfl⟩ : syracuseStep 2280519 = 3420779) B3420779
theorem B2565589 : Blo 2279435 2565589 := bbase (se 7 (by rfl) ⟨30065, by rfl⟩ : syracuseStep 2565589 = 60131) (by norm_num)
theorem B3420785 : Blo 2279435 3420785 := bstep (se 2 (by rfl) ⟨1282794, by rfl⟩ : syracuseStep 3420785 = 2565589) B2565589
theorem B2280523 : Blo 2279435 2280523 := bstep (se 1 (by rfl) ⟨1710392, by rfl⟩ : syracuseStep 2280523 = 3420785) B3420785
theorem B2886293 : Blo 2279435 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B7696781 : Blo 2279435 7696781 := bstep (se 3 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 7696781 = 2886293) B2886293
theorem B5131187 : Blo 2279435 5131187 := bstep (se 1 (by rfl) ⟨3848390, by rfl⟩ : syracuseStep 5131187 = 7696781) B7696781
theorem B3420791 : Blo 2279435 3420791 := bstep (se 1 (by rfl) ⟨2565593, by rfl⟩ : syracuseStep 3420791 = 5131187) B5131187
theorem B2280527 : Blo 2279435 2280527 := bstep (se 1 (by rfl) ⟨1710395, by rfl⟩ : syracuseStep 2280527 = 3420791) B3420791
theorem B3420797 : Blo 2279435 3420797 := bbase (se 3 (by rfl) ⟨641399, by rfl⟩ : syracuseStep 3420797 = 1282799) (by norm_num)
theorem B2280531 : Blo 2279435 2280531 := bstep (se 1 (by rfl) ⟨1710398, by rfl⟩ : syracuseStep 2280531 = 3420797) B3420797
theorem B5131205 : Blo 2279435 5131205 := bbase (se 4 (by rfl) ⟨481050, by rfl⟩ : syracuseStep 5131205 = 962101) (by norm_num)
theorem B3420803 : Blo 2279435 3420803 := bstep (se 1 (by rfl) ⟨2565602, by rfl⟩ : syracuseStep 3420803 = 5131205) B5131205
theorem B2280535 : Blo 2279435 2280535 := bstep (se 1 (by rfl) ⟨1710401, by rfl⟩ : syracuseStep 2280535 = 3420803) B3420803
theorem B3124261 : Blo 2279435 3124261 := bbase (se 4 (by rfl) ⟨292899, by rfl⟩ : syracuseStep 3124261 = 585799) (by norm_num)
theorem B4165681 : Blo 2279435 4165681 := bstep (se 2 (by rfl) ⟨1562130, by rfl⟩ : syracuseStep 4165681 = 3124261) B3124261
theorem B5554241 : Blo 2279435 5554241 := bstep (se 2 (by rfl) ⟨2082840, by rfl⟩ : syracuseStep 5554241 = 4165681) B4165681
theorem B3702827 : Blo 2279435 3702827 := bstep (se 1 (by rfl) ⟨2777120, by rfl⟩ : syracuseStep 3702827 = 5554241) B5554241
theorem B2468551 : Blo 2279435 2468551 := bstep (se 1 (by rfl) ⟨1851413, by rfl⟩ : syracuseStep 2468551 = 3702827) B3702827
theorem B3291401 : Blo 2279435 3291401 := bstep (se 2 (by rfl) ⟨1234275, by rfl⟩ : syracuseStep 3291401 = 2468551) B2468551
theorem B8777069 : Blo 2279435 8777069 := bstep (se 3 (by rfl) ⟨1645700, by rfl⟩ : syracuseStep 8777069 = 3291401) B3291401
theorem B5851379 : Blo 2279435 5851379 := bstep (se 1 (by rfl) ⟨4388534, by rfl⟩ : syracuseStep 5851379 = 8777069) B8777069
theorem B15603677 : Blo 2279435 15603677 := bstep (se 3 (by rfl) ⟨2925689, by rfl⟩ : syracuseStep 15603677 = 5851379) B5851379
theorem B10402451 : Blo 2279435 10402451 := bstep (se 1 (by rfl) ⟨7801838, by rfl⟩ : syracuseStep 10402451 = 15603677) B15603677
theorem B6934967 : Blo 2279435 6934967 := bstep (se 1 (by rfl) ⟨5201225, by rfl⟩ : syracuseStep 6934967 = 10402451) B10402451
theorem B4623311 : Blo 2279435 4623311 := bstep (se 1 (by rfl) ⟨3467483, by rfl⟩ : syracuseStep 4623311 = 6934967) B6934967
theorem B3082207 : Blo 2279435 3082207 := bstep (se 1 (by rfl) ⟨2311655, by rfl⟩ : syracuseStep 3082207 = 4623311) B4623311
theorem B4109609 : Blo 2279435 4109609 := bstep (se 2 (by rfl) ⟨1541103, by rfl⟩ : syracuseStep 4109609 = 3082207) B3082207
theorem B2739739 : Blo 2279435 2739739 := bstep (se 1 (by rfl) ⟨2054804, by rfl⟩ : syracuseStep 2739739 = 4109609) B4109609
theorem B3652985 : Blo 2279435 3652985 := bstep (se 2 (by rfl) ⟨1369869, by rfl⟩ : syracuseStep 3652985 = 2739739) B2739739
theorem B9741293 : Blo 2279435 9741293 := bstep (se 3 (by rfl) ⟨1826492, by rfl⟩ : syracuseStep 9741293 = 3652985) B3652985
theorem B6494195 : Blo 2279435 6494195 := bstep (se 1 (by rfl) ⟨4870646, by rfl⟩ : syracuseStep 6494195 = 9741293) B9741293
theorem B4329463 : Blo 2279435 4329463 := bstep (se 1 (by rfl) ⟨3247097, by rfl⟩ : syracuseStep 4329463 = 6494195) B6494195
theorem B5772617 : Blo 2279435 5772617 := bstep (se 2 (by rfl) ⟨2164731, by rfl⟩ : syracuseStep 5772617 = 4329463) B4329463
theorem B3848411 : Blo 2279435 3848411 := bstep (se 1 (by rfl) ⟨2886308, by rfl⟩ : syracuseStep 3848411 = 5772617) B5772617
theorem B2565607 : Blo 2279435 2565607 := bstep (se 1 (by rfl) ⟨1924205, by rfl⟩ : syracuseStep 2565607 = 3848411) B3848411
theorem B3420809 : Blo 2279435 3420809 := bstep (se 2 (by rfl) ⟨1282803, by rfl⟩ : syracuseStep 3420809 = 2565607) B2565607
theorem B2280539 : Blo 2279435 2280539 := bstep (se 1 (by rfl) ⟨1710404, by rfl⟩ : syracuseStep 2280539 = 3420809) B3420809
theorem B11545253 : Blo 2279435 11545253 := bbase (se 4 (by rfl) ⟨1082367, by rfl⟩ : syracuseStep 11545253 = 2164735) (by norm_num)
theorem B7696835 : Blo 2279435 7696835 := bstep (se 1 (by rfl) ⟨5772626, by rfl⟩ : syracuseStep 7696835 = 11545253) B11545253
theorem B5131223 : Blo 2279435 5131223 := bstep (se 1 (by rfl) ⟨3848417, by rfl⟩ : syracuseStep 5131223 = 7696835) B7696835
theorem B3420815 : Blo 2279435 3420815 := bstep (se 1 (by rfl) ⟨2565611, by rfl⟩ : syracuseStep 3420815 = 5131223) B5131223
theorem B2280543 : Blo 2279435 2280543 := bstep (se 1 (by rfl) ⟨1710407, by rfl⟩ : syracuseStep 2280543 = 3420815) B3420815
theorem B3420821 : Blo 2279435 3420821 := bbase (se 6 (by rfl) ⟨80175, by rfl⟩ : syracuseStep 3420821 = 160351) (by norm_num)
theorem B2280547 : Blo 2279435 2280547 := bstep (se 1 (by rfl) ⟨1710410, by rfl⟩ : syracuseStep 2280547 = 3420821) B3420821
theorem B140433749 : Blo 2279435 140433749 := bbase (se 10 (by rfl) ⟨205713, by rfl⟩ : syracuseStep 140433749 = 411427) (by norm_num)
theorem B93622499 : Blo 2279435 93622499 := bstep (se 1 (by rfl) ⟨70216874, by rfl⟩ : syracuseStep 93622499 = 140433749) B140433749
theorem B62414999 : Blo 2279435 62414999 := bstep (se 1 (by rfl) ⟨46811249, by rfl⟩ : syracuseStep 62414999 = 93622499) B93622499
theorem B41609999 : Blo 2279435 41609999 := bstep (se 1 (by rfl) ⟨31207499, by rfl⟩ : syracuseStep 41609999 = 62414999) B62414999
theorem B27739999 : Blo 2279435 27739999 := bstep (se 1 (by rfl) ⟨20804999, by rfl⟩ : syracuseStep 27739999 = 41609999) B41609999
theorem B36986665 : Blo 2279435 36986665 := bstep (se 2 (by rfl) ⟨13869999, by rfl⟩ : syracuseStep 36986665 = 27739999) B27739999
theorem B49315553 : Blo 2279435 49315553 := bstep (se 2 (by rfl) ⟨18493332, by rfl⟩ : syracuseStep 49315553 = 36986665) B36986665
theorem B32877035 : Blo 2279435 32877035 := bstep (se 1 (by rfl) ⟨24657776, by rfl⟩ : syracuseStep 32877035 = 49315553) B49315553
theorem B21918023 : Blo 2279435 21918023 := bstep (se 1 (by rfl) ⟨16438517, by rfl⟩ : syracuseStep 21918023 = 32877035) B32877035
theorem B14612015 : Blo 2279435 14612015 := bstep (se 1 (by rfl) ⟨10959011, by rfl⟩ : syracuseStep 14612015 = 21918023) B21918023
theorem B9741343 : Blo 2279435 9741343 := bstep (se 1 (by rfl) ⟨7306007, by rfl⟩ : syracuseStep 9741343 = 14612015) B14612015
theorem B12988457 : Blo 2279435 12988457 := bstep (se 2 (by rfl) ⟨4870671, by rfl⟩ : syracuseStep 12988457 = 9741343) B9741343
theorem B8658971 : Blo 2279435 8658971 := bstep (se 1 (by rfl) ⟨6494228, by rfl⟩ : syracuseStep 8658971 = 12988457) B12988457
theorem B5772647 : Blo 2279435 5772647 := bstep (se 1 (by rfl) ⟨4329485, by rfl⟩ : syracuseStep 5772647 = 8658971) B8658971
theorem B3848431 : Blo 2279435 3848431 := bstep (se 1 (by rfl) ⟨2886323, by rfl⟩ : syracuseStep 3848431 = 5772647) B5772647
theorem B5131241 : Blo 2279435 5131241 := bstep (se 2 (by rfl) ⟨1924215, by rfl⟩ : syracuseStep 5131241 = 3848431) B3848431
theorem B3420827 : Blo 2279435 3420827 := bstep (se 1 (by rfl) ⟨2565620, by rfl⟩ : syracuseStep 3420827 = 5131241) B5131241
theorem B2280551 : Blo 2279435 2280551 := bstep (se 1 (by rfl) ⟨1710413, by rfl⟩ : syracuseStep 2280551 = 3420827) B3420827
theorem B2565625 : Blo 2279435 2565625 := bbase (se 2 (by rfl) ⟨962109, by rfl⟩ : syracuseStep 2565625 = 1924219) (by norm_num)
theorem B3420833 : Blo 2279435 3420833 := bstep (se 2 (by rfl) ⟨1282812, by rfl⟩ : syracuseStep 3420833 = 2565625) B2565625
theorem B2280555 : Blo 2279435 2280555 := bstep (se 1 (by rfl) ⟨1710416, by rfl⟩ : syracuseStep 2280555 = 3420833) B3420833
theorem B5479525 : Blo 2279435 5479525 := bbase (se 4 (by rfl) ⟨513705, by rfl⟩ : syracuseStep 5479525 = 1027411) (by norm_num)
theorem B7306033 : Blo 2279435 7306033 := bstep (se 2 (by rfl) ⟨2739762, by rfl⟩ : syracuseStep 7306033 = 5479525) B5479525
theorem B9741377 : Blo 2279435 9741377 := bstep (se 2 (by rfl) ⟨3653016, by rfl⟩ : syracuseStep 9741377 = 7306033) B7306033
theorem B6494251 : Blo 2279435 6494251 := bstep (se 1 (by rfl) ⟨4870688, by rfl⟩ : syracuseStep 6494251 = 9741377) B9741377
theorem B8659001 : Blo 2279435 8659001 := bstep (se 2 (by rfl) ⟨3247125, by rfl⟩ : syracuseStep 8659001 = 6494251) B6494251
theorem B5772667 : Blo 2279435 5772667 := bstep (se 1 (by rfl) ⟨4329500, by rfl⟩ : syracuseStep 5772667 = 8659001) B8659001
theorem B7696889 : Blo 2279435 7696889 := bstep (se 2 (by rfl) ⟨2886333, by rfl⟩ : syracuseStep 7696889 = 5772667) B5772667
theorem B5131259 : Blo 2279435 5131259 := bstep (se 1 (by rfl) ⟨3848444, by rfl⟩ : syracuseStep 5131259 = 7696889) B7696889
theorem B3420839 : Blo 2279435 3420839 := bstep (se 1 (by rfl) ⟨2565629, by rfl⟩ : syracuseStep 3420839 = 5131259) B5131259
theorem B2280559 : Blo 2279435 2280559 := bstep (se 1 (by rfl) ⟨1710419, by rfl⟩ : syracuseStep 2280559 = 3420839) B3420839
theorem B3420845 : Blo 2279435 3420845 := bbase (se 3 (by rfl) ⟨641408, by rfl⟩ : syracuseStep 3420845 = 1282817) (by norm_num)
theorem B2280563 : Blo 2279435 2280563 := bstep (se 1 (by rfl) ⟨1710422, by rfl⟩ : syracuseStep 2280563 = 3420845) B3420845
theorem B5131277 : Blo 2279435 5131277 := bbase (se 3 (by rfl) ⟨962114, by rfl⟩ : syracuseStep 5131277 = 1924229) (by norm_num)
theorem B3420851 : Blo 2279435 3420851 := bstep (se 1 (by rfl) ⟨2565638, by rfl⟩ : syracuseStep 3420851 = 5131277) B5131277
theorem B2280567 : Blo 2279435 2280567 := bstep (se 1 (by rfl) ⟨1710425, by rfl⟩ : syracuseStep 2280567 = 3420851) B3420851
theorem B2886349 : Blo 2279435 2886349 := bbase (se 3 (by rfl) ⟨541190, by rfl⟩ : syracuseStep 2886349 = 1082381) (by norm_num)
theorem B3848465 : Blo 2279435 3848465 := bstep (se 2 (by rfl) ⟨1443174, by rfl⟩ : syracuseStep 3848465 = 2886349) B2886349
theorem B2565643 : Blo 2279435 2565643 := bstep (se 1 (by rfl) ⟨1924232, by rfl⟩ : syracuseStep 2565643 = 3848465) B3848465
theorem B3420857 : Blo 2279435 3420857 := bstep (se 2 (by rfl) ⟨1282821, by rfl⟩ : syracuseStep 3420857 = 2565643) B2565643
theorem B2280571 : Blo 2279435 2280571 := bstep (se 1 (by rfl) ⟨1710428, by rfl⟩ : syracuseStep 2280571 = 3420857) B3420857
theorem B18493525 : Blo 2279435 18493525 := bbase (se 8 (by rfl) ⟨108360, by rfl⟩ : syracuseStep 18493525 = 216721) (by norm_num)
theorem B24658033 : Blo 2279435 24658033 := bstep (se 2 (by rfl) ⟨9246762, by rfl⟩ : syracuseStep 24658033 = 18493525) B18493525
theorem B32877377 : Blo 2279435 32877377 := bstep (se 2 (by rfl) ⟨12329016, by rfl⟩ : syracuseStep 32877377 = 24658033) B24658033
theorem B21918251 : Blo 2279435 21918251 := bstep (se 1 (by rfl) ⟨16438688, by rfl⟩ : syracuseStep 21918251 = 32877377) B32877377
theorem B14612167 : Blo 2279435 14612167 := bstep (se 1 (by rfl) ⟨10959125, by rfl⟩ : syracuseStep 14612167 = 21918251) B21918251
theorem B19482889 : Blo 2279435 19482889 := bstep (se 2 (by rfl) ⟨7306083, by rfl⟩ : syracuseStep 19482889 = 14612167) B14612167
theorem B25977185 : Blo 2279435 25977185 := bstep (se 2 (by rfl) ⟨9741444, by rfl⟩ : syracuseStep 25977185 = 19482889) B19482889
theorem B17318123 : Blo 2279435 17318123 := bstep (se 1 (by rfl) ⟨12988592, by rfl⟩ : syracuseStep 17318123 = 25977185) B25977185
theorem B11545415 : Blo 2279435 11545415 := bstep (se 1 (by rfl) ⟨8659061, by rfl⟩ : syracuseStep 11545415 = 17318123) B17318123
theorem B7696943 : Blo 2279435 7696943 := bstep (se 1 (by rfl) ⟨5772707, by rfl⟩ : syracuseStep 7696943 = 11545415) B11545415
theorem B5131295 : Blo 2279435 5131295 := bstep (se 1 (by rfl) ⟨3848471, by rfl⟩ : syracuseStep 5131295 = 7696943) B7696943
theorem B3420863 : Blo 2279435 3420863 := bstep (se 1 (by rfl) ⟨2565647, by rfl⟩ : syracuseStep 3420863 = 5131295) B5131295
theorem B2280575 : Blo 2279435 2280575 := bstep (se 1 (by rfl) ⟨1710431, by rfl⟩ : syracuseStep 2280575 = 3420863) B3420863
theorem B3420869 : Blo 2279435 3420869 := bbase (se 4 (by rfl) ⟨320706, by rfl⟩ : syracuseStep 3420869 = 641413) (by norm_num)
theorem B2280579 : Blo 2279435 2280579 := bstep (se 1 (by rfl) ⟨1710434, by rfl⟩ : syracuseStep 2280579 = 3420869) B3420869
theorem B3848485 : Blo 2279435 3848485 := bbase (se 4 (by rfl) ⟨360795, by rfl⟩ : syracuseStep 3848485 = 721591) (by norm_num)
theorem B5131313 : Blo 2279435 5131313 := bstep (se 2 (by rfl) ⟨1924242, by rfl⟩ : syracuseStep 5131313 = 3848485) B3848485
theorem B3420875 : Blo 2279435 3420875 := bstep (se 1 (by rfl) ⟨2565656, by rfl⟩ : syracuseStep 3420875 = 5131313) B5131313
theorem B2280583 : Blo 2279435 2280583 := bstep (se 1 (by rfl) ⟨1710437, by rfl⟩ : syracuseStep 2280583 = 3420875) B3420875
theorem B2565661 : Blo 2279435 2565661 := bbase (se 3 (by rfl) ⟨481061, by rfl⟩ : syracuseStep 2565661 = 962123) (by norm_num)
theorem B3420881 : Blo 2279435 3420881 := bstep (se 2 (by rfl) ⟨1282830, by rfl⟩ : syracuseStep 3420881 = 2565661) B2565661
theorem B2280587 : Blo 2279435 2280587 := bstep (se 1 (by rfl) ⟨1710440, by rfl⟩ : syracuseStep 2280587 = 3420881) B3420881
theorem B7696997 : Blo 2279435 7696997 := bbase (se 4 (by rfl) ⟨721593, by rfl⟩ : syracuseStep 7696997 = 1443187) (by norm_num)
theorem B5131331 : Blo 2279435 5131331 := bstep (se 1 (by rfl) ⟨3848498, by rfl⟩ : syracuseStep 5131331 = 7696997) B7696997
theorem B3420887 : Blo 2279435 3420887 := bstep (se 1 (by rfl) ⟨2565665, by rfl⟩ : syracuseStep 3420887 = 5131331) B5131331
theorem B2280591 : Blo 2279435 2280591 := bstep (se 1 (by rfl) ⟨1710443, by rfl⟩ : syracuseStep 2280591 = 3420887) B3420887
theorem B3420893 : Blo 2279435 3420893 := bbase (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) (by norm_num)
theorem B2280595 : Blo 2279435 2280595 := bstep (se 1 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 2280595 = 3420893) B3420893
theorem B5131349 : Blo 2279435 5131349 := bbase (se 8 (by rfl) ⟨30066, by rfl⟩ : syracuseStep 5131349 = 60133) (by norm_num)
theorem B3420899 : Blo 2279435 3420899 := bstep (se 1 (by rfl) ⟨2565674, by rfl⟩ : syracuseStep 3420899 = 5131349) B5131349
theorem B2280599 : Blo 2279435 2280599 := bstep (se 1 (by rfl) ⟨1710449, by rfl⟩ : syracuseStep 2280599 = 3420899) B3420899
theorem B8331589 : Blo 2279435 8331589 := bbase (se 4 (by rfl) ⟨781086, by rfl⟩ : syracuseStep 8331589 = 1562173) (by norm_num)
theorem B44435141 : Blo 2279435 44435141 := bstep (se 4 (by rfl) ⟨4165794, by rfl⟩ : syracuseStep 44435141 = 8331589) B8331589
theorem B29623427 : Blo 2279435 29623427 := bstep (se 1 (by rfl) ⟨22217570, by rfl⟩ : syracuseStep 29623427 = 44435141) B44435141
theorem B19748951 : Blo 2279435 19748951 := bstep (se 1 (by rfl) ⟨14811713, by rfl⟩ : syracuseStep 19748951 = 29623427) B29623427
theorem B13165967 : Blo 2279435 13165967 := bstep (se 1 (by rfl) ⟨9874475, by rfl⟩ : syracuseStep 13165967 = 19748951) B19748951
theorem B8777311 : Blo 2279435 8777311 := bstep (se 1 (by rfl) ⟨6582983, by rfl⟩ : syracuseStep 8777311 = 13165967) B13165967
theorem B46812325 : Blo 2279435 46812325 := bstep (se 4 (by rfl) ⟨4388655, by rfl⟩ : syracuseStep 46812325 = 8777311) B8777311
theorem B62416433 : Blo 2279435 62416433 := bstep (se 2 (by rfl) ⟨23406162, by rfl⟩ : syracuseStep 62416433 = 46812325) B46812325
theorem B41610955 : Blo 2279435 41610955 := bstep (se 1 (by rfl) ⟨31208216, by rfl⟩ : syracuseStep 41610955 = 62416433) B62416433
theorem B55481273 : Blo 2279435 55481273 := bstep (se 2 (by rfl) ⟨20805477, by rfl⟩ : syracuseStep 55481273 = 41610955) B41610955
theorem B36987515 : Blo 2279435 36987515 := bstep (se 1 (by rfl) ⟨27740636, by rfl⟩ : syracuseStep 36987515 = 55481273) B55481273
theorem B24658343 : Blo 2279435 24658343 := bstep (se 1 (by rfl) ⟨18493757, by rfl⟩ : syracuseStep 24658343 = 36987515) B36987515
theorem B16438895 : Blo 2279435 16438895 := bstep (se 1 (by rfl) ⟨12329171, by rfl⟩ : syracuseStep 16438895 = 24658343) B24658343
theorem B10959263 : Blo 2279435 10959263 := bstep (se 1 (by rfl) ⟨8219447, by rfl⟩ : syracuseStep 10959263 = 16438895) B16438895
theorem B7306175 : Blo 2279435 7306175 := bstep (se 1 (by rfl) ⟨5479631, by rfl⟩ : syracuseStep 7306175 = 10959263) B10959263
theorem B4870783 : Blo 2279435 4870783 := bstep (se 1 (by rfl) ⟨3653087, by rfl⟩ : syracuseStep 4870783 = 7306175) B7306175
theorem B6494377 : Blo 2279435 6494377 := bstep (se 2 (by rfl) ⟨2435391, by rfl⟩ : syracuseStep 6494377 = 4870783) B4870783
theorem B8659169 : Blo 2279435 8659169 := bstep (se 2 (by rfl) ⟨3247188, by rfl⟩ : syracuseStep 8659169 = 6494377) B6494377
theorem B5772779 : Blo 2279435 5772779 := bstep (se 1 (by rfl) ⟨4329584, by rfl⟩ : syracuseStep 5772779 = 8659169) B8659169
theorem B3848519 : Blo 2279435 3848519 := bstep (se 1 (by rfl) ⟨2886389, by rfl⟩ : syracuseStep 3848519 = 5772779) B5772779
theorem B2565679 : Blo 2279435 2565679 := bstep (se 1 (by rfl) ⟨1924259, by rfl⟩ : syracuseStep 2565679 = 3848519) B3848519
theorem B3420905 : Blo 2279435 3420905 := bstep (se 2 (by rfl) ⟨1282839, by rfl⟩ : syracuseStep 3420905 = 2565679) B2565679
theorem B2280603 : Blo 2279435 2280603 := bstep (se 1 (by rfl) ⟨1710452, by rfl⟩ : syracuseStep 2280603 = 3420905) B3420905
theorem B8331605 : Blo 2279435 8331605 := bbase (se 10 (by rfl) ⟨12204, by rfl⟩ : syracuseStep 8331605 = 24409) (by norm_num)
theorem B5554403 : Blo 2279435 5554403 := bstep (se 1 (by rfl) ⟨4165802, by rfl⟩ : syracuseStep 5554403 = 8331605) B8331605
theorem B3702935 : Blo 2279435 3702935 := bstep (se 1 (by rfl) ⟨2777201, by rfl⟩ : syracuseStep 3702935 = 5554403) B5554403
theorem B9874493 : Blo 2279435 9874493 := bstep (se 3 (by rfl) ⟨1851467, by rfl⟩ : syracuseStep 9874493 = 3702935) B3702935
theorem B6582995 : Blo 2279435 6582995 := bstep (se 1 (by rfl) ⟨4937246, by rfl⟩ : syracuseStep 6582995 = 9874493) B9874493
theorem B4388663 : Blo 2279435 4388663 := bstep (se 1 (by rfl) ⟨3291497, by rfl⟩ : syracuseStep 4388663 = 6582995) B6582995
theorem B2925775 : Blo 2279435 2925775 := bstep (se 1 (by rfl) ⟨2194331, by rfl⟩ : syracuseStep 2925775 = 4388663) B4388663
theorem B3901033 : Blo 2279435 3901033 := bstep (se 2 (by rfl) ⟨1462887, by rfl⟩ : syracuseStep 3901033 = 2925775) B2925775
theorem B5201377 : Blo 2279435 5201377 := bstep (se 2 (by rfl) ⟨1950516, by rfl⟩ : syracuseStep 5201377 = 3901033) B3901033
theorem B110962709 : Blo 2279435 110962709 := bstep (se 6 (by rfl) ⟨2600688, by rfl⟩ : syracuseStep 110962709 = 5201377) B5201377
theorem B73975139 : Blo 2279435 73975139 := bstep (se 1 (by rfl) ⟨55481354, by rfl⟩ : syracuseStep 73975139 = 110962709) B110962709
theorem B49316759 : Blo 2279435 49316759 := bstep (se 1 (by rfl) ⟨36987569, by rfl⟩ : syracuseStep 49316759 = 73975139) B73975139
theorem B32877839 : Blo 2279435 32877839 := bstep (se 1 (by rfl) ⟨24658379, by rfl⟩ : syracuseStep 32877839 = 49316759) B49316759
theorem B21918559 : Blo 2279435 21918559 := bstep (se 1 (by rfl) ⟨16438919, by rfl⟩ : syracuseStep 21918559 = 32877839) B32877839
theorem B29224745 : Blo 2279435 29224745 := bstep (se 2 (by rfl) ⟨10959279, by rfl⟩ : syracuseStep 29224745 = 21918559) B21918559
theorem B19483163 : Blo 2279435 19483163 := bstep (se 1 (by rfl) ⟨14612372, by rfl⟩ : syracuseStep 19483163 = 29224745) B29224745
theorem B12988775 : Blo 2279435 12988775 := bstep (se 1 (by rfl) ⟨9741581, by rfl⟩ : syracuseStep 12988775 = 19483163) B19483163
theorem B8659183 : Blo 2279435 8659183 := bstep (se 1 (by rfl) ⟨6494387, by rfl⟩ : syracuseStep 8659183 = 12988775) B12988775
theorem B11545577 : Blo 2279435 11545577 := bstep (se 2 (by rfl) ⟨4329591, by rfl⟩ : syracuseStep 11545577 = 8659183) B8659183
theorem B7697051 : Blo 2279435 7697051 := bstep (se 1 (by rfl) ⟨5772788, by rfl⟩ : syracuseStep 7697051 = 11545577) B11545577
theorem B5131367 : Blo 2279435 5131367 := bstep (se 1 (by rfl) ⟨3848525, by rfl⟩ : syracuseStep 5131367 = 7697051) B7697051
theorem B3420911 : Blo 2279435 3420911 := bstep (se 1 (by rfl) ⟨2565683, by rfl⟩ : syracuseStep 3420911 = 5131367) B5131367
theorem B2280607 : Blo 2279435 2280607 := bstep (se 1 (by rfl) ⟨1710455, by rfl⟩ : syracuseStep 2280607 = 3420911) B3420911
theorem B3420917 : Blo 2279435 3420917 := bbase (se 5 (by rfl) ⟨160355, by rfl⟩ : syracuseStep 3420917 = 320711) (by norm_num)
theorem B2280611 : Blo 2279435 2280611 := bstep (se 1 (by rfl) ⟨1710458, by rfl⟩ : syracuseStep 2280611 = 3420917) B3420917
theorem B7306213 : Blo 2279435 7306213 := bbase (se 4 (by rfl) ⟨684957, by rfl⟩ : syracuseStep 7306213 = 1369915) (by norm_num)
theorem B9741617 : Blo 2279435 9741617 := bstep (se 2 (by rfl) ⟨3653106, by rfl⟩ : syracuseStep 9741617 = 7306213) B7306213
theorem B6494411 : Blo 2279435 6494411 := bstep (se 1 (by rfl) ⟨4870808, by rfl⟩ : syracuseStep 6494411 = 9741617) B9741617
theorem B4329607 : Blo 2279435 4329607 := bstep (se 1 (by rfl) ⟨3247205, by rfl⟩ : syracuseStep 4329607 = 6494411) B6494411
theorem B5772809 : Blo 2279435 5772809 := bstep (se 2 (by rfl) ⟨2164803, by rfl⟩ : syracuseStep 5772809 = 4329607) B4329607
theorem B3848539 : Blo 2279435 3848539 := bstep (se 1 (by rfl) ⟨2886404, by rfl⟩ : syracuseStep 3848539 = 5772809) B5772809
theorem B5131385 : Blo 2279435 5131385 := bstep (se 2 (by rfl) ⟨1924269, by rfl⟩ : syracuseStep 5131385 = 3848539) B3848539
theorem B3420923 : Blo 2279435 3420923 := bstep (se 1 (by rfl) ⟨2565692, by rfl⟩ : syracuseStep 3420923 = 5131385) B5131385
theorem B2280615 : Blo 2279435 2280615 := bstep (se 1 (by rfl) ⟨1710461, by rfl⟩ : syracuseStep 2280615 = 3420923) B3420923
theorem B2565697 : Blo 2279435 2565697 := bbase (se 2 (by rfl) ⟨962136, by rfl⟩ : syracuseStep 2565697 = 1924273) (by norm_num)
theorem B3420929 : Blo 2279435 3420929 := bstep (se 2 (by rfl) ⟨1282848, by rfl⟩ : syracuseStep 3420929 = 2565697) B2565697
theorem B2280619 : Blo 2279435 2280619 := bstep (se 1 (by rfl) ⟨1710464, by rfl⟩ : syracuseStep 2280619 = 3420929) B3420929
theorem B5772829 : Blo 2279435 5772829 := bbase (se 3 (by rfl) ⟨1082405, by rfl⟩ : syracuseStep 5772829 = 2164811) (by norm_num)
theorem B7697105 : Blo 2279435 7697105 := bstep (se 2 (by rfl) ⟨2886414, by rfl⟩ : syracuseStep 7697105 = 5772829) B5772829
theorem B5131403 : Blo 2279435 5131403 := bstep (se 1 (by rfl) ⟨3848552, by rfl⟩ : syracuseStep 5131403 = 7697105) B7697105
theorem B3420935 : Blo 2279435 3420935 := bstep (se 1 (by rfl) ⟨2565701, by rfl⟩ : syracuseStep 3420935 = 5131403) B5131403
theorem B2280623 : Blo 2279435 2280623 := bstep (se 1 (by rfl) ⟨1710467, by rfl⟩ : syracuseStep 2280623 = 3420935) B3420935
theorem B3420941 : Blo 2279435 3420941 := bbase (se 3 (by rfl) ⟨641426, by rfl⟩ : syracuseStep 3420941 = 1282853) (by norm_num)
theorem B2280627 : Blo 2279435 2280627 := bstep (se 1 (by rfl) ⟨1710470, by rfl⟩ : syracuseStep 2280627 = 3420941) B3420941
theorem B5131421 : Blo 2279435 5131421 := bbase (se 3 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 5131421 = 1924283) (by norm_num)
theorem B3420947 : Blo 2279435 3420947 := bstep (se 1 (by rfl) ⟨2565710, by rfl⟩ : syracuseStep 3420947 = 5131421) B5131421
theorem B2280631 : Blo 2279435 2280631 := bstep (se 1 (by rfl) ⟨1710473, by rfl⟩ : syracuseStep 2280631 = 3420947) B3420947
theorem B3848573 : Blo 2279435 3848573 := bbase (se 3 (by rfl) ⟨721607, by rfl⟩ : syracuseStep 3848573 = 1443215) (by norm_num)
theorem B2565715 : Blo 2279435 2565715 := bstep (se 1 (by rfl) ⟨1924286, by rfl⟩ : syracuseStep 2565715 = 3848573) B3848573
theorem B3420953 : Blo 2279435 3420953 := bstep (se 2 (by rfl) ⟨1282857, by rfl⟩ : syracuseStep 3420953 = 2565715) B2565715
theorem B2280635 : Blo 2279435 2280635 := bstep (se 1 (by rfl) ⟨1710476, by rfl⟩ : syracuseStep 2280635 = 3420953) B3420953
theorem B5479717 : Blo 2279435 5479717 := bbase (se 4 (by rfl) ⟨513723, by rfl⟩ : syracuseStep 5479717 = 1027447) (by norm_num)
theorem B7306289 : Blo 2279435 7306289 := bstep (se 2 (by rfl) ⟨2739858, by rfl⟩ : syracuseStep 7306289 = 5479717) B5479717
theorem B4870859 : Blo 2279435 4870859 := bstep (se 1 (by rfl) ⟨3653144, by rfl⟩ : syracuseStep 4870859 = 7306289) B7306289
theorem B12988957 : Blo 2279435 12988957 := bstep (se 3 (by rfl) ⟨2435429, by rfl⟩ : syracuseStep 12988957 = 4870859) B4870859
theorem B17318609 : Blo 2279435 17318609 := bstep (se 2 (by rfl) ⟨6494478, by rfl⟩ : syracuseStep 17318609 = 12988957) B12988957
theorem B11545739 : Blo 2279435 11545739 := bstep (se 1 (by rfl) ⟨8659304, by rfl⟩ : syracuseStep 11545739 = 17318609) B17318609
theorem B7697159 : Blo 2279435 7697159 := bstep (se 1 (by rfl) ⟨5772869, by rfl⟩ : syracuseStep 7697159 = 11545739) B11545739
theorem B5131439 : Blo 2279435 5131439 := bstep (se 1 (by rfl) ⟨3848579, by rfl⟩ : syracuseStep 5131439 = 7697159) B7697159
theorem B3420959 : Blo 2279435 3420959 := bstep (se 1 (by rfl) ⟨2565719, by rfl⟩ : syracuseStep 3420959 = 5131439) B5131439
theorem B2280639 : Blo 2279435 2280639 := bstep (se 1 (by rfl) ⟨1710479, by rfl⟩ : syracuseStep 2280639 = 3420959) B3420959
theorem B3420965 : Blo 2279435 3420965 := bbase (se 4 (by rfl) ⟨320715, by rfl⟩ : syracuseStep 3420965 = 641431) (by norm_num)
theorem B2280643 : Blo 2279435 2280643 := bstep (se 1 (by rfl) ⟨1710482, by rfl⟩ : syracuseStep 2280643 = 3420965) B3420965
theorem B2886445 : Blo 2279435 2886445 := bbase (se 3 (by rfl) ⟨541208, by rfl⟩ : syracuseStep 2886445 = 1082417) (by norm_num)
theorem B3848593 : Blo 2279435 3848593 := bstep (se 2 (by rfl) ⟨1443222, by rfl⟩ : syracuseStep 3848593 = 2886445) B2886445
theorem B5131457 : Blo 2279435 5131457 := bstep (se 2 (by rfl) ⟨1924296, by rfl⟩ : syracuseStep 5131457 = 3848593) B3848593
theorem B3420971 : Blo 2279435 3420971 := bstep (se 1 (by rfl) ⟨2565728, by rfl⟩ : syracuseStep 3420971 = 5131457) B5131457
theorem B2280647 : Blo 2279435 2280647 := bstep (se 1 (by rfl) ⟨1710485, by rfl⟩ : syracuseStep 2280647 = 3420971) B3420971
theorem B2565733 : Blo 2279435 2565733 := bbase (se 4 (by rfl) ⟨240537, by rfl⟩ : syracuseStep 2565733 = 481075) (by norm_num)
theorem B3420977 : Blo 2279435 3420977 := bstep (se 2 (by rfl) ⟨1282866, by rfl⟩ : syracuseStep 3420977 = 2565733) B2565733
theorem B2280651 : Blo 2279435 2280651 := bstep (se 1 (by rfl) ⟨1710488, by rfl⟩ : syracuseStep 2280651 = 3420977) B3420977
theorem B5479757 : Blo 2279435 5479757 := bbase (se 3 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 5479757 = 2054909) (by norm_num)
theorem B3653171 : Blo 2279435 3653171 := bstep (se 1 (by rfl) ⟨2739878, by rfl⟩ : syracuseStep 3653171 = 5479757) B5479757
theorem B2435447 : Blo 2279435 2435447 := bstep (se 1 (by rfl) ⟨1826585, by rfl⟩ : syracuseStep 2435447 = 3653171) B3653171
theorem B6494525 : Blo 2279435 6494525 := bstep (se 3 (by rfl) ⟨1217723, by rfl⟩ : syracuseStep 6494525 = 2435447) B2435447
theorem B4329683 : Blo 2279435 4329683 := bstep (se 1 (by rfl) ⟨3247262, by rfl⟩ : syracuseStep 4329683 = 6494525) B6494525
theorem B2886455 : Blo 2279435 2886455 := bstep (se 1 (by rfl) ⟨2164841, by rfl⟩ : syracuseStep 2886455 = 4329683) B4329683
theorem B7697213 : Blo 2279435 7697213 := bstep (se 3 (by rfl) ⟨1443227, by rfl⟩ : syracuseStep 7697213 = 2886455) B2886455
theorem B5131475 : Blo 2279435 5131475 := bstep (se 1 (by rfl) ⟨3848606, by rfl⟩ : syracuseStep 5131475 = 7697213) B7697213
theorem B3420983 : Blo 2279435 3420983 := bstep (se 1 (by rfl) ⟨2565737, by rfl⟩ : syracuseStep 3420983 = 5131475) B5131475
theorem B2280655 : Blo 2279435 2280655 := bstep (se 1 (by rfl) ⟨1710491, by rfl⟩ : syracuseStep 2280655 = 3420983) B3420983
theorem B3420989 : Blo 2279435 3420989 := bbase (se 3 (by rfl) ⟨641435, by rfl⟩ : syracuseStep 3420989 = 1282871) (by norm_num)
theorem B2280659 : Blo 2279435 2280659 := bstep (se 1 (by rfl) ⟨1710494, by rfl⟩ : syracuseStep 2280659 = 3420989) B3420989
theorem B5131493 : Blo 2279435 5131493 := bbase (se 4 (by rfl) ⟨481077, by rfl⟩ : syracuseStep 5131493 = 962155) (by norm_num)
theorem B3420995 : Blo 2279435 3420995 := bstep (se 1 (by rfl) ⟨2565746, by rfl⟩ : syracuseStep 3420995 = 5131493) B5131493
theorem B2280663 : Blo 2279435 2280663 := bstep (se 1 (by rfl) ⟨1710497, by rfl⟩ : syracuseStep 2280663 = 3420995) B3420995
theorem B5772941 : Blo 2279435 5772941 := bbase (se 3 (by rfl) ⟨1082426, by rfl⟩ : syracuseStep 5772941 = 2164853) (by norm_num)
theorem B3848627 : Blo 2279435 3848627 := bstep (se 1 (by rfl) ⟨2886470, by rfl⟩ : syracuseStep 3848627 = 5772941) B5772941
theorem B2565751 : Blo 2279435 2565751 := bstep (se 1 (by rfl) ⟨1924313, by rfl⟩ : syracuseStep 2565751 = 3848627) B3848627
theorem B3421001 : Blo 2279435 3421001 := bstep (se 2 (by rfl) ⟨1282875, by rfl⟩ : syracuseStep 3421001 = 2565751) B2565751
theorem B2280667 : Blo 2279435 2280667 := bstep (se 1 (by rfl) ⟨1710500, by rfl⟩ : syracuseStep 2280667 = 3421001) B3421001
theorem B3247285 : Blo 2279435 3247285 := bbase (se 5 (by rfl) ⟨152216, by rfl⟩ : syracuseStep 3247285 = 304433) (by norm_num)
theorem B4329713 : Blo 2279435 4329713 := bstep (se 2 (by rfl) ⟨1623642, by rfl⟩ : syracuseStep 4329713 = 3247285) B3247285
theorem B11545901 : Blo 2279435 11545901 := bstep (se 3 (by rfl) ⟨2164856, by rfl⟩ : syracuseStep 11545901 = 4329713) B4329713
theorem B7697267 : Blo 2279435 7697267 := bstep (se 1 (by rfl) ⟨5772950, by rfl⟩ : syracuseStep 7697267 = 11545901) B11545901
theorem B5131511 : Blo 2279435 5131511 := bstep (se 1 (by rfl) ⟨3848633, by rfl⟩ : syracuseStep 5131511 = 7697267) B7697267
theorem B3421007 : Blo 2279435 3421007 := bstep (se 1 (by rfl) ⟨2565755, by rfl⟩ : syracuseStep 3421007 = 5131511) B5131511
theorem B2280671 : Blo 2279435 2280671 := bstep (se 1 (by rfl) ⟨1710503, by rfl⟩ : syracuseStep 2280671 = 3421007) B3421007
theorem B3421013 : Blo 2279435 3421013 := bbase (se 9 (by rfl) ⟨10022, by rfl⟩ : syracuseStep 3421013 = 20045) (by norm_num)
theorem B2280675 : Blo 2279435 2280675 := bstep (se 1 (by rfl) ⟨1710506, by rfl⟩ : syracuseStep 2280675 = 3421013) B3421013
theorem B4109861 : Blo 2279435 4109861 := bbase (se 4 (by rfl) ⟨385299, by rfl⟩ : syracuseStep 4109861 = 770599) (by norm_num)
theorem B2739907 : Blo 2279435 2739907 := bstep (se 1 (by rfl) ⟨2054930, by rfl⟩ : syracuseStep 2739907 = 4109861) B4109861
theorem B3653209 : Blo 2279435 3653209 := bstep (se 2 (by rfl) ⟨1369953, by rfl⟩ : syracuseStep 3653209 = 2739907) B2739907
theorem B4870945 : Blo 2279435 4870945 := bstep (se 2 (by rfl) ⟨1826604, by rfl⟩ : syracuseStep 4870945 = 3653209) B3653209
theorem B6494593 : Blo 2279435 6494593 := bstep (se 2 (by rfl) ⟨2435472, by rfl⟩ : syracuseStep 6494593 = 4870945) B4870945
theorem B8659457 : Blo 2279435 8659457 := bstep (se 2 (by rfl) ⟨3247296, by rfl⟩ : syracuseStep 8659457 = 6494593) B6494593
theorem B5772971 : Blo 2279435 5772971 := bstep (se 1 (by rfl) ⟨4329728, by rfl⟩ : syracuseStep 5772971 = 8659457) B8659457
theorem B3848647 : Blo 2279435 3848647 := bstep (se 1 (by rfl) ⟨2886485, by rfl⟩ : syracuseStep 3848647 = 5772971) B5772971
theorem B5131529 : Blo 2279435 5131529 := bstep (se 2 (by rfl) ⟨1924323, by rfl⟩ : syracuseStep 5131529 = 3848647) B3848647
theorem B3421019 : Blo 2279435 3421019 := bstep (se 1 (by rfl) ⟨2565764, by rfl⟩ : syracuseStep 3421019 = 5131529) B5131529
theorem B2280679 : Blo 2279435 2280679 := bstep (se 1 (by rfl) ⟨1710509, by rfl⟩ : syracuseStep 2280679 = 3421019) B3421019
theorem B2565769 : Blo 2279435 2565769 := bbase (se 2 (by rfl) ⟨962163, by rfl⟩ : syracuseStep 2565769 = 1924327) (by norm_num)
theorem B3421025 : Blo 2279435 3421025 := bstep (se 2 (by rfl) ⟨1282884, by rfl⟩ : syracuseStep 3421025 = 2565769) B2565769
theorem B2280683 : Blo 2279435 2280683 := bstep (se 1 (by rfl) ⟨1710512, by rfl⟩ : syracuseStep 2280683 = 3421025) B3421025
theorem B6935413 : Blo 2279435 6935413 := bbase (se 5 (by rfl) ⟨325097, by rfl⟩ : syracuseStep 6935413 = 650195) (by norm_num)
theorem B9247217 : Blo 2279435 9247217 := bstep (se 2 (by rfl) ⟨3467706, by rfl⟩ : syracuseStep 9247217 = 6935413) B6935413
theorem B24659245 : Blo 2279435 24659245 := bstep (se 3 (by rfl) ⟨4623608, by rfl⟩ : syracuseStep 24659245 = 9247217) B9247217
theorem B32878993 : Blo 2279435 32878993 := bstep (se 2 (by rfl) ⟨12329622, by rfl⟩ : syracuseStep 32878993 = 24659245) B24659245
theorem B43838657 : Blo 2279435 43838657 := bstep (se 2 (by rfl) ⟨16439496, by rfl⟩ : syracuseStep 43838657 = 32878993) B32878993
theorem B29225771 : Blo 2279435 29225771 := bstep (se 1 (by rfl) ⟨21919328, by rfl⟩ : syracuseStep 29225771 = 43838657) B43838657
theorem B19483847 : Blo 2279435 19483847 := bstep (se 1 (by rfl) ⟨14612885, by rfl⟩ : syracuseStep 19483847 = 29225771) B29225771
theorem B12989231 : Blo 2279435 12989231 := bstep (se 1 (by rfl) ⟨9741923, by rfl⟩ : syracuseStep 12989231 = 19483847) B19483847
theorem B8659487 : Blo 2279435 8659487 := bstep (se 1 (by rfl) ⟨6494615, by rfl⟩ : syracuseStep 8659487 = 12989231) B12989231
theorem B5772991 : Blo 2279435 5772991 := bstep (se 1 (by rfl) ⟨4329743, by rfl⟩ : syracuseStep 5772991 = 8659487) B8659487
theorem B7697321 : Blo 2279435 7697321 := bstep (se 2 (by rfl) ⟨2886495, by rfl⟩ : syracuseStep 7697321 = 5772991) B5772991
theorem B5131547 : Blo 2279435 5131547 := bstep (se 1 (by rfl) ⟨3848660, by rfl⟩ : syracuseStep 5131547 = 7697321) B7697321
theorem B3421031 : Blo 2279435 3421031 := bstep (se 1 (by rfl) ⟨2565773, by rfl⟩ : syracuseStep 3421031 = 5131547) B5131547
theorem B2280687 : Blo 2279435 2280687 := bstep (se 1 (by rfl) ⟨1710515, by rfl⟩ : syracuseStep 2280687 = 3421031) B3421031
theorem B3421037 : Blo 2279435 3421037 := bbase (se 3 (by rfl) ⟨641444, by rfl⟩ : syracuseStep 3421037 = 1282889) (by norm_num)
theorem B2280691 : Blo 2279435 2280691 := bstep (se 1 (by rfl) ⟨1710518, by rfl⟩ : syracuseStep 2280691 = 3421037) B3421037
theorem B5131565 : Blo 2279435 5131565 := bbase (se 3 (by rfl) ⟨962168, by rfl⟩ : syracuseStep 5131565 = 1924337) (by norm_num)
theorem B3421043 : Blo 2279435 3421043 := bstep (se 1 (by rfl) ⟨2565782, by rfl⟩ : syracuseStep 3421043 = 5131565) B5131565
theorem B2280695 : Blo 2279435 2280695 := bstep (se 1 (by rfl) ⟨1710521, by rfl⟩ : syracuseStep 2280695 = 3421043) B3421043
theorem B3954421 : Blo 2279435 3954421 := bbase (se 5 (by rfl) ⟨185363, by rfl⟩ : syracuseStep 3954421 = 370727) (by norm_num)
theorem B5272561 : Blo 2279435 5272561 := bstep (se 2 (by rfl) ⟨1977210, by rfl⟩ : syracuseStep 5272561 = 3954421) B3954421
theorem B7030081 : Blo 2279435 7030081 := bstep (se 2 (by rfl) ⟨2636280, by rfl⟩ : syracuseStep 7030081 = 5272561) B5272561
theorem B9373441 : Blo 2279435 9373441 := bstep (se 2 (by rfl) ⟨3515040, by rfl⟩ : syracuseStep 9373441 = 7030081) B7030081
theorem B12497921 : Blo 2279435 12497921 := bstep (se 2 (by rfl) ⟨4686720, by rfl⟩ : syracuseStep 12497921 = 9373441) B9373441
theorem B8331947 : Blo 2279435 8331947 := bstep (se 1 (by rfl) ⟨6248960, by rfl⟩ : syracuseStep 8331947 = 12497921) B12497921
theorem B5554631 : Blo 2279435 5554631 := bstep (se 1 (by rfl) ⟨4165973, by rfl⟩ : syracuseStep 5554631 = 8331947) B8331947
theorem B3703087 : Blo 2279435 3703087 := bstep (se 1 (by rfl) ⟨2777315, by rfl⟩ : syracuseStep 3703087 = 5554631) B5554631
theorem B4937449 : Blo 2279435 4937449 := bstep (se 2 (by rfl) ⟨1851543, by rfl⟩ : syracuseStep 4937449 = 3703087) B3703087
theorem B6583265 : Blo 2279435 6583265 := bstep (se 2 (by rfl) ⟨2468724, by rfl⟩ : syracuseStep 6583265 = 4937449) B4937449
theorem B4388843 : Blo 2279435 4388843 := bstep (se 1 (by rfl) ⟨3291632, by rfl⟩ : syracuseStep 4388843 = 6583265) B6583265
theorem B2925895 : Blo 2279435 2925895 := bstep (se 1 (by rfl) ⟨2194421, by rfl⟩ : syracuseStep 2925895 = 4388843) B4388843
theorem B3901193 : Blo 2279435 3901193 := bstep (se 2 (by rfl) ⟨1462947, by rfl⟩ : syracuseStep 3901193 = 2925895) B2925895
theorem B2600795 : Blo 2279435 2600795 := bstep (se 1 (by rfl) ⟨1950596, by rfl⟩ : syracuseStep 2600795 = 3901193) B3901193
theorem B6935453 : Blo 2279435 6935453 := bstep (se 3 (by rfl) ⟨1300397, by rfl⟩ : syracuseStep 6935453 = 2600795) B2600795
theorem B4623635 : Blo 2279435 4623635 := bstep (se 1 (by rfl) ⟨3467726, by rfl⟩ : syracuseStep 4623635 = 6935453) B6935453
theorem B3082423 : Blo 2279435 3082423 := bstep (se 1 (by rfl) ⟨2311817, by rfl⟩ : syracuseStep 3082423 = 4623635) B4623635
theorem B4109897 : Blo 2279435 4109897 := bstep (se 2 (by rfl) ⟨1541211, by rfl⟩ : syracuseStep 4109897 = 3082423) B3082423
theorem B10959725 : Blo 2279435 10959725 := bstep (se 3 (by rfl) ⟨2054948, by rfl⟩ : syracuseStep 10959725 = 4109897) B4109897
theorem B7306483 : Blo 2279435 7306483 := bstep (se 1 (by rfl) ⟨5479862, by rfl⟩ : syracuseStep 7306483 = 10959725) B10959725
theorem B9741977 : Blo 2279435 9741977 := bstep (se 2 (by rfl) ⟨3653241, by rfl⟩ : syracuseStep 9741977 = 7306483) B7306483
theorem B6494651 : Blo 2279435 6494651 := bstep (se 1 (by rfl) ⟨4870988, by rfl⟩ : syracuseStep 6494651 = 9741977) B9741977
theorem B4329767 : Blo 2279435 4329767 := bstep (se 1 (by rfl) ⟨3247325, by rfl⟩ : syracuseStep 4329767 = 6494651) B6494651
theorem B2886511 : Blo 2279435 2886511 := bstep (se 1 (by rfl) ⟨2164883, by rfl⟩ : syracuseStep 2886511 = 4329767) B4329767
theorem B3848681 : Blo 2279435 3848681 := bstep (se 2 (by rfl) ⟨1443255, by rfl⟩ : syracuseStep 3848681 = 2886511) B2886511
theorem B2565787 : Blo 2279435 2565787 := bstep (se 1 (by rfl) ⟨1924340, by rfl⟩ : syracuseStep 2565787 = 3848681) B3848681
theorem B3421049 : Blo 2279435 3421049 := bstep (se 2 (by rfl) ⟨1282893, by rfl⟩ : syracuseStep 3421049 = 2565787) B2565787
theorem B2280699 : Blo 2279435 2280699 := bstep (se 1 (by rfl) ⟨1710524, by rfl⟩ : syracuseStep 2280699 = 3421049) B3421049
theorem B27741845 : Blo 2279435 27741845 := bbase (se 6 (by rfl) ⟨650199, by rfl⟩ : syracuseStep 27741845 = 1300399) (by norm_num)
theorem B18494563 : Blo 2279435 18494563 := bstep (se 1 (by rfl) ⟨13870922, by rfl⟩ : syracuseStep 18494563 = 27741845) B27741845
theorem B24659417 : Blo 2279435 24659417 := bstep (se 2 (by rfl) ⟨9247281, by rfl⟩ : syracuseStep 24659417 = 18494563) B18494563
theorem B16439611 : Blo 2279435 16439611 := bstep (se 1 (by rfl) ⟨12329708, by rfl⟩ : syracuseStep 16439611 = 24659417) B24659417
theorem B21919481 : Blo 2279435 21919481 := bstep (se 2 (by rfl) ⟨8219805, by rfl⟩ : syracuseStep 21919481 = 16439611) B16439611
theorem B14612987 : Blo 2279435 14612987 := bstep (se 1 (by rfl) ⟨10959740, by rfl⟩ : syracuseStep 14612987 = 21919481) B21919481
theorem B38967965 : Blo 2279435 38967965 := bstep (se 3 (by rfl) ⟨7306493, by rfl⟩ : syracuseStep 38967965 = 14612987) B14612987
theorem B25978643 : Blo 2279435 25978643 := bstep (se 1 (by rfl) ⟨19483982, by rfl⟩ : syracuseStep 25978643 = 38967965) B38967965
theorem B17319095 : Blo 2279435 17319095 := bstep (se 1 (by rfl) ⟨12989321, by rfl⟩ : syracuseStep 17319095 = 25978643) B25978643
theorem B11546063 : Blo 2279435 11546063 := bstep (se 1 (by rfl) ⟨8659547, by rfl⟩ : syracuseStep 11546063 = 17319095) B17319095
theorem B7697375 : Blo 2279435 7697375 := bstep (se 1 (by rfl) ⟨5773031, by rfl⟩ : syracuseStep 7697375 = 11546063) B11546063
theorem B5131583 : Blo 2279435 5131583 := bstep (se 1 (by rfl) ⟨3848687, by rfl⟩ : syracuseStep 5131583 = 7697375) B7697375
theorem B3421055 : Blo 2279435 3421055 := bstep (se 1 (by rfl) ⟨2565791, by rfl⟩ : syracuseStep 3421055 = 5131583) B5131583
theorem B2280703 : Blo 2279435 2280703 := bstep (se 1 (by rfl) ⟨1710527, by rfl⟩ : syracuseStep 2280703 = 3421055) B3421055
theorem B3421061 : Blo 2279435 3421061 := bbase (se 4 (by rfl) ⟨320724, by rfl⟩ : syracuseStep 3421061 = 641449) (by norm_num)
theorem B2280707 : Blo 2279435 2280707 := bstep (se 1 (by rfl) ⟨1710530, by rfl⟩ : syracuseStep 2280707 = 3421061) B3421061
theorem B3848701 : Blo 2279435 3848701 := bbase (se 3 (by rfl) ⟨721631, by rfl⟩ : syracuseStep 3848701 = 1443263) (by norm_num)
theorem B5131601 : Blo 2279435 5131601 := bstep (se 2 (by rfl) ⟨1924350, by rfl⟩ : syracuseStep 5131601 = 3848701) B3848701
theorem B3421067 : Blo 2279435 3421067 := bstep (se 1 (by rfl) ⟨2565800, by rfl⟩ : syracuseStep 3421067 = 5131601) B5131601
theorem B2280711 : Blo 2279435 2280711 := bstep (se 1 (by rfl) ⟨1710533, by rfl⟩ : syracuseStep 2280711 = 3421067) B3421067
theorem B2565805 : Blo 2279435 2565805 := bbase (se 3 (by rfl) ⟨481088, by rfl⟩ : syracuseStep 2565805 = 962177) (by norm_num)
theorem B3421073 : Blo 2279435 3421073 := bstep (se 2 (by rfl) ⟨1282902, by rfl⟩ : syracuseStep 3421073 = 2565805) B2565805
theorem B2280715 : Blo 2279435 2280715 := bstep (se 1 (by rfl) ⟨1710536, by rfl⟩ : syracuseStep 2280715 = 3421073) B3421073
theorem B7697429 : Blo 2279435 7697429 := bbase (se 6 (by rfl) ⟨180408, by rfl⟩ : syracuseStep 7697429 = 360817) (by norm_num)
theorem B5131619 : Blo 2279435 5131619 := bstep (se 1 (by rfl) ⟨3848714, by rfl⟩ : syracuseStep 5131619 = 7697429) B7697429
theorem B3421079 : Blo 2279435 3421079 := bstep (se 1 (by rfl) ⟨2565809, by rfl⟩ : syracuseStep 3421079 = 5131619) B5131619
theorem B2280719 : Blo 2279435 2280719 := bstep (se 1 (by rfl) ⟨1710539, by rfl⟩ : syracuseStep 2280719 = 3421079) B3421079
theorem B3421085 : Blo 2279435 3421085 := bbase (se 3 (by rfl) ⟨641453, by rfl⟩ : syracuseStep 3421085 = 1282907) (by norm_num)
theorem B2280723 : Blo 2279435 2280723 := bstep (se 1 (by rfl) ⟨1710542, by rfl⟩ : syracuseStep 2280723 = 3421085) B3421085
theorem B5131637 : Blo 2279435 5131637 := bbase (se 5 (by rfl) ⟨240545, by rfl⟩ : syracuseStep 5131637 = 481091) (by norm_num)
theorem B3421091 : Blo 2279435 3421091 := bstep (se 1 (by rfl) ⟨2565818, by rfl⟩ : syracuseStep 3421091 = 5131637) B5131637
theorem B2280727 : Blo 2279435 2280727 := bstep (se 1 (by rfl) ⟨1710545, by rfl⟩ : syracuseStep 2280727 = 3421091) B3421091
theorem B10959877 : Blo 2279435 10959877 := bbase (se 4 (by rfl) ⟨1027488, by rfl⟩ : syracuseStep 10959877 = 2054977) (by norm_num)
theorem B14613169 : Blo 2279435 14613169 := bstep (se 2 (by rfl) ⟨5479938, by rfl⟩ : syracuseStep 14613169 = 10959877) B10959877
theorem B19484225 : Blo 2279435 19484225 := bstep (se 2 (by rfl) ⟨7306584, by rfl⟩ : syracuseStep 19484225 = 14613169) B14613169
theorem B12989483 : Blo 2279435 12989483 := bstep (se 1 (by rfl) ⟨9742112, by rfl⟩ : syracuseStep 12989483 = 19484225) B19484225
theorem B8659655 : Blo 2279435 8659655 := bstep (se 1 (by rfl) ⟨6494741, by rfl⟩ : syracuseStep 8659655 = 12989483) B12989483
theorem B5773103 : Blo 2279435 5773103 := bstep (se 1 (by rfl) ⟨4329827, by rfl⟩ : syracuseStep 5773103 = 8659655) B8659655
theorem B3848735 : Blo 2279435 3848735 := bstep (se 1 (by rfl) ⟨2886551, by rfl⟩ : syracuseStep 3848735 = 5773103) B5773103
theorem B2565823 : Blo 2279435 2565823 := bstep (se 1 (by rfl) ⟨1924367, by rfl⟩ : syracuseStep 2565823 = 3848735) B3848735
theorem B3421097 : Blo 2279435 3421097 := bstep (se 2 (by rfl) ⟨1282911, by rfl⟩ : syracuseStep 3421097 = 2565823) B2565823
theorem B2280731 : Blo 2279435 2280731 := bstep (se 1 (by rfl) ⟨1710548, by rfl⟩ : syracuseStep 2280731 = 3421097) B3421097
theorem B8659669 : Blo 2279435 8659669 := bbase (se 7 (by rfl) ⟨101480, by rfl⟩ : syracuseStep 8659669 = 202961) (by norm_num)
theorem B11546225 : Blo 2279435 11546225 := bstep (se 2 (by rfl) ⟨4329834, by rfl⟩ : syracuseStep 11546225 = 8659669) B8659669
theorem B7697483 : Blo 2279435 7697483 := bstep (se 1 (by rfl) ⟨5773112, by rfl⟩ : syracuseStep 7697483 = 11546225) B11546225
theorem B5131655 : Blo 2279435 5131655 := bstep (se 1 (by rfl) ⟨3848741, by rfl⟩ : syracuseStep 5131655 = 7697483) B7697483
theorem B3421103 : Blo 2279435 3421103 := bstep (se 1 (by rfl) ⟨2565827, by rfl⟩ : syracuseStep 3421103 = 5131655) B5131655
theorem B2280735 : Blo 2279435 2280735 := bstep (se 1 (by rfl) ⟨1710551, by rfl⟩ : syracuseStep 2280735 = 3421103) B3421103
theorem B3421109 : Blo 2279435 3421109 := bbase (se 5 (by rfl) ⟨160364, by rfl⟩ : syracuseStep 3421109 = 320729) (by norm_num)
theorem B2280739 : Blo 2279435 2280739 := bstep (se 1 (by rfl) ⟨1710554, by rfl⟩ : syracuseStep 2280739 = 3421109) B3421109
theorem B5773133 : Blo 2279435 5773133 := bbase (se 3 (by rfl) ⟨1082462, by rfl⟩ : syracuseStep 5773133 = 2164925) (by norm_num)
theorem B3848755 : Blo 2279435 3848755 := bstep (se 1 (by rfl) ⟨2886566, by rfl⟩ : syracuseStep 3848755 = 5773133) B5773133
theorem B5131673 : Blo 2279435 5131673 := bstep (se 2 (by rfl) ⟨1924377, by rfl⟩ : syracuseStep 5131673 = 3848755) B3848755
theorem B3421115 : Blo 2279435 3421115 := bstep (se 1 (by rfl) ⟨2565836, by rfl⟩ : syracuseStep 3421115 = 5131673) B5131673
theorem B2280743 : Blo 2279435 2280743 := bstep (se 1 (by rfl) ⟨1710557, by rfl⟩ : syracuseStep 2280743 = 3421115) B3421115
theorem B2565841 : Blo 2279435 2565841 := bbase (se 2 (by rfl) ⟨962190, by rfl⟩ : syracuseStep 2565841 = 1924381) (by norm_num)
theorem B3421121 : Blo 2279435 3421121 := bstep (se 2 (by rfl) ⟨1282920, by rfl⟩ : syracuseStep 3421121 = 2565841) B2565841
theorem B2280747 : Blo 2279435 2280747 := bstep (se 1 (by rfl) ⟨1710560, by rfl⟩ : syracuseStep 2280747 = 3421121) B3421121
theorem B3082493 : Blo 2279435 3082493 := bbase (se 3 (by rfl) ⟨577967, by rfl⟩ : syracuseStep 3082493 = 1155935) (by norm_num)
theorem B8219981 : Blo 2279435 8219981 := bstep (se 3 (by rfl) ⟨1541246, by rfl⟩ : syracuseStep 8219981 = 3082493) B3082493
theorem B5479987 : Blo 2279435 5479987 := bstep (se 1 (by rfl) ⟨4109990, by rfl⟩ : syracuseStep 5479987 = 8219981) B8219981
theorem B7306649 : Blo 2279435 7306649 := bstep (se 2 (by rfl) ⟨2739993, by rfl⟩ : syracuseStep 7306649 = 5479987) B5479987
theorem B4871099 : Blo 2279435 4871099 := bstep (se 1 (by rfl) ⟨3653324, by rfl⟩ : syracuseStep 4871099 = 7306649) B7306649
theorem B3247399 : Blo 2279435 3247399 := bstep (se 1 (by rfl) ⟨2435549, by rfl⟩ : syracuseStep 3247399 = 4871099) B4871099
theorem B4329865 : Blo 2279435 4329865 := bstep (se 2 (by rfl) ⟨1623699, by rfl⟩ : syracuseStep 4329865 = 3247399) B3247399
theorem B5773153 : Blo 2279435 5773153 := bstep (se 2 (by rfl) ⟨2164932, by rfl⟩ : syracuseStep 5773153 = 4329865) B4329865
theorem B7697537 : Blo 2279435 7697537 := bstep (se 2 (by rfl) ⟨2886576, by rfl⟩ : syracuseStep 7697537 = 5773153) B5773153
theorem B5131691 : Blo 2279435 5131691 := bstep (se 1 (by rfl) ⟨3848768, by rfl⟩ : syracuseStep 5131691 = 7697537) B7697537
theorem B3421127 : Blo 2279435 3421127 := bstep (se 1 (by rfl) ⟨2565845, by rfl⟩ : syracuseStep 3421127 = 5131691) B5131691
theorem B2280751 : Blo 2279435 2280751 := bstep (se 1 (by rfl) ⟨1710563, by rfl⟩ : syracuseStep 2280751 = 3421127) B3421127
theorem B3421133 : Blo 2279435 3421133 := bbase (se 3 (by rfl) ⟨641462, by rfl⟩ : syracuseStep 3421133 = 1282925) (by norm_num)
theorem B2280755 : Blo 2279435 2280755 := bstep (se 1 (by rfl) ⟨1710566, by rfl⟩ : syracuseStep 2280755 = 3421133) B3421133
theorem B5131709 : Blo 2279435 5131709 := bbase (se 3 (by rfl) ⟨962195, by rfl⟩ : syracuseStep 5131709 = 1924391) (by norm_num)
theorem B3421139 : Blo 2279435 3421139 := bstep (se 1 (by rfl) ⟨2565854, by rfl⟩ : syracuseStep 3421139 = 5131709) B5131709
theorem B2280759 : Blo 2279435 2280759 := bstep (se 1 (by rfl) ⟨1710569, by rfl⟩ : syracuseStep 2280759 = 3421139) B3421139
theorem B3848789 : Blo 2279435 3848789 := bbase (se 8 (by rfl) ⟨22551, by rfl⟩ : syracuseStep 3848789 = 45103) (by norm_num)
theorem B2565859 : Blo 2279435 2565859 := bstep (se 1 (by rfl) ⟨1924394, by rfl⟩ : syracuseStep 2565859 = 3848789) B3848789
theorem B3421145 : Blo 2279435 3421145 := bstep (se 2 (by rfl) ⟨1282929, by rfl⟩ : syracuseStep 3421145 = 2565859) B2565859
theorem B2280763 : Blo 2279435 2280763 := bstep (se 1 (by rfl) ⟨1710572, by rfl⟩ : syracuseStep 2280763 = 3421145) B3421145
theorem B8220037 : Blo 2279435 8220037 := bbase (se 4 (by rfl) ⟨770628, by rfl⟩ : syracuseStep 8220037 = 1541257) (by norm_num)
theorem B10960049 : Blo 2279435 10960049 := bstep (se 2 (by rfl) ⟨4110018, by rfl⟩ : syracuseStep 10960049 = 8220037) B8220037
theorem B7306699 : Blo 2279435 7306699 := bstep (se 1 (by rfl) ⟨5480024, by rfl⟩ : syracuseStep 7306699 = 10960049) B10960049
theorem B9742265 : Blo 2279435 9742265 := bstep (se 2 (by rfl) ⟨3653349, by rfl⟩ : syracuseStep 9742265 = 7306699) B7306699
theorem B6494843 : Blo 2279435 6494843 := bstep (se 1 (by rfl) ⟨4871132, by rfl⟩ : syracuseStep 6494843 = 9742265) B9742265
theorem B17319581 : Blo 2279435 17319581 := bstep (se 3 (by rfl) ⟨3247421, by rfl⟩ : syracuseStep 17319581 = 6494843) B6494843
theorem B11546387 : Blo 2279435 11546387 := bstep (se 1 (by rfl) ⟨8659790, by rfl⟩ : syracuseStep 11546387 = 17319581) B17319581
theorem B7697591 : Blo 2279435 7697591 := bstep (se 1 (by rfl) ⟨5773193, by rfl⟩ : syracuseStep 7697591 = 11546387) B11546387
theorem B5131727 : Blo 2279435 5131727 := bstep (se 1 (by rfl) ⟨3848795, by rfl⟩ : syracuseStep 5131727 = 7697591) B7697591
theorem B3421151 : Blo 2279435 3421151 := bstep (se 1 (by rfl) ⟨2565863, by rfl⟩ : syracuseStep 3421151 = 5131727) B5131727
theorem B2280767 : Blo 2279435 2280767 := bstep (se 1 (by rfl) ⟨1710575, by rfl⟩ : syracuseStep 2280767 = 3421151) B3421151
theorem B3421157 : Blo 2279435 3421157 := bbase (se 4 (by rfl) ⟨320733, by rfl⟩ : syracuseStep 3421157 = 641467) (by norm_num)
theorem B2280771 : Blo 2279435 2280771 := bstep (se 1 (by rfl) ⟨1710578, by rfl⟩ : syracuseStep 2280771 = 3421157) B3421157
theorem B5480045 : Blo 2279435 5480045 := bbase (se 3 (by rfl) ⟨1027508, by rfl⟩ : syracuseStep 5480045 = 2055017) (by norm_num)
theorem B3653363 : Blo 2279435 3653363 := bstep (se 1 (by rfl) ⟨2740022, by rfl⟩ : syracuseStep 3653363 = 5480045) B5480045
theorem B9742301 : Blo 2279435 9742301 := bstep (se 3 (by rfl) ⟨1826681, by rfl⟩ : syracuseStep 9742301 = 3653363) B3653363
theorem B6494867 : Blo 2279435 6494867 := bstep (se 1 (by rfl) ⟨4871150, by rfl⟩ : syracuseStep 6494867 = 9742301) B9742301
theorem B4329911 : Blo 2279435 4329911 := bstep (se 1 (by rfl) ⟨3247433, by rfl⟩ : syracuseStep 4329911 = 6494867) B6494867
theorem B2886607 : Blo 2279435 2886607 := bstep (se 1 (by rfl) ⟨2164955, by rfl⟩ : syracuseStep 2886607 = 4329911) B4329911
theorem B3848809 : Blo 2279435 3848809 := bstep (se 2 (by rfl) ⟨1443303, by rfl⟩ : syracuseStep 3848809 = 2886607) B2886607
theorem B5131745 : Blo 2279435 5131745 := bstep (se 2 (by rfl) ⟨1924404, by rfl⟩ : syracuseStep 5131745 = 3848809) B3848809
theorem B3421163 : Blo 2279435 3421163 := bstep (se 1 (by rfl) ⟨2565872, by rfl⟩ : syracuseStep 3421163 = 5131745) B5131745
theorem B2280775 : Blo 2279435 2280775 := bstep (se 1 (by rfl) ⟨1710581, by rfl⟩ : syracuseStep 2280775 = 3421163) B3421163
theorem B2565877 : Blo 2279435 2565877 := bbase (se 5 (by rfl) ⟨120275, by rfl⟩ : syracuseStep 2565877 = 240551) (by norm_num)
theorem B3421169 : Blo 2279435 3421169 := bstep (se 2 (by rfl) ⟨1282938, by rfl⟩ : syracuseStep 3421169 = 2565877) B2565877
theorem B2280779 : Blo 2279435 2280779 := bstep (se 1 (by rfl) ⟨1710584, by rfl⟩ : syracuseStep 2280779 = 3421169) B3421169
theorem B2886617 : Blo 2279435 2886617 := bbase (se 2 (by rfl) ⟨1082481, by rfl⟩ : syracuseStep 2886617 = 2164963) (by norm_num)
theorem B7697645 : Blo 2279435 7697645 := bstep (se 3 (by rfl) ⟨1443308, by rfl⟩ : syracuseStep 7697645 = 2886617) B2886617
theorem B5131763 : Blo 2279435 5131763 := bstep (se 1 (by rfl) ⟨3848822, by rfl⟩ : syracuseStep 5131763 = 7697645) B7697645
theorem B3421175 : Blo 2279435 3421175 := bstep (se 1 (by rfl) ⟨2565881, by rfl⟩ : syracuseStep 3421175 = 5131763) B5131763
theorem B2280783 : Blo 2279435 2280783 := bstep (se 1 (by rfl) ⟨1710587, by rfl⟩ : syracuseStep 2280783 = 3421175) B3421175
theorem B3421181 : Blo 2279435 3421181 := bbase (se 3 (by rfl) ⟨641471, by rfl⟩ : syracuseStep 3421181 = 1282943) (by norm_num)
theorem B2280787 : Blo 2279435 2280787 := bstep (se 1 (by rfl) ⟨1710590, by rfl⟩ : syracuseStep 2280787 = 3421181) B3421181
theorem B5131781 : Blo 2279435 5131781 := bbase (se 4 (by rfl) ⟨481104, by rfl⟩ : syracuseStep 5131781 = 962209) (by norm_num)
theorem B3421187 : Blo 2279435 3421187 := bstep (se 1 (by rfl) ⟨2565890, by rfl⟩ : syracuseStep 3421187 = 5131781) B5131781
theorem B2280791 : Blo 2279435 2280791 := bstep (se 1 (by rfl) ⟨1710593, by rfl⟩ : syracuseStep 2280791 = 3421187) B3421187
theorem B4329949 : Blo 2279435 4329949 := bbase (se 3 (by rfl) ⟨811865, by rfl⟩ : syracuseStep 4329949 = 1623731) (by norm_num)
theorem B5773265 : Blo 2279435 5773265 := bstep (se 2 (by rfl) ⟨2164974, by rfl⟩ : syracuseStep 5773265 = 4329949) B4329949
theorem B3848843 : Blo 2279435 3848843 := bstep (se 1 (by rfl) ⟨2886632, by rfl⟩ : syracuseStep 3848843 = 5773265) B5773265
theorem B2565895 : Blo 2279435 2565895 := bstep (se 1 (by rfl) ⟨1924421, by rfl⟩ : syracuseStep 2565895 = 3848843) B3848843
theorem B3421193 : Blo 2279435 3421193 := bstep (se 2 (by rfl) ⟨1282947, by rfl⟩ : syracuseStep 3421193 = 2565895) B2565895
theorem B2280795 : Blo 2279435 2280795 := bstep (se 1 (by rfl) ⟨1710596, by rfl⟩ : syracuseStep 2280795 = 3421193) B3421193
theorem B11546549 : Blo 2279435 11546549 := bbase (se 5 (by rfl) ⟨541244, by rfl⟩ : syracuseStep 11546549 = 1082489) (by norm_num)
theorem B7697699 : Blo 2279435 7697699 := bstep (se 1 (by rfl) ⟨5773274, by rfl⟩ : syracuseStep 7697699 = 11546549) B11546549
theorem B5131799 : Blo 2279435 5131799 := bstep (se 1 (by rfl) ⟨3848849, by rfl⟩ : syracuseStep 5131799 = 7697699) B7697699
theorem B3421199 : Blo 2279435 3421199 := bstep (se 1 (by rfl) ⟨2565899, by rfl⟩ : syracuseStep 3421199 = 5131799) B5131799
theorem B2280799 : Blo 2279435 2280799 := bstep (se 1 (by rfl) ⟨1710599, by rfl⟩ : syracuseStep 2280799 = 3421199) B3421199
theorem B3421205 : Blo 2279435 3421205 := bbase (se 6 (by rfl) ⟨80184, by rfl⟩ : syracuseStep 3421205 = 160369) (by norm_num)
theorem B2280803 : Blo 2279435 2280803 := bstep (se 1 (by rfl) ⟨1710602, by rfl⟩ : syracuseStep 2280803 = 3421205) B3421205
theorem B32880725 : Blo 2279435 32880725 := bbase (se 8 (by rfl) ⟨192660, by rfl⟩ : syracuseStep 32880725 = 385321) (by norm_num)
theorem B21920483 : Blo 2279435 21920483 := bstep (se 1 (by rfl) ⟨16440362, by rfl⟩ : syracuseStep 21920483 = 32880725) B32880725
theorem B14613655 : Blo 2279435 14613655 := bstep (se 1 (by rfl) ⟨10960241, by rfl⟩ : syracuseStep 14613655 = 21920483) B21920483
theorem B19484873 : Blo 2279435 19484873 := bstep (se 2 (by rfl) ⟨7306827, by rfl⟩ : syracuseStep 19484873 = 14613655) B14613655
theorem B12989915 : Blo 2279435 12989915 := bstep (se 1 (by rfl) ⟨9742436, by rfl⟩ : syracuseStep 12989915 = 19484873) B19484873
theorem B8659943 : Blo 2279435 8659943 := bstep (se 1 (by rfl) ⟨6494957, by rfl⟩ : syracuseStep 8659943 = 12989915) B12989915
theorem B5773295 : Blo 2279435 5773295 := bstep (se 1 (by rfl) ⟨4329971, by rfl⟩ : syracuseStep 5773295 = 8659943) B8659943
theorem B3848863 : Blo 2279435 3848863 := bstep (se 1 (by rfl) ⟨2886647, by rfl⟩ : syracuseStep 3848863 = 5773295) B5773295
theorem B5131817 : Blo 2279435 5131817 := bstep (se 2 (by rfl) ⟨1924431, by rfl⟩ : syracuseStep 5131817 = 3848863) B3848863
theorem B3421211 : Blo 2279435 3421211 := bstep (se 1 (by rfl) ⟨2565908, by rfl⟩ : syracuseStep 3421211 = 5131817) B5131817
theorem B2280807 : Blo 2279435 2280807 := bstep (se 1 (by rfl) ⟨1710605, by rfl⟩ : syracuseStep 2280807 = 3421211) B3421211
theorem B2565913 : Blo 2279435 2565913 := bbase (se 2 (by rfl) ⟨962217, by rfl⟩ : syracuseStep 2565913 = 1924435) (by norm_num)
theorem B3421217 : Blo 2279435 3421217 := bstep (se 2 (by rfl) ⟨1282956, by rfl⟩ : syracuseStep 3421217 = 2565913) B2565913
theorem B2280811 : Blo 2279435 2280811 := bstep (se 1 (by rfl) ⟨1710608, by rfl⟩ : syracuseStep 2280811 = 3421217) B3421217
theorem B8659973 : Blo 2279435 8659973 := bbase (se 4 (by rfl) ⟨811872, by rfl⟩ : syracuseStep 8659973 = 1623745) (by norm_num)
theorem B5773315 : Blo 2279435 5773315 := bstep (se 1 (by rfl) ⟨4329986, by rfl⟩ : syracuseStep 5773315 = 8659973) B8659973
theorem B7697753 : Blo 2279435 7697753 := bstep (se 2 (by rfl) ⟨2886657, by rfl⟩ : syracuseStep 7697753 = 5773315) B5773315
theorem B5131835 : Blo 2279435 5131835 := bstep (se 1 (by rfl) ⟨3848876, by rfl⟩ : syracuseStep 5131835 = 7697753) B7697753
theorem B3421223 : Blo 2279435 3421223 := bstep (se 1 (by rfl) ⟨2565917, by rfl⟩ : syracuseStep 3421223 = 5131835) B5131835
theorem B2280815 : Blo 2279435 2280815 := bstep (se 1 (by rfl) ⟨1710611, by rfl⟩ : syracuseStep 2280815 = 3421223) B3421223
theorem B3421229 : Blo 2279435 3421229 := bbase (se 3 (by rfl) ⟨641480, by rfl⟩ : syracuseStep 3421229 = 1282961) (by norm_num)
theorem B2280819 : Blo 2279435 2280819 := bstep (se 1 (by rfl) ⟨1710614, by rfl⟩ : syracuseStep 2280819 = 3421229) B3421229
theorem B5131853 : Blo 2279435 5131853 := bbase (se 3 (by rfl) ⟨962222, by rfl⟩ : syracuseStep 5131853 = 1924445) (by norm_num)
theorem B3421235 : Blo 2279435 3421235 := bstep (se 1 (by rfl) ⟨2565926, by rfl⟩ : syracuseStep 3421235 = 5131853) B5131853
theorem B2280823 : Blo 2279435 2280823 := bstep (se 1 (by rfl) ⟨1710617, by rfl⟩ : syracuseStep 2280823 = 3421235) B3421235
theorem B2886673 : Blo 2279435 2886673 := bbase (se 2 (by rfl) ⟨1082502, by rfl⟩ : syracuseStep 2886673 = 2165005) (by norm_num)
theorem B3848897 : Blo 2279435 3848897 := bstep (se 2 (by rfl) ⟨1443336, by rfl⟩ : syracuseStep 3848897 = 2886673) B2886673
theorem B2565931 : Blo 2279435 2565931 := bstep (se 1 (by rfl) ⟨1924448, by rfl⟩ : syracuseStep 2565931 = 3848897) B3848897
theorem B3421241 : Blo 2279435 3421241 := bstep (se 2 (by rfl) ⟨1282965, by rfl⟩ : syracuseStep 3421241 = 2565931) B2565931
theorem B2280827 : Blo 2279435 2280827 := bstep (se 1 (by rfl) ⟨1710620, by rfl⟩ : syracuseStep 2280827 = 3421241) B3421241
theorem B4871269 : Blo 2279435 4871269 := bbase (se 4 (by rfl) ⟨456681, by rfl⟩ : syracuseStep 4871269 = 913363) (by norm_num)
theorem B25980101 : Blo 2279435 25980101 := bstep (se 4 (by rfl) ⟨2435634, by rfl⟩ : syracuseStep 25980101 = 4871269) B4871269
theorem B17320067 : Blo 2279435 17320067 := bstep (se 1 (by rfl) ⟨12990050, by rfl⟩ : syracuseStep 17320067 = 25980101) B25980101
theorem B11546711 : Blo 2279435 11546711 := bstep (se 1 (by rfl) ⟨8660033, by rfl⟩ : syracuseStep 11546711 = 17320067) B17320067
theorem B7697807 : Blo 2279435 7697807 := bstep (se 1 (by rfl) ⟨5773355, by rfl⟩ : syracuseStep 7697807 = 11546711) B11546711
theorem B5131871 : Blo 2279435 5131871 := bstep (se 1 (by rfl) ⟨3848903, by rfl⟩ : syracuseStep 5131871 = 7697807) B7697807
theorem B3421247 : Blo 2279435 3421247 := bstep (se 1 (by rfl) ⟨2565935, by rfl⟩ : syracuseStep 3421247 = 5131871) B5131871
theorem B2280831 : Blo 2279435 2280831 := bstep (se 1 (by rfl) ⟨1710623, by rfl⟩ : syracuseStep 2280831 = 3421247) B3421247
theorem B3421253 : Blo 2279435 3421253 := bbase (se 4 (by rfl) ⟨320742, by rfl⟩ : syracuseStep 3421253 = 641485) (by norm_num)
theorem B2280835 : Blo 2279435 2280835 := bstep (se 1 (by rfl) ⟨1710626, by rfl⟩ : syracuseStep 2280835 = 3421253) B3421253
theorem B3848917 : Blo 2279435 3848917 := bbase (se 7 (by rfl) ⟨45104, by rfl⟩ : syracuseStep 3848917 = 90209) (by norm_num)
theorem B5131889 : Blo 2279435 5131889 := bstep (se 2 (by rfl) ⟨1924458, by rfl⟩ : syracuseStep 5131889 = 3848917) B3848917
theorem B3421259 : Blo 2279435 3421259 := bstep (se 1 (by rfl) ⟨2565944, by rfl⟩ : syracuseStep 3421259 = 5131889) B5131889
theorem B2280839 : Blo 2279435 2280839 := bstep (se 1 (by rfl) ⟨1710629, by rfl⟩ : syracuseStep 2280839 = 3421259) B3421259
theorem B2565949 : Blo 2279435 2565949 := bbase (se 3 (by rfl) ⟨481115, by rfl⟩ : syracuseStep 2565949 = 962231) (by norm_num)
theorem B3421265 : Blo 2279435 3421265 := bstep (se 2 (by rfl) ⟨1282974, by rfl⟩ : syracuseStep 3421265 = 2565949) B2565949
theorem B2280843 : Blo 2279435 2280843 := bstep (se 1 (by rfl) ⟨1710632, by rfl⟩ : syracuseStep 2280843 = 3421265) B3421265
theorem B7697861 : Blo 2279435 7697861 := bbase (se 4 (by rfl) ⟨721674, by rfl⟩ : syracuseStep 7697861 = 1443349) (by norm_num)
theorem B5131907 : Blo 2279435 5131907 := bstep (se 1 (by rfl) ⟨3848930, by rfl⟩ : syracuseStep 5131907 = 7697861) B7697861
theorem B3421271 : Blo 2279435 3421271 := bstep (se 1 (by rfl) ⟨2565953, by rfl⟩ : syracuseStep 3421271 = 5131907) B5131907
theorem B2280847 : Blo 2279435 2280847 := bstep (se 1 (by rfl) ⟨1710635, by rfl⟩ : syracuseStep 2280847 = 3421271) B3421271
theorem B3421277 : Blo 2279435 3421277 := bbase (se 3 (by rfl) ⟨641489, by rfl⟩ : syracuseStep 3421277 = 1282979) (by norm_num)
theorem B2280851 : Blo 2279435 2280851 := bstep (se 1 (by rfl) ⟨1710638, by rfl⟩ : syracuseStep 2280851 = 3421277) B3421277
theorem B5131925 : Blo 2279435 5131925 := bbase (se 6 (by rfl) ⟨120279, by rfl⟩ : syracuseStep 5131925 = 240559) (by norm_num)
theorem B3421283 : Blo 2279435 3421283 := bstep (se 1 (by rfl) ⟨2565962, by rfl⟩ : syracuseStep 3421283 = 5131925) B5131925
theorem B2280855 : Blo 2279435 2280855 := bstep (se 1 (by rfl) ⟨1710641, by rfl⟩ : syracuseStep 2280855 = 3421283) B3421283
theorem B2435665 : Blo 2279435 2435665 := bbase (se 2 (by rfl) ⟨913374, by rfl⟩ : syracuseStep 2435665 = 1826749) (by norm_num)
theorem B3247553 : Blo 2279435 3247553 := bstep (se 2 (by rfl) ⟨1217832, by rfl⟩ : syracuseStep 3247553 = 2435665) B2435665
theorem B8660141 : Blo 2279435 8660141 := bstep (se 3 (by rfl) ⟨1623776, by rfl⟩ : syracuseStep 8660141 = 3247553) B3247553
theorem B5773427 : Blo 2279435 5773427 := bstep (se 1 (by rfl) ⟨4330070, by rfl⟩ : syracuseStep 5773427 = 8660141) B8660141
theorem B3848951 : Blo 2279435 3848951 := bstep (se 1 (by rfl) ⟨2886713, by rfl⟩ : syracuseStep 3848951 = 5773427) B5773427
theorem B2565967 : Blo 2279435 2565967 := bstep (se 1 (by rfl) ⟨1924475, by rfl⟩ : syracuseStep 2565967 = 3848951) B3848951
theorem B3421289 : Blo 2279435 3421289 := bstep (se 2 (by rfl) ⟨1282983, by rfl⟩ : syracuseStep 3421289 = 2565967) B2565967
theorem B2280859 : Blo 2279435 2280859 := bstep (se 1 (by rfl) ⟨1710644, by rfl⟩ : syracuseStep 2280859 = 3421289) B3421289
theorem B16665077 : Blo 2279435 16665077 := bbase (se 5 (by rfl) ⟨781175, by rfl⟩ : syracuseStep 16665077 = 1562351) (by norm_num)
theorem B11110051 : Blo 2279435 11110051 := bstep (se 1 (by rfl) ⟨8332538, by rfl⟩ : syracuseStep 11110051 = 16665077) B16665077
theorem B14813401 : Blo 2279435 14813401 := bstep (se 2 (by rfl) ⟨5555025, by rfl⟩ : syracuseStep 14813401 = 11110051) B11110051
theorem B19751201 : Blo 2279435 19751201 := bstep (se 2 (by rfl) ⟨7406700, by rfl⟩ : syracuseStep 19751201 = 14813401) B14813401
theorem B13167467 : Blo 2279435 13167467 := bstep (se 1 (by rfl) ⟨9875600, by rfl⟩ : syracuseStep 13167467 = 19751201) B19751201
theorem B8778311 : Blo 2279435 8778311 := bstep (se 1 (by rfl) ⟨6583733, by rfl⟩ : syracuseStep 8778311 = 13167467) B13167467
theorem B5852207 : Blo 2279435 5852207 := bstep (se 1 (by rfl) ⟨4389155, by rfl⟩ : syracuseStep 5852207 = 8778311) B8778311
theorem B15605885 : Blo 2279435 15605885 := bstep (se 3 (by rfl) ⟨2926103, by rfl⟩ : syracuseStep 15605885 = 5852207) B5852207
theorem B41615693 : Blo 2279435 41615693 := bstep (se 3 (by rfl) ⟨7802942, by rfl⟩ : syracuseStep 41615693 = 15605885) B15605885
theorem B27743795 : Blo 2279435 27743795 := bstep (se 1 (by rfl) ⟨20807846, by rfl⟩ : syracuseStep 27743795 = 41615693) B41615693
theorem B18495863 : Blo 2279435 18495863 := bstep (se 1 (by rfl) ⟨13871897, by rfl⟩ : syracuseStep 18495863 = 27743795) B27743795
theorem B12330575 : Blo 2279435 12330575 := bstep (se 1 (by rfl) ⟨9247931, by rfl⟩ : syracuseStep 12330575 = 18495863) B18495863
theorem B8220383 : Blo 2279435 8220383 := bstep (se 1 (by rfl) ⟨6165287, by rfl⟩ : syracuseStep 8220383 = 12330575) B12330575
theorem B5480255 : Blo 2279435 5480255 := bstep (se 1 (by rfl) ⟨4110191, by rfl⟩ : syracuseStep 5480255 = 8220383) B8220383
theorem B14614013 : Blo 2279435 14614013 := bstep (se 3 (by rfl) ⟨2740127, by rfl⟩ : syracuseStep 14614013 = 5480255) B5480255
theorem B9742675 : Blo 2279435 9742675 := bstep (se 1 (by rfl) ⟨7307006, by rfl⟩ : syracuseStep 9742675 = 14614013) B14614013
theorem B12990233 : Blo 2279435 12990233 := bstep (se 2 (by rfl) ⟨4871337, by rfl⟩ : syracuseStep 12990233 = 9742675) B9742675
theorem B8660155 : Blo 2279435 8660155 := bstep (se 1 (by rfl) ⟨6495116, by rfl⟩ : syracuseStep 8660155 = 12990233) B12990233
theorem B11546873 : Blo 2279435 11546873 := bstep (se 2 (by rfl) ⟨4330077, by rfl⟩ : syracuseStep 11546873 = 8660155) B8660155
theorem B7697915 : Blo 2279435 7697915 := bstep (se 1 (by rfl) ⟨5773436, by rfl⟩ : syracuseStep 7697915 = 11546873) B11546873
theorem B5131943 : Blo 2279435 5131943 := bstep (se 1 (by rfl) ⟨3848957, by rfl⟩ : syracuseStep 5131943 = 7697915) B7697915
theorem B3421295 : Blo 2279435 3421295 := bstep (se 1 (by rfl) ⟨2565971, by rfl⟩ : syracuseStep 3421295 = 5131943) B5131943
theorem B2280863 : Blo 2279435 2280863 := bstep (se 1 (by rfl) ⟨1710647, by rfl⟩ : syracuseStep 2280863 = 3421295) B3421295
theorem B3421301 : Blo 2279435 3421301 := bbase (se 5 (by rfl) ⟨160373, by rfl⟩ : syracuseStep 3421301 = 320747) (by norm_num)
theorem B2280867 : Blo 2279435 2280867 := bstep (se 1 (by rfl) ⟨1710650, by rfl⟩ : syracuseStep 2280867 = 3421301) B3421301
theorem B4330093 : Blo 2279435 4330093 := bbase (se 3 (by rfl) ⟨811892, by rfl⟩ : syracuseStep 4330093 = 1623785) (by norm_num)
theorem B5773457 : Blo 2279435 5773457 := bstep (se 2 (by rfl) ⟨2165046, by rfl⟩ : syracuseStep 5773457 = 4330093) B4330093
theorem B3848971 : Blo 2279435 3848971 := bstep (se 1 (by rfl) ⟨2886728, by rfl⟩ : syracuseStep 3848971 = 5773457) B5773457
theorem B5131961 : Blo 2279435 5131961 := bstep (se 2 (by rfl) ⟨1924485, by rfl⟩ : syracuseStep 5131961 = 3848971) B3848971
theorem B3421307 : Blo 2279435 3421307 := bstep (se 1 (by rfl) ⟨2565980, by rfl⟩ : syracuseStep 3421307 = 5131961) B5131961
theorem B2280871 : Blo 2279435 2280871 := bstep (se 1 (by rfl) ⟨1710653, by rfl⟩ : syracuseStep 2280871 = 3421307) B3421307
theorem B2565985 : Blo 2279435 2565985 := bbase (se 2 (by rfl) ⟨962244, by rfl⟩ : syracuseStep 2565985 = 1924489) (by norm_num)
theorem B3421313 : Blo 2279435 3421313 := bstep (se 2 (by rfl) ⟨1282992, by rfl⟩ : syracuseStep 3421313 = 2565985) B2565985
theorem B2280875 : Blo 2279435 2280875 := bstep (se 1 (by rfl) ⟨1710656, by rfl⟩ : syracuseStep 2280875 = 3421313) B3421313
theorem B5773477 : Blo 2279435 5773477 := bbase (se 4 (by rfl) ⟨541263, by rfl⟩ : syracuseStep 5773477 = 1082527) (by norm_num)
theorem B7697969 : Blo 2279435 7697969 := bstep (se 2 (by rfl) ⟨2886738, by rfl⟩ : syracuseStep 7697969 = 5773477) B5773477
theorem B5131979 : Blo 2279435 5131979 := bstep (se 1 (by rfl) ⟨3848984, by rfl⟩ : syracuseStep 5131979 = 7697969) B7697969
theorem B3421319 : Blo 2279435 3421319 := bstep (se 1 (by rfl) ⟨2565989, by rfl⟩ : syracuseStep 3421319 = 5131979) B5131979
theorem B2280879 : Blo 2279435 2280879 := bstep (se 1 (by rfl) ⟨1710659, by rfl⟩ : syracuseStep 2280879 = 3421319) B3421319
theorem B3421325 : Blo 2279435 3421325 := bbase (se 3 (by rfl) ⟨641498, by rfl⟩ : syracuseStep 3421325 = 1282997) (by norm_num)
theorem B2280883 : Blo 2279435 2280883 := bstep (se 1 (by rfl) ⟨1710662, by rfl⟩ : syracuseStep 2280883 = 3421325) B3421325
theorem B5131997 : Blo 2279435 5131997 := bbase (se 3 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 5131997 = 1924499) (by norm_num)
theorem B3421331 : Blo 2279435 3421331 := bstep (se 1 (by rfl) ⟨2565998, by rfl⟩ : syracuseStep 3421331 = 5131997) B5131997
theorem B2280887 : Blo 2279435 2280887 := bstep (se 1 (by rfl) ⟨1710665, by rfl⟩ : syracuseStep 2280887 = 3421331) B3421331
theorem B3849005 : Blo 2279435 3849005 := bbase (se 3 (by rfl) ⟨721688, by rfl⟩ : syracuseStep 3849005 = 1443377) (by norm_num)
theorem B2566003 : Blo 2279435 2566003 := bstep (se 1 (by rfl) ⟨1924502, by rfl⟩ : syracuseStep 2566003 = 3849005) B3849005
theorem B3421337 : Blo 2279435 3421337 := bstep (se 2 (by rfl) ⟨1283001, by rfl⟩ : syracuseStep 3421337 = 2566003) B2566003
theorem B2280891 : Blo 2279435 2280891 := bstep (se 1 (by rfl) ⟨1710668, by rfl⟩ : syracuseStep 2280891 = 3421337) B3421337
theorem B2926145 : Blo 2279435 2926145 := bbase (se 2 (by rfl) ⟨1097304, by rfl⟩ : syracuseStep 2926145 = 2194609) (by norm_num)
theorem B7803053 : Blo 2279435 7803053 := bstep (se 3 (by rfl) ⟨1463072, by rfl⟩ : syracuseStep 7803053 = 2926145) B2926145
theorem B5202035 : Blo 2279435 5202035 := bstep (se 1 (by rfl) ⟨3901526, by rfl⟩ : syracuseStep 5202035 = 7803053) B7803053
theorem B3468023 : Blo 2279435 3468023 := bstep (se 1 (by rfl) ⟨2601017, by rfl⟩ : syracuseStep 3468023 = 5202035) B5202035
theorem B2312015 : Blo 2279435 2312015 := bstep (se 1 (by rfl) ⟨1734011, by rfl⟩ : syracuseStep 2312015 = 3468023) B3468023
theorem B24661493 : Blo 2279435 24661493 := bstep (se 5 (by rfl) ⟨1156007, by rfl⟩ : syracuseStep 24661493 = 2312015) B2312015
theorem B16440995 : Blo 2279435 16440995 := bstep (se 1 (by rfl) ⟨12330746, by rfl⟩ : syracuseStep 16440995 = 24661493) B24661493
theorem B43842653 : Blo 2279435 43842653 := bstep (se 3 (by rfl) ⟨8220497, by rfl⟩ : syracuseStep 43842653 = 16440995) B16440995
theorem B29228435 : Blo 2279435 29228435 := bstep (se 1 (by rfl) ⟨21921326, by rfl⟩ : syracuseStep 29228435 = 43842653) B43842653
theorem B19485623 : Blo 2279435 19485623 := bstep (se 1 (by rfl) ⟨14614217, by rfl⟩ : syracuseStep 19485623 = 29228435) B29228435
theorem B12990415 : Blo 2279435 12990415 := bstep (se 1 (by rfl) ⟨9742811, by rfl⟩ : syracuseStep 12990415 = 19485623) B19485623
theorem B17320553 : Blo 2279435 17320553 := bstep (se 2 (by rfl) ⟨6495207, by rfl⟩ : syracuseStep 17320553 = 12990415) B12990415
theorem B11547035 : Blo 2279435 11547035 := bstep (se 1 (by rfl) ⟨8660276, by rfl⟩ : syracuseStep 11547035 = 17320553) B17320553
theorem B7698023 : Blo 2279435 7698023 := bstep (se 1 (by rfl) ⟨5773517, by rfl⟩ : syracuseStep 7698023 = 11547035) B11547035
theorem B5132015 : Blo 2279435 5132015 := bstep (se 1 (by rfl) ⟨3849011, by rfl⟩ : syracuseStep 5132015 = 7698023) B7698023
theorem B3421343 : Blo 2279435 3421343 := bstep (se 1 (by rfl) ⟨2566007, by rfl⟩ : syracuseStep 3421343 = 5132015) B5132015
theorem B2280895 : Blo 2279435 2280895 := bstep (se 1 (by rfl) ⟨1710671, by rfl⟩ : syracuseStep 2280895 = 3421343) B3421343
theorem B3421349 : Blo 2279435 3421349 := bbase (se 4 (by rfl) ⟨320751, by rfl⟩ : syracuseStep 3421349 = 641503) (by norm_num)
theorem B2280899 : Blo 2279435 2280899 := bstep (se 1 (by rfl) ⟨1710674, by rfl⟩ : syracuseStep 2280899 = 3421349) B3421349
theorem B2886769 : Blo 2279435 2886769 := bbase (se 2 (by rfl) ⟨1082538, by rfl⟩ : syracuseStep 2886769 = 2165077) (by norm_num)
theorem B3849025 : Blo 2279435 3849025 := bstep (se 2 (by rfl) ⟨1443384, by rfl⟩ : syracuseStep 3849025 = 2886769) B2886769
theorem B5132033 : Blo 2279435 5132033 := bstep (se 2 (by rfl) ⟨1924512, by rfl⟩ : syracuseStep 5132033 = 3849025) B3849025
theorem B3421355 : Blo 2279435 3421355 := bstep (se 1 (by rfl) ⟨2566016, by rfl⟩ : syracuseStep 3421355 = 5132033) B5132033
theorem B2280903 : Blo 2279435 2280903 := bstep (se 1 (by rfl) ⟨1710677, by rfl⟩ : syracuseStep 2280903 = 3421355) B3421355
theorem B2566021 : Blo 2279435 2566021 := bbase (se 4 (by rfl) ⟨240564, by rfl⟩ : syracuseStep 2566021 = 481129) (by norm_num)
theorem B3421361 : Blo 2279435 3421361 := bstep (se 2 (by rfl) ⟨1283010, by rfl⟩ : syracuseStep 3421361 = 2566021) B2566021
theorem B2280907 : Blo 2279435 2280907 := bstep (se 1 (by rfl) ⟨1710680, by rfl⟩ : syracuseStep 2280907 = 3421361) B3421361
theorem B3653581 : Blo 2279435 3653581 := bbase (se 3 (by rfl) ⟨685046, by rfl⟩ : syracuseStep 3653581 = 1370093) (by norm_num)
theorem B4871441 : Blo 2279435 4871441 := bstep (se 2 (by rfl) ⟨1826790, by rfl⟩ : syracuseStep 4871441 = 3653581) B3653581
theorem B3247627 : Blo 2279435 3247627 := bstep (se 1 (by rfl) ⟨2435720, by rfl⟩ : syracuseStep 3247627 = 4871441) B4871441
theorem B4330169 : Blo 2279435 4330169 := bstep (se 2 (by rfl) ⟨1623813, by rfl⟩ : syracuseStep 4330169 = 3247627) B3247627
theorem B2886779 : Blo 2279435 2886779 := bstep (se 1 (by rfl) ⟨2165084, by rfl⟩ : syracuseStep 2886779 = 4330169) B4330169
theorem B7698077 : Blo 2279435 7698077 := bstep (se 3 (by rfl) ⟨1443389, by rfl⟩ : syracuseStep 7698077 = 2886779) B2886779
theorem B5132051 : Blo 2279435 5132051 := bstep (se 1 (by rfl) ⟨3849038, by rfl⟩ : syracuseStep 5132051 = 7698077) B7698077
theorem B3421367 : Blo 2279435 3421367 := bstep (se 1 (by rfl) ⟨2566025, by rfl⟩ : syracuseStep 3421367 = 5132051) B5132051
theorem B2280911 : Blo 2279435 2280911 := bstep (se 1 (by rfl) ⟨1710683, by rfl⟩ : syracuseStep 2280911 = 3421367) B3421367
theorem B3421373 : Blo 2279435 3421373 := bbase (se 3 (by rfl) ⟨641507, by rfl⟩ : syracuseStep 3421373 = 1283015) (by norm_num)
theorem B2280915 : Blo 2279435 2280915 := bstep (se 1 (by rfl) ⟨1710686, by rfl⟩ : syracuseStep 2280915 = 3421373) B3421373
theorem B5132069 : Blo 2279435 5132069 := bbase (se 4 (by rfl) ⟨481131, by rfl⟩ : syracuseStep 5132069 = 962263) (by norm_num)
theorem B3421379 : Blo 2279435 3421379 := bstep (se 1 (by rfl) ⟨2566034, by rfl⟩ : syracuseStep 3421379 = 5132069) B5132069
theorem B2280919 : Blo 2279435 2280919 := bstep (se 1 (by rfl) ⟨1710689, by rfl⟩ : syracuseStep 2280919 = 3421379) B3421379
theorem B5773589 : Blo 2279435 5773589 := bbase (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) (by norm_num)
theorem B3849059 : Blo 2279435 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B2566039 : Blo 2279435 2566039 := bstep (se 1 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 2566039 = 3849059) B3849059
theorem B3421385 : Blo 2279435 3421385 := bstep (se 2 (by rfl) ⟨1283019, by rfl⟩ : syracuseStep 3421385 = 2566039) B2566039
theorem B2280923 : Blo 2279435 2280923 := bstep (se 1 (by rfl) ⟨1710692, by rfl⟩ : syracuseStep 2280923 = 3421385) B3421385
theorem B9742949 : Blo 2279435 9742949 := bbase (se 4 (by rfl) ⟨913401, by rfl⟩ : syracuseStep 9742949 = 1826803) (by norm_num)
theorem B6495299 : Blo 2279435 6495299 := bstep (se 1 (by rfl) ⟨4871474, by rfl⟩ : syracuseStep 6495299 = 9742949) B9742949
theorem B4330199 : Blo 2279435 4330199 := bstep (se 1 (by rfl) ⟨3247649, by rfl⟩ : syracuseStep 4330199 = 6495299) B6495299
theorem B11547197 : Blo 2279435 11547197 := bstep (se 3 (by rfl) ⟨2165099, by rfl⟩ : syracuseStep 11547197 = 4330199) B4330199
theorem B7698131 : Blo 2279435 7698131 := bstep (se 1 (by rfl) ⟨5773598, by rfl⟩ : syracuseStep 7698131 = 11547197) B11547197
theorem B5132087 : Blo 2279435 5132087 := bstep (se 1 (by rfl) ⟨3849065, by rfl⟩ : syracuseStep 5132087 = 7698131) B7698131
theorem B3421391 : Blo 2279435 3421391 := bstep (se 1 (by rfl) ⟨2566043, by rfl⟩ : syracuseStep 3421391 = 5132087) B5132087
theorem B2280927 : Blo 2279435 2280927 := bstep (se 1 (by rfl) ⟨1710695, by rfl⟩ : syracuseStep 2280927 = 3421391) B3421391
theorem B3421397 : Blo 2279435 3421397 := bbase (se 7 (by rfl) ⟨40094, by rfl⟩ : syracuseStep 3421397 = 80189) (by norm_num)
theorem B2280931 : Blo 2279435 2280931 := bstep (se 1 (by rfl) ⟨1710698, by rfl⟩ : syracuseStep 2280931 = 3421397) B3421397
theorem B3247661 : Blo 2279435 3247661 := bbase (se 3 (by rfl) ⟨608936, by rfl⟩ : syracuseStep 3247661 = 1217873) (by norm_num)
theorem B8660429 : Blo 2279435 8660429 := bstep (se 3 (by rfl) ⟨1623830, by rfl⟩ : syracuseStep 8660429 = 3247661) B3247661
theorem B5773619 : Blo 2279435 5773619 := bstep (se 1 (by rfl) ⟨4330214, by rfl⟩ : syracuseStep 5773619 = 8660429) B8660429
theorem B3849079 : Blo 2279435 3849079 := bstep (se 1 (by rfl) ⟨2886809, by rfl⟩ : syracuseStep 3849079 = 5773619) B5773619
theorem B5132105 : Blo 2279435 5132105 := bstep (se 2 (by rfl) ⟨1924539, by rfl⟩ : syracuseStep 5132105 = 3849079) B3849079
theorem B3421403 : Blo 2279435 3421403 := bstep (se 1 (by rfl) ⟨2566052, by rfl⟩ : syracuseStep 3421403 = 5132105) B5132105
theorem B2280935 : Blo 2279435 2280935 := bstep (se 1 (by rfl) ⟨1710701, by rfl⟩ : syracuseStep 2280935 = 3421403) B3421403
theorem B2566057 : Blo 2279435 2566057 := bbase (se 2 (by rfl) ⟨962271, by rfl⟩ : syracuseStep 2566057 = 1924543) (by norm_num)
theorem B3421409 : Blo 2279435 3421409 := bstep (se 2 (by rfl) ⟨1283028, by rfl⟩ : syracuseStep 3421409 = 2566057) B2566057
theorem B2280939 : Blo 2279435 2280939 := bstep (se 1 (by rfl) ⟨1710704, by rfl⟩ : syracuseStep 2280939 = 3421409) B3421409
theorem B12026389 : Blo 2279435 12026389 := bbase (se 6 (by rfl) ⟨281868, by rfl⟩ : syracuseStep 12026389 = 563737) (by norm_num)
theorem B16035185 : Blo 2279435 16035185 := bstep (se 2 (by rfl) ⟨6013194, by rfl⟩ : syracuseStep 16035185 = 12026389) B12026389
theorem B42760493 : Blo 2279435 42760493 := bstep (se 3 (by rfl) ⟨8017592, by rfl⟩ : syracuseStep 42760493 = 16035185) B16035185
theorem B28506995 : Blo 2279435 28506995 := bstep (se 1 (by rfl) ⟨21380246, by rfl⟩ : syracuseStep 28506995 = 42760493) B42760493
theorem B19004663 : Blo 2279435 19004663 := bstep (se 1 (by rfl) ⟨14253497, by rfl⟩ : syracuseStep 19004663 = 28506995) B28506995
theorem B50679101 : Blo 2279435 50679101 := bstep (se 3 (by rfl) ⟨9502331, by rfl⟩ : syracuseStep 50679101 = 19004663) B19004663
theorem B33786067 : Blo 2279435 33786067 := bstep (se 1 (by rfl) ⟨25339550, by rfl⟩ : syracuseStep 33786067 = 50679101) B50679101
theorem B45048089 : Blo 2279435 45048089 := bstep (se 2 (by rfl) ⟨16893033, by rfl⟩ : syracuseStep 45048089 = 33786067) B33786067
theorem B30032059 : Blo 2279435 30032059 := bstep (se 1 (by rfl) ⟨22524044, by rfl⟩ : syracuseStep 30032059 = 45048089) B45048089
theorem B40042745 : Blo 2279435 40042745 := bstep (se 2 (by rfl) ⟨15016029, by rfl⟩ : syracuseStep 40042745 = 30032059) B30032059
theorem B26695163 : Blo 2279435 26695163 := bstep (se 1 (by rfl) ⟨20021372, by rfl⟩ : syracuseStep 26695163 = 40042745) B40042745
theorem B17796775 : Blo 2279435 17796775 := bstep (se 1 (by rfl) ⟨13347581, by rfl⟩ : syracuseStep 17796775 = 26695163) B26695163
theorem B23729033 : Blo 2279435 23729033 := bstep (se 2 (by rfl) ⟨8898387, by rfl⟩ : syracuseStep 23729033 = 17796775) B17796775
theorem B15819355 : Blo 2279435 15819355 := bstep (se 1 (by rfl) ⟨11864516, by rfl⟩ : syracuseStep 15819355 = 23729033) B23729033
theorem B21092473 : Blo 2279435 21092473 := bstep (se 2 (by rfl) ⟨7909677, by rfl⟩ : syracuseStep 21092473 = 15819355) B15819355
theorem B112493189 : Blo 2279435 112493189 := bstep (se 4 (by rfl) ⟨10546236, by rfl⟩ : syracuseStep 112493189 = 21092473) B21092473
theorem B299981837 : Blo 2279435 299981837 := bstep (se 3 (by rfl) ⟨56246594, by rfl⟩ : syracuseStep 299981837 = 112493189) B112493189
theorem B799951565 : Blo 2279435 799951565 := bstep (se 3 (by rfl) ⟨149990918, by rfl⟩ : syracuseStep 799951565 = 299981837) B299981837
theorem B2133204173 : Blo 2279435 2133204173 := bstep (se 3 (by rfl) ⟨399975782, by rfl⟩ : syracuseStep 2133204173 = 799951565) B799951565
theorem B1422136115 : Blo 2279435 1422136115 := bstep (se 1 (by rfl) ⟨1066602086, by rfl⟩ : syracuseStep 1422136115 = 2133204173) B2133204173
theorem B948090743 : Blo 2279435 948090743 := bstep (se 1 (by rfl) ⟨711068057, by rfl⟩ : syracuseStep 948090743 = 1422136115) B1422136115
theorem B632060495 : Blo 2279435 632060495 := bstep (se 1 (by rfl) ⟨474045371, by rfl⟩ : syracuseStep 632060495 = 948090743) B948090743
theorem B421373663 : Blo 2279435 421373663 := bstep (se 1 (by rfl) ⟨316030247, by rfl⟩ : syracuseStep 421373663 = 632060495) B632060495
theorem B280915775 : Blo 2279435 280915775 := bstep (se 1 (by rfl) ⟨210686831, by rfl⟩ : syracuseStep 280915775 = 421373663) B421373663
theorem B187277183 : Blo 2279435 187277183 := bstep (se 1 (by rfl) ⟨140457887, by rfl⟩ : syracuseStep 187277183 = 280915775) B280915775
theorem B124851455 : Blo 2279435 124851455 := bstep (se 1 (by rfl) ⟨93638591, by rfl⟩ : syracuseStep 124851455 = 187277183) B187277183
theorem B83234303 : Blo 2279435 83234303 := bstep (se 1 (by rfl) ⟨62425727, by rfl⟩ : syracuseStep 83234303 = 124851455) B124851455
theorem B55489535 : Blo 2279435 55489535 := bstep (se 1 (by rfl) ⟨41617151, by rfl⟩ : syracuseStep 55489535 = 83234303) B83234303
theorem B36993023 : Blo 2279435 36993023 := bstep (se 1 (by rfl) ⟨27744767, by rfl⟩ : syracuseStep 36993023 = 55489535) B55489535
theorem B24662015 : Blo 2279435 24662015 := bstep (se 1 (by rfl) ⟨18496511, by rfl⟩ : syracuseStep 24662015 = 36993023) B36993023
theorem B16441343 : Blo 2279435 16441343 := bstep (se 1 (by rfl) ⟨12331007, by rfl⟩ : syracuseStep 16441343 = 24662015) B24662015
theorem B10960895 : Blo 2279435 10960895 := bstep (se 1 (by rfl) ⟨8220671, by rfl⟩ : syracuseStep 10960895 = 16441343) B16441343
theorem B7307263 : Blo 2279435 7307263 := bstep (se 1 (by rfl) ⟨5480447, by rfl⟩ : syracuseStep 7307263 = 10960895) B10960895
theorem B9743017 : Blo 2279435 9743017 := bstep (se 2 (by rfl) ⟨3653631, by rfl⟩ : syracuseStep 9743017 = 7307263) B7307263
theorem B12990689 : Blo 2279435 12990689 := bstep (se 2 (by rfl) ⟨4871508, by rfl⟩ : syracuseStep 12990689 = 9743017) B9743017
theorem B8660459 : Blo 2279435 8660459 := bstep (se 1 (by rfl) ⟨6495344, by rfl⟩ : syracuseStep 8660459 = 12990689) B12990689
theorem B5773639 : Blo 2279435 5773639 := bstep (se 1 (by rfl) ⟨4330229, by rfl⟩ : syracuseStep 5773639 = 8660459) B8660459
theorem B7698185 : Blo 2279435 7698185 := bstep (se 2 (by rfl) ⟨2886819, by rfl⟩ : syracuseStep 7698185 = 5773639) B5773639
theorem B5132123 : Blo 2279435 5132123 := bstep (se 1 (by rfl) ⟨3849092, by rfl⟩ : syracuseStep 5132123 = 7698185) B7698185
theorem B3421415 : Blo 2279435 3421415 := bstep (se 1 (by rfl) ⟨2566061, by rfl⟩ : syracuseStep 3421415 = 5132123) B5132123
theorem B2280943 : Blo 2279435 2280943 := bstep (se 1 (by rfl) ⟨1710707, by rfl⟩ : syracuseStep 2280943 = 3421415) B3421415
theorem B3421421 : Blo 2279435 3421421 := bbase (se 3 (by rfl) ⟨641516, by rfl⟩ : syracuseStep 3421421 = 1283033) (by norm_num)
theorem B2280947 : Blo 2279435 2280947 := bstep (se 1 (by rfl) ⟨1710710, by rfl⟩ : syracuseStep 2280947 = 3421421) B3421421
theorem B5132141 : Blo 2279435 5132141 := bbase (se 3 (by rfl) ⟨962276, by rfl⟩ : syracuseStep 5132141 = 1924553) (by norm_num)
theorem B3421427 : Blo 2279435 3421427 := bstep (se 1 (by rfl) ⟨2566070, by rfl⟩ : syracuseStep 3421427 = 5132141) B5132141
theorem B2280951 : Blo 2279435 2280951 := bstep (se 1 (by rfl) ⟨1710713, by rfl⟩ : syracuseStep 2280951 = 3421427) B3421427
theorem B4330253 : Blo 2279435 4330253 := bbase (se 3 (by rfl) ⟨811922, by rfl⟩ : syracuseStep 4330253 = 1623845) (by norm_num)
theorem B2886835 : Blo 2279435 2886835 := bstep (se 1 (by rfl) ⟨2165126, by rfl⟩ : syracuseStep 2886835 = 4330253) B4330253
theorem B3849113 : Blo 2279435 3849113 := bstep (se 2 (by rfl) ⟨1443417, by rfl⟩ : syracuseStep 3849113 = 2886835) B2886835
theorem B2566075 : Blo 2279435 2566075 := bstep (se 1 (by rfl) ⟨1924556, by rfl⟩ : syracuseStep 2566075 = 3849113) B3849113
theorem B3421433 : Blo 2279435 3421433 := bstep (se 2 (by rfl) ⟨1283037, by rfl⟩ : syracuseStep 3421433 = 2566075) B2566075
theorem B2280955 : Blo 2279435 2280955 := bstep (se 1 (by rfl) ⟨1710716, by rfl⟩ : syracuseStep 2280955 = 3421433) B3421433
theorem B21921941 : Blo 2279435 21921941 := bbase (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) (by norm_num)
theorem B58458509 : Blo 2279435 58458509 := bstep (se 3 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 58458509 = 21921941) B21921941
theorem B38972339 : Blo 2279435 38972339 := bstep (se 1 (by rfl) ⟨29229254, by rfl⟩ : syracuseStep 38972339 = 58458509) B58458509
theorem B25981559 : Blo 2279435 25981559 := bstep (se 1 (by rfl) ⟨19486169, by rfl⟩ : syracuseStep 25981559 = 38972339) B38972339
theorem B17321039 : Blo 2279435 17321039 := bstep (se 1 (by rfl) ⟨12990779, by rfl⟩ : syracuseStep 17321039 = 25981559) B25981559
theorem B11547359 : Blo 2279435 11547359 := bstep (se 1 (by rfl) ⟨8660519, by rfl⟩ : syracuseStep 11547359 = 17321039) B17321039
theorem B7698239 : Blo 2279435 7698239 := bstep (se 1 (by rfl) ⟨5773679, by rfl⟩ : syracuseStep 7698239 = 11547359) B11547359
theorem B5132159 : Blo 2279435 5132159 := bstep (se 1 (by rfl) ⟨3849119, by rfl⟩ : syracuseStep 5132159 = 7698239) B7698239
theorem B3421439 : Blo 2279435 3421439 := bstep (se 1 (by rfl) ⟨2566079, by rfl⟩ : syracuseStep 3421439 = 5132159) B5132159
theorem B2280959 : Blo 2279435 2280959 := bstep (se 1 (by rfl) ⟨1710719, by rfl⟩ : syracuseStep 2280959 = 3421439) B3421439
theorem B3421445 : Blo 2279435 3421445 := bbase (se 4 (by rfl) ⟨320760, by rfl⟩ : syracuseStep 3421445 = 641521) (by norm_num)
theorem B2280963 : Blo 2279435 2280963 := bstep (se 1 (by rfl) ⟨1710722, by rfl⟩ : syracuseStep 2280963 = 3421445) B3421445
theorem B3849133 : Blo 2279435 3849133 := bbase (se 3 (by rfl) ⟨721712, by rfl⟩ : syracuseStep 3849133 = 1443425) (by norm_num)
theorem B5132177 : Blo 2279435 5132177 := bstep (se 2 (by rfl) ⟨1924566, by rfl⟩ : syracuseStep 5132177 = 3849133) B3849133
theorem B3421451 : Blo 2279435 3421451 := bstep (se 1 (by rfl) ⟨2566088, by rfl⟩ : syracuseStep 3421451 = 5132177) B5132177
theorem B2280967 : Blo 2279435 2280967 := bstep (se 1 (by rfl) ⟨1710725, by rfl⟩ : syracuseStep 2280967 = 3421451) B3421451
theorem B2566093 : Blo 2279435 2566093 := bbase (se 3 (by rfl) ⟨481142, by rfl⟩ : syracuseStep 2566093 = 962285) (by norm_num)
theorem B3421457 : Blo 2279435 3421457 := bstep (se 2 (by rfl) ⟨1283046, by rfl⟩ : syracuseStep 3421457 = 2566093) B2566093
theorem B2280971 : Blo 2279435 2280971 := bstep (se 1 (by rfl) ⟨1710728, by rfl⟩ : syracuseStep 2280971 = 3421457) B3421457
theorem B7698293 : Blo 2279435 7698293 := bbase (se 5 (by rfl) ⟨360857, by rfl⟩ : syracuseStep 7698293 = 721715) (by norm_num)
theorem B5132195 : Blo 2279435 5132195 := bstep (se 1 (by rfl) ⟨3849146, by rfl⟩ : syracuseStep 5132195 = 7698293) B7698293
theorem B3421463 : Blo 2279435 3421463 := bstep (se 1 (by rfl) ⟨2566097, by rfl⟩ : syracuseStep 3421463 = 5132195) B5132195
theorem B2280975 : Blo 2279435 2280975 := bstep (se 1 (by rfl) ⟨1710731, by rfl⟩ : syracuseStep 2280975 = 3421463) B3421463
theorem B3421469 : Blo 2279435 3421469 := bbase (se 3 (by rfl) ⟨641525, by rfl⟩ : syracuseStep 3421469 = 1283051) (by norm_num)
theorem B2280979 : Blo 2279435 2280979 := bstep (se 1 (by rfl) ⟨1710734, by rfl⟩ : syracuseStep 2280979 = 3421469) B3421469
theorem B5132213 : Blo 2279435 5132213 := bbase (se 5 (by rfl) ⟨240572, by rfl⟩ : syracuseStep 5132213 = 481145) (by norm_num)
theorem B3421475 : Blo 2279435 3421475 := bstep (se 1 (by rfl) ⟨2566106, by rfl⟩ : syracuseStep 3421475 = 5132213) B5132213
theorem B2280983 : Blo 2279435 2280983 := bstep (se 1 (by rfl) ⟨1710737, by rfl⟩ : syracuseStep 2280983 = 3421475) B3421475
theorem B2740277 : Blo 2279435 2740277 := bbase (se 5 (by rfl) ⟨128450, by rfl⟩ : syracuseStep 2740277 = 256901) (by norm_num)
theorem B7307405 : Blo 2279435 7307405 := bstep (se 3 (by rfl) ⟨1370138, by rfl⟩ : syracuseStep 7307405 = 2740277) B2740277
theorem B4871603 : Blo 2279435 4871603 := bstep (se 1 (by rfl) ⟨3653702, by rfl⟩ : syracuseStep 4871603 = 7307405) B7307405
theorem B12990941 : Blo 2279435 12990941 := bstep (se 3 (by rfl) ⟨2435801, by rfl⟩ : syracuseStep 12990941 = 4871603) B4871603
theorem B8660627 : Blo 2279435 8660627 := bstep (se 1 (by rfl) ⟨6495470, by rfl⟩ : syracuseStep 8660627 = 12990941) B12990941
theorem B5773751 : Blo 2279435 5773751 := bstep (se 1 (by rfl) ⟨4330313, by rfl⟩ : syracuseStep 5773751 = 8660627) B8660627
theorem B3849167 : Blo 2279435 3849167 := bstep (se 1 (by rfl) ⟨2886875, by rfl⟩ : syracuseStep 3849167 = 5773751) B5773751
theorem B2566111 : Blo 2279435 2566111 := bstep (se 1 (by rfl) ⟨1924583, by rfl⟩ : syracuseStep 2566111 = 3849167) B3849167
theorem B3421481 : Blo 2279435 3421481 := bstep (se 2 (by rfl) ⟨1283055, by rfl⟩ : syracuseStep 3421481 = 2566111) B2566111
theorem B2280987 : Blo 2279435 2280987 := bstep (se 1 (by rfl) ⟨1710740, by rfl⟩ : syracuseStep 2280987 = 3421481) B3421481
theorem B2312113 : Blo 2279435 2312113 := bbase (se 2 (by rfl) ⟨867042, by rfl⟩ : syracuseStep 2312113 = 1734085) (by norm_num)
theorem B3082817 : Blo 2279435 3082817 := bstep (se 2 (by rfl) ⟨1156056, by rfl⟩ : syracuseStep 3082817 = 2312113) B2312113
theorem B8220845 : Blo 2279435 8220845 := bstep (se 3 (by rfl) ⟨1541408, by rfl⟩ : syracuseStep 8220845 = 3082817) B3082817
theorem B5480563 : Blo 2279435 5480563 := bstep (se 1 (by rfl) ⟨4110422, by rfl⟩ : syracuseStep 5480563 = 8220845) B8220845
theorem B7307417 : Blo 2279435 7307417 := bstep (se 2 (by rfl) ⟨2740281, by rfl⟩ : syracuseStep 7307417 = 5480563) B5480563
theorem B4871611 : Blo 2279435 4871611 := bstep (se 1 (by rfl) ⟨3653708, by rfl⟩ : syracuseStep 4871611 = 7307417) B7307417
theorem B6495481 : Blo 2279435 6495481 := bstep (se 2 (by rfl) ⟨2435805, by rfl⟩ : syracuseStep 6495481 = 4871611) B4871611
theorem B8660641 : Blo 2279435 8660641 := bstep (se 2 (by rfl) ⟨3247740, by rfl⟩ : syracuseStep 8660641 = 6495481) B6495481
theorem B11547521 : Blo 2279435 11547521 := bstep (se 2 (by rfl) ⟨4330320, by rfl⟩ : syracuseStep 11547521 = 8660641) B8660641
theorem B7698347 : Blo 2279435 7698347 := bstep (se 1 (by rfl) ⟨5773760, by rfl⟩ : syracuseStep 7698347 = 11547521) B11547521
theorem B5132231 : Blo 2279435 5132231 := bstep (se 1 (by rfl) ⟨3849173, by rfl⟩ : syracuseStep 5132231 = 7698347) B7698347
theorem B3421487 : Blo 2279435 3421487 := bstep (se 1 (by rfl) ⟨2566115, by rfl⟩ : syracuseStep 3421487 = 5132231) B5132231
theorem B2280991 : Blo 2279435 2280991 := bstep (se 1 (by rfl) ⟨1710743, by rfl⟩ : syracuseStep 2280991 = 3421487) B3421487
theorem B3421493 : Blo 2279435 3421493 := bbase (se 5 (by rfl) ⟨160382, by rfl⟩ : syracuseStep 3421493 = 320765) (by norm_num)
theorem B2280995 : Blo 2279435 2280995 := bstep (se 1 (by rfl) ⟨1710746, by rfl⟩ : syracuseStep 2280995 = 3421493) B3421493
theorem B5773781 : Blo 2279435 5773781 := bbase (se 7 (by rfl) ⟨67661, by rfl⟩ : syracuseStep 5773781 = 135323) (by norm_num)
theorem B3849187 : Blo 2279435 3849187 := bstep (se 1 (by rfl) ⟨2886890, by rfl⟩ : syracuseStep 3849187 = 5773781) B5773781
theorem B5132249 : Blo 2279435 5132249 := bstep (se 2 (by rfl) ⟨1924593, by rfl⟩ : syracuseStep 5132249 = 3849187) B3849187
theorem B3421499 : Blo 2279435 3421499 := bstep (se 1 (by rfl) ⟨2566124, by rfl⟩ : syracuseStep 3421499 = 5132249) B5132249
theorem B2280999 : Blo 2279435 2280999 := bstep (se 1 (by rfl) ⟨1710749, by rfl⟩ : syracuseStep 2280999 = 3421499) B3421499
theorem B2566129 : Blo 2279435 2566129 := bbase (se 2 (by rfl) ⟨962298, by rfl⟩ : syracuseStep 2566129 = 1924597) (by norm_num)
theorem B3421505 : Blo 2279435 3421505 := bstep (se 2 (by rfl) ⟨1283064, by rfl⟩ : syracuseStep 3421505 = 2566129) B2566129
theorem B2281003 : Blo 2279435 2281003 := bstep (se 1 (by rfl) ⟨1710752, by rfl⟩ : syracuseStep 2281003 = 3421505) B3421505
theorem B2312129 : Blo 2279435 2312129 := bbase (se 2 (by rfl) ⟨867048, by rfl⟩ : syracuseStep 2312129 = 1734097) (by norm_num)
theorem B6165677 : Blo 2279435 6165677 := bstep (se 3 (by rfl) ⟨1156064, by rfl⟩ : syracuseStep 6165677 = 2312129) B2312129
theorem B16441805 : Blo 2279435 16441805 := bstep (se 3 (by rfl) ⟨3082838, by rfl⟩ : syracuseStep 16441805 = 6165677) B6165677
theorem B10961203 : Blo 2279435 10961203 := bstep (se 1 (by rfl) ⟨8220902, by rfl⟩ : syracuseStep 10961203 = 16441805) B16441805
theorem B14614937 : Blo 2279435 14614937 := bstep (se 2 (by rfl) ⟨5480601, by rfl⟩ : syracuseStep 14614937 = 10961203) B10961203
theorem B9743291 : Blo 2279435 9743291 := bstep (se 1 (by rfl) ⟨7307468, by rfl⟩ : syracuseStep 9743291 = 14614937) B14614937
theorem B6495527 : Blo 2279435 6495527 := bstep (se 1 (by rfl) ⟨4871645, by rfl⟩ : syracuseStep 6495527 = 9743291) B9743291
theorem B4330351 : Blo 2279435 4330351 := bstep (se 1 (by rfl) ⟨3247763, by rfl⟩ : syracuseStep 4330351 = 6495527) B6495527
theorem B5773801 : Blo 2279435 5773801 := bstep (se 2 (by rfl) ⟨2165175, by rfl⟩ : syracuseStep 5773801 = 4330351) B4330351
theorem B7698401 : Blo 2279435 7698401 := bstep (se 2 (by rfl) ⟨2886900, by rfl⟩ : syracuseStep 7698401 = 5773801) B5773801
theorem B5132267 : Blo 2279435 5132267 := bstep (se 1 (by rfl) ⟨3849200, by rfl⟩ : syracuseStep 5132267 = 7698401) B7698401
theorem B3421511 : Blo 2279435 3421511 := bstep (se 1 (by rfl) ⟨2566133, by rfl⟩ : syracuseStep 3421511 = 5132267) B5132267
theorem B2281007 : Blo 2279435 2281007 := bstep (se 1 (by rfl) ⟨1710755, by rfl⟩ : syracuseStep 2281007 = 3421511) B3421511
theorem B3421517 : Blo 2279435 3421517 := bbase (se 3 (by rfl) ⟨641534, by rfl⟩ : syracuseStep 3421517 = 1283069) (by norm_num)
theorem B2281011 : Blo 2279435 2281011 := bstep (se 1 (by rfl) ⟨1710758, by rfl⟩ : syracuseStep 2281011 = 3421517) B3421517
theorem B5132285 : Blo 2279435 5132285 := bbase (se 3 (by rfl) ⟨962303, by rfl⟩ : syracuseStep 5132285 = 1924607) (by norm_num)
theorem B3421523 : Blo 2279435 3421523 := bstep (se 1 (by rfl) ⟨2566142, by rfl⟩ : syracuseStep 3421523 = 5132285) B5132285
theorem B2281015 : Blo 2279435 2281015 := bstep (se 1 (by rfl) ⟨1710761, by rfl⟩ : syracuseStep 2281015 = 3421523) B3421523
theorem B3849221 : Blo 2279435 3849221 := bbase (se 4 (by rfl) ⟨360864, by rfl⟩ : syracuseStep 3849221 = 721729) (by norm_num)
theorem B2566147 : Blo 2279435 2566147 := bstep (se 1 (by rfl) ⟨1924610, by rfl⟩ : syracuseStep 2566147 = 3849221) B3849221
theorem B3421529 : Blo 2279435 3421529 := bstep (se 2 (by rfl) ⟨1283073, by rfl⟩ : syracuseStep 3421529 = 2566147) B2566147
theorem B2281019 : Blo 2279435 2281019 := bstep (se 1 (by rfl) ⟨1710764, by rfl⟩ : syracuseStep 2281019 = 3421529) B3421529
theorem B17321525 : Blo 2279435 17321525 := bbase (se 5 (by rfl) ⟨811946, by rfl⟩ : syracuseStep 17321525 = 1623893) (by norm_num)
theorem B11547683 : Blo 2279435 11547683 := bstep (se 1 (by rfl) ⟨8660762, by rfl⟩ : syracuseStep 11547683 = 17321525) B17321525
theorem B7698455 : Blo 2279435 7698455 := bstep (se 1 (by rfl) ⟨5773841, by rfl⟩ : syracuseStep 7698455 = 11547683) B11547683
theorem B5132303 : Blo 2279435 5132303 := bstep (se 1 (by rfl) ⟨3849227, by rfl⟩ : syracuseStep 5132303 = 7698455) B7698455
theorem B3421535 : Blo 2279435 3421535 := bstep (se 1 (by rfl) ⟨2566151, by rfl⟩ : syracuseStep 3421535 = 5132303) B5132303
theorem B2281023 : Blo 2279435 2281023 := bstep (se 1 (by rfl) ⟨1710767, by rfl⟩ : syracuseStep 2281023 = 3421535) B3421535
theorem B3421541 : Blo 2279435 3421541 := bbase (se 4 (by rfl) ⟨320769, by rfl⟩ : syracuseStep 3421541 = 641539) (by norm_num)
theorem B2281027 : Blo 2279435 2281027 := bstep (se 1 (by rfl) ⟨1710770, by rfl⟩ : syracuseStep 2281027 = 3421541) B3421541
theorem B4330397 : Blo 2279435 4330397 := bbase (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) (by norm_num)
theorem B2886931 : Blo 2279435 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B3849241 : Blo 2279435 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B5132321 : Blo 2279435 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B3421547 : Blo 2279435 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B2281031 : Blo 2279435 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B2566165 : Blo 2279435 2566165 := bbase (se 6 (by rfl) ⟨60144, by rfl⟩ : syracuseStep 2566165 = 120289) (by norm_num)
theorem B3421553 : Blo 2279435 3421553 := bstep (se 2 (by rfl) ⟨1283082, by rfl⟩ : syracuseStep 3421553 = 2566165) B2566165
theorem B2281035 : Blo 2279435 2281035 := bstep (se 1 (by rfl) ⟨1710776, by rfl⟩ : syracuseStep 2281035 = 3421553) B3421553
theorem B2886941 : Blo 2279435 2886941 := bbase (se 3 (by rfl) ⟨541301, by rfl⟩ : syracuseStep 2886941 = 1082603) (by norm_num)
theorem B7698509 : Blo 2279435 7698509 := bstep (se 3 (by rfl) ⟨1443470, by rfl⟩ : syracuseStep 7698509 = 2886941) B2886941
theorem B5132339 : Blo 2279435 5132339 := bstep (se 1 (by rfl) ⟨3849254, by rfl⟩ : syracuseStep 5132339 = 7698509) B7698509
theorem B3421559 : Blo 2279435 3421559 := bstep (se 1 (by rfl) ⟨2566169, by rfl⟩ : syracuseStep 3421559 = 5132339) B5132339
theorem B2281039 : Blo 2279435 2281039 := bstep (se 1 (by rfl) ⟨1710779, by rfl⟩ : syracuseStep 2281039 = 3421559) B3421559
theorem B3421565 : Blo 2279435 3421565 := bbase (se 3 (by rfl) ⟨641543, by rfl⟩ : syracuseStep 3421565 = 1283087) (by norm_num)
theorem B2281043 : Blo 2279435 2281043 := bstep (se 1 (by rfl) ⟨1710782, by rfl⟩ : syracuseStep 2281043 = 3421565) B3421565
theorem B5132357 : Blo 2279435 5132357 := bbase (se 4 (by rfl) ⟨481158, by rfl⟩ : syracuseStep 5132357 = 962317) (by norm_num)
theorem B3421571 : Blo 2279435 3421571 := bstep (se 1 (by rfl) ⟨2566178, by rfl⟩ : syracuseStep 3421571 = 5132357) B5132357
theorem B2281047 : Blo 2279435 2281047 := bstep (se 1 (by rfl) ⟨1710785, by rfl⟩ : syracuseStep 2281047 = 3421571) B3421571
theorem B6495653 : Blo 2279435 6495653 := bbase (se 4 (by rfl) ⟨608967, by rfl⟩ : syracuseStep 6495653 = 1217935) (by norm_num)
theorem B4330435 : Blo 2279435 4330435 := bstep (se 1 (by rfl) ⟨3247826, by rfl⟩ : syracuseStep 4330435 = 6495653) B6495653
theorem B5773913 : Blo 2279435 5773913 := bstep (se 2 (by rfl) ⟨2165217, by rfl⟩ : syracuseStep 5773913 = 4330435) B4330435
theorem B3849275 : Blo 2279435 3849275 := bstep (se 1 (by rfl) ⟨2886956, by rfl⟩ : syracuseStep 3849275 = 5773913) B5773913
theorem B2566183 : Blo 2279435 2566183 := bstep (se 1 (by rfl) ⟨1924637, by rfl⟩ : syracuseStep 2566183 = 3849275) B3849275
theorem B3421577 : Blo 2279435 3421577 := bstep (se 2 (by rfl) ⟨1283091, by rfl⟩ : syracuseStep 3421577 = 2566183) B2566183
theorem B2281051 : Blo 2279435 2281051 := bstep (se 1 (by rfl) ⟨1710788, by rfl⟩ : syracuseStep 2281051 = 3421577) B3421577
theorem B11547845 : Blo 2279435 11547845 := bbase (se 4 (by rfl) ⟨1082610, by rfl⟩ : syracuseStep 11547845 = 2165221) (by norm_num)
theorem B7698563 : Blo 2279435 7698563 := bstep (se 1 (by rfl) ⟨5773922, by rfl⟩ : syracuseStep 7698563 = 11547845) B11547845
theorem B5132375 : Blo 2279435 5132375 := bstep (se 1 (by rfl) ⟨3849281, by rfl⟩ : syracuseStep 5132375 = 7698563) B7698563
theorem B3421583 : Blo 2279435 3421583 := bstep (se 1 (by rfl) ⟨2566187, by rfl⟩ : syracuseStep 3421583 = 5132375) B5132375
theorem B2281055 : Blo 2279435 2281055 := bstep (se 1 (by rfl) ⟨1710791, by rfl⟩ : syracuseStep 2281055 = 3421583) B3421583
theorem B3421589 : Blo 2279435 3421589 := bbase (se 6 (by rfl) ⟨80193, by rfl⟩ : syracuseStep 3421589 = 160387) (by norm_num)
theorem B2281059 : Blo 2279435 2281059 := bstep (se 1 (by rfl) ⟨1710794, by rfl⟩ : syracuseStep 2281059 = 3421589) B3421589
theorem B4871765 : Blo 2279435 4871765 := bbase (se 8 (by rfl) ⟨28545, by rfl⟩ : syracuseStep 4871765 = 57091) (by norm_num)
theorem B12991373 : Blo 2279435 12991373 := bstep (se 3 (by rfl) ⟨2435882, by rfl⟩ : syracuseStep 12991373 = 4871765) B4871765
theorem B8660915 : Blo 2279435 8660915 := bstep (se 1 (by rfl) ⟨6495686, by rfl⟩ : syracuseStep 8660915 = 12991373) B12991373
theorem B5773943 : Blo 2279435 5773943 := bstep (se 1 (by rfl) ⟨4330457, by rfl⟩ : syracuseStep 5773943 = 8660915) B8660915
theorem B3849295 : Blo 2279435 3849295 := bstep (se 1 (by rfl) ⟨2886971, by rfl⟩ : syracuseStep 3849295 = 5773943) B5773943
theorem B5132393 : Blo 2279435 5132393 := bstep (se 2 (by rfl) ⟨1924647, by rfl⟩ : syracuseStep 5132393 = 3849295) B3849295
theorem B3421595 : Blo 2279435 3421595 := bstep (se 1 (by rfl) ⟨2566196, by rfl⟩ : syracuseStep 3421595 = 5132393) B5132393
theorem B2281063 : Blo 2279435 2281063 := bstep (se 1 (by rfl) ⟨1710797, by rfl⟩ : syracuseStep 2281063 = 3421595) B3421595
theorem B2566201 : Blo 2279435 2566201 := bbase (se 2 (by rfl) ⟨962325, by rfl⟩ : syracuseStep 2566201 = 1924651) (by norm_num)
theorem B3421601 : Blo 2279435 3421601 := bstep (se 2 (by rfl) ⟨1283100, by rfl⟩ : syracuseStep 3421601 = 2566201) B2566201
theorem B2281067 : Blo 2279435 2281067 := bstep (se 1 (by rfl) ⟨1710800, by rfl⟩ : syracuseStep 2281067 = 3421601) B3421601
theorem B3653837 : Blo 2279435 3653837 := bbase (se 3 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 3653837 = 1370189) (by norm_num)
theorem B2435891 : Blo 2279435 2435891 := bstep (se 1 (by rfl) ⟨1826918, by rfl⟩ : syracuseStep 2435891 = 3653837) B3653837
theorem B6495709 : Blo 2279435 6495709 := bstep (se 3 (by rfl) ⟨1217945, by rfl⟩ : syracuseStep 6495709 = 2435891) B2435891
theorem B8660945 : Blo 2279435 8660945 := bstep (se 2 (by rfl) ⟨3247854, by rfl⟩ : syracuseStep 8660945 = 6495709) B6495709
theorem B5773963 : Blo 2279435 5773963 := bstep (se 1 (by rfl) ⟨4330472, by rfl⟩ : syracuseStep 5773963 = 8660945) B8660945
theorem B7698617 : Blo 2279435 7698617 := bstep (se 2 (by rfl) ⟨2886981, by rfl⟩ : syracuseStep 7698617 = 5773963) B5773963
theorem B5132411 : Blo 2279435 5132411 := bstep (se 1 (by rfl) ⟨3849308, by rfl⟩ : syracuseStep 5132411 = 7698617) B7698617
theorem B3421607 : Blo 2279435 3421607 := bstep (se 1 (by rfl) ⟨2566205, by rfl⟩ : syracuseStep 3421607 = 5132411) B5132411
theorem B2281071 : Blo 2279435 2281071 := bstep (se 1 (by rfl) ⟨1710803, by rfl⟩ : syracuseStep 2281071 = 3421607) B3421607
theorem B3421613 : Blo 2279435 3421613 := bbase (se 3 (by rfl) ⟨641552, by rfl⟩ : syracuseStep 3421613 = 1283105) (by norm_num)
theorem B2281075 : Blo 2279435 2281075 := bstep (se 1 (by rfl) ⟨1710806, by rfl⟩ : syracuseStep 2281075 = 3421613) B3421613
theorem B5132429 : Blo 2279435 5132429 := bbase (se 3 (by rfl) ⟨962330, by rfl⟩ : syracuseStep 5132429 = 1924661) (by norm_num)
theorem B3421619 : Blo 2279435 3421619 := bstep (se 1 (by rfl) ⟨2566214, by rfl⟩ : syracuseStep 3421619 = 5132429) B5132429
theorem B2281079 : Blo 2279435 2281079 := bstep (se 1 (by rfl) ⟨1710809, by rfl⟩ : syracuseStep 2281079 = 3421619) B3421619
theorem B2886997 : Blo 2279435 2886997 := bbase (se 11 (by rfl) ⟨2114, by rfl⟩ : syracuseStep 2886997 = 4229) (by norm_num)
theorem B3849329 : Blo 2279435 3849329 := bstep (se 2 (by rfl) ⟨1443498, by rfl⟩ : syracuseStep 3849329 = 2886997) B2886997
theorem B2566219 : Blo 2279435 2566219 := bstep (se 1 (by rfl) ⟨1924664, by rfl⟩ : syracuseStep 2566219 = 3849329) B3849329
theorem B3421625 : Blo 2279435 3421625 := bstep (se 2 (by rfl) ⟨1283109, by rfl⟩ : syracuseStep 3421625 = 2566219) B2566219
theorem B2281083 : Blo 2279435 2281083 := bstep (se 1 (by rfl) ⟨1710812, by rfl⟩ : syracuseStep 2281083 = 3421625) B3421625
theorem B13168757 : Blo 2279435 13168757 := bbase (se 5 (by rfl) ⟨617285, by rfl⟩ : syracuseStep 13168757 = 1234571) (by norm_num)
theorem B35116685 : Blo 2279435 35116685 := bstep (se 3 (by rfl) ⟨6584378, by rfl⟩ : syracuseStep 35116685 = 13168757) B13168757
theorem B23411123 : Blo 2279435 23411123 := bstep (se 1 (by rfl) ⟨17558342, by rfl⟩ : syracuseStep 23411123 = 35116685) B35116685
theorem B15607415 : Blo 2279435 15607415 := bstep (se 1 (by rfl) ⟨11705561, by rfl⟩ : syracuseStep 15607415 = 23411123) B23411123
theorem B10404943 : Blo 2279435 10404943 := bstep (se 1 (by rfl) ⟨7803707, by rfl⟩ : syracuseStep 10404943 = 15607415) B15607415
theorem B55493029 : Blo 2279435 55493029 := bstep (se 4 (by rfl) ⟨5202471, by rfl⟩ : syracuseStep 55493029 = 10404943) B10404943
theorem B73990705 : Blo 2279435 73990705 := bstep (se 2 (by rfl) ⟨27746514, by rfl⟩ : syracuseStep 73990705 = 55493029) B55493029
theorem B98654273 : Blo 2279435 98654273 := bstep (se 2 (by rfl) ⟨36995352, by rfl⟩ : syracuseStep 98654273 = 73990705) B73990705
theorem B65769515 : Blo 2279435 65769515 := bstep (se 1 (by rfl) ⟨49327136, by rfl⟩ : syracuseStep 65769515 = 98654273) B98654273
theorem B43846343 : Blo 2279435 43846343 := bstep (se 1 (by rfl) ⟨32884757, by rfl⟩ : syracuseStep 43846343 = 65769515) B65769515
theorem B29230895 : Blo 2279435 29230895 := bstep (se 1 (by rfl) ⟨21923171, by rfl⟩ : syracuseStep 29230895 = 43846343) B43846343
theorem B19487263 : Blo 2279435 19487263 := bstep (se 1 (by rfl) ⟨14615447, by rfl⟩ : syracuseStep 19487263 = 29230895) B29230895
theorem B25983017 : Blo 2279435 25983017 := bstep (se 2 (by rfl) ⟨9743631, by rfl⟩ : syracuseStep 25983017 = 19487263) B19487263
theorem B17322011 : Blo 2279435 17322011 := bstep (se 1 (by rfl) ⟨12991508, by rfl⟩ : syracuseStep 17322011 = 25983017) B25983017
theorem B11548007 : Blo 2279435 11548007 := bstep (se 1 (by rfl) ⟨8661005, by rfl⟩ : syracuseStep 11548007 = 17322011) B17322011
theorem B7698671 : Blo 2279435 7698671 := bstep (se 1 (by rfl) ⟨5774003, by rfl⟩ : syracuseStep 7698671 = 11548007) B11548007
theorem B5132447 : Blo 2279435 5132447 := bstep (se 1 (by rfl) ⟨3849335, by rfl⟩ : syracuseStep 5132447 = 7698671) B7698671
theorem B3421631 : Blo 2279435 3421631 := bstep (se 1 (by rfl) ⟨2566223, by rfl⟩ : syracuseStep 3421631 = 5132447) B5132447
theorem B2281087 : Blo 2279435 2281087 := bstep (se 1 (by rfl) ⟨1710815, by rfl⟩ : syracuseStep 2281087 = 3421631) B3421631
theorem B3421637 : Blo 2279435 3421637 := bbase (se 4 (by rfl) ⟨320778, by rfl⟩ : syracuseStep 3421637 = 641557) (by norm_num)
theorem B2281091 : Blo 2279435 2281091 := bstep (se 1 (by rfl) ⟨1710818, by rfl⟩ : syracuseStep 2281091 = 3421637) B3421637
theorem B3849349 : Blo 2279435 3849349 := bbase (se 4 (by rfl) ⟨360876, by rfl⟩ : syracuseStep 3849349 = 721753) (by norm_num)
theorem B5132465 : Blo 2279435 5132465 := bstep (se 2 (by rfl) ⟨1924674, by rfl⟩ : syracuseStep 5132465 = 3849349) B3849349
theorem B3421643 : Blo 2279435 3421643 := bstep (se 1 (by rfl) ⟨2566232, by rfl⟩ : syracuseStep 3421643 = 5132465) B5132465
theorem B2281095 : Blo 2279435 2281095 := bstep (se 1 (by rfl) ⟨1710821, by rfl⟩ : syracuseStep 2281095 = 3421643) B3421643
theorem B2566237 : Blo 2279435 2566237 := bbase (se 3 (by rfl) ⟨481169, by rfl⟩ : syracuseStep 2566237 = 962339) (by norm_num)
theorem B3421649 : Blo 2279435 3421649 := bstep (se 2 (by rfl) ⟨1283118, by rfl⟩ : syracuseStep 3421649 = 2566237) B2566237
theorem B2281099 : Blo 2279435 2281099 := bstep (se 1 (by rfl) ⟨1710824, by rfl⟩ : syracuseStep 2281099 = 3421649) B3421649
theorem B7698725 : Blo 2279435 7698725 := bbase (se 4 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 7698725 = 1443511) (by norm_num)
theorem B5132483 : Blo 2279435 5132483 := bstep (se 1 (by rfl) ⟨3849362, by rfl⟩ : syracuseStep 5132483 = 7698725) B7698725
theorem B3421655 : Blo 2279435 3421655 := bstep (se 1 (by rfl) ⟨2566241, by rfl⟩ : syracuseStep 3421655 = 5132483) B5132483
theorem B2281103 : Blo 2279435 2281103 := bstep (se 1 (by rfl) ⟨1710827, by rfl⟩ : syracuseStep 2281103 = 3421655) B3421655
theorem B3421661 : Blo 2279435 3421661 := bbase (se 3 (by rfl) ⟨641561, by rfl⟩ : syracuseStep 3421661 = 1283123) (by norm_num)
theorem B2281107 : Blo 2279435 2281107 := bstep (se 1 (by rfl) ⟨1710830, by rfl⟩ : syracuseStep 2281107 = 3421661) B3421661
theorem B5132501 : Blo 2279435 5132501 := bbase (se 7 (by rfl) ⟨60146, by rfl⟩ : syracuseStep 5132501 = 120293) (by norm_num)
theorem B3421667 : Blo 2279435 3421667 := bstep (se 1 (by rfl) ⟨2566250, by rfl⟩ : syracuseStep 3421667 = 5132501) B5132501
theorem B2281111 : Blo 2279435 2281111 := bstep (se 1 (by rfl) ⟨1710833, by rfl⟩ : syracuseStep 2281111 = 3421667) B3421667
theorem B18497909 : Blo 2279435 18497909 := bbase (se 5 (by rfl) ⟨867089, by rfl⟩ : syracuseStep 18497909 = 1734179) (by norm_num)
theorem B12331939 : Blo 2279435 12331939 := bstep (se 1 (by rfl) ⟨9248954, by rfl⟩ : syracuseStep 12331939 = 18497909) B18497909
theorem B16442585 : Blo 2279435 16442585 := bstep (se 2 (by rfl) ⟨6165969, by rfl⟩ : syracuseStep 16442585 = 12331939) B12331939
theorem B10961723 : Blo 2279435 10961723 := bstep (se 1 (by rfl) ⟨8221292, by rfl⟩ : syracuseStep 10961723 = 16442585) B16442585
theorem B7307815 : Blo 2279435 7307815 := bstep (se 1 (by rfl) ⟨5480861, by rfl⟩ : syracuseStep 7307815 = 10961723) B10961723
theorem B9743753 : Blo 2279435 9743753 := bstep (se 2 (by rfl) ⟨3653907, by rfl⟩ : syracuseStep 9743753 = 7307815) B7307815
theorem B6495835 : Blo 2279435 6495835 := bstep (se 1 (by rfl) ⟨4871876, by rfl⟩ : syracuseStep 6495835 = 9743753) B9743753
theorem B8661113 : Blo 2279435 8661113 := bstep (se 2 (by rfl) ⟨3247917, by rfl⟩ : syracuseStep 8661113 = 6495835) B6495835
theorem B5774075 : Blo 2279435 5774075 := bstep (se 1 (by rfl) ⟨4330556, by rfl⟩ : syracuseStep 5774075 = 8661113) B8661113
theorem B3849383 : Blo 2279435 3849383 := bstep (se 1 (by rfl) ⟨2887037, by rfl⟩ : syracuseStep 3849383 = 5774075) B5774075
theorem B2566255 : Blo 2279435 2566255 := bstep (se 1 (by rfl) ⟨1924691, by rfl⟩ : syracuseStep 2566255 = 3849383) B3849383
theorem B3421673 : Blo 2279435 3421673 := bstep (se 2 (by rfl) ⟨1283127, by rfl⟩ : syracuseStep 3421673 = 2566255) B2566255
theorem B2281115 : Blo 2279435 2281115 := bstep (se 1 (by rfl) ⟨1710836, by rfl⟩ : syracuseStep 2281115 = 3421673) B3421673
theorem B4110653 : Blo 2279435 4110653 := bbase (se 3 (by rfl) ⟨770747, by rfl⟩ : syracuseStep 4110653 = 1541495) (by norm_num)
theorem B2740435 : Blo 2279435 2740435 := bstep (se 1 (by rfl) ⟨2055326, by rfl⟩ : syracuseStep 2740435 = 4110653) B4110653
theorem B14615653 : Blo 2279435 14615653 := bstep (se 4 (by rfl) ⟨1370217, by rfl⟩ : syracuseStep 14615653 = 2740435) B2740435
theorem B19487537 : Blo 2279435 19487537 := bstep (se 2 (by rfl) ⟨7307826, by rfl⟩ : syracuseStep 19487537 = 14615653) B14615653
theorem B12991691 : Blo 2279435 12991691 := bstep (se 1 (by rfl) ⟨9743768, by rfl⟩ : syracuseStep 12991691 = 19487537) B19487537
theorem B8661127 : Blo 2279435 8661127 := bstep (se 1 (by rfl) ⟨6495845, by rfl⟩ : syracuseStep 8661127 = 12991691) B12991691
theorem B11548169 : Blo 2279435 11548169 := bstep (se 2 (by rfl) ⟨4330563, by rfl⟩ : syracuseStep 11548169 = 8661127) B8661127
theorem B7698779 : Blo 2279435 7698779 := bstep (se 1 (by rfl) ⟨5774084, by rfl⟩ : syracuseStep 7698779 = 11548169) B11548169
theorem B5132519 : Blo 2279435 5132519 := bstep (se 1 (by rfl) ⟨3849389, by rfl⟩ : syracuseStep 5132519 = 7698779) B7698779
theorem B3421679 : Blo 2279435 3421679 := bstep (se 1 (by rfl) ⟨2566259, by rfl⟩ : syracuseStep 3421679 = 5132519) B5132519
theorem B2281119 : Blo 2279435 2281119 := bstep (se 1 (by rfl) ⟨1710839, by rfl⟩ : syracuseStep 2281119 = 3421679) B3421679
theorem B3421685 : Blo 2279435 3421685 := bbase (se 5 (by rfl) ⟨160391, by rfl⟩ : syracuseStep 3421685 = 320783) (by norm_num)
theorem B2281123 : Blo 2279435 2281123 := bstep (se 1 (by rfl) ⟨1710842, by rfl⟩ : syracuseStep 2281123 = 3421685) B3421685
theorem B3901925 : Blo 2279435 3901925 := bbase (se 4 (by rfl) ⟨365805, by rfl⟩ : syracuseStep 3901925 = 731611) (by norm_num)
theorem B2601283 : Blo 2279435 2601283 := bstep (se 1 (by rfl) ⟨1950962, by rfl⟩ : syracuseStep 2601283 = 3901925) B3901925
theorem B3468377 : Blo 2279435 3468377 := bstep (se 2 (by rfl) ⟨1300641, by rfl⟩ : syracuseStep 3468377 = 2601283) B2601283
theorem B9249005 : Blo 2279435 9249005 := bstep (se 3 (by rfl) ⟨1734188, by rfl⟩ : syracuseStep 9249005 = 3468377) B3468377
theorem B6166003 : Blo 2279435 6166003 := bstep (se 1 (by rfl) ⟨4624502, by rfl⟩ : syracuseStep 6166003 = 9249005) B9249005
theorem B8221337 : Blo 2279435 8221337 := bstep (se 2 (by rfl) ⟨3083001, by rfl⟩ : syracuseStep 8221337 = 6166003) B6166003
theorem B5480891 : Blo 2279435 5480891 := bstep (se 1 (by rfl) ⟨4110668, by rfl⟩ : syracuseStep 5480891 = 8221337) B8221337
theorem B3653927 : Blo 2279435 3653927 := bstep (se 1 (by rfl) ⟨2740445, by rfl⟩ : syracuseStep 3653927 = 5480891) B5480891
theorem B2435951 : Blo 2279435 2435951 := bstep (se 1 (by rfl) ⟨1826963, by rfl⟩ : syracuseStep 2435951 = 3653927) B3653927
theorem B6495869 : Blo 2279435 6495869 := bstep (se 3 (by rfl) ⟨1217975, by rfl⟩ : syracuseStep 6495869 = 2435951) B2435951
theorem B4330579 : Blo 2279435 4330579 := bstep (se 1 (by rfl) ⟨3247934, by rfl⟩ : syracuseStep 4330579 = 6495869) B6495869
theorem B5774105 : Blo 2279435 5774105 := bstep (se 2 (by rfl) ⟨2165289, by rfl⟩ : syracuseStep 5774105 = 4330579) B4330579
theorem B3849403 : Blo 2279435 3849403 := bstep (se 1 (by rfl) ⟨2887052, by rfl⟩ : syracuseStep 3849403 = 5774105) B5774105
theorem B5132537 : Blo 2279435 5132537 := bstep (se 2 (by rfl) ⟨1924701, by rfl⟩ : syracuseStep 5132537 = 3849403) B3849403
theorem B3421691 : Blo 2279435 3421691 := bstep (se 1 (by rfl) ⟨2566268, by rfl⟩ : syracuseStep 3421691 = 5132537) B5132537
theorem B2281127 : Blo 2279435 2281127 := bstep (se 1 (by rfl) ⟨1710845, by rfl⟩ : syracuseStep 2281127 = 3421691) B3421691
theorem B2566273 : Blo 2279435 2566273 := bbase (se 2 (by rfl) ⟨962352, by rfl⟩ : syracuseStep 2566273 = 1924705) (by norm_num)
theorem B3421697 : Blo 2279435 3421697 := bstep (se 2 (by rfl) ⟨1283136, by rfl⟩ : syracuseStep 3421697 = 2566273) B2566273
theorem B2281131 : Blo 2279435 2281131 := bstep (se 1 (by rfl) ⟨1710848, by rfl⟩ : syracuseStep 2281131 = 3421697) B3421697
theorem B5774125 : Blo 2279435 5774125 := bbase (se 3 (by rfl) ⟨1082648, by rfl⟩ : syracuseStep 5774125 = 2165297) (by norm_num)
theorem B7698833 : Blo 2279435 7698833 := bstep (se 2 (by rfl) ⟨2887062, by rfl⟩ : syracuseStep 7698833 = 5774125) B5774125
theorem B5132555 : Blo 2279435 5132555 := bstep (se 1 (by rfl) ⟨3849416, by rfl⟩ : syracuseStep 5132555 = 7698833) B7698833
theorem B3421703 : Blo 2279435 3421703 := bstep (se 1 (by rfl) ⟨2566277, by rfl⟩ : syracuseStep 3421703 = 5132555) B5132555
theorem B2281135 : Blo 2279435 2281135 := bstep (se 1 (by rfl) ⟨1710851, by rfl⟩ : syracuseStep 2281135 = 3421703) B3421703
theorem B3421709 : Blo 2279435 3421709 := bbase (se 3 (by rfl) ⟨641570, by rfl⟩ : syracuseStep 3421709 = 1283141) (by norm_num)
theorem B2281139 : Blo 2279435 2281139 := bstep (se 1 (by rfl) ⟨1710854, by rfl⟩ : syracuseStep 2281139 = 3421709) B3421709
theorem B5132573 : Blo 2279435 5132573 := bbase (se 3 (by rfl) ⟨962357, by rfl⟩ : syracuseStep 5132573 = 1924715) (by norm_num)
theorem B3421715 : Blo 2279435 3421715 := bstep (se 1 (by rfl) ⟨2566286, by rfl⟩ : syracuseStep 3421715 = 5132573) B5132573
theorem B2281143 : Blo 2279435 2281143 := bstep (se 1 (by rfl) ⟨1710857, by rfl⟩ : syracuseStep 2281143 = 3421715) B3421715
theorem B3849437 : Blo 2279435 3849437 := bbase (se 3 (by rfl) ⟨721769, by rfl⟩ : syracuseStep 3849437 = 1443539) (by norm_num)
theorem B2566291 : Blo 2279435 2566291 := bstep (se 1 (by rfl) ⟨1924718, by rfl⟩ : syracuseStep 2566291 = 3849437) B3849437
theorem B3421721 : Blo 2279435 3421721 := bstep (se 2 (by rfl) ⟨1283145, by rfl⟩ : syracuseStep 3421721 = 2566291) B2566291
theorem B2281147 : Blo 2279435 2281147 := bstep (se 1 (by rfl) ⟨1710860, by rfl⟩ : syracuseStep 2281147 = 3421721) B3421721
theorem B3468413 : Blo 2279435 3468413 := bbase (se 3 (by rfl) ⟨650327, by rfl⟩ : syracuseStep 3468413 = 1300655) (by norm_num)
theorem B2312275 : Blo 2279435 2312275 := bstep (se 1 (by rfl) ⟨1734206, by rfl⟩ : syracuseStep 2312275 = 3468413) B3468413
theorem B3083033 : Blo 2279435 3083033 := bstep (se 2 (by rfl) ⟨1156137, by rfl⟩ : syracuseStep 3083033 = 2312275) B2312275
theorem B8221421 : Blo 2279435 8221421 := bstep (se 3 (by rfl) ⟨1541516, by rfl⟩ : syracuseStep 8221421 = 3083033) B3083033
theorem B5480947 : Blo 2279435 5480947 := bstep (se 1 (by rfl) ⟨4110710, by rfl⟩ : syracuseStep 5480947 = 8221421) B8221421
theorem B7307929 : Blo 2279435 7307929 := bstep (se 2 (by rfl) ⟨2740473, by rfl⟩ : syracuseStep 7307929 = 5480947) B5480947
theorem B9743905 : Blo 2279435 9743905 := bstep (se 2 (by rfl) ⟨3653964, by rfl⟩ : syracuseStep 9743905 = 7307929) B7307929
theorem B12991873 : Blo 2279435 12991873 := bstep (se 2 (by rfl) ⟨4871952, by rfl⟩ : syracuseStep 12991873 = 9743905) B9743905
theorem B17322497 : Blo 2279435 17322497 := bstep (se 2 (by rfl) ⟨6495936, by rfl⟩ : syracuseStep 17322497 = 12991873) B12991873
theorem B11548331 : Blo 2279435 11548331 := bstep (se 1 (by rfl) ⟨8661248, by rfl⟩ : syracuseStep 11548331 = 17322497) B17322497
theorem B7698887 : Blo 2279435 7698887 := bstep (se 1 (by rfl) ⟨5774165, by rfl⟩ : syracuseStep 7698887 = 11548331) B11548331
theorem B5132591 : Blo 2279435 5132591 := bstep (se 1 (by rfl) ⟨3849443, by rfl⟩ : syracuseStep 5132591 = 7698887) B7698887
theorem B3421727 : Blo 2279435 3421727 := bstep (se 1 (by rfl) ⟨2566295, by rfl⟩ : syracuseStep 3421727 = 5132591) B5132591
theorem B2281151 : Blo 2279435 2281151 := bstep (se 1 (by rfl) ⟨1710863, by rfl⟩ : syracuseStep 2281151 = 3421727) B3421727
theorem B3421733 : Blo 2279435 3421733 := bbase (se 4 (by rfl) ⟨320787, by rfl⟩ : syracuseStep 3421733 = 641575) (by norm_num)
theorem B2281155 : Blo 2279435 2281155 := bstep (se 1 (by rfl) ⟨1710866, by rfl⟩ : syracuseStep 2281155 = 3421733) B3421733
theorem B2887093 : Blo 2279435 2887093 := bbase (se 5 (by rfl) ⟨135332, by rfl⟩ : syracuseStep 2887093 = 270665) (by norm_num)
theorem B3849457 : Blo 2279435 3849457 := bstep (se 2 (by rfl) ⟨1443546, by rfl⟩ : syracuseStep 3849457 = 2887093) B2887093
theorem B5132609 : Blo 2279435 5132609 := bstep (se 2 (by rfl) ⟨1924728, by rfl⟩ : syracuseStep 5132609 = 3849457) B3849457
theorem B3421739 : Blo 2279435 3421739 := bstep (se 1 (by rfl) ⟨2566304, by rfl⟩ : syracuseStep 3421739 = 5132609) B5132609
theorem B2281159 : Blo 2279435 2281159 := bstep (se 1 (by rfl) ⟨1710869, by rfl⟩ : syracuseStep 2281159 = 3421739) B3421739
theorem B2566309 : Blo 2279435 2566309 := bbase (se 4 (by rfl) ⟨240591, by rfl⟩ : syracuseStep 2566309 = 481183) (by norm_num)
theorem B3421745 : Blo 2279435 3421745 := bstep (se 2 (by rfl) ⟨1283154, by rfl⟩ : syracuseStep 3421745 = 2566309) B2566309
theorem B2281163 : Blo 2279435 2281163 := bstep (se 1 (by rfl) ⟨1710872, by rfl⟩ : syracuseStep 2281163 = 3421745) B3421745
theorem B9876917 : Blo 2279435 9876917 := bbase (se 5 (by rfl) ⟨462980, by rfl⟩ : syracuseStep 9876917 = 925961) (by norm_num)
theorem B26338445 : Blo 2279435 26338445 := bstep (se 3 (by rfl) ⟨4938458, by rfl⟩ : syracuseStep 26338445 = 9876917) B9876917
theorem B17558963 : Blo 2279435 17558963 := bstep (se 1 (by rfl) ⟨13169222, by rfl⟩ : syracuseStep 17558963 = 26338445) B26338445
theorem B11705975 : Blo 2279435 11705975 := bstep (se 1 (by rfl) ⟨8779481, by rfl⟩ : syracuseStep 11705975 = 17558963) B17558963
theorem B7803983 : Blo 2279435 7803983 := bstep (se 1 (by rfl) ⟨5852987, by rfl⟩ : syracuseStep 7803983 = 11705975) B11705975
theorem B20810621 : Blo 2279435 20810621 := bstep (se 3 (by rfl) ⟨3901991, by rfl⟩ : syracuseStep 20810621 = 7803983) B7803983
theorem B55494989 : Blo 2279435 55494989 := bstep (se 3 (by rfl) ⟨10405310, by rfl⟩ : syracuseStep 55494989 = 20810621) B20810621
theorem B36996659 : Blo 2279435 36996659 := bstep (se 1 (by rfl) ⟨27747494, by rfl⟩ : syracuseStep 36996659 = 55494989) B55494989
theorem B24664439 : Blo 2279435 24664439 := bstep (se 1 (by rfl) ⟨18498329, by rfl⟩ : syracuseStep 24664439 = 36996659) B36996659
theorem B16442959 : Blo 2279435 16442959 := bstep (se 1 (by rfl) ⟨12332219, by rfl⟩ : syracuseStep 16442959 = 24664439) B24664439
theorem B21923945 : Blo 2279435 21923945 := bstep (se 2 (by rfl) ⟨8221479, by rfl⟩ : syracuseStep 21923945 = 16442959) B16442959
theorem B14615963 : Blo 2279435 14615963 := bstep (se 1 (by rfl) ⟨10961972, by rfl⟩ : syracuseStep 14615963 = 21923945) B21923945
theorem B9743975 : Blo 2279435 9743975 := bstep (se 1 (by rfl) ⟨7307981, by rfl⟩ : syracuseStep 9743975 = 14615963) B14615963
theorem B6495983 : Blo 2279435 6495983 := bstep (se 1 (by rfl) ⟨4871987, by rfl⟩ : syracuseStep 6495983 = 9743975) B9743975
theorem B4330655 : Blo 2279435 4330655 := bstep (se 1 (by rfl) ⟨3247991, by rfl⟩ : syracuseStep 4330655 = 6495983) B6495983
theorem B2887103 : Blo 2279435 2887103 := bstep (se 1 (by rfl) ⟨2165327, by rfl⟩ : syracuseStep 2887103 = 4330655) B4330655
theorem B7698941 : Blo 2279435 7698941 := bstep (se 3 (by rfl) ⟨1443551, by rfl⟩ : syracuseStep 7698941 = 2887103) B2887103
theorem B5132627 : Blo 2279435 5132627 := bstep (se 1 (by rfl) ⟨3849470, by rfl⟩ : syracuseStep 5132627 = 7698941) B7698941
theorem B3421751 : Blo 2279435 3421751 := bstep (se 1 (by rfl) ⟨2566313, by rfl⟩ : syracuseStep 3421751 = 5132627) B5132627
theorem B2281167 : Blo 2279435 2281167 := bstep (se 1 (by rfl) ⟨1710875, by rfl⟩ : syracuseStep 2281167 = 3421751) B3421751
theorem B3421757 : Blo 2279435 3421757 := bbase (se 3 (by rfl) ⟨641579, by rfl⟩ : syracuseStep 3421757 = 1283159) (by norm_num)
theorem B2281171 : Blo 2279435 2281171 := bstep (se 1 (by rfl) ⟨1710878, by rfl⟩ : syracuseStep 2281171 = 3421757) B3421757
theorem B5132645 : Blo 2279435 5132645 := bbase (se 4 (by rfl) ⟨481185, by rfl⟩ : syracuseStep 5132645 = 962371) (by norm_num)
theorem B3421763 : Blo 2279435 3421763 := bstep (se 1 (by rfl) ⟨2566322, by rfl⟩ : syracuseStep 3421763 = 5132645) B5132645
theorem B2281175 : Blo 2279435 2281175 := bstep (se 1 (by rfl) ⟨1710881, by rfl⟩ : syracuseStep 2281175 = 3421763) B3421763
theorem B5774237 : Blo 2279435 5774237 := bbase (se 3 (by rfl) ⟨1082669, by rfl⟩ : syracuseStep 5774237 = 2165339) (by norm_num)
theorem B3849491 : Blo 2279435 3849491 := bstep (se 1 (by rfl) ⟨2887118, by rfl⟩ : syracuseStep 3849491 = 5774237) B5774237
theorem B2566327 : Blo 2279435 2566327 := bstep (se 1 (by rfl) ⟨1924745, by rfl⟩ : syracuseStep 2566327 = 3849491) B3849491
theorem B3421769 : Blo 2279435 3421769 := bstep (se 2 (by rfl) ⟨1283163, by rfl⟩ : syracuseStep 3421769 = 2566327) B2566327
theorem B2281179 : Blo 2279435 2281179 := bstep (se 1 (by rfl) ⟨1710884, by rfl⟩ : syracuseStep 2281179 = 3421769) B3421769
theorem B4330685 : Blo 2279435 4330685 := bbase (se 3 (by rfl) ⟨812003, by rfl⟩ : syracuseStep 4330685 = 1624007) (by norm_num)
theorem B11548493 : Blo 2279435 11548493 := bstep (se 3 (by rfl) ⟨2165342, by rfl⟩ : syracuseStep 11548493 = 4330685) B4330685
theorem B7698995 : Blo 2279435 7698995 := bstep (se 1 (by rfl) ⟨5774246, by rfl⟩ : syracuseStep 7698995 = 11548493) B11548493
theorem B5132663 : Blo 2279435 5132663 := bstep (se 1 (by rfl) ⟨3849497, by rfl⟩ : syracuseStep 5132663 = 7698995) B7698995
theorem B3421775 : Blo 2279435 3421775 := bstep (se 1 (by rfl) ⟨2566331, by rfl⟩ : syracuseStep 3421775 = 5132663) B5132663
theorem B2281183 : Blo 2279435 2281183 := bstep (se 1 (by rfl) ⟨1710887, by rfl⟩ : syracuseStep 2281183 = 3421775) B3421775
theorem B3421781 : Blo 2279435 3421781 := bbase (se 8 (by rfl) ⟨20049, by rfl⟩ : syracuseStep 3421781 = 40099) (by norm_num)
theorem B2281187 : Blo 2279435 2281187 := bstep (se 1 (by rfl) ⟨1710890, by rfl⟩ : syracuseStep 2281187 = 3421781) B3421781
theorem B3654029 : Blo 2279435 3654029 := bbase (se 3 (by rfl) ⟨685130, by rfl⟩ : syracuseStep 3654029 = 1370261) (by norm_num)
theorem B9744077 : Blo 2279435 9744077 := bstep (se 3 (by rfl) ⟨1827014, by rfl⟩ : syracuseStep 9744077 = 3654029) B3654029
theorem B6496051 : Blo 2279435 6496051 := bstep (se 1 (by rfl) ⟨4872038, by rfl⟩ : syracuseStep 6496051 = 9744077) B9744077
theorem B8661401 : Blo 2279435 8661401 := bstep (se 2 (by rfl) ⟨3248025, by rfl⟩ : syracuseStep 8661401 = 6496051) B6496051
theorem B5774267 : Blo 2279435 5774267 := bstep (se 1 (by rfl) ⟨4330700, by rfl⟩ : syracuseStep 5774267 = 8661401) B8661401
theorem B3849511 : Blo 2279435 3849511 := bstep (se 1 (by rfl) ⟨2887133, by rfl⟩ : syracuseStep 3849511 = 5774267) B5774267
theorem B5132681 : Blo 2279435 5132681 := bstep (se 2 (by rfl) ⟨1924755, by rfl⟩ : syracuseStep 5132681 = 3849511) B3849511
theorem B3421787 : Blo 2279435 3421787 := bstep (se 1 (by rfl) ⟨2566340, by rfl⟩ : syracuseStep 3421787 = 5132681) B5132681
theorem B2281191 : Blo 2279435 2281191 := bstep (se 1 (by rfl) ⟨1710893, by rfl⟩ : syracuseStep 2281191 = 3421787) B3421787
theorem B2566345 : Blo 2279435 2566345 := bbase (se 2 (by rfl) ⟨962379, by rfl⟩ : syracuseStep 2566345 = 1924759) (by norm_num)
theorem B3421793 : Blo 2279435 3421793 := bstep (se 2 (by rfl) ⟨1283172, by rfl⟩ : syracuseStep 3421793 = 2566345) B2566345
theorem B2281195 : Blo 2279435 2281195 := bstep (se 1 (by rfl) ⟨1710896, by rfl⟩ : syracuseStep 2281195 = 3421793) B3421793
theorem B4110797 : Blo 2279435 4110797 := bbase (se 3 (by rfl) ⟨770774, by rfl⟩ : syracuseStep 4110797 = 1541549) (by norm_num)
theorem B10962125 : Blo 2279435 10962125 := bstep (se 3 (by rfl) ⟨2055398, by rfl⟩ : syracuseStep 10962125 = 4110797) B4110797
theorem B7308083 : Blo 2279435 7308083 := bstep (se 1 (by rfl) ⟨5481062, by rfl⟩ : syracuseStep 7308083 = 10962125) B10962125
theorem B19488221 : Blo 2279435 19488221 := bstep (se 3 (by rfl) ⟨3654041, by rfl⟩ : syracuseStep 19488221 = 7308083) B7308083
theorem B12992147 : Blo 2279435 12992147 := bstep (se 1 (by rfl) ⟨9744110, by rfl⟩ : syracuseStep 12992147 = 19488221) B19488221
theorem B8661431 : Blo 2279435 8661431 := bstep (se 1 (by rfl) ⟨6496073, by rfl⟩ : syracuseStep 8661431 = 12992147) B12992147
theorem B5774287 : Blo 2279435 5774287 := bstep (se 1 (by rfl) ⟨4330715, by rfl⟩ : syracuseStep 5774287 = 8661431) B8661431
theorem B7699049 : Blo 2279435 7699049 := bstep (se 2 (by rfl) ⟨2887143, by rfl⟩ : syracuseStep 7699049 = 5774287) B5774287
theorem B5132699 : Blo 2279435 5132699 := bstep (se 1 (by rfl) ⟨3849524, by rfl⟩ : syracuseStep 5132699 = 7699049) B7699049
theorem B3421799 : Blo 2279435 3421799 := bstep (se 1 (by rfl) ⟨2566349, by rfl⟩ : syracuseStep 3421799 = 5132699) B5132699
theorem B2281199 : Blo 2279435 2281199 := bstep (se 1 (by rfl) ⟨1710899, by rfl⟩ : syracuseStep 2281199 = 3421799) B3421799
theorem B3421805 : Blo 2279435 3421805 := bbase (se 3 (by rfl) ⟨641588, by rfl⟩ : syracuseStep 3421805 = 1283177) (by norm_num)
theorem B2281203 : Blo 2279435 2281203 := bstep (se 1 (by rfl) ⟨1710902, by rfl⟩ : syracuseStep 2281203 = 3421805) B3421805
theorem B5132717 : Blo 2279435 5132717 := bbase (se 3 (by rfl) ⟨962384, by rfl⟩ : syracuseStep 5132717 = 1924769) (by norm_num)
theorem B3421811 : Blo 2279435 3421811 := bstep (se 1 (by rfl) ⟨2566358, by rfl⟩ : syracuseStep 3421811 = 5132717) B5132717
theorem B2281207 : Blo 2279435 2281207 := bstep (se 1 (by rfl) ⟨1710905, by rfl⟩ : syracuseStep 2281207 = 3421811) B3421811
theorem B2436041 : Blo 2279435 2436041 := bbase (se 2 (by rfl) ⟨913515, by rfl⟩ : syracuseStep 2436041 = 1827031) (by norm_num)
theorem B6496109 : Blo 2279435 6496109 := bstep (se 3 (by rfl) ⟨1218020, by rfl⟩ : syracuseStep 6496109 = 2436041) B2436041
theorem B4330739 : Blo 2279435 4330739 := bstep (se 1 (by rfl) ⟨3248054, by rfl⟩ : syracuseStep 4330739 = 6496109) B6496109
theorem B2887159 : Blo 2279435 2887159 := bstep (se 1 (by rfl) ⟨2165369, by rfl⟩ : syracuseStep 2887159 = 4330739) B4330739
theorem B3849545 : Blo 2279435 3849545 := bstep (se 2 (by rfl) ⟨1443579, by rfl⟩ : syracuseStep 3849545 = 2887159) B2887159
theorem B2566363 : Blo 2279435 2566363 := bstep (se 1 (by rfl) ⟨1924772, by rfl⟩ : syracuseStep 2566363 = 3849545) B3849545
theorem B3421817 : Blo 2279435 3421817 := bstep (se 2 (by rfl) ⟨1283181, by rfl⟩ : syracuseStep 3421817 = 2566363) B2566363
theorem B2281211 : Blo 2279435 2281211 := bstep (se 1 (by rfl) ⟨1710908, by rfl⟩ : syracuseStep 2281211 = 3421817) B3421817
theorem B7407845 : Blo 2279435 7407845 := bbase (se 4 (by rfl) ⟨694485, by rfl⟩ : syracuseStep 7407845 = 1388971) (by norm_num)
theorem B4938563 : Blo 2279435 4938563 := bstep (se 1 (by rfl) ⟨3703922, by rfl⟩ : syracuseStep 4938563 = 7407845) B7407845
theorem B3292375 : Blo 2279435 3292375 := bstep (se 1 (by rfl) ⟨2469281, by rfl⟩ : syracuseStep 3292375 = 4938563) B4938563
theorem B4389833 : Blo 2279435 4389833 := bstep (se 2 (by rfl) ⟨1646187, by rfl⟩ : syracuseStep 4389833 = 3292375) B3292375
theorem B11706221 : Blo 2279435 11706221 := bstep (se 3 (by rfl) ⟨2194916, by rfl⟩ : syracuseStep 11706221 = 4389833) B4389833
theorem B7804147 : Blo 2279435 7804147 := bstep (se 1 (by rfl) ⟨5853110, by rfl⟩ : syracuseStep 7804147 = 11706221) B11706221
theorem B10405529 : Blo 2279435 10405529 := bstep (se 2 (by rfl) ⟨3902073, by rfl⟩ : syracuseStep 10405529 = 7804147) B7804147
theorem B6937019 : Blo 2279435 6937019 := bstep (se 1 (by rfl) ⟨5202764, by rfl⟩ : syracuseStep 6937019 = 10405529) B10405529
theorem B4624679 : Blo 2279435 4624679 := bstep (se 1 (by rfl) ⟨3468509, by rfl⟩ : syracuseStep 4624679 = 6937019) B6937019
theorem B3083119 : Blo 2279435 3083119 := bstep (se 1 (by rfl) ⟨2312339, by rfl⟩ : syracuseStep 3083119 = 4624679) B4624679
theorem B65773205 : Blo 2279435 65773205 := bstep (se 6 (by rfl) ⟨1541559, by rfl⟩ : syracuseStep 65773205 = 3083119) B3083119
theorem B43848803 : Blo 2279435 43848803 := bstep (se 1 (by rfl) ⟨32886602, by rfl⟩ : syracuseStep 43848803 = 65773205) B65773205
theorem B29232535 : Blo 2279435 29232535 := bstep (se 1 (by rfl) ⟨21924401, by rfl⟩ : syracuseStep 29232535 = 43848803) B43848803
theorem B38976713 : Blo 2279435 38976713 := bstep (se 2 (by rfl) ⟨14616267, by rfl⟩ : syracuseStep 38976713 = 29232535) B29232535
theorem B25984475 : Blo 2279435 25984475 := bstep (se 1 (by rfl) ⟨19488356, by rfl⟩ : syracuseStep 25984475 = 38976713) B38976713
theorem B17322983 : Blo 2279435 17322983 := bstep (se 1 (by rfl) ⟨12992237, by rfl⟩ : syracuseStep 17322983 = 25984475) B25984475
theorem B11548655 : Blo 2279435 11548655 := bstep (se 1 (by rfl) ⟨8661491, by rfl⟩ : syracuseStep 11548655 = 17322983) B17322983
theorem B7699103 : Blo 2279435 7699103 := bstep (se 1 (by rfl) ⟨5774327, by rfl⟩ : syracuseStep 7699103 = 11548655) B11548655
theorem B5132735 : Blo 2279435 5132735 := bstep (se 1 (by rfl) ⟨3849551, by rfl⟩ : syracuseStep 5132735 = 7699103) B7699103
theorem B3421823 : Blo 2279435 3421823 := bstep (se 1 (by rfl) ⟨2566367, by rfl⟩ : syracuseStep 3421823 = 5132735) B5132735
theorem B2281215 : Blo 2279435 2281215 := bstep (se 1 (by rfl) ⟨1710911, by rfl⟩ : syracuseStep 2281215 = 3421823) B3421823
theorem B3421829 : Blo 2279435 3421829 := bbase (se 4 (by rfl) ⟨320796, by rfl⟩ : syracuseStep 3421829 = 641593) (by norm_num)
theorem B2281219 : Blo 2279435 2281219 := bstep (se 1 (by rfl) ⟨1710914, by rfl⟩ : syracuseStep 2281219 = 3421829) B3421829
theorem B3849565 : Blo 2279435 3849565 := bbase (se 3 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 3849565 = 1443587) (by norm_num)
theorem B5132753 : Blo 2279435 5132753 := bstep (se 2 (by rfl) ⟨1924782, by rfl⟩ : syracuseStep 5132753 = 3849565) B3849565
theorem B3421835 : Blo 2279435 3421835 := bstep (se 1 (by rfl) ⟨2566376, by rfl⟩ : syracuseStep 3421835 = 5132753) B5132753
theorem B2281223 : Blo 2279435 2281223 := bstep (se 1 (by rfl) ⟨1710917, by rfl⟩ : syracuseStep 2281223 = 3421835) B3421835
theorem B2566381 : Blo 2279435 2566381 := bbase (se 3 (by rfl) ⟨481196, by rfl⟩ : syracuseStep 2566381 = 962393) (by norm_num)
theorem B3421841 : Blo 2279435 3421841 := bstep (se 2 (by rfl) ⟨1283190, by rfl⟩ : syracuseStep 3421841 = 2566381) B2566381
theorem B2281227 : Blo 2279435 2281227 := bstep (se 1 (by rfl) ⟨1710920, by rfl⟩ : syracuseStep 2281227 = 3421841) B3421841
theorem B7699157 : Blo 2279435 7699157 := bbase (se 7 (by rfl) ⟨90224, by rfl⟩ : syracuseStep 7699157 = 180449) (by norm_num)
theorem B5132771 : Blo 2279435 5132771 := bstep (se 1 (by rfl) ⟨3849578, by rfl⟩ : syracuseStep 5132771 = 7699157) B7699157
theorem B3421847 : Blo 2279435 3421847 := bstep (se 1 (by rfl) ⟨2566385, by rfl⟩ : syracuseStep 3421847 = 5132771) B5132771
theorem B2281231 : Blo 2279435 2281231 := bstep (se 1 (by rfl) ⟨1710923, by rfl⟩ : syracuseStep 2281231 = 3421847) B3421847
theorem B3421853 : Blo 2279435 3421853 := bbase (se 3 (by rfl) ⟨641597, by rfl⟩ : syracuseStep 3421853 = 1283195) (by norm_num)
theorem B2281235 : Blo 2279435 2281235 := bstep (se 1 (by rfl) ⟨1710926, by rfl⟩ : syracuseStep 2281235 = 3421853) B3421853
theorem B5132789 : Blo 2279435 5132789 := bbase (se 5 (by rfl) ⟨240599, by rfl⟩ : syracuseStep 5132789 = 481199) (by norm_num)
theorem B3421859 : Blo 2279435 3421859 := bstep (se 1 (by rfl) ⟨2566394, by rfl⟩ : syracuseStep 3421859 = 5132789) B5132789
theorem B2281239 : Blo 2279435 2281239 := bstep (se 1 (by rfl) ⟨1710929, by rfl⟩ : syracuseStep 2281239 = 3421859) B3421859
theorem B5202829 : Blo 2279435 5202829 := bbase (se 3 (by rfl) ⟨975530, by rfl⟩ : syracuseStep 5202829 = 1951061) (by norm_num)
theorem B6937105 : Blo 2279435 6937105 := bstep (se 2 (by rfl) ⟨2601414, by rfl⟩ : syracuseStep 6937105 = 5202829) B5202829
theorem B9249473 : Blo 2279435 9249473 := bstep (se 2 (by rfl) ⟨3468552, by rfl⟩ : syracuseStep 9249473 = 6937105) B6937105
theorem B6166315 : Blo 2279435 6166315 := bstep (se 1 (by rfl) ⟨4624736, by rfl⟩ : syracuseStep 6166315 = 9249473) B9249473
theorem B8221753 : Blo 2279435 8221753 := bstep (se 2 (by rfl) ⟨3083157, by rfl⟩ : syracuseStep 8221753 = 6166315) B6166315
theorem B43849349 : Blo 2279435 43849349 := bstep (se 4 (by rfl) ⟨4110876, by rfl⟩ : syracuseStep 43849349 = 8221753) B8221753
theorem B29232899 : Blo 2279435 29232899 := bstep (se 1 (by rfl) ⟨21924674, by rfl⟩ : syracuseStep 29232899 = 43849349) B43849349
theorem B19488599 : Blo 2279435 19488599 := bstep (se 1 (by rfl) ⟨14616449, by rfl⟩ : syracuseStep 19488599 = 29232899) B29232899
theorem B12992399 : Blo 2279435 12992399 := bstep (se 1 (by rfl) ⟨9744299, by rfl⟩ : syracuseStep 12992399 = 19488599) B19488599
theorem B8661599 : Blo 2279435 8661599 := bstep (se 1 (by rfl) ⟨6496199, by rfl⟩ : syracuseStep 8661599 = 12992399) B12992399
theorem B5774399 : Blo 2279435 5774399 := bstep (se 1 (by rfl) ⟨4330799, by rfl⟩ : syracuseStep 5774399 = 8661599) B8661599
theorem B3849599 : Blo 2279435 3849599 := bstep (se 1 (by rfl) ⟨2887199, by rfl⟩ : syracuseStep 3849599 = 5774399) B5774399
theorem B2566399 : Blo 2279435 2566399 := bstep (se 1 (by rfl) ⟨1924799, by rfl⟩ : syracuseStep 2566399 = 3849599) B3849599
theorem B3421865 : Blo 2279435 3421865 := bstep (se 2 (by rfl) ⟨1283199, by rfl⟩ : syracuseStep 3421865 = 2566399) B2566399
theorem B2281243 : Blo 2279435 2281243 := bstep (se 1 (by rfl) ⟨1710932, by rfl⟩ : syracuseStep 2281243 = 3421865) B3421865
theorem B11706389 : Blo 2279435 11706389 := bbase (se 6 (by rfl) ⟨274368, by rfl⟩ : syracuseStep 11706389 = 548737) (by norm_num)
theorem B7804259 : Blo 2279435 7804259 := bstep (se 1 (by rfl) ⟨5853194, by rfl⟩ : syracuseStep 7804259 = 11706389) B11706389
theorem B5202839 : Blo 2279435 5202839 := bstep (se 1 (by rfl) ⟨3902129, by rfl⟩ : syracuseStep 5202839 = 7804259) B7804259
theorem B13874237 : Blo 2279435 13874237 := bstep (se 3 (by rfl) ⟨2601419, by rfl⟩ : syracuseStep 13874237 = 5202839) B5202839
theorem B9249491 : Blo 2279435 9249491 := bstep (se 1 (by rfl) ⟨6937118, by rfl⟩ : syracuseStep 9249491 = 13874237) B13874237
theorem B6166327 : Blo 2279435 6166327 := bstep (se 1 (by rfl) ⟨4624745, by rfl⟩ : syracuseStep 6166327 = 9249491) B9249491
theorem B8221769 : Blo 2279435 8221769 := bstep (se 2 (by rfl) ⟨3083163, by rfl⟩ : syracuseStep 8221769 = 6166327) B6166327
theorem B5481179 : Blo 2279435 5481179 := bstep (se 1 (by rfl) ⟨4110884, by rfl⟩ : syracuseStep 5481179 = 8221769) B8221769
theorem B3654119 : Blo 2279435 3654119 := bstep (se 1 (by rfl) ⟨2740589, by rfl⟩ : syracuseStep 3654119 = 5481179) B5481179
theorem B2436079 : Blo 2279435 2436079 := bstep (se 1 (by rfl) ⟨1827059, by rfl⟩ : syracuseStep 2436079 = 3654119) B3654119
theorem B3248105 : Blo 2279435 3248105 := bstep (se 2 (by rfl) ⟨1218039, by rfl⟩ : syracuseStep 3248105 = 2436079) B2436079
theorem B8661613 : Blo 2279435 8661613 := bstep (se 3 (by rfl) ⟨1624052, by rfl⟩ : syracuseStep 8661613 = 3248105) B3248105
theorem B11548817 : Blo 2279435 11548817 := bstep (se 2 (by rfl) ⟨4330806, by rfl⟩ : syracuseStep 11548817 = 8661613) B8661613
theorem B7699211 : Blo 2279435 7699211 := bstep (se 1 (by rfl) ⟨5774408, by rfl⟩ : syracuseStep 7699211 = 11548817) B11548817
theorem B5132807 : Blo 2279435 5132807 := bstep (se 1 (by rfl) ⟨3849605, by rfl⟩ : syracuseStep 5132807 = 7699211) B7699211
theorem B3421871 : Blo 2279435 3421871 := bstep (se 1 (by rfl) ⟨2566403, by rfl⟩ : syracuseStep 3421871 = 5132807) B5132807
theorem B2281247 : Blo 2279435 2281247 := bstep (se 1 (by rfl) ⟨1710935, by rfl⟩ : syracuseStep 2281247 = 3421871) B3421871
theorem B3421877 : Blo 2279435 3421877 := bbase (se 5 (by rfl) ⟨160400, by rfl⟩ : syracuseStep 3421877 = 320801) (by norm_num)
theorem B2281251 : Blo 2279435 2281251 := bstep (se 1 (by rfl) ⟨1710938, by rfl⟩ : syracuseStep 2281251 = 3421877) B3421877
theorem B5774429 : Blo 2279435 5774429 := bbase (se 3 (by rfl) ⟨1082705, by rfl⟩ : syracuseStep 5774429 = 2165411) (by norm_num)
theorem B3849619 : Blo 2279435 3849619 := bstep (se 1 (by rfl) ⟨2887214, by rfl⟩ : syracuseStep 3849619 = 5774429) B5774429
theorem B5132825 : Blo 2279435 5132825 := bstep (se 2 (by rfl) ⟨1924809, by rfl⟩ : syracuseStep 5132825 = 3849619) B3849619
theorem B3421883 : Blo 2279435 3421883 := bstep (se 1 (by rfl) ⟨2566412, by rfl⟩ : syracuseStep 3421883 = 5132825) B5132825
theorem B2281255 : Blo 2279435 2281255 := bstep (se 1 (by rfl) ⟨1710941, by rfl⟩ : syracuseStep 2281255 = 3421883) B3421883
theorem B2566417 : Blo 2279435 2566417 := bbase (se 2 (by rfl) ⟨962406, by rfl⟩ : syracuseStep 2566417 = 1924813) (by norm_num)
theorem B3421889 : Blo 2279435 3421889 := bstep (se 2 (by rfl) ⟨1283208, by rfl⟩ : syracuseStep 3421889 = 2566417) B2566417
theorem B2281259 : Blo 2279435 2281259 := bstep (se 1 (by rfl) ⟨1710944, by rfl⟩ : syracuseStep 2281259 = 3421889) B3421889
theorem B4330837 : Blo 2279435 4330837 := bbase (se 14 (by rfl) ⟨396, by rfl⟩ : syracuseStep 4330837 = 793) (by norm_num)
theorem B5774449 : Blo 2279435 5774449 := bstep (se 2 (by rfl) ⟨2165418, by rfl⟩ : syracuseStep 5774449 = 4330837) B4330837
theorem B7699265 : Blo 2279435 7699265 := bstep (se 2 (by rfl) ⟨2887224, by rfl⟩ : syracuseStep 7699265 = 5774449) B5774449
theorem B5132843 : Blo 2279435 5132843 := bstep (se 1 (by rfl) ⟨3849632, by rfl⟩ : syracuseStep 5132843 = 7699265) B7699265
theorem B3421895 : Blo 2279435 3421895 := bstep (se 1 (by rfl) ⟨2566421, by rfl⟩ : syracuseStep 3421895 = 5132843) B5132843
theorem B2281263 : Blo 2279435 2281263 := bstep (se 1 (by rfl) ⟨1710947, by rfl⟩ : syracuseStep 2281263 = 3421895) B3421895
theorem B3421901 : Blo 2279435 3421901 := bbase (se 3 (by rfl) ⟨641606, by rfl⟩ : syracuseStep 3421901 = 1283213) (by norm_num)
theorem B2281267 : Blo 2279435 2281267 := bstep (se 1 (by rfl) ⟨1710950, by rfl⟩ : syracuseStep 2281267 = 3421901) B3421901
theorem B5132861 : Blo 2279435 5132861 := bbase (se 3 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 5132861 = 1924823) (by norm_num)
theorem B3421907 : Blo 2279435 3421907 := bstep (se 1 (by rfl) ⟨2566430, by rfl⟩ : syracuseStep 3421907 = 5132861) B5132861
theorem B2281271 : Blo 2279435 2281271 := bstep (se 1 (by rfl) ⟨1710953, by rfl⟩ : syracuseStep 2281271 = 3421907) B3421907
theorem B3849653 : Blo 2279435 3849653 := bbase (se 5 (by rfl) ⟨180452, by rfl⟩ : syracuseStep 3849653 = 360905) (by norm_num)
theorem B2566435 : Blo 2279435 2566435 := bstep (se 1 (by rfl) ⟨1924826, by rfl⟩ : syracuseStep 2566435 = 3849653) B3849653
theorem B3421913 : Blo 2279435 3421913 := bstep (se 2 (by rfl) ⟨1283217, by rfl⟩ : syracuseStep 3421913 = 2566435) B2566435
theorem B2281275 : Blo 2279435 2281275 := bstep (se 1 (by rfl) ⟨1710956, by rfl⟩ : syracuseStep 2281275 = 3421913) B3421913
theorem B2436113 : Blo 2279435 2436113 := bbase (se 2 (by rfl) ⟨913542, by rfl⟩ : syracuseStep 2436113 = 1827085) (by norm_num)
theorem B6496301 : Blo 2279435 6496301 := bstep (se 3 (by rfl) ⟨1218056, by rfl⟩ : syracuseStep 6496301 = 2436113) B2436113
theorem B17323469 : Blo 2279435 17323469 := bstep (se 3 (by rfl) ⟨3248150, by rfl⟩ : syracuseStep 17323469 = 6496301) B6496301
theorem B11548979 : Blo 2279435 11548979 := bstep (se 1 (by rfl) ⟨8661734, by rfl⟩ : syracuseStep 11548979 = 17323469) B17323469
theorem B7699319 : Blo 2279435 7699319 := bstep (se 1 (by rfl) ⟨5774489, by rfl⟩ : syracuseStep 7699319 = 11548979) B11548979
theorem B5132879 : Blo 2279435 5132879 := bstep (se 1 (by rfl) ⟨3849659, by rfl⟩ : syracuseStep 5132879 = 7699319) B7699319
theorem B3421919 : Blo 2279435 3421919 := bstep (se 1 (by rfl) ⟨2566439, by rfl⟩ : syracuseStep 3421919 = 5132879) B5132879
theorem B2281279 : Blo 2279435 2281279 := bstep (se 1 (by rfl) ⟨1710959, by rfl⟩ : syracuseStep 2281279 = 3421919) B3421919
theorem B3421925 : Blo 2279435 3421925 := bbase (se 4 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 3421925 = 641611) (by norm_num)
theorem B2281283 : Blo 2279435 2281283 := bstep (se 1 (by rfl) ⟨1710962, by rfl⟩ : syracuseStep 2281283 = 3421925) B3421925
theorem B6496325 : Blo 2279435 6496325 := bbase (se 4 (by rfl) ⟨609030, by rfl⟩ : syracuseStep 6496325 = 1218061) (by norm_num)
theorem B4330883 : Blo 2279435 4330883 := bstep (se 1 (by rfl) ⟨3248162, by rfl⟩ : syracuseStep 4330883 = 6496325) B6496325
theorem B2887255 : Blo 2279435 2887255 := bstep (se 1 (by rfl) ⟨2165441, by rfl⟩ : syracuseStep 2887255 = 4330883) B4330883
theorem B3849673 : Blo 2279435 3849673 := bstep (se 2 (by rfl) ⟨1443627, by rfl⟩ : syracuseStep 3849673 = 2887255) B2887255
theorem B5132897 : Blo 2279435 5132897 := bstep (se 2 (by rfl) ⟨1924836, by rfl⟩ : syracuseStep 5132897 = 3849673) B3849673
theorem B3421931 : Blo 2279435 3421931 := bstep (se 1 (by rfl) ⟨2566448, by rfl⟩ : syracuseStep 3421931 = 5132897) B5132897
theorem B2281287 : Blo 2279435 2281287 := bstep (se 1 (by rfl) ⟨1710965, by rfl⟩ : syracuseStep 2281287 = 3421931) B3421931
theorem B2566453 : Blo 2279435 2566453 := bbase (se 5 (by rfl) ⟨120302, by rfl⟩ : syracuseStep 2566453 = 240605) (by norm_num)
theorem B3421937 : Blo 2279435 3421937 := bstep (se 2 (by rfl) ⟨1283226, by rfl⟩ : syracuseStep 3421937 = 2566453) B2566453
theorem B2281291 : Blo 2279435 2281291 := bstep (se 1 (by rfl) ⟨1710968, by rfl⟩ : syracuseStep 2281291 = 3421937) B3421937
theorem B2887265 : Blo 2279435 2887265 := bbase (se 2 (by rfl) ⟨1082724, by rfl⟩ : syracuseStep 2887265 = 2165449) (by norm_num)
theorem B7699373 : Blo 2279435 7699373 := bstep (se 3 (by rfl) ⟨1443632, by rfl⟩ : syracuseStep 7699373 = 2887265) B2887265
theorem B5132915 : Blo 2279435 5132915 := bstep (se 1 (by rfl) ⟨3849686, by rfl⟩ : syracuseStep 5132915 = 7699373) B7699373
theorem B3421943 : Blo 2279435 3421943 := bstep (se 1 (by rfl) ⟨2566457, by rfl⟩ : syracuseStep 3421943 = 5132915) B5132915
theorem B2281295 : Blo 2279435 2281295 := bstep (se 1 (by rfl) ⟨1710971, by rfl⟩ : syracuseStep 2281295 = 3421943) B3421943
theorem B3421949 : Blo 2279435 3421949 := bbase (se 3 (by rfl) ⟨641615, by rfl⟩ : syracuseStep 3421949 = 1283231) (by norm_num)
theorem B2281299 : Blo 2279435 2281299 := bstep (se 1 (by rfl) ⟨1710974, by rfl⟩ : syracuseStep 2281299 = 3421949) B3421949
theorem B5132933 : Blo 2279435 5132933 := bbase (se 4 (by rfl) ⟨481212, by rfl⟩ : syracuseStep 5132933 = 962425) (by norm_num)
theorem B3421955 : Blo 2279435 3421955 := bstep (se 1 (by rfl) ⟨2566466, by rfl⟩ : syracuseStep 3421955 = 5132933) B5132933
theorem B2281303 : Blo 2279435 2281303 := bstep (se 1 (by rfl) ⟨1710977, by rfl⟩ : syracuseStep 2281303 = 3421955) B3421955
theorem B6937301 : Blo 2279435 6937301 := bbase (se 7 (by rfl) ⟨81296, by rfl⟩ : syracuseStep 6937301 = 162593) (by norm_num)
theorem B4624867 : Blo 2279435 4624867 := bstep (se 1 (by rfl) ⟨3468650, by rfl⟩ : syracuseStep 4624867 = 6937301) B6937301
theorem B24665957 : Blo 2279435 24665957 := bstep (se 4 (by rfl) ⟨2312433, by rfl⟩ : syracuseStep 24665957 = 4624867) B4624867
theorem B16443971 : Blo 2279435 16443971 := bstep (se 1 (by rfl) ⟨12332978, by rfl⟩ : syracuseStep 16443971 = 24665957) B24665957
theorem B10962647 : Blo 2279435 10962647 := bstep (se 1 (by rfl) ⟨8221985, by rfl⟩ : syracuseStep 10962647 = 16443971) B16443971
theorem B7308431 : Blo 2279435 7308431 := bstep (se 1 (by rfl) ⟨5481323, by rfl⟩ : syracuseStep 7308431 = 10962647) B10962647
theorem B4872287 : Blo 2279435 4872287 := bstep (se 1 (by rfl) ⟨3654215, by rfl⟩ : syracuseStep 4872287 = 7308431) B7308431
theorem B3248191 : Blo 2279435 3248191 := bstep (se 1 (by rfl) ⟨2436143, by rfl⟩ : syracuseStep 3248191 = 4872287) B4872287
theorem B4330921 : Blo 2279435 4330921 := bstep (se 2 (by rfl) ⟨1624095, by rfl⟩ : syracuseStep 4330921 = 3248191) B3248191
theorem B5774561 : Blo 2279435 5774561 := bstep (se 2 (by rfl) ⟨2165460, by rfl⟩ : syracuseStep 5774561 = 4330921) B4330921
theorem B3849707 : Blo 2279435 3849707 := bstep (se 1 (by rfl) ⟨2887280, by rfl⟩ : syracuseStep 3849707 = 5774561) B5774561
theorem B2566471 : Blo 2279435 2566471 := bstep (se 1 (by rfl) ⟨1924853, by rfl⟩ : syracuseStep 2566471 = 3849707) B3849707
theorem B3421961 : Blo 2279435 3421961 := bstep (se 2 (by rfl) ⟨1283235, by rfl⟩ : syracuseStep 3421961 = 2566471) B2566471
theorem B2281307 : Blo 2279435 2281307 := bstep (se 1 (by rfl) ⟨1710980, by rfl⟩ : syracuseStep 2281307 = 3421961) B3421961
theorem B11549141 : Blo 2279435 11549141 := bbase (se 7 (by rfl) ⟨135341, by rfl⟩ : syracuseStep 11549141 = 270683) (by norm_num)
theorem B7699427 : Blo 2279435 7699427 := bstep (se 1 (by rfl) ⟨5774570, by rfl⟩ : syracuseStep 7699427 = 11549141) B11549141
theorem B5132951 : Blo 2279435 5132951 := bstep (se 1 (by rfl) ⟨3849713, by rfl⟩ : syracuseStep 5132951 = 7699427) B7699427
theorem B3421967 : Blo 2279435 3421967 := bstep (se 1 (by rfl) ⟨2566475, by rfl⟩ : syracuseStep 3421967 = 5132951) B5132951
theorem B2281311 : Blo 2279435 2281311 := bstep (se 1 (by rfl) ⟨1710983, by rfl⟩ : syracuseStep 2281311 = 3421967) B3421967
theorem B3421973 : Blo 2279435 3421973 := bbase (se 6 (by rfl) ⟨80202, by rfl⟩ : syracuseStep 3421973 = 160405) (by norm_num)
theorem B2281315 : Blo 2279435 2281315 := bstep (se 1 (by rfl) ⟨1710986, by rfl⟩ : syracuseStep 2281315 = 3421973) B3421973
theorem B9877573 : Blo 2279435 9877573 := bbase (se 4 (by rfl) ⟨926022, by rfl⟩ : syracuseStep 9877573 = 1852045) (by norm_num)
theorem B13170097 : Blo 2279435 13170097 := bstep (se 2 (by rfl) ⟨4938786, by rfl⟩ : syracuseStep 13170097 = 9877573) B9877573
theorem B70240517 : Blo 2279435 70240517 := bstep (se 4 (by rfl) ⟨6585048, by rfl⟩ : syracuseStep 70240517 = 13170097) B13170097
theorem B46827011 : Blo 2279435 46827011 := bstep (se 1 (by rfl) ⟨35120258, by rfl⟩ : syracuseStep 46827011 = 70240517) B70240517
theorem B124872029 : Blo 2279435 124872029 := bstep (se 3 (by rfl) ⟨23413505, by rfl⟩ : syracuseStep 124872029 = 46827011) B46827011
theorem B83248019 : Blo 2279435 83248019 := bstep (se 1 (by rfl) ⟨62436014, by rfl⟩ : syracuseStep 83248019 = 124872029) B124872029
theorem B55498679 : Blo 2279435 55498679 := bstep (se 1 (by rfl) ⟨41624009, by rfl⟩ : syracuseStep 55498679 = 83248019) B83248019
theorem B36999119 : Blo 2279435 36999119 := bstep (se 1 (by rfl) ⟨27749339, by rfl⟩ : syracuseStep 36999119 = 55498679) B55498679
theorem B98664317 : Blo 2279435 98664317 := bstep (se 3 (by rfl) ⟨18499559, by rfl⟩ : syracuseStep 98664317 = 36999119) B36999119
theorem B65776211 : Blo 2279435 65776211 := bstep (se 1 (by rfl) ⟨49332158, by rfl⟩ : syracuseStep 65776211 = 98664317) B98664317
theorem B43850807 : Blo 2279435 43850807 := bstep (se 1 (by rfl) ⟨32888105, by rfl⟩ : syracuseStep 43850807 = 65776211) B65776211
theorem B29233871 : Blo 2279435 29233871 := bstep (se 1 (by rfl) ⟨21925403, by rfl⟩ : syracuseStep 29233871 = 43850807) B43850807
theorem B19489247 : Blo 2279435 19489247 := bstep (se 1 (by rfl) ⟨14616935, by rfl⟩ : syracuseStep 19489247 = 29233871) B29233871
theorem B12992831 : Blo 2279435 12992831 := bstep (se 1 (by rfl) ⟨9744623, by rfl⟩ : syracuseStep 12992831 = 19489247) B19489247
theorem B8661887 : Blo 2279435 8661887 := bstep (se 1 (by rfl) ⟨6496415, by rfl⟩ : syracuseStep 8661887 = 12992831) B12992831
theorem B5774591 : Blo 2279435 5774591 := bstep (se 1 (by rfl) ⟨4330943, by rfl⟩ : syracuseStep 5774591 = 8661887) B8661887
theorem B3849727 : Blo 2279435 3849727 := bstep (se 1 (by rfl) ⟨2887295, by rfl⟩ : syracuseStep 3849727 = 5774591) B5774591
theorem B5132969 : Blo 2279435 5132969 := bstep (se 2 (by rfl) ⟨1924863, by rfl⟩ : syracuseStep 5132969 = 3849727) B3849727
theorem B3421979 : Blo 2279435 3421979 := bstep (se 1 (by rfl) ⟨2566484, by rfl⟩ : syracuseStep 3421979 = 5132969) B5132969
theorem B2281319 : Blo 2279435 2281319 := bstep (se 1 (by rfl) ⟨1710989, by rfl⟩ : syracuseStep 2281319 = 3421979) B3421979
theorem B2566489 : Blo 2279435 2566489 := bbase (se 2 (by rfl) ⟨962433, by rfl⟩ : syracuseStep 2566489 = 1924867) (by norm_num)
theorem B3421985 : Blo 2279435 3421985 := bstep (se 2 (by rfl) ⟨1283244, by rfl⟩ : syracuseStep 3421985 = 2566489) B2566489
theorem B2281323 : Blo 2279435 2281323 := bstep (se 1 (by rfl) ⟨1710992, by rfl⟩ : syracuseStep 2281323 = 3421985) B3421985
theorem B20812085 : Blo 2279435 20812085 := bbase (se 5 (by rfl) ⟨975566, by rfl⟩ : syracuseStep 20812085 = 1951133) (by norm_num)
theorem B13874723 : Blo 2279435 13874723 := bstep (se 1 (by rfl) ⟨10406042, by rfl⟩ : syracuseStep 13874723 = 20812085) B20812085
theorem B9249815 : Blo 2279435 9249815 := bstep (se 1 (by rfl) ⟨6937361, by rfl⟩ : syracuseStep 9249815 = 13874723) B13874723
theorem B6166543 : Blo 2279435 6166543 := bstep (se 1 (by rfl) ⟨4624907, by rfl⟩ : syracuseStep 6166543 = 9249815) B9249815
theorem B8222057 : Blo 2279435 8222057 := bstep (se 2 (by rfl) ⟨3083271, by rfl⟩ : syracuseStep 8222057 = 6166543) B6166543
theorem B5481371 : Blo 2279435 5481371 := bstep (se 1 (by rfl) ⟨4111028, by rfl⟩ : syracuseStep 5481371 = 8222057) B8222057
theorem B3654247 : Blo 2279435 3654247 := bstep (se 1 (by rfl) ⟨2740685, by rfl⟩ : syracuseStep 3654247 = 5481371) B5481371
theorem B4872329 : Blo 2279435 4872329 := bstep (se 2 (by rfl) ⟨1827123, by rfl⟩ : syracuseStep 4872329 = 3654247) B3654247
theorem B3248219 : Blo 2279435 3248219 := bstep (se 1 (by rfl) ⟨2436164, by rfl⟩ : syracuseStep 3248219 = 4872329) B4872329
theorem B8661917 : Blo 2279435 8661917 := bstep (se 3 (by rfl) ⟨1624109, by rfl⟩ : syracuseStep 8661917 = 3248219) B3248219
theorem B5774611 : Blo 2279435 5774611 := bstep (se 1 (by rfl) ⟨4330958, by rfl⟩ : syracuseStep 5774611 = 8661917) B8661917
theorem B7699481 : Blo 2279435 7699481 := bstep (se 2 (by rfl) ⟨2887305, by rfl⟩ : syracuseStep 7699481 = 5774611) B5774611
theorem B5132987 : Blo 2279435 5132987 := bstep (se 1 (by rfl) ⟨3849740, by rfl⟩ : syracuseStep 5132987 = 7699481) B7699481
theorem B3421991 : Blo 2279435 3421991 := bstep (se 1 (by rfl) ⟨2566493, by rfl⟩ : syracuseStep 3421991 = 5132987) B5132987
theorem B2281327 : Blo 2279435 2281327 := bstep (se 1 (by rfl) ⟨1710995, by rfl⟩ : syracuseStep 2281327 = 3421991) B3421991
theorem B3421997 : Blo 2279435 3421997 := bbase (se 3 (by rfl) ⟨641624, by rfl⟩ : syracuseStep 3421997 = 1283249) (by norm_num)
theorem B2281331 : Blo 2279435 2281331 := bstep (se 1 (by rfl) ⟨1710998, by rfl⟩ : syracuseStep 2281331 = 3421997) B3421997
theorem B5133005 : Blo 2279435 5133005 := bbase (se 3 (by rfl) ⟨962438, by rfl⟩ : syracuseStep 5133005 = 1924877) (by norm_num)
theorem B3422003 : Blo 2279435 3422003 := bstep (se 1 (by rfl) ⟨2566502, by rfl⟩ : syracuseStep 3422003 = 5133005) B5133005
theorem B2281335 : Blo 2279435 2281335 := bstep (se 1 (by rfl) ⟨1711001, by rfl⟩ : syracuseStep 2281335 = 3422003) B3422003
theorem B2887321 : Blo 2279435 2887321 := bbase (se 2 (by rfl) ⟨1082745, by rfl⟩ : syracuseStep 2887321 = 2165491) (by norm_num)
theorem B3849761 : Blo 2279435 3849761 := bstep (se 2 (by rfl) ⟨1443660, by rfl⟩ : syracuseStep 3849761 = 2887321) B2887321
theorem B2566507 : Blo 2279435 2566507 := bstep (se 1 (by rfl) ⟨1924880, by rfl⟩ : syracuseStep 2566507 = 3849761) B3849761
theorem B3422009 : Blo 2279435 3422009 := bstep (se 2 (by rfl) ⟨1283253, by rfl⟩ : syracuseStep 3422009 = 2566507) B2566507
theorem B2281339 : Blo 2279435 2281339 := bstep (se 1 (by rfl) ⟨1711004, by rfl⟩ : syracuseStep 2281339 = 3422009) B3422009
theorem B9744725 : Blo 2279435 9744725 := bbase (se 10 (by rfl) ⟨14274, by rfl⟩ : syracuseStep 9744725 = 28549) (by norm_num)
theorem B25985933 : Blo 2279435 25985933 := bstep (se 3 (by rfl) ⟨4872362, by rfl⟩ : syracuseStep 25985933 = 9744725) B9744725
theorem B17323955 : Blo 2279435 17323955 := bstep (se 1 (by rfl) ⟨12992966, by rfl⟩ : syracuseStep 17323955 = 25985933) B25985933
theorem B11549303 : Blo 2279435 11549303 := bstep (se 1 (by rfl) ⟨8661977, by rfl⟩ : syracuseStep 11549303 = 17323955) B17323955
theorem B7699535 : Blo 2279435 7699535 := bstep (se 1 (by rfl) ⟨5774651, by rfl⟩ : syracuseStep 7699535 = 11549303) B11549303
theorem B5133023 : Blo 2279435 5133023 := bstep (se 1 (by rfl) ⟨3849767, by rfl⟩ : syracuseStep 5133023 = 7699535) B7699535
theorem B3422015 : Blo 2279435 3422015 := bstep (se 1 (by rfl) ⟨2566511, by rfl⟩ : syracuseStep 3422015 = 5133023) B5133023
theorem B2281343 : Blo 2279435 2281343 := bstep (se 1 (by rfl) ⟨1711007, by rfl⟩ : syracuseStep 2281343 = 3422015) B3422015
theorem B3422021 : Blo 2279435 3422021 := bbase (se 4 (by rfl) ⟨320814, by rfl⟩ : syracuseStep 3422021 = 641629) (by norm_num)
theorem B2281347 : Blo 2279435 2281347 := bstep (se 1 (by rfl) ⟨1711010, by rfl⟩ : syracuseStep 2281347 = 3422021) B3422021
theorem B3849781 : Blo 2279435 3849781 := bbase (se 5 (by rfl) ⟨180458, by rfl⟩ : syracuseStep 3849781 = 360917) (by norm_num)
theorem B5133041 : Blo 2279435 5133041 := bstep (se 2 (by rfl) ⟨1924890, by rfl⟩ : syracuseStep 5133041 = 3849781) B3849781
theorem B3422027 : Blo 2279435 3422027 := bstep (se 1 (by rfl) ⟨2566520, by rfl⟩ : syracuseStep 3422027 = 5133041) B5133041
theorem B2281351 : Blo 2279435 2281351 := bstep (se 1 (by rfl) ⟨1711013, by rfl⟩ : syracuseStep 2281351 = 3422027) B3422027
theorem B2566525 : Blo 2279435 2566525 := bbase (se 3 (by rfl) ⟨481223, by rfl⟩ : syracuseStep 2566525 = 962447) (by norm_num)
theorem B3422033 : Blo 2279435 3422033 := bstep (se 2 (by rfl) ⟨1283262, by rfl⟩ : syracuseStep 3422033 = 2566525) B2566525
theorem B2281355 : Blo 2279435 2281355 := bstep (se 1 (by rfl) ⟨1711016, by rfl⟩ : syracuseStep 2281355 = 3422033) B3422033
theorem B7699589 : Blo 2279435 7699589 := bbase (se 4 (by rfl) ⟨721836, by rfl⟩ : syracuseStep 7699589 = 1443673) (by norm_num)
theorem B5133059 : Blo 2279435 5133059 := bstep (se 1 (by rfl) ⟨3849794, by rfl⟩ : syracuseStep 5133059 = 7699589) B7699589
theorem B3422039 : Blo 2279435 3422039 := bstep (se 1 (by rfl) ⟨2566529, by rfl⟩ : syracuseStep 3422039 = 5133059) B5133059
theorem B2281359 : Blo 2279435 2281359 := bstep (se 1 (by rfl) ⟨1711019, by rfl⟩ : syracuseStep 2281359 = 3422039) B3422039
theorem B3422045 : Blo 2279435 3422045 := bbase (se 3 (by rfl) ⟨641633, by rfl⟩ : syracuseStep 3422045 = 1283267) (by norm_num)
theorem B2281363 : Blo 2279435 2281363 := bstep (se 1 (by rfl) ⟨1711022, by rfl⟩ : syracuseStep 2281363 = 3422045) B3422045
theorem B5133077 : Blo 2279435 5133077 := bbase (se 6 (by rfl) ⟨120306, by rfl⟩ : syracuseStep 5133077 = 240613) (by norm_num)
theorem B3422051 : Blo 2279435 3422051 := bstep (se 1 (by rfl) ⟨2566538, by rfl⟩ : syracuseStep 3422051 = 5133077) B5133077
theorem B2281367 : Blo 2279435 2281367 := bstep (se 1 (by rfl) ⟨1711025, by rfl⟩ : syracuseStep 2281367 = 3422051) B3422051
theorem B8662085 : Blo 2279435 8662085 := bbase (se 4 (by rfl) ⟨812070, by rfl⟩ : syracuseStep 8662085 = 1624141) (by norm_num)
theorem B5774723 : Blo 2279435 5774723 := bstep (se 1 (by rfl) ⟨4331042, by rfl⟩ : syracuseStep 5774723 = 8662085) B8662085
theorem B3849815 : Blo 2279435 3849815 := bstep (se 1 (by rfl) ⟨2887361, by rfl⟩ : syracuseStep 3849815 = 5774723) B5774723
theorem B2566543 : Blo 2279435 2566543 := bstep (se 1 (by rfl) ⟨1924907, by rfl⟩ : syracuseStep 2566543 = 3849815) B3849815
theorem B3422057 : Blo 2279435 3422057 := bstep (se 2 (by rfl) ⟨1283271, by rfl⟩ : syracuseStep 3422057 = 2566543) B2566543
theorem B2281371 : Blo 2279435 2281371 := bstep (se 1 (by rfl) ⟨1711028, by rfl⟩ : syracuseStep 2281371 = 3422057) B3422057
theorem B2816041 : Blo 2279435 2816041 := bbase (se 2 (by rfl) ⟨1056015, by rfl⟩ : syracuseStep 2816041 = 2112031) (by norm_num)
theorem B3754721 : Blo 2279435 3754721 := bstep (se 2 (by rfl) ⟨1408020, by rfl⟩ : syracuseStep 3754721 = 2816041) B2816041
theorem B2503147 : Blo 2279435 2503147 := bstep (se 1 (by rfl) ⟨1877360, by rfl⟩ : syracuseStep 2503147 = 3754721) B3754721
theorem B3337529 : Blo 2279435 3337529 := bstep (se 2 (by rfl) ⟨1251573, by rfl⟩ : syracuseStep 3337529 = 2503147) B2503147
theorem B8900077 : Blo 2279435 8900077 := bstep (se 3 (by rfl) ⟨1668764, by rfl⟩ : syracuseStep 8900077 = 3337529) B3337529
theorem B11866769 : Blo 2279435 11866769 := bstep (se 2 (by rfl) ⟨4450038, by rfl⟩ : syracuseStep 11866769 = 8900077) B8900077
theorem B7911179 : Blo 2279435 7911179 := bstep (se 1 (by rfl) ⟨5933384, by rfl⟩ : syracuseStep 7911179 = 11866769) B11866769
theorem B5274119 : Blo 2279435 5274119 := bstep (se 1 (by rfl) ⟨3955589, by rfl⟩ : syracuseStep 5274119 = 7911179) B7911179
theorem B14064317 : Blo 2279435 14064317 := bstep (se 3 (by rfl) ⟨2637059, by rfl⟩ : syracuseStep 14064317 = 5274119) B5274119
theorem B9376211 : Blo 2279435 9376211 := bstep (se 1 (by rfl) ⟨7032158, by rfl⟩ : syracuseStep 9376211 = 14064317) B14064317
theorem B6250807 : Blo 2279435 6250807 := bstep (se 1 (by rfl) ⟨4688105, by rfl⟩ : syracuseStep 6250807 = 9376211) B9376211
theorem B8334409 : Blo 2279435 8334409 := bstep (se 2 (by rfl) ⟨3125403, by rfl⟩ : syracuseStep 8334409 = 6250807) B6250807
theorem B11112545 : Blo 2279435 11112545 := bstep (se 2 (by rfl) ⟨4167204, by rfl⟩ : syracuseStep 11112545 = 8334409) B8334409
theorem B7408363 : Blo 2279435 7408363 := bstep (se 1 (by rfl) ⟨5556272, by rfl⟩ : syracuseStep 7408363 = 11112545) B11112545
theorem B9877817 : Blo 2279435 9877817 := bstep (se 2 (by rfl) ⟨3704181, by rfl⟩ : syracuseStep 9877817 = 7408363) B7408363
theorem B6585211 : Blo 2279435 6585211 := bstep (se 1 (by rfl) ⟨4938908, by rfl⟩ : syracuseStep 6585211 = 9877817) B9877817
theorem B8780281 : Blo 2279435 8780281 := bstep (se 2 (by rfl) ⟨3292605, by rfl⟩ : syracuseStep 8780281 = 6585211) B6585211
theorem B46828165 : Blo 2279435 46828165 := bstep (se 4 (by rfl) ⟨4390140, by rfl⟩ : syracuseStep 46828165 = 8780281) B8780281
theorem B62437553 : Blo 2279435 62437553 := bstep (se 2 (by rfl) ⟨23414082, by rfl⟩ : syracuseStep 62437553 = 46828165) B46828165
theorem B41625035 : Blo 2279435 41625035 := bstep (se 1 (by rfl) ⟨31218776, by rfl⟩ : syracuseStep 41625035 = 62437553) B62437553
theorem B27750023 : Blo 2279435 27750023 := bstep (se 1 (by rfl) ⟨20812517, by rfl⟩ : syracuseStep 27750023 = 41625035) B41625035
theorem B18500015 : Blo 2279435 18500015 := bstep (se 1 (by rfl) ⟨13875011, by rfl⟩ : syracuseStep 18500015 = 27750023) B27750023
theorem B12333343 : Blo 2279435 12333343 := bstep (se 1 (by rfl) ⟨9250007, by rfl⟩ : syracuseStep 12333343 = 18500015) B18500015
theorem B16444457 : Blo 2279435 16444457 := bstep (se 2 (by rfl) ⟨6166671, by rfl⟩ : syracuseStep 16444457 = 12333343) B12333343
theorem B10962971 : Blo 2279435 10962971 := bstep (se 1 (by rfl) ⟨8222228, by rfl⟩ : syracuseStep 10962971 = 16444457) B16444457
theorem B7308647 : Blo 2279435 7308647 := bstep (se 1 (by rfl) ⟨5481485, by rfl⟩ : syracuseStep 7308647 = 10962971) B10962971
theorem B4872431 : Blo 2279435 4872431 := bstep (se 1 (by rfl) ⟨3654323, by rfl⟩ : syracuseStep 4872431 = 7308647) B7308647
theorem B12993149 : Blo 2279435 12993149 := bstep (se 3 (by rfl) ⟨2436215, by rfl⟩ : syracuseStep 12993149 = 4872431) B4872431
theorem B8662099 : Blo 2279435 8662099 := bstep (se 1 (by rfl) ⟨6496574, by rfl⟩ : syracuseStep 8662099 = 12993149) B12993149
theorem B11549465 : Blo 2279435 11549465 := bstep (se 2 (by rfl) ⟨4331049, by rfl⟩ : syracuseStep 11549465 = 8662099) B8662099
theorem B7699643 : Blo 2279435 7699643 := bstep (se 1 (by rfl) ⟨5774732, by rfl⟩ : syracuseStep 7699643 = 11549465) B11549465
theorem B5133095 : Blo 2279435 5133095 := bstep (se 1 (by rfl) ⟨3849821, by rfl⟩ : syracuseStep 5133095 = 7699643) B7699643
theorem B3422063 : Blo 2279435 3422063 := bstep (se 1 (by rfl) ⟨2566547, by rfl⟩ : syracuseStep 3422063 = 5133095) B5133095
theorem B2281375 : Blo 2279435 2281375 := bstep (se 1 (by rfl) ⟨1711031, by rfl⟩ : syracuseStep 2281375 = 3422063) B3422063
theorem B3422069 : Blo 2279435 3422069 := bbase (se 5 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 3422069 = 320819) (by norm_num)
theorem B2281379 : Blo 2279435 2281379 := bstep (se 1 (by rfl) ⟨1711034, by rfl⟩ : syracuseStep 2281379 = 3422069) B3422069
theorem B2740753 : Blo 2279435 2740753 := bbase (se 2 (by rfl) ⟨1027782, by rfl⟩ : syracuseStep 2740753 = 2055565) (by norm_num)
theorem B3654337 : Blo 2279435 3654337 := bstep (se 2 (by rfl) ⟨1370376, by rfl⟩ : syracuseStep 3654337 = 2740753) B2740753
theorem B4872449 : Blo 2279435 4872449 := bstep (se 2 (by rfl) ⟨1827168, by rfl⟩ : syracuseStep 4872449 = 3654337) B3654337
theorem B3248299 : Blo 2279435 3248299 := bstep (se 1 (by rfl) ⟨2436224, by rfl⟩ : syracuseStep 3248299 = 4872449) B4872449
theorem B4331065 : Blo 2279435 4331065 := bstep (se 2 (by rfl) ⟨1624149, by rfl⟩ : syracuseStep 4331065 = 3248299) B3248299
theorem B5774753 : Blo 2279435 5774753 := bstep (se 2 (by rfl) ⟨2165532, by rfl⟩ : syracuseStep 5774753 = 4331065) B4331065
theorem B3849835 : Blo 2279435 3849835 := bstep (se 1 (by rfl) ⟨2887376, by rfl⟩ : syracuseStep 3849835 = 5774753) B5774753
theorem B5133113 : Blo 2279435 5133113 := bstep (se 2 (by rfl) ⟨1924917, by rfl⟩ : syracuseStep 5133113 = 3849835) B3849835
theorem B3422075 : Blo 2279435 3422075 := bstep (se 1 (by rfl) ⟨2566556, by rfl⟩ : syracuseStep 3422075 = 5133113) B5133113
theorem B2281383 : Blo 2279435 2281383 := bstep (se 1 (by rfl) ⟨1711037, by rfl⟩ : syracuseStep 2281383 = 3422075) B3422075
theorem B2566561 : Blo 2279435 2566561 := bbase (se 2 (by rfl) ⟨962460, by rfl⟩ : syracuseStep 2566561 = 1924921) (by norm_num)
theorem B3422081 : Blo 2279435 3422081 := bstep (se 2 (by rfl) ⟨1283280, by rfl⟩ : syracuseStep 3422081 = 2566561) B2566561
theorem B2281387 : Blo 2279435 2281387 := bstep (se 1 (by rfl) ⟨1711040, by rfl⟩ : syracuseStep 2281387 = 3422081) B3422081
theorem B5774773 : Blo 2279435 5774773 := bbase (se 5 (by rfl) ⟨270692, by rfl⟩ : syracuseStep 5774773 = 541385) (by norm_num)
theorem B7699697 : Blo 2279435 7699697 := bstep (se 2 (by rfl) ⟨2887386, by rfl⟩ : syracuseStep 7699697 = 5774773) B5774773
theorem B5133131 : Blo 2279435 5133131 := bstep (se 1 (by rfl) ⟨3849848, by rfl⟩ : syracuseStep 5133131 = 7699697) B7699697
theorem B3422087 : Blo 2279435 3422087 := bstep (se 1 (by rfl) ⟨2566565, by rfl⟩ : syracuseStep 3422087 = 5133131) B5133131
theorem B2281391 : Blo 2279435 2281391 := bstep (se 1 (by rfl) ⟨1711043, by rfl⟩ : syracuseStep 2281391 = 3422087) B3422087
theorem B3422093 : Blo 2279435 3422093 := bbase (se 3 (by rfl) ⟨641642, by rfl⟩ : syracuseStep 3422093 = 1283285) (by norm_num)
theorem B2281395 : Blo 2279435 2281395 := bstep (se 1 (by rfl) ⟨1711046, by rfl⟩ : syracuseStep 2281395 = 3422093) B3422093
theorem B5133149 : Blo 2279435 5133149 := bbase (se 3 (by rfl) ⟨962465, by rfl⟩ : syracuseStep 5133149 = 1924931) (by norm_num)
theorem B3422099 : Blo 2279435 3422099 := bstep (se 1 (by rfl) ⟨2566574, by rfl⟩ : syracuseStep 3422099 = 5133149) B5133149
theorem B2281399 : Blo 2279435 2281399 := bstep (se 1 (by rfl) ⟨1711049, by rfl⟩ : syracuseStep 2281399 = 3422099) B3422099
theorem B3849869 : Blo 2279435 3849869 := bbase (se 3 (by rfl) ⟨721850, by rfl⟩ : syracuseStep 3849869 = 1443701) (by norm_num)
theorem B2566579 : Blo 2279435 2566579 := bstep (se 1 (by rfl) ⟨1924934, by rfl⟩ : syracuseStep 2566579 = 3849869) B3849869
theorem B3422105 : Blo 2279435 3422105 := bstep (se 2 (by rfl) ⟨1283289, by rfl⟩ : syracuseStep 3422105 = 2566579) B2566579
theorem B2281403 : Blo 2279435 2281403 := bstep (se 1 (by rfl) ⟨1711052, by rfl⟩ : syracuseStep 2281403 = 3422105) B3422105
theorem B2740781 : Blo 2279435 2740781 := bbase (se 3 (by rfl) ⟨513896, by rfl⟩ : syracuseStep 2740781 = 1027793) (by norm_num)
theorem B7308749 : Blo 2279435 7308749 := bstep (se 3 (by rfl) ⟨1370390, by rfl⟩ : syracuseStep 7308749 = 2740781) B2740781
theorem B19489997 : Blo 2279435 19489997 := bstep (se 3 (by rfl) ⟨3654374, by rfl⟩ : syracuseStep 19489997 = 7308749) B7308749
theorem B12993331 : Blo 2279435 12993331 := bstep (se 1 (by rfl) ⟨9744998, by rfl⟩ : syracuseStep 12993331 = 19489997) B19489997
theorem B17324441 : Blo 2279435 17324441 := bstep (se 2 (by rfl) ⟨6496665, by rfl⟩ : syracuseStep 17324441 = 12993331) B12993331
theorem B11549627 : Blo 2279435 11549627 := bstep (se 1 (by rfl) ⟨8662220, by rfl⟩ : syracuseStep 11549627 = 17324441) B17324441
theorem B7699751 : Blo 2279435 7699751 := bstep (se 1 (by rfl) ⟨5774813, by rfl⟩ : syracuseStep 7699751 = 11549627) B11549627
theorem B5133167 : Blo 2279435 5133167 := bstep (se 1 (by rfl) ⟨3849875, by rfl⟩ : syracuseStep 5133167 = 7699751) B7699751
theorem B3422111 : Blo 2279435 3422111 := bstep (se 1 (by rfl) ⟨2566583, by rfl⟩ : syracuseStep 3422111 = 5133167) B5133167
theorem B2281407 : Blo 2279435 2281407 := bstep (se 1 (by rfl) ⟨1711055, by rfl⟩ : syracuseStep 2281407 = 3422111) B3422111
theorem B3422117 : Blo 2279435 3422117 := bbase (se 4 (by rfl) ⟨320823, by rfl⟩ : syracuseStep 3422117 = 641647) (by norm_num)
theorem B2281411 : Blo 2279435 2281411 := bstep (se 1 (by rfl) ⟨1711058, by rfl⟩ : syracuseStep 2281411 = 3422117) B3422117
theorem B2887417 : Blo 2279435 2887417 := bbase (se 2 (by rfl) ⟨1082781, by rfl⟩ : syracuseStep 2887417 = 2165563) (by norm_num)
theorem B3849889 : Blo 2279435 3849889 := bstep (se 2 (by rfl) ⟨1443708, by rfl⟩ : syracuseStep 3849889 = 2887417) B2887417
theorem B5133185 : Blo 2279435 5133185 := bstep (se 2 (by rfl) ⟨1924944, by rfl⟩ : syracuseStep 5133185 = 3849889) B3849889
theorem B3422123 : Blo 2279435 3422123 := bstep (se 1 (by rfl) ⟨2566592, by rfl⟩ : syracuseStep 3422123 = 5133185) B5133185
theorem B2281415 : Blo 2279435 2281415 := bstep (se 1 (by rfl) ⟨1711061, by rfl⟩ : syracuseStep 2281415 = 3422123) B3422123
theorem B2566597 : Blo 2279435 2566597 := bbase (se 4 (by rfl) ⟨240618, by rfl⟩ : syracuseStep 2566597 = 481237) (by norm_num)
theorem B3422129 : Blo 2279435 3422129 := bstep (se 2 (by rfl) ⟨1283298, by rfl⟩ : syracuseStep 3422129 = 2566597) B2566597
theorem B2281419 : Blo 2279435 2281419 := bstep (se 1 (by rfl) ⟨1711064, by rfl⟩ : syracuseStep 2281419 = 3422129) B3422129
theorem B4331141 : Blo 2279435 4331141 := bbase (se 4 (by rfl) ⟨406044, by rfl⟩ : syracuseStep 4331141 = 812089) (by norm_num)
theorem B2887427 : Blo 2279435 2887427 := bstep (se 1 (by rfl) ⟨2165570, by rfl⟩ : syracuseStep 2887427 = 4331141) B4331141
theorem B7699805 : Blo 2279435 7699805 := bstep (se 3 (by rfl) ⟨1443713, by rfl⟩ : syracuseStep 7699805 = 2887427) B2887427
theorem B5133203 : Blo 2279435 5133203 := bstep (se 1 (by rfl) ⟨3849902, by rfl⟩ : syracuseStep 5133203 = 7699805) B7699805
theorem B3422135 : Blo 2279435 3422135 := bstep (se 1 (by rfl) ⟨2566601, by rfl⟩ : syracuseStep 3422135 = 5133203) B5133203
theorem B2281423 : Blo 2279435 2281423 := bstep (se 1 (by rfl) ⟨1711067, by rfl⟩ : syracuseStep 2281423 = 3422135) B3422135
theorem B3422141 : Blo 2279435 3422141 := bbase (se 3 (by rfl) ⟨641651, by rfl⟩ : syracuseStep 3422141 = 1283303) (by norm_num)
theorem B2281427 : Blo 2279435 2281427 := bstep (se 1 (by rfl) ⟨1711070, by rfl⟩ : syracuseStep 2281427 = 3422141) B3422141
theorem B5133221 : Blo 2279435 5133221 := bbase (se 4 (by rfl) ⟨481239, by rfl⟩ : syracuseStep 5133221 = 962479) (by norm_num)
theorem B3422147 : Blo 2279435 3422147 := bstep (se 1 (by rfl) ⟨2566610, by rfl⟩ : syracuseStep 3422147 = 5133221) B5133221
theorem B2281431 : Blo 2279435 2281431 := bstep (se 1 (by rfl) ⟨1711073, by rfl⟩ : syracuseStep 2281431 = 3422147) B3422147
theorem B5774885 : Blo 2279435 5774885 := bbase (se 4 (by rfl) ⟨541395, by rfl⟩ : syracuseStep 5774885 = 1082791) (by norm_num)
theorem B3849923 : Blo 2279435 3849923 := bstep (se 1 (by rfl) ⟨2887442, by rfl⟩ : syracuseStep 3849923 = 5774885) B5774885
theorem B2566615 : Blo 2279435 2566615 := bstep (se 1 (by rfl) ⟨1924961, by rfl⟩ : syracuseStep 2566615 = 3849923) B3849923
theorem B3422153 : Blo 2279435 3422153 := bstep (se 2 (by rfl) ⟨1283307, by rfl⟩ : syracuseStep 3422153 = 2566615) B2566615
theorem B2281435 : Blo 2279435 2281435 := bstep (se 1 (by rfl) ⟨1711076, by rfl⟩ : syracuseStep 2281435 = 3422153) B3422153
theorem C0 (j : ℕ) (h1 : 569858 ≤ j) (h2 : j ≤ 570358) : Blo 2279435 (4 * j + 3) := by
  interval_cases j
  · exact B2279435
  · exact B2279439
  · exact B2279443
  · exact B2279447
  · exact B2279451
  · exact B2279455
  · exact B2279459
  · exact B2279463
  · exact B2279467
  · exact B2279471
  · exact B2279475
  · exact B2279479
  · exact B2279483
  · exact B2279487
  · exact B2279491
  · exact B2279495
  · exact B2279499
  · exact B2279503
  · exact B2279507
  · exact B2279511
  · exact B2279515
  · exact B2279519
  · exact B2279523
  · exact B2279527
  · exact B2279531
  · exact B2279535
  · exact B2279539
  · exact B2279543
  · exact B2279547
  · exact B2279551
  · exact B2279555
  · exact B2279559
  · exact B2279563
  · exact B2279567
  · exact B2279571
  · exact B2279575
  · exact B2279579
  · exact B2279583
  · exact B2279587
  · exact B2279591
  · exact B2279595
  · exact B2279599
  · exact B2279603
  · exact B2279607
  · exact B2279611
  · exact B2279615
  · exact B2279619
  · exact B2279623
  · exact B2279627
  · exact B2279631
  · exact B2279635
  · exact B2279639
  · exact B2279643
  · exact B2279647
  · exact B2279651
  · exact B2279655
  · exact B2279659
  · exact B2279663
  · exact B2279667
  · exact B2279671
  · exact B2279675
  · exact B2279679
  · exact B2279683
  · exact B2279687
  · exact B2279691
  · exact B2279695
  · exact B2279699
  · exact B2279703
  · exact B2279707
  · exact B2279711
  · exact B2279715
  · exact B2279719
  · exact B2279723
  · exact B2279727
  · exact B2279731
  · exact B2279735
  · exact B2279739
  · exact B2279743
  · exact B2279747
  · exact B2279751
  · exact B2279755
  · exact B2279759
  · exact B2279763
  · exact B2279767
  · exact B2279771
  · exact B2279775
  · exact B2279779
  · exact B2279783
  · exact B2279787
  · exact B2279791
  · exact B2279795
  · exact B2279799
  · exact B2279803
  · exact B2279807
  · exact B2279811
  · exact B2279815
  · exact B2279819
  · exact B2279823
  · exact B2279827
  · exact B2279831
  · exact B2279835
  · exact B2279839
  · exact B2279843
  · exact B2279847
  · exact B2279851
  · exact B2279855
  · exact B2279859
  · exact B2279863
  · exact B2279867
  · exact B2279871
  · exact B2279875
  · exact B2279879
  · exact B2279883
  · exact B2279887
  · exact B2279891
  · exact B2279895
  · exact B2279899
  · exact B2279903
  · exact B2279907
  · exact B2279911
  · exact B2279915
  · exact B2279919
  · exact B2279923
  · exact B2279927
  · exact B2279931
  · exact B2279935
  · exact B2279939
  · exact B2279943
  · exact B2279947
  · exact B2279951
  · exact B2279955
  · exact B2279959
  · exact B2279963
  · exact B2279967
  · exact B2279971
  · exact B2279975
  · exact B2279979
  · exact B2279983
  · exact B2279987
  · exact B2279991
  · exact B2279995
  · exact B2279999
  · exact B2280003
  · exact B2280007
  · exact B2280011
  · exact B2280015
  · exact B2280019
  · exact B2280023
  · exact B2280027
  · exact B2280031
  · exact B2280035
  · exact B2280039
  · exact B2280043
  · exact B2280047
  · exact B2280051
  · exact B2280055
  · exact B2280059
  · exact B2280063
  · exact B2280067
  · exact B2280071
  · exact B2280075
  · exact B2280079
  · exact B2280083
  · exact B2280087
  · exact B2280091
  · exact B2280095
  · exact B2280099
  · exact B2280103
  · exact B2280107
  · exact B2280111
  · exact B2280115
  · exact B2280119
  · exact B2280123
  · exact B2280127
  · exact B2280131
  · exact B2280135
  · exact B2280139
  · exact B2280143
  · exact B2280147
  · exact B2280151
  · exact B2280155
  · exact B2280159
  · exact B2280163
  · exact B2280167
  · exact B2280171
  · exact B2280175
  · exact B2280179
  · exact B2280183
  · exact B2280187
  · exact B2280191
  · exact B2280195
  · exact B2280199
  · exact B2280203
  · exact B2280207
  · exact B2280211
  · exact B2280215
  · exact B2280219
  · exact B2280223
  · exact B2280227
  · exact B2280231
  · exact B2280235
  · exact B2280239
  · exact B2280243
  · exact B2280247
  · exact B2280251
  · exact B2280255
  · exact B2280259
  · exact B2280263
  · exact B2280267
  · exact B2280271
  · exact B2280275
  · exact B2280279
  · exact B2280283
  · exact B2280287
  · exact B2280291
  · exact B2280295
  · exact B2280299
  · exact B2280303
  · exact B2280307
  · exact B2280311
  · exact B2280315
  · exact B2280319
  · exact B2280323
  · exact B2280327
  · exact B2280331
  · exact B2280335
  · exact B2280339
  · exact B2280343
  · exact B2280347
  · exact B2280351
  · exact B2280355
  · exact B2280359
  · exact B2280363
  · exact B2280367
  · exact B2280371
  · exact B2280375
  · exact B2280379
  · exact B2280383
  · exact B2280387
  · exact B2280391
  · exact B2280395
  · exact B2280399
  · exact B2280403
  · exact B2280407
  · exact B2280411
  · exact B2280415
  · exact B2280419
  · exact B2280423
  · exact B2280427
  · exact B2280431
  · exact B2280435
  · exact B2280439
  · exact B2280443
  · exact B2280447
  · exact B2280451
  · exact B2280455
  · exact B2280459
  · exact B2280463
  · exact B2280467
  · exact B2280471
  · exact B2280475
  · exact B2280479
  · exact B2280483
  · exact B2280487
  · exact B2280491
  · exact B2280495
  · exact B2280499
  · exact B2280503
  · exact B2280507
  · exact B2280511
  · exact B2280515
  · exact B2280519
  · exact B2280523
  · exact B2280527
  · exact B2280531
  · exact B2280535
  · exact B2280539
  · exact B2280543
  · exact B2280547
  · exact B2280551
  · exact B2280555
  · exact B2280559
  · exact B2280563
  · exact B2280567
  · exact B2280571
  · exact B2280575
  · exact B2280579
  · exact B2280583
  · exact B2280587
  · exact B2280591
  · exact B2280595
  · exact B2280599
  · exact B2280603
  · exact B2280607
  · exact B2280611
  · exact B2280615
  · exact B2280619
  · exact B2280623
  · exact B2280627
  · exact B2280631
  · exact B2280635
  · exact B2280639
  · exact B2280643
  · exact B2280647
  · exact B2280651
  · exact B2280655
  · exact B2280659
  · exact B2280663
  · exact B2280667
  · exact B2280671
  · exact B2280675
  · exact B2280679
  · exact B2280683
  · exact B2280687
  · exact B2280691
  · exact B2280695
  · exact B2280699
  · exact B2280703
  · exact B2280707
  · exact B2280711
  · exact B2280715
  · exact B2280719
  · exact B2280723
  · exact B2280727
  · exact B2280731
  · exact B2280735
  · exact B2280739
  · exact B2280743
  · exact B2280747
  · exact B2280751
  · exact B2280755
  · exact B2280759
  · exact B2280763
  · exact B2280767
  · exact B2280771
  · exact B2280775
  · exact B2280779
  · exact B2280783
  · exact B2280787
  · exact B2280791
  · exact B2280795
  · exact B2280799
  · exact B2280803
  · exact B2280807
  · exact B2280811
  · exact B2280815
  · exact B2280819
  · exact B2280823
  · exact B2280827
  · exact B2280831
  · exact B2280835
  · exact B2280839
  · exact B2280843
  · exact B2280847
  · exact B2280851
  · exact B2280855
  · exact B2280859
  · exact B2280863
  · exact B2280867
  · exact B2280871
  · exact B2280875
  · exact B2280879
  · exact B2280883
  · exact B2280887
  · exact B2280891
  · exact B2280895
  · exact B2280899
  · exact B2280903
  · exact B2280907
  · exact B2280911
  · exact B2280915
  · exact B2280919
  · exact B2280923
  · exact B2280927
  · exact B2280931
  · exact B2280935
  · exact B2280939
  · exact B2280943
  · exact B2280947
  · exact B2280951
  · exact B2280955
  · exact B2280959
  · exact B2280963
  · exact B2280967
  · exact B2280971
  · exact B2280975
  · exact B2280979
  · exact B2280983
  · exact B2280987
  · exact B2280991
  · exact B2280995
  · exact B2280999
  · exact B2281003
  · exact B2281007
  · exact B2281011
  · exact B2281015
  · exact B2281019
  · exact B2281023
  · exact B2281027
  · exact B2281031
  · exact B2281035
  · exact B2281039
  · exact B2281043
  · exact B2281047
  · exact B2281051
  · exact B2281055
  · exact B2281059
  · exact B2281063
  · exact B2281067
  · exact B2281071
  · exact B2281075
  · exact B2281079
  · exact B2281083
  · exact B2281087
  · exact B2281091
  · exact B2281095
  · exact B2281099
  · exact B2281103
  · exact B2281107
  · exact B2281111
  · exact B2281115
  · exact B2281119
  · exact B2281123
  · exact B2281127
  · exact B2281131
  · exact B2281135
  · exact B2281139
  · exact B2281143
  · exact B2281147
  · exact B2281151
  · exact B2281155
  · exact B2281159
  · exact B2281163
  · exact B2281167
  · exact B2281171
  · exact B2281175
  · exact B2281179
  · exact B2281183
  · exact B2281187
  · exact B2281191
  · exact B2281195
  · exact B2281199
  · exact B2281203
  · exact B2281207
  · exact B2281211
  · exact B2281215
  · exact B2281219
  · exact B2281223
  · exact B2281227
  · exact B2281231
  · exact B2281235
  · exact B2281239
  · exact B2281243
  · exact B2281247
  · exact B2281251
  · exact B2281255
  · exact B2281259
  · exact B2281263
  · exact B2281267
  · exact B2281271
  · exact B2281275
  · exact B2281279
  · exact B2281283
  · exact B2281287
  · exact B2281291
  · exact B2281295
  · exact B2281299
  · exact B2281303
  · exact B2281307
  · exact B2281311
  · exact B2281315
  · exact B2281319
  · exact B2281323
  · exact B2281327
  · exact B2281331
  · exact B2281335
  · exact B2281339
  · exact B2281343
  · exact B2281347
  · exact B2281351
  · exact B2281355
  · exact B2281359
  · exact B2281363
  · exact B2281367
  · exact B2281371
  · exact B2281375
  · exact B2281379
  · exact B2281383
  · exact B2281387
  · exact B2281391
  · exact B2281395
  · exact B2281399
  · exact B2281403
  · exact B2281407
  · exact B2281411
  · exact B2281415
  · exact B2281419
  · exact B2281423
  · exact B2281427
  · exact B2281431
  · exact B2281435
theorem solution (m : ℕ) (hlo : 2279435 ≤ m) (hhi : m ≤ 2281435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 569858 ≤ j := by omega
    have hj2 : j ≤ 570358 := by omega
    have hb : Blo 2279435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
