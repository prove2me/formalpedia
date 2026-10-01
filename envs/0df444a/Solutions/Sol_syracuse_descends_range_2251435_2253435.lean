-- Prove2me | solution 1 for syracuse_descends_range_2251435_2253435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:08.418231+00:00
-- url     : https://prove2.me/submissions/18be0dc3-3492-44a7-87af-2675edc4c84c

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

theorem B2532865 : Blo 2251435 2532865 := bbase (se 2 (by rfl) ⟨949824, by rfl⟩ : syracuseStep 2532865 = 1899649) (by norm_num)
theorem B3377153 : Blo 2251435 3377153 := bstep (se 2 (by rfl) ⟨1266432, by rfl⟩ : syracuseStep 3377153 = 2532865) B2532865
theorem B2251435 : Blo 2251435 2251435 := bstep (se 1 (by rfl) ⟨1688576, by rfl⟩ : syracuseStep 2251435 = 3377153) B3377153
theorem B5698957 : Blo 2251435 5698957 := bbase (se 3 (by rfl) ⟨1068554, by rfl⟩ : syracuseStep 5698957 = 2137109) (by norm_num)
theorem B7598609 : Blo 2251435 7598609 := bstep (se 2 (by rfl) ⟨2849478, by rfl⟩ : syracuseStep 7598609 = 5698957) B5698957
theorem B5065739 : Blo 2251435 5065739 := bstep (se 1 (by rfl) ⟨3799304, by rfl⟩ : syracuseStep 5065739 = 7598609) B7598609
theorem B3377159 : Blo 2251435 3377159 := bstep (se 1 (by rfl) ⟨2532869, by rfl⟩ : syracuseStep 3377159 = 5065739) B5065739
theorem B2251439 : Blo 2251435 2251439 := bstep (se 1 (by rfl) ⟨1688579, by rfl⟩ : syracuseStep 2251439 = 3377159) B3377159
theorem B3377165 : Blo 2251435 3377165 := bbase (se 3 (by rfl) ⟨633218, by rfl⟩ : syracuseStep 3377165 = 1266437) (by norm_num)
theorem B2251443 : Blo 2251435 2251443 := bstep (se 1 (by rfl) ⟨1688582, by rfl⟩ : syracuseStep 2251443 = 3377165) B3377165
theorem B5065757 : Blo 2251435 5065757 := bbase (se 3 (by rfl) ⟨949829, by rfl⟩ : syracuseStep 5065757 = 1899659) (by norm_num)
theorem B3377171 : Blo 2251435 3377171 := bstep (se 1 (by rfl) ⟨2532878, by rfl⟩ : syracuseStep 3377171 = 5065757) B5065757
theorem B2251447 : Blo 2251435 2251447 := bstep (se 1 (by rfl) ⟨1688585, by rfl⟩ : syracuseStep 2251447 = 3377171) B3377171
theorem B3799325 : Blo 2251435 3799325 := bbase (se 3 (by rfl) ⟨712373, by rfl⟩ : syracuseStep 3799325 = 1424747) (by norm_num)
theorem B2532883 : Blo 2251435 2532883 := bstep (se 1 (by rfl) ⟨1899662, by rfl⟩ : syracuseStep 2532883 = 3799325) B3799325
theorem B3377177 : Blo 2251435 3377177 := bstep (se 2 (by rfl) ⟨1266441, by rfl⟩ : syracuseStep 3377177 = 2532883) B2532883
theorem B2251451 : Blo 2251435 2251451 := bstep (se 1 (by rfl) ⟨1688588, by rfl⟩ : syracuseStep 2251451 = 3377177) B3377177
theorem B14425589 : Blo 2251435 14425589 := bbase (se 5 (by rfl) ⟨676199, by rfl⟩ : syracuseStep 14425589 = 1352399) (by norm_num)
theorem B9617059 : Blo 2251435 9617059 := bstep (se 1 (by rfl) ⟨7212794, by rfl⟩ : syracuseStep 9617059 = 14425589) B14425589
theorem B12822745 : Blo 2251435 12822745 := bstep (se 2 (by rfl) ⟨4808529, by rfl⟩ : syracuseStep 12822745 = 9617059) B9617059
theorem B17096993 : Blo 2251435 17096993 := bstep (se 2 (by rfl) ⟨6411372, by rfl⟩ : syracuseStep 17096993 = 12822745) B12822745
theorem B11397995 : Blo 2251435 11397995 := bstep (se 1 (by rfl) ⟨8548496, by rfl⟩ : syracuseStep 11397995 = 17096993) B17096993
theorem B7598663 : Blo 2251435 7598663 := bstep (se 1 (by rfl) ⟨5698997, by rfl⟩ : syracuseStep 7598663 = 11397995) B11397995
theorem B5065775 : Blo 2251435 5065775 := bstep (se 1 (by rfl) ⟨3799331, by rfl⟩ : syracuseStep 5065775 = 7598663) B7598663
theorem B3377183 : Blo 2251435 3377183 := bstep (se 1 (by rfl) ⟨2532887, by rfl⟩ : syracuseStep 3377183 = 5065775) B5065775
theorem B2251455 : Blo 2251435 2251455 := bstep (se 1 (by rfl) ⟨1688591, by rfl⟩ : syracuseStep 2251455 = 3377183) B3377183
theorem B3377189 : Blo 2251435 3377189 := bbase (se 4 (by rfl) ⟨316611, by rfl⟩ : syracuseStep 3377189 = 633223) (by norm_num)
theorem B2251459 : Blo 2251435 2251459 := bstep (se 1 (by rfl) ⟨1688594, by rfl⟩ : syracuseStep 2251459 = 3377189) B3377189
theorem B2849509 : Blo 2251435 2849509 := bbase (se 4 (by rfl) ⟨267141, by rfl⟩ : syracuseStep 2849509 = 534283) (by norm_num)
theorem B3799345 : Blo 2251435 3799345 := bstep (se 2 (by rfl) ⟨1424754, by rfl⟩ : syracuseStep 3799345 = 2849509) B2849509
theorem B5065793 : Blo 2251435 5065793 := bstep (se 2 (by rfl) ⟨1899672, by rfl⟩ : syracuseStep 5065793 = 3799345) B3799345
theorem B3377195 : Blo 2251435 3377195 := bstep (se 1 (by rfl) ⟨2532896, by rfl⟩ : syracuseStep 3377195 = 5065793) B5065793
theorem B2251463 : Blo 2251435 2251463 := bstep (se 1 (by rfl) ⟨1688597, by rfl⟩ : syracuseStep 2251463 = 3377195) B3377195
theorem B2532901 : Blo 2251435 2532901 := bbase (se 4 (by rfl) ⟨237459, by rfl⟩ : syracuseStep 2532901 = 474919) (by norm_num)
theorem B3377201 : Blo 2251435 3377201 := bstep (se 2 (by rfl) ⟨1266450, by rfl⟩ : syracuseStep 3377201 = 2532901) B2532901
theorem B2251467 : Blo 2251435 2251467 := bstep (se 1 (by rfl) ⟨1688600, by rfl⟩ : syracuseStep 2251467 = 3377201) B3377201
theorem B13693141 : Blo 2251435 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B18257521 : Blo 2251435 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B24343361 : Blo 2251435 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B16228907 : Blo 2251435 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B10819271 : Blo 2251435 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B7212847 : Blo 2251435 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B9617129 : Blo 2251435 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B6411419 : Blo 2251435 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B4274279 : Blo 2251435 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B2849519 : Blo 2251435 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B7598717 : Blo 2251435 7598717 := bstep (se 3 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 7598717 = 2849519) B2849519
theorem B5065811 : Blo 2251435 5065811 := bstep (se 1 (by rfl) ⟨3799358, by rfl⟩ : syracuseStep 5065811 = 7598717) B7598717
theorem B3377207 : Blo 2251435 3377207 := bstep (se 1 (by rfl) ⟨2532905, by rfl⟩ : syracuseStep 3377207 = 5065811) B5065811
theorem B2251471 : Blo 2251435 2251471 := bstep (se 1 (by rfl) ⟨1688603, by rfl⟩ : syracuseStep 2251471 = 3377207) B3377207
theorem B3377213 : Blo 2251435 3377213 := bbase (se 3 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 3377213 = 1266455) (by norm_num)
theorem B2251475 : Blo 2251435 2251475 := bstep (se 1 (by rfl) ⟨1688606, by rfl⟩ : syracuseStep 2251475 = 3377213) B3377213
theorem B5065829 : Blo 2251435 5065829 := bbase (se 4 (by rfl) ⟨474921, by rfl⟩ : syracuseStep 5065829 = 949843) (by norm_num)
theorem B3377219 : Blo 2251435 3377219 := bstep (se 1 (by rfl) ⟨2532914, by rfl⟩ : syracuseStep 3377219 = 5065829) B5065829
theorem B2251479 : Blo 2251435 2251479 := bstep (se 1 (by rfl) ⟨1688609, by rfl⟩ : syracuseStep 2251479 = 3377219) B3377219
theorem B5699069 : Blo 2251435 5699069 := bbase (se 3 (by rfl) ⟨1068575, by rfl⟩ : syracuseStep 5699069 = 2137151) (by norm_num)
theorem B3799379 : Blo 2251435 3799379 := bstep (se 1 (by rfl) ⟨2849534, by rfl⟩ : syracuseStep 3799379 = 5699069) B5699069
theorem B2532919 : Blo 2251435 2532919 := bstep (se 1 (by rfl) ⟨1899689, by rfl⟩ : syracuseStep 2532919 = 3799379) B3799379
theorem B3377225 : Blo 2251435 3377225 := bstep (se 2 (by rfl) ⟨1266459, by rfl⟩ : syracuseStep 3377225 = 2532919) B2532919
theorem B2251483 : Blo 2251435 2251483 := bstep (se 1 (by rfl) ⟨1688612, by rfl⟩ : syracuseStep 2251483 = 3377225) B3377225
theorem B4274309 : Blo 2251435 4274309 := bbase (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) (by norm_num)
theorem B11398157 : Blo 2251435 11398157 := bstep (se 3 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 11398157 = 4274309) B4274309
theorem B7598771 : Blo 2251435 7598771 := bstep (se 1 (by rfl) ⟨5699078, by rfl⟩ : syracuseStep 7598771 = 11398157) B11398157
theorem B5065847 : Blo 2251435 5065847 := bstep (se 1 (by rfl) ⟨3799385, by rfl⟩ : syracuseStep 5065847 = 7598771) B7598771
theorem B3377231 : Blo 2251435 3377231 := bstep (se 1 (by rfl) ⟨2532923, by rfl⟩ : syracuseStep 3377231 = 5065847) B5065847
theorem B2251487 : Blo 2251435 2251487 := bstep (se 1 (by rfl) ⟨1688615, by rfl⟩ : syracuseStep 2251487 = 3377231) B3377231
theorem B3377237 : Blo 2251435 3377237 := bbase (se 8 (by rfl) ⟨19788, by rfl⟩ : syracuseStep 3377237 = 39577) (by norm_num)
theorem B2251491 : Blo 2251435 2251491 := bstep (se 1 (by rfl) ⟨1688618, by rfl⟩ : syracuseStep 2251491 = 3377237) B3377237
theorem B3851237 : Blo 2251435 3851237 := bbase (se 4 (by rfl) ⟨361053, by rfl⟩ : syracuseStep 3851237 = 722107) (by norm_num)
theorem B10269965 : Blo 2251435 10269965 := bstep (se 3 (by rfl) ⟨1925618, by rfl⟩ : syracuseStep 10269965 = 3851237) B3851237
theorem B6846643 : Blo 2251435 6846643 := bstep (se 1 (by rfl) ⟨5134982, by rfl⟩ : syracuseStep 6846643 = 10269965) B10269965
theorem B9128857 : Blo 2251435 9128857 := bstep (se 2 (by rfl) ⟨3423321, by rfl⟩ : syracuseStep 9128857 = 6846643) B6846643
theorem B12171809 : Blo 2251435 12171809 := bstep (se 2 (by rfl) ⟨4564428, by rfl⟩ : syracuseStep 12171809 = 9128857) B9128857
theorem B32458157 : Blo 2251435 32458157 := bstep (se 3 (by rfl) ⟨6085904, by rfl⟩ : syracuseStep 32458157 = 12171809) B12171809
theorem B21638771 : Blo 2251435 21638771 := bstep (se 1 (by rfl) ⟨16229078, by rfl⟩ : syracuseStep 21638771 = 32458157) B32458157
theorem B14425847 : Blo 2251435 14425847 := bstep (se 1 (by rfl) ⟨10819385, by rfl⟩ : syracuseStep 14425847 = 21638771) B21638771
theorem B9617231 : Blo 2251435 9617231 := bstep (se 1 (by rfl) ⟨7212923, by rfl⟩ : syracuseStep 9617231 = 14425847) B14425847
theorem B6411487 : Blo 2251435 6411487 := bstep (se 1 (by rfl) ⟨4808615, by rfl⟩ : syracuseStep 6411487 = 9617231) B9617231
theorem B8548649 : Blo 2251435 8548649 := bstep (se 2 (by rfl) ⟨3205743, by rfl⟩ : syracuseStep 8548649 = 6411487) B6411487
theorem B5699099 : Blo 2251435 5699099 := bstep (se 1 (by rfl) ⟨4274324, by rfl⟩ : syracuseStep 5699099 = 8548649) B8548649
theorem B3799399 : Blo 2251435 3799399 := bstep (se 1 (by rfl) ⟨2849549, by rfl⟩ : syracuseStep 3799399 = 5699099) B5699099
theorem B5065865 : Blo 2251435 5065865 := bstep (se 2 (by rfl) ⟨1899699, by rfl⟩ : syracuseStep 5065865 = 3799399) B3799399
theorem B3377243 : Blo 2251435 3377243 := bstep (se 1 (by rfl) ⟨2532932, by rfl⟩ : syracuseStep 3377243 = 5065865) B5065865
theorem B2251495 : Blo 2251435 2251495 := bstep (se 1 (by rfl) ⟨1688621, by rfl⟩ : syracuseStep 2251495 = 3377243) B3377243
theorem B2532937 : Blo 2251435 2532937 := bbase (se 2 (by rfl) ⟨949851, by rfl⟩ : syracuseStep 2532937 = 1899703) (by norm_num)
theorem B3377249 : Blo 2251435 3377249 := bstep (se 2 (by rfl) ⟨1266468, by rfl⟩ : syracuseStep 3377249 = 2532937) B2532937
theorem B2251499 : Blo 2251435 2251499 := bstep (se 1 (by rfl) ⟨1688624, by rfl⟩ : syracuseStep 2251499 = 3377249) B3377249
theorem B54773333 : Blo 2251435 54773333 := bbase (se 8 (by rfl) ⟨320937, by rfl⟩ : syracuseStep 54773333 = 641875) (by norm_num)
theorem B36515555 : Blo 2251435 36515555 := bstep (se 1 (by rfl) ⟨27386666, by rfl⟩ : syracuseStep 36515555 = 54773333) B54773333
theorem B24343703 : Blo 2251435 24343703 := bstep (se 1 (by rfl) ⟨18257777, by rfl⟩ : syracuseStep 24343703 = 36515555) B36515555
theorem B16229135 : Blo 2251435 16229135 := bstep (se 1 (by rfl) ⟨12171851, by rfl⟩ : syracuseStep 16229135 = 24343703) B24343703
theorem B10819423 : Blo 2251435 10819423 := bstep (se 1 (by rfl) ⟨8114567, by rfl⟩ : syracuseStep 10819423 = 16229135) B16229135
theorem B14425897 : Blo 2251435 14425897 := bstep (se 2 (by rfl) ⟨5409711, by rfl⟩ : syracuseStep 14425897 = 10819423) B10819423
theorem B19234529 : Blo 2251435 19234529 := bstep (se 2 (by rfl) ⟨7212948, by rfl⟩ : syracuseStep 19234529 = 14425897) B14425897
theorem B12823019 : Blo 2251435 12823019 := bstep (se 1 (by rfl) ⟨9617264, by rfl⟩ : syracuseStep 12823019 = 19234529) B19234529
theorem B8548679 : Blo 2251435 8548679 := bstep (se 1 (by rfl) ⟨6411509, by rfl⟩ : syracuseStep 8548679 = 12823019) B12823019
theorem B5699119 : Blo 2251435 5699119 := bstep (se 1 (by rfl) ⟨4274339, by rfl⟩ : syracuseStep 5699119 = 8548679) B8548679
theorem B7598825 : Blo 2251435 7598825 := bstep (se 2 (by rfl) ⟨2849559, by rfl⟩ : syracuseStep 7598825 = 5699119) B5699119
theorem B5065883 : Blo 2251435 5065883 := bstep (se 1 (by rfl) ⟨3799412, by rfl⟩ : syracuseStep 5065883 = 7598825) B7598825
theorem B3377255 : Blo 2251435 3377255 := bstep (se 1 (by rfl) ⟨2532941, by rfl⟩ : syracuseStep 3377255 = 5065883) B5065883
theorem B2251503 : Blo 2251435 2251503 := bstep (se 1 (by rfl) ⟨1688627, by rfl⟩ : syracuseStep 2251503 = 3377255) B3377255
theorem B3377261 : Blo 2251435 3377261 := bbase (se 3 (by rfl) ⟨633236, by rfl⟩ : syracuseStep 3377261 = 1266473) (by norm_num)
theorem B2251507 : Blo 2251435 2251507 := bstep (se 1 (by rfl) ⟨1688630, by rfl⟩ : syracuseStep 2251507 = 3377261) B3377261
theorem B5065901 : Blo 2251435 5065901 := bbase (se 3 (by rfl) ⟨949856, by rfl⟩ : syracuseStep 5065901 = 1899713) (by norm_num)
theorem B3377267 : Blo 2251435 3377267 := bstep (se 1 (by rfl) ⟨2532950, by rfl⟩ : syracuseStep 3377267 = 5065901) B5065901
theorem B2251511 : Blo 2251435 2251511 := bstep (se 1 (by rfl) ⟨1688633, by rfl⟩ : syracuseStep 2251511 = 3377267) B3377267
theorem B4874269 : Blo 2251435 4874269 := bbase (se 3 (by rfl) ⟨913925, by rfl⟩ : syracuseStep 4874269 = 1827851) (by norm_num)
theorem B6499025 : Blo 2251435 6499025 := bstep (se 2 (by rfl) ⟨2437134, by rfl⟩ : syracuseStep 6499025 = 4874269) B4874269
theorem B4332683 : Blo 2251435 4332683 := bstep (se 1 (by rfl) ⟨3249512, by rfl⟩ : syracuseStep 4332683 = 6499025) B6499025
theorem B2888455 : Blo 2251435 2888455 := bstep (se 1 (by rfl) ⟨2166341, by rfl⟩ : syracuseStep 2888455 = 4332683) B4332683
theorem B3851273 : Blo 2251435 3851273 := bstep (se 2 (by rfl) ⟨1444227, by rfl⟩ : syracuseStep 3851273 = 2888455) B2888455
theorem B10270061 : Blo 2251435 10270061 := bstep (se 3 (by rfl) ⟨1925636, by rfl⟩ : syracuseStep 10270061 = 3851273) B3851273
theorem B6846707 : Blo 2251435 6846707 := bstep (se 1 (by rfl) ⟨5135030, by rfl⟩ : syracuseStep 6846707 = 10270061) B10270061
theorem B4564471 : Blo 2251435 4564471 := bstep (se 1 (by rfl) ⟨3423353, by rfl⟩ : syracuseStep 4564471 = 6846707) B6846707
theorem B6085961 : Blo 2251435 6085961 := bstep (se 2 (by rfl) ⟨2282235, by rfl⟩ : syracuseStep 6085961 = 4564471) B4564471
theorem B4057307 : Blo 2251435 4057307 := bstep (se 1 (by rfl) ⟨3042980, by rfl⟩ : syracuseStep 4057307 = 6085961) B6085961
theorem B2704871 : Blo 2251435 2704871 := bstep (se 1 (by rfl) ⟨2028653, by rfl⟩ : syracuseStep 2704871 = 4057307) B4057307
theorem B7212989 : Blo 2251435 7212989 := bstep (se 3 (by rfl) ⟨1352435, by rfl⟩ : syracuseStep 7212989 = 2704871) B2704871
theorem B4808659 : Blo 2251435 4808659 := bstep (se 1 (by rfl) ⟨3606494, by rfl⟩ : syracuseStep 4808659 = 7212989) B7212989
theorem B6411545 : Blo 2251435 6411545 := bstep (se 2 (by rfl) ⟨2404329, by rfl⟩ : syracuseStep 6411545 = 4808659) B4808659
theorem B4274363 : Blo 2251435 4274363 := bstep (se 1 (by rfl) ⟨3205772, by rfl⟩ : syracuseStep 4274363 = 6411545) B6411545
theorem B2849575 : Blo 2251435 2849575 := bstep (se 1 (by rfl) ⟨2137181, by rfl⟩ : syracuseStep 2849575 = 4274363) B4274363
theorem B3799433 : Blo 2251435 3799433 := bstep (se 2 (by rfl) ⟨1424787, by rfl⟩ : syracuseStep 3799433 = 2849575) B2849575
theorem B2532955 : Blo 2251435 2532955 := bstep (se 1 (by rfl) ⟨1899716, by rfl⟩ : syracuseStep 2532955 = 3799433) B3799433
theorem B3377273 : Blo 2251435 3377273 := bstep (se 2 (by rfl) ⟨1266477, by rfl⟩ : syracuseStep 3377273 = 2532955) B2532955
theorem B2251515 : Blo 2251435 2251515 := bstep (se 1 (by rfl) ⟨1688636, by rfl⟩ : syracuseStep 2251515 = 3377273) B3377273
theorem B23742517 : Blo 2251435 23742517 := bbase (se 5 (by rfl) ⟨1112930, by rfl⟩ : syracuseStep 23742517 = 2225861) (by norm_num)
theorem B31656689 : Blo 2251435 31656689 := bstep (se 2 (by rfl) ⟨11871258, by rfl⟩ : syracuseStep 31656689 = 23742517) B23742517
theorem B21104459 : Blo 2251435 21104459 := bstep (se 1 (by rfl) ⟨15828344, by rfl⟩ : syracuseStep 21104459 = 31656689) B31656689
theorem B14069639 : Blo 2251435 14069639 := bstep (se 1 (by rfl) ⟨10552229, by rfl⟩ : syracuseStep 14069639 = 21104459) B21104459
theorem B9379759 : Blo 2251435 9379759 := bstep (se 1 (by rfl) ⟨7034819, by rfl⟩ : syracuseStep 9379759 = 14069639) B14069639
theorem B12506345 : Blo 2251435 12506345 := bstep (se 2 (by rfl) ⟨4689879, by rfl⟩ : syracuseStep 12506345 = 9379759) B9379759
theorem B8337563 : Blo 2251435 8337563 := bstep (se 1 (by rfl) ⟨6253172, by rfl⟩ : syracuseStep 8337563 = 12506345) B12506345
theorem B5558375 : Blo 2251435 5558375 := bstep (se 1 (by rfl) ⟨4168781, by rfl⟩ : syracuseStep 5558375 = 8337563) B8337563
theorem B3705583 : Blo 2251435 3705583 := bstep (se 1 (by rfl) ⟨2779187, by rfl⟩ : syracuseStep 3705583 = 5558375) B5558375
theorem B4940777 : Blo 2251435 4940777 := bstep (se 2 (by rfl) ⟨1852791, by rfl⟩ : syracuseStep 4940777 = 3705583) B3705583
theorem B13175405 : Blo 2251435 13175405 := bstep (se 3 (by rfl) ⟨2470388, by rfl⟩ : syracuseStep 13175405 = 4940777) B4940777
theorem B8783603 : Blo 2251435 8783603 := bstep (se 1 (by rfl) ⟨6587702, by rfl⟩ : syracuseStep 8783603 = 13175405) B13175405
theorem B5855735 : Blo 2251435 5855735 := bstep (se 1 (by rfl) ⟨4391801, by rfl⟩ : syracuseStep 5855735 = 8783603) B8783603
theorem B3903823 : Blo 2251435 3903823 := bstep (se 1 (by rfl) ⟨2927867, by rfl⟩ : syracuseStep 3903823 = 5855735) B5855735
theorem B5205097 : Blo 2251435 5205097 := bstep (se 2 (by rfl) ⟨1951911, by rfl⟩ : syracuseStep 5205097 = 3903823) B3903823
theorem B6940129 : Blo 2251435 6940129 := bstep (se 2 (by rfl) ⟨2602548, by rfl⟩ : syracuseStep 6940129 = 5205097) B5205097
theorem B9253505 : Blo 2251435 9253505 := bstep (se 2 (by rfl) ⟨3470064, by rfl⟩ : syracuseStep 9253505 = 6940129) B6940129
theorem B6169003 : Blo 2251435 6169003 := bstep (se 1 (by rfl) ⟨4626752, by rfl⟩ : syracuseStep 6169003 = 9253505) B9253505
theorem B32901349 : Blo 2251435 32901349 := bstep (se 4 (by rfl) ⟨3084501, by rfl⟩ : syracuseStep 32901349 = 6169003) B6169003
theorem B43868465 : Blo 2251435 43868465 := bstep (se 2 (by rfl) ⟨16450674, by rfl⟩ : syracuseStep 43868465 = 32901349) B32901349
theorem B29245643 : Blo 2251435 29245643 := bstep (se 1 (by rfl) ⟨21934232, by rfl⟩ : syracuseStep 29245643 = 43868465) B43868465
theorem B19497095 : Blo 2251435 19497095 := bstep (se 1 (by rfl) ⟨14622821, by rfl⟩ : syracuseStep 19497095 = 29245643) B29245643
theorem B12998063 : Blo 2251435 12998063 := bstep (se 1 (by rfl) ⟨9748547, by rfl⟩ : syracuseStep 12998063 = 19497095) B19497095
theorem B8665375 : Blo 2251435 8665375 := bstep (se 1 (by rfl) ⟨6499031, by rfl⟩ : syracuseStep 8665375 = 12998063) B12998063
theorem B11553833 : Blo 2251435 11553833 := bstep (se 2 (by rfl) ⟨4332687, by rfl⟩ : syracuseStep 11553833 = 8665375) B8665375
theorem B7702555 : Blo 2251435 7702555 := bstep (se 1 (by rfl) ⟨5776916, by rfl⟩ : syracuseStep 7702555 = 11553833) B11553833
theorem B10270073 : Blo 2251435 10270073 := bstep (se 2 (by rfl) ⟨3851277, by rfl⟩ : syracuseStep 10270073 = 7702555) B7702555
theorem B6846715 : Blo 2251435 6846715 := bstep (se 1 (by rfl) ⟨5135036, by rfl⟩ : syracuseStep 6846715 = 10270073) B10270073
theorem B9128953 : Blo 2251435 9128953 := bstep (se 2 (by rfl) ⟨3423357, by rfl⟩ : syracuseStep 9128953 = 6846715) B6846715
theorem B12171937 : Blo 2251435 12171937 := bstep (se 2 (by rfl) ⟨4564476, by rfl⟩ : syracuseStep 12171937 = 9128953) B9128953
theorem B16229249 : Blo 2251435 16229249 := bstep (se 2 (by rfl) ⟨6085968, by rfl⟩ : syracuseStep 16229249 = 12171937) B12171937
theorem B10819499 : Blo 2251435 10819499 := bstep (se 1 (by rfl) ⟨8114624, by rfl⟩ : syracuseStep 10819499 = 16229249) B16229249
theorem B28851997 : Blo 2251435 28851997 := bstep (se 3 (by rfl) ⟨5409749, by rfl⟩ : syracuseStep 28851997 = 10819499) B10819499
theorem B38469329 : Blo 2251435 38469329 := bstep (se 2 (by rfl) ⟨14425998, by rfl⟩ : syracuseStep 38469329 = 28851997) B28851997
theorem B25646219 : Blo 2251435 25646219 := bstep (se 1 (by rfl) ⟨19234664, by rfl⟩ : syracuseStep 25646219 = 38469329) B38469329
theorem B17097479 : Blo 2251435 17097479 := bstep (se 1 (by rfl) ⟨12823109, by rfl⟩ : syracuseStep 17097479 = 25646219) B25646219
theorem B11398319 : Blo 2251435 11398319 := bstep (se 1 (by rfl) ⟨8548739, by rfl⟩ : syracuseStep 11398319 = 17097479) B17097479
theorem B7598879 : Blo 2251435 7598879 := bstep (se 1 (by rfl) ⟨5699159, by rfl⟩ : syracuseStep 7598879 = 11398319) B11398319
theorem B5065919 : Blo 2251435 5065919 := bstep (se 1 (by rfl) ⟨3799439, by rfl⟩ : syracuseStep 5065919 = 7598879) B7598879
theorem B3377279 : Blo 2251435 3377279 := bstep (se 1 (by rfl) ⟨2532959, by rfl⟩ : syracuseStep 3377279 = 5065919) B5065919
theorem B2251519 : Blo 2251435 2251519 := bstep (se 1 (by rfl) ⟨1688639, by rfl⟩ : syracuseStep 2251519 = 3377279) B3377279
theorem B3377285 : Blo 2251435 3377285 := bbase (se 4 (by rfl) ⟨316620, by rfl⟩ : syracuseStep 3377285 = 633241) (by norm_num)
theorem B2251523 : Blo 2251435 2251523 := bstep (se 1 (by rfl) ⟨1688642, by rfl⟩ : syracuseStep 2251523 = 3377285) B3377285
theorem B3799453 : Blo 2251435 3799453 := bbase (se 3 (by rfl) ⟨712397, by rfl⟩ : syracuseStep 3799453 = 1424795) (by norm_num)
theorem B5065937 : Blo 2251435 5065937 := bstep (se 2 (by rfl) ⟨1899726, by rfl⟩ : syracuseStep 5065937 = 3799453) B3799453
theorem B3377291 : Blo 2251435 3377291 := bstep (se 1 (by rfl) ⟨2532968, by rfl⟩ : syracuseStep 3377291 = 5065937) B5065937
theorem B2251527 : Blo 2251435 2251527 := bstep (se 1 (by rfl) ⟨1688645, by rfl⟩ : syracuseStep 2251527 = 3377291) B3377291
theorem B2532973 : Blo 2251435 2532973 := bbase (se 3 (by rfl) ⟨474932, by rfl⟩ : syracuseStep 2532973 = 949865) (by norm_num)
theorem B3377297 : Blo 2251435 3377297 := bstep (se 2 (by rfl) ⟨1266486, by rfl⟩ : syracuseStep 3377297 = 2532973) B2532973
theorem B2251531 : Blo 2251435 2251531 := bstep (se 1 (by rfl) ⟨1688648, by rfl⟩ : syracuseStep 2251531 = 3377297) B3377297
theorem B7598933 : Blo 2251435 7598933 := bbase (se 9 (by rfl) ⟨22262, by rfl⟩ : syracuseStep 7598933 = 44525) (by norm_num)
theorem B5065955 : Blo 2251435 5065955 := bstep (se 1 (by rfl) ⟨3799466, by rfl⟩ : syracuseStep 5065955 = 7598933) B7598933
theorem B3377303 : Blo 2251435 3377303 := bstep (se 1 (by rfl) ⟨2532977, by rfl⟩ : syracuseStep 3377303 = 5065955) B5065955
theorem B2251535 : Blo 2251435 2251535 := bstep (se 1 (by rfl) ⟨1688651, by rfl⟩ : syracuseStep 2251535 = 3377303) B3377303
theorem B3377309 : Blo 2251435 3377309 := bbase (se 3 (by rfl) ⟨633245, by rfl⟩ : syracuseStep 3377309 = 1266491) (by norm_num)
theorem B2251539 : Blo 2251435 2251539 := bstep (se 1 (by rfl) ⟨1688654, by rfl⟩ : syracuseStep 2251539 = 3377309) B3377309
theorem B5065973 : Blo 2251435 5065973 := bbase (se 5 (by rfl) ⟨237467, by rfl⟩ : syracuseStep 5065973 = 474935) (by norm_num)
theorem B3377315 : Blo 2251435 3377315 := bstep (se 1 (by rfl) ⟨2532986, by rfl⟩ : syracuseStep 3377315 = 5065973) B5065973
theorem B2251543 : Blo 2251435 2251543 := bstep (se 1 (by rfl) ⟨1688657, by rfl⟩ : syracuseStep 2251543 = 3377315) B3377315
theorem B17330965 : Blo 2251435 17330965 := bbase (se 6 (by rfl) ⟨406194, by rfl⟩ : syracuseStep 17330965 = 812389) (by norm_num)
theorem B92431813 : Blo 2251435 92431813 := bstep (se 4 (by rfl) ⟨8665482, by rfl⟩ : syracuseStep 92431813 = 17330965) B17330965
theorem B123242417 : Blo 2251435 123242417 := bstep (se 2 (by rfl) ⟨46215906, by rfl⟩ : syracuseStep 123242417 = 92431813) B92431813
theorem B82161611 : Blo 2251435 82161611 := bstep (se 1 (by rfl) ⟨61621208, by rfl⟩ : syracuseStep 82161611 = 123242417) B123242417
theorem B54774407 : Blo 2251435 54774407 := bstep (se 1 (by rfl) ⟨41080805, by rfl⟩ : syracuseStep 54774407 = 82161611) B82161611
theorem B36516271 : Blo 2251435 36516271 := bstep (se 1 (by rfl) ⟨27387203, by rfl⟩ : syracuseStep 36516271 = 54774407) B54774407
theorem B48688361 : Blo 2251435 48688361 := bstep (se 2 (by rfl) ⟨18258135, by rfl⟩ : syracuseStep 48688361 = 36516271) B36516271
theorem B32458907 : Blo 2251435 32458907 := bstep (se 1 (by rfl) ⟨24344180, by rfl⟩ : syracuseStep 32458907 = 48688361) B48688361
theorem B21639271 : Blo 2251435 21639271 := bstep (se 1 (by rfl) ⟨16229453, by rfl⟩ : syracuseStep 21639271 = 32458907) B32458907
theorem B28852361 : Blo 2251435 28852361 := bstep (se 2 (by rfl) ⟨10819635, by rfl⟩ : syracuseStep 28852361 = 21639271) B21639271
theorem B19234907 : Blo 2251435 19234907 := bstep (se 1 (by rfl) ⟨14426180, by rfl⟩ : syracuseStep 19234907 = 28852361) B28852361
theorem B12823271 : Blo 2251435 12823271 := bstep (se 1 (by rfl) ⟨9617453, by rfl⟩ : syracuseStep 12823271 = 19234907) B19234907
theorem B8548847 : Blo 2251435 8548847 := bstep (se 1 (by rfl) ⟨6411635, by rfl⟩ : syracuseStep 8548847 = 12823271) B12823271
theorem B5699231 : Blo 2251435 5699231 := bstep (se 1 (by rfl) ⟨4274423, by rfl⟩ : syracuseStep 5699231 = 8548847) B8548847
theorem B3799487 : Blo 2251435 3799487 := bstep (se 1 (by rfl) ⟨2849615, by rfl⟩ : syracuseStep 3799487 = 5699231) B5699231
theorem B2532991 : Blo 2251435 2532991 := bstep (se 1 (by rfl) ⟨1899743, by rfl⟩ : syracuseStep 2532991 = 3799487) B3799487
theorem B3377321 : Blo 2251435 3377321 := bstep (se 2 (by rfl) ⟨1266495, by rfl⟩ : syracuseStep 3377321 = 2532991) B2532991
theorem B2251547 : Blo 2251435 2251547 := bstep (se 1 (by rfl) ⟨1688660, by rfl⟩ : syracuseStep 2251547 = 3377321) B3377321
theorem B2927909 : Blo 2251435 2927909 := bbase (se 4 (by rfl) ⟨274491, by rfl⟩ : syracuseStep 2927909 = 548983) (by norm_num)
theorem B7807757 : Blo 2251435 7807757 := bstep (se 3 (by rfl) ⟨1463954, by rfl⟩ : syracuseStep 7807757 = 2927909) B2927909
theorem B20820685 : Blo 2251435 20820685 := bstep (se 3 (by rfl) ⟨3903878, by rfl⟩ : syracuseStep 20820685 = 7807757) B7807757
theorem B27760913 : Blo 2251435 27760913 := bstep (se 2 (by rfl) ⟨10410342, by rfl⟩ : syracuseStep 27760913 = 20820685) B20820685
theorem B18507275 : Blo 2251435 18507275 := bstep (se 1 (by rfl) ⟨13880456, by rfl⟩ : syracuseStep 18507275 = 27760913) B27760913
theorem B12338183 : Blo 2251435 12338183 := bstep (se 1 (by rfl) ⟨9253637, by rfl⟩ : syracuseStep 12338183 = 18507275) B18507275
theorem B32901821 : Blo 2251435 32901821 := bstep (se 3 (by rfl) ⟨6169091, by rfl⟩ : syracuseStep 32901821 = 12338183) B12338183
theorem B21934547 : Blo 2251435 21934547 := bstep (se 1 (by rfl) ⟨16450910, by rfl⟩ : syracuseStep 21934547 = 32901821) B32901821
theorem B14623031 : Blo 2251435 14623031 := bstep (se 1 (by rfl) ⟨10967273, by rfl⟩ : syracuseStep 14623031 = 21934547) B21934547
theorem B9748687 : Blo 2251435 9748687 := bstep (se 1 (by rfl) ⟨7311515, by rfl⟩ : syracuseStep 9748687 = 14623031) B14623031
theorem B12998249 : Blo 2251435 12998249 := bstep (se 2 (by rfl) ⟨4874343, by rfl⟩ : syracuseStep 12998249 = 9748687) B9748687
theorem B8665499 : Blo 2251435 8665499 := bstep (se 1 (by rfl) ⟨6499124, by rfl⟩ : syracuseStep 8665499 = 12998249) B12998249
theorem B23107997 : Blo 2251435 23107997 := bstep (se 3 (by rfl) ⟨4332749, by rfl⟩ : syracuseStep 23107997 = 8665499) B8665499
theorem B15405331 : Blo 2251435 15405331 := bstep (se 1 (by rfl) ⟨11553998, by rfl⟩ : syracuseStep 15405331 = 23107997) B23107997
theorem B20540441 : Blo 2251435 20540441 := bstep (se 2 (by rfl) ⟨7702665, by rfl⟩ : syracuseStep 20540441 = 15405331) B15405331
theorem B13693627 : Blo 2251435 13693627 := bstep (se 1 (by rfl) ⟨10270220, by rfl⟩ : syracuseStep 13693627 = 20540441) B20540441
theorem B18258169 : Blo 2251435 18258169 := bstep (se 2 (by rfl) ⟨6846813, by rfl⟩ : syracuseStep 18258169 = 13693627) B13693627
theorem B24344225 : Blo 2251435 24344225 := bstep (se 2 (by rfl) ⟨9129084, by rfl⟩ : syracuseStep 24344225 = 18258169) B18258169
theorem B16229483 : Blo 2251435 16229483 := bstep (se 1 (by rfl) ⟨12172112, by rfl⟩ : syracuseStep 16229483 = 24344225) B24344225
theorem B10819655 : Blo 2251435 10819655 := bstep (se 1 (by rfl) ⟨8114741, by rfl⟩ : syracuseStep 10819655 = 16229483) B16229483
theorem B7213103 : Blo 2251435 7213103 := bstep (se 1 (by rfl) ⟨5409827, by rfl⟩ : syracuseStep 7213103 = 10819655) B10819655
theorem B4808735 : Blo 2251435 4808735 := bstep (se 1 (by rfl) ⟨3606551, by rfl⟩ : syracuseStep 4808735 = 7213103) B7213103
theorem B3205823 : Blo 2251435 3205823 := bstep (se 1 (by rfl) ⟨2404367, by rfl⟩ : syracuseStep 3205823 = 4808735) B4808735
theorem B8548861 : Blo 2251435 8548861 := bstep (se 3 (by rfl) ⟨1602911, by rfl⟩ : syracuseStep 8548861 = 3205823) B3205823
theorem B11398481 : Blo 2251435 11398481 := bstep (se 2 (by rfl) ⟨4274430, by rfl⟩ : syracuseStep 11398481 = 8548861) B8548861
theorem B7598987 : Blo 2251435 7598987 := bstep (se 1 (by rfl) ⟨5699240, by rfl⟩ : syracuseStep 7598987 = 11398481) B11398481
theorem B5065991 : Blo 2251435 5065991 := bstep (se 1 (by rfl) ⟨3799493, by rfl⟩ : syracuseStep 5065991 = 7598987) B7598987
theorem B3377327 : Blo 2251435 3377327 := bstep (se 1 (by rfl) ⟨2532995, by rfl⟩ : syracuseStep 3377327 = 5065991) B5065991
theorem B2251551 : Blo 2251435 2251551 := bstep (se 1 (by rfl) ⟨1688663, by rfl⟩ : syracuseStep 2251551 = 3377327) B3377327
theorem B3377333 : Blo 2251435 3377333 := bbase (se 5 (by rfl) ⟨158312, by rfl⟩ : syracuseStep 3377333 = 316625) (by norm_num)
theorem B2251555 : Blo 2251435 2251555 := bstep (se 1 (by rfl) ⟨1688666, by rfl⟩ : syracuseStep 2251555 = 3377333) B3377333
theorem B5699261 : Blo 2251435 5699261 := bbase (se 3 (by rfl) ⟨1068611, by rfl⟩ : syracuseStep 5699261 = 2137223) (by norm_num)
theorem B3799507 : Blo 2251435 3799507 := bstep (se 1 (by rfl) ⟨2849630, by rfl⟩ : syracuseStep 3799507 = 5699261) B5699261
theorem B5066009 : Blo 2251435 5066009 := bstep (se 2 (by rfl) ⟨1899753, by rfl⟩ : syracuseStep 5066009 = 3799507) B3799507
theorem B3377339 : Blo 2251435 3377339 := bstep (se 1 (by rfl) ⟨2533004, by rfl⟩ : syracuseStep 3377339 = 5066009) B5066009
theorem B2251559 : Blo 2251435 2251559 := bstep (se 1 (by rfl) ⟨1688669, by rfl⟩ : syracuseStep 2251559 = 3377339) B3377339
theorem B2533009 : Blo 2251435 2533009 := bbase (se 2 (by rfl) ⟨949878, by rfl⟩ : syracuseStep 2533009 = 1899757) (by norm_num)
theorem B3377345 : Blo 2251435 3377345 := bstep (se 2 (by rfl) ⟨1266504, by rfl⟩ : syracuseStep 3377345 = 2533009) B2533009
theorem B2251563 : Blo 2251435 2251563 := bstep (se 1 (by rfl) ⟨1688672, by rfl⟩ : syracuseStep 2251563 = 3377345) B3377345
theorem B4274461 : Blo 2251435 4274461 := bbase (se 3 (by rfl) ⟨801461, by rfl⟩ : syracuseStep 4274461 = 1602923) (by norm_num)
theorem B5699281 : Blo 2251435 5699281 := bstep (se 2 (by rfl) ⟨2137230, by rfl⟩ : syracuseStep 5699281 = 4274461) B4274461
theorem B7599041 : Blo 2251435 7599041 := bstep (se 2 (by rfl) ⟨2849640, by rfl⟩ : syracuseStep 7599041 = 5699281) B5699281
theorem B5066027 : Blo 2251435 5066027 := bstep (se 1 (by rfl) ⟨3799520, by rfl⟩ : syracuseStep 5066027 = 7599041) B7599041
theorem B3377351 : Blo 2251435 3377351 := bstep (se 1 (by rfl) ⟨2533013, by rfl⟩ : syracuseStep 3377351 = 5066027) B5066027
theorem B2251567 : Blo 2251435 2251567 := bstep (se 1 (by rfl) ⟨1688675, by rfl⟩ : syracuseStep 2251567 = 3377351) B3377351
theorem B3377357 : Blo 2251435 3377357 := bbase (se 3 (by rfl) ⟨633254, by rfl⟩ : syracuseStep 3377357 = 1266509) (by norm_num)
theorem B2251571 : Blo 2251435 2251571 := bstep (se 1 (by rfl) ⟨1688678, by rfl⟩ : syracuseStep 2251571 = 3377357) B3377357
theorem B5066045 : Blo 2251435 5066045 := bbase (se 3 (by rfl) ⟨949883, by rfl⟩ : syracuseStep 5066045 = 1899767) (by norm_num)
theorem B3377363 : Blo 2251435 3377363 := bstep (se 1 (by rfl) ⟨2533022, by rfl⟩ : syracuseStep 3377363 = 5066045) B5066045
theorem B2251575 : Blo 2251435 2251575 := bstep (se 1 (by rfl) ⟨1688681, by rfl⟩ : syracuseStep 2251575 = 3377363) B3377363
theorem B3799541 : Blo 2251435 3799541 := bbase (se 5 (by rfl) ⟨178103, by rfl⟩ : syracuseStep 3799541 = 356207) (by norm_num)
theorem B2533027 : Blo 2251435 2533027 := bstep (se 1 (by rfl) ⟨1899770, by rfl⟩ : syracuseStep 2533027 = 3799541) B3799541
theorem B3377369 : Blo 2251435 3377369 := bstep (se 2 (by rfl) ⟨1266513, by rfl⟩ : syracuseStep 3377369 = 2533027) B2533027
theorem B2251579 : Blo 2251435 2251579 := bstep (se 1 (by rfl) ⟨1688684, by rfl⟩ : syracuseStep 2251579 = 3377369) B3377369
theorem B7213205 : Blo 2251435 7213205 := bbase (se 6 (by rfl) ⟨169059, by rfl⟩ : syracuseStep 7213205 = 338119) (by norm_num)
theorem B4808803 : Blo 2251435 4808803 := bstep (se 1 (by rfl) ⟨3606602, by rfl⟩ : syracuseStep 4808803 = 7213205) B7213205
theorem B6411737 : Blo 2251435 6411737 := bstep (se 2 (by rfl) ⟨2404401, by rfl⟩ : syracuseStep 6411737 = 4808803) B4808803
theorem B17097965 : Blo 2251435 17097965 := bstep (se 3 (by rfl) ⟨3205868, by rfl⟩ : syracuseStep 17097965 = 6411737) B6411737
theorem B11398643 : Blo 2251435 11398643 := bstep (se 1 (by rfl) ⟨8548982, by rfl⟩ : syracuseStep 11398643 = 17097965) B17097965
theorem B7599095 : Blo 2251435 7599095 := bstep (se 1 (by rfl) ⟨5699321, by rfl⟩ : syracuseStep 7599095 = 11398643) B11398643
theorem B5066063 : Blo 2251435 5066063 := bstep (se 1 (by rfl) ⟨3799547, by rfl⟩ : syracuseStep 5066063 = 7599095) B7599095
theorem B3377375 : Blo 2251435 3377375 := bstep (se 1 (by rfl) ⟨2533031, by rfl⟩ : syracuseStep 3377375 = 5066063) B5066063
theorem B2251583 : Blo 2251435 2251583 := bstep (se 1 (by rfl) ⟨1688687, by rfl⟩ : syracuseStep 2251583 = 3377375) B3377375
theorem B3377381 : Blo 2251435 3377381 := bbase (se 4 (by rfl) ⟨316629, by rfl⟩ : syracuseStep 3377381 = 633259) (by norm_num)
theorem B2251587 : Blo 2251435 2251587 := bstep (se 1 (by rfl) ⟨1688690, by rfl⟩ : syracuseStep 2251587 = 3377381) B3377381
theorem B4808821 : Blo 2251435 4808821 := bbase (se 5 (by rfl) ⟨225413, by rfl⟩ : syracuseStep 4808821 = 450827) (by norm_num)
theorem B6411761 : Blo 2251435 6411761 := bstep (se 2 (by rfl) ⟨2404410, by rfl⟩ : syracuseStep 6411761 = 4808821) B4808821
theorem B4274507 : Blo 2251435 4274507 := bstep (se 1 (by rfl) ⟨3205880, by rfl⟩ : syracuseStep 4274507 = 6411761) B6411761
theorem B2849671 : Blo 2251435 2849671 := bstep (se 1 (by rfl) ⟨2137253, by rfl⟩ : syracuseStep 2849671 = 4274507) B4274507
theorem B3799561 : Blo 2251435 3799561 := bstep (se 2 (by rfl) ⟨1424835, by rfl⟩ : syracuseStep 3799561 = 2849671) B2849671
theorem B5066081 : Blo 2251435 5066081 := bstep (se 2 (by rfl) ⟨1899780, by rfl⟩ : syracuseStep 5066081 = 3799561) B3799561
theorem B3377387 : Blo 2251435 3377387 := bstep (se 1 (by rfl) ⟨2533040, by rfl⟩ : syracuseStep 3377387 = 5066081) B5066081
theorem B2251591 : Blo 2251435 2251591 := bstep (se 1 (by rfl) ⟨1688693, by rfl⟩ : syracuseStep 2251591 = 3377387) B3377387
theorem B2533045 : Blo 2251435 2533045 := bbase (se 5 (by rfl) ⟨118736, by rfl⟩ : syracuseStep 2533045 = 237473) (by norm_num)
theorem B3377393 : Blo 2251435 3377393 := bstep (se 2 (by rfl) ⟨1266522, by rfl⟩ : syracuseStep 3377393 = 2533045) B2533045
theorem B2251595 : Blo 2251435 2251595 := bstep (se 1 (by rfl) ⟨1688696, by rfl⟩ : syracuseStep 2251595 = 3377393) B3377393
theorem B2849681 : Blo 2251435 2849681 := bbase (se 2 (by rfl) ⟨1068630, by rfl⟩ : syracuseStep 2849681 = 2137261) (by norm_num)
theorem B7599149 : Blo 2251435 7599149 := bstep (se 3 (by rfl) ⟨1424840, by rfl⟩ : syracuseStep 7599149 = 2849681) B2849681
theorem B5066099 : Blo 2251435 5066099 := bstep (se 1 (by rfl) ⟨3799574, by rfl⟩ : syracuseStep 5066099 = 7599149) B7599149
theorem B3377399 : Blo 2251435 3377399 := bstep (se 1 (by rfl) ⟨2533049, by rfl⟩ : syracuseStep 3377399 = 5066099) B5066099
theorem B2251599 : Blo 2251435 2251599 := bstep (se 1 (by rfl) ⟨1688699, by rfl⟩ : syracuseStep 2251599 = 3377399) B3377399
theorem B3377405 : Blo 2251435 3377405 := bbase (se 3 (by rfl) ⟨633263, by rfl⟩ : syracuseStep 3377405 = 1266527) (by norm_num)
theorem B2251603 : Blo 2251435 2251603 := bstep (se 1 (by rfl) ⟨1688702, by rfl⟩ : syracuseStep 2251603 = 3377405) B3377405
theorem B5066117 : Blo 2251435 5066117 := bbase (se 4 (by rfl) ⟨474948, by rfl⟩ : syracuseStep 5066117 = 949897) (by norm_num)
theorem B3377411 : Blo 2251435 3377411 := bstep (se 1 (by rfl) ⟨2533058, by rfl⟩ : syracuseStep 3377411 = 5066117) B5066117
theorem B2251607 : Blo 2251435 2251607 := bstep (se 1 (by rfl) ⟨1688705, by rfl⟩ : syracuseStep 2251607 = 3377411) B3377411
theorem B3205909 : Blo 2251435 3205909 := bbase (se 6 (by rfl) ⟨75138, by rfl⟩ : syracuseStep 3205909 = 150277) (by norm_num)
theorem B4274545 : Blo 2251435 4274545 := bstep (se 2 (by rfl) ⟨1602954, by rfl⟩ : syracuseStep 4274545 = 3205909) B3205909
theorem B5699393 : Blo 2251435 5699393 := bstep (se 2 (by rfl) ⟨2137272, by rfl⟩ : syracuseStep 5699393 = 4274545) B4274545
theorem B3799595 : Blo 2251435 3799595 := bstep (se 1 (by rfl) ⟨2849696, by rfl⟩ : syracuseStep 3799595 = 5699393) B5699393
theorem B2533063 : Blo 2251435 2533063 := bstep (se 1 (by rfl) ⟨1899797, by rfl⟩ : syracuseStep 2533063 = 3799595) B3799595
theorem B3377417 : Blo 2251435 3377417 := bstep (se 2 (by rfl) ⟨1266531, by rfl⟩ : syracuseStep 3377417 = 2533063) B2533063
theorem B2251611 : Blo 2251435 2251611 := bstep (se 1 (by rfl) ⟨1688708, by rfl⟩ : syracuseStep 2251611 = 3377417) B3377417
theorem B11398805 : Blo 2251435 11398805 := bbase (se 6 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 11398805 = 534319) (by norm_num)
theorem B7599203 : Blo 2251435 7599203 := bstep (se 1 (by rfl) ⟨5699402, by rfl⟩ : syracuseStep 7599203 = 11398805) B11398805
theorem B5066135 : Blo 2251435 5066135 := bstep (se 1 (by rfl) ⟨3799601, by rfl⟩ : syracuseStep 5066135 = 7599203) B7599203
theorem B3377423 : Blo 2251435 3377423 := bstep (se 1 (by rfl) ⟨2533067, by rfl⟩ : syracuseStep 3377423 = 5066135) B5066135
theorem B2251615 : Blo 2251435 2251615 := bstep (se 1 (by rfl) ⟨1688711, by rfl⟩ : syracuseStep 2251615 = 3377423) B3377423
theorem B3377429 : Blo 2251435 3377429 := bbase (se 6 (by rfl) ⟨79158, by rfl⟩ : syracuseStep 3377429 = 158317) (by norm_num)
theorem B2251619 : Blo 2251435 2251619 := bstep (se 1 (by rfl) ⟨1688714, by rfl⟩ : syracuseStep 2251619 = 3377429) B3377429
theorem B28853333 : Blo 2251435 28853333 := bbase (se 8 (by rfl) ⟨169062, by rfl⟩ : syracuseStep 28853333 = 338125) (by norm_num)
theorem B19235555 : Blo 2251435 19235555 := bstep (se 1 (by rfl) ⟨14426666, by rfl⟩ : syracuseStep 19235555 = 28853333) B28853333
theorem B12823703 : Blo 2251435 12823703 := bstep (se 1 (by rfl) ⟨9617777, by rfl⟩ : syracuseStep 12823703 = 19235555) B19235555
theorem B8549135 : Blo 2251435 8549135 := bstep (se 1 (by rfl) ⟨6411851, by rfl⟩ : syracuseStep 8549135 = 12823703) B12823703
theorem B5699423 : Blo 2251435 5699423 := bstep (se 1 (by rfl) ⟨4274567, by rfl⟩ : syracuseStep 5699423 = 8549135) B8549135
theorem B3799615 : Blo 2251435 3799615 := bstep (se 1 (by rfl) ⟨2849711, by rfl⟩ : syracuseStep 3799615 = 5699423) B5699423
theorem B5066153 : Blo 2251435 5066153 := bstep (se 2 (by rfl) ⟨1899807, by rfl⟩ : syracuseStep 5066153 = 3799615) B3799615
theorem B3377435 : Blo 2251435 3377435 := bstep (se 1 (by rfl) ⟨2533076, by rfl⟩ : syracuseStep 3377435 = 5066153) B5066153
theorem B2251623 : Blo 2251435 2251623 := bstep (se 1 (by rfl) ⟨1688717, by rfl⟩ : syracuseStep 2251623 = 3377435) B3377435
theorem B2533081 : Blo 2251435 2533081 := bbase (se 2 (by rfl) ⟨949905, by rfl⟩ : syracuseStep 2533081 = 1899811) (by norm_num)
theorem B3377441 : Blo 2251435 3377441 := bstep (se 2 (by rfl) ⟨1266540, by rfl⟩ : syracuseStep 3377441 = 2533081) B2533081
theorem B2251627 : Blo 2251435 2251627 := bstep (se 1 (by rfl) ⟨1688720, by rfl⟩ : syracuseStep 2251627 = 3377441) B3377441
theorem B2404453 : Blo 2251435 2404453 := bbase (se 4 (by rfl) ⟨225417, by rfl⟩ : syracuseStep 2404453 = 450835) (by norm_num)
theorem B3205937 : Blo 2251435 3205937 := bstep (se 2 (by rfl) ⟨1202226, by rfl⟩ : syracuseStep 3205937 = 2404453) B2404453
theorem B8549165 : Blo 2251435 8549165 := bstep (se 3 (by rfl) ⟨1602968, by rfl⟩ : syracuseStep 8549165 = 3205937) B3205937
theorem B5699443 : Blo 2251435 5699443 := bstep (se 1 (by rfl) ⟨4274582, by rfl⟩ : syracuseStep 5699443 = 8549165) B8549165
theorem B7599257 : Blo 2251435 7599257 := bstep (se 2 (by rfl) ⟨2849721, by rfl⟩ : syracuseStep 7599257 = 5699443) B5699443
theorem B5066171 : Blo 2251435 5066171 := bstep (se 1 (by rfl) ⟨3799628, by rfl⟩ : syracuseStep 5066171 = 7599257) B7599257
theorem B3377447 : Blo 2251435 3377447 := bstep (se 1 (by rfl) ⟨2533085, by rfl⟩ : syracuseStep 3377447 = 5066171) B5066171
theorem B2251631 : Blo 2251435 2251631 := bstep (se 1 (by rfl) ⟨1688723, by rfl⟩ : syracuseStep 2251631 = 3377447) B3377447
theorem B3377453 : Blo 2251435 3377453 := bbase (se 3 (by rfl) ⟨633272, by rfl⟩ : syracuseStep 3377453 = 1266545) (by norm_num)
theorem B2251635 : Blo 2251435 2251635 := bstep (se 1 (by rfl) ⟨1688726, by rfl⟩ : syracuseStep 2251635 = 3377453) B3377453
theorem B5066189 : Blo 2251435 5066189 := bbase (se 3 (by rfl) ⟨949910, by rfl⟩ : syracuseStep 5066189 = 1899821) (by norm_num)
theorem B3377459 : Blo 2251435 3377459 := bstep (se 1 (by rfl) ⟨2533094, by rfl⟩ : syracuseStep 3377459 = 5066189) B5066189
theorem B2251639 : Blo 2251435 2251639 := bstep (se 1 (by rfl) ⟨1688729, by rfl⟩ : syracuseStep 2251639 = 3377459) B3377459
theorem B2849737 : Blo 2251435 2849737 := bbase (se 2 (by rfl) ⟨1068651, by rfl⟩ : syracuseStep 2849737 = 2137303) (by norm_num)
theorem B3799649 : Blo 2251435 3799649 := bstep (se 2 (by rfl) ⟨1424868, by rfl⟩ : syracuseStep 3799649 = 2849737) B2849737
theorem B2533099 : Blo 2251435 2533099 := bstep (se 1 (by rfl) ⟨1899824, by rfl⟩ : syracuseStep 2533099 = 3799649) B3799649
theorem B3377465 : Blo 2251435 3377465 := bstep (se 2 (by rfl) ⟨1266549, by rfl⟩ : syracuseStep 3377465 = 2533099) B2533099
theorem B2251643 : Blo 2251435 2251643 := bstep (se 1 (by rfl) ⟨1688732, by rfl⟩ : syracuseStep 2251643 = 3377465) B3377465
theorem B7311829 : Blo 2251435 7311829 := bbase (se 7 (by rfl) ⟨85685, by rfl⟩ : syracuseStep 7311829 = 171371) (by norm_num)
theorem B9749105 : Blo 2251435 9749105 := bstep (se 2 (by rfl) ⟨3655914, by rfl⟩ : syracuseStep 9749105 = 7311829) B7311829
theorem B6499403 : Blo 2251435 6499403 := bstep (se 1 (by rfl) ⟨4874552, by rfl⟩ : syracuseStep 6499403 = 9749105) B9749105
theorem B4332935 : Blo 2251435 4332935 := bstep (se 1 (by rfl) ⟨3249701, by rfl⟩ : syracuseStep 4332935 = 6499403) B6499403
theorem B2888623 : Blo 2251435 2888623 := bstep (se 1 (by rfl) ⟨2166467, by rfl⟩ : syracuseStep 2888623 = 4332935) B4332935
theorem B3851497 : Blo 2251435 3851497 := bstep (se 2 (by rfl) ⟨1444311, by rfl⟩ : syracuseStep 3851497 = 2888623) B2888623
theorem B5135329 : Blo 2251435 5135329 := bstep (se 2 (by rfl) ⟨1925748, by rfl⟩ : syracuseStep 5135329 = 3851497) B3851497
theorem B6847105 : Blo 2251435 6847105 := bstep (se 2 (by rfl) ⟨2567664, by rfl⟩ : syracuseStep 6847105 = 5135329) B5135329
theorem B9129473 : Blo 2251435 9129473 := bstep (se 2 (by rfl) ⟨3423552, by rfl⟩ : syracuseStep 9129473 = 6847105) B6847105
theorem B6086315 : Blo 2251435 6086315 := bstep (se 1 (by rfl) ⟨4564736, by rfl⟩ : syracuseStep 6086315 = 9129473) B9129473
theorem B4057543 : Blo 2251435 4057543 := bstep (se 1 (by rfl) ⟨3043157, by rfl⟩ : syracuseStep 4057543 = 6086315) B6086315
theorem B21640229 : Blo 2251435 21640229 := bstep (se 4 (by rfl) ⟨2028771, by rfl⟩ : syracuseStep 21640229 = 4057543) B4057543
theorem B14426819 : Blo 2251435 14426819 := bstep (se 1 (by rfl) ⟨10820114, by rfl⟩ : syracuseStep 14426819 = 21640229) B21640229
theorem B9617879 : Blo 2251435 9617879 := bstep (se 1 (by rfl) ⟨7213409, by rfl⟩ : syracuseStep 9617879 = 14426819) B14426819
theorem B25647677 : Blo 2251435 25647677 := bstep (se 3 (by rfl) ⟨4808939, by rfl⟩ : syracuseStep 25647677 = 9617879) B9617879
theorem B17098451 : Blo 2251435 17098451 := bstep (se 1 (by rfl) ⟨12823838, by rfl⟩ : syracuseStep 17098451 = 25647677) B25647677
theorem B11398967 : Blo 2251435 11398967 := bstep (se 1 (by rfl) ⟨8549225, by rfl⟩ : syracuseStep 11398967 = 17098451) B17098451
theorem B7599311 : Blo 2251435 7599311 := bstep (se 1 (by rfl) ⟨5699483, by rfl⟩ : syracuseStep 7599311 = 11398967) B11398967
theorem B5066207 : Blo 2251435 5066207 := bstep (se 1 (by rfl) ⟨3799655, by rfl⟩ : syracuseStep 5066207 = 7599311) B7599311
theorem B3377471 : Blo 2251435 3377471 := bstep (se 1 (by rfl) ⟨2533103, by rfl⟩ : syracuseStep 3377471 = 5066207) B5066207
theorem B2251647 : Blo 2251435 2251647 := bstep (se 1 (by rfl) ⟨1688735, by rfl⟩ : syracuseStep 2251647 = 3377471) B3377471
theorem B3377477 : Blo 2251435 3377477 := bbase (se 4 (by rfl) ⟨316638, by rfl⟩ : syracuseStep 3377477 = 633277) (by norm_num)
theorem B2251651 : Blo 2251435 2251651 := bstep (se 1 (by rfl) ⟨1688738, by rfl⟩ : syracuseStep 2251651 = 3377477) B3377477
theorem B3799669 : Blo 2251435 3799669 := bbase (se 5 (by rfl) ⟨178109, by rfl⟩ : syracuseStep 3799669 = 356219) (by norm_num)
theorem B5066225 : Blo 2251435 5066225 := bstep (se 2 (by rfl) ⟨1899834, by rfl⟩ : syracuseStep 5066225 = 3799669) B3799669
theorem B3377483 : Blo 2251435 3377483 := bstep (se 1 (by rfl) ⟨2533112, by rfl⟩ : syracuseStep 3377483 = 5066225) B5066225
theorem B2251655 : Blo 2251435 2251655 := bstep (se 1 (by rfl) ⟨1688741, by rfl⟩ : syracuseStep 2251655 = 3377483) B3377483
theorem B2533117 : Blo 2251435 2533117 := bbase (se 3 (by rfl) ⟨474959, by rfl⟩ : syracuseStep 2533117 = 949919) (by norm_num)
theorem B3377489 : Blo 2251435 3377489 := bstep (se 2 (by rfl) ⟨1266558, by rfl⟩ : syracuseStep 3377489 = 2533117) B2533117
theorem B2251659 : Blo 2251435 2251659 := bstep (se 1 (by rfl) ⟨1688744, by rfl⟩ : syracuseStep 2251659 = 3377489) B3377489
theorem B7599365 : Blo 2251435 7599365 := bbase (se 4 (by rfl) ⟨712440, by rfl⟩ : syracuseStep 7599365 = 1424881) (by norm_num)
theorem B5066243 : Blo 2251435 5066243 := bstep (se 1 (by rfl) ⟨3799682, by rfl⟩ : syracuseStep 5066243 = 7599365) B7599365
theorem B3377495 : Blo 2251435 3377495 := bstep (se 1 (by rfl) ⟨2533121, by rfl⟩ : syracuseStep 3377495 = 5066243) B5066243
theorem B2251663 : Blo 2251435 2251663 := bstep (se 1 (by rfl) ⟨1688747, by rfl⟩ : syracuseStep 2251663 = 3377495) B3377495
theorem B3377501 : Blo 2251435 3377501 := bbase (se 3 (by rfl) ⟨633281, by rfl⟩ : syracuseStep 3377501 = 1266563) (by norm_num)
theorem B2251667 : Blo 2251435 2251667 := bstep (se 1 (by rfl) ⟨1688750, by rfl⟩ : syracuseStep 2251667 = 3377501) B3377501
theorem B5066261 : Blo 2251435 5066261 := bbase (se 6 (by rfl) ⟨118740, by rfl⟩ : syracuseStep 5066261 = 237481) (by norm_num)
theorem B3377507 : Blo 2251435 3377507 := bstep (se 1 (by rfl) ⟨2533130, by rfl⟩ : syracuseStep 3377507 = 5066261) B5066261
theorem B2251671 : Blo 2251435 2251671 := bstep (se 1 (by rfl) ⟨1688753, by rfl⟩ : syracuseStep 2251671 = 3377507) B3377507
theorem B8549333 : Blo 2251435 8549333 := bbase (se 7 (by rfl) ⟨100187, by rfl⟩ : syracuseStep 8549333 = 200375) (by norm_num)
theorem B5699555 : Blo 2251435 5699555 := bstep (se 1 (by rfl) ⟨4274666, by rfl⟩ : syracuseStep 5699555 = 8549333) B8549333
theorem B3799703 : Blo 2251435 3799703 := bstep (se 1 (by rfl) ⟨2849777, by rfl⟩ : syracuseStep 3799703 = 5699555) B5699555
theorem B2533135 : Blo 2251435 2533135 := bstep (se 1 (by rfl) ⟨1899851, by rfl⟩ : syracuseStep 2533135 = 3799703) B3799703
theorem B3377513 : Blo 2251435 3377513 := bstep (se 2 (by rfl) ⟨1266567, by rfl⟩ : syracuseStep 3377513 = 2533135) B2533135
theorem B2251675 : Blo 2251435 2251675 := bstep (se 1 (by rfl) ⟨1688756, by rfl⟩ : syracuseStep 2251675 = 3377513) B3377513
theorem B12824021 : Blo 2251435 12824021 := bbase (se 7 (by rfl) ⟨150281, by rfl⟩ : syracuseStep 12824021 = 300563) (by norm_num)
theorem B8549347 : Blo 2251435 8549347 := bstep (se 1 (by rfl) ⟨6412010, by rfl⟩ : syracuseStep 8549347 = 12824021) B12824021
theorem B11399129 : Blo 2251435 11399129 := bstep (se 2 (by rfl) ⟨4274673, by rfl⟩ : syracuseStep 11399129 = 8549347) B8549347
theorem B7599419 : Blo 2251435 7599419 := bstep (se 1 (by rfl) ⟨5699564, by rfl⟩ : syracuseStep 7599419 = 11399129) B11399129
theorem B5066279 : Blo 2251435 5066279 := bstep (se 1 (by rfl) ⟨3799709, by rfl⟩ : syracuseStep 5066279 = 7599419) B7599419
theorem B3377519 : Blo 2251435 3377519 := bstep (se 1 (by rfl) ⟨2533139, by rfl⟩ : syracuseStep 3377519 = 5066279) B5066279
theorem B2251679 : Blo 2251435 2251679 := bstep (se 1 (by rfl) ⟨1688759, by rfl⟩ : syracuseStep 2251679 = 3377519) B3377519
theorem B3377525 : Blo 2251435 3377525 := bbase (se 5 (by rfl) ⟨158321, by rfl⟩ : syracuseStep 3377525 = 316643) (by norm_num)
theorem B2251683 : Blo 2251435 2251683 := bstep (se 1 (by rfl) ⟨1688762, by rfl⟩ : syracuseStep 2251683 = 3377525) B3377525
theorem B2404513 : Blo 2251435 2404513 := bbase (se 2 (by rfl) ⟨901692, by rfl⟩ : syracuseStep 2404513 = 1803385) (by norm_num)
theorem B3206017 : Blo 2251435 3206017 := bstep (se 2 (by rfl) ⟨1202256, by rfl⟩ : syracuseStep 3206017 = 2404513) B2404513
theorem B4274689 : Blo 2251435 4274689 := bstep (se 2 (by rfl) ⟨1603008, by rfl⟩ : syracuseStep 4274689 = 3206017) B3206017
theorem B5699585 : Blo 2251435 5699585 := bstep (se 2 (by rfl) ⟨2137344, by rfl⟩ : syracuseStep 5699585 = 4274689) B4274689
theorem B3799723 : Blo 2251435 3799723 := bstep (se 1 (by rfl) ⟨2849792, by rfl⟩ : syracuseStep 3799723 = 5699585) B5699585
theorem B5066297 : Blo 2251435 5066297 := bstep (se 2 (by rfl) ⟨1899861, by rfl⟩ : syracuseStep 5066297 = 3799723) B3799723
theorem B3377531 : Blo 2251435 3377531 := bstep (se 1 (by rfl) ⟨2533148, by rfl⟩ : syracuseStep 3377531 = 5066297) B5066297
theorem B2251687 : Blo 2251435 2251687 := bstep (se 1 (by rfl) ⟨1688765, by rfl⟩ : syracuseStep 2251687 = 3377531) B3377531
theorem B2533153 : Blo 2251435 2533153 := bbase (se 2 (by rfl) ⟨949932, by rfl⟩ : syracuseStep 2533153 = 1899865) (by norm_num)
theorem B3377537 : Blo 2251435 3377537 := bstep (se 2 (by rfl) ⟨1266576, by rfl⟩ : syracuseStep 3377537 = 2533153) B2533153
theorem B2251691 : Blo 2251435 2251691 := bstep (se 1 (by rfl) ⟨1688768, by rfl⟩ : syracuseStep 2251691 = 3377537) B3377537
theorem B5699605 : Blo 2251435 5699605 := bbase (se 6 (by rfl) ⟨133584, by rfl⟩ : syracuseStep 5699605 = 267169) (by norm_num)
theorem B7599473 : Blo 2251435 7599473 := bstep (se 2 (by rfl) ⟨2849802, by rfl⟩ : syracuseStep 7599473 = 5699605) B5699605
theorem B5066315 : Blo 2251435 5066315 := bstep (se 1 (by rfl) ⟨3799736, by rfl⟩ : syracuseStep 5066315 = 7599473) B7599473
theorem B3377543 : Blo 2251435 3377543 := bstep (se 1 (by rfl) ⟨2533157, by rfl⟩ : syracuseStep 3377543 = 5066315) B5066315
theorem B2251695 : Blo 2251435 2251695 := bstep (se 1 (by rfl) ⟨1688771, by rfl⟩ : syracuseStep 2251695 = 3377543) B3377543
theorem B3377549 : Blo 2251435 3377549 := bbase (se 3 (by rfl) ⟨633290, by rfl⟩ : syracuseStep 3377549 = 1266581) (by norm_num)
theorem B2251699 : Blo 2251435 2251699 := bstep (se 1 (by rfl) ⟨1688774, by rfl⟩ : syracuseStep 2251699 = 3377549) B3377549
theorem B5066333 : Blo 2251435 5066333 := bbase (se 3 (by rfl) ⟨949937, by rfl⟩ : syracuseStep 5066333 = 1899875) (by norm_num)
theorem B3377555 : Blo 2251435 3377555 := bstep (se 1 (by rfl) ⟨2533166, by rfl⟩ : syracuseStep 3377555 = 5066333) B5066333
theorem B2251703 : Blo 2251435 2251703 := bstep (se 1 (by rfl) ⟨1688777, by rfl⟩ : syracuseStep 2251703 = 3377555) B3377555
theorem B3799757 : Blo 2251435 3799757 := bbase (se 3 (by rfl) ⟨712454, by rfl⟩ : syracuseStep 3799757 = 1424909) (by norm_num)
theorem B2533171 : Blo 2251435 2533171 := bstep (se 1 (by rfl) ⟨1899878, by rfl⟩ : syracuseStep 2533171 = 3799757) B3799757
theorem B3377561 : Blo 2251435 3377561 := bstep (se 2 (by rfl) ⟨1266585, by rfl⟩ : syracuseStep 3377561 = 2533171) B2533171
theorem B2251707 : Blo 2251435 2251707 := bstep (se 1 (by rfl) ⟨1688780, by rfl⟩ : syracuseStep 2251707 = 3377561) B3377561
theorem B8115317 : Blo 2251435 8115317 := bbase (se 5 (by rfl) ⟨380405, by rfl⟩ : syracuseStep 8115317 = 760811) (by norm_num)
theorem B5410211 : Blo 2251435 5410211 := bstep (se 1 (by rfl) ⟨4057658, by rfl⟩ : syracuseStep 5410211 = 8115317) B8115317
theorem B14427229 : Blo 2251435 14427229 := bstep (se 3 (by rfl) ⟨2705105, by rfl⟩ : syracuseStep 14427229 = 5410211) B5410211
theorem B19236305 : Blo 2251435 19236305 := bstep (se 2 (by rfl) ⟨7213614, by rfl⟩ : syracuseStep 19236305 = 14427229) B14427229
theorem B12824203 : Blo 2251435 12824203 := bstep (se 1 (by rfl) ⟨9618152, by rfl⟩ : syracuseStep 12824203 = 19236305) B19236305
theorem B17098937 : Blo 2251435 17098937 := bstep (se 2 (by rfl) ⟨6412101, by rfl⟩ : syracuseStep 17098937 = 12824203) B12824203
theorem B11399291 : Blo 2251435 11399291 := bstep (se 1 (by rfl) ⟨8549468, by rfl⟩ : syracuseStep 11399291 = 17098937) B17098937
theorem B7599527 : Blo 2251435 7599527 := bstep (se 1 (by rfl) ⟨5699645, by rfl⟩ : syracuseStep 7599527 = 11399291) B11399291
theorem B5066351 : Blo 2251435 5066351 := bstep (se 1 (by rfl) ⟨3799763, by rfl⟩ : syracuseStep 5066351 = 7599527) B7599527
theorem B3377567 : Blo 2251435 3377567 := bstep (se 1 (by rfl) ⟨2533175, by rfl⟩ : syracuseStep 3377567 = 5066351) B5066351
theorem B2251711 : Blo 2251435 2251711 := bstep (se 1 (by rfl) ⟨1688783, by rfl⟩ : syracuseStep 2251711 = 3377567) B3377567
theorem B3377573 : Blo 2251435 3377573 := bbase (se 4 (by rfl) ⟨316647, by rfl⟩ : syracuseStep 3377573 = 633295) (by norm_num)
theorem B2251715 : Blo 2251435 2251715 := bstep (se 1 (by rfl) ⟨1688786, by rfl⟩ : syracuseStep 2251715 = 3377573) B3377573
theorem B2849833 : Blo 2251435 2849833 := bbase (se 2 (by rfl) ⟨1068687, by rfl⟩ : syracuseStep 2849833 = 2137375) (by norm_num)
theorem B3799777 : Blo 2251435 3799777 := bstep (se 2 (by rfl) ⟨1424916, by rfl⟩ : syracuseStep 3799777 = 2849833) B2849833
theorem B5066369 : Blo 2251435 5066369 := bstep (se 2 (by rfl) ⟨1899888, by rfl⟩ : syracuseStep 5066369 = 3799777) B3799777
theorem B3377579 : Blo 2251435 3377579 := bstep (se 1 (by rfl) ⟨2533184, by rfl⟩ : syracuseStep 3377579 = 5066369) B5066369
theorem B2251719 : Blo 2251435 2251719 := bstep (se 1 (by rfl) ⟨1688789, by rfl⟩ : syracuseStep 2251719 = 3377579) B3377579
theorem B2533189 : Blo 2251435 2533189 := bbase (se 4 (by rfl) ⟨237486, by rfl⟩ : syracuseStep 2533189 = 474973) (by norm_num)
theorem B3377585 : Blo 2251435 3377585 := bstep (se 2 (by rfl) ⟨1266594, by rfl⟩ : syracuseStep 3377585 = 2533189) B2533189
theorem B2251723 : Blo 2251435 2251723 := bstep (se 1 (by rfl) ⟨1688792, by rfl⟩ : syracuseStep 2251723 = 3377585) B3377585
theorem B4274765 : Blo 2251435 4274765 := bbase (se 3 (by rfl) ⟨801518, by rfl⟩ : syracuseStep 4274765 = 1603037) (by norm_num)
theorem B2849843 : Blo 2251435 2849843 := bstep (se 1 (by rfl) ⟨2137382, by rfl⟩ : syracuseStep 2849843 = 4274765) B4274765
theorem B7599581 : Blo 2251435 7599581 := bstep (se 3 (by rfl) ⟨1424921, by rfl⟩ : syracuseStep 7599581 = 2849843) B2849843
theorem B5066387 : Blo 2251435 5066387 := bstep (se 1 (by rfl) ⟨3799790, by rfl⟩ : syracuseStep 5066387 = 7599581) B7599581
theorem B3377591 : Blo 2251435 3377591 := bstep (se 1 (by rfl) ⟨2533193, by rfl⟩ : syracuseStep 3377591 = 5066387) B5066387
theorem B2251727 : Blo 2251435 2251727 := bstep (se 1 (by rfl) ⟨1688795, by rfl⟩ : syracuseStep 2251727 = 3377591) B3377591
theorem B3377597 : Blo 2251435 3377597 := bbase (se 3 (by rfl) ⟨633299, by rfl⟩ : syracuseStep 3377597 = 1266599) (by norm_num)
theorem B2251731 : Blo 2251435 2251731 := bstep (se 1 (by rfl) ⟨1688798, by rfl⟩ : syracuseStep 2251731 = 3377597) B3377597
theorem B5066405 : Blo 2251435 5066405 := bbase (se 4 (by rfl) ⟨474975, by rfl⟩ : syracuseStep 5066405 = 949951) (by norm_num)
theorem B3377603 : Blo 2251435 3377603 := bstep (se 1 (by rfl) ⟨2533202, by rfl⟩ : syracuseStep 3377603 = 5066405) B5066405
theorem B2251735 : Blo 2251435 2251735 := bstep (se 1 (by rfl) ⟨1688801, by rfl⟩ : syracuseStep 2251735 = 3377603) B3377603
theorem B5699717 : Blo 2251435 5699717 := bbase (se 4 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 5699717 = 1068697) (by norm_num)
theorem B3799811 : Blo 2251435 3799811 := bstep (se 1 (by rfl) ⟨2849858, by rfl⟩ : syracuseStep 3799811 = 5699717) B5699717
theorem B2533207 : Blo 2251435 2533207 := bstep (se 1 (by rfl) ⟨1899905, by rfl⟩ : syracuseStep 2533207 = 3799811) B3799811
theorem B3377609 : Blo 2251435 3377609 := bstep (se 2 (by rfl) ⟨1266603, by rfl⟩ : syracuseStep 3377609 = 2533207) B2533207
theorem B2251739 : Blo 2251435 2251739 := bstep (se 1 (by rfl) ⟨1688804, by rfl⟩ : syracuseStep 2251739 = 3377609) B3377609
theorem B4057717 : Blo 2251435 4057717 := bbase (se 5 (by rfl) ⟨190205, by rfl⟩ : syracuseStep 4057717 = 380411) (by norm_num)
theorem B5410289 : Blo 2251435 5410289 := bstep (se 2 (by rfl) ⟨2028858, by rfl⟩ : syracuseStep 5410289 = 4057717) B4057717
theorem B3606859 : Blo 2251435 3606859 := bstep (se 1 (by rfl) ⟨2705144, by rfl⟩ : syracuseStep 3606859 = 5410289) B5410289
theorem B4809145 : Blo 2251435 4809145 := bstep (se 2 (by rfl) ⟨1803429, by rfl⟩ : syracuseStep 4809145 = 3606859) B3606859
theorem B6412193 : Blo 2251435 6412193 := bstep (se 2 (by rfl) ⟨2404572, by rfl⟩ : syracuseStep 6412193 = 4809145) B4809145
theorem B4274795 : Blo 2251435 4274795 := bstep (se 1 (by rfl) ⟨3206096, by rfl⟩ : syracuseStep 4274795 = 6412193) B6412193
theorem B11399453 : Blo 2251435 11399453 := bstep (se 3 (by rfl) ⟨2137397, by rfl⟩ : syracuseStep 11399453 = 4274795) B4274795
theorem B7599635 : Blo 2251435 7599635 := bstep (se 1 (by rfl) ⟨5699726, by rfl⟩ : syracuseStep 7599635 = 11399453) B11399453
theorem B5066423 : Blo 2251435 5066423 := bstep (se 1 (by rfl) ⟨3799817, by rfl⟩ : syracuseStep 5066423 = 7599635) B7599635
theorem B3377615 : Blo 2251435 3377615 := bstep (se 1 (by rfl) ⟨2533211, by rfl⟩ : syracuseStep 3377615 = 5066423) B5066423
theorem B2251743 : Blo 2251435 2251743 := bstep (se 1 (by rfl) ⟨1688807, by rfl⟩ : syracuseStep 2251743 = 3377615) B3377615
theorem B3377621 : Blo 2251435 3377621 := bbase (se 7 (by rfl) ⟨39581, by rfl⟩ : syracuseStep 3377621 = 79163) (by norm_num)
theorem B2251747 : Blo 2251435 2251747 := bstep (se 1 (by rfl) ⟨1688810, by rfl⟩ : syracuseStep 2251747 = 3377621) B3377621
theorem B8549621 : Blo 2251435 8549621 := bbase (se 5 (by rfl) ⟨400763, by rfl⟩ : syracuseStep 8549621 = 801527) (by norm_num)
theorem B5699747 : Blo 2251435 5699747 := bstep (se 1 (by rfl) ⟨4274810, by rfl⟩ : syracuseStep 5699747 = 8549621) B8549621
theorem B3799831 : Blo 2251435 3799831 := bstep (se 1 (by rfl) ⟨2849873, by rfl⟩ : syracuseStep 3799831 = 5699747) B5699747
theorem B5066441 : Blo 2251435 5066441 := bstep (se 2 (by rfl) ⟨1899915, by rfl⟩ : syracuseStep 5066441 = 3799831) B3799831
theorem B3377627 : Blo 2251435 3377627 := bstep (se 1 (by rfl) ⟨2533220, by rfl⟩ : syracuseStep 3377627 = 5066441) B5066441
theorem B2251751 : Blo 2251435 2251751 := bstep (se 1 (by rfl) ⟨1688813, by rfl⟩ : syracuseStep 2251751 = 3377627) B3377627
theorem B2533225 : Blo 2251435 2533225 := bbase (se 2 (by rfl) ⟨949959, by rfl⟩ : syracuseStep 2533225 = 1899919) (by norm_num)
theorem B3377633 : Blo 2251435 3377633 := bstep (se 2 (by rfl) ⟨1266612, by rfl⟩ : syracuseStep 3377633 = 2533225) B2533225
theorem B2251755 : Blo 2251435 2251755 := bstep (se 1 (by rfl) ⟨1688816, by rfl⟩ : syracuseStep 2251755 = 3377633) B3377633
theorem B12173237 : Blo 2251435 12173237 := bbase (se 5 (by rfl) ⟨570620, by rfl⟩ : syracuseStep 12173237 = 1141241) (by norm_num)
theorem B8115491 : Blo 2251435 8115491 := bstep (se 1 (by rfl) ⟨6086618, by rfl⟩ : syracuseStep 8115491 = 12173237) B12173237
theorem B5410327 : Blo 2251435 5410327 := bstep (se 1 (by rfl) ⟨4057745, by rfl⟩ : syracuseStep 5410327 = 8115491) B8115491
theorem B7213769 : Blo 2251435 7213769 := bstep (se 2 (by rfl) ⟨2705163, by rfl⟩ : syracuseStep 7213769 = 5410327) B5410327
theorem B4809179 : Blo 2251435 4809179 := bstep (se 1 (by rfl) ⟨3606884, by rfl⟩ : syracuseStep 4809179 = 7213769) B7213769
theorem B12824477 : Blo 2251435 12824477 := bstep (se 3 (by rfl) ⟨2404589, by rfl⟩ : syracuseStep 12824477 = 4809179) B4809179
theorem B8549651 : Blo 2251435 8549651 := bstep (se 1 (by rfl) ⟨6412238, by rfl⟩ : syracuseStep 8549651 = 12824477) B12824477
theorem B5699767 : Blo 2251435 5699767 := bstep (se 1 (by rfl) ⟨4274825, by rfl⟩ : syracuseStep 5699767 = 8549651) B8549651
theorem B7599689 : Blo 2251435 7599689 := bstep (se 2 (by rfl) ⟨2849883, by rfl⟩ : syracuseStep 7599689 = 5699767) B5699767
theorem B5066459 : Blo 2251435 5066459 := bstep (se 1 (by rfl) ⟨3799844, by rfl⟩ : syracuseStep 5066459 = 7599689) B7599689
theorem B3377639 : Blo 2251435 3377639 := bstep (se 1 (by rfl) ⟨2533229, by rfl⟩ : syracuseStep 3377639 = 5066459) B5066459
theorem B2251759 : Blo 2251435 2251759 := bstep (se 1 (by rfl) ⟨1688819, by rfl⟩ : syracuseStep 2251759 = 3377639) B3377639
theorem B3377645 : Blo 2251435 3377645 := bbase (se 3 (by rfl) ⟨633308, by rfl⟩ : syracuseStep 3377645 = 1266617) (by norm_num)
theorem B2251763 : Blo 2251435 2251763 := bstep (se 1 (by rfl) ⟨1688822, by rfl⟩ : syracuseStep 2251763 = 3377645) B3377645
theorem B5066477 : Blo 2251435 5066477 := bbase (se 3 (by rfl) ⟨949964, by rfl⟩ : syracuseStep 5066477 = 1899929) (by norm_num)
theorem B3377651 : Blo 2251435 3377651 := bstep (se 1 (by rfl) ⟨2533238, by rfl⟩ : syracuseStep 3377651 = 5066477) B5066477
theorem B2251767 : Blo 2251435 2251767 := bstep (se 1 (by rfl) ⟨1688825, by rfl⟩ : syracuseStep 2251767 = 3377651) B3377651
theorem B4452221 : Blo 2251435 4452221 := bbase (se 3 (by rfl) ⟨834791, by rfl⟩ : syracuseStep 4452221 = 1669583) (by norm_num)
theorem B2968147 : Blo 2251435 2968147 := bstep (se 1 (by rfl) ⟨2226110, by rfl⟩ : syracuseStep 2968147 = 4452221) B4452221
theorem B3957529 : Blo 2251435 3957529 := bstep (se 2 (by rfl) ⟨1484073, by rfl⟩ : syracuseStep 3957529 = 2968147) B2968147
theorem B84427285 : Blo 2251435 84427285 := bstep (se 6 (by rfl) ⟨1978764, by rfl⟩ : syracuseStep 84427285 = 3957529) B3957529
theorem B112569713 : Blo 2251435 112569713 := bstep (se 2 (by rfl) ⟨42213642, by rfl⟩ : syracuseStep 112569713 = 84427285) B84427285
theorem B75046475 : Blo 2251435 75046475 := bstep (se 1 (by rfl) ⟨56284856, by rfl⟩ : syracuseStep 75046475 = 112569713) B112569713
theorem B50030983 : Blo 2251435 50030983 := bstep (se 1 (by rfl) ⟨37523237, by rfl⟩ : syracuseStep 50030983 = 75046475) B75046475
theorem B66707977 : Blo 2251435 66707977 := bstep (se 2 (by rfl) ⟨25015491, by rfl⟩ : syracuseStep 66707977 = 50030983) B50030983
theorem B88943969 : Blo 2251435 88943969 := bstep (se 2 (by rfl) ⟨33353988, by rfl⟩ : syracuseStep 88943969 = 66707977) B66707977
theorem B59295979 : Blo 2251435 59295979 := bstep (se 1 (by rfl) ⟨44471984, by rfl⟩ : syracuseStep 59295979 = 88943969) B88943969
theorem B316245221 : Blo 2251435 316245221 := bstep (se 4 (by rfl) ⟨29647989, by rfl⟩ : syracuseStep 316245221 = 59295979) B59295979
theorem B210830147 : Blo 2251435 210830147 := bstep (se 1 (by rfl) ⟨158122610, by rfl⟩ : syracuseStep 210830147 = 316245221) B316245221
theorem B140553431 : Blo 2251435 140553431 := bstep (se 1 (by rfl) ⟨105415073, by rfl⟩ : syracuseStep 140553431 = 210830147) B210830147
theorem B93702287 : Blo 2251435 93702287 := bstep (se 1 (by rfl) ⟨70276715, by rfl⟩ : syracuseStep 93702287 = 140553431) B140553431
theorem B62468191 : Blo 2251435 62468191 := bstep (se 1 (by rfl) ⟨46851143, by rfl⟩ : syracuseStep 62468191 = 93702287) B93702287
theorem B333163685 : Blo 2251435 333163685 := bstep (se 4 (by rfl) ⟨31234095, by rfl⟩ : syracuseStep 333163685 = 62468191) B62468191
theorem B222109123 : Blo 2251435 222109123 := bstep (se 1 (by rfl) ⟨166581842, by rfl⟩ : syracuseStep 222109123 = 333163685) B333163685
theorem B296145497 : Blo 2251435 296145497 := bstep (se 2 (by rfl) ⟨111054561, by rfl⟩ : syracuseStep 296145497 = 222109123) B222109123
theorem B197430331 : Blo 2251435 197430331 := bstep (se 1 (by rfl) ⟨148072748, by rfl⟩ : syracuseStep 197430331 = 296145497) B296145497
theorem B263240441 : Blo 2251435 263240441 := bstep (se 2 (by rfl) ⟨98715165, by rfl⟩ : syracuseStep 263240441 = 197430331) B197430331
theorem B175493627 : Blo 2251435 175493627 := bstep (se 1 (by rfl) ⟨131620220, by rfl⟩ : syracuseStep 175493627 = 263240441) B263240441
theorem B116995751 : Blo 2251435 116995751 := bstep (se 1 (by rfl) ⟨87746813, by rfl⟩ : syracuseStep 116995751 = 175493627) B175493627
theorem B77997167 : Blo 2251435 77997167 := bstep (se 1 (by rfl) ⟨58497875, by rfl⟩ : syracuseStep 77997167 = 116995751) B116995751
theorem B51998111 : Blo 2251435 51998111 := bstep (se 1 (by rfl) ⟨38998583, by rfl⟩ : syracuseStep 51998111 = 77997167) B77997167
theorem B34665407 : Blo 2251435 34665407 := bstep (se 1 (by rfl) ⟨25999055, by rfl⟩ : syracuseStep 34665407 = 51998111) B51998111
theorem B23110271 : Blo 2251435 23110271 := bstep (se 1 (by rfl) ⟨17332703, by rfl⟩ : syracuseStep 23110271 = 34665407) B34665407
theorem B15406847 : Blo 2251435 15406847 := bstep (se 1 (by rfl) ⟨11555135, by rfl⟩ : syracuseStep 15406847 = 23110271) B23110271
theorem B10271231 : Blo 2251435 10271231 := bstep (se 1 (by rfl) ⟨7703423, by rfl⟩ : syracuseStep 10271231 = 15406847) B15406847
theorem B6847487 : Blo 2251435 6847487 := bstep (se 1 (by rfl) ⟨5135615, by rfl⟩ : syracuseStep 6847487 = 10271231) B10271231
theorem B4564991 : Blo 2251435 4564991 := bstep (se 1 (by rfl) ⟨3423743, by rfl⟩ : syracuseStep 4564991 = 6847487) B6847487
theorem B3043327 : Blo 2251435 3043327 := bstep (se 1 (by rfl) ⟨2282495, by rfl⟩ : syracuseStep 3043327 = 4564991) B4564991
theorem B4057769 : Blo 2251435 4057769 := bstep (se 2 (by rfl) ⟨1521663, by rfl⟩ : syracuseStep 4057769 = 3043327) B3043327
theorem B2705179 : Blo 2251435 2705179 := bstep (se 1 (by rfl) ⟨2028884, by rfl⟩ : syracuseStep 2705179 = 4057769) B4057769
theorem B3606905 : Blo 2251435 3606905 := bstep (se 2 (by rfl) ⟨1352589, by rfl⟩ : syracuseStep 3606905 = 2705179) B2705179
theorem B2404603 : Blo 2251435 2404603 := bstep (se 1 (by rfl) ⟨1803452, by rfl⟩ : syracuseStep 2404603 = 3606905) B3606905
theorem B3206137 : Blo 2251435 3206137 := bstep (se 2 (by rfl) ⟨1202301, by rfl⟩ : syracuseStep 3206137 = 2404603) B2404603
theorem B4274849 : Blo 2251435 4274849 := bstep (se 2 (by rfl) ⟨1603068, by rfl⟩ : syracuseStep 4274849 = 3206137) B3206137
theorem B2849899 : Blo 2251435 2849899 := bstep (se 1 (by rfl) ⟨2137424, by rfl⟩ : syracuseStep 2849899 = 4274849) B4274849
theorem B3799865 : Blo 2251435 3799865 := bstep (se 2 (by rfl) ⟨1424949, by rfl⟩ : syracuseStep 3799865 = 2849899) B2849899
theorem B2533243 : Blo 2251435 2533243 := bstep (se 1 (by rfl) ⟨1899932, by rfl⟩ : syracuseStep 2533243 = 3799865) B3799865
theorem B3377657 : Blo 2251435 3377657 := bstep (se 2 (by rfl) ⟨1266621, by rfl⟩ : syracuseStep 3377657 = 2533243) B2533243
theorem B2251771 : Blo 2251435 2251771 := bstep (se 1 (by rfl) ⟨1688828, by rfl⟩ : syracuseStep 2251771 = 3377657) B3377657
theorem B5484181 : Blo 2251435 5484181 := bbase (se 6 (by rfl) ⟨128535, by rfl⟩ : syracuseStep 5484181 = 257071) (by norm_num)
theorem B7312241 : Blo 2251435 7312241 := bstep (se 2 (by rfl) ⟨2742090, by rfl⟩ : syracuseStep 7312241 = 5484181) B5484181
theorem B4874827 : Blo 2251435 4874827 := bstep (se 1 (by rfl) ⟨3656120, by rfl⟩ : syracuseStep 4874827 = 7312241) B7312241
theorem B6499769 : Blo 2251435 6499769 := bstep (se 2 (by rfl) ⟨2437413, by rfl⟩ : syracuseStep 6499769 = 4874827) B4874827
theorem B17332717 : Blo 2251435 17332717 := bstep (se 3 (by rfl) ⟨3249884, by rfl⟩ : syracuseStep 17332717 = 6499769) B6499769
theorem B23110289 : Blo 2251435 23110289 := bstep (se 2 (by rfl) ⟨8666358, by rfl⟩ : syracuseStep 23110289 = 17332717) B17332717
theorem B15406859 : Blo 2251435 15406859 := bstep (se 1 (by rfl) ⟨11555144, by rfl⟩ : syracuseStep 15406859 = 23110289) B23110289
theorem B41084957 : Blo 2251435 41084957 := bstep (se 3 (by rfl) ⟨7703429, by rfl⟩ : syracuseStep 41084957 = 15406859) B15406859
theorem B27389971 : Blo 2251435 27389971 := bstep (se 1 (by rfl) ⟨20542478, by rfl⟩ : syracuseStep 27389971 = 41084957) B41084957
theorem B146079845 : Blo 2251435 146079845 := bstep (se 4 (by rfl) ⟨13694985, by rfl⟩ : syracuseStep 146079845 = 27389971) B27389971
theorem B97386563 : Blo 2251435 97386563 := bstep (se 1 (by rfl) ⟨73039922, by rfl⟩ : syracuseStep 97386563 = 146079845) B146079845
theorem B64924375 : Blo 2251435 64924375 := bstep (se 1 (by rfl) ⟨48693281, by rfl⟩ : syracuseStep 64924375 = 97386563) B97386563
theorem B86565833 : Blo 2251435 86565833 := bstep (se 2 (by rfl) ⟨32462187, by rfl⟩ : syracuseStep 86565833 = 64924375) B64924375
theorem B57710555 : Blo 2251435 57710555 := bstep (se 1 (by rfl) ⟨43282916, by rfl⟩ : syracuseStep 57710555 = 86565833) B86565833
theorem B38473703 : Blo 2251435 38473703 := bstep (se 1 (by rfl) ⟨28855277, by rfl⟩ : syracuseStep 38473703 = 57710555) B57710555
theorem B25649135 : Blo 2251435 25649135 := bstep (se 1 (by rfl) ⟨19236851, by rfl⟩ : syracuseStep 25649135 = 38473703) B38473703
theorem B17099423 : Blo 2251435 17099423 := bstep (se 1 (by rfl) ⟨12824567, by rfl⟩ : syracuseStep 17099423 = 25649135) B25649135
theorem B11399615 : Blo 2251435 11399615 := bstep (se 1 (by rfl) ⟨8549711, by rfl⟩ : syracuseStep 11399615 = 17099423) B17099423
theorem B7599743 : Blo 2251435 7599743 := bstep (se 1 (by rfl) ⟨5699807, by rfl⟩ : syracuseStep 7599743 = 11399615) B11399615
theorem B5066495 : Blo 2251435 5066495 := bstep (se 1 (by rfl) ⟨3799871, by rfl⟩ : syracuseStep 5066495 = 7599743) B7599743
theorem B3377663 : Blo 2251435 3377663 := bstep (se 1 (by rfl) ⟨2533247, by rfl⟩ : syracuseStep 3377663 = 5066495) B5066495
theorem B2251775 : Blo 2251435 2251775 := bstep (se 1 (by rfl) ⟨1688831, by rfl⟩ : syracuseStep 2251775 = 3377663) B3377663
theorem B3377669 : Blo 2251435 3377669 := bbase (se 4 (by rfl) ⟨316656, by rfl⟩ : syracuseStep 3377669 = 633313) (by norm_num)
theorem B2251779 : Blo 2251435 2251779 := bstep (se 1 (by rfl) ⟨1688834, by rfl⟩ : syracuseStep 2251779 = 3377669) B3377669
theorem B3799885 : Blo 2251435 3799885 := bbase (se 3 (by rfl) ⟨712478, by rfl⟩ : syracuseStep 3799885 = 1424957) (by norm_num)
theorem B5066513 : Blo 2251435 5066513 := bstep (se 2 (by rfl) ⟨1899942, by rfl⟩ : syracuseStep 5066513 = 3799885) B3799885
theorem B3377675 : Blo 2251435 3377675 := bstep (se 1 (by rfl) ⟨2533256, by rfl⟩ : syracuseStep 3377675 = 5066513) B5066513
theorem B2251783 : Blo 2251435 2251783 := bstep (se 1 (by rfl) ⟨1688837, by rfl⟩ : syracuseStep 2251783 = 3377675) B3377675
theorem B2533261 : Blo 2251435 2533261 := bbase (se 3 (by rfl) ⟨474986, by rfl⟩ : syracuseStep 2533261 = 949973) (by norm_num)
theorem B3377681 : Blo 2251435 3377681 := bstep (se 2 (by rfl) ⟨1266630, by rfl⟩ : syracuseStep 3377681 = 2533261) B2533261
theorem B2251787 : Blo 2251435 2251787 := bstep (se 1 (by rfl) ⟨1688840, by rfl⟩ : syracuseStep 2251787 = 3377681) B3377681
theorem B7599797 : Blo 2251435 7599797 := bbase (se 5 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 7599797 = 712481) (by norm_num)
theorem B5066531 : Blo 2251435 5066531 := bstep (se 1 (by rfl) ⟨3799898, by rfl⟩ : syracuseStep 5066531 = 7599797) B7599797
theorem B3377687 : Blo 2251435 3377687 := bstep (se 1 (by rfl) ⟨2533265, by rfl⟩ : syracuseStep 3377687 = 5066531) B5066531
theorem B2251791 : Blo 2251435 2251791 := bstep (se 1 (by rfl) ⟨1688843, by rfl⟩ : syracuseStep 2251791 = 3377687) B3377687
theorem B3377693 : Blo 2251435 3377693 := bbase (se 3 (by rfl) ⟨633317, by rfl⟩ : syracuseStep 3377693 = 1266635) (by norm_num)
theorem B2251795 : Blo 2251435 2251795 := bstep (se 1 (by rfl) ⟨1688846, by rfl⟩ : syracuseStep 2251795 = 3377693) B3377693
theorem B5066549 : Blo 2251435 5066549 := bbase (se 5 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 5066549 = 474989) (by norm_num)
theorem B3377699 : Blo 2251435 3377699 := bstep (se 1 (by rfl) ⟨2533274, by rfl⟩ : syracuseStep 3377699 = 5066549) B5066549
theorem B2251799 : Blo 2251435 2251799 := bstep (se 1 (by rfl) ⟨1688849, by rfl⟩ : syracuseStep 2251799 = 3377699) B3377699
theorem B21937013 : Blo 2251435 21937013 := bbase (se 5 (by rfl) ⟨1028297, by rfl⟩ : syracuseStep 21937013 = 2056595) (by norm_num)
theorem B14624675 : Blo 2251435 14624675 := bstep (se 1 (by rfl) ⟨10968506, by rfl⟩ : syracuseStep 14624675 = 21937013) B21937013
theorem B9749783 : Blo 2251435 9749783 := bstep (se 1 (by rfl) ⟨7312337, by rfl⟩ : syracuseStep 9749783 = 14624675) B14624675
theorem B6499855 : Blo 2251435 6499855 := bstep (se 1 (by rfl) ⟨4874891, by rfl⟩ : syracuseStep 6499855 = 9749783) B9749783
theorem B8666473 : Blo 2251435 8666473 := bstep (se 2 (by rfl) ⟨3249927, by rfl⟩ : syracuseStep 8666473 = 6499855) B6499855
theorem B11555297 : Blo 2251435 11555297 := bstep (se 2 (by rfl) ⟨4333236, by rfl⟩ : syracuseStep 11555297 = 8666473) B8666473
theorem B7703531 : Blo 2251435 7703531 := bstep (se 1 (by rfl) ⟨5777648, by rfl⟩ : syracuseStep 7703531 = 11555297) B11555297
theorem B5135687 : Blo 2251435 5135687 := bstep (se 1 (by rfl) ⟨3851765, by rfl⟩ : syracuseStep 5135687 = 7703531) B7703531
theorem B3423791 : Blo 2251435 3423791 := bstep (se 1 (by rfl) ⟨2567843, by rfl⟩ : syracuseStep 3423791 = 5135687) B5135687
theorem B2282527 : Blo 2251435 2282527 := bstep (se 1 (by rfl) ⟨1711895, by rfl⟩ : syracuseStep 2282527 = 3423791) B3423791
theorem B3043369 : Blo 2251435 3043369 := bstep (se 2 (by rfl) ⟨1141263, by rfl⟩ : syracuseStep 3043369 = 2282527) B2282527
theorem B4057825 : Blo 2251435 4057825 := bstep (se 2 (by rfl) ⟨1521684, by rfl⟩ : syracuseStep 4057825 = 3043369) B3043369
theorem B5410433 : Blo 2251435 5410433 := bstep (se 2 (by rfl) ⟨2028912, by rfl⟩ : syracuseStep 5410433 = 4057825) B4057825
theorem B14427821 : Blo 2251435 14427821 := bstep (se 3 (by rfl) ⟨2705216, by rfl⟩ : syracuseStep 14427821 = 5410433) B5410433
theorem B9618547 : Blo 2251435 9618547 := bstep (se 1 (by rfl) ⟨7213910, by rfl⟩ : syracuseStep 9618547 = 14427821) B14427821
theorem B12824729 : Blo 2251435 12824729 := bstep (se 2 (by rfl) ⟨4809273, by rfl⟩ : syracuseStep 12824729 = 9618547) B9618547
theorem B8549819 : Blo 2251435 8549819 := bstep (se 1 (by rfl) ⟨6412364, by rfl⟩ : syracuseStep 8549819 = 12824729) B12824729
theorem B5699879 : Blo 2251435 5699879 := bstep (se 1 (by rfl) ⟨4274909, by rfl⟩ : syracuseStep 5699879 = 8549819) B8549819
theorem B3799919 : Blo 2251435 3799919 := bstep (se 1 (by rfl) ⟨2849939, by rfl⟩ : syracuseStep 3799919 = 5699879) B5699879
theorem B2533279 : Blo 2251435 2533279 := bstep (se 1 (by rfl) ⟨1899959, by rfl⟩ : syracuseStep 2533279 = 3799919) B3799919
theorem B3377705 : Blo 2251435 3377705 := bstep (se 2 (by rfl) ⟨1266639, by rfl⟩ : syracuseStep 3377705 = 2533279) B2533279
theorem B2251803 : Blo 2251435 2251803 := bstep (se 1 (by rfl) ⟨1688852, by rfl⟩ : syracuseStep 2251803 = 3377705) B3377705
theorem B2705221 : Blo 2251435 2705221 := bbase (se 4 (by rfl) ⟨253614, by rfl⟩ : syracuseStep 2705221 = 507229) (by norm_num)
theorem B14427845 : Blo 2251435 14427845 := bstep (se 4 (by rfl) ⟨1352610, by rfl⟩ : syracuseStep 14427845 = 2705221) B2705221
theorem B9618563 : Blo 2251435 9618563 := bstep (se 1 (by rfl) ⟨7213922, by rfl⟩ : syracuseStep 9618563 = 14427845) B14427845
theorem B6412375 : Blo 2251435 6412375 := bstep (se 1 (by rfl) ⟨4809281, by rfl⟩ : syracuseStep 6412375 = 9618563) B9618563
theorem B8549833 : Blo 2251435 8549833 := bstep (se 2 (by rfl) ⟨3206187, by rfl⟩ : syracuseStep 8549833 = 6412375) B6412375
theorem B11399777 : Blo 2251435 11399777 := bstep (se 2 (by rfl) ⟨4274916, by rfl⟩ : syracuseStep 11399777 = 8549833) B8549833
theorem B7599851 : Blo 2251435 7599851 := bstep (se 1 (by rfl) ⟨5699888, by rfl⟩ : syracuseStep 7599851 = 11399777) B11399777
theorem B5066567 : Blo 2251435 5066567 := bstep (se 1 (by rfl) ⟨3799925, by rfl⟩ : syracuseStep 5066567 = 7599851) B7599851
theorem B3377711 : Blo 2251435 3377711 := bstep (se 1 (by rfl) ⟨2533283, by rfl⟩ : syracuseStep 3377711 = 5066567) B5066567
theorem B2251807 : Blo 2251435 2251807 := bstep (se 1 (by rfl) ⟨1688855, by rfl⟩ : syracuseStep 2251807 = 3377711) B3377711
theorem B3377717 : Blo 2251435 3377717 := bbase (se 5 (by rfl) ⟨158330, by rfl⟩ : syracuseStep 3377717 = 316661) (by norm_num)
theorem B2251811 : Blo 2251435 2251811 := bstep (se 1 (by rfl) ⟨1688858, by rfl⟩ : syracuseStep 2251811 = 3377717) B3377717
theorem B5699909 : Blo 2251435 5699909 := bbase (se 4 (by rfl) ⟨534366, by rfl⟩ : syracuseStep 5699909 = 1068733) (by norm_num)
theorem B3799939 : Blo 2251435 3799939 := bstep (se 1 (by rfl) ⟨2849954, by rfl⟩ : syracuseStep 3799939 = 5699909) B5699909
theorem B5066585 : Blo 2251435 5066585 := bstep (se 2 (by rfl) ⟨1899969, by rfl⟩ : syracuseStep 5066585 = 3799939) B3799939
theorem B3377723 : Blo 2251435 3377723 := bstep (se 1 (by rfl) ⟨2533292, by rfl⟩ : syracuseStep 3377723 = 5066585) B5066585
theorem B2251815 : Blo 2251435 2251815 := bstep (se 1 (by rfl) ⟨1688861, by rfl⟩ : syracuseStep 2251815 = 3377723) B3377723
theorem B2533297 : Blo 2251435 2533297 := bbase (se 2 (by rfl) ⟨949986, by rfl⟩ : syracuseStep 2533297 = 1899973) (by norm_num)
theorem B3377729 : Blo 2251435 3377729 := bstep (se 2 (by rfl) ⟨1266648, by rfl⟩ : syracuseStep 3377729 = 2533297) B2533297
theorem B2251819 : Blo 2251435 2251819 := bstep (se 1 (by rfl) ⟨1688864, by rfl⟩ : syracuseStep 2251819 = 3377729) B3377729
theorem B6412421 : Blo 2251435 6412421 := bbase (se 4 (by rfl) ⟨601164, by rfl⟩ : syracuseStep 6412421 = 1202329) (by norm_num)
theorem B4274947 : Blo 2251435 4274947 := bstep (se 1 (by rfl) ⟨3206210, by rfl⟩ : syracuseStep 4274947 = 6412421) B6412421
theorem B5699929 : Blo 2251435 5699929 := bstep (se 2 (by rfl) ⟨2137473, by rfl⟩ : syracuseStep 5699929 = 4274947) B4274947
theorem B7599905 : Blo 2251435 7599905 := bstep (se 2 (by rfl) ⟨2849964, by rfl⟩ : syracuseStep 7599905 = 5699929) B5699929
theorem B5066603 : Blo 2251435 5066603 := bstep (se 1 (by rfl) ⟨3799952, by rfl⟩ : syracuseStep 5066603 = 7599905) B7599905
theorem B3377735 : Blo 2251435 3377735 := bstep (se 1 (by rfl) ⟨2533301, by rfl⟩ : syracuseStep 3377735 = 5066603) B5066603
theorem B2251823 : Blo 2251435 2251823 := bstep (se 1 (by rfl) ⟨1688867, by rfl⟩ : syracuseStep 2251823 = 3377735) B3377735
theorem B3377741 : Blo 2251435 3377741 := bbase (se 3 (by rfl) ⟨633326, by rfl⟩ : syracuseStep 3377741 = 1266653) (by norm_num)
theorem B2251827 : Blo 2251435 2251827 := bstep (se 1 (by rfl) ⟨1688870, by rfl⟩ : syracuseStep 2251827 = 3377741) B3377741
theorem B5066621 : Blo 2251435 5066621 := bbase (se 3 (by rfl) ⟨949991, by rfl⟩ : syracuseStep 5066621 = 1899983) (by norm_num)
theorem B3377747 : Blo 2251435 3377747 := bstep (se 1 (by rfl) ⟨2533310, by rfl⟩ : syracuseStep 3377747 = 5066621) B5066621
theorem B2251831 : Blo 2251435 2251831 := bstep (se 1 (by rfl) ⟨1688873, by rfl⟩ : syracuseStep 2251831 = 3377747) B3377747
theorem B3799973 : Blo 2251435 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B2533315 : Blo 2251435 2533315 := bstep (se 1 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 2533315 = 3799973) B3799973
theorem B3377753 : Blo 2251435 3377753 := bstep (se 2 (by rfl) ⟨1266657, by rfl⟩ : syracuseStep 3377753 = 2533315) B2533315
theorem B2251835 : Blo 2251435 2251835 := bstep (se 1 (by rfl) ⟨1688876, by rfl⟩ : syracuseStep 2251835 = 3377753) B3377753
theorem B3607013 : Blo 2251435 3607013 := bbase (se 4 (by rfl) ⟨338157, by rfl⟩ : syracuseStep 3607013 = 676315) (by norm_num)
theorem B2404675 : Blo 2251435 2404675 := bstep (se 1 (by rfl) ⟨1803506, by rfl⟩ : syracuseStep 2404675 = 3607013) B3607013
theorem B3206233 : Blo 2251435 3206233 := bstep (se 2 (by rfl) ⟨1202337, by rfl⟩ : syracuseStep 3206233 = 2404675) B2404675
theorem B17099909 : Blo 2251435 17099909 := bstep (se 4 (by rfl) ⟨1603116, by rfl⟩ : syracuseStep 17099909 = 3206233) B3206233
theorem B11399939 : Blo 2251435 11399939 := bstep (se 1 (by rfl) ⟨8549954, by rfl⟩ : syracuseStep 11399939 = 17099909) B17099909
theorem B7599959 : Blo 2251435 7599959 := bstep (se 1 (by rfl) ⟨5699969, by rfl⟩ : syracuseStep 7599959 = 11399939) B11399939
theorem B5066639 : Blo 2251435 5066639 := bstep (se 1 (by rfl) ⟨3799979, by rfl⟩ : syracuseStep 5066639 = 7599959) B7599959
theorem B3377759 : Blo 2251435 3377759 := bstep (se 1 (by rfl) ⟨2533319, by rfl⟩ : syracuseStep 3377759 = 5066639) B5066639
theorem B2251839 : Blo 2251435 2251839 := bstep (se 1 (by rfl) ⟨1688879, by rfl⟩ : syracuseStep 2251839 = 3377759) B3377759
theorem B3377765 : Blo 2251435 3377765 := bbase (se 4 (by rfl) ⟨316665, by rfl⟩ : syracuseStep 3377765 = 633331) (by norm_num)
theorem B2251843 : Blo 2251435 2251843 := bstep (se 1 (by rfl) ⟨1688882, by rfl⟩ : syracuseStep 2251843 = 3377765) B3377765
theorem B3206245 : Blo 2251435 3206245 := bbase (se 4 (by rfl) ⟨300585, by rfl⟩ : syracuseStep 3206245 = 601171) (by norm_num)
theorem B4274993 : Blo 2251435 4274993 := bstep (se 2 (by rfl) ⟨1603122, by rfl⟩ : syracuseStep 4274993 = 3206245) B3206245
theorem B2849995 : Blo 2251435 2849995 := bstep (se 1 (by rfl) ⟨2137496, by rfl⟩ : syracuseStep 2849995 = 4274993) B4274993
theorem B3799993 : Blo 2251435 3799993 := bstep (se 2 (by rfl) ⟨1424997, by rfl⟩ : syracuseStep 3799993 = 2849995) B2849995
theorem B5066657 : Blo 2251435 5066657 := bstep (se 2 (by rfl) ⟨1899996, by rfl⟩ : syracuseStep 5066657 = 3799993) B3799993
theorem B3377771 : Blo 2251435 3377771 := bstep (se 1 (by rfl) ⟨2533328, by rfl⟩ : syracuseStep 3377771 = 5066657) B5066657
theorem B2251847 : Blo 2251435 2251847 := bstep (se 1 (by rfl) ⟨1688885, by rfl⟩ : syracuseStep 2251847 = 3377771) B3377771
theorem B2533333 : Blo 2251435 2533333 := bbase (se 7 (by rfl) ⟨29687, by rfl⟩ : syracuseStep 2533333 = 59375) (by norm_num)
theorem B3377777 : Blo 2251435 3377777 := bstep (se 2 (by rfl) ⟨1266666, by rfl⟩ : syracuseStep 3377777 = 2533333) B2533333
theorem B2251851 : Blo 2251435 2251851 := bstep (se 1 (by rfl) ⟨1688888, by rfl⟩ : syracuseStep 2251851 = 3377777) B3377777
theorem B2850005 : Blo 2251435 2850005 := bbase (se 7 (by rfl) ⟨33398, by rfl⟩ : syracuseStep 2850005 = 66797) (by norm_num)
theorem B7600013 : Blo 2251435 7600013 := bstep (se 3 (by rfl) ⟨1425002, by rfl⟩ : syracuseStep 7600013 = 2850005) B2850005
theorem B5066675 : Blo 2251435 5066675 := bstep (se 1 (by rfl) ⟨3800006, by rfl⟩ : syracuseStep 5066675 = 7600013) B7600013
theorem B3377783 : Blo 2251435 3377783 := bstep (se 1 (by rfl) ⟨2533337, by rfl⟩ : syracuseStep 3377783 = 5066675) B5066675
theorem B2251855 : Blo 2251435 2251855 := bstep (se 1 (by rfl) ⟨1688891, by rfl⟩ : syracuseStep 2251855 = 3377783) B3377783
theorem B3377789 : Blo 2251435 3377789 := bbase (se 3 (by rfl) ⟨633335, by rfl⟩ : syracuseStep 3377789 = 1266671) (by norm_num)
theorem B2251859 : Blo 2251435 2251859 := bstep (se 1 (by rfl) ⟨1688894, by rfl⟩ : syracuseStep 2251859 = 3377789) B3377789
theorem B5066693 : Blo 2251435 5066693 := bbase (se 4 (by rfl) ⟨475002, by rfl⟩ : syracuseStep 5066693 = 950005) (by norm_num)
theorem B3377795 : Blo 2251435 3377795 := bstep (se 1 (by rfl) ⟨2533346, by rfl⟩ : syracuseStep 3377795 = 5066693) B5066693
theorem B2251863 : Blo 2251435 2251863 := bstep (se 1 (by rfl) ⟨1688897, by rfl⟩ : syracuseStep 2251863 = 3377795) B3377795
theorem B9618821 : Blo 2251435 9618821 := bbase (se 4 (by rfl) ⟨901764, by rfl⟩ : syracuseStep 9618821 = 1803529) (by norm_num)
theorem B6412547 : Blo 2251435 6412547 := bstep (se 1 (by rfl) ⟨4809410, by rfl⟩ : syracuseStep 6412547 = 9618821) B9618821
theorem B4275031 : Blo 2251435 4275031 := bstep (se 1 (by rfl) ⟨3206273, by rfl⟩ : syracuseStep 4275031 = 6412547) B6412547
theorem B5700041 : Blo 2251435 5700041 := bstep (se 2 (by rfl) ⟨2137515, by rfl⟩ : syracuseStep 5700041 = 4275031) B4275031
theorem B3800027 : Blo 2251435 3800027 := bstep (se 1 (by rfl) ⟨2850020, by rfl⟩ : syracuseStep 3800027 = 5700041) B5700041
theorem B2533351 : Blo 2251435 2533351 := bstep (se 1 (by rfl) ⟨1900013, by rfl⟩ : syracuseStep 2533351 = 3800027) B3800027
theorem B3377801 : Blo 2251435 3377801 := bstep (se 2 (by rfl) ⟨1266675, by rfl⟩ : syracuseStep 3377801 = 2533351) B2533351
theorem B2251867 : Blo 2251435 2251867 := bstep (se 1 (by rfl) ⟨1688900, by rfl⟩ : syracuseStep 2251867 = 3377801) B3377801
theorem B11400101 : Blo 2251435 11400101 := bbase (se 4 (by rfl) ⟨1068759, by rfl⟩ : syracuseStep 11400101 = 2137519) (by norm_num)
theorem B7600067 : Blo 2251435 7600067 := bstep (se 1 (by rfl) ⟨5700050, by rfl⟩ : syracuseStep 7600067 = 11400101) B11400101
theorem B5066711 : Blo 2251435 5066711 := bstep (se 1 (by rfl) ⟨3800033, by rfl⟩ : syracuseStep 5066711 = 7600067) B7600067
theorem B3377807 : Blo 2251435 3377807 := bstep (se 1 (by rfl) ⟨2533355, by rfl⟩ : syracuseStep 3377807 = 5066711) B5066711
theorem B2251871 : Blo 2251435 2251871 := bstep (se 1 (by rfl) ⟨1688903, by rfl⟩ : syracuseStep 2251871 = 3377807) B3377807
theorem B3377813 : Blo 2251435 3377813 := bbase (se 6 (by rfl) ⟨79167, by rfl⟩ : syracuseStep 3377813 = 158335) (by norm_num)
theorem B2251875 : Blo 2251435 2251875 := bstep (se 1 (by rfl) ⟨1688906, by rfl⟩ : syracuseStep 2251875 = 3377813) B3377813
theorem B10271717 : Blo 2251435 10271717 := bbase (se 4 (by rfl) ⟨962973, by rfl⟩ : syracuseStep 10271717 = 1925947) (by norm_num)
theorem B6847811 : Blo 2251435 6847811 := bstep (se 1 (by rfl) ⟨5135858, by rfl⟩ : syracuseStep 6847811 = 10271717) B10271717
theorem B4565207 : Blo 2251435 4565207 := bstep (se 1 (by rfl) ⟨3423905, by rfl⟩ : syracuseStep 4565207 = 6847811) B6847811
theorem B12173885 : Blo 2251435 12173885 := bstep (se 3 (by rfl) ⟨2282603, by rfl⟩ : syracuseStep 12173885 = 4565207) B4565207
theorem B8115923 : Blo 2251435 8115923 := bstep (se 1 (by rfl) ⟨6086942, by rfl⟩ : syracuseStep 8115923 = 12173885) B12173885
theorem B21642461 : Blo 2251435 21642461 := bstep (se 3 (by rfl) ⟨4057961, by rfl⟩ : syracuseStep 21642461 = 8115923) B8115923
theorem B14428307 : Blo 2251435 14428307 := bstep (se 1 (by rfl) ⟨10821230, by rfl⟩ : syracuseStep 14428307 = 21642461) B21642461
theorem B9618871 : Blo 2251435 9618871 := bstep (se 1 (by rfl) ⟨7214153, by rfl⟩ : syracuseStep 9618871 = 14428307) B14428307
theorem B12825161 : Blo 2251435 12825161 := bstep (se 2 (by rfl) ⟨4809435, by rfl⟩ : syracuseStep 12825161 = 9618871) B9618871
theorem B8550107 : Blo 2251435 8550107 := bstep (se 1 (by rfl) ⟨6412580, by rfl⟩ : syracuseStep 8550107 = 12825161) B12825161
theorem B5700071 : Blo 2251435 5700071 := bstep (se 1 (by rfl) ⟨4275053, by rfl⟩ : syracuseStep 5700071 = 8550107) B8550107
theorem B3800047 : Blo 2251435 3800047 := bstep (se 1 (by rfl) ⟨2850035, by rfl⟩ : syracuseStep 3800047 = 5700071) B5700071
theorem B5066729 : Blo 2251435 5066729 := bstep (se 2 (by rfl) ⟨1900023, by rfl⟩ : syracuseStep 5066729 = 3800047) B3800047
theorem B3377819 : Blo 2251435 3377819 := bstep (se 1 (by rfl) ⟨2533364, by rfl⟩ : syracuseStep 3377819 = 5066729) B5066729
theorem B2251879 : Blo 2251435 2251879 := bstep (se 1 (by rfl) ⟨1688909, by rfl⟩ : syracuseStep 2251879 = 3377819) B3377819
theorem B2533369 : Blo 2251435 2533369 := bbase (se 2 (by rfl) ⟨950013, by rfl⟩ : syracuseStep 2533369 = 1900027) (by norm_num)
theorem B3377825 : Blo 2251435 3377825 := bstep (se 2 (by rfl) ⟨1266684, by rfl⟩ : syracuseStep 3377825 = 2533369) B2533369
theorem B2251883 : Blo 2251435 2251883 := bstep (se 1 (by rfl) ⟨1688912, by rfl⟩ : syracuseStep 2251883 = 3377825) B3377825
theorem B10821269 : Blo 2251435 10821269 := bbase (se 6 (by rfl) ⟨253623, by rfl⟩ : syracuseStep 10821269 = 507247) (by norm_num)
theorem B7214179 : Blo 2251435 7214179 := bstep (se 1 (by rfl) ⟨5410634, by rfl⟩ : syracuseStep 7214179 = 10821269) B10821269
theorem B9618905 : Blo 2251435 9618905 := bstep (se 2 (by rfl) ⟨3607089, by rfl⟩ : syracuseStep 9618905 = 7214179) B7214179
theorem B6412603 : Blo 2251435 6412603 := bstep (se 1 (by rfl) ⟨4809452, by rfl⟩ : syracuseStep 6412603 = 9618905) B9618905
theorem B8550137 : Blo 2251435 8550137 := bstep (se 2 (by rfl) ⟨3206301, by rfl⟩ : syracuseStep 8550137 = 6412603) B6412603
theorem B5700091 : Blo 2251435 5700091 := bstep (se 1 (by rfl) ⟨4275068, by rfl⟩ : syracuseStep 5700091 = 8550137) B8550137
theorem B7600121 : Blo 2251435 7600121 := bstep (se 2 (by rfl) ⟨2850045, by rfl⟩ : syracuseStep 7600121 = 5700091) B5700091
theorem B5066747 : Blo 2251435 5066747 := bstep (se 1 (by rfl) ⟨3800060, by rfl⟩ : syracuseStep 5066747 = 7600121) B7600121
theorem B3377831 : Blo 2251435 3377831 := bstep (se 1 (by rfl) ⟨2533373, by rfl⟩ : syracuseStep 3377831 = 5066747) B5066747
theorem B2251887 : Blo 2251435 2251887 := bstep (se 1 (by rfl) ⟨1688915, by rfl⟩ : syracuseStep 2251887 = 3377831) B3377831
theorem B3377837 : Blo 2251435 3377837 := bbase (se 3 (by rfl) ⟨633344, by rfl⟩ : syracuseStep 3377837 = 1266689) (by norm_num)
theorem B2251891 : Blo 2251435 2251891 := bstep (se 1 (by rfl) ⟨1688918, by rfl⟩ : syracuseStep 2251891 = 3377837) B3377837
theorem B5066765 : Blo 2251435 5066765 := bbase (se 3 (by rfl) ⟨950018, by rfl⟩ : syracuseStep 5066765 = 1900037) (by norm_num)
theorem B3377843 : Blo 2251435 3377843 := bstep (se 1 (by rfl) ⟨2533382, by rfl⟩ : syracuseStep 3377843 = 5066765) B5066765
theorem B2251895 : Blo 2251435 2251895 := bstep (se 1 (by rfl) ⟨1688921, by rfl⟩ : syracuseStep 2251895 = 3377843) B3377843
theorem B2850061 : Blo 2251435 2850061 := bbase (se 3 (by rfl) ⟨534386, by rfl⟩ : syracuseStep 2850061 = 1068773) (by norm_num)
theorem B3800081 : Blo 2251435 3800081 := bstep (se 2 (by rfl) ⟨1425030, by rfl⟩ : syracuseStep 3800081 = 2850061) B2850061
theorem B2533387 : Blo 2251435 2533387 := bstep (se 1 (by rfl) ⟨1900040, by rfl⟩ : syracuseStep 2533387 = 3800081) B3800081
theorem B3377849 : Blo 2251435 3377849 := bstep (se 2 (by rfl) ⟨1266693, by rfl⟩ : syracuseStep 3377849 = 2533387) B2533387
theorem B2251899 : Blo 2251435 2251899 := bstep (se 1 (by rfl) ⟨1688924, by rfl⟩ : syracuseStep 2251899 = 3377849) B3377849
theorem B2437553 : Blo 2251435 2437553 := bbase (se 2 (by rfl) ⟨914082, by rfl⟩ : syracuseStep 2437553 = 1828165) (by norm_num)
theorem B6500141 : Blo 2251435 6500141 := bstep (se 3 (by rfl) ⟨1218776, by rfl⟩ : syracuseStep 6500141 = 2437553) B2437553
theorem B4333427 : Blo 2251435 4333427 := bstep (se 1 (by rfl) ⟨3250070, by rfl⟩ : syracuseStep 4333427 = 6500141) B6500141
theorem B2888951 : Blo 2251435 2888951 := bstep (se 1 (by rfl) ⟨2166713, by rfl⟩ : syracuseStep 2888951 = 4333427) B4333427
theorem B7703869 : Blo 2251435 7703869 := bstep (se 3 (by rfl) ⟨1444475, by rfl⟩ : syracuseStep 7703869 = 2888951) B2888951
theorem B10271825 : Blo 2251435 10271825 := bstep (se 2 (by rfl) ⟨3851934, by rfl⟩ : syracuseStep 10271825 = 7703869) B7703869
theorem B6847883 : Blo 2251435 6847883 := bstep (se 1 (by rfl) ⟨5135912, by rfl⟩ : syracuseStep 6847883 = 10271825) B10271825
theorem B4565255 : Blo 2251435 4565255 := bstep (se 1 (by rfl) ⟨3423941, by rfl⟩ : syracuseStep 4565255 = 6847883) B6847883
theorem B12174013 : Blo 2251435 12174013 := bstep (se 3 (by rfl) ⟨2282627, by rfl⟩ : syracuseStep 12174013 = 4565255) B4565255
theorem B16232017 : Blo 2251435 16232017 := bstep (se 2 (by rfl) ⟨6087006, by rfl⟩ : syracuseStep 16232017 = 12174013) B12174013
theorem B21642689 : Blo 2251435 21642689 := bstep (se 2 (by rfl) ⟨8116008, by rfl⟩ : syracuseStep 21642689 = 16232017) B16232017
theorem B14428459 : Blo 2251435 14428459 := bstep (se 1 (by rfl) ⟨10821344, by rfl⟩ : syracuseStep 14428459 = 21642689) B21642689
theorem B19237945 : Blo 2251435 19237945 := bstep (se 2 (by rfl) ⟨7214229, by rfl⟩ : syracuseStep 19237945 = 14428459) B14428459
theorem B25650593 : Blo 2251435 25650593 := bstep (se 2 (by rfl) ⟨9618972, by rfl⟩ : syracuseStep 25650593 = 19237945) B19237945
theorem B17100395 : Blo 2251435 17100395 := bstep (se 1 (by rfl) ⟨12825296, by rfl⟩ : syracuseStep 17100395 = 25650593) B25650593
theorem B11400263 : Blo 2251435 11400263 := bstep (se 1 (by rfl) ⟨8550197, by rfl⟩ : syracuseStep 11400263 = 17100395) B17100395
theorem B7600175 : Blo 2251435 7600175 := bstep (se 1 (by rfl) ⟨5700131, by rfl⟩ : syracuseStep 7600175 = 11400263) B11400263
theorem B5066783 : Blo 2251435 5066783 := bstep (se 1 (by rfl) ⟨3800087, by rfl⟩ : syracuseStep 5066783 = 7600175) B7600175
theorem B3377855 : Blo 2251435 3377855 := bstep (se 1 (by rfl) ⟨2533391, by rfl⟩ : syracuseStep 3377855 = 5066783) B5066783
theorem B2251903 : Blo 2251435 2251903 := bstep (se 1 (by rfl) ⟨1688927, by rfl⟩ : syracuseStep 2251903 = 3377855) B3377855
theorem B3377861 : Blo 2251435 3377861 := bbase (se 4 (by rfl) ⟨316674, by rfl⟩ : syracuseStep 3377861 = 633349) (by norm_num)
theorem B2251907 : Blo 2251435 2251907 := bstep (se 1 (by rfl) ⟨1688930, by rfl⟩ : syracuseStep 2251907 = 3377861) B3377861
theorem B3800101 : Blo 2251435 3800101 := bbase (se 4 (by rfl) ⟨356259, by rfl⟩ : syracuseStep 3800101 = 712519) (by norm_num)
theorem B5066801 : Blo 2251435 5066801 := bstep (se 2 (by rfl) ⟨1900050, by rfl⟩ : syracuseStep 5066801 = 3800101) B3800101
theorem B3377867 : Blo 2251435 3377867 := bstep (se 1 (by rfl) ⟨2533400, by rfl⟩ : syracuseStep 3377867 = 5066801) B5066801
theorem B2251911 : Blo 2251435 2251911 := bstep (se 1 (by rfl) ⟨1688933, by rfl⟩ : syracuseStep 2251911 = 3377867) B3377867
theorem B2533405 : Blo 2251435 2533405 := bbase (se 3 (by rfl) ⟨475013, by rfl⟩ : syracuseStep 2533405 = 950027) (by norm_num)
theorem B3377873 : Blo 2251435 3377873 := bstep (se 2 (by rfl) ⟨1266702, by rfl⟩ : syracuseStep 3377873 = 2533405) B2533405
theorem B2251915 : Blo 2251435 2251915 := bstep (se 1 (by rfl) ⟨1688936, by rfl⟩ : syracuseStep 2251915 = 3377873) B3377873
theorem B7600229 : Blo 2251435 7600229 := bbase (se 4 (by rfl) ⟨712521, by rfl⟩ : syracuseStep 7600229 = 1425043) (by norm_num)
theorem B5066819 : Blo 2251435 5066819 := bstep (se 1 (by rfl) ⟨3800114, by rfl⟩ : syracuseStep 5066819 = 7600229) B7600229
theorem B3377879 : Blo 2251435 3377879 := bstep (se 1 (by rfl) ⟨2533409, by rfl⟩ : syracuseStep 3377879 = 5066819) B5066819
theorem B2251919 : Blo 2251435 2251919 := bstep (se 1 (by rfl) ⟨1688939, by rfl⟩ : syracuseStep 2251919 = 3377879) B3377879
theorem B3377885 : Blo 2251435 3377885 := bbase (se 3 (by rfl) ⟨633353, by rfl⟩ : syracuseStep 3377885 = 1266707) (by norm_num)
theorem B2251923 : Blo 2251435 2251923 := bstep (se 1 (by rfl) ⟨1688942, by rfl⟩ : syracuseStep 2251923 = 3377885) B3377885
theorem B5066837 : Blo 2251435 5066837 := bbase (se 8 (by rfl) ⟨29688, by rfl⟩ : syracuseStep 5066837 = 59377) (by norm_num)
theorem B3377891 : Blo 2251435 3377891 := bstep (se 1 (by rfl) ⟨2533418, by rfl⟩ : syracuseStep 3377891 = 5066837) B5066837
theorem B2251927 : Blo 2251435 2251927 := bstep (se 1 (by rfl) ⟨1688945, by rfl⟩ : syracuseStep 2251927 = 3377891) B3377891
theorem B5410741 : Blo 2251435 5410741 := bbase (se 5 (by rfl) ⟨253628, by rfl⟩ : syracuseStep 5410741 = 507257) (by norm_num)
theorem B7214321 : Blo 2251435 7214321 := bstep (se 2 (by rfl) ⟨2705370, by rfl⟩ : syracuseStep 7214321 = 5410741) B5410741
theorem B4809547 : Blo 2251435 4809547 := bstep (se 1 (by rfl) ⟨3607160, by rfl⟩ : syracuseStep 4809547 = 7214321) B7214321
theorem B6412729 : Blo 2251435 6412729 := bstep (se 2 (by rfl) ⟨2404773, by rfl⟩ : syracuseStep 6412729 = 4809547) B4809547
theorem B8550305 : Blo 2251435 8550305 := bstep (se 2 (by rfl) ⟨3206364, by rfl⟩ : syracuseStep 8550305 = 6412729) B6412729
theorem B5700203 : Blo 2251435 5700203 := bstep (se 1 (by rfl) ⟨4275152, by rfl⟩ : syracuseStep 5700203 = 8550305) B8550305
theorem B3800135 : Blo 2251435 3800135 := bstep (se 1 (by rfl) ⟨2850101, by rfl⟩ : syracuseStep 3800135 = 5700203) B5700203
theorem B2533423 : Blo 2251435 2533423 := bstep (se 1 (by rfl) ⟨1900067, by rfl⟩ : syracuseStep 2533423 = 3800135) B3800135
theorem B3377897 : Blo 2251435 3377897 := bstep (se 2 (by rfl) ⟨1266711, by rfl⟩ : syracuseStep 3377897 = 2533423) B2533423
theorem B2251931 : Blo 2251435 2251931 := bstep (se 1 (by rfl) ⟨1688948, by rfl⟩ : syracuseStep 2251931 = 3377897) B3377897
theorem B21642997 : Blo 2251435 21642997 := bbase (se 5 (by rfl) ⟨1014515, by rfl⟩ : syracuseStep 21642997 = 2029031) (by norm_num)
theorem B28857329 : Blo 2251435 28857329 := bstep (se 2 (by rfl) ⟨10821498, by rfl⟩ : syracuseStep 28857329 = 21642997) B21642997
theorem B19238219 : Blo 2251435 19238219 := bstep (se 1 (by rfl) ⟨14428664, by rfl⟩ : syracuseStep 19238219 = 28857329) B28857329
theorem B12825479 : Blo 2251435 12825479 := bstep (se 1 (by rfl) ⟨9619109, by rfl⟩ : syracuseStep 12825479 = 19238219) B19238219
theorem B8550319 : Blo 2251435 8550319 := bstep (se 1 (by rfl) ⟨6412739, by rfl⟩ : syracuseStep 8550319 = 12825479) B12825479
theorem B11400425 : Blo 2251435 11400425 := bstep (se 2 (by rfl) ⟨4275159, by rfl⟩ : syracuseStep 11400425 = 8550319) B8550319
theorem B7600283 : Blo 2251435 7600283 := bstep (se 1 (by rfl) ⟨5700212, by rfl⟩ : syracuseStep 7600283 = 11400425) B11400425
theorem B5066855 : Blo 2251435 5066855 := bstep (se 1 (by rfl) ⟨3800141, by rfl⟩ : syracuseStep 5066855 = 7600283) B7600283
theorem B3377903 : Blo 2251435 3377903 := bstep (se 1 (by rfl) ⟨2533427, by rfl⟩ : syracuseStep 3377903 = 5066855) B5066855
theorem B2251935 : Blo 2251435 2251935 := bstep (se 1 (by rfl) ⟨1688951, by rfl⟩ : syracuseStep 2251935 = 3377903) B3377903
theorem B3377909 : Blo 2251435 3377909 := bbase (se 5 (by rfl) ⟨158339, by rfl⟩ : syracuseStep 3377909 = 316679) (by norm_num)
theorem B2251939 : Blo 2251435 2251939 := bstep (se 1 (by rfl) ⟨1688954, by rfl⟩ : syracuseStep 2251939 = 3377909) B3377909
theorem B16232309 : Blo 2251435 16232309 := bbase (se 5 (by rfl) ⟨760889, by rfl⟩ : syracuseStep 16232309 = 1521779) (by norm_num)
theorem B10821539 : Blo 2251435 10821539 := bstep (se 1 (by rfl) ⟨8116154, by rfl⟩ : syracuseStep 10821539 = 16232309) B16232309
theorem B7214359 : Blo 2251435 7214359 := bstep (se 1 (by rfl) ⟨5410769, by rfl⟩ : syracuseStep 7214359 = 10821539) B10821539
theorem B9619145 : Blo 2251435 9619145 := bstep (se 2 (by rfl) ⟨3607179, by rfl⟩ : syracuseStep 9619145 = 7214359) B7214359
theorem B6412763 : Blo 2251435 6412763 := bstep (se 1 (by rfl) ⟨4809572, by rfl⟩ : syracuseStep 6412763 = 9619145) B9619145
theorem B4275175 : Blo 2251435 4275175 := bstep (se 1 (by rfl) ⟨3206381, by rfl⟩ : syracuseStep 4275175 = 6412763) B6412763
theorem B5700233 : Blo 2251435 5700233 := bstep (se 2 (by rfl) ⟨2137587, by rfl⟩ : syracuseStep 5700233 = 4275175) B4275175
theorem B3800155 : Blo 2251435 3800155 := bstep (se 1 (by rfl) ⟨2850116, by rfl⟩ : syracuseStep 3800155 = 5700233) B5700233
theorem B5066873 : Blo 2251435 5066873 := bstep (se 2 (by rfl) ⟨1900077, by rfl⟩ : syracuseStep 5066873 = 3800155) B3800155
theorem B3377915 : Blo 2251435 3377915 := bstep (se 1 (by rfl) ⟨2533436, by rfl⟩ : syracuseStep 3377915 = 5066873) B5066873
theorem B2251943 : Blo 2251435 2251943 := bstep (se 1 (by rfl) ⟨1688957, by rfl⟩ : syracuseStep 2251943 = 3377915) B3377915
theorem B2533441 : Blo 2251435 2533441 := bbase (se 2 (by rfl) ⟨950040, by rfl⟩ : syracuseStep 2533441 = 1900081) (by norm_num)
theorem B3377921 : Blo 2251435 3377921 := bstep (se 2 (by rfl) ⟨1266720, by rfl⟩ : syracuseStep 3377921 = 2533441) B2533441
theorem B2251947 : Blo 2251435 2251947 := bstep (se 1 (by rfl) ⟨1688960, by rfl⟩ : syracuseStep 2251947 = 3377921) B3377921
theorem B5700253 : Blo 2251435 5700253 := bbase (se 3 (by rfl) ⟨1068797, by rfl⟩ : syracuseStep 5700253 = 2137595) (by norm_num)
theorem B7600337 : Blo 2251435 7600337 := bstep (se 2 (by rfl) ⟨2850126, by rfl⟩ : syracuseStep 7600337 = 5700253) B5700253
theorem B5066891 : Blo 2251435 5066891 := bstep (se 1 (by rfl) ⟨3800168, by rfl⟩ : syracuseStep 5066891 = 7600337) B7600337
theorem B3377927 : Blo 2251435 3377927 := bstep (se 1 (by rfl) ⟨2533445, by rfl⟩ : syracuseStep 3377927 = 5066891) B5066891
theorem B2251951 : Blo 2251435 2251951 := bstep (se 1 (by rfl) ⟨1688963, by rfl⟩ : syracuseStep 2251951 = 3377927) B3377927
theorem B3377933 : Blo 2251435 3377933 := bbase (se 3 (by rfl) ⟨633362, by rfl⟩ : syracuseStep 3377933 = 1266725) (by norm_num)
theorem B2251955 : Blo 2251435 2251955 := bstep (se 1 (by rfl) ⟨1688966, by rfl⟩ : syracuseStep 2251955 = 3377933) B3377933
theorem B5066909 : Blo 2251435 5066909 := bbase (se 3 (by rfl) ⟨950045, by rfl⟩ : syracuseStep 5066909 = 1900091) (by norm_num)
theorem B3377939 : Blo 2251435 3377939 := bstep (se 1 (by rfl) ⟨2533454, by rfl⟩ : syracuseStep 3377939 = 5066909) B5066909
theorem B2251959 : Blo 2251435 2251959 := bstep (se 1 (by rfl) ⟨1688969, by rfl⟩ : syracuseStep 2251959 = 3377939) B3377939
theorem B3800189 : Blo 2251435 3800189 := bbase (se 3 (by rfl) ⟨712535, by rfl⟩ : syracuseStep 3800189 = 1425071) (by norm_num)
theorem B2533459 : Blo 2251435 2533459 := bstep (se 1 (by rfl) ⟨1900094, by rfl⟩ : syracuseStep 2533459 = 3800189) B3800189
theorem B3377945 : Blo 2251435 3377945 := bstep (se 2 (by rfl) ⟨1266729, by rfl⟩ : syracuseStep 3377945 = 2533459) B2533459
theorem B2251963 : Blo 2251435 2251963 := bstep (se 1 (by rfl) ⟨1688972, by rfl⟩ : syracuseStep 2251963 = 3377945) B3377945
theorem B10821653 : Blo 2251435 10821653 := bbase (se 6 (by rfl) ⟨253632, by rfl⟩ : syracuseStep 10821653 = 507265) (by norm_num)
theorem B7214435 : Blo 2251435 7214435 := bstep (se 1 (by rfl) ⟨5410826, by rfl⟩ : syracuseStep 7214435 = 10821653) B10821653
theorem B4809623 : Blo 2251435 4809623 := bstep (se 1 (by rfl) ⟨3607217, by rfl⟩ : syracuseStep 4809623 = 7214435) B7214435
theorem B12825661 : Blo 2251435 12825661 := bstep (se 3 (by rfl) ⟨2404811, by rfl⟩ : syracuseStep 12825661 = 4809623) B4809623
theorem B17100881 : Blo 2251435 17100881 := bstep (se 2 (by rfl) ⟨6412830, by rfl⟩ : syracuseStep 17100881 = 12825661) B12825661
theorem B11400587 : Blo 2251435 11400587 := bstep (se 1 (by rfl) ⟨8550440, by rfl⟩ : syracuseStep 11400587 = 17100881) B17100881
theorem B7600391 : Blo 2251435 7600391 := bstep (se 1 (by rfl) ⟨5700293, by rfl⟩ : syracuseStep 7600391 = 11400587) B11400587
theorem B5066927 : Blo 2251435 5066927 := bstep (se 1 (by rfl) ⟨3800195, by rfl⟩ : syracuseStep 5066927 = 7600391) B7600391
theorem B3377951 : Blo 2251435 3377951 := bstep (se 1 (by rfl) ⟨2533463, by rfl⟩ : syracuseStep 3377951 = 5066927) B5066927
theorem B2251967 : Blo 2251435 2251967 := bstep (se 1 (by rfl) ⟨1688975, by rfl⟩ : syracuseStep 2251967 = 3377951) B3377951
theorem B3377957 : Blo 2251435 3377957 := bbase (se 4 (by rfl) ⟨316683, by rfl⟩ : syracuseStep 3377957 = 633367) (by norm_num)
theorem B2251971 : Blo 2251435 2251971 := bstep (se 1 (by rfl) ⟨1688978, by rfl⟩ : syracuseStep 2251971 = 3377957) B3377957
theorem B2850157 : Blo 2251435 2850157 := bbase (se 3 (by rfl) ⟨534404, by rfl⟩ : syracuseStep 2850157 = 1068809) (by norm_num)
theorem B3800209 : Blo 2251435 3800209 := bstep (se 2 (by rfl) ⟨1425078, by rfl⟩ : syracuseStep 3800209 = 2850157) B2850157
theorem B5066945 : Blo 2251435 5066945 := bstep (se 2 (by rfl) ⟨1900104, by rfl⟩ : syracuseStep 5066945 = 3800209) B3800209
theorem B3377963 : Blo 2251435 3377963 := bstep (se 1 (by rfl) ⟨2533472, by rfl⟩ : syracuseStep 3377963 = 5066945) B5066945
theorem B2251975 : Blo 2251435 2251975 := bstep (se 1 (by rfl) ⟨1688981, by rfl⟩ : syracuseStep 2251975 = 3377963) B3377963
theorem B2533477 : Blo 2251435 2533477 := bbase (se 4 (by rfl) ⟨237513, by rfl⟩ : syracuseStep 2533477 = 475027) (by norm_num)
theorem B3377969 : Blo 2251435 3377969 := bstep (se 2 (by rfl) ⟨1266738, by rfl⟩ : syracuseStep 3377969 = 2533477) B2533477
theorem B2251979 : Blo 2251435 2251979 := bstep (se 1 (by rfl) ⟨1688984, by rfl⟩ : syracuseStep 2251979 = 3377969) B3377969
theorem B2404829 : Blo 2251435 2404829 := bbase (se 3 (by rfl) ⟨450905, by rfl⟩ : syracuseStep 2404829 = 901811) (by norm_num)
theorem B6412877 : Blo 2251435 6412877 := bstep (se 3 (by rfl) ⟨1202414, by rfl⟩ : syracuseStep 6412877 = 2404829) B2404829
theorem B4275251 : Blo 2251435 4275251 := bstep (se 1 (by rfl) ⟨3206438, by rfl⟩ : syracuseStep 4275251 = 6412877) B6412877
theorem B2850167 : Blo 2251435 2850167 := bstep (se 1 (by rfl) ⟨2137625, by rfl⟩ : syracuseStep 2850167 = 4275251) B4275251
theorem B7600445 : Blo 2251435 7600445 := bstep (se 3 (by rfl) ⟨1425083, by rfl⟩ : syracuseStep 7600445 = 2850167) B2850167
theorem B5066963 : Blo 2251435 5066963 := bstep (se 1 (by rfl) ⟨3800222, by rfl⟩ : syracuseStep 5066963 = 7600445) B7600445
theorem B3377975 : Blo 2251435 3377975 := bstep (se 1 (by rfl) ⟨2533481, by rfl⟩ : syracuseStep 3377975 = 5066963) B5066963
theorem B2251983 : Blo 2251435 2251983 := bstep (se 1 (by rfl) ⟨1688987, by rfl⟩ : syracuseStep 2251983 = 3377975) B3377975
theorem B3377981 : Blo 2251435 3377981 := bbase (se 3 (by rfl) ⟨633371, by rfl⟩ : syracuseStep 3377981 = 1266743) (by norm_num)
theorem B2251987 : Blo 2251435 2251987 := bstep (se 1 (by rfl) ⟨1688990, by rfl⟩ : syracuseStep 2251987 = 3377981) B3377981
theorem B5066981 : Blo 2251435 5066981 := bbase (se 4 (by rfl) ⟨475029, by rfl⟩ : syracuseStep 5066981 = 950059) (by norm_num)
theorem B3377987 : Blo 2251435 3377987 := bstep (se 1 (by rfl) ⟨2533490, by rfl⟩ : syracuseStep 3377987 = 5066981) B5066981
theorem B2251991 : Blo 2251435 2251991 := bstep (se 1 (by rfl) ⟨1688993, by rfl⟩ : syracuseStep 2251991 = 3377987) B3377987
theorem B5700365 : Blo 2251435 5700365 := bbase (se 3 (by rfl) ⟨1068818, by rfl⟩ : syracuseStep 5700365 = 2137637) (by norm_num)
theorem B3800243 : Blo 2251435 3800243 := bstep (se 1 (by rfl) ⟨2850182, by rfl⟩ : syracuseStep 3800243 = 5700365) B5700365
theorem B2533495 : Blo 2251435 2533495 := bstep (se 1 (by rfl) ⟨1900121, by rfl⟩ : syracuseStep 2533495 = 3800243) B3800243
theorem B3377993 : Blo 2251435 3377993 := bstep (se 2 (by rfl) ⟨1266747, by rfl⟩ : syracuseStep 3377993 = 2533495) B2533495
theorem B2251995 : Blo 2251435 2251995 := bstep (se 1 (by rfl) ⟨1688996, by rfl⟩ : syracuseStep 2251995 = 3377993) B3377993
theorem B3206461 : Blo 2251435 3206461 := bbase (se 3 (by rfl) ⟨601211, by rfl⟩ : syracuseStep 3206461 = 1202423) (by norm_num)
theorem B4275281 : Blo 2251435 4275281 := bstep (se 2 (by rfl) ⟨1603230, by rfl⟩ : syracuseStep 4275281 = 3206461) B3206461
theorem B11400749 : Blo 2251435 11400749 := bstep (se 3 (by rfl) ⟨2137640, by rfl⟩ : syracuseStep 11400749 = 4275281) B4275281
theorem B7600499 : Blo 2251435 7600499 := bstep (se 1 (by rfl) ⟨5700374, by rfl⟩ : syracuseStep 7600499 = 11400749) B11400749
theorem B5066999 : Blo 2251435 5066999 := bstep (se 1 (by rfl) ⟨3800249, by rfl⟩ : syracuseStep 5066999 = 7600499) B7600499
theorem B3377999 : Blo 2251435 3377999 := bstep (se 1 (by rfl) ⟨2533499, by rfl⟩ : syracuseStep 3377999 = 5066999) B5066999
theorem B2251999 : Blo 2251435 2251999 := bstep (se 1 (by rfl) ⟨1688999, by rfl⟩ : syracuseStep 2251999 = 3377999) B3377999
theorem B3378005 : Blo 2251435 3378005 := bbase (se 9 (by rfl) ⟨9896, by rfl⟩ : syracuseStep 3378005 = 19793) (by norm_num)
theorem B2252003 : Blo 2251435 2252003 := bstep (se 1 (by rfl) ⟨1689002, by rfl⟩ : syracuseStep 2252003 = 3378005) B3378005
theorem B4809709 : Blo 2251435 4809709 := bbase (se 3 (by rfl) ⟨901820, by rfl⟩ : syracuseStep 4809709 = 1803641) (by norm_num)
theorem B6412945 : Blo 2251435 6412945 := bstep (se 2 (by rfl) ⟨2404854, by rfl⟩ : syracuseStep 6412945 = 4809709) B4809709
theorem B8550593 : Blo 2251435 8550593 := bstep (se 2 (by rfl) ⟨3206472, by rfl⟩ : syracuseStep 8550593 = 6412945) B6412945
theorem B5700395 : Blo 2251435 5700395 := bstep (se 1 (by rfl) ⟨4275296, by rfl⟩ : syracuseStep 5700395 = 8550593) B8550593
theorem B3800263 : Blo 2251435 3800263 := bstep (se 1 (by rfl) ⟨2850197, by rfl⟩ : syracuseStep 3800263 = 5700395) B5700395
theorem B5067017 : Blo 2251435 5067017 := bstep (se 2 (by rfl) ⟨1900131, by rfl⟩ : syracuseStep 5067017 = 3800263) B3800263
theorem B3378011 : Blo 2251435 3378011 := bstep (se 1 (by rfl) ⟨2533508, by rfl⟩ : syracuseStep 3378011 = 5067017) B5067017
theorem B2252007 : Blo 2251435 2252007 := bstep (se 1 (by rfl) ⟨1689005, by rfl⟩ : syracuseStep 2252007 = 3378011) B3378011
theorem B2533513 : Blo 2251435 2533513 := bbase (se 2 (by rfl) ⟨950067, by rfl⟩ : syracuseStep 2533513 = 1900135) (by norm_num)
theorem B3378017 : Blo 2251435 3378017 := bstep (se 2 (by rfl) ⟨1266756, by rfl⟩ : syracuseStep 3378017 = 2533513) B2533513
theorem B2252011 : Blo 2251435 2252011 := bstep (se 1 (by rfl) ⟨1689008, by rfl⟩ : syracuseStep 2252011 = 3378017) B3378017
theorem B5349277 : Blo 2251435 5349277 := bbase (se 3 (by rfl) ⟨1002989, by rfl⟩ : syracuseStep 5349277 = 2005979) (by norm_num)
theorem B7132369 : Blo 2251435 7132369 := bstep (se 2 (by rfl) ⟨2674638, by rfl⟩ : syracuseStep 7132369 = 5349277) B5349277
theorem B9509825 : Blo 2251435 9509825 := bstep (se 2 (by rfl) ⟨3566184, by rfl⟩ : syracuseStep 9509825 = 7132369) B7132369
theorem B6339883 : Blo 2251435 6339883 := bstep (se 1 (by rfl) ⟨4754912, by rfl⟩ : syracuseStep 6339883 = 9509825) B9509825
theorem B8453177 : Blo 2251435 8453177 := bstep (se 2 (by rfl) ⟨3169941, by rfl⟩ : syracuseStep 8453177 = 6339883) B6339883
theorem B5635451 : Blo 2251435 5635451 := bstep (se 1 (by rfl) ⟨4226588, by rfl⟩ : syracuseStep 5635451 = 8453177) B8453177
theorem B15027869 : Blo 2251435 15027869 := bstep (se 3 (by rfl) ⟨2817725, by rfl⟩ : syracuseStep 15027869 = 5635451) B5635451
theorem B10018579 : Blo 2251435 10018579 := bstep (se 1 (by rfl) ⟨7513934, by rfl⟩ : syracuseStep 10018579 = 15027869) B15027869
theorem B13358105 : Blo 2251435 13358105 := bstep (se 2 (by rfl) ⟨5009289, by rfl⟩ : syracuseStep 13358105 = 10018579) B10018579
theorem B8905403 : Blo 2251435 8905403 := bstep (se 1 (by rfl) ⟨6679052, by rfl⟩ : syracuseStep 8905403 = 13358105) B13358105
theorem B5936935 : Blo 2251435 5936935 := bstep (se 1 (by rfl) ⟨4452701, by rfl⟩ : syracuseStep 5936935 = 8905403) B8905403
theorem B7915913 : Blo 2251435 7915913 := bstep (se 2 (by rfl) ⟨2968467, by rfl⟩ : syracuseStep 7915913 = 5936935) B5936935
theorem B5277275 : Blo 2251435 5277275 := bstep (se 1 (by rfl) ⟨3957956, by rfl⟩ : syracuseStep 5277275 = 7915913) B7915913
theorem B3518183 : Blo 2251435 3518183 := bstep (se 1 (by rfl) ⟨2638637, by rfl⟩ : syracuseStep 3518183 = 5277275) B5277275
theorem B2345455 : Blo 2251435 2345455 := bstep (se 1 (by rfl) ⟨1759091, by rfl⟩ : syracuseStep 2345455 = 3518183) B3518183
theorem B12509093 : Blo 2251435 12509093 := bstep (se 4 (by rfl) ⟨1172727, by rfl⟩ : syracuseStep 12509093 = 2345455) B2345455
theorem B33357581 : Blo 2251435 33357581 := bstep (se 3 (by rfl) ⟨6254546, by rfl⟩ : syracuseStep 33357581 = 12509093) B12509093
theorem B22238387 : Blo 2251435 22238387 := bstep (se 1 (by rfl) ⟨16678790, by rfl⟩ : syracuseStep 22238387 = 33357581) B33357581
theorem B14825591 : Blo 2251435 14825591 := bstep (se 1 (by rfl) ⟨11119193, by rfl⟩ : syracuseStep 14825591 = 22238387) B22238387
theorem B9883727 : Blo 2251435 9883727 := bstep (se 1 (by rfl) ⟨7412795, by rfl⟩ : syracuseStep 9883727 = 14825591) B14825591
theorem B6589151 : Blo 2251435 6589151 := bstep (se 1 (by rfl) ⟨4941863, by rfl⟩ : syracuseStep 6589151 = 9883727) B9883727
theorem B4392767 : Blo 2251435 4392767 := bstep (se 1 (by rfl) ⟨3294575, by rfl⟩ : syracuseStep 4392767 = 6589151) B6589151
theorem B11714045 : Blo 2251435 11714045 := bstep (se 3 (by rfl) ⟨2196383, by rfl⟩ : syracuseStep 11714045 = 4392767) B4392767
theorem B31237453 : Blo 2251435 31237453 := bstep (se 3 (by rfl) ⟨5857022, by rfl⟩ : syracuseStep 31237453 = 11714045) B11714045
theorem B166599749 : Blo 2251435 166599749 := bstep (se 4 (by rfl) ⟨15618726, by rfl⟩ : syracuseStep 166599749 = 31237453) B31237453
theorem B111066499 : Blo 2251435 111066499 := bstep (se 1 (by rfl) ⟨83299874, by rfl⟩ : syracuseStep 111066499 = 166599749) B166599749
theorem B148088665 : Blo 2251435 148088665 := bstep (se 2 (by rfl) ⟨55533249, by rfl⟩ : syracuseStep 148088665 = 111066499) B111066499
theorem B197451553 : Blo 2251435 197451553 := bstep (se 2 (by rfl) ⟨74044332, by rfl⟩ : syracuseStep 197451553 = 148088665) B148088665
theorem B263268737 : Blo 2251435 263268737 := bstep (se 2 (by rfl) ⟨98725776, by rfl⟩ : syracuseStep 263268737 = 197451553) B197451553
theorem B175512491 : Blo 2251435 175512491 := bstep (se 1 (by rfl) ⟨131634368, by rfl⟩ : syracuseStep 175512491 = 263268737) B263268737
theorem B117008327 : Blo 2251435 117008327 := bstep (se 1 (by rfl) ⟨87756245, by rfl⟩ : syracuseStep 117008327 = 175512491) B175512491
theorem B78005551 : Blo 2251435 78005551 := bstep (se 1 (by rfl) ⟨58504163, by rfl⟩ : syracuseStep 78005551 = 117008327) B117008327
theorem B104007401 : Blo 2251435 104007401 := bstep (se 2 (by rfl) ⟨39002775, by rfl⟩ : syracuseStep 104007401 = 78005551) B78005551
theorem B69338267 : Blo 2251435 69338267 := bstep (se 1 (by rfl) ⟨52003700, by rfl⟩ : syracuseStep 69338267 = 104007401) B104007401
theorem B46225511 : Blo 2251435 46225511 := bstep (se 1 (by rfl) ⟨34669133, by rfl⟩ : syracuseStep 46225511 = 69338267) B69338267
theorem B30817007 : Blo 2251435 30817007 := bstep (se 1 (by rfl) ⟨23112755, by rfl⟩ : syracuseStep 30817007 = 46225511) B46225511
theorem B20544671 : Blo 2251435 20544671 := bstep (se 1 (by rfl) ⟨15408503, by rfl⟩ : syracuseStep 20544671 = 30817007) B30817007
theorem B13696447 : Blo 2251435 13696447 := bstep (se 1 (by rfl) ⟨10272335, by rfl⟩ : syracuseStep 13696447 = 20544671) B20544671
theorem B18261929 : Blo 2251435 18261929 := bstep (se 2 (by rfl) ⟨6848223, by rfl⟩ : syracuseStep 18261929 = 13696447) B13696447
theorem B12174619 : Blo 2251435 12174619 := bstep (se 1 (by rfl) ⟨9130964, by rfl⟩ : syracuseStep 12174619 = 18261929) B18261929
theorem B16232825 : Blo 2251435 16232825 := bstep (se 2 (by rfl) ⟨6087309, by rfl⟩ : syracuseStep 16232825 = 12174619) B12174619
theorem B43287533 : Blo 2251435 43287533 := bstep (se 3 (by rfl) ⟨8116412, by rfl⟩ : syracuseStep 43287533 = 16232825) B16232825
theorem B28858355 : Blo 2251435 28858355 := bstep (se 1 (by rfl) ⟨21643766, by rfl⟩ : syracuseStep 28858355 = 43287533) B43287533
theorem B19238903 : Blo 2251435 19238903 := bstep (se 1 (by rfl) ⟨14429177, by rfl⟩ : syracuseStep 19238903 = 28858355) B28858355
theorem B12825935 : Blo 2251435 12825935 := bstep (se 1 (by rfl) ⟨9619451, by rfl⟩ : syracuseStep 12825935 = 19238903) B19238903
theorem B8550623 : Blo 2251435 8550623 := bstep (se 1 (by rfl) ⟨6412967, by rfl⟩ : syracuseStep 8550623 = 12825935) B12825935
theorem B5700415 : Blo 2251435 5700415 := bstep (se 1 (by rfl) ⟨4275311, by rfl⟩ : syracuseStep 5700415 = 8550623) B8550623
theorem B7600553 : Blo 2251435 7600553 := bstep (se 2 (by rfl) ⟨2850207, by rfl⟩ : syracuseStep 7600553 = 5700415) B5700415
theorem B5067035 : Blo 2251435 5067035 := bstep (se 1 (by rfl) ⟨3800276, by rfl⟩ : syracuseStep 5067035 = 7600553) B7600553
theorem B3378023 : Blo 2251435 3378023 := bstep (se 1 (by rfl) ⟨2533517, by rfl⟩ : syracuseStep 3378023 = 5067035) B5067035
theorem B2252015 : Blo 2251435 2252015 := bstep (se 1 (by rfl) ⟨1689011, by rfl⟩ : syracuseStep 2252015 = 3378023) B3378023
theorem B3378029 : Blo 2251435 3378029 := bbase (se 3 (by rfl) ⟨633380, by rfl⟩ : syracuseStep 3378029 = 1266761) (by norm_num)
theorem B2252019 : Blo 2251435 2252019 := bstep (se 1 (by rfl) ⟨1689014, by rfl⟩ : syracuseStep 2252019 = 3378029) B3378029
theorem B5067053 : Blo 2251435 5067053 := bbase (se 3 (by rfl) ⟨950072, by rfl⟩ : syracuseStep 5067053 = 1900145) (by norm_num)
theorem B3378035 : Blo 2251435 3378035 := bstep (se 1 (by rfl) ⟨2533526, by rfl⟩ : syracuseStep 3378035 = 5067053) B5067053
theorem B2252023 : Blo 2251435 2252023 := bstep (se 1 (by rfl) ⟨1689017, by rfl⟩ : syracuseStep 2252023 = 3378035) B3378035
theorem B7214629 : Blo 2251435 7214629 := bbase (se 4 (by rfl) ⟨676371, by rfl⟩ : syracuseStep 7214629 = 1352743) (by norm_num)
theorem B9619505 : Blo 2251435 9619505 := bstep (se 2 (by rfl) ⟨3607314, by rfl⟩ : syracuseStep 9619505 = 7214629) B7214629
theorem B6413003 : Blo 2251435 6413003 := bstep (se 1 (by rfl) ⟨4809752, by rfl⟩ : syracuseStep 6413003 = 9619505) B9619505
theorem B4275335 : Blo 2251435 4275335 := bstep (se 1 (by rfl) ⟨3206501, by rfl⟩ : syracuseStep 4275335 = 6413003) B6413003
theorem B2850223 : Blo 2251435 2850223 := bstep (se 1 (by rfl) ⟨2137667, by rfl⟩ : syracuseStep 2850223 = 4275335) B4275335
theorem B3800297 : Blo 2251435 3800297 := bstep (se 2 (by rfl) ⟨1425111, by rfl⟩ : syracuseStep 3800297 = 2850223) B2850223
theorem B2533531 : Blo 2251435 2533531 := bstep (se 1 (by rfl) ⟨1900148, by rfl⟩ : syracuseStep 2533531 = 3800297) B3800297
theorem B3378041 : Blo 2251435 3378041 := bstep (se 2 (by rfl) ⟨1266765, by rfl⟩ : syracuseStep 3378041 = 2533531) B2533531
theorem B2252027 : Blo 2251435 2252027 := bstep (se 1 (by rfl) ⟨1689020, by rfl⟩ : syracuseStep 2252027 = 3378041) B3378041
theorem B33497429 : Blo 2251435 33497429 := bbase (se 10 (by rfl) ⟨49068, by rfl⟩ : syracuseStep 33497429 = 98137) (by norm_num)
theorem B357305909 : Blo 2251435 357305909 := bstep (se 5 (by rfl) ⟨16748714, by rfl⟩ : syracuseStep 357305909 = 33497429) B33497429
theorem B3811263029 : Blo 2251435 3811263029 := bstep (se 5 (by rfl) ⟨178652954, by rfl⟩ : syracuseStep 3811263029 = 357305909) B357305909
theorem B2540842019 : Blo 2251435 2540842019 := bstep (se 1 (by rfl) ⟨1905631514, by rfl⟩ : syracuseStep 2540842019 = 3811263029) B3811263029
theorem B1693894679 : Blo 2251435 1693894679 := bstep (se 1 (by rfl) ⟨1270421009, by rfl⟩ : syracuseStep 1693894679 = 2540842019) B2540842019
theorem B1129263119 : Blo 2251435 1129263119 := bstep (se 1 (by rfl) ⟨846947339, by rfl⟩ : syracuseStep 1129263119 = 1693894679) B1693894679
theorem B752842079 : Blo 2251435 752842079 := bstep (se 1 (by rfl) ⟨564631559, by rfl⟩ : syracuseStep 752842079 = 1129263119) B1129263119
theorem B501894719 : Blo 2251435 501894719 := bstep (se 1 (by rfl) ⟨376421039, by rfl⟩ : syracuseStep 501894719 = 752842079) B752842079
theorem B334596479 : Blo 2251435 334596479 := bstep (se 1 (by rfl) ⟨250947359, by rfl⟩ : syracuseStep 334596479 = 501894719) B501894719
theorem B892257277 : Blo 2251435 892257277 := bstep (se 3 (by rfl) ⟨167298239, by rfl⟩ : syracuseStep 892257277 = 334596479) B334596479
theorem B1189676369 : Blo 2251435 1189676369 := bstep (se 2 (by rfl) ⟨446128638, by rfl⟩ : syracuseStep 1189676369 = 892257277) B892257277
theorem B3172470317 : Blo 2251435 3172470317 := bstep (se 3 (by rfl) ⟨594838184, by rfl⟩ : syracuseStep 3172470317 = 1189676369) B1189676369
theorem B2114980211 : Blo 2251435 2114980211 := bstep (se 1 (by rfl) ⟨1586235158, by rfl⟩ : syracuseStep 2114980211 = 3172470317) B3172470317
theorem B1409986807 : Blo 2251435 1409986807 := bstep (se 1 (by rfl) ⟨1057490105, by rfl⟩ : syracuseStep 1409986807 = 2114980211) B2114980211
theorem B30079718549 : Blo 2251435 30079718549 := bstep (se 6 (by rfl) ⟨704993403, by rfl⟩ : syracuseStep 30079718549 = 1409986807) B1409986807
theorem B20053145699 : Blo 2251435 20053145699 := bstep (se 1 (by rfl) ⟨15039859274, by rfl⟩ : syracuseStep 20053145699 = 30079718549) B30079718549
theorem B13368763799 : Blo 2251435 13368763799 := bstep (se 1 (by rfl) ⟨10026572849, by rfl⟩ : syracuseStep 13368763799 = 20053145699) B20053145699
theorem B8912509199 : Blo 2251435 8912509199 := bstep (se 1 (by rfl) ⟨6684381899, by rfl⟩ : syracuseStep 8912509199 = 13368763799) B13368763799
theorem B5941672799 : Blo 2251435 5941672799 := bstep (se 1 (by rfl) ⟨4456254599, by rfl⟩ : syracuseStep 5941672799 = 8912509199) B8912509199
theorem B15844460797 : Blo 2251435 15844460797 := bstep (se 3 (by rfl) ⟨2970836399, by rfl⟩ : syracuseStep 15844460797 = 5941672799) B5941672799
theorem B21125947729 : Blo 2251435 21125947729 := bstep (se 2 (by rfl) ⟨7922230398, by rfl⟩ : syracuseStep 21125947729 = 15844460797) B15844460797
theorem B28167930305 : Blo 2251435 28167930305 := bstep (se 2 (by rfl) ⟨10562973864, by rfl⟩ : syracuseStep 28167930305 = 21125947729) B21125947729
theorem B18778620203 : Blo 2251435 18778620203 := bstep (se 1 (by rfl) ⟨14083965152, by rfl⟩ : syracuseStep 18778620203 = 28167930305) B28167930305
theorem B12519080135 : Blo 2251435 12519080135 := bstep (se 1 (by rfl) ⟨9389310101, by rfl⟩ : syracuseStep 12519080135 = 18778620203) B18778620203
theorem B8346053423 : Blo 2251435 8346053423 := bstep (se 1 (by rfl) ⟨6259540067, by rfl⟩ : syracuseStep 8346053423 = 12519080135) B12519080135
theorem B22256142461 : Blo 2251435 22256142461 := bstep (se 3 (by rfl) ⟨4173026711, by rfl⟩ : syracuseStep 22256142461 = 8346053423) B8346053423
theorem B14837428307 : Blo 2251435 14837428307 := bstep (se 1 (by rfl) ⟨11128071230, by rfl⟩ : syracuseStep 14837428307 = 22256142461) B22256142461
theorem B9891618871 : Blo 2251435 9891618871 := bstep (se 1 (by rfl) ⟨7418714153, by rfl⟩ : syracuseStep 9891618871 = 14837428307) B14837428307
theorem B13188825161 : Blo 2251435 13188825161 := bstep (se 2 (by rfl) ⟨4945809435, by rfl⟩ : syracuseStep 13188825161 = 9891618871) B9891618871
theorem B8792550107 : Blo 2251435 8792550107 := bstep (se 1 (by rfl) ⟨6594412580, by rfl⟩ : syracuseStep 8792550107 = 13188825161) B13188825161
theorem B5861700071 : Blo 2251435 5861700071 := bstep (se 1 (by rfl) ⟨4396275053, by rfl⟩ : syracuseStep 5861700071 = 8792550107) B8792550107
theorem B3907800047 : Blo 2251435 3907800047 := bstep (se 1 (by rfl) ⟨2930850035, by rfl⟩ : syracuseStep 3907800047 = 5861700071) B5861700071
theorem B2605200031 : Blo 2251435 2605200031 := bstep (se 1 (by rfl) ⟨1953900023, by rfl⟩ : syracuseStep 2605200031 = 3907800047) B3907800047
theorem B3473600041 : Blo 2251435 3473600041 := bstep (se 2 (by rfl) ⟨1302600015, by rfl⟩ : syracuseStep 3473600041 = 2605200031) B2605200031
theorem B4631466721 : Blo 2251435 4631466721 := bstep (se 2 (by rfl) ⟨1736800020, by rfl⟩ : syracuseStep 4631466721 = 3473600041) B3473600041
theorem B6175288961 : Blo 2251435 6175288961 := bstep (se 2 (by rfl) ⟨2315733360, by rfl⟩ : syracuseStep 6175288961 = 4631466721) B4631466721
theorem B4116859307 : Blo 2251435 4116859307 := bstep (se 1 (by rfl) ⟨3087644480, by rfl⟩ : syracuseStep 4116859307 = 6175288961) B6175288961
theorem B2744572871 : Blo 2251435 2744572871 := bstep (se 1 (by rfl) ⟨2058429653, by rfl⟩ : syracuseStep 2744572871 = 4116859307) B4116859307
theorem B1829715247 : Blo 2251435 1829715247 := bstep (se 1 (by rfl) ⟨1372286435, by rfl⟩ : syracuseStep 1829715247 = 2744572871) B2744572871
theorem B2439620329 : Blo 2251435 2439620329 := bstep (se 2 (by rfl) ⟨914857623, by rfl⟩ : syracuseStep 2439620329 = 1829715247) B1829715247
theorem B3252827105 : Blo 2251435 3252827105 := bstep (se 2 (by rfl) ⟨1219810164, by rfl⟩ : syracuseStep 3252827105 = 2439620329) B2439620329
theorem B2168551403 : Blo 2251435 2168551403 := bstep (se 1 (by rfl) ⟨1626413552, by rfl⟩ : syracuseStep 2168551403 = 3252827105) B3252827105
theorem B1445700935 : Blo 2251435 1445700935 := bstep (se 1 (by rfl) ⟨1084275701, by rfl⟩ : syracuseStep 1445700935 = 2168551403) B2168551403
theorem B963800623 : Blo 2251435 963800623 := bstep (se 1 (by rfl) ⟨722850467, by rfl⟩ : syracuseStep 963800623 = 1445700935) B1445700935
theorem B5140269989 : Blo 2251435 5140269989 := bstep (se 4 (by rfl) ⟨481900311, by rfl⟩ : syracuseStep 5140269989 = 963800623) B963800623
theorem B3426846659 : Blo 2251435 3426846659 := bstep (se 1 (by rfl) ⟨2570134994, by rfl⟩ : syracuseStep 3426846659 = 5140269989) B5140269989
theorem B2284564439 : Blo 2251435 2284564439 := bstep (se 1 (by rfl) ⟨1713423329, by rfl⟩ : syracuseStep 2284564439 = 3426846659) B3426846659
theorem B1523042959 : Blo 2251435 1523042959 := bstep (se 1 (by rfl) ⟨1142282219, by rfl⟩ : syracuseStep 1523042959 = 2284564439) B2284564439
theorem B2030723945 : Blo 2251435 2030723945 := bstep (se 2 (by rfl) ⟨761521479, by rfl⟩ : syracuseStep 2030723945 = 1523042959) B1523042959
theorem B1353815963 : Blo 2251435 1353815963 := bstep (se 1 (by rfl) ⟨1015361972, by rfl⟩ : syracuseStep 1353815963 = 2030723945) B2030723945
theorem B902543975 : Blo 2251435 902543975 := bstep (se 1 (by rfl) ⟨676907981, by rfl⟩ : syracuseStep 902543975 = 1353815963) B1353815963
theorem B601695983 : Blo 2251435 601695983 := bstep (se 1 (by rfl) ⟨451271987, by rfl⟩ : syracuseStep 601695983 = 902543975) B902543975
theorem B1604522621 : Blo 2251435 1604522621 := bstep (se 3 (by rfl) ⟨300847991, by rfl⟩ : syracuseStep 1604522621 = 601695983) B601695983
theorem B4278726989 : Blo 2251435 4278726989 := bstep (se 3 (by rfl) ⟨802261310, by rfl⟩ : syracuseStep 4278726989 = 1604522621) B1604522621
theorem B2852484659 : Blo 2251435 2852484659 := bstep (se 1 (by rfl) ⟨2139363494, by rfl⟩ : syracuseStep 2852484659 = 4278726989) B4278726989
theorem B1901656439 : Blo 2251435 1901656439 := bstep (se 1 (by rfl) ⟨1426242329, by rfl⟩ : syracuseStep 1901656439 = 2852484659) B2852484659
theorem B1267770959 : Blo 2251435 1267770959 := bstep (se 1 (by rfl) ⟨950828219, by rfl⟩ : syracuseStep 1267770959 = 1901656439) B1901656439
theorem B845180639 : Blo 2251435 845180639 := bstep (se 1 (by rfl) ⟨633885479, by rfl⟩ : syracuseStep 845180639 = 1267770959) B1267770959
theorem B563453759 : Blo 2251435 563453759 := bstep (se 1 (by rfl) ⟨422590319, by rfl⟩ : syracuseStep 563453759 = 845180639) B845180639
theorem B1502543357 : Blo 2251435 1502543357 := bstep (se 3 (by rfl) ⟨281726879, by rfl⟩ : syracuseStep 1502543357 = 563453759) B563453759
theorem B1001695571 : Blo 2251435 1001695571 := bstep (se 1 (by rfl) ⟨751271678, by rfl⟩ : syracuseStep 1001695571 = 1502543357) B1502543357
theorem B667797047 : Blo 2251435 667797047 := bstep (se 1 (by rfl) ⟨500847785, by rfl⟩ : syracuseStep 667797047 = 1001695571) B1001695571
theorem B445198031 : Blo 2251435 445198031 := bstep (se 1 (by rfl) ⟨333898523, by rfl⟩ : syracuseStep 445198031 = 667797047) B667797047
theorem B296798687 : Blo 2251435 296798687 := bstep (se 1 (by rfl) ⟨222599015, by rfl⟩ : syracuseStep 296798687 = 445198031) B445198031
theorem B197865791 : Blo 2251435 197865791 := bstep (se 1 (by rfl) ⟨148399343, by rfl⟩ : syracuseStep 197865791 = 296798687) B296798687
theorem B131910527 : Blo 2251435 131910527 := bstep (se 1 (by rfl) ⟨98932895, by rfl⟩ : syracuseStep 131910527 = 197865791) B197865791
theorem B87940351 : Blo 2251435 87940351 := bstep (se 1 (by rfl) ⟨65955263, by rfl⟩ : syracuseStep 87940351 = 131910527) B131910527
theorem B117253801 : Blo 2251435 117253801 := bstep (se 2 (by rfl) ⟨43970175, by rfl⟩ : syracuseStep 117253801 = 87940351) B87940351
theorem B625353605 : Blo 2251435 625353605 := bstep (se 4 (by rfl) ⟨58626900, by rfl⟩ : syracuseStep 625353605 = 117253801) B117253801
theorem B416902403 : Blo 2251435 416902403 := bstep (se 1 (by rfl) ⟨312676802, by rfl⟩ : syracuseStep 416902403 = 625353605) B625353605
theorem B1111739741 : Blo 2251435 1111739741 := bstep (se 3 (by rfl) ⟨208451201, by rfl⟩ : syracuseStep 1111739741 = 416902403) B416902403
theorem B741159827 : Blo 2251435 741159827 := bstep (se 1 (by rfl) ⟨555869870, by rfl⟩ : syracuseStep 741159827 = 1111739741) B1111739741
theorem B494106551 : Blo 2251435 494106551 := bstep (se 1 (by rfl) ⟨370579913, by rfl⟩ : syracuseStep 494106551 = 741159827) B741159827
theorem B329404367 : Blo 2251435 329404367 := bstep (se 1 (by rfl) ⟨247053275, by rfl⟩ : syracuseStep 329404367 = 494106551) B494106551
theorem B219602911 : Blo 2251435 219602911 := bstep (se 1 (by rfl) ⟨164702183, by rfl⟩ : syracuseStep 219602911 = 329404367) B329404367
theorem B292803881 : Blo 2251435 292803881 := bstep (se 2 (by rfl) ⟨109801455, by rfl⟩ : syracuseStep 292803881 = 219602911) B219602911
theorem B780810349 : Blo 2251435 780810349 := bstep (se 3 (by rfl) ⟨146401940, by rfl⟩ : syracuseStep 780810349 = 292803881) B292803881
theorem B1041080465 : Blo 2251435 1041080465 := bstep (se 2 (by rfl) ⟨390405174, by rfl⟩ : syracuseStep 1041080465 = 780810349) B780810349
theorem B694053643 : Blo 2251435 694053643 := bstep (se 1 (by rfl) ⟨520540232, by rfl⟩ : syracuseStep 694053643 = 1041080465) B1041080465
theorem B925404857 : Blo 2251435 925404857 := bstep (se 2 (by rfl) ⟨347026821, by rfl⟩ : syracuseStep 925404857 = 694053643) B694053643
theorem B616936571 : Blo 2251435 616936571 := bstep (se 1 (by rfl) ⟨462702428, by rfl⟩ : syracuseStep 616936571 = 925404857) B925404857
theorem B411291047 : Blo 2251435 411291047 := bstep (se 1 (by rfl) ⟨308468285, by rfl⟩ : syracuseStep 411291047 = 616936571) B616936571
theorem B1096776125 : Blo 2251435 1096776125 := bstep (se 3 (by rfl) ⟨205645523, by rfl⟩ : syracuseStep 1096776125 = 411291047) B411291047
theorem B731184083 : Blo 2251435 731184083 := bstep (se 1 (by rfl) ⟨548388062, by rfl⟩ : syracuseStep 731184083 = 1096776125) B1096776125
theorem B487456055 : Blo 2251435 487456055 := bstep (se 1 (by rfl) ⟨365592041, by rfl⟩ : syracuseStep 487456055 = 731184083) B731184083
theorem B324970703 : Blo 2251435 324970703 := bstep (se 1 (by rfl) ⟨243728027, by rfl⟩ : syracuseStep 324970703 = 487456055) B487456055
theorem B216647135 : Blo 2251435 216647135 := bstep (se 1 (by rfl) ⟨162485351, by rfl⟩ : syracuseStep 216647135 = 324970703) B324970703
theorem B144431423 : Blo 2251435 144431423 := bstep (se 1 (by rfl) ⟨108323567, by rfl⟩ : syracuseStep 144431423 = 216647135) B216647135
theorem B96287615 : Blo 2251435 96287615 := bstep (se 1 (by rfl) ⟨72215711, by rfl⟩ : syracuseStep 96287615 = 144431423) B144431423
theorem B64191743 : Blo 2251435 64191743 := bstep (se 1 (by rfl) ⟨48143807, by rfl⟩ : syracuseStep 64191743 = 96287615) B96287615
theorem B42794495 : Blo 2251435 42794495 := bstep (se 1 (by rfl) ⟨32095871, by rfl⟩ : syracuseStep 42794495 = 64191743) B64191743
theorem B28529663 : Blo 2251435 28529663 := bstep (se 1 (by rfl) ⟨21397247, by rfl⟩ : syracuseStep 28529663 = 42794495) B42794495
theorem B76079101 : Blo 2251435 76079101 := bstep (se 3 (by rfl) ⟨14264831, by rfl⟩ : syracuseStep 76079101 = 28529663) B28529663
theorem B101438801 : Blo 2251435 101438801 := bstep (se 2 (by rfl) ⟨38039550, by rfl⟩ : syracuseStep 101438801 = 76079101) B76079101
theorem B67625867 : Blo 2251435 67625867 := bstep (se 1 (by rfl) ⟨50719400, by rfl⟩ : syracuseStep 67625867 = 101438801) B101438801
theorem B180335645 : Blo 2251435 180335645 := bstep (se 3 (by rfl) ⟨33812933, by rfl⟩ : syracuseStep 180335645 = 67625867) B67625867
theorem B120223763 : Blo 2251435 120223763 := bstep (se 1 (by rfl) ⟨90167822, by rfl⟩ : syracuseStep 120223763 = 180335645) B180335645
theorem B80149175 : Blo 2251435 80149175 := bstep (se 1 (by rfl) ⟨60111881, by rfl⟩ : syracuseStep 80149175 = 120223763) B120223763
theorem B53432783 : Blo 2251435 53432783 := bstep (se 1 (by rfl) ⟨40074587, by rfl⟩ : syracuseStep 53432783 = 80149175) B80149175
theorem B35621855 : Blo 2251435 35621855 := bstep (se 1 (by rfl) ⟨26716391, by rfl⟩ : syracuseStep 35621855 = 53432783) B53432783
theorem B23747903 : Blo 2251435 23747903 := bstep (se 1 (by rfl) ⟨17810927, by rfl⟩ : syracuseStep 23747903 = 35621855) B35621855
theorem B15831935 : Blo 2251435 15831935 := bstep (se 1 (by rfl) ⟨11873951, by rfl⟩ : syracuseStep 15831935 = 23747903) B23747903
theorem B10554623 : Blo 2251435 10554623 := bstep (se 1 (by rfl) ⟨7915967, by rfl⟩ : syracuseStep 10554623 = 15831935) B15831935
theorem B7036415 : Blo 2251435 7036415 := bstep (se 1 (by rfl) ⟨5277311, by rfl⟩ : syracuseStep 7036415 = 10554623) B10554623
theorem B4690943 : Blo 2251435 4690943 := bstep (se 1 (by rfl) ⟨3518207, by rfl⟩ : syracuseStep 4690943 = 7036415) B7036415
theorem B3127295 : Blo 2251435 3127295 := bstep (se 1 (by rfl) ⟨2345471, by rfl⟩ : syracuseStep 3127295 = 4690943) B4690943
theorem B8339453 : Blo 2251435 8339453 := bstep (se 3 (by rfl) ⟨1563647, by rfl⟩ : syracuseStep 8339453 = 3127295) B3127295
theorem B5559635 : Blo 2251435 5559635 := bstep (se 1 (by rfl) ⟨4169726, by rfl⟩ : syracuseStep 5559635 = 8339453) B8339453
theorem B14825693 : Blo 2251435 14825693 := bstep (se 3 (by rfl) ⟨2779817, by rfl⟩ : syracuseStep 14825693 = 5559635) B5559635
theorem B39535181 : Blo 2251435 39535181 := bstep (se 3 (by rfl) ⟨7412846, by rfl⟩ : syracuseStep 39535181 = 14825693) B14825693
theorem B26356787 : Blo 2251435 26356787 := bstep (se 1 (by rfl) ⟨19767590, by rfl⟩ : syracuseStep 26356787 = 39535181) B39535181
theorem B17571191 : Blo 2251435 17571191 := bstep (se 1 (by rfl) ⟨13178393, by rfl⟩ : syracuseStep 17571191 = 26356787) B26356787
theorem B187426037 : Blo 2251435 187426037 := bstep (se 5 (by rfl) ⟨8785595, by rfl⟩ : syracuseStep 187426037 = 17571191) B17571191
theorem B124950691 : Blo 2251435 124950691 := bstep (se 1 (by rfl) ⟨93713018, by rfl⟩ : syracuseStep 124950691 = 187426037) B187426037
theorem B166600921 : Blo 2251435 166600921 := bstep (se 2 (by rfl) ⟨62475345, by rfl⟩ : syracuseStep 166600921 = 124950691) B124950691
theorem B222134561 : Blo 2251435 222134561 := bstep (se 2 (by rfl) ⟨83300460, by rfl⟩ : syracuseStep 222134561 = 166600921) B166600921
theorem B148089707 : Blo 2251435 148089707 := bstep (se 1 (by rfl) ⟨111067280, by rfl⟩ : syracuseStep 148089707 = 222134561) B222134561
theorem B98726471 : Blo 2251435 98726471 := bstep (se 1 (by rfl) ⟨74044853, by rfl⟩ : syracuseStep 98726471 = 148089707) B148089707
theorem B65817647 : Blo 2251435 65817647 := bstep (se 1 (by rfl) ⟨49363235, by rfl⟩ : syracuseStep 65817647 = 98726471) B98726471
theorem B43878431 : Blo 2251435 43878431 := bstep (se 1 (by rfl) ⟨32908823, by rfl⟩ : syracuseStep 43878431 = 65817647) B65817647
theorem B29252287 : Blo 2251435 29252287 := bstep (se 1 (by rfl) ⟨21939215, by rfl⟩ : syracuseStep 29252287 = 43878431) B43878431
theorem B39003049 : Blo 2251435 39003049 := bstep (se 2 (by rfl) ⟨14626143, by rfl⟩ : syracuseStep 39003049 = 29252287) B29252287
theorem B52004065 : Blo 2251435 52004065 := bstep (se 2 (by rfl) ⟨19501524, by rfl⟩ : syracuseStep 52004065 = 39003049) B39003049
theorem B69338753 : Blo 2251435 69338753 := bstep (se 2 (by rfl) ⟨26002032, by rfl⟩ : syracuseStep 69338753 = 52004065) B52004065
theorem B46225835 : Blo 2251435 46225835 := bstep (se 1 (by rfl) ⟨34669376, by rfl⟩ : syracuseStep 46225835 = 69338753) B69338753
theorem B30817223 : Blo 2251435 30817223 := bstep (se 1 (by rfl) ⟨23112917, by rfl⟩ : syracuseStep 30817223 = 46225835) B46225835
theorem B20544815 : Blo 2251435 20544815 := bstep (se 1 (by rfl) ⟨15408611, by rfl⟩ : syracuseStep 20544815 = 30817223) B30817223
theorem B13696543 : Blo 2251435 13696543 := bstep (se 1 (by rfl) ⟨10272407, by rfl⟩ : syracuseStep 13696543 = 20544815) B20544815
theorem B73048229 : Blo 2251435 73048229 := bstep (se 4 (by rfl) ⟨6848271, by rfl⟩ : syracuseStep 73048229 = 13696543) B13696543
theorem B48698819 : Blo 2251435 48698819 := bstep (se 1 (by rfl) ⟨36524114, by rfl⟩ : syracuseStep 48698819 = 73048229) B73048229
theorem B32465879 : Blo 2251435 32465879 := bstep (se 1 (by rfl) ⟨24349409, by rfl⟩ : syracuseStep 32465879 = 48698819) B48698819
theorem B21643919 : Blo 2251435 21643919 := bstep (se 1 (by rfl) ⟨16232939, by rfl⟩ : syracuseStep 21643919 = 32465879) B32465879
theorem B14429279 : Blo 2251435 14429279 := bstep (se 1 (by rfl) ⟨10821959, by rfl⟩ : syracuseStep 14429279 = 21643919) B21643919
theorem B38478077 : Blo 2251435 38478077 := bstep (se 3 (by rfl) ⟨7214639, by rfl⟩ : syracuseStep 38478077 = 14429279) B14429279
theorem B25652051 : Blo 2251435 25652051 := bstep (se 1 (by rfl) ⟨19239038, by rfl⟩ : syracuseStep 25652051 = 38478077) B38478077
theorem B17101367 : Blo 2251435 17101367 := bstep (se 1 (by rfl) ⟨12826025, by rfl⟩ : syracuseStep 17101367 = 25652051) B25652051
theorem B11400911 : Blo 2251435 11400911 := bstep (se 1 (by rfl) ⟨8550683, by rfl⟩ : syracuseStep 11400911 = 17101367) B17101367
theorem B7600607 : Blo 2251435 7600607 := bstep (se 1 (by rfl) ⟨5700455, by rfl⟩ : syracuseStep 7600607 = 11400911) B11400911
theorem B5067071 : Blo 2251435 5067071 := bstep (se 1 (by rfl) ⟨3800303, by rfl⟩ : syracuseStep 5067071 = 7600607) B7600607
theorem B3378047 : Blo 2251435 3378047 := bstep (se 1 (by rfl) ⟨2533535, by rfl⟩ : syracuseStep 3378047 = 5067071) B5067071
theorem B2252031 : Blo 2251435 2252031 := bstep (se 1 (by rfl) ⟨1689023, by rfl⟩ : syracuseStep 2252031 = 3378047) B3378047
theorem B3378053 : Blo 2251435 3378053 := bbase (se 4 (by rfl) ⟨316692, by rfl⟩ : syracuseStep 3378053 = 633385) (by norm_num)
theorem B2252035 : Blo 2251435 2252035 := bstep (se 1 (by rfl) ⟨1689026, by rfl⟩ : syracuseStep 2252035 = 3378053) B3378053
theorem B3800317 : Blo 2251435 3800317 := bbase (se 3 (by rfl) ⟨712559, by rfl⟩ : syracuseStep 3800317 = 1425119) (by norm_num)
theorem B5067089 : Blo 2251435 5067089 := bstep (se 2 (by rfl) ⟨1900158, by rfl⟩ : syracuseStep 5067089 = 3800317) B3800317
theorem B3378059 : Blo 2251435 3378059 := bstep (se 1 (by rfl) ⟨2533544, by rfl⟩ : syracuseStep 3378059 = 5067089) B5067089
theorem B2252039 : Blo 2251435 2252039 := bstep (se 1 (by rfl) ⟨1689029, by rfl⟩ : syracuseStep 2252039 = 3378059) B3378059
theorem B2533549 : Blo 2251435 2533549 := bbase (se 3 (by rfl) ⟨475040, by rfl⟩ : syracuseStep 2533549 = 950081) (by norm_num)
theorem B3378065 : Blo 2251435 3378065 := bstep (se 2 (by rfl) ⟨1266774, by rfl⟩ : syracuseStep 3378065 = 2533549) B2533549
theorem B2252043 : Blo 2251435 2252043 := bstep (se 1 (by rfl) ⟨1689032, by rfl⟩ : syracuseStep 2252043 = 3378065) B3378065
theorem B7600661 : Blo 2251435 7600661 := bbase (se 6 (by rfl) ⟨178140, by rfl⟩ : syracuseStep 7600661 = 356281) (by norm_num)
theorem B5067107 : Blo 2251435 5067107 := bstep (se 1 (by rfl) ⟨3800330, by rfl⟩ : syracuseStep 5067107 = 7600661) B7600661
theorem B3378071 : Blo 2251435 3378071 := bstep (se 1 (by rfl) ⟨2533553, by rfl⟩ : syracuseStep 3378071 = 5067107) B5067107
theorem B2252047 : Blo 2251435 2252047 := bstep (se 1 (by rfl) ⟨1689035, by rfl⟩ : syracuseStep 2252047 = 3378071) B3378071
theorem B3378077 : Blo 2251435 3378077 := bbase (se 3 (by rfl) ⟨633389, by rfl⟩ : syracuseStep 3378077 = 1266779) (by norm_num)
theorem B2252051 : Blo 2251435 2252051 := bstep (se 1 (by rfl) ⟨1689038, by rfl⟩ : syracuseStep 2252051 = 3378077) B3378077
theorem B5067125 : Blo 2251435 5067125 := bbase (se 5 (by rfl) ⟨237521, by rfl⟩ : syracuseStep 5067125 = 475043) (by norm_num)
theorem B3378083 : Blo 2251435 3378083 := bstep (se 1 (by rfl) ⟨2533562, by rfl⟩ : syracuseStep 3378083 = 5067125) B5067125
theorem B2252055 : Blo 2251435 2252055 := bstep (se 1 (by rfl) ⟨1689041, by rfl⟩ : syracuseStep 2252055 = 3378083) B3378083
theorem B14429461 : Blo 2251435 14429461 := bbase (se 6 (by rfl) ⟨338190, by rfl⟩ : syracuseStep 14429461 = 676381) (by norm_num)
theorem B19239281 : Blo 2251435 19239281 := bstep (se 2 (by rfl) ⟨7214730, by rfl⟩ : syracuseStep 19239281 = 14429461) B14429461
theorem B12826187 : Blo 2251435 12826187 := bstep (se 1 (by rfl) ⟨9619640, by rfl⟩ : syracuseStep 12826187 = 19239281) B19239281
theorem B8550791 : Blo 2251435 8550791 := bstep (se 1 (by rfl) ⟨6413093, by rfl⟩ : syracuseStep 8550791 = 12826187) B12826187
theorem B5700527 : Blo 2251435 5700527 := bstep (se 1 (by rfl) ⟨4275395, by rfl⟩ : syracuseStep 5700527 = 8550791) B8550791
theorem B3800351 : Blo 2251435 3800351 := bstep (se 1 (by rfl) ⟨2850263, by rfl⟩ : syracuseStep 3800351 = 5700527) B5700527
theorem B2533567 : Blo 2251435 2533567 := bstep (se 1 (by rfl) ⟨1900175, by rfl⟩ : syracuseStep 2533567 = 3800351) B3800351
theorem B3378089 : Blo 2251435 3378089 := bstep (se 2 (by rfl) ⟨1266783, by rfl⟩ : syracuseStep 3378089 = 2533567) B2533567
theorem B2252059 : Blo 2251435 2252059 := bstep (se 1 (by rfl) ⟨1689044, by rfl⟩ : syracuseStep 2252059 = 3378089) B3378089
theorem B8550805 : Blo 2251435 8550805 := bbase (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) (by norm_num)
theorem B11401073 : Blo 2251435 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B7600715 : Blo 2251435 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B5067143 : Blo 2251435 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B3378095 : Blo 2251435 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B2252063 : Blo 2251435 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B3378101 : Blo 2251435 3378101 := bbase (se 5 (by rfl) ⟨158348, by rfl⟩ : syracuseStep 3378101 = 316697) (by norm_num)
theorem B2252067 : Blo 2251435 2252067 := bstep (se 1 (by rfl) ⟨1689050, by rfl⟩ : syracuseStep 2252067 = 3378101) B3378101
theorem B5700557 : Blo 2251435 5700557 := bbase (se 3 (by rfl) ⟨1068854, by rfl⟩ : syracuseStep 5700557 = 2137709) (by norm_num)
theorem B3800371 : Blo 2251435 3800371 := bstep (se 1 (by rfl) ⟨2850278, by rfl⟩ : syracuseStep 3800371 = 5700557) B5700557
theorem B5067161 : Blo 2251435 5067161 := bstep (se 2 (by rfl) ⟨1900185, by rfl⟩ : syracuseStep 5067161 = 3800371) B3800371
theorem B3378107 : Blo 2251435 3378107 := bstep (se 1 (by rfl) ⟨2533580, by rfl⟩ : syracuseStep 3378107 = 5067161) B5067161
theorem B2252071 : Blo 2251435 2252071 := bstep (se 1 (by rfl) ⟨1689053, by rfl⟩ : syracuseStep 2252071 = 3378107) B3378107
theorem B2533585 : Blo 2251435 2533585 := bbase (se 2 (by rfl) ⟨950094, by rfl⟩ : syracuseStep 2533585 = 1900189) (by norm_num)
theorem B3378113 : Blo 2251435 3378113 := bstep (se 2 (by rfl) ⟨1266792, by rfl⟩ : syracuseStep 3378113 = 2533585) B2533585
theorem B2252075 : Blo 2251435 2252075 := bstep (se 1 (by rfl) ⟨1689056, by rfl⟩ : syracuseStep 2252075 = 3378113) B3378113
theorem B8116645 : Blo 2251435 8116645 := bbase (se 4 (by rfl) ⟨760935, by rfl⟩ : syracuseStep 8116645 = 1521871) (by norm_num)
theorem B10822193 : Blo 2251435 10822193 := bstep (se 2 (by rfl) ⟨4058322, by rfl⟩ : syracuseStep 10822193 = 8116645) B8116645
theorem B7214795 : Blo 2251435 7214795 := bstep (se 1 (by rfl) ⟨5411096, by rfl⟩ : syracuseStep 7214795 = 10822193) B10822193
theorem B4809863 : Blo 2251435 4809863 := bstep (se 1 (by rfl) ⟨3607397, by rfl⟩ : syracuseStep 4809863 = 7214795) B7214795
theorem B3206575 : Blo 2251435 3206575 := bstep (se 1 (by rfl) ⟨2404931, by rfl⟩ : syracuseStep 3206575 = 4809863) B4809863
theorem B4275433 : Blo 2251435 4275433 := bstep (se 2 (by rfl) ⟨1603287, by rfl⟩ : syracuseStep 4275433 = 3206575) B3206575
theorem B5700577 : Blo 2251435 5700577 := bstep (se 2 (by rfl) ⟨2137716, by rfl⟩ : syracuseStep 5700577 = 4275433) B4275433
theorem B7600769 : Blo 2251435 7600769 := bstep (se 2 (by rfl) ⟨2850288, by rfl⟩ : syracuseStep 7600769 = 5700577) B5700577
theorem B5067179 : Blo 2251435 5067179 := bstep (se 1 (by rfl) ⟨3800384, by rfl⟩ : syracuseStep 5067179 = 7600769) B7600769
theorem B3378119 : Blo 2251435 3378119 := bstep (se 1 (by rfl) ⟨2533589, by rfl⟩ : syracuseStep 3378119 = 5067179) B5067179
theorem B2252079 : Blo 2251435 2252079 := bstep (se 1 (by rfl) ⟨1689059, by rfl⟩ : syracuseStep 2252079 = 3378119) B3378119
theorem B3378125 : Blo 2251435 3378125 := bbase (se 3 (by rfl) ⟨633398, by rfl⟩ : syracuseStep 3378125 = 1266797) (by norm_num)
theorem B2252083 : Blo 2251435 2252083 := bstep (se 1 (by rfl) ⟨1689062, by rfl⟩ : syracuseStep 2252083 = 3378125) B3378125
theorem B5067197 : Blo 2251435 5067197 := bbase (se 3 (by rfl) ⟨950099, by rfl⟩ : syracuseStep 5067197 = 1900199) (by norm_num)
theorem B3378131 : Blo 2251435 3378131 := bstep (se 1 (by rfl) ⟨2533598, by rfl⟩ : syracuseStep 3378131 = 5067197) B5067197
theorem B2252087 : Blo 2251435 2252087 := bstep (se 1 (by rfl) ⟨1689065, by rfl⟩ : syracuseStep 2252087 = 3378131) B3378131
theorem B3800405 : Blo 2251435 3800405 := bbase (se 11 (by rfl) ⟨2783, by rfl⟩ : syracuseStep 3800405 = 5567) (by norm_num)
theorem B2533603 : Blo 2251435 2533603 := bstep (se 1 (by rfl) ⟨1900202, by rfl⟩ : syracuseStep 2533603 = 3800405) B3800405
theorem B3378137 : Blo 2251435 3378137 := bstep (se 2 (by rfl) ⟨1266801, by rfl⟩ : syracuseStep 3378137 = 2533603) B2533603
theorem B2252091 : Blo 2251435 2252091 := bstep (se 1 (by rfl) ⟨1689068, by rfl⟩ : syracuseStep 2252091 = 3378137) B3378137
theorem B5206429 : Blo 2251435 5206429 := bbase (se 3 (by rfl) ⟨976205, by rfl⟩ : syracuseStep 5206429 = 1952411) (by norm_num)
theorem B6941905 : Blo 2251435 6941905 := bstep (se 2 (by rfl) ⟨2603214, by rfl⟩ : syracuseStep 6941905 = 5206429) B5206429
theorem B37023493 : Blo 2251435 37023493 := bstep (se 4 (by rfl) ⟨3470952, by rfl⟩ : syracuseStep 37023493 = 6941905) B6941905
theorem B49364657 : Blo 2251435 49364657 := bstep (se 2 (by rfl) ⟨18511746, by rfl⟩ : syracuseStep 49364657 = 37023493) B37023493
theorem B32909771 : Blo 2251435 32909771 := bstep (se 1 (by rfl) ⟨24682328, by rfl⟩ : syracuseStep 32909771 = 49364657) B49364657
theorem B87759389 : Blo 2251435 87759389 := bstep (se 3 (by rfl) ⟨16454885, by rfl⟩ : syracuseStep 87759389 = 32909771) B32909771
theorem B58506259 : Blo 2251435 58506259 := bstep (se 1 (by rfl) ⟨43879694, by rfl⟩ : syracuseStep 58506259 = 87759389) B87759389
theorem B78008345 : Blo 2251435 78008345 := bstep (se 2 (by rfl) ⟨29253129, by rfl⟩ : syracuseStep 78008345 = 58506259) B58506259
theorem B52005563 : Blo 2251435 52005563 := bstep (se 1 (by rfl) ⟨39004172, by rfl⟩ : syracuseStep 52005563 = 78008345) B78008345
theorem B34670375 : Blo 2251435 34670375 := bstep (se 1 (by rfl) ⟨26002781, by rfl⟩ : syracuseStep 34670375 = 52005563) B52005563
theorem B23113583 : Blo 2251435 23113583 := bstep (se 1 (by rfl) ⟨17335187, by rfl⟩ : syracuseStep 23113583 = 34670375) B34670375
theorem B15409055 : Blo 2251435 15409055 := bstep (se 1 (by rfl) ⟨11556791, by rfl⟩ : syracuseStep 15409055 = 23113583) B23113583
theorem B10272703 : Blo 2251435 10272703 := bstep (se 1 (by rfl) ⟨7704527, by rfl⟩ : syracuseStep 10272703 = 15409055) B15409055
theorem B13696937 : Blo 2251435 13696937 := bstep (se 2 (by rfl) ⟨5136351, by rfl⟩ : syracuseStep 13696937 = 10272703) B10272703
theorem B9131291 : Blo 2251435 9131291 := bstep (se 1 (by rfl) ⟨6848468, by rfl⟩ : syracuseStep 9131291 = 13696937) B13696937
theorem B6087527 : Blo 2251435 6087527 := bstep (se 1 (by rfl) ⟨4565645, by rfl⟩ : syracuseStep 6087527 = 9131291) B9131291
theorem B4058351 : Blo 2251435 4058351 := bstep (se 1 (by rfl) ⟨3043763, by rfl⟩ : syracuseStep 4058351 = 6087527) B6087527
theorem B2705567 : Blo 2251435 2705567 := bstep (se 1 (by rfl) ⟨2029175, by rfl⟩ : syracuseStep 2705567 = 4058351) B4058351
theorem B7214845 : Blo 2251435 7214845 := bstep (se 3 (by rfl) ⟨1352783, by rfl⟩ : syracuseStep 7214845 = 2705567) B2705567
theorem B9619793 : Blo 2251435 9619793 := bstep (se 2 (by rfl) ⟨3607422, by rfl⟩ : syracuseStep 9619793 = 7214845) B7214845
theorem B6413195 : Blo 2251435 6413195 := bstep (se 1 (by rfl) ⟨4809896, by rfl⟩ : syracuseStep 6413195 = 9619793) B9619793
theorem B17101853 : Blo 2251435 17101853 := bstep (se 3 (by rfl) ⟨3206597, by rfl⟩ : syracuseStep 17101853 = 6413195) B6413195
theorem B11401235 : Blo 2251435 11401235 := bstep (se 1 (by rfl) ⟨8550926, by rfl⟩ : syracuseStep 11401235 = 17101853) B17101853
theorem B7600823 : Blo 2251435 7600823 := bstep (se 1 (by rfl) ⟨5700617, by rfl⟩ : syracuseStep 7600823 = 11401235) B11401235
theorem B5067215 : Blo 2251435 5067215 := bstep (se 1 (by rfl) ⟨3800411, by rfl⟩ : syracuseStep 5067215 = 7600823) B7600823
theorem B3378143 : Blo 2251435 3378143 := bstep (se 1 (by rfl) ⟨2533607, by rfl⟩ : syracuseStep 3378143 = 5067215) B5067215
theorem B2252095 : Blo 2251435 2252095 := bstep (se 1 (by rfl) ⟨1689071, by rfl⟩ : syracuseStep 2252095 = 3378143) B3378143
theorem B3378149 : Blo 2251435 3378149 := bbase (se 4 (by rfl) ⟨316701, by rfl⟩ : syracuseStep 3378149 = 633403) (by norm_num)
theorem B2252099 : Blo 2251435 2252099 := bstep (se 1 (by rfl) ⟨1689074, by rfl⟩ : syracuseStep 2252099 = 3378149) B3378149
theorem B9619829 : Blo 2251435 9619829 := bbase (se 5 (by rfl) ⟨450929, by rfl⟩ : syracuseStep 9619829 = 901859) (by norm_num)
theorem B6413219 : Blo 2251435 6413219 := bstep (se 1 (by rfl) ⟨4809914, by rfl⟩ : syracuseStep 6413219 = 9619829) B9619829
theorem B4275479 : Blo 2251435 4275479 := bstep (se 1 (by rfl) ⟨3206609, by rfl⟩ : syracuseStep 4275479 = 6413219) B6413219
theorem B2850319 : Blo 2251435 2850319 := bstep (se 1 (by rfl) ⟨2137739, by rfl⟩ : syracuseStep 2850319 = 4275479) B4275479
theorem B3800425 : Blo 2251435 3800425 := bstep (se 2 (by rfl) ⟨1425159, by rfl⟩ : syracuseStep 3800425 = 2850319) B2850319
theorem B5067233 : Blo 2251435 5067233 := bstep (se 2 (by rfl) ⟨1900212, by rfl⟩ : syracuseStep 5067233 = 3800425) B3800425
theorem B3378155 : Blo 2251435 3378155 := bstep (se 1 (by rfl) ⟨2533616, by rfl⟩ : syracuseStep 3378155 = 5067233) B5067233
theorem B2252103 : Blo 2251435 2252103 := bstep (se 1 (by rfl) ⟨1689077, by rfl⟩ : syracuseStep 2252103 = 3378155) B3378155
theorem B2533621 : Blo 2251435 2533621 := bbase (se 5 (by rfl) ⟨118763, by rfl⟩ : syracuseStep 2533621 = 237527) (by norm_num)
theorem B3378161 : Blo 2251435 3378161 := bstep (se 2 (by rfl) ⟨1266810, by rfl⟩ : syracuseStep 3378161 = 2533621) B2533621
theorem B2252107 : Blo 2251435 2252107 := bstep (se 1 (by rfl) ⟨1689080, by rfl⟩ : syracuseStep 2252107 = 3378161) B3378161
theorem B2850329 : Blo 2251435 2850329 := bbase (se 2 (by rfl) ⟨1068873, by rfl⟩ : syracuseStep 2850329 = 2137747) (by norm_num)
theorem B7600877 : Blo 2251435 7600877 := bstep (se 3 (by rfl) ⟨1425164, by rfl⟩ : syracuseStep 7600877 = 2850329) B2850329
theorem B5067251 : Blo 2251435 5067251 := bstep (se 1 (by rfl) ⟨3800438, by rfl⟩ : syracuseStep 5067251 = 7600877) B7600877
theorem B3378167 : Blo 2251435 3378167 := bstep (se 1 (by rfl) ⟨2533625, by rfl⟩ : syracuseStep 3378167 = 5067251) B5067251
theorem B2252111 : Blo 2251435 2252111 := bstep (se 1 (by rfl) ⟨1689083, by rfl⟩ : syracuseStep 2252111 = 3378167) B3378167
theorem B3378173 : Blo 2251435 3378173 := bbase (se 3 (by rfl) ⟨633407, by rfl⟩ : syracuseStep 3378173 = 1266815) (by norm_num)
theorem B2252115 : Blo 2251435 2252115 := bstep (se 1 (by rfl) ⟨1689086, by rfl⟩ : syracuseStep 2252115 = 3378173) B3378173
theorem B5067269 : Blo 2251435 5067269 := bbase (se 4 (by rfl) ⟨475056, by rfl⟩ : syracuseStep 5067269 = 950113) (by norm_num)
theorem B3378179 : Blo 2251435 3378179 := bstep (se 1 (by rfl) ⟨2533634, by rfl⟩ : syracuseStep 3378179 = 5067269) B5067269
theorem B2252119 : Blo 2251435 2252119 := bstep (se 1 (by rfl) ⟨1689089, by rfl⟩ : syracuseStep 2252119 = 3378179) B3378179
theorem B4275517 : Blo 2251435 4275517 := bbase (se 3 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 4275517 = 1603319) (by norm_num)
theorem B5700689 : Blo 2251435 5700689 := bstep (se 2 (by rfl) ⟨2137758, by rfl⟩ : syracuseStep 5700689 = 4275517) B4275517
theorem B3800459 : Blo 2251435 3800459 := bstep (se 1 (by rfl) ⟨2850344, by rfl⟩ : syracuseStep 3800459 = 5700689) B5700689
theorem B2533639 : Blo 2251435 2533639 := bstep (se 1 (by rfl) ⟨1900229, by rfl⟩ : syracuseStep 2533639 = 3800459) B3800459
theorem B3378185 : Blo 2251435 3378185 := bstep (se 2 (by rfl) ⟨1266819, by rfl⟩ : syracuseStep 3378185 = 2533639) B2533639
theorem B2252123 : Blo 2251435 2252123 := bstep (se 1 (by rfl) ⟨1689092, by rfl⟩ : syracuseStep 2252123 = 3378185) B3378185
theorem B11401397 : Blo 2251435 11401397 := bbase (se 5 (by rfl) ⟨534440, by rfl⟩ : syracuseStep 11401397 = 1068881) (by norm_num)
theorem B7600931 : Blo 2251435 7600931 := bstep (se 1 (by rfl) ⟨5700698, by rfl⟩ : syracuseStep 7600931 = 11401397) B11401397
theorem B5067287 : Blo 2251435 5067287 := bstep (se 1 (by rfl) ⟨3800465, by rfl⟩ : syracuseStep 5067287 = 7600931) B7600931
theorem B3378191 : Blo 2251435 3378191 := bstep (se 1 (by rfl) ⟨2533643, by rfl⟩ : syracuseStep 3378191 = 5067287) B5067287
theorem B2252127 : Blo 2251435 2252127 := bstep (se 1 (by rfl) ⟨1689095, by rfl⟩ : syracuseStep 2252127 = 3378191) B3378191
theorem B3378197 : Blo 2251435 3378197 := bbase (se 6 (by rfl) ⟨79176, by rfl⟩ : syracuseStep 3378197 = 158353) (by norm_num)
theorem B2252131 : Blo 2251435 2252131 := bstep (se 1 (by rfl) ⟨1689098, by rfl⟩ : syracuseStep 2252131 = 3378197) B3378197
theorem B3250405 : Blo 2251435 3250405 := bbase (se 4 (by rfl) ⟨304725, by rfl⟩ : syracuseStep 3250405 = 609451) (by norm_num)
theorem B4333873 : Blo 2251435 4333873 := bstep (se 2 (by rfl) ⟨1625202, by rfl⟩ : syracuseStep 4333873 = 3250405) B3250405
theorem B5778497 : Blo 2251435 5778497 := bstep (se 2 (by rfl) ⟨2166936, by rfl⟩ : syracuseStep 5778497 = 4333873) B4333873
theorem B15409325 : Blo 2251435 15409325 := bstep (se 3 (by rfl) ⟨2889248, by rfl⟩ : syracuseStep 15409325 = 5778497) B5778497
theorem B41091533 : Blo 2251435 41091533 := bstep (se 3 (by rfl) ⟨7704662, by rfl⟩ : syracuseStep 41091533 = 15409325) B15409325
theorem B27394355 : Blo 2251435 27394355 := bstep (se 1 (by rfl) ⟨20545766, by rfl⟩ : syracuseStep 27394355 = 41091533) B41091533
theorem B18262903 : Blo 2251435 18262903 := bstep (se 1 (by rfl) ⟨13697177, by rfl⟩ : syracuseStep 18262903 = 27394355) B27394355
theorem B24350537 : Blo 2251435 24350537 := bstep (se 2 (by rfl) ⟨9131451, by rfl⟩ : syracuseStep 24350537 = 18262903) B18262903
theorem B16233691 : Blo 2251435 16233691 := bstep (se 1 (by rfl) ⟨12175268, by rfl⟩ : syracuseStep 16233691 = 24350537) B24350537
theorem B21644921 : Blo 2251435 21644921 := bstep (se 2 (by rfl) ⟨8116845, by rfl⟩ : syracuseStep 21644921 = 16233691) B16233691
theorem B14429947 : Blo 2251435 14429947 := bstep (se 1 (by rfl) ⟨10822460, by rfl⟩ : syracuseStep 14429947 = 21644921) B21644921
theorem B19239929 : Blo 2251435 19239929 := bstep (se 2 (by rfl) ⟨7214973, by rfl⟩ : syracuseStep 19239929 = 14429947) B14429947
theorem B12826619 : Blo 2251435 12826619 := bstep (se 1 (by rfl) ⟨9619964, by rfl⟩ : syracuseStep 12826619 = 19239929) B19239929
theorem B8551079 : Blo 2251435 8551079 := bstep (se 1 (by rfl) ⟨6413309, by rfl⟩ : syracuseStep 8551079 = 12826619) B12826619
theorem B5700719 : Blo 2251435 5700719 := bstep (se 1 (by rfl) ⟨4275539, by rfl⟩ : syracuseStep 5700719 = 8551079) B8551079
theorem B3800479 : Blo 2251435 3800479 := bstep (se 1 (by rfl) ⟨2850359, by rfl⟩ : syracuseStep 3800479 = 5700719) B5700719
theorem B5067305 : Blo 2251435 5067305 := bstep (se 2 (by rfl) ⟨1900239, by rfl⟩ : syracuseStep 5067305 = 3800479) B3800479
theorem B3378203 : Blo 2251435 3378203 := bstep (se 1 (by rfl) ⟨2533652, by rfl⟩ : syracuseStep 3378203 = 5067305) B5067305
theorem B2252135 : Blo 2251435 2252135 := bstep (se 1 (by rfl) ⟨1689101, by rfl⟩ : syracuseStep 2252135 = 3378203) B3378203
theorem B2533657 : Blo 2251435 2533657 := bbase (se 2 (by rfl) ⟨950121, by rfl⟩ : syracuseStep 2533657 = 1900243) (by norm_num)
theorem B3378209 : Blo 2251435 3378209 := bstep (se 2 (by rfl) ⟨1266828, by rfl⟩ : syracuseStep 3378209 = 2533657) B2533657
theorem B2252139 : Blo 2251435 2252139 := bstep (se 1 (by rfl) ⟨1689104, by rfl⟩ : syracuseStep 2252139 = 3378209) B3378209
theorem B8551109 : Blo 2251435 8551109 := bbase (se 4 (by rfl) ⟨801666, by rfl⟩ : syracuseStep 8551109 = 1603333) (by norm_num)
theorem B5700739 : Blo 2251435 5700739 := bstep (se 1 (by rfl) ⟨4275554, by rfl⟩ : syracuseStep 5700739 = 8551109) B8551109
theorem B7600985 : Blo 2251435 7600985 := bstep (se 2 (by rfl) ⟨2850369, by rfl⟩ : syracuseStep 7600985 = 5700739) B5700739
theorem B5067323 : Blo 2251435 5067323 := bstep (se 1 (by rfl) ⟨3800492, by rfl⟩ : syracuseStep 5067323 = 7600985) B7600985
theorem B3378215 : Blo 2251435 3378215 := bstep (se 1 (by rfl) ⟨2533661, by rfl⟩ : syracuseStep 3378215 = 5067323) B5067323
theorem B2252143 : Blo 2251435 2252143 := bstep (se 1 (by rfl) ⟨1689107, by rfl⟩ : syracuseStep 2252143 = 3378215) B3378215
theorem B3378221 : Blo 2251435 3378221 := bbase (se 3 (by rfl) ⟨633416, by rfl⟩ : syracuseStep 3378221 = 1266833) (by norm_num)
theorem B2252147 : Blo 2251435 2252147 := bstep (se 1 (by rfl) ⟨1689110, by rfl⟩ : syracuseStep 2252147 = 3378221) B3378221
theorem B5067341 : Blo 2251435 5067341 := bbase (se 3 (by rfl) ⟨950126, by rfl⟩ : syracuseStep 5067341 = 1900253) (by norm_num)
theorem B3378227 : Blo 2251435 3378227 := bstep (se 1 (by rfl) ⟨2533670, by rfl⟩ : syracuseStep 3378227 = 5067341) B5067341
theorem B2252151 : Blo 2251435 2252151 := bstep (se 1 (by rfl) ⟨1689113, by rfl⟩ : syracuseStep 2252151 = 3378227) B3378227
theorem B2850385 : Blo 2251435 2850385 := bbase (se 2 (by rfl) ⟨1068894, by rfl⟩ : syracuseStep 2850385 = 2137789) (by norm_num)
theorem B3800513 : Blo 2251435 3800513 := bstep (se 2 (by rfl) ⟨1425192, by rfl⟩ : syracuseStep 3800513 = 2850385) B2850385
theorem B2533675 : Blo 2251435 2533675 := bstep (se 1 (by rfl) ⟨1900256, by rfl⟩ : syracuseStep 2533675 = 3800513) B3800513
theorem B3378233 : Blo 2251435 3378233 := bstep (se 2 (by rfl) ⟨1266837, by rfl⟩ : syracuseStep 3378233 = 2533675) B2533675
theorem B2252155 : Blo 2251435 2252155 := bstep (se 1 (by rfl) ⟨1689116, by rfl⟩ : syracuseStep 2252155 = 3378233) B3378233
theorem B3607525 : Blo 2251435 3607525 := bbase (se 4 (by rfl) ⟨338205, by rfl⟩ : syracuseStep 3607525 = 676411) (by norm_num)
theorem B4810033 : Blo 2251435 4810033 := bstep (se 2 (by rfl) ⟨1803762, by rfl⟩ : syracuseStep 4810033 = 3607525) B3607525
theorem B25653509 : Blo 2251435 25653509 := bstep (se 4 (by rfl) ⟨2405016, by rfl⟩ : syracuseStep 25653509 = 4810033) B4810033
theorem B17102339 : Blo 2251435 17102339 := bstep (se 1 (by rfl) ⟨12826754, by rfl⟩ : syracuseStep 17102339 = 25653509) B25653509
theorem B11401559 : Blo 2251435 11401559 := bstep (se 1 (by rfl) ⟨8551169, by rfl⟩ : syracuseStep 11401559 = 17102339) B17102339
theorem B7601039 : Blo 2251435 7601039 := bstep (se 1 (by rfl) ⟨5700779, by rfl⟩ : syracuseStep 7601039 = 11401559) B11401559
theorem B5067359 : Blo 2251435 5067359 := bstep (se 1 (by rfl) ⟨3800519, by rfl⟩ : syracuseStep 5067359 = 7601039) B7601039
theorem B3378239 : Blo 2251435 3378239 := bstep (se 1 (by rfl) ⟨2533679, by rfl⟩ : syracuseStep 3378239 = 5067359) B5067359
theorem B2252159 : Blo 2251435 2252159 := bstep (se 1 (by rfl) ⟨1689119, by rfl⟩ : syracuseStep 2252159 = 3378239) B3378239
theorem B3378245 : Blo 2251435 3378245 := bbase (se 4 (by rfl) ⟨316710, by rfl⟩ : syracuseStep 3378245 = 633421) (by norm_num)
theorem B2252163 : Blo 2251435 2252163 := bstep (se 1 (by rfl) ⟨1689122, by rfl⟩ : syracuseStep 2252163 = 3378245) B3378245
theorem B3800533 : Blo 2251435 3800533 := bbase (se 7 (by rfl) ⟨44537, by rfl⟩ : syracuseStep 3800533 = 89075) (by norm_num)
theorem B5067377 : Blo 2251435 5067377 := bstep (se 2 (by rfl) ⟨1900266, by rfl⟩ : syracuseStep 5067377 = 3800533) B3800533
theorem B3378251 : Blo 2251435 3378251 := bstep (se 1 (by rfl) ⟨2533688, by rfl⟩ : syracuseStep 3378251 = 5067377) B5067377
theorem B2252167 : Blo 2251435 2252167 := bstep (se 1 (by rfl) ⟨1689125, by rfl⟩ : syracuseStep 2252167 = 3378251) B3378251
theorem B2533693 : Blo 2251435 2533693 := bbase (se 3 (by rfl) ⟨475067, by rfl⟩ : syracuseStep 2533693 = 950135) (by norm_num)
theorem B3378257 : Blo 2251435 3378257 := bstep (se 2 (by rfl) ⟨1266846, by rfl⟩ : syracuseStep 3378257 = 2533693) B2533693
theorem B2252171 : Blo 2251435 2252171 := bstep (se 1 (by rfl) ⟨1689128, by rfl⟩ : syracuseStep 2252171 = 3378257) B3378257
theorem B7601093 : Blo 2251435 7601093 := bbase (se 4 (by rfl) ⟨712602, by rfl⟩ : syracuseStep 7601093 = 1425205) (by norm_num)
theorem B5067395 : Blo 2251435 5067395 := bstep (se 1 (by rfl) ⟨3800546, by rfl⟩ : syracuseStep 5067395 = 7601093) B7601093
theorem B3378263 : Blo 2251435 3378263 := bstep (se 1 (by rfl) ⟨2533697, by rfl⟩ : syracuseStep 3378263 = 5067395) B5067395
theorem B2252175 : Blo 2251435 2252175 := bstep (se 1 (by rfl) ⟨1689131, by rfl⟩ : syracuseStep 2252175 = 3378263) B3378263
theorem B3378269 : Blo 2251435 3378269 := bbase (se 3 (by rfl) ⟨633425, by rfl⟩ : syracuseStep 3378269 = 1266851) (by norm_num)
theorem B2252179 : Blo 2251435 2252179 := bstep (se 1 (by rfl) ⟨1689134, by rfl⟩ : syracuseStep 2252179 = 3378269) B3378269
theorem B5067413 : Blo 2251435 5067413 := bbase (se 6 (by rfl) ⟨118767, by rfl⟩ : syracuseStep 5067413 = 237535) (by norm_num)
theorem B3378275 : Blo 2251435 3378275 := bstep (se 1 (by rfl) ⟨2533706, by rfl⟩ : syracuseStep 3378275 = 5067413) B5067413
theorem B2252183 : Blo 2251435 2252183 := bstep (se 1 (by rfl) ⟨1689137, by rfl⟩ : syracuseStep 2252183 = 3378275) B3378275
theorem B5411357 : Blo 2251435 5411357 := bbase (se 3 (by rfl) ⟨1014629, by rfl⟩ : syracuseStep 5411357 = 2029259) (by norm_num)
theorem B3607571 : Blo 2251435 3607571 := bstep (se 1 (by rfl) ⟨2705678, by rfl⟩ : syracuseStep 3607571 = 5411357) B5411357
theorem B2405047 : Blo 2251435 2405047 := bstep (se 1 (by rfl) ⟨1803785, by rfl⟩ : syracuseStep 2405047 = 3607571) B3607571
theorem B3206729 : Blo 2251435 3206729 := bstep (se 2 (by rfl) ⟨1202523, by rfl⟩ : syracuseStep 3206729 = 2405047) B2405047
theorem B8551277 : Blo 2251435 8551277 := bstep (se 3 (by rfl) ⟨1603364, by rfl⟩ : syracuseStep 8551277 = 3206729) B3206729
theorem B5700851 : Blo 2251435 5700851 := bstep (se 1 (by rfl) ⟨4275638, by rfl⟩ : syracuseStep 5700851 = 8551277) B8551277
theorem B3800567 : Blo 2251435 3800567 := bstep (se 1 (by rfl) ⟨2850425, by rfl⟩ : syracuseStep 3800567 = 5700851) B5700851
theorem B2533711 : Blo 2251435 2533711 := bstep (se 1 (by rfl) ⟨1900283, by rfl⟩ : syracuseStep 2533711 = 3800567) B3800567
theorem B3378281 : Blo 2251435 3378281 := bstep (se 2 (by rfl) ⟨1266855, by rfl⟩ : syracuseStep 3378281 = 2533711) B2533711
theorem B2252187 : Blo 2251435 2252187 := bstep (se 1 (by rfl) ⟨1689140, by rfl⟩ : syracuseStep 2252187 = 3378281) B3378281
theorem B4333981 : Blo 2251435 4333981 := bbase (se 3 (by rfl) ⟨812621, by rfl⟩ : syracuseStep 4333981 = 1625243) (by norm_num)
theorem B5778641 : Blo 2251435 5778641 := bstep (se 2 (by rfl) ⟨2166990, by rfl⟩ : syracuseStep 5778641 = 4333981) B4333981
theorem B15409709 : Blo 2251435 15409709 := bstep (se 3 (by rfl) ⟨2889320, by rfl⟩ : syracuseStep 15409709 = 5778641) B5778641
theorem B10273139 : Blo 2251435 10273139 := bstep (se 1 (by rfl) ⟨7704854, by rfl⟩ : syracuseStep 10273139 = 15409709) B15409709
theorem B6848759 : Blo 2251435 6848759 := bstep (se 1 (by rfl) ⟨5136569, by rfl⟩ : syracuseStep 6848759 = 10273139) B10273139
theorem B18263357 : Blo 2251435 18263357 := bstep (se 3 (by rfl) ⟨3424379, by rfl⟩ : syracuseStep 18263357 = 6848759) B6848759
theorem B12175571 : Blo 2251435 12175571 := bstep (se 1 (by rfl) ⟨9131678, by rfl⟩ : syracuseStep 12175571 = 18263357) B18263357
theorem B8117047 : Blo 2251435 8117047 := bstep (se 1 (by rfl) ⟨6087785, by rfl⟩ : syracuseStep 8117047 = 12175571) B12175571
theorem B10822729 : Blo 2251435 10822729 := bstep (se 2 (by rfl) ⟨4058523, by rfl⟩ : syracuseStep 10822729 = 8117047) B8117047
theorem B14430305 : Blo 2251435 14430305 := bstep (se 2 (by rfl) ⟨5411364, by rfl⟩ : syracuseStep 14430305 = 10822729) B10822729
theorem B9620203 : Blo 2251435 9620203 := bstep (se 1 (by rfl) ⟨7215152, by rfl⟩ : syracuseStep 9620203 = 14430305) B14430305
theorem B12826937 : Blo 2251435 12826937 := bstep (se 2 (by rfl) ⟨4810101, by rfl⟩ : syracuseStep 12826937 = 9620203) B9620203
theorem B8551291 : Blo 2251435 8551291 := bstep (se 1 (by rfl) ⟨6413468, by rfl⟩ : syracuseStep 8551291 = 12826937) B12826937
theorem B11401721 : Blo 2251435 11401721 := bstep (se 2 (by rfl) ⟨4275645, by rfl⟩ : syracuseStep 11401721 = 8551291) B8551291
theorem B7601147 : Blo 2251435 7601147 := bstep (se 1 (by rfl) ⟨5700860, by rfl⟩ : syracuseStep 7601147 = 11401721) B11401721
theorem B5067431 : Blo 2251435 5067431 := bstep (se 1 (by rfl) ⟨3800573, by rfl⟩ : syracuseStep 5067431 = 7601147) B7601147
theorem B3378287 : Blo 2251435 3378287 := bstep (se 1 (by rfl) ⟨2533715, by rfl⟩ : syracuseStep 3378287 = 5067431) B5067431
theorem B2252191 : Blo 2251435 2252191 := bstep (se 1 (by rfl) ⟨1689143, by rfl⟩ : syracuseStep 2252191 = 3378287) B3378287
theorem B3378293 : Blo 2251435 3378293 := bbase (se 5 (by rfl) ⟨158357, by rfl⟩ : syracuseStep 3378293 = 316715) (by norm_num)
theorem B2252195 : Blo 2251435 2252195 := bstep (se 1 (by rfl) ⟨1689146, by rfl⟩ : syracuseStep 2252195 = 3378293) B3378293
theorem B4275661 : Blo 2251435 4275661 := bbase (se 3 (by rfl) ⟨801686, by rfl⟩ : syracuseStep 4275661 = 1603373) (by norm_num)
theorem B5700881 : Blo 2251435 5700881 := bstep (se 2 (by rfl) ⟨2137830, by rfl⟩ : syracuseStep 5700881 = 4275661) B4275661
theorem B3800587 : Blo 2251435 3800587 := bstep (se 1 (by rfl) ⟨2850440, by rfl⟩ : syracuseStep 3800587 = 5700881) B5700881
theorem B5067449 : Blo 2251435 5067449 := bstep (se 2 (by rfl) ⟨1900293, by rfl⟩ : syracuseStep 5067449 = 3800587) B3800587
theorem B3378299 : Blo 2251435 3378299 := bstep (se 1 (by rfl) ⟨2533724, by rfl⟩ : syracuseStep 3378299 = 5067449) B5067449
theorem B2252199 : Blo 2251435 2252199 := bstep (se 1 (by rfl) ⟨1689149, by rfl⟩ : syracuseStep 2252199 = 3378299) B3378299
theorem B2533729 : Blo 2251435 2533729 := bbase (se 2 (by rfl) ⟨950148, by rfl⟩ : syracuseStep 2533729 = 1900297) (by norm_num)
theorem B3378305 : Blo 2251435 3378305 := bstep (se 2 (by rfl) ⟨1266864, by rfl⟩ : syracuseStep 3378305 = 2533729) B2533729
theorem B2252203 : Blo 2251435 2252203 := bstep (se 1 (by rfl) ⟨1689152, by rfl⟩ : syracuseStep 2252203 = 3378305) B3378305
theorem B5700901 : Blo 2251435 5700901 := bbase (se 4 (by rfl) ⟨534459, by rfl⟩ : syracuseStep 5700901 = 1068919) (by norm_num)
theorem B7601201 : Blo 2251435 7601201 := bstep (se 2 (by rfl) ⟨2850450, by rfl⟩ : syracuseStep 7601201 = 5700901) B5700901
theorem B5067467 : Blo 2251435 5067467 := bstep (se 1 (by rfl) ⟨3800600, by rfl⟩ : syracuseStep 5067467 = 7601201) B7601201
theorem B3378311 : Blo 2251435 3378311 := bstep (se 1 (by rfl) ⟨2533733, by rfl⟩ : syracuseStep 3378311 = 5067467) B5067467
theorem B2252207 : Blo 2251435 2252207 := bstep (se 1 (by rfl) ⟨1689155, by rfl⟩ : syracuseStep 2252207 = 3378311) B3378311
theorem B3378317 : Blo 2251435 3378317 := bbase (se 3 (by rfl) ⟨633434, by rfl⟩ : syracuseStep 3378317 = 1266869) (by norm_num)
theorem B2252211 : Blo 2251435 2252211 := bstep (se 1 (by rfl) ⟨1689158, by rfl⟩ : syracuseStep 2252211 = 3378317) B3378317
theorem B5067485 : Blo 2251435 5067485 := bbase (se 3 (by rfl) ⟨950153, by rfl⟩ : syracuseStep 5067485 = 1900307) (by norm_num)
theorem B3378323 : Blo 2251435 3378323 := bstep (se 1 (by rfl) ⟨2533742, by rfl⟩ : syracuseStep 3378323 = 5067485) B5067485
theorem B2252215 : Blo 2251435 2252215 := bstep (se 1 (by rfl) ⟨1689161, by rfl⟩ : syracuseStep 2252215 = 3378323) B3378323
theorem B3800621 : Blo 2251435 3800621 := bbase (se 3 (by rfl) ⟨712616, by rfl⟩ : syracuseStep 3800621 = 1425233) (by norm_num)
theorem B2533747 : Blo 2251435 2533747 := bstep (se 1 (by rfl) ⟨1900310, by rfl⟩ : syracuseStep 2533747 = 3800621) B3800621
theorem B3378329 : Blo 2251435 3378329 := bstep (se 2 (by rfl) ⟨1266873, by rfl⟩ : syracuseStep 3378329 = 2533747) B2533747
theorem B2252219 : Blo 2251435 2252219 := bstep (se 1 (by rfl) ⟨1689164, by rfl⟩ : syracuseStep 2252219 = 3378329) B3378329
theorem B7810085 : Blo 2251435 7810085 := bbase (se 4 (by rfl) ⟨732195, by rfl⟩ : syracuseStep 7810085 = 1464391) (by norm_num)
theorem B5206723 : Blo 2251435 5206723 := bstep (se 1 (by rfl) ⟨3905042, by rfl⟩ : syracuseStep 5206723 = 7810085) B7810085
theorem B27769189 : Blo 2251435 27769189 := bstep (se 4 (by rfl) ⟨2603361, by rfl⟩ : syracuseStep 27769189 = 5206723) B5206723
theorem B37025585 : Blo 2251435 37025585 := bstep (se 2 (by rfl) ⟨13884594, by rfl⟩ : syracuseStep 37025585 = 27769189) B27769189
theorem B24683723 : Blo 2251435 24683723 := bstep (se 1 (by rfl) ⟨18512792, by rfl⟩ : syracuseStep 24683723 = 37025585) B37025585
theorem B16455815 : Blo 2251435 16455815 := bstep (se 1 (by rfl) ⟨12341861, by rfl⟩ : syracuseStep 16455815 = 24683723) B24683723
theorem B10970543 : Blo 2251435 10970543 := bstep (se 1 (by rfl) ⟨8227907, by rfl⟩ : syracuseStep 10970543 = 16455815) B16455815
theorem B7313695 : Blo 2251435 7313695 := bstep (se 1 (by rfl) ⟨5485271, by rfl⟩ : syracuseStep 7313695 = 10970543) B10970543
theorem B39006373 : Blo 2251435 39006373 := bstep (se 4 (by rfl) ⟨3656847, by rfl⟩ : syracuseStep 39006373 = 7313695) B7313695
theorem B52008497 : Blo 2251435 52008497 := bstep (se 2 (by rfl) ⟨19503186, by rfl⟩ : syracuseStep 52008497 = 39006373) B39006373
theorem B34672331 : Blo 2251435 34672331 := bstep (se 1 (by rfl) ⟨26004248, by rfl⟩ : syracuseStep 34672331 = 52008497) B52008497
theorem B92459549 : Blo 2251435 92459549 := bstep (se 3 (by rfl) ⟨17336165, by rfl⟩ : syracuseStep 92459549 = 34672331) B34672331
theorem B61639699 : Blo 2251435 61639699 := bstep (se 1 (by rfl) ⟨46229774, by rfl⟩ : syracuseStep 61639699 = 92459549) B92459549
theorem B82186265 : Blo 2251435 82186265 := bstep (se 2 (by rfl) ⟨30819849, by rfl⟩ : syracuseStep 82186265 = 61639699) B61639699
theorem B54790843 : Blo 2251435 54790843 := bstep (se 1 (by rfl) ⟨41093132, by rfl⟩ : syracuseStep 54790843 = 82186265) B82186265
theorem B73054457 : Blo 2251435 73054457 := bstep (se 2 (by rfl) ⟨27395421, by rfl⟩ : syracuseStep 73054457 = 54790843) B54790843
theorem B48702971 : Blo 2251435 48702971 := bstep (se 1 (by rfl) ⟨36527228, by rfl⟩ : syracuseStep 48702971 = 73054457) B73054457
theorem B32468647 : Blo 2251435 32468647 := bstep (se 1 (by rfl) ⟨24351485, by rfl⟩ : syracuseStep 32468647 = 48702971) B48702971
theorem B43291529 : Blo 2251435 43291529 := bstep (se 2 (by rfl) ⟨16234323, by rfl⟩ : syracuseStep 43291529 = 32468647) B32468647
theorem B28861019 : Blo 2251435 28861019 := bstep (se 1 (by rfl) ⟨21645764, by rfl⟩ : syracuseStep 28861019 = 43291529) B43291529
theorem B19240679 : Blo 2251435 19240679 := bstep (se 1 (by rfl) ⟨14430509, by rfl⟩ : syracuseStep 19240679 = 28861019) B28861019
theorem B12827119 : Blo 2251435 12827119 := bstep (se 1 (by rfl) ⟨9620339, by rfl⟩ : syracuseStep 12827119 = 19240679) B19240679
theorem B17102825 : Blo 2251435 17102825 := bstep (se 2 (by rfl) ⟨6413559, by rfl⟩ : syracuseStep 17102825 = 12827119) B12827119
theorem B11401883 : Blo 2251435 11401883 := bstep (se 1 (by rfl) ⟨8551412, by rfl⟩ : syracuseStep 11401883 = 17102825) B17102825
theorem B7601255 : Blo 2251435 7601255 := bstep (se 1 (by rfl) ⟨5700941, by rfl⟩ : syracuseStep 7601255 = 11401883) B11401883
theorem B5067503 : Blo 2251435 5067503 := bstep (se 1 (by rfl) ⟨3800627, by rfl⟩ : syracuseStep 5067503 = 7601255) B7601255
theorem B3378335 : Blo 2251435 3378335 := bstep (se 1 (by rfl) ⟨2533751, by rfl⟩ : syracuseStep 3378335 = 5067503) B5067503
theorem B2252223 : Blo 2251435 2252223 := bstep (se 1 (by rfl) ⟨1689167, by rfl⟩ : syracuseStep 2252223 = 3378335) B3378335
theorem B3378341 : Blo 2251435 3378341 := bbase (se 4 (by rfl) ⟨316719, by rfl⟩ : syracuseStep 3378341 = 633439) (by norm_num)
theorem B2252227 : Blo 2251435 2252227 := bstep (se 1 (by rfl) ⟨1689170, by rfl⟩ : syracuseStep 2252227 = 3378341) B3378341
theorem B2850481 : Blo 2251435 2850481 := bbase (se 2 (by rfl) ⟨1068930, by rfl⟩ : syracuseStep 2850481 = 2137861) (by norm_num)
theorem B3800641 : Blo 2251435 3800641 := bstep (se 2 (by rfl) ⟨1425240, by rfl⟩ : syracuseStep 3800641 = 2850481) B2850481
theorem B5067521 : Blo 2251435 5067521 := bstep (se 2 (by rfl) ⟨1900320, by rfl⟩ : syracuseStep 5067521 = 3800641) B3800641
theorem B3378347 : Blo 2251435 3378347 := bstep (se 1 (by rfl) ⟨2533760, by rfl⟩ : syracuseStep 3378347 = 5067521) B5067521
theorem B2252231 : Blo 2251435 2252231 := bstep (se 1 (by rfl) ⟨1689173, by rfl⟩ : syracuseStep 2252231 = 3378347) B3378347
theorem B2533765 : Blo 2251435 2533765 := bbase (se 4 (by rfl) ⟨237540, by rfl⟩ : syracuseStep 2533765 = 475081) (by norm_num)
theorem B3378353 : Blo 2251435 3378353 := bstep (se 2 (by rfl) ⟨1266882, by rfl⟩ : syracuseStep 3378353 = 2533765) B2533765
theorem B2252235 : Blo 2251435 2252235 := bstep (se 1 (by rfl) ⟨1689176, by rfl⟩ : syracuseStep 2252235 = 3378353) B3378353
theorem B4810205 : Blo 2251435 4810205 := bbase (se 3 (by rfl) ⟨901913, by rfl⟩ : syracuseStep 4810205 = 1803827) (by norm_num)
theorem B3206803 : Blo 2251435 3206803 := bstep (se 1 (by rfl) ⟨2405102, by rfl⟩ : syracuseStep 3206803 = 4810205) B4810205
theorem B4275737 : Blo 2251435 4275737 := bstep (se 2 (by rfl) ⟨1603401, by rfl⟩ : syracuseStep 4275737 = 3206803) B3206803
theorem B2850491 : Blo 2251435 2850491 := bstep (se 1 (by rfl) ⟨2137868, by rfl⟩ : syracuseStep 2850491 = 4275737) B4275737
theorem B7601309 : Blo 2251435 7601309 := bstep (se 3 (by rfl) ⟨1425245, by rfl⟩ : syracuseStep 7601309 = 2850491) B2850491
theorem B5067539 : Blo 2251435 5067539 := bstep (se 1 (by rfl) ⟨3800654, by rfl⟩ : syracuseStep 5067539 = 7601309) B7601309
theorem B3378359 : Blo 2251435 3378359 := bstep (se 1 (by rfl) ⟨2533769, by rfl⟩ : syracuseStep 3378359 = 5067539) B5067539
theorem B2252239 : Blo 2251435 2252239 := bstep (se 1 (by rfl) ⟨1689179, by rfl⟩ : syracuseStep 2252239 = 3378359) B3378359
theorem B3378365 : Blo 2251435 3378365 := bbase (se 3 (by rfl) ⟨633443, by rfl⟩ : syracuseStep 3378365 = 1266887) (by norm_num)
theorem B2252243 : Blo 2251435 2252243 := bstep (se 1 (by rfl) ⟨1689182, by rfl⟩ : syracuseStep 2252243 = 3378365) B3378365
theorem B5067557 : Blo 2251435 5067557 := bbase (se 4 (by rfl) ⟨475083, by rfl⟩ : syracuseStep 5067557 = 950167) (by norm_num)
theorem B3378371 : Blo 2251435 3378371 := bstep (se 1 (by rfl) ⟨2533778, by rfl⟩ : syracuseStep 3378371 = 5067557) B5067557
theorem B2252247 : Blo 2251435 2252247 := bstep (se 1 (by rfl) ⟨1689185, by rfl⟩ : syracuseStep 2252247 = 3378371) B3378371
theorem B5701013 : Blo 2251435 5701013 := bbase (se 6 (by rfl) ⟨133617, by rfl⟩ : syracuseStep 5701013 = 267235) (by norm_num)
theorem B3800675 : Blo 2251435 3800675 := bstep (se 1 (by rfl) ⟨2850506, by rfl⟩ : syracuseStep 3800675 = 5701013) B5701013
theorem B2533783 : Blo 2251435 2533783 := bstep (se 1 (by rfl) ⟨1900337, by rfl⟩ : syracuseStep 2533783 = 3800675) B3800675
theorem B3378377 : Blo 2251435 3378377 := bstep (se 2 (by rfl) ⟨1266891, by rfl⟩ : syracuseStep 3378377 = 2533783) B2533783
theorem B2252251 : Blo 2251435 2252251 := bstep (se 1 (by rfl) ⟨1689188, by rfl⟩ : syracuseStep 2252251 = 3378377) B3378377
theorem B17572949 : Blo 2251435 17572949 := bbase (se 8 (by rfl) ⟨102966, by rfl⟩ : syracuseStep 17572949 = 205933) (by norm_num)
theorem B11715299 : Blo 2251435 11715299 := bstep (se 1 (by rfl) ⟨8786474, by rfl⟩ : syracuseStep 11715299 = 17572949) B17572949
theorem B7810199 : Blo 2251435 7810199 := bstep (se 1 (by rfl) ⟨5857649, by rfl⟩ : syracuseStep 7810199 = 11715299) B11715299
theorem B5206799 : Blo 2251435 5206799 := bstep (se 1 (by rfl) ⟨3905099, by rfl⟩ : syracuseStep 5206799 = 7810199) B7810199
theorem B13884797 : Blo 2251435 13884797 := bstep (se 3 (by rfl) ⟨2603399, by rfl⟩ : syracuseStep 13884797 = 5206799) B5206799
theorem B9256531 : Blo 2251435 9256531 := bstep (se 1 (by rfl) ⟨6942398, by rfl⟩ : syracuseStep 9256531 = 13884797) B13884797
theorem B12342041 : Blo 2251435 12342041 := bstep (se 2 (by rfl) ⟨4628265, by rfl⟩ : syracuseStep 12342041 = 9256531) B9256531
theorem B8228027 : Blo 2251435 8228027 := bstep (se 1 (by rfl) ⟨6171020, by rfl⟩ : syracuseStep 8228027 = 12342041) B12342041
theorem B21941405 : Blo 2251435 21941405 := bstep (se 3 (by rfl) ⟨4114013, by rfl⟩ : syracuseStep 21941405 = 8228027) B8228027
theorem B14627603 : Blo 2251435 14627603 := bstep (se 1 (by rfl) ⟨10970702, by rfl⟩ : syracuseStep 14627603 = 21941405) B21941405
theorem B9751735 : Blo 2251435 9751735 := bstep (se 1 (by rfl) ⟨7313801, by rfl⟩ : syracuseStep 9751735 = 14627603) B14627603
theorem B52009253 : Blo 2251435 52009253 := bstep (se 4 (by rfl) ⟨4875867, by rfl⟩ : syracuseStep 52009253 = 9751735) B9751735
theorem B34672835 : Blo 2251435 34672835 := bstep (se 1 (by rfl) ⟨26004626, by rfl⟩ : syracuseStep 34672835 = 52009253) B52009253
theorem B23115223 : Blo 2251435 23115223 := bstep (se 1 (by rfl) ⟨17336417, by rfl⟩ : syracuseStep 23115223 = 34672835) B34672835
theorem B30820297 : Blo 2251435 30820297 := bstep (se 2 (by rfl) ⟨11557611, by rfl⟩ : syracuseStep 30820297 = 23115223) B23115223
theorem B41093729 : Blo 2251435 41093729 := bstep (se 2 (by rfl) ⟨15410148, by rfl⟩ : syracuseStep 41093729 = 30820297) B30820297
theorem B27395819 : Blo 2251435 27395819 := bstep (se 1 (by rfl) ⟨20546864, by rfl⟩ : syracuseStep 27395819 = 41093729) B41093729
theorem B18263879 : Blo 2251435 18263879 := bstep (se 1 (by rfl) ⟨13697909, by rfl⟩ : syracuseStep 18263879 = 27395819) B27395819
theorem B12175919 : Blo 2251435 12175919 := bstep (se 1 (by rfl) ⟨9131939, by rfl⟩ : syracuseStep 12175919 = 18263879) B18263879
theorem B8117279 : Blo 2251435 8117279 := bstep (se 1 (by rfl) ⟨6087959, by rfl⟩ : syracuseStep 8117279 = 12175919) B12175919
theorem B5411519 : Blo 2251435 5411519 := bstep (se 1 (by rfl) ⟨4058639, by rfl⟩ : syracuseStep 5411519 = 8117279) B8117279
theorem B3607679 : Blo 2251435 3607679 := bstep (se 1 (by rfl) ⟨2705759, by rfl⟩ : syracuseStep 3607679 = 5411519) B5411519
theorem B9620477 : Blo 2251435 9620477 := bstep (se 3 (by rfl) ⟨1803839, by rfl⟩ : syracuseStep 9620477 = 3607679) B3607679
theorem B6413651 : Blo 2251435 6413651 := bstep (se 1 (by rfl) ⟨4810238, by rfl⟩ : syracuseStep 6413651 = 9620477) B9620477
theorem B4275767 : Blo 2251435 4275767 := bstep (se 1 (by rfl) ⟨3206825, by rfl⟩ : syracuseStep 4275767 = 6413651) B6413651
theorem B11402045 : Blo 2251435 11402045 := bstep (se 3 (by rfl) ⟨2137883, by rfl⟩ : syracuseStep 11402045 = 4275767) B4275767
theorem B7601363 : Blo 2251435 7601363 := bstep (se 1 (by rfl) ⟨5701022, by rfl⟩ : syracuseStep 7601363 = 11402045) B11402045
theorem B5067575 : Blo 2251435 5067575 := bstep (se 1 (by rfl) ⟨3800681, by rfl⟩ : syracuseStep 5067575 = 7601363) B7601363
theorem B3378383 : Blo 2251435 3378383 := bstep (se 1 (by rfl) ⟨2533787, by rfl⟩ : syracuseStep 3378383 = 5067575) B5067575
theorem B2252255 : Blo 2251435 2252255 := bstep (se 1 (by rfl) ⟨1689191, by rfl⟩ : syracuseStep 2252255 = 3378383) B3378383
theorem B3378389 : Blo 2251435 3378389 := bbase (se 7 (by rfl) ⟨39590, by rfl⟩ : syracuseStep 3378389 = 79181) (by norm_num)
theorem B2252259 : Blo 2251435 2252259 := bstep (se 1 (by rfl) ⟨1689194, by rfl⟩ : syracuseStep 2252259 = 3378389) B3378389
theorem B3206837 : Blo 2251435 3206837 := bbase (se 5 (by rfl) ⟨150320, by rfl⟩ : syracuseStep 3206837 = 300641) (by norm_num)
theorem B8551565 : Blo 2251435 8551565 := bstep (se 3 (by rfl) ⟨1603418, by rfl⟩ : syracuseStep 8551565 = 3206837) B3206837
theorem B5701043 : Blo 2251435 5701043 := bstep (se 1 (by rfl) ⟨4275782, by rfl⟩ : syracuseStep 5701043 = 8551565) B8551565
theorem B3800695 : Blo 2251435 3800695 := bstep (se 1 (by rfl) ⟨2850521, by rfl⟩ : syracuseStep 3800695 = 5701043) B5701043
theorem B5067593 : Blo 2251435 5067593 := bstep (se 2 (by rfl) ⟨1900347, by rfl⟩ : syracuseStep 5067593 = 3800695) B3800695
theorem B3378395 : Blo 2251435 3378395 := bstep (se 1 (by rfl) ⟨2533796, by rfl⟩ : syracuseStep 3378395 = 5067593) B5067593
theorem B2252263 : Blo 2251435 2252263 := bstep (se 1 (by rfl) ⟨1689197, by rfl⟩ : syracuseStep 2252263 = 3378395) B3378395
theorem B2533801 : Blo 2251435 2533801 := bbase (se 2 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 2533801 = 1900351) (by norm_num)
theorem B3378401 : Blo 2251435 3378401 := bstep (se 2 (by rfl) ⟨1266900, by rfl⟩ : syracuseStep 3378401 = 2533801) B2533801
theorem B2252267 : Blo 2251435 2252267 := bstep (se 1 (by rfl) ⟨1689200, by rfl⟩ : syracuseStep 2252267 = 3378401) B3378401
theorem B5411557 : Blo 2251435 5411557 := bbase (se 4 (by rfl) ⟨507333, by rfl⟩ : syracuseStep 5411557 = 1014667) (by norm_num)
theorem B7215409 : Blo 2251435 7215409 := bstep (se 2 (by rfl) ⟨2705778, by rfl⟩ : syracuseStep 7215409 = 5411557) B5411557
theorem B9620545 : Blo 2251435 9620545 := bstep (se 2 (by rfl) ⟨3607704, by rfl⟩ : syracuseStep 9620545 = 7215409) B7215409
theorem B12827393 : Blo 2251435 12827393 := bstep (se 2 (by rfl) ⟨4810272, by rfl⟩ : syracuseStep 12827393 = 9620545) B9620545
theorem B8551595 : Blo 2251435 8551595 := bstep (se 1 (by rfl) ⟨6413696, by rfl⟩ : syracuseStep 8551595 = 12827393) B12827393
theorem B5701063 : Blo 2251435 5701063 := bstep (se 1 (by rfl) ⟨4275797, by rfl⟩ : syracuseStep 5701063 = 8551595) B8551595
theorem B7601417 : Blo 2251435 7601417 := bstep (se 2 (by rfl) ⟨2850531, by rfl⟩ : syracuseStep 7601417 = 5701063) B5701063
theorem B5067611 : Blo 2251435 5067611 := bstep (se 1 (by rfl) ⟨3800708, by rfl⟩ : syracuseStep 5067611 = 7601417) B7601417
theorem B3378407 : Blo 2251435 3378407 := bstep (se 1 (by rfl) ⟨2533805, by rfl⟩ : syracuseStep 3378407 = 5067611) B5067611
theorem B2252271 : Blo 2251435 2252271 := bstep (se 1 (by rfl) ⟨1689203, by rfl⟩ : syracuseStep 2252271 = 3378407) B3378407
theorem B3378413 : Blo 2251435 3378413 := bbase (se 3 (by rfl) ⟨633452, by rfl⟩ : syracuseStep 3378413 = 1266905) (by norm_num)
theorem B2252275 : Blo 2251435 2252275 := bstep (se 1 (by rfl) ⟨1689206, by rfl⟩ : syracuseStep 2252275 = 3378413) B3378413
theorem B5067629 : Blo 2251435 5067629 := bbase (se 3 (by rfl) ⟨950180, by rfl⟩ : syracuseStep 5067629 = 1900361) (by norm_num)
theorem B3378419 : Blo 2251435 3378419 := bstep (se 1 (by rfl) ⟨2533814, by rfl⟩ : syracuseStep 3378419 = 5067629) B5067629
theorem B2252279 : Blo 2251435 2252279 := bstep (se 1 (by rfl) ⟨1689209, by rfl⟩ : syracuseStep 2252279 = 3378419) B3378419
theorem B4275821 : Blo 2251435 4275821 := bbase (se 3 (by rfl) ⟨801716, by rfl⟩ : syracuseStep 4275821 = 1603433) (by norm_num)
theorem B2850547 : Blo 2251435 2850547 := bstep (se 1 (by rfl) ⟨2137910, by rfl⟩ : syracuseStep 2850547 = 4275821) B4275821
theorem B3800729 : Blo 2251435 3800729 := bstep (se 2 (by rfl) ⟨1425273, by rfl⟩ : syracuseStep 3800729 = 2850547) B2850547
theorem B2533819 : Blo 2251435 2533819 := bstep (se 1 (by rfl) ⟨1900364, by rfl⟩ : syracuseStep 2533819 = 3800729) B3800729
theorem B3378425 : Blo 2251435 3378425 := bstep (se 2 (by rfl) ⟨1266909, by rfl⟩ : syracuseStep 3378425 = 2533819) B2533819
theorem B2252283 : Blo 2251435 2252283 := bstep (se 1 (by rfl) ⟨1689212, by rfl⟩ : syracuseStep 2252283 = 3378425) B3378425
theorem B3424525 : Blo 2251435 3424525 := bbase (se 3 (by rfl) ⟨642098, by rfl⟩ : syracuseStep 3424525 = 1284197) (by norm_num)
theorem B18264133 : Blo 2251435 18264133 := bstep (se 4 (by rfl) ⟨1712262, by rfl⟩ : syracuseStep 18264133 = 3424525) B3424525
theorem B24352177 : Blo 2251435 24352177 := bstep (se 2 (by rfl) ⟨9132066, by rfl⟩ : syracuseStep 24352177 = 18264133) B18264133
theorem B32469569 : Blo 2251435 32469569 := bstep (se 2 (by rfl) ⟨12176088, by rfl⟩ : syracuseStep 32469569 = 24352177) B24352177
theorem B21646379 : Blo 2251435 21646379 := bstep (se 1 (by rfl) ⟨16234784, by rfl⟩ : syracuseStep 21646379 = 32469569) B32469569
theorem B57723677 : Blo 2251435 57723677 := bstep (se 3 (by rfl) ⟨10823189, by rfl⟩ : syracuseStep 57723677 = 21646379) B21646379
theorem B38482451 : Blo 2251435 38482451 := bstep (se 1 (by rfl) ⟨28861838, by rfl⟩ : syracuseStep 38482451 = 57723677) B57723677
theorem B25654967 : Blo 2251435 25654967 := bstep (se 1 (by rfl) ⟨19241225, by rfl⟩ : syracuseStep 25654967 = 38482451) B38482451
theorem B17103311 : Blo 2251435 17103311 := bstep (se 1 (by rfl) ⟨12827483, by rfl⟩ : syracuseStep 17103311 = 25654967) B25654967
theorem B11402207 : Blo 2251435 11402207 := bstep (se 1 (by rfl) ⟨8551655, by rfl⟩ : syracuseStep 11402207 = 17103311) B17103311
theorem B7601471 : Blo 2251435 7601471 := bstep (se 1 (by rfl) ⟨5701103, by rfl⟩ : syracuseStep 7601471 = 11402207) B11402207
theorem B5067647 : Blo 2251435 5067647 := bstep (se 1 (by rfl) ⟨3800735, by rfl⟩ : syracuseStep 5067647 = 7601471) B7601471
theorem B3378431 : Blo 2251435 3378431 := bstep (se 1 (by rfl) ⟨2533823, by rfl⟩ : syracuseStep 3378431 = 5067647) B5067647
theorem B2252287 : Blo 2251435 2252287 := bstep (se 1 (by rfl) ⟨1689215, by rfl⟩ : syracuseStep 2252287 = 3378431) B3378431
theorem B3378437 : Blo 2251435 3378437 := bbase (se 4 (by rfl) ⟨316728, by rfl⟩ : syracuseStep 3378437 = 633457) (by norm_num)
theorem B2252291 : Blo 2251435 2252291 := bstep (se 1 (by rfl) ⟨1689218, by rfl⟩ : syracuseStep 2252291 = 3378437) B3378437
theorem B3800749 : Blo 2251435 3800749 := bbase (se 3 (by rfl) ⟨712640, by rfl⟩ : syracuseStep 3800749 = 1425281) (by norm_num)
theorem B5067665 : Blo 2251435 5067665 := bstep (se 2 (by rfl) ⟨1900374, by rfl⟩ : syracuseStep 5067665 = 3800749) B3800749
theorem B3378443 : Blo 2251435 3378443 := bstep (se 1 (by rfl) ⟨2533832, by rfl⟩ : syracuseStep 3378443 = 5067665) B5067665
theorem B2252295 : Blo 2251435 2252295 := bstep (se 1 (by rfl) ⟨1689221, by rfl⟩ : syracuseStep 2252295 = 3378443) B3378443
theorem B2533837 : Blo 2251435 2533837 := bbase (se 3 (by rfl) ⟨475094, by rfl⟩ : syracuseStep 2533837 = 950189) (by norm_num)
theorem B3378449 : Blo 2251435 3378449 := bstep (se 2 (by rfl) ⟨1266918, by rfl⟩ : syracuseStep 3378449 = 2533837) B2533837
theorem B2252299 : Blo 2251435 2252299 := bstep (se 1 (by rfl) ⟨1689224, by rfl⟩ : syracuseStep 2252299 = 3378449) B3378449
theorem B7601525 : Blo 2251435 7601525 := bbase (se 5 (by rfl) ⟨356321, by rfl⟩ : syracuseStep 7601525 = 712643) (by norm_num)
theorem B5067683 : Blo 2251435 5067683 := bstep (se 1 (by rfl) ⟨3800762, by rfl⟩ : syracuseStep 5067683 = 7601525) B7601525
theorem B3378455 : Blo 2251435 3378455 := bstep (se 1 (by rfl) ⟨2533841, by rfl⟩ : syracuseStep 3378455 = 5067683) B5067683
theorem B2252303 : Blo 2251435 2252303 := bstep (se 1 (by rfl) ⟨1689227, by rfl⟩ : syracuseStep 2252303 = 3378455) B3378455
theorem B3378461 : Blo 2251435 3378461 := bbase (se 3 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 3378461 = 1266923) (by norm_num)
theorem B2252307 : Blo 2251435 2252307 := bstep (se 1 (by rfl) ⟨1689230, by rfl⟩ : syracuseStep 2252307 = 3378461) B3378461
theorem B5067701 : Blo 2251435 5067701 := bbase (se 5 (by rfl) ⟨237548, by rfl⟩ : syracuseStep 5067701 = 475097) (by norm_num)
theorem B3378467 : Blo 2251435 3378467 := bstep (se 1 (by rfl) ⟨2533850, by rfl⟩ : syracuseStep 3378467 = 5067701) B5067701
theorem B2252311 : Blo 2251435 2252311 := bstep (se 1 (by rfl) ⟨1689233, by rfl⟩ : syracuseStep 2252311 = 3378467) B3378467
theorem B7810405 : Blo 2251435 7810405 := bbase (se 4 (by rfl) ⟨732225, by rfl⟩ : syracuseStep 7810405 = 1464451) (by norm_num)
theorem B41655493 : Blo 2251435 41655493 := bstep (se 4 (by rfl) ⟨3905202, by rfl⟩ : syracuseStep 41655493 = 7810405) B7810405
theorem B55540657 : Blo 2251435 55540657 := bstep (se 2 (by rfl) ⟨20827746, by rfl⟩ : syracuseStep 55540657 = 41655493) B41655493
theorem B74054209 : Blo 2251435 74054209 := bstep (se 2 (by rfl) ⟨27770328, by rfl⟩ : syracuseStep 74054209 = 55540657) B55540657
theorem B98738945 : Blo 2251435 98738945 := bstep (se 2 (by rfl) ⟨37027104, by rfl⟩ : syracuseStep 98738945 = 74054209) B74054209
theorem B65825963 : Blo 2251435 65825963 := bstep (se 1 (by rfl) ⟨49369472, by rfl⟩ : syracuseStep 65825963 = 98738945) B98738945
theorem B43883975 : Blo 2251435 43883975 := bstep (se 1 (by rfl) ⟨32912981, by rfl⟩ : syracuseStep 43883975 = 65825963) B65825963
theorem B117023933 : Blo 2251435 117023933 := bstep (se 3 (by rfl) ⟨21941987, by rfl⟩ : syracuseStep 117023933 = 43883975) B43883975
theorem B78015955 : Blo 2251435 78015955 := bstep (se 1 (by rfl) ⟨58511966, by rfl⟩ : syracuseStep 78015955 = 117023933) B117023933
theorem B104021273 : Blo 2251435 104021273 := bstep (se 2 (by rfl) ⟨39007977, by rfl⟩ : syracuseStep 104021273 = 78015955) B78015955
theorem B69347515 : Blo 2251435 69347515 := bstep (se 1 (by rfl) ⟨52010636, by rfl⟩ : syracuseStep 69347515 = 104021273) B104021273
theorem B92463353 : Blo 2251435 92463353 := bstep (se 2 (by rfl) ⟨34673757, by rfl⟩ : syracuseStep 92463353 = 69347515) B69347515
theorem B61642235 : Blo 2251435 61642235 := bstep (se 1 (by rfl) ⟨46231676, by rfl⟩ : syracuseStep 61642235 = 92463353) B92463353
theorem B41094823 : Blo 2251435 41094823 := bstep (se 1 (by rfl) ⟨30821117, by rfl⟩ : syracuseStep 41094823 = 61642235) B61642235
theorem B54793097 : Blo 2251435 54793097 := bstep (se 2 (by rfl) ⟨20547411, by rfl⟩ : syracuseStep 54793097 = 41094823) B41094823
theorem B36528731 : Blo 2251435 36528731 := bstep (se 1 (by rfl) ⟨27396548, by rfl⟩ : syracuseStep 36528731 = 54793097) B54793097
theorem B24352487 : Blo 2251435 24352487 := bstep (se 1 (by rfl) ⟨18264365, by rfl⟩ : syracuseStep 24352487 = 36528731) B36528731
theorem B16234991 : Blo 2251435 16234991 := bstep (se 1 (by rfl) ⟨12176243, by rfl⟩ : syracuseStep 16234991 = 24352487) B24352487
theorem B10823327 : Blo 2251435 10823327 := bstep (se 1 (by rfl) ⟨8117495, by rfl⟩ : syracuseStep 10823327 = 16234991) B16234991
theorem B7215551 : Blo 2251435 7215551 := bstep (se 1 (by rfl) ⟨5411663, by rfl⟩ : syracuseStep 7215551 = 10823327) B10823327
theorem B4810367 : Blo 2251435 4810367 := bstep (se 1 (by rfl) ⟨3607775, by rfl⟩ : syracuseStep 4810367 = 7215551) B7215551
theorem B12827645 : Blo 2251435 12827645 := bstep (se 3 (by rfl) ⟨2405183, by rfl⟩ : syracuseStep 12827645 = 4810367) B4810367
theorem B8551763 : Blo 2251435 8551763 := bstep (se 1 (by rfl) ⟨6413822, by rfl⟩ : syracuseStep 8551763 = 12827645) B12827645
theorem B5701175 : Blo 2251435 5701175 := bstep (se 1 (by rfl) ⟨4275881, by rfl⟩ : syracuseStep 5701175 = 8551763) B8551763
theorem B3800783 : Blo 2251435 3800783 := bstep (se 1 (by rfl) ⟨2850587, by rfl⟩ : syracuseStep 3800783 = 5701175) B5701175
theorem B2533855 : Blo 2251435 2533855 := bstep (se 1 (by rfl) ⟨1900391, by rfl⟩ : syracuseStep 2533855 = 3800783) B3800783
theorem B3378473 : Blo 2251435 3378473 := bstep (se 2 (by rfl) ⟨1266927, by rfl⟩ : syracuseStep 3378473 = 2533855) B2533855
theorem B2252315 : Blo 2251435 2252315 := bstep (se 1 (by rfl) ⟨1689236, by rfl⟩ : syracuseStep 2252315 = 3378473) B3378473
theorem B8117509 : Blo 2251435 8117509 := bbase (se 4 (by rfl) ⟨761016, by rfl⟩ : syracuseStep 8117509 = 1522033) (by norm_num)
theorem B10823345 : Blo 2251435 10823345 := bstep (se 2 (by rfl) ⟨4058754, by rfl⟩ : syracuseStep 10823345 = 8117509) B8117509
theorem B7215563 : Blo 2251435 7215563 := bstep (se 1 (by rfl) ⟨5411672, by rfl⟩ : syracuseStep 7215563 = 10823345) B10823345
theorem B4810375 : Blo 2251435 4810375 := bstep (se 1 (by rfl) ⟨3607781, by rfl⟩ : syracuseStep 4810375 = 7215563) B7215563
theorem B6413833 : Blo 2251435 6413833 := bstep (se 2 (by rfl) ⟨2405187, by rfl⟩ : syracuseStep 6413833 = 4810375) B4810375
theorem B8551777 : Blo 2251435 8551777 := bstep (se 2 (by rfl) ⟨3206916, by rfl⟩ : syracuseStep 8551777 = 6413833) B6413833
theorem B11402369 : Blo 2251435 11402369 := bstep (se 2 (by rfl) ⟨4275888, by rfl⟩ : syracuseStep 11402369 = 8551777) B8551777
theorem B7601579 : Blo 2251435 7601579 := bstep (se 1 (by rfl) ⟨5701184, by rfl⟩ : syracuseStep 7601579 = 11402369) B11402369
theorem B5067719 : Blo 2251435 5067719 := bstep (se 1 (by rfl) ⟨3800789, by rfl⟩ : syracuseStep 5067719 = 7601579) B7601579
theorem B3378479 : Blo 2251435 3378479 := bstep (se 1 (by rfl) ⟨2533859, by rfl⟩ : syracuseStep 3378479 = 5067719) B5067719
theorem B2252319 : Blo 2251435 2252319 := bstep (se 1 (by rfl) ⟨1689239, by rfl⟩ : syracuseStep 2252319 = 3378479) B3378479
theorem B3378485 : Blo 2251435 3378485 := bbase (se 5 (by rfl) ⟨158366, by rfl⟩ : syracuseStep 3378485 = 316733) (by norm_num)
theorem B2252323 : Blo 2251435 2252323 := bstep (se 1 (by rfl) ⟨1689242, by rfl⟩ : syracuseStep 2252323 = 3378485) B3378485
theorem B5701205 : Blo 2251435 5701205 := bbase (se 8 (by rfl) ⟨33405, by rfl⟩ : syracuseStep 5701205 = 66811) (by norm_num)
theorem B3800803 : Blo 2251435 3800803 := bstep (se 1 (by rfl) ⟨2850602, by rfl⟩ : syracuseStep 3800803 = 5701205) B5701205
theorem B5067737 : Blo 2251435 5067737 := bstep (se 2 (by rfl) ⟨1900401, by rfl⟩ : syracuseStep 5067737 = 3800803) B3800803
theorem B3378491 : Blo 2251435 3378491 := bstep (se 1 (by rfl) ⟨2533868, by rfl⟩ : syracuseStep 3378491 = 5067737) B5067737
theorem B2252327 : Blo 2251435 2252327 := bstep (se 1 (by rfl) ⟨1689245, by rfl⟩ : syracuseStep 2252327 = 3378491) B3378491
theorem B2533873 : Blo 2251435 2533873 := bbase (se 2 (by rfl) ⟨950202, by rfl⟩ : syracuseStep 2533873 = 1900405) (by norm_num)
theorem B3378497 : Blo 2251435 3378497 := bstep (se 2 (by rfl) ⟨1266936, by rfl⟩ : syracuseStep 3378497 = 2533873) B2533873
theorem B2252331 : Blo 2251435 2252331 := bstep (se 1 (by rfl) ⟨1689248, by rfl⟩ : syracuseStep 2252331 = 3378497) B3378497
theorem B2742773 : Blo 2251435 2742773 := bbase (se 5 (by rfl) ⟨128567, by rfl⟩ : syracuseStep 2742773 = 257135) (by norm_num)
theorem B7314061 : Blo 2251435 7314061 := bstep (se 3 (by rfl) ⟨1371386, by rfl⟩ : syracuseStep 7314061 = 2742773) B2742773
theorem B9752081 : Blo 2251435 9752081 := bstep (se 2 (by rfl) ⟨3657030, by rfl⟩ : syracuseStep 9752081 = 7314061) B7314061
theorem B26005549 : Blo 2251435 26005549 := bstep (se 3 (by rfl) ⟨4876040, by rfl⟩ : syracuseStep 26005549 = 9752081) B9752081
theorem B34674065 : Blo 2251435 34674065 := bstep (se 2 (by rfl) ⟨13002774, by rfl⟩ : syracuseStep 34674065 = 26005549) B26005549
theorem B23116043 : Blo 2251435 23116043 := bstep (se 1 (by rfl) ⟨17337032, by rfl⟩ : syracuseStep 23116043 = 34674065) B34674065
theorem B61642781 : Blo 2251435 61642781 := bstep (se 3 (by rfl) ⟨11558021, by rfl⟩ : syracuseStep 61642781 = 23116043) B23116043
theorem B41095187 : Blo 2251435 41095187 := bstep (se 1 (by rfl) ⟨30821390, by rfl⟩ : syracuseStep 41095187 = 61642781) B61642781
theorem B27396791 : Blo 2251435 27396791 := bstep (se 1 (by rfl) ⟨20547593, by rfl⟩ : syracuseStep 27396791 = 41095187) B41095187
theorem B18264527 : Blo 2251435 18264527 := bstep (se 1 (by rfl) ⟨13698395, by rfl⟩ : syracuseStep 18264527 = 27396791) B27396791
theorem B12176351 : Blo 2251435 12176351 := bstep (se 1 (by rfl) ⟨9132263, by rfl⟩ : syracuseStep 12176351 = 18264527) B18264527
theorem B8117567 : Blo 2251435 8117567 := bstep (se 1 (by rfl) ⟨6088175, by rfl⟩ : syracuseStep 8117567 = 12176351) B12176351
theorem B5411711 : Blo 2251435 5411711 := bstep (se 1 (by rfl) ⟨4058783, by rfl⟩ : syracuseStep 5411711 = 8117567) B8117567
theorem B14431229 : Blo 2251435 14431229 := bstep (se 3 (by rfl) ⟨2705855, by rfl⟩ : syracuseStep 14431229 = 5411711) B5411711
theorem B9620819 : Blo 2251435 9620819 := bstep (se 1 (by rfl) ⟨7215614, by rfl⟩ : syracuseStep 9620819 = 14431229) B14431229
theorem B6413879 : Blo 2251435 6413879 := bstep (se 1 (by rfl) ⟨4810409, by rfl⟩ : syracuseStep 6413879 = 9620819) B9620819
theorem B4275919 : Blo 2251435 4275919 := bstep (se 1 (by rfl) ⟨3206939, by rfl⟩ : syracuseStep 4275919 = 6413879) B6413879
theorem B5701225 : Blo 2251435 5701225 := bstep (se 2 (by rfl) ⟨2137959, by rfl⟩ : syracuseStep 5701225 = 4275919) B4275919
theorem B7601633 : Blo 2251435 7601633 := bstep (se 2 (by rfl) ⟨2850612, by rfl⟩ : syracuseStep 7601633 = 5701225) B5701225
theorem B5067755 : Blo 2251435 5067755 := bstep (se 1 (by rfl) ⟨3800816, by rfl⟩ : syracuseStep 5067755 = 7601633) B7601633
theorem B3378503 : Blo 2251435 3378503 := bstep (se 1 (by rfl) ⟨2533877, by rfl⟩ : syracuseStep 3378503 = 5067755) B5067755
theorem B2252335 : Blo 2251435 2252335 := bstep (se 1 (by rfl) ⟨1689251, by rfl⟩ : syracuseStep 2252335 = 3378503) B3378503
theorem B3378509 : Blo 2251435 3378509 := bbase (se 3 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 3378509 = 1266941) (by norm_num)
theorem B2252339 : Blo 2251435 2252339 := bstep (se 1 (by rfl) ⟨1689254, by rfl⟩ : syracuseStep 2252339 = 3378509) B3378509
theorem B5067773 : Blo 2251435 5067773 := bbase (se 3 (by rfl) ⟨950207, by rfl⟩ : syracuseStep 5067773 = 1900415) (by norm_num)
theorem B3378515 : Blo 2251435 3378515 := bstep (se 1 (by rfl) ⟨2533886, by rfl⟩ : syracuseStep 3378515 = 5067773) B5067773
theorem B2252343 : Blo 2251435 2252343 := bstep (se 1 (by rfl) ⟨1689257, by rfl⟩ : syracuseStep 2252343 = 3378515) B3378515
theorem B3800837 : Blo 2251435 3800837 := bbase (se 4 (by rfl) ⟨356328, by rfl⟩ : syracuseStep 3800837 = 712657) (by norm_num)
theorem B2533891 : Blo 2251435 2533891 := bstep (se 1 (by rfl) ⟨1900418, by rfl⟩ : syracuseStep 2533891 = 3800837) B3800837
theorem B3378521 : Blo 2251435 3378521 := bstep (se 2 (by rfl) ⟨1266945, by rfl⟩ : syracuseStep 3378521 = 2533891) B2533891
theorem B2252347 : Blo 2251435 2252347 := bstep (se 1 (by rfl) ⟨1689260, by rfl⟩ : syracuseStep 2252347 = 3378521) B3378521
theorem B17103797 : Blo 2251435 17103797 := bbase (se 5 (by rfl) ⟨801740, by rfl⟩ : syracuseStep 17103797 = 1603481) (by norm_num)
theorem B11402531 : Blo 2251435 11402531 := bstep (se 1 (by rfl) ⟨8551898, by rfl⟩ : syracuseStep 11402531 = 17103797) B17103797
theorem B7601687 : Blo 2251435 7601687 := bstep (se 1 (by rfl) ⟨5701265, by rfl⟩ : syracuseStep 7601687 = 11402531) B11402531
theorem B5067791 : Blo 2251435 5067791 := bstep (se 1 (by rfl) ⟨3800843, by rfl⟩ : syracuseStep 5067791 = 7601687) B7601687
theorem B3378527 : Blo 2251435 3378527 := bstep (se 1 (by rfl) ⟨2533895, by rfl⟩ : syracuseStep 3378527 = 5067791) B5067791
theorem B2252351 : Blo 2251435 2252351 := bstep (se 1 (by rfl) ⟨1689263, by rfl⟩ : syracuseStep 2252351 = 3378527) B3378527
theorem B3378533 : Blo 2251435 3378533 := bbase (se 4 (by rfl) ⟨316737, by rfl⟩ : syracuseStep 3378533 = 633475) (by norm_num)
theorem B2252355 : Blo 2251435 2252355 := bstep (se 1 (by rfl) ⟨1689266, by rfl⟩ : syracuseStep 2252355 = 3378533) B3378533
theorem B4275965 : Blo 2251435 4275965 := bbase (se 3 (by rfl) ⟨801743, by rfl⟩ : syracuseStep 4275965 = 1603487) (by norm_num)
theorem B2850643 : Blo 2251435 2850643 := bstep (se 1 (by rfl) ⟨2137982, by rfl⟩ : syracuseStep 2850643 = 4275965) B4275965
theorem B3800857 : Blo 2251435 3800857 := bstep (se 2 (by rfl) ⟨1425321, by rfl⟩ : syracuseStep 3800857 = 2850643) B2850643
theorem B5067809 : Blo 2251435 5067809 := bstep (se 2 (by rfl) ⟨1900428, by rfl⟩ : syracuseStep 5067809 = 3800857) B3800857
theorem B3378539 : Blo 2251435 3378539 := bstep (se 1 (by rfl) ⟨2533904, by rfl⟩ : syracuseStep 3378539 = 5067809) B5067809
theorem B2252359 : Blo 2251435 2252359 := bstep (se 1 (by rfl) ⟨1689269, by rfl⟩ : syracuseStep 2252359 = 3378539) B3378539
theorem B2533909 : Blo 2251435 2533909 := bbase (se 6 (by rfl) ⟨59388, by rfl⟩ : syracuseStep 2533909 = 118777) (by norm_num)
theorem B3378545 : Blo 2251435 3378545 := bstep (se 2 (by rfl) ⟨1266954, by rfl⟩ : syracuseStep 3378545 = 2533909) B2533909
theorem B2252363 : Blo 2251435 2252363 := bstep (se 1 (by rfl) ⟨1689272, by rfl⟩ : syracuseStep 2252363 = 3378545) B3378545
theorem B2850653 : Blo 2251435 2850653 := bbase (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) (by norm_num)
theorem B7601741 : Blo 2251435 7601741 := bstep (se 3 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 7601741 = 2850653) B2850653
theorem B5067827 : Blo 2251435 5067827 := bstep (se 1 (by rfl) ⟨3800870, by rfl⟩ : syracuseStep 5067827 = 7601741) B7601741
theorem B3378551 : Blo 2251435 3378551 := bstep (se 1 (by rfl) ⟨2533913, by rfl⟩ : syracuseStep 3378551 = 5067827) B5067827
theorem B2252367 : Blo 2251435 2252367 := bstep (se 1 (by rfl) ⟨1689275, by rfl⟩ : syracuseStep 2252367 = 3378551) B3378551
theorem B3378557 : Blo 2251435 3378557 := bbase (se 3 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 3378557 = 1266959) (by norm_num)
theorem B2252371 : Blo 2251435 2252371 := bstep (se 1 (by rfl) ⟨1689278, by rfl⟩ : syracuseStep 2252371 = 3378557) B3378557
theorem B5067845 : Blo 2251435 5067845 := bbase (se 4 (by rfl) ⟨475110, by rfl⟩ : syracuseStep 5067845 = 950221) (by norm_num)
theorem B3378563 : Blo 2251435 3378563 := bstep (se 1 (by rfl) ⟨2533922, by rfl⟩ : syracuseStep 3378563 = 5067845) B5067845
theorem B2252375 : Blo 2251435 2252375 := bstep (se 1 (by rfl) ⟨1689281, by rfl⟩ : syracuseStep 2252375 = 3378563) B3378563
theorem B6414005 : Blo 2251435 6414005 := bbase (se 5 (by rfl) ⟨300656, by rfl⟩ : syracuseStep 6414005 = 601313) (by norm_num)
theorem B4276003 : Blo 2251435 4276003 := bstep (se 1 (by rfl) ⟨3207002, by rfl⟩ : syracuseStep 4276003 = 6414005) B6414005
theorem B5701337 : Blo 2251435 5701337 := bstep (se 2 (by rfl) ⟨2138001, by rfl⟩ : syracuseStep 5701337 = 4276003) B4276003
theorem B3800891 : Blo 2251435 3800891 := bstep (se 1 (by rfl) ⟨2850668, by rfl⟩ : syracuseStep 3800891 = 5701337) B5701337
theorem B2533927 : Blo 2251435 2533927 := bstep (se 1 (by rfl) ⟨1900445, by rfl⟩ : syracuseStep 2533927 = 3800891) B3800891
theorem B3378569 : Blo 2251435 3378569 := bstep (se 2 (by rfl) ⟨1266963, by rfl⟩ : syracuseStep 3378569 = 2533927) B2533927
theorem B2252379 : Blo 2251435 2252379 := bstep (se 1 (by rfl) ⟨1689284, by rfl⟩ : syracuseStep 2252379 = 3378569) B3378569
theorem B11402693 : Blo 2251435 11402693 := bbase (se 4 (by rfl) ⟨1069002, by rfl⟩ : syracuseStep 11402693 = 2138005) (by norm_num)
theorem B7601795 : Blo 2251435 7601795 := bstep (se 1 (by rfl) ⟨5701346, by rfl⟩ : syracuseStep 7601795 = 11402693) B11402693
theorem B5067863 : Blo 2251435 5067863 := bstep (se 1 (by rfl) ⟨3800897, by rfl⟩ : syracuseStep 5067863 = 7601795) B7601795
theorem B3378575 : Blo 2251435 3378575 := bstep (se 1 (by rfl) ⟨2533931, by rfl⟩ : syracuseStep 3378575 = 5067863) B5067863
theorem B2252383 : Blo 2251435 2252383 := bstep (se 1 (by rfl) ⟨1689287, by rfl⟩ : syracuseStep 2252383 = 3378575) B3378575
theorem B3378581 : Blo 2251435 3378581 := bbase (se 6 (by rfl) ⟨79185, by rfl⟩ : syracuseStep 3378581 = 158371) (by norm_num)
theorem B2252387 : Blo 2251435 2252387 := bstep (se 1 (by rfl) ⟨1689290, by rfl⟩ : syracuseStep 2252387 = 3378581) B3378581
theorem B4058885 : Blo 2251435 4058885 := bbase (se 4 (by rfl) ⟨380520, by rfl⟩ : syracuseStep 4058885 = 761041) (by norm_num)
theorem B2705923 : Blo 2251435 2705923 := bstep (se 1 (by rfl) ⟨2029442, by rfl⟩ : syracuseStep 2705923 = 4058885) B4058885
theorem B3607897 : Blo 2251435 3607897 := bstep (se 2 (by rfl) ⟨1352961, by rfl⟩ : syracuseStep 3607897 = 2705923) B2705923
theorem B4810529 : Blo 2251435 4810529 := bstep (se 2 (by rfl) ⟨1803948, by rfl⟩ : syracuseStep 4810529 = 3607897) B3607897
theorem B12828077 : Blo 2251435 12828077 := bstep (se 3 (by rfl) ⟨2405264, by rfl⟩ : syracuseStep 12828077 = 4810529) B4810529
theorem B8552051 : Blo 2251435 8552051 := bstep (se 1 (by rfl) ⟨6414038, by rfl⟩ : syracuseStep 8552051 = 12828077) B12828077
theorem B5701367 : Blo 2251435 5701367 := bstep (se 1 (by rfl) ⟨4276025, by rfl⟩ : syracuseStep 5701367 = 8552051) B8552051
theorem B3800911 : Blo 2251435 3800911 := bstep (se 1 (by rfl) ⟨2850683, by rfl⟩ : syracuseStep 3800911 = 5701367) B5701367
theorem B5067881 : Blo 2251435 5067881 := bstep (se 2 (by rfl) ⟨1900455, by rfl⟩ : syracuseStep 5067881 = 3800911) B3800911
theorem B3378587 : Blo 2251435 3378587 := bstep (se 1 (by rfl) ⟨2533940, by rfl⟩ : syracuseStep 3378587 = 5067881) B5067881
theorem B2252391 : Blo 2251435 2252391 := bstep (se 1 (by rfl) ⟨1689293, by rfl⟩ : syracuseStep 2252391 = 3378587) B3378587
theorem B2533945 : Blo 2251435 2533945 := bbase (se 2 (by rfl) ⟨950229, by rfl⟩ : syracuseStep 2533945 = 1900459) (by norm_num)
theorem B3378593 : Blo 2251435 3378593 := bstep (se 2 (by rfl) ⟨1266972, by rfl⟩ : syracuseStep 3378593 = 2533945) B2533945
theorem B2252395 : Blo 2251435 2252395 := bstep (se 1 (by rfl) ⟨1689296, by rfl⟩ : syracuseStep 2252395 = 3378593) B3378593
theorem B2405273 : Blo 2251435 2405273 := bbase (se 2 (by rfl) ⟨901977, by rfl⟩ : syracuseStep 2405273 = 1803955) (by norm_num)
theorem B6414061 : Blo 2251435 6414061 := bstep (se 3 (by rfl) ⟨1202636, by rfl⟩ : syracuseStep 6414061 = 2405273) B2405273
theorem B8552081 : Blo 2251435 8552081 := bstep (se 2 (by rfl) ⟨3207030, by rfl⟩ : syracuseStep 8552081 = 6414061) B6414061
theorem B5701387 : Blo 2251435 5701387 := bstep (se 1 (by rfl) ⟨4276040, by rfl⟩ : syracuseStep 5701387 = 8552081) B8552081
theorem B7601849 : Blo 2251435 7601849 := bstep (se 2 (by rfl) ⟨2850693, by rfl⟩ : syracuseStep 7601849 = 5701387) B5701387
theorem B5067899 : Blo 2251435 5067899 := bstep (se 1 (by rfl) ⟨3800924, by rfl⟩ : syracuseStep 5067899 = 7601849) B7601849
theorem B3378599 : Blo 2251435 3378599 := bstep (se 1 (by rfl) ⟨2533949, by rfl⟩ : syracuseStep 3378599 = 5067899) B5067899
theorem B2252399 : Blo 2251435 2252399 := bstep (se 1 (by rfl) ⟨1689299, by rfl⟩ : syracuseStep 2252399 = 3378599) B3378599
theorem B3378605 : Blo 2251435 3378605 := bbase (se 3 (by rfl) ⟨633488, by rfl⟩ : syracuseStep 3378605 = 1266977) (by norm_num)
theorem B2252403 : Blo 2251435 2252403 := bstep (se 1 (by rfl) ⟨1689302, by rfl⟩ : syracuseStep 2252403 = 3378605) B3378605
theorem B5067917 : Blo 2251435 5067917 := bbase (se 3 (by rfl) ⟨950234, by rfl⟩ : syracuseStep 5067917 = 1900469) (by norm_num)
theorem B3378611 : Blo 2251435 3378611 := bstep (se 1 (by rfl) ⟨2533958, by rfl⟩ : syracuseStep 3378611 = 5067917) B5067917
theorem B2252407 : Blo 2251435 2252407 := bstep (se 1 (by rfl) ⟨1689305, by rfl⟩ : syracuseStep 2252407 = 3378611) B3378611
theorem B2850709 : Blo 2251435 2850709 := bbase (se 6 (by rfl) ⟨66813, by rfl⟩ : syracuseStep 2850709 = 133627) (by norm_num)
theorem B3800945 : Blo 2251435 3800945 := bstep (se 2 (by rfl) ⟨1425354, by rfl⟩ : syracuseStep 3800945 = 2850709) B2850709
theorem B2533963 : Blo 2251435 2533963 := bstep (se 1 (by rfl) ⟨1900472, by rfl⟩ : syracuseStep 2533963 = 3800945) B3800945
theorem B3378617 : Blo 2251435 3378617 := bstep (se 2 (by rfl) ⟨1266981, by rfl⟩ : syracuseStep 3378617 = 2533963) B2533963
theorem B2252411 : Blo 2251435 2252411 := bstep (se 1 (by rfl) ⟨1689308, by rfl⟩ : syracuseStep 2252411 = 3378617) B3378617
theorem B3471445 : Blo 2251435 3471445 := bbase (se 8 (by rfl) ⟨20340, by rfl⟩ : syracuseStep 3471445 = 40681) (by norm_num)
theorem B4628593 : Blo 2251435 4628593 := bstep (se 2 (by rfl) ⟨1735722, by rfl⟩ : syracuseStep 4628593 = 3471445) B3471445
theorem B24685829 : Blo 2251435 24685829 := bstep (se 4 (by rfl) ⟨2314296, by rfl⟩ : syracuseStep 24685829 = 4628593) B4628593
theorem B16457219 : Blo 2251435 16457219 := bstep (se 1 (by rfl) ⟨12342914, by rfl⟩ : syracuseStep 16457219 = 24685829) B24685829
theorem B10971479 : Blo 2251435 10971479 := bstep (se 1 (by rfl) ⟨8228609, by rfl⟩ : syracuseStep 10971479 = 16457219) B16457219
theorem B7314319 : Blo 2251435 7314319 := bstep (se 1 (by rfl) ⟨5485739, by rfl⟩ : syracuseStep 7314319 = 10971479) B10971479
theorem B39009701 : Blo 2251435 39009701 := bstep (se 4 (by rfl) ⟨3657159, by rfl⟩ : syracuseStep 39009701 = 7314319) B7314319
theorem B26006467 : Blo 2251435 26006467 := bstep (se 1 (by rfl) ⟨19504850, by rfl⟩ : syracuseStep 26006467 = 39009701) B39009701
theorem B34675289 : Blo 2251435 34675289 := bstep (se 2 (by rfl) ⟨13003233, by rfl⟩ : syracuseStep 34675289 = 26006467) B26006467
theorem B23116859 : Blo 2251435 23116859 := bstep (se 1 (by rfl) ⟨17337644, by rfl⟩ : syracuseStep 23116859 = 34675289) B34675289
theorem B15411239 : Blo 2251435 15411239 := bstep (se 1 (by rfl) ⟨11558429, by rfl⟩ : syracuseStep 15411239 = 23116859) B23116859
theorem B10274159 : Blo 2251435 10274159 := bstep (se 1 (by rfl) ⟨7705619, by rfl⟩ : syracuseStep 10274159 = 15411239) B15411239
theorem B27397757 : Blo 2251435 27397757 := bstep (se 3 (by rfl) ⟨5137079, by rfl⟩ : syracuseStep 27397757 = 10274159) B10274159
theorem B18265171 : Blo 2251435 18265171 := bstep (se 1 (by rfl) ⟨13698878, by rfl⟩ : syracuseStep 18265171 = 27397757) B27397757
theorem B24353561 : Blo 2251435 24353561 := bstep (se 2 (by rfl) ⟨9132585, by rfl⟩ : syracuseStep 24353561 = 18265171) B18265171
theorem B64942829 : Blo 2251435 64942829 := bstep (se 3 (by rfl) ⟨12176780, by rfl⟩ : syracuseStep 64942829 = 24353561) B24353561
theorem B43295219 : Blo 2251435 43295219 := bstep (se 1 (by rfl) ⟨32471414, by rfl⟩ : syracuseStep 43295219 = 64942829) B64942829
theorem B28863479 : Blo 2251435 28863479 := bstep (se 1 (by rfl) ⟨21647609, by rfl⟩ : syracuseStep 28863479 = 43295219) B43295219
theorem B19242319 : Blo 2251435 19242319 := bstep (se 1 (by rfl) ⟨14431739, by rfl⟩ : syracuseStep 19242319 = 28863479) B28863479
theorem B25656425 : Blo 2251435 25656425 := bstep (se 2 (by rfl) ⟨9621159, by rfl⟩ : syracuseStep 25656425 = 19242319) B19242319
theorem B17104283 : Blo 2251435 17104283 := bstep (se 1 (by rfl) ⟨12828212, by rfl⟩ : syracuseStep 17104283 = 25656425) B25656425
theorem B11402855 : Blo 2251435 11402855 := bstep (se 1 (by rfl) ⟨8552141, by rfl⟩ : syracuseStep 11402855 = 17104283) B17104283
theorem B7601903 : Blo 2251435 7601903 := bstep (se 1 (by rfl) ⟨5701427, by rfl⟩ : syracuseStep 7601903 = 11402855) B11402855
theorem B5067935 : Blo 2251435 5067935 := bstep (se 1 (by rfl) ⟨3800951, by rfl⟩ : syracuseStep 5067935 = 7601903) B7601903
theorem B3378623 : Blo 2251435 3378623 := bstep (se 1 (by rfl) ⟨2533967, by rfl⟩ : syracuseStep 3378623 = 5067935) B5067935
theorem B2252415 : Blo 2251435 2252415 := bstep (se 1 (by rfl) ⟨1689311, by rfl⟩ : syracuseStep 2252415 = 3378623) B3378623
theorem B3378629 : Blo 2251435 3378629 := bbase (se 4 (by rfl) ⟨316746, by rfl⟩ : syracuseStep 3378629 = 633493) (by norm_num)
theorem B2252419 : Blo 2251435 2252419 := bstep (se 1 (by rfl) ⟨1689314, by rfl⟩ : syracuseStep 2252419 = 3378629) B3378629
theorem B3800965 : Blo 2251435 3800965 := bbase (se 4 (by rfl) ⟨356340, by rfl⟩ : syracuseStep 3800965 = 712681) (by norm_num)
theorem B5067953 : Blo 2251435 5067953 := bstep (se 2 (by rfl) ⟨1900482, by rfl⟩ : syracuseStep 5067953 = 3800965) B3800965
theorem B3378635 : Blo 2251435 3378635 := bstep (se 1 (by rfl) ⟨2533976, by rfl⟩ : syracuseStep 3378635 = 5067953) B5067953
theorem B2252423 : Blo 2251435 2252423 := bstep (se 1 (by rfl) ⟨1689317, by rfl⟩ : syracuseStep 2252423 = 3378635) B3378635
theorem B2533981 : Blo 2251435 2533981 := bbase (se 3 (by rfl) ⟨475121, by rfl⟩ : syracuseStep 2533981 = 950243) (by norm_num)
theorem B3378641 : Blo 2251435 3378641 := bstep (se 2 (by rfl) ⟨1266990, by rfl⟩ : syracuseStep 3378641 = 2533981) B2533981
theorem B2252427 : Blo 2251435 2252427 := bstep (se 1 (by rfl) ⟨1689320, by rfl⟩ : syracuseStep 2252427 = 3378641) B3378641
theorem B7601957 : Blo 2251435 7601957 := bbase (se 4 (by rfl) ⟨712683, by rfl⟩ : syracuseStep 7601957 = 1425367) (by norm_num)
theorem B5067971 : Blo 2251435 5067971 := bstep (se 1 (by rfl) ⟨3800978, by rfl⟩ : syracuseStep 5067971 = 7601957) B7601957
theorem B3378647 : Blo 2251435 3378647 := bstep (se 1 (by rfl) ⟨2533985, by rfl⟩ : syracuseStep 3378647 = 5067971) B5067971
theorem B2252431 : Blo 2251435 2252431 := bstep (se 1 (by rfl) ⟨1689323, by rfl⟩ : syracuseStep 2252431 = 3378647) B3378647
theorem B3378653 : Blo 2251435 3378653 := bbase (se 3 (by rfl) ⟨633497, by rfl⟩ : syracuseStep 3378653 = 1266995) (by norm_num)
theorem B2252435 : Blo 2251435 2252435 := bstep (se 1 (by rfl) ⟨1689326, by rfl⟩ : syracuseStep 2252435 = 3378653) B3378653
theorem B5067989 : Blo 2251435 5067989 := bbase (se 7 (by rfl) ⟨59390, by rfl⟩ : syracuseStep 5067989 = 118781) (by norm_num)
theorem B3378659 : Blo 2251435 3378659 := bstep (se 1 (by rfl) ⟨2533994, by rfl⟩ : syracuseStep 3378659 = 5067989) B5067989
theorem B2252439 : Blo 2251435 2252439 := bstep (se 1 (by rfl) ⟨1689329, by rfl⟩ : syracuseStep 2252439 = 3378659) B3378659
theorem B8117957 : Blo 2251435 8117957 := bbase (se 4 (by rfl) ⟨761058, by rfl⟩ : syracuseStep 8117957 = 1522117) (by norm_num)
theorem B5411971 : Blo 2251435 5411971 := bstep (se 1 (by rfl) ⟨4058978, by rfl⟩ : syracuseStep 5411971 = 8117957) B8117957
theorem B7215961 : Blo 2251435 7215961 := bstep (se 2 (by rfl) ⟨2705985, by rfl⟩ : syracuseStep 7215961 = 5411971) B5411971
theorem B9621281 : Blo 2251435 9621281 := bstep (se 2 (by rfl) ⟨3607980, by rfl⟩ : syracuseStep 9621281 = 7215961) B7215961
theorem B6414187 : Blo 2251435 6414187 := bstep (se 1 (by rfl) ⟨4810640, by rfl⟩ : syracuseStep 6414187 = 9621281) B9621281
theorem B8552249 : Blo 2251435 8552249 := bstep (se 2 (by rfl) ⟨3207093, by rfl⟩ : syracuseStep 8552249 = 6414187) B6414187
theorem B5701499 : Blo 2251435 5701499 := bstep (se 1 (by rfl) ⟨4276124, by rfl⟩ : syracuseStep 5701499 = 8552249) B8552249
theorem B3800999 : Blo 2251435 3800999 := bstep (se 1 (by rfl) ⟨2850749, by rfl⟩ : syracuseStep 3800999 = 5701499) B5701499
theorem B2533999 : Blo 2251435 2533999 := bstep (se 1 (by rfl) ⟨1900499, by rfl⟩ : syracuseStep 2533999 = 3800999) B3800999
theorem B3378665 : Blo 2251435 3378665 := bstep (se 2 (by rfl) ⟨1266999, by rfl⟩ : syracuseStep 3378665 = 2533999) B2533999
theorem B2252443 : Blo 2251435 2252443 := bstep (se 1 (by rfl) ⟨1689332, by rfl⟩ : syracuseStep 2252443 = 3378665) B3378665
theorem B2568577 : Blo 2251435 2568577 := bbase (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) (by norm_num)
theorem B3424769 : Blo 2251435 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B2283179 : Blo 2251435 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B24353909 : Blo 2251435 24353909 := bstep (se 5 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 24353909 = 2283179) B2283179
theorem B16235939 : Blo 2251435 16235939 := bstep (se 1 (by rfl) ⟨12176954, by rfl⟩ : syracuseStep 16235939 = 24353909) B24353909
theorem B10823959 : Blo 2251435 10823959 := bstep (se 1 (by rfl) ⟨8117969, by rfl⟩ : syracuseStep 10823959 = 16235939) B16235939
theorem B14431945 : Blo 2251435 14431945 := bstep (se 2 (by rfl) ⟨5411979, by rfl⟩ : syracuseStep 14431945 = 10823959) B10823959
theorem B19242593 : Blo 2251435 19242593 := bstep (se 2 (by rfl) ⟨7215972, by rfl⟩ : syracuseStep 19242593 = 14431945) B14431945
theorem B12828395 : Blo 2251435 12828395 := bstep (se 1 (by rfl) ⟨9621296, by rfl⟩ : syracuseStep 12828395 = 19242593) B19242593
theorem B8552263 : Blo 2251435 8552263 := bstep (se 1 (by rfl) ⟨6414197, by rfl⟩ : syracuseStep 8552263 = 12828395) B12828395
theorem B11403017 : Blo 2251435 11403017 := bstep (se 2 (by rfl) ⟨4276131, by rfl⟩ : syracuseStep 11403017 = 8552263) B8552263
theorem B7602011 : Blo 2251435 7602011 := bstep (se 1 (by rfl) ⟨5701508, by rfl⟩ : syracuseStep 7602011 = 11403017) B11403017
theorem B5068007 : Blo 2251435 5068007 := bstep (se 1 (by rfl) ⟨3801005, by rfl⟩ : syracuseStep 5068007 = 7602011) B7602011
theorem B3378671 : Blo 2251435 3378671 := bstep (se 1 (by rfl) ⟨2534003, by rfl⟩ : syracuseStep 3378671 = 5068007) B5068007
theorem B2252447 : Blo 2251435 2252447 := bstep (se 1 (by rfl) ⟨1689335, by rfl⟩ : syracuseStep 2252447 = 3378671) B3378671
theorem B3378677 : Blo 2251435 3378677 := bbase (se 5 (by rfl) ⟨158375, by rfl⟩ : syracuseStep 3378677 = 316751) (by norm_num)
theorem B2252451 : Blo 2251435 2252451 := bstep (se 1 (by rfl) ⟨1689338, by rfl⟩ : syracuseStep 2252451 = 3378677) B3378677
theorem B2405333 : Blo 2251435 2405333 := bbase (se 7 (by rfl) ⟨28187, by rfl⟩ : syracuseStep 2405333 = 56375) (by norm_num)
theorem B6414221 : Blo 2251435 6414221 := bstep (se 3 (by rfl) ⟨1202666, by rfl⟩ : syracuseStep 6414221 = 2405333) B2405333
theorem B4276147 : Blo 2251435 4276147 := bstep (se 1 (by rfl) ⟨3207110, by rfl⟩ : syracuseStep 4276147 = 6414221) B6414221
theorem B5701529 : Blo 2251435 5701529 := bstep (se 2 (by rfl) ⟨2138073, by rfl⟩ : syracuseStep 5701529 = 4276147) B4276147
theorem B3801019 : Blo 2251435 3801019 := bstep (se 1 (by rfl) ⟨2850764, by rfl⟩ : syracuseStep 3801019 = 5701529) B5701529
theorem B5068025 : Blo 2251435 5068025 := bstep (se 2 (by rfl) ⟨1900509, by rfl⟩ : syracuseStep 5068025 = 3801019) B3801019
theorem B3378683 : Blo 2251435 3378683 := bstep (se 1 (by rfl) ⟨2534012, by rfl⟩ : syracuseStep 3378683 = 5068025) B5068025
theorem B2252455 : Blo 2251435 2252455 := bstep (se 1 (by rfl) ⟨1689341, by rfl⟩ : syracuseStep 2252455 = 3378683) B3378683
theorem B2534017 : Blo 2251435 2534017 := bbase (se 2 (by rfl) ⟨950256, by rfl⟩ : syracuseStep 2534017 = 1900513) (by norm_num)
theorem B3378689 : Blo 2251435 3378689 := bstep (se 2 (by rfl) ⟨1267008, by rfl⟩ : syracuseStep 3378689 = 2534017) B2534017
theorem B2252459 : Blo 2251435 2252459 := bstep (se 1 (by rfl) ⟨1689344, by rfl⟩ : syracuseStep 2252459 = 3378689) B3378689
theorem B5701549 : Blo 2251435 5701549 := bbase (se 3 (by rfl) ⟨1069040, by rfl⟩ : syracuseStep 5701549 = 2138081) (by norm_num)
theorem B7602065 : Blo 2251435 7602065 := bstep (se 2 (by rfl) ⟨2850774, by rfl⟩ : syracuseStep 7602065 = 5701549) B5701549
theorem B5068043 : Blo 2251435 5068043 := bstep (se 1 (by rfl) ⟨3801032, by rfl⟩ : syracuseStep 5068043 = 7602065) B7602065
theorem B3378695 : Blo 2251435 3378695 := bstep (se 1 (by rfl) ⟨2534021, by rfl⟩ : syracuseStep 3378695 = 5068043) B5068043
theorem B2252463 : Blo 2251435 2252463 := bstep (se 1 (by rfl) ⟨1689347, by rfl⟩ : syracuseStep 2252463 = 3378695) B3378695
theorem B3378701 : Blo 2251435 3378701 := bbase (se 3 (by rfl) ⟨633506, by rfl⟩ : syracuseStep 3378701 = 1267013) (by norm_num)
theorem B2252467 : Blo 2251435 2252467 := bstep (se 1 (by rfl) ⟨1689350, by rfl⟩ : syracuseStep 2252467 = 3378701) B3378701
theorem B5068061 : Blo 2251435 5068061 := bbase (se 3 (by rfl) ⟨950261, by rfl⟩ : syracuseStep 5068061 = 1900523) (by norm_num)
theorem B3378707 : Blo 2251435 3378707 := bstep (se 1 (by rfl) ⟨2534030, by rfl⟩ : syracuseStep 3378707 = 5068061) B5068061
theorem B2252471 : Blo 2251435 2252471 := bstep (se 1 (by rfl) ⟨1689353, by rfl⟩ : syracuseStep 2252471 = 3378707) B3378707
theorem B3801053 : Blo 2251435 3801053 := bbase (se 3 (by rfl) ⟨712697, by rfl⟩ : syracuseStep 3801053 = 1425395) (by norm_num)
theorem B2534035 : Blo 2251435 2534035 := bstep (se 1 (by rfl) ⟨1900526, by rfl⟩ : syracuseStep 2534035 = 3801053) B3801053
theorem B3378713 : Blo 2251435 3378713 := bstep (se 2 (by rfl) ⟨1267017, by rfl⟩ : syracuseStep 3378713 = 2534035) B2534035
theorem B2252475 : Blo 2251435 2252475 := bstep (se 1 (by rfl) ⟨1689356, by rfl⟩ : syracuseStep 2252475 = 3378713) B3378713
theorem B8118085 : Blo 2251435 8118085 := bbase (se 4 (by rfl) ⟨761070, by rfl⟩ : syracuseStep 8118085 = 1522141) (by norm_num)
theorem B10824113 : Blo 2251435 10824113 := bstep (se 2 (by rfl) ⟨4059042, by rfl⟩ : syracuseStep 10824113 = 8118085) B8118085
theorem B7216075 : Blo 2251435 7216075 := bstep (se 1 (by rfl) ⟨5412056, by rfl⟩ : syracuseStep 7216075 = 10824113) B10824113
theorem B9621433 : Blo 2251435 9621433 := bstep (se 2 (by rfl) ⟨3608037, by rfl⟩ : syracuseStep 9621433 = 7216075) B7216075
theorem B12828577 : Blo 2251435 12828577 := bstep (se 2 (by rfl) ⟨4810716, by rfl⟩ : syracuseStep 12828577 = 9621433) B9621433
theorem B17104769 : Blo 2251435 17104769 := bstep (se 2 (by rfl) ⟨6414288, by rfl⟩ : syracuseStep 17104769 = 12828577) B12828577
theorem B11403179 : Blo 2251435 11403179 := bstep (se 1 (by rfl) ⟨8552384, by rfl⟩ : syracuseStep 11403179 = 17104769) B17104769
theorem B7602119 : Blo 2251435 7602119 := bstep (se 1 (by rfl) ⟨5701589, by rfl⟩ : syracuseStep 7602119 = 11403179) B11403179
theorem B5068079 : Blo 2251435 5068079 := bstep (se 1 (by rfl) ⟨3801059, by rfl⟩ : syracuseStep 5068079 = 7602119) B7602119
theorem B3378719 : Blo 2251435 3378719 := bstep (se 1 (by rfl) ⟨2534039, by rfl⟩ : syracuseStep 3378719 = 5068079) B5068079
theorem B2252479 : Blo 2251435 2252479 := bstep (se 1 (by rfl) ⟨1689359, by rfl⟩ : syracuseStep 2252479 = 3378719) B3378719
theorem B3378725 : Blo 2251435 3378725 := bbase (se 4 (by rfl) ⟨316755, by rfl⟩ : syracuseStep 3378725 = 633511) (by norm_num)
theorem B2252483 : Blo 2251435 2252483 := bstep (se 1 (by rfl) ⟨1689362, by rfl⟩ : syracuseStep 2252483 = 3378725) B3378725
theorem B2850805 : Blo 2251435 2850805 := bbase (se 5 (by rfl) ⟨133631, by rfl⟩ : syracuseStep 2850805 = 267263) (by norm_num)
theorem B3801073 : Blo 2251435 3801073 := bstep (se 2 (by rfl) ⟨1425402, by rfl⟩ : syracuseStep 3801073 = 2850805) B2850805
theorem B5068097 : Blo 2251435 5068097 := bstep (se 2 (by rfl) ⟨1900536, by rfl⟩ : syracuseStep 5068097 = 3801073) B3801073
theorem B3378731 : Blo 2251435 3378731 := bstep (se 1 (by rfl) ⟨2534048, by rfl⟩ : syracuseStep 3378731 = 5068097) B5068097
theorem B2252487 : Blo 2251435 2252487 := bstep (se 1 (by rfl) ⟨1689365, by rfl⟩ : syracuseStep 2252487 = 3378731) B3378731
theorem B2534053 : Blo 2251435 2534053 := bbase (se 4 (by rfl) ⟨237567, by rfl⟩ : syracuseStep 2534053 = 475135) (by norm_num)
theorem B3378737 : Blo 2251435 3378737 := bstep (se 2 (by rfl) ⟨1267026, by rfl⟩ : syracuseStep 3378737 = 2534053) B2534053
theorem B2252491 : Blo 2251435 2252491 := bstep (se 1 (by rfl) ⟨1689368, by rfl⟩ : syracuseStep 2252491 = 3378737) B3378737
theorem B2603677 : Blo 2251435 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B3471569 : Blo 2251435 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B2314379 : Blo 2251435 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B6171677 : Blo 2251435 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B4114451 : Blo 2251435 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B702199637 : Blo 2251435 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B468133091 : Blo 2251435 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B312088727 : Blo 2251435 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B832236605 : Blo 2251435 832236605 := bstep (se 3 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 832236605 = 312088727) B312088727
theorem B554824403 : Blo 2251435 554824403 := bstep (se 1 (by rfl) ⟨416118302, by rfl⟩ : syracuseStep 554824403 = 832236605) B832236605
theorem B369882935 : Blo 2251435 369882935 := bstep (se 1 (by rfl) ⟨277412201, by rfl⟩ : syracuseStep 369882935 = 554824403) B554824403
theorem B246588623 : Blo 2251435 246588623 := bstep (se 1 (by rfl) ⟨184941467, by rfl⟩ : syracuseStep 246588623 = 369882935) B369882935
theorem B164392415 : Blo 2251435 164392415 := bstep (se 1 (by rfl) ⟨123294311, by rfl⟩ : syracuseStep 164392415 = 246588623) B246588623
theorem B109594943 : Blo 2251435 109594943 := bstep (se 1 (by rfl) ⟨82196207, by rfl⟩ : syracuseStep 109594943 = 164392415) B164392415
theorem B73063295 : Blo 2251435 73063295 := bstep (se 1 (by rfl) ⟨54797471, by rfl⟩ : syracuseStep 73063295 = 109594943) B109594943
theorem B48708863 : Blo 2251435 48708863 := bstep (se 1 (by rfl) ⟨36531647, by rfl⟩ : syracuseStep 48708863 = 73063295) B73063295
theorem B32472575 : Blo 2251435 32472575 := bstep (se 1 (by rfl) ⟨24354431, by rfl⟩ : syracuseStep 32472575 = 48708863) B48708863
theorem B21648383 : Blo 2251435 21648383 := bstep (se 1 (by rfl) ⟨16236287, by rfl⟩ : syracuseStep 21648383 = 32472575) B32472575
theorem B14432255 : Blo 2251435 14432255 := bstep (se 1 (by rfl) ⟨10824191, by rfl⟩ : syracuseStep 14432255 = 21648383) B21648383
theorem B9621503 : Blo 2251435 9621503 := bstep (se 1 (by rfl) ⟨7216127, by rfl⟩ : syracuseStep 9621503 = 14432255) B14432255
theorem B6414335 : Blo 2251435 6414335 := bstep (se 1 (by rfl) ⟨4810751, by rfl⟩ : syracuseStep 6414335 = 9621503) B9621503
theorem B4276223 : Blo 2251435 4276223 := bstep (se 1 (by rfl) ⟨3207167, by rfl⟩ : syracuseStep 4276223 = 6414335) B6414335
theorem B2850815 : Blo 2251435 2850815 := bstep (se 1 (by rfl) ⟨2138111, by rfl⟩ : syracuseStep 2850815 = 4276223) B4276223
theorem B7602173 : Blo 2251435 7602173 := bstep (se 3 (by rfl) ⟨1425407, by rfl⟩ : syracuseStep 7602173 = 2850815) B2850815
theorem B5068115 : Blo 2251435 5068115 := bstep (se 1 (by rfl) ⟨3801086, by rfl⟩ : syracuseStep 5068115 = 7602173) B7602173
theorem B3378743 : Blo 2251435 3378743 := bstep (se 1 (by rfl) ⟨2534057, by rfl⟩ : syracuseStep 3378743 = 5068115) B5068115
theorem B2252495 : Blo 2251435 2252495 := bstep (se 1 (by rfl) ⟨1689371, by rfl⟩ : syracuseStep 2252495 = 3378743) B3378743
theorem B3378749 : Blo 2251435 3378749 := bbase (se 3 (by rfl) ⟨633515, by rfl⟩ : syracuseStep 3378749 = 1267031) (by norm_num)
theorem B2252499 : Blo 2251435 2252499 := bstep (se 1 (by rfl) ⟨1689374, by rfl⟩ : syracuseStep 2252499 = 3378749) B3378749
theorem B5068133 : Blo 2251435 5068133 := bbase (se 4 (by rfl) ⟨475137, by rfl⟩ : syracuseStep 5068133 = 950275) (by norm_num)
theorem B3378755 : Blo 2251435 3378755 := bstep (se 1 (by rfl) ⟨2534066, by rfl⟩ : syracuseStep 3378755 = 5068133) B5068133
theorem B2252503 : Blo 2251435 2252503 := bstep (se 1 (by rfl) ⟨1689377, by rfl⟩ : syracuseStep 2252503 = 3378755) B3378755
theorem B5701661 : Blo 2251435 5701661 := bbase (se 3 (by rfl) ⟨1069061, by rfl⟩ : syracuseStep 5701661 = 2138123) (by norm_num)
theorem B3801107 : Blo 2251435 3801107 := bstep (se 1 (by rfl) ⟨2850830, by rfl⟩ : syracuseStep 3801107 = 5701661) B5701661
theorem B2534071 : Blo 2251435 2534071 := bstep (se 1 (by rfl) ⟨1900553, by rfl⟩ : syracuseStep 2534071 = 3801107) B3801107
theorem B3378761 : Blo 2251435 3378761 := bstep (se 2 (by rfl) ⟨1267035, by rfl⟩ : syracuseStep 3378761 = 2534071) B2534071
theorem B2252507 : Blo 2251435 2252507 := bstep (se 1 (by rfl) ⟨1689380, by rfl⟩ : syracuseStep 2252507 = 3378761) B3378761
theorem B4276253 : Blo 2251435 4276253 := bbase (se 3 (by rfl) ⟨801797, by rfl⟩ : syracuseStep 4276253 = 1603595) (by norm_num)
theorem B11403341 : Blo 2251435 11403341 := bstep (se 3 (by rfl) ⟨2138126, by rfl⟩ : syracuseStep 11403341 = 4276253) B4276253
theorem B7602227 : Blo 2251435 7602227 := bstep (se 1 (by rfl) ⟨5701670, by rfl⟩ : syracuseStep 7602227 = 11403341) B11403341
theorem B5068151 : Blo 2251435 5068151 := bstep (se 1 (by rfl) ⟨3801113, by rfl⟩ : syracuseStep 5068151 = 7602227) B7602227
theorem B3378767 : Blo 2251435 3378767 := bstep (se 1 (by rfl) ⟨2534075, by rfl⟩ : syracuseStep 3378767 = 5068151) B5068151
theorem B2252511 : Blo 2251435 2252511 := bstep (se 1 (by rfl) ⟨1689383, by rfl⟩ : syracuseStep 2252511 = 3378767) B3378767
theorem B3378773 : Blo 2251435 3378773 := bbase (se 8 (by rfl) ⟨19797, by rfl⟩ : syracuseStep 3378773 = 39595) (by norm_num)
theorem B2252515 : Blo 2251435 2252515 := bstep (se 1 (by rfl) ⟨1689386, by rfl⟩ : syracuseStep 2252515 = 3378773) B3378773
theorem B9621605 : Blo 2251435 9621605 := bbase (se 4 (by rfl) ⟨902025, by rfl⟩ : syracuseStep 9621605 = 1804051) (by norm_num)
theorem B6414403 : Blo 2251435 6414403 := bstep (se 1 (by rfl) ⟨4810802, by rfl⟩ : syracuseStep 6414403 = 9621605) B9621605
theorem B8552537 : Blo 2251435 8552537 := bstep (se 2 (by rfl) ⟨3207201, by rfl⟩ : syracuseStep 8552537 = 6414403) B6414403
theorem B5701691 : Blo 2251435 5701691 := bstep (se 1 (by rfl) ⟨4276268, by rfl⟩ : syracuseStep 5701691 = 8552537) B8552537
theorem B3801127 : Blo 2251435 3801127 := bstep (se 1 (by rfl) ⟨2850845, by rfl⟩ : syracuseStep 3801127 = 5701691) B5701691
theorem B5068169 : Blo 2251435 5068169 := bstep (se 2 (by rfl) ⟨1900563, by rfl⟩ : syracuseStep 5068169 = 3801127) B3801127
theorem B3378779 : Blo 2251435 3378779 := bstep (se 1 (by rfl) ⟨2534084, by rfl⟩ : syracuseStep 3378779 = 5068169) B5068169
theorem B2252519 : Blo 2251435 2252519 := bstep (se 1 (by rfl) ⟨1689389, by rfl⟩ : syracuseStep 2252519 = 3378779) B3378779
theorem B2534089 : Blo 2251435 2534089 := bbase (se 2 (by rfl) ⟨950283, by rfl⟩ : syracuseStep 2534089 = 1900567) (by norm_num)
theorem B3378785 : Blo 2251435 3378785 := bstep (se 2 (by rfl) ⟨1267044, by rfl⟩ : syracuseStep 3378785 = 2534089) B2534089
theorem B2252523 : Blo 2251435 2252523 := bstep (se 1 (by rfl) ⟨1689392, by rfl⟩ : syracuseStep 2252523 = 3378785) B3378785
theorem B7216229 : Blo 2251435 7216229 := bbase (se 4 (by rfl) ⟨676521, by rfl⟩ : syracuseStep 7216229 = 1353043) (by norm_num)
theorem B19243277 : Blo 2251435 19243277 := bstep (se 3 (by rfl) ⟨3608114, by rfl⟩ : syracuseStep 19243277 = 7216229) B7216229
theorem B12828851 : Blo 2251435 12828851 := bstep (se 1 (by rfl) ⟨9621638, by rfl⟩ : syracuseStep 12828851 = 19243277) B19243277
theorem B8552567 : Blo 2251435 8552567 := bstep (se 1 (by rfl) ⟨6414425, by rfl⟩ : syracuseStep 8552567 = 12828851) B12828851
theorem B5701711 : Blo 2251435 5701711 := bstep (se 1 (by rfl) ⟨4276283, by rfl⟩ : syracuseStep 5701711 = 8552567) B8552567
theorem B7602281 : Blo 2251435 7602281 := bstep (se 2 (by rfl) ⟨2850855, by rfl⟩ : syracuseStep 7602281 = 5701711) B5701711
theorem B5068187 : Blo 2251435 5068187 := bstep (se 1 (by rfl) ⟨3801140, by rfl⟩ : syracuseStep 5068187 = 7602281) B7602281
theorem B3378791 : Blo 2251435 3378791 := bstep (se 1 (by rfl) ⟨2534093, by rfl⟩ : syracuseStep 3378791 = 5068187) B5068187
theorem B2252527 : Blo 2251435 2252527 := bstep (se 1 (by rfl) ⟨1689395, by rfl⟩ : syracuseStep 2252527 = 3378791) B3378791
theorem B3378797 : Blo 2251435 3378797 := bbase (se 3 (by rfl) ⟨633524, by rfl⟩ : syracuseStep 3378797 = 1267049) (by norm_num)
theorem B2252531 : Blo 2251435 2252531 := bstep (se 1 (by rfl) ⟨1689398, by rfl⟩ : syracuseStep 2252531 = 3378797) B3378797
theorem B5068205 : Blo 2251435 5068205 := bbase (se 3 (by rfl) ⟨950288, by rfl⟩ : syracuseStep 5068205 = 1900577) (by norm_num)
theorem B3378803 : Blo 2251435 3378803 := bstep (se 1 (by rfl) ⟨2534102, by rfl⟩ : syracuseStep 3378803 = 5068205) B5068205
theorem B2252535 : Blo 2251435 2252535 := bstep (se 1 (by rfl) ⟨1689401, by rfl⟩ : syracuseStep 2252535 = 3378803) B3378803
theorem B2889769 : Blo 2251435 2889769 := bbase (se 2 (by rfl) ⟨1083663, by rfl⟩ : syracuseStep 2889769 = 2167327) (by norm_num)
theorem B3853025 : Blo 2251435 3853025 := bstep (se 2 (by rfl) ⟨1444884, by rfl⟩ : syracuseStep 3853025 = 2889769) B2889769
theorem B2568683 : Blo 2251435 2568683 := bstep (se 1 (by rfl) ⟨1926512, by rfl⟩ : syracuseStep 2568683 = 3853025) B3853025
theorem B6849821 : Blo 2251435 6849821 := bstep (se 3 (by rfl) ⟨1284341, by rfl⟩ : syracuseStep 6849821 = 2568683) B2568683
theorem B4566547 : Blo 2251435 4566547 := bstep (se 1 (by rfl) ⟨3424910, by rfl⟩ : syracuseStep 4566547 = 6849821) B6849821
theorem B6088729 : Blo 2251435 6088729 := bstep (se 2 (by rfl) ⟨2283273, by rfl⟩ : syracuseStep 6088729 = 4566547) B4566547
theorem B8118305 : Blo 2251435 8118305 := bstep (se 2 (by rfl) ⟨3044364, by rfl⟩ : syracuseStep 8118305 = 6088729) B6088729
theorem B5412203 : Blo 2251435 5412203 := bstep (se 1 (by rfl) ⟨4059152, by rfl⟩ : syracuseStep 5412203 = 8118305) B8118305
theorem B3608135 : Blo 2251435 3608135 := bstep (se 1 (by rfl) ⟨2706101, by rfl⟩ : syracuseStep 3608135 = 5412203) B5412203
theorem B2405423 : Blo 2251435 2405423 := bstep (se 1 (by rfl) ⟨1804067, by rfl⟩ : syracuseStep 2405423 = 3608135) B3608135
theorem B6414461 : Blo 2251435 6414461 := bstep (se 3 (by rfl) ⟨1202711, by rfl⟩ : syracuseStep 6414461 = 2405423) B2405423
theorem B4276307 : Blo 2251435 4276307 := bstep (se 1 (by rfl) ⟨3207230, by rfl⟩ : syracuseStep 4276307 = 6414461) B6414461
theorem B2850871 : Blo 2251435 2850871 := bstep (se 1 (by rfl) ⟨2138153, by rfl⟩ : syracuseStep 2850871 = 4276307) B4276307
theorem B3801161 : Blo 2251435 3801161 := bstep (se 2 (by rfl) ⟨1425435, by rfl⟩ : syracuseStep 3801161 = 2850871) B2850871
theorem B2534107 : Blo 2251435 2534107 := bstep (se 1 (by rfl) ⟨1900580, by rfl⟩ : syracuseStep 2534107 = 3801161) B3801161
theorem B3378809 : Blo 2251435 3378809 := bstep (se 2 (by rfl) ⟨1267053, by rfl⟩ : syracuseStep 3378809 = 2534107) B2534107
theorem B2252539 : Blo 2251435 2252539 := bstep (se 1 (by rfl) ⟨1689404, by rfl⟩ : syracuseStep 2252539 = 3378809) B3378809
theorem B2438245 : Blo 2251435 2438245 := bbase (se 4 (by rfl) ⟨228585, by rfl⟩ : syracuseStep 2438245 = 457171) (by norm_num)
theorem B13003973 : Blo 2251435 13003973 := bstep (se 4 (by rfl) ⟨1219122, by rfl⟩ : syracuseStep 13003973 = 2438245) B2438245
theorem B8669315 : Blo 2251435 8669315 := bstep (se 1 (by rfl) ⟨6501986, by rfl⟩ : syracuseStep 8669315 = 13003973) B13003973
theorem B5779543 : Blo 2251435 5779543 := bstep (se 1 (by rfl) ⟨4334657, by rfl⟩ : syracuseStep 5779543 = 8669315) B8669315
theorem B7706057 : Blo 2251435 7706057 := bstep (se 2 (by rfl) ⟨2889771, by rfl⟩ : syracuseStep 7706057 = 5779543) B5779543
theorem B20549485 : Blo 2251435 20549485 := bstep (se 3 (by rfl) ⟨3853028, by rfl⟩ : syracuseStep 20549485 = 7706057) B7706057
theorem B27399313 : Blo 2251435 27399313 := bstep (se 2 (by rfl) ⟨10274742, by rfl⟩ : syracuseStep 27399313 = 20549485) B20549485
theorem B146129669 : Blo 2251435 146129669 := bstep (se 4 (by rfl) ⟨13699656, by rfl⟩ : syracuseStep 146129669 = 27399313) B27399313
theorem B97419779 : Blo 2251435 97419779 := bstep (se 1 (by rfl) ⟨73064834, by rfl⟩ : syracuseStep 97419779 = 146129669) B146129669
theorem B64946519 : Blo 2251435 64946519 := bstep (se 1 (by rfl) ⟨48709889, by rfl⟩ : syracuseStep 64946519 = 97419779) B97419779
theorem B43297679 : Blo 2251435 43297679 := bstep (se 1 (by rfl) ⟨32473259, by rfl⟩ : syracuseStep 43297679 = 64946519) B64946519
theorem B28865119 : Blo 2251435 28865119 := bstep (se 1 (by rfl) ⟨21648839, by rfl⟩ : syracuseStep 28865119 = 43297679) B43297679
theorem B38486825 : Blo 2251435 38486825 := bstep (se 2 (by rfl) ⟨14432559, by rfl⟩ : syracuseStep 38486825 = 28865119) B28865119
theorem B25657883 : Blo 2251435 25657883 := bstep (se 1 (by rfl) ⟨19243412, by rfl⟩ : syracuseStep 25657883 = 38486825) B38486825
theorem B17105255 : Blo 2251435 17105255 := bstep (se 1 (by rfl) ⟨12828941, by rfl⟩ : syracuseStep 17105255 = 25657883) B25657883
theorem B11403503 : Blo 2251435 11403503 := bstep (se 1 (by rfl) ⟨8552627, by rfl⟩ : syracuseStep 11403503 = 17105255) B17105255
theorem B7602335 : Blo 2251435 7602335 := bstep (se 1 (by rfl) ⟨5701751, by rfl⟩ : syracuseStep 7602335 = 11403503) B11403503
theorem B5068223 : Blo 2251435 5068223 := bstep (se 1 (by rfl) ⟨3801167, by rfl⟩ : syracuseStep 5068223 = 7602335) B7602335
theorem B3378815 : Blo 2251435 3378815 := bstep (se 1 (by rfl) ⟨2534111, by rfl⟩ : syracuseStep 3378815 = 5068223) B5068223
theorem B2252543 : Blo 2251435 2252543 := bstep (se 1 (by rfl) ⟨1689407, by rfl⟩ : syracuseStep 2252543 = 3378815) B3378815
theorem B3378821 : Blo 2251435 3378821 := bbase (se 4 (by rfl) ⟨316764, by rfl⟩ : syracuseStep 3378821 = 633529) (by norm_num)
theorem B2252547 : Blo 2251435 2252547 := bstep (se 1 (by rfl) ⟨1689410, by rfl⟩ : syracuseStep 2252547 = 3378821) B3378821
theorem B3801181 : Blo 2251435 3801181 := bbase (se 3 (by rfl) ⟨712721, by rfl⟩ : syracuseStep 3801181 = 1425443) (by norm_num)
theorem B5068241 : Blo 2251435 5068241 := bstep (se 2 (by rfl) ⟨1900590, by rfl⟩ : syracuseStep 5068241 = 3801181) B3801181
theorem B3378827 : Blo 2251435 3378827 := bstep (se 1 (by rfl) ⟨2534120, by rfl⟩ : syracuseStep 3378827 = 5068241) B5068241
theorem B2252551 : Blo 2251435 2252551 := bstep (se 1 (by rfl) ⟨1689413, by rfl⟩ : syracuseStep 2252551 = 3378827) B3378827
theorem B2534125 : Blo 2251435 2534125 := bbase (se 3 (by rfl) ⟨475148, by rfl⟩ : syracuseStep 2534125 = 950297) (by norm_num)
theorem B3378833 : Blo 2251435 3378833 := bstep (se 2 (by rfl) ⟨1267062, by rfl⟩ : syracuseStep 3378833 = 2534125) B2534125
theorem B2252555 : Blo 2251435 2252555 := bstep (se 1 (by rfl) ⟨1689416, by rfl⟩ : syracuseStep 2252555 = 3378833) B3378833
theorem B7602389 : Blo 2251435 7602389 := bbase (se 7 (by rfl) ⟨89090, by rfl⟩ : syracuseStep 7602389 = 178181) (by norm_num)
theorem B5068259 : Blo 2251435 5068259 := bstep (se 1 (by rfl) ⟨3801194, by rfl⟩ : syracuseStep 5068259 = 7602389) B7602389
theorem B3378839 : Blo 2251435 3378839 := bstep (se 1 (by rfl) ⟨2534129, by rfl⟩ : syracuseStep 3378839 = 5068259) B5068259
theorem B2252559 : Blo 2251435 2252559 := bstep (se 1 (by rfl) ⟨1689419, by rfl⟩ : syracuseStep 2252559 = 3378839) B3378839
theorem B3378845 : Blo 2251435 3378845 := bbase (se 3 (by rfl) ⟨633533, by rfl⟩ : syracuseStep 3378845 = 1267067) (by norm_num)
theorem B2252563 : Blo 2251435 2252563 := bstep (se 1 (by rfl) ⟨1689422, by rfl⟩ : syracuseStep 2252563 = 3378845) B3378845
theorem B5068277 : Blo 2251435 5068277 := bbase (se 5 (by rfl) ⟨237575, by rfl⟩ : syracuseStep 5068277 = 475151) (by norm_num)
theorem B3378851 : Blo 2251435 3378851 := bstep (se 1 (by rfl) ⟨2534138, by rfl⟩ : syracuseStep 3378851 = 5068277) B5068277
theorem B2252567 : Blo 2251435 2252567 := bstep (se 1 (by rfl) ⟨1689425, by rfl⟩ : syracuseStep 2252567 = 3378851) B3378851
theorem B2283305 : Blo 2251435 2283305 := bbase (se 2 (by rfl) ⟨856239, by rfl⟩ : syracuseStep 2283305 = 1712479) (by norm_num)
theorem B6088813 : Blo 2251435 6088813 := bstep (se 3 (by rfl) ⟨1141652, by rfl⟩ : syracuseStep 6088813 = 2283305) B2283305
theorem B32473669 : Blo 2251435 32473669 := bstep (se 4 (by rfl) ⟨3044406, by rfl⟩ : syracuseStep 32473669 = 6088813) B6088813
theorem B43298225 : Blo 2251435 43298225 := bstep (se 2 (by rfl) ⟨16236834, by rfl⟩ : syracuseStep 43298225 = 32473669) B32473669
theorem B28865483 : Blo 2251435 28865483 := bstep (se 1 (by rfl) ⟨21649112, by rfl⟩ : syracuseStep 28865483 = 43298225) B43298225
theorem B19243655 : Blo 2251435 19243655 := bstep (se 1 (by rfl) ⟨14432741, by rfl⟩ : syracuseStep 19243655 = 28865483) B28865483
theorem B12829103 : Blo 2251435 12829103 := bstep (se 1 (by rfl) ⟨9621827, by rfl⟩ : syracuseStep 12829103 = 19243655) B19243655
theorem B8552735 : Blo 2251435 8552735 := bstep (se 1 (by rfl) ⟨6414551, by rfl⟩ : syracuseStep 8552735 = 12829103) B12829103
theorem B5701823 : Blo 2251435 5701823 := bstep (se 1 (by rfl) ⟨4276367, by rfl⟩ : syracuseStep 5701823 = 8552735) B8552735
theorem B3801215 : Blo 2251435 3801215 := bstep (se 1 (by rfl) ⟨2850911, by rfl⟩ : syracuseStep 3801215 = 5701823) B5701823
theorem B2534143 : Blo 2251435 2534143 := bstep (se 1 (by rfl) ⟨1900607, by rfl⟩ : syracuseStep 2534143 = 3801215) B3801215
theorem B3378857 : Blo 2251435 3378857 := bstep (se 2 (by rfl) ⟨1267071, by rfl⟩ : syracuseStep 3378857 = 2534143) B2534143
theorem B2252571 : Blo 2251435 2252571 := bstep (se 1 (by rfl) ⟨1689428, by rfl⟩ : syracuseStep 2252571 = 3378857) B3378857
theorem B2405461 : Blo 2251435 2405461 := bbase (se 8 (by rfl) ⟨14094, by rfl⟩ : syracuseStep 2405461 = 28189) (by norm_num)
theorem B3207281 : Blo 2251435 3207281 := bstep (se 2 (by rfl) ⟨1202730, by rfl⟩ : syracuseStep 3207281 = 2405461) B2405461
theorem B8552749 : Blo 2251435 8552749 := bstep (se 3 (by rfl) ⟨1603640, by rfl⟩ : syracuseStep 8552749 = 3207281) B3207281
theorem B11403665 : Blo 2251435 11403665 := bstep (se 2 (by rfl) ⟨4276374, by rfl⟩ : syracuseStep 11403665 = 8552749) B8552749
theorem B7602443 : Blo 2251435 7602443 := bstep (se 1 (by rfl) ⟨5701832, by rfl⟩ : syracuseStep 7602443 = 11403665) B11403665
theorem B5068295 : Blo 2251435 5068295 := bstep (se 1 (by rfl) ⟨3801221, by rfl⟩ : syracuseStep 5068295 = 7602443) B7602443
theorem B3378863 : Blo 2251435 3378863 := bstep (se 1 (by rfl) ⟨2534147, by rfl⟩ : syracuseStep 3378863 = 5068295) B5068295
theorem B2252575 : Blo 2251435 2252575 := bstep (se 1 (by rfl) ⟨1689431, by rfl⟩ : syracuseStep 2252575 = 3378863) B3378863
theorem B3378869 : Blo 2251435 3378869 := bbase (se 5 (by rfl) ⟨158384, by rfl⟩ : syracuseStep 3378869 = 316769) (by norm_num)
theorem B2252579 : Blo 2251435 2252579 := bstep (se 1 (by rfl) ⟨1689434, by rfl⟩ : syracuseStep 2252579 = 3378869) B3378869
theorem B5701853 : Blo 2251435 5701853 := bbase (se 3 (by rfl) ⟨1069097, by rfl⟩ : syracuseStep 5701853 = 2138195) (by norm_num)
theorem B3801235 : Blo 2251435 3801235 := bstep (se 1 (by rfl) ⟨2850926, by rfl⟩ : syracuseStep 3801235 = 5701853) B5701853
theorem B5068313 : Blo 2251435 5068313 := bstep (se 2 (by rfl) ⟨1900617, by rfl⟩ : syracuseStep 5068313 = 3801235) B3801235
theorem B3378875 : Blo 2251435 3378875 := bstep (se 1 (by rfl) ⟨2534156, by rfl⟩ : syracuseStep 3378875 = 5068313) B5068313
theorem B2252583 : Blo 2251435 2252583 := bstep (se 1 (by rfl) ⟨1689437, by rfl⟩ : syracuseStep 2252583 = 3378875) B3378875
theorem B2534161 : Blo 2251435 2534161 := bbase (se 2 (by rfl) ⟨950310, by rfl⟩ : syracuseStep 2534161 = 1900621) (by norm_num)
theorem B3378881 : Blo 2251435 3378881 := bstep (se 2 (by rfl) ⟨1267080, by rfl⟩ : syracuseStep 3378881 = 2534161) B2534161
theorem B2252587 : Blo 2251435 2252587 := bstep (se 1 (by rfl) ⟨1689440, by rfl⟩ : syracuseStep 2252587 = 3378881) B3378881
theorem B4276405 : Blo 2251435 4276405 := bbase (se 5 (by rfl) ⟨200456, by rfl⟩ : syracuseStep 4276405 = 400913) (by norm_num)
theorem B5701873 : Blo 2251435 5701873 := bstep (se 2 (by rfl) ⟨2138202, by rfl⟩ : syracuseStep 5701873 = 4276405) B4276405
theorem B7602497 : Blo 2251435 7602497 := bstep (se 2 (by rfl) ⟨2850936, by rfl⟩ : syracuseStep 7602497 = 5701873) B5701873
theorem B5068331 : Blo 2251435 5068331 := bstep (se 1 (by rfl) ⟨3801248, by rfl⟩ : syracuseStep 5068331 = 7602497) B7602497
theorem B3378887 : Blo 2251435 3378887 := bstep (se 1 (by rfl) ⟨2534165, by rfl⟩ : syracuseStep 3378887 = 5068331) B5068331
theorem B2252591 : Blo 2251435 2252591 := bstep (se 1 (by rfl) ⟨1689443, by rfl⟩ : syracuseStep 2252591 = 3378887) B3378887
theorem B3378893 : Blo 2251435 3378893 := bbase (se 3 (by rfl) ⟨633542, by rfl⟩ : syracuseStep 3378893 = 1267085) (by norm_num)
theorem B2252595 : Blo 2251435 2252595 := bstep (se 1 (by rfl) ⟨1689446, by rfl⟩ : syracuseStep 2252595 = 3378893) B3378893
theorem B5068349 : Blo 2251435 5068349 := bbase (se 3 (by rfl) ⟨950315, by rfl⟩ : syracuseStep 5068349 = 1900631) (by norm_num)
theorem B3378899 : Blo 2251435 3378899 := bstep (se 1 (by rfl) ⟨2534174, by rfl⟩ : syracuseStep 3378899 = 5068349) B5068349
theorem B2252599 : Blo 2251435 2252599 := bstep (se 1 (by rfl) ⟨1689449, by rfl⟩ : syracuseStep 2252599 = 3378899) B3378899
theorem B3801269 : Blo 2251435 3801269 := bbase (se 5 (by rfl) ⟨178184, by rfl⟩ : syracuseStep 3801269 = 356369) (by norm_num)
theorem B2534179 : Blo 2251435 2534179 := bstep (se 1 (by rfl) ⟨1900634, by rfl⟩ : syracuseStep 2534179 = 3801269) B3801269
theorem B3378905 : Blo 2251435 3378905 := bstep (se 2 (by rfl) ⟨1267089, by rfl⟩ : syracuseStep 3378905 = 2534179) B2534179
theorem B2252603 : Blo 2251435 2252603 := bstep (se 1 (by rfl) ⟨1689452, by rfl⟩ : syracuseStep 2252603 = 3378905) B3378905
theorem B5412365 : Blo 2251435 5412365 := bbase (se 3 (by rfl) ⟨1014818, by rfl⟩ : syracuseStep 5412365 = 2029637) (by norm_num)
theorem B3608243 : Blo 2251435 3608243 := bstep (se 1 (by rfl) ⟨2706182, by rfl⟩ : syracuseStep 3608243 = 5412365) B5412365
theorem B2405495 : Blo 2251435 2405495 := bstep (se 1 (by rfl) ⟨1804121, by rfl⟩ : syracuseStep 2405495 = 3608243) B3608243
theorem B6414653 : Blo 2251435 6414653 := bstep (se 3 (by rfl) ⟨1202747, by rfl⟩ : syracuseStep 6414653 = 2405495) B2405495
theorem B17105741 : Blo 2251435 17105741 := bstep (se 3 (by rfl) ⟨3207326, by rfl⟩ : syracuseStep 17105741 = 6414653) B6414653
theorem B11403827 : Blo 2251435 11403827 := bstep (se 1 (by rfl) ⟨8552870, by rfl⟩ : syracuseStep 11403827 = 17105741) B17105741
theorem B7602551 : Blo 2251435 7602551 := bstep (se 1 (by rfl) ⟨5701913, by rfl⟩ : syracuseStep 7602551 = 11403827) B11403827
theorem B5068367 : Blo 2251435 5068367 := bstep (se 1 (by rfl) ⟨3801275, by rfl⟩ : syracuseStep 5068367 = 7602551) B7602551
theorem B3378911 : Blo 2251435 3378911 := bstep (se 1 (by rfl) ⟨2534183, by rfl⟩ : syracuseStep 3378911 = 5068367) B5068367
theorem B2252607 : Blo 2251435 2252607 := bstep (se 1 (by rfl) ⟨1689455, by rfl⟩ : syracuseStep 2252607 = 3378911) B3378911
theorem B3378917 : Blo 2251435 3378917 := bbase (se 4 (by rfl) ⟨316773, by rfl⟩ : syracuseStep 3378917 = 633547) (by norm_num)
theorem B2252611 : Blo 2251435 2252611 := bstep (se 1 (by rfl) ⟨1689458, by rfl⟩ : syracuseStep 2252611 = 3378917) B3378917
theorem B6414677 : Blo 2251435 6414677 := bbase (se 10 (by rfl) ⟨9396, by rfl⟩ : syracuseStep 6414677 = 18793) (by norm_num)
theorem B4276451 : Blo 2251435 4276451 := bstep (se 1 (by rfl) ⟨3207338, by rfl⟩ : syracuseStep 4276451 = 6414677) B6414677
theorem B2850967 : Blo 2251435 2850967 := bstep (se 1 (by rfl) ⟨2138225, by rfl⟩ : syracuseStep 2850967 = 4276451) B4276451
theorem B3801289 : Blo 2251435 3801289 := bstep (se 2 (by rfl) ⟨1425483, by rfl⟩ : syracuseStep 3801289 = 2850967) B2850967
theorem B5068385 : Blo 2251435 5068385 := bstep (se 2 (by rfl) ⟨1900644, by rfl⟩ : syracuseStep 5068385 = 3801289) B3801289
theorem B3378923 : Blo 2251435 3378923 := bstep (se 1 (by rfl) ⟨2534192, by rfl⟩ : syracuseStep 3378923 = 5068385) B5068385
theorem B2252615 : Blo 2251435 2252615 := bstep (se 1 (by rfl) ⟨1689461, by rfl⟩ : syracuseStep 2252615 = 3378923) B3378923
theorem B2534197 : Blo 2251435 2534197 := bbase (se 5 (by rfl) ⟨118790, by rfl⟩ : syracuseStep 2534197 = 237581) (by norm_num)
theorem B3378929 : Blo 2251435 3378929 := bstep (se 2 (by rfl) ⟨1267098, by rfl⟩ : syracuseStep 3378929 = 2534197) B2534197
theorem B2252619 : Blo 2251435 2252619 := bstep (se 1 (by rfl) ⟨1689464, by rfl⟩ : syracuseStep 2252619 = 3378929) B3378929
theorem B2850977 : Blo 2251435 2850977 := bbase (se 2 (by rfl) ⟨1069116, by rfl⟩ : syracuseStep 2850977 = 2138233) (by norm_num)
theorem B7602605 : Blo 2251435 7602605 := bstep (se 3 (by rfl) ⟨1425488, by rfl⟩ : syracuseStep 7602605 = 2850977) B2850977
theorem B5068403 : Blo 2251435 5068403 := bstep (se 1 (by rfl) ⟨3801302, by rfl⟩ : syracuseStep 5068403 = 7602605) B7602605
theorem B3378935 : Blo 2251435 3378935 := bstep (se 1 (by rfl) ⟨2534201, by rfl⟩ : syracuseStep 3378935 = 5068403) B5068403
theorem B2252623 : Blo 2251435 2252623 := bstep (se 1 (by rfl) ⟨1689467, by rfl⟩ : syracuseStep 2252623 = 3378935) B3378935
theorem B3378941 : Blo 2251435 3378941 := bbase (se 3 (by rfl) ⟨633551, by rfl⟩ : syracuseStep 3378941 = 1267103) (by norm_num)
theorem B2252627 : Blo 2251435 2252627 := bstep (se 1 (by rfl) ⟨1689470, by rfl⟩ : syracuseStep 2252627 = 3378941) B3378941
theorem B5068421 : Blo 2251435 5068421 := bbase (se 4 (by rfl) ⟨475164, by rfl⟩ : syracuseStep 5068421 = 950329) (by norm_num)
theorem B3378947 : Blo 2251435 3378947 := bstep (se 1 (by rfl) ⟨2534210, by rfl⟩ : syracuseStep 3378947 = 5068421) B5068421
theorem B2252631 : Blo 2251435 2252631 := bstep (se 1 (by rfl) ⟨1689473, by rfl⟩ : syracuseStep 2252631 = 3378947) B3378947
theorem B4059325 : Blo 2251435 4059325 := bbase (se 3 (by rfl) ⟨761123, by rfl⟩ : syracuseStep 4059325 = 1522247) (by norm_num)
theorem B5412433 : Blo 2251435 5412433 := bstep (se 2 (by rfl) ⟨2029662, by rfl⟩ : syracuseStep 5412433 = 4059325) B4059325
theorem B7216577 : Blo 2251435 7216577 := bstep (se 2 (by rfl) ⟨2706216, by rfl⟩ : syracuseStep 7216577 = 5412433) B5412433
theorem B4811051 : Blo 2251435 4811051 := bstep (se 1 (by rfl) ⟨3608288, by rfl⟩ : syracuseStep 4811051 = 7216577) B7216577
theorem B3207367 : Blo 2251435 3207367 := bstep (se 1 (by rfl) ⟨2405525, by rfl⟩ : syracuseStep 3207367 = 4811051) B4811051
theorem B4276489 : Blo 2251435 4276489 := bstep (se 2 (by rfl) ⟨1603683, by rfl⟩ : syracuseStep 4276489 = 3207367) B3207367
theorem B5701985 : Blo 2251435 5701985 := bstep (se 2 (by rfl) ⟨2138244, by rfl⟩ : syracuseStep 5701985 = 4276489) B4276489
theorem B3801323 : Blo 2251435 3801323 := bstep (se 1 (by rfl) ⟨2850992, by rfl⟩ : syracuseStep 3801323 = 5701985) B5701985
theorem B2534215 : Blo 2251435 2534215 := bstep (se 1 (by rfl) ⟨1900661, by rfl⟩ : syracuseStep 2534215 = 3801323) B3801323
theorem B3378953 : Blo 2251435 3378953 := bstep (se 2 (by rfl) ⟨1267107, by rfl⟩ : syracuseStep 3378953 = 2534215) B2534215
theorem B2252635 : Blo 2251435 2252635 := bstep (se 1 (by rfl) ⟨1689476, by rfl⟩ : syracuseStep 2252635 = 3378953) B3378953
theorem B11403989 : Blo 2251435 11403989 := bbase (se 7 (by rfl) ⟨133640, by rfl⟩ : syracuseStep 11403989 = 267281) (by norm_num)
theorem B7602659 : Blo 2251435 7602659 := bstep (se 1 (by rfl) ⟨5701994, by rfl⟩ : syracuseStep 7602659 = 11403989) B11403989
theorem B5068439 : Blo 2251435 5068439 := bstep (se 1 (by rfl) ⟨3801329, by rfl⟩ : syracuseStep 5068439 = 7602659) B7602659
theorem B3378959 : Blo 2251435 3378959 := bstep (se 1 (by rfl) ⟨2534219, by rfl⟩ : syracuseStep 3378959 = 5068439) B5068439
theorem B2252639 : Blo 2251435 2252639 := bstep (se 1 (by rfl) ⟨1689479, by rfl⟩ : syracuseStep 2252639 = 3378959) B3378959
theorem B3378965 : Blo 2251435 3378965 := bbase (se 6 (by rfl) ⟨79194, by rfl⟩ : syracuseStep 3378965 = 158389) (by norm_num)
theorem B2252643 : Blo 2251435 2252643 := bstep (se 1 (by rfl) ⟨1689482, by rfl⟩ : syracuseStep 2252643 = 3378965) B3378965
theorem B3044509 : Blo 2251435 3044509 := bbase (se 3 (by rfl) ⟨570845, by rfl⟩ : syracuseStep 3044509 = 1141691) (by norm_num)
theorem B64949525 : Blo 2251435 64949525 := bstep (se 6 (by rfl) ⟨1522254, by rfl⟩ : syracuseStep 64949525 = 3044509) B3044509
theorem B43299683 : Blo 2251435 43299683 := bstep (se 1 (by rfl) ⟨32474762, by rfl⟩ : syracuseStep 43299683 = 64949525) B64949525
theorem B28866455 : Blo 2251435 28866455 := bstep (se 1 (by rfl) ⟨21649841, by rfl⟩ : syracuseStep 28866455 = 43299683) B43299683
theorem B19244303 : Blo 2251435 19244303 := bstep (se 1 (by rfl) ⟨14433227, by rfl⟩ : syracuseStep 19244303 = 28866455) B28866455
theorem B12829535 : Blo 2251435 12829535 := bstep (se 1 (by rfl) ⟨9622151, by rfl⟩ : syracuseStep 12829535 = 19244303) B19244303
theorem B8553023 : Blo 2251435 8553023 := bstep (se 1 (by rfl) ⟨6414767, by rfl⟩ : syracuseStep 8553023 = 12829535) B12829535
theorem B5702015 : Blo 2251435 5702015 := bstep (se 1 (by rfl) ⟨4276511, by rfl⟩ : syracuseStep 5702015 = 8553023) B8553023
theorem B3801343 : Blo 2251435 3801343 := bstep (se 1 (by rfl) ⟨2851007, by rfl⟩ : syracuseStep 3801343 = 5702015) B5702015
theorem B5068457 : Blo 2251435 5068457 := bstep (se 2 (by rfl) ⟨1900671, by rfl⟩ : syracuseStep 5068457 = 3801343) B3801343
theorem B3378971 : Blo 2251435 3378971 := bstep (se 1 (by rfl) ⟨2534228, by rfl⟩ : syracuseStep 3378971 = 5068457) B5068457
theorem B2252647 : Blo 2251435 2252647 := bstep (se 1 (by rfl) ⟨1689485, by rfl⟩ : syracuseStep 2252647 = 3378971) B3378971
theorem B2534233 : Blo 2251435 2534233 := bbase (se 2 (by rfl) ⟨950337, by rfl⟩ : syracuseStep 2534233 = 1900675) (by norm_num)
theorem B3378977 : Blo 2251435 3378977 := bstep (se 2 (by rfl) ⟨1267116, by rfl⟩ : syracuseStep 3378977 = 2534233) B2534233
theorem B2252651 : Blo 2251435 2252651 := bstep (se 1 (by rfl) ⟨1689488, by rfl⟩ : syracuseStep 2252651 = 3378977) B3378977
theorem B4811093 : Blo 2251435 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B3207395 : Blo 2251435 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B8553053 : Blo 2251435 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B5702035 : Blo 2251435 5702035 := bstep (se 1 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 5702035 = 8553053) B8553053
theorem B7602713 : Blo 2251435 7602713 := bstep (se 2 (by rfl) ⟨2851017, by rfl⟩ : syracuseStep 7602713 = 5702035) B5702035
theorem B5068475 : Blo 2251435 5068475 := bstep (se 1 (by rfl) ⟨3801356, by rfl⟩ : syracuseStep 5068475 = 7602713) B7602713
theorem B3378983 : Blo 2251435 3378983 := bstep (se 1 (by rfl) ⟨2534237, by rfl⟩ : syracuseStep 3378983 = 5068475) B5068475
theorem B2252655 : Blo 2251435 2252655 := bstep (se 1 (by rfl) ⟨1689491, by rfl⟩ : syracuseStep 2252655 = 3378983) B3378983
theorem B3378989 : Blo 2251435 3378989 := bbase (se 3 (by rfl) ⟨633560, by rfl⟩ : syracuseStep 3378989 = 1267121) (by norm_num)
theorem B2252659 : Blo 2251435 2252659 := bstep (se 1 (by rfl) ⟨1689494, by rfl⟩ : syracuseStep 2252659 = 3378989) B3378989
theorem B5068493 : Blo 2251435 5068493 := bbase (se 3 (by rfl) ⟨950342, by rfl⟩ : syracuseStep 5068493 = 1900685) (by norm_num)
theorem B3378995 : Blo 2251435 3378995 := bstep (se 1 (by rfl) ⟨2534246, by rfl⟩ : syracuseStep 3378995 = 5068493) B5068493
theorem B2252663 : Blo 2251435 2252663 := bstep (se 1 (by rfl) ⟨1689497, by rfl⟩ : syracuseStep 2252663 = 3378995) B3378995
theorem B2851033 : Blo 2251435 2851033 := bbase (se 2 (by rfl) ⟨1069137, by rfl⟩ : syracuseStep 2851033 = 2138275) (by norm_num)
theorem B3801377 : Blo 2251435 3801377 := bstep (se 2 (by rfl) ⟨1425516, by rfl⟩ : syracuseStep 3801377 = 2851033) B2851033
theorem B2534251 : Blo 2251435 2534251 := bstep (se 1 (by rfl) ⟨1900688, by rfl⟩ : syracuseStep 2534251 = 3801377) B3801377
theorem B3379001 : Blo 2251435 3379001 := bstep (se 2 (by rfl) ⟨1267125, by rfl⟩ : syracuseStep 3379001 = 2534251) B2534251
theorem B2252667 : Blo 2251435 2252667 := bstep (se 1 (by rfl) ⟨1689500, by rfl⟩ : syracuseStep 2252667 = 3379001) B3379001
theorem B4059389 : Blo 2251435 4059389 := bbase (se 3 (by rfl) ⟨761135, by rfl⟩ : syracuseStep 4059389 = 1522271) (by norm_num)
theorem B2706259 : Blo 2251435 2706259 := bstep (se 1 (by rfl) ⟨2029694, by rfl⟩ : syracuseStep 2706259 = 4059389) B4059389
theorem B3608345 : Blo 2251435 3608345 := bstep (se 2 (by rfl) ⟨1353129, by rfl⟩ : syracuseStep 3608345 = 2706259) B2706259
theorem B9622253 : Blo 2251435 9622253 := bstep (se 3 (by rfl) ⟨1804172, by rfl⟩ : syracuseStep 9622253 = 3608345) B3608345
theorem B25659341 : Blo 2251435 25659341 := bstep (se 3 (by rfl) ⟨4811126, by rfl⟩ : syracuseStep 25659341 = 9622253) B9622253
theorem B17106227 : Blo 2251435 17106227 := bstep (se 1 (by rfl) ⟨12829670, by rfl⟩ : syracuseStep 17106227 = 25659341) B25659341
theorem B11404151 : Blo 2251435 11404151 := bstep (se 1 (by rfl) ⟨8553113, by rfl⟩ : syracuseStep 11404151 = 17106227) B17106227
theorem B7602767 : Blo 2251435 7602767 := bstep (se 1 (by rfl) ⟨5702075, by rfl⟩ : syracuseStep 7602767 = 11404151) B11404151
theorem B5068511 : Blo 2251435 5068511 := bstep (se 1 (by rfl) ⟨3801383, by rfl⟩ : syracuseStep 5068511 = 7602767) B7602767
theorem B3379007 : Blo 2251435 3379007 := bstep (se 1 (by rfl) ⟨2534255, by rfl⟩ : syracuseStep 3379007 = 5068511) B5068511
theorem B2252671 : Blo 2251435 2252671 := bstep (se 1 (by rfl) ⟨1689503, by rfl⟩ : syracuseStep 2252671 = 3379007) B3379007
theorem B3379013 : Blo 2251435 3379013 := bbase (se 4 (by rfl) ⟨316782, by rfl⟩ : syracuseStep 3379013 = 633565) (by norm_num)
theorem B2252675 : Blo 2251435 2252675 := bstep (se 1 (by rfl) ⟨1689506, by rfl⟩ : syracuseStep 2252675 = 3379013) B3379013
theorem B3801397 : Blo 2251435 3801397 := bbase (se 5 (by rfl) ⟨178190, by rfl⟩ : syracuseStep 3801397 = 356381) (by norm_num)
theorem B5068529 : Blo 2251435 5068529 := bstep (se 2 (by rfl) ⟨1900698, by rfl⟩ : syracuseStep 5068529 = 3801397) B3801397
theorem B3379019 : Blo 2251435 3379019 := bstep (se 1 (by rfl) ⟨2534264, by rfl⟩ : syracuseStep 3379019 = 5068529) B5068529
theorem B2252679 : Blo 2251435 2252679 := bstep (se 1 (by rfl) ⟨1689509, by rfl⟩ : syracuseStep 2252679 = 3379019) B3379019
theorem B2534269 : Blo 2251435 2534269 := bbase (se 3 (by rfl) ⟨475175, by rfl⟩ : syracuseStep 2534269 = 950351) (by norm_num)
theorem B3379025 : Blo 2251435 3379025 := bstep (se 2 (by rfl) ⟨1267134, by rfl⟩ : syracuseStep 3379025 = 2534269) B2534269
theorem B2252683 : Blo 2251435 2252683 := bstep (se 1 (by rfl) ⟨1689512, by rfl⟩ : syracuseStep 2252683 = 3379025) B3379025
theorem B7602821 : Blo 2251435 7602821 := bbase (se 4 (by rfl) ⟨712764, by rfl⟩ : syracuseStep 7602821 = 1425529) (by norm_num)
theorem B5068547 : Blo 2251435 5068547 := bstep (se 1 (by rfl) ⟨3801410, by rfl⟩ : syracuseStep 5068547 = 7602821) B7602821
theorem B3379031 : Blo 2251435 3379031 := bstep (se 1 (by rfl) ⟨2534273, by rfl⟩ : syracuseStep 3379031 = 5068547) B5068547
theorem B2252687 : Blo 2251435 2252687 := bstep (se 1 (by rfl) ⟨1689515, by rfl⟩ : syracuseStep 2252687 = 3379031) B3379031
theorem B3379037 : Blo 2251435 3379037 := bbase (se 3 (by rfl) ⟨633569, by rfl⟩ : syracuseStep 3379037 = 1267139) (by norm_num)
theorem B2252691 : Blo 2251435 2252691 := bstep (se 1 (by rfl) ⟨1689518, by rfl⟩ : syracuseStep 2252691 = 3379037) B3379037
theorem B5068565 : Blo 2251435 5068565 := bbase (se 6 (by rfl) ⟨118794, by rfl⟩ : syracuseStep 5068565 = 237589) (by norm_num)
theorem B3379043 : Blo 2251435 3379043 := bstep (se 1 (by rfl) ⟨2534282, by rfl⟩ : syracuseStep 3379043 = 5068565) B5068565
theorem B2252695 : Blo 2251435 2252695 := bstep (se 1 (by rfl) ⟨1689521, by rfl⟩ : syracuseStep 2252695 = 3379043) B3379043
theorem B8553221 : Blo 2251435 8553221 := bbase (se 4 (by rfl) ⟨801864, by rfl⟩ : syracuseStep 8553221 = 1603729) (by norm_num)
theorem B5702147 : Blo 2251435 5702147 := bstep (se 1 (by rfl) ⟨4276610, by rfl⟩ : syracuseStep 5702147 = 8553221) B8553221
theorem B3801431 : Blo 2251435 3801431 := bstep (se 1 (by rfl) ⟨2851073, by rfl⟩ : syracuseStep 3801431 = 5702147) B5702147
theorem B2534287 : Blo 2251435 2534287 := bstep (se 1 (by rfl) ⟨1900715, by rfl⟩ : syracuseStep 2534287 = 3801431) B3801431
theorem B3379049 : Blo 2251435 3379049 := bstep (se 2 (by rfl) ⟨1267143, by rfl⟩ : syracuseStep 3379049 = 2534287) B2534287
theorem B2252699 : Blo 2251435 2252699 := bstep (se 1 (by rfl) ⟨1689524, by rfl⟩ : syracuseStep 2252699 = 3379049) B3379049
theorem B5779957 : Blo 2251435 5779957 := bbase (se 5 (by rfl) ⟨270935, by rfl⟩ : syracuseStep 5779957 = 541871) (by norm_num)
theorem B7706609 : Blo 2251435 7706609 := bstep (se 2 (by rfl) ⟨2889978, by rfl⟩ : syracuseStep 7706609 = 5779957) B5779957
theorem B5137739 : Blo 2251435 5137739 := bstep (se 1 (by rfl) ⟨3853304, by rfl⟩ : syracuseStep 5137739 = 7706609) B7706609
theorem B3425159 : Blo 2251435 3425159 := bstep (se 1 (by rfl) ⟨2568869, by rfl⟩ : syracuseStep 3425159 = 5137739) B5137739
theorem B2283439 : Blo 2251435 2283439 := bstep (se 1 (by rfl) ⟨1712579, by rfl⟩ : syracuseStep 2283439 = 3425159) B3425159
theorem B3044585 : Blo 2251435 3044585 := bstep (se 2 (by rfl) ⟨1141719, by rfl⟩ : syracuseStep 3044585 = 2283439) B2283439
theorem B8118893 : Blo 2251435 8118893 := bstep (se 3 (by rfl) ⟨1522292, by rfl⟩ : syracuseStep 8118893 = 3044585) B3044585
theorem B5412595 : Blo 2251435 5412595 := bstep (se 1 (by rfl) ⟨4059446, by rfl⟩ : syracuseStep 5412595 = 8118893) B8118893
theorem B7216793 : Blo 2251435 7216793 := bstep (se 2 (by rfl) ⟨2706297, by rfl⟩ : syracuseStep 7216793 = 5412595) B5412595
theorem B4811195 : Blo 2251435 4811195 := bstep (se 1 (by rfl) ⟨3608396, by rfl⟩ : syracuseStep 4811195 = 7216793) B7216793
theorem B12829853 : Blo 2251435 12829853 := bstep (se 3 (by rfl) ⟨2405597, by rfl⟩ : syracuseStep 12829853 = 4811195) B4811195
theorem B8553235 : Blo 2251435 8553235 := bstep (se 1 (by rfl) ⟨6414926, by rfl⟩ : syracuseStep 8553235 = 12829853) B12829853
theorem B11404313 : Blo 2251435 11404313 := bstep (se 2 (by rfl) ⟨4276617, by rfl⟩ : syracuseStep 11404313 = 8553235) B8553235
theorem B7602875 : Blo 2251435 7602875 := bstep (se 1 (by rfl) ⟨5702156, by rfl⟩ : syracuseStep 7602875 = 11404313) B11404313
theorem B5068583 : Blo 2251435 5068583 := bstep (se 1 (by rfl) ⟨3801437, by rfl⟩ : syracuseStep 5068583 = 7602875) B7602875
theorem B3379055 : Blo 2251435 3379055 := bstep (se 1 (by rfl) ⟨2534291, by rfl⟩ : syracuseStep 3379055 = 5068583) B5068583
theorem B2252703 : Blo 2251435 2252703 := bstep (se 1 (by rfl) ⟨1689527, by rfl⟩ : syracuseStep 2252703 = 3379055) B3379055
theorem B3379061 : Blo 2251435 3379061 := bbase (se 5 (by rfl) ⟨158393, by rfl⟩ : syracuseStep 3379061 = 316787) (by norm_num)
theorem B2252707 : Blo 2251435 2252707 := bstep (se 1 (by rfl) ⟨1689530, by rfl⟩ : syracuseStep 2252707 = 3379061) B3379061
theorem B4811213 : Blo 2251435 4811213 := bbase (se 3 (by rfl) ⟨902102, by rfl⟩ : syracuseStep 4811213 = 1804205) (by norm_num)
theorem B3207475 : Blo 2251435 3207475 := bstep (se 1 (by rfl) ⟨2405606, by rfl⟩ : syracuseStep 3207475 = 4811213) B4811213
theorem B4276633 : Blo 2251435 4276633 := bstep (se 2 (by rfl) ⟨1603737, by rfl⟩ : syracuseStep 4276633 = 3207475) B3207475
theorem B5702177 : Blo 2251435 5702177 := bstep (se 2 (by rfl) ⟨2138316, by rfl⟩ : syracuseStep 5702177 = 4276633) B4276633
theorem B3801451 : Blo 2251435 3801451 := bstep (se 1 (by rfl) ⟨2851088, by rfl⟩ : syracuseStep 3801451 = 5702177) B5702177
theorem B5068601 : Blo 2251435 5068601 := bstep (se 2 (by rfl) ⟨1900725, by rfl⟩ : syracuseStep 5068601 = 3801451) B3801451
theorem B3379067 : Blo 2251435 3379067 := bstep (se 1 (by rfl) ⟨2534300, by rfl⟩ : syracuseStep 3379067 = 5068601) B5068601
theorem B2252711 : Blo 2251435 2252711 := bstep (se 1 (by rfl) ⟨1689533, by rfl⟩ : syracuseStep 2252711 = 3379067) B3379067
theorem B2534305 : Blo 2251435 2534305 := bbase (se 2 (by rfl) ⟨950364, by rfl⟩ : syracuseStep 2534305 = 1900729) (by norm_num)
theorem B3379073 : Blo 2251435 3379073 := bstep (se 2 (by rfl) ⟨1267152, by rfl⟩ : syracuseStep 3379073 = 2534305) B2534305
theorem B2252715 : Blo 2251435 2252715 := bstep (se 1 (by rfl) ⟨1689536, by rfl⟩ : syracuseStep 2252715 = 3379073) B3379073
theorem B5702197 : Blo 2251435 5702197 := bbase (se 5 (by rfl) ⟨267290, by rfl⟩ : syracuseStep 5702197 = 534581) (by norm_num)
theorem B7602929 : Blo 2251435 7602929 := bstep (se 2 (by rfl) ⟨2851098, by rfl⟩ : syracuseStep 7602929 = 5702197) B5702197
theorem B5068619 : Blo 2251435 5068619 := bstep (se 1 (by rfl) ⟨3801464, by rfl⟩ : syracuseStep 5068619 = 7602929) B7602929
theorem B3379079 : Blo 2251435 3379079 := bstep (se 1 (by rfl) ⟨2534309, by rfl⟩ : syracuseStep 3379079 = 5068619) B5068619
theorem B2252719 : Blo 2251435 2252719 := bstep (se 1 (by rfl) ⟨1689539, by rfl⟩ : syracuseStep 2252719 = 3379079) B3379079
theorem B3379085 : Blo 2251435 3379085 := bbase (se 3 (by rfl) ⟨633578, by rfl⟩ : syracuseStep 3379085 = 1267157) (by norm_num)
theorem B2252723 : Blo 2251435 2252723 := bstep (se 1 (by rfl) ⟨1689542, by rfl⟩ : syracuseStep 2252723 = 3379085) B3379085
theorem B5068637 : Blo 2251435 5068637 := bbase (se 3 (by rfl) ⟨950369, by rfl⟩ : syracuseStep 5068637 = 1900739) (by norm_num)
theorem B3379091 : Blo 2251435 3379091 := bstep (se 1 (by rfl) ⟨2534318, by rfl⟩ : syracuseStep 3379091 = 5068637) B5068637
theorem B2252727 : Blo 2251435 2252727 := bstep (se 1 (by rfl) ⟨1689545, by rfl⟩ : syracuseStep 2252727 = 3379091) B3379091
theorem B3801485 : Blo 2251435 3801485 := bbase (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) (by norm_num)
theorem B2534323 : Blo 2251435 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B3379097 : Blo 2251435 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B2252731 : Blo 2251435 2252731 := bstep (se 1 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 2252731 = 3379097) B3379097
theorem B39547541 : Blo 2251435 39547541 := bbase (se 6 (by rfl) ⟨926895, by rfl⟩ : syracuseStep 39547541 = 1853791) (by norm_num)
theorem B26365027 : Blo 2251435 26365027 := bstep (se 1 (by rfl) ⟨19773770, by rfl⟩ : syracuseStep 26365027 = 39547541) B39547541
theorem B35153369 : Blo 2251435 35153369 := bstep (se 2 (by rfl) ⟨13182513, by rfl⟩ : syracuseStep 35153369 = 26365027) B26365027
theorem B23435579 : Blo 2251435 23435579 := bstep (se 1 (by rfl) ⟨17576684, by rfl⟩ : syracuseStep 23435579 = 35153369) B35153369
theorem B62494877 : Blo 2251435 62494877 := bstep (se 3 (by rfl) ⟨11717789, by rfl⟩ : syracuseStep 62494877 = 23435579) B23435579
theorem B41663251 : Blo 2251435 41663251 := bstep (se 1 (by rfl) ⟨31247438, by rfl⟩ : syracuseStep 41663251 = 62494877) B62494877
theorem B55551001 : Blo 2251435 55551001 := bstep (se 2 (by rfl) ⟨20831625, by rfl⟩ : syracuseStep 55551001 = 41663251) B41663251
theorem B74068001 : Blo 2251435 74068001 := bstep (se 2 (by rfl) ⟨27775500, by rfl⟩ : syracuseStep 74068001 = 55551001) B55551001
theorem B49378667 : Blo 2251435 49378667 := bstep (se 1 (by rfl) ⟨37034000, by rfl⟩ : syracuseStep 49378667 = 74068001) B74068001
theorem B131676445 : Blo 2251435 131676445 := bstep (se 3 (by rfl) ⟨24689333, by rfl⟩ : syracuseStep 131676445 = 49378667) B49378667
theorem B702274373 : Blo 2251435 702274373 := bstep (se 4 (by rfl) ⟨65838222, by rfl⟩ : syracuseStep 702274373 = 131676445) B131676445
theorem B468182915 : Blo 2251435 468182915 := bstep (se 1 (by rfl) ⟨351137186, by rfl⟩ : syracuseStep 468182915 = 702274373) B702274373
theorem B312121943 : Blo 2251435 312121943 := bstep (se 1 (by rfl) ⟨234091457, by rfl⟩ : syracuseStep 312121943 = 468182915) B468182915
theorem B208081295 : Blo 2251435 208081295 := bstep (se 1 (by rfl) ⟨156060971, by rfl⟩ : syracuseStep 208081295 = 312121943) B312121943
theorem B138720863 : Blo 2251435 138720863 := bstep (se 1 (by rfl) ⟨104040647, by rfl⟩ : syracuseStep 138720863 = 208081295) B208081295
theorem B92480575 : Blo 2251435 92480575 := bstep (se 1 (by rfl) ⟨69360431, by rfl⟩ : syracuseStep 92480575 = 138720863) B138720863
theorem B123307433 : Blo 2251435 123307433 := bstep (se 2 (by rfl) ⟨46240287, by rfl⟩ : syracuseStep 123307433 = 92480575) B92480575
theorem B82204955 : Blo 2251435 82204955 := bstep (se 1 (by rfl) ⟨61653716, by rfl⟩ : syracuseStep 82204955 = 123307433) B123307433
theorem B54803303 : Blo 2251435 54803303 := bstep (se 1 (by rfl) ⟨41102477, by rfl⟩ : syracuseStep 54803303 = 82204955) B82204955
theorem B36535535 : Blo 2251435 36535535 := bstep (se 1 (by rfl) ⟨27401651, by rfl⟩ : syracuseStep 36535535 = 54803303) B54803303
theorem B24357023 : Blo 2251435 24357023 := bstep (se 1 (by rfl) ⟨18267767, by rfl⟩ : syracuseStep 24357023 = 36535535) B36535535
theorem B16238015 : Blo 2251435 16238015 := bstep (se 1 (by rfl) ⟨12178511, by rfl⟩ : syracuseStep 16238015 = 24357023) B24357023
theorem B10825343 : Blo 2251435 10825343 := bstep (se 1 (by rfl) ⟨8119007, by rfl⟩ : syracuseStep 10825343 = 16238015) B16238015
theorem B7216895 : Blo 2251435 7216895 := bstep (se 1 (by rfl) ⟨5412671, by rfl⟩ : syracuseStep 7216895 = 10825343) B10825343
theorem B19245053 : Blo 2251435 19245053 := bstep (se 3 (by rfl) ⟨3608447, by rfl⟩ : syracuseStep 19245053 = 7216895) B7216895
theorem B12830035 : Blo 2251435 12830035 := bstep (se 1 (by rfl) ⟨9622526, by rfl⟩ : syracuseStep 12830035 = 19245053) B19245053
theorem B17106713 : Blo 2251435 17106713 := bstep (se 2 (by rfl) ⟨6415017, by rfl⟩ : syracuseStep 17106713 = 12830035) B12830035
theorem B11404475 : Blo 2251435 11404475 := bstep (se 1 (by rfl) ⟨8553356, by rfl⟩ : syracuseStep 11404475 = 17106713) B17106713
theorem B7602983 : Blo 2251435 7602983 := bstep (se 1 (by rfl) ⟨5702237, by rfl⟩ : syracuseStep 7602983 = 11404475) B11404475
theorem B5068655 : Blo 2251435 5068655 := bstep (se 1 (by rfl) ⟨3801491, by rfl⟩ : syracuseStep 5068655 = 7602983) B7602983
theorem B3379103 : Blo 2251435 3379103 := bstep (se 1 (by rfl) ⟨2534327, by rfl⟩ : syracuseStep 3379103 = 5068655) B5068655
theorem B2252735 : Blo 2251435 2252735 := bstep (se 1 (by rfl) ⟨1689551, by rfl⟩ : syracuseStep 2252735 = 3379103) B3379103
theorem B3379109 : Blo 2251435 3379109 := bbase (se 4 (by rfl) ⟨316791, by rfl⟩ : syracuseStep 3379109 = 633583) (by norm_num)
theorem B2252739 : Blo 2251435 2252739 := bstep (se 1 (by rfl) ⟨1689554, by rfl⟩ : syracuseStep 2252739 = 3379109) B3379109
theorem B2851129 : Blo 2251435 2851129 := bbase (se 2 (by rfl) ⟨1069173, by rfl⟩ : syracuseStep 2851129 = 2138347) (by norm_num)
theorem B3801505 : Blo 2251435 3801505 := bstep (se 2 (by rfl) ⟨1425564, by rfl⟩ : syracuseStep 3801505 = 2851129) B2851129
theorem B5068673 : Blo 2251435 5068673 := bstep (se 2 (by rfl) ⟨1900752, by rfl⟩ : syracuseStep 5068673 = 3801505) B3801505
theorem B3379115 : Blo 2251435 3379115 := bstep (se 1 (by rfl) ⟨2534336, by rfl⟩ : syracuseStep 3379115 = 5068673) B5068673
theorem B2252743 : Blo 2251435 2252743 := bstep (se 1 (by rfl) ⟨1689557, by rfl⟩ : syracuseStep 2252743 = 3379115) B3379115
theorem B2534341 : Blo 2251435 2534341 := bbase (se 4 (by rfl) ⟨237594, by rfl⟩ : syracuseStep 2534341 = 475189) (by norm_num)
theorem B3379121 : Blo 2251435 3379121 := bstep (se 2 (by rfl) ⟨1267170, by rfl⟩ : syracuseStep 3379121 = 2534341) B2534341
theorem B2252747 : Blo 2251435 2252747 := bstep (se 1 (by rfl) ⟨1689560, by rfl⟩ : syracuseStep 2252747 = 3379121) B3379121
theorem B4276709 : Blo 2251435 4276709 := bbase (se 4 (by rfl) ⟨400941, by rfl⟩ : syracuseStep 4276709 = 801883) (by norm_num)
theorem B2851139 : Blo 2251435 2851139 := bstep (se 1 (by rfl) ⟨2138354, by rfl⟩ : syracuseStep 2851139 = 4276709) B4276709
theorem B7603037 : Blo 2251435 7603037 := bstep (se 3 (by rfl) ⟨1425569, by rfl⟩ : syracuseStep 7603037 = 2851139) B2851139
theorem B5068691 : Blo 2251435 5068691 := bstep (se 1 (by rfl) ⟨3801518, by rfl⟩ : syracuseStep 5068691 = 7603037) B7603037
theorem B3379127 : Blo 2251435 3379127 := bstep (se 1 (by rfl) ⟨2534345, by rfl⟩ : syracuseStep 3379127 = 5068691) B5068691
theorem B2252751 : Blo 2251435 2252751 := bstep (se 1 (by rfl) ⟨1689563, by rfl⟩ : syracuseStep 2252751 = 3379127) B3379127
theorem B3379133 : Blo 2251435 3379133 := bbase (se 3 (by rfl) ⟨633587, by rfl⟩ : syracuseStep 3379133 = 1267175) (by norm_num)
theorem B2252755 : Blo 2251435 2252755 := bstep (se 1 (by rfl) ⟨1689566, by rfl⟩ : syracuseStep 2252755 = 3379133) B3379133
theorem B5068709 : Blo 2251435 5068709 := bbase (se 4 (by rfl) ⟨475191, by rfl⟩ : syracuseStep 5068709 = 950383) (by norm_num)
theorem B3379139 : Blo 2251435 3379139 := bstep (se 1 (by rfl) ⟨2534354, by rfl⟩ : syracuseStep 3379139 = 5068709) B5068709
theorem B2252759 : Blo 2251435 2252759 := bstep (se 1 (by rfl) ⟨1689569, by rfl⟩ : syracuseStep 2252759 = 3379139) B3379139
theorem B5702309 : Blo 2251435 5702309 := bbase (se 4 (by rfl) ⟨534591, by rfl⟩ : syracuseStep 5702309 = 1069183) (by norm_num)
theorem B3801539 : Blo 2251435 3801539 := bstep (se 1 (by rfl) ⟨2851154, by rfl⟩ : syracuseStep 3801539 = 5702309) B5702309
theorem B2534359 : Blo 2251435 2534359 := bstep (se 1 (by rfl) ⟨1900769, by rfl⟩ : syracuseStep 2534359 = 3801539) B3801539
theorem B3379145 : Blo 2251435 3379145 := bstep (se 2 (by rfl) ⟨1267179, by rfl⟩ : syracuseStep 3379145 = 2534359) B2534359
theorem B2252763 : Blo 2251435 2252763 := bstep (se 1 (by rfl) ⟨1689572, by rfl⟩ : syracuseStep 2252763 = 3379145) B3379145
theorem B6415109 : Blo 2251435 6415109 := bbase (se 4 (by rfl) ⟨601416, by rfl⟩ : syracuseStep 6415109 = 1202833) (by norm_num)
theorem B4276739 : Blo 2251435 4276739 := bstep (se 1 (by rfl) ⟨3207554, by rfl⟩ : syracuseStep 4276739 = 6415109) B6415109
theorem B11404637 : Blo 2251435 11404637 := bstep (se 3 (by rfl) ⟨2138369, by rfl⟩ : syracuseStep 11404637 = 4276739) B4276739
theorem B7603091 : Blo 2251435 7603091 := bstep (se 1 (by rfl) ⟨5702318, by rfl⟩ : syracuseStep 7603091 = 11404637) B11404637
theorem B5068727 : Blo 2251435 5068727 := bstep (se 1 (by rfl) ⟨3801545, by rfl⟩ : syracuseStep 5068727 = 7603091) B7603091
theorem B3379151 : Blo 2251435 3379151 := bstep (se 1 (by rfl) ⟨2534363, by rfl⟩ : syracuseStep 3379151 = 5068727) B5068727
theorem B2252767 : Blo 2251435 2252767 := bstep (se 1 (by rfl) ⟨1689575, by rfl⟩ : syracuseStep 2252767 = 3379151) B3379151
theorem B3379157 : Blo 2251435 3379157 := bbase (se 7 (by rfl) ⟨39599, by rfl⟩ : syracuseStep 3379157 = 79199) (by norm_num)
theorem B2252771 : Blo 2251435 2252771 := bstep (se 1 (by rfl) ⟨1689578, by rfl⟩ : syracuseStep 2252771 = 3379157) B3379157
theorem B8553509 : Blo 2251435 8553509 := bbase (se 4 (by rfl) ⟨801891, by rfl⟩ : syracuseStep 8553509 = 1603783) (by norm_num)
theorem B5702339 : Blo 2251435 5702339 := bstep (se 1 (by rfl) ⟨4276754, by rfl⟩ : syracuseStep 5702339 = 8553509) B8553509
theorem B3801559 : Blo 2251435 3801559 := bstep (se 1 (by rfl) ⟨2851169, by rfl⟩ : syracuseStep 3801559 = 5702339) B5702339
theorem B5068745 : Blo 2251435 5068745 := bstep (se 2 (by rfl) ⟨1900779, by rfl⟩ : syracuseStep 5068745 = 3801559) B3801559
theorem B3379163 : Blo 2251435 3379163 := bstep (se 1 (by rfl) ⟨2534372, by rfl⟩ : syracuseStep 3379163 = 5068745) B5068745
theorem B2252775 : Blo 2251435 2252775 := bstep (se 1 (by rfl) ⟨1689581, by rfl⟩ : syracuseStep 2252775 = 3379163) B3379163
theorem B2534377 : Blo 2251435 2534377 := bbase (se 2 (by rfl) ⟨950391, by rfl⟩ : syracuseStep 2534377 = 1900783) (by norm_num)
theorem B3379169 : Blo 2251435 3379169 := bstep (se 2 (by rfl) ⟨1267188, by rfl⟩ : syracuseStep 3379169 = 2534377) B2534377
theorem B2252779 : Blo 2251435 2252779 := bstep (se 1 (by rfl) ⟨1689584, by rfl⟩ : syracuseStep 2252779 = 3379169) B3379169
theorem B3608525 : Blo 2251435 3608525 := bbase (se 3 (by rfl) ⟨676598, by rfl⟩ : syracuseStep 3608525 = 1353197) (by norm_num)
theorem B2405683 : Blo 2251435 2405683 := bstep (se 1 (by rfl) ⟨1804262, by rfl⟩ : syracuseStep 2405683 = 3608525) B3608525
theorem B12830309 : Blo 2251435 12830309 := bstep (se 4 (by rfl) ⟨1202841, by rfl⟩ : syracuseStep 12830309 = 2405683) B2405683
theorem B8553539 : Blo 2251435 8553539 := bstep (se 1 (by rfl) ⟨6415154, by rfl⟩ : syracuseStep 8553539 = 12830309) B12830309
theorem B5702359 : Blo 2251435 5702359 := bstep (se 1 (by rfl) ⟨4276769, by rfl⟩ : syracuseStep 5702359 = 8553539) B8553539
theorem B7603145 : Blo 2251435 7603145 := bstep (se 2 (by rfl) ⟨2851179, by rfl⟩ : syracuseStep 7603145 = 5702359) B5702359
theorem B5068763 : Blo 2251435 5068763 := bstep (se 1 (by rfl) ⟨3801572, by rfl⟩ : syracuseStep 5068763 = 7603145) B7603145
theorem B3379175 : Blo 2251435 3379175 := bstep (se 1 (by rfl) ⟨2534381, by rfl⟩ : syracuseStep 3379175 = 5068763) B5068763
theorem B2252783 : Blo 2251435 2252783 := bstep (se 1 (by rfl) ⟨1689587, by rfl⟩ : syracuseStep 2252783 = 3379175) B3379175
theorem B3379181 : Blo 2251435 3379181 := bbase (se 3 (by rfl) ⟨633596, by rfl⟩ : syracuseStep 3379181 = 1267193) (by norm_num)
theorem B2252787 : Blo 2251435 2252787 := bstep (se 1 (by rfl) ⟨1689590, by rfl⟩ : syracuseStep 2252787 = 3379181) B3379181
theorem B5068781 : Blo 2251435 5068781 := bbase (se 3 (by rfl) ⟨950396, by rfl⟩ : syracuseStep 5068781 = 1900793) (by norm_num)
theorem B3379187 : Blo 2251435 3379187 := bstep (se 1 (by rfl) ⟨2534390, by rfl⟩ : syracuseStep 3379187 = 5068781) B5068781
theorem B2252791 : Blo 2251435 2252791 := bstep (se 1 (by rfl) ⟨1689593, by rfl⟩ : syracuseStep 2252791 = 3379187) B3379187
theorem B2706409 : Blo 2251435 2706409 := bbase (se 2 (by rfl) ⟨1014903, by rfl⟩ : syracuseStep 2706409 = 2029807) (by norm_num)
theorem B3608545 : Blo 2251435 3608545 := bstep (se 2 (by rfl) ⟨1353204, by rfl⟩ : syracuseStep 3608545 = 2706409) B2706409
theorem B4811393 : Blo 2251435 4811393 := bstep (se 2 (by rfl) ⟨1804272, by rfl⟩ : syracuseStep 4811393 = 3608545) B3608545
theorem B3207595 : Blo 2251435 3207595 := bstep (se 1 (by rfl) ⟨2405696, by rfl⟩ : syracuseStep 3207595 = 4811393) B4811393
theorem B4276793 : Blo 2251435 4276793 := bstep (se 2 (by rfl) ⟨1603797, by rfl⟩ : syracuseStep 4276793 = 3207595) B3207595
theorem B2851195 : Blo 2251435 2851195 := bstep (se 1 (by rfl) ⟨2138396, by rfl⟩ : syracuseStep 2851195 = 4276793) B4276793
theorem B3801593 : Blo 2251435 3801593 := bstep (se 2 (by rfl) ⟨1425597, by rfl⟩ : syracuseStep 3801593 = 2851195) B2851195
theorem B2534395 : Blo 2251435 2534395 := bstep (se 1 (by rfl) ⟨1900796, by rfl⟩ : syracuseStep 2534395 = 3801593) B3801593
theorem B3379193 : Blo 2251435 3379193 := bstep (se 2 (by rfl) ⟨1267197, by rfl⟩ : syracuseStep 3379193 = 2534395) B2534395
theorem B2252795 : Blo 2251435 2252795 := bstep (se 1 (by rfl) ⟨1689596, by rfl⟩ : syracuseStep 2252795 = 3379193) B3379193
theorem B7706933 : Blo 2251435 7706933 := bbase (se 5 (by rfl) ⟨361262, by rfl⟩ : syracuseStep 7706933 = 722525) (by norm_num)
theorem B5137955 : Blo 2251435 5137955 := bstep (se 1 (by rfl) ⟨3853466, by rfl⟩ : syracuseStep 5137955 = 7706933) B7706933
theorem B54804853 : Blo 2251435 54804853 := bstep (se 5 (by rfl) ⟨2568977, by rfl⟩ : syracuseStep 54804853 = 5137955) B5137955
theorem B292292549 : Blo 2251435 292292549 := bstep (se 4 (by rfl) ⟨27402426, by rfl⟩ : syracuseStep 292292549 = 54804853) B54804853
theorem B194861699 : Blo 2251435 194861699 := bstep (se 1 (by rfl) ⟨146146274, by rfl⟩ : syracuseStep 194861699 = 292292549) B292292549
theorem B129907799 : Blo 2251435 129907799 := bstep (se 1 (by rfl) ⟨97430849, by rfl⟩ : syracuseStep 129907799 = 194861699) B194861699
theorem B86605199 : Blo 2251435 86605199 := bstep (se 1 (by rfl) ⟨64953899, by rfl⟩ : syracuseStep 86605199 = 129907799) B129907799
theorem B57736799 : Blo 2251435 57736799 := bstep (se 1 (by rfl) ⟨43302599, by rfl⟩ : syracuseStep 57736799 = 86605199) B86605199
theorem B38491199 : Blo 2251435 38491199 := bstep (se 1 (by rfl) ⟨28868399, by rfl⟩ : syracuseStep 38491199 = 57736799) B57736799
theorem B25660799 : Blo 2251435 25660799 := bstep (se 1 (by rfl) ⟨19245599, by rfl⟩ : syracuseStep 25660799 = 38491199) B38491199
theorem B17107199 : Blo 2251435 17107199 := bstep (se 1 (by rfl) ⟨12830399, by rfl⟩ : syracuseStep 17107199 = 25660799) B25660799
theorem B11404799 : Blo 2251435 11404799 := bstep (se 1 (by rfl) ⟨8553599, by rfl⟩ : syracuseStep 11404799 = 17107199) B17107199
theorem B7603199 : Blo 2251435 7603199 := bstep (se 1 (by rfl) ⟨5702399, by rfl⟩ : syracuseStep 7603199 = 11404799) B11404799
theorem B5068799 : Blo 2251435 5068799 := bstep (se 1 (by rfl) ⟨3801599, by rfl⟩ : syracuseStep 5068799 = 7603199) B7603199
theorem B3379199 : Blo 2251435 3379199 := bstep (se 1 (by rfl) ⟨2534399, by rfl⟩ : syracuseStep 3379199 = 5068799) B5068799
theorem B2252799 : Blo 2251435 2252799 := bstep (se 1 (by rfl) ⟨1689599, by rfl⟩ : syracuseStep 2252799 = 3379199) B3379199
theorem B3379205 : Blo 2251435 3379205 := bbase (se 4 (by rfl) ⟨316800, by rfl⟩ : syracuseStep 3379205 = 633601) (by norm_num)
theorem B2252803 : Blo 2251435 2252803 := bstep (se 1 (by rfl) ⟨1689602, by rfl⟩ : syracuseStep 2252803 = 3379205) B3379205
theorem B3801613 : Blo 2251435 3801613 := bbase (se 3 (by rfl) ⟨712802, by rfl⟩ : syracuseStep 3801613 = 1425605) (by norm_num)
theorem B5068817 : Blo 2251435 5068817 := bstep (se 2 (by rfl) ⟨1900806, by rfl⟩ : syracuseStep 5068817 = 3801613) B3801613
theorem B3379211 : Blo 2251435 3379211 := bstep (se 1 (by rfl) ⟨2534408, by rfl⟩ : syracuseStep 3379211 = 5068817) B5068817
theorem B2252807 : Blo 2251435 2252807 := bstep (se 1 (by rfl) ⟨1689605, by rfl⟩ : syracuseStep 2252807 = 3379211) B3379211
theorem B2534413 : Blo 2251435 2534413 := bbase (se 3 (by rfl) ⟨475202, by rfl⟩ : syracuseStep 2534413 = 950405) (by norm_num)
theorem B3379217 : Blo 2251435 3379217 := bstep (se 2 (by rfl) ⟨1267206, by rfl⟩ : syracuseStep 3379217 = 2534413) B2534413
theorem B2252811 : Blo 2251435 2252811 := bstep (se 1 (by rfl) ⟨1689608, by rfl⟩ : syracuseStep 2252811 = 3379217) B3379217
theorem B7603253 : Blo 2251435 7603253 := bbase (se 5 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 7603253 = 712805) (by norm_num)
theorem B5068835 : Blo 2251435 5068835 := bstep (se 1 (by rfl) ⟨3801626, by rfl⟩ : syracuseStep 5068835 = 7603253) B7603253
theorem B3379223 : Blo 2251435 3379223 := bstep (se 1 (by rfl) ⟨2534417, by rfl⟩ : syracuseStep 3379223 = 5068835) B5068835
theorem B2252815 : Blo 2251435 2252815 := bstep (se 1 (by rfl) ⟨1689611, by rfl⟩ : syracuseStep 2252815 = 3379223) B3379223
theorem B3379229 : Blo 2251435 3379229 := bbase (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) (by norm_num)
theorem B2252819 : Blo 2251435 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B5068853 : Blo 2251435 5068853 := bbase (se 5 (by rfl) ⟨237602, by rfl⟩ : syracuseStep 5068853 = 475205) (by norm_num)
theorem B3379235 : Blo 2251435 3379235 := bstep (se 1 (by rfl) ⟨2534426, by rfl⟩ : syracuseStep 3379235 = 5068853) B5068853
theorem B2252823 : Blo 2251435 2252823 := bstep (se 1 (by rfl) ⟨1689617, by rfl⟩ : syracuseStep 2252823 = 3379235) B3379235
theorem B5138021 : Blo 2251435 5138021 := bbase (se 4 (by rfl) ⟨481689, by rfl⟩ : syracuseStep 5138021 = 963379) (by norm_num)
theorem B3425347 : Blo 2251435 3425347 := bstep (se 1 (by rfl) ⟨2569010, by rfl⟩ : syracuseStep 3425347 = 5138021) B5138021
theorem B18268517 : Blo 2251435 18268517 := bstep (se 4 (by rfl) ⟨1712673, by rfl⟩ : syracuseStep 18268517 = 3425347) B3425347
theorem B12179011 : Blo 2251435 12179011 := bstep (se 1 (by rfl) ⟨9134258, by rfl⟩ : syracuseStep 12179011 = 18268517) B18268517
theorem B16238681 : Blo 2251435 16238681 := bstep (se 2 (by rfl) ⟨6089505, by rfl⟩ : syracuseStep 16238681 = 12179011) B12179011
theorem B10825787 : Blo 2251435 10825787 := bstep (se 1 (by rfl) ⟨8119340, by rfl⟩ : syracuseStep 10825787 = 16238681) B16238681
theorem B7217191 : Blo 2251435 7217191 := bstep (se 1 (by rfl) ⟨5412893, by rfl⟩ : syracuseStep 7217191 = 10825787) B10825787
theorem B9622921 : Blo 2251435 9622921 := bstep (se 2 (by rfl) ⟨3608595, by rfl⟩ : syracuseStep 9622921 = 7217191) B7217191
theorem B12830561 : Blo 2251435 12830561 := bstep (se 2 (by rfl) ⟨4811460, by rfl⟩ : syracuseStep 12830561 = 9622921) B9622921
theorem B8553707 : Blo 2251435 8553707 := bstep (se 1 (by rfl) ⟨6415280, by rfl⟩ : syracuseStep 8553707 = 12830561) B12830561
theorem B5702471 : Blo 2251435 5702471 := bstep (se 1 (by rfl) ⟨4276853, by rfl⟩ : syracuseStep 5702471 = 8553707) B8553707
theorem B3801647 : Blo 2251435 3801647 := bstep (se 1 (by rfl) ⟨2851235, by rfl⟩ : syracuseStep 3801647 = 5702471) B5702471
theorem B2534431 : Blo 2251435 2534431 := bstep (se 1 (by rfl) ⟨1900823, by rfl⟩ : syracuseStep 2534431 = 3801647) B3801647
theorem B3379241 : Blo 2251435 3379241 := bstep (se 2 (by rfl) ⟨1267215, by rfl⟩ : syracuseStep 3379241 = 2534431) B2534431
theorem B2252827 : Blo 2251435 2252827 := bstep (se 1 (by rfl) ⟨1689620, by rfl⟩ : syracuseStep 2252827 = 3379241) B3379241
theorem B4059677 : Blo 2251435 4059677 := bbase (se 3 (by rfl) ⟨761189, by rfl⟩ : syracuseStep 4059677 = 1522379) (by norm_num)
theorem B10825805 : Blo 2251435 10825805 := bstep (se 3 (by rfl) ⟨2029838, by rfl⟩ : syracuseStep 10825805 = 4059677) B4059677
theorem B7217203 : Blo 2251435 7217203 := bstep (se 1 (by rfl) ⟨5412902, by rfl⟩ : syracuseStep 7217203 = 10825805) B10825805
theorem B9622937 : Blo 2251435 9622937 := bstep (se 2 (by rfl) ⟨3608601, by rfl⟩ : syracuseStep 9622937 = 7217203) B7217203
theorem B6415291 : Blo 2251435 6415291 := bstep (se 1 (by rfl) ⟨4811468, by rfl⟩ : syracuseStep 6415291 = 9622937) B9622937
theorem B8553721 : Blo 2251435 8553721 := bstep (se 2 (by rfl) ⟨3207645, by rfl⟩ : syracuseStep 8553721 = 6415291) B6415291
theorem B11404961 : Blo 2251435 11404961 := bstep (se 2 (by rfl) ⟨4276860, by rfl⟩ : syracuseStep 11404961 = 8553721) B8553721
theorem B7603307 : Blo 2251435 7603307 := bstep (se 1 (by rfl) ⟨5702480, by rfl⟩ : syracuseStep 7603307 = 11404961) B11404961
theorem B5068871 : Blo 2251435 5068871 := bstep (se 1 (by rfl) ⟨3801653, by rfl⟩ : syracuseStep 5068871 = 7603307) B7603307
theorem B3379247 : Blo 2251435 3379247 := bstep (se 1 (by rfl) ⟨2534435, by rfl⟩ : syracuseStep 3379247 = 5068871) B5068871
theorem B2252831 : Blo 2251435 2252831 := bstep (se 1 (by rfl) ⟨1689623, by rfl⟩ : syracuseStep 2252831 = 3379247) B3379247
theorem B3379253 : Blo 2251435 3379253 := bbase (se 5 (by rfl) ⟨158402, by rfl⟩ : syracuseStep 3379253 = 316805) (by norm_num)
theorem B2252835 : Blo 2251435 2252835 := bstep (se 1 (by rfl) ⟨1689626, by rfl⟩ : syracuseStep 2252835 = 3379253) B3379253
theorem B5702501 : Blo 2251435 5702501 := bbase (se 4 (by rfl) ⟨534609, by rfl⟩ : syracuseStep 5702501 = 1069219) (by norm_num)
theorem B3801667 : Blo 2251435 3801667 := bstep (se 1 (by rfl) ⟨2851250, by rfl⟩ : syracuseStep 3801667 = 5702501) B5702501
theorem B5068889 : Blo 2251435 5068889 := bstep (se 2 (by rfl) ⟨1900833, by rfl⟩ : syracuseStep 5068889 = 3801667) B3801667
theorem B3379259 : Blo 2251435 3379259 := bstep (se 1 (by rfl) ⟨2534444, by rfl⟩ : syracuseStep 3379259 = 5068889) B5068889
theorem B2252839 : Blo 2251435 2252839 := bstep (se 1 (by rfl) ⟨1689629, by rfl⟩ : syracuseStep 2252839 = 3379259) B3379259
theorem B2534449 : Blo 2251435 2534449 := bbase (se 2 (by rfl) ⟨950418, by rfl⟩ : syracuseStep 2534449 = 1900837) (by norm_num)
theorem B3379265 : Blo 2251435 3379265 := bstep (se 2 (by rfl) ⟨1267224, by rfl⟩ : syracuseStep 3379265 = 2534449) B2534449
theorem B2252843 : Blo 2251435 2252843 := bstep (se 1 (by rfl) ⟨1689632, by rfl⟩ : syracuseStep 2252843 = 3379265) B3379265
theorem B19508597 : Blo 2251435 19508597 := bbase (se 5 (by rfl) ⟨914465, by rfl⟩ : syracuseStep 19508597 = 1828931) (by norm_num)
theorem B13005731 : Blo 2251435 13005731 := bstep (se 1 (by rfl) ⟨9754298, by rfl⟩ : syracuseStep 13005731 = 19508597) B19508597
theorem B8670487 : Blo 2251435 8670487 := bstep (se 1 (by rfl) ⟨6502865, by rfl⟩ : syracuseStep 8670487 = 13005731) B13005731
theorem B11560649 : Blo 2251435 11560649 := bstep (se 2 (by rfl) ⟨4335243, by rfl⟩ : syracuseStep 11560649 = 8670487) B8670487
theorem B30828397 : Blo 2251435 30828397 := bstep (se 3 (by rfl) ⟨5780324, by rfl⟩ : syracuseStep 30828397 = 11560649) B11560649
theorem B41104529 : Blo 2251435 41104529 := bstep (se 2 (by rfl) ⟨15414198, by rfl⟩ : syracuseStep 41104529 = 30828397) B30828397
theorem B27403019 : Blo 2251435 27403019 := bstep (se 1 (by rfl) ⟨20552264, by rfl⟩ : syracuseStep 27403019 = 41104529) B41104529
theorem B18268679 : Blo 2251435 18268679 := bstep (se 1 (by rfl) ⟨13701509, by rfl⟩ : syracuseStep 18268679 = 27403019) B27403019
theorem B12179119 : Blo 2251435 12179119 := bstep (se 1 (by rfl) ⟨9134339, by rfl⟩ : syracuseStep 12179119 = 18268679) B18268679
theorem B16238825 : Blo 2251435 16238825 := bstep (se 2 (by rfl) ⟨6089559, by rfl⟩ : syracuseStep 16238825 = 12179119) B12179119
theorem B10825883 : Blo 2251435 10825883 := bstep (se 1 (by rfl) ⟨8119412, by rfl⟩ : syracuseStep 10825883 = 16238825) B16238825
theorem B7217255 : Blo 2251435 7217255 := bstep (se 1 (by rfl) ⟨5412941, by rfl⟩ : syracuseStep 7217255 = 10825883) B10825883
theorem B4811503 : Blo 2251435 4811503 := bstep (se 1 (by rfl) ⟨3608627, by rfl⟩ : syracuseStep 4811503 = 7217255) B7217255
theorem B6415337 : Blo 2251435 6415337 := bstep (se 2 (by rfl) ⟨2405751, by rfl⟩ : syracuseStep 6415337 = 4811503) B4811503
theorem B4276891 : Blo 2251435 4276891 := bstep (se 1 (by rfl) ⟨3207668, by rfl⟩ : syracuseStep 4276891 = 6415337) B6415337
theorem B5702521 : Blo 2251435 5702521 := bstep (se 2 (by rfl) ⟨2138445, by rfl⟩ : syracuseStep 5702521 = 4276891) B4276891
theorem B7603361 : Blo 2251435 7603361 := bstep (se 2 (by rfl) ⟨2851260, by rfl⟩ : syracuseStep 7603361 = 5702521) B5702521
theorem B5068907 : Blo 2251435 5068907 := bstep (se 1 (by rfl) ⟨3801680, by rfl⟩ : syracuseStep 5068907 = 7603361) B7603361
theorem B3379271 : Blo 2251435 3379271 := bstep (se 1 (by rfl) ⟨2534453, by rfl⟩ : syracuseStep 3379271 = 5068907) B5068907
theorem B2252847 : Blo 2251435 2252847 := bstep (se 1 (by rfl) ⟨1689635, by rfl⟩ : syracuseStep 2252847 = 3379271) B3379271
theorem B3379277 : Blo 2251435 3379277 := bbase (se 3 (by rfl) ⟨633614, by rfl⟩ : syracuseStep 3379277 = 1267229) (by norm_num)
theorem B2252851 : Blo 2251435 2252851 := bstep (se 1 (by rfl) ⟨1689638, by rfl⟩ : syracuseStep 2252851 = 3379277) B3379277
theorem B5068925 : Blo 2251435 5068925 := bbase (se 3 (by rfl) ⟨950423, by rfl⟩ : syracuseStep 5068925 = 1900847) (by norm_num)
theorem B3379283 : Blo 2251435 3379283 := bstep (se 1 (by rfl) ⟨2534462, by rfl⟩ : syracuseStep 3379283 = 5068925) B5068925
theorem B2252855 : Blo 2251435 2252855 := bstep (se 1 (by rfl) ⟨1689641, by rfl⟩ : syracuseStep 2252855 = 3379283) B3379283
theorem B3801701 : Blo 2251435 3801701 := bbase (se 4 (by rfl) ⟨356409, by rfl⟩ : syracuseStep 3801701 = 712819) (by norm_num)
theorem B2534467 : Blo 2251435 2534467 := bstep (se 1 (by rfl) ⟨1900850, by rfl⟩ : syracuseStep 2534467 = 3801701) B3801701
theorem B3379289 : Blo 2251435 3379289 := bstep (se 2 (by rfl) ⟨1267233, by rfl⟩ : syracuseStep 3379289 = 2534467) B2534467
theorem B2252859 : Blo 2251435 2252859 := bstep (se 1 (by rfl) ⟨1689644, by rfl⟩ : syracuseStep 2252859 = 3379289) B3379289
theorem B3608653 : Blo 2251435 3608653 := bbase (se 3 (by rfl) ⟨676622, by rfl⟩ : syracuseStep 3608653 = 1353245) (by norm_num)
theorem B4811537 : Blo 2251435 4811537 := bstep (se 2 (by rfl) ⟨1804326, by rfl⟩ : syracuseStep 4811537 = 3608653) B3608653
theorem B3207691 : Blo 2251435 3207691 := bstep (se 1 (by rfl) ⟨2405768, by rfl⟩ : syracuseStep 3207691 = 4811537) B4811537
theorem B17107685 : Blo 2251435 17107685 := bstep (se 4 (by rfl) ⟨1603845, by rfl⟩ : syracuseStep 17107685 = 3207691) B3207691
theorem B11405123 : Blo 2251435 11405123 := bstep (se 1 (by rfl) ⟨8553842, by rfl⟩ : syracuseStep 11405123 = 17107685) B17107685
theorem B7603415 : Blo 2251435 7603415 := bstep (se 1 (by rfl) ⟨5702561, by rfl⟩ : syracuseStep 7603415 = 11405123) B11405123
theorem B5068943 : Blo 2251435 5068943 := bstep (se 1 (by rfl) ⟨3801707, by rfl⟩ : syracuseStep 5068943 = 7603415) B7603415
theorem B3379295 : Blo 2251435 3379295 := bstep (se 1 (by rfl) ⟨2534471, by rfl⟩ : syracuseStep 3379295 = 5068943) B5068943
theorem B2252863 : Blo 2251435 2252863 := bstep (se 1 (by rfl) ⟨1689647, by rfl⟩ : syracuseStep 2252863 = 3379295) B3379295
theorem B3379301 : Blo 2251435 3379301 := bbase (se 4 (by rfl) ⟨316809, by rfl⟩ : syracuseStep 3379301 = 633619) (by norm_num)
theorem B2252867 : Blo 2251435 2252867 := bstep (se 1 (by rfl) ⟨1689650, by rfl⟩ : syracuseStep 2252867 = 3379301) B3379301
theorem B7217333 : Blo 2251435 7217333 := bbase (se 5 (by rfl) ⟨338312, by rfl⟩ : syracuseStep 7217333 = 676625) (by norm_num)
theorem B4811555 : Blo 2251435 4811555 := bstep (se 1 (by rfl) ⟨3608666, by rfl⟩ : syracuseStep 4811555 = 7217333) B7217333
theorem B3207703 : Blo 2251435 3207703 := bstep (se 1 (by rfl) ⟨2405777, by rfl⟩ : syracuseStep 3207703 = 4811555) B4811555
theorem B4276937 : Blo 2251435 4276937 := bstep (se 2 (by rfl) ⟨1603851, by rfl⟩ : syracuseStep 4276937 = 3207703) B3207703
theorem B2851291 : Blo 2251435 2851291 := bstep (se 1 (by rfl) ⟨2138468, by rfl⟩ : syracuseStep 2851291 = 4276937) B4276937
theorem B3801721 : Blo 2251435 3801721 := bstep (se 2 (by rfl) ⟨1425645, by rfl⟩ : syracuseStep 3801721 = 2851291) B2851291
theorem B5068961 : Blo 2251435 5068961 := bstep (se 2 (by rfl) ⟨1900860, by rfl⟩ : syracuseStep 5068961 = 3801721) B3801721
theorem B3379307 : Blo 2251435 3379307 := bstep (se 1 (by rfl) ⟨2534480, by rfl⟩ : syracuseStep 3379307 = 5068961) B5068961
theorem B2252871 : Blo 2251435 2252871 := bstep (se 1 (by rfl) ⟨1689653, by rfl⟩ : syracuseStep 2252871 = 3379307) B3379307
theorem B2534485 : Blo 2251435 2534485 := bbase (se 8 (by rfl) ⟨14850, by rfl⟩ : syracuseStep 2534485 = 29701) (by norm_num)
theorem B3379313 : Blo 2251435 3379313 := bstep (se 2 (by rfl) ⟨1267242, by rfl⟩ : syracuseStep 3379313 = 2534485) B2534485
theorem B2252875 : Blo 2251435 2252875 := bstep (se 1 (by rfl) ⟨1689656, by rfl⟩ : syracuseStep 2252875 = 3379313) B3379313
theorem B2851301 : Blo 2251435 2851301 := bbase (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) (by norm_num)
theorem B7603469 : Blo 2251435 7603469 := bstep (se 3 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 7603469 = 2851301) B2851301
theorem B5068979 : Blo 2251435 5068979 := bstep (se 1 (by rfl) ⟨3801734, by rfl⟩ : syracuseStep 5068979 = 7603469) B7603469
theorem B3379319 : Blo 2251435 3379319 := bstep (se 1 (by rfl) ⟨2534489, by rfl⟩ : syracuseStep 3379319 = 5068979) B5068979
theorem B2252879 : Blo 2251435 2252879 := bstep (se 1 (by rfl) ⟨1689659, by rfl⟩ : syracuseStep 2252879 = 3379319) B3379319
theorem B3379325 : Blo 2251435 3379325 := bbase (se 3 (by rfl) ⟨633623, by rfl⟩ : syracuseStep 3379325 = 1267247) (by norm_num)
theorem B2252883 : Blo 2251435 2252883 := bstep (se 1 (by rfl) ⟨1689662, by rfl⟩ : syracuseStep 2252883 = 3379325) B3379325
theorem B5068997 : Blo 2251435 5068997 := bbase (se 4 (by rfl) ⟨475218, by rfl⟩ : syracuseStep 5068997 = 950437) (by norm_num)
theorem B3379331 : Blo 2251435 3379331 := bstep (se 1 (by rfl) ⟨2534498, by rfl⟩ : syracuseStep 3379331 = 5068997) B5068997
theorem B2252887 : Blo 2251435 2252887 := bstep (se 1 (by rfl) ⟨1689665, by rfl⟩ : syracuseStep 2252887 = 3379331) B3379331
theorem B12513973 : Blo 2251435 12513973 := bbase (se 5 (by rfl) ⟨586592, by rfl⟩ : syracuseStep 12513973 = 1173185) (by norm_num)
theorem B16685297 : Blo 2251435 16685297 := bstep (se 2 (by rfl) ⟨6256986, by rfl⟩ : syracuseStep 16685297 = 12513973) B12513973
theorem B11123531 : Blo 2251435 11123531 := bstep (se 1 (by rfl) ⟨8342648, by rfl⟩ : syracuseStep 11123531 = 16685297) B16685297
theorem B7415687 : Blo 2251435 7415687 := bstep (se 1 (by rfl) ⟨5561765, by rfl⟩ : syracuseStep 7415687 = 11123531) B11123531
theorem B4943791 : Blo 2251435 4943791 := bstep (se 1 (by rfl) ⟨3707843, by rfl⟩ : syracuseStep 4943791 = 7415687) B7415687
theorem B6591721 : Blo 2251435 6591721 := bstep (se 2 (by rfl) ⟨2471895, by rfl⟩ : syracuseStep 6591721 = 4943791) B4943791
theorem B8788961 : Blo 2251435 8788961 := bstep (se 2 (by rfl) ⟨3295860, by rfl⟩ : syracuseStep 8788961 = 6591721) B6591721
theorem B5859307 : Blo 2251435 5859307 := bstep (se 1 (by rfl) ⟨4394480, by rfl⟩ : syracuseStep 5859307 = 8788961) B8788961
theorem B7812409 : Blo 2251435 7812409 := bstep (se 2 (by rfl) ⟨2929653, by rfl⟩ : syracuseStep 7812409 = 5859307) B5859307
theorem B10416545 : Blo 2251435 10416545 := bstep (se 2 (by rfl) ⟨3906204, by rfl⟩ : syracuseStep 10416545 = 7812409) B7812409
theorem B6944363 : Blo 2251435 6944363 := bstep (se 1 (by rfl) ⟨5208272, by rfl⟩ : syracuseStep 6944363 = 10416545) B10416545
theorem B4629575 : Blo 2251435 4629575 := bstep (se 1 (by rfl) ⟨3472181, by rfl⟩ : syracuseStep 4629575 = 6944363) B6944363
theorem B12345533 : Blo 2251435 12345533 := bstep (se 3 (by rfl) ⟨2314787, by rfl⟩ : syracuseStep 12345533 = 4629575) B4629575
theorem B8230355 : Blo 2251435 8230355 := bstep (se 1 (by rfl) ⟨6172766, by rfl⟩ : syracuseStep 8230355 = 12345533) B12345533
theorem B5486903 : Blo 2251435 5486903 := bstep (se 1 (by rfl) ⟨4115177, by rfl⟩ : syracuseStep 5486903 = 8230355) B8230355
theorem B3657935 : Blo 2251435 3657935 := bstep (se 1 (by rfl) ⟨2743451, by rfl⟩ : syracuseStep 3657935 = 5486903) B5486903
theorem B2438623 : Blo 2251435 2438623 := bstep (se 1 (by rfl) ⟨1828967, by rfl⟩ : syracuseStep 2438623 = 3657935) B3657935
theorem B3251497 : Blo 2251435 3251497 := bstep (se 2 (by rfl) ⟨1219311, by rfl⟩ : syracuseStep 3251497 = 2438623) B2438623
theorem B4335329 : Blo 2251435 4335329 := bstep (se 2 (by rfl) ⟨1625748, by rfl⟩ : syracuseStep 4335329 = 3251497) B3251497
theorem B2890219 : Blo 2251435 2890219 := bstep (se 1 (by rfl) ⟨2167664, by rfl⟩ : syracuseStep 2890219 = 4335329) B4335329
theorem B3853625 : Blo 2251435 3853625 := bstep (se 2 (by rfl) ⟨1445109, by rfl⟩ : syracuseStep 3853625 = 2890219) B2890219
theorem B41105333 : Blo 2251435 41105333 := bstep (se 5 (by rfl) ⟨1926812, by rfl⟩ : syracuseStep 41105333 = 3853625) B3853625
theorem B27403555 : Blo 2251435 27403555 := bstep (se 1 (by rfl) ⟨20552666, by rfl⟩ : syracuseStep 27403555 = 41105333) B41105333
theorem B36538073 : Blo 2251435 36538073 := bstep (se 2 (by rfl) ⟨13701777, by rfl⟩ : syracuseStep 36538073 = 27403555) B27403555
theorem B24358715 : Blo 2251435 24358715 := bstep (se 1 (by rfl) ⟨18269036, by rfl⟩ : syracuseStep 24358715 = 36538073) B36538073
theorem B16239143 : Blo 2251435 16239143 := bstep (se 1 (by rfl) ⟨12179357, by rfl⟩ : syracuseStep 16239143 = 24358715) B24358715
theorem B10826095 : Blo 2251435 10826095 := bstep (se 1 (by rfl) ⟨8119571, by rfl⟩ : syracuseStep 10826095 = 16239143) B16239143
theorem B14434793 : Blo 2251435 14434793 := bstep (se 2 (by rfl) ⟨5413047, by rfl⟩ : syracuseStep 14434793 = 10826095) B10826095
theorem B9623195 : Blo 2251435 9623195 := bstep (se 1 (by rfl) ⟨7217396, by rfl⟩ : syracuseStep 9623195 = 14434793) B14434793
theorem B6415463 : Blo 2251435 6415463 := bstep (se 1 (by rfl) ⟨4811597, by rfl⟩ : syracuseStep 6415463 = 9623195) B9623195
theorem B4276975 : Blo 2251435 4276975 := bstep (se 1 (by rfl) ⟨3207731, by rfl⟩ : syracuseStep 4276975 = 6415463) B6415463
theorem B5702633 : Blo 2251435 5702633 := bstep (se 2 (by rfl) ⟨2138487, by rfl⟩ : syracuseStep 5702633 = 4276975) B4276975
theorem B3801755 : Blo 2251435 3801755 := bstep (se 1 (by rfl) ⟨2851316, by rfl⟩ : syracuseStep 3801755 = 5702633) B5702633
theorem B2534503 : Blo 2251435 2534503 := bstep (se 1 (by rfl) ⟨1900877, by rfl⟩ : syracuseStep 2534503 = 3801755) B3801755
theorem B3379337 : Blo 2251435 3379337 := bstep (se 2 (by rfl) ⟨1267251, by rfl⟩ : syracuseStep 3379337 = 2534503) B2534503
theorem B2252891 : Blo 2251435 2252891 := bstep (se 1 (by rfl) ⟨1689668, by rfl⟩ : syracuseStep 2252891 = 3379337) B3379337
theorem B11405285 : Blo 2251435 11405285 := bbase (se 4 (by rfl) ⟨1069245, by rfl⟩ : syracuseStep 11405285 = 2138491) (by norm_num)
theorem B7603523 : Blo 2251435 7603523 := bstep (se 1 (by rfl) ⟨5702642, by rfl⟩ : syracuseStep 7603523 = 11405285) B11405285
theorem B5069015 : Blo 2251435 5069015 := bstep (se 1 (by rfl) ⟨3801761, by rfl⟩ : syracuseStep 5069015 = 7603523) B7603523
theorem B3379343 : Blo 2251435 3379343 := bstep (se 1 (by rfl) ⟨2534507, by rfl⟩ : syracuseStep 3379343 = 5069015) B5069015
theorem B2252895 : Blo 2251435 2252895 := bstep (se 1 (by rfl) ⟨1689671, by rfl⟩ : syracuseStep 2252895 = 3379343) B3379343
theorem B3379349 : Blo 2251435 3379349 := bbase (se 6 (by rfl) ⟨79203, by rfl⟩ : syracuseStep 3379349 = 158407) (by norm_num)
theorem B2252899 : Blo 2251435 2252899 := bstep (se 1 (by rfl) ⟨1689674, by rfl⟩ : syracuseStep 2252899 = 3379349) B3379349
theorem B3608717 : Blo 2251435 3608717 := bbase (se 3 (by rfl) ⟨676634, by rfl⟩ : syracuseStep 3608717 = 1353269) (by norm_num)
theorem B9623245 : Blo 2251435 9623245 := bstep (se 3 (by rfl) ⟨1804358, by rfl⟩ : syracuseStep 9623245 = 3608717) B3608717
theorem B12830993 : Blo 2251435 12830993 := bstep (se 2 (by rfl) ⟨4811622, by rfl⟩ : syracuseStep 12830993 = 9623245) B9623245
theorem B8553995 : Blo 2251435 8553995 := bstep (se 1 (by rfl) ⟨6415496, by rfl⟩ : syracuseStep 8553995 = 12830993) B12830993
theorem B5702663 : Blo 2251435 5702663 := bstep (se 1 (by rfl) ⟨4276997, by rfl⟩ : syracuseStep 5702663 = 8553995) B8553995
theorem B3801775 : Blo 2251435 3801775 := bstep (se 1 (by rfl) ⟨2851331, by rfl⟩ : syracuseStep 3801775 = 5702663) B5702663
theorem B5069033 : Blo 2251435 5069033 := bstep (se 2 (by rfl) ⟨1900887, by rfl⟩ : syracuseStep 5069033 = 3801775) B3801775
theorem B3379355 : Blo 2251435 3379355 := bstep (se 1 (by rfl) ⟨2534516, by rfl⟩ : syracuseStep 3379355 = 5069033) B5069033
theorem B2252903 : Blo 2251435 2252903 := bstep (se 1 (by rfl) ⟨1689677, by rfl⟩ : syracuseStep 2252903 = 3379355) B3379355
theorem B2534521 : Blo 2251435 2534521 := bbase (se 2 (by rfl) ⟨950445, by rfl⟩ : syracuseStep 2534521 = 1900891) (by norm_num)
theorem B3379361 : Blo 2251435 3379361 := bstep (se 2 (by rfl) ⟨1267260, by rfl⟩ : syracuseStep 3379361 = 2534521) B2534521
theorem B2252907 : Blo 2251435 2252907 := bstep (se 1 (by rfl) ⟨1689680, by rfl⟩ : syracuseStep 2252907 = 3379361) B3379361
theorem B7707317 : Blo 2251435 7707317 := bbase (se 5 (by rfl) ⟨361280, by rfl⟩ : syracuseStep 7707317 = 722561) (by norm_num)
theorem B82211381 : Blo 2251435 82211381 := bstep (se 5 (by rfl) ⟨3853658, by rfl⟩ : syracuseStep 82211381 = 7707317) B7707317
theorem B54807587 : Blo 2251435 54807587 := bstep (se 1 (by rfl) ⟨41105690, by rfl⟩ : syracuseStep 54807587 = 82211381) B82211381
theorem B36538391 : Blo 2251435 36538391 := bstep (se 1 (by rfl) ⟨27403793, by rfl⟩ : syracuseStep 36538391 = 54807587) B54807587
theorem B24358927 : Blo 2251435 24358927 := bstep (se 1 (by rfl) ⟨18269195, by rfl⟩ : syracuseStep 24358927 = 36538391) B36538391
theorem B32478569 : Blo 2251435 32478569 := bstep (se 2 (by rfl) ⟨12179463, by rfl⟩ : syracuseStep 32478569 = 24358927) B24358927
theorem B21652379 : Blo 2251435 21652379 := bstep (se 1 (by rfl) ⟨16239284, by rfl⟩ : syracuseStep 21652379 = 32478569) B32478569
theorem B14434919 : Blo 2251435 14434919 := bstep (se 1 (by rfl) ⟨10826189, by rfl⟩ : syracuseStep 14434919 = 21652379) B21652379
theorem B9623279 : Blo 2251435 9623279 := bstep (se 1 (by rfl) ⟨7217459, by rfl⟩ : syracuseStep 9623279 = 14434919) B14434919
theorem B6415519 : Blo 2251435 6415519 := bstep (se 1 (by rfl) ⟨4811639, by rfl⟩ : syracuseStep 6415519 = 9623279) B9623279
theorem B8554025 : Blo 2251435 8554025 := bstep (se 2 (by rfl) ⟨3207759, by rfl⟩ : syracuseStep 8554025 = 6415519) B6415519
theorem B5702683 : Blo 2251435 5702683 := bstep (se 1 (by rfl) ⟨4277012, by rfl⟩ : syracuseStep 5702683 = 8554025) B8554025
theorem B7603577 : Blo 2251435 7603577 := bstep (se 2 (by rfl) ⟨2851341, by rfl⟩ : syracuseStep 7603577 = 5702683) B5702683
theorem B5069051 : Blo 2251435 5069051 := bstep (se 1 (by rfl) ⟨3801788, by rfl⟩ : syracuseStep 5069051 = 7603577) B7603577
theorem B3379367 : Blo 2251435 3379367 := bstep (se 1 (by rfl) ⟨2534525, by rfl⟩ : syracuseStep 3379367 = 5069051) B5069051
theorem B2252911 : Blo 2251435 2252911 := bstep (se 1 (by rfl) ⟨1689683, by rfl⟩ : syracuseStep 2252911 = 3379367) B3379367
theorem B3379373 : Blo 2251435 3379373 := bbase (se 3 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 3379373 = 1267265) (by norm_num)
theorem B2252915 : Blo 2251435 2252915 := bstep (se 1 (by rfl) ⟨1689686, by rfl⟩ : syracuseStep 2252915 = 3379373) B3379373
theorem B5069069 : Blo 2251435 5069069 := bbase (se 3 (by rfl) ⟨950450, by rfl⟩ : syracuseStep 5069069 = 1900901) (by norm_num)
theorem B3379379 : Blo 2251435 3379379 := bstep (se 1 (by rfl) ⟨2534534, by rfl⟩ : syracuseStep 3379379 = 5069069) B5069069
theorem B2252919 : Blo 2251435 2252919 := bstep (se 1 (by rfl) ⟨1689689, by rfl⟩ : syracuseStep 2252919 = 3379379) B3379379
theorem B2851357 : Blo 2251435 2851357 := bbase (se 3 (by rfl) ⟨534629, by rfl⟩ : syracuseStep 2851357 = 1069259) (by norm_num)
theorem B3801809 : Blo 2251435 3801809 := bstep (se 2 (by rfl) ⟨1425678, by rfl⟩ : syracuseStep 3801809 = 2851357) B2851357
theorem B2534539 : Blo 2251435 2534539 := bstep (se 1 (by rfl) ⟨1900904, by rfl⟩ : syracuseStep 2534539 = 3801809) B3801809
theorem B3379385 : Blo 2251435 3379385 := bstep (se 2 (by rfl) ⟨1267269, by rfl⟩ : syracuseStep 3379385 = 2534539) B2534539
theorem B2252923 : Blo 2251435 2252923 := bstep (se 1 (by rfl) ⟨1689692, by rfl⟩ : syracuseStep 2252923 = 3379385) B3379385
theorem B5413133 : Blo 2251435 5413133 := bbase (se 3 (by rfl) ⟨1014962, by rfl⟩ : syracuseStep 5413133 = 2029925) (by norm_num)
theorem B3608755 : Blo 2251435 3608755 := bstep (se 1 (by rfl) ⟨2706566, by rfl⟩ : syracuseStep 3608755 = 5413133) B5413133
theorem B19246693 : Blo 2251435 19246693 := bstep (se 4 (by rfl) ⟨1804377, by rfl⟩ : syracuseStep 19246693 = 3608755) B3608755
theorem B25662257 : Blo 2251435 25662257 := bstep (se 2 (by rfl) ⟨9623346, by rfl⟩ : syracuseStep 25662257 = 19246693) B19246693
theorem B17108171 : Blo 2251435 17108171 := bstep (se 1 (by rfl) ⟨12831128, by rfl⟩ : syracuseStep 17108171 = 25662257) B25662257
theorem B11405447 : Blo 2251435 11405447 := bstep (se 1 (by rfl) ⟨8554085, by rfl⟩ : syracuseStep 11405447 = 17108171) B17108171
theorem B7603631 : Blo 2251435 7603631 := bstep (se 1 (by rfl) ⟨5702723, by rfl⟩ : syracuseStep 7603631 = 11405447) B11405447
theorem B5069087 : Blo 2251435 5069087 := bstep (se 1 (by rfl) ⟨3801815, by rfl⟩ : syracuseStep 5069087 = 7603631) B7603631
theorem B3379391 : Blo 2251435 3379391 := bstep (se 1 (by rfl) ⟨2534543, by rfl⟩ : syracuseStep 3379391 = 5069087) B5069087
theorem B2252927 : Blo 2251435 2252927 := bstep (se 1 (by rfl) ⟨1689695, by rfl⟩ : syracuseStep 2252927 = 3379391) B3379391
theorem B3379397 : Blo 2251435 3379397 := bbase (se 4 (by rfl) ⟨316818, by rfl⟩ : syracuseStep 3379397 = 633637) (by norm_num)
theorem B2252931 : Blo 2251435 2252931 := bstep (se 1 (by rfl) ⟨1689698, by rfl⟩ : syracuseStep 2252931 = 3379397) B3379397
theorem B3801829 : Blo 2251435 3801829 := bbase (se 4 (by rfl) ⟨356421, by rfl⟩ : syracuseStep 3801829 = 712843) (by norm_num)
theorem B5069105 : Blo 2251435 5069105 := bstep (se 2 (by rfl) ⟨1900914, by rfl⟩ : syracuseStep 5069105 = 3801829) B3801829
theorem B3379403 : Blo 2251435 3379403 := bstep (se 1 (by rfl) ⟨2534552, by rfl⟩ : syracuseStep 3379403 = 5069105) B5069105
theorem B2252935 : Blo 2251435 2252935 := bstep (se 1 (by rfl) ⟨1689701, by rfl⟩ : syracuseStep 2252935 = 3379403) B3379403
theorem B2534557 : Blo 2251435 2534557 := bbase (se 3 (by rfl) ⟨475229, by rfl⟩ : syracuseStep 2534557 = 950459) (by norm_num)
theorem B3379409 : Blo 2251435 3379409 := bstep (se 2 (by rfl) ⟨1267278, by rfl⟩ : syracuseStep 3379409 = 2534557) B2534557
theorem B2252939 : Blo 2251435 2252939 := bstep (se 1 (by rfl) ⟨1689704, by rfl⟩ : syracuseStep 2252939 = 3379409) B3379409
theorem B7603685 : Blo 2251435 7603685 := bbase (se 4 (by rfl) ⟨712845, by rfl⟩ : syracuseStep 7603685 = 1425691) (by norm_num)
theorem B5069123 : Blo 2251435 5069123 := bstep (se 1 (by rfl) ⟨3801842, by rfl⟩ : syracuseStep 5069123 = 7603685) B7603685
theorem B3379415 : Blo 2251435 3379415 := bstep (se 1 (by rfl) ⟨2534561, by rfl⟩ : syracuseStep 3379415 = 5069123) B5069123
theorem B2252943 : Blo 2251435 2252943 := bstep (se 1 (by rfl) ⟨1689707, by rfl⟩ : syracuseStep 2252943 = 3379415) B3379415
theorem B3379421 : Blo 2251435 3379421 := bbase (se 3 (by rfl) ⟨633641, by rfl⟩ : syracuseStep 3379421 = 1267283) (by norm_num)
theorem B2252947 : Blo 2251435 2252947 := bstep (se 1 (by rfl) ⟨1689710, by rfl⟩ : syracuseStep 2252947 = 3379421) B3379421
theorem B5069141 : Blo 2251435 5069141 := bbase (se 10 (by rfl) ⟨7425, by rfl⟩ : syracuseStep 5069141 = 14851) (by norm_num)
theorem B3379427 : Blo 2251435 3379427 := bstep (se 1 (by rfl) ⟨2534570, by rfl⟩ : syracuseStep 3379427 = 5069141) B5069141
theorem B2252951 : Blo 2251435 2252951 := bstep (se 1 (by rfl) ⟨1689713, by rfl⟩ : syracuseStep 2252951 = 3379427) B3379427
theorem B2706601 : Blo 2251435 2706601 := bbase (se 2 (by rfl) ⟨1014975, by rfl⟩ : syracuseStep 2706601 = 2029951) (by norm_num)
theorem B3608801 : Blo 2251435 3608801 := bstep (se 2 (by rfl) ⟨1353300, by rfl⟩ : syracuseStep 3608801 = 2706601) B2706601
theorem B2405867 : Blo 2251435 2405867 := bstep (se 1 (by rfl) ⟨1804400, by rfl⟩ : syracuseStep 2405867 = 3608801) B3608801
theorem B6415645 : Blo 2251435 6415645 := bstep (se 3 (by rfl) ⟨1202933, by rfl⟩ : syracuseStep 6415645 = 2405867) B2405867
theorem B8554193 : Blo 2251435 8554193 := bstep (se 2 (by rfl) ⟨3207822, by rfl⟩ : syracuseStep 8554193 = 6415645) B6415645
theorem B5702795 : Blo 2251435 5702795 := bstep (se 1 (by rfl) ⟨4277096, by rfl⟩ : syracuseStep 5702795 = 8554193) B8554193
theorem B3801863 : Blo 2251435 3801863 := bstep (se 1 (by rfl) ⟨2851397, by rfl⟩ : syracuseStep 3801863 = 5702795) B5702795
theorem B2534575 : Blo 2251435 2534575 := bstep (se 1 (by rfl) ⟨1900931, by rfl⟩ : syracuseStep 2534575 = 3801863) B3801863
theorem B3379433 : Blo 2251435 3379433 := bstep (se 2 (by rfl) ⟨1267287, by rfl⟩ : syracuseStep 3379433 = 2534575) B2534575
theorem B2252955 : Blo 2251435 2252955 := bstep (se 1 (by rfl) ⟨1689716, by rfl⟩ : syracuseStep 2252955 = 3379433) B3379433
theorem B6089861 : Blo 2251435 6089861 := bbase (se 4 (by rfl) ⟨570924, by rfl⟩ : syracuseStep 6089861 = 1141849) (by norm_num)
theorem B16239629 : Blo 2251435 16239629 := bstep (se 3 (by rfl) ⟨3044930, by rfl⟩ : syracuseStep 16239629 = 6089861) B6089861
theorem B43305677 : Blo 2251435 43305677 := bstep (se 3 (by rfl) ⟨8119814, by rfl⟩ : syracuseStep 43305677 = 16239629) B16239629
theorem B28870451 : Blo 2251435 28870451 := bstep (se 1 (by rfl) ⟨21652838, by rfl⟩ : syracuseStep 28870451 = 43305677) B43305677
theorem B19246967 : Blo 2251435 19246967 := bstep (se 1 (by rfl) ⟨14435225, by rfl⟩ : syracuseStep 19246967 = 28870451) B28870451
theorem B12831311 : Blo 2251435 12831311 := bstep (se 1 (by rfl) ⟨9623483, by rfl⟩ : syracuseStep 12831311 = 19246967) B19246967
theorem B8554207 : Blo 2251435 8554207 := bstep (se 1 (by rfl) ⟨6415655, by rfl⟩ : syracuseStep 8554207 = 12831311) B12831311
theorem B11405609 : Blo 2251435 11405609 := bstep (se 2 (by rfl) ⟨4277103, by rfl⟩ : syracuseStep 11405609 = 8554207) B8554207
theorem B7603739 : Blo 2251435 7603739 := bstep (se 1 (by rfl) ⟨5702804, by rfl⟩ : syracuseStep 7603739 = 11405609) B11405609
theorem B5069159 : Blo 2251435 5069159 := bstep (se 1 (by rfl) ⟨3801869, by rfl⟩ : syracuseStep 5069159 = 7603739) B7603739
theorem B3379439 : Blo 2251435 3379439 := bstep (se 1 (by rfl) ⟨2534579, by rfl⟩ : syracuseStep 3379439 = 5069159) B5069159
theorem B2252959 : Blo 2251435 2252959 := bstep (se 1 (by rfl) ⟨1689719, by rfl⟩ : syracuseStep 2252959 = 3379439) B3379439
theorem B3379445 : Blo 2251435 3379445 := bbase (se 5 (by rfl) ⟨158411, by rfl⟩ : syracuseStep 3379445 = 316823) (by norm_num)
theorem B2252963 : Blo 2251435 2252963 := bstep (se 1 (by rfl) ⟨1689722, by rfl⟩ : syracuseStep 2252963 = 3379445) B3379445
theorem B5487085 : Blo 2251435 5487085 := bbase (se 3 (by rfl) ⟨1028828, by rfl⟩ : syracuseStep 5487085 = 2057657) (by norm_num)
theorem B29264453 : Blo 2251435 29264453 := bstep (se 4 (by rfl) ⟨2743542, by rfl⟩ : syracuseStep 29264453 = 5487085) B5487085
theorem B19509635 : Blo 2251435 19509635 := bstep (se 1 (by rfl) ⟨14632226, by rfl⟩ : syracuseStep 19509635 = 29264453) B29264453
theorem B13006423 : Blo 2251435 13006423 := bstep (se 1 (by rfl) ⟨9754817, by rfl⟩ : syracuseStep 13006423 = 19509635) B19509635
theorem B17341897 : Blo 2251435 17341897 := bstep (se 2 (by rfl) ⟨6503211, by rfl⟩ : syracuseStep 17341897 = 13006423) B13006423
theorem B23122529 : Blo 2251435 23122529 := bstep (se 2 (by rfl) ⟨8670948, by rfl⟩ : syracuseStep 23122529 = 17341897) B17341897
theorem B15415019 : Blo 2251435 15415019 := bstep (se 1 (by rfl) ⟨11561264, by rfl⟩ : syracuseStep 15415019 = 23122529) B23122529
theorem B10276679 : Blo 2251435 10276679 := bstep (se 1 (by rfl) ⟨7707509, by rfl⟩ : syracuseStep 10276679 = 15415019) B15415019
theorem B27404477 : Blo 2251435 27404477 := bstep (se 3 (by rfl) ⟨5138339, by rfl⟩ : syracuseStep 27404477 = 10276679) B10276679
theorem B18269651 : Blo 2251435 18269651 := bstep (se 1 (by rfl) ⟨13702238, by rfl⟩ : syracuseStep 18269651 = 27404477) B27404477
theorem B48719069 : Blo 2251435 48719069 := bstep (se 3 (by rfl) ⟨9134825, by rfl⟩ : syracuseStep 48719069 = 18269651) B18269651
theorem B32479379 : Blo 2251435 32479379 := bstep (se 1 (by rfl) ⟨24359534, by rfl⟩ : syracuseStep 32479379 = 48719069) B48719069
theorem B21652919 : Blo 2251435 21652919 := bstep (se 1 (by rfl) ⟨16239689, by rfl⟩ : syracuseStep 21652919 = 32479379) B32479379
theorem B14435279 : Blo 2251435 14435279 := bstep (se 1 (by rfl) ⟨10826459, by rfl⟩ : syracuseStep 14435279 = 21652919) B21652919
theorem B9623519 : Blo 2251435 9623519 := bstep (se 1 (by rfl) ⟨7217639, by rfl⟩ : syracuseStep 9623519 = 14435279) B14435279
theorem B6415679 : Blo 2251435 6415679 := bstep (se 1 (by rfl) ⟨4811759, by rfl⟩ : syracuseStep 6415679 = 9623519) B9623519
theorem B4277119 : Blo 2251435 4277119 := bstep (se 1 (by rfl) ⟨3207839, by rfl⟩ : syracuseStep 4277119 = 6415679) B6415679
theorem B5702825 : Blo 2251435 5702825 := bstep (se 2 (by rfl) ⟨2138559, by rfl⟩ : syracuseStep 5702825 = 4277119) B4277119
theorem B3801883 : Blo 2251435 3801883 := bstep (se 1 (by rfl) ⟨2851412, by rfl⟩ : syracuseStep 3801883 = 5702825) B5702825
theorem B5069177 : Blo 2251435 5069177 := bstep (se 2 (by rfl) ⟨1900941, by rfl⟩ : syracuseStep 5069177 = 3801883) B3801883
theorem B3379451 : Blo 2251435 3379451 := bstep (se 1 (by rfl) ⟨2534588, by rfl⟩ : syracuseStep 3379451 = 5069177) B5069177
theorem B2252967 : Blo 2251435 2252967 := bstep (se 1 (by rfl) ⟨1689725, by rfl⟩ : syracuseStep 2252967 = 3379451) B3379451
theorem B2534593 : Blo 2251435 2534593 := bbase (se 2 (by rfl) ⟨950472, by rfl⟩ : syracuseStep 2534593 = 1900945) (by norm_num)
theorem B3379457 : Blo 2251435 3379457 := bstep (se 2 (by rfl) ⟨1267296, by rfl⟩ : syracuseStep 3379457 = 2534593) B2534593
theorem B2252971 : Blo 2251435 2252971 := bstep (se 1 (by rfl) ⟨1689728, by rfl⟩ : syracuseStep 2252971 = 3379457) B3379457
theorem B5702845 : Blo 2251435 5702845 := bbase (se 3 (by rfl) ⟨1069283, by rfl⟩ : syracuseStep 5702845 = 2138567) (by norm_num)
theorem B7603793 : Blo 2251435 7603793 := bstep (se 2 (by rfl) ⟨2851422, by rfl⟩ : syracuseStep 7603793 = 5702845) B5702845
theorem B5069195 : Blo 2251435 5069195 := bstep (se 1 (by rfl) ⟨3801896, by rfl⟩ : syracuseStep 5069195 = 7603793) B7603793
theorem B3379463 : Blo 2251435 3379463 := bstep (se 1 (by rfl) ⟨2534597, by rfl⟩ : syracuseStep 3379463 = 5069195) B5069195
theorem B2252975 : Blo 2251435 2252975 := bstep (se 1 (by rfl) ⟨1689731, by rfl⟩ : syracuseStep 2252975 = 3379463) B3379463
theorem B3379469 : Blo 2251435 3379469 := bbase (se 3 (by rfl) ⟨633650, by rfl⟩ : syracuseStep 3379469 = 1267301) (by norm_num)
theorem B2252979 : Blo 2251435 2252979 := bstep (se 1 (by rfl) ⟨1689734, by rfl⟩ : syracuseStep 2252979 = 3379469) B3379469
theorem B5069213 : Blo 2251435 5069213 := bbase (se 3 (by rfl) ⟨950477, by rfl⟩ : syracuseStep 5069213 = 1900955) (by norm_num)
theorem B3379475 : Blo 2251435 3379475 := bstep (se 1 (by rfl) ⟨2534606, by rfl⟩ : syracuseStep 3379475 = 5069213) B5069213
theorem B2252983 : Blo 2251435 2252983 := bstep (se 1 (by rfl) ⟨1689737, by rfl⟩ : syracuseStep 2252983 = 3379475) B3379475
theorem B3801917 : Blo 2251435 3801917 := bbase (se 3 (by rfl) ⟨712859, by rfl⟩ : syracuseStep 3801917 = 1425719) (by norm_num)
theorem B2534611 : Blo 2251435 2534611 := bstep (se 1 (by rfl) ⟨1900958, by rfl⟩ : syracuseStep 2534611 = 3801917) B3801917
theorem B3379481 : Blo 2251435 3379481 := bstep (se 2 (by rfl) ⟨1267305, by rfl⟩ : syracuseStep 3379481 = 2534611) B2534611
theorem B2252987 : Blo 2251435 2252987 := bstep (se 1 (by rfl) ⟨1689740, by rfl⟩ : syracuseStep 2252987 = 3379481) B3379481
theorem B2405905 : Blo 2251435 2405905 := bbase (se 2 (by rfl) ⟨902214, by rfl⟩ : syracuseStep 2405905 = 1804429) (by norm_num)
theorem B12831493 : Blo 2251435 12831493 := bstep (se 4 (by rfl) ⟨1202952, by rfl⟩ : syracuseStep 12831493 = 2405905) B2405905
theorem B17108657 : Blo 2251435 17108657 := bstep (se 2 (by rfl) ⟨6415746, by rfl⟩ : syracuseStep 17108657 = 12831493) B12831493
theorem B11405771 : Blo 2251435 11405771 := bstep (se 1 (by rfl) ⟨8554328, by rfl⟩ : syracuseStep 11405771 = 17108657) B17108657
theorem B7603847 : Blo 2251435 7603847 := bstep (se 1 (by rfl) ⟨5702885, by rfl⟩ : syracuseStep 7603847 = 11405771) B11405771
theorem B5069231 : Blo 2251435 5069231 := bstep (se 1 (by rfl) ⟨3801923, by rfl⟩ : syracuseStep 5069231 = 7603847) B7603847
theorem B3379487 : Blo 2251435 3379487 := bstep (se 1 (by rfl) ⟨2534615, by rfl⟩ : syracuseStep 3379487 = 5069231) B5069231
theorem B2252991 : Blo 2251435 2252991 := bstep (se 1 (by rfl) ⟨1689743, by rfl⟩ : syracuseStep 2252991 = 3379487) B3379487
theorem B3379493 : Blo 2251435 3379493 := bbase (se 4 (by rfl) ⟨316827, by rfl⟩ : syracuseStep 3379493 = 633655) (by norm_num)
theorem B2252995 : Blo 2251435 2252995 := bstep (se 1 (by rfl) ⟨1689746, by rfl⟩ : syracuseStep 2252995 = 3379493) B3379493
theorem B2851453 : Blo 2251435 2851453 := bbase (se 3 (by rfl) ⟨534647, by rfl⟩ : syracuseStep 2851453 = 1069295) (by norm_num)
theorem B3801937 : Blo 2251435 3801937 := bstep (se 2 (by rfl) ⟨1425726, by rfl⟩ : syracuseStep 3801937 = 2851453) B2851453
theorem B5069249 : Blo 2251435 5069249 := bstep (se 2 (by rfl) ⟨1900968, by rfl⟩ : syracuseStep 5069249 = 3801937) B3801937
theorem B3379499 : Blo 2251435 3379499 := bstep (se 1 (by rfl) ⟨2534624, by rfl⟩ : syracuseStep 3379499 = 5069249) B5069249
theorem B2252999 : Blo 2251435 2252999 := bstep (se 1 (by rfl) ⟨1689749, by rfl⟩ : syracuseStep 2252999 = 3379499) B3379499
theorem B2534629 : Blo 2251435 2534629 := bbase (se 4 (by rfl) ⟨237621, by rfl⟩ : syracuseStep 2534629 = 475243) (by norm_num)
theorem B3379505 : Blo 2251435 3379505 := bstep (se 2 (by rfl) ⟨1267314, by rfl⟩ : syracuseStep 3379505 = 2534629) B2534629
theorem B2253003 : Blo 2251435 2253003 := bstep (se 1 (by rfl) ⟨1689752, by rfl⟩ : syracuseStep 2253003 = 3379505) B3379505
theorem B4811845 : Blo 2251435 4811845 := bbase (se 4 (by rfl) ⟨451110, by rfl⟩ : syracuseStep 4811845 = 902221) (by norm_num)
theorem B6415793 : Blo 2251435 6415793 := bstep (se 2 (by rfl) ⟨2405922, by rfl⟩ : syracuseStep 6415793 = 4811845) B4811845
theorem B4277195 : Blo 2251435 4277195 := bstep (se 1 (by rfl) ⟨3207896, by rfl⟩ : syracuseStep 4277195 = 6415793) B6415793
theorem B2851463 : Blo 2251435 2851463 := bstep (se 1 (by rfl) ⟨2138597, by rfl⟩ : syracuseStep 2851463 = 4277195) B4277195
theorem B7603901 : Blo 2251435 7603901 := bstep (se 3 (by rfl) ⟨1425731, by rfl⟩ : syracuseStep 7603901 = 2851463) B2851463
theorem B5069267 : Blo 2251435 5069267 := bstep (se 1 (by rfl) ⟨3801950, by rfl⟩ : syracuseStep 5069267 = 7603901) B7603901
theorem B3379511 : Blo 2251435 3379511 := bstep (se 1 (by rfl) ⟨2534633, by rfl⟩ : syracuseStep 3379511 = 5069267) B5069267
theorem B2253007 : Blo 2251435 2253007 := bstep (se 1 (by rfl) ⟨1689755, by rfl⟩ : syracuseStep 2253007 = 3379511) B3379511
theorem B3379517 : Blo 2251435 3379517 := bbase (se 3 (by rfl) ⟨633659, by rfl⟩ : syracuseStep 3379517 = 1267319) (by norm_num)
theorem B2253011 : Blo 2251435 2253011 := bstep (se 1 (by rfl) ⟨1689758, by rfl⟩ : syracuseStep 2253011 = 3379517) B3379517
theorem B5069285 : Blo 2251435 5069285 := bbase (se 4 (by rfl) ⟨475245, by rfl⟩ : syracuseStep 5069285 = 950491) (by norm_num)
theorem B3379523 : Blo 2251435 3379523 := bstep (se 1 (by rfl) ⟨2534642, by rfl⟩ : syracuseStep 3379523 = 5069285) B5069285
theorem B2253015 : Blo 2251435 2253015 := bstep (se 1 (by rfl) ⟨1689761, by rfl⟩ : syracuseStep 2253015 = 3379523) B3379523
theorem B5702957 : Blo 2251435 5702957 := bbase (se 3 (by rfl) ⟨1069304, by rfl⟩ : syracuseStep 5702957 = 2138609) (by norm_num)
theorem B3801971 : Blo 2251435 3801971 := bstep (se 1 (by rfl) ⟨2851478, by rfl⟩ : syracuseStep 3801971 = 5702957) B5702957
theorem B2534647 : Blo 2251435 2534647 := bstep (se 1 (by rfl) ⟨1900985, by rfl⟩ : syracuseStep 2534647 = 3801971) B3801971
theorem B3379529 : Blo 2251435 3379529 := bstep (se 2 (by rfl) ⟨1267323, by rfl⟩ : syracuseStep 3379529 = 2534647) B2534647
theorem B2253019 : Blo 2251435 2253019 := bstep (se 1 (by rfl) ⟨1689764, by rfl⟩ : syracuseStep 2253019 = 3379529) B3379529
theorem B4171565 : Blo 2251435 4171565 := bbase (se 3 (by rfl) ⟨782168, by rfl⟩ : syracuseStep 4171565 = 1564337) (by norm_num)
theorem B11124173 : Blo 2251435 11124173 := bstep (se 3 (by rfl) ⟨2085782, by rfl⟩ : syracuseStep 11124173 = 4171565) B4171565
theorem B29664461 : Blo 2251435 29664461 := bstep (se 3 (by rfl) ⟨5562086, by rfl⟩ : syracuseStep 29664461 = 11124173) B11124173
theorem B19776307 : Blo 2251435 19776307 := bstep (se 1 (by rfl) ⟨14832230, by rfl⟩ : syracuseStep 19776307 = 29664461) B29664461
theorem B26368409 : Blo 2251435 26368409 := bstep (se 2 (by rfl) ⟨9888153, by rfl⟩ : syracuseStep 26368409 = 19776307) B19776307
theorem B17578939 : Blo 2251435 17578939 := bstep (se 1 (by rfl) ⟨13184204, by rfl⟩ : syracuseStep 17578939 = 26368409) B26368409
theorem B23438585 : Blo 2251435 23438585 := bstep (se 2 (by rfl) ⟨8789469, by rfl⟩ : syracuseStep 23438585 = 17578939) B17578939
theorem B15625723 : Blo 2251435 15625723 := bstep (se 1 (by rfl) ⟨11719292, by rfl⟩ : syracuseStep 15625723 = 23438585) B23438585
theorem B20834297 : Blo 2251435 20834297 := bstep (se 2 (by rfl) ⟨7812861, by rfl⟩ : syracuseStep 20834297 = 15625723) B15625723
theorem B13889531 : Blo 2251435 13889531 := bstep (se 1 (by rfl) ⟨10417148, by rfl⟩ : syracuseStep 13889531 = 20834297) B20834297
theorem B9259687 : Blo 2251435 9259687 := bstep (se 1 (by rfl) ⟨6944765, by rfl⟩ : syracuseStep 9259687 = 13889531) B13889531
theorem B49384997 : Blo 2251435 49384997 := bstep (se 4 (by rfl) ⟨4629843, by rfl⟩ : syracuseStep 49384997 = 9259687) B9259687
theorem B32923331 : Blo 2251435 32923331 := bstep (se 1 (by rfl) ⟨24692498, by rfl⟩ : syracuseStep 32923331 = 49384997) B49384997
theorem B21948887 : Blo 2251435 21948887 := bstep (se 1 (by rfl) ⟨16461665, by rfl⟩ : syracuseStep 21948887 = 32923331) B32923331
theorem B14632591 : Blo 2251435 14632591 := bstep (se 1 (by rfl) ⟨10974443, by rfl⟩ : syracuseStep 14632591 = 21948887) B21948887
theorem B19510121 : Blo 2251435 19510121 := bstep (se 2 (by rfl) ⟨7316295, by rfl⟩ : syracuseStep 19510121 = 14632591) B14632591
theorem B13006747 : Blo 2251435 13006747 := bstep (se 1 (by rfl) ⟨9755060, by rfl⟩ : syracuseStep 13006747 = 19510121) B19510121
theorem B69369317 : Blo 2251435 69369317 := bstep (se 4 (by rfl) ⟨6503373, by rfl⟩ : syracuseStep 69369317 = 13006747) B13006747
theorem B46246211 : Blo 2251435 46246211 := bstep (se 1 (by rfl) ⟨34684658, by rfl⟩ : syracuseStep 46246211 = 69369317) B69369317
theorem B30830807 : Blo 2251435 30830807 := bstep (se 1 (by rfl) ⟨23123105, by rfl⟩ : syracuseStep 30830807 = 46246211) B46246211
theorem B20553871 : Blo 2251435 20553871 := bstep (se 1 (by rfl) ⟨15415403, by rfl⟩ : syracuseStep 20553871 = 30830807) B30830807
theorem B27405161 : Blo 2251435 27405161 := bstep (se 2 (by rfl) ⟨10276935, by rfl⟩ : syracuseStep 27405161 = 20553871) B20553871
theorem B18270107 : Blo 2251435 18270107 := bstep (se 1 (by rfl) ⟨13702580, by rfl⟩ : syracuseStep 18270107 = 27405161) B27405161
theorem B12180071 : Blo 2251435 12180071 := bstep (se 1 (by rfl) ⟨9135053, by rfl⟩ : syracuseStep 12180071 = 18270107) B18270107
theorem B8120047 : Blo 2251435 8120047 := bstep (se 1 (by rfl) ⟨6090035, by rfl⟩ : syracuseStep 8120047 = 12180071) B12180071
theorem B10826729 : Blo 2251435 10826729 := bstep (se 2 (by rfl) ⟨4060023, by rfl⟩ : syracuseStep 10826729 = 8120047) B8120047
theorem B7217819 : Blo 2251435 7217819 := bstep (se 1 (by rfl) ⟨5413364, by rfl⟩ : syracuseStep 7217819 = 10826729) B10826729
theorem B4811879 : Blo 2251435 4811879 := bstep (se 1 (by rfl) ⟨3608909, by rfl⟩ : syracuseStep 4811879 = 7217819) B7217819
theorem B3207919 : Blo 2251435 3207919 := bstep (se 1 (by rfl) ⟨2405939, by rfl⟩ : syracuseStep 3207919 = 4811879) B4811879
theorem B4277225 : Blo 2251435 4277225 := bstep (se 2 (by rfl) ⟨1603959, by rfl⟩ : syracuseStep 4277225 = 3207919) B3207919
theorem B11405933 : Blo 2251435 11405933 := bstep (se 3 (by rfl) ⟨2138612, by rfl⟩ : syracuseStep 11405933 = 4277225) B4277225
theorem B7603955 : Blo 2251435 7603955 := bstep (se 1 (by rfl) ⟨5702966, by rfl⟩ : syracuseStep 7603955 = 11405933) B11405933
theorem B5069303 : Blo 2251435 5069303 := bstep (se 1 (by rfl) ⟨3801977, by rfl⟩ : syracuseStep 5069303 = 7603955) B7603955
theorem B3379535 : Blo 2251435 3379535 := bstep (se 1 (by rfl) ⟨2534651, by rfl⟩ : syracuseStep 3379535 = 5069303) B5069303
theorem B2253023 : Blo 2251435 2253023 := bstep (se 1 (by rfl) ⟨1689767, by rfl⟩ : syracuseStep 2253023 = 3379535) B3379535
theorem B3379541 : Blo 2251435 3379541 := bbase (se 10 (by rfl) ⟨4950, by rfl⟩ : syracuseStep 3379541 = 9901) (by norm_num)
theorem B2253027 : Blo 2251435 2253027 := bstep (se 1 (by rfl) ⟨1689770, by rfl⟩ : syracuseStep 2253027 = 3379541) B3379541
theorem B6415861 : Blo 2251435 6415861 := bbase (se 5 (by rfl) ⟨300743, by rfl⟩ : syracuseStep 6415861 = 601487) (by norm_num)
theorem B8554481 : Blo 2251435 8554481 := bstep (se 2 (by rfl) ⟨3207930, by rfl⟩ : syracuseStep 8554481 = 6415861) B6415861
theorem B5702987 : Blo 2251435 5702987 := bstep (se 1 (by rfl) ⟨4277240, by rfl⟩ : syracuseStep 5702987 = 8554481) B8554481
theorem B3801991 : Blo 2251435 3801991 := bstep (se 1 (by rfl) ⟨2851493, by rfl⟩ : syracuseStep 3801991 = 5702987) B5702987
theorem B5069321 : Blo 2251435 5069321 := bstep (se 2 (by rfl) ⟨1900995, by rfl⟩ : syracuseStep 5069321 = 3801991) B3801991
theorem B3379547 : Blo 2251435 3379547 := bstep (se 1 (by rfl) ⟨2534660, by rfl⟩ : syracuseStep 3379547 = 5069321) B5069321
theorem B2253031 : Blo 2251435 2253031 := bstep (se 1 (by rfl) ⟨1689773, by rfl⟩ : syracuseStep 2253031 = 3379547) B3379547
theorem B2534665 : Blo 2251435 2534665 := bbase (se 2 (by rfl) ⟨950499, by rfl⟩ : syracuseStep 2534665 = 1900999) (by norm_num)
theorem B3379553 : Blo 2251435 3379553 := bstep (se 2 (by rfl) ⟨1267332, by rfl⟩ : syracuseStep 3379553 = 2534665) B2534665
theorem B2253035 : Blo 2251435 2253035 := bstep (se 1 (by rfl) ⟨1689776, by rfl⟩ : syracuseStep 2253035 = 3379553) B3379553
theorem B2706701 : Blo 2251435 2706701 := bbase (se 3 (by rfl) ⟨507506, by rfl⟩ : syracuseStep 2706701 = 1015013) (by norm_num)
theorem B28871477 : Blo 2251435 28871477 := bstep (se 5 (by rfl) ⟨1353350, by rfl⟩ : syracuseStep 28871477 = 2706701) B2706701
theorem B19247651 : Blo 2251435 19247651 := bstep (se 1 (by rfl) ⟨14435738, by rfl⟩ : syracuseStep 19247651 = 28871477) B28871477
theorem B12831767 : Blo 2251435 12831767 := bstep (se 1 (by rfl) ⟨9623825, by rfl⟩ : syracuseStep 12831767 = 19247651) B19247651
theorem B8554511 : Blo 2251435 8554511 := bstep (se 1 (by rfl) ⟨6415883, by rfl⟩ : syracuseStep 8554511 = 12831767) B12831767
theorem B5703007 : Blo 2251435 5703007 := bstep (se 1 (by rfl) ⟨4277255, by rfl⟩ : syracuseStep 5703007 = 8554511) B8554511
theorem B7604009 : Blo 2251435 7604009 := bstep (se 2 (by rfl) ⟨2851503, by rfl⟩ : syracuseStep 7604009 = 5703007) B5703007
theorem B5069339 : Blo 2251435 5069339 := bstep (se 1 (by rfl) ⟨3802004, by rfl⟩ : syracuseStep 5069339 = 7604009) B7604009
theorem B3379559 : Blo 2251435 3379559 := bstep (se 1 (by rfl) ⟨2534669, by rfl⟩ : syracuseStep 3379559 = 5069339) B5069339
theorem B2253039 : Blo 2251435 2253039 := bstep (se 1 (by rfl) ⟨1689779, by rfl⟩ : syracuseStep 2253039 = 3379559) B3379559
theorem B3379565 : Blo 2251435 3379565 := bbase (se 3 (by rfl) ⟨633668, by rfl⟩ : syracuseStep 3379565 = 1267337) (by norm_num)
theorem B2253043 : Blo 2251435 2253043 := bstep (se 1 (by rfl) ⟨1689782, by rfl⟩ : syracuseStep 2253043 = 3379565) B3379565
theorem B5069357 : Blo 2251435 5069357 := bbase (se 3 (by rfl) ⟨950504, by rfl⟩ : syracuseStep 5069357 = 1901009) (by norm_num)
theorem B3379571 : Blo 2251435 3379571 := bstep (se 1 (by rfl) ⟨2534678, by rfl⟩ : syracuseStep 3379571 = 5069357) B5069357
theorem B2253047 : Blo 2251435 2253047 := bstep (se 1 (by rfl) ⟨1689785, by rfl⟩ : syracuseStep 2253047 = 3379571) B3379571
theorem B13364245 : Blo 2251435 13364245 := bbase (se 6 (by rfl) ⟨313224, by rfl⟩ : syracuseStep 13364245 = 626449) (by norm_num)
theorem B17818993 : Blo 2251435 17818993 := bstep (se 2 (by rfl) ⟨6682122, by rfl⟩ : syracuseStep 17818993 = 13364245) B13364245
theorem B23758657 : Blo 2251435 23758657 := bstep (se 2 (by rfl) ⟨8909496, by rfl⟩ : syracuseStep 23758657 = 17818993) B17818993
theorem B126712837 : Blo 2251435 126712837 := bstep (se 4 (by rfl) ⟨11879328, by rfl⟩ : syracuseStep 126712837 = 23758657) B23758657
theorem B168950449 : Blo 2251435 168950449 := bstep (se 2 (by rfl) ⟨63356418, by rfl⟩ : syracuseStep 168950449 = 126712837) B126712837
theorem B225267265 : Blo 2251435 225267265 := bstep (se 2 (by rfl) ⟨84475224, by rfl⟩ : syracuseStep 225267265 = 168950449) B168950449
theorem B300356353 : Blo 2251435 300356353 := bstep (se 2 (by rfl) ⟨112633632, by rfl⟩ : syracuseStep 300356353 = 225267265) B225267265
theorem B400475137 : Blo 2251435 400475137 := bstep (se 2 (by rfl) ⟨150178176, by rfl⟩ : syracuseStep 400475137 = 300356353) B300356353
theorem B533966849 : Blo 2251435 533966849 := bstep (se 2 (by rfl) ⟨200237568, by rfl⟩ : syracuseStep 533966849 = 400475137) B400475137
theorem B355977899 : Blo 2251435 355977899 := bstep (se 1 (by rfl) ⟨266983424, by rfl⟩ : syracuseStep 355977899 = 533966849) B533966849
theorem B237318599 : Blo 2251435 237318599 := bstep (se 1 (by rfl) ⟨177988949, by rfl⟩ : syracuseStep 237318599 = 355977899) B355977899
theorem B158212399 : Blo 2251435 158212399 := bstep (se 1 (by rfl) ⟨118659299, by rfl⟩ : syracuseStep 158212399 = 237318599) B237318599
theorem B210949865 : Blo 2251435 210949865 := bstep (se 2 (by rfl) ⟨79106199, by rfl⟩ : syracuseStep 210949865 = 158212399) B158212399
theorem B140633243 : Blo 2251435 140633243 := bstep (se 1 (by rfl) ⟨105474932, by rfl⟩ : syracuseStep 140633243 = 210949865) B210949865
theorem B93755495 : Blo 2251435 93755495 := bstep (se 1 (by rfl) ⟨70316621, by rfl⟩ : syracuseStep 93755495 = 140633243) B140633243
theorem B62503663 : Blo 2251435 62503663 := bstep (se 1 (by rfl) ⟨46877747, by rfl⟩ : syracuseStep 62503663 = 93755495) B93755495
theorem B83338217 : Blo 2251435 83338217 := bstep (se 2 (by rfl) ⟨31251831, by rfl⟩ : syracuseStep 83338217 = 62503663) B62503663
theorem B55558811 : Blo 2251435 55558811 := bstep (se 1 (by rfl) ⟨41669108, by rfl⟩ : syracuseStep 55558811 = 83338217) B83338217
theorem B37039207 : Blo 2251435 37039207 := bstep (se 1 (by rfl) ⟨27779405, by rfl⟩ : syracuseStep 37039207 = 55558811) B55558811
theorem B49385609 : Blo 2251435 49385609 := bstep (se 2 (by rfl) ⟨18519603, by rfl⟩ : syracuseStep 49385609 = 37039207) B37039207
theorem B32923739 : Blo 2251435 32923739 := bstep (se 1 (by rfl) ⟨24692804, by rfl⟩ : syracuseStep 32923739 = 49385609) B49385609
theorem B87796637 : Blo 2251435 87796637 := bstep (se 3 (by rfl) ⟨16461869, by rfl⟩ : syracuseStep 87796637 = 32923739) B32923739
theorem B58531091 : Blo 2251435 58531091 := bstep (se 1 (by rfl) ⟨43898318, by rfl⟩ : syracuseStep 58531091 = 87796637) B87796637
theorem B156082909 : Blo 2251435 156082909 := bstep (se 3 (by rfl) ⟨29265545, by rfl⟩ : syracuseStep 156082909 = 58531091) B58531091
theorem B208110545 : Blo 2251435 208110545 := bstep (se 2 (by rfl) ⟨78041454, by rfl⟩ : syracuseStep 208110545 = 156082909) B156082909
theorem B138740363 : Blo 2251435 138740363 := bstep (se 1 (by rfl) ⟨104055272, by rfl⟩ : syracuseStep 138740363 = 208110545) B208110545
theorem B92493575 : Blo 2251435 92493575 := bstep (se 1 (by rfl) ⟨69370181, by rfl⟩ : syracuseStep 92493575 = 138740363) B138740363
theorem B61662383 : Blo 2251435 61662383 := bstep (se 1 (by rfl) ⟨46246787, by rfl⟩ : syracuseStep 61662383 = 92493575) B92493575
theorem B41108255 : Blo 2251435 41108255 := bstep (se 1 (by rfl) ⟨30831191, by rfl⟩ : syracuseStep 41108255 = 61662383) B61662383
theorem B27405503 : Blo 2251435 27405503 := bstep (se 1 (by rfl) ⟨20554127, by rfl⟩ : syracuseStep 27405503 = 41108255) B41108255
theorem B18270335 : Blo 2251435 18270335 := bstep (se 1 (by rfl) ⟨13702751, by rfl⟩ : syracuseStep 18270335 = 27405503) B27405503
theorem B12180223 : Blo 2251435 12180223 := bstep (se 1 (by rfl) ⟨9135167, by rfl⟩ : syracuseStep 12180223 = 18270335) B18270335
theorem B16240297 : Blo 2251435 16240297 := bstep (se 2 (by rfl) ⟨6090111, by rfl⟩ : syracuseStep 16240297 = 12180223) B12180223
theorem B21653729 : Blo 2251435 21653729 := bstep (se 2 (by rfl) ⟨8120148, by rfl⟩ : syracuseStep 21653729 = 16240297) B16240297
theorem B14435819 : Blo 2251435 14435819 := bstep (se 1 (by rfl) ⟨10826864, by rfl⟩ : syracuseStep 14435819 = 21653729) B21653729
theorem B9623879 : Blo 2251435 9623879 := bstep (se 1 (by rfl) ⟨7217909, by rfl⟩ : syracuseStep 9623879 = 14435819) B14435819
theorem B6415919 : Blo 2251435 6415919 := bstep (se 1 (by rfl) ⟨4811939, by rfl⟩ : syracuseStep 6415919 = 9623879) B9623879
theorem B4277279 : Blo 2251435 4277279 := bstep (se 1 (by rfl) ⟨3207959, by rfl⟩ : syracuseStep 4277279 = 6415919) B6415919
theorem B2851519 : Blo 2251435 2851519 := bstep (se 1 (by rfl) ⟨2138639, by rfl⟩ : syracuseStep 2851519 = 4277279) B4277279
theorem B3802025 : Blo 2251435 3802025 := bstep (se 2 (by rfl) ⟨1425759, by rfl⟩ : syracuseStep 3802025 = 2851519) B2851519
theorem B2534683 : Blo 2251435 2534683 := bstep (se 1 (by rfl) ⟨1901012, by rfl⟩ : syracuseStep 2534683 = 3802025) B3802025
theorem B3379577 : Blo 2251435 3379577 := bstep (se 2 (by rfl) ⟨1267341, by rfl⟩ : syracuseStep 3379577 = 2534683) B2534683
theorem B2253051 : Blo 2251435 2253051 := bstep (se 1 (by rfl) ⟨1689788, by rfl⟩ : syracuseStep 2253051 = 3379577) B3379577
theorem B38495573 : Blo 2251435 38495573 := bbase (se 12 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 38495573 = 28195) (by norm_num)
theorem B25663715 : Blo 2251435 25663715 := bstep (se 1 (by rfl) ⟨19247786, by rfl⟩ : syracuseStep 25663715 = 38495573) B38495573
theorem B17109143 : Blo 2251435 17109143 := bstep (se 1 (by rfl) ⟨12831857, by rfl⟩ : syracuseStep 17109143 = 25663715) B25663715
theorem B11406095 : Blo 2251435 11406095 := bstep (se 1 (by rfl) ⟨8554571, by rfl⟩ : syracuseStep 11406095 = 17109143) B17109143
theorem B7604063 : Blo 2251435 7604063 := bstep (se 1 (by rfl) ⟨5703047, by rfl⟩ : syracuseStep 7604063 = 11406095) B11406095
theorem B5069375 : Blo 2251435 5069375 := bstep (se 1 (by rfl) ⟨3802031, by rfl⟩ : syracuseStep 5069375 = 7604063) B7604063
theorem B3379583 : Blo 2251435 3379583 := bstep (se 1 (by rfl) ⟨2534687, by rfl⟩ : syracuseStep 3379583 = 5069375) B5069375
theorem B2253055 : Blo 2251435 2253055 := bstep (se 1 (by rfl) ⟨1689791, by rfl⟩ : syracuseStep 2253055 = 3379583) B3379583
theorem B3379589 : Blo 2251435 3379589 := bbase (se 4 (by rfl) ⟨316836, by rfl⟩ : syracuseStep 3379589 = 633673) (by norm_num)
theorem B2253059 : Blo 2251435 2253059 := bstep (se 1 (by rfl) ⟨1689794, by rfl⟩ : syracuseStep 2253059 = 3379589) B3379589
theorem B3802045 : Blo 2251435 3802045 := bbase (se 3 (by rfl) ⟨712883, by rfl⟩ : syracuseStep 3802045 = 1425767) (by norm_num)
theorem B5069393 : Blo 2251435 5069393 := bstep (se 2 (by rfl) ⟨1901022, by rfl⟩ : syracuseStep 5069393 = 3802045) B3802045
theorem B3379595 : Blo 2251435 3379595 := bstep (se 1 (by rfl) ⟨2534696, by rfl⟩ : syracuseStep 3379595 = 5069393) B5069393
theorem B2253063 : Blo 2251435 2253063 := bstep (se 1 (by rfl) ⟨1689797, by rfl⟩ : syracuseStep 2253063 = 3379595) B3379595
theorem B2534701 : Blo 2251435 2534701 := bbase (se 3 (by rfl) ⟨475256, by rfl⟩ : syracuseStep 2534701 = 950513) (by norm_num)
theorem B3379601 : Blo 2251435 3379601 := bstep (se 2 (by rfl) ⟨1267350, by rfl⟩ : syracuseStep 3379601 = 2534701) B2534701
theorem B2253067 : Blo 2251435 2253067 := bstep (se 1 (by rfl) ⟨1689800, by rfl⟩ : syracuseStep 2253067 = 3379601) B3379601
theorem B7604117 : Blo 2251435 7604117 := bbase (se 6 (by rfl) ⟨178221, by rfl⟩ : syracuseStep 7604117 = 356443) (by norm_num)
theorem B5069411 : Blo 2251435 5069411 := bstep (se 1 (by rfl) ⟨3802058, by rfl⟩ : syracuseStep 5069411 = 7604117) B7604117
theorem B3379607 : Blo 2251435 3379607 := bstep (se 1 (by rfl) ⟨2534705, by rfl⟩ : syracuseStep 3379607 = 5069411) B5069411
theorem B2253071 : Blo 2251435 2253071 := bstep (se 1 (by rfl) ⟨1689803, by rfl⟩ : syracuseStep 2253071 = 3379607) B3379607
theorem B3379613 : Blo 2251435 3379613 := bbase (se 3 (by rfl) ⟨633677, by rfl⟩ : syracuseStep 3379613 = 1267355) (by norm_num)
theorem B2253075 : Blo 2251435 2253075 := bstep (se 1 (by rfl) ⟨1689806, by rfl⟩ : syracuseStep 2253075 = 3379613) B3379613
theorem B5069429 : Blo 2251435 5069429 := bbase (se 5 (by rfl) ⟨237629, by rfl⟩ : syracuseStep 5069429 = 475259) (by norm_num)
theorem B3379619 : Blo 2251435 3379619 := bstep (se 1 (by rfl) ⟨2534714, by rfl⟩ : syracuseStep 3379619 = 5069429) B5069429
theorem B2253079 : Blo 2251435 2253079 := bstep (se 1 (by rfl) ⟨1689809, by rfl⟩ : syracuseStep 2253079 = 3379619) B3379619
theorem B11561861 : Blo 2251435 11561861 := bbase (se 4 (by rfl) ⟨1083924, by rfl⟩ : syracuseStep 11561861 = 2167849) (by norm_num)
theorem B7707907 : Blo 2251435 7707907 := bstep (se 1 (by rfl) ⟨5780930, by rfl⟩ : syracuseStep 7707907 = 11561861) B11561861
theorem B10277209 : Blo 2251435 10277209 := bstep (se 2 (by rfl) ⟨3853953, by rfl⟩ : syracuseStep 10277209 = 7707907) B7707907
theorem B13702945 : Blo 2251435 13702945 := bstep (se 2 (by rfl) ⟨5138604, by rfl⟩ : syracuseStep 13702945 = 10277209) B10277209
theorem B18270593 : Blo 2251435 18270593 := bstep (se 2 (by rfl) ⟨6851472, by rfl⟩ : syracuseStep 18270593 = 13702945) B13702945
theorem B12180395 : Blo 2251435 12180395 := bstep (se 1 (by rfl) ⟨9135296, by rfl⟩ : syracuseStep 12180395 = 18270593) B18270593
theorem B8120263 : Blo 2251435 8120263 := bstep (se 1 (by rfl) ⟨6090197, by rfl⟩ : syracuseStep 8120263 = 12180395) B12180395
theorem B10827017 : Blo 2251435 10827017 := bstep (se 2 (by rfl) ⟨4060131, by rfl⟩ : syracuseStep 10827017 = 8120263) B8120263
theorem B7218011 : Blo 2251435 7218011 := bstep (se 1 (by rfl) ⟨5413508, by rfl⟩ : syracuseStep 7218011 = 10827017) B10827017
theorem B19248029 : Blo 2251435 19248029 := bstep (se 3 (by rfl) ⟨3609005, by rfl⟩ : syracuseStep 19248029 = 7218011) B7218011
theorem B12832019 : Blo 2251435 12832019 := bstep (se 1 (by rfl) ⟨9624014, by rfl⟩ : syracuseStep 12832019 = 19248029) B19248029
theorem B8554679 : Blo 2251435 8554679 := bstep (se 1 (by rfl) ⟨6416009, by rfl⟩ : syracuseStep 8554679 = 12832019) B12832019
theorem B5703119 : Blo 2251435 5703119 := bstep (se 1 (by rfl) ⟨4277339, by rfl⟩ : syracuseStep 5703119 = 8554679) B8554679
theorem B3802079 : Blo 2251435 3802079 := bstep (se 1 (by rfl) ⟨2851559, by rfl⟩ : syracuseStep 3802079 = 5703119) B5703119
theorem B2534719 : Blo 2251435 2534719 := bstep (se 1 (by rfl) ⟨1901039, by rfl⟩ : syracuseStep 2534719 = 3802079) B3802079
theorem B3379625 : Blo 2251435 3379625 := bstep (se 2 (by rfl) ⟨1267359, by rfl⟩ : syracuseStep 3379625 = 2534719) B2534719
theorem B2253083 : Blo 2251435 2253083 := bstep (se 1 (by rfl) ⟨1689812, by rfl⟩ : syracuseStep 2253083 = 3379625) B3379625
theorem B8554693 : Blo 2251435 8554693 := bbase (se 4 (by rfl) ⟨802002, by rfl⟩ : syracuseStep 8554693 = 1604005) (by norm_num)
theorem B11406257 : Blo 2251435 11406257 := bstep (se 2 (by rfl) ⟨4277346, by rfl⟩ : syracuseStep 11406257 = 8554693) B8554693
theorem B7604171 : Blo 2251435 7604171 := bstep (se 1 (by rfl) ⟨5703128, by rfl⟩ : syracuseStep 7604171 = 11406257) B11406257
theorem B5069447 : Blo 2251435 5069447 := bstep (se 1 (by rfl) ⟨3802085, by rfl⟩ : syracuseStep 5069447 = 7604171) B7604171
theorem B3379631 : Blo 2251435 3379631 := bstep (se 1 (by rfl) ⟨2534723, by rfl⟩ : syracuseStep 3379631 = 5069447) B5069447
theorem B2253087 : Blo 2251435 2253087 := bstep (se 1 (by rfl) ⟨1689815, by rfl⟩ : syracuseStep 2253087 = 3379631) B3379631
theorem B3379637 : Blo 2251435 3379637 := bbase (se 5 (by rfl) ⟨158420, by rfl⟩ : syracuseStep 3379637 = 316841) (by norm_num)
theorem B2253091 : Blo 2251435 2253091 := bstep (se 1 (by rfl) ⟨1689818, by rfl⟩ : syracuseStep 2253091 = 3379637) B3379637
theorem B5703149 : Blo 2251435 5703149 := bbase (se 3 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 5703149 = 2138681) (by norm_num)
theorem B3802099 : Blo 2251435 3802099 := bstep (se 1 (by rfl) ⟨2851574, by rfl⟩ : syracuseStep 3802099 = 5703149) B5703149
theorem B5069465 : Blo 2251435 5069465 := bstep (se 2 (by rfl) ⟨1901049, by rfl⟩ : syracuseStep 5069465 = 3802099) B3802099
theorem B3379643 : Blo 2251435 3379643 := bstep (se 1 (by rfl) ⟨2534732, by rfl⟩ : syracuseStep 3379643 = 5069465) B5069465
theorem B2253095 : Blo 2251435 2253095 := bstep (se 1 (by rfl) ⟨1689821, by rfl⟩ : syracuseStep 2253095 = 3379643) B3379643
theorem B2534737 : Blo 2251435 2534737 := bbase (se 2 (by rfl) ⟨950526, by rfl⟩ : syracuseStep 2534737 = 1901053) (by norm_num)
theorem B3379649 : Blo 2251435 3379649 := bstep (se 2 (by rfl) ⟨1267368, by rfl⟩ : syracuseStep 3379649 = 2534737) B2534737
theorem B2253099 : Blo 2251435 2253099 := bstep (se 1 (by rfl) ⟨1689824, by rfl⟩ : syracuseStep 2253099 = 3379649) B3379649
theorem B2406025 : Blo 2251435 2406025 := bbase (se 2 (by rfl) ⟨902259, by rfl⟩ : syracuseStep 2406025 = 1804519) (by norm_num)
theorem B3208033 : Blo 2251435 3208033 := bstep (se 2 (by rfl) ⟨1203012, by rfl⟩ : syracuseStep 3208033 = 2406025) B2406025
theorem B4277377 : Blo 2251435 4277377 := bstep (se 2 (by rfl) ⟨1604016, by rfl⟩ : syracuseStep 4277377 = 3208033) B3208033
theorem B5703169 : Blo 2251435 5703169 := bstep (se 2 (by rfl) ⟨2138688, by rfl⟩ : syracuseStep 5703169 = 4277377) B4277377
theorem B7604225 : Blo 2251435 7604225 := bstep (se 2 (by rfl) ⟨2851584, by rfl⟩ : syracuseStep 7604225 = 5703169) B5703169
theorem B5069483 : Blo 2251435 5069483 := bstep (se 1 (by rfl) ⟨3802112, by rfl⟩ : syracuseStep 5069483 = 7604225) B7604225
theorem B3379655 : Blo 2251435 3379655 := bstep (se 1 (by rfl) ⟨2534741, by rfl⟩ : syracuseStep 3379655 = 5069483) B5069483
theorem B2253103 : Blo 2251435 2253103 := bstep (se 1 (by rfl) ⟨1689827, by rfl⟩ : syracuseStep 2253103 = 3379655) B3379655
theorem B3379661 : Blo 2251435 3379661 := bbase (se 3 (by rfl) ⟨633686, by rfl⟩ : syracuseStep 3379661 = 1267373) (by norm_num)
theorem B2253107 : Blo 2251435 2253107 := bstep (se 1 (by rfl) ⟨1689830, by rfl⟩ : syracuseStep 2253107 = 3379661) B3379661
theorem B5069501 : Blo 2251435 5069501 := bbase (se 3 (by rfl) ⟨950531, by rfl⟩ : syracuseStep 5069501 = 1901063) (by norm_num)
theorem B3379667 : Blo 2251435 3379667 := bstep (se 1 (by rfl) ⟨2534750, by rfl⟩ : syracuseStep 3379667 = 5069501) B5069501
theorem B2253111 : Blo 2251435 2253111 := bstep (se 1 (by rfl) ⟨1689833, by rfl⟩ : syracuseStep 2253111 = 3379667) B3379667
theorem B3802133 : Blo 2251435 3802133 := bbase (se 6 (by rfl) ⟨89112, by rfl⟩ : syracuseStep 3802133 = 178225) (by norm_num)
theorem B2534755 : Blo 2251435 2534755 := bstep (se 1 (by rfl) ⟨1901066, by rfl⟩ : syracuseStep 2534755 = 3802133) B3802133
theorem B3379673 : Blo 2251435 3379673 := bstep (se 2 (by rfl) ⟨1267377, by rfl⟩ : syracuseStep 3379673 = 2534755) B2534755
theorem B2253115 : Blo 2251435 2253115 := bstep (se 1 (by rfl) ⟨1689836, by rfl⟩ : syracuseStep 2253115 = 3379673) B3379673
theorem B27780245 : Blo 2251435 27780245 := bbase (se 6 (by rfl) ⟨651099, by rfl⟩ : syracuseStep 27780245 = 1302199) (by norm_num)
theorem B18520163 : Blo 2251435 18520163 := bstep (se 1 (by rfl) ⟨13890122, by rfl⟩ : syracuseStep 18520163 = 27780245) B27780245
theorem B12346775 : Blo 2251435 12346775 := bstep (se 1 (by rfl) ⟨9260081, by rfl⟩ : syracuseStep 12346775 = 18520163) B18520163
theorem B8231183 : Blo 2251435 8231183 := bstep (se 1 (by rfl) ⟨6173387, by rfl⟩ : syracuseStep 8231183 = 12346775) B12346775
theorem B5487455 : Blo 2251435 5487455 := bstep (se 1 (by rfl) ⟨4115591, by rfl⟩ : syracuseStep 5487455 = 8231183) B8231183
theorem B3658303 : Blo 2251435 3658303 := bstep (se 1 (by rfl) ⟨2743727, by rfl⟩ : syracuseStep 3658303 = 5487455) B5487455
theorem B19510949 : Blo 2251435 19510949 := bstep (se 4 (by rfl) ⟨1829151, by rfl⟩ : syracuseStep 19510949 = 3658303) B3658303
theorem B13007299 : Blo 2251435 13007299 := bstep (se 1 (by rfl) ⟨9755474, by rfl⟩ : syracuseStep 13007299 = 19510949) B19510949
theorem B17343065 : Blo 2251435 17343065 := bstep (se 2 (by rfl) ⟨6503649, by rfl⟩ : syracuseStep 17343065 = 13007299) B13007299
theorem B11562043 : Blo 2251435 11562043 := bstep (se 1 (by rfl) ⟨8671532, by rfl⟩ : syracuseStep 11562043 = 17343065) B17343065
theorem B15416057 : Blo 2251435 15416057 := bstep (se 2 (by rfl) ⟨5781021, by rfl⟩ : syracuseStep 15416057 = 11562043) B11562043
theorem B10277371 : Blo 2251435 10277371 := bstep (se 1 (by rfl) ⟨7708028, by rfl⟩ : syracuseStep 10277371 = 15416057) B15416057
theorem B54812645 : Blo 2251435 54812645 := bstep (se 4 (by rfl) ⟨5138685, by rfl⟩ : syracuseStep 54812645 = 10277371) B10277371
theorem B36541763 : Blo 2251435 36541763 := bstep (se 1 (by rfl) ⟨27406322, by rfl⟩ : syracuseStep 36541763 = 54812645) B54812645
theorem B24361175 : Blo 2251435 24361175 := bstep (se 1 (by rfl) ⟨18270881, by rfl⟩ : syracuseStep 24361175 = 36541763) B36541763
theorem B16240783 : Blo 2251435 16240783 := bstep (se 1 (by rfl) ⟨12180587, by rfl⟩ : syracuseStep 16240783 = 24361175) B24361175
theorem B21654377 : Blo 2251435 21654377 := bstep (se 2 (by rfl) ⟨8120391, by rfl⟩ : syracuseStep 21654377 = 16240783) B16240783
theorem B14436251 : Blo 2251435 14436251 := bstep (se 1 (by rfl) ⟨10827188, by rfl⟩ : syracuseStep 14436251 = 21654377) B21654377
theorem B9624167 : Blo 2251435 9624167 := bstep (se 1 (by rfl) ⟨7218125, by rfl⟩ : syracuseStep 9624167 = 14436251) B14436251
theorem B6416111 : Blo 2251435 6416111 := bstep (se 1 (by rfl) ⟨4812083, by rfl⟩ : syracuseStep 6416111 = 9624167) B9624167
theorem B17109629 : Blo 2251435 17109629 := bstep (se 3 (by rfl) ⟨3208055, by rfl⟩ : syracuseStep 17109629 = 6416111) B6416111
theorem B11406419 : Blo 2251435 11406419 := bstep (se 1 (by rfl) ⟨8554814, by rfl⟩ : syracuseStep 11406419 = 17109629) B17109629
theorem B7604279 : Blo 2251435 7604279 := bstep (se 1 (by rfl) ⟨5703209, by rfl⟩ : syracuseStep 7604279 = 11406419) B11406419
theorem B5069519 : Blo 2251435 5069519 := bstep (se 1 (by rfl) ⟨3802139, by rfl⟩ : syracuseStep 5069519 = 7604279) B7604279
theorem B3379679 : Blo 2251435 3379679 := bstep (se 1 (by rfl) ⟨2534759, by rfl⟩ : syracuseStep 3379679 = 5069519) B5069519
theorem B2253119 : Blo 2251435 2253119 := bstep (se 1 (by rfl) ⟨1689839, by rfl⟩ : syracuseStep 2253119 = 3379679) B3379679
theorem B3379685 : Blo 2251435 3379685 := bbase (se 4 (by rfl) ⟨316845, by rfl⟩ : syracuseStep 3379685 = 633691) (by norm_num)
theorem B2253123 : Blo 2251435 2253123 := bstep (se 1 (by rfl) ⟨1689842, by rfl⟩ : syracuseStep 2253123 = 3379685) B3379685
theorem B2283869 : Blo 2251435 2283869 := bbase (se 3 (by rfl) ⟨428225, by rfl⟩ : syracuseStep 2283869 = 856451) (by norm_num)
theorem B6090317 : Blo 2251435 6090317 := bstep (se 3 (by rfl) ⟨1141934, by rfl⟩ : syracuseStep 6090317 = 2283869) B2283869
theorem B4060211 : Blo 2251435 4060211 := bstep (se 1 (by rfl) ⟨3045158, by rfl⟩ : syracuseStep 4060211 = 6090317) B6090317
theorem B10827229 : Blo 2251435 10827229 := bstep (se 3 (by rfl) ⟨2030105, by rfl⟩ : syracuseStep 10827229 = 4060211) B4060211
theorem B14436305 : Blo 2251435 14436305 := bstep (se 2 (by rfl) ⟨5413614, by rfl⟩ : syracuseStep 14436305 = 10827229) B10827229
theorem B9624203 : Blo 2251435 9624203 := bstep (se 1 (by rfl) ⟨7218152, by rfl⟩ : syracuseStep 9624203 = 14436305) B14436305
theorem B6416135 : Blo 2251435 6416135 := bstep (se 1 (by rfl) ⟨4812101, by rfl⟩ : syracuseStep 6416135 = 9624203) B9624203
theorem B4277423 : Blo 2251435 4277423 := bstep (se 1 (by rfl) ⟨3208067, by rfl⟩ : syracuseStep 4277423 = 6416135) B6416135
theorem B2851615 : Blo 2251435 2851615 := bstep (se 1 (by rfl) ⟨2138711, by rfl⟩ : syracuseStep 2851615 = 4277423) B4277423
theorem B3802153 : Blo 2251435 3802153 := bstep (se 2 (by rfl) ⟨1425807, by rfl⟩ : syracuseStep 3802153 = 2851615) B2851615
theorem B5069537 : Blo 2251435 5069537 := bstep (se 2 (by rfl) ⟨1901076, by rfl⟩ : syracuseStep 5069537 = 3802153) B3802153
theorem B3379691 : Blo 2251435 3379691 := bstep (se 1 (by rfl) ⟨2534768, by rfl⟩ : syracuseStep 3379691 = 5069537) B5069537
theorem B2253127 : Blo 2251435 2253127 := bstep (se 1 (by rfl) ⟨1689845, by rfl⟩ : syracuseStep 2253127 = 3379691) B3379691
theorem B2534773 : Blo 2251435 2534773 := bbase (se 5 (by rfl) ⟨118817, by rfl⟩ : syracuseStep 2534773 = 237635) (by norm_num)
theorem B3379697 : Blo 2251435 3379697 := bstep (se 2 (by rfl) ⟨1267386, by rfl⟩ : syracuseStep 3379697 = 2534773) B2534773
theorem B2253131 : Blo 2251435 2253131 := bstep (se 1 (by rfl) ⟨1689848, by rfl⟩ : syracuseStep 2253131 = 3379697) B3379697
theorem B2851625 : Blo 2251435 2851625 := bbase (se 2 (by rfl) ⟨1069359, by rfl⟩ : syracuseStep 2851625 = 2138719) (by norm_num)
theorem B7604333 : Blo 2251435 7604333 := bstep (se 3 (by rfl) ⟨1425812, by rfl⟩ : syracuseStep 7604333 = 2851625) B2851625
theorem B5069555 : Blo 2251435 5069555 := bstep (se 1 (by rfl) ⟨3802166, by rfl⟩ : syracuseStep 5069555 = 7604333) B7604333
theorem B3379703 : Blo 2251435 3379703 := bstep (se 1 (by rfl) ⟨2534777, by rfl⟩ : syracuseStep 3379703 = 5069555) B5069555
theorem B2253135 : Blo 2251435 2253135 := bstep (se 1 (by rfl) ⟨1689851, by rfl⟩ : syracuseStep 2253135 = 3379703) B3379703
theorem B3379709 : Blo 2251435 3379709 := bbase (se 3 (by rfl) ⟨633695, by rfl⟩ : syracuseStep 3379709 = 1267391) (by norm_num)
theorem B2253139 : Blo 2251435 2253139 := bstep (se 1 (by rfl) ⟨1689854, by rfl⟩ : syracuseStep 2253139 = 3379709) B3379709
theorem B5069573 : Blo 2251435 5069573 := bbase (se 4 (by rfl) ⟨475272, by rfl⟩ : syracuseStep 5069573 = 950545) (by norm_num)
theorem B3379715 : Blo 2251435 3379715 := bstep (se 1 (by rfl) ⟨2534786, by rfl⟩ : syracuseStep 3379715 = 5069573) B5069573
theorem B2253143 : Blo 2251435 2253143 := bstep (se 1 (by rfl) ⟨1689857, by rfl⟩ : syracuseStep 2253143 = 3379715) B3379715
theorem B4277461 : Blo 2251435 4277461 := bbase (se 7 (by rfl) ⟨50126, by rfl⟩ : syracuseStep 4277461 = 100253) (by norm_num)
theorem B5703281 : Blo 2251435 5703281 := bstep (se 2 (by rfl) ⟨2138730, by rfl⟩ : syracuseStep 5703281 = 4277461) B4277461
theorem B3802187 : Blo 2251435 3802187 := bstep (se 1 (by rfl) ⟨2851640, by rfl⟩ : syracuseStep 3802187 = 5703281) B5703281
theorem B2534791 : Blo 2251435 2534791 := bstep (se 1 (by rfl) ⟨1901093, by rfl⟩ : syracuseStep 2534791 = 3802187) B3802187
theorem B3379721 : Blo 2251435 3379721 := bstep (se 2 (by rfl) ⟨1267395, by rfl⟩ : syracuseStep 3379721 = 2534791) B2534791
theorem B2253147 : Blo 2251435 2253147 := bstep (se 1 (by rfl) ⟨1689860, by rfl⟩ : syracuseStep 2253147 = 3379721) B3379721
theorem B11406581 : Blo 2251435 11406581 := bbase (se 5 (by rfl) ⟨534683, by rfl⟩ : syracuseStep 11406581 = 1069367) (by norm_num)
theorem B7604387 : Blo 2251435 7604387 := bstep (se 1 (by rfl) ⟨5703290, by rfl⟩ : syracuseStep 7604387 = 11406581) B11406581
theorem B5069591 : Blo 2251435 5069591 := bstep (se 1 (by rfl) ⟨3802193, by rfl⟩ : syracuseStep 5069591 = 7604387) B7604387
theorem B3379727 : Blo 2251435 3379727 := bstep (se 1 (by rfl) ⟨2534795, by rfl⟩ : syracuseStep 3379727 = 5069591) B5069591
theorem B2253151 : Blo 2251435 2253151 := bstep (se 1 (by rfl) ⟨1689863, by rfl⟩ : syracuseStep 2253151 = 3379727) B3379727
theorem B3379733 : Blo 2251435 3379733 := bbase (se 6 (by rfl) ⟨79212, by rfl⟩ : syracuseStep 3379733 = 158425) (by norm_num)
theorem B2253155 : Blo 2251435 2253155 := bstep (se 1 (by rfl) ⟨1689866, by rfl⟩ : syracuseStep 2253155 = 3379733) B3379733
theorem B9135605 : Blo 2251435 9135605 := bbase (se 5 (by rfl) ⟨428231, by rfl⟩ : syracuseStep 9135605 = 856463) (by norm_num)
theorem B6090403 : Blo 2251435 6090403 := bstep (se 1 (by rfl) ⟨4567802, by rfl⟩ : syracuseStep 6090403 = 9135605) B9135605
theorem B8120537 : Blo 2251435 8120537 := bstep (se 2 (by rfl) ⟨3045201, by rfl⟩ : syracuseStep 8120537 = 6090403) B6090403
theorem B5413691 : Blo 2251435 5413691 := bstep (se 1 (by rfl) ⟨4060268, by rfl⟩ : syracuseStep 5413691 = 8120537) B8120537
theorem B3609127 : Blo 2251435 3609127 := bstep (se 1 (by rfl) ⟨2706845, by rfl⟩ : syracuseStep 3609127 = 5413691) B5413691
theorem B19248677 : Blo 2251435 19248677 := bstep (se 4 (by rfl) ⟨1804563, by rfl⟩ : syracuseStep 19248677 = 3609127) B3609127
theorem B12832451 : Blo 2251435 12832451 := bstep (se 1 (by rfl) ⟨9624338, by rfl⟩ : syracuseStep 12832451 = 19248677) B19248677
theorem B8554967 : Blo 2251435 8554967 := bstep (se 1 (by rfl) ⟨6416225, by rfl⟩ : syracuseStep 8554967 = 12832451) B12832451
theorem B5703311 : Blo 2251435 5703311 := bstep (se 1 (by rfl) ⟨4277483, by rfl⟩ : syracuseStep 5703311 = 8554967) B8554967
theorem B3802207 : Blo 2251435 3802207 := bstep (se 1 (by rfl) ⟨2851655, by rfl⟩ : syracuseStep 3802207 = 5703311) B5703311
theorem B5069609 : Blo 2251435 5069609 := bstep (se 2 (by rfl) ⟨1901103, by rfl⟩ : syracuseStep 5069609 = 3802207) B3802207
theorem B3379739 : Blo 2251435 3379739 := bstep (se 1 (by rfl) ⟨2534804, by rfl⟩ : syracuseStep 3379739 = 5069609) B5069609
theorem B2253159 : Blo 2251435 2253159 := bstep (se 1 (by rfl) ⟨1689869, by rfl⟩ : syracuseStep 2253159 = 3379739) B3379739
theorem B2534809 : Blo 2251435 2534809 := bbase (se 2 (by rfl) ⟨950553, by rfl⟩ : syracuseStep 2534809 = 1901107) (by norm_num)
theorem B3379745 : Blo 2251435 3379745 := bstep (se 2 (by rfl) ⟨1267404, by rfl⟩ : syracuseStep 3379745 = 2534809) B2534809
theorem B2253163 : Blo 2251435 2253163 := bstep (se 1 (by rfl) ⟨1689872, by rfl⟩ : syracuseStep 2253163 = 3379745) B3379745
theorem B8554997 : Blo 2251435 8554997 := bbase (se 5 (by rfl) ⟨401015, by rfl⟩ : syracuseStep 8554997 = 802031) (by norm_num)
theorem B5703331 : Blo 2251435 5703331 := bstep (se 1 (by rfl) ⟨4277498, by rfl⟩ : syracuseStep 5703331 = 8554997) B8554997
theorem B7604441 : Blo 2251435 7604441 := bstep (se 2 (by rfl) ⟨2851665, by rfl⟩ : syracuseStep 7604441 = 5703331) B5703331
theorem B5069627 : Blo 2251435 5069627 := bstep (se 1 (by rfl) ⟨3802220, by rfl⟩ : syracuseStep 5069627 = 7604441) B7604441
theorem B3379751 : Blo 2251435 3379751 := bstep (se 1 (by rfl) ⟨2534813, by rfl⟩ : syracuseStep 3379751 = 5069627) B5069627
theorem B2253167 : Blo 2251435 2253167 := bstep (se 1 (by rfl) ⟨1689875, by rfl⟩ : syracuseStep 2253167 = 3379751) B3379751
theorem B3379757 : Blo 2251435 3379757 := bbase (se 3 (by rfl) ⟨633704, by rfl⟩ : syracuseStep 3379757 = 1267409) (by norm_num)
theorem B2253171 : Blo 2251435 2253171 := bstep (se 1 (by rfl) ⟨1689878, by rfl⟩ : syracuseStep 2253171 = 3379757) B3379757
theorem B5069645 : Blo 2251435 5069645 := bbase (se 3 (by rfl) ⟨950558, by rfl⟩ : syracuseStep 5069645 = 1901117) (by norm_num)
theorem B3379763 : Blo 2251435 3379763 := bstep (se 1 (by rfl) ⟨2534822, by rfl⟩ : syracuseStep 3379763 = 5069645) B5069645
theorem B2253175 : Blo 2251435 2253175 := bstep (se 1 (by rfl) ⟨1689881, by rfl⟩ : syracuseStep 2253175 = 3379763) B3379763
theorem B2851681 : Blo 2251435 2851681 := bbase (se 2 (by rfl) ⟨1069380, by rfl⟩ : syracuseStep 2851681 = 2138761) (by norm_num)
theorem B3802241 : Blo 2251435 3802241 := bstep (se 2 (by rfl) ⟨1425840, by rfl⟩ : syracuseStep 3802241 = 2851681) B2851681
theorem B2534827 : Blo 2251435 2534827 := bstep (se 1 (by rfl) ⟨1901120, by rfl⟩ : syracuseStep 2534827 = 3802241) B3802241
theorem B3379769 : Blo 2251435 3379769 := bstep (se 2 (by rfl) ⟨1267413, by rfl⟩ : syracuseStep 3379769 = 2534827) B2534827
theorem B2253179 : Blo 2251435 2253179 := bstep (se 1 (by rfl) ⟨1689884, by rfl⟩ : syracuseStep 2253179 = 3379769) B3379769
theorem B25665173 : Blo 2251435 25665173 := bbase (se 6 (by rfl) ⟨601527, by rfl⟩ : syracuseStep 25665173 = 1203055) (by norm_num)
theorem B17110115 : Blo 2251435 17110115 := bstep (se 1 (by rfl) ⟨12832586, by rfl⟩ : syracuseStep 17110115 = 25665173) B25665173
theorem B11406743 : Blo 2251435 11406743 := bstep (se 1 (by rfl) ⟨8555057, by rfl⟩ : syracuseStep 11406743 = 17110115) B17110115
theorem B7604495 : Blo 2251435 7604495 := bstep (se 1 (by rfl) ⟨5703371, by rfl⟩ : syracuseStep 7604495 = 11406743) B11406743
theorem B5069663 : Blo 2251435 5069663 := bstep (se 1 (by rfl) ⟨3802247, by rfl⟩ : syracuseStep 5069663 = 7604495) B7604495
theorem B3379775 : Blo 2251435 3379775 := bstep (se 1 (by rfl) ⟨2534831, by rfl⟩ : syracuseStep 3379775 = 5069663) B5069663
theorem B2253183 : Blo 2251435 2253183 := bstep (se 1 (by rfl) ⟨1689887, by rfl⟩ : syracuseStep 2253183 = 3379775) B3379775
theorem B3379781 : Blo 2251435 3379781 := bbase (se 4 (by rfl) ⟨316854, by rfl⟩ : syracuseStep 3379781 = 633709) (by norm_num)
theorem B2253187 : Blo 2251435 2253187 := bstep (se 1 (by rfl) ⟨1689890, by rfl⟩ : syracuseStep 2253187 = 3379781) B3379781
theorem B3802261 : Blo 2251435 3802261 := bbase (se 6 (by rfl) ⟨89115, by rfl⟩ : syracuseStep 3802261 = 178231) (by norm_num)
theorem B5069681 : Blo 2251435 5069681 := bstep (se 2 (by rfl) ⟨1901130, by rfl⟩ : syracuseStep 5069681 = 3802261) B3802261
theorem B3379787 : Blo 2251435 3379787 := bstep (se 1 (by rfl) ⟨2534840, by rfl⟩ : syracuseStep 3379787 = 5069681) B5069681
theorem B2253191 : Blo 2251435 2253191 := bstep (se 1 (by rfl) ⟨1689893, by rfl⟩ : syracuseStep 2253191 = 3379787) B3379787
theorem B2534845 : Blo 2251435 2534845 := bbase (se 3 (by rfl) ⟨475283, by rfl⟩ : syracuseStep 2534845 = 950567) (by norm_num)
theorem B3379793 : Blo 2251435 3379793 := bstep (se 2 (by rfl) ⟨1267422, by rfl⟩ : syracuseStep 3379793 = 2534845) B2534845
theorem B2253195 : Blo 2251435 2253195 := bstep (se 1 (by rfl) ⟨1689896, by rfl⟩ : syracuseStep 2253195 = 3379793) B3379793
theorem B7604549 : Blo 2251435 7604549 := bbase (se 4 (by rfl) ⟨712926, by rfl⟩ : syracuseStep 7604549 = 1425853) (by norm_num)
theorem B5069699 : Blo 2251435 5069699 := bstep (se 1 (by rfl) ⟨3802274, by rfl⟩ : syracuseStep 5069699 = 7604549) B7604549
theorem B3379799 : Blo 2251435 3379799 := bstep (se 1 (by rfl) ⟨2534849, by rfl⟩ : syracuseStep 3379799 = 5069699) B5069699
theorem B2253199 : Blo 2251435 2253199 := bstep (se 1 (by rfl) ⟨1689899, by rfl⟩ : syracuseStep 2253199 = 3379799) B3379799
theorem B3379805 : Blo 2251435 3379805 := bbase (se 3 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 3379805 = 1267427) (by norm_num)
theorem B2253203 : Blo 2251435 2253203 := bstep (se 1 (by rfl) ⟨1689902, by rfl⟩ : syracuseStep 2253203 = 3379805) B3379805
theorem B5069717 : Blo 2251435 5069717 := bbase (se 6 (by rfl) ⟨118821, by rfl⟩ : syracuseStep 5069717 = 237643) (by norm_num)
theorem B3379811 : Blo 2251435 3379811 := bstep (se 1 (by rfl) ⟨2534858, by rfl⟩ : syracuseStep 3379811 = 5069717) B5069717
theorem B2253207 : Blo 2251435 2253207 := bstep (se 1 (by rfl) ⟨1689905, by rfl⟩ : syracuseStep 2253207 = 3379811) B3379811
theorem B4567909 : Blo 2251435 4567909 := bbase (se 4 (by rfl) ⟨428241, by rfl⟩ : syracuseStep 4567909 = 856483) (by norm_num)
theorem B6090545 : Blo 2251435 6090545 := bstep (se 2 (by rfl) ⟨2283954, by rfl⟩ : syracuseStep 6090545 = 4567909) B4567909
theorem B4060363 : Blo 2251435 4060363 := bstep (se 1 (by rfl) ⟨3045272, by rfl⟩ : syracuseStep 4060363 = 6090545) B6090545
theorem B5413817 : Blo 2251435 5413817 := bstep (se 2 (by rfl) ⟨2030181, by rfl⟩ : syracuseStep 5413817 = 4060363) B4060363
theorem B3609211 : Blo 2251435 3609211 := bstep (se 1 (by rfl) ⟨2706908, by rfl⟩ : syracuseStep 3609211 = 5413817) B5413817
theorem B4812281 : Blo 2251435 4812281 := bstep (se 2 (by rfl) ⟨1804605, by rfl⟩ : syracuseStep 4812281 = 3609211) B3609211
theorem B3208187 : Blo 2251435 3208187 := bstep (se 1 (by rfl) ⟨2406140, by rfl⟩ : syracuseStep 3208187 = 4812281) B4812281
theorem B8555165 : Blo 2251435 8555165 := bstep (se 3 (by rfl) ⟨1604093, by rfl⟩ : syracuseStep 8555165 = 3208187) B3208187
theorem B5703443 : Blo 2251435 5703443 := bstep (se 1 (by rfl) ⟨4277582, by rfl⟩ : syracuseStep 5703443 = 8555165) B8555165
theorem B3802295 : Blo 2251435 3802295 := bstep (se 1 (by rfl) ⟨2851721, by rfl⟩ : syracuseStep 3802295 = 5703443) B5703443
theorem B2534863 : Blo 2251435 2534863 := bstep (se 1 (by rfl) ⟨1901147, by rfl⟩ : syracuseStep 2534863 = 3802295) B3802295
theorem B3379817 : Blo 2251435 3379817 := bstep (se 2 (by rfl) ⟨1267431, by rfl⟩ : syracuseStep 3379817 = 2534863) B2534863
theorem B2253211 : Blo 2251435 2253211 := bstep (se 1 (by rfl) ⟨1689908, by rfl⟩ : syracuseStep 2253211 = 3379817) B3379817
theorem B3045277 : Blo 2251435 3045277 := bbase (se 3 (by rfl) ⟨570989, by rfl⟩ : syracuseStep 3045277 = 1141979) (by norm_num)
theorem B4060369 : Blo 2251435 4060369 := bstep (se 2 (by rfl) ⟨1522638, by rfl⟩ : syracuseStep 4060369 = 3045277) B3045277
theorem B5413825 : Blo 2251435 5413825 := bstep (se 2 (by rfl) ⟨2030184, by rfl⟩ : syracuseStep 5413825 = 4060369) B4060369
theorem B7218433 : Blo 2251435 7218433 := bstep (se 2 (by rfl) ⟨2706912, by rfl⟩ : syracuseStep 7218433 = 5413825) B5413825
theorem B9624577 : Blo 2251435 9624577 := bstep (se 2 (by rfl) ⟨3609216, by rfl⟩ : syracuseStep 9624577 = 7218433) B7218433
theorem B12832769 : Blo 2251435 12832769 := bstep (se 2 (by rfl) ⟨4812288, by rfl⟩ : syracuseStep 12832769 = 9624577) B9624577
theorem B8555179 : Blo 2251435 8555179 := bstep (se 1 (by rfl) ⟨6416384, by rfl⟩ : syracuseStep 8555179 = 12832769) B12832769
theorem B11406905 : Blo 2251435 11406905 := bstep (se 2 (by rfl) ⟨4277589, by rfl⟩ : syracuseStep 11406905 = 8555179) B8555179
theorem B7604603 : Blo 2251435 7604603 := bstep (se 1 (by rfl) ⟨5703452, by rfl⟩ : syracuseStep 7604603 = 11406905) B11406905
theorem B5069735 : Blo 2251435 5069735 := bstep (se 1 (by rfl) ⟨3802301, by rfl⟩ : syracuseStep 5069735 = 7604603) B7604603
theorem B3379823 : Blo 2251435 3379823 := bstep (se 1 (by rfl) ⟨2534867, by rfl⟩ : syracuseStep 3379823 = 5069735) B5069735
theorem B2253215 : Blo 2251435 2253215 := bstep (se 1 (by rfl) ⟨1689911, by rfl⟩ : syracuseStep 2253215 = 3379823) B3379823
theorem B3379829 : Blo 2251435 3379829 := bbase (se 5 (by rfl) ⟨158429, by rfl⟩ : syracuseStep 3379829 = 316859) (by norm_num)
theorem B2253219 : Blo 2251435 2253219 := bstep (se 1 (by rfl) ⟨1689914, by rfl⟩ : syracuseStep 2253219 = 3379829) B3379829
theorem B4277605 : Blo 2251435 4277605 := bbase (se 4 (by rfl) ⟨401025, by rfl⟩ : syracuseStep 4277605 = 802051) (by norm_num)
theorem B5703473 : Blo 2251435 5703473 := bstep (se 2 (by rfl) ⟨2138802, by rfl⟩ : syracuseStep 5703473 = 4277605) B4277605
theorem B3802315 : Blo 2251435 3802315 := bstep (se 1 (by rfl) ⟨2851736, by rfl⟩ : syracuseStep 3802315 = 5703473) B5703473
theorem B5069753 : Blo 2251435 5069753 := bstep (se 2 (by rfl) ⟨1901157, by rfl⟩ : syracuseStep 5069753 = 3802315) B3802315
theorem B3379835 : Blo 2251435 3379835 := bstep (se 1 (by rfl) ⟨2534876, by rfl⟩ : syracuseStep 3379835 = 5069753) B5069753
theorem B2253223 : Blo 2251435 2253223 := bstep (se 1 (by rfl) ⟨1689917, by rfl⟩ : syracuseStep 2253223 = 3379835) B3379835
theorem B2534881 : Blo 2251435 2534881 := bbase (se 2 (by rfl) ⟨950580, by rfl⟩ : syracuseStep 2534881 = 1901161) (by norm_num)
theorem B3379841 : Blo 2251435 3379841 := bstep (se 2 (by rfl) ⟨1267440, by rfl⟩ : syracuseStep 3379841 = 2534881) B2534881
theorem B2253227 : Blo 2251435 2253227 := bstep (se 1 (by rfl) ⟨1689920, by rfl⟩ : syracuseStep 2253227 = 3379841) B3379841
theorem B5703493 : Blo 2251435 5703493 := bbase (se 4 (by rfl) ⟨534702, by rfl⟩ : syracuseStep 5703493 = 1069405) (by norm_num)
theorem B7604657 : Blo 2251435 7604657 := bstep (se 2 (by rfl) ⟨2851746, by rfl⟩ : syracuseStep 7604657 = 5703493) B5703493
theorem B5069771 : Blo 2251435 5069771 := bstep (se 1 (by rfl) ⟨3802328, by rfl⟩ : syracuseStep 5069771 = 7604657) B7604657
theorem B3379847 : Blo 2251435 3379847 := bstep (se 1 (by rfl) ⟨2534885, by rfl⟩ : syracuseStep 3379847 = 5069771) B5069771
theorem B2253231 : Blo 2251435 2253231 := bstep (se 1 (by rfl) ⟨1689923, by rfl⟩ : syracuseStep 2253231 = 3379847) B3379847
theorem B3379853 : Blo 2251435 3379853 := bbase (se 3 (by rfl) ⟨633722, by rfl⟩ : syracuseStep 3379853 = 1267445) (by norm_num)
theorem B2253235 : Blo 2251435 2253235 := bstep (se 1 (by rfl) ⟨1689926, by rfl⟩ : syracuseStep 2253235 = 3379853) B3379853
theorem B5069789 : Blo 2251435 5069789 := bbase (se 3 (by rfl) ⟨950585, by rfl⟩ : syracuseStep 5069789 = 1901171) (by norm_num)
theorem B3379859 : Blo 2251435 3379859 := bstep (se 1 (by rfl) ⟨2534894, by rfl⟩ : syracuseStep 3379859 = 5069789) B5069789
theorem B2253239 : Blo 2251435 2253239 := bstep (se 1 (by rfl) ⟨1689929, by rfl⟩ : syracuseStep 2253239 = 3379859) B3379859
theorem B3802349 : Blo 2251435 3802349 := bbase (se 3 (by rfl) ⟨712940, by rfl⟩ : syracuseStep 3802349 = 1425881) (by norm_num)
theorem B2534899 : Blo 2251435 2534899 := bstep (se 1 (by rfl) ⟨1901174, by rfl⟩ : syracuseStep 2534899 = 3802349) B3802349
theorem B3379865 : Blo 2251435 3379865 := bstep (se 2 (by rfl) ⟨1267449, by rfl⟩ : syracuseStep 3379865 = 2534899) B2534899
theorem B2253243 : Blo 2251435 2253243 := bstep (se 1 (by rfl) ⟨1689932, by rfl⟩ : syracuseStep 2253243 = 3379865) B3379865
theorem B12347477 : Blo 2251435 12347477 := bbase (se 8 (by rfl) ⟨72348, by rfl⟩ : syracuseStep 12347477 = 144697) (by norm_num)
theorem B8231651 : Blo 2251435 8231651 := bstep (se 1 (by rfl) ⟨6173738, by rfl⟩ : syracuseStep 8231651 = 12347477) B12347477
theorem B5487767 : Blo 2251435 5487767 := bstep (se 1 (by rfl) ⟨4115825, by rfl⟩ : syracuseStep 5487767 = 8231651) B8231651
theorem B3658511 : Blo 2251435 3658511 := bstep (se 1 (by rfl) ⟨2743883, by rfl⟩ : syracuseStep 3658511 = 5487767) B5487767
theorem B2439007 : Blo 2251435 2439007 := bstep (se 1 (by rfl) ⟨1829255, by rfl⟩ : syracuseStep 2439007 = 3658511) B3658511
theorem B13008037 : Blo 2251435 13008037 := bstep (se 4 (by rfl) ⟨1219503, by rfl⟩ : syracuseStep 13008037 = 2439007) B2439007
theorem B17344049 : Blo 2251435 17344049 := bstep (se 2 (by rfl) ⟨6504018, by rfl⟩ : syracuseStep 17344049 = 13008037) B13008037
theorem B46250797 : Blo 2251435 46250797 := bstep (se 3 (by rfl) ⟨8672024, by rfl⟩ : syracuseStep 46250797 = 17344049) B17344049
theorem B61667729 : Blo 2251435 61667729 := bstep (se 2 (by rfl) ⟨23125398, by rfl⟩ : syracuseStep 61667729 = 46250797) B46250797
theorem B41111819 : Blo 2251435 41111819 := bstep (se 1 (by rfl) ⟨30833864, by rfl⟩ : syracuseStep 41111819 = 61667729) B61667729
theorem B27407879 : Blo 2251435 27407879 := bstep (se 1 (by rfl) ⟨20555909, by rfl⟩ : syracuseStep 27407879 = 41111819) B41111819
theorem B18271919 : Blo 2251435 18271919 := bstep (se 1 (by rfl) ⟨13703939, by rfl⟩ : syracuseStep 18271919 = 27407879) B27407879
theorem B12181279 : Blo 2251435 12181279 := bstep (se 1 (by rfl) ⟨9135959, by rfl⟩ : syracuseStep 12181279 = 18271919) B18271919
theorem B16241705 : Blo 2251435 16241705 := bstep (se 2 (by rfl) ⟨6090639, by rfl⟩ : syracuseStep 16241705 = 12181279) B12181279
theorem B10827803 : Blo 2251435 10827803 := bstep (se 1 (by rfl) ⟨8120852, by rfl⟩ : syracuseStep 10827803 = 16241705) B16241705
theorem B28874141 : Blo 2251435 28874141 := bstep (se 3 (by rfl) ⟨5413901, by rfl⟩ : syracuseStep 28874141 = 10827803) B10827803
theorem B19249427 : Blo 2251435 19249427 := bstep (se 1 (by rfl) ⟨14437070, by rfl⟩ : syracuseStep 19249427 = 28874141) B28874141
theorem B12832951 : Blo 2251435 12832951 := bstep (se 1 (by rfl) ⟨9624713, by rfl⟩ : syracuseStep 12832951 = 19249427) B19249427
theorem B17110601 : Blo 2251435 17110601 := bstep (se 2 (by rfl) ⟨6416475, by rfl⟩ : syracuseStep 17110601 = 12832951) B12832951
theorem B11407067 : Blo 2251435 11407067 := bstep (se 1 (by rfl) ⟨8555300, by rfl⟩ : syracuseStep 11407067 = 17110601) B17110601
theorem B7604711 : Blo 2251435 7604711 := bstep (se 1 (by rfl) ⟨5703533, by rfl⟩ : syracuseStep 7604711 = 11407067) B11407067
theorem B5069807 : Blo 2251435 5069807 := bstep (se 1 (by rfl) ⟨3802355, by rfl⟩ : syracuseStep 5069807 = 7604711) B7604711
theorem B3379871 : Blo 2251435 3379871 := bstep (se 1 (by rfl) ⟨2534903, by rfl⟩ : syracuseStep 3379871 = 5069807) B5069807
theorem B2253247 : Blo 2251435 2253247 := bstep (se 1 (by rfl) ⟨1689935, by rfl⟩ : syracuseStep 2253247 = 3379871) B3379871
theorem B3379877 : Blo 2251435 3379877 := bbase (se 4 (by rfl) ⟨316863, by rfl⟩ : syracuseStep 3379877 = 633727) (by norm_num)
theorem B2253251 : Blo 2251435 2253251 := bstep (se 1 (by rfl) ⟨1689938, by rfl⟩ : syracuseStep 2253251 = 3379877) B3379877
theorem B2851777 : Blo 2251435 2851777 := bbase (se 2 (by rfl) ⟨1069416, by rfl⟩ : syracuseStep 2851777 = 2138833) (by norm_num)
theorem B3802369 : Blo 2251435 3802369 := bstep (se 2 (by rfl) ⟨1425888, by rfl⟩ : syracuseStep 3802369 = 2851777) B2851777
theorem B5069825 : Blo 2251435 5069825 := bstep (se 2 (by rfl) ⟨1901184, by rfl⟩ : syracuseStep 5069825 = 3802369) B3802369
theorem B3379883 : Blo 2251435 3379883 := bstep (se 1 (by rfl) ⟨2534912, by rfl⟩ : syracuseStep 3379883 = 5069825) B5069825
theorem B2253255 : Blo 2251435 2253255 := bstep (se 1 (by rfl) ⟨1689941, by rfl⟩ : syracuseStep 2253255 = 3379883) B3379883
theorem B2534917 : Blo 2251435 2534917 := bbase (se 4 (by rfl) ⟨237648, by rfl⟩ : syracuseStep 2534917 = 475297) (by norm_num)
theorem B3379889 : Blo 2251435 3379889 := bstep (se 2 (by rfl) ⟨1267458, by rfl⟩ : syracuseStep 3379889 = 2534917) B2534917
theorem B2253259 : Blo 2251435 2253259 := bstep (se 1 (by rfl) ⟨1689944, by rfl⟩ : syracuseStep 2253259 = 3379889) B3379889
theorem B3208261 : Blo 2251435 3208261 := bbase (se 4 (by rfl) ⟨300774, by rfl⟩ : syracuseStep 3208261 = 601549) (by norm_num)
theorem B4277681 : Blo 2251435 4277681 := bstep (se 2 (by rfl) ⟨1604130, by rfl⟩ : syracuseStep 4277681 = 3208261) B3208261
theorem B2851787 : Blo 2251435 2851787 := bstep (se 1 (by rfl) ⟨2138840, by rfl⟩ : syracuseStep 2851787 = 4277681) B4277681
theorem B7604765 : Blo 2251435 7604765 := bstep (se 3 (by rfl) ⟨1425893, by rfl⟩ : syracuseStep 7604765 = 2851787) B2851787
theorem B5069843 : Blo 2251435 5069843 := bstep (se 1 (by rfl) ⟨3802382, by rfl⟩ : syracuseStep 5069843 = 7604765) B7604765
theorem B3379895 : Blo 2251435 3379895 := bstep (se 1 (by rfl) ⟨2534921, by rfl⟩ : syracuseStep 3379895 = 5069843) B5069843
theorem B2253263 : Blo 2251435 2253263 := bstep (se 1 (by rfl) ⟨1689947, by rfl⟩ : syracuseStep 2253263 = 3379895) B3379895
theorem B3379901 : Blo 2251435 3379901 := bbase (se 3 (by rfl) ⟨633731, by rfl⟩ : syracuseStep 3379901 = 1267463) (by norm_num)
theorem B2253267 : Blo 2251435 2253267 := bstep (se 1 (by rfl) ⟨1689950, by rfl⟩ : syracuseStep 2253267 = 3379901) B3379901
theorem B5069861 : Blo 2251435 5069861 := bbase (se 4 (by rfl) ⟨475299, by rfl⟩ : syracuseStep 5069861 = 950599) (by norm_num)
theorem B3379907 : Blo 2251435 3379907 := bstep (se 1 (by rfl) ⟨2534930, by rfl⟩ : syracuseStep 3379907 = 5069861) B5069861
theorem B2253271 : Blo 2251435 2253271 := bstep (se 1 (by rfl) ⟨1689953, by rfl⟩ : syracuseStep 2253271 = 3379907) B3379907
theorem B5703605 : Blo 2251435 5703605 := bbase (se 5 (by rfl) ⟨267356, by rfl⟩ : syracuseStep 5703605 = 534713) (by norm_num)
theorem B3802403 : Blo 2251435 3802403 := bstep (se 1 (by rfl) ⟨2851802, by rfl⟩ : syracuseStep 3802403 = 5703605) B5703605
theorem B2534935 : Blo 2251435 2534935 := bstep (se 1 (by rfl) ⟨1901201, by rfl⟩ : syracuseStep 2534935 = 3802403) B3802403
theorem B3379913 : Blo 2251435 3379913 := bstep (se 2 (by rfl) ⟨1267467, by rfl⟩ : syracuseStep 3379913 = 2534935) B2534935
theorem B2253275 : Blo 2251435 2253275 := bstep (se 1 (by rfl) ⟨1689956, by rfl⟩ : syracuseStep 2253275 = 3379913) B3379913
theorem B4878085 : Blo 2251435 4878085 := bbase (se 4 (by rfl) ⟨457320, by rfl⟩ : syracuseStep 4878085 = 914641) (by norm_num)
theorem B6504113 : Blo 2251435 6504113 := bstep (se 2 (by rfl) ⟨2439042, by rfl⟩ : syracuseStep 6504113 = 4878085) B4878085
theorem B4336075 : Blo 2251435 4336075 := bstep (se 1 (by rfl) ⟨3252056, by rfl⟩ : syracuseStep 4336075 = 6504113) B6504113
theorem B23125733 : Blo 2251435 23125733 := bstep (se 4 (by rfl) ⟨2168037, by rfl⟩ : syracuseStep 23125733 = 4336075) B4336075
theorem B15417155 : Blo 2251435 15417155 := bstep (se 1 (by rfl) ⟨11562866, by rfl⟩ : syracuseStep 15417155 = 23125733) B23125733
theorem B10278103 : Blo 2251435 10278103 := bstep (se 1 (by rfl) ⟨7708577, by rfl⟩ : syracuseStep 10278103 = 15417155) B15417155
theorem B13704137 : Blo 2251435 13704137 := bstep (se 2 (by rfl) ⟨5139051, by rfl⟩ : syracuseStep 13704137 = 10278103) B10278103
theorem B9136091 : Blo 2251435 9136091 := bstep (se 1 (by rfl) ⟨6852068, by rfl⟩ : syracuseStep 9136091 = 13704137) B13704137
theorem B6090727 : Blo 2251435 6090727 := bstep (se 1 (by rfl) ⟨4568045, by rfl⟩ : syracuseStep 6090727 = 9136091) B9136091
theorem B8120969 : Blo 2251435 8120969 := bstep (se 2 (by rfl) ⟨3045363, by rfl⟩ : syracuseStep 8120969 = 6090727) B6090727
theorem B5413979 : Blo 2251435 5413979 := bstep (se 1 (by rfl) ⟨4060484, by rfl⟩ : syracuseStep 5413979 = 8120969) B8120969
theorem B14437277 : Blo 2251435 14437277 := bstep (se 3 (by rfl) ⟨2706989, by rfl⟩ : syracuseStep 14437277 = 5413979) B5413979
theorem B9624851 : Blo 2251435 9624851 := bstep (se 1 (by rfl) ⟨7218638, by rfl⟩ : syracuseStep 9624851 = 14437277) B14437277
theorem B6416567 : Blo 2251435 6416567 := bstep (se 1 (by rfl) ⟨4812425, by rfl⟩ : syracuseStep 6416567 = 9624851) B9624851
theorem B4277711 : Blo 2251435 4277711 := bstep (se 1 (by rfl) ⟨3208283, by rfl⟩ : syracuseStep 4277711 = 6416567) B6416567
theorem B11407229 : Blo 2251435 11407229 := bstep (se 3 (by rfl) ⟨2138855, by rfl⟩ : syracuseStep 11407229 = 4277711) B4277711
theorem B7604819 : Blo 2251435 7604819 := bstep (se 1 (by rfl) ⟨5703614, by rfl⟩ : syracuseStep 7604819 = 11407229) B11407229
theorem B5069879 : Blo 2251435 5069879 := bstep (se 1 (by rfl) ⟨3802409, by rfl⟩ : syracuseStep 5069879 = 7604819) B7604819
theorem B3379919 : Blo 2251435 3379919 := bstep (se 1 (by rfl) ⟨2534939, by rfl⟩ : syracuseStep 3379919 = 5069879) B5069879
theorem B2253279 : Blo 2251435 2253279 := bstep (se 1 (by rfl) ⟨1689959, by rfl⟩ : syracuseStep 2253279 = 3379919) B3379919
theorem B3379925 : Blo 2251435 3379925 := bbase (se 7 (by rfl) ⟨39608, by rfl⟩ : syracuseStep 3379925 = 79217) (by norm_num)
theorem B2253283 : Blo 2251435 2253283 := bstep (se 1 (by rfl) ⟨1689962, by rfl⟩ : syracuseStep 2253283 = 3379925) B3379925
theorem B2604593 : Blo 2251435 2604593 := bbase (se 2 (by rfl) ⟨976722, by rfl⟩ : syracuseStep 2604593 = 1953445) (by norm_num)
theorem B6945581 : Blo 2251435 6945581 := bstep (se 3 (by rfl) ⟨1302296, by rfl⟩ : syracuseStep 6945581 = 2604593) B2604593
theorem B4630387 : Blo 2251435 4630387 := bstep (se 1 (by rfl) ⟨3472790, by rfl⟩ : syracuseStep 4630387 = 6945581) B6945581
theorem B6173849 : Blo 2251435 6173849 := bstep (se 2 (by rfl) ⟨2315193, by rfl⟩ : syracuseStep 6173849 = 4630387) B4630387
theorem B4115899 : Blo 2251435 4115899 := bstep (se 1 (by rfl) ⟨3086924, by rfl⟩ : syracuseStep 4115899 = 6173849) B6173849
theorem B21951461 : Blo 2251435 21951461 := bstep (se 4 (by rfl) ⟨2057949, by rfl⟩ : syracuseStep 21951461 = 4115899) B4115899
theorem B14634307 : Blo 2251435 14634307 := bstep (se 1 (by rfl) ⟨10975730, by rfl⟩ : syracuseStep 14634307 = 21951461) B21951461
theorem B19512409 : Blo 2251435 19512409 := bstep (se 2 (by rfl) ⟨7317153, by rfl⟩ : syracuseStep 19512409 = 14634307) B14634307
theorem B26016545 : Blo 2251435 26016545 := bstep (se 2 (by rfl) ⟨9756204, by rfl⟩ : syracuseStep 26016545 = 19512409) B19512409
theorem B17344363 : Blo 2251435 17344363 := bstep (se 1 (by rfl) ⟨13008272, by rfl⟩ : syracuseStep 17344363 = 26016545) B26016545
theorem B23125817 : Blo 2251435 23125817 := bstep (se 2 (by rfl) ⟨8672181, by rfl⟩ : syracuseStep 23125817 = 17344363) B17344363
theorem B15417211 : Blo 2251435 15417211 := bstep (se 1 (by rfl) ⟨11562908, by rfl⟩ : syracuseStep 15417211 = 23125817) B23125817
theorem B20556281 : Blo 2251435 20556281 := bstep (se 2 (by rfl) ⟨7708605, by rfl⟩ : syracuseStep 20556281 = 15417211) B15417211
theorem B13704187 : Blo 2251435 13704187 := bstep (se 1 (by rfl) ⟨10278140, by rfl⟩ : syracuseStep 13704187 = 20556281) B20556281
theorem B18272249 : Blo 2251435 18272249 := bstep (se 2 (by rfl) ⟨6852093, by rfl⟩ : syracuseStep 18272249 = 13704187) B13704187
theorem B12181499 : Blo 2251435 12181499 := bstep (se 1 (by rfl) ⟨9136124, by rfl⟩ : syracuseStep 12181499 = 18272249) B18272249
theorem B8120999 : Blo 2251435 8120999 := bstep (se 1 (by rfl) ⟨6090749, by rfl⟩ : syracuseStep 8120999 = 12181499) B12181499
theorem B5413999 : Blo 2251435 5413999 := bstep (se 1 (by rfl) ⟨4060499, by rfl⟩ : syracuseStep 5413999 = 8120999) B8120999
theorem B7218665 : Blo 2251435 7218665 := bstep (se 2 (by rfl) ⟨2706999, by rfl⟩ : syracuseStep 7218665 = 5413999) B5413999
theorem B4812443 : Blo 2251435 4812443 := bstep (se 1 (by rfl) ⟨3609332, by rfl⟩ : syracuseStep 4812443 = 7218665) B7218665
theorem B3208295 : Blo 2251435 3208295 := bstep (se 1 (by rfl) ⟨2406221, by rfl⟩ : syracuseStep 3208295 = 4812443) B4812443
theorem B8555453 : Blo 2251435 8555453 := bstep (se 3 (by rfl) ⟨1604147, by rfl⟩ : syracuseStep 8555453 = 3208295) B3208295
theorem B5703635 : Blo 2251435 5703635 := bstep (se 1 (by rfl) ⟨4277726, by rfl⟩ : syracuseStep 5703635 = 8555453) B8555453
theorem B3802423 : Blo 2251435 3802423 := bstep (se 1 (by rfl) ⟨2851817, by rfl⟩ : syracuseStep 3802423 = 5703635) B5703635
theorem B5069897 : Blo 2251435 5069897 := bstep (se 2 (by rfl) ⟨1901211, by rfl⟩ : syracuseStep 5069897 = 3802423) B3802423
theorem B3379931 : Blo 2251435 3379931 := bstep (se 1 (by rfl) ⟨2534948, by rfl⟩ : syracuseStep 3379931 = 5069897) B5069897
theorem B2253287 : Blo 2251435 2253287 := bstep (se 1 (by rfl) ⟨1689965, by rfl⟩ : syracuseStep 2253287 = 3379931) B3379931
theorem B2534953 : Blo 2251435 2534953 := bbase (se 2 (by rfl) ⟨950607, by rfl⟩ : syracuseStep 2534953 = 1901215) (by norm_num)
theorem B3379937 : Blo 2251435 3379937 := bstep (se 2 (by rfl) ⟨1267476, by rfl⟩ : syracuseStep 3379937 = 2534953) B2534953
theorem B2253291 : Blo 2251435 2253291 := bstep (se 1 (by rfl) ⟨1689968, by rfl⟩ : syracuseStep 2253291 = 3379937) B3379937
theorem B3854317 : Blo 2251435 3854317 := bbase (se 3 (by rfl) ⟨722684, by rfl⟩ : syracuseStep 3854317 = 1445369) (by norm_num)
theorem B5139089 : Blo 2251435 5139089 := bstep (se 2 (by rfl) ⟨1927158, by rfl⟩ : syracuseStep 5139089 = 3854317) B3854317
theorem B3426059 : Blo 2251435 3426059 := bstep (se 1 (by rfl) ⟨2569544, by rfl⟩ : syracuseStep 3426059 = 5139089) B5139089
theorem B2284039 : Blo 2251435 2284039 := bstep (se 1 (by rfl) ⟨1713029, by rfl⟩ : syracuseStep 2284039 = 3426059) B3426059
theorem B3045385 : Blo 2251435 3045385 := bstep (se 2 (by rfl) ⟨1142019, by rfl⟩ : syracuseStep 3045385 = 2284039) B2284039
theorem B4060513 : Blo 2251435 4060513 := bstep (se 2 (by rfl) ⟨1522692, by rfl⟩ : syracuseStep 4060513 = 3045385) B3045385
theorem B21656069 : Blo 2251435 21656069 := bstep (se 4 (by rfl) ⟨2030256, by rfl⟩ : syracuseStep 21656069 = 4060513) B4060513
theorem B14437379 : Blo 2251435 14437379 := bstep (se 1 (by rfl) ⟨10828034, by rfl⟩ : syracuseStep 14437379 = 21656069) B21656069
theorem B9624919 : Blo 2251435 9624919 := bstep (se 1 (by rfl) ⟨7218689, by rfl⟩ : syracuseStep 9624919 = 14437379) B14437379
theorem B12833225 : Blo 2251435 12833225 := bstep (se 2 (by rfl) ⟨4812459, by rfl⟩ : syracuseStep 12833225 = 9624919) B9624919
theorem B8555483 : Blo 2251435 8555483 := bstep (se 1 (by rfl) ⟨6416612, by rfl⟩ : syracuseStep 8555483 = 12833225) B12833225
theorem B5703655 : Blo 2251435 5703655 := bstep (se 1 (by rfl) ⟨4277741, by rfl⟩ : syracuseStep 5703655 = 8555483) B8555483
theorem B7604873 : Blo 2251435 7604873 := bstep (se 2 (by rfl) ⟨2851827, by rfl⟩ : syracuseStep 7604873 = 5703655) B5703655
theorem B5069915 : Blo 2251435 5069915 := bstep (se 1 (by rfl) ⟨3802436, by rfl⟩ : syracuseStep 5069915 = 7604873) B7604873
theorem B3379943 : Blo 2251435 3379943 := bstep (se 1 (by rfl) ⟨2534957, by rfl⟩ : syracuseStep 3379943 = 5069915) B5069915
theorem B2253295 : Blo 2251435 2253295 := bstep (se 1 (by rfl) ⟨1689971, by rfl⟩ : syracuseStep 2253295 = 3379943) B3379943
theorem B3379949 : Blo 2251435 3379949 := bbase (se 3 (by rfl) ⟨633740, by rfl⟩ : syracuseStep 3379949 = 1267481) (by norm_num)
theorem B2253299 : Blo 2251435 2253299 := bstep (se 1 (by rfl) ⟨1689974, by rfl⟩ : syracuseStep 2253299 = 3379949) B3379949
theorem B5069933 : Blo 2251435 5069933 := bbase (se 3 (by rfl) ⟨950612, by rfl⟩ : syracuseStep 5069933 = 1901225) (by norm_num)
theorem B3379955 : Blo 2251435 3379955 := bstep (se 1 (by rfl) ⟨2534966, by rfl⟩ : syracuseStep 3379955 = 5069933) B5069933
theorem B2253303 : Blo 2251435 2253303 := bstep (se 1 (by rfl) ⟨1689977, by rfl⟩ : syracuseStep 2253303 = 3379955) B3379955
theorem B4277765 : Blo 2251435 4277765 := bbase (se 4 (by rfl) ⟨401040, by rfl⟩ : syracuseStep 4277765 = 802081) (by norm_num)
theorem B2851843 : Blo 2251435 2851843 := bstep (se 1 (by rfl) ⟨2138882, by rfl⟩ : syracuseStep 2851843 = 4277765) B4277765
theorem B3802457 : Blo 2251435 3802457 := bstep (se 2 (by rfl) ⟨1425921, by rfl⟩ : syracuseStep 3802457 = 2851843) B2851843
theorem B2534971 : Blo 2251435 2534971 := bstep (se 1 (by rfl) ⟨1901228, by rfl⟩ : syracuseStep 2534971 = 3802457) B3802457
theorem B3379961 : Blo 2251435 3379961 := bstep (se 2 (by rfl) ⟨1267485, by rfl⟩ : syracuseStep 3379961 = 2534971) B2534971
theorem B2253307 : Blo 2251435 2253307 := bstep (se 1 (by rfl) ⟨1689980, by rfl⟩ : syracuseStep 2253307 = 3379961) B3379961
theorem B2743961 : Blo 2251435 2743961 := bbase (se 2 (by rfl) ⟨1028985, by rfl⟩ : syracuseStep 2743961 = 2057971) (by norm_num)
theorem B7317229 : Blo 2251435 7317229 := bstep (se 3 (by rfl) ⟨1371980, by rfl⟩ : syracuseStep 7317229 = 2743961) B2743961
theorem B9756305 : Blo 2251435 9756305 := bstep (se 2 (by rfl) ⟨3658614, by rfl⟩ : syracuseStep 9756305 = 7317229) B7317229
theorem B6504203 : Blo 2251435 6504203 := bstep (se 1 (by rfl) ⟨4878152, by rfl⟩ : syracuseStep 6504203 = 9756305) B9756305
theorem B4336135 : Blo 2251435 4336135 := bstep (se 1 (by rfl) ⟨3252101, by rfl⟩ : syracuseStep 4336135 = 6504203) B6504203
theorem B92504213 : Blo 2251435 92504213 := bstep (se 6 (by rfl) ⟨2168067, by rfl⟩ : syracuseStep 92504213 = 4336135) B4336135
theorem B61669475 : Blo 2251435 61669475 := bstep (se 1 (by rfl) ⟨46252106, by rfl⟩ : syracuseStep 61669475 = 92504213) B92504213
theorem B41112983 : Blo 2251435 41112983 := bstep (se 1 (by rfl) ⟨30834737, by rfl⟩ : syracuseStep 41112983 = 61669475) B61669475
theorem B27408655 : Blo 2251435 27408655 := bstep (se 1 (by rfl) ⟨20556491, by rfl⟩ : syracuseStep 27408655 = 41112983) B41112983
theorem B36544873 : Blo 2251435 36544873 := bstep (se 2 (by rfl) ⟨13704327, by rfl⟩ : syracuseStep 36544873 = 27408655) B27408655
theorem B48726497 : Blo 2251435 48726497 := bstep (se 2 (by rfl) ⟨18272436, by rfl⟩ : syracuseStep 48726497 = 36544873) B36544873
theorem B32484331 : Blo 2251435 32484331 := bstep (se 1 (by rfl) ⟨24363248, by rfl⟩ : syracuseStep 32484331 = 48726497) B48726497
theorem B43312441 : Blo 2251435 43312441 := bstep (se 2 (by rfl) ⟨16242165, by rfl⟩ : syracuseStep 43312441 = 32484331) B32484331
theorem B57749921 : Blo 2251435 57749921 := bstep (se 2 (by rfl) ⟨21656220, by rfl⟩ : syracuseStep 57749921 = 43312441) B43312441
theorem B38499947 : Blo 2251435 38499947 := bstep (se 1 (by rfl) ⟨28874960, by rfl⟩ : syracuseStep 38499947 = 57749921) B57749921
theorem B25666631 : Blo 2251435 25666631 := bstep (se 1 (by rfl) ⟨19249973, by rfl⟩ : syracuseStep 25666631 = 38499947) B38499947
theorem B17111087 : Blo 2251435 17111087 := bstep (se 1 (by rfl) ⟨12833315, by rfl⟩ : syracuseStep 17111087 = 25666631) B25666631
theorem B11407391 : Blo 2251435 11407391 := bstep (se 1 (by rfl) ⟨8555543, by rfl⟩ : syracuseStep 11407391 = 17111087) B17111087
theorem B7604927 : Blo 2251435 7604927 := bstep (se 1 (by rfl) ⟨5703695, by rfl⟩ : syracuseStep 7604927 = 11407391) B11407391
theorem B5069951 : Blo 2251435 5069951 := bstep (se 1 (by rfl) ⟨3802463, by rfl⟩ : syracuseStep 5069951 = 7604927) B7604927
theorem B3379967 : Blo 2251435 3379967 := bstep (se 1 (by rfl) ⟨2534975, by rfl⟩ : syracuseStep 3379967 = 5069951) B5069951
theorem B2253311 : Blo 2251435 2253311 := bstep (se 1 (by rfl) ⟨1689983, by rfl⟩ : syracuseStep 2253311 = 3379967) B3379967
theorem B3379973 : Blo 2251435 3379973 := bbase (se 4 (by rfl) ⟨316872, by rfl⟩ : syracuseStep 3379973 = 633745) (by norm_num)
theorem B2253315 : Blo 2251435 2253315 := bstep (se 1 (by rfl) ⟨1689986, by rfl⟩ : syracuseStep 2253315 = 3379973) B3379973
theorem B3802477 : Blo 2251435 3802477 := bbase (se 3 (by rfl) ⟨712964, by rfl⟩ : syracuseStep 3802477 = 1425929) (by norm_num)
theorem B5069969 : Blo 2251435 5069969 := bstep (se 2 (by rfl) ⟨1901238, by rfl⟩ : syracuseStep 5069969 = 3802477) B3802477
theorem B3379979 : Blo 2251435 3379979 := bstep (se 1 (by rfl) ⟨2534984, by rfl⟩ : syracuseStep 3379979 = 5069969) B5069969
theorem B2253319 : Blo 2251435 2253319 := bstep (se 1 (by rfl) ⟨1689989, by rfl⟩ : syracuseStep 2253319 = 3379979) B3379979
theorem B2534989 : Blo 2251435 2534989 := bbase (se 3 (by rfl) ⟨475310, by rfl⟩ : syracuseStep 2534989 = 950621) (by norm_num)
theorem B3379985 : Blo 2251435 3379985 := bstep (se 2 (by rfl) ⟨1267494, by rfl⟩ : syracuseStep 3379985 = 2534989) B2534989
theorem B2253323 : Blo 2251435 2253323 := bstep (se 1 (by rfl) ⟨1689992, by rfl⟩ : syracuseStep 2253323 = 3379985) B3379985
theorem B7604981 : Blo 2251435 7604981 := bbase (se 5 (by rfl) ⟨356483, by rfl⟩ : syracuseStep 7604981 = 712967) (by norm_num)
theorem B5069987 : Blo 2251435 5069987 := bstep (se 1 (by rfl) ⟨3802490, by rfl⟩ : syracuseStep 5069987 = 7604981) B7604981
theorem B3379991 : Blo 2251435 3379991 := bstep (se 1 (by rfl) ⟨2534993, by rfl⟩ : syracuseStep 3379991 = 5069987) B5069987
theorem B2253327 : Blo 2251435 2253327 := bstep (se 1 (by rfl) ⟨1689995, by rfl⟩ : syracuseStep 2253327 = 3379991) B3379991
theorem B3379997 : Blo 2251435 3379997 := bbase (se 3 (by rfl) ⟨633749, by rfl⟩ : syracuseStep 3379997 = 1267499) (by norm_num)
theorem B2253331 : Blo 2251435 2253331 := bstep (se 1 (by rfl) ⟨1689998, by rfl⟩ : syracuseStep 2253331 = 3379997) B3379997
theorem B5070005 : Blo 2251435 5070005 := bbase (se 5 (by rfl) ⟨237656, by rfl⟩ : syracuseStep 5070005 = 475313) (by norm_num)
theorem B3380003 : Blo 2251435 3380003 := bstep (se 1 (by rfl) ⟨2535002, by rfl⟩ : syracuseStep 3380003 = 5070005) B5070005
theorem B2253335 : Blo 2251435 2253335 := bstep (se 1 (by rfl) ⟨1690001, by rfl⟩ : syracuseStep 2253335 = 3380003) B3380003
theorem B2406277 : Blo 2251435 2406277 := bbase (se 4 (by rfl) ⟨225588, by rfl⟩ : syracuseStep 2406277 = 451177) (by norm_num)
theorem B12833477 : Blo 2251435 12833477 := bstep (se 4 (by rfl) ⟨1203138, by rfl⟩ : syracuseStep 12833477 = 2406277) B2406277
theorem B8555651 : Blo 2251435 8555651 := bstep (se 1 (by rfl) ⟨6416738, by rfl⟩ : syracuseStep 8555651 = 12833477) B12833477
theorem B5703767 : Blo 2251435 5703767 := bstep (se 1 (by rfl) ⟨4277825, by rfl⟩ : syracuseStep 5703767 = 8555651) B8555651
theorem B3802511 : Blo 2251435 3802511 := bstep (se 1 (by rfl) ⟨2851883, by rfl⟩ : syracuseStep 3802511 = 5703767) B5703767
theorem B2535007 : Blo 2251435 2535007 := bstep (se 1 (by rfl) ⟨1901255, by rfl⟩ : syracuseStep 2535007 = 3802511) B3802511
theorem B3380009 : Blo 2251435 3380009 := bstep (se 2 (by rfl) ⟨1267503, by rfl⟩ : syracuseStep 3380009 = 2535007) B2535007
theorem B2253339 : Blo 2251435 2253339 := bstep (se 1 (by rfl) ⟨1690004, by rfl⟩ : syracuseStep 2253339 = 3380009) B3380009
theorem B2406281 : Blo 2251435 2406281 := bbase (se 2 (by rfl) ⟨902355, by rfl⟩ : syracuseStep 2406281 = 1804711) (by norm_num)
theorem B6416749 : Blo 2251435 6416749 := bstep (se 3 (by rfl) ⟨1203140, by rfl⟩ : syracuseStep 6416749 = 2406281) B2406281
theorem B8555665 : Blo 2251435 8555665 := bstep (se 2 (by rfl) ⟨3208374, by rfl⟩ : syracuseStep 8555665 = 6416749) B6416749
theorem B11407553 : Blo 2251435 11407553 := bstep (se 2 (by rfl) ⟨4277832, by rfl⟩ : syracuseStep 11407553 = 8555665) B8555665
theorem B7605035 : Blo 2251435 7605035 := bstep (se 1 (by rfl) ⟨5703776, by rfl⟩ : syracuseStep 7605035 = 11407553) B11407553
theorem B5070023 : Blo 2251435 5070023 := bstep (se 1 (by rfl) ⟨3802517, by rfl⟩ : syracuseStep 5070023 = 7605035) B7605035
theorem B3380015 : Blo 2251435 3380015 := bstep (se 1 (by rfl) ⟨2535011, by rfl⟩ : syracuseStep 3380015 = 5070023) B5070023
theorem B2253343 : Blo 2251435 2253343 := bstep (se 1 (by rfl) ⟨1690007, by rfl⟩ : syracuseStep 2253343 = 3380015) B3380015
theorem B3380021 : Blo 2251435 3380021 := bbase (se 5 (by rfl) ⟨158438, by rfl⟩ : syracuseStep 3380021 = 316877) (by norm_num)
theorem B2253347 : Blo 2251435 2253347 := bstep (se 1 (by rfl) ⟨1690010, by rfl⟩ : syracuseStep 2253347 = 3380021) B3380021
theorem B5703797 : Blo 2251435 5703797 := bbase (se 5 (by rfl) ⟨267365, by rfl⟩ : syracuseStep 5703797 = 534731) (by norm_num)
theorem B3802531 : Blo 2251435 3802531 := bstep (se 1 (by rfl) ⟨2851898, by rfl⟩ : syracuseStep 3802531 = 5703797) B5703797
theorem B5070041 : Blo 2251435 5070041 := bstep (se 2 (by rfl) ⟨1901265, by rfl⟩ : syracuseStep 5070041 = 3802531) B3802531
theorem B3380027 : Blo 2251435 3380027 := bstep (se 1 (by rfl) ⟨2535020, by rfl⟩ : syracuseStep 3380027 = 5070041) B5070041
theorem B2253351 : Blo 2251435 2253351 := bstep (se 1 (by rfl) ⟨1690013, by rfl⟩ : syracuseStep 2253351 = 3380027) B3380027
theorem B2535025 : Blo 2251435 2535025 := bbase (se 2 (by rfl) ⟨950634, by rfl⟩ : syracuseStep 2535025 = 1901269) (by norm_num)
theorem B3380033 : Blo 2251435 3380033 := bstep (se 2 (by rfl) ⟨1267512, by rfl⟩ : syracuseStep 3380033 = 2535025) B2535025
theorem B2253355 : Blo 2251435 2253355 := bstep (se 1 (by rfl) ⟨1690016, by rfl⟩ : syracuseStep 2253355 = 3380033) B3380033
theorem B14634773 : Blo 2251435 14634773 := bbase (se 6 (by rfl) ⟨343002, by rfl⟩ : syracuseStep 14634773 = 686005) (by norm_num)
theorem B9756515 : Blo 2251435 9756515 := bstep (se 1 (by rfl) ⟨7317386, by rfl⟩ : syracuseStep 9756515 = 14634773) B14634773
theorem B6504343 : Blo 2251435 6504343 := bstep (se 1 (by rfl) ⟨4878257, by rfl⟩ : syracuseStep 6504343 = 9756515) B9756515
theorem B34689829 : Blo 2251435 34689829 := bstep (se 4 (by rfl) ⟨3252171, by rfl⟩ : syracuseStep 34689829 = 6504343) B6504343
theorem B46253105 : Blo 2251435 46253105 := bstep (se 2 (by rfl) ⟨17344914, by rfl⟩ : syracuseStep 46253105 = 34689829) B34689829
theorem B30835403 : Blo 2251435 30835403 := bstep (se 1 (by rfl) ⟨23126552, by rfl⟩ : syracuseStep 30835403 = 46253105) B46253105
theorem B20556935 : Blo 2251435 20556935 := bstep (se 1 (by rfl) ⟨15417701, by rfl⟩ : syracuseStep 20556935 = 30835403) B30835403
theorem B13704623 : Blo 2251435 13704623 := bstep (se 1 (by rfl) ⟨10278467, by rfl⟩ : syracuseStep 13704623 = 20556935) B20556935
theorem B9136415 : Blo 2251435 9136415 := bstep (se 1 (by rfl) ⟨6852311, by rfl⟩ : syracuseStep 9136415 = 13704623) B13704623
theorem B24363773 : Blo 2251435 24363773 := bstep (se 3 (by rfl) ⟨4568207, by rfl⟩ : syracuseStep 24363773 = 9136415) B9136415
theorem B16242515 : Blo 2251435 16242515 := bstep (se 1 (by rfl) ⟨12181886, by rfl⟩ : syracuseStep 16242515 = 24363773) B24363773
theorem B10828343 : Blo 2251435 10828343 := bstep (se 1 (by rfl) ⟨8121257, by rfl⟩ : syracuseStep 10828343 = 16242515) B16242515
theorem B7218895 : Blo 2251435 7218895 := bstep (se 1 (by rfl) ⟨5414171, by rfl⟩ : syracuseStep 7218895 = 10828343) B10828343
theorem B9625193 : Blo 2251435 9625193 := bstep (se 2 (by rfl) ⟨3609447, by rfl⟩ : syracuseStep 9625193 = 7218895) B7218895
theorem B6416795 : Blo 2251435 6416795 := bstep (se 1 (by rfl) ⟨4812596, by rfl⟩ : syracuseStep 6416795 = 9625193) B9625193
theorem B4277863 : Blo 2251435 4277863 := bstep (se 1 (by rfl) ⟨3208397, by rfl⟩ : syracuseStep 4277863 = 6416795) B6416795
theorem B5703817 : Blo 2251435 5703817 := bstep (se 2 (by rfl) ⟨2138931, by rfl⟩ : syracuseStep 5703817 = 4277863) B4277863
theorem B7605089 : Blo 2251435 7605089 := bstep (se 2 (by rfl) ⟨2851908, by rfl⟩ : syracuseStep 7605089 = 5703817) B5703817
theorem B5070059 : Blo 2251435 5070059 := bstep (se 1 (by rfl) ⟨3802544, by rfl⟩ : syracuseStep 5070059 = 7605089) B7605089
theorem B3380039 : Blo 2251435 3380039 := bstep (se 1 (by rfl) ⟨2535029, by rfl⟩ : syracuseStep 3380039 = 5070059) B5070059
theorem B2253359 : Blo 2251435 2253359 := bstep (se 1 (by rfl) ⟨1690019, by rfl⟩ : syracuseStep 2253359 = 3380039) B3380039
theorem B3380045 : Blo 2251435 3380045 := bbase (se 3 (by rfl) ⟨633758, by rfl⟩ : syracuseStep 3380045 = 1267517) (by norm_num)
theorem B2253363 : Blo 2251435 2253363 := bstep (se 1 (by rfl) ⟨1690022, by rfl⟩ : syracuseStep 2253363 = 3380045) B3380045
theorem B5070077 : Blo 2251435 5070077 := bbase (se 3 (by rfl) ⟨950639, by rfl⟩ : syracuseStep 5070077 = 1901279) (by norm_num)
theorem B3380051 : Blo 2251435 3380051 := bstep (se 1 (by rfl) ⟨2535038, by rfl⟩ : syracuseStep 3380051 = 5070077) B5070077
theorem B2253367 : Blo 2251435 2253367 := bstep (se 1 (by rfl) ⟨1690025, by rfl⟩ : syracuseStep 2253367 = 3380051) B3380051
theorem B3802565 : Blo 2251435 3802565 := bbase (se 4 (by rfl) ⟨356490, by rfl⟩ : syracuseStep 3802565 = 712981) (by norm_num)
theorem B2535043 : Blo 2251435 2535043 := bstep (se 1 (by rfl) ⟨1901282, by rfl⟩ : syracuseStep 2535043 = 3802565) B3802565
theorem B3380057 : Blo 2251435 3380057 := bstep (se 2 (by rfl) ⟨1267521, by rfl⟩ : syracuseStep 3380057 = 2535043) B2535043
theorem B2253371 : Blo 2251435 2253371 := bstep (se 1 (by rfl) ⟨1690028, by rfl⟩ : syracuseStep 2253371 = 3380057) B3380057
theorem B17111573 : Blo 2251435 17111573 := bbase (se 6 (by rfl) ⟨401052, by rfl⟩ : syracuseStep 17111573 = 802105) (by norm_num)
theorem B11407715 : Blo 2251435 11407715 := bstep (se 1 (by rfl) ⟨8555786, by rfl⟩ : syracuseStep 11407715 = 17111573) B17111573
theorem B7605143 : Blo 2251435 7605143 := bstep (se 1 (by rfl) ⟨5703857, by rfl⟩ : syracuseStep 7605143 = 11407715) B11407715
theorem B5070095 : Blo 2251435 5070095 := bstep (se 1 (by rfl) ⟨3802571, by rfl⟩ : syracuseStep 5070095 = 7605143) B7605143
theorem B3380063 : Blo 2251435 3380063 := bstep (se 1 (by rfl) ⟨2535047, by rfl⟩ : syracuseStep 3380063 = 5070095) B5070095
theorem B2253375 : Blo 2251435 2253375 := bstep (se 1 (by rfl) ⟨1690031, by rfl⟩ : syracuseStep 2253375 = 3380063) B3380063
theorem B3380069 : Blo 2251435 3380069 := bbase (se 4 (by rfl) ⟨316881, by rfl⟩ : syracuseStep 3380069 = 633763) (by norm_num)
theorem B2253379 : Blo 2251435 2253379 := bstep (se 1 (by rfl) ⟨1690034, by rfl⟩ : syracuseStep 2253379 = 3380069) B3380069
theorem B4277909 : Blo 2251435 4277909 := bbase (se 6 (by rfl) ⟨100263, by rfl⟩ : syracuseStep 4277909 = 200527) (by norm_num)
theorem B2851939 : Blo 2251435 2851939 := bstep (se 1 (by rfl) ⟨2138954, by rfl⟩ : syracuseStep 2851939 = 4277909) B4277909
theorem B3802585 : Blo 2251435 3802585 := bstep (se 2 (by rfl) ⟨1425969, by rfl⟩ : syracuseStep 3802585 = 2851939) B2851939
theorem B5070113 : Blo 2251435 5070113 := bstep (se 2 (by rfl) ⟨1901292, by rfl⟩ : syracuseStep 5070113 = 3802585) B3802585
theorem B3380075 : Blo 2251435 3380075 := bstep (se 1 (by rfl) ⟨2535056, by rfl⟩ : syracuseStep 3380075 = 5070113) B5070113
theorem B2253383 : Blo 2251435 2253383 := bstep (se 1 (by rfl) ⟨1690037, by rfl⟩ : syracuseStep 2253383 = 3380075) B3380075
theorem B2535061 : Blo 2251435 2535061 := bbase (se 6 (by rfl) ⟨59415, by rfl⟩ : syracuseStep 2535061 = 118831) (by norm_num)
theorem B3380081 : Blo 2251435 3380081 := bstep (se 2 (by rfl) ⟨1267530, by rfl⟩ : syracuseStep 3380081 = 2535061) B2535061
theorem B2253387 : Blo 2251435 2253387 := bstep (se 1 (by rfl) ⟨1690040, by rfl⟩ : syracuseStep 2253387 = 3380081) B3380081
theorem B2851949 : Blo 2251435 2851949 := bbase (se 3 (by rfl) ⟨534740, by rfl⟩ : syracuseStep 2851949 = 1069481) (by norm_num)
theorem B7605197 : Blo 2251435 7605197 := bstep (se 3 (by rfl) ⟨1425974, by rfl⟩ : syracuseStep 7605197 = 2851949) B2851949
theorem B5070131 : Blo 2251435 5070131 := bstep (se 1 (by rfl) ⟨3802598, by rfl⟩ : syracuseStep 5070131 = 7605197) B7605197
theorem B3380087 : Blo 2251435 3380087 := bstep (se 1 (by rfl) ⟨2535065, by rfl⟩ : syracuseStep 3380087 = 5070131) B5070131
theorem B2253391 : Blo 2251435 2253391 := bstep (se 1 (by rfl) ⟨1690043, by rfl⟩ : syracuseStep 2253391 = 3380087) B3380087
theorem B3380093 : Blo 2251435 3380093 := bbase (se 3 (by rfl) ⟨633767, by rfl⟩ : syracuseStep 3380093 = 1267535) (by norm_num)
theorem B2253395 : Blo 2251435 2253395 := bstep (se 1 (by rfl) ⟨1690046, by rfl⟩ : syracuseStep 2253395 = 3380093) B3380093
theorem B5070149 : Blo 2251435 5070149 := bbase (se 4 (by rfl) ⟨475326, by rfl⟩ : syracuseStep 5070149 = 950653) (by norm_num)
theorem B3380099 : Blo 2251435 3380099 := bstep (se 1 (by rfl) ⟨2535074, by rfl⟩ : syracuseStep 3380099 = 5070149) B5070149
theorem B2253399 : Blo 2251435 2253399 := bstep (se 1 (by rfl) ⟨1690049, by rfl⟩ : syracuseStep 2253399 = 3380099) B3380099
theorem B4060709 : Blo 2251435 4060709 := bbase (se 4 (by rfl) ⟨380691, by rfl⟩ : syracuseStep 4060709 = 761383) (by norm_num)
theorem B2707139 : Blo 2251435 2707139 := bstep (se 1 (by rfl) ⟨2030354, by rfl⟩ : syracuseStep 2707139 = 4060709) B4060709
theorem B7219037 : Blo 2251435 7219037 := bstep (se 3 (by rfl) ⟨1353569, by rfl⟩ : syracuseStep 7219037 = 2707139) B2707139
theorem B4812691 : Blo 2251435 4812691 := bstep (se 1 (by rfl) ⟨3609518, by rfl⟩ : syracuseStep 4812691 = 7219037) B7219037
theorem B6416921 : Blo 2251435 6416921 := bstep (se 2 (by rfl) ⟨2406345, by rfl⟩ : syracuseStep 6416921 = 4812691) B4812691
theorem B4277947 : Blo 2251435 4277947 := bstep (se 1 (by rfl) ⟨3208460, by rfl⟩ : syracuseStep 4277947 = 6416921) B6416921
theorem B5703929 : Blo 2251435 5703929 := bstep (se 2 (by rfl) ⟨2138973, by rfl⟩ : syracuseStep 5703929 = 4277947) B4277947
theorem B3802619 : Blo 2251435 3802619 := bstep (se 1 (by rfl) ⟨2851964, by rfl⟩ : syracuseStep 3802619 = 5703929) B5703929
theorem B2535079 : Blo 2251435 2535079 := bstep (se 1 (by rfl) ⟨1901309, by rfl⟩ : syracuseStep 2535079 = 3802619) B3802619
theorem B3380105 : Blo 2251435 3380105 := bstep (se 2 (by rfl) ⟨1267539, by rfl⟩ : syracuseStep 3380105 = 2535079) B2535079
theorem B2253403 : Blo 2251435 2253403 := bstep (se 1 (by rfl) ⟨1690052, by rfl⟩ : syracuseStep 2253403 = 3380105) B3380105
theorem B11407877 : Blo 2251435 11407877 := bbase (se 4 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 11407877 = 2138977) (by norm_num)
theorem B7605251 : Blo 2251435 7605251 := bstep (se 1 (by rfl) ⟨5703938, by rfl⟩ : syracuseStep 7605251 = 11407877) B11407877
theorem B5070167 : Blo 2251435 5070167 := bstep (se 1 (by rfl) ⟨3802625, by rfl⟩ : syracuseStep 5070167 = 7605251) B7605251
theorem B3380111 : Blo 2251435 3380111 := bstep (se 1 (by rfl) ⟨2535083, by rfl⟩ : syracuseStep 3380111 = 5070167) B5070167
theorem B2253407 : Blo 2251435 2253407 := bstep (se 1 (by rfl) ⟨1690055, by rfl⟩ : syracuseStep 2253407 = 3380111) B3380111
theorem B3380117 : Blo 2251435 3380117 := bbase (se 6 (by rfl) ⟨79221, by rfl⟩ : syracuseStep 3380117 = 158443) (by norm_num)
theorem B2253411 : Blo 2251435 2253411 := bstep (se 1 (by rfl) ⟨1690058, by rfl⟩ : syracuseStep 2253411 = 3380117) B3380117
theorem B12833909 : Blo 2251435 12833909 := bbase (se 5 (by rfl) ⟨601589, by rfl⟩ : syracuseStep 12833909 = 1203179) (by norm_num)
theorem B8555939 : Blo 2251435 8555939 := bstep (se 1 (by rfl) ⟨6416954, by rfl⟩ : syracuseStep 8555939 = 12833909) B12833909
theorem B5703959 : Blo 2251435 5703959 := bstep (se 1 (by rfl) ⟨4277969, by rfl⟩ : syracuseStep 5703959 = 8555939) B8555939
theorem B3802639 : Blo 2251435 3802639 := bstep (se 1 (by rfl) ⟨2851979, by rfl⟩ : syracuseStep 3802639 = 5703959) B5703959
theorem B5070185 : Blo 2251435 5070185 := bstep (se 2 (by rfl) ⟨1901319, by rfl⟩ : syracuseStep 5070185 = 3802639) B3802639
theorem B3380123 : Blo 2251435 3380123 := bstep (se 1 (by rfl) ⟨2535092, by rfl⟩ : syracuseStep 3380123 = 5070185) B5070185
theorem B2253415 : Blo 2251435 2253415 := bstep (se 1 (by rfl) ⟨1690061, by rfl⟩ : syracuseStep 2253415 = 3380123) B3380123
theorem B2535097 : Blo 2251435 2535097 := bbase (se 2 (by rfl) ⟨950661, by rfl⟩ : syracuseStep 2535097 = 1901323) (by norm_num)
theorem B3380129 : Blo 2251435 3380129 := bstep (se 2 (by rfl) ⟨1267548, by rfl⟩ : syracuseStep 3380129 = 2535097) B2535097
theorem B2253419 : Blo 2251435 2253419 := bstep (se 1 (by rfl) ⟨1690064, by rfl⟩ : syracuseStep 2253419 = 3380129) B3380129
theorem B4812733 : Blo 2251435 4812733 := bbase (se 3 (by rfl) ⟨902387, by rfl⟩ : syracuseStep 4812733 = 1804775) (by norm_num)
theorem B6416977 : Blo 2251435 6416977 := bstep (se 2 (by rfl) ⟨2406366, by rfl⟩ : syracuseStep 6416977 = 4812733) B4812733
theorem B8555969 : Blo 2251435 8555969 := bstep (se 2 (by rfl) ⟨3208488, by rfl⟩ : syracuseStep 8555969 = 6416977) B6416977
theorem B5703979 : Blo 2251435 5703979 := bstep (se 1 (by rfl) ⟨4277984, by rfl⟩ : syracuseStep 5703979 = 8555969) B8555969
theorem B7605305 : Blo 2251435 7605305 := bstep (se 2 (by rfl) ⟨2851989, by rfl⟩ : syracuseStep 7605305 = 5703979) B5703979
theorem B5070203 : Blo 2251435 5070203 := bstep (se 1 (by rfl) ⟨3802652, by rfl⟩ : syracuseStep 5070203 = 7605305) B7605305
theorem B3380135 : Blo 2251435 3380135 := bstep (se 1 (by rfl) ⟨2535101, by rfl⟩ : syracuseStep 3380135 = 5070203) B5070203
theorem B2253423 : Blo 2251435 2253423 := bstep (se 1 (by rfl) ⟨1690067, by rfl⟩ : syracuseStep 2253423 = 3380135) B3380135
theorem B3380141 : Blo 2251435 3380141 := bbase (se 3 (by rfl) ⟨633776, by rfl⟩ : syracuseStep 3380141 = 1267553) (by norm_num)
theorem B2253427 : Blo 2251435 2253427 := bstep (se 1 (by rfl) ⟨1690070, by rfl⟩ : syracuseStep 2253427 = 3380141) B3380141
theorem B5070221 : Blo 2251435 5070221 := bbase (se 3 (by rfl) ⟨950666, by rfl⟩ : syracuseStep 5070221 = 1901333) (by norm_num)
theorem B3380147 : Blo 2251435 3380147 := bstep (se 1 (by rfl) ⟨2535110, by rfl⟩ : syracuseStep 3380147 = 5070221) B5070221
theorem B2253431 : Blo 2251435 2253431 := bstep (se 1 (by rfl) ⟨1690073, by rfl⟩ : syracuseStep 2253431 = 3380147) B3380147
theorem B2852005 : Blo 2251435 2852005 := bbase (se 4 (by rfl) ⟨267375, by rfl⟩ : syracuseStep 2852005 = 534751) (by norm_num)
theorem B3802673 : Blo 2251435 3802673 := bstep (se 2 (by rfl) ⟨1426002, by rfl⟩ : syracuseStep 3802673 = 2852005) B2852005
theorem B2535115 : Blo 2251435 2535115 := bstep (se 1 (by rfl) ⟨1901336, by rfl⟩ : syracuseStep 2535115 = 3802673) B3802673
theorem B3380153 : Blo 2251435 3380153 := bstep (se 2 (by rfl) ⟨1267557, by rfl⟩ : syracuseStep 3380153 = 2535115) B2535115
theorem B2253435 : Blo 2251435 2253435 := bstep (se 1 (by rfl) ⟨1690076, by rfl⟩ : syracuseStep 2253435 = 3380153) B3380153
theorem C0 (j : ℕ) (h1 : 562858 ≤ j) (h2 : j ≤ 563358) : Blo 2251435 (4 * j + 3) := by
  interval_cases j
  · exact B2251435
  · exact B2251439
  · exact B2251443
  · exact B2251447
  · exact B2251451
  · exact B2251455
  · exact B2251459
  · exact B2251463
  · exact B2251467
  · exact B2251471
  · exact B2251475
  · exact B2251479
  · exact B2251483
  · exact B2251487
  · exact B2251491
  · exact B2251495
  · exact B2251499
  · exact B2251503
  · exact B2251507
  · exact B2251511
  · exact B2251515
  · exact B2251519
  · exact B2251523
  · exact B2251527
  · exact B2251531
  · exact B2251535
  · exact B2251539
  · exact B2251543
  · exact B2251547
  · exact B2251551
  · exact B2251555
  · exact B2251559
  · exact B2251563
  · exact B2251567
  · exact B2251571
  · exact B2251575
  · exact B2251579
  · exact B2251583
  · exact B2251587
  · exact B2251591
  · exact B2251595
  · exact B2251599
  · exact B2251603
  · exact B2251607
  · exact B2251611
  · exact B2251615
  · exact B2251619
  · exact B2251623
  · exact B2251627
  · exact B2251631
  · exact B2251635
  · exact B2251639
  · exact B2251643
  · exact B2251647
  · exact B2251651
  · exact B2251655
  · exact B2251659
  · exact B2251663
  · exact B2251667
  · exact B2251671
  · exact B2251675
  · exact B2251679
  · exact B2251683
  · exact B2251687
  · exact B2251691
  · exact B2251695
  · exact B2251699
  · exact B2251703
  · exact B2251707
  · exact B2251711
  · exact B2251715
  · exact B2251719
  · exact B2251723
  · exact B2251727
  · exact B2251731
  · exact B2251735
  · exact B2251739
  · exact B2251743
  · exact B2251747
  · exact B2251751
  · exact B2251755
  · exact B2251759
  · exact B2251763
  · exact B2251767
  · exact B2251771
  · exact B2251775
  · exact B2251779
  · exact B2251783
  · exact B2251787
  · exact B2251791
  · exact B2251795
  · exact B2251799
  · exact B2251803
  · exact B2251807
  · exact B2251811
  · exact B2251815
  · exact B2251819
  · exact B2251823
  · exact B2251827
  · exact B2251831
  · exact B2251835
  · exact B2251839
  · exact B2251843
  · exact B2251847
  · exact B2251851
  · exact B2251855
  · exact B2251859
  · exact B2251863
  · exact B2251867
  · exact B2251871
  · exact B2251875
  · exact B2251879
  · exact B2251883
  · exact B2251887
  · exact B2251891
  · exact B2251895
  · exact B2251899
  · exact B2251903
  · exact B2251907
  · exact B2251911
  · exact B2251915
  · exact B2251919
  · exact B2251923
  · exact B2251927
  · exact B2251931
  · exact B2251935
  · exact B2251939
  · exact B2251943
  · exact B2251947
  · exact B2251951
  · exact B2251955
  · exact B2251959
  · exact B2251963
  · exact B2251967
  · exact B2251971
  · exact B2251975
  · exact B2251979
  · exact B2251983
  · exact B2251987
  · exact B2251991
  · exact B2251995
  · exact B2251999
  · exact B2252003
  · exact B2252007
  · exact B2252011
  · exact B2252015
  · exact B2252019
  · exact B2252023
  · exact B2252027
  · exact B2252031
  · exact B2252035
  · exact B2252039
  · exact B2252043
  · exact B2252047
  · exact B2252051
  · exact B2252055
  · exact B2252059
  · exact B2252063
  · exact B2252067
  · exact B2252071
  · exact B2252075
  · exact B2252079
  · exact B2252083
  · exact B2252087
  · exact B2252091
  · exact B2252095
  · exact B2252099
  · exact B2252103
  · exact B2252107
  · exact B2252111
  · exact B2252115
  · exact B2252119
  · exact B2252123
  · exact B2252127
  · exact B2252131
  · exact B2252135
  · exact B2252139
  · exact B2252143
  · exact B2252147
  · exact B2252151
  · exact B2252155
  · exact B2252159
  · exact B2252163
  · exact B2252167
  · exact B2252171
  · exact B2252175
  · exact B2252179
  · exact B2252183
  · exact B2252187
  · exact B2252191
  · exact B2252195
  · exact B2252199
  · exact B2252203
  · exact B2252207
  · exact B2252211
  · exact B2252215
  · exact B2252219
  · exact B2252223
  · exact B2252227
  · exact B2252231
  · exact B2252235
  · exact B2252239
  · exact B2252243
  · exact B2252247
  · exact B2252251
  · exact B2252255
  · exact B2252259
  · exact B2252263
  · exact B2252267
  · exact B2252271
  · exact B2252275
  · exact B2252279
  · exact B2252283
  · exact B2252287
  · exact B2252291
  · exact B2252295
  · exact B2252299
  · exact B2252303
  · exact B2252307
  · exact B2252311
  · exact B2252315
  · exact B2252319
  · exact B2252323
  · exact B2252327
  · exact B2252331
  · exact B2252335
  · exact B2252339
  · exact B2252343
  · exact B2252347
  · exact B2252351
  · exact B2252355
  · exact B2252359
  · exact B2252363
  · exact B2252367
  · exact B2252371
  · exact B2252375
  · exact B2252379
  · exact B2252383
  · exact B2252387
  · exact B2252391
  · exact B2252395
  · exact B2252399
  · exact B2252403
  · exact B2252407
  · exact B2252411
  · exact B2252415
  · exact B2252419
  · exact B2252423
  · exact B2252427
  · exact B2252431
  · exact B2252435
  · exact B2252439
  · exact B2252443
  · exact B2252447
  · exact B2252451
  · exact B2252455
  · exact B2252459
  · exact B2252463
  · exact B2252467
  · exact B2252471
  · exact B2252475
  · exact B2252479
  · exact B2252483
  · exact B2252487
  · exact B2252491
  · exact B2252495
  · exact B2252499
  · exact B2252503
  · exact B2252507
  · exact B2252511
  · exact B2252515
  · exact B2252519
  · exact B2252523
  · exact B2252527
  · exact B2252531
  · exact B2252535
  · exact B2252539
  · exact B2252543
  · exact B2252547
  · exact B2252551
  · exact B2252555
  · exact B2252559
  · exact B2252563
  · exact B2252567
  · exact B2252571
  · exact B2252575
  · exact B2252579
  · exact B2252583
  · exact B2252587
  · exact B2252591
  · exact B2252595
  · exact B2252599
  · exact B2252603
  · exact B2252607
  · exact B2252611
  · exact B2252615
  · exact B2252619
  · exact B2252623
  · exact B2252627
  · exact B2252631
  · exact B2252635
  · exact B2252639
  · exact B2252643
  · exact B2252647
  · exact B2252651
  · exact B2252655
  · exact B2252659
  · exact B2252663
  · exact B2252667
  · exact B2252671
  · exact B2252675
  · exact B2252679
  · exact B2252683
  · exact B2252687
  · exact B2252691
  · exact B2252695
  · exact B2252699
  · exact B2252703
  · exact B2252707
  · exact B2252711
  · exact B2252715
  · exact B2252719
  · exact B2252723
  · exact B2252727
  · exact B2252731
  · exact B2252735
  · exact B2252739
  · exact B2252743
  · exact B2252747
  · exact B2252751
  · exact B2252755
  · exact B2252759
  · exact B2252763
  · exact B2252767
  · exact B2252771
  · exact B2252775
  · exact B2252779
  · exact B2252783
  · exact B2252787
  · exact B2252791
  · exact B2252795
  · exact B2252799
  · exact B2252803
  · exact B2252807
  · exact B2252811
  · exact B2252815
  · exact B2252819
  · exact B2252823
  · exact B2252827
  · exact B2252831
  · exact B2252835
  · exact B2252839
  · exact B2252843
  · exact B2252847
  · exact B2252851
  · exact B2252855
  · exact B2252859
  · exact B2252863
  · exact B2252867
  · exact B2252871
  · exact B2252875
  · exact B2252879
  · exact B2252883
  · exact B2252887
  · exact B2252891
  · exact B2252895
  · exact B2252899
  · exact B2252903
  · exact B2252907
  · exact B2252911
  · exact B2252915
  · exact B2252919
  · exact B2252923
  · exact B2252927
  · exact B2252931
  · exact B2252935
  · exact B2252939
  · exact B2252943
  · exact B2252947
  · exact B2252951
  · exact B2252955
  · exact B2252959
  · exact B2252963
  · exact B2252967
  · exact B2252971
  · exact B2252975
  · exact B2252979
  · exact B2252983
  · exact B2252987
  · exact B2252991
  · exact B2252995
  · exact B2252999
  · exact B2253003
  · exact B2253007
  · exact B2253011
  · exact B2253015
  · exact B2253019
  · exact B2253023
  · exact B2253027
  · exact B2253031
  · exact B2253035
  · exact B2253039
  · exact B2253043
  · exact B2253047
  · exact B2253051
  · exact B2253055
  · exact B2253059
  · exact B2253063
  · exact B2253067
  · exact B2253071
  · exact B2253075
  · exact B2253079
  · exact B2253083
  · exact B2253087
  · exact B2253091
  · exact B2253095
  · exact B2253099
  · exact B2253103
  · exact B2253107
  · exact B2253111
  · exact B2253115
  · exact B2253119
  · exact B2253123
  · exact B2253127
  · exact B2253131
  · exact B2253135
  · exact B2253139
  · exact B2253143
  · exact B2253147
  · exact B2253151
  · exact B2253155
  · exact B2253159
  · exact B2253163
  · exact B2253167
  · exact B2253171
  · exact B2253175
  · exact B2253179
  · exact B2253183
  · exact B2253187
  · exact B2253191
  · exact B2253195
  · exact B2253199
  · exact B2253203
  · exact B2253207
  · exact B2253211
  · exact B2253215
  · exact B2253219
  · exact B2253223
  · exact B2253227
  · exact B2253231
  · exact B2253235
  · exact B2253239
  · exact B2253243
  · exact B2253247
  · exact B2253251
  · exact B2253255
  · exact B2253259
  · exact B2253263
  · exact B2253267
  · exact B2253271
  · exact B2253275
  · exact B2253279
  · exact B2253283
  · exact B2253287
  · exact B2253291
  · exact B2253295
  · exact B2253299
  · exact B2253303
  · exact B2253307
  · exact B2253311
  · exact B2253315
  · exact B2253319
  · exact B2253323
  · exact B2253327
  · exact B2253331
  · exact B2253335
  · exact B2253339
  · exact B2253343
  · exact B2253347
  · exact B2253351
  · exact B2253355
  · exact B2253359
  · exact B2253363
  · exact B2253367
  · exact B2253371
  · exact B2253375
  · exact B2253379
  · exact B2253383
  · exact B2253387
  · exact B2253391
  · exact B2253395
  · exact B2253399
  · exact B2253403
  · exact B2253407
  · exact B2253411
  · exact B2253415
  · exact B2253419
  · exact B2253423
  · exact B2253427
  · exact B2253431
  · exact B2253435
theorem solution (m : ℕ) (hlo : 2251435 ≤ m) (hhi : m ≤ 2253435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 562858 ≤ j := by omega
    have hj2 : j ≤ 563358 := by omega
    have hb : Blo 2251435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
