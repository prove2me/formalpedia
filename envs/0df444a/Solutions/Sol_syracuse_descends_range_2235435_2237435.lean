-- Prove2me | solution 1 for syracuse_descends_range_2235435_2237435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:53.464623+00:00
-- url     : https://prove2.me/submissions/8bdc9733-d33d-441b-b301-449e7fd887b9

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

theorem B2514865 : Blo 2235435 2514865 := bbase (se 2 (by rfl) ⟨943074, by rfl⟩ : syracuseStep 2514865 = 1886149) (by norm_num)
theorem B3353153 : Blo 2235435 3353153 := bstep (se 2 (by rfl) ⟨1257432, by rfl⟩ : syracuseStep 3353153 = 2514865) B2514865
theorem B2235435 : Blo 2235435 2235435 := bstep (se 1 (by rfl) ⟨1676576, by rfl⟩ : syracuseStep 2235435 = 3353153) B3353153
theorem B6365765 : Blo 2235435 6365765 := bbase (se 4 (by rfl) ⟨596790, by rfl⟩ : syracuseStep 6365765 = 1193581) (by norm_num)
theorem B4243843 : Blo 2235435 4243843 := bstep (se 1 (by rfl) ⟨3182882, by rfl⟩ : syracuseStep 4243843 = 6365765) B6365765
theorem B5658457 : Blo 2235435 5658457 := bstep (se 2 (by rfl) ⟨2121921, by rfl⟩ : syracuseStep 5658457 = 4243843) B4243843
theorem B7544609 : Blo 2235435 7544609 := bstep (se 2 (by rfl) ⟨2829228, by rfl⟩ : syracuseStep 7544609 = 5658457) B5658457
theorem B5029739 : Blo 2235435 5029739 := bstep (se 1 (by rfl) ⟨3772304, by rfl⟩ : syracuseStep 5029739 = 7544609) B7544609
theorem B3353159 : Blo 2235435 3353159 := bstep (se 1 (by rfl) ⟨2514869, by rfl⟩ : syracuseStep 3353159 = 5029739) B5029739
theorem B2235439 : Blo 2235435 2235439 := bstep (se 1 (by rfl) ⟨1676579, by rfl⟩ : syracuseStep 2235439 = 3353159) B3353159
theorem B3353165 : Blo 2235435 3353165 := bbase (se 3 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 3353165 = 1257437) (by norm_num)
theorem B2235443 : Blo 2235435 2235443 := bstep (se 1 (by rfl) ⟨1676582, by rfl⟩ : syracuseStep 2235443 = 3353165) B3353165
theorem B5029757 : Blo 2235435 5029757 := bbase (se 3 (by rfl) ⟨943079, by rfl⟩ : syracuseStep 5029757 = 1886159) (by norm_num)
theorem B3353171 : Blo 2235435 3353171 := bstep (se 1 (by rfl) ⟨2514878, by rfl⟩ : syracuseStep 3353171 = 5029757) B5029757
theorem B2235447 : Blo 2235435 2235447 := bstep (se 1 (by rfl) ⟨1676585, by rfl⟩ : syracuseStep 2235447 = 3353171) B3353171
theorem B3772325 : Blo 2235435 3772325 := bbase (se 4 (by rfl) ⟨353655, by rfl⟩ : syracuseStep 3772325 = 707311) (by norm_num)
theorem B2514883 : Blo 2235435 2514883 := bstep (se 1 (by rfl) ⟨1886162, by rfl⟩ : syracuseStep 2514883 = 3772325) B3772325
theorem B3353177 : Blo 2235435 3353177 := bstep (se 2 (by rfl) ⟨1257441, by rfl⟩ : syracuseStep 3353177 = 2514883) B2514883
theorem B2235451 : Blo 2235435 2235451 := bstep (se 1 (by rfl) ⟨1676588, by rfl⟩ : syracuseStep 2235451 = 3353177) B3353177
theorem B2685577 : Blo 2235435 2685577 := bbase (se 2 (by rfl) ⟨1007091, by rfl⟩ : syracuseStep 2685577 = 2014183) (by norm_num)
theorem B3580769 : Blo 2235435 3580769 := bstep (se 2 (by rfl) ⟨1342788, by rfl⟩ : syracuseStep 3580769 = 2685577) B2685577
theorem B2387179 : Blo 2235435 2387179 := bstep (se 1 (by rfl) ⟨1790384, by rfl⟩ : syracuseStep 2387179 = 3580769) B3580769
theorem B3182905 : Blo 2235435 3182905 := bstep (se 2 (by rfl) ⟨1193589, by rfl⟩ : syracuseStep 3182905 = 2387179) B2387179
theorem B16975493 : Blo 2235435 16975493 := bstep (se 4 (by rfl) ⟨1591452, by rfl⟩ : syracuseStep 16975493 = 3182905) B3182905
theorem B11316995 : Blo 2235435 11316995 := bstep (se 1 (by rfl) ⟨8487746, by rfl⟩ : syracuseStep 11316995 = 16975493) B16975493
theorem B7544663 : Blo 2235435 7544663 := bstep (se 1 (by rfl) ⟨5658497, by rfl⟩ : syracuseStep 7544663 = 11316995) B11316995
theorem B5029775 : Blo 2235435 5029775 := bstep (se 1 (by rfl) ⟨3772331, by rfl⟩ : syracuseStep 5029775 = 7544663) B7544663
theorem B3353183 : Blo 2235435 3353183 := bstep (se 1 (by rfl) ⟨2514887, by rfl⟩ : syracuseStep 3353183 = 5029775) B5029775
theorem B2235455 : Blo 2235435 2235455 := bstep (se 1 (by rfl) ⟨1676591, by rfl⟩ : syracuseStep 2235455 = 3353183) B3353183
theorem B3353189 : Blo 2235435 3353189 := bbase (se 4 (by rfl) ⟨314361, by rfl⟩ : syracuseStep 3353189 = 628723) (by norm_num)
theorem B2235459 : Blo 2235435 2235459 := bstep (se 1 (by rfl) ⟨1676594, by rfl⟩ : syracuseStep 2235459 = 3353189) B3353189
theorem B3182917 : Blo 2235435 3182917 := bbase (se 4 (by rfl) ⟨298398, by rfl⟩ : syracuseStep 3182917 = 596797) (by norm_num)
theorem B4243889 : Blo 2235435 4243889 := bstep (se 2 (by rfl) ⟨1591458, by rfl⟩ : syracuseStep 4243889 = 3182917) B3182917
theorem B2829259 : Blo 2235435 2829259 := bstep (se 1 (by rfl) ⟨2121944, by rfl⟩ : syracuseStep 2829259 = 4243889) B4243889
theorem B3772345 : Blo 2235435 3772345 := bstep (se 2 (by rfl) ⟨1414629, by rfl⟩ : syracuseStep 3772345 = 2829259) B2829259
theorem B5029793 : Blo 2235435 5029793 := bstep (se 2 (by rfl) ⟨1886172, by rfl⟩ : syracuseStep 5029793 = 3772345) B3772345
theorem B3353195 : Blo 2235435 3353195 := bstep (se 1 (by rfl) ⟨2514896, by rfl⟩ : syracuseStep 3353195 = 5029793) B5029793
theorem B2235463 : Blo 2235435 2235463 := bstep (se 1 (by rfl) ⟨1676597, by rfl⟩ : syracuseStep 2235463 = 3353195) B3353195
theorem B2514901 : Blo 2235435 2514901 := bbase (se 7 (by rfl) ⟨29471, by rfl⟩ : syracuseStep 2514901 = 58943) (by norm_num)
theorem B3353201 : Blo 2235435 3353201 := bstep (se 2 (by rfl) ⟨1257450, by rfl⟩ : syracuseStep 3353201 = 2514901) B2514901
theorem B2235467 : Blo 2235435 2235467 := bstep (se 1 (by rfl) ⟨1676600, by rfl⟩ : syracuseStep 2235467 = 3353201) B3353201
theorem B2829269 : Blo 2235435 2829269 := bbase (se 7 (by rfl) ⟨33155, by rfl⟩ : syracuseStep 2829269 = 66311) (by norm_num)
theorem B7544717 : Blo 2235435 7544717 := bstep (se 3 (by rfl) ⟨1414634, by rfl⟩ : syracuseStep 7544717 = 2829269) B2829269
theorem B5029811 : Blo 2235435 5029811 := bstep (se 1 (by rfl) ⟨3772358, by rfl⟩ : syracuseStep 5029811 = 7544717) B7544717
theorem B3353207 : Blo 2235435 3353207 := bstep (se 1 (by rfl) ⟨2514905, by rfl⟩ : syracuseStep 3353207 = 5029811) B5029811
theorem B2235471 : Blo 2235435 2235471 := bstep (se 1 (by rfl) ⟨1676603, by rfl⟩ : syracuseStep 2235471 = 3353207) B3353207
theorem B3353213 : Blo 2235435 3353213 := bbase (se 3 (by rfl) ⟨628727, by rfl⟩ : syracuseStep 3353213 = 1257455) (by norm_num)
theorem B2235475 : Blo 2235435 2235475 := bstep (se 1 (by rfl) ⟨1676606, by rfl⟩ : syracuseStep 2235475 = 3353213) B3353213
theorem B5029829 : Blo 2235435 5029829 := bbase (se 4 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 5029829 = 943093) (by norm_num)
theorem B3353219 : Blo 2235435 3353219 := bstep (se 1 (by rfl) ⟨2514914, by rfl⟩ : syracuseStep 3353219 = 5029829) B5029829
theorem B2235479 : Blo 2235435 2235479 := bstep (se 1 (by rfl) ⟨1676609, by rfl⟩ : syracuseStep 2235479 = 3353219) B3353219
theorem B9548837 : Blo 2235435 9548837 := bbase (se 4 (by rfl) ⟨895203, by rfl⟩ : syracuseStep 9548837 = 1790407) (by norm_num)
theorem B6365891 : Blo 2235435 6365891 := bstep (se 1 (by rfl) ⟨4774418, by rfl⟩ : syracuseStep 6365891 = 9548837) B9548837
theorem B4243927 : Blo 2235435 4243927 := bstep (se 1 (by rfl) ⟨3182945, by rfl⟩ : syracuseStep 4243927 = 6365891) B6365891
theorem B5658569 : Blo 2235435 5658569 := bstep (se 2 (by rfl) ⟨2121963, by rfl⟩ : syracuseStep 5658569 = 4243927) B4243927
theorem B3772379 : Blo 2235435 3772379 := bstep (se 1 (by rfl) ⟨2829284, by rfl⟩ : syracuseStep 3772379 = 5658569) B5658569
theorem B2514919 : Blo 2235435 2514919 := bstep (se 1 (by rfl) ⟨1886189, by rfl⟩ : syracuseStep 2514919 = 3772379) B3772379
theorem B3353225 : Blo 2235435 3353225 := bstep (se 2 (by rfl) ⟨1257459, by rfl⟩ : syracuseStep 3353225 = 2514919) B2514919
theorem B2235483 : Blo 2235435 2235483 := bstep (se 1 (by rfl) ⟨1676612, by rfl⟩ : syracuseStep 2235483 = 3353225) B3353225
theorem B11317157 : Blo 2235435 11317157 := bbase (se 4 (by rfl) ⟨1060983, by rfl⟩ : syracuseStep 11317157 = 2121967) (by norm_num)
theorem B7544771 : Blo 2235435 7544771 := bstep (se 1 (by rfl) ⟨5658578, by rfl⟩ : syracuseStep 7544771 = 11317157) B11317157
theorem B5029847 : Blo 2235435 5029847 := bstep (se 1 (by rfl) ⟨3772385, by rfl⟩ : syracuseStep 5029847 = 7544771) B7544771
theorem B3353231 : Blo 2235435 3353231 := bstep (se 1 (by rfl) ⟨2514923, by rfl⟩ : syracuseStep 3353231 = 5029847) B5029847
theorem B2235487 : Blo 2235435 2235487 := bstep (se 1 (by rfl) ⟨1676615, by rfl⟩ : syracuseStep 2235487 = 3353231) B3353231
theorem B3353237 : Blo 2235435 3353237 := bbase (se 6 (by rfl) ⟨78591, by rfl⟩ : syracuseStep 3353237 = 157183) (by norm_num)
theorem B2235491 : Blo 2235435 2235491 := bstep (se 1 (by rfl) ⟨1676618, by rfl⟩ : syracuseStep 2235491 = 3353237) B3353237
theorem B4028437 : Blo 2235435 4028437 := bbase (se 6 (by rfl) ⟨94416, by rfl⟩ : syracuseStep 4028437 = 188833) (by norm_num)
theorem B21484997 : Blo 2235435 21484997 := bstep (se 4 (by rfl) ⟨2014218, by rfl⟩ : syracuseStep 21484997 = 4028437) B4028437
theorem B14323331 : Blo 2235435 14323331 := bstep (se 1 (by rfl) ⟨10742498, by rfl⟩ : syracuseStep 14323331 = 21484997) B21484997
theorem B9548887 : Blo 2235435 9548887 := bstep (se 1 (by rfl) ⟨7161665, by rfl⟩ : syracuseStep 9548887 = 14323331) B14323331
theorem B12731849 : Blo 2235435 12731849 := bstep (se 2 (by rfl) ⟨4774443, by rfl⟩ : syracuseStep 12731849 = 9548887) B9548887
theorem B8487899 : Blo 2235435 8487899 := bstep (se 1 (by rfl) ⟨6365924, by rfl⟩ : syracuseStep 8487899 = 12731849) B12731849
theorem B5658599 : Blo 2235435 5658599 := bstep (se 1 (by rfl) ⟨4243949, by rfl⟩ : syracuseStep 5658599 = 8487899) B8487899
theorem B3772399 : Blo 2235435 3772399 := bstep (se 1 (by rfl) ⟨2829299, by rfl⟩ : syracuseStep 3772399 = 5658599) B5658599
theorem B5029865 : Blo 2235435 5029865 := bstep (se 2 (by rfl) ⟨1886199, by rfl⟩ : syracuseStep 5029865 = 3772399) B3772399
theorem B3353243 : Blo 2235435 3353243 := bstep (se 1 (by rfl) ⟨2514932, by rfl⟩ : syracuseStep 3353243 = 5029865) B5029865
theorem B2235495 : Blo 2235435 2235495 := bstep (se 1 (by rfl) ⟨1676621, by rfl⟩ : syracuseStep 2235495 = 3353243) B3353243
theorem B2514937 : Blo 2235435 2514937 := bbase (se 2 (by rfl) ⟨943101, by rfl⟩ : syracuseStep 2514937 = 1886203) (by norm_num)
theorem B3353249 : Blo 2235435 3353249 := bstep (se 2 (by rfl) ⟨1257468, by rfl⟩ : syracuseStep 3353249 = 2514937) B2514937
theorem B2235499 : Blo 2235435 2235499 := bstep (se 1 (by rfl) ⟨1676624, by rfl⟩ : syracuseStep 2235499 = 3353249) B3353249
theorem B9945125 : Blo 2235435 9945125 := bbase (se 4 (by rfl) ⟨932355, by rfl⟩ : syracuseStep 9945125 = 1864711) (by norm_num)
theorem B6630083 : Blo 2235435 6630083 := bstep (se 1 (by rfl) ⟨4972562, by rfl⟩ : syracuseStep 6630083 = 9945125) B9945125
theorem B4420055 : Blo 2235435 4420055 := bstep (se 1 (by rfl) ⟨3315041, by rfl⟩ : syracuseStep 4420055 = 6630083) B6630083
theorem B2946703 : Blo 2235435 2946703 := bstep (se 1 (by rfl) ⟨2210027, by rfl⟩ : syracuseStep 2946703 = 4420055) B4420055
theorem B3928937 : Blo 2235435 3928937 := bstep (se 2 (by rfl) ⟨1473351, by rfl⟩ : syracuseStep 3928937 = 2946703) B2946703
theorem B41908661 : Blo 2235435 41908661 := bstep (se 5 (by rfl) ⟨1964468, by rfl⟩ : syracuseStep 41908661 = 3928937) B3928937
theorem B27939107 : Blo 2235435 27939107 := bstep (se 1 (by rfl) ⟨20954330, by rfl⟩ : syracuseStep 27939107 = 41908661) B41908661
theorem B18626071 : Blo 2235435 18626071 := bstep (se 1 (by rfl) ⟨13969553, by rfl⟩ : syracuseStep 18626071 = 27939107) B27939107
theorem B24834761 : Blo 2235435 24834761 := bstep (se 2 (by rfl) ⟨9313035, by rfl⟩ : syracuseStep 24834761 = 18626071) B18626071
theorem B16556507 : Blo 2235435 16556507 := bstep (se 1 (by rfl) ⟨12417380, by rfl⟩ : syracuseStep 16556507 = 24834761) B24834761
theorem B11037671 : Blo 2235435 11037671 := bstep (se 1 (by rfl) ⟨8278253, by rfl⟩ : syracuseStep 11037671 = 16556507) B16556507
theorem B7358447 : Blo 2235435 7358447 := bstep (se 1 (by rfl) ⟨5518835, by rfl⟩ : syracuseStep 7358447 = 11037671) B11037671
theorem B4905631 : Blo 2235435 4905631 := bstep (se 1 (by rfl) ⟨3679223, by rfl⟩ : syracuseStep 4905631 = 7358447) B7358447
theorem B6540841 : Blo 2235435 6540841 := bstep (se 2 (by rfl) ⟨2452815, by rfl⟩ : syracuseStep 6540841 = 4905631) B4905631
theorem B8721121 : Blo 2235435 8721121 := bstep (se 2 (by rfl) ⟨3270420, by rfl⟩ : syracuseStep 8721121 = 6540841) B6540841
theorem B11628161 : Blo 2235435 11628161 := bstep (se 2 (by rfl) ⟨4360560, by rfl⟩ : syracuseStep 11628161 = 8721121) B8721121
theorem B7752107 : Blo 2235435 7752107 := bstep (se 1 (by rfl) ⟨5814080, by rfl⟩ : syracuseStep 7752107 = 11628161) B11628161
theorem B5168071 : Blo 2235435 5168071 := bstep (se 1 (by rfl) ⟨3876053, by rfl⟩ : syracuseStep 5168071 = 7752107) B7752107
theorem B6890761 : Blo 2235435 6890761 := bstep (se 2 (by rfl) ⟨2584035, by rfl⟩ : syracuseStep 6890761 = 5168071) B5168071
theorem B36750725 : Blo 2235435 36750725 := bstep (se 4 (by rfl) ⟨3445380, by rfl⟩ : syracuseStep 36750725 = 6890761) B6890761
theorem B24500483 : Blo 2235435 24500483 := bstep (se 1 (by rfl) ⟨18375362, by rfl⟩ : syracuseStep 24500483 = 36750725) B36750725
theorem B16333655 : Blo 2235435 16333655 := bstep (se 1 (by rfl) ⟨12250241, by rfl⟩ : syracuseStep 16333655 = 24500483) B24500483
theorem B43556413 : Blo 2235435 43556413 := bstep (se 3 (by rfl) ⟨8166827, by rfl⟩ : syracuseStep 43556413 = 16333655) B16333655
theorem B58075217 : Blo 2235435 58075217 := bstep (se 2 (by rfl) ⟨21778206, by rfl⟩ : syracuseStep 58075217 = 43556413) B43556413
theorem B38716811 : Blo 2235435 38716811 := bstep (se 1 (by rfl) ⟨29037608, by rfl⟩ : syracuseStep 38716811 = 58075217) B58075217
theorem B25811207 : Blo 2235435 25811207 := bstep (se 1 (by rfl) ⟨19358405, by rfl⟩ : syracuseStep 25811207 = 38716811) B38716811
theorem B17207471 : Blo 2235435 17207471 := bstep (se 1 (by rfl) ⟨12905603, by rfl⟩ : syracuseStep 17207471 = 25811207) B25811207
theorem B11471647 : Blo 2235435 11471647 := bstep (se 1 (by rfl) ⟨8603735, by rfl⟩ : syracuseStep 11471647 = 17207471) B17207471
theorem B15295529 : Blo 2235435 15295529 := bstep (se 2 (by rfl) ⟨5735823, by rfl⟩ : syracuseStep 15295529 = 11471647) B11471647
theorem B10197019 : Blo 2235435 10197019 := bstep (se 1 (by rfl) ⟨7647764, by rfl⟩ : syracuseStep 10197019 = 15295529) B15295529
theorem B13596025 : Blo 2235435 13596025 := bstep (se 2 (by rfl) ⟨5098509, by rfl⟩ : syracuseStep 13596025 = 10197019) B10197019
theorem B18128033 : Blo 2235435 18128033 := bstep (se 2 (by rfl) ⟨6798012, by rfl⟩ : syracuseStep 18128033 = 13596025) B13596025
theorem B12085355 : Blo 2235435 12085355 := bstep (se 1 (by rfl) ⟨9064016, by rfl⟩ : syracuseStep 12085355 = 18128033) B18128033
theorem B8056903 : Blo 2235435 8056903 := bstep (se 1 (by rfl) ⟨6042677, by rfl⟩ : syracuseStep 8056903 = 12085355) B12085355
theorem B10742537 : Blo 2235435 10742537 := bstep (se 2 (by rfl) ⟨4028451, by rfl⟩ : syracuseStep 10742537 = 8056903) B8056903
theorem B7161691 : Blo 2235435 7161691 := bstep (se 1 (by rfl) ⟨5371268, by rfl⟩ : syracuseStep 7161691 = 10742537) B10742537
theorem B9548921 : Blo 2235435 9548921 := bstep (se 2 (by rfl) ⟨3580845, by rfl⟩ : syracuseStep 9548921 = 7161691) B7161691
theorem B6365947 : Blo 2235435 6365947 := bstep (se 1 (by rfl) ⟨4774460, by rfl⟩ : syracuseStep 6365947 = 9548921) B9548921
theorem B8487929 : Blo 2235435 8487929 := bstep (se 2 (by rfl) ⟨3182973, by rfl⟩ : syracuseStep 8487929 = 6365947) B6365947
theorem B5658619 : Blo 2235435 5658619 := bstep (se 1 (by rfl) ⟨4243964, by rfl⟩ : syracuseStep 5658619 = 8487929) B8487929
theorem B7544825 : Blo 2235435 7544825 := bstep (se 2 (by rfl) ⟨2829309, by rfl⟩ : syracuseStep 7544825 = 5658619) B5658619
theorem B5029883 : Blo 2235435 5029883 := bstep (se 1 (by rfl) ⟨3772412, by rfl⟩ : syracuseStep 5029883 = 7544825) B7544825
theorem B3353255 : Blo 2235435 3353255 := bstep (se 1 (by rfl) ⟨2514941, by rfl⟩ : syracuseStep 3353255 = 5029883) B5029883
theorem B2235503 : Blo 2235435 2235503 := bstep (se 1 (by rfl) ⟨1676627, by rfl⟩ : syracuseStep 2235503 = 3353255) B3353255
theorem B3353261 : Blo 2235435 3353261 := bbase (se 3 (by rfl) ⟨628736, by rfl⟩ : syracuseStep 3353261 = 1257473) (by norm_num)
theorem B2235507 : Blo 2235435 2235507 := bstep (se 1 (by rfl) ⟨1676630, by rfl⟩ : syracuseStep 2235507 = 3353261) B3353261
theorem B5029901 : Blo 2235435 5029901 := bbase (se 3 (by rfl) ⟨943106, by rfl⟩ : syracuseStep 5029901 = 1886213) (by norm_num)
theorem B3353267 : Blo 2235435 3353267 := bstep (se 1 (by rfl) ⟨2514950, by rfl⟩ : syracuseStep 3353267 = 5029901) B5029901
theorem B2235511 : Blo 2235435 2235511 := bstep (se 1 (by rfl) ⟨1676633, by rfl⟩ : syracuseStep 2235511 = 3353267) B3353267
theorem B2829325 : Blo 2235435 2829325 := bbase (se 3 (by rfl) ⟨530498, by rfl⟩ : syracuseStep 2829325 = 1060997) (by norm_num)
theorem B3772433 : Blo 2235435 3772433 := bstep (se 2 (by rfl) ⟨1414662, by rfl⟩ : syracuseStep 3772433 = 2829325) B2829325
theorem B2514955 : Blo 2235435 2514955 := bstep (se 1 (by rfl) ⟨1886216, by rfl⟩ : syracuseStep 2514955 = 3772433) B3772433
theorem B3353273 : Blo 2235435 3353273 := bstep (se 2 (by rfl) ⟨1257477, by rfl⟩ : syracuseStep 3353273 = 2514955) B2514955
theorem B2235515 : Blo 2235435 2235515 := bstep (se 1 (by rfl) ⟨1676636, by rfl⟩ : syracuseStep 2235515 = 3353273) B3353273
theorem B2296937 : Blo 2235435 2296937 := bbase (se 2 (by rfl) ⟨861351, by rfl⟩ : syracuseStep 2296937 = 1722703) (by norm_num)
theorem B6125165 : Blo 2235435 6125165 := bstep (se 3 (by rfl) ⟨1148468, by rfl⟩ : syracuseStep 6125165 = 2296937) B2296937
theorem B4083443 : Blo 2235435 4083443 := bstep (se 1 (by rfl) ⟨3062582, by rfl⟩ : syracuseStep 4083443 = 6125165) B6125165
theorem B2722295 : Blo 2235435 2722295 := bstep (se 1 (by rfl) ⟨2041721, by rfl⟩ : syracuseStep 2722295 = 4083443) B4083443
theorem B7259453 : Blo 2235435 7259453 := bstep (se 3 (by rfl) ⟨1361147, by rfl⟩ : syracuseStep 7259453 = 2722295) B2722295
theorem B4839635 : Blo 2235435 4839635 := bstep (se 1 (by rfl) ⟨3629726, by rfl⟩ : syracuseStep 4839635 = 7259453) B7259453
theorem B3226423 : Blo 2235435 3226423 := bstep (se 1 (by rfl) ⟨2419817, by rfl⟩ : syracuseStep 3226423 = 4839635) B4839635
theorem B275321429 : Blo 2235435 275321429 := bstep (se 8 (by rfl) ⟨1613211, by rfl⟩ : syracuseStep 275321429 = 3226423) B3226423
theorem B183547619 : Blo 2235435 183547619 := bstep (se 1 (by rfl) ⟨137660714, by rfl⟩ : syracuseStep 183547619 = 275321429) B275321429
theorem B122365079 : Blo 2235435 122365079 := bstep (se 1 (by rfl) ⟨91773809, by rfl⟩ : syracuseStep 122365079 = 183547619) B183547619
theorem B81576719 : Blo 2235435 81576719 := bstep (se 1 (by rfl) ⟨61182539, by rfl⟩ : syracuseStep 81576719 = 122365079) B122365079
theorem B54384479 : Blo 2235435 54384479 := bstep (se 1 (by rfl) ⟨40788359, by rfl⟩ : syracuseStep 54384479 = 81576719) B81576719
theorem B36256319 : Blo 2235435 36256319 := bstep (se 1 (by rfl) ⟨27192239, by rfl⟩ : syracuseStep 36256319 = 54384479) B54384479
theorem B24170879 : Blo 2235435 24170879 := bstep (se 1 (by rfl) ⟨18128159, by rfl⟩ : syracuseStep 24170879 = 36256319) B36256319
theorem B16113919 : Blo 2235435 16113919 := bstep (se 1 (by rfl) ⟨12085439, by rfl⟩ : syracuseStep 16113919 = 24170879) B24170879
theorem B21485225 : Blo 2235435 21485225 := bstep (se 2 (by rfl) ⟨8056959, by rfl⟩ : syracuseStep 21485225 = 16113919) B16113919
theorem B14323483 : Blo 2235435 14323483 := bstep (se 1 (by rfl) ⟨10742612, by rfl⟩ : syracuseStep 14323483 = 21485225) B21485225
theorem B19097977 : Blo 2235435 19097977 := bstep (se 2 (by rfl) ⟨7161741, by rfl⟩ : syracuseStep 19097977 = 14323483) B14323483
theorem B25463969 : Blo 2235435 25463969 := bstep (se 2 (by rfl) ⟨9548988, by rfl⟩ : syracuseStep 25463969 = 19097977) B19097977
theorem B16975979 : Blo 2235435 16975979 := bstep (se 1 (by rfl) ⟨12731984, by rfl⟩ : syracuseStep 16975979 = 25463969) B25463969
theorem B11317319 : Blo 2235435 11317319 := bstep (se 1 (by rfl) ⟨8487989, by rfl⟩ : syracuseStep 11317319 = 16975979) B16975979
theorem B7544879 : Blo 2235435 7544879 := bstep (se 1 (by rfl) ⟨5658659, by rfl⟩ : syracuseStep 7544879 = 11317319) B11317319
theorem B5029919 : Blo 2235435 5029919 := bstep (se 1 (by rfl) ⟨3772439, by rfl⟩ : syracuseStep 5029919 = 7544879) B7544879
theorem B3353279 : Blo 2235435 3353279 := bstep (se 1 (by rfl) ⟨2514959, by rfl⟩ : syracuseStep 3353279 = 5029919) B5029919
theorem B2235519 : Blo 2235435 2235519 := bstep (se 1 (by rfl) ⟨1676639, by rfl⟩ : syracuseStep 2235519 = 3353279) B3353279
theorem B3353285 : Blo 2235435 3353285 := bbase (se 4 (by rfl) ⟨314370, by rfl⟩ : syracuseStep 3353285 = 628741) (by norm_num)
theorem B2235523 : Blo 2235435 2235523 := bstep (se 1 (by rfl) ⟨1676642, by rfl⟩ : syracuseStep 2235523 = 3353285) B3353285
theorem B3772453 : Blo 2235435 3772453 := bbase (se 4 (by rfl) ⟨353667, by rfl⟩ : syracuseStep 3772453 = 707335) (by norm_num)
theorem B5029937 : Blo 2235435 5029937 := bstep (se 2 (by rfl) ⟨1886226, by rfl⟩ : syracuseStep 5029937 = 3772453) B3772453
theorem B3353291 : Blo 2235435 3353291 := bstep (se 1 (by rfl) ⟨2514968, by rfl⟩ : syracuseStep 3353291 = 5029937) B5029937
theorem B2235527 : Blo 2235435 2235527 := bstep (se 1 (by rfl) ⟨1676645, by rfl⟩ : syracuseStep 2235527 = 3353291) B3353291
theorem B2514973 : Blo 2235435 2514973 := bbase (se 3 (by rfl) ⟨471557, by rfl⟩ : syracuseStep 2514973 = 943115) (by norm_num)
theorem B3353297 : Blo 2235435 3353297 := bstep (se 2 (by rfl) ⟨1257486, by rfl⟩ : syracuseStep 3353297 = 2514973) B2514973
theorem B2235531 : Blo 2235435 2235531 := bstep (se 1 (by rfl) ⟨1676648, by rfl⟩ : syracuseStep 2235531 = 3353297) B3353297
theorem B7544933 : Blo 2235435 7544933 := bbase (se 4 (by rfl) ⟨707337, by rfl⟩ : syracuseStep 7544933 = 1414675) (by norm_num)
theorem B5029955 : Blo 2235435 5029955 := bstep (se 1 (by rfl) ⟨3772466, by rfl⟩ : syracuseStep 5029955 = 7544933) B7544933
theorem B3353303 : Blo 2235435 3353303 := bstep (se 1 (by rfl) ⟨2514977, by rfl⟩ : syracuseStep 3353303 = 5029955) B5029955
theorem B2235535 : Blo 2235435 2235535 := bstep (se 1 (by rfl) ⟨1676651, by rfl⟩ : syracuseStep 2235535 = 3353303) B3353303
theorem B3353309 : Blo 2235435 3353309 := bbase (se 3 (by rfl) ⟨628745, by rfl⟩ : syracuseStep 3353309 = 1257491) (by norm_num)
theorem B2235539 : Blo 2235435 2235539 := bstep (se 1 (by rfl) ⟨1676654, by rfl⟩ : syracuseStep 2235539 = 3353309) B3353309
theorem B5029973 : Blo 2235435 5029973 := bbase (se 8 (by rfl) ⟨29472, by rfl⟩ : syracuseStep 5029973 = 58945) (by norm_num)
theorem B3353315 : Blo 2235435 3353315 := bstep (se 1 (by rfl) ⟨2514986, by rfl⟩ : syracuseStep 3353315 = 5029973) B5029973
theorem B2235543 : Blo 2235435 2235543 := bstep (se 1 (by rfl) ⟨1676657, by rfl⟩ : syracuseStep 2235543 = 3353315) B3353315
theorem B2419849 : Blo 2235435 2419849 := bbase (se 2 (by rfl) ⟨907443, by rfl⟩ : syracuseStep 2419849 = 1814887) (by norm_num)
theorem B3226465 : Blo 2235435 3226465 := bstep (se 2 (by rfl) ⟨1209924, by rfl⟩ : syracuseStep 3226465 = 2419849) B2419849
theorem B4301953 : Blo 2235435 4301953 := bstep (se 2 (by rfl) ⟨1613232, by rfl⟩ : syracuseStep 4301953 = 3226465) B3226465
theorem B22943749 : Blo 2235435 22943749 := bstep (se 4 (by rfl) ⟨2150976, by rfl⟩ : syracuseStep 22943749 = 4301953) B4301953
theorem B30591665 : Blo 2235435 30591665 := bstep (se 2 (by rfl) ⟨11471874, by rfl⟩ : syracuseStep 30591665 = 22943749) B22943749
theorem B20394443 : Blo 2235435 20394443 := bstep (se 1 (by rfl) ⟨15295832, by rfl⟩ : syracuseStep 20394443 = 30591665) B30591665
theorem B13596295 : Blo 2235435 13596295 := bstep (se 1 (by rfl) ⟨10197221, by rfl⟩ : syracuseStep 13596295 = 20394443) B20394443
theorem B18128393 : Blo 2235435 18128393 := bstep (se 2 (by rfl) ⟨6798147, by rfl⟩ : syracuseStep 18128393 = 13596295) B13596295
theorem B12085595 : Blo 2235435 12085595 := bstep (se 1 (by rfl) ⟨9064196, by rfl⟩ : syracuseStep 12085595 = 18128393) B18128393
theorem B8057063 : Blo 2235435 8057063 := bstep (se 1 (by rfl) ⟨6042797, by rfl⟩ : syracuseStep 8057063 = 12085595) B12085595
theorem B5371375 : Blo 2235435 5371375 := bstep (se 1 (by rfl) ⟨4028531, by rfl⟩ : syracuseStep 5371375 = 8057063) B8057063
theorem B7161833 : Blo 2235435 7161833 := bstep (se 2 (by rfl) ⟨2685687, by rfl⟩ : syracuseStep 7161833 = 5371375) B5371375
theorem B4774555 : Blo 2235435 4774555 := bstep (se 1 (by rfl) ⟨3580916, by rfl⟩ : syracuseStep 4774555 = 7161833) B7161833
theorem B6366073 : Blo 2235435 6366073 := bstep (se 2 (by rfl) ⟨2387277, by rfl⟩ : syracuseStep 6366073 = 4774555) B4774555
theorem B8488097 : Blo 2235435 8488097 := bstep (se 2 (by rfl) ⟨3183036, by rfl⟩ : syracuseStep 8488097 = 6366073) B6366073
theorem B5658731 : Blo 2235435 5658731 := bstep (se 1 (by rfl) ⟨4244048, by rfl⟩ : syracuseStep 5658731 = 8488097) B8488097
theorem B3772487 : Blo 2235435 3772487 := bstep (se 1 (by rfl) ⟨2829365, by rfl⟩ : syracuseStep 3772487 = 5658731) B5658731
theorem B2514991 : Blo 2235435 2514991 := bstep (se 1 (by rfl) ⟨1886243, by rfl⟩ : syracuseStep 2514991 = 3772487) B3772487
theorem B3353321 : Blo 2235435 3353321 := bstep (se 2 (by rfl) ⟨1257495, by rfl⟩ : syracuseStep 3353321 = 2514991) B2514991
theorem B2235547 : Blo 2235435 2235547 := bstep (se 1 (by rfl) ⟨1676660, by rfl⟩ : syracuseStep 2235547 = 3353321) B3353321
theorem B2419853 : Blo 2235435 2419853 := bbase (se 3 (by rfl) ⟨453722, by rfl⟩ : syracuseStep 2419853 = 907445) (by norm_num)
theorem B6452941 : Blo 2235435 6452941 := bstep (se 3 (by rfl) ⟨1209926, by rfl⟩ : syracuseStep 6452941 = 2419853) B2419853
theorem B8603921 : Blo 2235435 8603921 := bstep (se 2 (by rfl) ⟨3226470, by rfl⟩ : syracuseStep 8603921 = 6452941) B6452941
theorem B5735947 : Blo 2235435 5735947 := bstep (se 1 (by rfl) ⟨4301960, by rfl⟩ : syracuseStep 5735947 = 8603921) B8603921
theorem B7647929 : Blo 2235435 7647929 := bstep (se 2 (by rfl) ⟨2867973, by rfl⟩ : syracuseStep 7647929 = 5735947) B5735947
theorem B5098619 : Blo 2235435 5098619 := bstep (se 1 (by rfl) ⟨3823964, by rfl⟩ : syracuseStep 5098619 = 7647929) B7647929
theorem B3399079 : Blo 2235435 3399079 := bstep (se 1 (by rfl) ⟨2549309, by rfl⟩ : syracuseStep 3399079 = 5098619) B5098619
theorem B4532105 : Blo 2235435 4532105 := bstep (se 2 (by rfl) ⟨1699539, by rfl⟩ : syracuseStep 4532105 = 3399079) B3399079
theorem B12085613 : Blo 2235435 12085613 := bstep (se 3 (by rfl) ⟨2266052, by rfl⟩ : syracuseStep 12085613 = 4532105) B4532105
theorem B8057075 : Blo 2235435 8057075 := bstep (se 1 (by rfl) ⟨6042806, by rfl⟩ : syracuseStep 8057075 = 12085613) B12085613
theorem B21485533 : Blo 2235435 21485533 := bstep (se 3 (by rfl) ⟨4028537, by rfl⟩ : syracuseStep 21485533 = 8057075) B8057075
theorem B28647377 : Blo 2235435 28647377 := bstep (se 2 (by rfl) ⟨10742766, by rfl⟩ : syracuseStep 28647377 = 21485533) B21485533
theorem B19098251 : Blo 2235435 19098251 := bstep (se 1 (by rfl) ⟨14323688, by rfl⟩ : syracuseStep 19098251 = 28647377) B28647377
theorem B12732167 : Blo 2235435 12732167 := bstep (se 1 (by rfl) ⟨9549125, by rfl⟩ : syracuseStep 12732167 = 19098251) B19098251
theorem B8488111 : Blo 2235435 8488111 := bstep (se 1 (by rfl) ⟨6366083, by rfl⟩ : syracuseStep 8488111 = 12732167) B12732167
theorem B11317481 : Blo 2235435 11317481 := bstep (se 2 (by rfl) ⟨4244055, by rfl⟩ : syracuseStep 11317481 = 8488111) B8488111
theorem B7544987 : Blo 2235435 7544987 := bstep (se 1 (by rfl) ⟨5658740, by rfl⟩ : syracuseStep 7544987 = 11317481) B11317481
theorem B5029991 : Blo 2235435 5029991 := bstep (se 1 (by rfl) ⟨3772493, by rfl⟩ : syracuseStep 5029991 = 7544987) B7544987
theorem B3353327 : Blo 2235435 3353327 := bstep (se 1 (by rfl) ⟨2514995, by rfl⟩ : syracuseStep 3353327 = 5029991) B5029991
theorem B2235551 : Blo 2235435 2235551 := bstep (se 1 (by rfl) ⟨1676663, by rfl⟩ : syracuseStep 2235551 = 3353327) B3353327
theorem B3353333 : Blo 2235435 3353333 := bbase (se 5 (by rfl) ⟨157187, by rfl⟩ : syracuseStep 3353333 = 314375) (by norm_num)
theorem B2235555 : Blo 2235435 2235555 := bstep (se 1 (by rfl) ⟨1676666, by rfl⟩ : syracuseStep 2235555 = 3353333) B3353333
theorem B2266061 : Blo 2235435 2266061 := bbase (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) (by norm_num)
theorem B24171317 : Blo 2235435 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B16114211 : Blo 2235435 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B10742807 : Blo 2235435 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B7161871 : Blo 2235435 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B9549161 : Blo 2235435 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B6366107 : Blo 2235435 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B4244071 : Blo 2235435 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B5658761 : Blo 2235435 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B3772507 : Blo 2235435 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B5030009 : Blo 2235435 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B3353339 : Blo 2235435 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B2235559 : Blo 2235435 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B2515009 : Blo 2235435 2515009 := bbase (se 2 (by rfl) ⟨943128, by rfl⟩ : syracuseStep 2515009 = 1886257) (by norm_num)
theorem B3353345 : Blo 2235435 3353345 := bstep (se 2 (by rfl) ⟨1257504, by rfl⟩ : syracuseStep 3353345 = 2515009) B2515009
theorem B2235563 : Blo 2235435 2235563 := bstep (se 1 (by rfl) ⟨1676672, by rfl⟩ : syracuseStep 2235563 = 3353345) B3353345
theorem B5658781 : Blo 2235435 5658781 := bbase (se 3 (by rfl) ⟨1061021, by rfl⟩ : syracuseStep 5658781 = 2122043) (by norm_num)
theorem B7545041 : Blo 2235435 7545041 := bstep (se 2 (by rfl) ⟨2829390, by rfl⟩ : syracuseStep 7545041 = 5658781) B5658781
theorem B5030027 : Blo 2235435 5030027 := bstep (se 1 (by rfl) ⟨3772520, by rfl⟩ : syracuseStep 5030027 = 7545041) B7545041
theorem B3353351 : Blo 2235435 3353351 := bstep (se 1 (by rfl) ⟨2515013, by rfl⟩ : syracuseStep 3353351 = 5030027) B5030027
theorem B2235567 : Blo 2235435 2235567 := bstep (se 1 (by rfl) ⟨1676675, by rfl⟩ : syracuseStep 2235567 = 3353351) B3353351
theorem B3353357 : Blo 2235435 3353357 := bbase (se 3 (by rfl) ⟨628754, by rfl⟩ : syracuseStep 3353357 = 1257509) (by norm_num)
theorem B2235571 : Blo 2235435 2235571 := bstep (se 1 (by rfl) ⟨1676678, by rfl⟩ : syracuseStep 2235571 = 3353357) B3353357
theorem B5030045 : Blo 2235435 5030045 := bbase (se 3 (by rfl) ⟨943133, by rfl⟩ : syracuseStep 5030045 = 1886267) (by norm_num)
theorem B3353363 : Blo 2235435 3353363 := bstep (se 1 (by rfl) ⟨2515022, by rfl⟩ : syracuseStep 3353363 = 5030045) B5030045
theorem B2235575 : Blo 2235435 2235575 := bstep (se 1 (by rfl) ⟨1676681, by rfl⟩ : syracuseStep 2235575 = 3353363) B3353363
theorem B3772541 : Blo 2235435 3772541 := bbase (se 3 (by rfl) ⟨707351, by rfl⟩ : syracuseStep 3772541 = 1414703) (by norm_num)
theorem B2515027 : Blo 2235435 2515027 := bstep (se 1 (by rfl) ⟨1886270, by rfl⟩ : syracuseStep 2515027 = 3772541) B3772541
theorem B3353369 : Blo 2235435 3353369 := bstep (se 2 (by rfl) ⟨1257513, by rfl⟩ : syracuseStep 3353369 = 2515027) B2515027
theorem B2235579 : Blo 2235435 2235579 := bstep (se 1 (by rfl) ⟨1676684, by rfl⟩ : syracuseStep 2235579 = 3353369) B3353369
theorem B68832341 : Blo 2235435 68832341 := bbase (se 8 (by rfl) ⟨403314, by rfl⟩ : syracuseStep 68832341 = 806629) (by norm_num)
theorem B45888227 : Blo 2235435 45888227 := bstep (se 1 (by rfl) ⟨34416170, by rfl⟩ : syracuseStep 45888227 = 68832341) B68832341
theorem B30592151 : Blo 2235435 30592151 := bstep (se 1 (by rfl) ⟨22944113, by rfl⟩ : syracuseStep 30592151 = 45888227) B45888227
theorem B20394767 : Blo 2235435 20394767 := bstep (se 1 (by rfl) ⟨15296075, by rfl⟩ : syracuseStep 20394767 = 30592151) B30592151
theorem B13596511 : Blo 2235435 13596511 := bstep (se 1 (by rfl) ⟨10197383, by rfl⟩ : syracuseStep 13596511 = 20394767) B20394767
theorem B18128681 : Blo 2235435 18128681 := bstep (se 2 (by rfl) ⟨6798255, by rfl⟩ : syracuseStep 18128681 = 13596511) B13596511
theorem B12085787 : Blo 2235435 12085787 := bstep (se 1 (by rfl) ⟨9064340, by rfl⟩ : syracuseStep 12085787 = 18128681) B18128681
theorem B8057191 : Blo 2235435 8057191 := bstep (se 1 (by rfl) ⟨6042893, by rfl⟩ : syracuseStep 8057191 = 12085787) B12085787
theorem B10742921 : Blo 2235435 10742921 := bstep (se 2 (by rfl) ⟨4028595, by rfl⟩ : syracuseStep 10742921 = 8057191) B8057191
theorem B7161947 : Blo 2235435 7161947 := bstep (se 1 (by rfl) ⟨5371460, by rfl⟩ : syracuseStep 7161947 = 10742921) B10742921
theorem B4774631 : Blo 2235435 4774631 := bstep (se 1 (by rfl) ⟨3580973, by rfl⟩ : syracuseStep 4774631 = 7161947) B7161947
theorem B12732349 : Blo 2235435 12732349 := bstep (se 3 (by rfl) ⟨2387315, by rfl⟩ : syracuseStep 12732349 = 4774631) B4774631
theorem B16976465 : Blo 2235435 16976465 := bstep (se 2 (by rfl) ⟨6366174, by rfl⟩ : syracuseStep 16976465 = 12732349) B12732349
theorem B11317643 : Blo 2235435 11317643 := bstep (se 1 (by rfl) ⟨8488232, by rfl⟩ : syracuseStep 11317643 = 16976465) B16976465
theorem B7545095 : Blo 2235435 7545095 := bstep (se 1 (by rfl) ⟨5658821, by rfl⟩ : syracuseStep 7545095 = 11317643) B11317643
theorem B5030063 : Blo 2235435 5030063 := bstep (se 1 (by rfl) ⟨3772547, by rfl⟩ : syracuseStep 5030063 = 7545095) B7545095
theorem B3353375 : Blo 2235435 3353375 := bstep (se 1 (by rfl) ⟨2515031, by rfl⟩ : syracuseStep 3353375 = 5030063) B5030063
theorem B2235583 : Blo 2235435 2235583 := bstep (se 1 (by rfl) ⟨1676687, by rfl⟩ : syracuseStep 2235583 = 3353375) B3353375
theorem B3353381 : Blo 2235435 3353381 := bbase (se 4 (by rfl) ⟨314379, by rfl⟩ : syracuseStep 3353381 = 628759) (by norm_num)
theorem B2235587 : Blo 2235435 2235587 := bstep (se 1 (by rfl) ⟨1676690, by rfl⟩ : syracuseStep 2235587 = 3353381) B3353381
theorem B2829421 : Blo 2235435 2829421 := bbase (se 3 (by rfl) ⟨530516, by rfl⟩ : syracuseStep 2829421 = 1061033) (by norm_num)
theorem B3772561 : Blo 2235435 3772561 := bstep (se 2 (by rfl) ⟨1414710, by rfl⟩ : syracuseStep 3772561 = 2829421) B2829421
theorem B5030081 : Blo 2235435 5030081 := bstep (se 2 (by rfl) ⟨1886280, by rfl⟩ : syracuseStep 5030081 = 3772561) B3772561
theorem B3353387 : Blo 2235435 3353387 := bstep (se 1 (by rfl) ⟨2515040, by rfl⟩ : syracuseStep 3353387 = 5030081) B5030081
theorem B2235591 : Blo 2235435 2235591 := bstep (se 1 (by rfl) ⟨1676693, by rfl⟩ : syracuseStep 2235591 = 3353387) B3353387
theorem B2515045 : Blo 2235435 2515045 := bbase (se 4 (by rfl) ⟨235785, by rfl⟩ : syracuseStep 2515045 = 471571) (by norm_num)
theorem B3353393 : Blo 2235435 3353393 := bstep (se 2 (by rfl) ⟨1257522, by rfl⟩ : syracuseStep 3353393 = 2515045) B2515045
theorem B2235595 : Blo 2235435 2235595 := bstep (se 1 (by rfl) ⟨1676696, by rfl⟩ : syracuseStep 2235595 = 3353393) B3353393
theorem B2387333 : Blo 2235435 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B6366221 : Blo 2235435 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B4244147 : Blo 2235435 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B2829431 : Blo 2235435 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B7545149 : Blo 2235435 7545149 := bstep (se 3 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 7545149 = 2829431) B2829431
theorem B5030099 : Blo 2235435 5030099 := bstep (se 1 (by rfl) ⟨3772574, by rfl⟩ : syracuseStep 5030099 = 7545149) B7545149
theorem B3353399 : Blo 2235435 3353399 := bstep (se 1 (by rfl) ⟨2515049, by rfl⟩ : syracuseStep 3353399 = 5030099) B5030099
theorem B2235599 : Blo 2235435 2235599 := bstep (se 1 (by rfl) ⟨1676699, by rfl⟩ : syracuseStep 2235599 = 3353399) B3353399
theorem B3353405 : Blo 2235435 3353405 := bbase (se 3 (by rfl) ⟨628763, by rfl⟩ : syracuseStep 3353405 = 1257527) (by norm_num)
theorem B2235603 : Blo 2235435 2235603 := bstep (se 1 (by rfl) ⟨1676702, by rfl⟩ : syracuseStep 2235603 = 3353405) B3353405
theorem B5030117 : Blo 2235435 5030117 := bbase (se 4 (by rfl) ⟨471573, by rfl⟩ : syracuseStep 5030117 = 943147) (by norm_num)
theorem B3353411 : Blo 2235435 3353411 := bstep (se 1 (by rfl) ⟨2515058, by rfl⟩ : syracuseStep 3353411 = 5030117) B5030117
theorem B2235607 : Blo 2235435 2235607 := bstep (se 1 (by rfl) ⟨1676705, by rfl⟩ : syracuseStep 2235607 = 3353411) B3353411
theorem B5658893 : Blo 2235435 5658893 := bbase (se 3 (by rfl) ⟨1061042, by rfl⟩ : syracuseStep 5658893 = 2122085) (by norm_num)
theorem B3772595 : Blo 2235435 3772595 := bstep (se 1 (by rfl) ⟨2829446, by rfl⟩ : syracuseStep 3772595 = 5658893) B5658893
theorem B2515063 : Blo 2235435 2515063 := bstep (se 1 (by rfl) ⟨1886297, by rfl⟩ : syracuseStep 2515063 = 3772595) B3772595
theorem B3353417 : Blo 2235435 3353417 := bstep (se 2 (by rfl) ⟨1257531, by rfl⟩ : syracuseStep 3353417 = 2515063) B2515063
theorem B2235611 : Blo 2235435 2235611 := bstep (se 1 (by rfl) ⟨1676708, by rfl⟩ : syracuseStep 2235611 = 3353417) B3353417
theorem B3183133 : Blo 2235435 3183133 := bbase (se 3 (by rfl) ⟨596837, by rfl⟩ : syracuseStep 3183133 = 1193675) (by norm_num)
theorem B4244177 : Blo 2235435 4244177 := bstep (se 2 (by rfl) ⟨1591566, by rfl⟩ : syracuseStep 4244177 = 3183133) B3183133
theorem B11317805 : Blo 2235435 11317805 := bstep (se 3 (by rfl) ⟨2122088, by rfl⟩ : syracuseStep 11317805 = 4244177) B4244177
theorem B7545203 : Blo 2235435 7545203 := bstep (se 1 (by rfl) ⟨5658902, by rfl⟩ : syracuseStep 7545203 = 11317805) B11317805
theorem B5030135 : Blo 2235435 5030135 := bstep (se 1 (by rfl) ⟨3772601, by rfl⟩ : syracuseStep 5030135 = 7545203) B7545203
theorem B3353423 : Blo 2235435 3353423 := bstep (se 1 (by rfl) ⟨2515067, by rfl⟩ : syracuseStep 3353423 = 5030135) B5030135
theorem B2235615 : Blo 2235435 2235615 := bstep (se 1 (by rfl) ⟨1676711, by rfl⟩ : syracuseStep 2235615 = 3353423) B3353423
theorem B3353429 : Blo 2235435 3353429 := bbase (se 9 (by rfl) ⟨9824, by rfl⟩ : syracuseStep 3353429 = 19649) (by norm_num)
theorem B2235619 : Blo 2235435 2235619 := bstep (se 1 (by rfl) ⟨1676714, by rfl⟩ : syracuseStep 2235619 = 3353429) B3353429
theorem B4774717 : Blo 2235435 4774717 := bbase (se 3 (by rfl) ⟨895259, by rfl⟩ : syracuseStep 4774717 = 1790519) (by norm_num)
theorem B6366289 : Blo 2235435 6366289 := bstep (se 2 (by rfl) ⟨2387358, by rfl⟩ : syracuseStep 6366289 = 4774717) B4774717
theorem B8488385 : Blo 2235435 8488385 := bstep (se 2 (by rfl) ⟨3183144, by rfl⟩ : syracuseStep 8488385 = 6366289) B6366289
theorem B5658923 : Blo 2235435 5658923 := bstep (se 1 (by rfl) ⟨4244192, by rfl⟩ : syracuseStep 5658923 = 8488385) B8488385
theorem B3772615 : Blo 2235435 3772615 := bstep (se 1 (by rfl) ⟨2829461, by rfl⟩ : syracuseStep 3772615 = 5658923) B5658923
theorem B5030153 : Blo 2235435 5030153 := bstep (se 2 (by rfl) ⟨1886307, by rfl⟩ : syracuseStep 5030153 = 3772615) B3772615
theorem B3353435 : Blo 2235435 3353435 := bstep (se 1 (by rfl) ⟨2515076, by rfl⟩ : syracuseStep 3353435 = 5030153) B5030153
theorem B2235623 : Blo 2235435 2235623 := bstep (se 1 (by rfl) ⟨1676717, by rfl⟩ : syracuseStep 2235623 = 3353435) B3353435
theorem B2515081 : Blo 2235435 2515081 := bbase (se 2 (by rfl) ⟨943155, by rfl⟩ : syracuseStep 2515081 = 1886311) (by norm_num)
theorem B3353441 : Blo 2235435 3353441 := bstep (se 2 (by rfl) ⟨1257540, by rfl⟩ : syracuseStep 3353441 = 2515081) B2515081
theorem B2235627 : Blo 2235435 2235627 := bstep (se 1 (by rfl) ⟨1676720, by rfl⟩ : syracuseStep 2235627 = 3353441) B3353441
theorem B3629909 : Blo 2235435 3629909 := bbase (se 9 (by rfl) ⟨10634, by rfl⟩ : syracuseStep 3629909 = 21269) (by norm_num)
theorem B2419939 : Blo 2235435 2419939 := bstep (se 1 (by rfl) ⟨1814954, by rfl⟩ : syracuseStep 2419939 = 3629909) B3629909
theorem B12906341 : Blo 2235435 12906341 := bstep (se 4 (by rfl) ⟨1209969, by rfl⟩ : syracuseStep 12906341 = 2419939) B2419939
theorem B8604227 : Blo 2235435 8604227 := bstep (se 1 (by rfl) ⟨6453170, by rfl⟩ : syracuseStep 8604227 = 12906341) B12906341
theorem B5736151 : Blo 2235435 5736151 := bstep (se 1 (by rfl) ⟨4302113, by rfl⟩ : syracuseStep 5736151 = 8604227) B8604227
theorem B7648201 : Blo 2235435 7648201 := bstep (se 2 (by rfl) ⟨2868075, by rfl⟩ : syracuseStep 7648201 = 5736151) B5736151
theorem B40790405 : Blo 2235435 40790405 := bstep (se 4 (by rfl) ⟨3824100, by rfl⟩ : syracuseStep 40790405 = 7648201) B7648201
theorem B27193603 : Blo 2235435 27193603 := bstep (se 1 (by rfl) ⟨20395202, by rfl⟩ : syracuseStep 27193603 = 40790405) B40790405
theorem B36258137 : Blo 2235435 36258137 := bstep (se 2 (by rfl) ⟨13596801, by rfl⟩ : syracuseStep 36258137 = 27193603) B27193603
theorem B24172091 : Blo 2235435 24172091 := bstep (se 1 (by rfl) ⟨18129068, by rfl⟩ : syracuseStep 24172091 = 36258137) B36258137
theorem B16114727 : Blo 2235435 16114727 := bstep (se 1 (by rfl) ⟨12086045, by rfl⟩ : syracuseStep 16114727 = 24172091) B24172091
theorem B42972605 : Blo 2235435 42972605 := bstep (se 3 (by rfl) ⟨8057363, by rfl⟩ : syracuseStep 42972605 = 16114727) B16114727
theorem B28648403 : Blo 2235435 28648403 := bstep (se 1 (by rfl) ⟨21486302, by rfl⟩ : syracuseStep 28648403 = 42972605) B42972605
theorem B19098935 : Blo 2235435 19098935 := bstep (se 1 (by rfl) ⟨14324201, by rfl⟩ : syracuseStep 19098935 = 28648403) B28648403
theorem B12732623 : Blo 2235435 12732623 := bstep (se 1 (by rfl) ⟨9549467, by rfl⟩ : syracuseStep 12732623 = 19098935) B19098935
theorem B8488415 : Blo 2235435 8488415 := bstep (se 1 (by rfl) ⟨6366311, by rfl⟩ : syracuseStep 8488415 = 12732623) B12732623
theorem B5658943 : Blo 2235435 5658943 := bstep (se 1 (by rfl) ⟨4244207, by rfl⟩ : syracuseStep 5658943 = 8488415) B8488415
theorem B7545257 : Blo 2235435 7545257 := bstep (se 2 (by rfl) ⟨2829471, by rfl⟩ : syracuseStep 7545257 = 5658943) B5658943
theorem B5030171 : Blo 2235435 5030171 := bstep (se 1 (by rfl) ⟨3772628, by rfl⟩ : syracuseStep 5030171 = 7545257) B7545257
theorem B3353447 : Blo 2235435 3353447 := bstep (se 1 (by rfl) ⟨2515085, by rfl⟩ : syracuseStep 3353447 = 5030171) B5030171
theorem B2235631 : Blo 2235435 2235631 := bstep (se 1 (by rfl) ⟨1676723, by rfl⟩ : syracuseStep 2235631 = 3353447) B3353447
theorem B3353453 : Blo 2235435 3353453 := bbase (se 3 (by rfl) ⟨628772, by rfl⟩ : syracuseStep 3353453 = 1257545) (by norm_num)
theorem B2235635 : Blo 2235435 2235635 := bstep (se 1 (by rfl) ⟨1676726, by rfl⟩ : syracuseStep 2235635 = 3353453) B3353453
theorem B5030189 : Blo 2235435 5030189 := bbase (se 3 (by rfl) ⟨943160, by rfl⟩ : syracuseStep 5030189 = 1886321) (by norm_num)
theorem B3353459 : Blo 2235435 3353459 := bstep (se 1 (by rfl) ⟨2515094, by rfl⟩ : syracuseStep 3353459 = 5030189) B5030189
theorem B2235639 : Blo 2235435 2235639 := bstep (se 1 (by rfl) ⟨1676729, by rfl⟩ : syracuseStep 2235639 = 3353459) B3353459
theorem B3399221 : Blo 2235435 3399221 := bbase (se 5 (by rfl) ⟨159338, by rfl⟩ : syracuseStep 3399221 = 318677) (by norm_num)
theorem B2266147 : Blo 2235435 2266147 := bstep (se 1 (by rfl) ⟨1699610, by rfl⟩ : syracuseStep 2266147 = 3399221) B3399221
theorem B3021529 : Blo 2235435 3021529 := bstep (se 2 (by rfl) ⟨1133073, by rfl⟩ : syracuseStep 3021529 = 2266147) B2266147
theorem B4028705 : Blo 2235435 4028705 := bstep (se 2 (by rfl) ⟨1510764, by rfl⟩ : syracuseStep 4028705 = 3021529) B3021529
theorem B2685803 : Blo 2235435 2685803 := bstep (se 1 (by rfl) ⟨2014352, by rfl⟩ : syracuseStep 2685803 = 4028705) B4028705
theorem B7162141 : Blo 2235435 7162141 := bstep (se 3 (by rfl) ⟨1342901, by rfl⟩ : syracuseStep 7162141 = 2685803) B2685803
theorem B9549521 : Blo 2235435 9549521 := bstep (se 2 (by rfl) ⟨3581070, by rfl⟩ : syracuseStep 9549521 = 7162141) B7162141
theorem B6366347 : Blo 2235435 6366347 := bstep (se 1 (by rfl) ⟨4774760, by rfl⟩ : syracuseStep 6366347 = 9549521) B9549521
theorem B4244231 : Blo 2235435 4244231 := bstep (se 1 (by rfl) ⟨3183173, by rfl⟩ : syracuseStep 4244231 = 6366347) B6366347
theorem B2829487 : Blo 2235435 2829487 := bstep (se 1 (by rfl) ⟨2122115, by rfl⟩ : syracuseStep 2829487 = 4244231) B4244231
theorem B3772649 : Blo 2235435 3772649 := bstep (se 2 (by rfl) ⟨1414743, by rfl⟩ : syracuseStep 3772649 = 2829487) B2829487
theorem B2515099 : Blo 2235435 2515099 := bstep (se 1 (by rfl) ⟨1886324, by rfl⟩ : syracuseStep 2515099 = 3772649) B3772649
theorem B3353465 : Blo 2235435 3353465 := bstep (se 2 (by rfl) ⟨1257549, by rfl⟩ : syracuseStep 3353465 = 2515099) B2515099
theorem B2235643 : Blo 2235435 2235643 := bstep (se 1 (by rfl) ⟨1676732, by rfl⟩ : syracuseStep 2235643 = 3353465) B3353465
theorem B5098837 : Blo 2235435 5098837 := bbase (se 11 (by rfl) ⟨3734, by rfl⟩ : syracuseStep 5098837 = 7469) (by norm_num)
theorem B6798449 : Blo 2235435 6798449 := bstep (se 2 (by rfl) ⟨2549418, by rfl⟩ : syracuseStep 6798449 = 5098837) B5098837
theorem B18129197 : Blo 2235435 18129197 := bstep (se 3 (by rfl) ⟨3399224, by rfl⟩ : syracuseStep 18129197 = 6798449) B6798449
theorem B48344525 : Blo 2235435 48344525 := bstep (se 3 (by rfl) ⟨9064598, by rfl⟩ : syracuseStep 48344525 = 18129197) B18129197
theorem B32229683 : Blo 2235435 32229683 := bstep (se 1 (by rfl) ⟨24172262, by rfl⟩ : syracuseStep 32229683 = 48344525) B48344525
theorem B21486455 : Blo 2235435 21486455 := bstep (se 1 (by rfl) ⟨16114841, by rfl⟩ : syracuseStep 21486455 = 32229683) B32229683
theorem B14324303 : Blo 2235435 14324303 := bstep (se 1 (by rfl) ⟨10743227, by rfl⟩ : syracuseStep 14324303 = 21486455) B21486455
theorem B38198141 : Blo 2235435 38198141 := bstep (se 3 (by rfl) ⟨7162151, by rfl⟩ : syracuseStep 38198141 = 14324303) B14324303
theorem B25465427 : Blo 2235435 25465427 := bstep (se 1 (by rfl) ⟨19099070, by rfl⟩ : syracuseStep 25465427 = 38198141) B38198141
theorem B16976951 : Blo 2235435 16976951 := bstep (se 1 (by rfl) ⟨12732713, by rfl⟩ : syracuseStep 16976951 = 25465427) B25465427
theorem B11317967 : Blo 2235435 11317967 := bstep (se 1 (by rfl) ⟨8488475, by rfl⟩ : syracuseStep 11317967 = 16976951) B16976951
theorem B7545311 : Blo 2235435 7545311 := bstep (se 1 (by rfl) ⟨5658983, by rfl⟩ : syracuseStep 7545311 = 11317967) B11317967
theorem B5030207 : Blo 2235435 5030207 := bstep (se 1 (by rfl) ⟨3772655, by rfl⟩ : syracuseStep 5030207 = 7545311) B7545311
theorem B3353471 : Blo 2235435 3353471 := bstep (se 1 (by rfl) ⟨2515103, by rfl⟩ : syracuseStep 3353471 = 5030207) B5030207
theorem B2235647 : Blo 2235435 2235647 := bstep (se 1 (by rfl) ⟨1676735, by rfl⟩ : syracuseStep 2235647 = 3353471) B3353471
theorem B3353477 : Blo 2235435 3353477 := bbase (se 4 (by rfl) ⟨314388, by rfl⟩ : syracuseStep 3353477 = 628777) (by norm_num)
theorem B2235651 : Blo 2235435 2235651 := bstep (se 1 (by rfl) ⟨1676738, by rfl⟩ : syracuseStep 2235651 = 3353477) B3353477
theorem B3772669 : Blo 2235435 3772669 := bbase (se 3 (by rfl) ⟨707375, by rfl⟩ : syracuseStep 3772669 = 1414751) (by norm_num)
theorem B5030225 : Blo 2235435 5030225 := bstep (se 2 (by rfl) ⟨1886334, by rfl⟩ : syracuseStep 5030225 = 3772669) B3772669
theorem B3353483 : Blo 2235435 3353483 := bstep (se 1 (by rfl) ⟨2515112, by rfl⟩ : syracuseStep 3353483 = 5030225) B5030225
theorem B2235655 : Blo 2235435 2235655 := bstep (se 1 (by rfl) ⟨1676741, by rfl⟩ : syracuseStep 2235655 = 3353483) B3353483
theorem B2515117 : Blo 2235435 2515117 := bbase (se 3 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 2515117 = 943169) (by norm_num)
theorem B3353489 : Blo 2235435 3353489 := bstep (se 2 (by rfl) ⟨1257558, by rfl⟩ : syracuseStep 3353489 = 2515117) B2515117
theorem B2235659 : Blo 2235435 2235659 := bstep (se 1 (by rfl) ⟨1676744, by rfl⟩ : syracuseStep 2235659 = 3353489) B3353489
theorem B7545365 : Blo 2235435 7545365 := bbase (se 6 (by rfl) ⟨176844, by rfl⟩ : syracuseStep 7545365 = 353689) (by norm_num)
theorem B5030243 : Blo 2235435 5030243 := bstep (se 1 (by rfl) ⟨3772682, by rfl⟩ : syracuseStep 5030243 = 7545365) B7545365
theorem B3353495 : Blo 2235435 3353495 := bstep (se 1 (by rfl) ⟨2515121, by rfl⟩ : syracuseStep 3353495 = 5030243) B5030243
theorem B2235663 : Blo 2235435 2235663 := bstep (se 1 (by rfl) ⟨1676747, by rfl⟩ : syracuseStep 2235663 = 3353495) B3353495
theorem B3353501 : Blo 2235435 3353501 := bbase (se 3 (by rfl) ⟨628781, by rfl⟩ : syracuseStep 3353501 = 1257563) (by norm_num)
theorem B2235667 : Blo 2235435 2235667 := bstep (se 1 (by rfl) ⟨1676750, by rfl⟩ : syracuseStep 2235667 = 3353501) B3353501
theorem B5030261 : Blo 2235435 5030261 := bbase (se 5 (by rfl) ⟨235793, by rfl⟩ : syracuseStep 5030261 = 471587) (by norm_num)
theorem B3353507 : Blo 2235435 3353507 := bstep (se 1 (by rfl) ⟨2515130, by rfl⟩ : syracuseStep 3353507 = 5030261) B5030261
theorem B2235671 : Blo 2235435 2235671 := bstep (se 1 (by rfl) ⟨1676753, by rfl⟩ : syracuseStep 2235671 = 3353507) B3353507
theorem B2685841 : Blo 2235435 2685841 := bbase (se 2 (by rfl) ⟨1007190, by rfl⟩ : syracuseStep 2685841 = 2014381) (by norm_num)
theorem B14324485 : Blo 2235435 14324485 := bstep (se 4 (by rfl) ⟨1342920, by rfl⟩ : syracuseStep 14324485 = 2685841) B2685841
theorem B19099313 : Blo 2235435 19099313 := bstep (se 2 (by rfl) ⟨7162242, by rfl⟩ : syracuseStep 19099313 = 14324485) B14324485
theorem B12732875 : Blo 2235435 12732875 := bstep (se 1 (by rfl) ⟨9549656, by rfl⟩ : syracuseStep 12732875 = 19099313) B19099313
theorem B8488583 : Blo 2235435 8488583 := bstep (se 1 (by rfl) ⟨6366437, by rfl⟩ : syracuseStep 8488583 = 12732875) B12732875
theorem B5659055 : Blo 2235435 5659055 := bstep (se 1 (by rfl) ⟨4244291, by rfl⟩ : syracuseStep 5659055 = 8488583) B8488583
theorem B3772703 : Blo 2235435 3772703 := bstep (se 1 (by rfl) ⟨2829527, by rfl⟩ : syracuseStep 3772703 = 5659055) B5659055
theorem B2515135 : Blo 2235435 2515135 := bstep (se 1 (by rfl) ⟨1886351, by rfl⟩ : syracuseStep 2515135 = 3772703) B3772703
theorem B3353513 : Blo 2235435 3353513 := bstep (se 2 (by rfl) ⟨1257567, by rfl⟩ : syracuseStep 3353513 = 2515135) B2515135
theorem B2235675 : Blo 2235435 2235675 := bstep (se 1 (by rfl) ⟨1676756, by rfl⟩ : syracuseStep 2235675 = 3353513) B3353513
theorem B8488597 : Blo 2235435 8488597 := bbase (se 6 (by rfl) ⟨198951, by rfl⟩ : syracuseStep 8488597 = 397903) (by norm_num)
theorem B11318129 : Blo 2235435 11318129 := bstep (se 2 (by rfl) ⟨4244298, by rfl⟩ : syracuseStep 11318129 = 8488597) B8488597
theorem B7545419 : Blo 2235435 7545419 := bstep (se 1 (by rfl) ⟨5659064, by rfl⟩ : syracuseStep 7545419 = 11318129) B11318129
theorem B5030279 : Blo 2235435 5030279 := bstep (se 1 (by rfl) ⟨3772709, by rfl⟩ : syracuseStep 5030279 = 7545419) B7545419
theorem B3353519 : Blo 2235435 3353519 := bstep (se 1 (by rfl) ⟨2515139, by rfl⟩ : syracuseStep 3353519 = 5030279) B5030279
theorem B2235679 : Blo 2235435 2235679 := bstep (se 1 (by rfl) ⟨1676759, by rfl⟩ : syracuseStep 2235679 = 3353519) B3353519
theorem B3353525 : Blo 2235435 3353525 := bbase (se 5 (by rfl) ⟨157196, by rfl⟩ : syracuseStep 3353525 = 314393) (by norm_num)
theorem B2235683 : Blo 2235435 2235683 := bstep (se 1 (by rfl) ⟨1676762, by rfl⟩ : syracuseStep 2235683 = 3353525) B3353525
theorem B5659085 : Blo 2235435 5659085 := bbase (se 3 (by rfl) ⟨1061078, by rfl⟩ : syracuseStep 5659085 = 2122157) (by norm_num)
theorem B3772723 : Blo 2235435 3772723 := bstep (se 1 (by rfl) ⟨2829542, by rfl⟩ : syracuseStep 3772723 = 5659085) B5659085
theorem B5030297 : Blo 2235435 5030297 := bstep (se 2 (by rfl) ⟨1886361, by rfl⟩ : syracuseStep 5030297 = 3772723) B3772723
theorem B3353531 : Blo 2235435 3353531 := bstep (se 1 (by rfl) ⟨2515148, by rfl⟩ : syracuseStep 3353531 = 5030297) B5030297
theorem B2235687 : Blo 2235435 2235687 := bstep (se 1 (by rfl) ⟨1676765, by rfl⟩ : syracuseStep 2235687 = 3353531) B3353531
theorem B2515153 : Blo 2235435 2515153 := bbase (se 2 (by rfl) ⟨943182, by rfl⟩ : syracuseStep 2515153 = 1886365) (by norm_num)
theorem B3353537 : Blo 2235435 3353537 := bstep (se 2 (by rfl) ⟨1257576, by rfl⟩ : syracuseStep 3353537 = 2515153) B2515153
theorem B2235691 : Blo 2235435 2235691 := bstep (se 1 (by rfl) ⟨1676768, by rfl⟩ : syracuseStep 2235691 = 3353537) B3353537
theorem B10743461 : Blo 2235435 10743461 := bbase (se 4 (by rfl) ⟨1007199, by rfl⟩ : syracuseStep 10743461 = 2014399) (by norm_num)
theorem B7162307 : Blo 2235435 7162307 := bstep (se 1 (by rfl) ⟨5371730, by rfl⟩ : syracuseStep 7162307 = 10743461) B10743461
theorem B4774871 : Blo 2235435 4774871 := bstep (se 1 (by rfl) ⟨3581153, by rfl⟩ : syracuseStep 4774871 = 7162307) B7162307
theorem B3183247 : Blo 2235435 3183247 := bstep (se 1 (by rfl) ⟨2387435, by rfl⟩ : syracuseStep 3183247 = 4774871) B4774871
theorem B4244329 : Blo 2235435 4244329 := bstep (se 2 (by rfl) ⟨1591623, by rfl⟩ : syracuseStep 4244329 = 3183247) B3183247
theorem B5659105 : Blo 2235435 5659105 := bstep (se 2 (by rfl) ⟨2122164, by rfl⟩ : syracuseStep 5659105 = 4244329) B4244329
theorem B7545473 : Blo 2235435 7545473 := bstep (se 2 (by rfl) ⟨2829552, by rfl⟩ : syracuseStep 7545473 = 5659105) B5659105
theorem B5030315 : Blo 2235435 5030315 := bstep (se 1 (by rfl) ⟨3772736, by rfl⟩ : syracuseStep 5030315 = 7545473) B7545473
theorem B3353543 : Blo 2235435 3353543 := bstep (se 1 (by rfl) ⟨2515157, by rfl⟩ : syracuseStep 3353543 = 5030315) B5030315
theorem B2235695 : Blo 2235435 2235695 := bstep (se 1 (by rfl) ⟨1676771, by rfl⟩ : syracuseStep 2235695 = 3353543) B3353543
theorem B3353549 : Blo 2235435 3353549 := bbase (se 3 (by rfl) ⟨628790, by rfl⟩ : syracuseStep 3353549 = 1257581) (by norm_num)
theorem B2235699 : Blo 2235435 2235699 := bstep (se 1 (by rfl) ⟨1676774, by rfl⟩ : syracuseStep 2235699 = 3353549) B3353549
theorem B5030333 : Blo 2235435 5030333 := bbase (se 3 (by rfl) ⟨943187, by rfl⟩ : syracuseStep 5030333 = 1886375) (by norm_num)
theorem B3353555 : Blo 2235435 3353555 := bstep (se 1 (by rfl) ⟨2515166, by rfl⟩ : syracuseStep 3353555 = 5030333) B5030333
theorem B2235703 : Blo 2235435 2235703 := bstep (se 1 (by rfl) ⟨1676777, by rfl⟩ : syracuseStep 2235703 = 3353555) B3353555
theorem B3772757 : Blo 2235435 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B2515171 : Blo 2235435 2515171 := bstep (se 1 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 2515171 = 3772757) B3772757
theorem B3353561 : Blo 2235435 3353561 := bstep (se 2 (by rfl) ⟨1257585, by rfl⟩ : syracuseStep 3353561 = 2515171) B2515171
theorem B2235707 : Blo 2235435 2235707 := bstep (se 1 (by rfl) ⟨1676780, by rfl⟩ : syracuseStep 2235707 = 3353561) B3353561
theorem B7162357 : Blo 2235435 7162357 := bbase (se 5 (by rfl) ⟨335735, by rfl⟩ : syracuseStep 7162357 = 671471) (by norm_num)
theorem B9549809 : Blo 2235435 9549809 := bstep (se 2 (by rfl) ⟨3581178, by rfl⟩ : syracuseStep 9549809 = 7162357) B7162357
theorem B6366539 : Blo 2235435 6366539 := bstep (se 1 (by rfl) ⟨4774904, by rfl⟩ : syracuseStep 6366539 = 9549809) B9549809
theorem B16977437 : Blo 2235435 16977437 := bstep (se 3 (by rfl) ⟨3183269, by rfl⟩ : syracuseStep 16977437 = 6366539) B6366539
theorem B11318291 : Blo 2235435 11318291 := bstep (se 1 (by rfl) ⟨8488718, by rfl⟩ : syracuseStep 11318291 = 16977437) B16977437
theorem B7545527 : Blo 2235435 7545527 := bstep (se 1 (by rfl) ⟨5659145, by rfl⟩ : syracuseStep 7545527 = 11318291) B11318291
theorem B5030351 : Blo 2235435 5030351 := bstep (se 1 (by rfl) ⟨3772763, by rfl⟩ : syracuseStep 5030351 = 7545527) B7545527
theorem B3353567 : Blo 2235435 3353567 := bstep (se 1 (by rfl) ⟨2515175, by rfl⟩ : syracuseStep 3353567 = 5030351) B5030351
theorem B2235711 : Blo 2235435 2235711 := bstep (se 1 (by rfl) ⟨1676783, by rfl⟩ : syracuseStep 2235711 = 3353567) B3353567
theorem B3353573 : Blo 2235435 3353573 := bbase (se 4 (by rfl) ⟨314397, by rfl⟩ : syracuseStep 3353573 = 628795) (by norm_num)
theorem B2235715 : Blo 2235435 2235715 := bstep (se 1 (by rfl) ⟨1676786, by rfl⟩ : syracuseStep 2235715 = 3353573) B3353573
theorem B9549845 : Blo 2235435 9549845 := bbase (se 6 (by rfl) ⟨223824, by rfl⟩ : syracuseStep 9549845 = 447649) (by norm_num)
theorem B6366563 : Blo 2235435 6366563 := bstep (se 1 (by rfl) ⟨4774922, by rfl⟩ : syracuseStep 6366563 = 9549845) B9549845
theorem B4244375 : Blo 2235435 4244375 := bstep (se 1 (by rfl) ⟨3183281, by rfl⟩ : syracuseStep 4244375 = 6366563) B6366563
theorem B2829583 : Blo 2235435 2829583 := bstep (se 1 (by rfl) ⟨2122187, by rfl⟩ : syracuseStep 2829583 = 4244375) B4244375
theorem B3772777 : Blo 2235435 3772777 := bstep (se 2 (by rfl) ⟨1414791, by rfl⟩ : syracuseStep 3772777 = 2829583) B2829583
theorem B5030369 : Blo 2235435 5030369 := bstep (se 2 (by rfl) ⟨1886388, by rfl⟩ : syracuseStep 5030369 = 3772777) B3772777
theorem B3353579 : Blo 2235435 3353579 := bstep (se 1 (by rfl) ⟨2515184, by rfl⟩ : syracuseStep 3353579 = 5030369) B5030369
theorem B2235719 : Blo 2235435 2235719 := bstep (se 1 (by rfl) ⟨1676789, by rfl⟩ : syracuseStep 2235719 = 3353579) B3353579
theorem B2515189 : Blo 2235435 2515189 := bbase (se 5 (by rfl) ⟨117899, by rfl⟩ : syracuseStep 2515189 = 235799) (by norm_num)
theorem B3353585 : Blo 2235435 3353585 := bstep (se 2 (by rfl) ⟨1257594, by rfl⟩ : syracuseStep 3353585 = 2515189) B2515189
theorem B2235723 : Blo 2235435 2235723 := bstep (se 1 (by rfl) ⟨1676792, by rfl⟩ : syracuseStep 2235723 = 3353585) B3353585
theorem B2829593 : Blo 2235435 2829593 := bbase (se 2 (by rfl) ⟨1061097, by rfl⟩ : syracuseStep 2829593 = 2122195) (by norm_num)
theorem B7545581 : Blo 2235435 7545581 := bstep (se 3 (by rfl) ⟨1414796, by rfl⟩ : syracuseStep 7545581 = 2829593) B2829593
theorem B5030387 : Blo 2235435 5030387 := bstep (se 1 (by rfl) ⟨3772790, by rfl⟩ : syracuseStep 5030387 = 7545581) B7545581
theorem B3353591 : Blo 2235435 3353591 := bstep (se 1 (by rfl) ⟨2515193, by rfl⟩ : syracuseStep 3353591 = 5030387) B5030387
theorem B2235727 : Blo 2235435 2235727 := bstep (se 1 (by rfl) ⟨1676795, by rfl⟩ : syracuseStep 2235727 = 3353591) B3353591
theorem B3353597 : Blo 2235435 3353597 := bbase (se 3 (by rfl) ⟨628799, by rfl⟩ : syracuseStep 3353597 = 1257599) (by norm_num)
theorem B2235731 : Blo 2235435 2235731 := bstep (se 1 (by rfl) ⟨1676798, by rfl⟩ : syracuseStep 2235731 = 3353597) B3353597
theorem B5030405 : Blo 2235435 5030405 := bbase (se 4 (by rfl) ⟨471600, by rfl⟩ : syracuseStep 5030405 = 943201) (by norm_num)
theorem B3353603 : Blo 2235435 3353603 := bstep (se 1 (by rfl) ⟨2515202, by rfl⟩ : syracuseStep 3353603 = 5030405) B5030405
theorem B2235735 : Blo 2235435 2235735 := bstep (se 1 (by rfl) ⟨1676801, by rfl⟩ : syracuseStep 2235735 = 3353603) B3353603
theorem B4244413 : Blo 2235435 4244413 := bbase (se 3 (by rfl) ⟨795827, by rfl⟩ : syracuseStep 4244413 = 1591655) (by norm_num)
theorem B5659217 : Blo 2235435 5659217 := bstep (se 2 (by rfl) ⟨2122206, by rfl⟩ : syracuseStep 5659217 = 4244413) B4244413
theorem B3772811 : Blo 2235435 3772811 := bstep (se 1 (by rfl) ⟨2829608, by rfl⟩ : syracuseStep 3772811 = 5659217) B5659217
theorem B2515207 : Blo 2235435 2515207 := bstep (se 1 (by rfl) ⟨1886405, by rfl⟩ : syracuseStep 2515207 = 3772811) B3772811
theorem B3353609 : Blo 2235435 3353609 := bstep (se 2 (by rfl) ⟨1257603, by rfl⟩ : syracuseStep 3353609 = 2515207) B2515207
theorem B2235739 : Blo 2235435 2235739 := bstep (se 1 (by rfl) ⟨1676804, by rfl⟩ : syracuseStep 2235739 = 3353609) B3353609
theorem B11318453 : Blo 2235435 11318453 := bbase (se 5 (by rfl) ⟨530552, by rfl⟩ : syracuseStep 11318453 = 1061105) (by norm_num)
theorem B7545635 : Blo 2235435 7545635 := bstep (se 1 (by rfl) ⟨5659226, by rfl⟩ : syracuseStep 7545635 = 11318453) B11318453
theorem B5030423 : Blo 2235435 5030423 := bstep (se 1 (by rfl) ⟨3772817, by rfl⟩ : syracuseStep 5030423 = 7545635) B7545635
theorem B3353615 : Blo 2235435 3353615 := bstep (se 1 (by rfl) ⟨2515211, by rfl⟩ : syracuseStep 3353615 = 5030423) B5030423
theorem B2235743 : Blo 2235435 2235743 := bstep (se 1 (by rfl) ⟨1676807, by rfl⟩ : syracuseStep 2235743 = 3353615) B3353615
theorem B3353621 : Blo 2235435 3353621 := bbase (se 6 (by rfl) ⟨78600, by rfl⟩ : syracuseStep 3353621 = 157201) (by norm_num)
theorem B2235747 : Blo 2235435 2235747 := bstep (se 1 (by rfl) ⟨1676810, by rfl⟩ : syracuseStep 2235747 = 3353621) B3353621
theorem B2420069 : Blo 2235435 2420069 := bbase (se 4 (by rfl) ⟨226881, by rfl⟩ : syracuseStep 2420069 = 453763) (by norm_num)
theorem B6453517 : Blo 2235435 6453517 := bstep (se 3 (by rfl) ⟨1210034, by rfl⟩ : syracuseStep 6453517 = 2420069) B2420069
theorem B8604689 : Blo 2235435 8604689 := bstep (se 2 (by rfl) ⟨3226758, by rfl⟩ : syracuseStep 8604689 = 6453517) B6453517
theorem B22945837 : Blo 2235435 22945837 := bstep (se 3 (by rfl) ⟨4302344, by rfl⟩ : syracuseStep 22945837 = 8604689) B8604689
theorem B30594449 : Blo 2235435 30594449 := bstep (se 2 (by rfl) ⟨11472918, by rfl⟩ : syracuseStep 30594449 = 22945837) B22945837
theorem B20396299 : Blo 2235435 20396299 := bstep (se 1 (by rfl) ⟨15297224, by rfl⟩ : syracuseStep 20396299 = 30594449) B30594449
theorem B27195065 : Blo 2235435 27195065 := bstep (se 2 (by rfl) ⟨10198149, by rfl⟩ : syracuseStep 27195065 = 20396299) B20396299
theorem B18130043 : Blo 2235435 18130043 := bstep (se 1 (by rfl) ⟨13597532, by rfl⟩ : syracuseStep 18130043 = 27195065) B27195065
theorem B12086695 : Blo 2235435 12086695 := bstep (se 1 (by rfl) ⟨9065021, by rfl⟩ : syracuseStep 12086695 = 18130043) B18130043
theorem B16115593 : Blo 2235435 16115593 := bstep (se 2 (by rfl) ⟨6043347, by rfl⟩ : syracuseStep 16115593 = 12086695) B12086695
theorem B21487457 : Blo 2235435 21487457 := bstep (se 2 (by rfl) ⟨8057796, by rfl⟩ : syracuseStep 21487457 = 16115593) B16115593
theorem B14324971 : Blo 2235435 14324971 := bstep (se 1 (by rfl) ⟨10743728, by rfl⟩ : syracuseStep 14324971 = 21487457) B21487457
theorem B19099961 : Blo 2235435 19099961 := bstep (se 2 (by rfl) ⟨7162485, by rfl⟩ : syracuseStep 19099961 = 14324971) B14324971
theorem B12733307 : Blo 2235435 12733307 := bstep (se 1 (by rfl) ⟨9549980, by rfl⟩ : syracuseStep 12733307 = 19099961) B19099961
theorem B8488871 : Blo 2235435 8488871 := bstep (se 1 (by rfl) ⟨6366653, by rfl⟩ : syracuseStep 8488871 = 12733307) B12733307
theorem B5659247 : Blo 2235435 5659247 := bstep (se 1 (by rfl) ⟨4244435, by rfl⟩ : syracuseStep 5659247 = 8488871) B8488871
theorem B3772831 : Blo 2235435 3772831 := bstep (se 1 (by rfl) ⟨2829623, by rfl⟩ : syracuseStep 3772831 = 5659247) B5659247
theorem B5030441 : Blo 2235435 5030441 := bstep (se 2 (by rfl) ⟨1886415, by rfl⟩ : syracuseStep 5030441 = 3772831) B3772831
theorem B3353627 : Blo 2235435 3353627 := bstep (se 1 (by rfl) ⟨2515220, by rfl⟩ : syracuseStep 3353627 = 5030441) B5030441
theorem B2235751 : Blo 2235435 2235751 := bstep (se 1 (by rfl) ⟨1676813, by rfl⟩ : syracuseStep 2235751 = 3353627) B3353627
theorem B2515225 : Blo 2235435 2515225 := bbase (se 2 (by rfl) ⟨943209, by rfl⟩ : syracuseStep 2515225 = 1886419) (by norm_num)
theorem B3353633 : Blo 2235435 3353633 := bstep (se 2 (by rfl) ⟨1257612, by rfl⟩ : syracuseStep 3353633 = 2515225) B2515225
theorem B2235755 : Blo 2235435 2235755 := bstep (se 1 (by rfl) ⟨1676816, by rfl⟩ : syracuseStep 2235755 = 3353633) B3353633
theorem B8488901 : Blo 2235435 8488901 := bbase (se 4 (by rfl) ⟨795834, by rfl⟩ : syracuseStep 8488901 = 1591669) (by norm_num)
theorem B5659267 : Blo 2235435 5659267 := bstep (se 1 (by rfl) ⟨4244450, by rfl⟩ : syracuseStep 5659267 = 8488901) B8488901
theorem B7545689 : Blo 2235435 7545689 := bstep (se 2 (by rfl) ⟨2829633, by rfl⟩ : syracuseStep 7545689 = 5659267) B5659267
theorem B5030459 : Blo 2235435 5030459 := bstep (se 1 (by rfl) ⟨3772844, by rfl⟩ : syracuseStep 5030459 = 7545689) B7545689
theorem B3353639 : Blo 2235435 3353639 := bstep (se 1 (by rfl) ⟨2515229, by rfl⟩ : syracuseStep 3353639 = 5030459) B5030459
theorem B2235759 : Blo 2235435 2235759 := bstep (se 1 (by rfl) ⟨1676819, by rfl⟩ : syracuseStep 2235759 = 3353639) B3353639
theorem B3353645 : Blo 2235435 3353645 := bbase (se 3 (by rfl) ⟨628808, by rfl⟩ : syracuseStep 3353645 = 1257617) (by norm_num)
theorem B2235763 : Blo 2235435 2235763 := bstep (se 1 (by rfl) ⟨1676822, by rfl⟩ : syracuseStep 2235763 = 3353645) B3353645
theorem B5030477 : Blo 2235435 5030477 := bbase (se 3 (by rfl) ⟨943214, by rfl⟩ : syracuseStep 5030477 = 1886429) (by norm_num)
theorem B3353651 : Blo 2235435 3353651 := bstep (se 1 (by rfl) ⟨2515238, by rfl⟩ : syracuseStep 3353651 = 5030477) B5030477
theorem B2235767 : Blo 2235435 2235767 := bstep (se 1 (by rfl) ⟨1676825, by rfl⟩ : syracuseStep 2235767 = 3353651) B3353651
theorem B2829649 : Blo 2235435 2829649 := bbase (se 2 (by rfl) ⟨1061118, by rfl⟩ : syracuseStep 2829649 = 2122237) (by norm_num)
theorem B3772865 : Blo 2235435 3772865 := bstep (se 2 (by rfl) ⟨1414824, by rfl⟩ : syracuseStep 3772865 = 2829649) B2829649
theorem B2515243 : Blo 2235435 2515243 := bstep (se 1 (by rfl) ⟨1886432, by rfl⟩ : syracuseStep 2515243 = 3772865) B3772865
theorem B3353657 : Blo 2235435 3353657 := bstep (se 2 (by rfl) ⟨1257621, by rfl⟩ : syracuseStep 3353657 = 2515243) B2515243
theorem B2235771 : Blo 2235435 2235771 := bstep (se 1 (by rfl) ⟨1676828, by rfl⟩ : syracuseStep 2235771 = 3353657) B3353657
theorem B2685961 : Blo 2235435 2685961 := bbase (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) (by norm_num)
theorem B3581281 : Blo 2235435 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B4775041 : Blo 2235435 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B25466885 : Blo 2235435 25466885 := bstep (se 4 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 25466885 = 4775041) B4775041
theorem B16977923 : Blo 2235435 16977923 := bstep (se 1 (by rfl) ⟨12733442, by rfl⟩ : syracuseStep 16977923 = 25466885) B25466885
theorem B11318615 : Blo 2235435 11318615 := bstep (se 1 (by rfl) ⟨8488961, by rfl⟩ : syracuseStep 11318615 = 16977923) B16977923
theorem B7545743 : Blo 2235435 7545743 := bstep (se 1 (by rfl) ⟨5659307, by rfl⟩ : syracuseStep 7545743 = 11318615) B11318615
theorem B5030495 : Blo 2235435 5030495 := bstep (se 1 (by rfl) ⟨3772871, by rfl⟩ : syracuseStep 5030495 = 7545743) B7545743
theorem B3353663 : Blo 2235435 3353663 := bstep (se 1 (by rfl) ⟨2515247, by rfl⟩ : syracuseStep 3353663 = 5030495) B5030495
theorem B2235775 : Blo 2235435 2235775 := bstep (se 1 (by rfl) ⟨1676831, by rfl⟩ : syracuseStep 2235775 = 3353663) B3353663
theorem B3353669 : Blo 2235435 3353669 := bbase (se 4 (by rfl) ⟨314406, by rfl⟩ : syracuseStep 3353669 = 628813) (by norm_num)
theorem B2235779 : Blo 2235435 2235779 := bstep (se 1 (by rfl) ⟨1676834, by rfl⟩ : syracuseStep 2235779 = 3353669) B3353669
theorem B3772885 : Blo 2235435 3772885 := bbase (se 7 (by rfl) ⟨44213, by rfl⟩ : syracuseStep 3772885 = 88427) (by norm_num)
theorem B5030513 : Blo 2235435 5030513 := bstep (se 2 (by rfl) ⟨1886442, by rfl⟩ : syracuseStep 5030513 = 3772885) B3772885
theorem B3353675 : Blo 2235435 3353675 := bstep (se 1 (by rfl) ⟨2515256, by rfl⟩ : syracuseStep 3353675 = 5030513) B5030513
theorem B2235783 : Blo 2235435 2235783 := bstep (se 1 (by rfl) ⟨1676837, by rfl⟩ : syracuseStep 2235783 = 3353675) B3353675
theorem B2515261 : Blo 2235435 2515261 := bbase (se 3 (by rfl) ⟨471611, by rfl⟩ : syracuseStep 2515261 = 943223) (by norm_num)
theorem B3353681 : Blo 2235435 3353681 := bstep (se 2 (by rfl) ⟨1257630, by rfl⟩ : syracuseStep 3353681 = 2515261) B2515261
theorem B2235787 : Blo 2235435 2235787 := bstep (se 1 (by rfl) ⟨1676840, by rfl⟩ : syracuseStep 2235787 = 3353681) B3353681
theorem B7545797 : Blo 2235435 7545797 := bbase (se 4 (by rfl) ⟨707418, by rfl⟩ : syracuseStep 7545797 = 1414837) (by norm_num)
theorem B5030531 : Blo 2235435 5030531 := bstep (se 1 (by rfl) ⟨3772898, by rfl⟩ : syracuseStep 5030531 = 7545797) B7545797
theorem B3353687 : Blo 2235435 3353687 := bstep (se 1 (by rfl) ⟨2515265, by rfl⟩ : syracuseStep 3353687 = 5030531) B5030531
theorem B2235791 : Blo 2235435 2235791 := bstep (se 1 (by rfl) ⟨1676843, by rfl⟩ : syracuseStep 2235791 = 3353687) B3353687
theorem B3353693 : Blo 2235435 3353693 := bbase (se 3 (by rfl) ⟨628817, by rfl⟩ : syracuseStep 3353693 = 1257635) (by norm_num)
theorem B2235795 : Blo 2235435 2235795 := bstep (se 1 (by rfl) ⟨1676846, by rfl⟩ : syracuseStep 2235795 = 3353693) B3353693
theorem B5030549 : Blo 2235435 5030549 := bbase (se 6 (by rfl) ⟨117903, by rfl⟩ : syracuseStep 5030549 = 235807) (by norm_num)
theorem B3353699 : Blo 2235435 3353699 := bstep (se 1 (by rfl) ⟨2515274, by rfl⟩ : syracuseStep 3353699 = 5030549) B5030549
theorem B2235799 : Blo 2235435 2235799 := bstep (se 1 (by rfl) ⟨1676849, by rfl⟩ : syracuseStep 2235799 = 3353699) B3353699
theorem B2266309 : Blo 2235435 2266309 := bbase (se 4 (by rfl) ⟨212466, by rfl⟩ : syracuseStep 2266309 = 424933) (by norm_num)
theorem B12086981 : Blo 2235435 12086981 := bstep (se 4 (by rfl) ⟨1133154, by rfl⟩ : syracuseStep 12086981 = 2266309) B2266309
theorem B8057987 : Blo 2235435 8057987 := bstep (se 1 (by rfl) ⟨6043490, by rfl⟩ : syracuseStep 8057987 = 12086981) B12086981
theorem B5371991 : Blo 2235435 5371991 := bstep (se 1 (by rfl) ⟨4028993, by rfl⟩ : syracuseStep 5371991 = 8057987) B8057987
theorem B3581327 : Blo 2235435 3581327 := bstep (se 1 (by rfl) ⟨2685995, by rfl⟩ : syracuseStep 3581327 = 5371991) B5371991
theorem B2387551 : Blo 2235435 2387551 := bstep (se 1 (by rfl) ⟨1790663, by rfl⟩ : syracuseStep 2387551 = 3581327) B3581327
theorem B3183401 : Blo 2235435 3183401 := bstep (se 2 (by rfl) ⟨1193775, by rfl⟩ : syracuseStep 3183401 = 2387551) B2387551
theorem B8489069 : Blo 2235435 8489069 := bstep (se 3 (by rfl) ⟨1591700, by rfl⟩ : syracuseStep 8489069 = 3183401) B3183401
theorem B5659379 : Blo 2235435 5659379 := bstep (se 1 (by rfl) ⟨4244534, by rfl⟩ : syracuseStep 5659379 = 8489069) B8489069
theorem B3772919 : Blo 2235435 3772919 := bstep (se 1 (by rfl) ⟨2829689, by rfl⟩ : syracuseStep 3772919 = 5659379) B5659379
theorem B2515279 : Blo 2235435 2515279 := bstep (se 1 (by rfl) ⟨1886459, by rfl⟩ : syracuseStep 2515279 = 3772919) B3772919
theorem B3353705 : Blo 2235435 3353705 := bstep (se 2 (by rfl) ⟨1257639, by rfl⟩ : syracuseStep 3353705 = 2515279) B2515279
theorem B2235803 : Blo 2235435 2235803 := bstep (se 1 (by rfl) ⟨1676852, by rfl⟩ : syracuseStep 2235803 = 3353705) B3353705
theorem B7648805 : Blo 2235435 7648805 := bbase (se 4 (by rfl) ⟨717075, by rfl⟩ : syracuseStep 7648805 = 1434151) (by norm_num)
theorem B5099203 : Blo 2235435 5099203 := bstep (se 1 (by rfl) ⟨3824402, by rfl⟩ : syracuseStep 5099203 = 7648805) B7648805
theorem B6798937 : Blo 2235435 6798937 := bstep (se 2 (by rfl) ⟨2549601, by rfl⟩ : syracuseStep 6798937 = 5099203) B5099203
theorem B9065249 : Blo 2235435 9065249 := bstep (se 2 (by rfl) ⟨3399468, by rfl⟩ : syracuseStep 9065249 = 6798937) B6798937
theorem B6043499 : Blo 2235435 6043499 := bstep (se 1 (by rfl) ⟨4532624, by rfl⟩ : syracuseStep 6043499 = 9065249) B9065249
theorem B4028999 : Blo 2235435 4028999 := bstep (se 1 (by rfl) ⟨3021749, by rfl⟩ : syracuseStep 4028999 = 6043499) B6043499
theorem B10743997 : Blo 2235435 10743997 := bstep (se 3 (by rfl) ⟨2014499, by rfl⟩ : syracuseStep 10743997 = 4028999) B4028999
theorem B14325329 : Blo 2235435 14325329 := bstep (se 2 (by rfl) ⟨5371998, by rfl⟩ : syracuseStep 14325329 = 10743997) B10743997
theorem B9550219 : Blo 2235435 9550219 := bstep (se 1 (by rfl) ⟨7162664, by rfl⟩ : syracuseStep 9550219 = 14325329) B14325329
theorem B12733625 : Blo 2235435 12733625 := bstep (se 2 (by rfl) ⟨4775109, by rfl⟩ : syracuseStep 12733625 = 9550219) B9550219
theorem B8489083 : Blo 2235435 8489083 := bstep (se 1 (by rfl) ⟨6366812, by rfl⟩ : syracuseStep 8489083 = 12733625) B12733625
theorem B11318777 : Blo 2235435 11318777 := bstep (se 2 (by rfl) ⟨4244541, by rfl⟩ : syracuseStep 11318777 = 8489083) B8489083
theorem B7545851 : Blo 2235435 7545851 := bstep (se 1 (by rfl) ⟨5659388, by rfl⟩ : syracuseStep 7545851 = 11318777) B11318777
theorem B5030567 : Blo 2235435 5030567 := bstep (se 1 (by rfl) ⟨3772925, by rfl⟩ : syracuseStep 5030567 = 7545851) B7545851
theorem B3353711 : Blo 2235435 3353711 := bstep (se 1 (by rfl) ⟨2515283, by rfl⟩ : syracuseStep 3353711 = 5030567) B5030567
theorem B2235807 : Blo 2235435 2235807 := bstep (se 1 (by rfl) ⟨1676855, by rfl⟩ : syracuseStep 2235807 = 3353711) B3353711
theorem B3353717 : Blo 2235435 3353717 := bbase (se 5 (by rfl) ⟨157205, by rfl⟩ : syracuseStep 3353717 = 314411) (by norm_num)
theorem B2235811 : Blo 2235435 2235811 := bstep (se 1 (by rfl) ⟨1676858, by rfl⟩ : syracuseStep 2235811 = 3353717) B3353717
theorem B4244557 : Blo 2235435 4244557 := bbase (se 3 (by rfl) ⟨795854, by rfl⟩ : syracuseStep 4244557 = 1591709) (by norm_num)
theorem B5659409 : Blo 2235435 5659409 := bstep (se 2 (by rfl) ⟨2122278, by rfl⟩ : syracuseStep 5659409 = 4244557) B4244557
theorem B3772939 : Blo 2235435 3772939 := bstep (se 1 (by rfl) ⟨2829704, by rfl⟩ : syracuseStep 3772939 = 5659409) B5659409
theorem B5030585 : Blo 2235435 5030585 := bstep (se 2 (by rfl) ⟨1886469, by rfl⟩ : syracuseStep 5030585 = 3772939) B3772939
theorem B3353723 : Blo 2235435 3353723 := bstep (se 1 (by rfl) ⟨2515292, by rfl⟩ : syracuseStep 3353723 = 5030585) B5030585
theorem B2235815 : Blo 2235435 2235815 := bstep (se 1 (by rfl) ⟨1676861, by rfl⟩ : syracuseStep 2235815 = 3353723) B3353723
theorem B2515297 : Blo 2235435 2515297 := bbase (se 2 (by rfl) ⟨943236, by rfl⟩ : syracuseStep 2515297 = 1886473) (by norm_num)
theorem B3353729 : Blo 2235435 3353729 := bstep (se 2 (by rfl) ⟨1257648, by rfl⟩ : syracuseStep 3353729 = 2515297) B2515297
theorem B2235819 : Blo 2235435 2235819 := bstep (se 1 (by rfl) ⟨1676864, by rfl⟩ : syracuseStep 2235819 = 3353729) B3353729
theorem B5659429 : Blo 2235435 5659429 := bbase (se 4 (by rfl) ⟨530571, by rfl⟩ : syracuseStep 5659429 = 1061143) (by norm_num)
theorem B7545905 : Blo 2235435 7545905 := bstep (se 2 (by rfl) ⟨2829714, by rfl⟩ : syracuseStep 7545905 = 5659429) B5659429
theorem B5030603 : Blo 2235435 5030603 := bstep (se 1 (by rfl) ⟨3772952, by rfl⟩ : syracuseStep 5030603 = 7545905) B7545905
theorem B3353735 : Blo 2235435 3353735 := bstep (se 1 (by rfl) ⟨2515301, by rfl⟩ : syracuseStep 3353735 = 5030603) B5030603
theorem B2235823 : Blo 2235435 2235823 := bstep (se 1 (by rfl) ⟨1676867, by rfl⟩ : syracuseStep 2235823 = 3353735) B3353735
theorem B3353741 : Blo 2235435 3353741 := bbase (se 3 (by rfl) ⟨628826, by rfl⟩ : syracuseStep 3353741 = 1257653) (by norm_num)
theorem B2235827 : Blo 2235435 2235827 := bstep (se 1 (by rfl) ⟨1676870, by rfl⟩ : syracuseStep 2235827 = 3353741) B3353741
theorem B5030621 : Blo 2235435 5030621 := bbase (se 3 (by rfl) ⟨943241, by rfl⟩ : syracuseStep 5030621 = 1886483) (by norm_num)
theorem B3353747 : Blo 2235435 3353747 := bstep (se 1 (by rfl) ⟨2515310, by rfl⟩ : syracuseStep 3353747 = 5030621) B5030621
theorem B2235831 : Blo 2235435 2235831 := bstep (se 1 (by rfl) ⟨1676873, by rfl⟩ : syracuseStep 2235831 = 3353747) B3353747
theorem B3772973 : Blo 2235435 3772973 := bbase (se 3 (by rfl) ⟨707432, by rfl⟩ : syracuseStep 3772973 = 1414865) (by norm_num)
theorem B2515315 : Blo 2235435 2515315 := bstep (se 1 (by rfl) ⟨1886486, by rfl⟩ : syracuseStep 2515315 = 3772973) B3772973
theorem B3353753 : Blo 2235435 3353753 := bstep (se 2 (by rfl) ⟨1257657, by rfl⟩ : syracuseStep 3353753 = 2515315) B2515315
theorem B2235835 : Blo 2235435 2235835 := bstep (se 1 (by rfl) ⟨1676876, by rfl⟩ : syracuseStep 2235835 = 3353753) B3353753
theorem B5736685 : Blo 2235435 5736685 := bbase (se 3 (by rfl) ⟨1075628, by rfl⟩ : syracuseStep 5736685 = 2151257) (by norm_num)
theorem B7648913 : Blo 2235435 7648913 := bstep (se 2 (by rfl) ⟨2868342, by rfl⟩ : syracuseStep 7648913 = 5736685) B5736685
theorem B5099275 : Blo 2235435 5099275 := bstep (se 1 (by rfl) ⟨3824456, by rfl⟩ : syracuseStep 5099275 = 7648913) B7648913
theorem B6799033 : Blo 2235435 6799033 := bstep (se 2 (by rfl) ⟨2549637, by rfl⟩ : syracuseStep 6799033 = 5099275) B5099275
theorem B9065377 : Blo 2235435 9065377 := bstep (se 2 (by rfl) ⟨3399516, by rfl⟩ : syracuseStep 9065377 = 6799033) B6799033
theorem B48348677 : Blo 2235435 48348677 := bstep (se 4 (by rfl) ⟨4532688, by rfl⟩ : syracuseStep 48348677 = 9065377) B9065377
theorem B32232451 : Blo 2235435 32232451 := bstep (se 1 (by rfl) ⟨24174338, by rfl⟩ : syracuseStep 32232451 = 48348677) B48348677
theorem B42976601 : Blo 2235435 42976601 := bstep (se 2 (by rfl) ⟨16116225, by rfl⟩ : syracuseStep 42976601 = 32232451) B32232451
theorem B28651067 : Blo 2235435 28651067 := bstep (se 1 (by rfl) ⟨21488300, by rfl⟩ : syracuseStep 28651067 = 42976601) B42976601
theorem B19100711 : Blo 2235435 19100711 := bstep (se 1 (by rfl) ⟨14325533, by rfl⟩ : syracuseStep 19100711 = 28651067) B28651067
theorem B12733807 : Blo 2235435 12733807 := bstep (se 1 (by rfl) ⟨9550355, by rfl⟩ : syracuseStep 12733807 = 19100711) B19100711
theorem B16978409 : Blo 2235435 16978409 := bstep (se 2 (by rfl) ⟨6366903, by rfl⟩ : syracuseStep 16978409 = 12733807) B12733807
theorem B11318939 : Blo 2235435 11318939 := bstep (se 1 (by rfl) ⟨8489204, by rfl⟩ : syracuseStep 11318939 = 16978409) B16978409
theorem B7545959 : Blo 2235435 7545959 := bstep (se 1 (by rfl) ⟨5659469, by rfl⟩ : syracuseStep 7545959 = 11318939) B11318939
theorem B5030639 : Blo 2235435 5030639 := bstep (se 1 (by rfl) ⟨3772979, by rfl⟩ : syracuseStep 5030639 = 7545959) B7545959
theorem B3353759 : Blo 2235435 3353759 := bstep (se 1 (by rfl) ⟨2515319, by rfl⟩ : syracuseStep 3353759 = 5030639) B5030639
theorem B2235839 : Blo 2235435 2235839 := bstep (se 1 (by rfl) ⟨1676879, by rfl⟩ : syracuseStep 2235839 = 3353759) B3353759
theorem B3353765 : Blo 2235435 3353765 := bbase (se 4 (by rfl) ⟨314415, by rfl⟩ : syracuseStep 3353765 = 628831) (by norm_num)
theorem B2235843 : Blo 2235435 2235843 := bstep (se 1 (by rfl) ⟨1676882, by rfl⟩ : syracuseStep 2235843 = 3353765) B3353765
theorem B2829745 : Blo 2235435 2829745 := bbase (se 2 (by rfl) ⟨1061154, by rfl⟩ : syracuseStep 2829745 = 2122309) (by norm_num)
theorem B3772993 : Blo 2235435 3772993 := bstep (se 2 (by rfl) ⟨1414872, by rfl⟩ : syracuseStep 3772993 = 2829745) B2829745
theorem B5030657 : Blo 2235435 5030657 := bstep (se 2 (by rfl) ⟨1886496, by rfl⟩ : syracuseStep 5030657 = 3772993) B3772993
theorem B3353771 : Blo 2235435 3353771 := bstep (se 1 (by rfl) ⟨2515328, by rfl⟩ : syracuseStep 3353771 = 5030657) B5030657
theorem B2235847 : Blo 2235435 2235847 := bstep (se 1 (by rfl) ⟨1676885, by rfl⟩ : syracuseStep 2235847 = 3353771) B3353771
theorem B2515333 : Blo 2235435 2515333 := bbase (se 4 (by rfl) ⟨235812, by rfl⟩ : syracuseStep 2515333 = 471625) (by norm_num)
theorem B3353777 : Blo 2235435 3353777 := bstep (se 2 (by rfl) ⟨1257666, by rfl⟩ : syracuseStep 3353777 = 2515333) B2515333
theorem B2235851 : Blo 2235435 2235851 := bstep (se 1 (by rfl) ⟨1676888, by rfl⟩ : syracuseStep 2235851 = 3353777) B3353777
theorem B4775213 : Blo 2235435 4775213 := bbase (se 3 (by rfl) ⟨895352, by rfl⟩ : syracuseStep 4775213 = 1790705) (by norm_num)
theorem B3183475 : Blo 2235435 3183475 := bstep (se 1 (by rfl) ⟨2387606, by rfl⟩ : syracuseStep 3183475 = 4775213) B4775213
theorem B4244633 : Blo 2235435 4244633 := bstep (se 2 (by rfl) ⟨1591737, by rfl⟩ : syracuseStep 4244633 = 3183475) B3183475
theorem B2829755 : Blo 2235435 2829755 := bstep (se 1 (by rfl) ⟨2122316, by rfl⟩ : syracuseStep 2829755 = 4244633) B4244633
theorem B7546013 : Blo 2235435 7546013 := bstep (se 3 (by rfl) ⟨1414877, by rfl⟩ : syracuseStep 7546013 = 2829755) B2829755
theorem B5030675 : Blo 2235435 5030675 := bstep (se 1 (by rfl) ⟨3773006, by rfl⟩ : syracuseStep 5030675 = 7546013) B7546013
theorem B3353783 : Blo 2235435 3353783 := bstep (se 1 (by rfl) ⟨2515337, by rfl⟩ : syracuseStep 3353783 = 5030675) B5030675
theorem B2235855 : Blo 2235435 2235855 := bstep (se 1 (by rfl) ⟨1676891, by rfl⟩ : syracuseStep 2235855 = 3353783) B3353783
theorem B3353789 : Blo 2235435 3353789 := bbase (se 3 (by rfl) ⟨628835, by rfl⟩ : syracuseStep 3353789 = 1257671) (by norm_num)
theorem B2235859 : Blo 2235435 2235859 := bstep (se 1 (by rfl) ⟨1676894, by rfl⟩ : syracuseStep 2235859 = 3353789) B3353789
theorem B5030693 : Blo 2235435 5030693 := bbase (se 4 (by rfl) ⟨471627, by rfl⟩ : syracuseStep 5030693 = 943255) (by norm_num)
theorem B3353795 : Blo 2235435 3353795 := bstep (se 1 (by rfl) ⟨2515346, by rfl⟩ : syracuseStep 3353795 = 5030693) B5030693
theorem B2235863 : Blo 2235435 2235863 := bstep (se 1 (by rfl) ⟨1676897, by rfl⟩ : syracuseStep 2235863 = 3353795) B3353795
theorem B5659541 : Blo 2235435 5659541 := bbase (se 6 (by rfl) ⟨132645, by rfl⟩ : syracuseStep 5659541 = 265291) (by norm_num)
theorem B3773027 : Blo 2235435 3773027 := bstep (se 1 (by rfl) ⟨2829770, by rfl⟩ : syracuseStep 3773027 = 5659541) B5659541
theorem B2515351 : Blo 2235435 2515351 := bstep (se 1 (by rfl) ⟨1886513, by rfl⟩ : syracuseStep 2515351 = 3773027) B3773027
theorem B3353801 : Blo 2235435 3353801 := bstep (se 2 (by rfl) ⟨1257675, by rfl⟩ : syracuseStep 3353801 = 2515351) B2515351
theorem B2235867 : Blo 2235435 2235867 := bstep (se 1 (by rfl) ⟨1676900, by rfl⟩ : syracuseStep 2235867 = 3353801) B3353801
theorem B2868385 : Blo 2235435 2868385 := bbase (se 2 (by rfl) ⟨1075644, by rfl⟩ : syracuseStep 2868385 = 2151289) (by norm_num)
theorem B3824513 : Blo 2235435 3824513 := bstep (se 2 (by rfl) ⟨1434192, by rfl⟩ : syracuseStep 3824513 = 2868385) B2868385
theorem B2549675 : Blo 2235435 2549675 := bstep (se 1 (by rfl) ⟨1912256, by rfl⟩ : syracuseStep 2549675 = 3824513) B3824513
theorem B6799133 : Blo 2235435 6799133 := bstep (se 3 (by rfl) ⟨1274837, by rfl⟩ : syracuseStep 6799133 = 2549675) B2549675
theorem B4532755 : Blo 2235435 4532755 := bstep (se 1 (by rfl) ⟨3399566, by rfl⟩ : syracuseStep 4532755 = 6799133) B6799133
theorem B6043673 : Blo 2235435 6043673 := bstep (se 2 (by rfl) ⟨2266377, by rfl⟩ : syracuseStep 6043673 = 4532755) B4532755
theorem B4029115 : Blo 2235435 4029115 := bstep (se 1 (by rfl) ⟨3021836, by rfl⟩ : syracuseStep 4029115 = 6043673) B6043673
theorem B5372153 : Blo 2235435 5372153 := bstep (se 2 (by rfl) ⟨2014557, by rfl⟩ : syracuseStep 5372153 = 4029115) B4029115
theorem B3581435 : Blo 2235435 3581435 := bstep (se 1 (by rfl) ⟨2686076, by rfl⟩ : syracuseStep 3581435 = 5372153) B5372153
theorem B9550493 : Blo 2235435 9550493 := bstep (se 3 (by rfl) ⟨1790717, by rfl⟩ : syracuseStep 9550493 = 3581435) B3581435
theorem B6366995 : Blo 2235435 6366995 := bstep (se 1 (by rfl) ⟨4775246, by rfl⟩ : syracuseStep 6366995 = 9550493) B9550493
theorem B4244663 : Blo 2235435 4244663 := bstep (se 1 (by rfl) ⟨3183497, by rfl⟩ : syracuseStep 4244663 = 6366995) B6366995
theorem B11319101 : Blo 2235435 11319101 := bstep (se 3 (by rfl) ⟨2122331, by rfl⟩ : syracuseStep 11319101 = 4244663) B4244663
theorem B7546067 : Blo 2235435 7546067 := bstep (se 1 (by rfl) ⟨5659550, by rfl⟩ : syracuseStep 7546067 = 11319101) B11319101
theorem B5030711 : Blo 2235435 5030711 := bstep (se 1 (by rfl) ⟨3773033, by rfl⟩ : syracuseStep 5030711 = 7546067) B7546067
theorem B3353807 : Blo 2235435 3353807 := bstep (se 1 (by rfl) ⟨2515355, by rfl⟩ : syracuseStep 3353807 = 5030711) B5030711
theorem B2235871 : Blo 2235435 2235871 := bstep (se 1 (by rfl) ⟨1676903, by rfl⟩ : syracuseStep 2235871 = 3353807) B3353807
theorem B3353813 : Blo 2235435 3353813 := bbase (se 7 (by rfl) ⟨39302, by rfl⟩ : syracuseStep 3353813 = 78605) (by norm_num)
theorem B2235875 : Blo 2235435 2235875 := bstep (se 1 (by rfl) ⟨1676906, by rfl⟩ : syracuseStep 2235875 = 3353813) B3353813
theorem B3183509 : Blo 2235435 3183509 := bbase (se 6 (by rfl) ⟨74613, by rfl⟩ : syracuseStep 3183509 = 149227) (by norm_num)
theorem B8489357 : Blo 2235435 8489357 := bstep (se 3 (by rfl) ⟨1591754, by rfl⟩ : syracuseStep 8489357 = 3183509) B3183509
theorem B5659571 : Blo 2235435 5659571 := bstep (se 1 (by rfl) ⟨4244678, by rfl⟩ : syracuseStep 5659571 = 8489357) B8489357
theorem B3773047 : Blo 2235435 3773047 := bstep (se 1 (by rfl) ⟨2829785, by rfl⟩ : syracuseStep 3773047 = 5659571) B5659571
theorem B5030729 : Blo 2235435 5030729 := bstep (se 2 (by rfl) ⟨1886523, by rfl⟩ : syracuseStep 5030729 = 3773047) B3773047
theorem B3353819 : Blo 2235435 3353819 := bstep (se 1 (by rfl) ⟨2515364, by rfl⟩ : syracuseStep 3353819 = 5030729) B5030729
theorem B2235879 : Blo 2235435 2235879 := bstep (se 1 (by rfl) ⟨1676909, by rfl⟩ : syracuseStep 2235879 = 3353819) B3353819
theorem B2515369 : Blo 2235435 2515369 := bbase (se 2 (by rfl) ⟨943263, by rfl⟩ : syracuseStep 2515369 = 1886527) (by norm_num)
theorem B3353825 : Blo 2235435 3353825 := bstep (se 2 (by rfl) ⟨1257684, by rfl⟩ : syracuseStep 3353825 = 2515369) B2515369
theorem B2235883 : Blo 2235435 2235883 := bstep (se 1 (by rfl) ⟨1676912, by rfl⟩ : syracuseStep 2235883 = 3353825) B3353825
theorem B14521301 : Blo 2235435 14521301 := bbase (se 7 (by rfl) ⟨170171, by rfl⟩ : syracuseStep 14521301 = 340343) (by norm_num)
theorem B9680867 : Blo 2235435 9680867 := bstep (se 1 (by rfl) ⟨7260650, by rfl⟩ : syracuseStep 9680867 = 14521301) B14521301
theorem B6453911 : Blo 2235435 6453911 := bstep (se 1 (by rfl) ⟨4840433, by rfl⟩ : syracuseStep 6453911 = 9680867) B9680867
theorem B4302607 : Blo 2235435 4302607 := bstep (se 1 (by rfl) ⟨3226955, by rfl⟩ : syracuseStep 4302607 = 6453911) B6453911
theorem B5736809 : Blo 2235435 5736809 := bstep (se 2 (by rfl) ⟨2151303, by rfl⟩ : syracuseStep 5736809 = 4302607) B4302607
theorem B3824539 : Blo 2235435 3824539 := bstep (se 1 (by rfl) ⟨2868404, by rfl⟩ : syracuseStep 3824539 = 5736809) B5736809
theorem B20397541 : Blo 2235435 20397541 := bstep (se 4 (by rfl) ⟨1912269, by rfl⟩ : syracuseStep 20397541 = 3824539) B3824539
theorem B27196721 : Blo 2235435 27196721 := bstep (se 2 (by rfl) ⟨10198770, by rfl⟩ : syracuseStep 27196721 = 20397541) B20397541
theorem B18131147 : Blo 2235435 18131147 := bstep (se 1 (by rfl) ⟨13598360, by rfl⟩ : syracuseStep 18131147 = 27196721) B27196721
theorem B12087431 : Blo 2235435 12087431 := bstep (se 1 (by rfl) ⟨9065573, by rfl⟩ : syracuseStep 12087431 = 18131147) B18131147
theorem B8058287 : Blo 2235435 8058287 := bstep (se 1 (by rfl) ⟨6043715, by rfl⟩ : syracuseStep 8058287 = 12087431) B12087431
theorem B5372191 : Blo 2235435 5372191 := bstep (se 1 (by rfl) ⟨4029143, by rfl⟩ : syracuseStep 5372191 = 8058287) B8058287
theorem B7162921 : Blo 2235435 7162921 := bstep (se 2 (by rfl) ⟨2686095, by rfl⟩ : syracuseStep 7162921 = 5372191) B5372191
theorem B9550561 : Blo 2235435 9550561 := bstep (se 2 (by rfl) ⟨3581460, by rfl⟩ : syracuseStep 9550561 = 7162921) B7162921
theorem B12734081 : Blo 2235435 12734081 := bstep (se 2 (by rfl) ⟨4775280, by rfl⟩ : syracuseStep 12734081 = 9550561) B9550561
theorem B8489387 : Blo 2235435 8489387 := bstep (se 1 (by rfl) ⟨6367040, by rfl⟩ : syracuseStep 8489387 = 12734081) B12734081
theorem B5659591 : Blo 2235435 5659591 := bstep (se 1 (by rfl) ⟨4244693, by rfl⟩ : syracuseStep 5659591 = 8489387) B8489387
theorem B7546121 : Blo 2235435 7546121 := bstep (se 2 (by rfl) ⟨2829795, by rfl⟩ : syracuseStep 7546121 = 5659591) B5659591
theorem B5030747 : Blo 2235435 5030747 := bstep (se 1 (by rfl) ⟨3773060, by rfl⟩ : syracuseStep 5030747 = 7546121) B7546121
theorem B3353831 : Blo 2235435 3353831 := bstep (se 1 (by rfl) ⟨2515373, by rfl⟩ : syracuseStep 3353831 = 5030747) B5030747
theorem B2235887 : Blo 2235435 2235887 := bstep (se 1 (by rfl) ⟨1676915, by rfl⟩ : syracuseStep 2235887 = 3353831) B3353831
theorem B3353837 : Blo 2235435 3353837 := bbase (se 3 (by rfl) ⟨628844, by rfl⟩ : syracuseStep 3353837 = 1257689) (by norm_num)
theorem B2235891 : Blo 2235435 2235891 := bstep (se 1 (by rfl) ⟨1676918, by rfl⟩ : syracuseStep 2235891 = 3353837) B3353837
theorem B5030765 : Blo 2235435 5030765 := bbase (se 3 (by rfl) ⟨943268, by rfl⟩ : syracuseStep 5030765 = 1886537) (by norm_num)
theorem B3353843 : Blo 2235435 3353843 := bstep (se 1 (by rfl) ⟨2515382, by rfl⟩ : syracuseStep 3353843 = 5030765) B5030765
theorem B2235895 : Blo 2235435 2235895 := bstep (se 1 (by rfl) ⟨1676921, by rfl⟩ : syracuseStep 2235895 = 3353843) B3353843
theorem B4244717 : Blo 2235435 4244717 := bbase (se 3 (by rfl) ⟨795884, by rfl⟩ : syracuseStep 4244717 = 1591769) (by norm_num)
theorem B2829811 : Blo 2235435 2829811 := bstep (se 1 (by rfl) ⟨2122358, by rfl⟩ : syracuseStep 2829811 = 4244717) B4244717
theorem B3773081 : Blo 2235435 3773081 := bstep (se 2 (by rfl) ⟨1414905, by rfl⟩ : syracuseStep 3773081 = 2829811) B2829811
theorem B2515387 : Blo 2235435 2515387 := bstep (se 1 (by rfl) ⟨1886540, by rfl⟩ : syracuseStep 2515387 = 3773081) B3773081
theorem B3353849 : Blo 2235435 3353849 := bstep (se 2 (by rfl) ⟨1257693, by rfl⟩ : syracuseStep 3353849 = 2515387) B2515387
theorem B2235899 : Blo 2235435 2235899 := bstep (se 1 (by rfl) ⟨1676924, by rfl⟩ : syracuseStep 2235899 = 3353849) B3353849
theorem B9680933 : Blo 2235435 9680933 := bbase (se 4 (by rfl) ⟨907587, by rfl⟩ : syracuseStep 9680933 = 1815175) (by norm_num)
theorem B6453955 : Blo 2235435 6453955 := bstep (se 1 (by rfl) ⟨4840466, by rfl⟩ : syracuseStep 6453955 = 9680933) B9680933
theorem B8605273 : Blo 2235435 8605273 := bstep (se 2 (by rfl) ⟨3226977, by rfl⟩ : syracuseStep 8605273 = 6453955) B6453955
theorem B11473697 : Blo 2235435 11473697 := bstep (se 2 (by rfl) ⟨4302636, by rfl⟩ : syracuseStep 11473697 = 8605273) B8605273
theorem B30596525 : Blo 2235435 30596525 := bstep (se 3 (by rfl) ⟨5736848, by rfl⟩ : syracuseStep 30596525 = 11473697) B11473697
theorem B20397683 : Blo 2235435 20397683 := bstep (se 1 (by rfl) ⟨15298262, by rfl⟩ : syracuseStep 20397683 = 30596525) B30596525
theorem B13598455 : Blo 2235435 13598455 := bstep (se 1 (by rfl) ⟨10198841, by rfl⟩ : syracuseStep 13598455 = 20397683) B20397683
theorem B18131273 : Blo 2235435 18131273 := bstep (se 2 (by rfl) ⟨6799227, by rfl⟩ : syracuseStep 18131273 = 13598455) B13598455
theorem B12087515 : Blo 2235435 12087515 := bstep (se 1 (by rfl) ⟨9065636, by rfl⟩ : syracuseStep 12087515 = 18131273) B18131273
theorem B32233373 : Blo 2235435 32233373 := bstep (se 3 (by rfl) ⟨6043757, by rfl⟩ : syracuseStep 32233373 = 12087515) B12087515
theorem B21488915 : Blo 2235435 21488915 := bstep (se 1 (by rfl) ⟨16116686, by rfl⟩ : syracuseStep 21488915 = 32233373) B32233373
theorem B57303773 : Blo 2235435 57303773 := bstep (se 3 (by rfl) ⟨10744457, by rfl⟩ : syracuseStep 57303773 = 21488915) B21488915
theorem B38202515 : Blo 2235435 38202515 := bstep (se 1 (by rfl) ⟨28651886, by rfl⟩ : syracuseStep 38202515 = 57303773) B57303773
theorem B25468343 : Blo 2235435 25468343 := bstep (se 1 (by rfl) ⟨19101257, by rfl⟩ : syracuseStep 25468343 = 38202515) B38202515
theorem B16978895 : Blo 2235435 16978895 := bstep (se 1 (by rfl) ⟨12734171, by rfl⟩ : syracuseStep 16978895 = 25468343) B25468343
theorem B11319263 : Blo 2235435 11319263 := bstep (se 1 (by rfl) ⟨8489447, by rfl⟩ : syracuseStep 11319263 = 16978895) B16978895
theorem B7546175 : Blo 2235435 7546175 := bstep (se 1 (by rfl) ⟨5659631, by rfl⟩ : syracuseStep 7546175 = 11319263) B11319263
theorem B5030783 : Blo 2235435 5030783 := bstep (se 1 (by rfl) ⟨3773087, by rfl⟩ : syracuseStep 5030783 = 7546175) B7546175
theorem B3353855 : Blo 2235435 3353855 := bstep (se 1 (by rfl) ⟨2515391, by rfl⟩ : syracuseStep 3353855 = 5030783) B5030783
theorem B2235903 : Blo 2235435 2235903 := bstep (se 1 (by rfl) ⟨1676927, by rfl⟩ : syracuseStep 2235903 = 3353855) B3353855
theorem B3353861 : Blo 2235435 3353861 := bbase (se 4 (by rfl) ⟨314424, by rfl⟩ : syracuseStep 3353861 = 628849) (by norm_num)
theorem B2235907 : Blo 2235435 2235907 := bstep (se 1 (by rfl) ⟨1676930, by rfl⟩ : syracuseStep 2235907 = 3353861) B3353861
theorem B3773101 : Blo 2235435 3773101 := bbase (se 3 (by rfl) ⟨707456, by rfl⟩ : syracuseStep 3773101 = 1414913) (by norm_num)
theorem B5030801 : Blo 2235435 5030801 := bstep (se 2 (by rfl) ⟨1886550, by rfl⟩ : syracuseStep 5030801 = 3773101) B3773101
theorem B3353867 : Blo 2235435 3353867 := bstep (se 1 (by rfl) ⟨2515400, by rfl⟩ : syracuseStep 3353867 = 5030801) B5030801
theorem B2235911 : Blo 2235435 2235911 := bstep (se 1 (by rfl) ⟨1676933, by rfl⟩ : syracuseStep 2235911 = 3353867) B3353867
theorem B2515405 : Blo 2235435 2515405 := bbase (se 3 (by rfl) ⟨471638, by rfl⟩ : syracuseStep 2515405 = 943277) (by norm_num)
theorem B3353873 : Blo 2235435 3353873 := bstep (se 2 (by rfl) ⟨1257702, by rfl⟩ : syracuseStep 3353873 = 2515405) B2515405
theorem B2235915 : Blo 2235435 2235915 := bstep (se 1 (by rfl) ⟨1676936, by rfl⟩ : syracuseStep 2235915 = 3353873) B3353873
theorem B7546229 : Blo 2235435 7546229 := bbase (se 5 (by rfl) ⟨353729, by rfl⟩ : syracuseStep 7546229 = 707459) (by norm_num)
theorem B5030819 : Blo 2235435 5030819 := bstep (se 1 (by rfl) ⟨3773114, by rfl⟩ : syracuseStep 5030819 = 7546229) B7546229
theorem B3353879 : Blo 2235435 3353879 := bstep (se 1 (by rfl) ⟨2515409, by rfl⟩ : syracuseStep 3353879 = 5030819) B5030819
theorem B2235919 : Blo 2235435 2235919 := bstep (se 1 (by rfl) ⟨1676939, by rfl⟩ : syracuseStep 2235919 = 3353879) B3353879
theorem B3353885 : Blo 2235435 3353885 := bbase (se 3 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 3353885 = 1257707) (by norm_num)
theorem B2235923 : Blo 2235435 2235923 := bstep (se 1 (by rfl) ⟨1676942, by rfl⟩ : syracuseStep 2235923 = 3353885) B3353885
theorem B5030837 : Blo 2235435 5030837 := bbase (se 5 (by rfl) ⟨235820, by rfl⟩ : syracuseStep 5030837 = 471641) (by norm_num)
theorem B3353891 : Blo 2235435 3353891 := bstep (se 1 (by rfl) ⟨2515418, by rfl⟩ : syracuseStep 3353891 = 5030837) B5030837
theorem B2235927 : Blo 2235435 2235927 := bstep (se 1 (by rfl) ⟨1676945, by rfl⟩ : syracuseStep 2235927 = 3353891) B3353891
theorem B14521589 : Blo 2235435 14521589 := bbase (se 5 (by rfl) ⟨680699, by rfl⟩ : syracuseStep 14521589 = 1361399) (by norm_num)
theorem B9681059 : Blo 2235435 9681059 := bstep (se 1 (by rfl) ⟨7260794, by rfl⟩ : syracuseStep 9681059 = 14521589) B14521589
theorem B6454039 : Blo 2235435 6454039 := bstep (se 1 (by rfl) ⟨4840529, by rfl⟩ : syracuseStep 6454039 = 9681059) B9681059
theorem B8605385 : Blo 2235435 8605385 := bstep (se 2 (by rfl) ⟨3227019, by rfl⟩ : syracuseStep 8605385 = 6454039) B6454039
theorem B5736923 : Blo 2235435 5736923 := bstep (se 1 (by rfl) ⟨4302692, by rfl⟩ : syracuseStep 5736923 = 8605385) B8605385
theorem B3824615 : Blo 2235435 3824615 := bstep (se 1 (by rfl) ⟨2868461, by rfl⟩ : syracuseStep 3824615 = 5736923) B5736923
theorem B10198973 : Blo 2235435 10198973 := bstep (se 3 (by rfl) ⟨1912307, by rfl⟩ : syracuseStep 10198973 = 3824615) B3824615
theorem B6799315 : Blo 2235435 6799315 := bstep (se 1 (by rfl) ⟨5099486, by rfl⟩ : syracuseStep 6799315 = 10198973) B10198973
theorem B9065753 : Blo 2235435 9065753 := bstep (se 2 (by rfl) ⟨3399657, by rfl⟩ : syracuseStep 9065753 = 6799315) B6799315
theorem B6043835 : Blo 2235435 6043835 := bstep (se 1 (by rfl) ⟨4532876, by rfl⟩ : syracuseStep 6043835 = 9065753) B9065753
theorem B16116893 : Blo 2235435 16116893 := bstep (se 3 (by rfl) ⟨3021917, by rfl⟩ : syracuseStep 16116893 = 6043835) B6043835
theorem B10744595 : Blo 2235435 10744595 := bstep (se 1 (by rfl) ⟨8058446, by rfl⟩ : syracuseStep 10744595 = 16116893) B16116893
theorem B7163063 : Blo 2235435 7163063 := bstep (se 1 (by rfl) ⟨5372297, by rfl⟩ : syracuseStep 7163063 = 10744595) B10744595
theorem B4775375 : Blo 2235435 4775375 := bstep (se 1 (by rfl) ⟨3581531, by rfl⟩ : syracuseStep 4775375 = 7163063) B7163063
theorem B12734333 : Blo 2235435 12734333 := bstep (se 3 (by rfl) ⟨2387687, by rfl⟩ : syracuseStep 12734333 = 4775375) B4775375
theorem B8489555 : Blo 2235435 8489555 := bstep (se 1 (by rfl) ⟨6367166, by rfl⟩ : syracuseStep 8489555 = 12734333) B12734333
theorem B5659703 : Blo 2235435 5659703 := bstep (se 1 (by rfl) ⟨4244777, by rfl⟩ : syracuseStep 5659703 = 8489555) B8489555
theorem B3773135 : Blo 2235435 3773135 := bstep (se 1 (by rfl) ⟨2829851, by rfl⟩ : syracuseStep 3773135 = 5659703) B5659703
theorem B2515423 : Blo 2235435 2515423 := bstep (se 1 (by rfl) ⟨1886567, by rfl⟩ : syracuseStep 2515423 = 3773135) B3773135
theorem B3353897 : Blo 2235435 3353897 := bstep (se 2 (by rfl) ⟨1257711, by rfl⟩ : syracuseStep 3353897 = 2515423) B2515423
theorem B2235931 : Blo 2235435 2235931 := bstep (se 1 (by rfl) ⟨1676948, by rfl⟩ : syracuseStep 2235931 = 3353897) B3353897
theorem B10744613 : Blo 2235435 10744613 := bbase (se 4 (by rfl) ⟨1007307, by rfl⟩ : syracuseStep 10744613 = 2014615) (by norm_num)
theorem B7163075 : Blo 2235435 7163075 := bstep (se 1 (by rfl) ⟨5372306, by rfl⟩ : syracuseStep 7163075 = 10744613) B10744613
theorem B4775383 : Blo 2235435 4775383 := bstep (se 1 (by rfl) ⟨3581537, by rfl⟩ : syracuseStep 4775383 = 7163075) B7163075
theorem B6367177 : Blo 2235435 6367177 := bstep (se 2 (by rfl) ⟨2387691, by rfl⟩ : syracuseStep 6367177 = 4775383) B4775383
theorem B8489569 : Blo 2235435 8489569 := bstep (se 2 (by rfl) ⟨3183588, by rfl⟩ : syracuseStep 8489569 = 6367177) B6367177
theorem B11319425 : Blo 2235435 11319425 := bstep (se 2 (by rfl) ⟨4244784, by rfl⟩ : syracuseStep 11319425 = 8489569) B8489569
theorem B7546283 : Blo 2235435 7546283 := bstep (se 1 (by rfl) ⟨5659712, by rfl⟩ : syracuseStep 7546283 = 11319425) B11319425
theorem B5030855 : Blo 2235435 5030855 := bstep (se 1 (by rfl) ⟨3773141, by rfl⟩ : syracuseStep 5030855 = 7546283) B7546283
theorem B3353903 : Blo 2235435 3353903 := bstep (se 1 (by rfl) ⟨2515427, by rfl⟩ : syracuseStep 3353903 = 5030855) B5030855
theorem B2235935 : Blo 2235435 2235935 := bstep (se 1 (by rfl) ⟨1676951, by rfl⟩ : syracuseStep 2235935 = 3353903) B3353903
theorem B3353909 : Blo 2235435 3353909 := bbase (se 5 (by rfl) ⟨157214, by rfl⟩ : syracuseStep 3353909 = 314429) (by norm_num)
theorem B2235939 : Blo 2235435 2235939 := bstep (se 1 (by rfl) ⟨1676954, by rfl⟩ : syracuseStep 2235939 = 3353909) B3353909
theorem B5659733 : Blo 2235435 5659733 := bbase (se 8 (by rfl) ⟨33162, by rfl⟩ : syracuseStep 5659733 = 66325) (by norm_num)
theorem B3773155 : Blo 2235435 3773155 := bstep (se 1 (by rfl) ⟨2829866, by rfl⟩ : syracuseStep 3773155 = 5659733) B5659733
theorem B5030873 : Blo 2235435 5030873 := bstep (se 2 (by rfl) ⟨1886577, by rfl⟩ : syracuseStep 5030873 = 3773155) B3773155
theorem B3353915 : Blo 2235435 3353915 := bstep (se 1 (by rfl) ⟨2515436, by rfl⟩ : syracuseStep 3353915 = 5030873) B5030873
theorem B2235943 : Blo 2235435 2235943 := bstep (se 1 (by rfl) ⟨1676957, by rfl⟩ : syracuseStep 2235943 = 3353915) B3353915
theorem B2515441 : Blo 2235435 2515441 := bbase (se 2 (by rfl) ⟨943290, by rfl⟩ : syracuseStep 2515441 = 1886581) (by norm_num)
theorem B3353921 : Blo 2235435 3353921 := bstep (se 2 (by rfl) ⟨1257720, by rfl⟩ : syracuseStep 3353921 = 2515441) B2515441
theorem B2235947 : Blo 2235435 2235947 := bstep (se 1 (by rfl) ⟨1676960, by rfl⟩ : syracuseStep 2235947 = 3353921) B3353921
theorem B4532917 : Blo 2235435 4532917 := bbase (se 5 (by rfl) ⟨212480, by rfl⟩ : syracuseStep 4532917 = 424961) (by norm_num)
theorem B6043889 : Blo 2235435 6043889 := bstep (se 2 (by rfl) ⟨2266458, by rfl⟩ : syracuseStep 6043889 = 4532917) B4532917
theorem B4029259 : Blo 2235435 4029259 := bstep (se 1 (by rfl) ⟨3021944, by rfl⟩ : syracuseStep 4029259 = 6043889) B6043889
theorem B5372345 : Blo 2235435 5372345 := bstep (se 2 (by rfl) ⟨2014629, by rfl⟩ : syracuseStep 5372345 = 4029259) B4029259
theorem B14326253 : Blo 2235435 14326253 := bstep (se 3 (by rfl) ⟨2686172, by rfl⟩ : syracuseStep 14326253 = 5372345) B5372345
theorem B9550835 : Blo 2235435 9550835 := bstep (se 1 (by rfl) ⟨7163126, by rfl⟩ : syracuseStep 9550835 = 14326253) B14326253
theorem B6367223 : Blo 2235435 6367223 := bstep (se 1 (by rfl) ⟨4775417, by rfl⟩ : syracuseStep 6367223 = 9550835) B9550835
theorem B4244815 : Blo 2235435 4244815 := bstep (se 1 (by rfl) ⟨3183611, by rfl⟩ : syracuseStep 4244815 = 6367223) B6367223
theorem B5659753 : Blo 2235435 5659753 := bstep (se 2 (by rfl) ⟨2122407, by rfl⟩ : syracuseStep 5659753 = 4244815) B4244815
theorem B7546337 : Blo 2235435 7546337 := bstep (se 2 (by rfl) ⟨2829876, by rfl⟩ : syracuseStep 7546337 = 5659753) B5659753
theorem B5030891 : Blo 2235435 5030891 := bstep (se 1 (by rfl) ⟨3773168, by rfl⟩ : syracuseStep 5030891 = 7546337) B7546337
theorem B3353927 : Blo 2235435 3353927 := bstep (se 1 (by rfl) ⟨2515445, by rfl⟩ : syracuseStep 3353927 = 5030891) B5030891
theorem B2235951 : Blo 2235435 2235951 := bstep (se 1 (by rfl) ⟨1676963, by rfl⟩ : syracuseStep 2235951 = 3353927) B3353927
theorem B3353933 : Blo 2235435 3353933 := bbase (se 3 (by rfl) ⟨628862, by rfl⟩ : syracuseStep 3353933 = 1257725) (by norm_num)
theorem B2235955 : Blo 2235435 2235955 := bstep (se 1 (by rfl) ⟨1676966, by rfl⟩ : syracuseStep 2235955 = 3353933) B3353933
theorem B5030909 : Blo 2235435 5030909 := bbase (se 3 (by rfl) ⟨943295, by rfl⟩ : syracuseStep 5030909 = 1886591) (by norm_num)
theorem B3353939 : Blo 2235435 3353939 := bstep (se 1 (by rfl) ⟨2515454, by rfl⟩ : syracuseStep 3353939 = 5030909) B5030909
theorem B2235959 : Blo 2235435 2235959 := bstep (se 1 (by rfl) ⟨1676969, by rfl⟩ : syracuseStep 2235959 = 3353939) B3353939
theorem B3773189 : Blo 2235435 3773189 := bbase (se 4 (by rfl) ⟨353736, by rfl⟩ : syracuseStep 3773189 = 707473) (by norm_num)
theorem B2515459 : Blo 2235435 2515459 := bstep (se 1 (by rfl) ⟨1886594, by rfl⟩ : syracuseStep 2515459 = 3773189) B3773189
theorem B3353945 : Blo 2235435 3353945 := bstep (se 2 (by rfl) ⟨1257729, by rfl⟩ : syracuseStep 3353945 = 2515459) B2515459
theorem B2235963 : Blo 2235435 2235963 := bstep (se 1 (by rfl) ⟨1676972, by rfl⟩ : syracuseStep 2235963 = 3353945) B3353945
theorem B16979381 : Blo 2235435 16979381 := bbase (se 5 (by rfl) ⟨795908, by rfl⟩ : syracuseStep 16979381 = 1591817) (by norm_num)
theorem B11319587 : Blo 2235435 11319587 := bstep (se 1 (by rfl) ⟨8489690, by rfl⟩ : syracuseStep 11319587 = 16979381) B16979381
theorem B7546391 : Blo 2235435 7546391 := bstep (se 1 (by rfl) ⟨5659793, by rfl⟩ : syracuseStep 7546391 = 11319587) B11319587
theorem B5030927 : Blo 2235435 5030927 := bstep (se 1 (by rfl) ⟨3773195, by rfl⟩ : syracuseStep 5030927 = 7546391) B7546391
theorem B3353951 : Blo 2235435 3353951 := bstep (se 1 (by rfl) ⟨2515463, by rfl⟩ : syracuseStep 3353951 = 5030927) B5030927
theorem B2235967 : Blo 2235435 2235967 := bstep (se 1 (by rfl) ⟨1676975, by rfl⟩ : syracuseStep 2235967 = 3353951) B3353951
theorem B3353957 : Blo 2235435 3353957 := bbase (se 4 (by rfl) ⟨314433, by rfl⟩ : syracuseStep 3353957 = 628867) (by norm_num)
theorem B2235971 : Blo 2235435 2235971 := bstep (se 1 (by rfl) ⟨1676978, by rfl⟩ : syracuseStep 2235971 = 3353957) B3353957
theorem B4244861 : Blo 2235435 4244861 := bbase (se 3 (by rfl) ⟨795911, by rfl⟩ : syracuseStep 4244861 = 1591823) (by norm_num)
theorem B2829907 : Blo 2235435 2829907 := bstep (se 1 (by rfl) ⟨2122430, by rfl⟩ : syracuseStep 2829907 = 4244861) B4244861
theorem B3773209 : Blo 2235435 3773209 := bstep (se 2 (by rfl) ⟨1414953, by rfl⟩ : syracuseStep 3773209 = 2829907) B2829907
theorem B5030945 : Blo 2235435 5030945 := bstep (se 2 (by rfl) ⟨1886604, by rfl⟩ : syracuseStep 5030945 = 3773209) B3773209
theorem B3353963 : Blo 2235435 3353963 := bstep (se 1 (by rfl) ⟨2515472, by rfl⟩ : syracuseStep 3353963 = 5030945) B5030945
theorem B2235975 : Blo 2235435 2235975 := bstep (se 1 (by rfl) ⟨1676981, by rfl⟩ : syracuseStep 2235975 = 3353963) B3353963
theorem B2515477 : Blo 2235435 2515477 := bbase (se 6 (by rfl) ⟨58956, by rfl⟩ : syracuseStep 2515477 = 117913) (by norm_num)
theorem B3353969 : Blo 2235435 3353969 := bstep (se 2 (by rfl) ⟨1257738, by rfl⟩ : syracuseStep 3353969 = 2515477) B2515477
theorem B2235979 : Blo 2235435 2235979 := bstep (se 1 (by rfl) ⟨1676984, by rfl⟩ : syracuseStep 2235979 = 3353969) B3353969
theorem B2829917 : Blo 2235435 2829917 := bbase (se 3 (by rfl) ⟨530609, by rfl⟩ : syracuseStep 2829917 = 1061219) (by norm_num)
theorem B7546445 : Blo 2235435 7546445 := bstep (se 3 (by rfl) ⟨1414958, by rfl⟩ : syracuseStep 7546445 = 2829917) B2829917
theorem B5030963 : Blo 2235435 5030963 := bstep (se 1 (by rfl) ⟨3773222, by rfl⟩ : syracuseStep 5030963 = 7546445) B7546445
theorem B3353975 : Blo 2235435 3353975 := bstep (se 1 (by rfl) ⟨2515481, by rfl⟩ : syracuseStep 3353975 = 5030963) B5030963
theorem B2235983 : Blo 2235435 2235983 := bstep (se 1 (by rfl) ⟨1676987, by rfl⟩ : syracuseStep 2235983 = 3353975) B3353975
theorem B3353981 : Blo 2235435 3353981 := bbase (se 3 (by rfl) ⟨628871, by rfl⟩ : syracuseStep 3353981 = 1257743) (by norm_num)
theorem B2235987 : Blo 2235435 2235987 := bstep (se 1 (by rfl) ⟨1676990, by rfl⟩ : syracuseStep 2235987 = 3353981) B3353981
theorem B5030981 : Blo 2235435 5030981 := bbase (se 4 (by rfl) ⟨471654, by rfl⟩ : syracuseStep 5030981 = 943309) (by norm_num)
theorem B3353987 : Blo 2235435 3353987 := bstep (se 1 (by rfl) ⟨2515490, by rfl⟩ : syracuseStep 3353987 = 5030981) B5030981
theorem B2235991 : Blo 2235435 2235991 := bstep (se 1 (by rfl) ⟨1676993, by rfl⟩ : syracuseStep 2235991 = 3353987) B3353987
theorem B6367349 : Blo 2235435 6367349 := bbase (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) (by norm_num)
theorem B4244899 : Blo 2235435 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B5659865 : Blo 2235435 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B3773243 : Blo 2235435 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B2515495 : Blo 2235435 2515495 := bstep (se 1 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 2515495 = 3773243) B3773243
theorem B3353993 : Blo 2235435 3353993 := bstep (se 2 (by rfl) ⟨1257747, by rfl⟩ : syracuseStep 3353993 = 2515495) B2515495
theorem B2235995 : Blo 2235435 2235995 := bstep (se 1 (by rfl) ⟨1676996, by rfl⟩ : syracuseStep 2235995 = 3353993) B3353993
theorem B11319749 : Blo 2235435 11319749 := bbase (se 4 (by rfl) ⟨1061226, by rfl⟩ : syracuseStep 11319749 = 2122453) (by norm_num)
theorem B7546499 : Blo 2235435 7546499 := bstep (se 1 (by rfl) ⟨5659874, by rfl⟩ : syracuseStep 7546499 = 11319749) B11319749
theorem B5030999 : Blo 2235435 5030999 := bstep (se 1 (by rfl) ⟨3773249, by rfl⟩ : syracuseStep 5030999 = 7546499) B7546499
theorem B3353999 : Blo 2235435 3353999 := bstep (se 1 (by rfl) ⟨2515499, by rfl⟩ : syracuseStep 3353999 = 5030999) B5030999
theorem B2235999 : Blo 2235435 2235999 := bstep (se 1 (by rfl) ⟨1676999, by rfl⟩ : syracuseStep 2235999 = 3353999) B3353999
theorem B3354005 : Blo 2235435 3354005 := bbase (se 6 (by rfl) ⟨78609, by rfl⟩ : syracuseStep 3354005 = 157219) (by norm_num)
theorem B2236003 : Blo 2235435 2236003 := bstep (se 1 (by rfl) ⟨1677002, by rfl⟩ : syracuseStep 2236003 = 3354005) B3354005
theorem B3581653 : Blo 2235435 3581653 := bbase (se 7 (by rfl) ⟨41972, by rfl⟩ : syracuseStep 3581653 = 83945) (by norm_num)
theorem B4775537 : Blo 2235435 4775537 := bstep (se 2 (by rfl) ⟨1790826, by rfl⟩ : syracuseStep 4775537 = 3581653) B3581653
theorem B12734765 : Blo 2235435 12734765 := bstep (se 3 (by rfl) ⟨2387768, by rfl⟩ : syracuseStep 12734765 = 4775537) B4775537
theorem B8489843 : Blo 2235435 8489843 := bstep (se 1 (by rfl) ⟨6367382, by rfl⟩ : syracuseStep 8489843 = 12734765) B12734765
theorem B5659895 : Blo 2235435 5659895 := bstep (se 1 (by rfl) ⟨4244921, by rfl⟩ : syracuseStep 5659895 = 8489843) B8489843
theorem B3773263 : Blo 2235435 3773263 := bstep (se 1 (by rfl) ⟨2829947, by rfl⟩ : syracuseStep 3773263 = 5659895) B5659895
theorem B5031017 : Blo 2235435 5031017 := bstep (se 2 (by rfl) ⟨1886631, by rfl⟩ : syracuseStep 5031017 = 3773263) B3773263
theorem B3354011 : Blo 2235435 3354011 := bstep (se 1 (by rfl) ⟨2515508, by rfl⟩ : syracuseStep 3354011 = 5031017) B5031017
theorem B2236007 : Blo 2235435 2236007 := bstep (se 1 (by rfl) ⟨1677005, by rfl⟩ : syracuseStep 2236007 = 3354011) B3354011
theorem B2515513 : Blo 2235435 2515513 := bbase (se 2 (by rfl) ⟨943317, by rfl⟩ : syracuseStep 2515513 = 1886635) (by norm_num)
theorem B3354017 : Blo 2235435 3354017 := bstep (se 2 (by rfl) ⟨1257756, by rfl⟩ : syracuseStep 3354017 = 2515513) B2515513
theorem B2236011 : Blo 2235435 2236011 := bstep (se 1 (by rfl) ⟨1677008, by rfl⟩ : syracuseStep 2236011 = 3354017) B3354017
theorem B2387777 : Blo 2235435 2387777 := bbase (se 2 (by rfl) ⟨895416, by rfl⟩ : syracuseStep 2387777 = 1790833) (by norm_num)
theorem B6367405 : Blo 2235435 6367405 := bstep (se 3 (by rfl) ⟨1193888, by rfl⟩ : syracuseStep 6367405 = 2387777) B2387777
theorem B8489873 : Blo 2235435 8489873 := bstep (se 2 (by rfl) ⟨3183702, by rfl⟩ : syracuseStep 8489873 = 6367405) B6367405
theorem B5659915 : Blo 2235435 5659915 := bstep (se 1 (by rfl) ⟨4244936, by rfl⟩ : syracuseStep 5659915 = 8489873) B8489873
theorem B7546553 : Blo 2235435 7546553 := bstep (se 2 (by rfl) ⟨2829957, by rfl⟩ : syracuseStep 7546553 = 5659915) B5659915
theorem B5031035 : Blo 2235435 5031035 := bstep (se 1 (by rfl) ⟨3773276, by rfl⟩ : syracuseStep 5031035 = 7546553) B7546553
theorem B3354023 : Blo 2235435 3354023 := bstep (se 1 (by rfl) ⟨2515517, by rfl⟩ : syracuseStep 3354023 = 5031035) B5031035
theorem B2236015 : Blo 2235435 2236015 := bstep (se 1 (by rfl) ⟨1677011, by rfl⟩ : syracuseStep 2236015 = 3354023) B3354023
theorem B3354029 : Blo 2235435 3354029 := bbase (se 3 (by rfl) ⟨628880, by rfl⟩ : syracuseStep 3354029 = 1257761) (by norm_num)
theorem B2236019 : Blo 2235435 2236019 := bstep (se 1 (by rfl) ⟨1677014, by rfl⟩ : syracuseStep 2236019 = 3354029) B3354029
theorem B5031053 : Blo 2235435 5031053 := bbase (se 3 (by rfl) ⟨943322, by rfl⟩ : syracuseStep 5031053 = 1886645) (by norm_num)
theorem B3354035 : Blo 2235435 3354035 := bstep (se 1 (by rfl) ⟨2515526, by rfl⟩ : syracuseStep 3354035 = 5031053) B5031053
theorem B2236023 : Blo 2235435 2236023 := bstep (se 1 (by rfl) ⟨1677017, by rfl⟩ : syracuseStep 2236023 = 3354035) B3354035
theorem B2829973 : Blo 2235435 2829973 := bbase (se 6 (by rfl) ⟨66327, by rfl⟩ : syracuseStep 2829973 = 132655) (by norm_num)
theorem B3773297 : Blo 2235435 3773297 := bstep (se 2 (by rfl) ⟨1414986, by rfl⟩ : syracuseStep 3773297 = 2829973) B2829973
theorem B2515531 : Blo 2235435 2515531 := bstep (se 1 (by rfl) ⟨1886648, by rfl⟩ : syracuseStep 2515531 = 3773297) B3773297
theorem B3354041 : Blo 2235435 3354041 := bstep (se 2 (by rfl) ⟨1257765, by rfl⟩ : syracuseStep 3354041 = 2515531) B2515531
theorem B2236027 : Blo 2235435 2236027 := bstep (se 1 (by rfl) ⟨1677020, by rfl⟩ : syracuseStep 2236027 = 3354041) B3354041
theorem B6454325 : Blo 2235435 6454325 := bbase (se 5 (by rfl) ⟨302546, by rfl⟩ : syracuseStep 6454325 = 605093) (by norm_num)
theorem B4302883 : Blo 2235435 4302883 := bstep (se 1 (by rfl) ⟨3227162, by rfl⟩ : syracuseStep 4302883 = 6454325) B6454325
theorem B5737177 : Blo 2235435 5737177 := bstep (se 2 (by rfl) ⟨2151441, by rfl⟩ : syracuseStep 5737177 = 4302883) B4302883
theorem B7649569 : Blo 2235435 7649569 := bstep (se 2 (by rfl) ⟨2868588, by rfl⟩ : syracuseStep 7649569 = 5737177) B5737177
theorem B40797701 : Blo 2235435 40797701 := bstep (se 4 (by rfl) ⟨3824784, by rfl⟩ : syracuseStep 40797701 = 7649569) B7649569
theorem B27198467 : Blo 2235435 27198467 := bstep (se 1 (by rfl) ⟨20398850, by rfl⟩ : syracuseStep 27198467 = 40797701) B40797701
theorem B18132311 : Blo 2235435 18132311 := bstep (se 1 (by rfl) ⟨13599233, by rfl⟩ : syracuseStep 18132311 = 27198467) B27198467
theorem B12088207 : Blo 2235435 12088207 := bstep (se 1 (by rfl) ⟨9066155, by rfl⟩ : syracuseStep 12088207 = 18132311) B18132311
theorem B64470437 : Blo 2235435 64470437 := bstep (se 4 (by rfl) ⟨6044103, by rfl⟩ : syracuseStep 64470437 = 12088207) B12088207
theorem B42980291 : Blo 2235435 42980291 := bstep (se 1 (by rfl) ⟨32235218, by rfl⟩ : syracuseStep 42980291 = 64470437) B64470437
theorem B28653527 : Blo 2235435 28653527 := bstep (se 1 (by rfl) ⟨21490145, by rfl⟩ : syracuseStep 28653527 = 42980291) B42980291
theorem B19102351 : Blo 2235435 19102351 := bstep (se 1 (by rfl) ⟨14326763, by rfl⟩ : syracuseStep 19102351 = 28653527) B28653527
theorem B25469801 : Blo 2235435 25469801 := bstep (se 2 (by rfl) ⟨9551175, by rfl⟩ : syracuseStep 25469801 = 19102351) B19102351
theorem B16979867 : Blo 2235435 16979867 := bstep (se 1 (by rfl) ⟨12734900, by rfl⟩ : syracuseStep 16979867 = 25469801) B25469801
theorem B11319911 : Blo 2235435 11319911 := bstep (se 1 (by rfl) ⟨8489933, by rfl⟩ : syracuseStep 11319911 = 16979867) B16979867
theorem B7546607 : Blo 2235435 7546607 := bstep (se 1 (by rfl) ⟨5659955, by rfl⟩ : syracuseStep 7546607 = 11319911) B11319911
theorem B5031071 : Blo 2235435 5031071 := bstep (se 1 (by rfl) ⟨3773303, by rfl⟩ : syracuseStep 5031071 = 7546607) B7546607
theorem B3354047 : Blo 2235435 3354047 := bstep (se 1 (by rfl) ⟨2515535, by rfl⟩ : syracuseStep 3354047 = 5031071) B5031071
theorem B2236031 : Blo 2235435 2236031 := bstep (se 1 (by rfl) ⟨1677023, by rfl⟩ : syracuseStep 2236031 = 3354047) B3354047
theorem B3354053 : Blo 2235435 3354053 := bbase (se 4 (by rfl) ⟨314442, by rfl⟩ : syracuseStep 3354053 = 628885) (by norm_num)
theorem B2236035 : Blo 2235435 2236035 := bstep (se 1 (by rfl) ⟨1677026, by rfl⟩ : syracuseStep 2236035 = 3354053) B3354053
theorem B3773317 : Blo 2235435 3773317 := bbase (se 4 (by rfl) ⟨353748, by rfl⟩ : syracuseStep 3773317 = 707497) (by norm_num)
theorem B5031089 : Blo 2235435 5031089 := bstep (se 2 (by rfl) ⟨1886658, by rfl⟩ : syracuseStep 5031089 = 3773317) B3773317
theorem B3354059 : Blo 2235435 3354059 := bstep (se 1 (by rfl) ⟨2515544, by rfl⟩ : syracuseStep 3354059 = 5031089) B5031089
theorem B2236039 : Blo 2235435 2236039 := bstep (se 1 (by rfl) ⟨1677029, by rfl⟩ : syracuseStep 2236039 = 3354059) B3354059
theorem B2515549 : Blo 2235435 2515549 := bbase (se 3 (by rfl) ⟨471665, by rfl⟩ : syracuseStep 2515549 = 943331) (by norm_num)
theorem B3354065 : Blo 2235435 3354065 := bstep (se 2 (by rfl) ⟨1257774, by rfl⟩ : syracuseStep 3354065 = 2515549) B2515549
theorem B2236043 : Blo 2235435 2236043 := bstep (se 1 (by rfl) ⟨1677032, by rfl⟩ : syracuseStep 2236043 = 3354065) B3354065
theorem B7546661 : Blo 2235435 7546661 := bbase (se 4 (by rfl) ⟨707499, by rfl⟩ : syracuseStep 7546661 = 1414999) (by norm_num)
theorem B5031107 : Blo 2235435 5031107 := bstep (se 1 (by rfl) ⟨3773330, by rfl⟩ : syracuseStep 5031107 = 7546661) B7546661
theorem B3354071 : Blo 2235435 3354071 := bstep (se 1 (by rfl) ⟨2515553, by rfl⟩ : syracuseStep 3354071 = 5031107) B5031107
theorem B2236047 : Blo 2235435 2236047 := bstep (se 1 (by rfl) ⟨1677035, by rfl⟩ : syracuseStep 2236047 = 3354071) B3354071
theorem B3354077 : Blo 2235435 3354077 := bbase (se 3 (by rfl) ⟨628889, by rfl⟩ : syracuseStep 3354077 = 1257779) (by norm_num)
theorem B2236051 : Blo 2235435 2236051 := bstep (se 1 (by rfl) ⟨1677038, by rfl⟩ : syracuseStep 2236051 = 3354077) B3354077
theorem B5031125 : Blo 2235435 5031125 := bbase (se 7 (by rfl) ⟨58958, by rfl⟩ : syracuseStep 5031125 = 117917) (by norm_num)
theorem B3354083 : Blo 2235435 3354083 := bstep (se 1 (by rfl) ⟨2515562, by rfl⟩ : syracuseStep 3354083 = 5031125) B5031125
theorem B2236055 : Blo 2235435 2236055 := bstep (se 1 (by rfl) ⟨1677041, by rfl⟩ : syracuseStep 2236055 = 3354083) B3354083
theorem B5372605 : Blo 2235435 5372605 := bbase (se 3 (by rfl) ⟨1007363, by rfl⟩ : syracuseStep 5372605 = 2014727) (by norm_num)
theorem B7163473 : Blo 2235435 7163473 := bstep (se 2 (by rfl) ⟨2686302, by rfl⟩ : syracuseStep 7163473 = 5372605) B5372605
theorem B9551297 : Blo 2235435 9551297 := bstep (se 2 (by rfl) ⟨3581736, by rfl⟩ : syracuseStep 9551297 = 7163473) B7163473
theorem B6367531 : Blo 2235435 6367531 := bstep (se 1 (by rfl) ⟨4775648, by rfl⟩ : syracuseStep 6367531 = 9551297) B9551297
theorem B8490041 : Blo 2235435 8490041 := bstep (se 2 (by rfl) ⟨3183765, by rfl⟩ : syracuseStep 8490041 = 6367531) B6367531
theorem B5660027 : Blo 2235435 5660027 := bstep (se 1 (by rfl) ⟨4245020, by rfl⟩ : syracuseStep 5660027 = 8490041) B8490041
theorem B3773351 : Blo 2235435 3773351 := bstep (se 1 (by rfl) ⟨2830013, by rfl⟩ : syracuseStep 3773351 = 5660027) B5660027
theorem B2515567 : Blo 2235435 2515567 := bstep (se 1 (by rfl) ⟨1886675, by rfl⟩ : syracuseStep 2515567 = 3773351) B3773351
theorem B3354089 : Blo 2235435 3354089 := bstep (se 2 (by rfl) ⟨1257783, by rfl⟩ : syracuseStep 3354089 = 2515567) B2515567
theorem B2236059 : Blo 2235435 2236059 := bstep (se 1 (by rfl) ⟨1677044, by rfl⟩ : syracuseStep 2236059 = 3354089) B3354089
theorem B10199573 : Blo 2235435 10199573 := bbase (se 6 (by rfl) ⟨239052, by rfl⟩ : syracuseStep 10199573 = 478105) (by norm_num)
theorem B6799715 : Blo 2235435 6799715 := bstep (se 1 (by rfl) ⟨5099786, by rfl⟩ : syracuseStep 6799715 = 10199573) B10199573
theorem B4533143 : Blo 2235435 4533143 := bstep (se 1 (by rfl) ⟨3399857, by rfl⟩ : syracuseStep 4533143 = 6799715) B6799715
theorem B12088381 : Blo 2235435 12088381 := bstep (se 3 (by rfl) ⟨2266571, by rfl⟩ : syracuseStep 12088381 = 4533143) B4533143
theorem B16117841 : Blo 2235435 16117841 := bstep (se 2 (by rfl) ⟨6044190, by rfl⟩ : syracuseStep 16117841 = 12088381) B12088381
theorem B10745227 : Blo 2235435 10745227 := bstep (se 1 (by rfl) ⟨8058920, by rfl⟩ : syracuseStep 10745227 = 16117841) B16117841
theorem B14326969 : Blo 2235435 14326969 := bstep (se 2 (by rfl) ⟨5372613, by rfl⟩ : syracuseStep 14326969 = 10745227) B10745227
theorem B19102625 : Blo 2235435 19102625 := bstep (se 2 (by rfl) ⟨7163484, by rfl⟩ : syracuseStep 19102625 = 14326969) B14326969
theorem B12735083 : Blo 2235435 12735083 := bstep (se 1 (by rfl) ⟨9551312, by rfl⟩ : syracuseStep 12735083 = 19102625) B19102625
theorem B8490055 : Blo 2235435 8490055 := bstep (se 1 (by rfl) ⟨6367541, by rfl⟩ : syracuseStep 8490055 = 12735083) B12735083
theorem B11320073 : Blo 2235435 11320073 := bstep (se 2 (by rfl) ⟨4245027, by rfl⟩ : syracuseStep 11320073 = 8490055) B8490055
theorem B7546715 : Blo 2235435 7546715 := bstep (se 1 (by rfl) ⟨5660036, by rfl⟩ : syracuseStep 7546715 = 11320073) B11320073
theorem B5031143 : Blo 2235435 5031143 := bstep (se 1 (by rfl) ⟨3773357, by rfl⟩ : syracuseStep 5031143 = 7546715) B7546715
theorem B3354095 : Blo 2235435 3354095 := bstep (se 1 (by rfl) ⟨2515571, by rfl⟩ : syracuseStep 3354095 = 5031143) B5031143
theorem B2236063 : Blo 2235435 2236063 := bstep (se 1 (by rfl) ⟨1677047, by rfl⟩ : syracuseStep 2236063 = 3354095) B3354095
theorem B3354101 : Blo 2235435 3354101 := bbase (se 5 (by rfl) ⟨157223, by rfl⟩ : syracuseStep 3354101 = 314447) (by norm_num)
theorem B2236067 : Blo 2235435 2236067 := bstep (se 1 (by rfl) ⟨1677050, by rfl⟩ : syracuseStep 2236067 = 3354101) B3354101
theorem B2387837 : Blo 2235435 2387837 := bbase (se 3 (by rfl) ⟨447719, by rfl⟩ : syracuseStep 2387837 = 895439) (by norm_num)
theorem B6367565 : Blo 2235435 6367565 := bstep (se 3 (by rfl) ⟨1193918, by rfl⟩ : syracuseStep 6367565 = 2387837) B2387837
theorem B4245043 : Blo 2235435 4245043 := bstep (se 1 (by rfl) ⟨3183782, by rfl⟩ : syracuseStep 4245043 = 6367565) B6367565
theorem B5660057 : Blo 2235435 5660057 := bstep (se 2 (by rfl) ⟨2122521, by rfl⟩ : syracuseStep 5660057 = 4245043) B4245043
theorem B3773371 : Blo 2235435 3773371 := bstep (se 1 (by rfl) ⟨2830028, by rfl⟩ : syracuseStep 3773371 = 5660057) B5660057
theorem B5031161 : Blo 2235435 5031161 := bstep (se 2 (by rfl) ⟨1886685, by rfl⟩ : syracuseStep 5031161 = 3773371) B3773371
theorem B3354107 : Blo 2235435 3354107 := bstep (se 1 (by rfl) ⟨2515580, by rfl⟩ : syracuseStep 3354107 = 5031161) B5031161
theorem B2236071 : Blo 2235435 2236071 := bstep (se 1 (by rfl) ⟨1677053, by rfl⟩ : syracuseStep 2236071 = 3354107) B3354107
theorem B2515585 : Blo 2235435 2515585 := bbase (se 2 (by rfl) ⟨943344, by rfl⟩ : syracuseStep 2515585 = 1886689) (by norm_num)
theorem B3354113 : Blo 2235435 3354113 := bstep (se 2 (by rfl) ⟨1257792, by rfl⟩ : syracuseStep 3354113 = 2515585) B2515585
theorem B2236075 : Blo 2235435 2236075 := bstep (se 1 (by rfl) ⟨1677056, by rfl⟩ : syracuseStep 2236075 = 3354113) B3354113
theorem B5660077 : Blo 2235435 5660077 := bbase (se 3 (by rfl) ⟨1061264, by rfl⟩ : syracuseStep 5660077 = 2122529) (by norm_num)
theorem B7546769 : Blo 2235435 7546769 := bstep (se 2 (by rfl) ⟨2830038, by rfl⟩ : syracuseStep 7546769 = 5660077) B5660077
theorem B5031179 : Blo 2235435 5031179 := bstep (se 1 (by rfl) ⟨3773384, by rfl⟩ : syracuseStep 5031179 = 7546769) B7546769
theorem B3354119 : Blo 2235435 3354119 := bstep (se 1 (by rfl) ⟨2515589, by rfl⟩ : syracuseStep 3354119 = 5031179) B5031179
theorem B2236079 : Blo 2235435 2236079 := bstep (se 1 (by rfl) ⟨1677059, by rfl⟩ : syracuseStep 2236079 = 3354119) B3354119
theorem B3354125 : Blo 2235435 3354125 := bbase (se 3 (by rfl) ⟨628898, by rfl⟩ : syracuseStep 3354125 = 1257797) (by norm_num)
theorem B2236083 : Blo 2235435 2236083 := bstep (se 1 (by rfl) ⟨1677062, by rfl⟩ : syracuseStep 2236083 = 3354125) B3354125
theorem B5031197 : Blo 2235435 5031197 := bbase (se 3 (by rfl) ⟨943349, by rfl⟩ : syracuseStep 5031197 = 1886699) (by norm_num)
theorem B3354131 : Blo 2235435 3354131 := bstep (se 1 (by rfl) ⟨2515598, by rfl⟩ : syracuseStep 3354131 = 5031197) B5031197
theorem B2236087 : Blo 2235435 2236087 := bstep (se 1 (by rfl) ⟨1677065, by rfl⟩ : syracuseStep 2236087 = 3354131) B3354131
theorem B3773405 : Blo 2235435 3773405 := bbase (se 3 (by rfl) ⟨707513, by rfl⟩ : syracuseStep 3773405 = 1415027) (by norm_num)
theorem B2515603 : Blo 2235435 2515603 := bstep (se 1 (by rfl) ⟨1886702, by rfl⟩ : syracuseStep 2515603 = 3773405) B3773405
theorem B3354137 : Blo 2235435 3354137 := bstep (se 2 (by rfl) ⟨1257801, by rfl⟩ : syracuseStep 3354137 = 2515603) B2515603
theorem B2236091 : Blo 2235435 2236091 := bstep (se 1 (by rfl) ⟨1677068, by rfl⟩ : syracuseStep 2236091 = 3354137) B3354137
theorem B10745381 : Blo 2235435 10745381 := bbase (se 4 (by rfl) ⟨1007379, by rfl⟩ : syracuseStep 10745381 = 2014759) (by norm_num)
theorem B7163587 : Blo 2235435 7163587 := bstep (se 1 (by rfl) ⟨5372690, by rfl⟩ : syracuseStep 7163587 = 10745381) B10745381
theorem B9551449 : Blo 2235435 9551449 := bstep (se 2 (by rfl) ⟨3581793, by rfl⟩ : syracuseStep 9551449 = 7163587) B7163587
theorem B12735265 : Blo 2235435 12735265 := bstep (se 2 (by rfl) ⟨4775724, by rfl⟩ : syracuseStep 12735265 = 9551449) B9551449
theorem B16980353 : Blo 2235435 16980353 := bstep (se 2 (by rfl) ⟨6367632, by rfl⟩ : syracuseStep 16980353 = 12735265) B12735265
theorem B11320235 : Blo 2235435 11320235 := bstep (se 1 (by rfl) ⟨8490176, by rfl⟩ : syracuseStep 11320235 = 16980353) B16980353
theorem B7546823 : Blo 2235435 7546823 := bstep (se 1 (by rfl) ⟨5660117, by rfl⟩ : syracuseStep 7546823 = 11320235) B11320235
theorem B5031215 : Blo 2235435 5031215 := bstep (se 1 (by rfl) ⟨3773411, by rfl⟩ : syracuseStep 5031215 = 7546823) B7546823
theorem B3354143 : Blo 2235435 3354143 := bstep (se 1 (by rfl) ⟨2515607, by rfl⟩ : syracuseStep 3354143 = 5031215) B5031215
theorem B2236095 : Blo 2235435 2236095 := bstep (se 1 (by rfl) ⟨1677071, by rfl⟩ : syracuseStep 2236095 = 3354143) B3354143
theorem B3354149 : Blo 2235435 3354149 := bbase (se 4 (by rfl) ⟨314451, by rfl⟩ : syracuseStep 3354149 = 628903) (by norm_num)
theorem B2236099 : Blo 2235435 2236099 := bstep (se 1 (by rfl) ⟨1677074, by rfl⟩ : syracuseStep 2236099 = 3354149) B3354149
theorem B2830069 : Blo 2235435 2830069 := bbase (se 5 (by rfl) ⟨132659, by rfl⟩ : syracuseStep 2830069 = 265319) (by norm_num)
theorem B3773425 : Blo 2235435 3773425 := bstep (se 2 (by rfl) ⟨1415034, by rfl⟩ : syracuseStep 3773425 = 2830069) B2830069
theorem B5031233 : Blo 2235435 5031233 := bstep (se 2 (by rfl) ⟨1886712, by rfl⟩ : syracuseStep 5031233 = 3773425) B3773425
theorem B3354155 : Blo 2235435 3354155 := bstep (se 1 (by rfl) ⟨2515616, by rfl⟩ : syracuseStep 3354155 = 5031233) B5031233
theorem B2236103 : Blo 2235435 2236103 := bstep (se 1 (by rfl) ⟨1677077, by rfl⟩ : syracuseStep 2236103 = 3354155) B3354155
theorem B2515621 : Blo 2235435 2515621 := bbase (se 4 (by rfl) ⟨235839, by rfl⟩ : syracuseStep 2515621 = 471679) (by norm_num)
theorem B3354161 : Blo 2235435 3354161 := bstep (se 2 (by rfl) ⟨1257810, by rfl⟩ : syracuseStep 3354161 = 2515621) B2515621
theorem B2236107 : Blo 2235435 2236107 := bstep (se 1 (by rfl) ⟨1677080, by rfl⟩ : syracuseStep 2236107 = 3354161) B3354161
theorem B5895005 : Blo 2235435 5895005 := bbase (se 3 (by rfl) ⟨1105313, by rfl⟩ : syracuseStep 5895005 = 2210627) (by norm_num)
theorem B15720013 : Blo 2235435 15720013 := bstep (se 3 (by rfl) ⟨2947502, by rfl⟩ : syracuseStep 15720013 = 5895005) B5895005
theorem B20960017 : Blo 2235435 20960017 := bstep (se 2 (by rfl) ⟨7860006, by rfl⟩ : syracuseStep 20960017 = 15720013) B15720013
theorem B447147029 : Blo 2235435 447147029 := bstep (se 6 (by rfl) ⟨10480008, by rfl⟩ : syracuseStep 447147029 = 20960017) B20960017
theorem B298098019 : Blo 2235435 298098019 := bstep (se 1 (by rfl) ⟨223573514, by rfl⟩ : syracuseStep 298098019 = 447147029) B447147029
theorem B397464025 : Blo 2235435 397464025 := bstep (se 2 (by rfl) ⟨149049009, by rfl⟩ : syracuseStep 397464025 = 298098019) B298098019
theorem B529952033 : Blo 2235435 529952033 := bstep (se 2 (by rfl) ⟨198732012, by rfl⟩ : syracuseStep 529952033 = 397464025) B397464025
theorem B353301355 : Blo 2235435 353301355 := bstep (se 1 (by rfl) ⟨264976016, by rfl⟩ : syracuseStep 353301355 = 529952033) B529952033
theorem B471068473 : Blo 2235435 471068473 := bstep (se 2 (by rfl) ⟨176650677, by rfl⟩ : syracuseStep 471068473 = 353301355) B353301355
theorem B628091297 : Blo 2235435 628091297 := bstep (se 2 (by rfl) ⟨235534236, by rfl⟩ : syracuseStep 628091297 = 471068473) B471068473
theorem B418727531 : Blo 2235435 418727531 := bstep (se 1 (by rfl) ⟨314045648, by rfl⟩ : syracuseStep 418727531 = 628091297) B628091297
theorem B279151687 : Blo 2235435 279151687 := bstep (se 1 (by rfl) ⟨209363765, by rfl⟩ : syracuseStep 279151687 = 418727531) B418727531
theorem B372202249 : Blo 2235435 372202249 := bstep (se 2 (by rfl) ⟨139575843, by rfl⟩ : syracuseStep 372202249 = 279151687) B279151687
theorem B496269665 : Blo 2235435 496269665 := bstep (se 2 (by rfl) ⟨186101124, by rfl⟩ : syracuseStep 496269665 = 372202249) B372202249
theorem B330846443 : Blo 2235435 330846443 := bstep (se 1 (by rfl) ⟨248134832, by rfl⟩ : syracuseStep 330846443 = 496269665) B496269665
theorem B220564295 : Blo 2235435 220564295 := bstep (se 1 (by rfl) ⟨165423221, by rfl⟩ : syracuseStep 220564295 = 330846443) B330846443
theorem B147042863 : Blo 2235435 147042863 := bstep (se 1 (by rfl) ⟨110282147, by rfl⟩ : syracuseStep 147042863 = 220564295) B220564295
theorem B98028575 : Blo 2235435 98028575 := bstep (se 1 (by rfl) ⟨73521431, by rfl⟩ : syracuseStep 98028575 = 147042863) B147042863
theorem B65352383 : Blo 2235435 65352383 := bstep (se 1 (by rfl) ⟨49014287, by rfl⟩ : syracuseStep 65352383 = 98028575) B98028575
theorem B43568255 : Blo 2235435 43568255 := bstep (se 1 (by rfl) ⟨32676191, by rfl⟩ : syracuseStep 43568255 = 65352383) B65352383
theorem B29045503 : Blo 2235435 29045503 := bstep (se 1 (by rfl) ⟨21784127, by rfl⟩ : syracuseStep 29045503 = 43568255) B43568255
theorem B38727337 : Blo 2235435 38727337 := bstep (se 2 (by rfl) ⟨14522751, by rfl⟩ : syracuseStep 38727337 = 29045503) B29045503
theorem B51636449 : Blo 2235435 51636449 := bstep (se 2 (by rfl) ⟨19363668, by rfl⟩ : syracuseStep 51636449 = 38727337) B38727337
theorem B34424299 : Blo 2235435 34424299 := bstep (se 1 (by rfl) ⟨25818224, by rfl⟩ : syracuseStep 34424299 = 51636449) B51636449
theorem B45899065 : Blo 2235435 45899065 := bstep (se 2 (by rfl) ⟨17212149, by rfl⟩ : syracuseStep 45899065 = 34424299) B34424299
theorem B61198753 : Blo 2235435 61198753 := bstep (se 2 (by rfl) ⟨22949532, by rfl⟩ : syracuseStep 61198753 = 45899065) B45899065
theorem B81598337 : Blo 2235435 81598337 := bstep (se 2 (by rfl) ⟨30599376, by rfl⟩ : syracuseStep 81598337 = 61198753) B61198753
theorem B54398891 : Blo 2235435 54398891 := bstep (se 1 (by rfl) ⟨40799168, by rfl⟩ : syracuseStep 54398891 = 81598337) B81598337
theorem B36265927 : Blo 2235435 36265927 := bstep (se 1 (by rfl) ⟨27199445, by rfl⟩ : syracuseStep 36265927 = 54398891) B54398891
theorem B48354569 : Blo 2235435 48354569 := bstep (se 2 (by rfl) ⟨18132963, by rfl⟩ : syracuseStep 48354569 = 36265927) B36265927
theorem B32236379 : Blo 2235435 32236379 := bstep (se 1 (by rfl) ⟨24177284, by rfl⟩ : syracuseStep 32236379 = 48354569) B48354569
theorem B21490919 : Blo 2235435 21490919 := bstep (se 1 (by rfl) ⟨16118189, by rfl⟩ : syracuseStep 21490919 = 32236379) B32236379
theorem B14327279 : Blo 2235435 14327279 := bstep (se 1 (by rfl) ⟨10745459, by rfl⟩ : syracuseStep 14327279 = 21490919) B21490919
theorem B9551519 : Blo 2235435 9551519 := bstep (se 1 (by rfl) ⟨7163639, by rfl⟩ : syracuseStep 9551519 = 14327279) B14327279
theorem B6367679 : Blo 2235435 6367679 := bstep (se 1 (by rfl) ⟨4775759, by rfl⟩ : syracuseStep 6367679 = 9551519) B9551519
theorem B4245119 : Blo 2235435 4245119 := bstep (se 1 (by rfl) ⟨3183839, by rfl⟩ : syracuseStep 4245119 = 6367679) B6367679
theorem B2830079 : Blo 2235435 2830079 := bstep (se 1 (by rfl) ⟨2122559, by rfl⟩ : syracuseStep 2830079 = 4245119) B4245119
theorem B7546877 : Blo 2235435 7546877 := bstep (se 3 (by rfl) ⟨1415039, by rfl⟩ : syracuseStep 7546877 = 2830079) B2830079
theorem B5031251 : Blo 2235435 5031251 := bstep (se 1 (by rfl) ⟨3773438, by rfl⟩ : syracuseStep 5031251 = 7546877) B7546877
theorem B3354167 : Blo 2235435 3354167 := bstep (se 1 (by rfl) ⟨2515625, by rfl⟩ : syracuseStep 3354167 = 5031251) B5031251
theorem B2236111 : Blo 2235435 2236111 := bstep (se 1 (by rfl) ⟨1677083, by rfl⟩ : syracuseStep 2236111 = 3354167) B3354167
theorem B3354173 : Blo 2235435 3354173 := bbase (se 3 (by rfl) ⟨628907, by rfl⟩ : syracuseStep 3354173 = 1257815) (by norm_num)
theorem B2236115 : Blo 2235435 2236115 := bstep (se 1 (by rfl) ⟨1677086, by rfl⟩ : syracuseStep 2236115 = 3354173) B3354173
theorem B5031269 : Blo 2235435 5031269 := bbase (se 4 (by rfl) ⟨471681, by rfl⟩ : syracuseStep 5031269 = 943363) (by norm_num)
theorem B3354179 : Blo 2235435 3354179 := bstep (se 1 (by rfl) ⟨2515634, by rfl⟩ : syracuseStep 3354179 = 5031269) B5031269
theorem B2236119 : Blo 2235435 2236119 := bstep (se 1 (by rfl) ⟨1677089, by rfl⟩ : syracuseStep 2236119 = 3354179) B3354179
theorem B5660189 : Blo 2235435 5660189 := bbase (se 3 (by rfl) ⟨1061285, by rfl⟩ : syracuseStep 5660189 = 2122571) (by norm_num)
theorem B3773459 : Blo 2235435 3773459 := bstep (se 1 (by rfl) ⟨2830094, by rfl⟩ : syracuseStep 3773459 = 5660189) B5660189
theorem B2515639 : Blo 2235435 2515639 := bstep (se 1 (by rfl) ⟨1886729, by rfl⟩ : syracuseStep 2515639 = 3773459) B3773459
theorem B3354185 : Blo 2235435 3354185 := bstep (se 2 (by rfl) ⟨1257819, by rfl⟩ : syracuseStep 3354185 = 2515639) B2515639
theorem B2236123 : Blo 2235435 2236123 := bstep (se 1 (by rfl) ⟨1677092, by rfl⟩ : syracuseStep 2236123 = 3354185) B3354185
theorem B4245149 : Blo 2235435 4245149 := bbase (se 3 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 4245149 = 1591931) (by norm_num)
theorem B11320397 : Blo 2235435 11320397 := bstep (se 3 (by rfl) ⟨2122574, by rfl⟩ : syracuseStep 11320397 = 4245149) B4245149
theorem B7546931 : Blo 2235435 7546931 := bstep (se 1 (by rfl) ⟨5660198, by rfl⟩ : syracuseStep 7546931 = 11320397) B11320397
theorem B5031287 : Blo 2235435 5031287 := bstep (se 1 (by rfl) ⟨3773465, by rfl⟩ : syracuseStep 5031287 = 7546931) B7546931
theorem B3354191 : Blo 2235435 3354191 := bstep (se 1 (by rfl) ⟨2515643, by rfl⟩ : syracuseStep 3354191 = 5031287) B5031287
theorem B2236127 : Blo 2235435 2236127 := bstep (se 1 (by rfl) ⟨1677095, by rfl⟩ : syracuseStep 2236127 = 3354191) B3354191
theorem B3354197 : Blo 2235435 3354197 := bbase (se 8 (by rfl) ⟨19653, by rfl⟩ : syracuseStep 3354197 = 39307) (by norm_num)
theorem B2236131 : Blo 2235435 2236131 := bstep (se 1 (by rfl) ⟨1677098, by rfl⟩ : syracuseStep 2236131 = 3354197) B3354197
theorem B9551621 : Blo 2235435 9551621 := bbase (se 4 (by rfl) ⟨895464, by rfl⟩ : syracuseStep 9551621 = 1790929) (by norm_num)
theorem B6367747 : Blo 2235435 6367747 := bstep (se 1 (by rfl) ⟨4775810, by rfl⟩ : syracuseStep 6367747 = 9551621) B9551621
theorem B8490329 : Blo 2235435 8490329 := bstep (se 2 (by rfl) ⟨3183873, by rfl⟩ : syracuseStep 8490329 = 6367747) B6367747
theorem B5660219 : Blo 2235435 5660219 := bstep (se 1 (by rfl) ⟨4245164, by rfl⟩ : syracuseStep 5660219 = 8490329) B8490329
theorem B3773479 : Blo 2235435 3773479 := bstep (se 1 (by rfl) ⟨2830109, by rfl⟩ : syracuseStep 3773479 = 5660219) B5660219
theorem B5031305 : Blo 2235435 5031305 := bstep (se 2 (by rfl) ⟨1886739, by rfl⟩ : syracuseStep 5031305 = 3773479) B3773479
theorem B3354203 : Blo 2235435 3354203 := bstep (se 1 (by rfl) ⟨2515652, by rfl⟩ : syracuseStep 3354203 = 5031305) B5031305
theorem B2236135 : Blo 2235435 2236135 := bstep (se 1 (by rfl) ⟨1677101, by rfl⟩ : syracuseStep 2236135 = 3354203) B3354203
theorem B2515657 : Blo 2235435 2515657 := bbase (se 2 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 2515657 = 1886743) (by norm_num)
theorem B3354209 : Blo 2235435 3354209 := bstep (se 2 (by rfl) ⟨1257828, by rfl⟩ : syracuseStep 3354209 = 2515657) B2515657
theorem B2236139 : Blo 2235435 2236139 := bstep (se 1 (by rfl) ⟨1677104, by rfl⟩ : syracuseStep 2236139 = 3354209) B3354209
theorem B4029605 : Blo 2235435 4029605 := bbase (se 4 (by rfl) ⟨377775, by rfl⟩ : syracuseStep 4029605 = 755551) (by norm_num)
theorem B2686403 : Blo 2235435 2686403 := bstep (se 1 (by rfl) ⟨2014802, by rfl⟩ : syracuseStep 2686403 = 4029605) B4029605
theorem B7163741 : Blo 2235435 7163741 := bstep (se 3 (by rfl) ⟨1343201, by rfl⟩ : syracuseStep 7163741 = 2686403) B2686403
theorem B19103309 : Blo 2235435 19103309 := bstep (se 3 (by rfl) ⟨3581870, by rfl⟩ : syracuseStep 19103309 = 7163741) B7163741
theorem B12735539 : Blo 2235435 12735539 := bstep (se 1 (by rfl) ⟨9551654, by rfl⟩ : syracuseStep 12735539 = 19103309) B19103309
theorem B8490359 : Blo 2235435 8490359 := bstep (se 1 (by rfl) ⟨6367769, by rfl⟩ : syracuseStep 8490359 = 12735539) B12735539
theorem B5660239 : Blo 2235435 5660239 := bstep (se 1 (by rfl) ⟨4245179, by rfl⟩ : syracuseStep 5660239 = 8490359) B8490359
theorem B7546985 : Blo 2235435 7546985 := bstep (se 2 (by rfl) ⟨2830119, by rfl⟩ : syracuseStep 7546985 = 5660239) B5660239
theorem B5031323 : Blo 2235435 5031323 := bstep (se 1 (by rfl) ⟨3773492, by rfl⟩ : syracuseStep 5031323 = 7546985) B7546985
theorem B3354215 : Blo 2235435 3354215 := bstep (se 1 (by rfl) ⟨2515661, by rfl⟩ : syracuseStep 3354215 = 5031323) B5031323
theorem B2236143 : Blo 2235435 2236143 := bstep (se 1 (by rfl) ⟨1677107, by rfl⟩ : syracuseStep 2236143 = 3354215) B3354215
theorem B3354221 : Blo 2235435 3354221 := bbase (se 3 (by rfl) ⟨628916, by rfl⟩ : syracuseStep 3354221 = 1257833) (by norm_num)
theorem B2236147 : Blo 2235435 2236147 := bstep (se 1 (by rfl) ⟨1677110, by rfl⟩ : syracuseStep 2236147 = 3354221) B3354221
theorem B5031341 : Blo 2235435 5031341 := bbase (se 3 (by rfl) ⟨943376, by rfl⟩ : syracuseStep 5031341 = 1886753) (by norm_num)
theorem B3354227 : Blo 2235435 3354227 := bstep (se 1 (by rfl) ⟨2515670, by rfl⟩ : syracuseStep 3354227 = 5031341) B5031341
theorem B2236151 : Blo 2235435 2236151 := bstep (se 1 (by rfl) ⟨1677113, by rfl⟩ : syracuseStep 2236151 = 3354227) B3354227
theorem B5372837 : Blo 2235435 5372837 := bbase (se 4 (by rfl) ⟨503703, by rfl⟩ : syracuseStep 5372837 = 1007407) (by norm_num)
theorem B3581891 : Blo 2235435 3581891 := bstep (se 1 (by rfl) ⟨2686418, by rfl⟩ : syracuseStep 3581891 = 5372837) B5372837
theorem B2387927 : Blo 2235435 2387927 := bstep (se 1 (by rfl) ⟨1790945, by rfl⟩ : syracuseStep 2387927 = 3581891) B3581891
theorem B6367805 : Blo 2235435 6367805 := bstep (se 3 (by rfl) ⟨1193963, by rfl⟩ : syracuseStep 6367805 = 2387927) B2387927
theorem B4245203 : Blo 2235435 4245203 := bstep (se 1 (by rfl) ⟨3183902, by rfl⟩ : syracuseStep 4245203 = 6367805) B6367805
theorem B2830135 : Blo 2235435 2830135 := bstep (se 1 (by rfl) ⟨2122601, by rfl⟩ : syracuseStep 2830135 = 4245203) B4245203
theorem B3773513 : Blo 2235435 3773513 := bstep (se 2 (by rfl) ⟨1415067, by rfl⟩ : syracuseStep 3773513 = 2830135) B2830135
theorem B2515675 : Blo 2235435 2515675 := bstep (se 1 (by rfl) ⟨1886756, by rfl⟩ : syracuseStep 2515675 = 3773513) B3773513
theorem B3354233 : Blo 2235435 3354233 := bstep (se 2 (by rfl) ⟨1257837, by rfl⟩ : syracuseStep 3354233 = 2515675) B2515675
theorem B2236155 : Blo 2235435 2236155 := bstep (se 1 (by rfl) ⟨1677116, by rfl⟩ : syracuseStep 2236155 = 3354233) B3354233
theorem B4841021 : Blo 2235435 4841021 := bbase (se 3 (by rfl) ⟨907691, by rfl⟩ : syracuseStep 4841021 = 1815383) (by norm_num)
theorem B3227347 : Blo 2235435 3227347 := bstep (se 1 (by rfl) ⟨2420510, by rfl⟩ : syracuseStep 3227347 = 4841021) B4841021
theorem B4303129 : Blo 2235435 4303129 := bstep (se 2 (by rfl) ⟨1613673, by rfl⟩ : syracuseStep 4303129 = 3227347) B3227347
theorem B5737505 : Blo 2235435 5737505 := bstep (se 2 (by rfl) ⟨2151564, by rfl⟩ : syracuseStep 5737505 = 4303129) B4303129
theorem B15300013 : Blo 2235435 15300013 := bstep (se 3 (by rfl) ⟨2868752, by rfl⟩ : syracuseStep 15300013 = 5737505) B5737505
theorem B20400017 : Blo 2235435 20400017 := bstep (se 2 (by rfl) ⟨7650006, by rfl⟩ : syracuseStep 20400017 = 15300013) B15300013
theorem B217600181 : Blo 2235435 217600181 := bstep (se 5 (by rfl) ⟨10200008, by rfl⟩ : syracuseStep 217600181 = 20400017) B20400017
theorem B145066787 : Blo 2235435 145066787 := bstep (se 1 (by rfl) ⟨108800090, by rfl⟩ : syracuseStep 145066787 = 217600181) B217600181
theorem B96711191 : Blo 2235435 96711191 := bstep (se 1 (by rfl) ⟨72533393, by rfl⟩ : syracuseStep 96711191 = 145066787) B145066787
theorem B64474127 : Blo 2235435 64474127 := bstep (se 1 (by rfl) ⟨48355595, by rfl⟩ : syracuseStep 64474127 = 96711191) B96711191
theorem B42982751 : Blo 2235435 42982751 := bstep (se 1 (by rfl) ⟨32237063, by rfl⟩ : syracuseStep 42982751 = 64474127) B64474127
theorem B28655167 : Blo 2235435 28655167 := bstep (se 1 (by rfl) ⟨21491375, by rfl⟩ : syracuseStep 28655167 = 42982751) B42982751
theorem B38206889 : Blo 2235435 38206889 := bstep (se 2 (by rfl) ⟨14327583, by rfl⟩ : syracuseStep 38206889 = 28655167) B28655167
theorem B25471259 : Blo 2235435 25471259 := bstep (se 1 (by rfl) ⟨19103444, by rfl⟩ : syracuseStep 25471259 = 38206889) B38206889
theorem B16980839 : Blo 2235435 16980839 := bstep (se 1 (by rfl) ⟨12735629, by rfl⟩ : syracuseStep 16980839 = 25471259) B25471259
theorem B11320559 : Blo 2235435 11320559 := bstep (se 1 (by rfl) ⟨8490419, by rfl⟩ : syracuseStep 11320559 = 16980839) B16980839
theorem B7547039 : Blo 2235435 7547039 := bstep (se 1 (by rfl) ⟨5660279, by rfl⟩ : syracuseStep 7547039 = 11320559) B11320559
theorem B5031359 : Blo 2235435 5031359 := bstep (se 1 (by rfl) ⟨3773519, by rfl⟩ : syracuseStep 5031359 = 7547039) B7547039
theorem B3354239 : Blo 2235435 3354239 := bstep (se 1 (by rfl) ⟨2515679, by rfl⟩ : syracuseStep 3354239 = 5031359) B5031359
theorem B2236159 : Blo 2235435 2236159 := bstep (se 1 (by rfl) ⟨1677119, by rfl⟩ : syracuseStep 2236159 = 3354239) B3354239
theorem B3354245 : Blo 2235435 3354245 := bbase (se 4 (by rfl) ⟨314460, by rfl⟩ : syracuseStep 3354245 = 628921) (by norm_num)
theorem B2236163 : Blo 2235435 2236163 := bstep (se 1 (by rfl) ⟨1677122, by rfl⟩ : syracuseStep 2236163 = 3354245) B3354245
theorem B3773533 : Blo 2235435 3773533 := bbase (se 3 (by rfl) ⟨707537, by rfl⟩ : syracuseStep 3773533 = 1415075) (by norm_num)
theorem B5031377 : Blo 2235435 5031377 := bstep (se 2 (by rfl) ⟨1886766, by rfl⟩ : syracuseStep 5031377 = 3773533) B3773533
theorem B3354251 : Blo 2235435 3354251 := bstep (se 1 (by rfl) ⟨2515688, by rfl⟩ : syracuseStep 3354251 = 5031377) B5031377
theorem B2236167 : Blo 2235435 2236167 := bstep (se 1 (by rfl) ⟨1677125, by rfl⟩ : syracuseStep 2236167 = 3354251) B3354251
theorem B2515693 : Blo 2235435 2515693 := bbase (se 3 (by rfl) ⟨471692, by rfl⟩ : syracuseStep 2515693 = 943385) (by norm_num)
theorem B3354257 : Blo 2235435 3354257 := bstep (se 2 (by rfl) ⟨1257846, by rfl⟩ : syracuseStep 3354257 = 2515693) B2515693
theorem B2236171 : Blo 2235435 2236171 := bstep (se 1 (by rfl) ⟨1677128, by rfl⟩ : syracuseStep 2236171 = 3354257) B3354257
theorem B7547093 : Blo 2235435 7547093 := bbase (se 7 (by rfl) ⟨88442, by rfl⟩ : syracuseStep 7547093 = 176885) (by norm_num)
theorem B5031395 : Blo 2235435 5031395 := bstep (se 1 (by rfl) ⟨3773546, by rfl⟩ : syracuseStep 5031395 = 7547093) B7547093
theorem B3354263 : Blo 2235435 3354263 := bstep (se 1 (by rfl) ⟨2515697, by rfl⟩ : syracuseStep 3354263 = 5031395) B5031395
theorem B2236175 : Blo 2235435 2236175 := bstep (se 1 (by rfl) ⟨1677131, by rfl⟩ : syracuseStep 2236175 = 3354263) B3354263
theorem B3354269 : Blo 2235435 3354269 := bbase (se 3 (by rfl) ⟨628925, by rfl⟩ : syracuseStep 3354269 = 1257851) (by norm_num)
theorem B2236179 : Blo 2235435 2236179 := bstep (se 1 (by rfl) ⟨1677134, by rfl⟩ : syracuseStep 2236179 = 3354269) B3354269
theorem B5031413 : Blo 2235435 5031413 := bbase (se 5 (by rfl) ⟨235847, by rfl⟩ : syracuseStep 5031413 = 471695) (by norm_num)
theorem B3354275 : Blo 2235435 3354275 := bstep (se 1 (by rfl) ⟨2515706, by rfl⟩ : syracuseStep 3354275 = 5031413) B5031413
theorem B2236183 : Blo 2235435 2236183 := bstep (se 1 (by rfl) ⟨1677137, by rfl⟩ : syracuseStep 2236183 = 3354275) B3354275
theorem B20400277 : Blo 2235435 20400277 := bbase (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) (by norm_num)
theorem B27200369 : Blo 2235435 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B18133579 : Blo 2235435 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B24178105 : Blo 2235435 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B32237473 : Blo 2235435 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B42983297 : Blo 2235435 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B28655531 : Blo 2235435 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B19103687 : Blo 2235435 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B12735791 : Blo 2235435 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B8490527 : Blo 2235435 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B5660351 : Blo 2235435 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B3773567 : Blo 2235435 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B2515711 : Blo 2235435 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B3354281 : Blo 2235435 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B2236187 : Blo 2235435 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B2387965 : Blo 2235435 2387965 := bbase (se 3 (by rfl) ⟨447743, by rfl⟩ : syracuseStep 2387965 = 895487) (by norm_num)
theorem B3183953 : Blo 2235435 3183953 := bstep (se 2 (by rfl) ⟨1193982, by rfl⟩ : syracuseStep 3183953 = 2387965) B2387965
theorem B8490541 : Blo 2235435 8490541 := bstep (se 3 (by rfl) ⟨1591976, by rfl⟩ : syracuseStep 8490541 = 3183953) B3183953
theorem B11320721 : Blo 2235435 11320721 := bstep (se 2 (by rfl) ⟨4245270, by rfl⟩ : syracuseStep 11320721 = 8490541) B8490541
theorem B7547147 : Blo 2235435 7547147 := bstep (se 1 (by rfl) ⟨5660360, by rfl⟩ : syracuseStep 7547147 = 11320721) B11320721
theorem B5031431 : Blo 2235435 5031431 := bstep (se 1 (by rfl) ⟨3773573, by rfl⟩ : syracuseStep 5031431 = 7547147) B7547147
theorem B3354287 : Blo 2235435 3354287 := bstep (se 1 (by rfl) ⟨2515715, by rfl⟩ : syracuseStep 3354287 = 5031431) B5031431
theorem B2236191 : Blo 2235435 2236191 := bstep (se 1 (by rfl) ⟨1677143, by rfl⟩ : syracuseStep 2236191 = 3354287) B3354287
theorem B3354293 : Blo 2235435 3354293 := bbase (se 5 (by rfl) ⟨157232, by rfl⟩ : syracuseStep 3354293 = 314465) (by norm_num)
theorem B2236195 : Blo 2235435 2236195 := bstep (se 1 (by rfl) ⟨1677146, by rfl⟩ : syracuseStep 2236195 = 3354293) B3354293
theorem B5660381 : Blo 2235435 5660381 := bbase (se 3 (by rfl) ⟨1061321, by rfl⟩ : syracuseStep 5660381 = 2122643) (by norm_num)
theorem B3773587 : Blo 2235435 3773587 := bstep (se 1 (by rfl) ⟨2830190, by rfl⟩ : syracuseStep 3773587 = 5660381) B5660381
theorem B5031449 : Blo 2235435 5031449 := bstep (se 2 (by rfl) ⟨1886793, by rfl⟩ : syracuseStep 5031449 = 3773587) B3773587
theorem B3354299 : Blo 2235435 3354299 := bstep (se 1 (by rfl) ⟨2515724, by rfl⟩ : syracuseStep 3354299 = 5031449) B5031449
theorem B2236199 : Blo 2235435 2236199 := bstep (se 1 (by rfl) ⟨1677149, by rfl⟩ : syracuseStep 2236199 = 3354299) B3354299
theorem B2515729 : Blo 2235435 2515729 := bbase (se 2 (by rfl) ⟨943398, by rfl⟩ : syracuseStep 2515729 = 1886797) (by norm_num)
theorem B3354305 : Blo 2235435 3354305 := bstep (se 2 (by rfl) ⟨1257864, by rfl⟩ : syracuseStep 3354305 = 2515729) B2515729
theorem B2236203 : Blo 2235435 2236203 := bstep (se 1 (by rfl) ⟨1677152, by rfl⟩ : syracuseStep 2236203 = 3354305) B3354305
theorem B4245301 : Blo 2235435 4245301 := bbase (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) (by norm_num)
theorem B5660401 : Blo 2235435 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B7547201 : Blo 2235435 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B5031467 : Blo 2235435 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B3354311 : Blo 2235435 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B2236207 : Blo 2235435 2236207 := bstep (se 1 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 2236207 = 3354311) B3354311
theorem B3354317 : Blo 2235435 3354317 := bbase (se 3 (by rfl) ⟨628934, by rfl⟩ : syracuseStep 3354317 = 1257869) (by norm_num)
theorem B2236211 : Blo 2235435 2236211 := bstep (se 1 (by rfl) ⟨1677158, by rfl⟩ : syracuseStep 2236211 = 3354317) B3354317
theorem B5031485 : Blo 2235435 5031485 := bbase (se 3 (by rfl) ⟨943403, by rfl⟩ : syracuseStep 5031485 = 1886807) (by norm_num)
theorem B3354323 : Blo 2235435 3354323 := bstep (se 1 (by rfl) ⟨2515742, by rfl⟩ : syracuseStep 3354323 = 5031485) B5031485
theorem B2236215 : Blo 2235435 2236215 := bstep (se 1 (by rfl) ⟨1677161, by rfl⟩ : syracuseStep 2236215 = 3354323) B3354323
theorem B3773621 : Blo 2235435 3773621 := bbase (se 5 (by rfl) ⟨176888, by rfl⟩ : syracuseStep 3773621 = 353777) (by norm_num)
theorem B2515747 : Blo 2235435 2515747 := bstep (se 1 (by rfl) ⟨1886810, by rfl⟩ : syracuseStep 2515747 = 3773621) B3773621
theorem B3354329 : Blo 2235435 3354329 := bstep (se 2 (by rfl) ⟨1257873, by rfl⟩ : syracuseStep 3354329 = 2515747) B2515747
theorem B2236219 : Blo 2235435 2236219 := bstep (se 1 (by rfl) ⟨1677164, by rfl⟩ : syracuseStep 2236219 = 3354329) B3354329
theorem B7650229 : Blo 2235435 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B10200305 : Blo 2235435 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B6800203 : Blo 2235435 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B9066937 : Blo 2235435 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B12089249 : Blo 2235435 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B8059499 : Blo 2235435 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B5372999 : Blo 2235435 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B3581999 : Blo 2235435 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B2387999 : Blo 2235435 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B6367997 : Blo 2235435 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B16981325 : Blo 2235435 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B11320883 : Blo 2235435 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B7547255 : Blo 2235435 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B5031503 : Blo 2235435 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B3354335 : Blo 2235435 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B2236223 : Blo 2235435 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B3354341 : Blo 2235435 3354341 := bbase (se 4 (by rfl) ⟨314469, by rfl⟩ : syracuseStep 3354341 = 628939) (by norm_num)
theorem B2236227 : Blo 2235435 2236227 := bstep (se 1 (by rfl) ⟨1677170, by rfl⟩ : syracuseStep 2236227 = 3354341) B3354341
theorem B6368021 : Blo 2235435 6368021 := bbase (se 6 (by rfl) ⟨149250, by rfl⟩ : syracuseStep 6368021 = 298501) (by norm_num)
theorem B4245347 : Blo 2235435 4245347 := bstep (se 1 (by rfl) ⟨3184010, by rfl⟩ : syracuseStep 4245347 = 6368021) B6368021
theorem B2830231 : Blo 2235435 2830231 := bstep (se 1 (by rfl) ⟨2122673, by rfl⟩ : syracuseStep 2830231 = 4245347) B4245347
theorem B3773641 : Blo 2235435 3773641 := bstep (se 2 (by rfl) ⟨1415115, by rfl⟩ : syracuseStep 3773641 = 2830231) B2830231
theorem B5031521 : Blo 2235435 5031521 := bstep (se 2 (by rfl) ⟨1886820, by rfl⟩ : syracuseStep 5031521 = 3773641) B3773641
theorem B3354347 : Blo 2235435 3354347 := bstep (se 1 (by rfl) ⟨2515760, by rfl⟩ : syracuseStep 3354347 = 5031521) B5031521
theorem B2236231 : Blo 2235435 2236231 := bstep (se 1 (by rfl) ⟨1677173, by rfl⟩ : syracuseStep 2236231 = 3354347) B3354347
theorem B2515765 : Blo 2235435 2515765 := bbase (se 5 (by rfl) ⟨117926, by rfl⟩ : syracuseStep 2515765 = 235853) (by norm_num)
theorem B3354353 : Blo 2235435 3354353 := bstep (se 2 (by rfl) ⟨1257882, by rfl⟩ : syracuseStep 3354353 = 2515765) B2515765
theorem B2236235 : Blo 2235435 2236235 := bstep (se 1 (by rfl) ⟨1677176, by rfl⟩ : syracuseStep 2236235 = 3354353) B3354353
theorem B2830241 : Blo 2235435 2830241 := bbase (se 2 (by rfl) ⟨1061340, by rfl⟩ : syracuseStep 2830241 = 2122681) (by norm_num)
theorem B7547309 : Blo 2235435 7547309 := bstep (se 3 (by rfl) ⟨1415120, by rfl⟩ : syracuseStep 7547309 = 2830241) B2830241
theorem B5031539 : Blo 2235435 5031539 := bstep (se 1 (by rfl) ⟨3773654, by rfl⟩ : syracuseStep 5031539 = 7547309) B7547309
theorem B3354359 : Blo 2235435 3354359 := bstep (se 1 (by rfl) ⟨2515769, by rfl⟩ : syracuseStep 3354359 = 5031539) B5031539
theorem B2236239 : Blo 2235435 2236239 := bstep (se 1 (by rfl) ⟨1677179, by rfl⟩ : syracuseStep 2236239 = 3354359) B3354359
theorem B3354365 : Blo 2235435 3354365 := bbase (se 3 (by rfl) ⟨628943, by rfl⟩ : syracuseStep 3354365 = 1257887) (by norm_num)
theorem B2236243 : Blo 2235435 2236243 := bstep (se 1 (by rfl) ⟨1677182, by rfl⟩ : syracuseStep 2236243 = 3354365) B3354365
theorem B5031557 : Blo 2235435 5031557 := bbase (se 4 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 5031557 = 943417) (by norm_num)
theorem B3354371 : Blo 2235435 3354371 := bstep (se 1 (by rfl) ⟨2515778, by rfl⟩ : syracuseStep 3354371 = 5031557) B5031557
theorem B2236247 : Blo 2235435 2236247 := bstep (se 1 (by rfl) ⟨1677185, by rfl⟩ : syracuseStep 2236247 = 3354371) B3354371
theorem B2550109 : Blo 2235435 2550109 := bbase (se 3 (by rfl) ⟨478145, by rfl⟩ : syracuseStep 2550109 = 956291) (by norm_num)
theorem B3400145 : Blo 2235435 3400145 := bstep (se 2 (by rfl) ⟨1275054, by rfl⟩ : syracuseStep 3400145 = 2550109) B2550109
theorem B2266763 : Blo 2235435 2266763 := bstep (se 1 (by rfl) ⟨1700072, by rfl⟩ : syracuseStep 2266763 = 3400145) B3400145
theorem B6044701 : Blo 2235435 6044701 := bstep (se 3 (by rfl) ⟨1133381, by rfl⟩ : syracuseStep 6044701 = 2266763) B2266763
theorem B8059601 : Blo 2235435 8059601 := bstep (se 2 (by rfl) ⟨3022350, by rfl⟩ : syracuseStep 8059601 = 6044701) B6044701
theorem B5373067 : Blo 2235435 5373067 := bstep (se 1 (by rfl) ⟨4029800, by rfl⟩ : syracuseStep 5373067 = 8059601) B8059601
theorem B7164089 : Blo 2235435 7164089 := bstep (se 2 (by rfl) ⟨2686533, by rfl⟩ : syracuseStep 7164089 = 5373067) B5373067
theorem B4776059 : Blo 2235435 4776059 := bstep (se 1 (by rfl) ⟨3582044, by rfl⟩ : syracuseStep 4776059 = 7164089) B7164089
theorem B3184039 : Blo 2235435 3184039 := bstep (se 1 (by rfl) ⟨2388029, by rfl⟩ : syracuseStep 3184039 = 4776059) B4776059
theorem B4245385 : Blo 2235435 4245385 := bstep (se 2 (by rfl) ⟨1592019, by rfl⟩ : syracuseStep 4245385 = 3184039) B3184039
theorem B5660513 : Blo 2235435 5660513 := bstep (se 2 (by rfl) ⟨2122692, by rfl⟩ : syracuseStep 5660513 = 4245385) B4245385
theorem B3773675 : Blo 2235435 3773675 := bstep (se 1 (by rfl) ⟨2830256, by rfl⟩ : syracuseStep 3773675 = 5660513) B5660513
theorem B2515783 : Blo 2235435 2515783 := bstep (se 1 (by rfl) ⟨1886837, by rfl⟩ : syracuseStep 2515783 = 3773675) B3773675
theorem B3354377 : Blo 2235435 3354377 := bstep (se 2 (by rfl) ⟨1257891, by rfl⟩ : syracuseStep 3354377 = 2515783) B2515783
theorem B2236251 : Blo 2235435 2236251 := bstep (se 1 (by rfl) ⟨1677188, by rfl⟩ : syracuseStep 2236251 = 3354377) B3354377
theorem B11321045 : Blo 2235435 11321045 := bbase (se 7 (by rfl) ⟨132668, by rfl⟩ : syracuseStep 11321045 = 265337) (by norm_num)
theorem B7547363 : Blo 2235435 7547363 := bstep (se 1 (by rfl) ⟨5660522, by rfl⟩ : syracuseStep 7547363 = 11321045) B11321045
theorem B5031575 : Blo 2235435 5031575 := bstep (se 1 (by rfl) ⟨3773681, by rfl⟩ : syracuseStep 5031575 = 7547363) B7547363
theorem B3354383 : Blo 2235435 3354383 := bstep (se 1 (by rfl) ⟨2515787, by rfl⟩ : syracuseStep 3354383 = 5031575) B5031575
theorem B2236255 : Blo 2235435 2236255 := bstep (se 1 (by rfl) ⟨1677191, by rfl⟩ : syracuseStep 2236255 = 3354383) B3354383
theorem B3354389 : Blo 2235435 3354389 := bbase (se 6 (by rfl) ⟨78618, by rfl⟩ : syracuseStep 3354389 = 157237) (by norm_num)
theorem B2236259 : Blo 2235435 2236259 := bstep (se 1 (by rfl) ⟨1677194, by rfl⟩ : syracuseStep 2236259 = 3354389) B3354389
theorem B10200485 : Blo 2235435 10200485 := bbase (se 4 (by rfl) ⟨956295, by rfl⟩ : syracuseStep 10200485 = 1912591) (by norm_num)
theorem B6800323 : Blo 2235435 6800323 := bstep (se 1 (by rfl) ⟨5100242, by rfl⟩ : syracuseStep 6800323 = 10200485) B10200485
theorem B9067097 : Blo 2235435 9067097 := bstep (se 2 (by rfl) ⟨3400161, by rfl⟩ : syracuseStep 9067097 = 6800323) B6800323
theorem B24178925 : Blo 2235435 24178925 := bstep (se 3 (by rfl) ⟨4533548, by rfl⟩ : syracuseStep 24178925 = 9067097) B9067097
theorem B64477133 : Blo 2235435 64477133 := bstep (se 3 (by rfl) ⟨12089462, by rfl⟩ : syracuseStep 64477133 = 24178925) B24178925
theorem B42984755 : Blo 2235435 42984755 := bstep (se 1 (by rfl) ⟨32238566, by rfl⟩ : syracuseStep 42984755 = 64477133) B64477133
theorem B28656503 : Blo 2235435 28656503 := bstep (se 1 (by rfl) ⟨21492377, by rfl⟩ : syracuseStep 28656503 = 42984755) B42984755
theorem B19104335 : Blo 2235435 19104335 := bstep (se 1 (by rfl) ⟨14328251, by rfl⟩ : syracuseStep 19104335 = 28656503) B28656503
theorem B12736223 : Blo 2235435 12736223 := bstep (se 1 (by rfl) ⟨9552167, by rfl⟩ : syracuseStep 12736223 = 19104335) B19104335
theorem B8490815 : Blo 2235435 8490815 := bstep (se 1 (by rfl) ⟨6368111, by rfl⟩ : syracuseStep 8490815 = 12736223) B12736223
theorem B5660543 : Blo 2235435 5660543 := bstep (se 1 (by rfl) ⟨4245407, by rfl⟩ : syracuseStep 5660543 = 8490815) B8490815
theorem B3773695 : Blo 2235435 3773695 := bstep (se 1 (by rfl) ⟨2830271, by rfl⟩ : syracuseStep 3773695 = 5660543) B5660543
theorem B5031593 : Blo 2235435 5031593 := bstep (se 2 (by rfl) ⟨1886847, by rfl⟩ : syracuseStep 5031593 = 3773695) B3773695
theorem B3354395 : Blo 2235435 3354395 := bstep (se 1 (by rfl) ⟨2515796, by rfl⟩ : syracuseStep 3354395 = 5031593) B5031593
theorem B2236263 : Blo 2235435 2236263 := bstep (se 1 (by rfl) ⟨1677197, by rfl⟩ : syracuseStep 2236263 = 3354395) B3354395
theorem B2515801 : Blo 2235435 2515801 := bbase (se 2 (by rfl) ⟨943425, by rfl⟩ : syracuseStep 2515801 = 1886851) (by norm_num)
theorem B3354401 : Blo 2235435 3354401 := bstep (se 2 (by rfl) ⟨1257900, by rfl⟩ : syracuseStep 3354401 = 2515801) B2515801
theorem B2236267 : Blo 2235435 2236267 := bstep (se 1 (by rfl) ⟨1677200, by rfl⟩ : syracuseStep 2236267 = 3354401) B3354401
theorem B4776101 : Blo 2235435 4776101 := bbase (se 4 (by rfl) ⟨447759, by rfl⟩ : syracuseStep 4776101 = 895519) (by norm_num)
theorem B3184067 : Blo 2235435 3184067 := bstep (se 1 (by rfl) ⟨2388050, by rfl⟩ : syracuseStep 3184067 = 4776101) B4776101
theorem B8490845 : Blo 2235435 8490845 := bstep (se 3 (by rfl) ⟨1592033, by rfl⟩ : syracuseStep 8490845 = 3184067) B3184067
theorem B5660563 : Blo 2235435 5660563 := bstep (se 1 (by rfl) ⟨4245422, by rfl⟩ : syracuseStep 5660563 = 8490845) B8490845
theorem B7547417 : Blo 2235435 7547417 := bstep (se 2 (by rfl) ⟨2830281, by rfl⟩ : syracuseStep 7547417 = 5660563) B5660563
theorem B5031611 : Blo 2235435 5031611 := bstep (se 1 (by rfl) ⟨3773708, by rfl⟩ : syracuseStep 5031611 = 7547417) B7547417
theorem B3354407 : Blo 2235435 3354407 := bstep (se 1 (by rfl) ⟨2515805, by rfl⟩ : syracuseStep 3354407 = 5031611) B5031611
theorem B2236271 : Blo 2235435 2236271 := bstep (se 1 (by rfl) ⟨1677203, by rfl⟩ : syracuseStep 2236271 = 3354407) B3354407
theorem B3354413 : Blo 2235435 3354413 := bbase (se 3 (by rfl) ⟨628952, by rfl⟩ : syracuseStep 3354413 = 1257905) (by norm_num)
theorem B2236275 : Blo 2235435 2236275 := bstep (se 1 (by rfl) ⟨1677206, by rfl⟩ : syracuseStep 2236275 = 3354413) B3354413
theorem B5031629 : Blo 2235435 5031629 := bbase (se 3 (by rfl) ⟨943430, by rfl⟩ : syracuseStep 5031629 = 1886861) (by norm_num)
theorem B3354419 : Blo 2235435 3354419 := bstep (se 1 (by rfl) ⟨2515814, by rfl⟩ : syracuseStep 3354419 = 5031629) B5031629
theorem B2236279 : Blo 2235435 2236279 := bstep (se 1 (by rfl) ⟨1677209, by rfl⟩ : syracuseStep 2236279 = 3354419) B3354419
theorem B2830297 : Blo 2235435 2830297 := bbase (se 2 (by rfl) ⟨1061361, by rfl⟩ : syracuseStep 2830297 = 2122723) (by norm_num)
theorem B3773729 : Blo 2235435 3773729 := bstep (se 2 (by rfl) ⟨1415148, by rfl⟩ : syracuseStep 3773729 = 2830297) B2830297
theorem B2515819 : Blo 2235435 2515819 := bstep (se 1 (by rfl) ⟨1886864, by rfl⟩ : syracuseStep 2515819 = 3773729) B3773729
theorem B3354425 : Blo 2235435 3354425 := bstep (se 2 (by rfl) ⟨1257909, by rfl⟩ : syracuseStep 3354425 = 2515819) B2515819
theorem B2236283 : Blo 2235435 2236283 := bstep (se 1 (by rfl) ⟨1677212, by rfl⟩ : syracuseStep 2236283 = 3354425) B3354425
theorem B3582101 : Blo 2235435 3582101 := bbase (se 6 (by rfl) ⟨83955, by rfl⟩ : syracuseStep 3582101 = 167911) (by norm_num)
theorem B9552269 : Blo 2235435 9552269 := bstep (se 3 (by rfl) ⟨1791050, by rfl⟩ : syracuseStep 9552269 = 3582101) B3582101
theorem B25472717 : Blo 2235435 25472717 := bstep (se 3 (by rfl) ⟨4776134, by rfl⟩ : syracuseStep 25472717 = 9552269) B9552269
theorem B16981811 : Blo 2235435 16981811 := bstep (se 1 (by rfl) ⟨12736358, by rfl⟩ : syracuseStep 16981811 = 25472717) B25472717
theorem B11321207 : Blo 2235435 11321207 := bstep (se 1 (by rfl) ⟨8490905, by rfl⟩ : syracuseStep 11321207 = 16981811) B16981811
theorem B7547471 : Blo 2235435 7547471 := bstep (se 1 (by rfl) ⟨5660603, by rfl⟩ : syracuseStep 7547471 = 11321207) B11321207
theorem B5031647 : Blo 2235435 5031647 := bstep (se 1 (by rfl) ⟨3773735, by rfl⟩ : syracuseStep 5031647 = 7547471) B7547471
theorem B3354431 : Blo 2235435 3354431 := bstep (se 1 (by rfl) ⟨2515823, by rfl⟩ : syracuseStep 3354431 = 5031647) B5031647
theorem B2236287 : Blo 2235435 2236287 := bstep (se 1 (by rfl) ⟨1677215, by rfl⟩ : syracuseStep 2236287 = 3354431) B3354431
theorem B3354437 : Blo 2235435 3354437 := bbase (se 4 (by rfl) ⟨314478, by rfl⟩ : syracuseStep 3354437 = 628957) (by norm_num)
theorem B2236291 : Blo 2235435 2236291 := bstep (se 1 (by rfl) ⟨1677218, by rfl⟩ : syracuseStep 2236291 = 3354437) B3354437
theorem B3773749 : Blo 2235435 3773749 := bbase (se 5 (by rfl) ⟨176894, by rfl⟩ : syracuseStep 3773749 = 353789) (by norm_num)
theorem B5031665 : Blo 2235435 5031665 := bstep (se 2 (by rfl) ⟨1886874, by rfl⟩ : syracuseStep 5031665 = 3773749) B3773749
theorem B3354443 : Blo 2235435 3354443 := bstep (se 1 (by rfl) ⟨2515832, by rfl⟩ : syracuseStep 3354443 = 5031665) B5031665
theorem B2236295 : Blo 2235435 2236295 := bstep (se 1 (by rfl) ⟨1677221, by rfl⟩ : syracuseStep 2236295 = 3354443) B3354443
theorem B2515837 : Blo 2235435 2515837 := bbase (se 3 (by rfl) ⟨471719, by rfl⟩ : syracuseStep 2515837 = 943439) (by norm_num)
theorem B3354449 : Blo 2235435 3354449 := bstep (se 2 (by rfl) ⟨1257918, by rfl⟩ : syracuseStep 3354449 = 2515837) B2515837
theorem B2236299 : Blo 2235435 2236299 := bstep (se 1 (by rfl) ⟨1677224, by rfl⟩ : syracuseStep 2236299 = 3354449) B3354449
theorem B7547525 : Blo 2235435 7547525 := bbase (se 4 (by rfl) ⟨707580, by rfl⟩ : syracuseStep 7547525 = 1415161) (by norm_num)
theorem B5031683 : Blo 2235435 5031683 := bstep (se 1 (by rfl) ⟨3773762, by rfl⟩ : syracuseStep 5031683 = 7547525) B7547525
theorem B3354455 : Blo 2235435 3354455 := bstep (se 1 (by rfl) ⟨2515841, by rfl⟩ : syracuseStep 3354455 = 5031683) B5031683
theorem B2236303 : Blo 2235435 2236303 := bstep (se 1 (by rfl) ⟨1677227, by rfl⟩ : syracuseStep 2236303 = 3354455) B3354455
theorem B3354461 : Blo 2235435 3354461 := bbase (se 3 (by rfl) ⟨628961, by rfl⟩ : syracuseStep 3354461 = 1257923) (by norm_num)
theorem B2236307 : Blo 2235435 2236307 := bstep (se 1 (by rfl) ⟨1677230, by rfl⟩ : syracuseStep 2236307 = 3354461) B3354461
theorem B5031701 : Blo 2235435 5031701 := bbase (se 6 (by rfl) ⟨117930, by rfl⟩ : syracuseStep 5031701 = 235861) (by norm_num)
theorem B3354467 : Blo 2235435 3354467 := bstep (se 1 (by rfl) ⟨2515850, by rfl⟩ : syracuseStep 3354467 = 5031701) B5031701
theorem B2236311 : Blo 2235435 2236311 := bstep (se 1 (by rfl) ⟨1677233, by rfl⟩ : syracuseStep 2236311 = 3354467) B3354467
theorem B8491013 : Blo 2235435 8491013 := bbase (se 4 (by rfl) ⟨796032, by rfl⟩ : syracuseStep 8491013 = 1592065) (by norm_num)
theorem B5660675 : Blo 2235435 5660675 := bstep (se 1 (by rfl) ⟨4245506, by rfl⟩ : syracuseStep 5660675 = 8491013) B8491013
theorem B3773783 : Blo 2235435 3773783 := bstep (se 1 (by rfl) ⟨2830337, by rfl⟩ : syracuseStep 3773783 = 5660675) B5660675
theorem B2515855 : Blo 2235435 2515855 := bstep (se 1 (by rfl) ⟨1886891, by rfl⟩ : syracuseStep 2515855 = 3773783) B3773783
theorem B3354473 : Blo 2235435 3354473 := bstep (se 2 (by rfl) ⟨1257927, by rfl⟩ : syracuseStep 3354473 = 2515855) B2515855
theorem B2236315 : Blo 2235435 2236315 := bstep (se 1 (by rfl) ⟨1677236, by rfl⟩ : syracuseStep 2236315 = 3354473) B3354473
theorem B5373229 : Blo 2235435 5373229 := bbase (se 3 (by rfl) ⟨1007480, by rfl⟩ : syracuseStep 5373229 = 2014961) (by norm_num)
theorem B7164305 : Blo 2235435 7164305 := bstep (se 2 (by rfl) ⟨2686614, by rfl⟩ : syracuseStep 7164305 = 5373229) B5373229
theorem B4776203 : Blo 2235435 4776203 := bstep (se 1 (by rfl) ⟨3582152, by rfl⟩ : syracuseStep 4776203 = 7164305) B7164305
theorem B12736541 : Blo 2235435 12736541 := bstep (se 3 (by rfl) ⟨2388101, by rfl⟩ : syracuseStep 12736541 = 4776203) B4776203
theorem B8491027 : Blo 2235435 8491027 := bstep (se 1 (by rfl) ⟨6368270, by rfl⟩ : syracuseStep 8491027 = 12736541) B12736541
theorem B11321369 : Blo 2235435 11321369 := bstep (se 2 (by rfl) ⟨4245513, by rfl⟩ : syracuseStep 11321369 = 8491027) B8491027
theorem B7547579 : Blo 2235435 7547579 := bstep (se 1 (by rfl) ⟨5660684, by rfl⟩ : syracuseStep 7547579 = 11321369) B11321369
theorem B5031719 : Blo 2235435 5031719 := bstep (se 1 (by rfl) ⟨3773789, by rfl⟩ : syracuseStep 5031719 = 7547579) B7547579
theorem B3354479 : Blo 2235435 3354479 := bstep (se 1 (by rfl) ⟨2515859, by rfl⟩ : syracuseStep 3354479 = 5031719) B5031719
theorem B2236319 : Blo 2235435 2236319 := bstep (se 1 (by rfl) ⟨1677239, by rfl⟩ : syracuseStep 2236319 = 3354479) B3354479
theorem B3354485 : Blo 2235435 3354485 := bbase (se 5 (by rfl) ⟨157241, by rfl⟩ : syracuseStep 3354485 = 314483) (by norm_num)
theorem B2236323 : Blo 2235435 2236323 := bstep (se 1 (by rfl) ⟨1677242, by rfl⟩ : syracuseStep 2236323 = 3354485) B3354485
theorem B4776221 : Blo 2235435 4776221 := bbase (se 3 (by rfl) ⟨895541, by rfl⟩ : syracuseStep 4776221 = 1791083) (by norm_num)
theorem B3184147 : Blo 2235435 3184147 := bstep (se 1 (by rfl) ⟨2388110, by rfl⟩ : syracuseStep 3184147 = 4776221) B4776221
theorem B4245529 : Blo 2235435 4245529 := bstep (se 2 (by rfl) ⟨1592073, by rfl⟩ : syracuseStep 4245529 = 3184147) B3184147
theorem B5660705 : Blo 2235435 5660705 := bstep (se 2 (by rfl) ⟨2122764, by rfl⟩ : syracuseStep 5660705 = 4245529) B4245529
theorem B3773803 : Blo 2235435 3773803 := bstep (se 1 (by rfl) ⟨2830352, by rfl⟩ : syracuseStep 3773803 = 5660705) B5660705
theorem B5031737 : Blo 2235435 5031737 := bstep (se 2 (by rfl) ⟨1886901, by rfl⟩ : syracuseStep 5031737 = 3773803) B3773803
theorem B3354491 : Blo 2235435 3354491 := bstep (se 1 (by rfl) ⟨2515868, by rfl⟩ : syracuseStep 3354491 = 5031737) B5031737
theorem B2236327 : Blo 2235435 2236327 := bstep (se 1 (by rfl) ⟨1677245, by rfl⟩ : syracuseStep 2236327 = 3354491) B3354491
theorem B2515873 : Blo 2235435 2515873 := bbase (se 2 (by rfl) ⟨943452, by rfl⟩ : syracuseStep 2515873 = 1886905) (by norm_num)
theorem B3354497 : Blo 2235435 3354497 := bstep (se 2 (by rfl) ⟨1257936, by rfl⟩ : syracuseStep 3354497 = 2515873) B2515873
theorem B2236331 : Blo 2235435 2236331 := bstep (se 1 (by rfl) ⟨1677248, by rfl⟩ : syracuseStep 2236331 = 3354497) B3354497
theorem B5660725 : Blo 2235435 5660725 := bbase (se 5 (by rfl) ⟨265346, by rfl⟩ : syracuseStep 5660725 = 530693) (by norm_num)
theorem B7547633 : Blo 2235435 7547633 := bstep (se 2 (by rfl) ⟨2830362, by rfl⟩ : syracuseStep 7547633 = 5660725) B5660725
theorem B5031755 : Blo 2235435 5031755 := bstep (se 1 (by rfl) ⟨3773816, by rfl⟩ : syracuseStep 5031755 = 7547633) B7547633
theorem B3354503 : Blo 2235435 3354503 := bstep (se 1 (by rfl) ⟨2515877, by rfl⟩ : syracuseStep 3354503 = 5031755) B5031755
theorem B2236335 : Blo 2235435 2236335 := bstep (se 1 (by rfl) ⟨1677251, by rfl⟩ : syracuseStep 2236335 = 3354503) B3354503
theorem B3354509 : Blo 2235435 3354509 := bbase (se 3 (by rfl) ⟨628970, by rfl⟩ : syracuseStep 3354509 = 1257941) (by norm_num)
theorem B2236339 : Blo 2235435 2236339 := bstep (se 1 (by rfl) ⟨1677254, by rfl⟩ : syracuseStep 2236339 = 3354509) B3354509
theorem B5031773 : Blo 2235435 5031773 := bbase (se 3 (by rfl) ⟨943457, by rfl⟩ : syracuseStep 5031773 = 1886915) (by norm_num)
theorem B3354515 : Blo 2235435 3354515 := bstep (se 1 (by rfl) ⟨2515886, by rfl⟩ : syracuseStep 3354515 = 5031773) B5031773
theorem B2236343 : Blo 2235435 2236343 := bstep (se 1 (by rfl) ⟨1677257, by rfl⟩ : syracuseStep 2236343 = 3354515) B3354515
theorem B3773837 : Blo 2235435 3773837 := bbase (se 3 (by rfl) ⟨707594, by rfl⟩ : syracuseStep 3773837 = 1415189) (by norm_num)
theorem B2515891 : Blo 2235435 2515891 := bstep (se 1 (by rfl) ⟨1886918, by rfl⟩ : syracuseStep 2515891 = 3773837) B3773837
theorem B3354521 : Blo 2235435 3354521 := bstep (se 2 (by rfl) ⟨1257945, by rfl⟩ : syracuseStep 3354521 = 2515891) B2515891
theorem B2236347 : Blo 2235435 2236347 := bstep (se 1 (by rfl) ⟨1677260, by rfl⟩ : syracuseStep 2236347 = 3354521) B3354521
theorem B19365749 : Blo 2235435 19365749 := bbase (se 5 (by rfl) ⟨907769, by rfl⟩ : syracuseStep 19365749 = 1815539) (by norm_num)
theorem B12910499 : Blo 2235435 12910499 := bstep (se 1 (by rfl) ⟨9682874, by rfl⟩ : syracuseStep 12910499 = 19365749) B19365749
theorem B8606999 : Blo 2235435 8606999 := bstep (se 1 (by rfl) ⟨6455249, by rfl⟩ : syracuseStep 8606999 = 12910499) B12910499
theorem B22951997 : Blo 2235435 22951997 := bstep (se 3 (by rfl) ⟨4303499, by rfl⟩ : syracuseStep 22951997 = 8606999) B8606999
theorem B15301331 : Blo 2235435 15301331 := bstep (se 1 (by rfl) ⟨11475998, by rfl⟩ : syracuseStep 15301331 = 22951997) B22951997
theorem B10200887 : Blo 2235435 10200887 := bstep (se 1 (by rfl) ⟨7650665, by rfl⟩ : syracuseStep 10200887 = 15301331) B15301331
theorem B6800591 : Blo 2235435 6800591 := bstep (se 1 (by rfl) ⟨5100443, by rfl⟩ : syracuseStep 6800591 = 10200887) B10200887
theorem B4533727 : Blo 2235435 4533727 := bstep (se 1 (by rfl) ⟨3400295, by rfl⟩ : syracuseStep 4533727 = 6800591) B6800591
theorem B6044969 : Blo 2235435 6044969 := bstep (se 2 (by rfl) ⟨2266863, by rfl⟩ : syracuseStep 6044969 = 4533727) B4533727
theorem B16119917 : Blo 2235435 16119917 := bstep (se 3 (by rfl) ⟨3022484, by rfl⟩ : syracuseStep 16119917 = 6044969) B6044969
theorem B10746611 : Blo 2235435 10746611 := bstep (se 1 (by rfl) ⟨8059958, by rfl⟩ : syracuseStep 10746611 = 16119917) B16119917
theorem B7164407 : Blo 2235435 7164407 := bstep (se 1 (by rfl) ⟨5373305, by rfl⟩ : syracuseStep 7164407 = 10746611) B10746611
theorem B19105085 : Blo 2235435 19105085 := bstep (se 3 (by rfl) ⟨3582203, by rfl⟩ : syracuseStep 19105085 = 7164407) B7164407
theorem B12736723 : Blo 2235435 12736723 := bstep (se 1 (by rfl) ⟨9552542, by rfl⟩ : syracuseStep 12736723 = 19105085) B19105085
theorem B16982297 : Blo 2235435 16982297 := bstep (se 2 (by rfl) ⟨6368361, by rfl⟩ : syracuseStep 16982297 = 12736723) B12736723
theorem B11321531 : Blo 2235435 11321531 := bstep (se 1 (by rfl) ⟨8491148, by rfl⟩ : syracuseStep 11321531 = 16982297) B16982297
theorem B7547687 : Blo 2235435 7547687 := bstep (se 1 (by rfl) ⟨5660765, by rfl⟩ : syracuseStep 7547687 = 11321531) B11321531
theorem B5031791 : Blo 2235435 5031791 := bstep (se 1 (by rfl) ⟨3773843, by rfl⟩ : syracuseStep 5031791 = 7547687) B7547687
theorem B3354527 : Blo 2235435 3354527 := bstep (se 1 (by rfl) ⟨2515895, by rfl⟩ : syracuseStep 3354527 = 5031791) B5031791
theorem B2236351 : Blo 2235435 2236351 := bstep (se 1 (by rfl) ⟨1677263, by rfl⟩ : syracuseStep 2236351 = 3354527) B3354527
theorem B3354533 : Blo 2235435 3354533 := bbase (se 4 (by rfl) ⟨314487, by rfl⟩ : syracuseStep 3354533 = 628975) (by norm_num)
theorem B2236355 : Blo 2235435 2236355 := bstep (se 1 (by rfl) ⟨1677266, by rfl⟩ : syracuseStep 2236355 = 3354533) B3354533
theorem B2830393 : Blo 2235435 2830393 := bbase (se 2 (by rfl) ⟨1061397, by rfl⟩ : syracuseStep 2830393 = 2122795) (by norm_num)
theorem B3773857 : Blo 2235435 3773857 := bstep (se 2 (by rfl) ⟨1415196, by rfl⟩ : syracuseStep 3773857 = 2830393) B2830393
theorem B5031809 : Blo 2235435 5031809 := bstep (se 2 (by rfl) ⟨1886928, by rfl⟩ : syracuseStep 5031809 = 3773857) B3773857
theorem B3354539 : Blo 2235435 3354539 := bstep (se 1 (by rfl) ⟨2515904, by rfl⟩ : syracuseStep 3354539 = 5031809) B5031809
theorem B2236359 : Blo 2235435 2236359 := bstep (se 1 (by rfl) ⟨1677269, by rfl⟩ : syracuseStep 2236359 = 3354539) B3354539
theorem B2515909 : Blo 2235435 2515909 := bbase (se 4 (by rfl) ⟨235866, by rfl⟩ : syracuseStep 2515909 = 471733) (by norm_num)
theorem B3354545 : Blo 2235435 3354545 := bstep (se 2 (by rfl) ⟨1257954, by rfl⟩ : syracuseStep 3354545 = 2515909) B2515909
theorem B2236363 : Blo 2235435 2236363 := bstep (se 1 (by rfl) ⟨1677272, by rfl⟩ : syracuseStep 2236363 = 3354545) B3354545
theorem B4245605 : Blo 2235435 4245605 := bbase (se 4 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 4245605 = 796051) (by norm_num)
theorem B2830403 : Blo 2235435 2830403 := bstep (se 1 (by rfl) ⟨2122802, by rfl⟩ : syracuseStep 2830403 = 4245605) B4245605
theorem B7547741 : Blo 2235435 7547741 := bstep (se 3 (by rfl) ⟨1415201, by rfl⟩ : syracuseStep 7547741 = 2830403) B2830403
theorem B5031827 : Blo 2235435 5031827 := bstep (se 1 (by rfl) ⟨3773870, by rfl⟩ : syracuseStep 5031827 = 7547741) B7547741
theorem B3354551 : Blo 2235435 3354551 := bstep (se 1 (by rfl) ⟨2515913, by rfl⟩ : syracuseStep 3354551 = 5031827) B5031827
theorem B2236367 : Blo 2235435 2236367 := bstep (se 1 (by rfl) ⟨1677275, by rfl⟩ : syracuseStep 2236367 = 3354551) B3354551
theorem B3354557 : Blo 2235435 3354557 := bbase (se 3 (by rfl) ⟨628979, by rfl⟩ : syracuseStep 3354557 = 1257959) (by norm_num)
theorem B2236371 : Blo 2235435 2236371 := bstep (se 1 (by rfl) ⟨1677278, by rfl⟩ : syracuseStep 2236371 = 3354557) B3354557
theorem B5031845 : Blo 2235435 5031845 := bbase (se 4 (by rfl) ⟨471735, by rfl⟩ : syracuseStep 5031845 = 943471) (by norm_num)
theorem B3354563 : Blo 2235435 3354563 := bstep (se 1 (by rfl) ⟨2515922, by rfl⟩ : syracuseStep 3354563 = 5031845) B5031845
theorem B2236375 : Blo 2235435 2236375 := bstep (se 1 (by rfl) ⟨1677281, by rfl⟩ : syracuseStep 2236375 = 3354563) B3354563
theorem B5660837 : Blo 2235435 5660837 := bbase (se 4 (by rfl) ⟨530703, by rfl⟩ : syracuseStep 5660837 = 1061407) (by norm_num)
theorem B3773891 : Blo 2235435 3773891 := bstep (se 1 (by rfl) ⟨2830418, by rfl⟩ : syracuseStep 3773891 = 5660837) B5660837
theorem B2515927 : Blo 2235435 2515927 := bstep (se 1 (by rfl) ⟨1886945, by rfl⟩ : syracuseStep 2515927 = 3773891) B3773891
theorem B3354569 : Blo 2235435 3354569 := bstep (se 2 (by rfl) ⟨1257963, by rfl⟩ : syracuseStep 3354569 = 2515927) B2515927
theorem B2236379 : Blo 2235435 2236379 := bstep (se 1 (by rfl) ⟨1677284, by rfl⟩ : syracuseStep 2236379 = 3354569) B3354569
theorem B6368453 : Blo 2235435 6368453 := bbase (se 4 (by rfl) ⟨597042, by rfl⟩ : syracuseStep 6368453 = 1194085) (by norm_num)
theorem B4245635 : Blo 2235435 4245635 := bstep (se 1 (by rfl) ⟨3184226, by rfl⟩ : syracuseStep 4245635 = 6368453) B6368453
theorem B11321693 : Blo 2235435 11321693 := bstep (se 3 (by rfl) ⟨2122817, by rfl⟩ : syracuseStep 11321693 = 4245635) B4245635
theorem B7547795 : Blo 2235435 7547795 := bstep (se 1 (by rfl) ⟨5660846, by rfl⟩ : syracuseStep 7547795 = 11321693) B11321693
theorem B5031863 : Blo 2235435 5031863 := bstep (se 1 (by rfl) ⟨3773897, by rfl⟩ : syracuseStep 5031863 = 7547795) B7547795
theorem B3354575 : Blo 2235435 3354575 := bstep (se 1 (by rfl) ⟨2515931, by rfl⟩ : syracuseStep 3354575 = 5031863) B5031863
theorem B2236383 : Blo 2235435 2236383 := bstep (se 1 (by rfl) ⟨1677287, by rfl⟩ : syracuseStep 2236383 = 3354575) B3354575
theorem B3354581 : Blo 2235435 3354581 := bbase (se 7 (by rfl) ⟨39311, by rfl⟩ : syracuseStep 3354581 = 78623) (by norm_num)
theorem B2236387 : Blo 2235435 2236387 := bstep (se 1 (by rfl) ⟨1677290, by rfl⟩ : syracuseStep 2236387 = 3354581) B3354581
theorem B8491301 : Blo 2235435 8491301 := bbase (se 4 (by rfl) ⟨796059, by rfl⟩ : syracuseStep 8491301 = 1592119) (by norm_num)
theorem B5660867 : Blo 2235435 5660867 := bstep (se 1 (by rfl) ⟨4245650, by rfl⟩ : syracuseStep 5660867 = 8491301) B8491301
theorem B3773911 : Blo 2235435 3773911 := bstep (se 1 (by rfl) ⟨2830433, by rfl⟩ : syracuseStep 3773911 = 5660867) B5660867
theorem B5031881 : Blo 2235435 5031881 := bstep (se 2 (by rfl) ⟨1886955, by rfl⟩ : syracuseStep 5031881 = 3773911) B3773911
theorem B3354587 : Blo 2235435 3354587 := bstep (se 1 (by rfl) ⟨2515940, by rfl⟩ : syracuseStep 3354587 = 5031881) B5031881
theorem B2236391 : Blo 2235435 2236391 := bstep (se 1 (by rfl) ⟨1677293, by rfl⟩ : syracuseStep 2236391 = 3354587) B3354587
theorem B2515945 : Blo 2235435 2515945 := bbase (se 2 (by rfl) ⟨943479, by rfl⟩ : syracuseStep 2515945 = 1886959) (by norm_num)
theorem B3354593 : Blo 2235435 3354593 := bstep (se 2 (by rfl) ⟨1257972, by rfl⟩ : syracuseStep 3354593 = 2515945) B2515945
theorem B2236395 : Blo 2235435 2236395 := bstep (se 1 (by rfl) ⟨1677296, by rfl⟩ : syracuseStep 2236395 = 3354593) B3354593
theorem B2266913 : Blo 2235435 2266913 := bbase (se 2 (by rfl) ⟨850092, by rfl⟩ : syracuseStep 2266913 = 1700185) (by norm_num)
theorem B6045101 : Blo 2235435 6045101 := bstep (se 3 (by rfl) ⟨1133456, by rfl⟩ : syracuseStep 6045101 = 2266913) B2266913
theorem B4030067 : Blo 2235435 4030067 := bstep (se 1 (by rfl) ⟨3022550, by rfl⟩ : syracuseStep 4030067 = 6045101) B6045101
theorem B2686711 : Blo 2235435 2686711 := bstep (se 1 (by rfl) ⟨2015033, by rfl⟩ : syracuseStep 2686711 = 4030067) B4030067
theorem B3582281 : Blo 2235435 3582281 := bstep (se 2 (by rfl) ⟨1343355, by rfl⟩ : syracuseStep 3582281 = 2686711) B2686711
theorem B2388187 : Blo 2235435 2388187 := bstep (se 1 (by rfl) ⟨1791140, by rfl⟩ : syracuseStep 2388187 = 3582281) B3582281
theorem B12736997 : Blo 2235435 12736997 := bstep (se 4 (by rfl) ⟨1194093, by rfl⟩ : syracuseStep 12736997 = 2388187) B2388187
theorem B8491331 : Blo 2235435 8491331 := bstep (se 1 (by rfl) ⟨6368498, by rfl⟩ : syracuseStep 8491331 = 12736997) B12736997
theorem B5660887 : Blo 2235435 5660887 := bstep (se 1 (by rfl) ⟨4245665, by rfl⟩ : syracuseStep 5660887 = 8491331) B8491331
theorem B7547849 : Blo 2235435 7547849 := bstep (se 2 (by rfl) ⟨2830443, by rfl⟩ : syracuseStep 7547849 = 5660887) B5660887
theorem B5031899 : Blo 2235435 5031899 := bstep (se 1 (by rfl) ⟨3773924, by rfl⟩ : syracuseStep 5031899 = 7547849) B7547849
theorem B3354599 : Blo 2235435 3354599 := bstep (se 1 (by rfl) ⟨2515949, by rfl⟩ : syracuseStep 3354599 = 5031899) B5031899
theorem B2236399 : Blo 2235435 2236399 := bstep (se 1 (by rfl) ⟨1677299, by rfl⟩ : syracuseStep 2236399 = 3354599) B3354599
theorem B3354605 : Blo 2235435 3354605 := bbase (se 3 (by rfl) ⟨628988, by rfl⟩ : syracuseStep 3354605 = 1257977) (by norm_num)
theorem B2236403 : Blo 2235435 2236403 := bstep (se 1 (by rfl) ⟨1677302, by rfl⟩ : syracuseStep 2236403 = 3354605) B3354605
theorem B5031917 : Blo 2235435 5031917 := bbase (se 3 (by rfl) ⟨943484, by rfl⟩ : syracuseStep 5031917 = 1886969) (by norm_num)
theorem B3354611 : Blo 2235435 3354611 := bstep (se 1 (by rfl) ⟨2515958, by rfl⟩ : syracuseStep 3354611 = 5031917) B5031917
theorem B2236407 : Blo 2235435 2236407 := bstep (se 1 (by rfl) ⟨1677305, by rfl⟩ : syracuseStep 2236407 = 3354611) B3354611
theorem B3582301 : Blo 2235435 3582301 := bbase (se 3 (by rfl) ⟨671681, by rfl⟩ : syracuseStep 3582301 = 1343363) (by norm_num)
theorem B4776401 : Blo 2235435 4776401 := bstep (se 2 (by rfl) ⟨1791150, by rfl⟩ : syracuseStep 4776401 = 3582301) B3582301
theorem B3184267 : Blo 2235435 3184267 := bstep (se 1 (by rfl) ⟨2388200, by rfl⟩ : syracuseStep 3184267 = 4776401) B4776401
theorem B4245689 : Blo 2235435 4245689 := bstep (se 2 (by rfl) ⟨1592133, by rfl⟩ : syracuseStep 4245689 = 3184267) B3184267
theorem B2830459 : Blo 2235435 2830459 := bstep (se 1 (by rfl) ⟨2122844, by rfl⟩ : syracuseStep 2830459 = 4245689) B4245689
theorem B3773945 : Blo 2235435 3773945 := bstep (se 2 (by rfl) ⟨1415229, by rfl⟩ : syracuseStep 3773945 = 2830459) B2830459
theorem B2515963 : Blo 2235435 2515963 := bstep (se 1 (by rfl) ⟨1886972, by rfl⟩ : syracuseStep 2515963 = 3773945) B3773945
theorem B3354617 : Blo 2235435 3354617 := bstep (se 2 (by rfl) ⟨1257981, by rfl⟩ : syracuseStep 3354617 = 2515963) B2515963
theorem B2236411 : Blo 2235435 2236411 := bstep (se 1 (by rfl) ⟨1677308, by rfl⟩ : syracuseStep 2236411 = 3354617) B3354617
theorem B2908225 : Blo 2235435 2908225 := bbase (se 2 (by rfl) ⟨1090584, by rfl⟩ : syracuseStep 2908225 = 2181169) (by norm_num)
theorem B3877633 : Blo 2235435 3877633 := bstep (se 2 (by rfl) ⟨1454112, by rfl⟩ : syracuseStep 3877633 = 2908225) B2908225
theorem B5170177 : Blo 2235435 5170177 := bstep (se 2 (by rfl) ⟨1938816, by rfl⟩ : syracuseStep 5170177 = 3877633) B3877633
theorem B27574277 : Blo 2235435 27574277 := bstep (se 4 (by rfl) ⟨2585088, by rfl⟩ : syracuseStep 27574277 = 5170177) B5170177
theorem B73531405 : Blo 2235435 73531405 := bstep (se 3 (by rfl) ⟨13787138, by rfl⟩ : syracuseStep 73531405 = 27574277) B27574277
theorem B98041873 : Blo 2235435 98041873 := bstep (se 2 (by rfl) ⟨36765702, by rfl⟩ : syracuseStep 98041873 = 73531405) B73531405
theorem B130722497 : Blo 2235435 130722497 := bstep (se 2 (by rfl) ⟨49020936, by rfl⟩ : syracuseStep 130722497 = 98041873) B98041873
theorem B87148331 : Blo 2235435 87148331 := bstep (se 1 (by rfl) ⟨65361248, by rfl⟩ : syracuseStep 87148331 = 130722497) B130722497
theorem B58098887 : Blo 2235435 58098887 := bstep (se 1 (by rfl) ⟨43574165, by rfl⟩ : syracuseStep 58098887 = 87148331) B87148331
theorem B38732591 : Blo 2235435 38732591 := bstep (se 1 (by rfl) ⟨29049443, by rfl⟩ : syracuseStep 38732591 = 58098887) B58098887
theorem B103286909 : Blo 2235435 103286909 := bstep (se 3 (by rfl) ⟨19366295, by rfl⟩ : syracuseStep 103286909 = 38732591) B38732591
theorem B68857939 : Blo 2235435 68857939 := bstep (se 1 (by rfl) ⟨51643454, by rfl⟩ : syracuseStep 68857939 = 103286909) B103286909
theorem B91810585 : Blo 2235435 91810585 := bstep (se 2 (by rfl) ⟨34428969, by rfl⟩ : syracuseStep 91810585 = 68857939) B68857939
theorem B122414113 : Blo 2235435 122414113 := bstep (se 2 (by rfl) ⟨45905292, by rfl⟩ : syracuseStep 122414113 = 91810585) B91810585
theorem B163218817 : Blo 2235435 163218817 := bstep (se 2 (by rfl) ⟨61207056, by rfl⟩ : syracuseStep 163218817 = 122414113) B122414113
theorem B217625089 : Blo 2235435 217625089 := bstep (se 2 (by rfl) ⟨81609408, by rfl⟩ : syracuseStep 217625089 = 163218817) B163218817
theorem B290166785 : Blo 2235435 290166785 := bstep (se 2 (by rfl) ⟨108812544, by rfl⟩ : syracuseStep 290166785 = 217625089) B217625089
theorem B193444523 : Blo 2235435 193444523 := bstep (se 1 (by rfl) ⟨145083392, by rfl⟩ : syracuseStep 193444523 = 290166785) B290166785
theorem B128963015 : Blo 2235435 128963015 := bstep (se 1 (by rfl) ⟨96722261, by rfl⟩ : syracuseStep 128963015 = 193444523) B193444523
theorem B85975343 : Blo 2235435 85975343 := bstep (se 1 (by rfl) ⟨64481507, by rfl⟩ : syracuseStep 85975343 = 128963015) B128963015
theorem B57316895 : Blo 2235435 57316895 := bstep (se 1 (by rfl) ⟨42987671, by rfl⟩ : syracuseStep 57316895 = 85975343) B85975343
theorem B38211263 : Blo 2235435 38211263 := bstep (se 1 (by rfl) ⟨28658447, by rfl⟩ : syracuseStep 38211263 = 57316895) B57316895
theorem B25474175 : Blo 2235435 25474175 := bstep (se 1 (by rfl) ⟨19105631, by rfl⟩ : syracuseStep 25474175 = 38211263) B38211263
theorem B16982783 : Blo 2235435 16982783 := bstep (se 1 (by rfl) ⟨12737087, by rfl⟩ : syracuseStep 16982783 = 25474175) B25474175
theorem B11321855 : Blo 2235435 11321855 := bstep (se 1 (by rfl) ⟨8491391, by rfl⟩ : syracuseStep 11321855 = 16982783) B16982783
theorem B7547903 : Blo 2235435 7547903 := bstep (se 1 (by rfl) ⟨5660927, by rfl⟩ : syracuseStep 7547903 = 11321855) B11321855
theorem B5031935 : Blo 2235435 5031935 := bstep (se 1 (by rfl) ⟨3773951, by rfl⟩ : syracuseStep 5031935 = 7547903) B7547903
theorem B3354623 : Blo 2235435 3354623 := bstep (se 1 (by rfl) ⟨2515967, by rfl⟩ : syracuseStep 3354623 = 5031935) B5031935
theorem B2236415 : Blo 2235435 2236415 := bstep (se 1 (by rfl) ⟨1677311, by rfl⟩ : syracuseStep 2236415 = 3354623) B3354623
theorem B3354629 : Blo 2235435 3354629 := bbase (se 4 (by rfl) ⟨314496, by rfl⟩ : syracuseStep 3354629 = 628993) (by norm_num)
theorem B2236419 : Blo 2235435 2236419 := bstep (se 1 (by rfl) ⟨1677314, by rfl⟩ : syracuseStep 2236419 = 3354629) B3354629
theorem B3773965 : Blo 2235435 3773965 := bbase (se 3 (by rfl) ⟨707618, by rfl⟩ : syracuseStep 3773965 = 1415237) (by norm_num)
theorem B5031953 : Blo 2235435 5031953 := bstep (se 2 (by rfl) ⟨1886982, by rfl⟩ : syracuseStep 5031953 = 3773965) B3773965
theorem B3354635 : Blo 2235435 3354635 := bstep (se 1 (by rfl) ⟨2515976, by rfl⟩ : syracuseStep 3354635 = 5031953) B5031953
theorem B2236423 : Blo 2235435 2236423 := bstep (se 1 (by rfl) ⟨1677317, by rfl⟩ : syracuseStep 2236423 = 3354635) B3354635
theorem B2515981 : Blo 2235435 2515981 := bbase (se 3 (by rfl) ⟨471746, by rfl⟩ : syracuseStep 2515981 = 943493) (by norm_num)
theorem B3354641 : Blo 2235435 3354641 := bstep (se 2 (by rfl) ⟨1257990, by rfl⟩ : syracuseStep 3354641 = 2515981) B2515981
theorem B2236427 : Blo 2235435 2236427 := bstep (se 1 (by rfl) ⟨1677320, by rfl⟩ : syracuseStep 2236427 = 3354641) B3354641
theorem B7547957 : Blo 2235435 7547957 := bbase (se 5 (by rfl) ⟨353810, by rfl⟩ : syracuseStep 7547957 = 707621) (by norm_num)
theorem B5031971 : Blo 2235435 5031971 := bstep (se 1 (by rfl) ⟨3773978, by rfl⟩ : syracuseStep 5031971 = 7547957) B7547957
theorem B3354647 : Blo 2235435 3354647 := bstep (se 1 (by rfl) ⟨2515985, by rfl⟩ : syracuseStep 3354647 = 5031971) B5031971
theorem B2236431 : Blo 2235435 2236431 := bstep (se 1 (by rfl) ⟨1677323, by rfl⟩ : syracuseStep 2236431 = 3354647) B3354647
theorem B3354653 : Blo 2235435 3354653 := bbase (se 3 (by rfl) ⟨628997, by rfl⟩ : syracuseStep 3354653 = 1257995) (by norm_num)
theorem B2236435 : Blo 2235435 2236435 := bstep (se 1 (by rfl) ⟨1677326, by rfl⟩ : syracuseStep 2236435 = 3354653) B3354653
theorem B5031989 : Blo 2235435 5031989 := bbase (se 5 (by rfl) ⟨235874, by rfl⟩ : syracuseStep 5031989 = 471749) (by norm_num)
theorem B3354659 : Blo 2235435 3354659 := bstep (se 1 (by rfl) ⟨2515994, by rfl⟩ : syracuseStep 3354659 = 5031989) B5031989
theorem B2236439 : Blo 2235435 2236439 := bstep (se 1 (by rfl) ⟨1677329, by rfl⟩ : syracuseStep 2236439 = 3354659) B3354659
theorem B4595773 : Blo 2235435 4595773 := bbase (se 3 (by rfl) ⟨861707, by rfl⟩ : syracuseStep 4595773 = 1723415) (by norm_num)
theorem B6127697 : Blo 2235435 6127697 := bstep (se 2 (by rfl) ⟨2297886, by rfl⟩ : syracuseStep 6127697 = 4595773) B4595773
theorem B16340525 : Blo 2235435 16340525 := bstep (se 3 (by rfl) ⟨3063848, by rfl⟩ : syracuseStep 16340525 = 6127697) B6127697
theorem B10893683 : Blo 2235435 10893683 := bstep (se 1 (by rfl) ⟨8170262, by rfl⟩ : syracuseStep 10893683 = 16340525) B16340525
theorem B7262455 : Blo 2235435 7262455 := bstep (se 1 (by rfl) ⟨5446841, by rfl⟩ : syracuseStep 7262455 = 10893683) B10893683
theorem B9683273 : Blo 2235435 9683273 := bstep (se 2 (by rfl) ⟨3631227, by rfl⟩ : syracuseStep 9683273 = 7262455) B7262455
theorem B25822061 : Blo 2235435 25822061 := bstep (se 3 (by rfl) ⟨4841636, by rfl⟩ : syracuseStep 25822061 = 9683273) B9683273
theorem B17214707 : Blo 2235435 17214707 := bstep (se 1 (by rfl) ⟨12911030, by rfl⟩ : syracuseStep 17214707 = 25822061) B25822061
theorem B11476471 : Blo 2235435 11476471 := bstep (se 1 (by rfl) ⟨8607353, by rfl⟩ : syracuseStep 11476471 = 17214707) B17214707
theorem B15301961 : Blo 2235435 15301961 := bstep (se 2 (by rfl) ⟨5738235, by rfl⟩ : syracuseStep 15301961 = 11476471) B11476471
theorem B10201307 : Blo 2235435 10201307 := bstep (se 1 (by rfl) ⟨7650980, by rfl⟩ : syracuseStep 10201307 = 15301961) B15301961
theorem B27203485 : Blo 2235435 27203485 := bstep (se 3 (by rfl) ⟨5100653, by rfl⟩ : syracuseStep 27203485 = 10201307) B10201307
theorem B36271313 : Blo 2235435 36271313 := bstep (se 2 (by rfl) ⟨13601742, by rfl⟩ : syracuseStep 36271313 = 27203485) B27203485
theorem B24180875 : Blo 2235435 24180875 := bstep (se 1 (by rfl) ⟨18135656, by rfl⟩ : syracuseStep 24180875 = 36271313) B36271313
theorem B16120583 : Blo 2235435 16120583 := bstep (se 1 (by rfl) ⟨12090437, by rfl⟩ : syracuseStep 16120583 = 24180875) B24180875
theorem B10747055 : Blo 2235435 10747055 := bstep (se 1 (by rfl) ⟨8060291, by rfl⟩ : syracuseStep 10747055 = 16120583) B16120583
theorem B7164703 : Blo 2235435 7164703 := bstep (se 1 (by rfl) ⟨5373527, by rfl⟩ : syracuseStep 7164703 = 10747055) B10747055
theorem B9552937 : Blo 2235435 9552937 := bstep (se 2 (by rfl) ⟨3582351, by rfl⟩ : syracuseStep 9552937 = 7164703) B7164703
theorem B12737249 : Blo 2235435 12737249 := bstep (se 2 (by rfl) ⟨4776468, by rfl⟩ : syracuseStep 12737249 = 9552937) B9552937
theorem B8491499 : Blo 2235435 8491499 := bstep (se 1 (by rfl) ⟨6368624, by rfl⟩ : syracuseStep 8491499 = 12737249) B12737249
theorem B5660999 : Blo 2235435 5660999 := bstep (se 1 (by rfl) ⟨4245749, by rfl⟩ : syracuseStep 5660999 = 8491499) B8491499
theorem B3773999 : Blo 2235435 3773999 := bstep (se 1 (by rfl) ⟨2830499, by rfl⟩ : syracuseStep 3773999 = 5660999) B5660999
theorem B2515999 : Blo 2235435 2515999 := bstep (se 1 (by rfl) ⟨1886999, by rfl⟩ : syracuseStep 2515999 = 3773999) B3773999
theorem B3354665 : Blo 2235435 3354665 := bstep (se 2 (by rfl) ⟨1257999, by rfl⟩ : syracuseStep 3354665 = 2515999) B2515999
theorem B2236443 : Blo 2235435 2236443 := bstep (se 1 (by rfl) ⟨1677332, by rfl⟩ : syracuseStep 2236443 = 3354665) B3354665
theorem B2266961 : Blo 2235435 2266961 := bbase (se 2 (by rfl) ⟨850110, by rfl⟩ : syracuseStep 2266961 = 1700221) (by norm_num)
theorem B6045229 : Blo 2235435 6045229 := bstep (se 3 (by rfl) ⟨1133480, by rfl⟩ : syracuseStep 6045229 = 2266961) B2266961
theorem B8060305 : Blo 2235435 8060305 := bstep (se 2 (by rfl) ⟨3022614, by rfl⟩ : syracuseStep 8060305 = 6045229) B6045229
theorem B10747073 : Blo 2235435 10747073 := bstep (se 2 (by rfl) ⟨4030152, by rfl⟩ : syracuseStep 10747073 = 8060305) B8060305
theorem B7164715 : Blo 2235435 7164715 := bstep (se 1 (by rfl) ⟨5373536, by rfl⟩ : syracuseStep 7164715 = 10747073) B10747073
theorem B9552953 : Blo 2235435 9552953 := bstep (se 2 (by rfl) ⟨3582357, by rfl⟩ : syracuseStep 9552953 = 7164715) B7164715
theorem B6368635 : Blo 2235435 6368635 := bstep (se 1 (by rfl) ⟨4776476, by rfl⟩ : syracuseStep 6368635 = 9552953) B9552953
theorem B8491513 : Blo 2235435 8491513 := bstep (se 2 (by rfl) ⟨3184317, by rfl⟩ : syracuseStep 8491513 = 6368635) B6368635
theorem B11322017 : Blo 2235435 11322017 := bstep (se 2 (by rfl) ⟨4245756, by rfl⟩ : syracuseStep 11322017 = 8491513) B8491513
theorem B7548011 : Blo 2235435 7548011 := bstep (se 1 (by rfl) ⟨5661008, by rfl⟩ : syracuseStep 7548011 = 11322017) B11322017
theorem B5032007 : Blo 2235435 5032007 := bstep (se 1 (by rfl) ⟨3774005, by rfl⟩ : syracuseStep 5032007 = 7548011) B7548011
theorem B3354671 : Blo 2235435 3354671 := bstep (se 1 (by rfl) ⟨2516003, by rfl⟩ : syracuseStep 3354671 = 5032007) B5032007
theorem B2236447 : Blo 2235435 2236447 := bstep (se 1 (by rfl) ⟨1677335, by rfl⟩ : syracuseStep 2236447 = 3354671) B3354671
theorem B3354677 : Blo 2235435 3354677 := bbase (se 5 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 3354677 = 314501) (by norm_num)
theorem B2236451 : Blo 2235435 2236451 := bstep (se 1 (by rfl) ⟨1677338, by rfl⟩ : syracuseStep 2236451 = 3354677) B3354677
theorem B5661029 : Blo 2235435 5661029 := bbase (se 4 (by rfl) ⟨530721, by rfl⟩ : syracuseStep 5661029 = 1061443) (by norm_num)
theorem B3774019 : Blo 2235435 3774019 := bstep (se 1 (by rfl) ⟨2830514, by rfl⟩ : syracuseStep 3774019 = 5661029) B5661029
theorem B5032025 : Blo 2235435 5032025 := bstep (se 2 (by rfl) ⟨1887009, by rfl⟩ : syracuseStep 5032025 = 3774019) B3774019
theorem B3354683 : Blo 2235435 3354683 := bstep (se 1 (by rfl) ⟨2516012, by rfl⟩ : syracuseStep 3354683 = 5032025) B5032025
theorem B2236455 : Blo 2235435 2236455 := bstep (se 1 (by rfl) ⟨1677341, by rfl⟩ : syracuseStep 2236455 = 3354683) B3354683
theorem B2516017 : Blo 2235435 2516017 := bbase (se 2 (by rfl) ⟨943506, by rfl⟩ : syracuseStep 2516017 = 1887013) (by norm_num)
theorem B3354689 : Blo 2235435 3354689 := bstep (se 2 (by rfl) ⟨1258008, by rfl⟩ : syracuseStep 3354689 = 2516017) B2516017
theorem B2236459 : Blo 2235435 2236459 := bstep (se 1 (by rfl) ⟨1677344, by rfl⟩ : syracuseStep 2236459 = 3354689) B3354689
theorem B36271637 : Blo 2235435 36271637 := bbase (se 6 (by rfl) ⟨850116, by rfl⟩ : syracuseStep 36271637 = 1700233) (by norm_num)
theorem B24181091 : Blo 2235435 24181091 := bstep (se 1 (by rfl) ⟨18135818, by rfl⟩ : syracuseStep 24181091 = 36271637) B36271637
theorem B16120727 : Blo 2235435 16120727 := bstep (se 1 (by rfl) ⟨12090545, by rfl⟩ : syracuseStep 16120727 = 24181091) B24181091
theorem B10747151 : Blo 2235435 10747151 := bstep (se 1 (by rfl) ⟨8060363, by rfl⟩ : syracuseStep 10747151 = 16120727) B16120727
theorem B7164767 : Blo 2235435 7164767 := bstep (se 1 (by rfl) ⟨5373575, by rfl⟩ : syracuseStep 7164767 = 10747151) B10747151
theorem B4776511 : Blo 2235435 4776511 := bstep (se 1 (by rfl) ⟨3582383, by rfl⟩ : syracuseStep 4776511 = 7164767) B7164767
theorem B6368681 : Blo 2235435 6368681 := bstep (se 2 (by rfl) ⟨2388255, by rfl⟩ : syracuseStep 6368681 = 4776511) B4776511
theorem B4245787 : Blo 2235435 4245787 := bstep (se 1 (by rfl) ⟨3184340, by rfl⟩ : syracuseStep 4245787 = 6368681) B6368681
theorem B5661049 : Blo 2235435 5661049 := bstep (se 2 (by rfl) ⟨2122893, by rfl⟩ : syracuseStep 5661049 = 4245787) B4245787
theorem B7548065 : Blo 2235435 7548065 := bstep (se 2 (by rfl) ⟨2830524, by rfl⟩ : syracuseStep 7548065 = 5661049) B5661049
theorem B5032043 : Blo 2235435 5032043 := bstep (se 1 (by rfl) ⟨3774032, by rfl⟩ : syracuseStep 5032043 = 7548065) B7548065
theorem B3354695 : Blo 2235435 3354695 := bstep (se 1 (by rfl) ⟨2516021, by rfl⟩ : syracuseStep 3354695 = 5032043) B5032043
theorem B2236463 : Blo 2235435 2236463 := bstep (se 1 (by rfl) ⟨1677347, by rfl⟩ : syracuseStep 2236463 = 3354695) B3354695
theorem B3354701 : Blo 2235435 3354701 := bbase (se 3 (by rfl) ⟨629006, by rfl⟩ : syracuseStep 3354701 = 1258013) (by norm_num)
theorem B2236467 : Blo 2235435 2236467 := bstep (se 1 (by rfl) ⟨1677350, by rfl⟩ : syracuseStep 2236467 = 3354701) B3354701
theorem B5032061 : Blo 2235435 5032061 := bbase (se 3 (by rfl) ⟨943511, by rfl⟩ : syracuseStep 5032061 = 1887023) (by norm_num)
theorem B3354707 : Blo 2235435 3354707 := bstep (se 1 (by rfl) ⟨2516030, by rfl⟩ : syracuseStep 3354707 = 5032061) B5032061
theorem B2236471 : Blo 2235435 2236471 := bstep (se 1 (by rfl) ⟨1677353, by rfl⟩ : syracuseStep 2236471 = 3354707) B3354707
theorem B3774053 : Blo 2235435 3774053 := bbase (se 4 (by rfl) ⟨353817, by rfl⟩ : syracuseStep 3774053 = 707635) (by norm_num)
theorem B2516035 : Blo 2235435 2516035 := bstep (se 1 (by rfl) ⟨1887026, by rfl⟩ : syracuseStep 2516035 = 3774053) B3774053
theorem B3354713 : Blo 2235435 3354713 := bstep (se 2 (by rfl) ⟨1258017, by rfl⟩ : syracuseStep 3354713 = 2516035) B2516035
theorem B2236475 : Blo 2235435 2236475 := bstep (se 1 (by rfl) ⟨1677356, by rfl⟩ : syracuseStep 2236475 = 3354713) B3354713
theorem B6045317 : Blo 2235435 6045317 := bbase (se 4 (by rfl) ⟨566748, by rfl⟩ : syracuseStep 6045317 = 1133497) (by norm_num)
theorem B4030211 : Blo 2235435 4030211 := bstep (se 1 (by rfl) ⟨3022658, by rfl⟩ : syracuseStep 4030211 = 6045317) B6045317
theorem B2686807 : Blo 2235435 2686807 := bstep (se 1 (by rfl) ⟨2015105, by rfl⟩ : syracuseStep 2686807 = 4030211) B4030211
theorem B3582409 : Blo 2235435 3582409 := bstep (se 2 (by rfl) ⟨1343403, by rfl⟩ : syracuseStep 3582409 = 2686807) B2686807
theorem B4776545 : Blo 2235435 4776545 := bstep (se 2 (by rfl) ⟨1791204, by rfl⟩ : syracuseStep 4776545 = 3582409) B3582409
theorem B3184363 : Blo 2235435 3184363 := bstep (se 1 (by rfl) ⟨2388272, by rfl⟩ : syracuseStep 3184363 = 4776545) B4776545
theorem B16983269 : Blo 2235435 16983269 := bstep (se 4 (by rfl) ⟨1592181, by rfl⟩ : syracuseStep 16983269 = 3184363) B3184363
theorem B11322179 : Blo 2235435 11322179 := bstep (se 1 (by rfl) ⟨8491634, by rfl⟩ : syracuseStep 11322179 = 16983269) B16983269
theorem B7548119 : Blo 2235435 7548119 := bstep (se 1 (by rfl) ⟨5661089, by rfl⟩ : syracuseStep 7548119 = 11322179) B11322179
theorem B5032079 : Blo 2235435 5032079 := bstep (se 1 (by rfl) ⟨3774059, by rfl⟩ : syracuseStep 5032079 = 7548119) B7548119
theorem B3354719 : Blo 2235435 3354719 := bstep (se 1 (by rfl) ⟨2516039, by rfl⟩ : syracuseStep 3354719 = 5032079) B5032079
theorem B2236479 : Blo 2235435 2236479 := bstep (se 1 (by rfl) ⟨1677359, by rfl⟩ : syracuseStep 2236479 = 3354719) B3354719
theorem B3354725 : Blo 2235435 3354725 := bbase (se 4 (by rfl) ⟨314505, by rfl⟩ : syracuseStep 3354725 = 629011) (by norm_num)
theorem B2236483 : Blo 2235435 2236483 := bstep (se 1 (by rfl) ⟨1677362, by rfl⟩ : syracuseStep 2236483 = 3354725) B3354725
theorem B2686817 : Blo 2235435 2686817 := bbase (se 2 (by rfl) ⟨1007556, by rfl⟩ : syracuseStep 2686817 = 2015113) (by norm_num)
theorem B7164845 : Blo 2235435 7164845 := bstep (se 3 (by rfl) ⟨1343408, by rfl⟩ : syracuseStep 7164845 = 2686817) B2686817
theorem B4776563 : Blo 2235435 4776563 := bstep (se 1 (by rfl) ⟨3582422, by rfl⟩ : syracuseStep 4776563 = 7164845) B7164845
theorem B3184375 : Blo 2235435 3184375 := bstep (se 1 (by rfl) ⟨2388281, by rfl⟩ : syracuseStep 3184375 = 4776563) B4776563
theorem B4245833 : Blo 2235435 4245833 := bstep (se 2 (by rfl) ⟨1592187, by rfl⟩ : syracuseStep 4245833 = 3184375) B3184375
theorem B2830555 : Blo 2235435 2830555 := bstep (se 1 (by rfl) ⟨2122916, by rfl⟩ : syracuseStep 2830555 = 4245833) B4245833
theorem B3774073 : Blo 2235435 3774073 := bstep (se 2 (by rfl) ⟨1415277, by rfl⟩ : syracuseStep 3774073 = 2830555) B2830555
theorem B5032097 : Blo 2235435 5032097 := bstep (se 2 (by rfl) ⟨1887036, by rfl⟩ : syracuseStep 5032097 = 3774073) B3774073
theorem B3354731 : Blo 2235435 3354731 := bstep (se 1 (by rfl) ⟨2516048, by rfl⟩ : syracuseStep 3354731 = 5032097) B5032097
theorem B2236487 : Blo 2235435 2236487 := bstep (se 1 (by rfl) ⟨1677365, by rfl⟩ : syracuseStep 2236487 = 3354731) B3354731
theorem B2516053 : Blo 2235435 2516053 := bbase (se 8 (by rfl) ⟨14742, by rfl⟩ : syracuseStep 2516053 = 29485) (by norm_num)
theorem B3354737 : Blo 2235435 3354737 := bstep (se 2 (by rfl) ⟨1258026, by rfl⟩ : syracuseStep 3354737 = 2516053) B2516053
theorem B2236491 : Blo 2235435 2236491 := bstep (se 1 (by rfl) ⟨1677368, by rfl⟩ : syracuseStep 2236491 = 3354737) B3354737
theorem B2830565 : Blo 2235435 2830565 := bbase (se 4 (by rfl) ⟨265365, by rfl⟩ : syracuseStep 2830565 = 530731) (by norm_num)
theorem B7548173 : Blo 2235435 7548173 := bstep (se 3 (by rfl) ⟨1415282, by rfl⟩ : syracuseStep 7548173 = 2830565) B2830565
theorem B5032115 : Blo 2235435 5032115 := bstep (se 1 (by rfl) ⟨3774086, by rfl⟩ : syracuseStep 5032115 = 7548173) B7548173
theorem B3354743 : Blo 2235435 3354743 := bstep (se 1 (by rfl) ⟨2516057, by rfl⟩ : syracuseStep 3354743 = 5032115) B5032115
theorem B2236495 : Blo 2235435 2236495 := bstep (se 1 (by rfl) ⟨1677371, by rfl⟩ : syracuseStep 2236495 = 3354743) B3354743
theorem B3354749 : Blo 2235435 3354749 := bbase (se 3 (by rfl) ⟨629015, by rfl⟩ : syracuseStep 3354749 = 1258031) (by norm_num)
theorem B2236499 : Blo 2235435 2236499 := bstep (se 1 (by rfl) ⟨1677374, by rfl⟩ : syracuseStep 2236499 = 3354749) B3354749
theorem B5032133 : Blo 2235435 5032133 := bbase (se 4 (by rfl) ⟨471762, by rfl⟩ : syracuseStep 5032133 = 943525) (by norm_num)
theorem B3354755 : Blo 2235435 3354755 := bstep (se 1 (by rfl) ⟨2516066, by rfl⟩ : syracuseStep 3354755 = 5032133) B5032133
theorem B2236503 : Blo 2235435 2236503 := bstep (se 1 (by rfl) ⟨1677377, by rfl⟩ : syracuseStep 2236503 = 3354755) B3354755
theorem B16121045 : Blo 2235435 16121045 := bbase (se 7 (by rfl) ⟨188918, by rfl⟩ : syracuseStep 16121045 = 377837) (by norm_num)
theorem B10747363 : Blo 2235435 10747363 := bstep (se 1 (by rfl) ⟨8060522, by rfl⟩ : syracuseStep 10747363 = 16121045) B16121045
theorem B14329817 : Blo 2235435 14329817 := bstep (se 2 (by rfl) ⟨5373681, by rfl⟩ : syracuseStep 14329817 = 10747363) B10747363
theorem B9553211 : Blo 2235435 9553211 := bstep (se 1 (by rfl) ⟨7164908, by rfl⟩ : syracuseStep 9553211 = 14329817) B14329817
theorem B6368807 : Blo 2235435 6368807 := bstep (se 1 (by rfl) ⟨4776605, by rfl⟩ : syracuseStep 6368807 = 9553211) B9553211
theorem B4245871 : Blo 2235435 4245871 := bstep (se 1 (by rfl) ⟨3184403, by rfl⟩ : syracuseStep 4245871 = 6368807) B6368807
theorem B5661161 : Blo 2235435 5661161 := bstep (se 2 (by rfl) ⟨2122935, by rfl⟩ : syracuseStep 5661161 = 4245871) B4245871
theorem B3774107 : Blo 2235435 3774107 := bstep (se 1 (by rfl) ⟨2830580, by rfl⟩ : syracuseStep 3774107 = 5661161) B5661161
theorem B2516071 : Blo 2235435 2516071 := bstep (se 1 (by rfl) ⟨1887053, by rfl⟩ : syracuseStep 2516071 = 3774107) B3774107
theorem B3354761 : Blo 2235435 3354761 := bstep (se 2 (by rfl) ⟨1258035, by rfl⟩ : syracuseStep 3354761 = 2516071) B2516071
theorem B2236507 : Blo 2235435 2236507 := bstep (se 1 (by rfl) ⟨1677380, by rfl⟩ : syracuseStep 2236507 = 3354761) B3354761
theorem B11322341 : Blo 2235435 11322341 := bbase (se 4 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 11322341 = 2122939) (by norm_num)
theorem B7548227 : Blo 2235435 7548227 := bstep (se 1 (by rfl) ⟨5661170, by rfl⟩ : syracuseStep 7548227 = 11322341) B11322341
theorem B5032151 : Blo 2235435 5032151 := bstep (se 1 (by rfl) ⟨3774113, by rfl⟩ : syracuseStep 5032151 = 7548227) B7548227
theorem B3354767 : Blo 2235435 3354767 := bstep (se 1 (by rfl) ⟨2516075, by rfl⟩ : syracuseStep 3354767 = 5032151) B5032151
theorem B2236511 : Blo 2235435 2236511 := bstep (se 1 (by rfl) ⟨1677383, by rfl⟩ : syracuseStep 2236511 = 3354767) B3354767
theorem B3354773 : Blo 2235435 3354773 := bbase (se 6 (by rfl) ⟨78627, by rfl⟩ : syracuseStep 3354773 = 157255) (by norm_num)
theorem B2236515 : Blo 2235435 2236515 := bstep (se 1 (by rfl) ⟨1677386, by rfl⟩ : syracuseStep 2236515 = 3354773) B3354773
theorem B4534069 : Blo 2235435 4534069 := bbase (se 5 (by rfl) ⟨212534, by rfl⟩ : syracuseStep 4534069 = 425069) (by norm_num)
theorem B6045425 : Blo 2235435 6045425 := bstep (se 2 (by rfl) ⟨2267034, by rfl⟩ : syracuseStep 6045425 = 4534069) B4534069
theorem B4030283 : Blo 2235435 4030283 := bstep (se 1 (by rfl) ⟨3022712, by rfl⟩ : syracuseStep 4030283 = 6045425) B6045425
theorem B2686855 : Blo 2235435 2686855 := bstep (se 1 (by rfl) ⟨2015141, by rfl⟩ : syracuseStep 2686855 = 4030283) B4030283
theorem B3582473 : Blo 2235435 3582473 := bstep (se 2 (by rfl) ⟨1343427, by rfl⟩ : syracuseStep 3582473 = 2686855) B2686855
theorem B9553261 : Blo 2235435 9553261 := bstep (se 3 (by rfl) ⟨1791236, by rfl⟩ : syracuseStep 9553261 = 3582473) B3582473
theorem B12737681 : Blo 2235435 12737681 := bstep (se 2 (by rfl) ⟨4776630, by rfl⟩ : syracuseStep 12737681 = 9553261) B9553261
theorem B8491787 : Blo 2235435 8491787 := bstep (se 1 (by rfl) ⟨6368840, by rfl⟩ : syracuseStep 8491787 = 12737681) B12737681
theorem B5661191 : Blo 2235435 5661191 := bstep (se 1 (by rfl) ⟨4245893, by rfl⟩ : syracuseStep 5661191 = 8491787) B8491787
theorem B3774127 : Blo 2235435 3774127 := bstep (se 1 (by rfl) ⟨2830595, by rfl⟩ : syracuseStep 3774127 = 5661191) B5661191
theorem B5032169 : Blo 2235435 5032169 := bstep (se 2 (by rfl) ⟨1887063, by rfl⟩ : syracuseStep 5032169 = 3774127) B3774127
theorem B3354779 : Blo 2235435 3354779 := bstep (se 1 (by rfl) ⟨2516084, by rfl⟩ : syracuseStep 3354779 = 5032169) B5032169
theorem B2236519 : Blo 2235435 2236519 := bstep (se 1 (by rfl) ⟨1677389, by rfl⟩ : syracuseStep 2236519 = 3354779) B3354779
theorem B2516089 : Blo 2235435 2516089 := bbase (se 2 (by rfl) ⟨943533, by rfl⟩ : syracuseStep 2516089 = 1887067) (by norm_num)
theorem B3354785 : Blo 2235435 3354785 := bstep (se 2 (by rfl) ⟨1258044, by rfl⟩ : syracuseStep 3354785 = 2516089) B2516089
theorem B2236523 : Blo 2235435 2236523 := bstep (se 1 (by rfl) ⟨1677392, by rfl⟩ : syracuseStep 2236523 = 3354785) B3354785
theorem B6045445 : Blo 2235435 6045445 := bbase (se 4 (by rfl) ⟨566760, by rfl⟩ : syracuseStep 6045445 = 1133521) (by norm_num)
theorem B32242373 : Blo 2235435 32242373 := bstep (se 4 (by rfl) ⟨3022722, by rfl⟩ : syracuseStep 32242373 = 6045445) B6045445
theorem B21494915 : Blo 2235435 21494915 := bstep (se 1 (by rfl) ⟨16121186, by rfl⟩ : syracuseStep 21494915 = 32242373) B32242373
theorem B14329943 : Blo 2235435 14329943 := bstep (se 1 (by rfl) ⟨10747457, by rfl⟩ : syracuseStep 14329943 = 21494915) B21494915
theorem B9553295 : Blo 2235435 9553295 := bstep (se 1 (by rfl) ⟨7164971, by rfl⟩ : syracuseStep 9553295 = 14329943) B14329943
theorem B6368863 : Blo 2235435 6368863 := bstep (se 1 (by rfl) ⟨4776647, by rfl⟩ : syracuseStep 6368863 = 9553295) B9553295
theorem B8491817 : Blo 2235435 8491817 := bstep (se 2 (by rfl) ⟨3184431, by rfl⟩ : syracuseStep 8491817 = 6368863) B6368863
theorem B5661211 : Blo 2235435 5661211 := bstep (se 1 (by rfl) ⟨4245908, by rfl⟩ : syracuseStep 5661211 = 8491817) B8491817
theorem B7548281 : Blo 2235435 7548281 := bstep (se 2 (by rfl) ⟨2830605, by rfl⟩ : syracuseStep 7548281 = 5661211) B5661211
theorem B5032187 : Blo 2235435 5032187 := bstep (se 1 (by rfl) ⟨3774140, by rfl⟩ : syracuseStep 5032187 = 7548281) B7548281
theorem B3354791 : Blo 2235435 3354791 := bstep (se 1 (by rfl) ⟨2516093, by rfl⟩ : syracuseStep 3354791 = 5032187) B5032187
theorem B2236527 : Blo 2235435 2236527 := bstep (se 1 (by rfl) ⟨1677395, by rfl⟩ : syracuseStep 2236527 = 3354791) B3354791
theorem B3354797 : Blo 2235435 3354797 := bbase (se 3 (by rfl) ⟨629024, by rfl⟩ : syracuseStep 3354797 = 1258049) (by norm_num)
theorem B2236531 : Blo 2235435 2236531 := bstep (se 1 (by rfl) ⟨1677398, by rfl⟩ : syracuseStep 2236531 = 3354797) B3354797
theorem B5032205 : Blo 2235435 5032205 := bbase (se 3 (by rfl) ⟨943538, by rfl⟩ : syracuseStep 5032205 = 1887077) (by norm_num)
theorem B3354803 : Blo 2235435 3354803 := bstep (se 1 (by rfl) ⟨2516102, by rfl⟩ : syracuseStep 3354803 = 5032205) B5032205
theorem B2236535 : Blo 2235435 2236535 := bstep (se 1 (by rfl) ⟨1677401, by rfl⟩ : syracuseStep 2236535 = 3354803) B3354803
theorem B2830621 : Blo 2235435 2830621 := bbase (se 3 (by rfl) ⟨530741, by rfl⟩ : syracuseStep 2830621 = 1061483) (by norm_num)
theorem B3774161 : Blo 2235435 3774161 := bstep (se 2 (by rfl) ⟨1415310, by rfl⟩ : syracuseStep 3774161 = 2830621) B2830621
theorem B2516107 : Blo 2235435 2516107 := bstep (se 1 (by rfl) ⟨1887080, by rfl⟩ : syracuseStep 2516107 = 3774161) B3774161
theorem B3354809 : Blo 2235435 3354809 := bstep (se 2 (by rfl) ⟨1258053, by rfl⟩ : syracuseStep 3354809 = 2516107) B2516107
theorem B2236539 : Blo 2235435 2236539 := bstep (se 1 (by rfl) ⟨1677404, by rfl⟩ : syracuseStep 2236539 = 3354809) B3354809
theorem B15302645 : Blo 2235435 15302645 := bbase (se 5 (by rfl) ⟨717311, by rfl⟩ : syracuseStep 15302645 = 1434623) (by norm_num)
theorem B10201763 : Blo 2235435 10201763 := bstep (se 1 (by rfl) ⟨7651322, by rfl⟩ : syracuseStep 10201763 = 15302645) B15302645
theorem B6801175 : Blo 2235435 6801175 := bstep (se 1 (by rfl) ⟨5100881, by rfl⟩ : syracuseStep 6801175 = 10201763) B10201763
theorem B9068233 : Blo 2235435 9068233 := bstep (se 2 (by rfl) ⟨3400587, by rfl⟩ : syracuseStep 9068233 = 6801175) B6801175
theorem B12090977 : Blo 2235435 12090977 := bstep (se 2 (by rfl) ⟨4534116, by rfl⟩ : syracuseStep 12090977 = 9068233) B9068233
theorem B8060651 : Blo 2235435 8060651 := bstep (se 1 (by rfl) ⟨6045488, by rfl⟩ : syracuseStep 8060651 = 12090977) B12090977
theorem B5373767 : Blo 2235435 5373767 := bstep (se 1 (by rfl) ⟨4030325, by rfl⟩ : syracuseStep 5373767 = 8060651) B8060651
theorem B3582511 : Blo 2235435 3582511 := bstep (se 1 (by rfl) ⟨2686883, by rfl⟩ : syracuseStep 3582511 = 5373767) B5373767
theorem B19106725 : Blo 2235435 19106725 := bstep (se 4 (by rfl) ⟨1791255, by rfl⟩ : syracuseStep 19106725 = 3582511) B3582511
theorem B25475633 : Blo 2235435 25475633 := bstep (se 2 (by rfl) ⟨9553362, by rfl⟩ : syracuseStep 25475633 = 19106725) B19106725
theorem B16983755 : Blo 2235435 16983755 := bstep (se 1 (by rfl) ⟨12737816, by rfl⟩ : syracuseStep 16983755 = 25475633) B25475633
theorem B11322503 : Blo 2235435 11322503 := bstep (se 1 (by rfl) ⟨8491877, by rfl⟩ : syracuseStep 11322503 = 16983755) B16983755
theorem B7548335 : Blo 2235435 7548335 := bstep (se 1 (by rfl) ⟨5661251, by rfl⟩ : syracuseStep 7548335 = 11322503) B11322503
theorem B5032223 : Blo 2235435 5032223 := bstep (se 1 (by rfl) ⟨3774167, by rfl⟩ : syracuseStep 5032223 = 7548335) B7548335
theorem B3354815 : Blo 2235435 3354815 := bstep (se 1 (by rfl) ⟨2516111, by rfl⟩ : syracuseStep 3354815 = 5032223) B5032223
theorem B2236543 : Blo 2235435 2236543 := bstep (se 1 (by rfl) ⟨1677407, by rfl⟩ : syracuseStep 2236543 = 3354815) B3354815
theorem B3354821 : Blo 2235435 3354821 := bbase (se 4 (by rfl) ⟨314514, by rfl⟩ : syracuseStep 3354821 = 629029) (by norm_num)
theorem B2236547 : Blo 2235435 2236547 := bstep (se 1 (by rfl) ⟨1677410, by rfl⟩ : syracuseStep 2236547 = 3354821) B3354821
theorem B3774181 : Blo 2235435 3774181 := bbase (se 4 (by rfl) ⟨353829, by rfl⟩ : syracuseStep 3774181 = 707659) (by norm_num)
theorem B5032241 : Blo 2235435 5032241 := bstep (se 2 (by rfl) ⟨1887090, by rfl⟩ : syracuseStep 5032241 = 3774181) B3774181
theorem B3354827 : Blo 2235435 3354827 := bstep (se 1 (by rfl) ⟨2516120, by rfl⟩ : syracuseStep 3354827 = 5032241) B5032241
theorem B2236551 : Blo 2235435 2236551 := bstep (se 1 (by rfl) ⟨1677413, by rfl⟩ : syracuseStep 2236551 = 3354827) B3354827
theorem B2516125 : Blo 2235435 2516125 := bbase (se 3 (by rfl) ⟨471773, by rfl⟩ : syracuseStep 2516125 = 943547) (by norm_num)
theorem B3354833 : Blo 2235435 3354833 := bstep (se 2 (by rfl) ⟨1258062, by rfl⟩ : syracuseStep 3354833 = 2516125) B2516125
theorem B2236555 : Blo 2235435 2236555 := bstep (se 1 (by rfl) ⟨1677416, by rfl⟩ : syracuseStep 2236555 = 3354833) B3354833
theorem B7548389 : Blo 2235435 7548389 := bbase (se 4 (by rfl) ⟨707661, by rfl⟩ : syracuseStep 7548389 = 1415323) (by norm_num)
theorem B5032259 : Blo 2235435 5032259 := bstep (se 1 (by rfl) ⟨3774194, by rfl⟩ : syracuseStep 5032259 = 7548389) B7548389
theorem B3354839 : Blo 2235435 3354839 := bstep (se 1 (by rfl) ⟨2516129, by rfl⟩ : syracuseStep 3354839 = 5032259) B5032259
theorem B2236559 : Blo 2235435 2236559 := bstep (se 1 (by rfl) ⟨1677419, by rfl⟩ : syracuseStep 2236559 = 3354839) B3354839
theorem B3354845 : Blo 2235435 3354845 := bbase (se 3 (by rfl) ⟨629033, by rfl⟩ : syracuseStep 3354845 = 1258067) (by norm_num)
theorem B2236563 : Blo 2235435 2236563 := bstep (se 1 (by rfl) ⟨1677422, by rfl⟩ : syracuseStep 2236563 = 3354845) B3354845
theorem B5032277 : Blo 2235435 5032277 := bbase (se 10 (by rfl) ⟨7371, by rfl⟩ : syracuseStep 5032277 = 14743) (by norm_num)
theorem B3354851 : Blo 2235435 3354851 := bstep (se 1 (by rfl) ⟨2516138, by rfl⟩ : syracuseStep 3354851 = 5032277) B5032277
theorem B2236567 : Blo 2235435 2236567 := bstep (se 1 (by rfl) ⟨1677425, by rfl⟩ : syracuseStep 2236567 = 3354851) B3354851
theorem B3582557 : Blo 2235435 3582557 := bbase (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) (by norm_num)
theorem B2388371 : Blo 2235435 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B6368989 : Blo 2235435 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B8491985 : Blo 2235435 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B5661323 : Blo 2235435 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B3774215 : Blo 2235435 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B2516143 : Blo 2235435 2516143 := bstep (se 1 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 2516143 = 3774215) B3774215
theorem B3354857 : Blo 2235435 3354857 := bstep (se 2 (by rfl) ⟨1258071, by rfl⟩ : syracuseStep 3354857 = 2516143) B2516143
theorem B2236571 : Blo 2235435 2236571 := bstep (se 1 (by rfl) ⟨1677428, by rfl⟩ : syracuseStep 2236571 = 3354857) B3354857
theorem B5738573 : Blo 2235435 5738573 := bbase (se 3 (by rfl) ⟨1075982, by rfl⟩ : syracuseStep 5738573 = 2151965) (by norm_num)
theorem B15302861 : Blo 2235435 15302861 := bstep (se 3 (by rfl) ⟨2869286, by rfl⟩ : syracuseStep 15302861 = 5738573) B5738573
theorem B10201907 : Blo 2235435 10201907 := bstep (se 1 (by rfl) ⟨7651430, by rfl⟩ : syracuseStep 10201907 = 15302861) B15302861
theorem B27205085 : Blo 2235435 27205085 := bstep (se 3 (by rfl) ⟨5100953, by rfl⟩ : syracuseStep 27205085 = 10201907) B10201907
theorem B18136723 : Blo 2235435 18136723 := bstep (se 1 (by rfl) ⟨13602542, by rfl⟩ : syracuseStep 18136723 = 27205085) B27205085
theorem B24182297 : Blo 2235435 24182297 := bstep (se 2 (by rfl) ⟨9068361, by rfl⟩ : syracuseStep 24182297 = 18136723) B18136723
theorem B16121531 : Blo 2235435 16121531 := bstep (se 1 (by rfl) ⟨12091148, by rfl⟩ : syracuseStep 16121531 = 24182297) B24182297
theorem B42990749 : Blo 2235435 42990749 := bstep (se 3 (by rfl) ⟨8060765, by rfl⟩ : syracuseStep 42990749 = 16121531) B16121531
theorem B28660499 : Blo 2235435 28660499 := bstep (se 1 (by rfl) ⟨21495374, by rfl⟩ : syracuseStep 28660499 = 42990749) B42990749
theorem B19106999 : Blo 2235435 19106999 := bstep (se 1 (by rfl) ⟨14330249, by rfl⟩ : syracuseStep 19106999 = 28660499) B28660499
theorem B12737999 : Blo 2235435 12737999 := bstep (se 1 (by rfl) ⟨9553499, by rfl⟩ : syracuseStep 12737999 = 19106999) B19106999
theorem B8491999 : Blo 2235435 8491999 := bstep (se 1 (by rfl) ⟨6368999, by rfl⟩ : syracuseStep 8491999 = 12737999) B12737999
theorem B11322665 : Blo 2235435 11322665 := bstep (se 2 (by rfl) ⟨4245999, by rfl⟩ : syracuseStep 11322665 = 8491999) B8491999
theorem B7548443 : Blo 2235435 7548443 := bstep (se 1 (by rfl) ⟨5661332, by rfl⟩ : syracuseStep 7548443 = 11322665) B11322665
theorem B5032295 : Blo 2235435 5032295 := bstep (se 1 (by rfl) ⟨3774221, by rfl⟩ : syracuseStep 5032295 = 7548443) B7548443
theorem B3354863 : Blo 2235435 3354863 := bstep (se 1 (by rfl) ⟨2516147, by rfl⟩ : syracuseStep 3354863 = 5032295) B5032295
theorem B2236575 : Blo 2235435 2236575 := bstep (se 1 (by rfl) ⟨1677431, by rfl⟩ : syracuseStep 2236575 = 3354863) B3354863
theorem B3354869 : Blo 2235435 3354869 := bbase (se 5 (by rfl) ⟨157259, by rfl⟩ : syracuseStep 3354869 = 314519) (by norm_num)
theorem B2236579 : Blo 2235435 2236579 := bstep (se 1 (by rfl) ⟨1677434, by rfl⟩ : syracuseStep 2236579 = 3354869) B3354869
theorem B21788725 : Blo 2235435 21788725 := bbase (se 5 (by rfl) ⟨1021346, by rfl⟩ : syracuseStep 21788725 = 2042693) (by norm_num)
theorem B29051633 : Blo 2235435 29051633 := bstep (se 2 (by rfl) ⟨10894362, by rfl⟩ : syracuseStep 29051633 = 21788725) B21788725
theorem B19367755 : Blo 2235435 19367755 := bstep (se 1 (by rfl) ⟨14525816, by rfl⟩ : syracuseStep 19367755 = 29051633) B29051633
theorem B103294693 : Blo 2235435 103294693 := bstep (se 4 (by rfl) ⟨9683877, by rfl⟩ : syracuseStep 103294693 = 19367755) B19367755
theorem B137726257 : Blo 2235435 137726257 := bstep (se 2 (by rfl) ⟨51647346, by rfl⟩ : syracuseStep 137726257 = 103294693) B103294693
theorem B183635009 : Blo 2235435 183635009 := bstep (se 2 (by rfl) ⟨68863128, by rfl⟩ : syracuseStep 183635009 = 137726257) B137726257
theorem B122423339 : Blo 2235435 122423339 := bstep (se 1 (by rfl) ⟨91817504, by rfl⟩ : syracuseStep 122423339 = 183635009) B183635009
theorem B81615559 : Blo 2235435 81615559 := bstep (se 1 (by rfl) ⟨61211669, by rfl⟩ : syracuseStep 81615559 = 122423339) B122423339
theorem B108820745 : Blo 2235435 108820745 := bstep (se 2 (by rfl) ⟨40807779, by rfl⟩ : syracuseStep 108820745 = 81615559) B81615559
theorem B72547163 : Blo 2235435 72547163 := bstep (se 1 (by rfl) ⟨54410372, by rfl⟩ : syracuseStep 72547163 = 108820745) B108820745
theorem B48364775 : Blo 2235435 48364775 := bstep (se 1 (by rfl) ⟨36273581, by rfl⟩ : syracuseStep 48364775 = 72547163) B72547163
theorem B32243183 : Blo 2235435 32243183 := bstep (se 1 (by rfl) ⟨24182387, by rfl⟩ : syracuseStep 32243183 = 48364775) B48364775
theorem B21495455 : Blo 2235435 21495455 := bstep (se 1 (by rfl) ⟨16121591, by rfl⟩ : syracuseStep 21495455 = 32243183) B32243183
theorem B14330303 : Blo 2235435 14330303 := bstep (se 1 (by rfl) ⟨10747727, by rfl⟩ : syracuseStep 14330303 = 21495455) B21495455
theorem B9553535 : Blo 2235435 9553535 := bstep (se 1 (by rfl) ⟨7165151, by rfl⟩ : syracuseStep 9553535 = 14330303) B14330303
theorem B6369023 : Blo 2235435 6369023 := bstep (se 1 (by rfl) ⟨4776767, by rfl⟩ : syracuseStep 6369023 = 9553535) B9553535
theorem B4246015 : Blo 2235435 4246015 := bstep (se 1 (by rfl) ⟨3184511, by rfl⟩ : syracuseStep 4246015 = 6369023) B6369023
theorem B5661353 : Blo 2235435 5661353 := bstep (se 2 (by rfl) ⟨2123007, by rfl⟩ : syracuseStep 5661353 = 4246015) B4246015
theorem B3774235 : Blo 2235435 3774235 := bstep (se 1 (by rfl) ⟨2830676, by rfl⟩ : syracuseStep 3774235 = 5661353) B5661353
theorem B5032313 : Blo 2235435 5032313 := bstep (se 2 (by rfl) ⟨1887117, by rfl⟩ : syracuseStep 5032313 = 3774235) B3774235
theorem B3354875 : Blo 2235435 3354875 := bstep (se 1 (by rfl) ⟨2516156, by rfl⟩ : syracuseStep 3354875 = 5032313) B5032313
theorem B2236583 : Blo 2235435 2236583 := bstep (se 1 (by rfl) ⟨1677437, by rfl⟩ : syracuseStep 2236583 = 3354875) B3354875
theorem B2516161 : Blo 2235435 2516161 := bbase (se 2 (by rfl) ⟨943560, by rfl⟩ : syracuseStep 2516161 = 1887121) (by norm_num)
theorem B3354881 : Blo 2235435 3354881 := bstep (se 2 (by rfl) ⟨1258080, by rfl⟩ : syracuseStep 3354881 = 2516161) B2516161
theorem B2236587 : Blo 2235435 2236587 := bstep (se 1 (by rfl) ⟨1677440, by rfl⟩ : syracuseStep 2236587 = 3354881) B3354881
theorem B5661373 : Blo 2235435 5661373 := bbase (se 3 (by rfl) ⟨1061507, by rfl⟩ : syracuseStep 5661373 = 2123015) (by norm_num)
theorem B7548497 : Blo 2235435 7548497 := bstep (se 2 (by rfl) ⟨2830686, by rfl⟩ : syracuseStep 7548497 = 5661373) B5661373
theorem B5032331 : Blo 2235435 5032331 := bstep (se 1 (by rfl) ⟨3774248, by rfl⟩ : syracuseStep 5032331 = 7548497) B7548497
theorem B3354887 : Blo 2235435 3354887 := bstep (se 1 (by rfl) ⟨2516165, by rfl⟩ : syracuseStep 3354887 = 5032331) B5032331
theorem B2236591 : Blo 2235435 2236591 := bstep (se 1 (by rfl) ⟨1677443, by rfl⟩ : syracuseStep 2236591 = 3354887) B3354887
theorem B3354893 : Blo 2235435 3354893 := bbase (se 3 (by rfl) ⟨629042, by rfl⟩ : syracuseStep 3354893 = 1258085) (by norm_num)
theorem B2236595 : Blo 2235435 2236595 := bstep (se 1 (by rfl) ⟨1677446, by rfl⟩ : syracuseStep 2236595 = 3354893) B3354893
theorem B5032349 : Blo 2235435 5032349 := bbase (se 3 (by rfl) ⟨943565, by rfl⟩ : syracuseStep 5032349 = 1887131) (by norm_num)
theorem B3354899 : Blo 2235435 3354899 := bstep (se 1 (by rfl) ⟨2516174, by rfl⟩ : syracuseStep 3354899 = 5032349) B5032349
theorem B2236599 : Blo 2235435 2236599 := bstep (se 1 (by rfl) ⟨1677449, by rfl⟩ : syracuseStep 2236599 = 3354899) B3354899
theorem B3774269 : Blo 2235435 3774269 := bbase (se 3 (by rfl) ⟨707675, by rfl⟩ : syracuseStep 3774269 = 1415351) (by norm_num)
theorem B2516179 : Blo 2235435 2516179 := bstep (se 1 (by rfl) ⟨1887134, by rfl⟩ : syracuseStep 2516179 = 3774269) B3774269
theorem B3354905 : Blo 2235435 3354905 := bstep (se 2 (by rfl) ⟨1258089, by rfl⟩ : syracuseStep 3354905 = 2516179) B2516179
theorem B2236603 : Blo 2235435 2236603 := bstep (se 1 (by rfl) ⟨1677452, by rfl⟩ : syracuseStep 2236603 = 3354905) B3354905
theorem B2388409 : Blo 2235435 2388409 := bbase (se 2 (by rfl) ⟨895653, by rfl⟩ : syracuseStep 2388409 = 1791307) (by norm_num)
theorem B12738181 : Blo 2235435 12738181 := bstep (se 4 (by rfl) ⟨1194204, by rfl⟩ : syracuseStep 12738181 = 2388409) B2388409
theorem B16984241 : Blo 2235435 16984241 := bstep (se 2 (by rfl) ⟨6369090, by rfl⟩ : syracuseStep 16984241 = 12738181) B12738181
theorem B11322827 : Blo 2235435 11322827 := bstep (se 1 (by rfl) ⟨8492120, by rfl⟩ : syracuseStep 11322827 = 16984241) B16984241
theorem B7548551 : Blo 2235435 7548551 := bstep (se 1 (by rfl) ⟨5661413, by rfl⟩ : syracuseStep 7548551 = 11322827) B11322827
theorem B5032367 : Blo 2235435 5032367 := bstep (se 1 (by rfl) ⟨3774275, by rfl⟩ : syracuseStep 5032367 = 7548551) B7548551
theorem B3354911 : Blo 2235435 3354911 := bstep (se 1 (by rfl) ⟨2516183, by rfl⟩ : syracuseStep 3354911 = 5032367) B5032367
theorem B2236607 : Blo 2235435 2236607 := bstep (se 1 (by rfl) ⟨1677455, by rfl⟩ : syracuseStep 2236607 = 3354911) B3354911
theorem B3354917 : Blo 2235435 3354917 := bbase (se 4 (by rfl) ⟨314523, by rfl⟩ : syracuseStep 3354917 = 629047) (by norm_num)
theorem B2236611 : Blo 2235435 2236611 := bstep (se 1 (by rfl) ⟨1677458, by rfl⟩ : syracuseStep 2236611 = 3354917) B3354917
theorem B2830717 : Blo 2235435 2830717 := bbase (se 3 (by rfl) ⟨530759, by rfl⟩ : syracuseStep 2830717 = 1061519) (by norm_num)
theorem B3774289 : Blo 2235435 3774289 := bstep (se 2 (by rfl) ⟨1415358, by rfl⟩ : syracuseStep 3774289 = 2830717) B2830717
theorem B5032385 : Blo 2235435 5032385 := bstep (se 2 (by rfl) ⟨1887144, by rfl⟩ : syracuseStep 5032385 = 3774289) B3774289
theorem B3354923 : Blo 2235435 3354923 := bstep (se 1 (by rfl) ⟨2516192, by rfl⟩ : syracuseStep 3354923 = 5032385) B5032385
theorem B2236615 : Blo 2235435 2236615 := bstep (se 1 (by rfl) ⟨1677461, by rfl⟩ : syracuseStep 2236615 = 3354923) B3354923
theorem B2516197 : Blo 2235435 2516197 := bbase (se 4 (by rfl) ⟨235893, by rfl⟩ : syracuseStep 2516197 = 471787) (by norm_num)
theorem B3354929 : Blo 2235435 3354929 := bstep (se 2 (by rfl) ⟨1258098, by rfl⟩ : syracuseStep 3354929 = 2516197) B2516197
theorem B2236619 : Blo 2235435 2236619 := bstep (se 1 (by rfl) ⟨1677464, by rfl⟩ : syracuseStep 2236619 = 3354929) B3354929
theorem B4776853 : Blo 2235435 4776853 := bbase (se 6 (by rfl) ⟨111957, by rfl⟩ : syracuseStep 4776853 = 223915) (by norm_num)
theorem B6369137 : Blo 2235435 6369137 := bstep (se 2 (by rfl) ⟨2388426, by rfl⟩ : syracuseStep 6369137 = 4776853) B4776853
theorem B4246091 : Blo 2235435 4246091 := bstep (se 1 (by rfl) ⟨3184568, by rfl⟩ : syracuseStep 4246091 = 6369137) B6369137
theorem B2830727 : Blo 2235435 2830727 := bstep (se 1 (by rfl) ⟨2123045, by rfl⟩ : syracuseStep 2830727 = 4246091) B4246091
theorem B7548605 : Blo 2235435 7548605 := bstep (se 3 (by rfl) ⟨1415363, by rfl⟩ : syracuseStep 7548605 = 2830727) B2830727
theorem B5032403 : Blo 2235435 5032403 := bstep (se 1 (by rfl) ⟨3774302, by rfl⟩ : syracuseStep 5032403 = 7548605) B7548605
theorem B3354935 : Blo 2235435 3354935 := bstep (se 1 (by rfl) ⟨2516201, by rfl⟩ : syracuseStep 3354935 = 5032403) B5032403
theorem B2236623 : Blo 2235435 2236623 := bstep (se 1 (by rfl) ⟨1677467, by rfl⟩ : syracuseStep 2236623 = 3354935) B3354935
theorem B3354941 : Blo 2235435 3354941 := bbase (se 3 (by rfl) ⟨629051, by rfl⟩ : syracuseStep 3354941 = 1258103) (by norm_num)
theorem B2236627 : Blo 2235435 2236627 := bstep (se 1 (by rfl) ⟨1677470, by rfl⟩ : syracuseStep 2236627 = 3354941) B3354941
theorem B5032421 : Blo 2235435 5032421 := bbase (se 4 (by rfl) ⟨471789, by rfl⟩ : syracuseStep 5032421 = 943579) (by norm_num)
theorem B3354947 : Blo 2235435 3354947 := bstep (se 1 (by rfl) ⟨2516210, by rfl⟩ : syracuseStep 3354947 = 5032421) B5032421
theorem B2236631 : Blo 2235435 2236631 := bstep (se 1 (by rfl) ⟨1677473, by rfl⟩ : syracuseStep 2236631 = 3354947) B3354947
theorem B5661485 : Blo 2235435 5661485 := bbase (se 3 (by rfl) ⟨1061528, by rfl⟩ : syracuseStep 5661485 = 2123057) (by norm_num)
theorem B3774323 : Blo 2235435 3774323 := bstep (se 1 (by rfl) ⟨2830742, by rfl⟩ : syracuseStep 3774323 = 5661485) B5661485
theorem B2516215 : Blo 2235435 2516215 := bstep (se 1 (by rfl) ⟨1887161, by rfl⟩ : syracuseStep 2516215 = 3774323) B3774323
theorem B3354953 : Blo 2235435 3354953 := bstep (se 2 (by rfl) ⟨1258107, by rfl⟩ : syracuseStep 3354953 = 2516215) B2516215
theorem B2236635 : Blo 2235435 2236635 := bstep (se 1 (by rfl) ⟨1677476, by rfl⟩ : syracuseStep 2236635 = 3354953) B3354953
theorem B6045749 : Blo 2235435 6045749 := bbase (se 5 (by rfl) ⟨283394, by rfl⟩ : syracuseStep 6045749 = 566789) (by norm_num)
theorem B4030499 : Blo 2235435 4030499 := bstep (se 1 (by rfl) ⟨3022874, by rfl⟩ : syracuseStep 4030499 = 6045749) B6045749
theorem B10747997 : Blo 2235435 10747997 := bstep (se 3 (by rfl) ⟨2015249, by rfl⟩ : syracuseStep 10747997 = 4030499) B4030499
theorem B7165331 : Blo 2235435 7165331 := bstep (se 1 (by rfl) ⟨5373998, by rfl⟩ : syracuseStep 7165331 = 10747997) B10747997
theorem B4776887 : Blo 2235435 4776887 := bstep (se 1 (by rfl) ⟨3582665, by rfl⟩ : syracuseStep 4776887 = 7165331) B7165331
theorem B3184591 : Blo 2235435 3184591 := bstep (se 1 (by rfl) ⟨2388443, by rfl⟩ : syracuseStep 3184591 = 4776887) B4776887
theorem B4246121 : Blo 2235435 4246121 := bstep (se 2 (by rfl) ⟨1592295, by rfl⟩ : syracuseStep 4246121 = 3184591) B3184591
theorem B11322989 : Blo 2235435 11322989 := bstep (se 3 (by rfl) ⟨2123060, by rfl⟩ : syracuseStep 11322989 = 4246121) B4246121
theorem B7548659 : Blo 2235435 7548659 := bstep (se 1 (by rfl) ⟨5661494, by rfl⟩ : syracuseStep 7548659 = 11322989) B11322989
theorem B5032439 : Blo 2235435 5032439 := bstep (se 1 (by rfl) ⟨3774329, by rfl⟩ : syracuseStep 5032439 = 7548659) B7548659
theorem B3354959 : Blo 2235435 3354959 := bstep (se 1 (by rfl) ⟨2516219, by rfl⟩ : syracuseStep 3354959 = 5032439) B5032439
theorem B2236639 : Blo 2235435 2236639 := bstep (se 1 (by rfl) ⟨1677479, by rfl⟩ : syracuseStep 2236639 = 3354959) B3354959
theorem B3354965 : Blo 2235435 3354965 := bbase (se 10 (by rfl) ⟨4914, by rfl⟩ : syracuseStep 3354965 = 9829) (by norm_num)
theorem B2236643 : Blo 2235435 2236643 := bstep (se 1 (by rfl) ⟨1677482, by rfl⟩ : syracuseStep 2236643 = 3354965) B3354965
theorem B6369205 : Blo 2235435 6369205 := bbase (se 5 (by rfl) ⟨298556, by rfl⟩ : syracuseStep 6369205 = 597113) (by norm_num)
theorem B8492273 : Blo 2235435 8492273 := bstep (se 2 (by rfl) ⟨3184602, by rfl⟩ : syracuseStep 8492273 = 6369205) B6369205
theorem B5661515 : Blo 2235435 5661515 := bstep (se 1 (by rfl) ⟨4246136, by rfl⟩ : syracuseStep 5661515 = 8492273) B8492273
theorem B3774343 : Blo 2235435 3774343 := bstep (se 1 (by rfl) ⟨2830757, by rfl⟩ : syracuseStep 3774343 = 5661515) B5661515
theorem B5032457 : Blo 2235435 5032457 := bstep (se 2 (by rfl) ⟨1887171, by rfl⟩ : syracuseStep 5032457 = 3774343) B3774343
theorem B3354971 : Blo 2235435 3354971 := bstep (se 1 (by rfl) ⟨2516228, by rfl⟩ : syracuseStep 3354971 = 5032457) B5032457
theorem B2236647 : Blo 2235435 2236647 := bstep (se 1 (by rfl) ⟨1677485, by rfl⟩ : syracuseStep 2236647 = 3354971) B3354971
theorem B2516233 : Blo 2235435 2516233 := bbase (se 2 (by rfl) ⟨943587, by rfl⟩ : syracuseStep 2516233 = 1887175) (by norm_num)
theorem B3354977 : Blo 2235435 3354977 := bstep (se 2 (by rfl) ⟨1258116, by rfl⟩ : syracuseStep 3354977 = 2516233) B2516233
theorem B2236651 : Blo 2235435 2236651 := bstep (se 1 (by rfl) ⟨1677488, by rfl⟩ : syracuseStep 2236651 = 3354977) B3354977
theorem B28661525 : Blo 2235435 28661525 := bbase (se 6 (by rfl) ⟨671754, by rfl⟩ : syracuseStep 28661525 = 1343509) (by norm_num)
theorem B19107683 : Blo 2235435 19107683 := bstep (se 1 (by rfl) ⟨14330762, by rfl⟩ : syracuseStep 19107683 = 28661525) B28661525
theorem B12738455 : Blo 2235435 12738455 := bstep (se 1 (by rfl) ⟨9553841, by rfl⟩ : syracuseStep 12738455 = 19107683) B19107683
theorem B8492303 : Blo 2235435 8492303 := bstep (se 1 (by rfl) ⟨6369227, by rfl⟩ : syracuseStep 8492303 = 12738455) B12738455
theorem B5661535 : Blo 2235435 5661535 := bstep (se 1 (by rfl) ⟨4246151, by rfl⟩ : syracuseStep 5661535 = 8492303) B8492303
theorem B7548713 : Blo 2235435 7548713 := bstep (se 2 (by rfl) ⟨2830767, by rfl⟩ : syracuseStep 7548713 = 5661535) B5661535
theorem B5032475 : Blo 2235435 5032475 := bstep (se 1 (by rfl) ⟨3774356, by rfl⟩ : syracuseStep 5032475 = 7548713) B7548713
theorem B3354983 : Blo 2235435 3354983 := bstep (se 1 (by rfl) ⟨2516237, by rfl⟩ : syracuseStep 3354983 = 5032475) B5032475
theorem B2236655 : Blo 2235435 2236655 := bstep (se 1 (by rfl) ⟨1677491, by rfl⟩ : syracuseStep 2236655 = 3354983) B3354983
theorem B3354989 : Blo 2235435 3354989 := bbase (se 3 (by rfl) ⟨629060, by rfl⟩ : syracuseStep 3354989 = 1258121) (by norm_num)
theorem B2236659 : Blo 2235435 2236659 := bstep (se 1 (by rfl) ⟨1677494, by rfl⟩ : syracuseStep 2236659 = 3354989) B3354989
theorem B5032493 : Blo 2235435 5032493 := bbase (se 3 (by rfl) ⟨943592, by rfl⟩ : syracuseStep 5032493 = 1887185) (by norm_num)
theorem B3354995 : Blo 2235435 3354995 := bstep (se 1 (by rfl) ⟨2516246, by rfl⟩ : syracuseStep 3354995 = 5032493) B5032493
theorem B2236663 : Blo 2235435 2236663 := bstep (se 1 (by rfl) ⟨1677497, by rfl⟩ : syracuseStep 2236663 = 3354995) B3354995
theorem B5101165 : Blo 2235435 5101165 := bbase (se 3 (by rfl) ⟨956468, by rfl⟩ : syracuseStep 5101165 = 1912937) (by norm_num)
theorem B6801553 : Blo 2235435 6801553 := bstep (se 2 (by rfl) ⟨2550582, by rfl⟩ : syracuseStep 6801553 = 5101165) B5101165
theorem B36274949 : Blo 2235435 36274949 := bstep (se 4 (by rfl) ⟨3400776, by rfl⟩ : syracuseStep 36274949 = 6801553) B6801553
theorem B24183299 : Blo 2235435 24183299 := bstep (se 1 (by rfl) ⟨18137474, by rfl⟩ : syracuseStep 24183299 = 36274949) B36274949
theorem B16122199 : Blo 2235435 16122199 := bstep (se 1 (by rfl) ⟨12091649, by rfl⟩ : syracuseStep 16122199 = 24183299) B24183299
theorem B21496265 : Blo 2235435 21496265 := bstep (se 2 (by rfl) ⟨8061099, by rfl⟩ : syracuseStep 21496265 = 16122199) B16122199
theorem B14330843 : Blo 2235435 14330843 := bstep (se 1 (by rfl) ⟨10748132, by rfl⟩ : syracuseStep 14330843 = 21496265) B21496265
theorem B9553895 : Blo 2235435 9553895 := bstep (se 1 (by rfl) ⟨7165421, by rfl⟩ : syracuseStep 9553895 = 14330843) B14330843
theorem B6369263 : Blo 2235435 6369263 := bstep (se 1 (by rfl) ⟨4776947, by rfl⟩ : syracuseStep 6369263 = 9553895) B9553895
theorem B4246175 : Blo 2235435 4246175 := bstep (se 1 (by rfl) ⟨3184631, by rfl⟩ : syracuseStep 4246175 = 6369263) B6369263
theorem B2830783 : Blo 2235435 2830783 := bstep (se 1 (by rfl) ⟨2123087, by rfl⟩ : syracuseStep 2830783 = 4246175) B4246175
theorem B3774377 : Blo 2235435 3774377 := bstep (se 2 (by rfl) ⟨1415391, by rfl⟩ : syracuseStep 3774377 = 2830783) B2830783
theorem B2516251 : Blo 2235435 2516251 := bstep (se 1 (by rfl) ⟨1887188, by rfl⟩ : syracuseStep 2516251 = 3774377) B3774377
theorem B3355001 : Blo 2235435 3355001 := bstep (se 2 (by rfl) ⟨1258125, by rfl⟩ : syracuseStep 3355001 = 2516251) B2516251
theorem B2236667 : Blo 2235435 2236667 := bstep (se 1 (by rfl) ⟨1677500, by rfl⟩ : syracuseStep 2236667 = 3355001) B3355001
theorem B38215637 : Blo 2235435 38215637 := bbase (se 7 (by rfl) ⟨447839, by rfl⟩ : syracuseStep 38215637 = 895679) (by norm_num)
theorem B25477091 : Blo 2235435 25477091 := bstep (se 1 (by rfl) ⟨19107818, by rfl⟩ : syracuseStep 25477091 = 38215637) B38215637
theorem B16984727 : Blo 2235435 16984727 := bstep (se 1 (by rfl) ⟨12738545, by rfl⟩ : syracuseStep 16984727 = 25477091) B25477091
theorem B11323151 : Blo 2235435 11323151 := bstep (se 1 (by rfl) ⟨8492363, by rfl⟩ : syracuseStep 11323151 = 16984727) B16984727
theorem B7548767 : Blo 2235435 7548767 := bstep (se 1 (by rfl) ⟨5661575, by rfl⟩ : syracuseStep 7548767 = 11323151) B11323151
theorem B5032511 : Blo 2235435 5032511 := bstep (se 1 (by rfl) ⟨3774383, by rfl⟩ : syracuseStep 5032511 = 7548767) B7548767
theorem B3355007 : Blo 2235435 3355007 := bstep (se 1 (by rfl) ⟨2516255, by rfl⟩ : syracuseStep 3355007 = 5032511) B5032511
theorem B2236671 : Blo 2235435 2236671 := bstep (se 1 (by rfl) ⟨1677503, by rfl⟩ : syracuseStep 2236671 = 3355007) B3355007
theorem B3355013 : Blo 2235435 3355013 := bbase (se 4 (by rfl) ⟨314532, by rfl⟩ : syracuseStep 3355013 = 629065) (by norm_num)
theorem B2236675 : Blo 2235435 2236675 := bstep (se 1 (by rfl) ⟨1677506, by rfl⟩ : syracuseStep 2236675 = 3355013) B3355013
theorem B3774397 : Blo 2235435 3774397 := bbase (se 3 (by rfl) ⟨707699, by rfl⟩ : syracuseStep 3774397 = 1415399) (by norm_num)
theorem B5032529 : Blo 2235435 5032529 := bstep (se 2 (by rfl) ⟨1887198, by rfl⟩ : syracuseStep 5032529 = 3774397) B3774397
theorem B3355019 : Blo 2235435 3355019 := bstep (se 1 (by rfl) ⟨2516264, by rfl⟩ : syracuseStep 3355019 = 5032529) B5032529
theorem B2236679 : Blo 2235435 2236679 := bstep (se 1 (by rfl) ⟨1677509, by rfl⟩ : syracuseStep 2236679 = 3355019) B3355019
theorem B2516269 : Blo 2235435 2516269 := bbase (se 3 (by rfl) ⟨471800, by rfl⟩ : syracuseStep 2516269 = 943601) (by norm_num)
theorem B3355025 : Blo 2235435 3355025 := bstep (se 2 (by rfl) ⟨1258134, by rfl⟩ : syracuseStep 3355025 = 2516269) B2516269
theorem B2236683 : Blo 2235435 2236683 := bstep (se 1 (by rfl) ⟨1677512, by rfl⟩ : syracuseStep 2236683 = 3355025) B3355025
theorem B7548821 : Blo 2235435 7548821 := bbase (se 6 (by rfl) ⟨176925, by rfl⟩ : syracuseStep 7548821 = 353851) (by norm_num)
theorem B5032547 : Blo 2235435 5032547 := bstep (se 1 (by rfl) ⟨3774410, by rfl⟩ : syracuseStep 5032547 = 7548821) B7548821
theorem B3355031 : Blo 2235435 3355031 := bstep (se 1 (by rfl) ⟨2516273, by rfl⟩ : syracuseStep 3355031 = 5032547) B5032547
theorem B2236687 : Blo 2235435 2236687 := bstep (se 1 (by rfl) ⟨1677515, by rfl⟩ : syracuseStep 2236687 = 3355031) B3355031
theorem B3355037 : Blo 2235435 3355037 := bbase (se 3 (by rfl) ⟨629069, by rfl⟩ : syracuseStep 3355037 = 1258139) (by norm_num)
theorem B2236691 : Blo 2235435 2236691 := bstep (se 1 (by rfl) ⟨1677518, by rfl⟩ : syracuseStep 2236691 = 3355037) B3355037
theorem B5032565 : Blo 2235435 5032565 := bbase (se 5 (by rfl) ⟨235901, by rfl⟩ : syracuseStep 5032565 = 471803) (by norm_num)
theorem B3355043 : Blo 2235435 3355043 := bstep (se 1 (by rfl) ⟨2516282, by rfl⟩ : syracuseStep 3355043 = 5032565) B5032565
theorem B2236695 : Blo 2235435 2236695 := bstep (se 1 (by rfl) ⟨1677521, by rfl⟩ : syracuseStep 2236695 = 3355043) B3355043
theorem B3631645 : Blo 2235435 3631645 := bbase (se 3 (by rfl) ⟨680933, by rfl⟩ : syracuseStep 3631645 = 1361867) (by norm_num)
theorem B4842193 : Blo 2235435 4842193 := bstep (se 2 (by rfl) ⟨1815822, by rfl⟩ : syracuseStep 4842193 = 3631645) B3631645
theorem B6456257 : Blo 2235435 6456257 := bstep (se 2 (by rfl) ⟨2421096, by rfl⟩ : syracuseStep 6456257 = 4842193) B4842193
theorem B4304171 : Blo 2235435 4304171 := bstep (se 1 (by rfl) ⟨3228128, by rfl⟩ : syracuseStep 4304171 = 6456257) B6456257
theorem B2869447 : Blo 2235435 2869447 := bstep (se 1 (by rfl) ⟨2152085, by rfl⟩ : syracuseStep 2869447 = 4304171) B4304171
theorem B3825929 : Blo 2235435 3825929 := bstep (se 2 (by rfl) ⟨1434723, by rfl⟩ : syracuseStep 3825929 = 2869447) B2869447
theorem B2550619 : Blo 2235435 2550619 := bstep (se 1 (by rfl) ⟨1912964, by rfl⟩ : syracuseStep 2550619 = 3825929) B3825929
theorem B13603301 : Blo 2235435 13603301 := bstep (se 4 (by rfl) ⟨1275309, by rfl⟩ : syracuseStep 13603301 = 2550619) B2550619
theorem B9068867 : Blo 2235435 9068867 := bstep (se 1 (by rfl) ⟨6801650, by rfl⟩ : syracuseStep 9068867 = 13603301) B13603301
theorem B6045911 : Blo 2235435 6045911 := bstep (se 1 (by rfl) ⟨4534433, by rfl⟩ : syracuseStep 6045911 = 9068867) B9068867
theorem B4030607 : Blo 2235435 4030607 := bstep (se 1 (by rfl) ⟨3022955, by rfl⟩ : syracuseStep 4030607 = 6045911) B6045911
theorem B10748285 : Blo 2235435 10748285 := bstep (se 3 (by rfl) ⟨2015303, by rfl⟩ : syracuseStep 10748285 = 4030607) B4030607
theorem B7165523 : Blo 2235435 7165523 := bstep (se 1 (by rfl) ⟨5374142, by rfl⟩ : syracuseStep 7165523 = 10748285) B10748285
theorem B19108061 : Blo 2235435 19108061 := bstep (se 3 (by rfl) ⟨3582761, by rfl⟩ : syracuseStep 19108061 = 7165523) B7165523
theorem B12738707 : Blo 2235435 12738707 := bstep (se 1 (by rfl) ⟨9554030, by rfl⟩ : syracuseStep 12738707 = 19108061) B19108061
theorem B8492471 : Blo 2235435 8492471 := bstep (se 1 (by rfl) ⟨6369353, by rfl⟩ : syracuseStep 8492471 = 12738707) B12738707
theorem B5661647 : Blo 2235435 5661647 := bstep (se 1 (by rfl) ⟨4246235, by rfl⟩ : syracuseStep 5661647 = 8492471) B8492471
theorem B3774431 : Blo 2235435 3774431 := bstep (se 1 (by rfl) ⟨2830823, by rfl⟩ : syracuseStep 3774431 = 5661647) B5661647
theorem B2516287 : Blo 2235435 2516287 := bstep (se 1 (by rfl) ⟨1887215, by rfl⟩ : syracuseStep 2516287 = 3774431) B3774431
theorem B3355049 : Blo 2235435 3355049 := bstep (se 2 (by rfl) ⟨1258143, by rfl⟩ : syracuseStep 3355049 = 2516287) B2516287
theorem B2236699 : Blo 2235435 2236699 := bstep (se 1 (by rfl) ⟨1677524, by rfl⟩ : syracuseStep 2236699 = 3355049) B3355049
theorem B8492485 : Blo 2235435 8492485 := bbase (se 4 (by rfl) ⟨796170, by rfl⟩ : syracuseStep 8492485 = 1592341) (by norm_num)
theorem B11323313 : Blo 2235435 11323313 := bstep (se 2 (by rfl) ⟨4246242, by rfl⟩ : syracuseStep 11323313 = 8492485) B8492485
theorem B7548875 : Blo 2235435 7548875 := bstep (se 1 (by rfl) ⟨5661656, by rfl⟩ : syracuseStep 7548875 = 11323313) B11323313
theorem B5032583 : Blo 2235435 5032583 := bstep (se 1 (by rfl) ⟨3774437, by rfl⟩ : syracuseStep 5032583 = 7548875) B7548875
theorem B3355055 : Blo 2235435 3355055 := bstep (se 1 (by rfl) ⟨2516291, by rfl⟩ : syracuseStep 3355055 = 5032583) B5032583
theorem B2236703 : Blo 2235435 2236703 := bstep (se 1 (by rfl) ⟨1677527, by rfl⟩ : syracuseStep 2236703 = 3355055) B3355055
theorem B3355061 : Blo 2235435 3355061 := bbase (se 5 (by rfl) ⟨157268, by rfl⟩ : syracuseStep 3355061 = 314537) (by norm_num)
theorem B2236707 : Blo 2235435 2236707 := bstep (se 1 (by rfl) ⟨1677530, by rfl⟩ : syracuseStep 2236707 = 3355061) B3355061
theorem B5661677 : Blo 2235435 5661677 := bbase (se 3 (by rfl) ⟨1061564, by rfl⟩ : syracuseStep 5661677 = 2123129) (by norm_num)
theorem B3774451 : Blo 2235435 3774451 := bstep (se 1 (by rfl) ⟨2830838, by rfl⟩ : syracuseStep 3774451 = 5661677) B5661677
theorem B5032601 : Blo 2235435 5032601 := bstep (se 2 (by rfl) ⟨1887225, by rfl⟩ : syracuseStep 5032601 = 3774451) B3774451
theorem B3355067 : Blo 2235435 3355067 := bstep (se 1 (by rfl) ⟨2516300, by rfl⟩ : syracuseStep 3355067 = 5032601) B5032601
theorem B2236711 : Blo 2235435 2236711 := bstep (se 1 (by rfl) ⟨1677533, by rfl⟩ : syracuseStep 2236711 = 3355067) B3355067
theorem B2516305 : Blo 2235435 2516305 := bbase (se 2 (by rfl) ⟨943614, by rfl⟩ : syracuseStep 2516305 = 1887229) (by norm_num)
theorem B3355073 : Blo 2235435 3355073 := bstep (se 2 (by rfl) ⟨1258152, by rfl⟩ : syracuseStep 3355073 = 2516305) B2516305
theorem B2236715 : Blo 2235435 2236715 := bstep (se 1 (by rfl) ⟨1677536, by rfl⟩ : syracuseStep 2236715 = 3355073) B3355073
theorem B2388529 : Blo 2235435 2388529 := bbase (se 2 (by rfl) ⟨895698, by rfl⟩ : syracuseStep 2388529 = 1791397) (by norm_num)
theorem B3184705 : Blo 2235435 3184705 := bstep (se 2 (by rfl) ⟨1194264, by rfl⟩ : syracuseStep 3184705 = 2388529) B2388529
theorem B4246273 : Blo 2235435 4246273 := bstep (se 2 (by rfl) ⟨1592352, by rfl⟩ : syracuseStep 4246273 = 3184705) B3184705
theorem B5661697 : Blo 2235435 5661697 := bstep (se 2 (by rfl) ⟨2123136, by rfl⟩ : syracuseStep 5661697 = 4246273) B4246273
theorem B7548929 : Blo 2235435 7548929 := bstep (se 2 (by rfl) ⟨2830848, by rfl⟩ : syracuseStep 7548929 = 5661697) B5661697
theorem B5032619 : Blo 2235435 5032619 := bstep (se 1 (by rfl) ⟨3774464, by rfl⟩ : syracuseStep 5032619 = 7548929) B7548929
theorem B3355079 : Blo 2235435 3355079 := bstep (se 1 (by rfl) ⟨2516309, by rfl⟩ : syracuseStep 3355079 = 5032619) B5032619
theorem B2236719 : Blo 2235435 2236719 := bstep (se 1 (by rfl) ⟨1677539, by rfl⟩ : syracuseStep 2236719 = 3355079) B3355079
theorem B3355085 : Blo 2235435 3355085 := bbase (se 3 (by rfl) ⟨629078, by rfl⟩ : syracuseStep 3355085 = 1258157) (by norm_num)
theorem B2236723 : Blo 2235435 2236723 := bstep (se 1 (by rfl) ⟨1677542, by rfl⟩ : syracuseStep 2236723 = 3355085) B3355085
theorem B5032637 : Blo 2235435 5032637 := bbase (se 3 (by rfl) ⟨943619, by rfl⟩ : syracuseStep 5032637 = 1887239) (by norm_num)
theorem B3355091 : Blo 2235435 3355091 := bstep (se 1 (by rfl) ⟨2516318, by rfl⟩ : syracuseStep 3355091 = 5032637) B5032637
theorem B2236727 : Blo 2235435 2236727 := bstep (se 1 (by rfl) ⟨1677545, by rfl⟩ : syracuseStep 2236727 = 3355091) B3355091
theorem B3774485 : Blo 2235435 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B2516323 : Blo 2235435 2516323 := bstep (se 1 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 2516323 = 3774485) B3774485
theorem B3355097 : Blo 2235435 3355097 := bstep (se 2 (by rfl) ⟨1258161, by rfl⟩ : syracuseStep 3355097 = 2516323) B2516323
theorem B2236731 : Blo 2235435 2236731 := bstep (se 1 (by rfl) ⟨1677548, by rfl⟩ : syracuseStep 2236731 = 3355097) B3355097
theorem B4842269 : Blo 2235435 4842269 := bbase (se 3 (by rfl) ⟨907925, by rfl⟩ : syracuseStep 4842269 = 1815851) (by norm_num)
theorem B3228179 : Blo 2235435 3228179 := bstep (se 1 (by rfl) ⟨2421134, by rfl⟩ : syracuseStep 3228179 = 4842269) B4842269
theorem B8608477 : Blo 2235435 8608477 := bstep (se 3 (by rfl) ⟨1614089, by rfl⟩ : syracuseStep 8608477 = 3228179) B3228179
theorem B11477969 : Blo 2235435 11477969 := bstep (se 2 (by rfl) ⟨4304238, by rfl⟩ : syracuseStep 11477969 = 8608477) B8608477
theorem B7651979 : Blo 2235435 7651979 := bstep (se 1 (by rfl) ⟨5738984, by rfl⟩ : syracuseStep 7651979 = 11477969) B11477969
theorem B5101319 : Blo 2235435 5101319 := bstep (se 1 (by rfl) ⟨3825989, by rfl⟩ : syracuseStep 5101319 = 7651979) B7651979
theorem B13603517 : Blo 2235435 13603517 := bstep (se 3 (by rfl) ⟨2550659, by rfl⟩ : syracuseStep 13603517 = 5101319) B5101319
theorem B9069011 : Blo 2235435 9069011 := bstep (se 1 (by rfl) ⟨6801758, by rfl⟩ : syracuseStep 9069011 = 13603517) B13603517
theorem B6046007 : Blo 2235435 6046007 := bstep (se 1 (by rfl) ⟨4534505, by rfl⟩ : syracuseStep 6046007 = 9069011) B9069011
theorem B16122685 : Blo 2235435 16122685 := bstep (se 3 (by rfl) ⟨3023003, by rfl⟩ : syracuseStep 16122685 = 6046007) B6046007
theorem B21496913 : Blo 2235435 21496913 := bstep (se 2 (by rfl) ⟨8061342, by rfl⟩ : syracuseStep 21496913 = 16122685) B16122685
theorem B14331275 : Blo 2235435 14331275 := bstep (se 1 (by rfl) ⟨10748456, by rfl⟩ : syracuseStep 14331275 = 21496913) B21496913
theorem B9554183 : Blo 2235435 9554183 := bstep (se 1 (by rfl) ⟨7165637, by rfl⟩ : syracuseStep 9554183 = 14331275) B14331275
theorem B6369455 : Blo 2235435 6369455 := bstep (se 1 (by rfl) ⟨4777091, by rfl⟩ : syracuseStep 6369455 = 9554183) B9554183
theorem B16985213 : Blo 2235435 16985213 := bstep (se 3 (by rfl) ⟨3184727, by rfl⟩ : syracuseStep 16985213 = 6369455) B6369455
theorem B11323475 : Blo 2235435 11323475 := bstep (se 1 (by rfl) ⟨8492606, by rfl⟩ : syracuseStep 11323475 = 16985213) B16985213
theorem B7548983 : Blo 2235435 7548983 := bstep (se 1 (by rfl) ⟨5661737, by rfl⟩ : syracuseStep 7548983 = 11323475) B11323475
theorem B5032655 : Blo 2235435 5032655 := bstep (se 1 (by rfl) ⟨3774491, by rfl⟩ : syracuseStep 5032655 = 7548983) B7548983
theorem B3355103 : Blo 2235435 3355103 := bstep (se 1 (by rfl) ⟨2516327, by rfl⟩ : syracuseStep 3355103 = 5032655) B5032655
theorem B2236735 : Blo 2235435 2236735 := bstep (se 1 (by rfl) ⟨1677551, by rfl⟩ : syracuseStep 2236735 = 3355103) B3355103
theorem B3355109 : Blo 2235435 3355109 := bbase (se 4 (by rfl) ⟨314541, by rfl⟩ : syracuseStep 3355109 = 629083) (by norm_num)
theorem B2236739 : Blo 2235435 2236739 := bstep (se 1 (by rfl) ⟨1677554, by rfl⟩ : syracuseStep 2236739 = 3355109) B3355109
theorem B15724469 : Blo 2235435 15724469 := bbase (se 5 (by rfl) ⟨737084, by rfl⟩ : syracuseStep 15724469 = 1474169) (by norm_num)
theorem B10482979 : Blo 2235435 10482979 := bstep (se 1 (by rfl) ⟨7862234, by rfl⟩ : syracuseStep 10482979 = 15724469) B15724469
theorem B13977305 : Blo 2235435 13977305 := bstep (se 2 (by rfl) ⟨5241489, by rfl⟩ : syracuseStep 13977305 = 10482979) B10482979
theorem B9318203 : Blo 2235435 9318203 := bstep (se 1 (by rfl) ⟨6988652, by rfl⟩ : syracuseStep 9318203 = 13977305) B13977305
theorem B6212135 : Blo 2235435 6212135 := bstep (se 1 (by rfl) ⟨4659101, by rfl⟩ : syracuseStep 6212135 = 9318203) B9318203
theorem B4141423 : Blo 2235435 4141423 := bstep (se 1 (by rfl) ⟨3106067, by rfl⟩ : syracuseStep 4141423 = 6212135) B6212135
theorem B5521897 : Blo 2235435 5521897 := bstep (se 2 (by rfl) ⟨2070711, by rfl⟩ : syracuseStep 5521897 = 4141423) B4141423
theorem B29450117 : Blo 2235435 29450117 := bstep (se 4 (by rfl) ⟨2760948, by rfl⟩ : syracuseStep 29450117 = 5521897) B5521897
theorem B19633411 : Blo 2235435 19633411 := bstep (se 1 (by rfl) ⟨14725058, by rfl⟩ : syracuseStep 19633411 = 29450117) B29450117
theorem B104711525 : Blo 2235435 104711525 := bstep (se 4 (by rfl) ⟨9816705, by rfl⟩ : syracuseStep 104711525 = 19633411) B19633411
theorem B69807683 : Blo 2235435 69807683 := bstep (se 1 (by rfl) ⟨52355762, by rfl⟩ : syracuseStep 69807683 = 104711525) B104711525
theorem B46538455 : Blo 2235435 46538455 := bstep (se 1 (by rfl) ⟨34903841, by rfl⟩ : syracuseStep 46538455 = 69807683) B69807683
theorem B62051273 : Blo 2235435 62051273 := bstep (se 2 (by rfl) ⟨23269227, by rfl⟩ : syracuseStep 62051273 = 46538455) B46538455
theorem B41367515 : Blo 2235435 41367515 := bstep (se 1 (by rfl) ⟨31025636, by rfl⟩ : syracuseStep 41367515 = 62051273) B62051273
theorem B110313373 : Blo 2235435 110313373 := bstep (se 3 (by rfl) ⟨20683757, by rfl⟩ : syracuseStep 110313373 = 41367515) B41367515
theorem B147084497 : Blo 2235435 147084497 := bstep (se 2 (by rfl) ⟨55156686, by rfl⟩ : syracuseStep 147084497 = 110313373) B110313373
theorem B98056331 : Blo 2235435 98056331 := bstep (se 1 (by rfl) ⟨73542248, by rfl⟩ : syracuseStep 98056331 = 147084497) B147084497
theorem B65370887 : Blo 2235435 65370887 := bstep (se 1 (by rfl) ⟨49028165, by rfl⟩ : syracuseStep 65370887 = 98056331) B98056331
theorem B43580591 : Blo 2235435 43580591 := bstep (se 1 (by rfl) ⟨32685443, by rfl⟩ : syracuseStep 43580591 = 65370887) B65370887
theorem B29053727 : Blo 2235435 29053727 := bstep (se 1 (by rfl) ⟨21790295, by rfl⟩ : syracuseStep 29053727 = 43580591) B43580591
theorem B19369151 : Blo 2235435 19369151 := bstep (se 1 (by rfl) ⟨14526863, by rfl⟩ : syracuseStep 19369151 = 29053727) B29053727
theorem B12912767 : Blo 2235435 12912767 := bstep (se 1 (by rfl) ⟨9684575, by rfl⟩ : syracuseStep 12912767 = 19369151) B19369151
theorem B8608511 : Blo 2235435 8608511 := bstep (se 1 (by rfl) ⟨6456383, by rfl⟩ : syracuseStep 8608511 = 12912767) B12912767
theorem B5739007 : Blo 2235435 5739007 := bstep (se 1 (by rfl) ⟨4304255, by rfl⟩ : syracuseStep 5739007 = 8608511) B8608511
theorem B7652009 : Blo 2235435 7652009 := bstep (se 2 (by rfl) ⟨2869503, by rfl⟩ : syracuseStep 7652009 = 5739007) B5739007
theorem B5101339 : Blo 2235435 5101339 := bstep (se 1 (by rfl) ⟨3826004, by rfl⟩ : syracuseStep 5101339 = 7652009) B7652009
theorem B6801785 : Blo 2235435 6801785 := bstep (se 2 (by rfl) ⟨2550669, by rfl⟩ : syracuseStep 6801785 = 5101339) B5101339
theorem B4534523 : Blo 2235435 4534523 := bstep (se 1 (by rfl) ⟨3400892, by rfl⟩ : syracuseStep 4534523 = 6801785) B6801785
theorem B3023015 : Blo 2235435 3023015 := bstep (se 1 (by rfl) ⟨2267261, by rfl⟩ : syracuseStep 3023015 = 4534523) B4534523
theorem B8061373 : Blo 2235435 8061373 := bstep (se 3 (by rfl) ⟨1511507, by rfl⟩ : syracuseStep 8061373 = 3023015) B3023015
theorem B10748497 : Blo 2235435 10748497 := bstep (se 2 (by rfl) ⟨4030686, by rfl⟩ : syracuseStep 10748497 = 8061373) B8061373
theorem B14331329 : Blo 2235435 14331329 := bstep (se 2 (by rfl) ⟨5374248, by rfl⟩ : syracuseStep 14331329 = 10748497) B10748497
theorem B9554219 : Blo 2235435 9554219 := bstep (se 1 (by rfl) ⟨7165664, by rfl⟩ : syracuseStep 9554219 = 14331329) B14331329
theorem B6369479 : Blo 2235435 6369479 := bstep (se 1 (by rfl) ⟨4777109, by rfl⟩ : syracuseStep 6369479 = 9554219) B9554219
theorem B4246319 : Blo 2235435 4246319 := bstep (se 1 (by rfl) ⟨3184739, by rfl⟩ : syracuseStep 4246319 = 6369479) B6369479
theorem B2830879 : Blo 2235435 2830879 := bstep (se 1 (by rfl) ⟨2123159, by rfl⟩ : syracuseStep 2830879 = 4246319) B4246319
theorem B3774505 : Blo 2235435 3774505 := bstep (se 2 (by rfl) ⟨1415439, by rfl⟩ : syracuseStep 3774505 = 2830879) B2830879
theorem B5032673 : Blo 2235435 5032673 := bstep (se 2 (by rfl) ⟨1887252, by rfl⟩ : syracuseStep 5032673 = 3774505) B3774505
theorem B3355115 : Blo 2235435 3355115 := bstep (se 1 (by rfl) ⟨2516336, by rfl⟩ : syracuseStep 3355115 = 5032673) B5032673
theorem B2236743 : Blo 2235435 2236743 := bstep (se 1 (by rfl) ⟨1677557, by rfl⟩ : syracuseStep 2236743 = 3355115) B3355115
theorem B2516341 : Blo 2235435 2516341 := bbase (se 5 (by rfl) ⟨117953, by rfl⟩ : syracuseStep 2516341 = 235907) (by norm_num)
theorem B3355121 : Blo 2235435 3355121 := bstep (se 2 (by rfl) ⟨1258170, by rfl⟩ : syracuseStep 3355121 = 2516341) B2516341
theorem B2236747 : Blo 2235435 2236747 := bstep (se 1 (by rfl) ⟨1677560, by rfl⟩ : syracuseStep 2236747 = 3355121) B3355121
theorem B2830889 : Blo 2235435 2830889 := bbase (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) (by norm_num)
theorem B7549037 : Blo 2235435 7549037 := bstep (se 3 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 7549037 = 2830889) B2830889
theorem B5032691 : Blo 2235435 5032691 := bstep (se 1 (by rfl) ⟨3774518, by rfl⟩ : syracuseStep 5032691 = 7549037) B7549037
theorem B3355127 : Blo 2235435 3355127 := bstep (se 1 (by rfl) ⟨2516345, by rfl⟩ : syracuseStep 3355127 = 5032691) B5032691
theorem B2236751 : Blo 2235435 2236751 := bstep (se 1 (by rfl) ⟨1677563, by rfl⟩ : syracuseStep 2236751 = 3355127) B3355127
theorem B3355133 : Blo 2235435 3355133 := bbase (se 3 (by rfl) ⟨629087, by rfl⟩ : syracuseStep 3355133 = 1258175) (by norm_num)
theorem B2236755 : Blo 2235435 2236755 := bstep (se 1 (by rfl) ⟨1677566, by rfl⟩ : syracuseStep 2236755 = 3355133) B3355133
theorem B5032709 : Blo 2235435 5032709 := bbase (se 4 (by rfl) ⟨471816, by rfl⟩ : syracuseStep 5032709 = 943633) (by norm_num)
theorem B3355139 : Blo 2235435 3355139 := bstep (se 1 (by rfl) ⟨2516354, by rfl⟩ : syracuseStep 3355139 = 5032709) B5032709
theorem B2236759 : Blo 2235435 2236759 := bstep (se 1 (by rfl) ⟨1677569, by rfl⟩ : syracuseStep 2236759 = 3355139) B3355139
theorem B4246357 : Blo 2235435 4246357 := bbase (se 9 (by rfl) ⟨12440, by rfl⟩ : syracuseStep 4246357 = 24881) (by norm_num)
theorem B5661809 : Blo 2235435 5661809 := bstep (se 2 (by rfl) ⟨2123178, by rfl⟩ : syracuseStep 5661809 = 4246357) B4246357
theorem B3774539 : Blo 2235435 3774539 := bstep (se 1 (by rfl) ⟨2830904, by rfl⟩ : syracuseStep 3774539 = 5661809) B5661809
theorem B2516359 : Blo 2235435 2516359 := bstep (se 1 (by rfl) ⟨1887269, by rfl⟩ : syracuseStep 2516359 = 3774539) B3774539
theorem B3355145 : Blo 2235435 3355145 := bstep (se 2 (by rfl) ⟨1258179, by rfl⟩ : syracuseStep 3355145 = 2516359) B2516359
theorem B2236763 : Blo 2235435 2236763 := bstep (se 1 (by rfl) ⟨1677572, by rfl⟩ : syracuseStep 2236763 = 3355145) B3355145
theorem B11323637 : Blo 2235435 11323637 := bbase (se 5 (by rfl) ⟨530795, by rfl⟩ : syracuseStep 11323637 = 1061591) (by norm_num)
theorem B7549091 : Blo 2235435 7549091 := bstep (se 1 (by rfl) ⟨5661818, by rfl⟩ : syracuseStep 7549091 = 11323637) B11323637
theorem B5032727 : Blo 2235435 5032727 := bstep (se 1 (by rfl) ⟨3774545, by rfl⟩ : syracuseStep 5032727 = 7549091) B7549091
theorem B3355151 : Blo 2235435 3355151 := bstep (se 1 (by rfl) ⟨2516363, by rfl⟩ : syracuseStep 3355151 = 5032727) B5032727
theorem B2236767 : Blo 2235435 2236767 := bstep (se 1 (by rfl) ⟨1677575, by rfl⟩ : syracuseStep 2236767 = 3355151) B3355151
theorem B3355157 : Blo 2235435 3355157 := bbase (se 6 (by rfl) ⟨78636, by rfl⟩ : syracuseStep 3355157 = 157273) (by norm_num)
theorem B2236771 : Blo 2235435 2236771 := bstep (se 1 (by rfl) ⟨1677578, by rfl⟩ : syracuseStep 2236771 = 3355157) B3355157
theorem B5374325 : Blo 2235435 5374325 := bbase (se 5 (by rfl) ⟨251921, by rfl⟩ : syracuseStep 5374325 = 503843) (by norm_num)
theorem B3582883 : Blo 2235435 3582883 := bstep (se 1 (by rfl) ⟨2687162, by rfl⟩ : syracuseStep 3582883 = 5374325) B5374325
theorem B19108709 : Blo 2235435 19108709 := bstep (se 4 (by rfl) ⟨1791441, by rfl⟩ : syracuseStep 19108709 = 3582883) B3582883
theorem B12739139 : Blo 2235435 12739139 := bstep (se 1 (by rfl) ⟨9554354, by rfl⟩ : syracuseStep 12739139 = 19108709) B19108709
theorem B8492759 : Blo 2235435 8492759 := bstep (se 1 (by rfl) ⟨6369569, by rfl⟩ : syracuseStep 8492759 = 12739139) B12739139
theorem B5661839 : Blo 2235435 5661839 := bstep (se 1 (by rfl) ⟨4246379, by rfl⟩ : syracuseStep 5661839 = 8492759) B8492759
theorem B3774559 : Blo 2235435 3774559 := bstep (se 1 (by rfl) ⟨2830919, by rfl⟩ : syracuseStep 3774559 = 5661839) B5661839
theorem B5032745 : Blo 2235435 5032745 := bstep (se 2 (by rfl) ⟨1887279, by rfl⟩ : syracuseStep 5032745 = 3774559) B3774559
theorem B3355163 : Blo 2235435 3355163 := bstep (se 1 (by rfl) ⟨2516372, by rfl⟩ : syracuseStep 3355163 = 5032745) B5032745
theorem B2236775 : Blo 2235435 2236775 := bstep (se 1 (by rfl) ⟨1677581, by rfl⟩ : syracuseStep 2236775 = 3355163) B3355163
theorem B2516377 : Blo 2235435 2516377 := bbase (se 2 (by rfl) ⟨943641, by rfl⟩ : syracuseStep 2516377 = 1887283) (by norm_num)
theorem B3355169 : Blo 2235435 3355169 := bstep (se 2 (by rfl) ⟨1258188, by rfl⟩ : syracuseStep 3355169 = 2516377) B2516377
theorem B2236779 : Blo 2235435 2236779 := bstep (se 1 (by rfl) ⟨1677584, by rfl⟩ : syracuseStep 2236779 = 3355169) B3355169
theorem B8492789 : Blo 2235435 8492789 := bbase (se 5 (by rfl) ⟨398099, by rfl⟩ : syracuseStep 8492789 = 796199) (by norm_num)
theorem B5661859 : Blo 2235435 5661859 := bstep (se 1 (by rfl) ⟨4246394, by rfl⟩ : syracuseStep 5661859 = 8492789) B8492789
theorem B7549145 : Blo 2235435 7549145 := bstep (se 2 (by rfl) ⟨2830929, by rfl⟩ : syracuseStep 7549145 = 5661859) B5661859
theorem B5032763 : Blo 2235435 5032763 := bstep (se 1 (by rfl) ⟨3774572, by rfl⟩ : syracuseStep 5032763 = 7549145) B7549145
theorem B3355175 : Blo 2235435 3355175 := bstep (se 1 (by rfl) ⟨2516381, by rfl⟩ : syracuseStep 3355175 = 5032763) B5032763
theorem B2236783 : Blo 2235435 2236783 := bstep (se 1 (by rfl) ⟨1677587, by rfl⟩ : syracuseStep 2236783 = 3355175) B3355175
theorem B3355181 : Blo 2235435 3355181 := bbase (se 3 (by rfl) ⟨629096, by rfl⟩ : syracuseStep 3355181 = 1258193) (by norm_num)
theorem B2236787 : Blo 2235435 2236787 := bstep (se 1 (by rfl) ⟨1677590, by rfl⟩ : syracuseStep 2236787 = 3355181) B3355181
theorem B5032781 : Blo 2235435 5032781 := bbase (se 3 (by rfl) ⟨943646, by rfl⟩ : syracuseStep 5032781 = 1887293) (by norm_num)
theorem B3355187 : Blo 2235435 3355187 := bstep (se 1 (by rfl) ⟨2516390, by rfl⟩ : syracuseStep 3355187 = 5032781) B5032781
theorem B2236791 : Blo 2235435 2236791 := bstep (se 1 (by rfl) ⟨1677593, by rfl⟩ : syracuseStep 2236791 = 3355187) B3355187
theorem B2830945 : Blo 2235435 2830945 := bbase (se 2 (by rfl) ⟨1061604, by rfl⟩ : syracuseStep 2830945 = 2123209) (by norm_num)
theorem B3774593 : Blo 2235435 3774593 := bstep (se 2 (by rfl) ⟨1415472, by rfl⟩ : syracuseStep 3774593 = 2830945) B2830945
theorem B2516395 : Blo 2235435 2516395 := bstep (se 1 (by rfl) ⟨1887296, by rfl⟩ : syracuseStep 2516395 = 3774593) B3774593
theorem B3355193 : Blo 2235435 3355193 := bstep (se 2 (by rfl) ⟨1258197, by rfl⟩ : syracuseStep 3355193 = 2516395) B2516395
theorem B2236795 : Blo 2235435 2236795 := bstep (se 1 (by rfl) ⟨1677596, by rfl⟩ : syracuseStep 2236795 = 3355193) B3355193
theorem B25478549 : Blo 2235435 25478549 := bbase (se 6 (by rfl) ⟨597153, by rfl⟩ : syracuseStep 25478549 = 1194307) (by norm_num)
theorem B16985699 : Blo 2235435 16985699 := bstep (se 1 (by rfl) ⟨12739274, by rfl⟩ : syracuseStep 16985699 = 25478549) B25478549
theorem B11323799 : Blo 2235435 11323799 := bstep (se 1 (by rfl) ⟨8492849, by rfl⟩ : syracuseStep 11323799 = 16985699) B16985699
theorem B7549199 : Blo 2235435 7549199 := bstep (se 1 (by rfl) ⟨5661899, by rfl⟩ : syracuseStep 7549199 = 11323799) B11323799
theorem B5032799 : Blo 2235435 5032799 := bstep (se 1 (by rfl) ⟨3774599, by rfl⟩ : syracuseStep 5032799 = 7549199) B7549199
theorem B3355199 : Blo 2235435 3355199 := bstep (se 1 (by rfl) ⟨2516399, by rfl⟩ : syracuseStep 3355199 = 5032799) B5032799
theorem B2236799 : Blo 2235435 2236799 := bstep (se 1 (by rfl) ⟨1677599, by rfl⟩ : syracuseStep 2236799 = 3355199) B3355199
theorem B3355205 : Blo 2235435 3355205 := bbase (se 4 (by rfl) ⟨314550, by rfl⟩ : syracuseStep 3355205 = 629101) (by norm_num)
theorem B2236803 : Blo 2235435 2236803 := bstep (se 1 (by rfl) ⟨1677602, by rfl⟩ : syracuseStep 2236803 = 3355205) B3355205
theorem B3774613 : Blo 2235435 3774613 := bbase (se 6 (by rfl) ⟨88467, by rfl⟩ : syracuseStep 3774613 = 176935) (by norm_num)
theorem B5032817 : Blo 2235435 5032817 := bstep (se 2 (by rfl) ⟨1887306, by rfl⟩ : syracuseStep 5032817 = 3774613) B3774613
theorem B3355211 : Blo 2235435 3355211 := bstep (se 1 (by rfl) ⟨2516408, by rfl⟩ : syracuseStep 3355211 = 5032817) B5032817
theorem B2236807 : Blo 2235435 2236807 := bstep (se 1 (by rfl) ⟨1677605, by rfl⟩ : syracuseStep 2236807 = 3355211) B3355211
theorem B2516413 : Blo 2235435 2516413 := bbase (se 3 (by rfl) ⟨471827, by rfl⟩ : syracuseStep 2516413 = 943655) (by norm_num)
theorem B3355217 : Blo 2235435 3355217 := bstep (se 2 (by rfl) ⟨1258206, by rfl⟩ : syracuseStep 3355217 = 2516413) B2516413
theorem B2236811 : Blo 2235435 2236811 := bstep (se 1 (by rfl) ⟨1677608, by rfl⟩ : syracuseStep 2236811 = 3355217) B3355217
theorem B7549253 : Blo 2235435 7549253 := bbase (se 4 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 7549253 = 1415485) (by norm_num)
theorem B5032835 : Blo 2235435 5032835 := bstep (se 1 (by rfl) ⟨3774626, by rfl⟩ : syracuseStep 5032835 = 7549253) B7549253
theorem B3355223 : Blo 2235435 3355223 := bstep (se 1 (by rfl) ⟨2516417, by rfl⟩ : syracuseStep 3355223 = 5032835) B5032835
theorem B2236815 : Blo 2235435 2236815 := bstep (se 1 (by rfl) ⟨1677611, by rfl⟩ : syracuseStep 2236815 = 3355223) B3355223
theorem B3355229 : Blo 2235435 3355229 := bbase (se 3 (by rfl) ⟨629105, by rfl⟩ : syracuseStep 3355229 = 1258211) (by norm_num)
theorem B2236819 : Blo 2235435 2236819 := bstep (se 1 (by rfl) ⟨1677614, by rfl⟩ : syracuseStep 2236819 = 3355229) B3355229
theorem B5032853 : Blo 2235435 5032853 := bbase (se 6 (by rfl) ⟨117957, by rfl⟩ : syracuseStep 5032853 = 235915) (by norm_num)
theorem B3355235 : Blo 2235435 3355235 := bstep (se 1 (by rfl) ⟨2516426, by rfl⟩ : syracuseStep 3355235 = 5032853) B5032853
theorem B2236823 : Blo 2235435 2236823 := bstep (se 1 (by rfl) ⟨1677617, by rfl⟩ : syracuseStep 2236823 = 3355235) B3355235
theorem B3401021 : Blo 2235435 3401021 := bbase (se 3 (by rfl) ⟨637691, by rfl⟩ : syracuseStep 3401021 = 1275383) (by norm_num)
theorem B2267347 : Blo 2235435 2267347 := bstep (se 1 (by rfl) ⟨1700510, by rfl⟩ : syracuseStep 2267347 = 3401021) B3401021
theorem B3023129 : Blo 2235435 3023129 := bstep (se 2 (by rfl) ⟨1133673, by rfl⟩ : syracuseStep 3023129 = 2267347) B2267347
theorem B8061677 : Blo 2235435 8061677 := bstep (se 3 (by rfl) ⟨1511564, by rfl⟩ : syracuseStep 8061677 = 3023129) B3023129
theorem B5374451 : Blo 2235435 5374451 := bstep (se 1 (by rfl) ⟨4030838, by rfl⟩ : syracuseStep 5374451 = 8061677) B8061677
theorem B3582967 : Blo 2235435 3582967 := bstep (se 1 (by rfl) ⟨2687225, by rfl⟩ : syracuseStep 3582967 = 5374451) B5374451
theorem B4777289 : Blo 2235435 4777289 := bstep (se 2 (by rfl) ⟨1791483, by rfl⟩ : syracuseStep 4777289 = 3582967) B3582967
theorem B3184859 : Blo 2235435 3184859 := bstep (se 1 (by rfl) ⟨2388644, by rfl⟩ : syracuseStep 3184859 = 4777289) B4777289
theorem B8492957 : Blo 2235435 8492957 := bstep (se 3 (by rfl) ⟨1592429, by rfl⟩ : syracuseStep 8492957 = 3184859) B3184859
theorem B5661971 : Blo 2235435 5661971 := bstep (se 1 (by rfl) ⟨4246478, by rfl⟩ : syracuseStep 5661971 = 8492957) B8492957
theorem B3774647 : Blo 2235435 3774647 := bstep (se 1 (by rfl) ⟨2830985, by rfl⟩ : syracuseStep 3774647 = 5661971) B5661971
theorem B2516431 : Blo 2235435 2516431 := bstep (se 1 (by rfl) ⟨1887323, by rfl⟩ : syracuseStep 2516431 = 3774647) B3774647
theorem B3355241 : Blo 2235435 3355241 := bstep (se 2 (by rfl) ⟨1258215, by rfl⟩ : syracuseStep 3355241 = 2516431) B2516431
theorem B2236827 : Blo 2235435 2236827 := bstep (se 1 (by rfl) ⟨1677620, by rfl⟩ : syracuseStep 2236827 = 3355241) B3355241
theorem B10203077 : Blo 2235435 10203077 := bbase (se 4 (by rfl) ⟨956538, by rfl⟩ : syracuseStep 10203077 = 1913077) (by norm_num)
theorem B6802051 : Blo 2235435 6802051 := bstep (se 1 (by rfl) ⟨5101538, by rfl⟩ : syracuseStep 6802051 = 10203077) B10203077
theorem B9069401 : Blo 2235435 9069401 := bstep (se 2 (by rfl) ⟨3401025, by rfl⟩ : syracuseStep 9069401 = 6802051) B6802051
theorem B6046267 : Blo 2235435 6046267 := bstep (se 1 (by rfl) ⟨4534700, by rfl⟩ : syracuseStep 6046267 = 9069401) B9069401
theorem B8061689 : Blo 2235435 8061689 := bstep (se 2 (by rfl) ⟨3023133, by rfl⟩ : syracuseStep 8061689 = 6046267) B6046267
theorem B5374459 : Blo 2235435 5374459 := bstep (se 1 (by rfl) ⟨4030844, by rfl⟩ : syracuseStep 5374459 = 8061689) B8061689
theorem B7165945 : Blo 2235435 7165945 := bstep (se 2 (by rfl) ⟨2687229, by rfl⟩ : syracuseStep 7165945 = 5374459) B5374459
theorem B9554593 : Blo 2235435 9554593 := bstep (se 2 (by rfl) ⟨3582972, by rfl⟩ : syracuseStep 9554593 = 7165945) B7165945
theorem B12739457 : Blo 2235435 12739457 := bstep (se 2 (by rfl) ⟨4777296, by rfl⟩ : syracuseStep 12739457 = 9554593) B9554593
theorem B8492971 : Blo 2235435 8492971 := bstep (se 1 (by rfl) ⟨6369728, by rfl⟩ : syracuseStep 8492971 = 12739457) B12739457
theorem B11323961 : Blo 2235435 11323961 := bstep (se 2 (by rfl) ⟨4246485, by rfl⟩ : syracuseStep 11323961 = 8492971) B8492971
theorem B7549307 : Blo 2235435 7549307 := bstep (se 1 (by rfl) ⟨5661980, by rfl⟩ : syracuseStep 7549307 = 11323961) B11323961
theorem B5032871 : Blo 2235435 5032871 := bstep (se 1 (by rfl) ⟨3774653, by rfl⟩ : syracuseStep 5032871 = 7549307) B7549307
theorem B3355247 : Blo 2235435 3355247 := bstep (se 1 (by rfl) ⟨2516435, by rfl⟩ : syracuseStep 3355247 = 5032871) B5032871
theorem B2236831 : Blo 2235435 2236831 := bstep (se 1 (by rfl) ⟨1677623, by rfl⟩ : syracuseStep 2236831 = 3355247) B3355247
theorem B3355253 : Blo 2235435 3355253 := bbase (se 5 (by rfl) ⟨157277, by rfl⟩ : syracuseStep 3355253 = 314555) (by norm_num)
theorem B2236835 : Blo 2235435 2236835 := bstep (se 1 (by rfl) ⟨1677626, by rfl⟩ : syracuseStep 2236835 = 3355253) B3355253
theorem B4246501 : Blo 2235435 4246501 := bbase (se 4 (by rfl) ⟨398109, by rfl⟩ : syracuseStep 4246501 = 796219) (by norm_num)
theorem B5662001 : Blo 2235435 5662001 := bstep (se 2 (by rfl) ⟨2123250, by rfl⟩ : syracuseStep 5662001 = 4246501) B4246501
theorem B3774667 : Blo 2235435 3774667 := bstep (se 1 (by rfl) ⟨2831000, by rfl⟩ : syracuseStep 3774667 = 5662001) B5662001
theorem B5032889 : Blo 2235435 5032889 := bstep (se 2 (by rfl) ⟨1887333, by rfl⟩ : syracuseStep 5032889 = 3774667) B3774667
theorem B3355259 : Blo 2235435 3355259 := bstep (se 1 (by rfl) ⟨2516444, by rfl⟩ : syracuseStep 3355259 = 5032889) B5032889
theorem B2236839 : Blo 2235435 2236839 := bstep (se 1 (by rfl) ⟨1677629, by rfl⟩ : syracuseStep 2236839 = 3355259) B3355259
theorem B2516449 : Blo 2235435 2516449 := bbase (se 2 (by rfl) ⟨943668, by rfl⟩ : syracuseStep 2516449 = 1887337) (by norm_num)
theorem B3355265 : Blo 2235435 3355265 := bstep (se 2 (by rfl) ⟨1258224, by rfl⟩ : syracuseStep 3355265 = 2516449) B2516449
theorem B2236843 : Blo 2235435 2236843 := bstep (se 1 (by rfl) ⟨1677632, by rfl⟩ : syracuseStep 2236843 = 3355265) B3355265
theorem B5662021 : Blo 2235435 5662021 := bbase (se 4 (by rfl) ⟨530814, by rfl⟩ : syracuseStep 5662021 = 1061629) (by norm_num)
theorem B7549361 : Blo 2235435 7549361 := bstep (se 2 (by rfl) ⟨2831010, by rfl⟩ : syracuseStep 7549361 = 5662021) B5662021
theorem B5032907 : Blo 2235435 5032907 := bstep (se 1 (by rfl) ⟨3774680, by rfl⟩ : syracuseStep 5032907 = 7549361) B7549361
theorem B3355271 : Blo 2235435 3355271 := bstep (se 1 (by rfl) ⟨2516453, by rfl⟩ : syracuseStep 3355271 = 5032907) B5032907
theorem B2236847 : Blo 2235435 2236847 := bstep (se 1 (by rfl) ⟨1677635, by rfl⟩ : syracuseStep 2236847 = 3355271) B3355271
theorem B3355277 : Blo 2235435 3355277 := bbase (se 3 (by rfl) ⟨629114, by rfl⟩ : syracuseStep 3355277 = 1258229) (by norm_num)
theorem B2236851 : Blo 2235435 2236851 := bstep (se 1 (by rfl) ⟨1677638, by rfl⟩ : syracuseStep 2236851 = 3355277) B3355277
theorem B5032925 : Blo 2235435 5032925 := bbase (se 3 (by rfl) ⟨943673, by rfl⟩ : syracuseStep 5032925 = 1887347) (by norm_num)
theorem B3355283 : Blo 2235435 3355283 := bstep (se 1 (by rfl) ⟨2516462, by rfl⟩ : syracuseStep 3355283 = 5032925) B5032925
theorem B2236855 : Blo 2235435 2236855 := bstep (se 1 (by rfl) ⟨1677641, by rfl⟩ : syracuseStep 2236855 = 3355283) B3355283
theorem B3774701 : Blo 2235435 3774701 := bbase (se 3 (by rfl) ⟨707756, by rfl⟩ : syracuseStep 3774701 = 1415513) (by norm_num)
theorem B2516467 : Blo 2235435 2516467 := bstep (se 1 (by rfl) ⟨1887350, by rfl⟩ : syracuseStep 2516467 = 3774701) B3774701
theorem B3355289 : Blo 2235435 3355289 := bstep (se 2 (by rfl) ⟨1258233, by rfl⟩ : syracuseStep 3355289 = 2516467) B2516467
theorem B2236859 : Blo 2235435 2236859 := bstep (se 1 (by rfl) ⟨1677644, by rfl⟩ : syracuseStep 2236859 = 3355289) B3355289
theorem B10203221 : Blo 2235435 10203221 := bbase (se 8 (by rfl) ⟨59784, by rfl⟩ : syracuseStep 10203221 = 119569) (by norm_num)
theorem B6802147 : Blo 2235435 6802147 := bstep (se 1 (by rfl) ⟨5101610, by rfl⟩ : syracuseStep 6802147 = 10203221) B10203221
theorem B36278117 : Blo 2235435 36278117 := bstep (se 4 (by rfl) ⟨3401073, by rfl⟩ : syracuseStep 36278117 = 6802147) B6802147
theorem B24185411 : Blo 2235435 24185411 := bstep (se 1 (by rfl) ⟨18139058, by rfl⟩ : syracuseStep 24185411 = 36278117) B36278117
theorem B16123607 : Blo 2235435 16123607 := bstep (se 1 (by rfl) ⟨12092705, by rfl⟩ : syracuseStep 16123607 = 24185411) B24185411
theorem B10749071 : Blo 2235435 10749071 := bstep (se 1 (by rfl) ⟨8061803, by rfl⟩ : syracuseStep 10749071 = 16123607) B16123607
theorem B28664189 : Blo 2235435 28664189 := bstep (se 3 (by rfl) ⟨5374535, by rfl⟩ : syracuseStep 28664189 = 10749071) B10749071
theorem B19109459 : Blo 2235435 19109459 := bstep (se 1 (by rfl) ⟨14332094, by rfl⟩ : syracuseStep 19109459 = 28664189) B28664189
theorem B12739639 : Blo 2235435 12739639 := bstep (se 1 (by rfl) ⟨9554729, by rfl⟩ : syracuseStep 12739639 = 19109459) B19109459
theorem B16986185 : Blo 2235435 16986185 := bstep (se 2 (by rfl) ⟨6369819, by rfl⟩ : syracuseStep 16986185 = 12739639) B12739639
theorem B11324123 : Blo 2235435 11324123 := bstep (se 1 (by rfl) ⟨8493092, by rfl⟩ : syracuseStep 11324123 = 16986185) B16986185
theorem B7549415 : Blo 2235435 7549415 := bstep (se 1 (by rfl) ⟨5662061, by rfl⟩ : syracuseStep 7549415 = 11324123) B11324123
theorem B5032943 : Blo 2235435 5032943 := bstep (se 1 (by rfl) ⟨3774707, by rfl⟩ : syracuseStep 5032943 = 7549415) B7549415
theorem B3355295 : Blo 2235435 3355295 := bstep (se 1 (by rfl) ⟨2516471, by rfl⟩ : syracuseStep 3355295 = 5032943) B5032943
theorem B2236863 : Blo 2235435 2236863 := bstep (se 1 (by rfl) ⟨1677647, by rfl⟩ : syracuseStep 2236863 = 3355295) B3355295
theorem B3355301 : Blo 2235435 3355301 := bbase (se 4 (by rfl) ⟨314559, by rfl⟩ : syracuseStep 3355301 = 629119) (by norm_num)
theorem B2236867 : Blo 2235435 2236867 := bstep (se 1 (by rfl) ⟨1677650, by rfl⟩ : syracuseStep 2236867 = 3355301) B3355301
theorem B2831041 : Blo 2235435 2831041 := bbase (se 2 (by rfl) ⟨1061640, by rfl⟩ : syracuseStep 2831041 = 2123281) (by norm_num)
theorem B3774721 : Blo 2235435 3774721 := bstep (se 2 (by rfl) ⟨1415520, by rfl⟩ : syracuseStep 3774721 = 2831041) B2831041
theorem B5032961 : Blo 2235435 5032961 := bstep (se 2 (by rfl) ⟨1887360, by rfl⟩ : syracuseStep 5032961 = 3774721) B3774721
theorem B3355307 : Blo 2235435 3355307 := bstep (se 1 (by rfl) ⟨2516480, by rfl⟩ : syracuseStep 3355307 = 5032961) B5032961
theorem B2236871 : Blo 2235435 2236871 := bstep (se 1 (by rfl) ⟨1677653, by rfl⟩ : syracuseStep 2236871 = 3355307) B3355307
theorem B2516485 : Blo 2235435 2516485 := bbase (se 4 (by rfl) ⟨235920, by rfl⟩ : syracuseStep 2516485 = 471841) (by norm_num)
theorem B3355313 : Blo 2235435 3355313 := bstep (se 2 (by rfl) ⟨1258242, by rfl⟩ : syracuseStep 3355313 = 2516485) B2516485
theorem B2236875 : Blo 2235435 2236875 := bstep (se 1 (by rfl) ⟨1677656, by rfl⟩ : syracuseStep 2236875 = 3355313) B3355313
theorem B3184933 : Blo 2235435 3184933 := bbase (se 4 (by rfl) ⟨298587, by rfl⟩ : syracuseStep 3184933 = 597175) (by norm_num)
theorem B4246577 : Blo 2235435 4246577 := bstep (se 2 (by rfl) ⟨1592466, by rfl⟩ : syracuseStep 4246577 = 3184933) B3184933
theorem B2831051 : Blo 2235435 2831051 := bstep (se 1 (by rfl) ⟨2123288, by rfl⟩ : syracuseStep 2831051 = 4246577) B4246577
theorem B7549469 : Blo 2235435 7549469 := bstep (se 3 (by rfl) ⟨1415525, by rfl⟩ : syracuseStep 7549469 = 2831051) B2831051
theorem B5032979 : Blo 2235435 5032979 := bstep (se 1 (by rfl) ⟨3774734, by rfl⟩ : syracuseStep 5032979 = 7549469) B7549469
theorem B3355319 : Blo 2235435 3355319 := bstep (se 1 (by rfl) ⟨2516489, by rfl⟩ : syracuseStep 3355319 = 5032979) B5032979
theorem B2236879 : Blo 2235435 2236879 := bstep (se 1 (by rfl) ⟨1677659, by rfl⟩ : syracuseStep 2236879 = 3355319) B3355319
theorem B3355325 : Blo 2235435 3355325 := bbase (se 3 (by rfl) ⟨629123, by rfl⟩ : syracuseStep 3355325 = 1258247) (by norm_num)
theorem B2236883 : Blo 2235435 2236883 := bstep (se 1 (by rfl) ⟨1677662, by rfl⟩ : syracuseStep 2236883 = 3355325) B3355325
theorem B5032997 : Blo 2235435 5032997 := bbase (se 4 (by rfl) ⟨471843, by rfl⟩ : syracuseStep 5032997 = 943687) (by norm_num)
theorem B3355331 : Blo 2235435 3355331 := bstep (se 1 (by rfl) ⟨2516498, by rfl⟩ : syracuseStep 3355331 = 5032997) B5032997
theorem B2236887 : Blo 2235435 2236887 := bstep (se 1 (by rfl) ⟨1677665, by rfl⟩ : syracuseStep 2236887 = 3355331) B3355331
theorem B5662133 : Blo 2235435 5662133 := bbase (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) (by norm_num)
theorem B3774755 : Blo 2235435 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B2516503 : Blo 2235435 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B3355337 : Blo 2235435 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B2236891 : Blo 2235435 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B5374613 : Blo 2235435 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B14332301 : Blo 2235435 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B9554867 : Blo 2235435 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B6369911 : Blo 2235435 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B4246607 : Blo 2235435 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B11324285 : Blo 2235435 11324285 := bstep (se 3 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 11324285 = 4246607) B4246607
theorem B7549523 : Blo 2235435 7549523 := bstep (se 1 (by rfl) ⟨5662142, by rfl⟩ : syracuseStep 7549523 = 11324285) B11324285
theorem B5033015 : Blo 2235435 5033015 := bstep (se 1 (by rfl) ⟨3774761, by rfl⟩ : syracuseStep 5033015 = 7549523) B7549523
theorem B3355343 : Blo 2235435 3355343 := bstep (se 1 (by rfl) ⟨2516507, by rfl⟩ : syracuseStep 3355343 = 5033015) B5033015
theorem B2236895 : Blo 2235435 2236895 := bstep (se 1 (by rfl) ⟨1677671, by rfl⟩ : syracuseStep 2236895 = 3355343) B3355343
theorem B3355349 : Blo 2235435 3355349 := bbase (se 7 (by rfl) ⟨39320, by rfl⟩ : syracuseStep 3355349 = 78641) (by norm_num)
theorem B2236899 : Blo 2235435 2236899 := bstep (se 1 (by rfl) ⟨1677674, by rfl⟩ : syracuseStep 2236899 = 3355349) B3355349
theorem B2908861 : Blo 2235435 2908861 := bbase (se 3 (by rfl) ⟨545411, by rfl⟩ : syracuseStep 2908861 = 1090823) (by norm_num)
theorem B15513925 : Blo 2235435 15513925 := bstep (se 4 (by rfl) ⟨1454430, by rfl⟩ : syracuseStep 15513925 = 2908861) B2908861
theorem B20685233 : Blo 2235435 20685233 := bstep (se 2 (by rfl) ⟨7756962, by rfl⟩ : syracuseStep 20685233 = 15513925) B15513925
theorem B55160621 : Blo 2235435 55160621 := bstep (se 3 (by rfl) ⟨10342616, by rfl⟩ : syracuseStep 55160621 = 20685233) B20685233
theorem B36773747 : Blo 2235435 36773747 := bstep (se 1 (by rfl) ⟨27580310, by rfl⟩ : syracuseStep 36773747 = 55160621) B55160621
theorem B24515831 : Blo 2235435 24515831 := bstep (se 1 (by rfl) ⟨18386873, by rfl⟩ : syracuseStep 24515831 = 36773747) B36773747
theorem B16343887 : Blo 2235435 16343887 := bstep (se 1 (by rfl) ⟨12257915, by rfl⟩ : syracuseStep 16343887 = 24515831) B24515831
theorem B21791849 : Blo 2235435 21791849 := bstep (se 2 (by rfl) ⟨8171943, by rfl⟩ : syracuseStep 21791849 = 16343887) B16343887
theorem B58111597 : Blo 2235435 58111597 := bstep (se 3 (by rfl) ⟨10895924, by rfl⟩ : syracuseStep 58111597 = 21791849) B21791849
theorem B77482129 : Blo 2235435 77482129 := bstep (se 2 (by rfl) ⟨29055798, by rfl⟩ : syracuseStep 77482129 = 58111597) B58111597
theorem B103309505 : Blo 2235435 103309505 := bstep (se 2 (by rfl) ⟨38741064, by rfl⟩ : syracuseStep 103309505 = 77482129) B77482129
theorem B68873003 : Blo 2235435 68873003 := bstep (se 1 (by rfl) ⟨51654752, by rfl⟩ : syracuseStep 68873003 = 103309505) B103309505
theorem B45915335 : Blo 2235435 45915335 := bstep (se 1 (by rfl) ⟨34436501, by rfl⟩ : syracuseStep 45915335 = 68873003) B68873003
theorem B30610223 : Blo 2235435 30610223 := bstep (se 1 (by rfl) ⟨22957667, by rfl⟩ : syracuseStep 30610223 = 45915335) B45915335
theorem B20406815 : Blo 2235435 20406815 := bstep (se 1 (by rfl) ⟨15305111, by rfl⟩ : syracuseStep 20406815 = 30610223) B30610223
theorem B13604543 : Blo 2235435 13604543 := bstep (se 1 (by rfl) ⟨10203407, by rfl⟩ : syracuseStep 13604543 = 20406815) B20406815
theorem B9069695 : Blo 2235435 9069695 := bstep (se 1 (by rfl) ⟨6802271, by rfl⟩ : syracuseStep 9069695 = 13604543) B13604543
theorem B6046463 : Blo 2235435 6046463 := bstep (se 1 (by rfl) ⟨4534847, by rfl⟩ : syracuseStep 6046463 = 9069695) B9069695
theorem B4030975 : Blo 2235435 4030975 := bstep (se 1 (by rfl) ⟨3023231, by rfl⟩ : syracuseStep 4030975 = 6046463) B6046463
theorem B5374633 : Blo 2235435 5374633 := bstep (se 2 (by rfl) ⟨2015487, by rfl⟩ : syracuseStep 5374633 = 4030975) B4030975
theorem B7166177 : Blo 2235435 7166177 := bstep (se 2 (by rfl) ⟨2687316, by rfl⟩ : syracuseStep 7166177 = 5374633) B5374633
theorem B4777451 : Blo 2235435 4777451 := bstep (se 1 (by rfl) ⟨3583088, by rfl⟩ : syracuseStep 4777451 = 7166177) B7166177
theorem B3184967 : Blo 2235435 3184967 := bstep (se 1 (by rfl) ⟨2388725, by rfl⟩ : syracuseStep 3184967 = 4777451) B4777451
theorem B8493245 : Blo 2235435 8493245 := bstep (se 3 (by rfl) ⟨1592483, by rfl⟩ : syracuseStep 8493245 = 3184967) B3184967
theorem B5662163 : Blo 2235435 5662163 := bstep (se 1 (by rfl) ⟨4246622, by rfl⟩ : syracuseStep 5662163 = 8493245) B8493245
theorem B3774775 : Blo 2235435 3774775 := bstep (se 1 (by rfl) ⟨2831081, by rfl⟩ : syracuseStep 3774775 = 5662163) B5662163
theorem B5033033 : Blo 2235435 5033033 := bstep (se 2 (by rfl) ⟨1887387, by rfl⟩ : syracuseStep 5033033 = 3774775) B3774775
theorem B3355355 : Blo 2235435 3355355 := bstep (se 1 (by rfl) ⟨2516516, by rfl⟩ : syracuseStep 3355355 = 5033033) B5033033
theorem B2236903 : Blo 2235435 2236903 := bstep (se 1 (by rfl) ⟨1677677, by rfl⟩ : syracuseStep 2236903 = 3355355) B3355355
theorem B2516521 : Blo 2235435 2516521 := bbase (se 2 (by rfl) ⟨943695, by rfl⟩ : syracuseStep 2516521 = 1887391) (by norm_num)
theorem B3355361 : Blo 2235435 3355361 := bstep (se 2 (by rfl) ⟨1258260, by rfl⟩ : syracuseStep 3355361 = 2516521) B2516521
theorem B2236907 : Blo 2235435 2236907 := bstep (se 1 (by rfl) ⟨1677680, by rfl⟩ : syracuseStep 2236907 = 3355361) B3355361
theorem B5739437 : Blo 2235435 5739437 := bbase (se 3 (by rfl) ⟨1076144, by rfl⟩ : syracuseStep 5739437 = 2152289) (by norm_num)
theorem B3826291 : Blo 2235435 3826291 := bstep (se 1 (by rfl) ⟨2869718, by rfl⟩ : syracuseStep 3826291 = 5739437) B5739437
theorem B5101721 : Blo 2235435 5101721 := bstep (se 2 (by rfl) ⟨1913145, by rfl⟩ : syracuseStep 5101721 = 3826291) B3826291
theorem B3401147 : Blo 2235435 3401147 := bstep (se 1 (by rfl) ⟨2550860, by rfl⟩ : syracuseStep 3401147 = 5101721) B5101721
theorem B9069725 : Blo 2235435 9069725 := bstep (se 3 (by rfl) ⟨1700573, by rfl⟩ : syracuseStep 9069725 = 3401147) B3401147
theorem B6046483 : Blo 2235435 6046483 := bstep (se 1 (by rfl) ⟨4534862, by rfl⟩ : syracuseStep 6046483 = 9069725) B9069725
theorem B8061977 : Blo 2235435 8061977 := bstep (se 2 (by rfl) ⟨3023241, by rfl⟩ : syracuseStep 8061977 = 6046483) B6046483
theorem B21498605 : Blo 2235435 21498605 := bstep (se 3 (by rfl) ⟨4030988, by rfl⟩ : syracuseStep 21498605 = 8061977) B8061977
theorem B14332403 : Blo 2235435 14332403 := bstep (se 1 (by rfl) ⟨10749302, by rfl⟩ : syracuseStep 14332403 = 21498605) B21498605
theorem B9554935 : Blo 2235435 9554935 := bstep (se 1 (by rfl) ⟨7166201, by rfl⟩ : syracuseStep 9554935 = 14332403) B14332403
theorem B12739913 : Blo 2235435 12739913 := bstep (se 2 (by rfl) ⟨4777467, by rfl⟩ : syracuseStep 12739913 = 9554935) B9554935
theorem B8493275 : Blo 2235435 8493275 := bstep (se 1 (by rfl) ⟨6369956, by rfl⟩ : syracuseStep 8493275 = 12739913) B12739913
theorem B5662183 : Blo 2235435 5662183 := bstep (se 1 (by rfl) ⟨4246637, by rfl⟩ : syracuseStep 5662183 = 8493275) B8493275
theorem B7549577 : Blo 2235435 7549577 := bstep (se 2 (by rfl) ⟨2831091, by rfl⟩ : syracuseStep 7549577 = 5662183) B5662183
theorem B5033051 : Blo 2235435 5033051 := bstep (se 1 (by rfl) ⟨3774788, by rfl⟩ : syracuseStep 5033051 = 7549577) B7549577
theorem B3355367 : Blo 2235435 3355367 := bstep (se 1 (by rfl) ⟨2516525, by rfl⟩ : syracuseStep 3355367 = 5033051) B5033051
theorem B2236911 : Blo 2235435 2236911 := bstep (se 1 (by rfl) ⟨1677683, by rfl⟩ : syracuseStep 2236911 = 3355367) B3355367
theorem B3355373 : Blo 2235435 3355373 := bbase (se 3 (by rfl) ⟨629132, by rfl⟩ : syracuseStep 3355373 = 1258265) (by norm_num)
theorem B2236915 : Blo 2235435 2236915 := bstep (se 1 (by rfl) ⟨1677686, by rfl⟩ : syracuseStep 2236915 = 3355373) B3355373
theorem B5033069 : Blo 2235435 5033069 := bbase (se 3 (by rfl) ⟨943700, by rfl⟩ : syracuseStep 5033069 = 1887401) (by norm_num)
theorem B3355379 : Blo 2235435 3355379 := bstep (se 1 (by rfl) ⟨2516534, by rfl⟩ : syracuseStep 3355379 = 5033069) B5033069
theorem B2236919 : Blo 2235435 2236919 := bstep (se 1 (by rfl) ⟨1677689, by rfl⟩ : syracuseStep 2236919 = 3355379) B3355379
theorem B4246661 : Blo 2235435 4246661 := bbase (se 4 (by rfl) ⟨398124, by rfl⟩ : syracuseStep 4246661 = 796249) (by norm_num)
theorem B2831107 : Blo 2235435 2831107 := bstep (se 1 (by rfl) ⟨2123330, by rfl⟩ : syracuseStep 2831107 = 4246661) B4246661
theorem B3774809 : Blo 2235435 3774809 := bstep (se 2 (by rfl) ⟨1415553, by rfl⟩ : syracuseStep 3774809 = 2831107) B2831107
theorem B2516539 : Blo 2235435 2516539 := bstep (se 1 (by rfl) ⟨1887404, by rfl⟩ : syracuseStep 2516539 = 3774809) B3774809
theorem B3355385 : Blo 2235435 3355385 := bstep (se 2 (by rfl) ⟨1258269, by rfl⟩ : syracuseStep 3355385 = 2516539) B2516539
theorem B2236923 : Blo 2235435 2236923 := bstep (se 1 (by rfl) ⟨1677692, by rfl⟩ : syracuseStep 2236923 = 3355385) B3355385
theorem B5241917 : Blo 2235435 5241917 := bbase (se 3 (by rfl) ⟨982859, by rfl⟩ : syracuseStep 5241917 = 1965719) (by norm_num)
theorem B3494611 : Blo 2235435 3494611 := bstep (se 1 (by rfl) ⟨2620958, by rfl⟩ : syracuseStep 3494611 = 5241917) B5241917
theorem B4659481 : Blo 2235435 4659481 := bstep (se 2 (by rfl) ⟨1747305, by rfl⟩ : syracuseStep 4659481 = 3494611) B3494611
theorem B6212641 : Blo 2235435 6212641 := bstep (se 2 (by rfl) ⟨2329740, by rfl⟩ : syracuseStep 6212641 = 4659481) B4659481
theorem B8283521 : Blo 2235435 8283521 := bstep (se 2 (by rfl) ⟨3106320, by rfl⟩ : syracuseStep 8283521 = 6212641) B6212641
theorem B5522347 : Blo 2235435 5522347 := bstep (se 1 (by rfl) ⟨4141760, by rfl⟩ : syracuseStep 5522347 = 8283521) B8283521
theorem B29452517 : Blo 2235435 29452517 := bstep (se 4 (by rfl) ⟨2761173, by rfl⟩ : syracuseStep 29452517 = 5522347) B5522347
theorem B19635011 : Blo 2235435 19635011 := bstep (se 1 (by rfl) ⟨14726258, by rfl⟩ : syracuseStep 19635011 = 29452517) B29452517
theorem B13090007 : Blo 2235435 13090007 := bstep (se 1 (by rfl) ⟨9817505, by rfl⟩ : syracuseStep 13090007 = 19635011) B19635011
theorem B34906685 : Blo 2235435 34906685 := bstep (se 3 (by rfl) ⟨6545003, by rfl⟩ : syracuseStep 34906685 = 13090007) B13090007
theorem B93084493 : Blo 2235435 93084493 := bstep (se 3 (by rfl) ⟨17453342, by rfl⟩ : syracuseStep 93084493 = 34906685) B34906685
theorem B124112657 : Blo 2235435 124112657 := bstep (se 2 (by rfl) ⟨46542246, by rfl⟩ : syracuseStep 124112657 = 93084493) B93084493
theorem B82741771 : Blo 2235435 82741771 := bstep (se 1 (by rfl) ⟨62056328, by rfl⟩ : syracuseStep 82741771 = 124112657) B124112657
theorem B110322361 : Blo 2235435 110322361 := bstep (se 2 (by rfl) ⟨41370885, by rfl⟩ : syracuseStep 110322361 = 82741771) B82741771
theorem B147096481 : Blo 2235435 147096481 := bstep (se 2 (by rfl) ⟨55161180, by rfl⟩ : syracuseStep 147096481 = 110322361) B110322361
theorem B196128641 : Blo 2235435 196128641 := bstep (se 2 (by rfl) ⟨73548240, by rfl⟩ : syracuseStep 196128641 = 147096481) B147096481
theorem B130752427 : Blo 2235435 130752427 := bstep (se 1 (by rfl) ⟨98064320, by rfl⟩ : syracuseStep 130752427 = 196128641) B196128641
theorem B174336569 : Blo 2235435 174336569 := bstep (se 2 (by rfl) ⟨65376213, by rfl⟩ : syracuseStep 174336569 = 130752427) B130752427
theorem B116224379 : Blo 2235435 116224379 := bstep (se 1 (by rfl) ⟨87168284, by rfl⟩ : syracuseStep 116224379 = 174336569) B174336569
theorem B77482919 : Blo 2235435 77482919 := bstep (se 1 (by rfl) ⟨58112189, by rfl⟩ : syracuseStep 77482919 = 116224379) B116224379
theorem B206621117 : Blo 2235435 206621117 := bstep (se 3 (by rfl) ⟨38741459, by rfl⟩ : syracuseStep 206621117 = 77482919) B77482919
theorem B137747411 : Blo 2235435 137747411 := bstep (se 1 (by rfl) ⟨103310558, by rfl⟩ : syracuseStep 137747411 = 206621117) B206621117
theorem B91831607 : Blo 2235435 91831607 := bstep (se 1 (by rfl) ⟨68873705, by rfl⟩ : syracuseStep 91831607 = 137747411) B137747411
theorem B61221071 : Blo 2235435 61221071 := bstep (se 1 (by rfl) ⟨45915803, by rfl⟩ : syracuseStep 61221071 = 91831607) B91831607
theorem B40814047 : Blo 2235435 40814047 := bstep (se 1 (by rfl) ⟨30610535, by rfl⟩ : syracuseStep 40814047 = 61221071) B61221071
theorem B54418729 : Blo 2235435 54418729 := bstep (se 2 (by rfl) ⟨20407023, by rfl⟩ : syracuseStep 54418729 = 40814047) B40814047
theorem B72558305 : Blo 2235435 72558305 := bstep (se 2 (by rfl) ⟨27209364, by rfl⟩ : syracuseStep 72558305 = 54418729) B54418729
theorem B48372203 : Blo 2235435 48372203 := bstep (se 1 (by rfl) ⟨36279152, by rfl⟩ : syracuseStep 48372203 = 72558305) B72558305
theorem B32248135 : Blo 2235435 32248135 := bstep (se 1 (by rfl) ⟨24186101, by rfl⟩ : syracuseStep 32248135 = 48372203) B48372203
theorem B42997513 : Blo 2235435 42997513 := bstep (se 2 (by rfl) ⟨16124067, by rfl⟩ : syracuseStep 42997513 = 32248135) B32248135
theorem B57330017 : Blo 2235435 57330017 := bstep (se 2 (by rfl) ⟨21498756, by rfl⟩ : syracuseStep 57330017 = 42997513) B42997513
theorem B38220011 : Blo 2235435 38220011 := bstep (se 1 (by rfl) ⟨28665008, by rfl⟩ : syracuseStep 38220011 = 57330017) B57330017
theorem B25480007 : Blo 2235435 25480007 := bstep (se 1 (by rfl) ⟨19110005, by rfl⟩ : syracuseStep 25480007 = 38220011) B38220011
theorem B16986671 : Blo 2235435 16986671 := bstep (se 1 (by rfl) ⟨12740003, by rfl⟩ : syracuseStep 16986671 = 25480007) B25480007
theorem B11324447 : Blo 2235435 11324447 := bstep (se 1 (by rfl) ⟨8493335, by rfl⟩ : syracuseStep 11324447 = 16986671) B16986671
theorem B7549631 : Blo 2235435 7549631 := bstep (se 1 (by rfl) ⟨5662223, by rfl⟩ : syracuseStep 7549631 = 11324447) B11324447
theorem B5033087 : Blo 2235435 5033087 := bstep (se 1 (by rfl) ⟨3774815, by rfl⟩ : syracuseStep 5033087 = 7549631) B7549631
theorem B3355391 : Blo 2235435 3355391 := bstep (se 1 (by rfl) ⟨2516543, by rfl⟩ : syracuseStep 3355391 = 5033087) B5033087
theorem B2236927 : Blo 2235435 2236927 := bstep (se 1 (by rfl) ⟨1677695, by rfl⟩ : syracuseStep 2236927 = 3355391) B3355391
theorem B3355397 : Blo 2235435 3355397 := bbase (se 4 (by rfl) ⟨314568, by rfl⟩ : syracuseStep 3355397 = 629137) (by norm_num)
theorem B2236931 : Blo 2235435 2236931 := bstep (se 1 (by rfl) ⟨1677698, by rfl⟩ : syracuseStep 2236931 = 3355397) B3355397
theorem B3774829 : Blo 2235435 3774829 := bbase (se 3 (by rfl) ⟨707780, by rfl⟩ : syracuseStep 3774829 = 1415561) (by norm_num)
theorem B5033105 : Blo 2235435 5033105 := bstep (se 2 (by rfl) ⟨1887414, by rfl⟩ : syracuseStep 5033105 = 3774829) B3774829
theorem B3355403 : Blo 2235435 3355403 := bstep (se 1 (by rfl) ⟨2516552, by rfl⟩ : syracuseStep 3355403 = 5033105) B5033105
theorem B2236935 : Blo 2235435 2236935 := bstep (se 1 (by rfl) ⟨1677701, by rfl⟩ : syracuseStep 2236935 = 3355403) B3355403
theorem B2516557 : Blo 2235435 2516557 := bbase (se 3 (by rfl) ⟨471854, by rfl⟩ : syracuseStep 2516557 = 943709) (by norm_num)
theorem B3355409 : Blo 2235435 3355409 := bstep (se 2 (by rfl) ⟨1258278, by rfl⟩ : syracuseStep 3355409 = 2516557) B2516557
theorem B2236939 : Blo 2235435 2236939 := bstep (se 1 (by rfl) ⟨1677704, by rfl⟩ : syracuseStep 2236939 = 3355409) B3355409
theorem B7549685 : Blo 2235435 7549685 := bbase (se 5 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 7549685 = 707783) (by norm_num)
theorem B5033123 : Blo 2235435 5033123 := bstep (se 1 (by rfl) ⟨3774842, by rfl⟩ : syracuseStep 5033123 = 7549685) B7549685
theorem B3355415 : Blo 2235435 3355415 := bstep (se 1 (by rfl) ⟨2516561, by rfl⟩ : syracuseStep 3355415 = 5033123) B5033123
theorem B2236943 : Blo 2235435 2236943 := bstep (se 1 (by rfl) ⟨1677707, by rfl⟩ : syracuseStep 2236943 = 3355415) B3355415
theorem B3355421 : Blo 2235435 3355421 := bbase (se 3 (by rfl) ⟨629141, by rfl⟩ : syracuseStep 3355421 = 1258283) (by norm_num)
theorem B2236947 : Blo 2235435 2236947 := bstep (se 1 (by rfl) ⟨1677710, by rfl⟩ : syracuseStep 2236947 = 3355421) B3355421
theorem B5033141 : Blo 2235435 5033141 := bbase (se 5 (by rfl) ⟨235928, by rfl⟩ : syracuseStep 5033141 = 471857) (by norm_num)
theorem B3355427 : Blo 2235435 3355427 := bstep (se 1 (by rfl) ⟨2516570, by rfl⟩ : syracuseStep 3355427 = 5033141) B5033141
theorem B2236951 : Blo 2235435 2236951 := bstep (se 1 (by rfl) ⟨1677713, by rfl⟩ : syracuseStep 2236951 = 3355427) B3355427
theorem B2388781 : Blo 2235435 2388781 := bbase (se 3 (by rfl) ⟨447896, by rfl⟩ : syracuseStep 2388781 = 895793) (by norm_num)
theorem B12740165 : Blo 2235435 12740165 := bstep (se 4 (by rfl) ⟨1194390, by rfl⟩ : syracuseStep 12740165 = 2388781) B2388781
theorem B8493443 : Blo 2235435 8493443 := bstep (se 1 (by rfl) ⟨6370082, by rfl⟩ : syracuseStep 8493443 = 12740165) B12740165
theorem B5662295 : Blo 2235435 5662295 := bstep (se 1 (by rfl) ⟨4246721, by rfl⟩ : syracuseStep 5662295 = 8493443) B8493443
theorem B3774863 : Blo 2235435 3774863 := bstep (se 1 (by rfl) ⟨2831147, by rfl⟩ : syracuseStep 3774863 = 5662295) B5662295
theorem B2516575 : Blo 2235435 2516575 := bstep (se 1 (by rfl) ⟨1887431, by rfl⟩ : syracuseStep 2516575 = 3774863) B3774863
theorem B3355433 : Blo 2235435 3355433 := bstep (se 2 (by rfl) ⟨1258287, by rfl⟩ : syracuseStep 3355433 = 2516575) B2516575
theorem B2236955 : Blo 2235435 2236955 := bstep (se 1 (by rfl) ⟨1677716, by rfl⟩ : syracuseStep 2236955 = 3355433) B3355433
theorem B2388785 : Blo 2235435 2388785 := bbase (se 2 (by rfl) ⟨895794, by rfl⟩ : syracuseStep 2388785 = 1791589) (by norm_num)
theorem B6370093 : Blo 2235435 6370093 := bstep (se 3 (by rfl) ⟨1194392, by rfl⟩ : syracuseStep 6370093 = 2388785) B2388785
theorem B8493457 : Blo 2235435 8493457 := bstep (se 2 (by rfl) ⟨3185046, by rfl⟩ : syracuseStep 8493457 = 6370093) B6370093
theorem B11324609 : Blo 2235435 11324609 := bstep (se 2 (by rfl) ⟨4246728, by rfl⟩ : syracuseStep 11324609 = 8493457) B8493457
theorem B7549739 : Blo 2235435 7549739 := bstep (se 1 (by rfl) ⟨5662304, by rfl⟩ : syracuseStep 7549739 = 11324609) B11324609
theorem B5033159 : Blo 2235435 5033159 := bstep (se 1 (by rfl) ⟨3774869, by rfl⟩ : syracuseStep 5033159 = 7549739) B7549739
theorem B3355439 : Blo 2235435 3355439 := bstep (se 1 (by rfl) ⟨2516579, by rfl⟩ : syracuseStep 3355439 = 5033159) B5033159
theorem B2236959 : Blo 2235435 2236959 := bstep (se 1 (by rfl) ⟨1677719, by rfl⟩ : syracuseStep 2236959 = 3355439) B3355439
theorem B3355445 : Blo 2235435 3355445 := bbase (se 5 (by rfl) ⟨157286, by rfl⟩ : syracuseStep 3355445 = 314573) (by norm_num)
theorem B2236963 : Blo 2235435 2236963 := bstep (se 1 (by rfl) ⟨1677722, by rfl⟩ : syracuseStep 2236963 = 3355445) B3355445
theorem B5662325 : Blo 2235435 5662325 := bbase (se 5 (by rfl) ⟨265421, by rfl⟩ : syracuseStep 5662325 = 530843) (by norm_num)
theorem B3774883 : Blo 2235435 3774883 := bstep (se 1 (by rfl) ⟨2831162, by rfl⟩ : syracuseStep 3774883 = 5662325) B5662325
theorem B5033177 : Blo 2235435 5033177 := bstep (se 2 (by rfl) ⟨1887441, by rfl⟩ : syracuseStep 5033177 = 3774883) B3774883
theorem B3355451 : Blo 2235435 3355451 := bstep (se 1 (by rfl) ⟨2516588, by rfl⟩ : syracuseStep 3355451 = 5033177) B5033177
theorem B2236967 : Blo 2235435 2236967 := bstep (se 1 (by rfl) ⟨1677725, by rfl⟩ : syracuseStep 2236967 = 3355451) B3355451
theorem B2516593 : Blo 2235435 2516593 := bbase (se 2 (by rfl) ⟨943722, by rfl⟩ : syracuseStep 2516593 = 1887445) (by norm_num)
theorem B3355457 : Blo 2235435 3355457 := bstep (se 2 (by rfl) ⟨1258296, by rfl⟩ : syracuseStep 3355457 = 2516593) B2516593
theorem B2236971 : Blo 2235435 2236971 := bstep (se 1 (by rfl) ⟨1677728, by rfl⟩ : syracuseStep 2236971 = 3355457) B3355457
theorem B4304701 : Blo 2235435 4304701 := bbase (se 3 (by rfl) ⟨807131, by rfl⟩ : syracuseStep 4304701 = 1614263) (by norm_num)
theorem B5739601 : Blo 2235435 5739601 := bstep (se 2 (by rfl) ⟨2152350, by rfl⟩ : syracuseStep 5739601 = 4304701) B4304701
theorem B7652801 : Blo 2235435 7652801 := bstep (se 2 (by rfl) ⟨2869800, by rfl⟩ : syracuseStep 7652801 = 5739601) B5739601
theorem B5101867 : Blo 2235435 5101867 := bstep (se 1 (by rfl) ⟨3826400, by rfl⟩ : syracuseStep 5101867 = 7652801) B7652801
theorem B6802489 : Blo 2235435 6802489 := bstep (se 2 (by rfl) ⟨2550933, by rfl⟩ : syracuseStep 6802489 = 5101867) B5101867
theorem B9069985 : Blo 2235435 9069985 := bstep (se 2 (by rfl) ⟨3401244, by rfl⟩ : syracuseStep 9069985 = 6802489) B6802489
theorem B12093313 : Blo 2235435 12093313 := bstep (se 2 (by rfl) ⟨4534992, by rfl⟩ : syracuseStep 12093313 = 9069985) B9069985
theorem B16124417 : Blo 2235435 16124417 := bstep (se 2 (by rfl) ⟨6046656, by rfl⟩ : syracuseStep 16124417 = 12093313) B12093313
theorem B10749611 : Blo 2235435 10749611 := bstep (se 1 (by rfl) ⟨8062208, by rfl⟩ : syracuseStep 10749611 = 16124417) B16124417
theorem B7166407 : Blo 2235435 7166407 := bstep (se 1 (by rfl) ⟨5374805, by rfl⟩ : syracuseStep 7166407 = 10749611) B10749611
theorem B9555209 : Blo 2235435 9555209 := bstep (se 2 (by rfl) ⟨3583203, by rfl⟩ : syracuseStep 9555209 = 7166407) B7166407
theorem B6370139 : Blo 2235435 6370139 := bstep (se 1 (by rfl) ⟨4777604, by rfl⟩ : syracuseStep 6370139 = 9555209) B9555209
theorem B4246759 : Blo 2235435 4246759 := bstep (se 1 (by rfl) ⟨3185069, by rfl⟩ : syracuseStep 4246759 = 6370139) B6370139
theorem B5662345 : Blo 2235435 5662345 := bstep (se 2 (by rfl) ⟨2123379, by rfl⟩ : syracuseStep 5662345 = 4246759) B4246759
theorem B7549793 : Blo 2235435 7549793 := bstep (se 2 (by rfl) ⟨2831172, by rfl⟩ : syracuseStep 7549793 = 5662345) B5662345
theorem B5033195 : Blo 2235435 5033195 := bstep (se 1 (by rfl) ⟨3774896, by rfl⟩ : syracuseStep 5033195 = 7549793) B7549793
theorem B3355463 : Blo 2235435 3355463 := bstep (se 1 (by rfl) ⟨2516597, by rfl⟩ : syracuseStep 3355463 = 5033195) B5033195
theorem B2236975 : Blo 2235435 2236975 := bstep (se 1 (by rfl) ⟨1677731, by rfl⟩ : syracuseStep 2236975 = 3355463) B3355463
theorem B3355469 : Blo 2235435 3355469 := bbase (se 3 (by rfl) ⟨629150, by rfl⟩ : syracuseStep 3355469 = 1258301) (by norm_num)
theorem B2236979 : Blo 2235435 2236979 := bstep (se 1 (by rfl) ⟨1677734, by rfl⟩ : syracuseStep 2236979 = 3355469) B3355469
theorem B5033213 : Blo 2235435 5033213 := bbase (se 3 (by rfl) ⟨943727, by rfl⟩ : syracuseStep 5033213 = 1887455) (by norm_num)
theorem B3355475 : Blo 2235435 3355475 := bstep (se 1 (by rfl) ⟨2516606, by rfl⟩ : syracuseStep 3355475 = 5033213) B5033213
theorem B2236983 : Blo 2235435 2236983 := bstep (se 1 (by rfl) ⟨1677737, by rfl⟩ : syracuseStep 2236983 = 3355475) B3355475
theorem B3774917 : Blo 2235435 3774917 := bbase (se 4 (by rfl) ⟨353898, by rfl⟩ : syracuseStep 3774917 = 707797) (by norm_num)
theorem B2516611 : Blo 2235435 2516611 := bstep (se 1 (by rfl) ⟨1887458, by rfl⟩ : syracuseStep 2516611 = 3774917) B3774917
theorem B3355481 : Blo 2235435 3355481 := bstep (se 2 (by rfl) ⟨1258305, by rfl⟩ : syracuseStep 3355481 = 2516611) B2516611
theorem B2236987 : Blo 2235435 2236987 := bstep (se 1 (by rfl) ⟨1677740, by rfl⟩ : syracuseStep 2236987 = 3355481) B3355481
theorem B16987157 : Blo 2235435 16987157 := bbase (se 6 (by rfl) ⟨398136, by rfl⟩ : syracuseStep 16987157 = 796273) (by norm_num)
theorem B11324771 : Blo 2235435 11324771 := bstep (se 1 (by rfl) ⟨8493578, by rfl⟩ : syracuseStep 11324771 = 16987157) B16987157
theorem B7549847 : Blo 2235435 7549847 := bstep (se 1 (by rfl) ⟨5662385, by rfl⟩ : syracuseStep 7549847 = 11324771) B11324771
theorem B5033231 : Blo 2235435 5033231 := bstep (se 1 (by rfl) ⟨3774923, by rfl⟩ : syracuseStep 5033231 = 7549847) B7549847
theorem B3355487 : Blo 2235435 3355487 := bstep (se 1 (by rfl) ⟨2516615, by rfl⟩ : syracuseStep 3355487 = 5033231) B5033231
theorem B2236991 : Blo 2235435 2236991 := bstep (se 1 (by rfl) ⟨1677743, by rfl⟩ : syracuseStep 2236991 = 3355487) B3355487
theorem B3355493 : Blo 2235435 3355493 := bbase (se 4 (by rfl) ⟨314577, by rfl⟩ : syracuseStep 3355493 = 629155) (by norm_num)
theorem B2236995 : Blo 2235435 2236995 := bstep (se 1 (by rfl) ⟨1677746, by rfl⟩ : syracuseStep 2236995 = 3355493) B3355493
theorem B4246805 : Blo 2235435 4246805 := bbase (se 6 (by rfl) ⟨99534, by rfl⟩ : syracuseStep 4246805 = 199069) (by norm_num)
theorem B2831203 : Blo 2235435 2831203 := bstep (se 1 (by rfl) ⟨2123402, by rfl⟩ : syracuseStep 2831203 = 4246805) B4246805
theorem B3774937 : Blo 2235435 3774937 := bstep (se 2 (by rfl) ⟨1415601, by rfl⟩ : syracuseStep 3774937 = 2831203) B2831203
theorem B5033249 : Blo 2235435 5033249 := bstep (se 2 (by rfl) ⟨1887468, by rfl⟩ : syracuseStep 5033249 = 3774937) B3774937
theorem B3355499 : Blo 2235435 3355499 := bstep (se 1 (by rfl) ⟨2516624, by rfl⟩ : syracuseStep 3355499 = 5033249) B5033249
theorem B2236999 : Blo 2235435 2236999 := bstep (se 1 (by rfl) ⟨1677749, by rfl⟩ : syracuseStep 2236999 = 3355499) B3355499
theorem B2516629 : Blo 2235435 2516629 := bbase (se 6 (by rfl) ⟨58983, by rfl⟩ : syracuseStep 2516629 = 117967) (by norm_num)
theorem B3355505 : Blo 2235435 3355505 := bstep (se 2 (by rfl) ⟨1258314, by rfl⟩ : syracuseStep 3355505 = 2516629) B2516629
theorem B2237003 : Blo 2235435 2237003 := bstep (se 1 (by rfl) ⟨1677752, by rfl⟩ : syracuseStep 2237003 = 3355505) B3355505
theorem B2831213 : Blo 2235435 2831213 := bbase (se 3 (by rfl) ⟨530852, by rfl⟩ : syracuseStep 2831213 = 1061705) (by norm_num)
theorem B7549901 : Blo 2235435 7549901 := bstep (se 3 (by rfl) ⟨1415606, by rfl⟩ : syracuseStep 7549901 = 2831213) B2831213
theorem B5033267 : Blo 2235435 5033267 := bstep (se 1 (by rfl) ⟨3774950, by rfl⟩ : syracuseStep 5033267 = 7549901) B7549901
theorem B3355511 : Blo 2235435 3355511 := bstep (se 1 (by rfl) ⟨2516633, by rfl⟩ : syracuseStep 3355511 = 5033267) B5033267
theorem B2237007 : Blo 2235435 2237007 := bstep (se 1 (by rfl) ⟨1677755, by rfl⟩ : syracuseStep 2237007 = 3355511) B3355511
theorem B3355517 : Blo 2235435 3355517 := bbase (se 3 (by rfl) ⟨629159, by rfl⟩ : syracuseStep 3355517 = 1258319) (by norm_num)
theorem B2237011 : Blo 2235435 2237011 := bstep (se 1 (by rfl) ⟨1677758, by rfl⟩ : syracuseStep 2237011 = 3355517) B3355517
theorem B5033285 : Blo 2235435 5033285 := bbase (se 4 (by rfl) ⟨471870, by rfl⟩ : syracuseStep 5033285 = 943741) (by norm_num)
theorem B3355523 : Blo 2235435 3355523 := bstep (se 1 (by rfl) ⟨2516642, by rfl⟩ : syracuseStep 3355523 = 5033285) B5033285
theorem B2237015 : Blo 2235435 2237015 := bstep (se 1 (by rfl) ⟨1677761, by rfl⟩ : syracuseStep 2237015 = 3355523) B3355523
theorem B7166549 : Blo 2235435 7166549 := bbase (se 8 (by rfl) ⟨41991, by rfl⟩ : syracuseStep 7166549 = 83983) (by norm_num)
theorem B4777699 : Blo 2235435 4777699 := bstep (se 1 (by rfl) ⟨3583274, by rfl⟩ : syracuseStep 4777699 = 7166549) B7166549
theorem B6370265 : Blo 2235435 6370265 := bstep (se 2 (by rfl) ⟨2388849, by rfl⟩ : syracuseStep 6370265 = 4777699) B4777699
theorem B4246843 : Blo 2235435 4246843 := bstep (se 1 (by rfl) ⟨3185132, by rfl⟩ : syracuseStep 4246843 = 6370265) B6370265
theorem B5662457 : Blo 2235435 5662457 := bstep (se 2 (by rfl) ⟨2123421, by rfl⟩ : syracuseStep 5662457 = 4246843) B4246843
theorem B3774971 : Blo 2235435 3774971 := bstep (se 1 (by rfl) ⟨2831228, by rfl⟩ : syracuseStep 3774971 = 5662457) B5662457
theorem B2516647 : Blo 2235435 2516647 := bstep (se 1 (by rfl) ⟨1887485, by rfl⟩ : syracuseStep 2516647 = 3774971) B3774971
theorem B3355529 : Blo 2235435 3355529 := bstep (se 2 (by rfl) ⟨1258323, by rfl⟩ : syracuseStep 3355529 = 2516647) B2516647
theorem B2237019 : Blo 2235435 2237019 := bstep (se 1 (by rfl) ⟨1677764, by rfl⟩ : syracuseStep 2237019 = 3355529) B3355529
theorem B11324933 : Blo 2235435 11324933 := bbase (se 4 (by rfl) ⟨1061712, by rfl⟩ : syracuseStep 11324933 = 2123425) (by norm_num)
theorem B7549955 : Blo 2235435 7549955 := bstep (se 1 (by rfl) ⟨5662466, by rfl⟩ : syracuseStep 7549955 = 11324933) B11324933
theorem B5033303 : Blo 2235435 5033303 := bstep (se 1 (by rfl) ⟨3774977, by rfl⟩ : syracuseStep 5033303 = 7549955) B7549955
theorem B3355535 : Blo 2235435 3355535 := bstep (se 1 (by rfl) ⟨2516651, by rfl⟩ : syracuseStep 3355535 = 5033303) B5033303
theorem B2237023 : Blo 2235435 2237023 := bstep (se 1 (by rfl) ⟨1677767, by rfl⟩ : syracuseStep 2237023 = 3355535) B3355535
theorem B3355541 : Blo 2235435 3355541 := bbase (se 6 (by rfl) ⟨78645, by rfl⟩ : syracuseStep 3355541 = 157291) (by norm_num)
theorem B2237027 : Blo 2235435 2237027 := bstep (se 1 (by rfl) ⟨1677770, by rfl⟩ : syracuseStep 2237027 = 3355541) B3355541
theorem B12740597 : Blo 2235435 12740597 := bbase (se 5 (by rfl) ⟨597215, by rfl⟩ : syracuseStep 12740597 = 1194431) (by norm_num)
theorem B8493731 : Blo 2235435 8493731 := bstep (se 1 (by rfl) ⟨6370298, by rfl⟩ : syracuseStep 8493731 = 12740597) B12740597
theorem B5662487 : Blo 2235435 5662487 := bstep (se 1 (by rfl) ⟨4246865, by rfl⟩ : syracuseStep 5662487 = 8493731) B8493731
theorem B3774991 : Blo 2235435 3774991 := bstep (se 1 (by rfl) ⟨2831243, by rfl⟩ : syracuseStep 3774991 = 5662487) B5662487
theorem B5033321 : Blo 2235435 5033321 := bstep (se 2 (by rfl) ⟨1887495, by rfl⟩ : syracuseStep 5033321 = 3774991) B3774991
theorem B3355547 : Blo 2235435 3355547 := bstep (se 1 (by rfl) ⟨2516660, by rfl⟩ : syracuseStep 3355547 = 5033321) B5033321
theorem B2237031 : Blo 2235435 2237031 := bstep (se 1 (by rfl) ⟨1677773, by rfl⟩ : syracuseStep 2237031 = 3355547) B3355547
theorem B2516665 : Blo 2235435 2516665 := bbase (se 2 (by rfl) ⟨943749, by rfl⟩ : syracuseStep 2516665 = 1887499) (by norm_num)
theorem B3355553 : Blo 2235435 3355553 := bstep (se 2 (by rfl) ⟨1258332, by rfl⟩ : syracuseStep 3355553 = 2516665) B2516665
theorem B2237035 : Blo 2235435 2237035 := bstep (se 1 (by rfl) ⟨1677776, by rfl⟩ : syracuseStep 2237035 = 3355553) B3355553
theorem B4777741 : Blo 2235435 4777741 := bbase (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) (by norm_num)
theorem B6370321 : Blo 2235435 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B8493761 : Blo 2235435 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B5662507 : Blo 2235435 5662507 := bstep (se 1 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 5662507 = 8493761) B8493761
theorem B7550009 : Blo 2235435 7550009 := bstep (se 2 (by rfl) ⟨2831253, by rfl⟩ : syracuseStep 7550009 = 5662507) B5662507
theorem B5033339 : Blo 2235435 5033339 := bstep (se 1 (by rfl) ⟨3775004, by rfl⟩ : syracuseStep 5033339 = 7550009) B7550009
theorem B3355559 : Blo 2235435 3355559 := bstep (se 1 (by rfl) ⟨2516669, by rfl⟩ : syracuseStep 3355559 = 5033339) B5033339
theorem B2237039 : Blo 2235435 2237039 := bstep (se 1 (by rfl) ⟨1677779, by rfl⟩ : syracuseStep 2237039 = 3355559) B3355559
theorem B3355565 : Blo 2235435 3355565 := bbase (se 3 (by rfl) ⟨629168, by rfl⟩ : syracuseStep 3355565 = 1258337) (by norm_num)
theorem B2237043 : Blo 2235435 2237043 := bstep (se 1 (by rfl) ⟨1677782, by rfl⟩ : syracuseStep 2237043 = 3355565) B3355565
theorem B5033357 : Blo 2235435 5033357 := bbase (se 3 (by rfl) ⟨943754, by rfl⟩ : syracuseStep 5033357 = 1887509) (by norm_num)
theorem B3355571 : Blo 2235435 3355571 := bstep (se 1 (by rfl) ⟨2516678, by rfl⟩ : syracuseStep 3355571 = 5033357) B5033357
theorem B2237047 : Blo 2235435 2237047 := bstep (se 1 (by rfl) ⟨1677785, by rfl⟩ : syracuseStep 2237047 = 3355571) B3355571
theorem B2831269 : Blo 2235435 2831269 := bbase (se 4 (by rfl) ⟨265431, by rfl⟩ : syracuseStep 2831269 = 530863) (by norm_num)
theorem B3775025 : Blo 2235435 3775025 := bstep (se 2 (by rfl) ⟨1415634, by rfl⟩ : syracuseStep 3775025 = 2831269) B2831269
theorem B2516683 : Blo 2235435 2516683 := bstep (se 1 (by rfl) ⟨1887512, by rfl⟩ : syracuseStep 2516683 = 3775025) B3775025
theorem B3355577 : Blo 2235435 3355577 := bstep (se 2 (by rfl) ⟨1258341, by rfl⟩ : syracuseStep 3355577 = 2516683) B2516683
theorem B2237051 : Blo 2235435 2237051 := bstep (se 1 (by rfl) ⟨1677788, by rfl⟩ : syracuseStep 2237051 = 3355577) B3355577
theorem B17219413 : Blo 2235435 17219413 := bbase (se 9 (by rfl) ⟨50447, by rfl⟩ : syracuseStep 17219413 = 100895) (by norm_num)
theorem B22959217 : Blo 2235435 22959217 := bstep (se 2 (by rfl) ⟨8609706, by rfl⟩ : syracuseStep 22959217 = 17219413) B17219413
theorem B30612289 : Blo 2235435 30612289 := bstep (se 2 (by rfl) ⟨11479608, by rfl⟩ : syracuseStep 30612289 = 22959217) B22959217
theorem B40816385 : Blo 2235435 40816385 := bstep (se 2 (by rfl) ⟨15306144, by rfl⟩ : syracuseStep 40816385 = 30612289) B30612289
theorem B27210923 : Blo 2235435 27210923 := bstep (se 1 (by rfl) ⟨20408192, by rfl⟩ : syracuseStep 27210923 = 40816385) B40816385
theorem B18140615 : Blo 2235435 18140615 := bstep (se 1 (by rfl) ⟨13605461, by rfl⟩ : syracuseStep 18140615 = 27210923) B27210923
theorem B12093743 : Blo 2235435 12093743 := bstep (se 1 (by rfl) ⟨9070307, by rfl⟩ : syracuseStep 12093743 = 18140615) B18140615
theorem B32249981 : Blo 2235435 32249981 := bstep (se 3 (by rfl) ⟨6046871, by rfl⟩ : syracuseStep 32249981 = 12093743) B12093743
theorem B21499987 : Blo 2235435 21499987 := bstep (se 1 (by rfl) ⟨16124990, by rfl⟩ : syracuseStep 21499987 = 32249981) B32249981
theorem B28666649 : Blo 2235435 28666649 := bstep (se 2 (by rfl) ⟨10749993, by rfl⟩ : syracuseStep 28666649 = 21499987) B21499987
theorem B19111099 : Blo 2235435 19111099 := bstep (se 1 (by rfl) ⟨14333324, by rfl⟩ : syracuseStep 19111099 = 28666649) B28666649
theorem B25481465 : Blo 2235435 25481465 := bstep (se 2 (by rfl) ⟨9555549, by rfl⟩ : syracuseStep 25481465 = 19111099) B19111099
theorem B16987643 : Blo 2235435 16987643 := bstep (se 1 (by rfl) ⟨12740732, by rfl⟩ : syracuseStep 16987643 = 25481465) B25481465
theorem B11325095 : Blo 2235435 11325095 := bstep (se 1 (by rfl) ⟨8493821, by rfl⟩ : syracuseStep 11325095 = 16987643) B16987643
theorem B7550063 : Blo 2235435 7550063 := bstep (se 1 (by rfl) ⟨5662547, by rfl⟩ : syracuseStep 7550063 = 11325095) B11325095
theorem B5033375 : Blo 2235435 5033375 := bstep (se 1 (by rfl) ⟨3775031, by rfl⟩ : syracuseStep 5033375 = 7550063) B7550063
theorem B3355583 : Blo 2235435 3355583 := bstep (se 1 (by rfl) ⟨2516687, by rfl⟩ : syracuseStep 3355583 = 5033375) B5033375
theorem B2237055 : Blo 2235435 2237055 := bstep (se 1 (by rfl) ⟨1677791, by rfl⟩ : syracuseStep 2237055 = 3355583) B3355583
theorem B3355589 : Blo 2235435 3355589 := bbase (se 4 (by rfl) ⟨314586, by rfl⟩ : syracuseStep 3355589 = 629173) (by norm_num)
theorem B2237059 : Blo 2235435 2237059 := bstep (se 1 (by rfl) ⟨1677794, by rfl⟩ : syracuseStep 2237059 = 3355589) B3355589
theorem B3775045 : Blo 2235435 3775045 := bbase (se 4 (by rfl) ⟨353910, by rfl⟩ : syracuseStep 3775045 = 707821) (by norm_num)
theorem B5033393 : Blo 2235435 5033393 := bstep (se 2 (by rfl) ⟨1887522, by rfl⟩ : syracuseStep 5033393 = 3775045) B3775045
theorem B3355595 : Blo 2235435 3355595 := bstep (se 1 (by rfl) ⟨2516696, by rfl⟩ : syracuseStep 3355595 = 5033393) B5033393
theorem B2237063 : Blo 2235435 2237063 := bstep (se 1 (by rfl) ⟨1677797, by rfl⟩ : syracuseStep 2237063 = 3355595) B3355595
theorem B2516701 : Blo 2235435 2516701 := bbase (se 3 (by rfl) ⟨471881, by rfl⟩ : syracuseStep 2516701 = 943763) (by norm_num)
theorem B3355601 : Blo 2235435 3355601 := bstep (se 2 (by rfl) ⟨1258350, by rfl⟩ : syracuseStep 3355601 = 2516701) B2516701
theorem B2237067 : Blo 2235435 2237067 := bstep (se 1 (by rfl) ⟨1677800, by rfl⟩ : syracuseStep 2237067 = 3355601) B3355601
theorem B7550117 : Blo 2235435 7550117 := bbase (se 4 (by rfl) ⟨707823, by rfl⟩ : syracuseStep 7550117 = 1415647) (by norm_num)
theorem B5033411 : Blo 2235435 5033411 := bstep (se 1 (by rfl) ⟨3775058, by rfl⟩ : syracuseStep 5033411 = 7550117) B7550117
theorem B3355607 : Blo 2235435 3355607 := bstep (se 1 (by rfl) ⟨2516705, by rfl⟩ : syracuseStep 3355607 = 5033411) B5033411
theorem B2237071 : Blo 2235435 2237071 := bstep (se 1 (by rfl) ⟨1677803, by rfl⟩ : syracuseStep 2237071 = 3355607) B3355607
theorem B3355613 : Blo 2235435 3355613 := bbase (se 3 (by rfl) ⟨629177, by rfl⟩ : syracuseStep 3355613 = 1258355) (by norm_num)
theorem B2237075 : Blo 2235435 2237075 := bstep (se 1 (by rfl) ⟨1677806, by rfl⟩ : syracuseStep 2237075 = 3355613) B3355613
theorem B5033429 : Blo 2235435 5033429 := bbase (se 7 (by rfl) ⟨58985, by rfl⟩ : syracuseStep 5033429 = 117971) (by norm_num)
theorem B3355619 : Blo 2235435 3355619 := bstep (se 1 (by rfl) ⟨2516714, by rfl⟩ : syracuseStep 3355619 = 5033429) B5033429
theorem B2237079 : Blo 2235435 2237079 := bstep (se 1 (by rfl) ⟨1677809, by rfl⟩ : syracuseStep 2237079 = 3355619) B3355619
theorem B6046949 : Blo 2235435 6046949 := bbase (se 4 (by rfl) ⟨566901, by rfl⟩ : syracuseStep 6046949 = 1133803) (by norm_num)
theorem B4031299 : Blo 2235435 4031299 := bstep (se 1 (by rfl) ⟨3023474, by rfl⟩ : syracuseStep 4031299 = 6046949) B6046949
theorem B21500261 : Blo 2235435 21500261 := bstep (se 4 (by rfl) ⟨2015649, by rfl⟩ : syracuseStep 21500261 = 4031299) B4031299
theorem B14333507 : Blo 2235435 14333507 := bstep (se 1 (by rfl) ⟨10750130, by rfl⟩ : syracuseStep 14333507 = 21500261) B21500261
theorem B9555671 : Blo 2235435 9555671 := bstep (se 1 (by rfl) ⟨7166753, by rfl⟩ : syracuseStep 9555671 = 14333507) B14333507
theorem B6370447 : Blo 2235435 6370447 := bstep (se 1 (by rfl) ⟨4777835, by rfl⟩ : syracuseStep 6370447 = 9555671) B9555671
theorem B8493929 : Blo 2235435 8493929 := bstep (se 2 (by rfl) ⟨3185223, by rfl⟩ : syracuseStep 8493929 = 6370447) B6370447
theorem B5662619 : Blo 2235435 5662619 := bstep (se 1 (by rfl) ⟨4246964, by rfl⟩ : syracuseStep 5662619 = 8493929) B8493929
theorem B3775079 : Blo 2235435 3775079 := bstep (se 1 (by rfl) ⟨2831309, by rfl⟩ : syracuseStep 3775079 = 5662619) B5662619
theorem B2516719 : Blo 2235435 2516719 := bstep (se 1 (by rfl) ⟨1887539, by rfl⟩ : syracuseStep 2516719 = 3775079) B3775079
theorem B3355625 : Blo 2235435 3355625 := bstep (se 2 (by rfl) ⟨1258359, by rfl⟩ : syracuseStep 3355625 = 2516719) B2516719
theorem B2237083 : Blo 2235435 2237083 := bstep (se 1 (by rfl) ⟨1677812, by rfl⟩ : syracuseStep 2237083 = 3355625) B3355625
theorem B2687537 : Blo 2235435 2687537 := bbase (se 2 (by rfl) ⟨1007826, by rfl⟩ : syracuseStep 2687537 = 2015653) (by norm_num)
theorem B7166765 : Blo 2235435 7166765 := bstep (se 3 (by rfl) ⟨1343768, by rfl⟩ : syracuseStep 7166765 = 2687537) B2687537
theorem B19111373 : Blo 2235435 19111373 := bstep (se 3 (by rfl) ⟨3583382, by rfl⟩ : syracuseStep 19111373 = 7166765) B7166765
theorem B12740915 : Blo 2235435 12740915 := bstep (se 1 (by rfl) ⟨9555686, by rfl⟩ : syracuseStep 12740915 = 19111373) B19111373
theorem B8493943 : Blo 2235435 8493943 := bstep (se 1 (by rfl) ⟨6370457, by rfl⟩ : syracuseStep 8493943 = 12740915) B12740915
theorem B11325257 : Blo 2235435 11325257 := bstep (se 2 (by rfl) ⟨4246971, by rfl⟩ : syracuseStep 11325257 = 8493943) B8493943
theorem B7550171 : Blo 2235435 7550171 := bstep (se 1 (by rfl) ⟨5662628, by rfl⟩ : syracuseStep 7550171 = 11325257) B11325257
theorem B5033447 : Blo 2235435 5033447 := bstep (se 1 (by rfl) ⟨3775085, by rfl⟩ : syracuseStep 5033447 = 7550171) B7550171
theorem B3355631 : Blo 2235435 3355631 := bstep (se 1 (by rfl) ⟨2516723, by rfl⟩ : syracuseStep 3355631 = 5033447) B5033447
theorem B2237087 : Blo 2235435 2237087 := bstep (se 1 (by rfl) ⟨1677815, by rfl⟩ : syracuseStep 2237087 = 3355631) B3355631
theorem B3355637 : Blo 2235435 3355637 := bbase (se 5 (by rfl) ⟨157295, by rfl⟩ : syracuseStep 3355637 = 314591) (by norm_num)
theorem B2237091 : Blo 2235435 2237091 := bstep (se 1 (by rfl) ⟨1677818, by rfl⟩ : syracuseStep 2237091 = 3355637) B3355637
theorem B4777861 : Blo 2235435 4777861 := bbase (se 4 (by rfl) ⟨447924, by rfl⟩ : syracuseStep 4777861 = 895849) (by norm_num)
theorem B6370481 : Blo 2235435 6370481 := bstep (se 2 (by rfl) ⟨2388930, by rfl⟩ : syracuseStep 6370481 = 4777861) B4777861
theorem B4246987 : Blo 2235435 4246987 := bstep (se 1 (by rfl) ⟨3185240, by rfl⟩ : syracuseStep 4246987 = 6370481) B6370481
theorem B5662649 : Blo 2235435 5662649 := bstep (se 2 (by rfl) ⟨2123493, by rfl⟩ : syracuseStep 5662649 = 4246987) B4246987
theorem B3775099 : Blo 2235435 3775099 := bstep (se 1 (by rfl) ⟨2831324, by rfl⟩ : syracuseStep 3775099 = 5662649) B5662649
theorem B5033465 : Blo 2235435 5033465 := bstep (se 2 (by rfl) ⟨1887549, by rfl⟩ : syracuseStep 5033465 = 3775099) B3775099
theorem B3355643 : Blo 2235435 3355643 := bstep (se 1 (by rfl) ⟨2516732, by rfl⟩ : syracuseStep 3355643 = 5033465) B5033465
theorem B2237095 : Blo 2235435 2237095 := bstep (se 1 (by rfl) ⟨1677821, by rfl⟩ : syracuseStep 2237095 = 3355643) B3355643
theorem B2516737 : Blo 2235435 2516737 := bbase (se 2 (by rfl) ⟨943776, by rfl⟩ : syracuseStep 2516737 = 1887553) (by norm_num)
theorem B3355649 : Blo 2235435 3355649 := bstep (se 2 (by rfl) ⟨1258368, by rfl⟩ : syracuseStep 3355649 = 2516737) B2516737
theorem B2237099 : Blo 2235435 2237099 := bstep (se 1 (by rfl) ⟨1677824, by rfl⟩ : syracuseStep 2237099 = 3355649) B3355649
theorem B5662669 : Blo 2235435 5662669 := bbase (se 3 (by rfl) ⟨1061750, by rfl⟩ : syracuseStep 5662669 = 2123501) (by norm_num)
theorem B7550225 : Blo 2235435 7550225 := bstep (se 2 (by rfl) ⟨2831334, by rfl⟩ : syracuseStep 7550225 = 5662669) B5662669
theorem B5033483 : Blo 2235435 5033483 := bstep (se 1 (by rfl) ⟨3775112, by rfl⟩ : syracuseStep 5033483 = 7550225) B7550225
theorem B3355655 : Blo 2235435 3355655 := bstep (se 1 (by rfl) ⟨2516741, by rfl⟩ : syracuseStep 3355655 = 5033483) B5033483
theorem B2237103 : Blo 2235435 2237103 := bstep (se 1 (by rfl) ⟨1677827, by rfl⟩ : syracuseStep 2237103 = 3355655) B3355655
theorem B3355661 : Blo 2235435 3355661 := bbase (se 3 (by rfl) ⟨629186, by rfl⟩ : syracuseStep 3355661 = 1258373) (by norm_num)
theorem B2237107 : Blo 2235435 2237107 := bstep (se 1 (by rfl) ⟨1677830, by rfl⟩ : syracuseStep 2237107 = 3355661) B3355661
theorem B5033501 : Blo 2235435 5033501 := bbase (se 3 (by rfl) ⟨943781, by rfl⟩ : syracuseStep 5033501 = 1887563) (by norm_num)
theorem B3355667 : Blo 2235435 3355667 := bstep (se 1 (by rfl) ⟨2516750, by rfl⟩ : syracuseStep 3355667 = 5033501) B5033501
theorem B2237111 : Blo 2235435 2237111 := bstep (se 1 (by rfl) ⟨1677833, by rfl⟩ : syracuseStep 2237111 = 3355667) B3355667
theorem B3775133 : Blo 2235435 3775133 := bbase (se 3 (by rfl) ⟨707837, by rfl⟩ : syracuseStep 3775133 = 1415675) (by norm_num)
theorem B2516755 : Blo 2235435 2516755 := bstep (se 1 (by rfl) ⟨1887566, by rfl⟩ : syracuseStep 2516755 = 3775133) B3775133
theorem B3355673 : Blo 2235435 3355673 := bstep (se 2 (by rfl) ⟨1258377, by rfl⟩ : syracuseStep 3355673 = 2516755) B2516755
theorem B2237115 : Blo 2235435 2237115 := bstep (se 1 (by rfl) ⟨1677836, by rfl⟩ : syracuseStep 2237115 = 3355673) B3355673
theorem B10484741 : Blo 2235435 10484741 := bbase (se 4 (by rfl) ⟨982944, by rfl⟩ : syracuseStep 10484741 = 1965889) (by norm_num)
theorem B6989827 : Blo 2235435 6989827 := bstep (se 1 (by rfl) ⟨5242370, by rfl⟩ : syracuseStep 6989827 = 10484741) B10484741
theorem B9319769 : Blo 2235435 9319769 := bstep (se 2 (by rfl) ⟨3494913, by rfl⟩ : syracuseStep 9319769 = 6989827) B6989827
theorem B6213179 : Blo 2235435 6213179 := bstep (se 1 (by rfl) ⟨4659884, by rfl⟩ : syracuseStep 6213179 = 9319769) B9319769
theorem B4142119 : Blo 2235435 4142119 := bstep (se 1 (by rfl) ⟨3106589, by rfl⟩ : syracuseStep 4142119 = 6213179) B6213179
theorem B5522825 : Blo 2235435 5522825 := bstep (se 2 (by rfl) ⟨2071059, by rfl⟩ : syracuseStep 5522825 = 4142119) B4142119
theorem B3681883 : Blo 2235435 3681883 := bstep (se 1 (by rfl) ⟨2761412, by rfl⟩ : syracuseStep 3681883 = 5522825) B5522825
theorem B4909177 : Blo 2235435 4909177 := bstep (se 2 (by rfl) ⟨1840941, by rfl⟩ : syracuseStep 4909177 = 3681883) B3681883
theorem B26182277 : Blo 2235435 26182277 := bstep (se 4 (by rfl) ⟨2454588, by rfl⟩ : syracuseStep 26182277 = 4909177) B4909177
theorem B17454851 : Blo 2235435 17454851 := bstep (se 1 (by rfl) ⟨13091138, by rfl⟩ : syracuseStep 17454851 = 26182277) B26182277
theorem B11636567 : Blo 2235435 11636567 := bstep (se 1 (by rfl) ⟨8727425, by rfl⟩ : syracuseStep 11636567 = 17454851) B17454851
theorem B7757711 : Blo 2235435 7757711 := bstep (se 1 (by rfl) ⟨5818283, by rfl⟩ : syracuseStep 7757711 = 11636567) B11636567
theorem B5171807 : Blo 2235435 5171807 := bstep (se 1 (by rfl) ⟨3878855, by rfl⟩ : syracuseStep 5171807 = 7757711) B7757711
theorem B13791485 : Blo 2235435 13791485 := bstep (se 3 (by rfl) ⟨2585903, by rfl⟩ : syracuseStep 13791485 = 5171807) B5171807
theorem B9194323 : Blo 2235435 9194323 := bstep (se 1 (by rfl) ⟨6895742, by rfl⟩ : syracuseStep 9194323 = 13791485) B13791485
theorem B12259097 : Blo 2235435 12259097 := bstep (se 2 (by rfl) ⟨4597161, by rfl⟩ : syracuseStep 12259097 = 9194323) B9194323
theorem B8172731 : Blo 2235435 8172731 := bstep (se 1 (by rfl) ⟨6129548, by rfl⟩ : syracuseStep 8172731 = 12259097) B12259097
theorem B5448487 : Blo 2235435 5448487 := bstep (se 1 (by rfl) ⟨4086365, by rfl⟩ : syracuseStep 5448487 = 8172731) B8172731
theorem B7264649 : Blo 2235435 7264649 := bstep (se 2 (by rfl) ⟨2724243, by rfl⟩ : syracuseStep 7264649 = 5448487) B5448487
theorem B4843099 : Blo 2235435 4843099 := bstep (se 1 (by rfl) ⟨3632324, by rfl⟩ : syracuseStep 4843099 = 7264649) B7264649
theorem B6457465 : Blo 2235435 6457465 := bstep (se 2 (by rfl) ⟨2421549, by rfl⟩ : syracuseStep 6457465 = 4843099) B4843099
theorem B34439813 : Blo 2235435 34439813 := bstep (se 4 (by rfl) ⟨3228732, by rfl⟩ : syracuseStep 34439813 = 6457465) B6457465
theorem B22959875 : Blo 2235435 22959875 := bstep (se 1 (by rfl) ⟨17219906, by rfl⟩ : syracuseStep 22959875 = 34439813) B34439813
theorem B15306583 : Blo 2235435 15306583 := bstep (se 1 (by rfl) ⟨11479937, by rfl⟩ : syracuseStep 15306583 = 22959875) B22959875
theorem B20408777 : Blo 2235435 20408777 := bstep (se 2 (by rfl) ⟨7653291, by rfl⟩ : syracuseStep 20408777 = 15306583) B15306583
theorem B13605851 : Blo 2235435 13605851 := bstep (se 1 (by rfl) ⟨10204388, by rfl⟩ : syracuseStep 13605851 = 20408777) B20408777
theorem B36282269 : Blo 2235435 36282269 := bstep (se 3 (by rfl) ⟨6802925, by rfl⟩ : syracuseStep 36282269 = 13605851) B13605851
theorem B24188179 : Blo 2235435 24188179 := bstep (se 1 (by rfl) ⟨18141134, by rfl⟩ : syracuseStep 24188179 = 36282269) B36282269
theorem B32250905 : Blo 2235435 32250905 := bstep (se 2 (by rfl) ⟨12094089, by rfl⟩ : syracuseStep 32250905 = 24188179) B24188179
theorem B21500603 : Blo 2235435 21500603 := bstep (se 1 (by rfl) ⟨16125452, by rfl⟩ : syracuseStep 21500603 = 32250905) B32250905
theorem B14333735 : Blo 2235435 14333735 := bstep (se 1 (by rfl) ⟨10750301, by rfl⟩ : syracuseStep 14333735 = 21500603) B21500603
theorem B9555823 : Blo 2235435 9555823 := bstep (se 1 (by rfl) ⟨7166867, by rfl⟩ : syracuseStep 9555823 = 14333735) B14333735
theorem B12741097 : Blo 2235435 12741097 := bstep (se 2 (by rfl) ⟨4777911, by rfl⟩ : syracuseStep 12741097 = 9555823) B9555823
theorem B16988129 : Blo 2235435 16988129 := bstep (se 2 (by rfl) ⟨6370548, by rfl⟩ : syracuseStep 16988129 = 12741097) B12741097
theorem B11325419 : Blo 2235435 11325419 := bstep (se 1 (by rfl) ⟨8494064, by rfl⟩ : syracuseStep 11325419 = 16988129) B16988129
theorem B7550279 : Blo 2235435 7550279 := bstep (se 1 (by rfl) ⟨5662709, by rfl⟩ : syracuseStep 7550279 = 11325419) B11325419
theorem B5033519 : Blo 2235435 5033519 := bstep (se 1 (by rfl) ⟨3775139, by rfl⟩ : syracuseStep 5033519 = 7550279) B7550279
theorem B3355679 : Blo 2235435 3355679 := bstep (se 1 (by rfl) ⟨2516759, by rfl⟩ : syracuseStep 3355679 = 5033519) B5033519
theorem B2237119 : Blo 2235435 2237119 := bstep (se 1 (by rfl) ⟨1677839, by rfl⟩ : syracuseStep 2237119 = 3355679) B3355679
theorem B3355685 : Blo 2235435 3355685 := bbase (se 4 (by rfl) ⟨314595, by rfl⟩ : syracuseStep 3355685 = 629191) (by norm_num)
theorem B2237123 : Blo 2235435 2237123 := bstep (se 1 (by rfl) ⟨1677842, by rfl⟩ : syracuseStep 2237123 = 3355685) B3355685
theorem B2831365 : Blo 2235435 2831365 := bbase (se 4 (by rfl) ⟨265440, by rfl⟩ : syracuseStep 2831365 = 530881) (by norm_num)
theorem B3775153 : Blo 2235435 3775153 := bstep (se 2 (by rfl) ⟨1415682, by rfl⟩ : syracuseStep 3775153 = 2831365) B2831365
theorem B5033537 : Blo 2235435 5033537 := bstep (se 2 (by rfl) ⟨1887576, by rfl⟩ : syracuseStep 5033537 = 3775153) B3775153
theorem B3355691 : Blo 2235435 3355691 := bstep (se 1 (by rfl) ⟨2516768, by rfl⟩ : syracuseStep 3355691 = 5033537) B5033537
theorem B2237127 : Blo 2235435 2237127 := bstep (se 1 (by rfl) ⟨1677845, by rfl⟩ : syracuseStep 2237127 = 3355691) B3355691
theorem B2516773 : Blo 2235435 2516773 := bbase (se 4 (by rfl) ⟨235947, by rfl⟩ : syracuseStep 2516773 = 471895) (by norm_num)
theorem B3355697 : Blo 2235435 3355697 := bstep (se 2 (by rfl) ⟨1258386, by rfl⟩ : syracuseStep 3355697 = 2516773) B2516773
theorem B2237131 : Blo 2235435 2237131 := bstep (se 1 (by rfl) ⟨1677848, by rfl⟩ : syracuseStep 2237131 = 3355697) B3355697
theorem B9555893 : Blo 2235435 9555893 := bbase (se 5 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 9555893 = 895865) (by norm_num)
theorem B6370595 : Blo 2235435 6370595 := bstep (se 1 (by rfl) ⟨4777946, by rfl⟩ : syracuseStep 6370595 = 9555893) B9555893
theorem B4247063 : Blo 2235435 4247063 := bstep (se 1 (by rfl) ⟨3185297, by rfl⟩ : syracuseStep 4247063 = 6370595) B6370595
theorem B2831375 : Blo 2235435 2831375 := bstep (se 1 (by rfl) ⟨2123531, by rfl⟩ : syracuseStep 2831375 = 4247063) B4247063
theorem B7550333 : Blo 2235435 7550333 := bstep (se 3 (by rfl) ⟨1415687, by rfl⟩ : syracuseStep 7550333 = 2831375) B2831375
theorem B5033555 : Blo 2235435 5033555 := bstep (se 1 (by rfl) ⟨3775166, by rfl⟩ : syracuseStep 5033555 = 7550333) B7550333
theorem B3355703 : Blo 2235435 3355703 := bstep (se 1 (by rfl) ⟨2516777, by rfl⟩ : syracuseStep 3355703 = 5033555) B5033555
theorem B2237135 : Blo 2235435 2237135 := bstep (se 1 (by rfl) ⟨1677851, by rfl⟩ : syracuseStep 2237135 = 3355703) B3355703
theorem B3355709 : Blo 2235435 3355709 := bbase (se 3 (by rfl) ⟨629195, by rfl⟩ : syracuseStep 3355709 = 1258391) (by norm_num)
theorem B2237139 : Blo 2235435 2237139 := bstep (se 1 (by rfl) ⟨1677854, by rfl⟩ : syracuseStep 2237139 = 3355709) B3355709
theorem B5033573 : Blo 2235435 5033573 := bbase (se 4 (by rfl) ⟨471897, by rfl⟩ : syracuseStep 5033573 = 943795) (by norm_num)
theorem B3355715 : Blo 2235435 3355715 := bstep (se 1 (by rfl) ⟨2516786, by rfl⟩ : syracuseStep 3355715 = 5033573) B5033573
theorem B2237143 : Blo 2235435 2237143 := bstep (se 1 (by rfl) ⟨1677857, by rfl⟩ : syracuseStep 2237143 = 3355715) B3355715
theorem B5662781 : Blo 2235435 5662781 := bbase (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) (by norm_num)
theorem B3775187 : Blo 2235435 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B2516791 : Blo 2235435 2516791 := bstep (se 1 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 2516791 = 3775187) B3775187
theorem B3355721 : Blo 2235435 3355721 := bstep (se 2 (by rfl) ⟨1258395, by rfl⟩ : syracuseStep 3355721 = 2516791) B2516791
theorem B2237147 : Blo 2235435 2237147 := bstep (se 1 (by rfl) ⟨1677860, by rfl⟩ : syracuseStep 2237147 = 3355721) B3355721
theorem B4247093 : Blo 2235435 4247093 := bbase (se 5 (by rfl) ⟨199082, by rfl⟩ : syracuseStep 4247093 = 398165) (by norm_num)
theorem B11325581 : Blo 2235435 11325581 := bstep (se 3 (by rfl) ⟨2123546, by rfl⟩ : syracuseStep 11325581 = 4247093) B4247093
theorem B7550387 : Blo 2235435 7550387 := bstep (se 1 (by rfl) ⟨5662790, by rfl⟩ : syracuseStep 7550387 = 11325581) B11325581
theorem B5033591 : Blo 2235435 5033591 := bstep (se 1 (by rfl) ⟨3775193, by rfl⟩ : syracuseStep 5033591 = 7550387) B7550387
theorem B3355727 : Blo 2235435 3355727 := bstep (se 1 (by rfl) ⟨2516795, by rfl⟩ : syracuseStep 3355727 = 5033591) B5033591
theorem B2237151 : Blo 2235435 2237151 := bstep (se 1 (by rfl) ⟨1677863, by rfl⟩ : syracuseStep 2237151 = 3355727) B3355727
theorem B3355733 : Blo 2235435 3355733 := bbase (se 8 (by rfl) ⟨19662, by rfl⟩ : syracuseStep 3355733 = 39325) (by norm_num)
theorem B2237155 : Blo 2235435 2237155 := bstep (se 1 (by rfl) ⟨1677866, by rfl⟩ : syracuseStep 2237155 = 3355733) B3355733
theorem B30613717 : Blo 2235435 30613717 := bbase (se 7 (by rfl) ⟨358754, by rfl⟩ : syracuseStep 30613717 = 717509) (by norm_num)
theorem B40818289 : Blo 2235435 40818289 := bstep (se 2 (by rfl) ⟨15306858, by rfl⟩ : syracuseStep 40818289 = 30613717) B30613717
theorem B54424385 : Blo 2235435 54424385 := bstep (se 2 (by rfl) ⟨20409144, by rfl⟩ : syracuseStep 54424385 = 40818289) B40818289
theorem B36282923 : Blo 2235435 36282923 := bstep (se 1 (by rfl) ⟨27212192, by rfl⟩ : syracuseStep 36282923 = 54424385) B54424385
theorem B24188615 : Blo 2235435 24188615 := bstep (se 1 (by rfl) ⟨18141461, by rfl⟩ : syracuseStep 24188615 = 36282923) B36282923
theorem B16125743 : Blo 2235435 16125743 := bstep (se 1 (by rfl) ⟨12094307, by rfl⟩ : syracuseStep 16125743 = 24188615) B24188615
theorem B10750495 : Blo 2235435 10750495 := bstep (se 1 (by rfl) ⟨8062871, by rfl⟩ : syracuseStep 10750495 = 16125743) B16125743
theorem B14333993 : Blo 2235435 14333993 := bstep (se 2 (by rfl) ⟨5375247, by rfl⟩ : syracuseStep 14333993 = 10750495) B10750495
theorem B9555995 : Blo 2235435 9555995 := bstep (se 1 (by rfl) ⟨7166996, by rfl⟩ : syracuseStep 9555995 = 14333993) B14333993
theorem B6370663 : Blo 2235435 6370663 := bstep (se 1 (by rfl) ⟨4777997, by rfl⟩ : syracuseStep 6370663 = 9555995) B9555995
theorem B8494217 : Blo 2235435 8494217 := bstep (se 2 (by rfl) ⟨3185331, by rfl⟩ : syracuseStep 8494217 = 6370663) B6370663
theorem B5662811 : Blo 2235435 5662811 := bstep (se 1 (by rfl) ⟨4247108, by rfl⟩ : syracuseStep 5662811 = 8494217) B8494217
theorem B3775207 : Blo 2235435 3775207 := bstep (se 1 (by rfl) ⟨2831405, by rfl⟩ : syracuseStep 3775207 = 5662811) B5662811
theorem B5033609 : Blo 2235435 5033609 := bstep (se 2 (by rfl) ⟨1887603, by rfl⟩ : syracuseStep 5033609 = 3775207) B3775207
theorem B3355739 : Blo 2235435 3355739 := bstep (se 1 (by rfl) ⟨2516804, by rfl⟩ : syracuseStep 3355739 = 5033609) B5033609
theorem B2237159 : Blo 2235435 2237159 := bstep (se 1 (by rfl) ⟨1677869, by rfl⟩ : syracuseStep 2237159 = 3355739) B3355739
theorem B2516809 : Blo 2235435 2516809 := bbase (se 2 (by rfl) ⟨943803, by rfl⟩ : syracuseStep 2516809 = 1887607) (by norm_num)
theorem B3355745 : Blo 2235435 3355745 := bstep (se 2 (by rfl) ⟨1258404, by rfl⟩ : syracuseStep 3355745 = 2516809) B2516809
theorem B2237163 : Blo 2235435 2237163 := bstep (se 1 (by rfl) ⟨1677872, by rfl⟩ : syracuseStep 2237163 = 3355745) B3355745
theorem B125819477 : Blo 2235435 125819477 := bbase (se 8 (by rfl) ⟨737223, by rfl⟩ : syracuseStep 125819477 = 1474447) (by norm_num)
theorem B83879651 : Blo 2235435 83879651 := bstep (se 1 (by rfl) ⟨62909738, by rfl⟩ : syracuseStep 83879651 = 125819477) B125819477
theorem B223679069 : Blo 2235435 223679069 := bstep (se 3 (by rfl) ⟨41939825, by rfl⟩ : syracuseStep 223679069 = 83879651) B83879651
theorem B149119379 : Blo 2235435 149119379 := bstep (se 1 (by rfl) ⟨111839534, by rfl⟩ : syracuseStep 149119379 = 223679069) B223679069
theorem B99412919 : Blo 2235435 99412919 := bstep (se 1 (by rfl) ⟨74559689, by rfl⟩ : syracuseStep 99412919 = 149119379) B149119379
theorem B66275279 : Blo 2235435 66275279 := bstep (se 1 (by rfl) ⟨49706459, by rfl⟩ : syracuseStep 66275279 = 99412919) B99412919
theorem B44183519 : Blo 2235435 44183519 := bstep (se 1 (by rfl) ⟨33137639, by rfl⟩ : syracuseStep 44183519 = 66275279) B66275279
theorem B29455679 : Blo 2235435 29455679 := bstep (se 1 (by rfl) ⟨22091759, by rfl⟩ : syracuseStep 29455679 = 44183519) B44183519
theorem B19637119 : Blo 2235435 19637119 := bstep (se 1 (by rfl) ⟨14727839, by rfl⟩ : syracuseStep 19637119 = 29455679) B29455679
theorem B104731301 : Blo 2235435 104731301 := bstep (se 4 (by rfl) ⟨9818559, by rfl⟩ : syracuseStep 104731301 = 19637119) B19637119
theorem B279283469 : Blo 2235435 279283469 := bstep (se 3 (by rfl) ⟨52365650, by rfl⟩ : syracuseStep 279283469 = 104731301) B104731301
theorem B2979023669 : Blo 2235435 2979023669 := bstep (se 5 (by rfl) ⟨139641734, by rfl⟩ : syracuseStep 2979023669 = 279283469) B279283469
theorem B1986015779 : Blo 2235435 1986015779 := bstep (se 1 (by rfl) ⟨1489511834, by rfl⟩ : syracuseStep 1986015779 = 2979023669) B2979023669
theorem B1324010519 : Blo 2235435 1324010519 := bstep (se 1 (by rfl) ⟨993007889, by rfl⟩ : syracuseStep 1324010519 = 1986015779) B1986015779
theorem B882673679 : Blo 2235435 882673679 := bstep (se 1 (by rfl) ⟨662005259, by rfl⟩ : syracuseStep 882673679 = 1324010519) B1324010519
theorem B588449119 : Blo 2235435 588449119 := bstep (se 1 (by rfl) ⟨441336839, by rfl⟩ : syracuseStep 588449119 = 882673679) B882673679
theorem B784598825 : Blo 2235435 784598825 := bstep (se 2 (by rfl) ⟨294224559, by rfl⟩ : syracuseStep 784598825 = 588449119) B588449119
theorem B523065883 : Blo 2235435 523065883 := bstep (se 1 (by rfl) ⟨392299412, by rfl⟩ : syracuseStep 523065883 = 784598825) B784598825
theorem B697421177 : Blo 2235435 697421177 := bstep (se 2 (by rfl) ⟨261532941, by rfl⟩ : syracuseStep 697421177 = 523065883) B523065883
theorem B464947451 : Blo 2235435 464947451 := bstep (se 1 (by rfl) ⟨348710588, by rfl⟩ : syracuseStep 464947451 = 697421177) B697421177
theorem B309964967 : Blo 2235435 309964967 := bstep (se 1 (by rfl) ⟨232473725, by rfl⟩ : syracuseStep 309964967 = 464947451) B464947451
theorem B206643311 : Blo 2235435 206643311 := bstep (se 1 (by rfl) ⟨154982483, by rfl⟩ : syracuseStep 206643311 = 309964967) B309964967
theorem B137762207 : Blo 2235435 137762207 := bstep (se 1 (by rfl) ⟨103321655, by rfl⟩ : syracuseStep 137762207 = 206643311) B206643311
theorem B91841471 : Blo 2235435 91841471 := bstep (se 1 (by rfl) ⟨68881103, by rfl⟩ : syracuseStep 91841471 = 137762207) B137762207
theorem B61227647 : Blo 2235435 61227647 := bstep (se 1 (by rfl) ⟨45920735, by rfl⟩ : syracuseStep 61227647 = 91841471) B91841471
theorem B40818431 : Blo 2235435 40818431 := bstep (se 1 (by rfl) ⟨30613823, by rfl⟩ : syracuseStep 40818431 = 61227647) B61227647
theorem B27212287 : Blo 2235435 27212287 := bstep (se 1 (by rfl) ⟨20409215, by rfl⟩ : syracuseStep 27212287 = 40818431) B40818431
theorem B36283049 : Blo 2235435 36283049 := bstep (se 2 (by rfl) ⟨13606143, by rfl⟩ : syracuseStep 36283049 = 27212287) B27212287
theorem B24188699 : Blo 2235435 24188699 := bstep (se 1 (by rfl) ⟨18141524, by rfl⟩ : syracuseStep 24188699 = 36283049) B36283049
theorem B16125799 : Blo 2235435 16125799 := bstep (se 1 (by rfl) ⟨12094349, by rfl⟩ : syracuseStep 16125799 = 24188699) B24188699
theorem B21501065 : Blo 2235435 21501065 := bstep (se 2 (by rfl) ⟨8062899, by rfl⟩ : syracuseStep 21501065 = 16125799) B16125799
theorem B14334043 : Blo 2235435 14334043 := bstep (se 1 (by rfl) ⟨10750532, by rfl⟩ : syracuseStep 14334043 = 21501065) B21501065
theorem B19112057 : Blo 2235435 19112057 := bstep (se 2 (by rfl) ⟨7167021, by rfl⟩ : syracuseStep 19112057 = 14334043) B14334043
theorem B12741371 : Blo 2235435 12741371 := bstep (se 1 (by rfl) ⟨9556028, by rfl⟩ : syracuseStep 12741371 = 19112057) B19112057
theorem B8494247 : Blo 2235435 8494247 := bstep (se 1 (by rfl) ⟨6370685, by rfl⟩ : syracuseStep 8494247 = 12741371) B12741371
theorem B5662831 : Blo 2235435 5662831 := bstep (se 1 (by rfl) ⟨4247123, by rfl⟩ : syracuseStep 5662831 = 8494247) B8494247
theorem B7550441 : Blo 2235435 7550441 := bstep (se 2 (by rfl) ⟨2831415, by rfl⟩ : syracuseStep 7550441 = 5662831) B5662831
theorem B5033627 : Blo 2235435 5033627 := bstep (se 1 (by rfl) ⟨3775220, by rfl⟩ : syracuseStep 5033627 = 7550441) B7550441
theorem B3355751 : Blo 2235435 3355751 := bstep (se 1 (by rfl) ⟨2516813, by rfl⟩ : syracuseStep 3355751 = 5033627) B5033627
theorem B2237167 : Blo 2235435 2237167 := bstep (se 1 (by rfl) ⟨1677875, by rfl⟩ : syracuseStep 2237167 = 3355751) B3355751
theorem B3355757 : Blo 2235435 3355757 := bbase (se 3 (by rfl) ⟨629204, by rfl⟩ : syracuseStep 3355757 = 1258409) (by norm_num)
theorem B2237171 : Blo 2235435 2237171 := bstep (se 1 (by rfl) ⟨1677878, by rfl⟩ : syracuseStep 2237171 = 3355757) B3355757
theorem B5033645 : Blo 2235435 5033645 := bbase (se 3 (by rfl) ⟨943808, by rfl⟩ : syracuseStep 5033645 = 1887617) (by norm_num)
theorem B3355763 : Blo 2235435 3355763 := bstep (se 1 (by rfl) ⟨2516822, by rfl⟩ : syracuseStep 3355763 = 5033645) B5033645
theorem B2237175 : Blo 2235435 2237175 := bstep (se 1 (by rfl) ⟨1677881, by rfl⟩ : syracuseStep 2237175 = 3355763) B3355763
theorem B3023605 : Blo 2235435 3023605 := bbase (se 5 (by rfl) ⟨141731, by rfl⟩ : syracuseStep 3023605 = 283463) (by norm_num)
theorem B4031473 : Blo 2235435 4031473 := bstep (se 2 (by rfl) ⟨1511802, by rfl⟩ : syracuseStep 4031473 = 3023605) B3023605
theorem B5375297 : Blo 2235435 5375297 := bstep (se 2 (by rfl) ⟨2015736, by rfl⟩ : syracuseStep 5375297 = 4031473) B4031473
theorem B3583531 : Blo 2235435 3583531 := bstep (se 1 (by rfl) ⟨2687648, by rfl⟩ : syracuseStep 3583531 = 5375297) B5375297
theorem B4778041 : Blo 2235435 4778041 := bstep (se 2 (by rfl) ⟨1791765, by rfl⟩ : syracuseStep 4778041 = 3583531) B3583531
theorem B6370721 : Blo 2235435 6370721 := bstep (se 2 (by rfl) ⟨2389020, by rfl⟩ : syracuseStep 6370721 = 4778041) B4778041
theorem B4247147 : Blo 2235435 4247147 := bstep (se 1 (by rfl) ⟨3185360, by rfl⟩ : syracuseStep 4247147 = 6370721) B6370721
theorem B2831431 : Blo 2235435 2831431 := bstep (se 1 (by rfl) ⟨2123573, by rfl⟩ : syracuseStep 2831431 = 4247147) B4247147
theorem B3775241 : Blo 2235435 3775241 := bstep (se 2 (by rfl) ⟨1415715, by rfl⟩ : syracuseStep 3775241 = 2831431) B2831431
theorem B2516827 : Blo 2235435 2516827 := bstep (se 1 (by rfl) ⟨1887620, by rfl⟩ : syracuseStep 2516827 = 3775241) B3775241
theorem B3355769 : Blo 2235435 3355769 := bstep (se 2 (by rfl) ⟨1258413, by rfl⟩ : syracuseStep 3355769 = 2516827) B2516827
theorem B2237179 : Blo 2235435 2237179 := bstep (se 1 (by rfl) ⟨1677884, by rfl⟩ : syracuseStep 2237179 = 3355769) B3355769
theorem B18141653 : Blo 2235435 18141653 := bbase (se 7 (by rfl) ⟨212597, by rfl⟩ : syracuseStep 18141653 = 425195) (by norm_num)
theorem B12094435 : Blo 2235435 12094435 := bstep (se 1 (by rfl) ⟨9070826, by rfl⟩ : syracuseStep 12094435 = 18141653) B18141653
theorem B16125913 : Blo 2235435 16125913 := bstep (se 2 (by rfl) ⟨6047217, by rfl⟩ : syracuseStep 16125913 = 12094435) B12094435
theorem B21501217 : Blo 2235435 21501217 := bstep (se 2 (by rfl) ⟨8062956, by rfl⟩ : syracuseStep 21501217 = 16125913) B16125913
theorem B28668289 : Blo 2235435 28668289 := bstep (se 2 (by rfl) ⟨10750608, by rfl⟩ : syracuseStep 28668289 = 21501217) B21501217
theorem B38224385 : Blo 2235435 38224385 := bstep (se 2 (by rfl) ⟨14334144, by rfl⟩ : syracuseStep 38224385 = 28668289) B28668289
theorem B25482923 : Blo 2235435 25482923 := bstep (se 1 (by rfl) ⟨19112192, by rfl⟩ : syracuseStep 25482923 = 38224385) B38224385
theorem B16988615 : Blo 2235435 16988615 := bstep (se 1 (by rfl) ⟨12741461, by rfl⟩ : syracuseStep 16988615 = 25482923) B25482923
theorem B11325743 : Blo 2235435 11325743 := bstep (se 1 (by rfl) ⟨8494307, by rfl⟩ : syracuseStep 11325743 = 16988615) B16988615
theorem B7550495 : Blo 2235435 7550495 := bstep (se 1 (by rfl) ⟨5662871, by rfl⟩ : syracuseStep 7550495 = 11325743) B11325743
theorem B5033663 : Blo 2235435 5033663 := bstep (se 1 (by rfl) ⟨3775247, by rfl⟩ : syracuseStep 5033663 = 7550495) B7550495
theorem B3355775 : Blo 2235435 3355775 := bstep (se 1 (by rfl) ⟨2516831, by rfl⟩ : syracuseStep 3355775 = 5033663) B5033663
theorem B2237183 : Blo 2235435 2237183 := bstep (se 1 (by rfl) ⟨1677887, by rfl⟩ : syracuseStep 2237183 = 3355775) B3355775
theorem B3355781 : Blo 2235435 3355781 := bbase (se 4 (by rfl) ⟨314604, by rfl⟩ : syracuseStep 3355781 = 629209) (by norm_num)
theorem B2237187 : Blo 2235435 2237187 := bstep (se 1 (by rfl) ⟨1677890, by rfl⟩ : syracuseStep 2237187 = 3355781) B3355781
theorem B3775261 : Blo 2235435 3775261 := bbase (se 3 (by rfl) ⟨707861, by rfl⟩ : syracuseStep 3775261 = 1415723) (by norm_num)
theorem B5033681 : Blo 2235435 5033681 := bstep (se 2 (by rfl) ⟨1887630, by rfl⟩ : syracuseStep 5033681 = 3775261) B3775261
theorem B3355787 : Blo 2235435 3355787 := bstep (se 1 (by rfl) ⟨2516840, by rfl⟩ : syracuseStep 3355787 = 5033681) B5033681
theorem B2237191 : Blo 2235435 2237191 := bstep (se 1 (by rfl) ⟨1677893, by rfl⟩ : syracuseStep 2237191 = 3355787) B3355787
theorem B2516845 : Blo 2235435 2516845 := bbase (se 3 (by rfl) ⟨471908, by rfl⟩ : syracuseStep 2516845 = 943817) (by norm_num)
theorem B3355793 : Blo 2235435 3355793 := bstep (se 2 (by rfl) ⟨1258422, by rfl⟩ : syracuseStep 3355793 = 2516845) B2516845
theorem B2237195 : Blo 2235435 2237195 := bstep (se 1 (by rfl) ⟨1677896, by rfl⟩ : syracuseStep 2237195 = 3355793) B3355793
theorem B7550549 : Blo 2235435 7550549 := bbase (se 8 (by rfl) ⟨44241, by rfl⟩ : syracuseStep 7550549 = 88483) (by norm_num)
theorem B5033699 : Blo 2235435 5033699 := bstep (se 1 (by rfl) ⟨3775274, by rfl⟩ : syracuseStep 5033699 = 7550549) B7550549
theorem B3355799 : Blo 2235435 3355799 := bstep (se 1 (by rfl) ⟨2516849, by rfl⟩ : syracuseStep 3355799 = 5033699) B5033699
theorem B2237199 : Blo 2235435 2237199 := bstep (se 1 (by rfl) ⟨1677899, by rfl⟩ : syracuseStep 2237199 = 3355799) B3355799
theorem B3355805 : Blo 2235435 3355805 := bbase (se 3 (by rfl) ⟨629213, by rfl⟩ : syracuseStep 3355805 = 1258427) (by norm_num)
theorem B2237203 : Blo 2235435 2237203 := bstep (se 1 (by rfl) ⟨1677902, by rfl⟩ : syracuseStep 2237203 = 3355805) B3355805
theorem B5033717 : Blo 2235435 5033717 := bbase (se 5 (by rfl) ⟨235955, by rfl⟩ : syracuseStep 5033717 = 471911) (by norm_num)
theorem B3355811 : Blo 2235435 3355811 := bstep (se 1 (by rfl) ⟨2516858, by rfl⟩ : syracuseStep 3355811 = 5033717) B5033717
theorem B2237207 : Blo 2235435 2237207 := bstep (se 1 (by rfl) ⟨1677905, by rfl⟩ : syracuseStep 2237207 = 3355811) B3355811
theorem B6457733 : Blo 2235435 6457733 := bbase (se 4 (by rfl) ⟨605412, by rfl⟩ : syracuseStep 6457733 = 1210825) (by norm_num)
theorem B4305155 : Blo 2235435 4305155 := bstep (se 1 (by rfl) ⟨3228866, by rfl⟩ : syracuseStep 4305155 = 6457733) B6457733
theorem B11480413 : Blo 2235435 11480413 := bstep (se 3 (by rfl) ⟨2152577, by rfl⟩ : syracuseStep 11480413 = 4305155) B4305155
theorem B15307217 : Blo 2235435 15307217 := bstep (se 2 (by rfl) ⟨5740206, by rfl⟩ : syracuseStep 15307217 = 11480413) B11480413
theorem B10204811 : Blo 2235435 10204811 := bstep (se 1 (by rfl) ⟨7653608, by rfl⟩ : syracuseStep 10204811 = 15307217) B15307217
theorem B6803207 : Blo 2235435 6803207 := bstep (se 1 (by rfl) ⟨5102405, by rfl⟩ : syracuseStep 6803207 = 10204811) B10204811
theorem B4535471 : Blo 2235435 4535471 := bstep (se 1 (by rfl) ⟨3401603, by rfl⟩ : syracuseStep 4535471 = 6803207) B6803207
theorem B12094589 : Blo 2235435 12094589 := bstep (se 3 (by rfl) ⟨2267735, by rfl⟩ : syracuseStep 12094589 = 4535471) B4535471
theorem B8063059 : Blo 2235435 8063059 := bstep (se 1 (by rfl) ⟨6047294, by rfl⟩ : syracuseStep 8063059 = 12094589) B12094589
theorem B10750745 : Blo 2235435 10750745 := bstep (se 2 (by rfl) ⟨4031529, by rfl⟩ : syracuseStep 10750745 = 8063059) B8063059
theorem B28668653 : Blo 2235435 28668653 := bstep (se 3 (by rfl) ⟨5375372, by rfl⟩ : syracuseStep 28668653 = 10750745) B10750745
theorem B19112435 : Blo 2235435 19112435 := bstep (se 1 (by rfl) ⟨14334326, by rfl⟩ : syracuseStep 19112435 = 28668653) B28668653
theorem B12741623 : Blo 2235435 12741623 := bstep (se 1 (by rfl) ⟨9556217, by rfl⟩ : syracuseStep 12741623 = 19112435) B19112435
theorem B8494415 : Blo 2235435 8494415 := bstep (se 1 (by rfl) ⟨6370811, by rfl⟩ : syracuseStep 8494415 = 12741623) B12741623
theorem B5662943 : Blo 2235435 5662943 := bstep (se 1 (by rfl) ⟨4247207, by rfl⟩ : syracuseStep 5662943 = 8494415) B8494415
theorem B3775295 : Blo 2235435 3775295 := bstep (se 1 (by rfl) ⟨2831471, by rfl⟩ : syracuseStep 3775295 = 5662943) B5662943
theorem B2516863 : Blo 2235435 2516863 := bstep (se 1 (by rfl) ⟨1887647, by rfl⟩ : syracuseStep 2516863 = 3775295) B3775295
theorem B3355817 : Blo 2235435 3355817 := bstep (se 2 (by rfl) ⟨1258431, by rfl⟩ : syracuseStep 3355817 = 2516863) B2516863
theorem B2237211 : Blo 2235435 2237211 := bstep (se 1 (by rfl) ⟨1677908, by rfl⟩ : syracuseStep 2237211 = 3355817) B3355817
theorem B4778117 : Blo 2235435 4778117 := bbase (se 4 (by rfl) ⟨447948, by rfl⟩ : syracuseStep 4778117 = 895897) (by norm_num)
theorem B3185411 : Blo 2235435 3185411 := bstep (se 1 (by rfl) ⟨2389058, by rfl⟩ : syracuseStep 3185411 = 4778117) B4778117
theorem B8494429 : Blo 2235435 8494429 := bstep (se 3 (by rfl) ⟨1592705, by rfl⟩ : syracuseStep 8494429 = 3185411) B3185411
theorem B11325905 : Blo 2235435 11325905 := bstep (se 2 (by rfl) ⟨4247214, by rfl⟩ : syracuseStep 11325905 = 8494429) B8494429
theorem B7550603 : Blo 2235435 7550603 := bstep (se 1 (by rfl) ⟨5662952, by rfl⟩ : syracuseStep 7550603 = 11325905) B11325905
theorem B5033735 : Blo 2235435 5033735 := bstep (se 1 (by rfl) ⟨3775301, by rfl⟩ : syracuseStep 5033735 = 7550603) B7550603
theorem B3355823 : Blo 2235435 3355823 := bstep (se 1 (by rfl) ⟨2516867, by rfl⟩ : syracuseStep 3355823 = 5033735) B5033735
theorem B2237215 : Blo 2235435 2237215 := bstep (se 1 (by rfl) ⟨1677911, by rfl⟩ : syracuseStep 2237215 = 3355823) B3355823
theorem B3355829 : Blo 2235435 3355829 := bbase (se 5 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 3355829 = 314609) (by norm_num)
theorem B2237219 : Blo 2235435 2237219 := bstep (se 1 (by rfl) ⟨1677914, by rfl⟩ : syracuseStep 2237219 = 3355829) B3355829
theorem B5662973 : Blo 2235435 5662973 := bbase (se 3 (by rfl) ⟨1061807, by rfl⟩ : syracuseStep 5662973 = 2123615) (by norm_num)
theorem B3775315 : Blo 2235435 3775315 := bstep (se 1 (by rfl) ⟨2831486, by rfl⟩ : syracuseStep 3775315 = 5662973) B5662973
theorem B5033753 : Blo 2235435 5033753 := bstep (se 2 (by rfl) ⟨1887657, by rfl⟩ : syracuseStep 5033753 = 3775315) B3775315
theorem B3355835 : Blo 2235435 3355835 := bstep (se 1 (by rfl) ⟨2516876, by rfl⟩ : syracuseStep 3355835 = 5033753) B5033753
theorem B2237223 : Blo 2235435 2237223 := bstep (se 1 (by rfl) ⟨1677917, by rfl⟩ : syracuseStep 2237223 = 3355835) B3355835
theorem B2516881 : Blo 2235435 2516881 := bbase (se 2 (by rfl) ⟨943830, by rfl⟩ : syracuseStep 2516881 = 1887661) (by norm_num)
theorem B3355841 : Blo 2235435 3355841 := bstep (se 2 (by rfl) ⟨1258440, by rfl⟩ : syracuseStep 3355841 = 2516881) B2516881
theorem B2237227 : Blo 2235435 2237227 := bstep (se 1 (by rfl) ⟨1677920, by rfl⟩ : syracuseStep 2237227 = 3355841) B3355841
theorem B4247245 : Blo 2235435 4247245 := bbase (se 3 (by rfl) ⟨796358, by rfl⟩ : syracuseStep 4247245 = 1592717) (by norm_num)
theorem B5662993 : Blo 2235435 5662993 := bstep (se 2 (by rfl) ⟨2123622, by rfl⟩ : syracuseStep 5662993 = 4247245) B4247245
theorem B7550657 : Blo 2235435 7550657 := bstep (se 2 (by rfl) ⟨2831496, by rfl⟩ : syracuseStep 7550657 = 5662993) B5662993
theorem B5033771 : Blo 2235435 5033771 := bstep (se 1 (by rfl) ⟨3775328, by rfl⟩ : syracuseStep 5033771 = 7550657) B7550657
theorem B3355847 : Blo 2235435 3355847 := bstep (se 1 (by rfl) ⟨2516885, by rfl⟩ : syracuseStep 3355847 = 5033771) B5033771
theorem B2237231 : Blo 2235435 2237231 := bstep (se 1 (by rfl) ⟨1677923, by rfl⟩ : syracuseStep 2237231 = 3355847) B3355847
theorem B3355853 : Blo 2235435 3355853 := bbase (se 3 (by rfl) ⟨629222, by rfl⟩ : syracuseStep 3355853 = 1258445) (by norm_num)
theorem B2237235 : Blo 2235435 2237235 := bstep (se 1 (by rfl) ⟨1677926, by rfl⟩ : syracuseStep 2237235 = 3355853) B3355853
theorem B5033789 : Blo 2235435 5033789 := bbase (se 3 (by rfl) ⟨943835, by rfl⟩ : syracuseStep 5033789 = 1887671) (by norm_num)
theorem B3355859 : Blo 2235435 3355859 := bstep (se 1 (by rfl) ⟨2516894, by rfl⟩ : syracuseStep 3355859 = 5033789) B5033789
theorem B2237239 : Blo 2235435 2237239 := bstep (se 1 (by rfl) ⟨1677929, by rfl⟩ : syracuseStep 2237239 = 3355859) B3355859
theorem B3775349 : Blo 2235435 3775349 := bbase (se 5 (by rfl) ⟨176969, by rfl⟩ : syracuseStep 3775349 = 353939) (by norm_num)
theorem B2516899 : Blo 2235435 2516899 := bstep (se 1 (by rfl) ⟨1887674, by rfl⟩ : syracuseStep 2516899 = 3775349) B3775349
theorem B3355865 : Blo 2235435 3355865 := bstep (se 2 (by rfl) ⟨1258449, by rfl⟩ : syracuseStep 3355865 = 2516899) B2516899
theorem B2237243 : Blo 2235435 2237243 := bstep (se 1 (by rfl) ⟨1677932, by rfl⟩ : syracuseStep 2237243 = 3355865) B3355865
theorem B8063189 : Blo 2235435 8063189 := bbase (se 7 (by rfl) ⟨94490, by rfl⟩ : syracuseStep 8063189 = 188981) (by norm_num)
theorem B5375459 : Blo 2235435 5375459 := bstep (se 1 (by rfl) ⟨4031594, by rfl⟩ : syracuseStep 5375459 = 8063189) B8063189
theorem B3583639 : Blo 2235435 3583639 := bstep (se 1 (by rfl) ⟨2687729, by rfl⟩ : syracuseStep 3583639 = 5375459) B5375459
theorem B4778185 : Blo 2235435 4778185 := bstep (se 2 (by rfl) ⟨1791819, by rfl⟩ : syracuseStep 4778185 = 3583639) B3583639
theorem B6370913 : Blo 2235435 6370913 := bstep (se 2 (by rfl) ⟨2389092, by rfl⟩ : syracuseStep 6370913 = 4778185) B4778185
theorem B16989101 : Blo 2235435 16989101 := bstep (se 3 (by rfl) ⟨3185456, by rfl⟩ : syracuseStep 16989101 = 6370913) B6370913
theorem B11326067 : Blo 2235435 11326067 := bstep (se 1 (by rfl) ⟨8494550, by rfl⟩ : syracuseStep 11326067 = 16989101) B16989101
theorem B7550711 : Blo 2235435 7550711 := bstep (se 1 (by rfl) ⟨5663033, by rfl⟩ : syracuseStep 7550711 = 11326067) B11326067
theorem B5033807 : Blo 2235435 5033807 := bstep (se 1 (by rfl) ⟨3775355, by rfl⟩ : syracuseStep 5033807 = 7550711) B7550711
theorem B3355871 : Blo 2235435 3355871 := bstep (se 1 (by rfl) ⟨2516903, by rfl⟩ : syracuseStep 3355871 = 5033807) B5033807
theorem B2237247 : Blo 2235435 2237247 := bstep (se 1 (by rfl) ⟨1677935, by rfl⟩ : syracuseStep 2237247 = 3355871) B3355871
theorem B3355877 : Blo 2235435 3355877 := bbase (se 4 (by rfl) ⟨314613, by rfl⟩ : syracuseStep 3355877 = 629227) (by norm_num)
theorem B2237251 : Blo 2235435 2237251 := bstep (se 1 (by rfl) ⟨1677938, by rfl⟩ : syracuseStep 2237251 = 3355877) B3355877
theorem B4843397 : Blo 2235435 4843397 := bbase (se 4 (by rfl) ⟨454068, by rfl⟩ : syracuseStep 4843397 = 908137) (by norm_num)
theorem B3228931 : Blo 2235435 3228931 := bstep (se 1 (by rfl) ⟨2421698, by rfl⟩ : syracuseStep 3228931 = 4843397) B4843397
theorem B4305241 : Blo 2235435 4305241 := bstep (se 2 (by rfl) ⟨1614465, by rfl⟩ : syracuseStep 4305241 = 3228931) B3228931
theorem B5740321 : Blo 2235435 5740321 := bstep (se 2 (by rfl) ⟨2152620, by rfl⟩ : syracuseStep 5740321 = 4305241) B4305241
theorem B7653761 : Blo 2235435 7653761 := bstep (se 2 (by rfl) ⟨2870160, by rfl⟩ : syracuseStep 7653761 = 5740321) B5740321
theorem B5102507 : Blo 2235435 5102507 := bstep (se 1 (by rfl) ⟨3826880, by rfl⟩ : syracuseStep 5102507 = 7653761) B7653761
theorem B3401671 : Blo 2235435 3401671 := bstep (se 1 (by rfl) ⟨2551253, by rfl⟩ : syracuseStep 3401671 = 5102507) B5102507
theorem B4535561 : Blo 2235435 4535561 := bstep (se 2 (by rfl) ⟨1700835, by rfl⟩ : syracuseStep 4535561 = 3401671) B3401671
theorem B12094829 : Blo 2235435 12094829 := bstep (se 3 (by rfl) ⟨2267780, by rfl⟩ : syracuseStep 12094829 = 4535561) B4535561
theorem B8063219 : Blo 2235435 8063219 := bstep (se 1 (by rfl) ⟨6047414, by rfl⟩ : syracuseStep 8063219 = 12094829) B12094829
theorem B5375479 : Blo 2235435 5375479 := bstep (se 1 (by rfl) ⟨4031609, by rfl⟩ : syracuseStep 5375479 = 8063219) B8063219
theorem B7167305 : Blo 2235435 7167305 := bstep (se 2 (by rfl) ⟨2687739, by rfl⟩ : syracuseStep 7167305 = 5375479) B5375479
theorem B4778203 : Blo 2235435 4778203 := bstep (se 1 (by rfl) ⟨3583652, by rfl⟩ : syracuseStep 4778203 = 7167305) B7167305
theorem B6370937 : Blo 2235435 6370937 := bstep (se 2 (by rfl) ⟨2389101, by rfl⟩ : syracuseStep 6370937 = 4778203) B4778203
theorem B4247291 : Blo 2235435 4247291 := bstep (se 1 (by rfl) ⟨3185468, by rfl⟩ : syracuseStep 4247291 = 6370937) B6370937
theorem B2831527 : Blo 2235435 2831527 := bstep (se 1 (by rfl) ⟨2123645, by rfl⟩ : syracuseStep 2831527 = 4247291) B4247291
theorem B3775369 : Blo 2235435 3775369 := bstep (se 2 (by rfl) ⟨1415763, by rfl⟩ : syracuseStep 3775369 = 2831527) B2831527
theorem B5033825 : Blo 2235435 5033825 := bstep (se 2 (by rfl) ⟨1887684, by rfl⟩ : syracuseStep 5033825 = 3775369) B3775369
theorem B3355883 : Blo 2235435 3355883 := bstep (se 1 (by rfl) ⟨2516912, by rfl⟩ : syracuseStep 3355883 = 5033825) B5033825
theorem B2237255 : Blo 2235435 2237255 := bstep (se 1 (by rfl) ⟨1677941, by rfl⟩ : syracuseStep 2237255 = 3355883) B3355883
theorem B2516917 : Blo 2235435 2516917 := bbase (se 5 (by rfl) ⟨117980, by rfl⟩ : syracuseStep 2516917 = 235961) (by norm_num)
theorem B3355889 : Blo 2235435 3355889 := bstep (se 2 (by rfl) ⟨1258458, by rfl⟩ : syracuseStep 3355889 = 2516917) B2516917
theorem B2237259 : Blo 2235435 2237259 := bstep (se 1 (by rfl) ⟨1677944, by rfl⟩ : syracuseStep 2237259 = 3355889) B3355889
theorem B2831537 : Blo 2235435 2831537 := bbase (se 2 (by rfl) ⟨1061826, by rfl⟩ : syracuseStep 2831537 = 2123653) (by norm_num)
theorem B7550765 : Blo 2235435 7550765 := bstep (se 3 (by rfl) ⟨1415768, by rfl⟩ : syracuseStep 7550765 = 2831537) B2831537
theorem B5033843 : Blo 2235435 5033843 := bstep (se 1 (by rfl) ⟨3775382, by rfl⟩ : syracuseStep 5033843 = 7550765) B7550765
theorem B3355895 : Blo 2235435 3355895 := bstep (se 1 (by rfl) ⟨2516921, by rfl⟩ : syracuseStep 3355895 = 5033843) B5033843
theorem B2237263 : Blo 2235435 2237263 := bstep (se 1 (by rfl) ⟨1677947, by rfl⟩ : syracuseStep 2237263 = 3355895) B3355895
theorem B3355901 : Blo 2235435 3355901 := bbase (se 3 (by rfl) ⟨629231, by rfl⟩ : syracuseStep 3355901 = 1258463) (by norm_num)
theorem B2237267 : Blo 2235435 2237267 := bstep (se 1 (by rfl) ⟨1677950, by rfl⟩ : syracuseStep 2237267 = 3355901) B3355901
theorem B5033861 : Blo 2235435 5033861 := bbase (se 4 (by rfl) ⟨471924, by rfl⟩ : syracuseStep 5033861 = 943849) (by norm_num)
theorem B3355907 : Blo 2235435 3355907 := bstep (se 1 (by rfl) ⟨2516930, by rfl⟩ : syracuseStep 3355907 = 5033861) B5033861
theorem B2237271 : Blo 2235435 2237271 := bstep (se 1 (by rfl) ⟨1677953, by rfl⟩ : syracuseStep 2237271 = 3355907) B3355907
theorem B3583685 : Blo 2235435 3583685 := bbase (se 4 (by rfl) ⟨335970, by rfl⟩ : syracuseStep 3583685 = 671941) (by norm_num)
theorem B2389123 : Blo 2235435 2389123 := bstep (se 1 (by rfl) ⟨1791842, by rfl⟩ : syracuseStep 2389123 = 3583685) B3583685
theorem B3185497 : Blo 2235435 3185497 := bstep (se 2 (by rfl) ⟨1194561, by rfl⟩ : syracuseStep 3185497 = 2389123) B2389123
theorem B4247329 : Blo 2235435 4247329 := bstep (se 2 (by rfl) ⟨1592748, by rfl⟩ : syracuseStep 4247329 = 3185497) B3185497
theorem B5663105 : Blo 2235435 5663105 := bstep (se 2 (by rfl) ⟨2123664, by rfl⟩ : syracuseStep 5663105 = 4247329) B4247329
theorem B3775403 : Blo 2235435 3775403 := bstep (se 1 (by rfl) ⟨2831552, by rfl⟩ : syracuseStep 3775403 = 5663105) B5663105
theorem B2516935 : Blo 2235435 2516935 := bstep (se 1 (by rfl) ⟨1887701, by rfl⟩ : syracuseStep 2516935 = 3775403) B3775403
theorem B3355913 : Blo 2235435 3355913 := bstep (se 2 (by rfl) ⟨1258467, by rfl⟩ : syracuseStep 3355913 = 2516935) B2516935
theorem B2237275 : Blo 2235435 2237275 := bstep (se 1 (by rfl) ⟨1677956, by rfl⟩ : syracuseStep 2237275 = 3355913) B3355913
theorem B11326229 : Blo 2235435 11326229 := bbase (se 6 (by rfl) ⟨265458, by rfl⟩ : syracuseStep 11326229 = 530917) (by norm_num)
theorem B7550819 : Blo 2235435 7550819 := bstep (se 1 (by rfl) ⟨5663114, by rfl⟩ : syracuseStep 7550819 = 11326229) B11326229
theorem B5033879 : Blo 2235435 5033879 := bstep (se 1 (by rfl) ⟨3775409, by rfl⟩ : syracuseStep 5033879 = 7550819) B7550819
theorem B3355919 : Blo 2235435 3355919 := bstep (se 1 (by rfl) ⟨2516939, by rfl⟩ : syracuseStep 3355919 = 5033879) B5033879
theorem B2237279 : Blo 2235435 2237279 := bstep (se 1 (by rfl) ⟨1677959, by rfl⟩ : syracuseStep 2237279 = 3355919) B3355919
theorem B3355925 : Blo 2235435 3355925 := bbase (se 6 (by rfl) ⟨78654, by rfl⟩ : syracuseStep 3355925 = 157309) (by norm_num)
theorem B2237283 : Blo 2235435 2237283 := bstep (se 1 (by rfl) ⟨1677962, by rfl⟩ : syracuseStep 2237283 = 3355925) B3355925
theorem B2551289 : Blo 2235435 2551289 := bbase (se 2 (by rfl) ⟨956733, by rfl⟩ : syracuseStep 2551289 = 1913467) (by norm_num)
theorem B6803437 : Blo 2235435 6803437 := bstep (se 3 (by rfl) ⟨1275644, by rfl⟩ : syracuseStep 6803437 = 2551289) B2551289
theorem B9071249 : Blo 2235435 9071249 := bstep (se 2 (by rfl) ⟨3401718, by rfl⟩ : syracuseStep 9071249 = 6803437) B6803437
theorem B24189997 : Blo 2235435 24189997 := bstep (se 3 (by rfl) ⟨4535624, by rfl⟩ : syracuseStep 24189997 = 9071249) B9071249
theorem B32253329 : Blo 2235435 32253329 := bstep (se 2 (by rfl) ⟨12094998, by rfl⟩ : syracuseStep 32253329 = 24189997) B24189997
theorem B21502219 : Blo 2235435 21502219 := bstep (se 1 (by rfl) ⟨16126664, by rfl⟩ : syracuseStep 21502219 = 32253329) B32253329
theorem B28669625 : Blo 2235435 28669625 := bstep (se 2 (by rfl) ⟨10751109, by rfl⟩ : syracuseStep 28669625 = 21502219) B21502219
theorem B19113083 : Blo 2235435 19113083 := bstep (se 1 (by rfl) ⟨14334812, by rfl⟩ : syracuseStep 19113083 = 28669625) B28669625
theorem B12742055 : Blo 2235435 12742055 := bstep (se 1 (by rfl) ⟨9556541, by rfl⟩ : syracuseStep 12742055 = 19113083) B19113083
theorem B8494703 : Blo 2235435 8494703 := bstep (se 1 (by rfl) ⟨6371027, by rfl⟩ : syracuseStep 8494703 = 12742055) B12742055
theorem B5663135 : Blo 2235435 5663135 := bstep (se 1 (by rfl) ⟨4247351, by rfl⟩ : syracuseStep 5663135 = 8494703) B8494703
theorem B3775423 : Blo 2235435 3775423 := bstep (se 1 (by rfl) ⟨2831567, by rfl⟩ : syracuseStep 3775423 = 5663135) B5663135
theorem B5033897 : Blo 2235435 5033897 := bstep (se 2 (by rfl) ⟨1887711, by rfl⟩ : syracuseStep 5033897 = 3775423) B3775423
theorem B3355931 : Blo 2235435 3355931 := bstep (se 1 (by rfl) ⟨2516948, by rfl⟩ : syracuseStep 3355931 = 5033897) B5033897
theorem B2237287 : Blo 2235435 2237287 := bstep (se 1 (by rfl) ⟨1677965, by rfl⟩ : syracuseStep 2237287 = 3355931) B3355931
theorem B2516953 : Blo 2235435 2516953 := bbase (se 2 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 2516953 = 1887715) (by norm_num)
theorem B3355937 : Blo 2235435 3355937 := bstep (se 2 (by rfl) ⟨1258476, by rfl⟩ : syracuseStep 3355937 = 2516953) B2516953
theorem B2237291 : Blo 2235435 2237291 := bstep (se 1 (by rfl) ⟨1677968, by rfl⟩ : syracuseStep 2237291 = 3355937) B3355937
theorem B3185525 : Blo 2235435 3185525 := bbase (se 5 (by rfl) ⟨149321, by rfl⟩ : syracuseStep 3185525 = 298643) (by norm_num)
theorem B8494733 : Blo 2235435 8494733 := bstep (se 3 (by rfl) ⟨1592762, by rfl⟩ : syracuseStep 8494733 = 3185525) B3185525
theorem B5663155 : Blo 2235435 5663155 := bstep (se 1 (by rfl) ⟨4247366, by rfl⟩ : syracuseStep 5663155 = 8494733) B8494733
theorem B7550873 : Blo 2235435 7550873 := bstep (se 2 (by rfl) ⟨2831577, by rfl⟩ : syracuseStep 7550873 = 5663155) B5663155
theorem B5033915 : Blo 2235435 5033915 := bstep (se 1 (by rfl) ⟨3775436, by rfl⟩ : syracuseStep 5033915 = 7550873) B7550873
theorem B3355943 : Blo 2235435 3355943 := bstep (se 1 (by rfl) ⟨2516957, by rfl⟩ : syracuseStep 3355943 = 5033915) B5033915
theorem B2237295 : Blo 2235435 2237295 := bstep (se 1 (by rfl) ⟨1677971, by rfl⟩ : syracuseStep 2237295 = 3355943) B3355943
theorem B3355949 : Blo 2235435 3355949 := bbase (se 3 (by rfl) ⟨629240, by rfl⟩ : syracuseStep 3355949 = 1258481) (by norm_num)
theorem B2237299 : Blo 2235435 2237299 := bstep (se 1 (by rfl) ⟨1677974, by rfl⟩ : syracuseStep 2237299 = 3355949) B3355949
theorem B5033933 : Blo 2235435 5033933 := bbase (se 3 (by rfl) ⟨943862, by rfl⟩ : syracuseStep 5033933 = 1887725) (by norm_num)
theorem B3355955 : Blo 2235435 3355955 := bstep (se 1 (by rfl) ⟨2516966, by rfl⟩ : syracuseStep 3355955 = 5033933) B5033933
theorem B2237303 : Blo 2235435 2237303 := bstep (se 1 (by rfl) ⟨1677977, by rfl⟩ : syracuseStep 2237303 = 3355955) B3355955
theorem B2831593 : Blo 2235435 2831593 := bbase (se 2 (by rfl) ⟨1061847, by rfl⟩ : syracuseStep 2831593 = 2123695) (by norm_num)
theorem B3775457 : Blo 2235435 3775457 := bstep (se 2 (by rfl) ⟨1415796, by rfl⟩ : syracuseStep 3775457 = 2831593) B2831593
theorem B2516971 : Blo 2235435 2516971 := bstep (se 1 (by rfl) ⟨1887728, by rfl⟩ : syracuseStep 2516971 = 3775457) B3775457
theorem B3355961 : Blo 2235435 3355961 := bstep (se 2 (by rfl) ⟨1258485, by rfl⟩ : syracuseStep 3355961 = 2516971) B2516971
theorem B2237307 : Blo 2235435 2237307 := bstep (se 1 (by rfl) ⟨1677980, by rfl⟩ : syracuseStep 2237307 = 3355961) B3355961
theorem B14334965 : Blo 2235435 14334965 := bbase (se 5 (by rfl) ⟨671951, by rfl⟩ : syracuseStep 14334965 = 1343903) (by norm_num)
theorem B9556643 : Blo 2235435 9556643 := bstep (se 1 (by rfl) ⟨7167482, by rfl⟩ : syracuseStep 9556643 = 14334965) B14334965
theorem B25484381 : Blo 2235435 25484381 := bstep (se 3 (by rfl) ⟨4778321, by rfl⟩ : syracuseStep 25484381 = 9556643) B9556643
theorem B16989587 : Blo 2235435 16989587 := bstep (se 1 (by rfl) ⟨12742190, by rfl⟩ : syracuseStep 16989587 = 25484381) B25484381
theorem B11326391 : Blo 2235435 11326391 := bstep (se 1 (by rfl) ⟨8494793, by rfl⟩ : syracuseStep 11326391 = 16989587) B16989587
theorem B7550927 : Blo 2235435 7550927 := bstep (se 1 (by rfl) ⟨5663195, by rfl⟩ : syracuseStep 7550927 = 11326391) B11326391
theorem B5033951 : Blo 2235435 5033951 := bstep (se 1 (by rfl) ⟨3775463, by rfl⟩ : syracuseStep 5033951 = 7550927) B7550927
theorem B3355967 : Blo 2235435 3355967 := bstep (se 1 (by rfl) ⟨2516975, by rfl⟩ : syracuseStep 3355967 = 5033951) B5033951
theorem B2237311 : Blo 2235435 2237311 := bstep (se 1 (by rfl) ⟨1677983, by rfl⟩ : syracuseStep 2237311 = 3355967) B3355967
theorem B3355973 : Blo 2235435 3355973 := bbase (se 4 (by rfl) ⟨314622, by rfl⟩ : syracuseStep 3355973 = 629245) (by norm_num)
theorem B2237315 : Blo 2235435 2237315 := bstep (se 1 (by rfl) ⟨1677986, by rfl⟩ : syracuseStep 2237315 = 3355973) B3355973
theorem B3775477 : Blo 2235435 3775477 := bbase (se 5 (by rfl) ⟨176975, by rfl⟩ : syracuseStep 3775477 = 353951) (by norm_num)
theorem B5033969 : Blo 2235435 5033969 := bstep (se 2 (by rfl) ⟨1887738, by rfl⟩ : syracuseStep 5033969 = 3775477) B3775477
theorem B3355979 : Blo 2235435 3355979 := bstep (se 1 (by rfl) ⟨2516984, by rfl⟩ : syracuseStep 3355979 = 5033969) B5033969
theorem B2237319 : Blo 2235435 2237319 := bstep (se 1 (by rfl) ⟨1677989, by rfl⟩ : syracuseStep 2237319 = 3355979) B3355979
theorem B2516989 : Blo 2235435 2516989 := bbase (se 3 (by rfl) ⟨471935, by rfl⟩ : syracuseStep 2516989 = 943871) (by norm_num)
theorem B3355985 : Blo 2235435 3355985 := bstep (se 2 (by rfl) ⟨1258494, by rfl⟩ : syracuseStep 3355985 = 2516989) B2516989
theorem B2237323 : Blo 2235435 2237323 := bstep (se 1 (by rfl) ⟨1677992, by rfl⟩ : syracuseStep 2237323 = 3355985) B3355985
theorem B7550981 : Blo 2235435 7550981 := bbase (se 4 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 7550981 = 1415809) (by norm_num)
theorem B5033987 : Blo 2235435 5033987 := bstep (se 1 (by rfl) ⟨3775490, by rfl⟩ : syracuseStep 5033987 = 7550981) B7550981
theorem B3355991 : Blo 2235435 3355991 := bstep (se 1 (by rfl) ⟨2516993, by rfl⟩ : syracuseStep 3355991 = 5033987) B5033987
theorem B2237327 : Blo 2235435 2237327 := bstep (se 1 (by rfl) ⟨1677995, by rfl⟩ : syracuseStep 2237327 = 3355991) B3355991
theorem B3355997 : Blo 2235435 3355997 := bbase (se 3 (by rfl) ⟨629249, by rfl⟩ : syracuseStep 3355997 = 1258499) (by norm_num)
theorem B2237331 : Blo 2235435 2237331 := bstep (se 1 (by rfl) ⟨1677998, by rfl⟩ : syracuseStep 2237331 = 3355997) B3355997
theorem B5034005 : Blo 2235435 5034005 := bbase (se 6 (by rfl) ⟨117984, by rfl⟩ : syracuseStep 5034005 = 235969) (by norm_num)
theorem B3356003 : Blo 2235435 3356003 := bstep (se 1 (by rfl) ⟨2517002, by rfl⟩ : syracuseStep 3356003 = 5034005) B5034005
theorem B2237335 : Blo 2235435 2237335 := bstep (se 1 (by rfl) ⟨1678001, by rfl⟩ : syracuseStep 2237335 = 3356003) B3356003
theorem B8494901 : Blo 2235435 8494901 := bbase (se 5 (by rfl) ⟨398198, by rfl⟩ : syracuseStep 8494901 = 796397) (by norm_num)
theorem B5663267 : Blo 2235435 5663267 := bstep (se 1 (by rfl) ⟨4247450, by rfl⟩ : syracuseStep 5663267 = 8494901) B8494901
theorem B3775511 : Blo 2235435 3775511 := bstep (se 1 (by rfl) ⟨2831633, by rfl⟩ : syracuseStep 3775511 = 5663267) B5663267
theorem B2517007 : Blo 2235435 2517007 := bstep (se 1 (by rfl) ⟨1887755, by rfl⟩ : syracuseStep 2517007 = 3775511) B3775511
theorem B3356009 : Blo 2235435 3356009 := bstep (se 2 (by rfl) ⟨1258503, by rfl⟩ : syracuseStep 3356009 = 2517007) B2517007
theorem B2237339 : Blo 2235435 2237339 := bstep (se 1 (by rfl) ⟨1678004, by rfl⟩ : syracuseStep 2237339 = 3356009) B3356009
theorem B2687845 : Blo 2235435 2687845 := bbase (se 4 (by rfl) ⟨251985, by rfl⟩ : syracuseStep 2687845 = 503971) (by norm_num)
theorem B3583793 : Blo 2235435 3583793 := bstep (se 2 (by rfl) ⟨1343922, by rfl⟩ : syracuseStep 3583793 = 2687845) B2687845
theorem B2389195 : Blo 2235435 2389195 := bstep (se 1 (by rfl) ⟨1791896, by rfl⟩ : syracuseStep 2389195 = 3583793) B3583793
theorem B12742373 : Blo 2235435 12742373 := bstep (se 4 (by rfl) ⟨1194597, by rfl⟩ : syracuseStep 12742373 = 2389195) B2389195
theorem B8494915 : Blo 2235435 8494915 := bstep (se 1 (by rfl) ⟨6371186, by rfl⟩ : syracuseStep 8494915 = 12742373) B12742373
theorem B11326553 : Blo 2235435 11326553 := bstep (se 2 (by rfl) ⟨4247457, by rfl⟩ : syracuseStep 11326553 = 8494915) B8494915
theorem B7551035 : Blo 2235435 7551035 := bstep (se 1 (by rfl) ⟨5663276, by rfl⟩ : syracuseStep 7551035 = 11326553) B11326553
theorem B5034023 : Blo 2235435 5034023 := bstep (se 1 (by rfl) ⟨3775517, by rfl⟩ : syracuseStep 5034023 = 7551035) B7551035
theorem B3356015 : Blo 2235435 3356015 := bstep (se 1 (by rfl) ⟨2517011, by rfl⟩ : syracuseStep 3356015 = 5034023) B5034023
theorem B2237343 : Blo 2235435 2237343 := bstep (se 1 (by rfl) ⟨1678007, by rfl⟩ : syracuseStep 2237343 = 3356015) B3356015
theorem B3356021 : Blo 2235435 3356021 := bbase (se 5 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 3356021 = 314627) (by norm_num)
theorem B2237347 : Blo 2235435 2237347 := bstep (se 1 (by rfl) ⟨1678010, by rfl⟩ : syracuseStep 2237347 = 3356021) B3356021
theorem B3185605 : Blo 2235435 3185605 := bbase (se 4 (by rfl) ⟨298650, by rfl⟩ : syracuseStep 3185605 = 597301) (by norm_num)
theorem B4247473 : Blo 2235435 4247473 := bstep (se 2 (by rfl) ⟨1592802, by rfl⟩ : syracuseStep 4247473 = 3185605) B3185605
theorem B5663297 : Blo 2235435 5663297 := bstep (se 2 (by rfl) ⟨2123736, by rfl⟩ : syracuseStep 5663297 = 4247473) B4247473
theorem B3775531 : Blo 2235435 3775531 := bstep (se 1 (by rfl) ⟨2831648, by rfl⟩ : syracuseStep 3775531 = 5663297) B5663297
theorem B5034041 : Blo 2235435 5034041 := bstep (se 2 (by rfl) ⟨1887765, by rfl⟩ : syracuseStep 5034041 = 3775531) B3775531
theorem B3356027 : Blo 2235435 3356027 := bstep (se 1 (by rfl) ⟨2517020, by rfl⟩ : syracuseStep 3356027 = 5034041) B5034041
theorem B2237351 : Blo 2235435 2237351 := bstep (se 1 (by rfl) ⟨1678013, by rfl⟩ : syracuseStep 2237351 = 3356027) B3356027
theorem B2517025 : Blo 2235435 2517025 := bbase (se 2 (by rfl) ⟨943884, by rfl⟩ : syracuseStep 2517025 = 1887769) (by norm_num)
theorem B3356033 : Blo 2235435 3356033 := bstep (se 2 (by rfl) ⟨1258512, by rfl⟩ : syracuseStep 3356033 = 2517025) B2517025
theorem B2237355 : Blo 2235435 2237355 := bstep (se 1 (by rfl) ⟨1678016, by rfl⟩ : syracuseStep 2237355 = 3356033) B3356033
theorem B5663317 : Blo 2235435 5663317 := bbase (se 8 (by rfl) ⟨33183, by rfl⟩ : syracuseStep 5663317 = 66367) (by norm_num)
theorem B7551089 : Blo 2235435 7551089 := bstep (se 2 (by rfl) ⟨2831658, by rfl⟩ : syracuseStep 7551089 = 5663317) B5663317
theorem B5034059 : Blo 2235435 5034059 := bstep (se 1 (by rfl) ⟨3775544, by rfl⟩ : syracuseStep 5034059 = 7551089) B7551089
theorem B3356039 : Blo 2235435 3356039 := bstep (se 1 (by rfl) ⟨2517029, by rfl⟩ : syracuseStep 3356039 = 5034059) B5034059
theorem B2237359 : Blo 2235435 2237359 := bstep (se 1 (by rfl) ⟨1678019, by rfl⟩ : syracuseStep 2237359 = 3356039) B3356039
theorem B3356045 : Blo 2235435 3356045 := bbase (se 3 (by rfl) ⟨629258, by rfl⟩ : syracuseStep 3356045 = 1258517) (by norm_num)
theorem B2237363 : Blo 2235435 2237363 := bstep (se 1 (by rfl) ⟨1678022, by rfl⟩ : syracuseStep 2237363 = 3356045) B3356045
theorem B5034077 : Blo 2235435 5034077 := bbase (se 3 (by rfl) ⟨943889, by rfl⟩ : syracuseStep 5034077 = 1887779) (by norm_num)
theorem B3356051 : Blo 2235435 3356051 := bstep (se 1 (by rfl) ⟨2517038, by rfl⟩ : syracuseStep 3356051 = 5034077) B5034077
theorem B2237367 : Blo 2235435 2237367 := bstep (se 1 (by rfl) ⟨1678025, by rfl⟩ : syracuseStep 2237367 = 3356051) B3356051
theorem B3775565 : Blo 2235435 3775565 := bbase (se 3 (by rfl) ⟨707918, by rfl⟩ : syracuseStep 3775565 = 1415837) (by norm_num)
theorem B2517043 : Blo 2235435 2517043 := bstep (se 1 (by rfl) ⟨1887782, by rfl⟩ : syracuseStep 2517043 = 3775565) B3775565
theorem B3356057 : Blo 2235435 3356057 := bstep (se 2 (by rfl) ⟨1258521, by rfl⟩ : syracuseStep 3356057 = 2517043) B2517043
theorem B2237371 : Blo 2235435 2237371 := bstep (se 1 (by rfl) ⟨1678028, by rfl⟩ : syracuseStep 2237371 = 3356057) B3356057
theorem B9071605 : Blo 2235435 9071605 := bbase (se 5 (by rfl) ⟨425231, by rfl⟩ : syracuseStep 9071605 = 850463) (by norm_num)
theorem B48381893 : Blo 2235435 48381893 := bstep (se 4 (by rfl) ⟨4535802, by rfl⟩ : syracuseStep 48381893 = 9071605) B9071605
theorem B32254595 : Blo 2235435 32254595 := bstep (se 1 (by rfl) ⟨24190946, by rfl⟩ : syracuseStep 32254595 = 48381893) B48381893
theorem B21503063 : Blo 2235435 21503063 := bstep (se 1 (by rfl) ⟨16127297, by rfl⟩ : syracuseStep 21503063 = 32254595) B32254595
theorem B14335375 : Blo 2235435 14335375 := bstep (se 1 (by rfl) ⟨10751531, by rfl⟩ : syracuseStep 14335375 = 21503063) B21503063
theorem B19113833 : Blo 2235435 19113833 := bstep (se 2 (by rfl) ⟨7167687, by rfl⟩ : syracuseStep 19113833 = 14335375) B14335375
theorem B12742555 : Blo 2235435 12742555 := bstep (se 1 (by rfl) ⟨9556916, by rfl⟩ : syracuseStep 12742555 = 19113833) B19113833
theorem B16990073 : Blo 2235435 16990073 := bstep (se 2 (by rfl) ⟨6371277, by rfl⟩ : syracuseStep 16990073 = 12742555) B12742555
theorem B11326715 : Blo 2235435 11326715 := bstep (se 1 (by rfl) ⟨8495036, by rfl⟩ : syracuseStep 11326715 = 16990073) B16990073
theorem B7551143 : Blo 2235435 7551143 := bstep (se 1 (by rfl) ⟨5663357, by rfl⟩ : syracuseStep 7551143 = 11326715) B11326715
theorem B5034095 : Blo 2235435 5034095 := bstep (se 1 (by rfl) ⟨3775571, by rfl⟩ : syracuseStep 5034095 = 7551143) B7551143
theorem B3356063 : Blo 2235435 3356063 := bstep (se 1 (by rfl) ⟨2517047, by rfl⟩ : syracuseStep 3356063 = 5034095) B5034095
theorem B2237375 : Blo 2235435 2237375 := bstep (se 1 (by rfl) ⟨1678031, by rfl⟩ : syracuseStep 2237375 = 3356063) B3356063
theorem B3356069 : Blo 2235435 3356069 := bbase (se 4 (by rfl) ⟨314631, by rfl⟩ : syracuseStep 3356069 = 629263) (by norm_num)
theorem B2237379 : Blo 2235435 2237379 := bstep (se 1 (by rfl) ⟨1678034, by rfl⟩ : syracuseStep 2237379 = 3356069) B3356069
theorem B2831689 : Blo 2235435 2831689 := bbase (se 2 (by rfl) ⟨1061883, by rfl⟩ : syracuseStep 2831689 = 2123767) (by norm_num)
theorem B3775585 : Blo 2235435 3775585 := bstep (se 2 (by rfl) ⟨1415844, by rfl⟩ : syracuseStep 3775585 = 2831689) B2831689
theorem B5034113 : Blo 2235435 5034113 := bstep (se 2 (by rfl) ⟨1887792, by rfl⟩ : syracuseStep 5034113 = 3775585) B3775585
theorem B3356075 : Blo 2235435 3356075 := bstep (se 1 (by rfl) ⟨2517056, by rfl⟩ : syracuseStep 3356075 = 5034113) B5034113
theorem B2237383 : Blo 2235435 2237383 := bstep (se 1 (by rfl) ⟨1678037, by rfl⟩ : syracuseStep 2237383 = 3356075) B3356075
theorem B2517061 : Blo 2235435 2517061 := bbase (se 4 (by rfl) ⟨235974, by rfl⟩ : syracuseStep 2517061 = 471949) (by norm_num)
theorem B3356081 : Blo 2235435 3356081 := bstep (se 2 (by rfl) ⟨1258530, by rfl⟩ : syracuseStep 3356081 = 2517061) B2517061
theorem B2237387 : Blo 2235435 2237387 := bstep (se 1 (by rfl) ⟨1678040, by rfl⟩ : syracuseStep 2237387 = 3356081) B3356081
theorem B4247549 : Blo 2235435 4247549 := bbase (se 3 (by rfl) ⟨796415, by rfl⟩ : syracuseStep 4247549 = 1592831) (by norm_num)
theorem B2831699 : Blo 2235435 2831699 := bstep (se 1 (by rfl) ⟨2123774, by rfl⟩ : syracuseStep 2831699 = 4247549) B4247549
theorem B7551197 : Blo 2235435 7551197 := bstep (se 3 (by rfl) ⟨1415849, by rfl⟩ : syracuseStep 7551197 = 2831699) B2831699
theorem B5034131 : Blo 2235435 5034131 := bstep (se 1 (by rfl) ⟨3775598, by rfl⟩ : syracuseStep 5034131 = 7551197) B7551197
theorem B3356087 : Blo 2235435 3356087 := bstep (se 1 (by rfl) ⟨2517065, by rfl⟩ : syracuseStep 3356087 = 5034131) B5034131
theorem B2237391 : Blo 2235435 2237391 := bstep (se 1 (by rfl) ⟨1678043, by rfl⟩ : syracuseStep 2237391 = 3356087) B3356087
theorem B3356093 : Blo 2235435 3356093 := bbase (se 3 (by rfl) ⟨629267, by rfl⟩ : syracuseStep 3356093 = 1258535) (by norm_num)
theorem B2237395 : Blo 2235435 2237395 := bstep (se 1 (by rfl) ⟨1678046, by rfl⟩ : syracuseStep 2237395 = 3356093) B3356093
theorem B5034149 : Blo 2235435 5034149 := bbase (se 4 (by rfl) ⟨471951, by rfl⟩ : syracuseStep 5034149 = 943903) (by norm_num)
theorem B3356099 : Blo 2235435 3356099 := bstep (se 1 (by rfl) ⟨2517074, by rfl⟩ : syracuseStep 3356099 = 5034149) B5034149
theorem B2237399 : Blo 2235435 2237399 := bstep (se 1 (by rfl) ⟨1678049, by rfl⟩ : syracuseStep 2237399 = 3356099) B3356099
theorem B5663429 : Blo 2235435 5663429 := bbase (se 4 (by rfl) ⟨530946, by rfl⟩ : syracuseStep 5663429 = 1061893) (by norm_num)
theorem B3775619 : Blo 2235435 3775619 := bstep (se 1 (by rfl) ⟨2831714, by rfl⟩ : syracuseStep 3775619 = 5663429) B5663429
theorem B2517079 : Blo 2235435 2517079 := bstep (se 1 (by rfl) ⟨1887809, by rfl⟩ : syracuseStep 2517079 = 3775619) B3775619
theorem B3356105 : Blo 2235435 3356105 := bstep (se 2 (by rfl) ⟨1258539, by rfl⟩ : syracuseStep 3356105 = 2517079) B2517079
theorem B2237403 : Blo 2235435 2237403 := bstep (se 1 (by rfl) ⟨1678052, by rfl⟩ : syracuseStep 2237403 = 3356105) B3356105
theorem B13607605 : Blo 2235435 13607605 := bbase (se 5 (by rfl) ⟨637856, by rfl⟩ : syracuseStep 13607605 = 1275713) (by norm_num)
theorem B18143473 : Blo 2235435 18143473 := bstep (se 2 (by rfl) ⟨6803802, by rfl⟩ : syracuseStep 18143473 = 13607605) B13607605
theorem B24191297 : Blo 2235435 24191297 := bstep (se 2 (by rfl) ⟨9071736, by rfl⟩ : syracuseStep 24191297 = 18143473) B18143473
theorem B16127531 : Blo 2235435 16127531 := bstep (se 1 (by rfl) ⟨12095648, by rfl⟩ : syracuseStep 16127531 = 24191297) B24191297
theorem B10751687 : Blo 2235435 10751687 := bstep (se 1 (by rfl) ⟨8063765, by rfl⟩ : syracuseStep 10751687 = 16127531) B16127531
theorem B7167791 : Blo 2235435 7167791 := bstep (se 1 (by rfl) ⟨5375843, by rfl⟩ : syracuseStep 7167791 = 10751687) B10751687
theorem B4778527 : Blo 2235435 4778527 := bstep (se 1 (by rfl) ⟨3583895, by rfl⟩ : syracuseStep 4778527 = 7167791) B7167791
theorem B6371369 : Blo 2235435 6371369 := bstep (se 2 (by rfl) ⟨2389263, by rfl⟩ : syracuseStep 6371369 = 4778527) B4778527
theorem B4247579 : Blo 2235435 4247579 := bstep (se 1 (by rfl) ⟨3185684, by rfl⟩ : syracuseStep 4247579 = 6371369) B6371369
theorem B11326877 : Blo 2235435 11326877 := bstep (se 3 (by rfl) ⟨2123789, by rfl⟩ : syracuseStep 11326877 = 4247579) B4247579
theorem B7551251 : Blo 2235435 7551251 := bstep (se 1 (by rfl) ⟨5663438, by rfl⟩ : syracuseStep 7551251 = 11326877) B11326877
theorem B5034167 : Blo 2235435 5034167 := bstep (se 1 (by rfl) ⟨3775625, by rfl⟩ : syracuseStep 5034167 = 7551251) B7551251
theorem B3356111 : Blo 2235435 3356111 := bstep (se 1 (by rfl) ⟨2517083, by rfl⟩ : syracuseStep 3356111 = 5034167) B5034167
theorem B2237407 : Blo 2235435 2237407 := bstep (se 1 (by rfl) ⟨1678055, by rfl⟩ : syracuseStep 2237407 = 3356111) B3356111
theorem B3356117 : Blo 2235435 3356117 := bbase (se 7 (by rfl) ⟨39329, by rfl⟩ : syracuseStep 3356117 = 78659) (by norm_num)
theorem B2237411 : Blo 2235435 2237411 := bstep (se 1 (by rfl) ⟨1678058, by rfl⟩ : syracuseStep 2237411 = 3356117) B3356117
theorem B8495189 : Blo 2235435 8495189 := bbase (se 8 (by rfl) ⟨49776, by rfl⟩ : syracuseStep 8495189 = 99553) (by norm_num)
theorem B5663459 : Blo 2235435 5663459 := bstep (se 1 (by rfl) ⟨4247594, by rfl⟩ : syracuseStep 5663459 = 8495189) B8495189
theorem B3775639 : Blo 2235435 3775639 := bstep (se 1 (by rfl) ⟨2831729, by rfl⟩ : syracuseStep 3775639 = 5663459) B5663459
theorem B5034185 : Blo 2235435 5034185 := bstep (se 2 (by rfl) ⟨1887819, by rfl⟩ : syracuseStep 5034185 = 3775639) B3775639
theorem B3356123 : Blo 2235435 3356123 := bstep (se 1 (by rfl) ⟨2517092, by rfl⟩ : syracuseStep 3356123 = 5034185) B5034185
theorem B2237415 : Blo 2235435 2237415 := bstep (se 1 (by rfl) ⟨1678061, by rfl⟩ : syracuseStep 2237415 = 3356123) B3356123
theorem B2517097 : Blo 2235435 2517097 := bbase (se 2 (by rfl) ⟨943911, by rfl⟩ : syracuseStep 2517097 = 1887823) (by norm_num)
theorem B3356129 : Blo 2235435 3356129 := bstep (se 2 (by rfl) ⟨1258548, by rfl⟩ : syracuseStep 3356129 = 2517097) B2517097
theorem B2237419 : Blo 2235435 2237419 := bstep (se 1 (by rfl) ⟨1678064, by rfl⟩ : syracuseStep 2237419 = 3356129) B3356129
theorem B2687941 : Blo 2235435 2687941 := bbase (se 4 (by rfl) ⟨251994, by rfl⟩ : syracuseStep 2687941 = 503989) (by norm_num)
theorem B3583921 : Blo 2235435 3583921 := bstep (se 2 (by rfl) ⟨1343970, by rfl⟩ : syracuseStep 3583921 = 2687941) B2687941
theorem B4778561 : Blo 2235435 4778561 := bstep (se 2 (by rfl) ⟨1791960, by rfl⟩ : syracuseStep 4778561 = 3583921) B3583921
theorem B12742829 : Blo 2235435 12742829 := bstep (se 3 (by rfl) ⟨2389280, by rfl⟩ : syracuseStep 12742829 = 4778561) B4778561
theorem B8495219 : Blo 2235435 8495219 := bstep (se 1 (by rfl) ⟨6371414, by rfl⟩ : syracuseStep 8495219 = 12742829) B12742829
theorem B5663479 : Blo 2235435 5663479 := bstep (se 1 (by rfl) ⟨4247609, by rfl⟩ : syracuseStep 5663479 = 8495219) B8495219
theorem B7551305 : Blo 2235435 7551305 := bstep (se 2 (by rfl) ⟨2831739, by rfl⟩ : syracuseStep 7551305 = 5663479) B5663479
theorem B5034203 : Blo 2235435 5034203 := bstep (se 1 (by rfl) ⟨3775652, by rfl⟩ : syracuseStep 5034203 = 7551305) B7551305
theorem B3356135 : Blo 2235435 3356135 := bstep (se 1 (by rfl) ⟨2517101, by rfl⟩ : syracuseStep 3356135 = 5034203) B5034203
theorem B2237423 : Blo 2235435 2237423 := bstep (se 1 (by rfl) ⟨1678067, by rfl⟩ : syracuseStep 2237423 = 3356135) B3356135
theorem B3356141 : Blo 2235435 3356141 := bbase (se 3 (by rfl) ⟨629276, by rfl⟩ : syracuseStep 3356141 = 1258553) (by norm_num)
theorem B2237427 : Blo 2235435 2237427 := bstep (se 1 (by rfl) ⟨1678070, by rfl⟩ : syracuseStep 2237427 = 3356141) B3356141
theorem B5034221 : Blo 2235435 5034221 := bbase (se 3 (by rfl) ⟨943916, by rfl⟩ : syracuseStep 5034221 = 1887833) (by norm_num)
theorem B3356147 : Blo 2235435 3356147 := bstep (se 1 (by rfl) ⟨2517110, by rfl⟩ : syracuseStep 3356147 = 5034221) B5034221
theorem B2237431 : Blo 2235435 2237431 := bstep (se 1 (by rfl) ⟨1678073, by rfl⟩ : syracuseStep 2237431 = 3356147) B3356147
theorem B3185725 : Blo 2235435 3185725 := bbase (se 3 (by rfl) ⟨597323, by rfl⟩ : syracuseStep 3185725 = 1194647) (by norm_num)
theorem B4247633 : Blo 2235435 4247633 := bstep (se 2 (by rfl) ⟨1592862, by rfl⟩ : syracuseStep 4247633 = 3185725) B3185725
theorem B2831755 : Blo 2235435 2831755 := bstep (se 1 (by rfl) ⟨2123816, by rfl⟩ : syracuseStep 2831755 = 4247633) B4247633
theorem B3775673 : Blo 2235435 3775673 := bstep (se 2 (by rfl) ⟨1415877, by rfl⟩ : syracuseStep 3775673 = 2831755) B2831755
theorem B2517115 : Blo 2235435 2517115 := bstep (se 1 (by rfl) ⟨1887836, by rfl⟩ : syracuseStep 2517115 = 3775673) B3775673
theorem B3356153 : Blo 2235435 3356153 := bstep (se 2 (by rfl) ⟨1258557, by rfl⟩ : syracuseStep 3356153 = 2517115) B2517115
theorem B2237435 : Blo 2235435 2237435 := bstep (se 1 (by rfl) ⟨1678076, by rfl⟩ : syracuseStep 2237435 = 3356153) B3356153
theorem C0 (j : ℕ) (h1 : 558858 ≤ j) (h2 : j ≤ 559358) : Blo 2235435 (4 * j + 3) := by
  interval_cases j
  · exact B2235435
  · exact B2235439
  · exact B2235443
  · exact B2235447
  · exact B2235451
  · exact B2235455
  · exact B2235459
  · exact B2235463
  · exact B2235467
  · exact B2235471
  · exact B2235475
  · exact B2235479
  · exact B2235483
  · exact B2235487
  · exact B2235491
  · exact B2235495
  · exact B2235499
  · exact B2235503
  · exact B2235507
  · exact B2235511
  · exact B2235515
  · exact B2235519
  · exact B2235523
  · exact B2235527
  · exact B2235531
  · exact B2235535
  · exact B2235539
  · exact B2235543
  · exact B2235547
  · exact B2235551
  · exact B2235555
  · exact B2235559
  · exact B2235563
  · exact B2235567
  · exact B2235571
  · exact B2235575
  · exact B2235579
  · exact B2235583
  · exact B2235587
  · exact B2235591
  · exact B2235595
  · exact B2235599
  · exact B2235603
  · exact B2235607
  · exact B2235611
  · exact B2235615
  · exact B2235619
  · exact B2235623
  · exact B2235627
  · exact B2235631
  · exact B2235635
  · exact B2235639
  · exact B2235643
  · exact B2235647
  · exact B2235651
  · exact B2235655
  · exact B2235659
  · exact B2235663
  · exact B2235667
  · exact B2235671
  · exact B2235675
  · exact B2235679
  · exact B2235683
  · exact B2235687
  · exact B2235691
  · exact B2235695
  · exact B2235699
  · exact B2235703
  · exact B2235707
  · exact B2235711
  · exact B2235715
  · exact B2235719
  · exact B2235723
  · exact B2235727
  · exact B2235731
  · exact B2235735
  · exact B2235739
  · exact B2235743
  · exact B2235747
  · exact B2235751
  · exact B2235755
  · exact B2235759
  · exact B2235763
  · exact B2235767
  · exact B2235771
  · exact B2235775
  · exact B2235779
  · exact B2235783
  · exact B2235787
  · exact B2235791
  · exact B2235795
  · exact B2235799
  · exact B2235803
  · exact B2235807
  · exact B2235811
  · exact B2235815
  · exact B2235819
  · exact B2235823
  · exact B2235827
  · exact B2235831
  · exact B2235835
  · exact B2235839
  · exact B2235843
  · exact B2235847
  · exact B2235851
  · exact B2235855
  · exact B2235859
  · exact B2235863
  · exact B2235867
  · exact B2235871
  · exact B2235875
  · exact B2235879
  · exact B2235883
  · exact B2235887
  · exact B2235891
  · exact B2235895
  · exact B2235899
  · exact B2235903
  · exact B2235907
  · exact B2235911
  · exact B2235915
  · exact B2235919
  · exact B2235923
  · exact B2235927
  · exact B2235931
  · exact B2235935
  · exact B2235939
  · exact B2235943
  · exact B2235947
  · exact B2235951
  · exact B2235955
  · exact B2235959
  · exact B2235963
  · exact B2235967
  · exact B2235971
  · exact B2235975
  · exact B2235979
  · exact B2235983
  · exact B2235987
  · exact B2235991
  · exact B2235995
  · exact B2235999
  · exact B2236003
  · exact B2236007
  · exact B2236011
  · exact B2236015
  · exact B2236019
  · exact B2236023
  · exact B2236027
  · exact B2236031
  · exact B2236035
  · exact B2236039
  · exact B2236043
  · exact B2236047
  · exact B2236051
  · exact B2236055
  · exact B2236059
  · exact B2236063
  · exact B2236067
  · exact B2236071
  · exact B2236075
  · exact B2236079
  · exact B2236083
  · exact B2236087
  · exact B2236091
  · exact B2236095
  · exact B2236099
  · exact B2236103
  · exact B2236107
  · exact B2236111
  · exact B2236115
  · exact B2236119
  · exact B2236123
  · exact B2236127
  · exact B2236131
  · exact B2236135
  · exact B2236139
  · exact B2236143
  · exact B2236147
  · exact B2236151
  · exact B2236155
  · exact B2236159
  · exact B2236163
  · exact B2236167
  · exact B2236171
  · exact B2236175
  · exact B2236179
  · exact B2236183
  · exact B2236187
  · exact B2236191
  · exact B2236195
  · exact B2236199
  · exact B2236203
  · exact B2236207
  · exact B2236211
  · exact B2236215
  · exact B2236219
  · exact B2236223
  · exact B2236227
  · exact B2236231
  · exact B2236235
  · exact B2236239
  · exact B2236243
  · exact B2236247
  · exact B2236251
  · exact B2236255
  · exact B2236259
  · exact B2236263
  · exact B2236267
  · exact B2236271
  · exact B2236275
  · exact B2236279
  · exact B2236283
  · exact B2236287
  · exact B2236291
  · exact B2236295
  · exact B2236299
  · exact B2236303
  · exact B2236307
  · exact B2236311
  · exact B2236315
  · exact B2236319
  · exact B2236323
  · exact B2236327
  · exact B2236331
  · exact B2236335
  · exact B2236339
  · exact B2236343
  · exact B2236347
  · exact B2236351
  · exact B2236355
  · exact B2236359
  · exact B2236363
  · exact B2236367
  · exact B2236371
  · exact B2236375
  · exact B2236379
  · exact B2236383
  · exact B2236387
  · exact B2236391
  · exact B2236395
  · exact B2236399
  · exact B2236403
  · exact B2236407
  · exact B2236411
  · exact B2236415
  · exact B2236419
  · exact B2236423
  · exact B2236427
  · exact B2236431
  · exact B2236435
  · exact B2236439
  · exact B2236443
  · exact B2236447
  · exact B2236451
  · exact B2236455
  · exact B2236459
  · exact B2236463
  · exact B2236467
  · exact B2236471
  · exact B2236475
  · exact B2236479
  · exact B2236483
  · exact B2236487
  · exact B2236491
  · exact B2236495
  · exact B2236499
  · exact B2236503
  · exact B2236507
  · exact B2236511
  · exact B2236515
  · exact B2236519
  · exact B2236523
  · exact B2236527
  · exact B2236531
  · exact B2236535
  · exact B2236539
  · exact B2236543
  · exact B2236547
  · exact B2236551
  · exact B2236555
  · exact B2236559
  · exact B2236563
  · exact B2236567
  · exact B2236571
  · exact B2236575
  · exact B2236579
  · exact B2236583
  · exact B2236587
  · exact B2236591
  · exact B2236595
  · exact B2236599
  · exact B2236603
  · exact B2236607
  · exact B2236611
  · exact B2236615
  · exact B2236619
  · exact B2236623
  · exact B2236627
  · exact B2236631
  · exact B2236635
  · exact B2236639
  · exact B2236643
  · exact B2236647
  · exact B2236651
  · exact B2236655
  · exact B2236659
  · exact B2236663
  · exact B2236667
  · exact B2236671
  · exact B2236675
  · exact B2236679
  · exact B2236683
  · exact B2236687
  · exact B2236691
  · exact B2236695
  · exact B2236699
  · exact B2236703
  · exact B2236707
  · exact B2236711
  · exact B2236715
  · exact B2236719
  · exact B2236723
  · exact B2236727
  · exact B2236731
  · exact B2236735
  · exact B2236739
  · exact B2236743
  · exact B2236747
  · exact B2236751
  · exact B2236755
  · exact B2236759
  · exact B2236763
  · exact B2236767
  · exact B2236771
  · exact B2236775
  · exact B2236779
  · exact B2236783
  · exact B2236787
  · exact B2236791
  · exact B2236795
  · exact B2236799
  · exact B2236803
  · exact B2236807
  · exact B2236811
  · exact B2236815
  · exact B2236819
  · exact B2236823
  · exact B2236827
  · exact B2236831
  · exact B2236835
  · exact B2236839
  · exact B2236843
  · exact B2236847
  · exact B2236851
  · exact B2236855
  · exact B2236859
  · exact B2236863
  · exact B2236867
  · exact B2236871
  · exact B2236875
  · exact B2236879
  · exact B2236883
  · exact B2236887
  · exact B2236891
  · exact B2236895
  · exact B2236899
  · exact B2236903
  · exact B2236907
  · exact B2236911
  · exact B2236915
  · exact B2236919
  · exact B2236923
  · exact B2236927
  · exact B2236931
  · exact B2236935
  · exact B2236939
  · exact B2236943
  · exact B2236947
  · exact B2236951
  · exact B2236955
  · exact B2236959
  · exact B2236963
  · exact B2236967
  · exact B2236971
  · exact B2236975
  · exact B2236979
  · exact B2236983
  · exact B2236987
  · exact B2236991
  · exact B2236995
  · exact B2236999
  · exact B2237003
  · exact B2237007
  · exact B2237011
  · exact B2237015
  · exact B2237019
  · exact B2237023
  · exact B2237027
  · exact B2237031
  · exact B2237035
  · exact B2237039
  · exact B2237043
  · exact B2237047
  · exact B2237051
  · exact B2237055
  · exact B2237059
  · exact B2237063
  · exact B2237067
  · exact B2237071
  · exact B2237075
  · exact B2237079
  · exact B2237083
  · exact B2237087
  · exact B2237091
  · exact B2237095
  · exact B2237099
  · exact B2237103
  · exact B2237107
  · exact B2237111
  · exact B2237115
  · exact B2237119
  · exact B2237123
  · exact B2237127
  · exact B2237131
  · exact B2237135
  · exact B2237139
  · exact B2237143
  · exact B2237147
  · exact B2237151
  · exact B2237155
  · exact B2237159
  · exact B2237163
  · exact B2237167
  · exact B2237171
  · exact B2237175
  · exact B2237179
  · exact B2237183
  · exact B2237187
  · exact B2237191
  · exact B2237195
  · exact B2237199
  · exact B2237203
  · exact B2237207
  · exact B2237211
  · exact B2237215
  · exact B2237219
  · exact B2237223
  · exact B2237227
  · exact B2237231
  · exact B2237235
  · exact B2237239
  · exact B2237243
  · exact B2237247
  · exact B2237251
  · exact B2237255
  · exact B2237259
  · exact B2237263
  · exact B2237267
  · exact B2237271
  · exact B2237275
  · exact B2237279
  · exact B2237283
  · exact B2237287
  · exact B2237291
  · exact B2237295
  · exact B2237299
  · exact B2237303
  · exact B2237307
  · exact B2237311
  · exact B2237315
  · exact B2237319
  · exact B2237323
  · exact B2237327
  · exact B2237331
  · exact B2237335
  · exact B2237339
  · exact B2237343
  · exact B2237347
  · exact B2237351
  · exact B2237355
  · exact B2237359
  · exact B2237363
  · exact B2237367
  · exact B2237371
  · exact B2237375
  · exact B2237379
  · exact B2237383
  · exact B2237387
  · exact B2237391
  · exact B2237395
  · exact B2237399
  · exact B2237403
  · exact B2237407
  · exact B2237411
  · exact B2237415
  · exact B2237419
  · exact B2237423
  · exact B2237427
  · exact B2237431
  · exact B2237435
theorem solution (m : ℕ) (hlo : 2235435 ≤ m) (hhi : m ≤ 2237435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 558858 ≤ j := by omega
    have hj2 : j ≤ 559358 := by omega
    have hb : Blo 2235435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
