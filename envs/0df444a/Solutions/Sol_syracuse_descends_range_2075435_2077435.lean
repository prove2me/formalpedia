-- Prove2me | solution 1 for syracuse_descends_range_2075435_2077435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:10.74938+00:00
-- url     : https://prove2.me/submissions/fc84ceeb-3459-4d68-bdd4-f64631923db7

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

theorem B2334865 : Blo 2075435 2334865 := bbase (se 2 (by rfl) ⟨875574, by rfl⟩ : syracuseStep 2334865 = 1751149) (by norm_num)
theorem B3113153 : Blo 2075435 3113153 := bstep (se 2 (by rfl) ⟨1167432, by rfl⟩ : syracuseStep 3113153 = 2334865) B2334865
theorem B2075435 : Blo 2075435 2075435 := bstep (se 1 (by rfl) ⟨1556576, by rfl⟩ : syracuseStep 2075435 = 3113153) B3113153
theorem B3940093 : Blo 2075435 3940093 := bbase (se 3 (by rfl) ⟨738767, by rfl⟩ : syracuseStep 3940093 = 1477535) (by norm_num)
theorem B5253457 : Blo 2075435 5253457 := bstep (se 2 (by rfl) ⟨1970046, by rfl⟩ : syracuseStep 5253457 = 3940093) B3940093
theorem B7004609 : Blo 2075435 7004609 := bstep (se 2 (by rfl) ⟨2626728, by rfl⟩ : syracuseStep 7004609 = 5253457) B5253457
theorem B4669739 : Blo 2075435 4669739 := bstep (se 1 (by rfl) ⟨3502304, by rfl⟩ : syracuseStep 4669739 = 7004609) B7004609
theorem B3113159 : Blo 2075435 3113159 := bstep (se 1 (by rfl) ⟨2334869, by rfl⟩ : syracuseStep 3113159 = 4669739) B4669739
theorem B2075439 : Blo 2075435 2075439 := bstep (se 1 (by rfl) ⟨1556579, by rfl⟩ : syracuseStep 2075439 = 3113159) B3113159
theorem B3113165 : Blo 2075435 3113165 := bbase (se 3 (by rfl) ⟨583718, by rfl⟩ : syracuseStep 3113165 = 1167437) (by norm_num)
theorem B2075443 : Blo 2075435 2075443 := bstep (se 1 (by rfl) ⟨1556582, by rfl⟩ : syracuseStep 2075443 = 3113165) B3113165
theorem B4669757 : Blo 2075435 4669757 := bbase (se 3 (by rfl) ⟨875579, by rfl⟩ : syracuseStep 4669757 = 1751159) (by norm_num)
theorem B3113171 : Blo 2075435 3113171 := bstep (se 1 (by rfl) ⟨2334878, by rfl⟩ : syracuseStep 3113171 = 4669757) B4669757
theorem B2075447 : Blo 2075435 2075447 := bstep (se 1 (by rfl) ⟨1556585, by rfl⟩ : syracuseStep 2075447 = 3113171) B3113171
theorem B3502325 : Blo 2075435 3502325 := bbase (se 5 (by rfl) ⟨164171, by rfl⟩ : syracuseStep 3502325 = 328343) (by norm_num)
theorem B2334883 : Blo 2075435 2334883 := bstep (se 1 (by rfl) ⟨1751162, by rfl⟩ : syracuseStep 2334883 = 3502325) B3502325
theorem B3113177 : Blo 2075435 3113177 := bstep (se 2 (by rfl) ⟨1167441, by rfl⟩ : syracuseStep 3113177 = 2334883) B2334883
theorem B2075451 : Blo 2075435 2075451 := bstep (se 1 (by rfl) ⟨1556588, by rfl⟩ : syracuseStep 2075451 = 3113177) B3113177
theorem B5990821 : Blo 2075435 5990821 := bbase (se 4 (by rfl) ⟨561639, by rfl⟩ : syracuseStep 5990821 = 1123279) (by norm_num)
theorem B31951045 : Blo 2075435 31951045 := bstep (se 4 (by rfl) ⟨2995410, by rfl⟩ : syracuseStep 31951045 = 5990821) B5990821
theorem B42601393 : Blo 2075435 42601393 := bstep (se 2 (by rfl) ⟨15975522, by rfl⟩ : syracuseStep 42601393 = 31951045) B31951045
theorem B56801857 : Blo 2075435 56801857 := bstep (se 2 (by rfl) ⟨21300696, by rfl⟩ : syracuseStep 56801857 = 42601393) B42601393
theorem B75735809 : Blo 2075435 75735809 := bstep (se 2 (by rfl) ⟨28400928, by rfl⟩ : syracuseStep 75735809 = 56801857) B56801857
theorem B50490539 : Blo 2075435 50490539 := bstep (se 1 (by rfl) ⟨37867904, by rfl⟩ : syracuseStep 50490539 = 75735809) B75735809
theorem B33660359 : Blo 2075435 33660359 := bstep (se 1 (by rfl) ⟨25245269, by rfl⟩ : syracuseStep 33660359 = 50490539) B50490539
theorem B22440239 : Blo 2075435 22440239 := bstep (se 1 (by rfl) ⟨16830179, by rfl⟩ : syracuseStep 22440239 = 33660359) B33660359
theorem B14960159 : Blo 2075435 14960159 := bstep (se 1 (by rfl) ⟨11220119, by rfl⟩ : syracuseStep 14960159 = 22440239) B22440239
theorem B9973439 : Blo 2075435 9973439 := bstep (se 1 (by rfl) ⟨7480079, by rfl⟩ : syracuseStep 9973439 = 14960159) B14960159
theorem B6648959 : Blo 2075435 6648959 := bstep (se 1 (by rfl) ⟨4986719, by rfl⟩ : syracuseStep 6648959 = 9973439) B9973439
theorem B4432639 : Blo 2075435 4432639 := bstep (se 1 (by rfl) ⟨3324479, by rfl⟩ : syracuseStep 4432639 = 6648959) B6648959
theorem B5910185 : Blo 2075435 5910185 := bstep (se 2 (by rfl) ⟨2216319, by rfl⟩ : syracuseStep 5910185 = 4432639) B4432639
theorem B15760493 : Blo 2075435 15760493 := bstep (se 3 (by rfl) ⟨2955092, by rfl⟩ : syracuseStep 15760493 = 5910185) B5910185
theorem B10506995 : Blo 2075435 10506995 := bstep (se 1 (by rfl) ⟨7880246, by rfl⟩ : syracuseStep 10506995 = 15760493) B15760493
theorem B7004663 : Blo 2075435 7004663 := bstep (se 1 (by rfl) ⟨5253497, by rfl⟩ : syracuseStep 7004663 = 10506995) B10506995
theorem B4669775 : Blo 2075435 4669775 := bstep (se 1 (by rfl) ⟨3502331, by rfl⟩ : syracuseStep 4669775 = 7004663) B7004663
theorem B3113183 : Blo 2075435 3113183 := bstep (se 1 (by rfl) ⟨2334887, by rfl⟩ : syracuseStep 3113183 = 4669775) B4669775
theorem B2075455 : Blo 2075435 2075455 := bstep (se 1 (by rfl) ⟨1556591, by rfl⟩ : syracuseStep 2075455 = 3113183) B3113183
theorem B3113189 : Blo 2075435 3113189 := bbase (se 4 (by rfl) ⟨291861, by rfl⟩ : syracuseStep 3113189 = 583723) (by norm_num)
theorem B2075459 : Blo 2075435 2075459 := bstep (se 1 (by rfl) ⟨1556594, by rfl⟩ : syracuseStep 2075459 = 3113189) B3113189
theorem B3324493 : Blo 2075435 3324493 := bbase (se 3 (by rfl) ⟨623342, by rfl⟩ : syracuseStep 3324493 = 1246685) (by norm_num)
theorem B4432657 : Blo 2075435 4432657 := bstep (se 2 (by rfl) ⟨1662246, by rfl⟩ : syracuseStep 4432657 = 3324493) B3324493
theorem B5910209 : Blo 2075435 5910209 := bstep (se 2 (by rfl) ⟨2216328, by rfl⟩ : syracuseStep 5910209 = 4432657) B4432657
theorem B3940139 : Blo 2075435 3940139 := bstep (se 1 (by rfl) ⟨2955104, by rfl⟩ : syracuseStep 3940139 = 5910209) B5910209
theorem B2626759 : Blo 2075435 2626759 := bstep (se 1 (by rfl) ⟨1970069, by rfl⟩ : syracuseStep 2626759 = 3940139) B3940139
theorem B3502345 : Blo 2075435 3502345 := bstep (se 2 (by rfl) ⟨1313379, by rfl⟩ : syracuseStep 3502345 = 2626759) B2626759
theorem B4669793 : Blo 2075435 4669793 := bstep (se 2 (by rfl) ⟨1751172, by rfl⟩ : syracuseStep 4669793 = 3502345) B3502345
theorem B3113195 : Blo 2075435 3113195 := bstep (se 1 (by rfl) ⟨2334896, by rfl⟩ : syracuseStep 3113195 = 4669793) B4669793
theorem B2075463 : Blo 2075435 2075463 := bstep (se 1 (by rfl) ⟨1556597, by rfl⟩ : syracuseStep 2075463 = 3113195) B3113195
theorem B2334901 : Blo 2075435 2334901 := bbase (se 5 (by rfl) ⟨109448, by rfl⟩ : syracuseStep 2334901 = 218897) (by norm_num)
theorem B3113201 : Blo 2075435 3113201 := bstep (se 2 (by rfl) ⟨1167450, by rfl⟩ : syracuseStep 3113201 = 2334901) B2334901
theorem B2075467 : Blo 2075435 2075467 := bstep (se 1 (by rfl) ⟨1556600, by rfl⟩ : syracuseStep 2075467 = 3113201) B3113201
theorem B2626769 : Blo 2075435 2626769 := bbase (se 2 (by rfl) ⟨985038, by rfl⟩ : syracuseStep 2626769 = 1970077) (by norm_num)
theorem B7004717 : Blo 2075435 7004717 := bstep (se 3 (by rfl) ⟨1313384, by rfl⟩ : syracuseStep 7004717 = 2626769) B2626769
theorem B4669811 : Blo 2075435 4669811 := bstep (se 1 (by rfl) ⟨3502358, by rfl⟩ : syracuseStep 4669811 = 7004717) B7004717
theorem B3113207 : Blo 2075435 3113207 := bstep (se 1 (by rfl) ⟨2334905, by rfl⟩ : syracuseStep 3113207 = 4669811) B4669811
theorem B2075471 : Blo 2075435 2075471 := bstep (se 1 (by rfl) ⟨1556603, by rfl⟩ : syracuseStep 2075471 = 3113207) B3113207
theorem B3113213 : Blo 2075435 3113213 := bbase (se 3 (by rfl) ⟨583727, by rfl⟩ : syracuseStep 3113213 = 1167455) (by norm_num)
theorem B2075475 : Blo 2075435 2075475 := bstep (se 1 (by rfl) ⟨1556606, by rfl⟩ : syracuseStep 2075475 = 3113213) B3113213
theorem B4669829 : Blo 2075435 4669829 := bbase (se 4 (by rfl) ⟨437796, by rfl⟩ : syracuseStep 4669829 = 875593) (by norm_num)
theorem B3113219 : Blo 2075435 3113219 := bstep (se 1 (by rfl) ⟨2334914, by rfl⟩ : syracuseStep 3113219 = 4669829) B4669829
theorem B2075479 : Blo 2075435 2075479 := bstep (se 1 (by rfl) ⟨1556609, by rfl⟩ : syracuseStep 2075479 = 3113219) B3113219
theorem B2955133 : Blo 2075435 2955133 := bbase (se 3 (by rfl) ⟨554087, by rfl⟩ : syracuseStep 2955133 = 1108175) (by norm_num)
theorem B3940177 : Blo 2075435 3940177 := bstep (se 2 (by rfl) ⟨1477566, by rfl⟩ : syracuseStep 3940177 = 2955133) B2955133
theorem B5253569 : Blo 2075435 5253569 := bstep (se 2 (by rfl) ⟨1970088, by rfl⟩ : syracuseStep 5253569 = 3940177) B3940177
theorem B3502379 : Blo 2075435 3502379 := bstep (se 1 (by rfl) ⟨2626784, by rfl⟩ : syracuseStep 3502379 = 5253569) B5253569
theorem B2334919 : Blo 2075435 2334919 := bstep (se 1 (by rfl) ⟨1751189, by rfl⟩ : syracuseStep 2334919 = 3502379) B3502379
theorem B3113225 : Blo 2075435 3113225 := bstep (se 2 (by rfl) ⟨1167459, by rfl⟩ : syracuseStep 3113225 = 2334919) B2334919
theorem B2075483 : Blo 2075435 2075483 := bstep (se 1 (by rfl) ⟨1556612, by rfl⟩ : syracuseStep 2075483 = 3113225) B3113225
theorem B10507157 : Blo 2075435 10507157 := bbase (se 6 (by rfl) ⟨246261, by rfl⟩ : syracuseStep 10507157 = 492523) (by norm_num)
theorem B7004771 : Blo 2075435 7004771 := bstep (se 1 (by rfl) ⟨5253578, by rfl⟩ : syracuseStep 7004771 = 10507157) B10507157
theorem B4669847 : Blo 2075435 4669847 := bstep (se 1 (by rfl) ⟨3502385, by rfl⟩ : syracuseStep 4669847 = 7004771) B7004771
theorem B3113231 : Blo 2075435 3113231 := bstep (se 1 (by rfl) ⟨2334923, by rfl⟩ : syracuseStep 3113231 = 4669847) B4669847
theorem B2075487 : Blo 2075435 2075487 := bstep (se 1 (by rfl) ⟨1556615, by rfl⟩ : syracuseStep 2075487 = 3113231) B3113231
theorem B3113237 : Blo 2075435 3113237 := bbase (se 6 (by rfl) ⟨72966, by rfl⟩ : syracuseStep 3113237 = 145933) (by norm_num)
theorem B2075491 : Blo 2075435 2075491 := bstep (se 1 (by rfl) ⟨1556618, by rfl⟩ : syracuseStep 2075491 = 3113237) B3113237
theorem B8986405 : Blo 2075435 8986405 := bbase (se 4 (by rfl) ⟨842475, by rfl⟩ : syracuseStep 8986405 = 1684951) (by norm_num)
theorem B11981873 : Blo 2075435 11981873 := bstep (se 2 (by rfl) ⟨4493202, by rfl⟩ : syracuseStep 11981873 = 8986405) B8986405
theorem B7987915 : Blo 2075435 7987915 := bstep (se 1 (by rfl) ⟨5990936, by rfl⟩ : syracuseStep 7987915 = 11981873) B11981873
theorem B42602213 : Blo 2075435 42602213 := bstep (se 4 (by rfl) ⟨3993957, by rfl⟩ : syracuseStep 42602213 = 7987915) B7987915
theorem B113605901 : Blo 2075435 113605901 := bstep (se 3 (by rfl) ⟨21301106, by rfl⟩ : syracuseStep 113605901 = 42602213) B42602213
theorem B75737267 : Blo 2075435 75737267 := bstep (se 1 (by rfl) ⟨56802950, by rfl⟩ : syracuseStep 75737267 = 113605901) B113605901
theorem B50491511 : Blo 2075435 50491511 := bstep (se 1 (by rfl) ⟨37868633, by rfl⟩ : syracuseStep 50491511 = 75737267) B75737267
theorem B33661007 : Blo 2075435 33661007 := bstep (se 1 (by rfl) ⟨25245755, by rfl⟩ : syracuseStep 33661007 = 50491511) B50491511
theorem B22440671 : Blo 2075435 22440671 := bstep (se 1 (by rfl) ⟨16830503, by rfl⟩ : syracuseStep 22440671 = 33661007) B33661007
theorem B14960447 : Blo 2075435 14960447 := bstep (se 1 (by rfl) ⟨11220335, by rfl⟩ : syracuseStep 14960447 = 22440671) B22440671
theorem B9973631 : Blo 2075435 9973631 := bstep (se 1 (by rfl) ⟨7480223, by rfl⟩ : syracuseStep 9973631 = 14960447) B14960447
theorem B26596349 : Blo 2075435 26596349 := bstep (se 3 (by rfl) ⟨4986815, by rfl⟩ : syracuseStep 26596349 = 9973631) B9973631
theorem B17730899 : Blo 2075435 17730899 := bstep (se 1 (by rfl) ⟨13298174, by rfl⟩ : syracuseStep 17730899 = 26596349) B26596349
theorem B11820599 : Blo 2075435 11820599 := bstep (se 1 (by rfl) ⟨8865449, by rfl⟩ : syracuseStep 11820599 = 17730899) B17730899
theorem B7880399 : Blo 2075435 7880399 := bstep (se 1 (by rfl) ⟨5910299, by rfl⟩ : syracuseStep 7880399 = 11820599) B11820599
theorem B5253599 : Blo 2075435 5253599 := bstep (se 1 (by rfl) ⟨3940199, by rfl⟩ : syracuseStep 5253599 = 7880399) B7880399
theorem B3502399 : Blo 2075435 3502399 := bstep (se 1 (by rfl) ⟨2626799, by rfl⟩ : syracuseStep 3502399 = 5253599) B5253599
theorem B4669865 : Blo 2075435 4669865 := bstep (se 2 (by rfl) ⟨1751199, by rfl⟩ : syracuseStep 4669865 = 3502399) B3502399
theorem B3113243 : Blo 2075435 3113243 := bstep (se 1 (by rfl) ⟨2334932, by rfl⟩ : syracuseStep 3113243 = 4669865) B4669865
theorem B2075495 : Blo 2075435 2075495 := bstep (se 1 (by rfl) ⟨1556621, by rfl⟩ : syracuseStep 2075495 = 3113243) B3113243
theorem B2334937 : Blo 2075435 2334937 := bbase (se 2 (by rfl) ⟨875601, by rfl⟩ : syracuseStep 2334937 = 1751203) (by norm_num)
theorem B3113249 : Blo 2075435 3113249 := bstep (se 2 (by rfl) ⟨1167468, by rfl⟩ : syracuseStep 3113249 = 2334937) B2334937
theorem B2075499 : Blo 2075435 2075499 := bstep (se 1 (by rfl) ⟨1556624, by rfl⟩ : syracuseStep 2075499 = 3113249) B3113249
theorem B3324557 : Blo 2075435 3324557 := bbase (se 3 (by rfl) ⟨623354, by rfl⟩ : syracuseStep 3324557 = 1246709) (by norm_num)
theorem B2216371 : Blo 2075435 2216371 := bstep (se 1 (by rfl) ⟨1662278, by rfl⟩ : syracuseStep 2216371 = 3324557) B3324557
theorem B2955161 : Blo 2075435 2955161 := bstep (se 2 (by rfl) ⟨1108185, by rfl⟩ : syracuseStep 2955161 = 2216371) B2216371
theorem B7880429 : Blo 2075435 7880429 := bstep (se 3 (by rfl) ⟨1477580, by rfl⟩ : syracuseStep 7880429 = 2955161) B2955161
theorem B5253619 : Blo 2075435 5253619 := bstep (se 1 (by rfl) ⟨3940214, by rfl⟩ : syracuseStep 5253619 = 7880429) B7880429
theorem B7004825 : Blo 2075435 7004825 := bstep (se 2 (by rfl) ⟨2626809, by rfl⟩ : syracuseStep 7004825 = 5253619) B5253619
theorem B4669883 : Blo 2075435 4669883 := bstep (se 1 (by rfl) ⟨3502412, by rfl⟩ : syracuseStep 4669883 = 7004825) B7004825
theorem B3113255 : Blo 2075435 3113255 := bstep (se 1 (by rfl) ⟨2334941, by rfl⟩ : syracuseStep 3113255 = 4669883) B4669883
theorem B2075503 : Blo 2075435 2075503 := bstep (se 1 (by rfl) ⟨1556627, by rfl⟩ : syracuseStep 2075503 = 3113255) B3113255
theorem B3113261 : Blo 2075435 3113261 := bbase (se 3 (by rfl) ⟨583736, by rfl⟩ : syracuseStep 3113261 = 1167473) (by norm_num)
theorem B2075507 : Blo 2075435 2075507 := bstep (se 1 (by rfl) ⟨1556630, by rfl⟩ : syracuseStep 2075507 = 3113261) B3113261
theorem B4669901 : Blo 2075435 4669901 := bbase (se 3 (by rfl) ⟨875606, by rfl⟩ : syracuseStep 4669901 = 1751213) (by norm_num)
theorem B3113267 : Blo 2075435 3113267 := bstep (se 1 (by rfl) ⟨2334950, by rfl⟩ : syracuseStep 3113267 = 4669901) B4669901
theorem B2075511 : Blo 2075435 2075511 := bstep (se 1 (by rfl) ⟨1556633, by rfl⟩ : syracuseStep 2075511 = 3113267) B3113267
theorem B2626825 : Blo 2075435 2626825 := bbase (se 2 (by rfl) ⟨985059, by rfl⟩ : syracuseStep 2626825 = 1970119) (by norm_num)
theorem B3502433 : Blo 2075435 3502433 := bstep (se 2 (by rfl) ⟨1313412, by rfl⟩ : syracuseStep 3502433 = 2626825) B2626825
theorem B2334955 : Blo 2075435 2334955 := bstep (se 1 (by rfl) ⟨1751216, by rfl⟩ : syracuseStep 2334955 = 3502433) B3502433
theorem B3113273 : Blo 2075435 3113273 := bstep (se 2 (by rfl) ⟨1167477, by rfl⟩ : syracuseStep 3113273 = 2334955) B2334955
theorem B2075515 : Blo 2075435 2075515 := bstep (se 1 (by rfl) ⟨1556636, by rfl⟩ : syracuseStep 2075515 = 3113273) B3113273
theorem B29921237 : Blo 2075435 29921237 := bbase (se 7 (by rfl) ⟨350639, by rfl⟩ : syracuseStep 29921237 = 701279) (by norm_num)
theorem B19947491 : Blo 2075435 19947491 := bstep (se 1 (by rfl) ⟨14960618, by rfl⟩ : syracuseStep 19947491 = 29921237) B29921237
theorem B13298327 : Blo 2075435 13298327 := bstep (se 1 (by rfl) ⟨9973745, by rfl⟩ : syracuseStep 13298327 = 19947491) B19947491
theorem B8865551 : Blo 2075435 8865551 := bstep (se 1 (by rfl) ⟨6649163, by rfl⟩ : syracuseStep 8865551 = 13298327) B13298327
theorem B23641469 : Blo 2075435 23641469 := bstep (se 3 (by rfl) ⟨4432775, by rfl⟩ : syracuseStep 23641469 = 8865551) B8865551
theorem B15760979 : Blo 2075435 15760979 := bstep (se 1 (by rfl) ⟨11820734, by rfl⟩ : syracuseStep 15760979 = 23641469) B23641469
theorem B10507319 : Blo 2075435 10507319 := bstep (se 1 (by rfl) ⟨7880489, by rfl⟩ : syracuseStep 10507319 = 15760979) B15760979
theorem B7004879 : Blo 2075435 7004879 := bstep (se 1 (by rfl) ⟨5253659, by rfl⟩ : syracuseStep 7004879 = 10507319) B10507319
theorem B4669919 : Blo 2075435 4669919 := bstep (se 1 (by rfl) ⟨3502439, by rfl⟩ : syracuseStep 4669919 = 7004879) B7004879
theorem B3113279 : Blo 2075435 3113279 := bstep (se 1 (by rfl) ⟨2334959, by rfl⟩ : syracuseStep 3113279 = 4669919) B4669919
theorem B2075519 : Blo 2075435 2075519 := bstep (se 1 (by rfl) ⟨1556639, by rfl⟩ : syracuseStep 2075519 = 3113279) B3113279
theorem B3113285 : Blo 2075435 3113285 := bbase (se 4 (by rfl) ⟨291870, by rfl⟩ : syracuseStep 3113285 = 583741) (by norm_num)
theorem B2075523 : Blo 2075435 2075523 := bstep (se 1 (by rfl) ⟨1556642, by rfl⟩ : syracuseStep 2075523 = 3113285) B3113285
theorem B3502453 : Blo 2075435 3502453 := bbase (se 5 (by rfl) ⟨164177, by rfl⟩ : syracuseStep 3502453 = 328355) (by norm_num)
theorem B4669937 : Blo 2075435 4669937 := bstep (se 2 (by rfl) ⟨1751226, by rfl⟩ : syracuseStep 4669937 = 3502453) B3502453
theorem B3113291 : Blo 2075435 3113291 := bstep (se 1 (by rfl) ⟨2334968, by rfl⟩ : syracuseStep 3113291 = 4669937) B4669937
theorem B2075527 : Blo 2075435 2075527 := bstep (se 1 (by rfl) ⟨1556645, by rfl⟩ : syracuseStep 2075527 = 3113291) B3113291
theorem B2334973 : Blo 2075435 2334973 := bbase (se 3 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 2334973 = 875615) (by norm_num)
theorem B3113297 : Blo 2075435 3113297 := bstep (se 2 (by rfl) ⟨1167486, by rfl⟩ : syracuseStep 3113297 = 2334973) B2334973
theorem B2075531 : Blo 2075435 2075531 := bstep (se 1 (by rfl) ⟨1556648, by rfl⟩ : syracuseStep 2075531 = 3113297) B3113297
theorem B7004933 : Blo 2075435 7004933 := bbase (se 4 (by rfl) ⟨656712, by rfl⟩ : syracuseStep 7004933 = 1313425) (by norm_num)
theorem B4669955 : Blo 2075435 4669955 := bstep (se 1 (by rfl) ⟨3502466, by rfl⟩ : syracuseStep 4669955 = 7004933) B7004933
theorem B3113303 : Blo 2075435 3113303 := bstep (se 1 (by rfl) ⟨2334977, by rfl⟩ : syracuseStep 3113303 = 4669955) B4669955
theorem B2075535 : Blo 2075435 2075535 := bstep (se 1 (by rfl) ⟨1556651, by rfl⟩ : syracuseStep 2075535 = 3113303) B3113303
theorem B3113309 : Blo 2075435 3113309 := bbase (se 3 (by rfl) ⟨583745, by rfl⟩ : syracuseStep 3113309 = 1167491) (by norm_num)
theorem B2075539 : Blo 2075435 2075539 := bstep (se 1 (by rfl) ⟨1556654, by rfl⟩ : syracuseStep 2075539 = 3113309) B3113309
theorem B4669973 : Blo 2075435 4669973 := bbase (se 6 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 4669973 = 218905) (by norm_num)
theorem B3113315 : Blo 2075435 3113315 := bstep (se 1 (by rfl) ⟨2334986, by rfl⟩ : syracuseStep 3113315 = 4669973) B4669973
theorem B2075543 : Blo 2075435 2075543 := bstep (se 1 (by rfl) ⟨1556657, by rfl⟩ : syracuseStep 2075543 = 3113315) B3113315
theorem B7880597 : Blo 2075435 7880597 := bbase (se 6 (by rfl) ⟨184701, by rfl⟩ : syracuseStep 7880597 = 369403) (by norm_num)
theorem B5253731 : Blo 2075435 5253731 := bstep (se 1 (by rfl) ⟨3940298, by rfl⟩ : syracuseStep 5253731 = 7880597) B7880597
theorem B3502487 : Blo 2075435 3502487 := bstep (se 1 (by rfl) ⟨2626865, by rfl⟩ : syracuseStep 3502487 = 5253731) B5253731
theorem B2334991 : Blo 2075435 2334991 := bstep (se 1 (by rfl) ⟨1751243, by rfl⟩ : syracuseStep 2334991 = 3502487) B3502487
theorem B3113321 : Blo 2075435 3113321 := bstep (se 2 (by rfl) ⟨1167495, by rfl⟩ : syracuseStep 3113321 = 2334991) B2334991
theorem B2075547 : Blo 2075435 2075547 := bstep (se 1 (by rfl) ⟨1556660, by rfl⟩ : syracuseStep 2075547 = 3113321) B3113321
theorem B11820917 : Blo 2075435 11820917 := bbase (se 5 (by rfl) ⟨554105, by rfl⟩ : syracuseStep 11820917 = 1108211) (by norm_num)
theorem B7880611 : Blo 2075435 7880611 := bstep (se 1 (by rfl) ⟨5910458, by rfl⟩ : syracuseStep 7880611 = 11820917) B11820917
theorem B10507481 : Blo 2075435 10507481 := bstep (se 2 (by rfl) ⟨3940305, by rfl⟩ : syracuseStep 10507481 = 7880611) B7880611
theorem B7004987 : Blo 2075435 7004987 := bstep (se 1 (by rfl) ⟨5253740, by rfl⟩ : syracuseStep 7004987 = 10507481) B10507481
theorem B4669991 : Blo 2075435 4669991 := bstep (se 1 (by rfl) ⟨3502493, by rfl⟩ : syracuseStep 4669991 = 7004987) B7004987
theorem B3113327 : Blo 2075435 3113327 := bstep (se 1 (by rfl) ⟨2334995, by rfl⟩ : syracuseStep 3113327 = 4669991) B4669991
theorem B2075551 : Blo 2075435 2075551 := bstep (se 1 (by rfl) ⟨1556663, by rfl⟩ : syracuseStep 2075551 = 3113327) B3113327
theorem B3113333 : Blo 2075435 3113333 := bbase (se 5 (by rfl) ⟨145937, by rfl⟩ : syracuseStep 3113333 = 291875) (by norm_num)
theorem B2075555 : Blo 2075435 2075555 := bstep (se 1 (by rfl) ⟨1556666, by rfl⟩ : syracuseStep 2075555 = 3113333) B3113333
theorem B6831973 : Blo 2075435 6831973 := bbase (se 4 (by rfl) ⟨640497, by rfl⟩ : syracuseStep 6831973 = 1280995) (by norm_num)
theorem B9109297 : Blo 2075435 9109297 := bstep (se 2 (by rfl) ⟨3415986, by rfl⟩ : syracuseStep 9109297 = 6831973) B6831973
theorem B12145729 : Blo 2075435 12145729 := bstep (se 2 (by rfl) ⟨4554648, by rfl⟩ : syracuseStep 12145729 = 9109297) B9109297
theorem B16194305 : Blo 2075435 16194305 := bstep (se 2 (by rfl) ⟨6072864, by rfl⟩ : syracuseStep 16194305 = 12145729) B12145729
theorem B10796203 : Blo 2075435 10796203 := bstep (se 1 (by rfl) ⟨8097152, by rfl⟩ : syracuseStep 10796203 = 16194305) B16194305
theorem B14394937 : Blo 2075435 14394937 := bstep (se 2 (by rfl) ⟨5398101, by rfl⟩ : syracuseStep 14394937 = 10796203) B10796203
theorem B19193249 : Blo 2075435 19193249 := bstep (se 2 (by rfl) ⟨7197468, by rfl⟩ : syracuseStep 19193249 = 14394937) B14394937
theorem B12795499 : Blo 2075435 12795499 := bstep (se 1 (by rfl) ⟨9596624, by rfl⟩ : syracuseStep 12795499 = 19193249) B19193249
theorem B17060665 : Blo 2075435 17060665 := bstep (se 2 (by rfl) ⟨6397749, by rfl⟩ : syracuseStep 17060665 = 12795499) B12795499
theorem B22747553 : Blo 2075435 22747553 := bstep (se 2 (by rfl) ⟨8530332, by rfl⟩ : syracuseStep 22747553 = 17060665) B17060665
theorem B15165035 : Blo 2075435 15165035 := bstep (se 1 (by rfl) ⟨11373776, by rfl⟩ : syracuseStep 15165035 = 22747553) B22747553
theorem B10110023 : Blo 2075435 10110023 := bstep (se 1 (by rfl) ⟨7582517, by rfl⟩ : syracuseStep 10110023 = 15165035) B15165035
theorem B6740015 : Blo 2075435 6740015 := bstep (se 1 (by rfl) ⟨5055011, by rfl⟩ : syracuseStep 6740015 = 10110023) B10110023
theorem B71893493 : Blo 2075435 71893493 := bstep (se 5 (by rfl) ⟨3370007, by rfl⟩ : syracuseStep 71893493 = 6740015) B6740015
theorem B47928995 : Blo 2075435 47928995 := bstep (se 1 (by rfl) ⟨35946746, by rfl⟩ : syracuseStep 47928995 = 71893493) B71893493
theorem B31952663 : Blo 2075435 31952663 := bstep (se 1 (by rfl) ⟨23964497, by rfl⟩ : syracuseStep 31952663 = 47928995) B47928995
theorem B21301775 : Blo 2075435 21301775 := bstep (se 1 (by rfl) ⟨15976331, by rfl⟩ : syracuseStep 21301775 = 31952663) B31952663
theorem B14201183 : Blo 2075435 14201183 := bstep (se 1 (by rfl) ⟨10650887, by rfl⟩ : syracuseStep 14201183 = 21301775) B21301775
theorem B9467455 : Blo 2075435 9467455 := bstep (se 1 (by rfl) ⟨7100591, by rfl⟩ : syracuseStep 9467455 = 14201183) B14201183
theorem B12623273 : Blo 2075435 12623273 := bstep (se 2 (by rfl) ⟨4733727, by rfl⟩ : syracuseStep 12623273 = 9467455) B9467455
theorem B8415515 : Blo 2075435 8415515 := bstep (se 1 (by rfl) ⟨6311636, by rfl⟩ : syracuseStep 8415515 = 12623273) B12623273
theorem B5610343 : Blo 2075435 5610343 := bstep (se 1 (by rfl) ⟨4207757, by rfl⟩ : syracuseStep 5610343 = 8415515) B8415515
theorem B7480457 : Blo 2075435 7480457 := bstep (se 2 (by rfl) ⟨2805171, by rfl⟩ : syracuseStep 7480457 = 5610343) B5610343
theorem B4986971 : Blo 2075435 4986971 := bstep (se 1 (by rfl) ⟨3740228, by rfl⟩ : syracuseStep 4986971 = 7480457) B7480457
theorem B3324647 : Blo 2075435 3324647 := bstep (se 1 (by rfl) ⟨2493485, by rfl⟩ : syracuseStep 3324647 = 4986971) B4986971
theorem B2216431 : Blo 2075435 2216431 := bstep (se 1 (by rfl) ⟨1662323, by rfl⟩ : syracuseStep 2216431 = 3324647) B3324647
theorem B2955241 : Blo 2075435 2955241 := bstep (se 2 (by rfl) ⟨1108215, by rfl⟩ : syracuseStep 2955241 = 2216431) B2216431
theorem B3940321 : Blo 2075435 3940321 := bstep (se 2 (by rfl) ⟨1477620, by rfl⟩ : syracuseStep 3940321 = 2955241) B2955241
theorem B5253761 : Blo 2075435 5253761 := bstep (se 2 (by rfl) ⟨1970160, by rfl⟩ : syracuseStep 5253761 = 3940321) B3940321
theorem B3502507 : Blo 2075435 3502507 := bstep (se 1 (by rfl) ⟨2626880, by rfl⟩ : syracuseStep 3502507 = 5253761) B5253761
theorem B4670009 : Blo 2075435 4670009 := bstep (se 2 (by rfl) ⟨1751253, by rfl⟩ : syracuseStep 4670009 = 3502507) B3502507
theorem B3113339 : Blo 2075435 3113339 := bstep (se 1 (by rfl) ⟨2335004, by rfl⟩ : syracuseStep 3113339 = 4670009) B4670009
theorem B2075559 : Blo 2075435 2075559 := bstep (se 1 (by rfl) ⟨1556669, by rfl⟩ : syracuseStep 2075559 = 3113339) B3113339
theorem B2335009 : Blo 2075435 2335009 := bbase (se 2 (by rfl) ⟨875628, by rfl⟩ : syracuseStep 2335009 = 1751257) (by norm_num)
theorem B3113345 : Blo 2075435 3113345 := bstep (se 2 (by rfl) ⟨1167504, by rfl⟩ : syracuseStep 3113345 = 2335009) B2335009
theorem B2075563 : Blo 2075435 2075563 := bstep (se 1 (by rfl) ⟨1556672, by rfl⟩ : syracuseStep 2075563 = 3113345) B3113345
theorem B5253781 : Blo 2075435 5253781 := bbase (se 6 (by rfl) ⟨123135, by rfl⟩ : syracuseStep 5253781 = 246271) (by norm_num)
theorem B7005041 : Blo 2075435 7005041 := bstep (se 2 (by rfl) ⟨2626890, by rfl⟩ : syracuseStep 7005041 = 5253781) B5253781
theorem B4670027 : Blo 2075435 4670027 := bstep (se 1 (by rfl) ⟨3502520, by rfl⟩ : syracuseStep 4670027 = 7005041) B7005041
theorem B3113351 : Blo 2075435 3113351 := bstep (se 1 (by rfl) ⟨2335013, by rfl⟩ : syracuseStep 3113351 = 4670027) B4670027
theorem B2075567 : Blo 2075435 2075567 := bstep (se 1 (by rfl) ⟨1556675, by rfl⟩ : syracuseStep 2075567 = 3113351) B3113351
theorem B3113357 : Blo 2075435 3113357 := bbase (se 3 (by rfl) ⟨583754, by rfl⟩ : syracuseStep 3113357 = 1167509) (by norm_num)
theorem B2075571 : Blo 2075435 2075571 := bstep (se 1 (by rfl) ⟨1556678, by rfl⟩ : syracuseStep 2075571 = 3113357) B3113357
theorem B4670045 : Blo 2075435 4670045 := bbase (se 3 (by rfl) ⟨875633, by rfl⟩ : syracuseStep 4670045 = 1751267) (by norm_num)
theorem B3113363 : Blo 2075435 3113363 := bstep (se 1 (by rfl) ⟨2335022, by rfl⟩ : syracuseStep 3113363 = 4670045) B4670045
theorem B2075575 : Blo 2075435 2075575 := bstep (se 1 (by rfl) ⟨1556681, by rfl⟩ : syracuseStep 2075575 = 3113363) B3113363
theorem B3502541 : Blo 2075435 3502541 := bbase (se 3 (by rfl) ⟨656726, by rfl⟩ : syracuseStep 3502541 = 1313453) (by norm_num)
theorem B2335027 : Blo 2075435 2335027 := bstep (se 1 (by rfl) ⟨1751270, by rfl⟩ : syracuseStep 2335027 = 3502541) B3502541
theorem B3113369 : Blo 2075435 3113369 := bstep (se 2 (by rfl) ⟨1167513, by rfl⟩ : syracuseStep 3113369 = 2335027) B2335027
theorem B2075579 : Blo 2075435 2075579 := bstep (se 1 (by rfl) ⟨1556684, by rfl⟩ : syracuseStep 2075579 = 3113369) B3113369
theorem B9974053 : Blo 2075435 9974053 := bbase (se 4 (by rfl) ⟨935067, by rfl⟩ : syracuseStep 9974053 = 1870135) (by norm_num)
theorem B13298737 : Blo 2075435 13298737 := bstep (se 2 (by rfl) ⟨4987026, by rfl⟩ : syracuseStep 13298737 = 9974053) B9974053
theorem B17731649 : Blo 2075435 17731649 := bstep (se 2 (by rfl) ⟨6649368, by rfl⟩ : syracuseStep 17731649 = 13298737) B13298737
theorem B11821099 : Blo 2075435 11821099 := bstep (se 1 (by rfl) ⟨8865824, by rfl⟩ : syracuseStep 11821099 = 17731649) B17731649
theorem B15761465 : Blo 2075435 15761465 := bstep (se 2 (by rfl) ⟨5910549, by rfl⟩ : syracuseStep 15761465 = 11821099) B11821099
theorem B10507643 : Blo 2075435 10507643 := bstep (se 1 (by rfl) ⟨7880732, by rfl⟩ : syracuseStep 10507643 = 15761465) B15761465
theorem B7005095 : Blo 2075435 7005095 := bstep (se 1 (by rfl) ⟨5253821, by rfl⟩ : syracuseStep 7005095 = 10507643) B10507643
theorem B4670063 : Blo 2075435 4670063 := bstep (se 1 (by rfl) ⟨3502547, by rfl⟩ : syracuseStep 4670063 = 7005095) B7005095
theorem B3113375 : Blo 2075435 3113375 := bstep (se 1 (by rfl) ⟨2335031, by rfl⟩ : syracuseStep 3113375 = 4670063) B4670063
theorem B2075583 : Blo 2075435 2075583 := bstep (se 1 (by rfl) ⟨1556687, by rfl⟩ : syracuseStep 2075583 = 3113375) B3113375
theorem B3113381 : Blo 2075435 3113381 := bbase (se 4 (by rfl) ⟨291879, by rfl⟩ : syracuseStep 3113381 = 583759) (by norm_num)
theorem B2075587 : Blo 2075435 2075587 := bstep (se 1 (by rfl) ⟨1556690, by rfl⟩ : syracuseStep 2075587 = 3113381) B3113381
theorem B2626921 : Blo 2075435 2626921 := bbase (se 2 (by rfl) ⟨985095, by rfl⟩ : syracuseStep 2626921 = 1970191) (by norm_num)
theorem B3502561 : Blo 2075435 3502561 := bstep (se 2 (by rfl) ⟨1313460, by rfl⟩ : syracuseStep 3502561 = 2626921) B2626921
theorem B4670081 : Blo 2075435 4670081 := bstep (se 2 (by rfl) ⟨1751280, by rfl⟩ : syracuseStep 4670081 = 3502561) B3502561
theorem B3113387 : Blo 2075435 3113387 := bstep (se 1 (by rfl) ⟨2335040, by rfl⟩ : syracuseStep 3113387 = 4670081) B4670081
theorem B2075591 : Blo 2075435 2075591 := bstep (se 1 (by rfl) ⟨1556693, by rfl⟩ : syracuseStep 2075591 = 3113387) B3113387
theorem B2335045 : Blo 2075435 2335045 := bbase (se 4 (by rfl) ⟨218910, by rfl⟩ : syracuseStep 2335045 = 437821) (by norm_num)
theorem B3113393 : Blo 2075435 3113393 := bstep (se 2 (by rfl) ⟨1167522, by rfl⟩ : syracuseStep 3113393 = 2335045) B2335045
theorem B2075595 : Blo 2075435 2075595 := bstep (se 1 (by rfl) ⟨1556696, by rfl⟩ : syracuseStep 2075595 = 3113393) B3113393
theorem B3940397 : Blo 2075435 3940397 := bbase (se 3 (by rfl) ⟨738824, by rfl⟩ : syracuseStep 3940397 = 1477649) (by norm_num)
theorem B2626931 : Blo 2075435 2626931 := bstep (se 1 (by rfl) ⟨1970198, by rfl⟩ : syracuseStep 2626931 = 3940397) B3940397
theorem B7005149 : Blo 2075435 7005149 := bstep (se 3 (by rfl) ⟨1313465, by rfl⟩ : syracuseStep 7005149 = 2626931) B2626931
theorem B4670099 : Blo 2075435 4670099 := bstep (se 1 (by rfl) ⟨3502574, by rfl⟩ : syracuseStep 4670099 = 7005149) B7005149
theorem B3113399 : Blo 2075435 3113399 := bstep (se 1 (by rfl) ⟨2335049, by rfl⟩ : syracuseStep 3113399 = 4670099) B4670099
theorem B2075599 : Blo 2075435 2075599 := bstep (se 1 (by rfl) ⟨1556699, by rfl⟩ : syracuseStep 2075599 = 3113399) B3113399
theorem B3113405 : Blo 2075435 3113405 := bbase (se 3 (by rfl) ⟨583763, by rfl⟩ : syracuseStep 3113405 = 1167527) (by norm_num)
theorem B2075603 : Blo 2075435 2075603 := bstep (se 1 (by rfl) ⟨1556702, by rfl⟩ : syracuseStep 2075603 = 3113405) B3113405
theorem B4670117 : Blo 2075435 4670117 := bbase (se 4 (by rfl) ⟨437823, by rfl⟩ : syracuseStep 4670117 = 875647) (by norm_num)
theorem B3113411 : Blo 2075435 3113411 := bstep (se 1 (by rfl) ⟨2335058, by rfl⟩ : syracuseStep 3113411 = 4670117) B4670117
theorem B2075607 : Blo 2075435 2075607 := bstep (se 1 (by rfl) ⟨1556705, by rfl⟩ : syracuseStep 2075607 = 3113411) B3113411
theorem B5253893 : Blo 2075435 5253893 := bbase (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) (by norm_num)
theorem B3502595 : Blo 2075435 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B2335063 : Blo 2075435 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B3113417 : Blo 2075435 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B2075611 : Blo 2075435 2075611 := bstep (se 1 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 2075611 = 3113417) B3113417
theorem B4432981 : Blo 2075435 4432981 := bbase (se 8 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 4432981 = 51949) (by norm_num)
theorem B5910641 : Blo 2075435 5910641 := bstep (se 2 (by rfl) ⟨2216490, by rfl⟩ : syracuseStep 5910641 = 4432981) B4432981
theorem B3940427 : Blo 2075435 3940427 := bstep (se 1 (by rfl) ⟨2955320, by rfl⟩ : syracuseStep 3940427 = 5910641) B5910641
theorem B10507805 : Blo 2075435 10507805 := bstep (se 3 (by rfl) ⟨1970213, by rfl⟩ : syracuseStep 10507805 = 3940427) B3940427
theorem B7005203 : Blo 2075435 7005203 := bstep (se 1 (by rfl) ⟨5253902, by rfl⟩ : syracuseStep 7005203 = 10507805) B10507805
theorem B4670135 : Blo 2075435 4670135 := bstep (se 1 (by rfl) ⟨3502601, by rfl⟩ : syracuseStep 4670135 = 7005203) B7005203
theorem B3113423 : Blo 2075435 3113423 := bstep (se 1 (by rfl) ⟨2335067, by rfl⟩ : syracuseStep 3113423 = 4670135) B4670135
theorem B2075615 : Blo 2075435 2075615 := bstep (se 1 (by rfl) ⟨1556711, by rfl⟩ : syracuseStep 2075615 = 3113423) B3113423
theorem B3113429 : Blo 2075435 3113429 := bbase (se 7 (by rfl) ⟨36485, by rfl⟩ : syracuseStep 3113429 = 72971) (by norm_num)
theorem B2075619 : Blo 2075435 2075619 := bstep (se 1 (by rfl) ⟨1556714, by rfl⟩ : syracuseStep 2075619 = 3113429) B3113429
theorem B7880885 : Blo 2075435 7880885 := bbase (se 5 (by rfl) ⟨369416, by rfl⟩ : syracuseStep 7880885 = 738833) (by norm_num)
theorem B5253923 : Blo 2075435 5253923 := bstep (se 1 (by rfl) ⟨3940442, by rfl⟩ : syracuseStep 5253923 = 7880885) B7880885
theorem B3502615 : Blo 2075435 3502615 := bstep (se 1 (by rfl) ⟨2626961, by rfl⟩ : syracuseStep 3502615 = 5253923) B5253923
theorem B4670153 : Blo 2075435 4670153 := bstep (se 2 (by rfl) ⟨1751307, by rfl⟩ : syracuseStep 4670153 = 3502615) B3502615
theorem B3113435 : Blo 2075435 3113435 := bstep (se 1 (by rfl) ⟨2335076, by rfl⟩ : syracuseStep 3113435 = 4670153) B4670153
theorem B2075623 : Blo 2075435 2075623 := bstep (se 1 (by rfl) ⟨1556717, by rfl⟩ : syracuseStep 2075623 = 3113435) B3113435
theorem B2335081 : Blo 2075435 2335081 := bbase (se 2 (by rfl) ⟨875655, by rfl⟩ : syracuseStep 2335081 = 1751311) (by norm_num)
theorem B3113441 : Blo 2075435 3113441 := bstep (se 2 (by rfl) ⟨1167540, by rfl⟩ : syracuseStep 3113441 = 2335081) B2335081
theorem B2075627 : Blo 2075435 2075627 := bstep (se 1 (by rfl) ⟨1556720, by rfl⟩ : syracuseStep 2075627 = 3113441) B3113441
theorem B3740357 : Blo 2075435 3740357 := bbase (se 4 (by rfl) ⟨350658, by rfl⟩ : syracuseStep 3740357 = 701317) (by norm_num)
theorem B9974285 : Blo 2075435 9974285 := bstep (se 3 (by rfl) ⟨1870178, by rfl⟩ : syracuseStep 9974285 = 3740357) B3740357
theorem B6649523 : Blo 2075435 6649523 := bstep (se 1 (by rfl) ⟨4987142, by rfl⟩ : syracuseStep 6649523 = 9974285) B9974285
theorem B4433015 : Blo 2075435 4433015 := bstep (se 1 (by rfl) ⟨3324761, by rfl⟩ : syracuseStep 4433015 = 6649523) B6649523
theorem B11821373 : Blo 2075435 11821373 := bstep (se 3 (by rfl) ⟨2216507, by rfl⟩ : syracuseStep 11821373 = 4433015) B4433015
theorem B7880915 : Blo 2075435 7880915 := bstep (se 1 (by rfl) ⟨5910686, by rfl⟩ : syracuseStep 7880915 = 11821373) B11821373
theorem B5253943 : Blo 2075435 5253943 := bstep (se 1 (by rfl) ⟨3940457, by rfl⟩ : syracuseStep 5253943 = 7880915) B7880915
theorem B7005257 : Blo 2075435 7005257 := bstep (se 2 (by rfl) ⟨2626971, by rfl⟩ : syracuseStep 7005257 = 5253943) B5253943
theorem B4670171 : Blo 2075435 4670171 := bstep (se 1 (by rfl) ⟨3502628, by rfl⟩ : syracuseStep 4670171 = 7005257) B7005257
theorem B3113447 : Blo 2075435 3113447 := bstep (se 1 (by rfl) ⟨2335085, by rfl⟩ : syracuseStep 3113447 = 4670171) B4670171
theorem B2075631 : Blo 2075435 2075631 := bstep (se 1 (by rfl) ⟨1556723, by rfl⟩ : syracuseStep 2075631 = 3113447) B3113447
theorem B3113453 : Blo 2075435 3113453 := bbase (se 3 (by rfl) ⟨583772, by rfl⟩ : syracuseStep 3113453 = 1167545) (by norm_num)
theorem B2075635 : Blo 2075435 2075635 := bstep (se 1 (by rfl) ⟨1556726, by rfl⟩ : syracuseStep 2075635 = 3113453) B3113453
theorem B4670189 : Blo 2075435 4670189 := bbase (se 3 (by rfl) ⟨875660, by rfl⟩ : syracuseStep 4670189 = 1751321) (by norm_num)
theorem B3113459 : Blo 2075435 3113459 := bstep (se 1 (by rfl) ⟨2335094, by rfl⟩ : syracuseStep 3113459 = 4670189) B4670189
theorem B2075639 : Blo 2075435 2075639 := bstep (se 1 (by rfl) ⟨1556729, by rfl⟩ : syracuseStep 2075639 = 3113459) B3113459
theorem B2216521 : Blo 2075435 2216521 := bbase (se 2 (by rfl) ⟨831195, by rfl⟩ : syracuseStep 2216521 = 1662391) (by norm_num)
theorem B2955361 : Blo 2075435 2955361 := bstep (se 2 (by rfl) ⟨1108260, by rfl⟩ : syracuseStep 2955361 = 2216521) B2216521
theorem B3940481 : Blo 2075435 3940481 := bstep (se 2 (by rfl) ⟨1477680, by rfl⟩ : syracuseStep 3940481 = 2955361) B2955361
theorem B2626987 : Blo 2075435 2626987 := bstep (se 1 (by rfl) ⟨1970240, by rfl⟩ : syracuseStep 2626987 = 3940481) B3940481
theorem B3502649 : Blo 2075435 3502649 := bstep (se 2 (by rfl) ⟨1313493, by rfl⟩ : syracuseStep 3502649 = 2626987) B2626987
theorem B2335099 : Blo 2075435 2335099 := bstep (se 1 (by rfl) ⟨1751324, by rfl⟩ : syracuseStep 2335099 = 3502649) B3502649
theorem B3113465 : Blo 2075435 3113465 := bstep (se 2 (by rfl) ⟨1167549, by rfl⟩ : syracuseStep 3113465 = 2335099) B2335099
theorem B2075643 : Blo 2075435 2075643 := bstep (se 1 (by rfl) ⟨1556732, by rfl⟩ : syracuseStep 2075643 = 3113465) B3113465
theorem B16831733 : Blo 2075435 16831733 := bbase (se 5 (by rfl) ⟨788987, by rfl⟩ : syracuseStep 16831733 = 1577975) (by norm_num)
theorem B44884621 : Blo 2075435 44884621 := bstep (se 3 (by rfl) ⟨8415866, by rfl⟩ : syracuseStep 44884621 = 16831733) B16831733
theorem B59846161 : Blo 2075435 59846161 := bstep (se 2 (by rfl) ⟨22442310, by rfl⟩ : syracuseStep 59846161 = 44884621) B44884621
theorem B79794881 : Blo 2075435 79794881 := bstep (se 2 (by rfl) ⟨29923080, by rfl⟩ : syracuseStep 79794881 = 59846161) B59846161
theorem B53196587 : Blo 2075435 53196587 := bstep (se 1 (by rfl) ⟨39897440, by rfl⟩ : syracuseStep 53196587 = 79794881) B79794881
theorem B35464391 : Blo 2075435 35464391 := bstep (se 1 (by rfl) ⟨26598293, by rfl⟩ : syracuseStep 35464391 = 53196587) B53196587
theorem B23642927 : Blo 2075435 23642927 := bstep (se 1 (by rfl) ⟨17732195, by rfl⟩ : syracuseStep 23642927 = 35464391) B35464391
theorem B15761951 : Blo 2075435 15761951 := bstep (se 1 (by rfl) ⟨11821463, by rfl⟩ : syracuseStep 15761951 = 23642927) B23642927
theorem B10507967 : Blo 2075435 10507967 := bstep (se 1 (by rfl) ⟨7880975, by rfl⟩ : syracuseStep 10507967 = 15761951) B15761951
theorem B7005311 : Blo 2075435 7005311 := bstep (se 1 (by rfl) ⟨5253983, by rfl⟩ : syracuseStep 7005311 = 10507967) B10507967
theorem B4670207 : Blo 2075435 4670207 := bstep (se 1 (by rfl) ⟨3502655, by rfl⟩ : syracuseStep 4670207 = 7005311) B7005311
theorem B3113471 : Blo 2075435 3113471 := bstep (se 1 (by rfl) ⟨2335103, by rfl⟩ : syracuseStep 3113471 = 4670207) B4670207
theorem B2075647 : Blo 2075435 2075647 := bstep (se 1 (by rfl) ⟨1556735, by rfl⟩ : syracuseStep 2075647 = 3113471) B3113471
theorem B3113477 : Blo 2075435 3113477 := bbase (se 4 (by rfl) ⟨291888, by rfl⟩ : syracuseStep 3113477 = 583777) (by norm_num)
theorem B2075651 : Blo 2075435 2075651 := bstep (se 1 (by rfl) ⟨1556738, by rfl⟩ : syracuseStep 2075651 = 3113477) B3113477
theorem B3502669 : Blo 2075435 3502669 := bbase (se 3 (by rfl) ⟨656750, by rfl⟩ : syracuseStep 3502669 = 1313501) (by norm_num)
theorem B4670225 : Blo 2075435 4670225 := bstep (se 2 (by rfl) ⟨1751334, by rfl⟩ : syracuseStep 4670225 = 3502669) B3502669
theorem B3113483 : Blo 2075435 3113483 := bstep (se 1 (by rfl) ⟨2335112, by rfl⟩ : syracuseStep 3113483 = 4670225) B4670225
theorem B2075655 : Blo 2075435 2075655 := bstep (se 1 (by rfl) ⟨1556741, by rfl⟩ : syracuseStep 2075655 = 3113483) B3113483
theorem B2335117 : Blo 2075435 2335117 := bbase (se 3 (by rfl) ⟨437834, by rfl⟩ : syracuseStep 2335117 = 875669) (by norm_num)
theorem B3113489 : Blo 2075435 3113489 := bstep (se 2 (by rfl) ⟨1167558, by rfl⟩ : syracuseStep 3113489 = 2335117) B2335117
theorem B2075659 : Blo 2075435 2075659 := bstep (se 1 (by rfl) ⟨1556744, by rfl⟩ : syracuseStep 2075659 = 3113489) B3113489
theorem B7005365 : Blo 2075435 7005365 := bbase (se 5 (by rfl) ⟨328376, by rfl⟩ : syracuseStep 7005365 = 656753) (by norm_num)
theorem B4670243 : Blo 2075435 4670243 := bstep (se 1 (by rfl) ⟨3502682, by rfl⟩ : syracuseStep 4670243 = 7005365) B7005365
theorem B3113495 : Blo 2075435 3113495 := bstep (se 1 (by rfl) ⟨2335121, by rfl⟩ : syracuseStep 3113495 = 4670243) B4670243
theorem B2075663 : Blo 2075435 2075663 := bstep (se 1 (by rfl) ⟨1556747, by rfl⟩ : syracuseStep 2075663 = 3113495) B3113495
theorem B3113501 : Blo 2075435 3113501 := bbase (se 3 (by rfl) ⟨583781, by rfl⟩ : syracuseStep 3113501 = 1167563) (by norm_num)
theorem B2075667 : Blo 2075435 2075667 := bstep (se 1 (by rfl) ⟨1556750, by rfl⟩ : syracuseStep 2075667 = 3113501) B3113501
theorem B4670261 : Blo 2075435 4670261 := bbase (se 5 (by rfl) ⟨218918, by rfl⟩ : syracuseStep 4670261 = 437837) (by norm_num)
theorem B3113507 : Blo 2075435 3113507 := bstep (se 1 (by rfl) ⟨2335130, by rfl⟩ : syracuseStep 3113507 = 4670261) B4670261
theorem B2075671 : Blo 2075435 2075671 := bstep (se 1 (by rfl) ⟨1556753, by rfl⟩ : syracuseStep 2075671 = 3113507) B3113507
theorem B15165877 : Blo 2075435 15165877 := bbase (se 5 (by rfl) ⟨710900, by rfl⟩ : syracuseStep 15165877 = 1421801) (by norm_num)
theorem B20221169 : Blo 2075435 20221169 := bstep (se 2 (by rfl) ⟨7582938, by rfl⟩ : syracuseStep 20221169 = 15165877) B15165877
theorem B53923117 : Blo 2075435 53923117 := bstep (se 3 (by rfl) ⟨10110584, by rfl⟩ : syracuseStep 53923117 = 20221169) B20221169
theorem B71897489 : Blo 2075435 71897489 := bstep (se 2 (by rfl) ⟨26961558, by rfl⟩ : syracuseStep 71897489 = 53923117) B53923117
theorem B47931659 : Blo 2075435 47931659 := bstep (se 1 (by rfl) ⟨35948744, by rfl⟩ : syracuseStep 47931659 = 71897489) B71897489
theorem B31954439 : Blo 2075435 31954439 := bstep (se 1 (by rfl) ⟨23965829, by rfl⟩ : syracuseStep 31954439 = 47931659) B47931659
theorem B21302959 : Blo 2075435 21302959 := bstep (se 1 (by rfl) ⟨15977219, by rfl⟩ : syracuseStep 21302959 = 31954439) B31954439
theorem B28403945 : Blo 2075435 28403945 := bstep (se 2 (by rfl) ⟨10651479, by rfl⟩ : syracuseStep 28403945 = 21302959) B21302959
theorem B18935963 : Blo 2075435 18935963 := bstep (se 1 (by rfl) ⟨14201972, by rfl⟩ : syracuseStep 18935963 = 28403945) B28403945
theorem B12623975 : Blo 2075435 12623975 := bstep (se 1 (by rfl) ⟨9467981, by rfl⟩ : syracuseStep 12623975 = 18935963) B18935963
theorem B8415983 : Blo 2075435 8415983 := bstep (se 1 (by rfl) ⟨6311987, by rfl⟩ : syracuseStep 8415983 = 12623975) B12623975
theorem B5610655 : Blo 2075435 5610655 := bstep (se 1 (by rfl) ⟨4207991, by rfl⟩ : syracuseStep 5610655 = 8415983) B8415983
theorem B7480873 : Blo 2075435 7480873 := bstep (se 2 (by rfl) ⟨2805327, by rfl⟩ : syracuseStep 7480873 = 5610655) B5610655
theorem B9974497 : Blo 2075435 9974497 := bstep (se 2 (by rfl) ⟨3740436, by rfl⟩ : syracuseStep 9974497 = 7480873) B7480873
theorem B13299329 : Blo 2075435 13299329 := bstep (se 2 (by rfl) ⟨4987248, by rfl⟩ : syracuseStep 13299329 = 9974497) B9974497
theorem B8866219 : Blo 2075435 8866219 := bstep (se 1 (by rfl) ⟨6649664, by rfl⟩ : syracuseStep 8866219 = 13299329) B13299329
theorem B11821625 : Blo 2075435 11821625 := bstep (se 2 (by rfl) ⟨4433109, by rfl⟩ : syracuseStep 11821625 = 8866219) B8866219
theorem B7881083 : Blo 2075435 7881083 := bstep (se 1 (by rfl) ⟨5910812, by rfl⟩ : syracuseStep 7881083 = 11821625) B11821625
theorem B5254055 : Blo 2075435 5254055 := bstep (se 1 (by rfl) ⟨3940541, by rfl⟩ : syracuseStep 5254055 = 7881083) B7881083
theorem B3502703 : Blo 2075435 3502703 := bstep (se 1 (by rfl) ⟨2627027, by rfl⟩ : syracuseStep 3502703 = 5254055) B5254055
theorem B2335135 : Blo 2075435 2335135 := bstep (se 1 (by rfl) ⟨1751351, by rfl⟩ : syracuseStep 2335135 = 3502703) B3502703
theorem B3113513 : Blo 2075435 3113513 := bstep (se 2 (by rfl) ⟨1167567, by rfl⟩ : syracuseStep 3113513 = 2335135) B2335135
theorem B2075675 : Blo 2075435 2075675 := bstep (se 1 (by rfl) ⟨1556756, by rfl⟩ : syracuseStep 2075675 = 3113513) B3113513
theorem B3791477 : Blo 2075435 3791477 := bbase (se 5 (by rfl) ⟨177725, by rfl⟩ : syracuseStep 3791477 = 355451) (by norm_num)
theorem B2527651 : Blo 2075435 2527651 := bstep (se 1 (by rfl) ⟨1895738, by rfl⟩ : syracuseStep 2527651 = 3791477) B3791477
theorem B13480805 : Blo 2075435 13480805 := bstep (se 4 (by rfl) ⟨1263825, by rfl⟩ : syracuseStep 13480805 = 2527651) B2527651
theorem B8987203 : Blo 2075435 8987203 := bstep (se 1 (by rfl) ⟨6740402, by rfl⟩ : syracuseStep 8987203 = 13480805) B13480805
theorem B47931749 : Blo 2075435 47931749 := bstep (se 4 (by rfl) ⟨4493601, by rfl⟩ : syracuseStep 47931749 = 8987203) B8987203
theorem B31954499 : Blo 2075435 31954499 := bstep (se 1 (by rfl) ⟨23965874, by rfl⟩ : syracuseStep 31954499 = 47931749) B47931749
theorem B21302999 : Blo 2075435 21302999 := bstep (se 1 (by rfl) ⟨15977249, by rfl⟩ : syracuseStep 21302999 = 31954499) B31954499
theorem B14201999 : Blo 2075435 14201999 := bstep (se 1 (by rfl) ⟨10651499, by rfl⟩ : syracuseStep 14201999 = 21302999) B21302999
theorem B9467999 : Blo 2075435 9467999 := bstep (se 1 (by rfl) ⟨7100999, by rfl⟩ : syracuseStep 9467999 = 14201999) B14201999
theorem B6311999 : Blo 2075435 6311999 := bstep (se 1 (by rfl) ⟨4733999, by rfl⟩ : syracuseStep 6311999 = 9467999) B9467999
theorem B4207999 : Blo 2075435 4207999 := bstep (se 1 (by rfl) ⟨3155999, by rfl⟩ : syracuseStep 4207999 = 6311999) B6311999
theorem B5610665 : Blo 2075435 5610665 := bstep (se 2 (by rfl) ⟨2103999, by rfl⟩ : syracuseStep 5610665 = 4207999) B4207999
theorem B14961773 : Blo 2075435 14961773 := bstep (se 3 (by rfl) ⟨2805332, by rfl⟩ : syracuseStep 14961773 = 5610665) B5610665
theorem B9974515 : Blo 2075435 9974515 := bstep (se 1 (by rfl) ⟨7480886, by rfl⟩ : syracuseStep 9974515 = 14961773) B14961773
theorem B13299353 : Blo 2075435 13299353 := bstep (se 2 (by rfl) ⟨4987257, by rfl⟩ : syracuseStep 13299353 = 9974515) B9974515
theorem B8866235 : Blo 2075435 8866235 := bstep (se 1 (by rfl) ⟨6649676, by rfl⟩ : syracuseStep 8866235 = 13299353) B13299353
theorem B5910823 : Blo 2075435 5910823 := bstep (se 1 (by rfl) ⟨4433117, by rfl⟩ : syracuseStep 5910823 = 8866235) B8866235
theorem B7881097 : Blo 2075435 7881097 := bstep (se 2 (by rfl) ⟨2955411, by rfl⟩ : syracuseStep 7881097 = 5910823) B5910823
theorem B10508129 : Blo 2075435 10508129 := bstep (se 2 (by rfl) ⟨3940548, by rfl⟩ : syracuseStep 10508129 = 7881097) B7881097
theorem B7005419 : Blo 2075435 7005419 := bstep (se 1 (by rfl) ⟨5254064, by rfl⟩ : syracuseStep 7005419 = 10508129) B10508129
theorem B4670279 : Blo 2075435 4670279 := bstep (se 1 (by rfl) ⟨3502709, by rfl⟩ : syracuseStep 4670279 = 7005419) B7005419
theorem B3113519 : Blo 2075435 3113519 := bstep (se 1 (by rfl) ⟨2335139, by rfl⟩ : syracuseStep 3113519 = 4670279) B4670279
theorem B2075679 : Blo 2075435 2075679 := bstep (se 1 (by rfl) ⟨1556759, by rfl⟩ : syracuseStep 2075679 = 3113519) B3113519
theorem B3113525 : Blo 2075435 3113525 := bbase (se 5 (by rfl) ⟨145946, by rfl⟩ : syracuseStep 3113525 = 291893) (by norm_num)
theorem B2075683 : Blo 2075435 2075683 := bstep (se 1 (by rfl) ⟨1556762, by rfl⟩ : syracuseStep 2075683 = 3113525) B3113525
theorem B5254085 : Blo 2075435 5254085 := bbase (se 4 (by rfl) ⟨492570, by rfl⟩ : syracuseStep 5254085 = 985141) (by norm_num)
theorem B3502723 : Blo 2075435 3502723 := bstep (se 1 (by rfl) ⟨2627042, by rfl⟩ : syracuseStep 3502723 = 5254085) B5254085
theorem B4670297 : Blo 2075435 4670297 := bstep (se 2 (by rfl) ⟨1751361, by rfl⟩ : syracuseStep 4670297 = 3502723) B3502723
theorem B3113531 : Blo 2075435 3113531 := bstep (se 1 (by rfl) ⟨2335148, by rfl⟩ : syracuseStep 3113531 = 4670297) B4670297
theorem B2075687 : Blo 2075435 2075687 := bstep (se 1 (by rfl) ⟨1556765, by rfl⟩ : syracuseStep 2075687 = 3113531) B3113531
theorem B2335153 : Blo 2075435 2335153 := bbase (se 2 (by rfl) ⟨875682, by rfl⟩ : syracuseStep 2335153 = 1751365) (by norm_num)
theorem B3113537 : Blo 2075435 3113537 := bstep (se 2 (by rfl) ⟨1167576, by rfl⟩ : syracuseStep 3113537 = 2335153) B2335153
theorem B2075691 : Blo 2075435 2075691 := bstep (se 1 (by rfl) ⟨1556768, by rfl⟩ : syracuseStep 2075691 = 3113537) B3113537
theorem B5910869 : Blo 2075435 5910869 := bbase (se 10 (by rfl) ⟨8658, by rfl⟩ : syracuseStep 5910869 = 17317) (by norm_num)
theorem B3940579 : Blo 2075435 3940579 := bstep (se 1 (by rfl) ⟨2955434, by rfl⟩ : syracuseStep 3940579 = 5910869) B5910869
theorem B5254105 : Blo 2075435 5254105 := bstep (se 2 (by rfl) ⟨1970289, by rfl⟩ : syracuseStep 5254105 = 3940579) B3940579
theorem B7005473 : Blo 2075435 7005473 := bstep (se 2 (by rfl) ⟨2627052, by rfl⟩ : syracuseStep 7005473 = 5254105) B5254105
theorem B4670315 : Blo 2075435 4670315 := bstep (se 1 (by rfl) ⟨3502736, by rfl⟩ : syracuseStep 4670315 = 7005473) B7005473
theorem B3113543 : Blo 2075435 3113543 := bstep (se 1 (by rfl) ⟨2335157, by rfl⟩ : syracuseStep 3113543 = 4670315) B4670315
theorem B2075695 : Blo 2075435 2075695 := bstep (se 1 (by rfl) ⟨1556771, by rfl⟩ : syracuseStep 2075695 = 3113543) B3113543
theorem B3113549 : Blo 2075435 3113549 := bbase (se 3 (by rfl) ⟨583790, by rfl⟩ : syracuseStep 3113549 = 1167581) (by norm_num)
theorem B2075699 : Blo 2075435 2075699 := bstep (se 1 (by rfl) ⟨1556774, by rfl⟩ : syracuseStep 2075699 = 3113549) B3113549
theorem B4670333 : Blo 2075435 4670333 := bbase (se 3 (by rfl) ⟨875687, by rfl⟩ : syracuseStep 4670333 = 1751375) (by norm_num)
theorem B3113555 : Blo 2075435 3113555 := bstep (se 1 (by rfl) ⟨2335166, by rfl⟩ : syracuseStep 3113555 = 4670333) B4670333
theorem B2075703 : Blo 2075435 2075703 := bstep (se 1 (by rfl) ⟨1556777, by rfl⟩ : syracuseStep 2075703 = 3113555) B3113555
theorem B3502757 : Blo 2075435 3502757 := bbase (se 4 (by rfl) ⟨328383, by rfl⟩ : syracuseStep 3502757 = 656767) (by norm_num)
theorem B2335171 : Blo 2075435 2335171 := bstep (se 1 (by rfl) ⟨1751378, by rfl⟩ : syracuseStep 2335171 = 3502757) B3502757
theorem B3113561 : Blo 2075435 3113561 := bstep (se 2 (by rfl) ⟨1167585, by rfl⟩ : syracuseStep 3113561 = 2335171) B2335171
theorem B2075707 : Blo 2075435 2075707 := bstep (se 1 (by rfl) ⟨1556780, by rfl⟩ : syracuseStep 2075707 = 3113561) B3113561
theorem B2216593 : Blo 2075435 2216593 := bbase (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) (by norm_num)
theorem B2955457 : Blo 2075435 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B15762437 : Blo 2075435 15762437 := bstep (se 4 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 15762437 = 2955457) B2955457
theorem B10508291 : Blo 2075435 10508291 := bstep (se 1 (by rfl) ⟨7881218, by rfl⟩ : syracuseStep 10508291 = 15762437) B15762437
theorem B7005527 : Blo 2075435 7005527 := bstep (se 1 (by rfl) ⟨5254145, by rfl⟩ : syracuseStep 7005527 = 10508291) B10508291
theorem B4670351 : Blo 2075435 4670351 := bstep (se 1 (by rfl) ⟨3502763, by rfl⟩ : syracuseStep 4670351 = 7005527) B7005527
theorem B3113567 : Blo 2075435 3113567 := bstep (se 1 (by rfl) ⟨2335175, by rfl⟩ : syracuseStep 3113567 = 4670351) B4670351
theorem B2075711 : Blo 2075435 2075711 := bstep (se 1 (by rfl) ⟨1556783, by rfl⟩ : syracuseStep 2075711 = 3113567) B3113567
theorem B3113573 : Blo 2075435 3113573 := bbase (se 4 (by rfl) ⟨291897, by rfl⟩ : syracuseStep 3113573 = 583795) (by norm_num)
theorem B2075715 : Blo 2075435 2075715 := bstep (se 1 (by rfl) ⟨1556786, by rfl⟩ : syracuseStep 2075715 = 3113573) B3113573
theorem B2955469 : Blo 2075435 2955469 := bbase (se 3 (by rfl) ⟨554150, by rfl⟩ : syracuseStep 2955469 = 1108301) (by norm_num)
theorem B3940625 : Blo 2075435 3940625 := bstep (se 2 (by rfl) ⟨1477734, by rfl⟩ : syracuseStep 3940625 = 2955469) B2955469
theorem B2627083 : Blo 2075435 2627083 := bstep (se 1 (by rfl) ⟨1970312, by rfl⟩ : syracuseStep 2627083 = 3940625) B3940625
theorem B3502777 : Blo 2075435 3502777 := bstep (se 2 (by rfl) ⟨1313541, by rfl⟩ : syracuseStep 3502777 = 2627083) B2627083
theorem B4670369 : Blo 2075435 4670369 := bstep (se 2 (by rfl) ⟨1751388, by rfl⟩ : syracuseStep 4670369 = 3502777) B3502777
theorem B3113579 : Blo 2075435 3113579 := bstep (se 1 (by rfl) ⟨2335184, by rfl⟩ : syracuseStep 3113579 = 4670369) B4670369
theorem B2075719 : Blo 2075435 2075719 := bstep (se 1 (by rfl) ⟨1556789, by rfl⟩ : syracuseStep 2075719 = 3113579) B3113579
theorem B2335189 : Blo 2075435 2335189 := bbase (se 7 (by rfl) ⟨27365, by rfl⟩ : syracuseStep 2335189 = 54731) (by norm_num)
theorem B3113585 : Blo 2075435 3113585 := bstep (se 2 (by rfl) ⟨1167594, by rfl⟩ : syracuseStep 3113585 = 2335189) B2335189
theorem B2075723 : Blo 2075435 2075723 := bstep (se 1 (by rfl) ⟨1556792, by rfl⟩ : syracuseStep 2075723 = 3113585) B3113585
theorem B2627093 : Blo 2075435 2627093 := bbase (se 6 (by rfl) ⟨61572, by rfl⟩ : syracuseStep 2627093 = 123145) (by norm_num)
theorem B7005581 : Blo 2075435 7005581 := bstep (se 3 (by rfl) ⟨1313546, by rfl⟩ : syracuseStep 7005581 = 2627093) B2627093
theorem B4670387 : Blo 2075435 4670387 := bstep (se 1 (by rfl) ⟨3502790, by rfl⟩ : syracuseStep 4670387 = 7005581) B7005581
theorem B3113591 : Blo 2075435 3113591 := bstep (se 1 (by rfl) ⟨2335193, by rfl⟩ : syracuseStep 3113591 = 4670387) B4670387
theorem B2075727 : Blo 2075435 2075727 := bstep (se 1 (by rfl) ⟨1556795, by rfl⟩ : syracuseStep 2075727 = 3113591) B3113591
theorem B3113597 : Blo 2075435 3113597 := bbase (se 3 (by rfl) ⟨583799, by rfl⟩ : syracuseStep 3113597 = 1167599) (by norm_num)
theorem B2075731 : Blo 2075435 2075731 := bstep (se 1 (by rfl) ⟨1556798, by rfl⟩ : syracuseStep 2075731 = 3113597) B3113597
theorem B4670405 : Blo 2075435 4670405 := bbase (se 4 (by rfl) ⟨437850, by rfl⟩ : syracuseStep 4670405 = 875701) (by norm_num)
theorem B3113603 : Blo 2075435 3113603 := bstep (se 1 (by rfl) ⟨2335202, by rfl⟩ : syracuseStep 3113603 = 4670405) B4670405
theorem B2075735 : Blo 2075435 2075735 := bstep (se 1 (by rfl) ⟨1556801, by rfl⟩ : syracuseStep 2075735 = 3113603) B3113603
theorem B2104061 : Blo 2075435 2104061 := bbase (se 3 (by rfl) ⟨394511, by rfl⟩ : syracuseStep 2104061 = 789023) (by norm_num)
theorem B5610829 : Blo 2075435 5610829 := bstep (se 3 (by rfl) ⟨1052030, by rfl⟩ : syracuseStep 5610829 = 2104061) B2104061
theorem B7481105 : Blo 2075435 7481105 := bstep (se 2 (by rfl) ⟨2805414, by rfl⟩ : syracuseStep 7481105 = 5610829) B5610829
theorem B4987403 : Blo 2075435 4987403 := bstep (se 1 (by rfl) ⟨3740552, by rfl⟩ : syracuseStep 4987403 = 7481105) B7481105
theorem B3324935 : Blo 2075435 3324935 := bstep (se 1 (by rfl) ⟨2493701, by rfl⟩ : syracuseStep 3324935 = 4987403) B4987403
theorem B8866493 : Blo 2075435 8866493 := bstep (se 3 (by rfl) ⟨1662467, by rfl⟩ : syracuseStep 8866493 = 3324935) B3324935
theorem B5910995 : Blo 2075435 5910995 := bstep (se 1 (by rfl) ⟨4433246, by rfl⟩ : syracuseStep 5910995 = 8866493) B8866493
theorem B3940663 : Blo 2075435 3940663 := bstep (se 1 (by rfl) ⟨2955497, by rfl⟩ : syracuseStep 3940663 = 5910995) B5910995
theorem B5254217 : Blo 2075435 5254217 := bstep (se 2 (by rfl) ⟨1970331, by rfl⟩ : syracuseStep 5254217 = 3940663) B3940663
theorem B3502811 : Blo 2075435 3502811 := bstep (se 1 (by rfl) ⟨2627108, by rfl⟩ : syracuseStep 3502811 = 5254217) B5254217
theorem B2335207 : Blo 2075435 2335207 := bstep (se 1 (by rfl) ⟨1751405, by rfl⟩ : syracuseStep 2335207 = 3502811) B3502811
theorem B3113609 : Blo 2075435 3113609 := bstep (se 2 (by rfl) ⟨1167603, by rfl⟩ : syracuseStep 3113609 = 2335207) B2335207
theorem B2075739 : Blo 2075435 2075739 := bstep (se 1 (by rfl) ⟨1556804, by rfl⟩ : syracuseStep 2075739 = 3113609) B3113609
theorem B10508453 : Blo 2075435 10508453 := bbase (se 4 (by rfl) ⟨985167, by rfl⟩ : syracuseStep 10508453 = 1970335) (by norm_num)
theorem B7005635 : Blo 2075435 7005635 := bstep (se 1 (by rfl) ⟨5254226, by rfl⟩ : syracuseStep 7005635 = 10508453) B10508453
theorem B4670423 : Blo 2075435 4670423 := bstep (se 1 (by rfl) ⟨3502817, by rfl⟩ : syracuseStep 4670423 = 7005635) B7005635
theorem B3113615 : Blo 2075435 3113615 := bstep (se 1 (by rfl) ⟨2335211, by rfl⟩ : syracuseStep 3113615 = 4670423) B4670423
theorem B2075743 : Blo 2075435 2075743 := bstep (se 1 (by rfl) ⟨1556807, by rfl⟩ : syracuseStep 2075743 = 3113615) B3113615
theorem B3113621 : Blo 2075435 3113621 := bbase (se 6 (by rfl) ⟨72975, by rfl⟩ : syracuseStep 3113621 = 145951) (by norm_num)
theorem B2075747 : Blo 2075435 2075747 := bstep (se 1 (by rfl) ⟨1556810, by rfl⟩ : syracuseStep 2075747 = 3113621) B3113621
theorem B7686677 : Blo 2075435 7686677 := bbase (se 6 (by rfl) ⟨180156, by rfl⟩ : syracuseStep 7686677 = 360313) (by norm_num)
theorem B20497805 : Blo 2075435 20497805 := bstep (se 3 (by rfl) ⟨3843338, by rfl⟩ : syracuseStep 20497805 = 7686677) B7686677
theorem B13665203 : Blo 2075435 13665203 := bstep (se 1 (by rfl) ⟨10248902, by rfl⟩ : syracuseStep 13665203 = 20497805) B20497805
theorem B9110135 : Blo 2075435 9110135 := bstep (se 1 (by rfl) ⟨6832601, by rfl⟩ : syracuseStep 9110135 = 13665203) B13665203
theorem B6073423 : Blo 2075435 6073423 := bstep (se 1 (by rfl) ⟨4555067, by rfl⟩ : syracuseStep 6073423 = 9110135) B9110135
theorem B32391589 : Blo 2075435 32391589 := bstep (se 4 (by rfl) ⟨3036711, by rfl⟩ : syracuseStep 32391589 = 6073423) B6073423
theorem B43188785 : Blo 2075435 43188785 := bstep (se 2 (by rfl) ⟨16195794, by rfl⟩ : syracuseStep 43188785 = 32391589) B32391589
theorem B28792523 : Blo 2075435 28792523 := bstep (se 1 (by rfl) ⟨21594392, by rfl⟩ : syracuseStep 28792523 = 43188785) B43188785
theorem B19195015 : Blo 2075435 19195015 := bstep (se 1 (by rfl) ⟨14396261, by rfl⟩ : syracuseStep 19195015 = 28792523) B28792523
theorem B25593353 : Blo 2075435 25593353 := bstep (se 2 (by rfl) ⟨9597507, by rfl⟩ : syracuseStep 25593353 = 19195015) B19195015
theorem B17062235 : Blo 2075435 17062235 := bstep (se 1 (by rfl) ⟨12796676, by rfl⟩ : syracuseStep 17062235 = 25593353) B25593353
theorem B11374823 : Blo 2075435 11374823 := bstep (se 1 (by rfl) ⟨8531117, by rfl⟩ : syracuseStep 11374823 = 17062235) B17062235
theorem B7583215 : Blo 2075435 7583215 := bstep (se 1 (by rfl) ⟨5687411, by rfl⟩ : syracuseStep 7583215 = 11374823) B11374823
theorem B10110953 : Blo 2075435 10110953 := bstep (se 2 (by rfl) ⟨3791607, by rfl⟩ : syracuseStep 10110953 = 7583215) B7583215
theorem B26962541 : Blo 2075435 26962541 := bstep (se 3 (by rfl) ⟨5055476, by rfl⟩ : syracuseStep 26962541 = 10110953) B10110953
theorem B17975027 : Blo 2075435 17975027 := bstep (se 1 (by rfl) ⟨13481270, by rfl⟩ : syracuseStep 17975027 = 26962541) B26962541
theorem B11983351 : Blo 2075435 11983351 := bstep (se 1 (by rfl) ⟨8987513, by rfl⟩ : syracuseStep 11983351 = 17975027) B17975027
theorem B15977801 : Blo 2075435 15977801 := bstep (se 2 (by rfl) ⟨5991675, by rfl⟩ : syracuseStep 15977801 = 11983351) B11983351
theorem B10651867 : Blo 2075435 10651867 := bstep (se 1 (by rfl) ⟨7988900, by rfl⟩ : syracuseStep 10651867 = 15977801) B15977801
theorem B56809957 : Blo 2075435 56809957 := bstep (se 4 (by rfl) ⟨5325933, by rfl⟩ : syracuseStep 56809957 = 10651867) B10651867
theorem B75746609 : Blo 2075435 75746609 := bstep (se 2 (by rfl) ⟨28404978, by rfl⟩ : syracuseStep 75746609 = 56809957) B56809957
theorem B50497739 : Blo 2075435 50497739 := bstep (se 1 (by rfl) ⟨37873304, by rfl⟩ : syracuseStep 50497739 = 75746609) B75746609
theorem B33665159 : Blo 2075435 33665159 := bstep (se 1 (by rfl) ⟨25248869, by rfl⟩ : syracuseStep 33665159 = 50497739) B50497739
theorem B22443439 : Blo 2075435 22443439 := bstep (se 1 (by rfl) ⟨16832579, by rfl⟩ : syracuseStep 22443439 = 33665159) B33665159
theorem B29924585 : Blo 2075435 29924585 := bstep (se 2 (by rfl) ⟨11221719, by rfl⟩ : syracuseStep 29924585 = 22443439) B22443439
theorem B19949723 : Blo 2075435 19949723 := bstep (se 1 (by rfl) ⟨14962292, by rfl⟩ : syracuseStep 19949723 = 29924585) B29924585
theorem B13299815 : Blo 2075435 13299815 := bstep (se 1 (by rfl) ⟨9974861, by rfl⟩ : syracuseStep 13299815 = 19949723) B19949723
theorem B8866543 : Blo 2075435 8866543 := bstep (se 1 (by rfl) ⟨6649907, by rfl⟩ : syracuseStep 8866543 = 13299815) B13299815
theorem B11822057 : Blo 2075435 11822057 := bstep (se 2 (by rfl) ⟨4433271, by rfl⟩ : syracuseStep 11822057 = 8866543) B8866543
theorem B7881371 : Blo 2075435 7881371 := bstep (se 1 (by rfl) ⟨5911028, by rfl⟩ : syracuseStep 7881371 = 11822057) B11822057
theorem B5254247 : Blo 2075435 5254247 := bstep (se 1 (by rfl) ⟨3940685, by rfl⟩ : syracuseStep 5254247 = 7881371) B7881371
theorem B3502831 : Blo 2075435 3502831 := bstep (se 1 (by rfl) ⟨2627123, by rfl⟩ : syracuseStep 3502831 = 5254247) B5254247
theorem B4670441 : Blo 2075435 4670441 := bstep (se 2 (by rfl) ⟨1751415, by rfl⟩ : syracuseStep 4670441 = 3502831) B3502831
theorem B3113627 : Blo 2075435 3113627 := bstep (se 1 (by rfl) ⟨2335220, by rfl⟩ : syracuseStep 3113627 = 4670441) B4670441
theorem B2075751 : Blo 2075435 2075751 := bstep (se 1 (by rfl) ⟨1556813, by rfl⟩ : syracuseStep 2075751 = 3113627) B3113627
theorem B2335225 : Blo 2075435 2335225 := bbase (se 2 (by rfl) ⟨875709, by rfl⟩ : syracuseStep 2335225 = 1751419) (by norm_num)
theorem B3113633 : Blo 2075435 3113633 := bstep (se 2 (by rfl) ⟨1167612, by rfl⟩ : syracuseStep 3113633 = 2335225) B2335225
theorem B2075755 : Blo 2075435 2075755 := bstep (se 1 (by rfl) ⟨1556816, by rfl⟩ : syracuseStep 2075755 = 3113633) B3113633
theorem B2493725 : Blo 2075435 2493725 := bbase (se 3 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 2493725 = 935147) (by norm_num)
theorem B6649933 : Blo 2075435 6649933 := bstep (se 3 (by rfl) ⟨1246862, by rfl⟩ : syracuseStep 6649933 = 2493725) B2493725
theorem B8866577 : Blo 2075435 8866577 := bstep (se 2 (by rfl) ⟨3324966, by rfl⟩ : syracuseStep 8866577 = 6649933) B6649933
theorem B5911051 : Blo 2075435 5911051 := bstep (se 1 (by rfl) ⟨4433288, by rfl⟩ : syracuseStep 5911051 = 8866577) B8866577
theorem B7881401 : Blo 2075435 7881401 := bstep (se 2 (by rfl) ⟨2955525, by rfl⟩ : syracuseStep 7881401 = 5911051) B5911051
theorem B5254267 : Blo 2075435 5254267 := bstep (se 1 (by rfl) ⟨3940700, by rfl⟩ : syracuseStep 5254267 = 7881401) B7881401
theorem B7005689 : Blo 2075435 7005689 := bstep (se 2 (by rfl) ⟨2627133, by rfl⟩ : syracuseStep 7005689 = 5254267) B5254267
theorem B4670459 : Blo 2075435 4670459 := bstep (se 1 (by rfl) ⟨3502844, by rfl⟩ : syracuseStep 4670459 = 7005689) B7005689
theorem B3113639 : Blo 2075435 3113639 := bstep (se 1 (by rfl) ⟨2335229, by rfl⟩ : syracuseStep 3113639 = 4670459) B4670459
theorem B2075759 : Blo 2075435 2075759 := bstep (se 1 (by rfl) ⟨1556819, by rfl⟩ : syracuseStep 2075759 = 3113639) B3113639
theorem B3113645 : Blo 2075435 3113645 := bbase (se 3 (by rfl) ⟨583808, by rfl⟩ : syracuseStep 3113645 = 1167617) (by norm_num)
theorem B2075763 : Blo 2075435 2075763 := bstep (se 1 (by rfl) ⟨1556822, by rfl⟩ : syracuseStep 2075763 = 3113645) B3113645
theorem B4670477 : Blo 2075435 4670477 := bbase (se 3 (by rfl) ⟨875714, by rfl⟩ : syracuseStep 4670477 = 1751429) (by norm_num)
theorem B3113651 : Blo 2075435 3113651 := bstep (se 1 (by rfl) ⟨2335238, by rfl⟩ : syracuseStep 3113651 = 4670477) B4670477
theorem B2075767 : Blo 2075435 2075767 := bstep (se 1 (by rfl) ⟨1556825, by rfl⟩ : syracuseStep 2075767 = 3113651) B3113651
theorem B2627149 : Blo 2075435 2627149 := bbase (se 3 (by rfl) ⟨492590, by rfl⟩ : syracuseStep 2627149 = 985181) (by norm_num)
theorem B3502865 : Blo 2075435 3502865 := bstep (se 2 (by rfl) ⟨1313574, by rfl⟩ : syracuseStep 3502865 = 2627149) B2627149
theorem B2335243 : Blo 2075435 2335243 := bstep (se 1 (by rfl) ⟨1751432, by rfl⟩ : syracuseStep 2335243 = 3502865) B3502865
theorem B3113657 : Blo 2075435 3113657 := bstep (se 2 (by rfl) ⟨1167621, by rfl⟩ : syracuseStep 3113657 = 2335243) B2335243
theorem B2075771 : Blo 2075435 2075771 := bstep (se 1 (by rfl) ⟨1556828, by rfl⟩ : syracuseStep 2075771 = 3113657) B3113657
theorem B5124509 : Blo 2075435 5124509 := bbase (se 3 (by rfl) ⟨960845, by rfl⟩ : syracuseStep 5124509 = 1921691) (by norm_num)
theorem B3416339 : Blo 2075435 3416339 := bstep (se 1 (by rfl) ⟨2562254, by rfl⟩ : syracuseStep 3416339 = 5124509) B5124509
theorem B9110237 : Blo 2075435 9110237 := bstep (se 3 (by rfl) ⟨1708169, by rfl⟩ : syracuseStep 9110237 = 3416339) B3416339
theorem B24293965 : Blo 2075435 24293965 := bstep (se 3 (by rfl) ⟨4555118, by rfl⟩ : syracuseStep 24293965 = 9110237) B9110237
theorem B32391953 : Blo 2075435 32391953 := bstep (se 2 (by rfl) ⟨12146982, by rfl⟩ : syracuseStep 32391953 = 24293965) B24293965
theorem B21594635 : Blo 2075435 21594635 := bstep (se 1 (by rfl) ⟨16195976, by rfl⟩ : syracuseStep 21594635 = 32391953) B32391953
theorem B14396423 : Blo 2075435 14396423 := bstep (se 1 (by rfl) ⟨10797317, by rfl⟩ : syracuseStep 14396423 = 21594635) B21594635
theorem B153561845 : Blo 2075435 153561845 := bstep (se 5 (by rfl) ⟨7198211, by rfl⟩ : syracuseStep 153561845 = 14396423) B14396423
theorem B409498253 : Blo 2075435 409498253 := bstep (se 3 (by rfl) ⟨76780922, by rfl⟩ : syracuseStep 409498253 = 153561845) B153561845
theorem B272998835 : Blo 2075435 272998835 := bstep (se 1 (by rfl) ⟨204749126, by rfl⟩ : syracuseStep 272998835 = 409498253) B409498253
theorem B181999223 : Blo 2075435 181999223 := bstep (se 1 (by rfl) ⟨136499417, by rfl⟩ : syracuseStep 181999223 = 272998835) B272998835
theorem B121332815 : Blo 2075435 121332815 := bstep (se 1 (by rfl) ⟨90999611, by rfl⟩ : syracuseStep 121332815 = 181999223) B181999223
theorem B80888543 : Blo 2075435 80888543 := bstep (se 1 (by rfl) ⟨60666407, by rfl⟩ : syracuseStep 80888543 = 121332815) B121332815
theorem B53925695 : Blo 2075435 53925695 := bstep (se 1 (by rfl) ⟨40444271, by rfl⟩ : syracuseStep 53925695 = 80888543) B80888543
theorem B35950463 : Blo 2075435 35950463 := bstep (se 1 (by rfl) ⟨26962847, by rfl⟩ : syracuseStep 35950463 = 53925695) B53925695
theorem B23966975 : Blo 2075435 23966975 := bstep (se 1 (by rfl) ⟨17975231, by rfl⟩ : syracuseStep 23966975 = 35950463) B35950463
theorem B15977983 : Blo 2075435 15977983 := bstep (se 1 (by rfl) ⟨11983487, by rfl⟩ : syracuseStep 15977983 = 23966975) B23966975
theorem B21303977 : Blo 2075435 21303977 := bstep (se 2 (by rfl) ⟨7988991, by rfl⟩ : syracuseStep 21303977 = 15977983) B15977983
theorem B227242421 : Blo 2075435 227242421 := bstep (se 5 (by rfl) ⟨10651988, by rfl⟩ : syracuseStep 227242421 = 21303977) B21303977
theorem B151494947 : Blo 2075435 151494947 := bstep (se 1 (by rfl) ⟨113621210, by rfl⟩ : syracuseStep 151494947 = 227242421) B227242421
theorem B100996631 : Blo 2075435 100996631 := bstep (se 1 (by rfl) ⟨75747473, by rfl⟩ : syracuseStep 100996631 = 151494947) B151494947
theorem B67331087 : Blo 2075435 67331087 := bstep (se 1 (by rfl) ⟨50498315, by rfl⟩ : syracuseStep 67331087 = 100996631) B100996631
theorem B44887391 : Blo 2075435 44887391 := bstep (se 1 (by rfl) ⟨33665543, by rfl⟩ : syracuseStep 44887391 = 67331087) B67331087
theorem B29924927 : Blo 2075435 29924927 := bstep (se 1 (by rfl) ⟨22443695, by rfl⟩ : syracuseStep 29924927 = 44887391) B44887391
theorem B19949951 : Blo 2075435 19949951 := bstep (se 1 (by rfl) ⟨14962463, by rfl⟩ : syracuseStep 19949951 = 29924927) B29924927
theorem B13299967 : Blo 2075435 13299967 := bstep (se 1 (by rfl) ⟨9974975, by rfl⟩ : syracuseStep 13299967 = 19949951) B19949951
theorem B17733289 : Blo 2075435 17733289 := bstep (se 2 (by rfl) ⟨6649983, by rfl⟩ : syracuseStep 17733289 = 13299967) B13299967
theorem B23644385 : Blo 2075435 23644385 := bstep (se 2 (by rfl) ⟨8866644, by rfl⟩ : syracuseStep 23644385 = 17733289) B17733289
theorem B15762923 : Blo 2075435 15762923 := bstep (se 1 (by rfl) ⟨11822192, by rfl⟩ : syracuseStep 15762923 = 23644385) B23644385
theorem B10508615 : Blo 2075435 10508615 := bstep (se 1 (by rfl) ⟨7881461, by rfl⟩ : syracuseStep 10508615 = 15762923) B15762923
theorem B7005743 : Blo 2075435 7005743 := bstep (se 1 (by rfl) ⟨5254307, by rfl⟩ : syracuseStep 7005743 = 10508615) B10508615
theorem B4670495 : Blo 2075435 4670495 := bstep (se 1 (by rfl) ⟨3502871, by rfl⟩ : syracuseStep 4670495 = 7005743) B7005743
theorem B3113663 : Blo 2075435 3113663 := bstep (se 1 (by rfl) ⟨2335247, by rfl⟩ : syracuseStep 3113663 = 4670495) B4670495
theorem B2075775 : Blo 2075435 2075775 := bstep (se 1 (by rfl) ⟨1556831, by rfl⟩ : syracuseStep 2075775 = 3113663) B3113663
theorem B3113669 : Blo 2075435 3113669 := bbase (se 4 (by rfl) ⟨291906, by rfl⟩ : syracuseStep 3113669 = 583813) (by norm_num)
theorem B2075779 : Blo 2075435 2075779 := bstep (se 1 (by rfl) ⟨1556834, by rfl⟩ : syracuseStep 2075779 = 3113669) B3113669
theorem B3502885 : Blo 2075435 3502885 := bbase (se 4 (by rfl) ⟨328395, by rfl⟩ : syracuseStep 3502885 = 656791) (by norm_num)
theorem B4670513 : Blo 2075435 4670513 := bstep (se 2 (by rfl) ⟨1751442, by rfl⟩ : syracuseStep 4670513 = 3502885) B3502885
theorem B3113675 : Blo 2075435 3113675 := bstep (se 1 (by rfl) ⟨2335256, by rfl⟩ : syracuseStep 3113675 = 4670513) B4670513
theorem B2075783 : Blo 2075435 2075783 := bstep (se 1 (by rfl) ⟨1556837, by rfl⟩ : syracuseStep 2075783 = 3113675) B3113675
theorem B2335261 : Blo 2075435 2335261 := bbase (se 3 (by rfl) ⟨437861, by rfl⟩ : syracuseStep 2335261 = 875723) (by norm_num)
theorem B3113681 : Blo 2075435 3113681 := bstep (se 2 (by rfl) ⟨1167630, by rfl⟩ : syracuseStep 3113681 = 2335261) B2335261
theorem B2075787 : Blo 2075435 2075787 := bstep (se 1 (by rfl) ⟨1556840, by rfl⟩ : syracuseStep 2075787 = 3113681) B3113681
theorem B7005797 : Blo 2075435 7005797 := bbase (se 4 (by rfl) ⟨656793, by rfl⟩ : syracuseStep 7005797 = 1313587) (by norm_num)
theorem B4670531 : Blo 2075435 4670531 := bstep (se 1 (by rfl) ⟨3502898, by rfl⟩ : syracuseStep 4670531 = 7005797) B7005797
theorem B3113687 : Blo 2075435 3113687 := bstep (se 1 (by rfl) ⟨2335265, by rfl⟩ : syracuseStep 3113687 = 4670531) B4670531
theorem B2075791 : Blo 2075435 2075791 := bstep (se 1 (by rfl) ⟨1556843, by rfl⟩ : syracuseStep 2075791 = 3113687) B3113687
theorem B3113693 : Blo 2075435 3113693 := bbase (se 3 (by rfl) ⟨583817, by rfl⟩ : syracuseStep 3113693 = 1167635) (by norm_num)
theorem B2075795 : Blo 2075435 2075795 := bstep (se 1 (by rfl) ⟨1556846, by rfl⟩ : syracuseStep 2075795 = 3113693) B3113693
theorem B4670549 : Blo 2075435 4670549 := bbase (se 8 (by rfl) ⟨27366, by rfl⟩ : syracuseStep 4670549 = 54733) (by norm_num)
theorem B3113699 : Blo 2075435 3113699 := bstep (se 1 (by rfl) ⟨2335274, by rfl⟩ : syracuseStep 3113699 = 4670549) B4670549
theorem B2075799 : Blo 2075435 2075799 := bstep (se 1 (by rfl) ⟨1556849, by rfl⟩ : syracuseStep 2075799 = 3113699) B3113699
theorem B5326069 : Blo 2075435 5326069 := bbase (se 5 (by rfl) ⟨249659, by rfl⟩ : syracuseStep 5326069 = 499319) (by norm_num)
theorem B7101425 : Blo 2075435 7101425 := bstep (se 2 (by rfl) ⟨2663034, by rfl⟩ : syracuseStep 7101425 = 5326069) B5326069
theorem B4734283 : Blo 2075435 4734283 := bstep (se 1 (by rfl) ⟨3550712, by rfl⟩ : syracuseStep 4734283 = 7101425) B7101425
theorem B6312377 : Blo 2075435 6312377 := bstep (se 2 (by rfl) ⟨2367141, by rfl⟩ : syracuseStep 6312377 = 4734283) B4734283
theorem B16833005 : Blo 2075435 16833005 := bstep (se 3 (by rfl) ⟨3156188, by rfl⟩ : syracuseStep 16833005 = 6312377) B6312377
theorem B11222003 : Blo 2075435 11222003 := bstep (se 1 (by rfl) ⟨8416502, by rfl⟩ : syracuseStep 11222003 = 16833005) B16833005
theorem B7481335 : Blo 2075435 7481335 := bstep (se 1 (by rfl) ⟨5611001, by rfl⟩ : syracuseStep 7481335 = 11222003) B11222003
theorem B9975113 : Blo 2075435 9975113 := bstep (se 2 (by rfl) ⟨3740667, by rfl⟩ : syracuseStep 9975113 = 7481335) B7481335
theorem B6650075 : Blo 2075435 6650075 := bstep (se 1 (by rfl) ⟨4987556, by rfl⟩ : syracuseStep 6650075 = 9975113) B9975113
theorem B4433383 : Blo 2075435 4433383 := bstep (se 1 (by rfl) ⟨3325037, by rfl⟩ : syracuseStep 4433383 = 6650075) B6650075
theorem B5911177 : Blo 2075435 5911177 := bstep (se 2 (by rfl) ⟨2216691, by rfl⟩ : syracuseStep 5911177 = 4433383) B4433383
theorem B7881569 : Blo 2075435 7881569 := bstep (se 2 (by rfl) ⟨2955588, by rfl⟩ : syracuseStep 7881569 = 5911177) B5911177
theorem B5254379 : Blo 2075435 5254379 := bstep (se 1 (by rfl) ⟨3940784, by rfl⟩ : syracuseStep 5254379 = 7881569) B7881569
theorem B3502919 : Blo 2075435 3502919 := bstep (se 1 (by rfl) ⟨2627189, by rfl⟩ : syracuseStep 3502919 = 5254379) B5254379
theorem B2335279 : Blo 2075435 2335279 := bstep (se 1 (by rfl) ⟨1751459, by rfl⟩ : syracuseStep 2335279 = 3502919) B3502919
theorem B3113705 : Blo 2075435 3113705 := bstep (se 2 (by rfl) ⟨1167639, by rfl⟩ : syracuseStep 3113705 = 2335279) B2335279
theorem B2075803 : Blo 2075435 2075803 := bstep (se 1 (by rfl) ⟨1556852, by rfl⟩ : syracuseStep 2075803 = 3113705) B3113705
theorem B2104129 : Blo 2075435 2104129 := bbase (se 2 (by rfl) ⟨789048, by rfl⟩ : syracuseStep 2104129 = 1578097) (by norm_num)
theorem B11222021 : Blo 2075435 11222021 := bstep (se 4 (by rfl) ⟨1052064, by rfl⟩ : syracuseStep 11222021 = 2104129) B2104129
theorem B29925389 : Blo 2075435 29925389 := bstep (se 3 (by rfl) ⟨5611010, by rfl⟩ : syracuseStep 29925389 = 11222021) B11222021
theorem B19950259 : Blo 2075435 19950259 := bstep (se 1 (by rfl) ⟨14962694, by rfl⟩ : syracuseStep 19950259 = 29925389) B29925389
theorem B26600345 : Blo 2075435 26600345 := bstep (se 2 (by rfl) ⟨9975129, by rfl⟩ : syracuseStep 26600345 = 19950259) B19950259
theorem B17733563 : Blo 2075435 17733563 := bstep (se 1 (by rfl) ⟨13300172, by rfl⟩ : syracuseStep 17733563 = 26600345) B26600345
theorem B11822375 : Blo 2075435 11822375 := bstep (se 1 (by rfl) ⟨8866781, by rfl⟩ : syracuseStep 11822375 = 17733563) B17733563
theorem B7881583 : Blo 2075435 7881583 := bstep (se 1 (by rfl) ⟨5911187, by rfl⟩ : syracuseStep 7881583 = 11822375) B11822375
theorem B10508777 : Blo 2075435 10508777 := bstep (se 2 (by rfl) ⟨3940791, by rfl⟩ : syracuseStep 10508777 = 7881583) B7881583
theorem B7005851 : Blo 2075435 7005851 := bstep (se 1 (by rfl) ⟨5254388, by rfl⟩ : syracuseStep 7005851 = 10508777) B10508777
theorem B4670567 : Blo 2075435 4670567 := bstep (se 1 (by rfl) ⟨3502925, by rfl⟩ : syracuseStep 4670567 = 7005851) B7005851
theorem B3113711 : Blo 2075435 3113711 := bstep (se 1 (by rfl) ⟨2335283, by rfl⟩ : syracuseStep 3113711 = 4670567) B4670567
theorem B2075807 : Blo 2075435 2075807 := bstep (se 1 (by rfl) ⟨1556855, by rfl⟩ : syracuseStep 2075807 = 3113711) B3113711
theorem B3113717 : Blo 2075435 3113717 := bbase (se 5 (by rfl) ⟨145955, by rfl⟩ : syracuseStep 3113717 = 291911) (by norm_num)
theorem B2075811 : Blo 2075435 2075811 := bstep (se 1 (by rfl) ⟨1556858, by rfl⟩ : syracuseStep 2075811 = 3113717) B3113717
theorem B2805517 : Blo 2075435 2805517 := bbase (se 3 (by rfl) ⟨526034, by rfl⟩ : syracuseStep 2805517 = 1052069) (by norm_num)
theorem B3740689 : Blo 2075435 3740689 := bstep (se 2 (by rfl) ⟨1402758, by rfl⟩ : syracuseStep 3740689 = 2805517) B2805517
theorem B4987585 : Blo 2075435 4987585 := bstep (se 2 (by rfl) ⟨1870344, by rfl⟩ : syracuseStep 4987585 = 3740689) B3740689
theorem B6650113 : Blo 2075435 6650113 := bstep (se 2 (by rfl) ⟨2493792, by rfl⟩ : syracuseStep 6650113 = 4987585) B4987585
theorem B8866817 : Blo 2075435 8866817 := bstep (se 2 (by rfl) ⟨3325056, by rfl⟩ : syracuseStep 8866817 = 6650113) B6650113
theorem B5911211 : Blo 2075435 5911211 := bstep (se 1 (by rfl) ⟨4433408, by rfl⟩ : syracuseStep 5911211 = 8866817) B8866817
theorem B3940807 : Blo 2075435 3940807 := bstep (se 1 (by rfl) ⟨2955605, by rfl⟩ : syracuseStep 3940807 = 5911211) B5911211
theorem B5254409 : Blo 2075435 5254409 := bstep (se 2 (by rfl) ⟨1970403, by rfl⟩ : syracuseStep 5254409 = 3940807) B3940807
theorem B3502939 : Blo 2075435 3502939 := bstep (se 1 (by rfl) ⟨2627204, by rfl⟩ : syracuseStep 3502939 = 5254409) B5254409
theorem B4670585 : Blo 2075435 4670585 := bstep (se 2 (by rfl) ⟨1751469, by rfl⟩ : syracuseStep 4670585 = 3502939) B3502939
theorem B3113723 : Blo 2075435 3113723 := bstep (se 1 (by rfl) ⟨2335292, by rfl⟩ : syracuseStep 3113723 = 4670585) B4670585
theorem B2075815 : Blo 2075435 2075815 := bstep (se 1 (by rfl) ⟨1556861, by rfl⟩ : syracuseStep 2075815 = 3113723) B3113723
theorem B2335297 : Blo 2075435 2335297 := bbase (se 2 (by rfl) ⟨875736, by rfl⟩ : syracuseStep 2335297 = 1751473) (by norm_num)
theorem B3113729 : Blo 2075435 3113729 := bstep (se 2 (by rfl) ⟨1167648, by rfl⟩ : syracuseStep 3113729 = 2335297) B2335297
theorem B2075819 : Blo 2075435 2075819 := bstep (se 1 (by rfl) ⟨1556864, by rfl⟩ : syracuseStep 2075819 = 3113729) B3113729
theorem B5254429 : Blo 2075435 5254429 := bbase (se 3 (by rfl) ⟨985205, by rfl⟩ : syracuseStep 5254429 = 1970411) (by norm_num)
theorem B7005905 : Blo 2075435 7005905 := bstep (se 2 (by rfl) ⟨2627214, by rfl⟩ : syracuseStep 7005905 = 5254429) B5254429
theorem B4670603 : Blo 2075435 4670603 := bstep (se 1 (by rfl) ⟨3502952, by rfl⟩ : syracuseStep 4670603 = 7005905) B7005905
theorem B3113735 : Blo 2075435 3113735 := bstep (se 1 (by rfl) ⟨2335301, by rfl⟩ : syracuseStep 3113735 = 4670603) B4670603
theorem B2075823 : Blo 2075435 2075823 := bstep (se 1 (by rfl) ⟨1556867, by rfl⟩ : syracuseStep 2075823 = 3113735) B3113735
theorem B3113741 : Blo 2075435 3113741 := bbase (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) (by norm_num)
theorem B2075827 : Blo 2075435 2075827 := bstep (se 1 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 2075827 = 3113741) B3113741
theorem B4670621 : Blo 2075435 4670621 := bbase (se 3 (by rfl) ⟨875741, by rfl⟩ : syracuseStep 4670621 = 1751483) (by norm_num)
theorem B3113747 : Blo 2075435 3113747 := bstep (se 1 (by rfl) ⟨2335310, by rfl⟩ : syracuseStep 3113747 = 4670621) B4670621
theorem B2075831 : Blo 2075435 2075831 := bstep (se 1 (by rfl) ⟨1556873, by rfl⟩ : syracuseStep 2075831 = 3113747) B3113747
theorem B3502973 : Blo 2075435 3502973 := bbase (se 3 (by rfl) ⟨656807, by rfl⟩ : syracuseStep 3502973 = 1313615) (by norm_num)
theorem B2335315 : Blo 2075435 2335315 := bstep (se 1 (by rfl) ⟨1751486, by rfl⟩ : syracuseStep 2335315 = 3502973) B3502973
theorem B3113753 : Blo 2075435 3113753 := bstep (se 2 (by rfl) ⟨1167657, by rfl⟩ : syracuseStep 3113753 = 2335315) B2335315
theorem B2075835 : Blo 2075435 2075835 := bstep (se 1 (by rfl) ⟨1556876, by rfl⟩ : syracuseStep 2075835 = 3113753) B3113753
theorem B2493821 : Blo 2075435 2493821 := bbase (se 3 (by rfl) ⟨467591, by rfl⟩ : syracuseStep 2493821 = 935183) (by norm_num)
theorem B6650189 : Blo 2075435 6650189 := bstep (se 3 (by rfl) ⟨1246910, by rfl⟩ : syracuseStep 6650189 = 2493821) B2493821
theorem B4433459 : Blo 2075435 4433459 := bstep (se 1 (by rfl) ⟨3325094, by rfl⟩ : syracuseStep 4433459 = 6650189) B6650189
theorem B11822557 : Blo 2075435 11822557 := bstep (se 3 (by rfl) ⟨2216729, by rfl⟩ : syracuseStep 11822557 = 4433459) B4433459
theorem B15763409 : Blo 2075435 15763409 := bstep (se 2 (by rfl) ⟨5911278, by rfl⟩ : syracuseStep 15763409 = 11822557) B11822557
theorem B10508939 : Blo 2075435 10508939 := bstep (se 1 (by rfl) ⟨7881704, by rfl⟩ : syracuseStep 10508939 = 15763409) B15763409
theorem B7005959 : Blo 2075435 7005959 := bstep (se 1 (by rfl) ⟨5254469, by rfl⟩ : syracuseStep 7005959 = 10508939) B10508939
theorem B4670639 : Blo 2075435 4670639 := bstep (se 1 (by rfl) ⟨3502979, by rfl⟩ : syracuseStep 4670639 = 7005959) B7005959
theorem B3113759 : Blo 2075435 3113759 := bstep (se 1 (by rfl) ⟨2335319, by rfl⟩ : syracuseStep 3113759 = 4670639) B4670639
theorem B2075839 : Blo 2075435 2075839 := bstep (se 1 (by rfl) ⟨1556879, by rfl⟩ : syracuseStep 2075839 = 3113759) B3113759
theorem B3113765 : Blo 2075435 3113765 := bbase (se 4 (by rfl) ⟨291915, by rfl⟩ : syracuseStep 3113765 = 583831) (by norm_num)
theorem B2075843 : Blo 2075435 2075843 := bstep (se 1 (by rfl) ⟨1556882, by rfl⟩ : syracuseStep 2075843 = 3113765) B3113765
theorem B2627245 : Blo 2075435 2627245 := bbase (se 3 (by rfl) ⟨492608, by rfl⟩ : syracuseStep 2627245 = 985217) (by norm_num)
theorem B3502993 : Blo 2075435 3502993 := bstep (se 2 (by rfl) ⟨1313622, by rfl⟩ : syracuseStep 3502993 = 2627245) B2627245
theorem B4670657 : Blo 2075435 4670657 := bstep (se 2 (by rfl) ⟨1751496, by rfl⟩ : syracuseStep 4670657 = 3502993) B3502993
theorem B3113771 : Blo 2075435 3113771 := bstep (se 1 (by rfl) ⟨2335328, by rfl⟩ : syracuseStep 3113771 = 4670657) B4670657
theorem B2075847 : Blo 2075435 2075847 := bstep (se 1 (by rfl) ⟨1556885, by rfl⟩ : syracuseStep 2075847 = 3113771) B3113771
theorem B2335333 : Blo 2075435 2335333 := bbase (se 4 (by rfl) ⟨218937, by rfl⟩ : syracuseStep 2335333 = 437875) (by norm_num)
theorem B3113777 : Blo 2075435 3113777 := bstep (se 2 (by rfl) ⟨1167666, by rfl⟩ : syracuseStep 3113777 = 2335333) B2335333
theorem B2075851 : Blo 2075435 2075851 := bstep (se 1 (by rfl) ⟨1556888, by rfl⟩ : syracuseStep 2075851 = 3113777) B3113777
theorem B2493841 : Blo 2075435 2493841 := bbase (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) (by norm_num)
theorem B3325121 : Blo 2075435 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B2216747 : Blo 2075435 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B5911325 : Blo 2075435 5911325 := bstep (se 3 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 5911325 = 2216747) B2216747
theorem B3940883 : Blo 2075435 3940883 := bstep (se 1 (by rfl) ⟨2955662, by rfl⟩ : syracuseStep 3940883 = 5911325) B5911325
theorem B2627255 : Blo 2075435 2627255 := bstep (se 1 (by rfl) ⟨1970441, by rfl⟩ : syracuseStep 2627255 = 3940883) B3940883
theorem B7006013 : Blo 2075435 7006013 := bstep (se 3 (by rfl) ⟨1313627, by rfl⟩ : syracuseStep 7006013 = 2627255) B2627255
theorem B4670675 : Blo 2075435 4670675 := bstep (se 1 (by rfl) ⟨3503006, by rfl⟩ : syracuseStep 4670675 = 7006013) B7006013
theorem B3113783 : Blo 2075435 3113783 := bstep (se 1 (by rfl) ⟨2335337, by rfl⟩ : syracuseStep 3113783 = 4670675) B4670675
theorem B2075855 : Blo 2075435 2075855 := bstep (se 1 (by rfl) ⟨1556891, by rfl⟩ : syracuseStep 2075855 = 3113783) B3113783
theorem B3113789 : Blo 2075435 3113789 := bbase (se 3 (by rfl) ⟨583835, by rfl⟩ : syracuseStep 3113789 = 1167671) (by norm_num)
theorem B2075859 : Blo 2075435 2075859 := bstep (se 1 (by rfl) ⟨1556894, by rfl⟩ : syracuseStep 2075859 = 3113789) B3113789
theorem B4670693 : Blo 2075435 4670693 := bbase (se 4 (by rfl) ⟨437877, by rfl⟩ : syracuseStep 4670693 = 875755) (by norm_num)
theorem B3113795 : Blo 2075435 3113795 := bstep (se 1 (by rfl) ⟨2335346, by rfl⟩ : syracuseStep 3113795 = 4670693) B4670693
theorem B2075863 : Blo 2075435 2075863 := bstep (se 1 (by rfl) ⟨1556897, by rfl⟩ : syracuseStep 2075863 = 3113795) B3113795
theorem B5254541 : Blo 2075435 5254541 := bbase (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) (by norm_num)
theorem B3503027 : Blo 2075435 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B2335351 : Blo 2075435 2335351 := bstep (se 1 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 2335351 = 3503027) B3503027
theorem B3113801 : Blo 2075435 3113801 := bstep (se 2 (by rfl) ⟨1167675, by rfl⟩ : syracuseStep 3113801 = 2335351) B2335351
theorem B2075867 : Blo 2075435 2075867 := bstep (se 1 (by rfl) ⟨1556900, by rfl⟩ : syracuseStep 2075867 = 3113801) B3113801
theorem B2955685 : Blo 2075435 2955685 := bbase (se 4 (by rfl) ⟨277095, by rfl⟩ : syracuseStep 2955685 = 554191) (by norm_num)
theorem B3940913 : Blo 2075435 3940913 := bstep (se 2 (by rfl) ⟨1477842, by rfl⟩ : syracuseStep 3940913 = 2955685) B2955685
theorem B10509101 : Blo 2075435 10509101 := bstep (se 3 (by rfl) ⟨1970456, by rfl⟩ : syracuseStep 10509101 = 3940913) B3940913
theorem B7006067 : Blo 2075435 7006067 := bstep (se 1 (by rfl) ⟨5254550, by rfl⟩ : syracuseStep 7006067 = 10509101) B10509101
theorem B4670711 : Blo 2075435 4670711 := bstep (se 1 (by rfl) ⟨3503033, by rfl⟩ : syracuseStep 4670711 = 7006067) B7006067
theorem B3113807 : Blo 2075435 3113807 := bstep (se 1 (by rfl) ⟨2335355, by rfl⟩ : syracuseStep 3113807 = 4670711) B4670711
theorem B2075871 : Blo 2075435 2075871 := bstep (se 1 (by rfl) ⟨1556903, by rfl⟩ : syracuseStep 2075871 = 3113807) B3113807
theorem B3113813 : Blo 2075435 3113813 := bbase (se 9 (by rfl) ⟨9122, by rfl⟩ : syracuseStep 3113813 = 18245) (by norm_num)
theorem B2075875 : Blo 2075435 2075875 := bstep (se 1 (by rfl) ⟨1556906, by rfl⟩ : syracuseStep 2075875 = 3113813) B3113813
theorem B7101685 : Blo 2075435 7101685 := bbase (se 5 (by rfl) ⟨332891, by rfl⟩ : syracuseStep 7101685 = 665783) (by norm_num)
theorem B9468913 : Blo 2075435 9468913 := bstep (se 2 (by rfl) ⟨3550842, by rfl⟩ : syracuseStep 9468913 = 7101685) B7101685
theorem B12625217 : Blo 2075435 12625217 := bstep (se 2 (by rfl) ⟨4734456, by rfl⟩ : syracuseStep 12625217 = 9468913) B9468913
theorem B8416811 : Blo 2075435 8416811 := bstep (se 1 (by rfl) ⟨6312608, by rfl⟩ : syracuseStep 8416811 = 12625217) B12625217
theorem B5611207 : Blo 2075435 5611207 := bstep (se 1 (by rfl) ⟨4208405, by rfl⟩ : syracuseStep 5611207 = 8416811) B8416811
theorem B7481609 : Blo 2075435 7481609 := bstep (se 2 (by rfl) ⟨2805603, by rfl⟩ : syracuseStep 7481609 = 5611207) B5611207
theorem B4987739 : Blo 2075435 4987739 := bstep (se 1 (by rfl) ⟨3740804, by rfl⟩ : syracuseStep 4987739 = 7481609) B7481609
theorem B3325159 : Blo 2075435 3325159 := bstep (se 1 (by rfl) ⟨2493869, by rfl⟩ : syracuseStep 3325159 = 4987739) B4987739
theorem B4433545 : Blo 2075435 4433545 := bstep (se 2 (by rfl) ⟨1662579, by rfl⟩ : syracuseStep 4433545 = 3325159) B3325159
theorem B5911393 : Blo 2075435 5911393 := bstep (se 2 (by rfl) ⟨2216772, by rfl⟩ : syracuseStep 5911393 = 4433545) B4433545
theorem B7881857 : Blo 2075435 7881857 := bstep (se 2 (by rfl) ⟨2955696, by rfl⟩ : syracuseStep 7881857 = 5911393) B5911393
theorem B5254571 : Blo 2075435 5254571 := bstep (se 1 (by rfl) ⟨3940928, by rfl⟩ : syracuseStep 5254571 = 7881857) B7881857
theorem B3503047 : Blo 2075435 3503047 := bstep (se 1 (by rfl) ⟨2627285, by rfl⟩ : syracuseStep 3503047 = 5254571) B5254571
theorem B4670729 : Blo 2075435 4670729 := bstep (se 2 (by rfl) ⟨1751523, by rfl⟩ : syracuseStep 4670729 = 3503047) B3503047
theorem B3113819 : Blo 2075435 3113819 := bstep (se 1 (by rfl) ⟨2335364, by rfl⟩ : syracuseStep 3113819 = 4670729) B4670729
theorem B2075879 : Blo 2075435 2075879 := bstep (se 1 (by rfl) ⟨1556909, by rfl⟩ : syracuseStep 2075879 = 3113819) B3113819
theorem B2335369 : Blo 2075435 2335369 := bbase (se 2 (by rfl) ⟨875763, by rfl⟩ : syracuseStep 2335369 = 1751527) (by norm_num)
theorem B3113825 : Blo 2075435 3113825 := bstep (se 2 (by rfl) ⟨1167684, by rfl⟩ : syracuseStep 3113825 = 2335369) B2335369
theorem B2075883 : Blo 2075435 2075883 := bstep (se 1 (by rfl) ⟨1556912, by rfl⟩ : syracuseStep 2075883 = 3113825) B3113825
theorem B2663141 : Blo 2075435 2663141 := bbase (se 4 (by rfl) ⟨249669, by rfl⟩ : syracuseStep 2663141 = 499339) (by norm_num)
theorem B28406837 : Blo 2075435 28406837 := bstep (se 5 (by rfl) ⟨1331570, by rfl⟩ : syracuseStep 28406837 = 2663141) B2663141
theorem B18937891 : Blo 2075435 18937891 := bstep (se 1 (by rfl) ⟨14203418, by rfl⟩ : syracuseStep 18937891 = 28406837) B28406837
theorem B101002085 : Blo 2075435 101002085 := bstep (se 4 (by rfl) ⟨9468945, by rfl⟩ : syracuseStep 101002085 = 18937891) B18937891
theorem B67334723 : Blo 2075435 67334723 := bstep (se 1 (by rfl) ⟨50501042, by rfl⟩ : syracuseStep 67334723 = 101002085) B101002085
theorem B44889815 : Blo 2075435 44889815 := bstep (se 1 (by rfl) ⟨33667361, by rfl⟩ : syracuseStep 44889815 = 67334723) B67334723
theorem B29926543 : Blo 2075435 29926543 := bstep (se 1 (by rfl) ⟨22444907, by rfl⟩ : syracuseStep 29926543 = 44889815) B44889815
theorem B39902057 : Blo 2075435 39902057 := bstep (se 2 (by rfl) ⟨14963271, by rfl⟩ : syracuseStep 39902057 = 29926543) B29926543
theorem B26601371 : Blo 2075435 26601371 := bstep (se 1 (by rfl) ⟨19951028, by rfl⟩ : syracuseStep 26601371 = 39902057) B39902057
theorem B17734247 : Blo 2075435 17734247 := bstep (se 1 (by rfl) ⟨13300685, by rfl⟩ : syracuseStep 17734247 = 26601371) B26601371
theorem B11822831 : Blo 2075435 11822831 := bstep (se 1 (by rfl) ⟨8867123, by rfl⟩ : syracuseStep 11822831 = 17734247) B17734247
theorem B7881887 : Blo 2075435 7881887 := bstep (se 1 (by rfl) ⟨5911415, by rfl⟩ : syracuseStep 7881887 = 11822831) B11822831
theorem B5254591 : Blo 2075435 5254591 := bstep (se 1 (by rfl) ⟨3940943, by rfl⟩ : syracuseStep 5254591 = 7881887) B7881887
theorem B7006121 : Blo 2075435 7006121 := bstep (se 2 (by rfl) ⟨2627295, by rfl⟩ : syracuseStep 7006121 = 5254591) B5254591
theorem B4670747 : Blo 2075435 4670747 := bstep (se 1 (by rfl) ⟨3503060, by rfl⟩ : syracuseStep 4670747 = 7006121) B7006121
theorem B3113831 : Blo 2075435 3113831 := bstep (se 1 (by rfl) ⟨2335373, by rfl⟩ : syracuseStep 3113831 = 4670747) B4670747
theorem B2075887 : Blo 2075435 2075887 := bstep (se 1 (by rfl) ⟨1556915, by rfl⟩ : syracuseStep 2075887 = 3113831) B3113831
theorem B3113837 : Blo 2075435 3113837 := bbase (se 3 (by rfl) ⟨583844, by rfl⟩ : syracuseStep 3113837 = 1167689) (by norm_num)
theorem B2075891 : Blo 2075435 2075891 := bstep (se 1 (by rfl) ⟨1556918, by rfl⟩ : syracuseStep 2075891 = 3113837) B3113837
theorem B4670765 : Blo 2075435 4670765 := bbase (se 3 (by rfl) ⟨875768, by rfl⟩ : syracuseStep 4670765 = 1751537) (by norm_num)
theorem B3113843 : Blo 2075435 3113843 := bstep (se 1 (by rfl) ⟨2335382, by rfl⟩ : syracuseStep 3113843 = 4670765) B4670765
theorem B2075895 : Blo 2075435 2075895 := bstep (se 1 (by rfl) ⟨1556921, by rfl⟩ : syracuseStep 2075895 = 3113843) B3113843
theorem B11984213 : Blo 2075435 11984213 := bbase (se 11 (by rfl) ⟨8777, by rfl⟩ : syracuseStep 11984213 = 17555) (by norm_num)
theorem B7989475 : Blo 2075435 7989475 := bstep (se 1 (by rfl) ⟨5992106, by rfl⟩ : syracuseStep 7989475 = 11984213) B11984213
theorem B10652633 : Blo 2075435 10652633 := bstep (se 2 (by rfl) ⟨3994737, by rfl⟩ : syracuseStep 10652633 = 7989475) B7989475
theorem B7101755 : Blo 2075435 7101755 := bstep (se 1 (by rfl) ⟨5326316, by rfl⟩ : syracuseStep 7101755 = 10652633) B10652633
theorem B4734503 : Blo 2075435 4734503 := bstep (se 1 (by rfl) ⟨3550877, by rfl⟩ : syracuseStep 4734503 = 7101755) B7101755
theorem B3156335 : Blo 2075435 3156335 := bstep (se 1 (by rfl) ⟨2367251, by rfl⟩ : syracuseStep 3156335 = 4734503) B4734503
theorem B2104223 : Blo 2075435 2104223 := bstep (se 1 (by rfl) ⟨1578167, by rfl⟩ : syracuseStep 2104223 = 3156335) B3156335
theorem B22445045 : Blo 2075435 22445045 := bstep (se 5 (by rfl) ⟨1052111, by rfl⟩ : syracuseStep 22445045 = 2104223) B2104223
theorem B14963363 : Blo 2075435 14963363 := bstep (se 1 (by rfl) ⟨11222522, by rfl⟩ : syracuseStep 14963363 = 22445045) B22445045
theorem B9975575 : Blo 2075435 9975575 := bstep (se 1 (by rfl) ⟨7481681, by rfl⟩ : syracuseStep 9975575 = 14963363) B14963363
theorem B6650383 : Blo 2075435 6650383 := bstep (se 1 (by rfl) ⟨4987787, by rfl⟩ : syracuseStep 6650383 = 9975575) B9975575
theorem B8867177 : Blo 2075435 8867177 := bstep (se 2 (by rfl) ⟨3325191, by rfl⟩ : syracuseStep 8867177 = 6650383) B6650383
theorem B5911451 : Blo 2075435 5911451 := bstep (se 1 (by rfl) ⟨4433588, by rfl⟩ : syracuseStep 5911451 = 8867177) B8867177
theorem B3940967 : Blo 2075435 3940967 := bstep (se 1 (by rfl) ⟨2955725, by rfl⟩ : syracuseStep 3940967 = 5911451) B5911451
theorem B2627311 : Blo 2075435 2627311 := bstep (se 1 (by rfl) ⟨1970483, by rfl⟩ : syracuseStep 2627311 = 3940967) B3940967
theorem B3503081 : Blo 2075435 3503081 := bstep (se 2 (by rfl) ⟨1313655, by rfl⟩ : syracuseStep 3503081 = 2627311) B2627311
theorem B2335387 : Blo 2075435 2335387 := bstep (se 1 (by rfl) ⟨1751540, by rfl⟩ : syracuseStep 2335387 = 3503081) B3503081
theorem B3113849 : Blo 2075435 3113849 := bstep (se 2 (by rfl) ⟨1167693, by rfl⟩ : syracuseStep 3113849 = 2335387) B2335387
theorem B2075899 : Blo 2075435 2075899 := bstep (se 1 (by rfl) ⟨1556924, by rfl⟩ : syracuseStep 2075899 = 3113849) B3113849
theorem B4208453 : Blo 2075435 4208453 := bbase (se 4 (by rfl) ⟨394542, by rfl⟩ : syracuseStep 4208453 = 789085) (by norm_num)
theorem B2805635 : Blo 2075435 2805635 := bstep (se 1 (by rfl) ⟨2104226, by rfl⟩ : syracuseStep 2805635 = 4208453) B4208453
theorem B7481693 : Blo 2075435 7481693 := bstep (se 3 (by rfl) ⟨1402817, by rfl⟩ : syracuseStep 7481693 = 2805635) B2805635
theorem B19951181 : Blo 2075435 19951181 := bstep (se 3 (by rfl) ⟨3740846, by rfl⟩ : syracuseStep 19951181 = 7481693) B7481693
theorem B13300787 : Blo 2075435 13300787 := bstep (se 1 (by rfl) ⟨9975590, by rfl⟩ : syracuseStep 13300787 = 19951181) B19951181
theorem B35468765 : Blo 2075435 35468765 := bstep (se 3 (by rfl) ⟨6650393, by rfl⟩ : syracuseStep 35468765 = 13300787) B13300787
theorem B23645843 : Blo 2075435 23645843 := bstep (se 1 (by rfl) ⟨17734382, by rfl⟩ : syracuseStep 23645843 = 35468765) B35468765
theorem B15763895 : Blo 2075435 15763895 := bstep (se 1 (by rfl) ⟨11822921, by rfl⟩ : syracuseStep 15763895 = 23645843) B23645843
theorem B10509263 : Blo 2075435 10509263 := bstep (se 1 (by rfl) ⟨7881947, by rfl⟩ : syracuseStep 10509263 = 15763895) B15763895
theorem B7006175 : Blo 2075435 7006175 := bstep (se 1 (by rfl) ⟨5254631, by rfl⟩ : syracuseStep 7006175 = 10509263) B10509263
theorem B4670783 : Blo 2075435 4670783 := bstep (se 1 (by rfl) ⟨3503087, by rfl⟩ : syracuseStep 4670783 = 7006175) B7006175
theorem B3113855 : Blo 2075435 3113855 := bstep (se 1 (by rfl) ⟨2335391, by rfl⟩ : syracuseStep 3113855 = 4670783) B4670783
theorem B2075903 : Blo 2075435 2075903 := bstep (se 1 (by rfl) ⟨1556927, by rfl⟩ : syracuseStep 2075903 = 3113855) B3113855
theorem B3113861 : Blo 2075435 3113861 := bbase (se 4 (by rfl) ⟨291924, by rfl⟩ : syracuseStep 3113861 = 583849) (by norm_num)
theorem B2075907 : Blo 2075435 2075907 := bstep (se 1 (by rfl) ⟨1556930, by rfl⟩ : syracuseStep 2075907 = 3113861) B3113861
theorem B3503101 : Blo 2075435 3503101 := bbase (se 3 (by rfl) ⟨656831, by rfl⟩ : syracuseStep 3503101 = 1313663) (by norm_num)
theorem B4670801 : Blo 2075435 4670801 := bstep (se 2 (by rfl) ⟨1751550, by rfl⟩ : syracuseStep 4670801 = 3503101) B3503101
theorem B3113867 : Blo 2075435 3113867 := bstep (se 1 (by rfl) ⟨2335400, by rfl⟩ : syracuseStep 3113867 = 4670801) B4670801
theorem B2075911 : Blo 2075435 2075911 := bstep (se 1 (by rfl) ⟨1556933, by rfl⟩ : syracuseStep 2075911 = 3113867) B3113867
theorem B2335405 : Blo 2075435 2335405 := bbase (se 3 (by rfl) ⟨437888, by rfl⟩ : syracuseStep 2335405 = 875777) (by norm_num)
theorem B3113873 : Blo 2075435 3113873 := bstep (se 2 (by rfl) ⟨1167702, by rfl⟩ : syracuseStep 3113873 = 2335405) B2335405
theorem B2075915 : Blo 2075435 2075915 := bstep (se 1 (by rfl) ⟨1556936, by rfl⟩ : syracuseStep 2075915 = 3113873) B3113873
theorem B7006229 : Blo 2075435 7006229 := bbase (se 6 (by rfl) ⟨164208, by rfl⟩ : syracuseStep 7006229 = 328417) (by norm_num)
theorem B4670819 : Blo 2075435 4670819 := bstep (se 1 (by rfl) ⟨3503114, by rfl⟩ : syracuseStep 4670819 = 7006229) B7006229
theorem B3113879 : Blo 2075435 3113879 := bstep (se 1 (by rfl) ⟨2335409, by rfl⟩ : syracuseStep 3113879 = 4670819) B4670819
theorem B2075919 : Blo 2075435 2075919 := bstep (se 1 (by rfl) ⟨1556939, by rfl⟩ : syracuseStep 2075919 = 3113879) B3113879
theorem B3113885 : Blo 2075435 3113885 := bbase (se 3 (by rfl) ⟨583853, by rfl⟩ : syracuseStep 3113885 = 1167707) (by norm_num)
theorem B2075923 : Blo 2075435 2075923 := bstep (se 1 (by rfl) ⟨1556942, by rfl⟩ : syracuseStep 2075923 = 3113885) B3113885
theorem B4670837 : Blo 2075435 4670837 := bbase (se 5 (by rfl) ⟨218945, by rfl⟩ : syracuseStep 4670837 = 437891) (by norm_num)
theorem B3113891 : Blo 2075435 3113891 := bstep (se 1 (by rfl) ⟨2335418, by rfl⟩ : syracuseStep 3113891 = 4670837) B4670837
theorem B2075927 : Blo 2075435 2075927 := bstep (se 1 (by rfl) ⟨1556945, by rfl⟩ : syracuseStep 2075927 = 3113891) B3113891
theorem B5326397 : Blo 2075435 5326397 := bbase (se 3 (by rfl) ⟨998699, by rfl⟩ : syracuseStep 5326397 = 1997399) (by norm_num)
theorem B3550931 : Blo 2075435 3550931 := bstep (se 1 (by rfl) ⟨2663198, by rfl⟩ : syracuseStep 3550931 = 5326397) B5326397
theorem B2367287 : Blo 2075435 2367287 := bstep (se 1 (by rfl) ⟨1775465, by rfl⟩ : syracuseStep 2367287 = 3550931) B3550931
theorem B25251061 : Blo 2075435 25251061 := bstep (se 5 (by rfl) ⟨1183643, by rfl⟩ : syracuseStep 25251061 = 2367287) B2367287
theorem B33668081 : Blo 2075435 33668081 := bstep (se 2 (by rfl) ⟨12625530, by rfl⟩ : syracuseStep 33668081 = 25251061) B25251061
theorem B22445387 : Blo 2075435 22445387 := bstep (se 1 (by rfl) ⟨16834040, by rfl⟩ : syracuseStep 22445387 = 33668081) B33668081
theorem B14963591 : Blo 2075435 14963591 := bstep (se 1 (by rfl) ⟨11222693, by rfl⟩ : syracuseStep 14963591 = 22445387) B22445387
theorem B9975727 : Blo 2075435 9975727 := bstep (se 1 (by rfl) ⟨7481795, by rfl⟩ : syracuseStep 9975727 = 14963591) B14963591
theorem B13300969 : Blo 2075435 13300969 := bstep (se 2 (by rfl) ⟨4987863, by rfl⟩ : syracuseStep 13300969 = 9975727) B9975727
theorem B17734625 : Blo 2075435 17734625 := bstep (se 2 (by rfl) ⟨6650484, by rfl⟩ : syracuseStep 17734625 = 13300969) B13300969
theorem B11823083 : Blo 2075435 11823083 := bstep (se 1 (by rfl) ⟨8867312, by rfl⟩ : syracuseStep 11823083 = 17734625) B17734625
theorem B7882055 : Blo 2075435 7882055 := bstep (se 1 (by rfl) ⟨5911541, by rfl⟩ : syracuseStep 7882055 = 11823083) B11823083
theorem B5254703 : Blo 2075435 5254703 := bstep (se 1 (by rfl) ⟨3941027, by rfl⟩ : syracuseStep 5254703 = 7882055) B7882055
theorem B3503135 : Blo 2075435 3503135 := bstep (se 1 (by rfl) ⟨2627351, by rfl⟩ : syracuseStep 3503135 = 5254703) B5254703
theorem B2335423 : Blo 2075435 2335423 := bstep (se 1 (by rfl) ⟨1751567, by rfl⟩ : syracuseStep 2335423 = 3503135) B3503135
theorem B3113897 : Blo 2075435 3113897 := bstep (se 2 (by rfl) ⟨1167711, by rfl⟩ : syracuseStep 3113897 = 2335423) B2335423
theorem B2075931 : Blo 2075435 2075931 := bstep (se 1 (by rfl) ⟨1556948, by rfl⟩ : syracuseStep 2075931 = 3113897) B3113897
theorem B7882069 : Blo 2075435 7882069 := bbase (se 12 (by rfl) ⟨2886, by rfl⟩ : syracuseStep 7882069 = 5773) (by norm_num)
theorem B10509425 : Blo 2075435 10509425 := bstep (se 2 (by rfl) ⟨3941034, by rfl⟩ : syracuseStep 10509425 = 7882069) B7882069
theorem B7006283 : Blo 2075435 7006283 := bstep (se 1 (by rfl) ⟨5254712, by rfl⟩ : syracuseStep 7006283 = 10509425) B10509425
theorem B4670855 : Blo 2075435 4670855 := bstep (se 1 (by rfl) ⟨3503141, by rfl⟩ : syracuseStep 4670855 = 7006283) B7006283
theorem B3113903 : Blo 2075435 3113903 := bstep (se 1 (by rfl) ⟨2335427, by rfl⟩ : syracuseStep 3113903 = 4670855) B4670855
theorem B2075935 : Blo 2075435 2075935 := bstep (se 1 (by rfl) ⟨1556951, by rfl⟩ : syracuseStep 2075935 = 3113903) B3113903
theorem B3113909 : Blo 2075435 3113909 := bbase (se 5 (by rfl) ⟨145964, by rfl⟩ : syracuseStep 3113909 = 291929) (by norm_num)
theorem B2075939 : Blo 2075435 2075939 := bstep (se 1 (by rfl) ⟨1556954, by rfl⟩ : syracuseStep 2075939 = 3113909) B3113909
theorem B5254733 : Blo 2075435 5254733 := bbase (se 3 (by rfl) ⟨985262, by rfl⟩ : syracuseStep 5254733 = 1970525) (by norm_num)
theorem B3503155 : Blo 2075435 3503155 := bstep (se 1 (by rfl) ⟨2627366, by rfl⟩ : syracuseStep 3503155 = 5254733) B5254733
theorem B4670873 : Blo 2075435 4670873 := bstep (se 2 (by rfl) ⟨1751577, by rfl⟩ : syracuseStep 4670873 = 3503155) B3503155
theorem B3113915 : Blo 2075435 3113915 := bstep (se 1 (by rfl) ⟨2335436, by rfl⟩ : syracuseStep 3113915 = 4670873) B4670873
theorem B2075943 : Blo 2075435 2075943 := bstep (se 1 (by rfl) ⟨1556957, by rfl⟩ : syracuseStep 2075943 = 3113915) B3113915
theorem B2335441 : Blo 2075435 2335441 := bbase (se 2 (by rfl) ⟨875790, by rfl⟩ : syracuseStep 2335441 = 1751581) (by norm_num)
theorem B3113921 : Blo 2075435 3113921 := bstep (se 2 (by rfl) ⟨1167720, by rfl⟩ : syracuseStep 3113921 = 2335441) B2335441
theorem B2075947 : Blo 2075435 2075947 := bstep (se 1 (by rfl) ⟨1556960, by rfl⟩ : syracuseStep 2075947 = 3113921) B3113921
theorem B6650549 : Blo 2075435 6650549 := bbase (se 5 (by rfl) ⟨311744, by rfl⟩ : syracuseStep 6650549 = 623489) (by norm_num)
theorem B4433699 : Blo 2075435 4433699 := bstep (se 1 (by rfl) ⟨3325274, by rfl⟩ : syracuseStep 4433699 = 6650549) B6650549
theorem B2955799 : Blo 2075435 2955799 := bstep (se 1 (by rfl) ⟨2216849, by rfl⟩ : syracuseStep 2955799 = 4433699) B4433699
theorem B3941065 : Blo 2075435 3941065 := bstep (se 2 (by rfl) ⟨1477899, by rfl⟩ : syracuseStep 3941065 = 2955799) B2955799
theorem B5254753 : Blo 2075435 5254753 := bstep (se 2 (by rfl) ⟨1970532, by rfl⟩ : syracuseStep 5254753 = 3941065) B3941065
theorem B7006337 : Blo 2075435 7006337 := bstep (se 2 (by rfl) ⟨2627376, by rfl⟩ : syracuseStep 7006337 = 5254753) B5254753
theorem B4670891 : Blo 2075435 4670891 := bstep (se 1 (by rfl) ⟨3503168, by rfl⟩ : syracuseStep 4670891 = 7006337) B7006337
theorem B3113927 : Blo 2075435 3113927 := bstep (se 1 (by rfl) ⟨2335445, by rfl⟩ : syracuseStep 3113927 = 4670891) B4670891
theorem B2075951 : Blo 2075435 2075951 := bstep (se 1 (by rfl) ⟨1556963, by rfl⟩ : syracuseStep 2075951 = 3113927) B3113927
theorem B3113933 : Blo 2075435 3113933 := bbase (se 3 (by rfl) ⟨583862, by rfl⟩ : syracuseStep 3113933 = 1167725) (by norm_num)
theorem B2075955 : Blo 2075435 2075955 := bstep (se 1 (by rfl) ⟨1556966, by rfl⟩ : syracuseStep 2075955 = 3113933) B3113933
theorem B4670909 : Blo 2075435 4670909 := bbase (se 3 (by rfl) ⟨875795, by rfl⟩ : syracuseStep 4670909 = 1751591) (by norm_num)
theorem B3113939 : Blo 2075435 3113939 := bstep (se 1 (by rfl) ⟨2335454, by rfl⟩ : syracuseStep 3113939 = 4670909) B4670909
theorem B2075959 : Blo 2075435 2075959 := bstep (se 1 (by rfl) ⟨1556969, by rfl⟩ : syracuseStep 2075959 = 3113939) B3113939
theorem B3503189 : Blo 2075435 3503189 := bbase (se 8 (by rfl) ⟨20526, by rfl⟩ : syracuseStep 3503189 = 41053) (by norm_num)
theorem B2335459 : Blo 2075435 2335459 := bstep (se 1 (by rfl) ⟨1751594, by rfl⟩ : syracuseStep 2335459 = 3503189) B3503189
theorem B3113945 : Blo 2075435 3113945 := bstep (se 2 (by rfl) ⟨1167729, by rfl⟩ : syracuseStep 3113945 = 2335459) B2335459
theorem B2075963 : Blo 2075435 2075963 := bstep (se 1 (by rfl) ⟨1556972, by rfl⟩ : syracuseStep 2075963 = 3113945) B3113945
theorem B4324205 : Blo 2075435 4324205 := bbase (se 3 (by rfl) ⟨810788, by rfl⟩ : syracuseStep 4324205 = 1621577) (by norm_num)
theorem B11531213 : Blo 2075435 11531213 := bstep (se 3 (by rfl) ⟨2162102, by rfl⟩ : syracuseStep 11531213 = 4324205) B4324205
theorem B7687475 : Blo 2075435 7687475 := bstep (se 1 (by rfl) ⟨5765606, by rfl⟩ : syracuseStep 7687475 = 11531213) B11531213
theorem B5124983 : Blo 2075435 5124983 := bstep (se 1 (by rfl) ⟨3843737, by rfl⟩ : syracuseStep 5124983 = 7687475) B7687475
theorem B13666621 : Blo 2075435 13666621 := bstep (se 3 (by rfl) ⟨2562491, by rfl⟩ : syracuseStep 13666621 = 5124983) B5124983
theorem B18222161 : Blo 2075435 18222161 := bstep (se 2 (by rfl) ⟨6833310, by rfl⟩ : syracuseStep 18222161 = 13666621) B13666621
theorem B48592429 : Blo 2075435 48592429 := bstep (se 3 (by rfl) ⟨9111080, by rfl⟩ : syracuseStep 48592429 = 18222161) B18222161
theorem B259159621 : Blo 2075435 259159621 := bstep (se 4 (by rfl) ⟨24296214, by rfl⟩ : syracuseStep 259159621 = 48592429) B48592429
theorem B345546161 : Blo 2075435 345546161 := bstep (se 2 (by rfl) ⟨129579810, by rfl⟩ : syracuseStep 345546161 = 259159621) B259159621
theorem B230364107 : Blo 2075435 230364107 := bstep (se 1 (by rfl) ⟨172773080, by rfl⟩ : syracuseStep 230364107 = 345546161) B345546161
theorem B153576071 : Blo 2075435 153576071 := bstep (se 1 (by rfl) ⟨115182053, by rfl⟩ : syracuseStep 153576071 = 230364107) B230364107
theorem B102384047 : Blo 2075435 102384047 := bstep (se 1 (by rfl) ⟨76788035, by rfl⟩ : syracuseStep 102384047 = 153576071) B153576071
theorem B68256031 : Blo 2075435 68256031 := bstep (se 1 (by rfl) ⟨51192023, by rfl⟩ : syracuseStep 68256031 = 102384047) B102384047
theorem B91008041 : Blo 2075435 91008041 := bstep (se 2 (by rfl) ⟨34128015, by rfl⟩ : syracuseStep 91008041 = 68256031) B68256031
theorem B242688109 : Blo 2075435 242688109 := bstep (se 3 (by rfl) ⟨45504020, by rfl⟩ : syracuseStep 242688109 = 91008041) B91008041
theorem B323584145 : Blo 2075435 323584145 := bstep (se 2 (by rfl) ⟨121344054, by rfl⟩ : syracuseStep 323584145 = 242688109) B242688109
theorem B215722763 : Blo 2075435 215722763 := bstep (se 1 (by rfl) ⟨161792072, by rfl⟩ : syracuseStep 215722763 = 323584145) B323584145
theorem B143815175 : Blo 2075435 143815175 := bstep (se 1 (by rfl) ⟨107861381, by rfl⟩ : syracuseStep 143815175 = 215722763) B215722763
theorem B95876783 : Blo 2075435 95876783 := bstep (se 1 (by rfl) ⟨71907587, by rfl⟩ : syracuseStep 95876783 = 143815175) B143815175
theorem B63917855 : Blo 2075435 63917855 := bstep (se 1 (by rfl) ⟨47938391, by rfl⟩ : syracuseStep 63917855 = 95876783) B95876783
theorem B42611903 : Blo 2075435 42611903 := bstep (se 1 (by rfl) ⟨31958927, by rfl⟩ : syracuseStep 42611903 = 63917855) B63917855
theorem B28407935 : Blo 2075435 28407935 := bstep (se 1 (by rfl) ⟨21305951, by rfl⟩ : syracuseStep 28407935 = 42611903) B42611903
theorem B18938623 : Blo 2075435 18938623 := bstep (se 1 (by rfl) ⟨14203967, by rfl⟩ : syracuseStep 18938623 = 28407935) B28407935
theorem B25251497 : Blo 2075435 25251497 := bstep (se 2 (by rfl) ⟨9469311, by rfl⟩ : syracuseStep 25251497 = 18938623) B18938623
theorem B16834331 : Blo 2075435 16834331 := bstep (se 1 (by rfl) ⟨12625748, by rfl⟩ : syracuseStep 16834331 = 25251497) B25251497
theorem B11222887 : Blo 2075435 11222887 := bstep (se 1 (by rfl) ⟨8417165, by rfl⟩ : syracuseStep 11222887 = 16834331) B16834331
theorem B14963849 : Blo 2075435 14963849 := bstep (se 2 (by rfl) ⟨5611443, by rfl⟩ : syracuseStep 14963849 = 11222887) B11222887
theorem B9975899 : Blo 2075435 9975899 := bstep (se 1 (by rfl) ⟨7481924, by rfl⟩ : syracuseStep 9975899 = 14963849) B14963849
theorem B6650599 : Blo 2075435 6650599 := bstep (se 1 (by rfl) ⟨4987949, by rfl⟩ : syracuseStep 6650599 = 9975899) B9975899
theorem B8867465 : Blo 2075435 8867465 := bstep (se 2 (by rfl) ⟨3325299, by rfl⟩ : syracuseStep 8867465 = 6650599) B6650599
theorem B5911643 : Blo 2075435 5911643 := bstep (se 1 (by rfl) ⟨4433732, by rfl⟩ : syracuseStep 5911643 = 8867465) B8867465
theorem B15764381 : Blo 2075435 15764381 := bstep (se 3 (by rfl) ⟨2955821, by rfl⟩ : syracuseStep 15764381 = 5911643) B5911643
theorem B10509587 : Blo 2075435 10509587 := bstep (se 1 (by rfl) ⟨7882190, by rfl⟩ : syracuseStep 10509587 = 15764381) B15764381
theorem B7006391 : Blo 2075435 7006391 := bstep (se 1 (by rfl) ⟨5254793, by rfl⟩ : syracuseStep 7006391 = 10509587) B10509587
theorem B4670927 : Blo 2075435 4670927 := bstep (se 1 (by rfl) ⟨3503195, by rfl⟩ : syracuseStep 4670927 = 7006391) B7006391
theorem B3113951 : Blo 2075435 3113951 := bstep (se 1 (by rfl) ⟨2335463, by rfl⟩ : syracuseStep 3113951 = 4670927) B4670927
theorem B2075967 : Blo 2075435 2075967 := bstep (se 1 (by rfl) ⟨1556975, by rfl⟩ : syracuseStep 2075967 = 3113951) B3113951
theorem B3113957 : Blo 2075435 3113957 := bbase (se 4 (by rfl) ⟨291933, by rfl⟩ : syracuseStep 3113957 = 583867) (by norm_num)
theorem B2075971 : Blo 2075435 2075971 := bstep (se 1 (by rfl) ⟨1556978, by rfl⟩ : syracuseStep 2075971 = 3113957) B3113957
theorem B2493985 : Blo 2075435 2493985 := bbase (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) (by norm_num)
theorem B3325313 : Blo 2075435 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B8867501 : Blo 2075435 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B5911667 : Blo 2075435 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B3941111 : Blo 2075435 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B2627407 : Blo 2075435 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B3503209 : Blo 2075435 3503209 := bstep (se 2 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 3503209 = 2627407) B2627407
theorem B4670945 : Blo 2075435 4670945 := bstep (se 2 (by rfl) ⟨1751604, by rfl⟩ : syracuseStep 4670945 = 3503209) B3503209
theorem B3113963 : Blo 2075435 3113963 := bstep (se 1 (by rfl) ⟨2335472, by rfl⟩ : syracuseStep 3113963 = 4670945) B4670945
theorem B2075975 : Blo 2075435 2075975 := bstep (se 1 (by rfl) ⟨1556981, by rfl⟩ : syracuseStep 2075975 = 3113963) B3113963
theorem B2335477 : Blo 2075435 2335477 := bbase (se 5 (by rfl) ⟨109475, by rfl⟩ : syracuseStep 2335477 = 218951) (by norm_num)
theorem B3113969 : Blo 2075435 3113969 := bstep (se 2 (by rfl) ⟨1167738, by rfl⟩ : syracuseStep 3113969 = 2335477) B2335477
theorem B2075979 : Blo 2075435 2075979 := bstep (se 1 (by rfl) ⟨1556984, by rfl⟩ : syracuseStep 2075979 = 3113969) B3113969
theorem B2627417 : Blo 2075435 2627417 := bbase (se 2 (by rfl) ⟨985281, by rfl⟩ : syracuseStep 2627417 = 1970563) (by norm_num)
theorem B7006445 : Blo 2075435 7006445 := bstep (se 3 (by rfl) ⟨1313708, by rfl⟩ : syracuseStep 7006445 = 2627417) B2627417
theorem B4670963 : Blo 2075435 4670963 := bstep (se 1 (by rfl) ⟨3503222, by rfl⟩ : syracuseStep 4670963 = 7006445) B7006445
theorem B3113975 : Blo 2075435 3113975 := bstep (se 1 (by rfl) ⟨2335481, by rfl⟩ : syracuseStep 3113975 = 4670963) B4670963
theorem B2075983 : Blo 2075435 2075983 := bstep (se 1 (by rfl) ⟨1556987, by rfl⟩ : syracuseStep 2075983 = 3113975) B3113975
theorem B3113981 : Blo 2075435 3113981 := bbase (se 3 (by rfl) ⟨583871, by rfl⟩ : syracuseStep 3113981 = 1167743) (by norm_num)
theorem B2075987 : Blo 2075435 2075987 := bstep (se 1 (by rfl) ⟨1556990, by rfl⟩ : syracuseStep 2075987 = 3113981) B3113981
theorem B4670981 : Blo 2075435 4670981 := bbase (se 4 (by rfl) ⟨437904, by rfl⟩ : syracuseStep 4670981 = 875809) (by norm_num)
theorem B3113987 : Blo 2075435 3113987 := bstep (se 1 (by rfl) ⟨2335490, by rfl⟩ : syracuseStep 3113987 = 4670981) B4670981
theorem B2075991 : Blo 2075435 2075991 := bstep (se 1 (by rfl) ⟨1556993, by rfl⟩ : syracuseStep 2075991 = 3113987) B3113987
theorem B3941149 : Blo 2075435 3941149 := bbase (se 3 (by rfl) ⟨738965, by rfl⟩ : syracuseStep 3941149 = 1477931) (by norm_num)
theorem B5254865 : Blo 2075435 5254865 := bstep (se 2 (by rfl) ⟨1970574, by rfl⟩ : syracuseStep 5254865 = 3941149) B3941149
theorem B3503243 : Blo 2075435 3503243 := bstep (se 1 (by rfl) ⟨2627432, by rfl⟩ : syracuseStep 3503243 = 5254865) B5254865
theorem B2335495 : Blo 2075435 2335495 := bstep (se 1 (by rfl) ⟨1751621, by rfl⟩ : syracuseStep 2335495 = 3503243) B3503243
theorem B3113993 : Blo 2075435 3113993 := bstep (se 2 (by rfl) ⟨1167747, by rfl⟩ : syracuseStep 3113993 = 2335495) B2335495
theorem B2075995 : Blo 2075435 2075995 := bstep (se 1 (by rfl) ⟨1556996, by rfl⟩ : syracuseStep 2075995 = 3113993) B3113993
theorem B10509749 : Blo 2075435 10509749 := bbase (se 5 (by rfl) ⟨492644, by rfl⟩ : syracuseStep 10509749 = 985289) (by norm_num)
theorem B7006499 : Blo 2075435 7006499 := bstep (se 1 (by rfl) ⟨5254874, by rfl⟩ : syracuseStep 7006499 = 10509749) B10509749
theorem B4670999 : Blo 2075435 4670999 := bstep (se 1 (by rfl) ⟨3503249, by rfl⟩ : syracuseStep 4670999 = 7006499) B7006499
theorem B3113999 : Blo 2075435 3113999 := bstep (se 1 (by rfl) ⟨2335499, by rfl⟩ : syracuseStep 3113999 = 4670999) B4670999
theorem B2075999 : Blo 2075435 2075999 := bstep (se 1 (by rfl) ⟨1556999, by rfl⟩ : syracuseStep 2075999 = 3113999) B3113999
theorem B3114005 : Blo 2075435 3114005 := bbase (se 6 (by rfl) ⟨72984, by rfl⟩ : syracuseStep 3114005 = 145969) (by norm_num)
theorem B2076003 : Blo 2075435 2076003 := bstep (se 1 (by rfl) ⟨1557002, by rfl⟩ : syracuseStep 2076003 = 3114005) B3114005
theorem B3599509 : Blo 2075435 3599509 := bbase (se 6 (by rfl) ⟨84363, by rfl⟩ : syracuseStep 3599509 = 168727) (by norm_num)
theorem B4799345 : Blo 2075435 4799345 := bstep (se 2 (by rfl) ⟨1799754, by rfl⟩ : syracuseStep 4799345 = 3599509) B3599509
theorem B12798253 : Blo 2075435 12798253 := bstep (se 3 (by rfl) ⟨2399672, by rfl⟩ : syracuseStep 12798253 = 4799345) B4799345
theorem B68257349 : Blo 2075435 68257349 := bstep (se 4 (by rfl) ⟨6399126, by rfl⟩ : syracuseStep 68257349 = 12798253) B12798253
theorem B45504899 : Blo 2075435 45504899 := bstep (se 1 (by rfl) ⟨34128674, by rfl⟩ : syracuseStep 45504899 = 68257349) B68257349
theorem B30336599 : Blo 2075435 30336599 := bstep (se 1 (by rfl) ⟨22752449, by rfl⟩ : syracuseStep 30336599 = 45504899) B45504899
theorem B20224399 : Blo 2075435 20224399 := bstep (se 1 (by rfl) ⟨15168299, by rfl⟩ : syracuseStep 20224399 = 30336599) B30336599
theorem B26965865 : Blo 2075435 26965865 := bstep (se 2 (by rfl) ⟨10112199, by rfl⟩ : syracuseStep 26965865 = 20224399) B20224399
theorem B17977243 : Blo 2075435 17977243 := bstep (se 1 (by rfl) ⟨13482932, by rfl⟩ : syracuseStep 17977243 = 26965865) B26965865
theorem B23969657 : Blo 2075435 23969657 := bstep (se 2 (by rfl) ⟨8988621, by rfl⟩ : syracuseStep 23969657 = 17977243) B17977243
theorem B15979771 : Blo 2075435 15979771 := bstep (se 1 (by rfl) ⟨11984828, by rfl⟩ : syracuseStep 15979771 = 23969657) B23969657
theorem B85225445 : Blo 2075435 85225445 := bstep (se 4 (by rfl) ⟨7989885, by rfl⟩ : syracuseStep 85225445 = 15979771) B15979771
theorem B56816963 : Blo 2075435 56816963 := bstep (se 1 (by rfl) ⟨42612722, by rfl⟩ : syracuseStep 56816963 = 85225445) B85225445
theorem B37877975 : Blo 2075435 37877975 := bstep (se 1 (by rfl) ⟨28408481, by rfl⟩ : syracuseStep 37877975 = 56816963) B56816963
theorem B25251983 : Blo 2075435 25251983 := bstep (se 1 (by rfl) ⟨18938987, by rfl⟩ : syracuseStep 25251983 = 37877975) B37877975
theorem B16834655 : Blo 2075435 16834655 := bstep (se 1 (by rfl) ⟨12625991, by rfl⟩ : syracuseStep 16834655 = 25251983) B25251983
theorem B44892413 : Blo 2075435 44892413 := bstep (se 3 (by rfl) ⟨8417327, by rfl⟩ : syracuseStep 44892413 = 16834655) B16834655
theorem B29928275 : Blo 2075435 29928275 := bstep (se 1 (by rfl) ⟨22446206, by rfl⟩ : syracuseStep 29928275 = 44892413) B44892413
theorem B19952183 : Blo 2075435 19952183 := bstep (se 1 (by rfl) ⟨14964137, by rfl⟩ : syracuseStep 19952183 = 29928275) B29928275
theorem B13301455 : Blo 2075435 13301455 := bstep (se 1 (by rfl) ⟨9976091, by rfl⟩ : syracuseStep 13301455 = 19952183) B19952183
theorem B17735273 : Blo 2075435 17735273 := bstep (se 2 (by rfl) ⟨6650727, by rfl⟩ : syracuseStep 17735273 = 13301455) B13301455
theorem B11823515 : Blo 2075435 11823515 := bstep (se 1 (by rfl) ⟨8867636, by rfl⟩ : syracuseStep 11823515 = 17735273) B17735273
theorem B7882343 : Blo 2075435 7882343 := bstep (se 1 (by rfl) ⟨5911757, by rfl⟩ : syracuseStep 7882343 = 11823515) B11823515
theorem B5254895 : Blo 2075435 5254895 := bstep (se 1 (by rfl) ⟨3941171, by rfl⟩ : syracuseStep 5254895 = 7882343) B7882343
theorem B3503263 : Blo 2075435 3503263 := bstep (se 1 (by rfl) ⟨2627447, by rfl⟩ : syracuseStep 3503263 = 5254895) B5254895
theorem B4671017 : Blo 2075435 4671017 := bstep (se 2 (by rfl) ⟨1751631, by rfl⟩ : syracuseStep 4671017 = 3503263) B3503263
theorem B3114011 : Blo 2075435 3114011 := bstep (se 1 (by rfl) ⟨2335508, by rfl⟩ : syracuseStep 3114011 = 4671017) B4671017
theorem B2076007 : Blo 2075435 2076007 := bstep (se 1 (by rfl) ⟨1557005, by rfl⟩ : syracuseStep 2076007 = 3114011) B3114011
theorem B2335513 : Blo 2075435 2335513 := bbase (se 2 (by rfl) ⟨875817, by rfl⟩ : syracuseStep 2335513 = 1751635) (by norm_num)
theorem B3114017 : Blo 2075435 3114017 := bstep (se 2 (by rfl) ⟨1167756, by rfl⟩ : syracuseStep 3114017 = 2335513) B2335513
theorem B2076011 : Blo 2075435 2076011 := bstep (se 1 (by rfl) ⟨1557008, by rfl⟩ : syracuseStep 2076011 = 3114017) B3114017
theorem B7882373 : Blo 2075435 7882373 := bbase (se 4 (by rfl) ⟨738972, by rfl⟩ : syracuseStep 7882373 = 1477945) (by norm_num)
theorem B5254915 : Blo 2075435 5254915 := bstep (se 1 (by rfl) ⟨3941186, by rfl⟩ : syracuseStep 5254915 = 7882373) B7882373
theorem B7006553 : Blo 2075435 7006553 := bstep (se 2 (by rfl) ⟨2627457, by rfl⟩ : syracuseStep 7006553 = 5254915) B5254915
theorem B4671035 : Blo 2075435 4671035 := bstep (se 1 (by rfl) ⟨3503276, by rfl⟩ : syracuseStep 4671035 = 7006553) B7006553
theorem B3114023 : Blo 2075435 3114023 := bstep (se 1 (by rfl) ⟨2335517, by rfl⟩ : syracuseStep 3114023 = 4671035) B4671035
theorem B2076015 : Blo 2075435 2076015 := bstep (se 1 (by rfl) ⟨1557011, by rfl⟩ : syracuseStep 2076015 = 3114023) B3114023
theorem B3114029 : Blo 2075435 3114029 := bbase (se 3 (by rfl) ⟨583880, by rfl⟩ : syracuseStep 3114029 = 1167761) (by norm_num)
theorem B2076019 : Blo 2075435 2076019 := bstep (se 1 (by rfl) ⟨1557014, by rfl⟩ : syracuseStep 2076019 = 3114029) B3114029
theorem B4671053 : Blo 2075435 4671053 := bbase (se 3 (by rfl) ⟨875822, by rfl⟩ : syracuseStep 4671053 = 1751645) (by norm_num)
theorem B3114035 : Blo 2075435 3114035 := bstep (se 1 (by rfl) ⟨2335526, by rfl⟩ : syracuseStep 3114035 = 4671053) B4671053
theorem B2076023 : Blo 2075435 2076023 := bstep (se 1 (by rfl) ⟨1557017, by rfl⟩ : syracuseStep 2076023 = 3114035) B3114035
theorem B2627473 : Blo 2075435 2627473 := bbase (se 2 (by rfl) ⟨985302, by rfl⟩ : syracuseStep 2627473 = 1970605) (by norm_num)
theorem B3503297 : Blo 2075435 3503297 := bstep (se 2 (by rfl) ⟨1313736, by rfl⟩ : syracuseStep 3503297 = 2627473) B2627473
theorem B2335531 : Blo 2075435 2335531 := bstep (se 1 (by rfl) ⟨1751648, by rfl⟩ : syracuseStep 2335531 = 3503297) B3503297
theorem B3114041 : Blo 2075435 3114041 := bstep (se 2 (by rfl) ⟨1167765, by rfl⟩ : syracuseStep 3114041 = 2335531) B2335531
theorem B2076027 : Blo 2075435 2076027 := bstep (se 1 (by rfl) ⟨1557020, by rfl⟩ : syracuseStep 2076027 = 3114041) B3114041
theorem B4433869 : Blo 2075435 4433869 := bbase (se 3 (by rfl) ⟨831350, by rfl⟩ : syracuseStep 4433869 = 1662701) (by norm_num)
theorem B23647301 : Blo 2075435 23647301 := bstep (se 4 (by rfl) ⟨2216934, by rfl⟩ : syracuseStep 23647301 = 4433869) B4433869
theorem B15764867 : Blo 2075435 15764867 := bstep (se 1 (by rfl) ⟨11823650, by rfl⟩ : syracuseStep 15764867 = 23647301) B23647301
theorem B10509911 : Blo 2075435 10509911 := bstep (se 1 (by rfl) ⟨7882433, by rfl⟩ : syracuseStep 10509911 = 15764867) B15764867
theorem B7006607 : Blo 2075435 7006607 := bstep (se 1 (by rfl) ⟨5254955, by rfl⟩ : syracuseStep 7006607 = 10509911) B10509911
theorem B4671071 : Blo 2075435 4671071 := bstep (se 1 (by rfl) ⟨3503303, by rfl⟩ : syracuseStep 4671071 = 7006607) B7006607
theorem B3114047 : Blo 2075435 3114047 := bstep (se 1 (by rfl) ⟨2335535, by rfl⟩ : syracuseStep 3114047 = 4671071) B4671071
theorem B2076031 : Blo 2075435 2076031 := bstep (se 1 (by rfl) ⟨1557023, by rfl⟩ : syracuseStep 2076031 = 3114047) B3114047
theorem B3114053 : Blo 2075435 3114053 := bbase (se 4 (by rfl) ⟨291942, by rfl⟩ : syracuseStep 3114053 = 583885) (by norm_num)
theorem B2076035 : Blo 2075435 2076035 := bstep (se 1 (by rfl) ⟨1557026, by rfl⟩ : syracuseStep 2076035 = 3114053) B3114053
theorem B3503317 : Blo 2075435 3503317 := bbase (se 7 (by rfl) ⟨41054, by rfl⟩ : syracuseStep 3503317 = 82109) (by norm_num)
theorem B4671089 : Blo 2075435 4671089 := bstep (se 2 (by rfl) ⟨1751658, by rfl⟩ : syracuseStep 4671089 = 3503317) B3503317
theorem B3114059 : Blo 2075435 3114059 := bstep (se 1 (by rfl) ⟨2335544, by rfl⟩ : syracuseStep 3114059 = 4671089) B4671089
theorem B2076039 : Blo 2075435 2076039 := bstep (se 1 (by rfl) ⟨1557029, by rfl⟩ : syracuseStep 2076039 = 3114059) B3114059
theorem B2335549 : Blo 2075435 2335549 := bbase (se 3 (by rfl) ⟨437915, by rfl⟩ : syracuseStep 2335549 = 875831) (by norm_num)
theorem B3114065 : Blo 2075435 3114065 := bstep (se 2 (by rfl) ⟨1167774, by rfl⟩ : syracuseStep 3114065 = 2335549) B2335549
theorem B2076043 : Blo 2075435 2076043 := bstep (se 1 (by rfl) ⟨1557032, by rfl⟩ : syracuseStep 2076043 = 3114065) B3114065
theorem B7006661 : Blo 2075435 7006661 := bbase (se 4 (by rfl) ⟨656874, by rfl⟩ : syracuseStep 7006661 = 1313749) (by norm_num)
theorem B4671107 : Blo 2075435 4671107 := bstep (se 1 (by rfl) ⟨3503330, by rfl⟩ : syracuseStep 4671107 = 7006661) B7006661
theorem B3114071 : Blo 2075435 3114071 := bstep (se 1 (by rfl) ⟨2335553, by rfl⟩ : syracuseStep 3114071 = 4671107) B4671107
theorem B2076047 : Blo 2075435 2076047 := bstep (se 1 (by rfl) ⟨1557035, by rfl⟩ : syracuseStep 2076047 = 3114071) B3114071
theorem B3114077 : Blo 2075435 3114077 := bbase (se 3 (by rfl) ⟨583889, by rfl⟩ : syracuseStep 3114077 = 1167779) (by norm_num)
theorem B2076051 : Blo 2075435 2076051 := bstep (se 1 (by rfl) ⟨1557038, by rfl⟩ : syracuseStep 2076051 = 3114077) B3114077
theorem B4671125 : Blo 2075435 4671125 := bbase (se 6 (by rfl) ⟨109479, by rfl⟩ : syracuseStep 4671125 = 218959) (by norm_num)
theorem B3114083 : Blo 2075435 3114083 := bstep (se 1 (by rfl) ⟨2335562, by rfl⟩ : syracuseStep 3114083 = 4671125) B4671125
theorem B2076055 : Blo 2075435 2076055 := bstep (se 1 (by rfl) ⟨1557041, by rfl⟩ : syracuseStep 2076055 = 3114083) B3114083
theorem B2216965 : Blo 2075435 2216965 := bbase (se 4 (by rfl) ⟨207840, by rfl⟩ : syracuseStep 2216965 = 415681) (by norm_num)
theorem B2955953 : Blo 2075435 2955953 := bstep (se 2 (by rfl) ⟨1108482, by rfl⟩ : syracuseStep 2955953 = 2216965) B2216965
theorem B7882541 : Blo 2075435 7882541 := bstep (se 3 (by rfl) ⟨1477976, by rfl⟩ : syracuseStep 7882541 = 2955953) B2955953
theorem B5255027 : Blo 2075435 5255027 := bstep (se 1 (by rfl) ⟨3941270, by rfl⟩ : syracuseStep 5255027 = 7882541) B7882541
theorem B3503351 : Blo 2075435 3503351 := bstep (se 1 (by rfl) ⟨2627513, by rfl⟩ : syracuseStep 3503351 = 5255027) B5255027
theorem B2335567 : Blo 2075435 2335567 := bstep (se 1 (by rfl) ⟨1751675, by rfl⟩ : syracuseStep 2335567 = 3503351) B3503351
theorem B3114089 : Blo 2075435 3114089 := bstep (se 2 (by rfl) ⟨1167783, by rfl⟩ : syracuseStep 3114089 = 2335567) B2335567
theorem B2076059 : Blo 2075435 2076059 := bstep (se 1 (by rfl) ⟨1557044, by rfl⟩ : syracuseStep 2076059 = 3114089) B3114089
theorem B13301813 : Blo 2075435 13301813 := bbase (se 5 (by rfl) ⟨623522, by rfl⟩ : syracuseStep 13301813 = 1247045) (by norm_num)
theorem B8867875 : Blo 2075435 8867875 := bstep (se 1 (by rfl) ⟨6650906, by rfl⟩ : syracuseStep 8867875 = 13301813) B13301813
theorem B11823833 : Blo 2075435 11823833 := bstep (se 2 (by rfl) ⟨4433937, by rfl⟩ : syracuseStep 11823833 = 8867875) B8867875
theorem B7882555 : Blo 2075435 7882555 := bstep (se 1 (by rfl) ⟨5911916, by rfl⟩ : syracuseStep 7882555 = 11823833) B11823833
theorem B10510073 : Blo 2075435 10510073 := bstep (se 2 (by rfl) ⟨3941277, by rfl⟩ : syracuseStep 10510073 = 7882555) B7882555
theorem B7006715 : Blo 2075435 7006715 := bstep (se 1 (by rfl) ⟨5255036, by rfl⟩ : syracuseStep 7006715 = 10510073) B10510073
theorem B4671143 : Blo 2075435 4671143 := bstep (se 1 (by rfl) ⟨3503357, by rfl⟩ : syracuseStep 4671143 = 7006715) B7006715
theorem B3114095 : Blo 2075435 3114095 := bstep (se 1 (by rfl) ⟨2335571, by rfl⟩ : syracuseStep 3114095 = 4671143) B4671143
theorem B2076063 : Blo 2075435 2076063 := bstep (se 1 (by rfl) ⟨1557047, by rfl⟩ : syracuseStep 2076063 = 3114095) B3114095
theorem B3114101 : Blo 2075435 3114101 := bbase (se 5 (by rfl) ⟨145973, by rfl⟩ : syracuseStep 3114101 = 291947) (by norm_num)
theorem B2076067 : Blo 2075435 2076067 := bstep (se 1 (by rfl) ⟨1557050, by rfl⟩ : syracuseStep 2076067 = 3114101) B3114101
theorem B3941293 : Blo 2075435 3941293 := bbase (se 3 (by rfl) ⟨738992, by rfl⟩ : syracuseStep 3941293 = 1477985) (by norm_num)
theorem B5255057 : Blo 2075435 5255057 := bstep (se 2 (by rfl) ⟨1970646, by rfl⟩ : syracuseStep 5255057 = 3941293) B3941293
theorem B3503371 : Blo 2075435 3503371 := bstep (se 1 (by rfl) ⟨2627528, by rfl⟩ : syracuseStep 3503371 = 5255057) B5255057
theorem B4671161 : Blo 2075435 4671161 := bstep (se 2 (by rfl) ⟨1751685, by rfl⟩ : syracuseStep 4671161 = 3503371) B3503371
theorem B3114107 : Blo 2075435 3114107 := bstep (se 1 (by rfl) ⟨2335580, by rfl⟩ : syracuseStep 3114107 = 4671161) B4671161
theorem B2076071 : Blo 2075435 2076071 := bstep (se 1 (by rfl) ⟨1557053, by rfl⟩ : syracuseStep 2076071 = 3114107) B3114107
theorem B2335585 : Blo 2075435 2335585 := bbase (se 2 (by rfl) ⟨875844, by rfl⟩ : syracuseStep 2335585 = 1751689) (by norm_num)
theorem B3114113 : Blo 2075435 3114113 := bstep (se 2 (by rfl) ⟨1167792, by rfl⟩ : syracuseStep 3114113 = 2335585) B2335585
theorem B2076075 : Blo 2075435 2076075 := bstep (se 1 (by rfl) ⟨1557056, by rfl⟩ : syracuseStep 2076075 = 3114113) B3114113
theorem B5255077 : Blo 2075435 5255077 := bbase (se 4 (by rfl) ⟨492663, by rfl⟩ : syracuseStep 5255077 = 985327) (by norm_num)
theorem B7006769 : Blo 2075435 7006769 := bstep (se 2 (by rfl) ⟨2627538, by rfl⟩ : syracuseStep 7006769 = 5255077) B5255077
theorem B4671179 : Blo 2075435 4671179 := bstep (se 1 (by rfl) ⟨3503384, by rfl⟩ : syracuseStep 4671179 = 7006769) B7006769
theorem B3114119 : Blo 2075435 3114119 := bstep (se 1 (by rfl) ⟨2335589, by rfl⟩ : syracuseStep 3114119 = 4671179) B4671179
theorem B2076079 : Blo 2075435 2076079 := bstep (se 1 (by rfl) ⟨1557059, by rfl⟩ : syracuseStep 2076079 = 3114119) B3114119
theorem B3114125 : Blo 2075435 3114125 := bbase (se 3 (by rfl) ⟨583898, by rfl⟩ : syracuseStep 3114125 = 1167797) (by norm_num)
theorem B2076083 : Blo 2075435 2076083 := bstep (se 1 (by rfl) ⟨1557062, by rfl⟩ : syracuseStep 2076083 = 3114125) B3114125
theorem B4671197 : Blo 2075435 4671197 := bbase (se 3 (by rfl) ⟨875849, by rfl⟩ : syracuseStep 4671197 = 1751699) (by norm_num)
theorem B3114131 : Blo 2075435 3114131 := bstep (se 1 (by rfl) ⟨2335598, by rfl⟩ : syracuseStep 3114131 = 4671197) B4671197
theorem B2076087 : Blo 2075435 2076087 := bstep (se 1 (by rfl) ⟨1557065, by rfl⟩ : syracuseStep 2076087 = 3114131) B3114131
theorem B3503405 : Blo 2075435 3503405 := bbase (se 3 (by rfl) ⟨656888, by rfl⟩ : syracuseStep 3503405 = 1313777) (by norm_num)
theorem B2335603 : Blo 2075435 2335603 := bstep (se 1 (by rfl) ⟨1751702, by rfl⟩ : syracuseStep 2335603 = 3503405) B3503405
theorem B3114137 : Blo 2075435 3114137 := bstep (se 2 (by rfl) ⟨1167801, by rfl⟩ : syracuseStep 3114137 = 2335603) B2335603
theorem B2076091 : Blo 2075435 2076091 := bstep (se 1 (by rfl) ⟨1557068, by rfl⟩ : syracuseStep 2076091 = 3114137) B3114137
theorem B2104421 : Blo 2075435 2104421 := bbase (se 4 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 2104421 = 394579) (by norm_num)
theorem B5611789 : Blo 2075435 5611789 := bstep (se 3 (by rfl) ⟨1052210, by rfl⟩ : syracuseStep 5611789 = 2104421) B2104421
theorem B7482385 : Blo 2075435 7482385 := bstep (se 2 (by rfl) ⟨2805894, by rfl⟩ : syracuseStep 7482385 = 5611789) B5611789
theorem B39906053 : Blo 2075435 39906053 := bstep (se 4 (by rfl) ⟨3741192, by rfl⟩ : syracuseStep 39906053 = 7482385) B7482385
theorem B26604035 : Blo 2075435 26604035 := bstep (se 1 (by rfl) ⟨19953026, by rfl⟩ : syracuseStep 26604035 = 39906053) B39906053
theorem B17736023 : Blo 2075435 17736023 := bstep (se 1 (by rfl) ⟨13302017, by rfl⟩ : syracuseStep 17736023 = 26604035) B26604035
theorem B11824015 : Blo 2075435 11824015 := bstep (se 1 (by rfl) ⟨8868011, by rfl⟩ : syracuseStep 11824015 = 17736023) B17736023
theorem B15765353 : Blo 2075435 15765353 := bstep (se 2 (by rfl) ⟨5912007, by rfl⟩ : syracuseStep 15765353 = 11824015) B11824015
theorem B10510235 : Blo 2075435 10510235 := bstep (se 1 (by rfl) ⟨7882676, by rfl⟩ : syracuseStep 10510235 = 15765353) B15765353
theorem B7006823 : Blo 2075435 7006823 := bstep (se 1 (by rfl) ⟨5255117, by rfl⟩ : syracuseStep 7006823 = 10510235) B10510235
theorem B4671215 : Blo 2075435 4671215 := bstep (se 1 (by rfl) ⟨3503411, by rfl⟩ : syracuseStep 4671215 = 7006823) B7006823
theorem B3114143 : Blo 2075435 3114143 := bstep (se 1 (by rfl) ⟨2335607, by rfl⟩ : syracuseStep 3114143 = 4671215) B4671215
theorem B2076095 : Blo 2075435 2076095 := bstep (se 1 (by rfl) ⟨1557071, by rfl⟩ : syracuseStep 2076095 = 3114143) B3114143
theorem B3114149 : Blo 2075435 3114149 := bbase (se 4 (by rfl) ⟨291951, by rfl⟩ : syracuseStep 3114149 = 583903) (by norm_num)
theorem B2076099 : Blo 2075435 2076099 := bstep (se 1 (by rfl) ⟨1557074, by rfl⟩ : syracuseStep 2076099 = 3114149) B3114149
theorem B2627569 : Blo 2075435 2627569 := bbase (se 2 (by rfl) ⟨985338, by rfl⟩ : syracuseStep 2627569 = 1970677) (by norm_num)
theorem B3503425 : Blo 2075435 3503425 := bstep (se 2 (by rfl) ⟨1313784, by rfl⟩ : syracuseStep 3503425 = 2627569) B2627569
theorem B4671233 : Blo 2075435 4671233 := bstep (se 2 (by rfl) ⟨1751712, by rfl⟩ : syracuseStep 4671233 = 3503425) B3503425
theorem B3114155 : Blo 2075435 3114155 := bstep (se 1 (by rfl) ⟨2335616, by rfl⟩ : syracuseStep 3114155 = 4671233) B4671233
theorem B2076103 : Blo 2075435 2076103 := bstep (se 1 (by rfl) ⟨1557077, by rfl⟩ : syracuseStep 2076103 = 3114155) B3114155
theorem B2335621 : Blo 2075435 2335621 := bbase (se 4 (by rfl) ⟨218964, by rfl⟩ : syracuseStep 2335621 = 437929) (by norm_num)
theorem B3114161 : Blo 2075435 3114161 := bstep (se 2 (by rfl) ⟨1167810, by rfl⟩ : syracuseStep 3114161 = 2335621) B2335621
theorem B2076107 : Blo 2075435 2076107 := bstep (se 1 (by rfl) ⟨1557080, by rfl⟩ : syracuseStep 2076107 = 3114161) B3114161
theorem B9469973 : Blo 2075435 9469973 := bbase (se 6 (by rfl) ⟨221952, by rfl⟩ : syracuseStep 9469973 = 443905) (by norm_num)
theorem B6313315 : Blo 2075435 6313315 := bstep (se 1 (by rfl) ⟨4734986, by rfl⟩ : syracuseStep 6313315 = 9469973) B9469973
theorem B8417753 : Blo 2075435 8417753 := bstep (se 2 (by rfl) ⟨3156657, by rfl⟩ : syracuseStep 8417753 = 6313315) B6313315
theorem B5611835 : Blo 2075435 5611835 := bstep (se 1 (by rfl) ⟨4208876, by rfl⟩ : syracuseStep 5611835 = 8417753) B8417753
theorem B3741223 : Blo 2075435 3741223 := bstep (se 1 (by rfl) ⟨2805917, by rfl⟩ : syracuseStep 3741223 = 5611835) B5611835
theorem B4988297 : Blo 2075435 4988297 := bstep (se 2 (by rfl) ⟨1870611, by rfl⟩ : syracuseStep 4988297 = 3741223) B3741223
theorem B3325531 : Blo 2075435 3325531 := bstep (se 1 (by rfl) ⟨2494148, by rfl⟩ : syracuseStep 3325531 = 4988297) B4988297
theorem B4434041 : Blo 2075435 4434041 := bstep (se 2 (by rfl) ⟨1662765, by rfl⟩ : syracuseStep 4434041 = 3325531) B3325531
theorem B2956027 : Blo 2075435 2956027 := bstep (se 1 (by rfl) ⟨2217020, by rfl⟩ : syracuseStep 2956027 = 4434041) B4434041
theorem B3941369 : Blo 2075435 3941369 := bstep (se 2 (by rfl) ⟨1478013, by rfl⟩ : syracuseStep 3941369 = 2956027) B2956027
theorem B2627579 : Blo 2075435 2627579 := bstep (se 1 (by rfl) ⟨1970684, by rfl⟩ : syracuseStep 2627579 = 3941369) B3941369
theorem B7006877 : Blo 2075435 7006877 := bstep (se 3 (by rfl) ⟨1313789, by rfl⟩ : syracuseStep 7006877 = 2627579) B2627579
theorem B4671251 : Blo 2075435 4671251 := bstep (se 1 (by rfl) ⟨3503438, by rfl⟩ : syracuseStep 4671251 = 7006877) B7006877
theorem B3114167 : Blo 2075435 3114167 := bstep (se 1 (by rfl) ⟨2335625, by rfl⟩ : syracuseStep 3114167 = 4671251) B4671251
theorem B2076111 : Blo 2075435 2076111 := bstep (se 1 (by rfl) ⟨1557083, by rfl⟩ : syracuseStep 2076111 = 3114167) B3114167
theorem B3114173 : Blo 2075435 3114173 := bbase (se 3 (by rfl) ⟨583907, by rfl⟩ : syracuseStep 3114173 = 1167815) (by norm_num)
theorem B2076115 : Blo 2075435 2076115 := bstep (se 1 (by rfl) ⟨1557086, by rfl⟩ : syracuseStep 2076115 = 3114173) B3114173
theorem B4671269 : Blo 2075435 4671269 := bbase (se 4 (by rfl) ⟨437931, by rfl⟩ : syracuseStep 4671269 = 875863) (by norm_num)
theorem B3114179 : Blo 2075435 3114179 := bstep (se 1 (by rfl) ⟨2335634, by rfl⟩ : syracuseStep 3114179 = 4671269) B4671269
theorem B2076119 : Blo 2075435 2076119 := bstep (se 1 (by rfl) ⟨1557089, by rfl⟩ : syracuseStep 2076119 = 3114179) B3114179
theorem B5255189 : Blo 2075435 5255189 := bbase (se 6 (by rfl) ⟨123168, by rfl⟩ : syracuseStep 5255189 = 246337) (by norm_num)
theorem B3503459 : Blo 2075435 3503459 := bstep (se 1 (by rfl) ⟨2627594, by rfl⟩ : syracuseStep 3503459 = 5255189) B5255189
theorem B2335639 : Blo 2075435 2335639 := bstep (se 1 (by rfl) ⟨1751729, by rfl⟩ : syracuseStep 2335639 = 3503459) B3503459
theorem B3114185 : Blo 2075435 3114185 := bstep (se 2 (by rfl) ⟨1167819, by rfl⟩ : syracuseStep 3114185 = 2335639) B2335639
theorem B2076123 : Blo 2075435 2076123 := bstep (se 1 (by rfl) ⟨1557092, by rfl⟩ : syracuseStep 2076123 = 3114185) B3114185
theorem B8868149 : Blo 2075435 8868149 := bbase (se 5 (by rfl) ⟨415694, by rfl⟩ : syracuseStep 8868149 = 831389) (by norm_num)
theorem B5912099 : Blo 2075435 5912099 := bstep (se 1 (by rfl) ⟨4434074, by rfl⟩ : syracuseStep 5912099 = 8868149) B8868149
theorem B3941399 : Blo 2075435 3941399 := bstep (se 1 (by rfl) ⟨2956049, by rfl⟩ : syracuseStep 3941399 = 5912099) B5912099
theorem B10510397 : Blo 2075435 10510397 := bstep (se 3 (by rfl) ⟨1970699, by rfl⟩ : syracuseStep 10510397 = 3941399) B3941399
theorem B7006931 : Blo 2075435 7006931 := bstep (se 1 (by rfl) ⟨5255198, by rfl⟩ : syracuseStep 7006931 = 10510397) B10510397
theorem B4671287 : Blo 2075435 4671287 := bstep (se 1 (by rfl) ⟨3503465, by rfl⟩ : syracuseStep 4671287 = 7006931) B7006931
theorem B3114191 : Blo 2075435 3114191 := bstep (se 1 (by rfl) ⟨2335643, by rfl⟩ : syracuseStep 3114191 = 4671287) B4671287
theorem B2076127 : Blo 2075435 2076127 := bstep (se 1 (by rfl) ⟨1557095, by rfl⟩ : syracuseStep 2076127 = 3114191) B3114191
theorem B3114197 : Blo 2075435 3114197 := bbase (se 7 (by rfl) ⟨36494, by rfl⟩ : syracuseStep 3114197 = 72989) (by norm_num)
theorem B2076131 : Blo 2075435 2076131 := bstep (se 1 (by rfl) ⟨1557098, by rfl⟩ : syracuseStep 2076131 = 3114197) B3114197
theorem B2956061 : Blo 2075435 2956061 := bbase (se 3 (by rfl) ⟨554261, by rfl⟩ : syracuseStep 2956061 = 1108523) (by norm_num)
theorem B7882829 : Blo 2075435 7882829 := bstep (se 3 (by rfl) ⟨1478030, by rfl⟩ : syracuseStep 7882829 = 2956061) B2956061
theorem B5255219 : Blo 2075435 5255219 := bstep (se 1 (by rfl) ⟨3941414, by rfl⟩ : syracuseStep 5255219 = 7882829) B7882829
theorem B3503479 : Blo 2075435 3503479 := bstep (se 1 (by rfl) ⟨2627609, by rfl⟩ : syracuseStep 3503479 = 5255219) B5255219
theorem B4671305 : Blo 2075435 4671305 := bstep (se 2 (by rfl) ⟨1751739, by rfl⟩ : syracuseStep 4671305 = 3503479) B3503479
theorem B3114203 : Blo 2075435 3114203 := bstep (se 1 (by rfl) ⟨2335652, by rfl⟩ : syracuseStep 3114203 = 4671305) B4671305
theorem B2076135 : Blo 2075435 2076135 := bstep (se 1 (by rfl) ⟨1557101, by rfl⟩ : syracuseStep 2076135 = 3114203) B3114203
theorem B2335657 : Blo 2075435 2335657 := bbase (se 2 (by rfl) ⟨875871, by rfl⟩ : syracuseStep 2335657 = 1751743) (by norm_num)
theorem B3114209 : Blo 2075435 3114209 := bstep (se 2 (by rfl) ⟨1167828, by rfl⟩ : syracuseStep 3114209 = 2335657) B2335657
theorem B2076139 : Blo 2075435 2076139 := bstep (se 1 (by rfl) ⟨1557104, by rfl⟩ : syracuseStep 2076139 = 3114209) B3114209
theorem B51196373 : Blo 2075435 51196373 := bbase (se 7 (by rfl) ⟨599957, by rfl⟩ : syracuseStep 51196373 = 1199915) (by norm_num)
theorem B34130915 : Blo 2075435 34130915 := bstep (se 1 (by rfl) ⟨25598186, by rfl⟩ : syracuseStep 34130915 = 51196373) B51196373
theorem B22753943 : Blo 2075435 22753943 := bstep (se 1 (by rfl) ⟨17065457, by rfl⟩ : syracuseStep 22753943 = 34130915) B34130915
theorem B15169295 : Blo 2075435 15169295 := bstep (se 1 (by rfl) ⟨11376971, by rfl⟩ : syracuseStep 15169295 = 22753943) B22753943
theorem B10112863 : Blo 2075435 10112863 := bstep (se 1 (by rfl) ⟨7584647, by rfl⟩ : syracuseStep 10112863 = 15169295) B15169295
theorem B13483817 : Blo 2075435 13483817 := bstep (se 2 (by rfl) ⟨5056431, by rfl⟩ : syracuseStep 13483817 = 10112863) B10112863
theorem B8989211 : Blo 2075435 8989211 := bstep (se 1 (by rfl) ⟨6741908, by rfl⟩ : syracuseStep 8989211 = 13483817) B13483817
theorem B23971229 : Blo 2075435 23971229 := bstep (se 3 (by rfl) ⟨4494605, by rfl⟩ : syracuseStep 23971229 = 8989211) B8989211
theorem B15980819 : Blo 2075435 15980819 := bstep (se 1 (by rfl) ⟨11985614, by rfl⟩ : syracuseStep 15980819 = 23971229) B23971229
theorem B42615517 : Blo 2075435 42615517 := bstep (se 3 (by rfl) ⟨7990409, by rfl⟩ : syracuseStep 42615517 = 15980819) B15980819
theorem B56820689 : Blo 2075435 56820689 := bstep (se 2 (by rfl) ⟨21307758, by rfl⟩ : syracuseStep 56820689 = 42615517) B42615517
theorem B37880459 : Blo 2075435 37880459 := bstep (se 1 (by rfl) ⟨28410344, by rfl⟩ : syracuseStep 37880459 = 56820689) B56820689
theorem B25253639 : Blo 2075435 25253639 := bstep (se 1 (by rfl) ⟨18940229, by rfl⟩ : syracuseStep 25253639 = 37880459) B37880459
theorem B16835759 : Blo 2075435 16835759 := bstep (se 1 (by rfl) ⟨12626819, by rfl⟩ : syracuseStep 16835759 = 25253639) B25253639
theorem B11223839 : Blo 2075435 11223839 := bstep (se 1 (by rfl) ⟨8417879, by rfl⟩ : syracuseStep 11223839 = 16835759) B16835759
theorem B7482559 : Blo 2075435 7482559 := bstep (se 1 (by rfl) ⟨5611919, by rfl⟩ : syracuseStep 7482559 = 11223839) B11223839
theorem B9976745 : Blo 2075435 9976745 := bstep (se 2 (by rfl) ⟨3741279, by rfl⟩ : syracuseStep 9976745 = 7482559) B7482559
theorem B6651163 : Blo 2075435 6651163 := bstep (se 1 (by rfl) ⟨4988372, by rfl⟩ : syracuseStep 6651163 = 9976745) B9976745
theorem B8868217 : Blo 2075435 8868217 := bstep (se 2 (by rfl) ⟨3325581, by rfl⟩ : syracuseStep 8868217 = 6651163) B6651163
theorem B11824289 : Blo 2075435 11824289 := bstep (se 2 (by rfl) ⟨4434108, by rfl⟩ : syracuseStep 11824289 = 8868217) B8868217
theorem B7882859 : Blo 2075435 7882859 := bstep (se 1 (by rfl) ⟨5912144, by rfl⟩ : syracuseStep 7882859 = 11824289) B11824289
theorem B5255239 : Blo 2075435 5255239 := bstep (se 1 (by rfl) ⟨3941429, by rfl⟩ : syracuseStep 5255239 = 7882859) B7882859
theorem B7006985 : Blo 2075435 7006985 := bstep (se 2 (by rfl) ⟨2627619, by rfl⟩ : syracuseStep 7006985 = 5255239) B5255239
theorem B4671323 : Blo 2075435 4671323 := bstep (se 1 (by rfl) ⟨3503492, by rfl⟩ : syracuseStep 4671323 = 7006985) B7006985
theorem B3114215 : Blo 2075435 3114215 := bstep (se 1 (by rfl) ⟨2335661, by rfl⟩ : syracuseStep 3114215 = 4671323) B4671323
theorem B2076143 : Blo 2075435 2076143 := bstep (se 1 (by rfl) ⟨1557107, by rfl⟩ : syracuseStep 2076143 = 3114215) B3114215
theorem B3114221 : Blo 2075435 3114221 := bbase (se 3 (by rfl) ⟨583916, by rfl⟩ : syracuseStep 3114221 = 1167833) (by norm_num)
theorem B2076147 : Blo 2075435 2076147 := bstep (se 1 (by rfl) ⟨1557110, by rfl⟩ : syracuseStep 2076147 = 3114221) B3114221
theorem B4671341 : Blo 2075435 4671341 := bbase (se 3 (by rfl) ⟨875876, by rfl⟩ : syracuseStep 4671341 = 1751753) (by norm_num)
theorem B3114227 : Blo 2075435 3114227 := bstep (se 1 (by rfl) ⟨2335670, by rfl⟩ : syracuseStep 3114227 = 4671341) B4671341
theorem B2076151 : Blo 2075435 2076151 := bstep (se 1 (by rfl) ⟨1557113, by rfl⟩ : syracuseStep 2076151 = 3114227) B3114227
theorem B3941453 : Blo 2075435 3941453 := bbase (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) (by norm_num)
theorem B2627635 : Blo 2075435 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B3503513 : Blo 2075435 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B2335675 : Blo 2075435 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B3114233 : Blo 2075435 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B2076155 : Blo 2075435 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B5056469 : Blo 2075435 5056469 := bbase (se 7 (by rfl) ⟨59255, by rfl⟩ : syracuseStep 5056469 = 118511) (by norm_num)
theorem B53935669 : Blo 2075435 53935669 := bstep (se 5 (by rfl) ⟨2528234, by rfl⟩ : syracuseStep 53935669 = 5056469) B5056469
theorem B71914225 : Blo 2075435 71914225 := bstep (se 2 (by rfl) ⟨26967834, by rfl⟩ : syracuseStep 71914225 = 53935669) B53935669
theorem B95885633 : Blo 2075435 95885633 := bstep (se 2 (by rfl) ⟨35957112, by rfl⟩ : syracuseStep 95885633 = 71914225) B71914225
theorem B63923755 : Blo 2075435 63923755 := bstep (se 1 (by rfl) ⟨47942816, by rfl⟩ : syracuseStep 63923755 = 95885633) B95885633
theorem B85231673 : Blo 2075435 85231673 := bstep (se 2 (by rfl) ⟨31961877, by rfl⟩ : syracuseStep 85231673 = 63923755) B63923755
theorem B56821115 : Blo 2075435 56821115 := bstep (se 1 (by rfl) ⟨42615836, by rfl⟩ : syracuseStep 56821115 = 85231673) B85231673
theorem B37880743 : Blo 2075435 37880743 := bstep (se 1 (by rfl) ⟨28410557, by rfl⟩ : syracuseStep 37880743 = 56821115) B56821115
theorem B50507657 : Blo 2075435 50507657 := bstep (se 2 (by rfl) ⟨18940371, by rfl⟩ : syracuseStep 50507657 = 37880743) B37880743
theorem B33671771 : Blo 2075435 33671771 := bstep (se 1 (by rfl) ⟨25253828, by rfl⟩ : syracuseStep 33671771 = 50507657) B50507657
theorem B22447847 : Blo 2075435 22447847 := bstep (se 1 (by rfl) ⟨16835885, by rfl⟩ : syracuseStep 22447847 = 33671771) B33671771
theorem B14965231 : Blo 2075435 14965231 := bstep (se 1 (by rfl) ⟨11223923, by rfl⟩ : syracuseStep 14965231 = 22447847) B22447847
theorem B19953641 : Blo 2075435 19953641 := bstep (se 2 (by rfl) ⟨7482615, by rfl⟩ : syracuseStep 19953641 = 14965231) B14965231
theorem B53209709 : Blo 2075435 53209709 := bstep (se 3 (by rfl) ⟨9976820, by rfl⟩ : syracuseStep 53209709 = 19953641) B19953641
theorem B35473139 : Blo 2075435 35473139 := bstep (se 1 (by rfl) ⟨26604854, by rfl⟩ : syracuseStep 35473139 = 53209709) B53209709
theorem B23648759 : Blo 2075435 23648759 := bstep (se 1 (by rfl) ⟨17736569, by rfl⟩ : syracuseStep 23648759 = 35473139) B35473139
theorem B15765839 : Blo 2075435 15765839 := bstep (se 1 (by rfl) ⟨11824379, by rfl⟩ : syracuseStep 15765839 = 23648759) B23648759
theorem B10510559 : Blo 2075435 10510559 := bstep (se 1 (by rfl) ⟨7882919, by rfl⟩ : syracuseStep 10510559 = 15765839) B15765839
theorem B7007039 : Blo 2075435 7007039 := bstep (se 1 (by rfl) ⟨5255279, by rfl⟩ : syracuseStep 7007039 = 10510559) B10510559
theorem B4671359 : Blo 2075435 4671359 := bstep (se 1 (by rfl) ⟨3503519, by rfl⟩ : syracuseStep 4671359 = 7007039) B7007039
theorem B3114239 : Blo 2075435 3114239 := bstep (se 1 (by rfl) ⟨2335679, by rfl⟩ : syracuseStep 3114239 = 4671359) B4671359
theorem B2076159 : Blo 2075435 2076159 := bstep (se 1 (by rfl) ⟨1557119, by rfl⟩ : syracuseStep 2076159 = 3114239) B3114239
theorem B3114245 : Blo 2075435 3114245 := bbase (se 4 (by rfl) ⟨291960, by rfl⟩ : syracuseStep 3114245 = 583921) (by norm_num)
theorem B2076163 : Blo 2075435 2076163 := bstep (se 1 (by rfl) ⟨1557122, by rfl⟩ : syracuseStep 2076163 = 3114245) B3114245
theorem B3503533 : Blo 2075435 3503533 := bbase (se 3 (by rfl) ⟨656912, by rfl⟩ : syracuseStep 3503533 = 1313825) (by norm_num)
theorem B4671377 : Blo 2075435 4671377 := bstep (se 2 (by rfl) ⟨1751766, by rfl⟩ : syracuseStep 4671377 = 3503533) B3503533
theorem B3114251 : Blo 2075435 3114251 := bstep (se 1 (by rfl) ⟨2335688, by rfl⟩ : syracuseStep 3114251 = 4671377) B4671377
theorem B2076167 : Blo 2075435 2076167 := bstep (se 1 (by rfl) ⟨1557125, by rfl⟩ : syracuseStep 2076167 = 3114251) B3114251
theorem B2335693 : Blo 2075435 2335693 := bbase (se 3 (by rfl) ⟨437942, by rfl⟩ : syracuseStep 2335693 = 875885) (by norm_num)
theorem B3114257 : Blo 2075435 3114257 := bstep (se 2 (by rfl) ⟨1167846, by rfl⟩ : syracuseStep 3114257 = 2335693) B2335693
theorem B2076171 : Blo 2075435 2076171 := bstep (se 1 (by rfl) ⟨1557128, by rfl⟩ : syracuseStep 2076171 = 3114257) B3114257
theorem B7007093 : Blo 2075435 7007093 := bbase (se 5 (by rfl) ⟨328457, by rfl⟩ : syracuseStep 7007093 = 656915) (by norm_num)
theorem B4671395 : Blo 2075435 4671395 := bstep (se 1 (by rfl) ⟨3503546, by rfl⟩ : syracuseStep 4671395 = 7007093) B7007093
theorem B3114263 : Blo 2075435 3114263 := bstep (se 1 (by rfl) ⟨2335697, by rfl⟩ : syracuseStep 3114263 = 4671395) B4671395
theorem B2076175 : Blo 2075435 2076175 := bstep (se 1 (by rfl) ⟨1557131, by rfl⟩ : syracuseStep 2076175 = 3114263) B3114263
theorem B3114269 : Blo 2075435 3114269 := bbase (se 3 (by rfl) ⟨583925, by rfl⟩ : syracuseStep 3114269 = 1167851) (by norm_num)
theorem B2076179 : Blo 2075435 2076179 := bstep (se 1 (by rfl) ⟨1557134, by rfl⟩ : syracuseStep 2076179 = 3114269) B3114269
theorem B4671413 : Blo 2075435 4671413 := bbase (se 5 (by rfl) ⟨218972, by rfl⟩ : syracuseStep 4671413 = 437945) (by norm_num)
theorem B3114275 : Blo 2075435 3114275 := bstep (se 1 (by rfl) ⟨2335706, by rfl⟩ : syracuseStep 3114275 = 4671413) B4671413
theorem B2076183 : Blo 2075435 2076183 := bstep (se 1 (by rfl) ⟨1557137, by rfl⟩ : syracuseStep 2076183 = 3114275) B3114275
theorem B4799765 : Blo 2075435 4799765 := bbase (se 6 (by rfl) ⟨112494, by rfl⟩ : syracuseStep 4799765 = 224989) (by norm_num)
theorem B3199843 : Blo 2075435 3199843 := bstep (se 1 (by rfl) ⟨2399882, by rfl⟩ : syracuseStep 3199843 = 4799765) B4799765
theorem B17065829 : Blo 2075435 17065829 := bstep (se 4 (by rfl) ⟨1599921, by rfl⟩ : syracuseStep 17065829 = 3199843) B3199843
theorem B11377219 : Blo 2075435 11377219 := bstep (se 1 (by rfl) ⟨8532914, by rfl⟩ : syracuseStep 11377219 = 17065829) B17065829
theorem B15169625 : Blo 2075435 15169625 := bstep (se 2 (by rfl) ⟨5688609, by rfl⟩ : syracuseStep 15169625 = 11377219) B11377219
theorem B10113083 : Blo 2075435 10113083 := bstep (se 1 (by rfl) ⟨7584812, by rfl⟩ : syracuseStep 10113083 = 15169625) B15169625
theorem B6742055 : Blo 2075435 6742055 := bstep (se 1 (by rfl) ⟨5056541, by rfl⟩ : syracuseStep 6742055 = 10113083) B10113083
theorem B4494703 : Blo 2075435 4494703 := bstep (se 1 (by rfl) ⟨3371027, by rfl⟩ : syracuseStep 4494703 = 6742055) B6742055
theorem B5992937 : Blo 2075435 5992937 := bstep (se 2 (by rfl) ⟨2247351, by rfl⟩ : syracuseStep 5992937 = 4494703) B4494703
theorem B3995291 : Blo 2075435 3995291 := bstep (se 1 (by rfl) ⟨2996468, by rfl⟩ : syracuseStep 3995291 = 5992937) B5992937
theorem B2663527 : Blo 2075435 2663527 := bstep (se 1 (by rfl) ⟨1997645, by rfl⟩ : syracuseStep 2663527 = 3995291) B3995291
theorem B3551369 : Blo 2075435 3551369 := bstep (se 2 (by rfl) ⟨1331763, by rfl⟩ : syracuseStep 3551369 = 2663527) B2663527
theorem B37881269 : Blo 2075435 37881269 := bstep (se 5 (by rfl) ⟨1775684, by rfl⟩ : syracuseStep 37881269 = 3551369) B3551369
theorem B25254179 : Blo 2075435 25254179 := bstep (se 1 (by rfl) ⟨18940634, by rfl⟩ : syracuseStep 25254179 = 37881269) B37881269
theorem B16836119 : Blo 2075435 16836119 := bstep (se 1 (by rfl) ⟨12627089, by rfl⟩ : syracuseStep 16836119 = 25254179) B25254179
theorem B11224079 : Blo 2075435 11224079 := bstep (se 1 (by rfl) ⟨8418059, by rfl⟩ : syracuseStep 11224079 = 16836119) B16836119
theorem B7482719 : Blo 2075435 7482719 := bstep (se 1 (by rfl) ⟨5612039, by rfl⟩ : syracuseStep 7482719 = 11224079) B11224079
theorem B4988479 : Blo 2075435 4988479 := bstep (se 1 (by rfl) ⟨3741359, by rfl⟩ : syracuseStep 4988479 = 7482719) B7482719
theorem B6651305 : Blo 2075435 6651305 := bstep (se 2 (by rfl) ⟨2494239, by rfl⟩ : syracuseStep 6651305 = 4988479) B4988479
theorem B4434203 : Blo 2075435 4434203 := bstep (se 1 (by rfl) ⟨3325652, by rfl⟩ : syracuseStep 4434203 = 6651305) B6651305
theorem B11824541 : Blo 2075435 11824541 := bstep (se 3 (by rfl) ⟨2217101, by rfl⟩ : syracuseStep 11824541 = 4434203) B4434203
theorem B7883027 : Blo 2075435 7883027 := bstep (se 1 (by rfl) ⟨5912270, by rfl⟩ : syracuseStep 7883027 = 11824541) B11824541
theorem B5255351 : Blo 2075435 5255351 := bstep (se 1 (by rfl) ⟨3941513, by rfl⟩ : syracuseStep 5255351 = 7883027) B7883027
theorem B3503567 : Blo 2075435 3503567 := bstep (se 1 (by rfl) ⟨2627675, by rfl⟩ : syracuseStep 3503567 = 5255351) B5255351
theorem B2335711 : Blo 2075435 2335711 := bstep (se 1 (by rfl) ⟨1751783, by rfl⟩ : syracuseStep 2335711 = 3503567) B3503567
theorem B3114281 : Blo 2075435 3114281 := bstep (se 2 (by rfl) ⟨1167855, by rfl⟩ : syracuseStep 3114281 = 2335711) B2335711
theorem B2076187 : Blo 2075435 2076187 := bstep (se 1 (by rfl) ⟨1557140, by rfl⟩ : syracuseStep 2076187 = 3114281) B3114281
theorem B6651317 : Blo 2075435 6651317 := bbase (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) (by norm_num)
theorem B4434211 : Blo 2075435 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B5912281 : Blo 2075435 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B7883041 : Blo 2075435 7883041 := bstep (se 2 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 7883041 = 5912281) B5912281
theorem B10510721 : Blo 2075435 10510721 := bstep (se 2 (by rfl) ⟨3941520, by rfl⟩ : syracuseStep 10510721 = 7883041) B7883041
theorem B7007147 : Blo 2075435 7007147 := bstep (se 1 (by rfl) ⟨5255360, by rfl⟩ : syracuseStep 7007147 = 10510721) B10510721
theorem B4671431 : Blo 2075435 4671431 := bstep (se 1 (by rfl) ⟨3503573, by rfl⟩ : syracuseStep 4671431 = 7007147) B7007147
theorem B3114287 : Blo 2075435 3114287 := bstep (se 1 (by rfl) ⟨2335715, by rfl⟩ : syracuseStep 3114287 = 4671431) B4671431
theorem B2076191 : Blo 2075435 2076191 := bstep (se 1 (by rfl) ⟨1557143, by rfl⟩ : syracuseStep 2076191 = 3114287) B3114287
theorem B3114293 : Blo 2075435 3114293 := bbase (se 5 (by rfl) ⟨145982, by rfl⟩ : syracuseStep 3114293 = 291965) (by norm_num)
theorem B2076195 : Blo 2075435 2076195 := bstep (se 1 (by rfl) ⟨1557146, by rfl⟩ : syracuseStep 2076195 = 3114293) B3114293
theorem B5255381 : Blo 2075435 5255381 := bbase (se 7 (by rfl) ⟨61586, by rfl⟩ : syracuseStep 5255381 = 123173) (by norm_num)
theorem B3503587 : Blo 2075435 3503587 := bstep (se 1 (by rfl) ⟨2627690, by rfl⟩ : syracuseStep 3503587 = 5255381) B5255381
theorem B4671449 : Blo 2075435 4671449 := bstep (se 2 (by rfl) ⟨1751793, by rfl⟩ : syracuseStep 4671449 = 3503587) B3503587
theorem B3114299 : Blo 2075435 3114299 := bstep (se 1 (by rfl) ⟨2335724, by rfl⟩ : syracuseStep 3114299 = 4671449) B4671449
theorem B2076199 : Blo 2075435 2076199 := bstep (se 1 (by rfl) ⟨1557149, by rfl⟩ : syracuseStep 2076199 = 3114299) B3114299
theorem B2335729 : Blo 2075435 2335729 := bbase (se 2 (by rfl) ⟨875898, by rfl⟩ : syracuseStep 2335729 = 1751797) (by norm_num)
theorem B3114305 : Blo 2075435 3114305 := bstep (se 2 (by rfl) ⟨1167864, by rfl⟩ : syracuseStep 3114305 = 2335729) B2335729
theorem B2076203 : Blo 2075435 2076203 := bstep (se 1 (by rfl) ⟨1557152, by rfl⟩ : syracuseStep 2076203 = 3114305) B3114305
theorem B4735205 : Blo 2075435 4735205 := bbase (se 4 (by rfl) ⟨443925, by rfl⟩ : syracuseStep 4735205 = 887851) (by norm_num)
theorem B3156803 : Blo 2075435 3156803 := bstep (se 1 (by rfl) ⟨2367602, by rfl⟩ : syracuseStep 3156803 = 4735205) B4735205
theorem B2104535 : Blo 2075435 2104535 := bstep (se 1 (by rfl) ⟨1578401, by rfl⟩ : syracuseStep 2104535 = 3156803) B3156803
theorem B5612093 : Blo 2075435 5612093 := bstep (se 3 (by rfl) ⟨1052267, by rfl⟩ : syracuseStep 5612093 = 2104535) B2104535
theorem B3741395 : Blo 2075435 3741395 := bstep (se 1 (by rfl) ⟨2806046, by rfl⟩ : syracuseStep 3741395 = 5612093) B5612093
theorem B9977053 : Blo 2075435 9977053 := bstep (se 3 (by rfl) ⟨1870697, by rfl⟩ : syracuseStep 9977053 = 3741395) B3741395
theorem B13302737 : Blo 2075435 13302737 := bstep (se 2 (by rfl) ⟨4988526, by rfl⟩ : syracuseStep 13302737 = 9977053) B9977053
theorem B8868491 : Blo 2075435 8868491 := bstep (se 1 (by rfl) ⟨6651368, by rfl⟩ : syracuseStep 8868491 = 13302737) B13302737
theorem B5912327 : Blo 2075435 5912327 := bstep (se 1 (by rfl) ⟨4434245, by rfl⟩ : syracuseStep 5912327 = 8868491) B8868491
theorem B3941551 : Blo 2075435 3941551 := bstep (se 1 (by rfl) ⟨2956163, by rfl⟩ : syracuseStep 3941551 = 5912327) B5912327
theorem B5255401 : Blo 2075435 5255401 := bstep (se 2 (by rfl) ⟨1970775, by rfl⟩ : syracuseStep 5255401 = 3941551) B3941551
theorem B7007201 : Blo 2075435 7007201 := bstep (se 2 (by rfl) ⟨2627700, by rfl⟩ : syracuseStep 7007201 = 5255401) B5255401
theorem B4671467 : Blo 2075435 4671467 := bstep (se 1 (by rfl) ⟨3503600, by rfl⟩ : syracuseStep 4671467 = 7007201) B7007201
theorem B3114311 : Blo 2075435 3114311 := bstep (se 1 (by rfl) ⟨2335733, by rfl⟩ : syracuseStep 3114311 = 4671467) B4671467
theorem B2076207 : Blo 2075435 2076207 := bstep (se 1 (by rfl) ⟨1557155, by rfl⟩ : syracuseStep 2076207 = 3114311) B3114311
theorem B3114317 : Blo 2075435 3114317 := bbase (se 3 (by rfl) ⟨583934, by rfl⟩ : syracuseStep 3114317 = 1167869) (by norm_num)
theorem B2076211 : Blo 2075435 2076211 := bstep (se 1 (by rfl) ⟨1557158, by rfl⟩ : syracuseStep 2076211 = 3114317) B3114317
theorem B4671485 : Blo 2075435 4671485 := bbase (se 3 (by rfl) ⟨875903, by rfl⟩ : syracuseStep 4671485 = 1751807) (by norm_num)
theorem B3114323 : Blo 2075435 3114323 := bstep (se 1 (by rfl) ⟨2335742, by rfl⟩ : syracuseStep 3114323 = 4671485) B4671485
theorem B2076215 : Blo 2075435 2076215 := bstep (se 1 (by rfl) ⟨1557161, by rfl⟩ : syracuseStep 2076215 = 3114323) B3114323
theorem B3503621 : Blo 2075435 3503621 := bbase (se 4 (by rfl) ⟨328464, by rfl⟩ : syracuseStep 3503621 = 656929) (by norm_num)
theorem B2335747 : Blo 2075435 2335747 := bstep (se 1 (by rfl) ⟨1751810, by rfl⟩ : syracuseStep 2335747 = 3503621) B3503621
theorem B3114329 : Blo 2075435 3114329 := bstep (se 2 (by rfl) ⟨1167873, by rfl⟩ : syracuseStep 3114329 = 2335747) B2335747
theorem B2076219 : Blo 2075435 2076219 := bstep (se 1 (by rfl) ⟨1557164, by rfl⟩ : syracuseStep 2076219 = 3114329) B3114329
theorem B15766325 : Blo 2075435 15766325 := bbase (se 5 (by rfl) ⟨739046, by rfl⟩ : syracuseStep 15766325 = 1478093) (by norm_num)
theorem B10510883 : Blo 2075435 10510883 := bstep (se 1 (by rfl) ⟨7883162, by rfl⟩ : syracuseStep 10510883 = 15766325) B15766325
theorem B7007255 : Blo 2075435 7007255 := bstep (se 1 (by rfl) ⟨5255441, by rfl⟩ : syracuseStep 7007255 = 10510883) B10510883
theorem B4671503 : Blo 2075435 4671503 := bstep (se 1 (by rfl) ⟨3503627, by rfl⟩ : syracuseStep 4671503 = 7007255) B7007255
theorem B3114335 : Blo 2075435 3114335 := bstep (se 1 (by rfl) ⟨2335751, by rfl⟩ : syracuseStep 3114335 = 4671503) B4671503
theorem B2076223 : Blo 2075435 2076223 := bstep (se 1 (by rfl) ⟨1557167, by rfl⟩ : syracuseStep 2076223 = 3114335) B3114335
theorem B3114341 : Blo 2075435 3114341 := bbase (se 4 (by rfl) ⟨291969, by rfl⟩ : syracuseStep 3114341 = 583939) (by norm_num)
theorem B2076227 : Blo 2075435 2076227 := bstep (se 1 (by rfl) ⟨1557170, by rfl⟩ : syracuseStep 2076227 = 3114341) B3114341
theorem B3941597 : Blo 2075435 3941597 := bbase (se 3 (by rfl) ⟨739049, by rfl⟩ : syracuseStep 3941597 = 1478099) (by norm_num)
theorem B2627731 : Blo 2075435 2627731 := bstep (se 1 (by rfl) ⟨1970798, by rfl⟩ : syracuseStep 2627731 = 3941597) B3941597
theorem B3503641 : Blo 2075435 3503641 := bstep (se 2 (by rfl) ⟨1313865, by rfl⟩ : syracuseStep 3503641 = 2627731) B2627731
theorem B4671521 : Blo 2075435 4671521 := bstep (se 2 (by rfl) ⟨1751820, by rfl⟩ : syracuseStep 4671521 = 3503641) B3503641
theorem B3114347 : Blo 2075435 3114347 := bstep (se 1 (by rfl) ⟨2335760, by rfl⟩ : syracuseStep 3114347 = 4671521) B4671521
theorem B2076231 : Blo 2075435 2076231 := bstep (se 1 (by rfl) ⟨1557173, by rfl⟩ : syracuseStep 2076231 = 3114347) B3114347
theorem B2335765 : Blo 2075435 2335765 := bbase (se 6 (by rfl) ⟨54744, by rfl⟩ : syracuseStep 2335765 = 109489) (by norm_num)
theorem B3114353 : Blo 2075435 3114353 := bstep (se 2 (by rfl) ⟨1167882, by rfl⟩ : syracuseStep 3114353 = 2335765) B2335765
theorem B2076235 : Blo 2075435 2076235 := bstep (se 1 (by rfl) ⟨1557176, by rfl⟩ : syracuseStep 2076235 = 3114353) B3114353
theorem B2627741 : Blo 2075435 2627741 := bbase (se 3 (by rfl) ⟨492701, by rfl⟩ : syracuseStep 2627741 = 985403) (by norm_num)
theorem B7007309 : Blo 2075435 7007309 := bstep (se 3 (by rfl) ⟨1313870, by rfl⟩ : syracuseStep 7007309 = 2627741) B2627741
theorem B4671539 : Blo 2075435 4671539 := bstep (se 1 (by rfl) ⟨3503654, by rfl⟩ : syracuseStep 4671539 = 7007309) B7007309
theorem B3114359 : Blo 2075435 3114359 := bstep (se 1 (by rfl) ⟨2335769, by rfl⟩ : syracuseStep 3114359 = 4671539) B4671539
theorem B2076239 : Blo 2075435 2076239 := bstep (se 1 (by rfl) ⟨1557179, by rfl⟩ : syracuseStep 2076239 = 3114359) B3114359
theorem B3114365 : Blo 2075435 3114365 := bbase (se 3 (by rfl) ⟨583943, by rfl⟩ : syracuseStep 3114365 = 1167887) (by norm_num)
theorem B2076243 : Blo 2075435 2076243 := bstep (se 1 (by rfl) ⟨1557182, by rfl⟩ : syracuseStep 2076243 = 3114365) B3114365
theorem B4671557 : Blo 2075435 4671557 := bbase (se 4 (by rfl) ⟨437958, by rfl⟩ : syracuseStep 4671557 = 875917) (by norm_num)
theorem B3114371 : Blo 2075435 3114371 := bstep (se 1 (by rfl) ⟨2335778, by rfl⟩ : syracuseStep 3114371 = 4671557) B4671557
theorem B2076247 : Blo 2075435 2076247 := bstep (se 1 (by rfl) ⟨1557185, by rfl⟩ : syracuseStep 2076247 = 3114371) B3114371
theorem B5912453 : Blo 2075435 5912453 := bbase (se 4 (by rfl) ⟨554292, by rfl⟩ : syracuseStep 5912453 = 1108585) (by norm_num)
theorem B3941635 : Blo 2075435 3941635 := bstep (se 1 (by rfl) ⟨2956226, by rfl⟩ : syracuseStep 3941635 = 5912453) B5912453
theorem B5255513 : Blo 2075435 5255513 := bstep (se 2 (by rfl) ⟨1970817, by rfl⟩ : syracuseStep 5255513 = 3941635) B3941635
theorem B3503675 : Blo 2075435 3503675 := bstep (se 1 (by rfl) ⟨2627756, by rfl⟩ : syracuseStep 3503675 = 5255513) B5255513
theorem B2335783 : Blo 2075435 2335783 := bstep (se 1 (by rfl) ⟨1751837, by rfl⟩ : syracuseStep 2335783 = 3503675) B3503675
theorem B3114377 : Blo 2075435 3114377 := bstep (se 2 (by rfl) ⟨1167891, by rfl⟩ : syracuseStep 3114377 = 2335783) B2335783
theorem B2076251 : Blo 2075435 2076251 := bstep (se 1 (by rfl) ⟨1557188, by rfl⟩ : syracuseStep 2076251 = 3114377) B3114377
theorem B10511045 : Blo 2075435 10511045 := bbase (se 4 (by rfl) ⟨985410, by rfl⟩ : syracuseStep 10511045 = 1970821) (by norm_num)
theorem B7007363 : Blo 2075435 7007363 := bstep (se 1 (by rfl) ⟨5255522, by rfl⟩ : syracuseStep 7007363 = 10511045) B10511045
theorem B4671575 : Blo 2075435 4671575 := bstep (se 1 (by rfl) ⟨3503681, by rfl⟩ : syracuseStep 4671575 = 7007363) B7007363
theorem B3114383 : Blo 2075435 3114383 := bstep (se 1 (by rfl) ⟨2335787, by rfl⟩ : syracuseStep 3114383 = 4671575) B4671575
theorem B2076255 : Blo 2075435 2076255 := bstep (se 1 (by rfl) ⟨1557191, by rfl⟩ : syracuseStep 2076255 = 3114383) B3114383
theorem B3114389 : Blo 2075435 3114389 := bbase (se 6 (by rfl) ⟨72993, by rfl⟩ : syracuseStep 3114389 = 145987) (by norm_num)
theorem B2076259 : Blo 2075435 2076259 := bstep (se 1 (by rfl) ⟨1557194, by rfl⟩ : syracuseStep 2076259 = 3114389) B3114389
theorem B4434365 : Blo 2075435 4434365 := bbase (se 3 (by rfl) ⟨831443, by rfl⟩ : syracuseStep 4434365 = 1662887) (by norm_num)
theorem B11824973 : Blo 2075435 11824973 := bstep (se 3 (by rfl) ⟨2217182, by rfl⟩ : syracuseStep 11824973 = 4434365) B4434365
theorem B7883315 : Blo 2075435 7883315 := bstep (se 1 (by rfl) ⟨5912486, by rfl⟩ : syracuseStep 7883315 = 11824973) B11824973
theorem B5255543 : Blo 2075435 5255543 := bstep (se 1 (by rfl) ⟨3941657, by rfl⟩ : syracuseStep 5255543 = 7883315) B7883315
theorem B3503695 : Blo 2075435 3503695 := bstep (se 1 (by rfl) ⟨2627771, by rfl⟩ : syracuseStep 3503695 = 5255543) B5255543
theorem B4671593 : Blo 2075435 4671593 := bstep (se 2 (by rfl) ⟨1751847, by rfl⟩ : syracuseStep 4671593 = 3503695) B3503695
theorem B3114395 : Blo 2075435 3114395 := bstep (se 1 (by rfl) ⟨2335796, by rfl⟩ : syracuseStep 3114395 = 4671593) B4671593
theorem B2076263 : Blo 2075435 2076263 := bstep (se 1 (by rfl) ⟨1557197, by rfl⟩ : syracuseStep 2076263 = 3114395) B3114395
theorem B2335801 : Blo 2075435 2335801 := bbase (se 2 (by rfl) ⟨875925, by rfl⟩ : syracuseStep 2335801 = 1751851) (by norm_num)
theorem B3114401 : Blo 2075435 3114401 := bstep (se 2 (by rfl) ⟨1167900, by rfl⟩ : syracuseStep 3114401 = 2335801) B2335801
theorem B2076267 : Blo 2075435 2076267 := bstep (se 1 (by rfl) ⟨1557200, by rfl⟩ : syracuseStep 2076267 = 3114401) B3114401
theorem B3995453 : Blo 2075435 3995453 := bbase (se 3 (by rfl) ⟨749147, by rfl⟩ : syracuseStep 3995453 = 1498295) (by norm_num)
theorem B10654541 : Blo 2075435 10654541 := bstep (se 3 (by rfl) ⟨1997726, by rfl⟩ : syracuseStep 10654541 = 3995453) B3995453
theorem B7103027 : Blo 2075435 7103027 := bstep (se 1 (by rfl) ⟨5327270, by rfl⟩ : syracuseStep 7103027 = 10654541) B10654541
theorem B4735351 : Blo 2075435 4735351 := bstep (se 1 (by rfl) ⟨3551513, by rfl⟩ : syracuseStep 4735351 = 7103027) B7103027
theorem B6313801 : Blo 2075435 6313801 := bstep (se 2 (by rfl) ⟨2367675, by rfl⟩ : syracuseStep 6313801 = 4735351) B4735351
theorem B8418401 : Blo 2075435 8418401 := bstep (se 2 (by rfl) ⟨3156900, by rfl⟩ : syracuseStep 8418401 = 6313801) B6313801
theorem B5612267 : Blo 2075435 5612267 := bstep (se 1 (by rfl) ⟨4209200, by rfl⟩ : syracuseStep 5612267 = 8418401) B8418401
theorem B3741511 : Blo 2075435 3741511 := bstep (se 1 (by rfl) ⟨2806133, by rfl⟩ : syracuseStep 3741511 = 5612267) B5612267
theorem B4988681 : Blo 2075435 4988681 := bstep (se 2 (by rfl) ⟨1870755, by rfl⟩ : syracuseStep 4988681 = 3741511) B3741511
theorem B3325787 : Blo 2075435 3325787 := bstep (se 1 (by rfl) ⟨2494340, by rfl⟩ : syracuseStep 3325787 = 4988681) B4988681
theorem B2217191 : Blo 2075435 2217191 := bstep (se 1 (by rfl) ⟨1662893, by rfl⟩ : syracuseStep 2217191 = 3325787) B3325787
theorem B5912509 : Blo 2075435 5912509 := bstep (se 3 (by rfl) ⟨1108595, by rfl⟩ : syracuseStep 5912509 = 2217191) B2217191
theorem B7883345 : Blo 2075435 7883345 := bstep (se 2 (by rfl) ⟨2956254, by rfl⟩ : syracuseStep 7883345 = 5912509) B5912509
theorem B5255563 : Blo 2075435 5255563 := bstep (se 1 (by rfl) ⟨3941672, by rfl⟩ : syracuseStep 5255563 = 7883345) B7883345
theorem B7007417 : Blo 2075435 7007417 := bstep (se 2 (by rfl) ⟨2627781, by rfl⟩ : syracuseStep 7007417 = 5255563) B5255563
theorem B4671611 : Blo 2075435 4671611 := bstep (se 1 (by rfl) ⟨3503708, by rfl⟩ : syracuseStep 4671611 = 7007417) B7007417
theorem B3114407 : Blo 2075435 3114407 := bstep (se 1 (by rfl) ⟨2335805, by rfl⟩ : syracuseStep 3114407 = 4671611) B4671611
theorem B2076271 : Blo 2075435 2076271 := bstep (se 1 (by rfl) ⟨1557203, by rfl⟩ : syracuseStep 2076271 = 3114407) B3114407
theorem B3114413 : Blo 2075435 3114413 := bbase (se 3 (by rfl) ⟨583952, by rfl⟩ : syracuseStep 3114413 = 1167905) (by norm_num)
theorem B2076275 : Blo 2075435 2076275 := bstep (se 1 (by rfl) ⟨1557206, by rfl⟩ : syracuseStep 2076275 = 3114413) B3114413
theorem B4671629 : Blo 2075435 4671629 := bbase (se 3 (by rfl) ⟨875930, by rfl⟩ : syracuseStep 4671629 = 1751861) (by norm_num)
theorem B3114419 : Blo 2075435 3114419 := bstep (se 1 (by rfl) ⟨2335814, by rfl⟩ : syracuseStep 3114419 = 4671629) B4671629
theorem B2076279 : Blo 2075435 2076279 := bstep (se 1 (by rfl) ⟨1557209, by rfl⟩ : syracuseStep 2076279 = 3114419) B3114419
theorem B2627797 : Blo 2075435 2627797 := bbase (se 7 (by rfl) ⟨30794, by rfl⟩ : syracuseStep 2627797 = 61589) (by norm_num)
theorem B3503729 : Blo 2075435 3503729 := bstep (se 2 (by rfl) ⟨1313898, by rfl⟩ : syracuseStep 3503729 = 2627797) B2627797
theorem B2335819 : Blo 2075435 2335819 := bstep (se 1 (by rfl) ⟨1751864, by rfl⟩ : syracuseStep 2335819 = 3503729) B3503729
theorem B3114425 : Blo 2075435 3114425 := bstep (se 2 (by rfl) ⟨1167909, by rfl⟩ : syracuseStep 3114425 = 2335819) B2335819
theorem B2076283 : Blo 2075435 2076283 := bstep (se 1 (by rfl) ⟨1557212, by rfl⟩ : syracuseStep 2076283 = 3114425) B3114425
theorem B7103077 : Blo 2075435 7103077 := bbase (se 4 (by rfl) ⟨665913, by rfl⟩ : syracuseStep 7103077 = 1331827) (by norm_num)
theorem B151532309 : Blo 2075435 151532309 := bstep (se 6 (by rfl) ⟨3551538, by rfl⟩ : syracuseStep 151532309 = 7103077) B7103077
theorem B101021539 : Blo 2075435 101021539 := bstep (se 1 (by rfl) ⟨75766154, by rfl⟩ : syracuseStep 101021539 = 151532309) B151532309
theorem B134695385 : Blo 2075435 134695385 := bstep (se 2 (by rfl) ⟨50510769, by rfl⟩ : syracuseStep 134695385 = 101021539) B101021539
theorem B89796923 : Blo 2075435 89796923 := bstep (se 1 (by rfl) ⟨67347692, by rfl⟩ : syracuseStep 89796923 = 134695385) B134695385
theorem B59864615 : Blo 2075435 59864615 := bstep (se 1 (by rfl) ⟨44898461, by rfl⟩ : syracuseStep 59864615 = 89796923) B89796923
theorem B39909743 : Blo 2075435 39909743 := bstep (se 1 (by rfl) ⟨29932307, by rfl⟩ : syracuseStep 39909743 = 59864615) B59864615
theorem B26606495 : Blo 2075435 26606495 := bstep (se 1 (by rfl) ⟨19954871, by rfl⟩ : syracuseStep 26606495 = 39909743) B39909743
theorem B17737663 : Blo 2075435 17737663 := bstep (se 1 (by rfl) ⟨13303247, by rfl⟩ : syracuseStep 17737663 = 26606495) B26606495
theorem B23650217 : Blo 2075435 23650217 := bstep (se 2 (by rfl) ⟨8868831, by rfl⟩ : syracuseStep 23650217 = 17737663) B17737663
theorem B15766811 : Blo 2075435 15766811 := bstep (se 1 (by rfl) ⟨11825108, by rfl⟩ : syracuseStep 15766811 = 23650217) B23650217
theorem B10511207 : Blo 2075435 10511207 := bstep (se 1 (by rfl) ⟨7883405, by rfl⟩ : syracuseStep 10511207 = 15766811) B15766811
theorem B7007471 : Blo 2075435 7007471 := bstep (se 1 (by rfl) ⟨5255603, by rfl⟩ : syracuseStep 7007471 = 10511207) B10511207
theorem B4671647 : Blo 2075435 4671647 := bstep (se 1 (by rfl) ⟨3503735, by rfl⟩ : syracuseStep 4671647 = 7007471) B7007471
theorem B3114431 : Blo 2075435 3114431 := bstep (se 1 (by rfl) ⟨2335823, by rfl⟩ : syracuseStep 3114431 = 4671647) B4671647
theorem B2076287 : Blo 2075435 2076287 := bstep (se 1 (by rfl) ⟨1557215, by rfl⟩ : syracuseStep 2076287 = 3114431) B3114431
theorem B3114437 : Blo 2075435 3114437 := bbase (se 4 (by rfl) ⟨291978, by rfl⟩ : syracuseStep 3114437 = 583957) (by norm_num)
theorem B2076291 : Blo 2075435 2076291 := bstep (se 1 (by rfl) ⟨1557218, by rfl⟩ : syracuseStep 2076291 = 3114437) B3114437
theorem B3503749 : Blo 2075435 3503749 := bbase (se 4 (by rfl) ⟨328476, by rfl⟩ : syracuseStep 3503749 = 656953) (by norm_num)
theorem B4671665 : Blo 2075435 4671665 := bstep (se 2 (by rfl) ⟨1751874, by rfl⟩ : syracuseStep 4671665 = 3503749) B3503749
theorem B3114443 : Blo 2075435 3114443 := bstep (se 1 (by rfl) ⟨2335832, by rfl⟩ : syracuseStep 3114443 = 4671665) B4671665
theorem B2076295 : Blo 2075435 2076295 := bstep (se 1 (by rfl) ⟨1557221, by rfl⟩ : syracuseStep 2076295 = 3114443) B3114443
theorem B2335837 : Blo 2075435 2335837 := bbase (se 3 (by rfl) ⟨437969, by rfl⟩ : syracuseStep 2335837 = 875939) (by norm_num)
theorem B3114449 : Blo 2075435 3114449 := bstep (se 2 (by rfl) ⟨1167918, by rfl⟩ : syracuseStep 3114449 = 2335837) B2335837
theorem B2076299 : Blo 2075435 2076299 := bstep (se 1 (by rfl) ⟨1557224, by rfl⟩ : syracuseStep 2076299 = 3114449) B3114449
theorem B7007525 : Blo 2075435 7007525 := bbase (se 4 (by rfl) ⟨656955, by rfl⟩ : syracuseStep 7007525 = 1313911) (by norm_num)
theorem B4671683 : Blo 2075435 4671683 := bstep (se 1 (by rfl) ⟨3503762, by rfl⟩ : syracuseStep 4671683 = 7007525) B7007525
theorem B3114455 : Blo 2075435 3114455 := bstep (se 1 (by rfl) ⟨2335841, by rfl⟩ : syracuseStep 3114455 = 4671683) B4671683
theorem B2076303 : Blo 2075435 2076303 := bstep (se 1 (by rfl) ⟨1557227, by rfl⟩ : syracuseStep 2076303 = 3114455) B3114455
theorem B3114461 : Blo 2075435 3114461 := bbase (se 3 (by rfl) ⟨583961, by rfl⟩ : syracuseStep 3114461 = 1167923) (by norm_num)
theorem B2076307 : Blo 2075435 2076307 := bstep (se 1 (by rfl) ⟨1557230, by rfl⟩ : syracuseStep 2076307 = 3114461) B3114461
theorem B4671701 : Blo 2075435 4671701 := bbase (se 7 (by rfl) ⟨54746, by rfl⟩ : syracuseStep 4671701 = 109493) (by norm_num)
theorem B3114467 : Blo 2075435 3114467 := bstep (se 1 (by rfl) ⟨2335850, by rfl⟩ : syracuseStep 3114467 = 4671701) B4671701
theorem B2076311 : Blo 2075435 2076311 := bstep (se 1 (by rfl) ⟨1557233, by rfl⟩ : syracuseStep 2076311 = 3114467) B3114467
theorem B9977573 : Blo 2075435 9977573 := bbase (se 4 (by rfl) ⟨935397, by rfl⟩ : syracuseStep 9977573 = 1870795) (by norm_num)
theorem B6651715 : Blo 2075435 6651715 := bstep (se 1 (by rfl) ⟨4988786, by rfl⟩ : syracuseStep 6651715 = 9977573) B9977573
theorem B8868953 : Blo 2075435 8868953 := bstep (se 2 (by rfl) ⟨3325857, by rfl⟩ : syracuseStep 8868953 = 6651715) B6651715
theorem B5912635 : Blo 2075435 5912635 := bstep (se 1 (by rfl) ⟨4434476, by rfl⟩ : syracuseStep 5912635 = 8868953) B8868953
theorem B7883513 : Blo 2075435 7883513 := bstep (se 2 (by rfl) ⟨2956317, by rfl⟩ : syracuseStep 7883513 = 5912635) B5912635
theorem B5255675 : Blo 2075435 5255675 := bstep (se 1 (by rfl) ⟨3941756, by rfl⟩ : syracuseStep 5255675 = 7883513) B7883513
theorem B3503783 : Blo 2075435 3503783 := bstep (se 1 (by rfl) ⟨2627837, by rfl⟩ : syracuseStep 3503783 = 5255675) B5255675
theorem B2335855 : Blo 2075435 2335855 := bstep (se 1 (by rfl) ⟨1751891, by rfl⟩ : syracuseStep 2335855 = 3503783) B3503783
theorem B3114473 : Blo 2075435 3114473 := bstep (se 2 (by rfl) ⟨1167927, by rfl⟩ : syracuseStep 3114473 = 2335855) B2335855
theorem B2076315 : Blo 2075435 2076315 := bstep (se 1 (by rfl) ⟨1557236, by rfl⟩ : syracuseStep 2076315 = 3114473) B3114473
theorem B7103189 : Blo 2075435 7103189 := bbase (se 7 (by rfl) ⟨83240, by rfl⟩ : syracuseStep 7103189 = 166481) (by norm_num)
theorem B4735459 : Blo 2075435 4735459 := bstep (se 1 (by rfl) ⟨3551594, by rfl⟩ : syracuseStep 4735459 = 7103189) B7103189
theorem B6313945 : Blo 2075435 6313945 := bstep (se 2 (by rfl) ⟨2367729, by rfl⟩ : syracuseStep 6313945 = 4735459) B4735459
theorem B8418593 : Blo 2075435 8418593 := bstep (se 2 (by rfl) ⟨3156972, by rfl⟩ : syracuseStep 8418593 = 6313945) B6313945
theorem B5612395 : Blo 2075435 5612395 := bstep (se 1 (by rfl) ⟨4209296, by rfl⟩ : syracuseStep 5612395 = 8418593) B8418593
theorem B7483193 : Blo 2075435 7483193 := bstep (se 2 (by rfl) ⟨2806197, by rfl⟩ : syracuseStep 7483193 = 5612395) B5612395
theorem B4988795 : Blo 2075435 4988795 := bstep (se 1 (by rfl) ⟨3741596, by rfl⟩ : syracuseStep 4988795 = 7483193) B7483193
theorem B13303453 : Blo 2075435 13303453 := bstep (se 3 (by rfl) ⟨2494397, by rfl⟩ : syracuseStep 13303453 = 4988795) B4988795
theorem B17737937 : Blo 2075435 17737937 := bstep (se 2 (by rfl) ⟨6651726, by rfl⟩ : syracuseStep 17737937 = 13303453) B13303453
theorem B11825291 : Blo 2075435 11825291 := bstep (se 1 (by rfl) ⟨8868968, by rfl⟩ : syracuseStep 11825291 = 17737937) B17737937
theorem B7883527 : Blo 2075435 7883527 := bstep (se 1 (by rfl) ⟨5912645, by rfl⟩ : syracuseStep 7883527 = 11825291) B11825291
theorem B10511369 : Blo 2075435 10511369 := bstep (se 2 (by rfl) ⟨3941763, by rfl⟩ : syracuseStep 10511369 = 7883527) B7883527
theorem B7007579 : Blo 2075435 7007579 := bstep (se 1 (by rfl) ⟨5255684, by rfl⟩ : syracuseStep 7007579 = 10511369) B10511369
theorem B4671719 : Blo 2075435 4671719 := bstep (se 1 (by rfl) ⟨3503789, by rfl⟩ : syracuseStep 4671719 = 7007579) B7007579
theorem B3114479 : Blo 2075435 3114479 := bstep (se 1 (by rfl) ⟨2335859, by rfl⟩ : syracuseStep 3114479 = 4671719) B4671719
theorem B2076319 : Blo 2075435 2076319 := bstep (se 1 (by rfl) ⟨1557239, by rfl⟩ : syracuseStep 2076319 = 3114479) B3114479
theorem B3114485 : Blo 2075435 3114485 := bbase (se 5 (by rfl) ⟨145991, by rfl⟩ : syracuseStep 3114485 = 291983) (by norm_num)
theorem B2076323 : Blo 2075435 2076323 := bstep (se 1 (by rfl) ⟨1557242, by rfl⟩ : syracuseStep 2076323 = 3114485) B3114485
theorem B3325877 : Blo 2075435 3325877 := bbase (se 5 (by rfl) ⟨155900, by rfl⟩ : syracuseStep 3325877 = 311801) (by norm_num)
theorem B2217251 : Blo 2075435 2217251 := bstep (se 1 (by rfl) ⟨1662938, by rfl⟩ : syracuseStep 2217251 = 3325877) B3325877
theorem B5912669 : Blo 2075435 5912669 := bstep (se 3 (by rfl) ⟨1108625, by rfl⟩ : syracuseStep 5912669 = 2217251) B2217251
theorem B3941779 : Blo 2075435 3941779 := bstep (se 1 (by rfl) ⟨2956334, by rfl⟩ : syracuseStep 3941779 = 5912669) B5912669
theorem B5255705 : Blo 2075435 5255705 := bstep (se 2 (by rfl) ⟨1970889, by rfl⟩ : syracuseStep 5255705 = 3941779) B3941779
theorem B3503803 : Blo 2075435 3503803 := bstep (se 1 (by rfl) ⟨2627852, by rfl⟩ : syracuseStep 3503803 = 5255705) B5255705
theorem B4671737 : Blo 2075435 4671737 := bstep (se 2 (by rfl) ⟨1751901, by rfl⟩ : syracuseStep 4671737 = 3503803) B3503803
theorem B3114491 : Blo 2075435 3114491 := bstep (se 1 (by rfl) ⟨2335868, by rfl⟩ : syracuseStep 3114491 = 4671737) B4671737
theorem B2076327 : Blo 2075435 2076327 := bstep (se 1 (by rfl) ⟨1557245, by rfl⟩ : syracuseStep 2076327 = 3114491) B3114491
theorem B2335873 : Blo 2075435 2335873 := bbase (se 2 (by rfl) ⟨875952, by rfl⟩ : syracuseStep 2335873 = 1751905) (by norm_num)
theorem B3114497 : Blo 2075435 3114497 := bstep (se 2 (by rfl) ⟨1167936, by rfl⟩ : syracuseStep 3114497 = 2335873) B2335873
theorem B2076331 : Blo 2075435 2076331 := bstep (se 1 (by rfl) ⟨1557248, by rfl⟩ : syracuseStep 2076331 = 3114497) B3114497
theorem B5255725 : Blo 2075435 5255725 := bbase (se 3 (by rfl) ⟨985448, by rfl⟩ : syracuseStep 5255725 = 1970897) (by norm_num)
theorem B7007633 : Blo 2075435 7007633 := bstep (se 2 (by rfl) ⟨2627862, by rfl⟩ : syracuseStep 7007633 = 5255725) B5255725
theorem B4671755 : Blo 2075435 4671755 := bstep (se 1 (by rfl) ⟨3503816, by rfl⟩ : syracuseStep 4671755 = 7007633) B7007633
theorem B3114503 : Blo 2075435 3114503 := bstep (se 1 (by rfl) ⟨2335877, by rfl⟩ : syracuseStep 3114503 = 4671755) B4671755
theorem B2076335 : Blo 2075435 2076335 := bstep (se 1 (by rfl) ⟨1557251, by rfl⟩ : syracuseStep 2076335 = 3114503) B3114503
theorem B3114509 : Blo 2075435 3114509 := bbase (se 3 (by rfl) ⟨583970, by rfl⟩ : syracuseStep 3114509 = 1167941) (by norm_num)
theorem B2076339 : Blo 2075435 2076339 := bstep (se 1 (by rfl) ⟨1557254, by rfl⟩ : syracuseStep 2076339 = 3114509) B3114509
theorem B4671773 : Blo 2075435 4671773 := bbase (se 3 (by rfl) ⟨875957, by rfl⟩ : syracuseStep 4671773 = 1751915) (by norm_num)
theorem B3114515 : Blo 2075435 3114515 := bstep (se 1 (by rfl) ⟨2335886, by rfl⟩ : syracuseStep 3114515 = 4671773) B4671773
theorem B2076343 : Blo 2075435 2076343 := bstep (se 1 (by rfl) ⟨1557257, by rfl⟩ : syracuseStep 2076343 = 3114515) B3114515
theorem B3503837 : Blo 2075435 3503837 := bbase (se 3 (by rfl) ⟨656969, by rfl⟩ : syracuseStep 3503837 = 1313939) (by norm_num)
theorem B2335891 : Blo 2075435 2335891 := bstep (se 1 (by rfl) ⟨1751918, by rfl⟩ : syracuseStep 2335891 = 3503837) B3503837
theorem B3114521 : Blo 2075435 3114521 := bstep (se 2 (by rfl) ⟨1167945, by rfl⟩ : syracuseStep 3114521 = 2335891) B2335891
theorem B2076347 : Blo 2075435 2076347 := bstep (se 1 (by rfl) ⟨1557260, by rfl⟩ : syracuseStep 2076347 = 3114521) B3114521
theorem B6651829 : Blo 2075435 6651829 := bbase (se 5 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 6651829 = 623609) (by norm_num)
theorem B8869105 : Blo 2075435 8869105 := bstep (se 2 (by rfl) ⟨3325914, by rfl⟩ : syracuseStep 8869105 = 6651829) B6651829
theorem B11825473 : Blo 2075435 11825473 := bstep (se 2 (by rfl) ⟨4434552, by rfl⟩ : syracuseStep 11825473 = 8869105) B8869105
theorem B15767297 : Blo 2075435 15767297 := bstep (se 2 (by rfl) ⟨5912736, by rfl⟩ : syracuseStep 15767297 = 11825473) B11825473
theorem B10511531 : Blo 2075435 10511531 := bstep (se 1 (by rfl) ⟨7883648, by rfl⟩ : syracuseStep 10511531 = 15767297) B15767297
theorem B7007687 : Blo 2075435 7007687 := bstep (se 1 (by rfl) ⟨5255765, by rfl⟩ : syracuseStep 7007687 = 10511531) B10511531
theorem B4671791 : Blo 2075435 4671791 := bstep (se 1 (by rfl) ⟨3503843, by rfl⟩ : syracuseStep 4671791 = 7007687) B7007687
theorem B3114527 : Blo 2075435 3114527 := bstep (se 1 (by rfl) ⟨2335895, by rfl⟩ : syracuseStep 3114527 = 4671791) B4671791
theorem B2076351 : Blo 2075435 2076351 := bstep (se 1 (by rfl) ⟨1557263, by rfl⟩ : syracuseStep 2076351 = 3114527) B3114527
theorem B3114533 : Blo 2075435 3114533 := bbase (se 4 (by rfl) ⟨291987, by rfl⟩ : syracuseStep 3114533 = 583975) (by norm_num)
theorem B2076355 : Blo 2075435 2076355 := bstep (se 1 (by rfl) ⟨1557266, by rfl⟩ : syracuseStep 2076355 = 3114533) B3114533
theorem B2627893 : Blo 2075435 2627893 := bbase (se 5 (by rfl) ⟨123182, by rfl⟩ : syracuseStep 2627893 = 246365) (by norm_num)
theorem B3503857 : Blo 2075435 3503857 := bstep (se 2 (by rfl) ⟨1313946, by rfl⟩ : syracuseStep 3503857 = 2627893) B2627893
theorem B4671809 : Blo 2075435 4671809 := bstep (se 2 (by rfl) ⟨1751928, by rfl⟩ : syracuseStep 4671809 = 3503857) B3503857
theorem B3114539 : Blo 2075435 3114539 := bstep (se 1 (by rfl) ⟨2335904, by rfl⟩ : syracuseStep 3114539 = 4671809) B4671809
theorem B2076359 : Blo 2075435 2076359 := bstep (se 1 (by rfl) ⟨1557269, by rfl⟩ : syracuseStep 2076359 = 3114539) B3114539
theorem B2335909 : Blo 2075435 2335909 := bbase (se 4 (by rfl) ⟨218991, by rfl⟩ : syracuseStep 2335909 = 437983) (by norm_num)
theorem B3114545 : Blo 2075435 3114545 := bstep (se 2 (by rfl) ⟨1167954, by rfl⟩ : syracuseStep 3114545 = 2335909) B2335909
theorem B2076363 : Blo 2075435 2076363 := bstep (se 1 (by rfl) ⟨1557272, by rfl⟩ : syracuseStep 2076363 = 3114545) B3114545
theorem B2700101 : Blo 2075435 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B7200269 : Blo 2075435 7200269 := bstep (se 3 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 7200269 = 2700101) B2700101
theorem B4800179 : Blo 2075435 4800179 := bstep (se 1 (by rfl) ⟨3600134, by rfl⟩ : syracuseStep 4800179 = 7200269) B7200269
theorem B12800477 : Blo 2075435 12800477 := bstep (se 3 (by rfl) ⟨2400089, by rfl⟩ : syracuseStep 12800477 = 4800179) B4800179
theorem B34134605 : Blo 2075435 34134605 := bstep (se 3 (by rfl) ⟨6400238, by rfl⟩ : syracuseStep 34134605 = 12800477) B12800477
theorem B22756403 : Blo 2075435 22756403 := bstep (se 1 (by rfl) ⟨17067302, by rfl⟩ : syracuseStep 22756403 = 34134605) B34134605
theorem B15170935 : Blo 2075435 15170935 := bstep (se 1 (by rfl) ⟨11378201, by rfl⟩ : syracuseStep 15170935 = 22756403) B22756403
theorem B20227913 : Blo 2075435 20227913 := bstep (se 2 (by rfl) ⟨7585467, by rfl⟩ : syracuseStep 20227913 = 15170935) B15170935
theorem B13485275 : Blo 2075435 13485275 := bstep (se 1 (by rfl) ⟨10113956, by rfl⟩ : syracuseStep 13485275 = 20227913) B20227913
theorem B8990183 : Blo 2075435 8990183 := bstep (se 1 (by rfl) ⟨6742637, by rfl⟩ : syracuseStep 8990183 = 13485275) B13485275
theorem B5993455 : Blo 2075435 5993455 := bstep (se 1 (by rfl) ⟨4495091, by rfl⟩ : syracuseStep 5993455 = 8990183) B8990183
theorem B7991273 : Blo 2075435 7991273 := bstep (se 2 (by rfl) ⟨2996727, by rfl⟩ : syracuseStep 7991273 = 5993455) B5993455
theorem B5327515 : Blo 2075435 5327515 := bstep (se 1 (by rfl) ⟨3995636, by rfl⟩ : syracuseStep 5327515 = 7991273) B7991273
theorem B28413413 : Blo 2075435 28413413 := bstep (se 4 (by rfl) ⟨2663757, by rfl⟩ : syracuseStep 28413413 = 5327515) B5327515
theorem B18942275 : Blo 2075435 18942275 := bstep (se 1 (by rfl) ⟨14206706, by rfl⟩ : syracuseStep 18942275 = 28413413) B28413413
theorem B12628183 : Blo 2075435 12628183 := bstep (se 1 (by rfl) ⟨9471137, by rfl⟩ : syracuseStep 12628183 = 18942275) B18942275
theorem B16837577 : Blo 2075435 16837577 := bstep (se 2 (by rfl) ⟨6314091, by rfl⟩ : syracuseStep 16837577 = 12628183) B12628183
theorem B11225051 : Blo 2075435 11225051 := bstep (se 1 (by rfl) ⟨8418788, by rfl⟩ : syracuseStep 11225051 = 16837577) B16837577
theorem B7483367 : Blo 2075435 7483367 := bstep (se 1 (by rfl) ⟨5612525, by rfl⟩ : syracuseStep 7483367 = 11225051) B11225051
theorem B19955645 : Blo 2075435 19955645 := bstep (se 3 (by rfl) ⟨3741683, by rfl⟩ : syracuseStep 19955645 = 7483367) B7483367
theorem B13303763 : Blo 2075435 13303763 := bstep (se 1 (by rfl) ⟨9977822, by rfl⟩ : syracuseStep 13303763 = 19955645) B19955645
theorem B8869175 : Blo 2075435 8869175 := bstep (se 1 (by rfl) ⟨6651881, by rfl⟩ : syracuseStep 8869175 = 13303763) B13303763
theorem B5912783 : Blo 2075435 5912783 := bstep (se 1 (by rfl) ⟨4434587, by rfl⟩ : syracuseStep 5912783 = 8869175) B8869175
theorem B3941855 : Blo 2075435 3941855 := bstep (se 1 (by rfl) ⟨2956391, by rfl⟩ : syracuseStep 3941855 = 5912783) B5912783
theorem B2627903 : Blo 2075435 2627903 := bstep (se 1 (by rfl) ⟨1970927, by rfl⟩ : syracuseStep 2627903 = 3941855) B3941855
theorem B7007741 : Blo 2075435 7007741 := bstep (se 3 (by rfl) ⟨1313951, by rfl⟩ : syracuseStep 7007741 = 2627903) B2627903
theorem B4671827 : Blo 2075435 4671827 := bstep (se 1 (by rfl) ⟨3503870, by rfl⟩ : syracuseStep 4671827 = 7007741) B7007741
theorem B3114551 : Blo 2075435 3114551 := bstep (se 1 (by rfl) ⟨2335913, by rfl⟩ : syracuseStep 3114551 = 4671827) B4671827
theorem B2076367 : Blo 2075435 2076367 := bstep (se 1 (by rfl) ⟨1557275, by rfl⟩ : syracuseStep 2076367 = 3114551) B3114551
theorem B3114557 : Blo 2075435 3114557 := bbase (se 3 (by rfl) ⟨583979, by rfl⟩ : syracuseStep 3114557 = 1167959) (by norm_num)
theorem B2076371 : Blo 2075435 2076371 := bstep (se 1 (by rfl) ⟨1557278, by rfl⟩ : syracuseStep 2076371 = 3114557) B3114557
theorem B4671845 : Blo 2075435 4671845 := bbase (se 4 (by rfl) ⟨437985, by rfl⟩ : syracuseStep 4671845 = 875971) (by norm_num)
theorem B3114563 : Blo 2075435 3114563 := bstep (se 1 (by rfl) ⟨2335922, by rfl⟩ : syracuseStep 3114563 = 4671845) B4671845
theorem B2076375 : Blo 2075435 2076375 := bstep (se 1 (by rfl) ⟨1557281, by rfl⟩ : syracuseStep 2076375 = 3114563) B3114563
theorem B5255837 : Blo 2075435 5255837 := bbase (se 3 (by rfl) ⟨985469, by rfl⟩ : syracuseStep 5255837 = 1970939) (by norm_num)
theorem B3503891 : Blo 2075435 3503891 := bstep (se 1 (by rfl) ⟨2627918, by rfl⟩ : syracuseStep 3503891 = 5255837) B5255837
theorem B2335927 : Blo 2075435 2335927 := bstep (se 1 (by rfl) ⟨1751945, by rfl⟩ : syracuseStep 2335927 = 3503891) B3503891
theorem B3114569 : Blo 2075435 3114569 := bstep (se 2 (by rfl) ⟨1167963, by rfl⟩ : syracuseStep 3114569 = 2335927) B2335927
theorem B2076379 : Blo 2075435 2076379 := bstep (se 1 (by rfl) ⟨1557284, by rfl⟩ : syracuseStep 2076379 = 3114569) B3114569
theorem B3941885 : Blo 2075435 3941885 := bbase (se 3 (by rfl) ⟨739103, by rfl⟩ : syracuseStep 3941885 = 1478207) (by norm_num)
theorem B10511693 : Blo 2075435 10511693 := bstep (se 3 (by rfl) ⟨1970942, by rfl⟩ : syracuseStep 10511693 = 3941885) B3941885
theorem B7007795 : Blo 2075435 7007795 := bstep (se 1 (by rfl) ⟨5255846, by rfl⟩ : syracuseStep 7007795 = 10511693) B10511693
theorem B4671863 : Blo 2075435 4671863 := bstep (se 1 (by rfl) ⟨3503897, by rfl⟩ : syracuseStep 4671863 = 7007795) B7007795
theorem B3114575 : Blo 2075435 3114575 := bstep (se 1 (by rfl) ⟨2335931, by rfl⟩ : syracuseStep 3114575 = 4671863) B4671863
theorem B2076383 : Blo 2075435 2076383 := bstep (se 1 (by rfl) ⟨1557287, by rfl⟩ : syracuseStep 2076383 = 3114575) B3114575
theorem B3114581 : Blo 2075435 3114581 := bbase (se 8 (by rfl) ⟨18249, by rfl⟩ : syracuseStep 3114581 = 36499) (by norm_num)
theorem B2076387 : Blo 2075435 2076387 := bstep (se 1 (by rfl) ⟨1557290, by rfl⟩ : syracuseStep 2076387 = 3114581) B3114581
theorem B5993525 : Blo 2075435 5993525 := bbase (se 5 (by rfl) ⟨280946, by rfl⟩ : syracuseStep 5993525 = 561893) (by norm_num)
theorem B15982733 : Blo 2075435 15982733 := bstep (se 3 (by rfl) ⟨2996762, by rfl⟩ : syracuseStep 15982733 = 5993525) B5993525
theorem B10655155 : Blo 2075435 10655155 := bstep (se 1 (by rfl) ⟨7991366, by rfl⟩ : syracuseStep 10655155 = 15982733) B15982733
theorem B14206873 : Blo 2075435 14206873 := bstep (se 2 (by rfl) ⟨5327577, by rfl⟩ : syracuseStep 14206873 = 10655155) B10655155
theorem B18942497 : Blo 2075435 18942497 := bstep (se 2 (by rfl) ⟨7103436, by rfl⟩ : syracuseStep 18942497 = 14206873) B14206873
theorem B12628331 : Blo 2075435 12628331 := bstep (se 1 (by rfl) ⟨9471248, by rfl⟩ : syracuseStep 12628331 = 18942497) B18942497
theorem B8418887 : Blo 2075435 8418887 := bstep (se 1 (by rfl) ⟨6314165, by rfl⟩ : syracuseStep 8418887 = 12628331) B12628331
theorem B5612591 : Blo 2075435 5612591 := bstep (se 1 (by rfl) ⟨4209443, by rfl⟩ : syracuseStep 5612591 = 8418887) B8418887
theorem B3741727 : Blo 2075435 3741727 := bstep (se 1 (by rfl) ⟨2806295, by rfl⟩ : syracuseStep 3741727 = 5612591) B5612591
theorem B4988969 : Blo 2075435 4988969 := bstep (se 2 (by rfl) ⟨1870863, by rfl⟩ : syracuseStep 4988969 = 3741727) B3741727
theorem B3325979 : Blo 2075435 3325979 := bstep (se 1 (by rfl) ⟨2494484, by rfl⟩ : syracuseStep 3325979 = 4988969) B4988969
theorem B8869277 : Blo 2075435 8869277 := bstep (se 3 (by rfl) ⟨1662989, by rfl⟩ : syracuseStep 8869277 = 3325979) B3325979
theorem B5912851 : Blo 2075435 5912851 := bstep (se 1 (by rfl) ⟨4434638, by rfl⟩ : syracuseStep 5912851 = 8869277) B8869277
theorem B7883801 : Blo 2075435 7883801 := bstep (se 2 (by rfl) ⟨2956425, by rfl⟩ : syracuseStep 7883801 = 5912851) B5912851
theorem B5255867 : Blo 2075435 5255867 := bstep (se 1 (by rfl) ⟨3941900, by rfl⟩ : syracuseStep 5255867 = 7883801) B7883801
theorem B3503911 : Blo 2075435 3503911 := bstep (se 1 (by rfl) ⟨2627933, by rfl⟩ : syracuseStep 3503911 = 5255867) B5255867
theorem B4671881 : Blo 2075435 4671881 := bstep (se 2 (by rfl) ⟨1751955, by rfl⟩ : syracuseStep 4671881 = 3503911) B3503911
theorem B3114587 : Blo 2075435 3114587 := bstep (se 1 (by rfl) ⟨2335940, by rfl⟩ : syracuseStep 3114587 = 4671881) B4671881
theorem B2076391 : Blo 2075435 2076391 := bstep (se 1 (by rfl) ⟨1557293, by rfl⟩ : syracuseStep 2076391 = 3114587) B3114587
theorem B2335945 : Blo 2075435 2335945 := bbase (se 2 (by rfl) ⟨875979, by rfl⟩ : syracuseStep 2335945 = 1751959) (by norm_num)
theorem B3114593 : Blo 2075435 3114593 := bstep (se 2 (by rfl) ⟨1167972, by rfl⟩ : syracuseStep 3114593 = 2335945) B2335945
theorem B2076395 : Blo 2075435 2076395 := bstep (se 1 (by rfl) ⟨1557296, by rfl⟩ : syracuseStep 2076395 = 3114593) B3114593
theorem B8418917 : Blo 2075435 8418917 := bbase (se 4 (by rfl) ⟨789273, by rfl⟩ : syracuseStep 8418917 = 1578547) (by norm_num)
theorem B22450445 : Blo 2075435 22450445 := bstep (se 3 (by rfl) ⟨4209458, by rfl⟩ : syracuseStep 22450445 = 8418917) B8418917
theorem B14966963 : Blo 2075435 14966963 := bstep (se 1 (by rfl) ⟨11225222, by rfl⟩ : syracuseStep 14966963 = 22450445) B22450445
theorem B9977975 : Blo 2075435 9977975 := bstep (se 1 (by rfl) ⟨7483481, by rfl⟩ : syracuseStep 9977975 = 14966963) B14966963
theorem B6651983 : Blo 2075435 6651983 := bstep (se 1 (by rfl) ⟨4988987, by rfl⟩ : syracuseStep 6651983 = 9977975) B9977975
theorem B17738621 : Blo 2075435 17738621 := bstep (se 3 (by rfl) ⟨3325991, by rfl⟩ : syracuseStep 17738621 = 6651983) B6651983
theorem B11825747 : Blo 2075435 11825747 := bstep (se 1 (by rfl) ⟨8869310, by rfl⟩ : syracuseStep 11825747 = 17738621) B17738621
theorem B7883831 : Blo 2075435 7883831 := bstep (se 1 (by rfl) ⟨5912873, by rfl⟩ : syracuseStep 7883831 = 11825747) B11825747
theorem B5255887 : Blo 2075435 5255887 := bstep (se 1 (by rfl) ⟨3941915, by rfl⟩ : syracuseStep 5255887 = 7883831) B7883831
theorem B7007849 : Blo 2075435 7007849 := bstep (se 2 (by rfl) ⟨2627943, by rfl⟩ : syracuseStep 7007849 = 5255887) B5255887
theorem B4671899 : Blo 2075435 4671899 := bstep (se 1 (by rfl) ⟨3503924, by rfl⟩ : syracuseStep 4671899 = 7007849) B7007849
theorem B3114599 : Blo 2075435 3114599 := bstep (se 1 (by rfl) ⟨2335949, by rfl⟩ : syracuseStep 3114599 = 4671899) B4671899
theorem B2076399 : Blo 2075435 2076399 := bstep (se 1 (by rfl) ⟨1557299, by rfl⟩ : syracuseStep 2076399 = 3114599) B3114599
theorem B3114605 : Blo 2075435 3114605 := bbase (se 3 (by rfl) ⟨583988, by rfl⟩ : syracuseStep 3114605 = 1167977) (by norm_num)
theorem B2076403 : Blo 2075435 2076403 := bstep (se 1 (by rfl) ⟨1557302, by rfl⟩ : syracuseStep 2076403 = 3114605) B3114605
theorem B4671917 : Blo 2075435 4671917 := bbase (se 3 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 4671917 = 1751969) (by norm_num)
theorem B3114611 : Blo 2075435 3114611 := bstep (se 1 (by rfl) ⟨2335958, by rfl⟩ : syracuseStep 3114611 = 4671917) B4671917
theorem B2076407 : Blo 2075435 2076407 := bstep (se 1 (by rfl) ⟨1557305, by rfl⟩ : syracuseStep 2076407 = 3114611) B3114611
theorem B2217341 : Blo 2075435 2217341 := bbase (se 3 (by rfl) ⟨415751, by rfl⟩ : syracuseStep 2217341 = 831503) (by norm_num)
theorem B5912909 : Blo 2075435 5912909 := bstep (se 3 (by rfl) ⟨1108670, by rfl⟩ : syracuseStep 5912909 = 2217341) B2217341
theorem B3941939 : Blo 2075435 3941939 := bstep (se 1 (by rfl) ⟨2956454, by rfl⟩ : syracuseStep 3941939 = 5912909) B5912909
theorem B2627959 : Blo 2075435 2627959 := bstep (se 1 (by rfl) ⟨1970969, by rfl⟩ : syracuseStep 2627959 = 3941939) B3941939
theorem B3503945 : Blo 2075435 3503945 := bstep (se 2 (by rfl) ⟨1313979, by rfl⟩ : syracuseStep 3503945 = 2627959) B2627959
theorem B2335963 : Blo 2075435 2335963 := bstep (se 1 (by rfl) ⟨1751972, by rfl⟩ : syracuseStep 2335963 = 3503945) B3503945
theorem B3114617 : Blo 2075435 3114617 := bstep (se 2 (by rfl) ⟨1167981, by rfl⟩ : syracuseStep 3114617 = 2335963) B2335963
theorem B2076411 : Blo 2075435 2076411 := bstep (se 1 (by rfl) ⟨1557308, by rfl⟩ : syracuseStep 2076411 = 3114617) B3114617
theorem B9751909 : Blo 2075435 9751909 := bbase (se 4 (by rfl) ⟨914241, by rfl⟩ : syracuseStep 9751909 = 1828483) (by norm_num)
theorem B13002545 : Blo 2075435 13002545 := bstep (se 2 (by rfl) ⟨4875954, by rfl⟩ : syracuseStep 13002545 = 9751909) B9751909
theorem B8668363 : Blo 2075435 8668363 := bstep (se 1 (by rfl) ⟨6501272, by rfl⟩ : syracuseStep 8668363 = 13002545) B13002545
theorem B11557817 : Blo 2075435 11557817 := bstep (se 2 (by rfl) ⟨4334181, by rfl⟩ : syracuseStep 11557817 = 8668363) B8668363
theorem B7705211 : Blo 2075435 7705211 := bstep (se 1 (by rfl) ⟨5778908, by rfl⟩ : syracuseStep 7705211 = 11557817) B11557817
theorem B20547229 : Blo 2075435 20547229 := bstep (se 3 (by rfl) ⟨3852605, by rfl⟩ : syracuseStep 20547229 = 7705211) B7705211
theorem B27396305 : Blo 2075435 27396305 := bstep (se 2 (by rfl) ⟨10273614, by rfl⟩ : syracuseStep 27396305 = 20547229) B20547229
theorem B18264203 : Blo 2075435 18264203 := bstep (se 1 (by rfl) ⟨13698152, by rfl⟩ : syracuseStep 18264203 = 27396305) B27396305
theorem B12176135 : Blo 2075435 12176135 := bstep (se 1 (by rfl) ⟨9132101, by rfl⟩ : syracuseStep 12176135 = 18264203) B18264203
theorem B8117423 : Blo 2075435 8117423 := bstep (se 1 (by rfl) ⟨6088067, by rfl⟩ : syracuseStep 8117423 = 12176135) B12176135
theorem B5411615 : Blo 2075435 5411615 := bstep (se 1 (by rfl) ⟨4058711, by rfl⟩ : syracuseStep 5411615 = 8117423) B8117423
theorem B14430973 : Blo 2075435 14430973 := bstep (se 3 (by rfl) ⟨2705807, by rfl⟩ : syracuseStep 14430973 = 5411615) B5411615
theorem B19241297 : Blo 2075435 19241297 := bstep (se 2 (by rfl) ⟨7215486, by rfl⟩ : syracuseStep 19241297 = 14430973) B14430973
theorem B12827531 : Blo 2075435 12827531 := bstep (se 1 (by rfl) ⟨9620648, by rfl⟩ : syracuseStep 12827531 = 19241297) B19241297
theorem B34206749 : Blo 2075435 34206749 := bstep (se 3 (by rfl) ⟨6413765, by rfl⟩ : syracuseStep 34206749 = 12827531) B12827531
theorem B22804499 : Blo 2075435 22804499 := bstep (se 1 (by rfl) ⟨17103374, by rfl⟩ : syracuseStep 22804499 = 34206749) B34206749
theorem B15202999 : Blo 2075435 15202999 := bstep (se 1 (by rfl) ⟨11402249, by rfl⟩ : syracuseStep 15202999 = 22804499) B22804499
theorem B20270665 : Blo 2075435 20270665 := bstep (se 2 (by rfl) ⟨7601499, by rfl⟩ : syracuseStep 20270665 = 15202999) B15202999
theorem B108110213 : Blo 2075435 108110213 := bstep (se 4 (by rfl) ⟨10135332, by rfl⟩ : syracuseStep 108110213 = 20270665) B20270665
theorem B72073475 : Blo 2075435 72073475 := bstep (se 1 (by rfl) ⟨54055106, by rfl⟩ : syracuseStep 72073475 = 108110213) B108110213
theorem B48048983 : Blo 2075435 48048983 := bstep (se 1 (by rfl) ⟨36036737, by rfl⟩ : syracuseStep 48048983 = 72073475) B72073475
theorem B32032655 : Blo 2075435 32032655 := bstep (se 1 (by rfl) ⟨24024491, by rfl⟩ : syracuseStep 32032655 = 48048983) B48048983
theorem B21355103 : Blo 2075435 21355103 := bstep (se 1 (by rfl) ⟨16016327, by rfl⟩ : syracuseStep 21355103 = 32032655) B32032655
theorem B14236735 : Blo 2075435 14236735 := bstep (se 1 (by rfl) ⟨10677551, by rfl⟩ : syracuseStep 14236735 = 21355103) B21355103
theorem B18982313 : Blo 2075435 18982313 := bstep (se 2 (by rfl) ⟨7118367, by rfl⟩ : syracuseStep 18982313 = 14236735) B14236735
theorem B12654875 : Blo 2075435 12654875 := bstep (se 1 (by rfl) ⟨9491156, by rfl⟩ : syracuseStep 12654875 = 18982313) B18982313
theorem B8436583 : Blo 2075435 8436583 := bstep (se 1 (by rfl) ⟨6327437, by rfl⟩ : syracuseStep 8436583 = 12654875) B12654875
theorem B11248777 : Blo 2075435 11248777 := bstep (se 2 (by rfl) ⟨4218291, by rfl⟩ : syracuseStep 11248777 = 8436583) B8436583
theorem B59993477 : Blo 2075435 59993477 := bstep (se 4 (by rfl) ⟨5624388, by rfl⟩ : syracuseStep 59993477 = 11248777) B11248777
theorem B39995651 : Blo 2075435 39995651 := bstep (se 1 (by rfl) ⟨29996738, by rfl⟩ : syracuseStep 39995651 = 59993477) B59993477
theorem B106655069 : Blo 2075435 106655069 := bstep (se 3 (by rfl) ⟨19997825, by rfl⟩ : syracuseStep 106655069 = 39995651) B39995651
theorem B71103379 : Blo 2075435 71103379 := bstep (se 1 (by rfl) ⟨53327534, by rfl⟩ : syracuseStep 71103379 = 106655069) B106655069
theorem B94804505 : Blo 2075435 94804505 := bstep (se 2 (by rfl) ⟨35551689, by rfl⟩ : syracuseStep 94804505 = 71103379) B71103379
theorem B63203003 : Blo 2075435 63203003 := bstep (se 1 (by rfl) ⟨47402252, by rfl⟩ : syracuseStep 63203003 = 94804505) B94804505
theorem B42135335 : Blo 2075435 42135335 := bstep (se 1 (by rfl) ⟨31601501, by rfl⟩ : syracuseStep 42135335 = 63203003) B63203003
theorem B28090223 : Blo 2075435 28090223 := bstep (se 1 (by rfl) ⟨21067667, by rfl⟩ : syracuseStep 28090223 = 42135335) B42135335
theorem B18726815 : Blo 2075435 18726815 := bstep (se 1 (by rfl) ⟨14045111, by rfl⟩ : syracuseStep 18726815 = 28090223) B28090223
theorem B12484543 : Blo 2075435 12484543 := bstep (se 1 (by rfl) ⟨9363407, by rfl⟩ : syracuseStep 12484543 = 18726815) B18726815
theorem B16646057 : Blo 2075435 16646057 := bstep (se 2 (by rfl) ⟨6242271, by rfl⟩ : syracuseStep 16646057 = 12484543) B12484543
theorem B11097371 : Blo 2075435 11097371 := bstep (se 1 (by rfl) ⟨8323028, by rfl⟩ : syracuseStep 11097371 = 16646057) B16646057
theorem B29592989 : Blo 2075435 29592989 := bstep (se 3 (by rfl) ⟨5548685, by rfl⟩ : syracuseStep 29592989 = 11097371) B11097371
theorem B19728659 : Blo 2075435 19728659 := bstep (se 1 (by rfl) ⟨14796494, by rfl⟩ : syracuseStep 19728659 = 29592989) B29592989
theorem B13152439 : Blo 2075435 13152439 := bstep (se 1 (by rfl) ⟨9864329, by rfl⟩ : syracuseStep 13152439 = 19728659) B19728659
theorem B70146341 : Blo 2075435 70146341 := bstep (se 4 (by rfl) ⟨6576219, by rfl⟩ : syracuseStep 70146341 = 13152439) B13152439
theorem B748227637 : Blo 2075435 748227637 := bstep (se 5 (by rfl) ⟨35073170, by rfl⟩ : syracuseStep 748227637 = 70146341) B70146341
theorem B3990547397 : Blo 2075435 3990547397 := bstep (se 4 (by rfl) ⟨374113818, by rfl⟩ : syracuseStep 3990547397 = 748227637) B748227637
theorem B2660364931 : Blo 2075435 2660364931 := bstep (se 1 (by rfl) ⟨1995273698, by rfl⟩ : syracuseStep 2660364931 = 3990547397) B3990547397
theorem B3547153241 : Blo 2075435 3547153241 := bstep (se 2 (by rfl) ⟨1330182465, by rfl⟩ : syracuseStep 3547153241 = 2660364931) B2660364931
theorem B2364768827 : Blo 2075435 2364768827 := bstep (se 1 (by rfl) ⟨1773576620, by rfl⟩ : syracuseStep 2364768827 = 3547153241) B3547153241
theorem B1576512551 : Blo 2075435 1576512551 := bstep (se 1 (by rfl) ⟨1182384413, by rfl⟩ : syracuseStep 1576512551 = 2364768827) B2364768827
theorem B1051008367 : Blo 2075435 1051008367 := bstep (se 1 (by rfl) ⟨788256275, by rfl⟩ : syracuseStep 1051008367 = 1576512551) B1576512551
theorem B1401344489 : Blo 2075435 1401344489 := bstep (se 2 (by rfl) ⟨525504183, by rfl⟩ : syracuseStep 1401344489 = 1051008367) B1051008367
theorem B934229659 : Blo 2075435 934229659 := bstep (se 1 (by rfl) ⟨700672244, by rfl⟩ : syracuseStep 934229659 = 1401344489) B1401344489
theorem B1245639545 : Blo 2075435 1245639545 := bstep (se 2 (by rfl) ⟨467114829, by rfl⟩ : syracuseStep 1245639545 = 934229659) B934229659
theorem B830426363 : Blo 2075435 830426363 := bstep (se 1 (by rfl) ⟨622819772, by rfl⟩ : syracuseStep 830426363 = 1245639545) B1245639545
theorem B553617575 : Blo 2075435 553617575 := bstep (se 1 (by rfl) ⟨415213181, by rfl⟩ : syracuseStep 553617575 = 830426363) B830426363
theorem B369078383 : Blo 2075435 369078383 := bstep (se 1 (by rfl) ⟨276808787, by rfl⟩ : syracuseStep 369078383 = 553617575) B553617575
theorem B246052255 : Blo 2075435 246052255 := bstep (se 1 (by rfl) ⟨184539191, by rfl⟩ : syracuseStep 246052255 = 369078383) B369078383
theorem B328069673 : Blo 2075435 328069673 := bstep (se 2 (by rfl) ⟨123026127, by rfl⟩ : syracuseStep 328069673 = 246052255) B246052255
theorem B218713115 : Blo 2075435 218713115 := bstep (se 1 (by rfl) ⟨164034836, by rfl⟩ : syracuseStep 218713115 = 328069673) B328069673
theorem B145808743 : Blo 2075435 145808743 := bstep (se 1 (by rfl) ⟨109356557, by rfl⟩ : syracuseStep 145808743 = 218713115) B218713115
theorem B194411657 : Blo 2075435 194411657 := bstep (se 2 (by rfl) ⟨72904371, by rfl⟩ : syracuseStep 194411657 = 145808743) B145808743
theorem B129607771 : Blo 2075435 129607771 := bstep (se 1 (by rfl) ⟨97205828, by rfl⟩ : syracuseStep 129607771 = 194411657) B194411657
theorem B172810361 : Blo 2075435 172810361 := bstep (se 2 (by rfl) ⟨64803885, by rfl⟩ : syracuseStep 172810361 = 129607771) B129607771
theorem B115206907 : Blo 2075435 115206907 := bstep (se 1 (by rfl) ⟨86405180, by rfl⟩ : syracuseStep 115206907 = 172810361) B172810361
theorem B153609209 : Blo 2075435 153609209 := bstep (se 2 (by rfl) ⟨57603453, by rfl⟩ : syracuseStep 153609209 = 115206907) B115206907
theorem B102406139 : Blo 2075435 102406139 := bstep (se 1 (by rfl) ⟨76804604, by rfl⟩ : syracuseStep 102406139 = 153609209) B153609209
theorem B68270759 : Blo 2075435 68270759 := bstep (se 1 (by rfl) ⟨51203069, by rfl⟩ : syracuseStep 68270759 = 102406139) B102406139
theorem B45513839 : Blo 2075435 45513839 := bstep (se 1 (by rfl) ⟨34135379, by rfl⟩ : syracuseStep 45513839 = 68270759) B68270759
theorem B30342559 : Blo 2075435 30342559 := bstep (se 1 (by rfl) ⟨22756919, by rfl⟩ : syracuseStep 30342559 = 45513839) B45513839
theorem B40456745 : Blo 2075435 40456745 := bstep (se 2 (by rfl) ⟨15171279, by rfl⟩ : syracuseStep 40456745 = 30342559) B30342559
theorem B26971163 : Blo 2075435 26971163 := bstep (se 1 (by rfl) ⟨20228372, by rfl⟩ : syracuseStep 26971163 = 40456745) B40456745
theorem B17980775 : Blo 2075435 17980775 := bstep (se 1 (by rfl) ⟨13485581, by rfl⟩ : syracuseStep 17980775 = 26971163) B26971163
theorem B11987183 : Blo 2075435 11987183 := bstep (se 1 (by rfl) ⟨8990387, by rfl⟩ : syracuseStep 11987183 = 17980775) B17980775
theorem B7991455 : Blo 2075435 7991455 := bstep (se 1 (by rfl) ⟨5993591, by rfl⟩ : syracuseStep 7991455 = 11987183) B11987183
theorem B10655273 : Blo 2075435 10655273 := bstep (se 2 (by rfl) ⟨3995727, by rfl⟩ : syracuseStep 10655273 = 7991455) B7991455
theorem B28414061 : Blo 2075435 28414061 := bstep (se 3 (by rfl) ⟨5327636, by rfl⟩ : syracuseStep 28414061 = 10655273) B10655273
theorem B18942707 : Blo 2075435 18942707 := bstep (se 1 (by rfl) ⟨14207030, by rfl⟩ : syracuseStep 18942707 = 28414061) B28414061
theorem B12628471 : Blo 2075435 12628471 := bstep (se 1 (by rfl) ⟨9471353, by rfl⟩ : syracuseStep 12628471 = 18942707) B18942707
theorem B16837961 : Blo 2075435 16837961 := bstep (se 2 (by rfl) ⟨6314235, by rfl⟩ : syracuseStep 16837961 = 12628471) B12628471
theorem B44901229 : Blo 2075435 44901229 := bstep (se 3 (by rfl) ⟨8418980, by rfl⟩ : syracuseStep 44901229 = 16837961) B16837961
theorem B59868305 : Blo 2075435 59868305 := bstep (se 2 (by rfl) ⟨22450614, by rfl⟩ : syracuseStep 59868305 = 44901229) B44901229
theorem B39912203 : Blo 2075435 39912203 := bstep (se 1 (by rfl) ⟨29934152, by rfl⟩ : syracuseStep 39912203 = 59868305) B59868305
theorem B26608135 : Blo 2075435 26608135 := bstep (se 1 (by rfl) ⟨19956101, by rfl⟩ : syracuseStep 26608135 = 39912203) B39912203
theorem B35477513 : Blo 2075435 35477513 := bstep (se 2 (by rfl) ⟨13304067, by rfl⟩ : syracuseStep 35477513 = 26608135) B26608135
theorem B23651675 : Blo 2075435 23651675 := bstep (se 1 (by rfl) ⟨17738756, by rfl⟩ : syracuseStep 23651675 = 35477513) B35477513
theorem B15767783 : Blo 2075435 15767783 := bstep (se 1 (by rfl) ⟨11825837, by rfl⟩ : syracuseStep 15767783 = 23651675) B23651675
theorem B10511855 : Blo 2075435 10511855 := bstep (se 1 (by rfl) ⟨7883891, by rfl⟩ : syracuseStep 10511855 = 15767783) B15767783
theorem B7007903 : Blo 2075435 7007903 := bstep (se 1 (by rfl) ⟨5255927, by rfl⟩ : syracuseStep 7007903 = 10511855) B10511855
theorem B4671935 : Blo 2075435 4671935 := bstep (se 1 (by rfl) ⟨3503951, by rfl⟩ : syracuseStep 4671935 = 7007903) B7007903
theorem B3114623 : Blo 2075435 3114623 := bstep (se 1 (by rfl) ⟨2335967, by rfl⟩ : syracuseStep 3114623 = 4671935) B4671935
theorem B2076415 : Blo 2075435 2076415 := bstep (se 1 (by rfl) ⟨1557311, by rfl⟩ : syracuseStep 2076415 = 3114623) B3114623
theorem B3114629 : Blo 2075435 3114629 := bbase (se 4 (by rfl) ⟨291996, by rfl⟩ : syracuseStep 3114629 = 583993) (by norm_num)
theorem B2076419 : Blo 2075435 2076419 := bstep (se 1 (by rfl) ⟨1557314, by rfl⟩ : syracuseStep 2076419 = 3114629) B3114629
theorem B3503965 : Blo 2075435 3503965 := bbase (se 3 (by rfl) ⟨656993, by rfl⟩ : syracuseStep 3503965 = 1313987) (by norm_num)
theorem B4671953 : Blo 2075435 4671953 := bstep (se 2 (by rfl) ⟨1751982, by rfl⟩ : syracuseStep 4671953 = 3503965) B3503965
theorem B3114635 : Blo 2075435 3114635 := bstep (se 1 (by rfl) ⟨2335976, by rfl⟩ : syracuseStep 3114635 = 4671953) B4671953
theorem B2076423 : Blo 2075435 2076423 := bstep (se 1 (by rfl) ⟨1557317, by rfl⟩ : syracuseStep 2076423 = 3114635) B3114635
theorem B2335981 : Blo 2075435 2335981 := bbase (se 3 (by rfl) ⟨437996, by rfl⟩ : syracuseStep 2335981 = 875993) (by norm_num)
theorem B3114641 : Blo 2075435 3114641 := bstep (se 2 (by rfl) ⟨1167990, by rfl⟩ : syracuseStep 3114641 = 2335981) B2335981
theorem B2076427 : Blo 2075435 2076427 := bstep (se 1 (by rfl) ⟨1557320, by rfl⟩ : syracuseStep 2076427 = 3114641) B3114641
theorem B7007957 : Blo 2075435 7007957 := bbase (se 7 (by rfl) ⟨82124, by rfl⟩ : syracuseStep 7007957 = 164249) (by norm_num)
theorem B4671971 : Blo 2075435 4671971 := bstep (se 1 (by rfl) ⟨3503978, by rfl⟩ : syracuseStep 4671971 = 7007957) B7007957
theorem B3114647 : Blo 2075435 3114647 := bstep (se 1 (by rfl) ⟨2335985, by rfl⟩ : syracuseStep 3114647 = 4671971) B4671971
theorem B2076431 : Blo 2075435 2076431 := bstep (se 1 (by rfl) ⟨1557323, by rfl⟩ : syracuseStep 2076431 = 3114647) B3114647
theorem B3114653 : Blo 2075435 3114653 := bbase (se 3 (by rfl) ⟨583997, by rfl⟩ : syracuseStep 3114653 = 1167995) (by norm_num)
theorem B2076435 : Blo 2075435 2076435 := bstep (se 1 (by rfl) ⟨1557326, by rfl⟩ : syracuseStep 2076435 = 3114653) B3114653
theorem B4671989 : Blo 2075435 4671989 := bbase (se 5 (by rfl) ⟨218999, by rfl⟩ : syracuseStep 4671989 = 437999) (by norm_num)
theorem B3114659 : Blo 2075435 3114659 := bstep (se 1 (by rfl) ⟨2335994, by rfl⟩ : syracuseStep 3114659 = 4671989) B4671989
theorem B2076439 : Blo 2075435 2076439 := bstep (se 1 (by rfl) ⟨1557329, by rfl⟩ : syracuseStep 2076439 = 3114659) B3114659
theorem B11225461 : Blo 2075435 11225461 := bbase (se 5 (by rfl) ⟨526193, by rfl⟩ : syracuseStep 11225461 = 1052387) (by norm_num)
theorem B14967281 : Blo 2075435 14967281 := bstep (se 2 (by rfl) ⟨5612730, by rfl⟩ : syracuseStep 14967281 = 11225461) B11225461
theorem B39912749 : Blo 2075435 39912749 := bstep (se 3 (by rfl) ⟨7483640, by rfl⟩ : syracuseStep 39912749 = 14967281) B14967281
theorem B26608499 : Blo 2075435 26608499 := bstep (se 1 (by rfl) ⟨19956374, by rfl⟩ : syracuseStep 26608499 = 39912749) B39912749
theorem B17738999 : Blo 2075435 17738999 := bstep (se 1 (by rfl) ⟨13304249, by rfl⟩ : syracuseStep 17738999 = 26608499) B26608499
theorem B11825999 : Blo 2075435 11825999 := bstep (se 1 (by rfl) ⟨8869499, by rfl⟩ : syracuseStep 11825999 = 17738999) B17738999
theorem B7883999 : Blo 2075435 7883999 := bstep (se 1 (by rfl) ⟨5912999, by rfl⟩ : syracuseStep 7883999 = 11825999) B11825999
theorem B5255999 : Blo 2075435 5255999 := bstep (se 1 (by rfl) ⟨3941999, by rfl⟩ : syracuseStep 5255999 = 7883999) B7883999
theorem B3503999 : Blo 2075435 3503999 := bstep (se 1 (by rfl) ⟨2627999, by rfl⟩ : syracuseStep 3503999 = 5255999) B5255999
theorem B2335999 : Blo 2075435 2335999 := bstep (se 1 (by rfl) ⟨1751999, by rfl⟩ : syracuseStep 2335999 = 3503999) B3503999
theorem B3114665 : Blo 2075435 3114665 := bstep (se 2 (by rfl) ⟨1167999, by rfl⟩ : syracuseStep 3114665 = 2335999) B2335999
theorem B2076443 : Blo 2075435 2076443 := bstep (se 1 (by rfl) ⟨1557332, by rfl⟩ : syracuseStep 2076443 = 3114665) B3114665
theorem B3326069 : Blo 2075435 3326069 := bbase (se 5 (by rfl) ⟨155909, by rfl⟩ : syracuseStep 3326069 = 311819) (by norm_num)
theorem B2217379 : Blo 2075435 2217379 := bstep (se 1 (by rfl) ⟨1663034, by rfl⟩ : syracuseStep 2217379 = 3326069) B3326069
theorem B2956505 : Blo 2075435 2956505 := bstep (se 2 (by rfl) ⟨1108689, by rfl⟩ : syracuseStep 2956505 = 2217379) B2217379
theorem B7884013 : Blo 2075435 7884013 := bstep (se 3 (by rfl) ⟨1478252, by rfl⟩ : syracuseStep 7884013 = 2956505) B2956505
theorem B10512017 : Blo 2075435 10512017 := bstep (se 2 (by rfl) ⟨3942006, by rfl⟩ : syracuseStep 10512017 = 7884013) B7884013
theorem B7008011 : Blo 2075435 7008011 := bstep (se 1 (by rfl) ⟨5256008, by rfl⟩ : syracuseStep 7008011 = 10512017) B10512017
theorem B4672007 : Blo 2075435 4672007 := bstep (se 1 (by rfl) ⟨3504005, by rfl⟩ : syracuseStep 4672007 = 7008011) B7008011
theorem B3114671 : Blo 2075435 3114671 := bstep (se 1 (by rfl) ⟨2336003, by rfl⟩ : syracuseStep 3114671 = 4672007) B4672007
theorem B2076447 : Blo 2075435 2076447 := bstep (se 1 (by rfl) ⟨1557335, by rfl⟩ : syracuseStep 2076447 = 3114671) B3114671
theorem B3114677 : Blo 2075435 3114677 := bbase (se 5 (by rfl) ⟨146000, by rfl⟩ : syracuseStep 3114677 = 292001) (by norm_num)
theorem B2076451 : Blo 2075435 2076451 := bstep (se 1 (by rfl) ⟨1557338, by rfl⟩ : syracuseStep 2076451 = 3114677) B3114677
theorem B5256029 : Blo 2075435 5256029 := bbase (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) (by norm_num)
theorem B3504019 : Blo 2075435 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B4672025 : Blo 2075435 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B3114683 : Blo 2075435 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B2076455 : Blo 2075435 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B2336017 : Blo 2075435 2336017 := bbase (se 2 (by rfl) ⟨876006, by rfl⟩ : syracuseStep 2336017 = 1752013) (by norm_num)
theorem B3114689 : Blo 2075435 3114689 := bstep (se 2 (by rfl) ⟨1168008, by rfl⟩ : syracuseStep 3114689 = 2336017) B2336017
theorem B2076459 : Blo 2075435 2076459 := bstep (se 1 (by rfl) ⟨1557344, by rfl⟩ : syracuseStep 2076459 = 3114689) B3114689
theorem B3942037 : Blo 2075435 3942037 := bbase (se 6 (by rfl) ⟨92391, by rfl⟩ : syracuseStep 3942037 = 184783) (by norm_num)
theorem B5256049 : Blo 2075435 5256049 := bstep (se 2 (by rfl) ⟨1971018, by rfl⟩ : syracuseStep 5256049 = 3942037) B3942037
theorem B7008065 : Blo 2075435 7008065 := bstep (se 2 (by rfl) ⟨2628024, by rfl⟩ : syracuseStep 7008065 = 5256049) B5256049
theorem B4672043 : Blo 2075435 4672043 := bstep (se 1 (by rfl) ⟨3504032, by rfl⟩ : syracuseStep 4672043 = 7008065) B7008065
theorem B3114695 : Blo 2075435 3114695 := bstep (se 1 (by rfl) ⟨2336021, by rfl⟩ : syracuseStep 3114695 = 4672043) B4672043
theorem B2076463 : Blo 2075435 2076463 := bstep (se 1 (by rfl) ⟨1557347, by rfl⟩ : syracuseStep 2076463 = 3114695) B3114695
theorem B3114701 : Blo 2075435 3114701 := bbase (se 3 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 3114701 = 1168013) (by norm_num)
theorem B2076467 : Blo 2075435 2076467 := bstep (se 1 (by rfl) ⟨1557350, by rfl⟩ : syracuseStep 2076467 = 3114701) B3114701
theorem B4672061 : Blo 2075435 4672061 := bbase (se 3 (by rfl) ⟨876011, by rfl⟩ : syracuseStep 4672061 = 1752023) (by norm_num)
theorem B3114707 : Blo 2075435 3114707 := bstep (se 1 (by rfl) ⟨2336030, by rfl⟩ : syracuseStep 3114707 = 4672061) B4672061
theorem B2076471 : Blo 2075435 2076471 := bstep (se 1 (by rfl) ⟨1557353, by rfl⟩ : syracuseStep 2076471 = 3114707) B3114707
theorem B3504053 : Blo 2075435 3504053 := bbase (se 5 (by rfl) ⟨164252, by rfl⟩ : syracuseStep 3504053 = 328505) (by norm_num)
theorem B2336035 : Blo 2075435 2336035 := bstep (se 1 (by rfl) ⟨1752026, by rfl⟩ : syracuseStep 2336035 = 3504053) B3504053
theorem B3114713 : Blo 2075435 3114713 := bstep (se 2 (by rfl) ⟨1168017, by rfl⟩ : syracuseStep 3114713 = 2336035) B2336035
theorem B2076475 : Blo 2075435 2076475 := bstep (se 1 (by rfl) ⟨1557356, by rfl⟩ : syracuseStep 2076475 = 3114713) B3114713
theorem B2217413 : Blo 2075435 2217413 := bbase (se 4 (by rfl) ⟨207882, by rfl⟩ : syracuseStep 2217413 = 415765) (by norm_num)
theorem B5913101 : Blo 2075435 5913101 := bstep (se 3 (by rfl) ⟨1108706, by rfl⟩ : syracuseStep 5913101 = 2217413) B2217413
theorem B15768269 : Blo 2075435 15768269 := bstep (se 3 (by rfl) ⟨2956550, by rfl⟩ : syracuseStep 15768269 = 5913101) B5913101
theorem B10512179 : Blo 2075435 10512179 := bstep (se 1 (by rfl) ⟨7884134, by rfl⟩ : syracuseStep 10512179 = 15768269) B15768269
theorem B7008119 : Blo 2075435 7008119 := bstep (se 1 (by rfl) ⟨5256089, by rfl⟩ : syracuseStep 7008119 = 10512179) B10512179
theorem B4672079 : Blo 2075435 4672079 := bstep (se 1 (by rfl) ⟨3504059, by rfl⟩ : syracuseStep 4672079 = 7008119) B7008119
theorem B3114719 : Blo 2075435 3114719 := bstep (se 1 (by rfl) ⟨2336039, by rfl⟩ : syracuseStep 3114719 = 4672079) B4672079
theorem B2076479 : Blo 2075435 2076479 := bstep (se 1 (by rfl) ⟨1557359, by rfl⟩ : syracuseStep 2076479 = 3114719) B3114719
theorem B3114725 : Blo 2075435 3114725 := bbase (se 4 (by rfl) ⟨292005, by rfl⟩ : syracuseStep 3114725 = 584011) (by norm_num)
theorem B2076483 : Blo 2075435 2076483 := bstep (se 1 (by rfl) ⟨1557362, by rfl⟩ : syracuseStep 2076483 = 3114725) B3114725
theorem B5913125 : Blo 2075435 5913125 := bbase (se 4 (by rfl) ⟨554355, by rfl⟩ : syracuseStep 5913125 = 1108711) (by norm_num)
theorem B3942083 : Blo 2075435 3942083 := bstep (se 1 (by rfl) ⟨2956562, by rfl⟩ : syracuseStep 3942083 = 5913125) B5913125
theorem B2628055 : Blo 2075435 2628055 := bstep (se 1 (by rfl) ⟨1971041, by rfl⟩ : syracuseStep 2628055 = 3942083) B3942083
theorem B3504073 : Blo 2075435 3504073 := bstep (se 2 (by rfl) ⟨1314027, by rfl⟩ : syracuseStep 3504073 = 2628055) B2628055
theorem B4672097 : Blo 2075435 4672097 := bstep (se 2 (by rfl) ⟨1752036, by rfl⟩ : syracuseStep 4672097 = 3504073) B3504073
theorem B3114731 : Blo 2075435 3114731 := bstep (se 1 (by rfl) ⟨2336048, by rfl⟩ : syracuseStep 3114731 = 4672097) B4672097
theorem B2076487 : Blo 2075435 2076487 := bstep (se 1 (by rfl) ⟨1557365, by rfl⟩ : syracuseStep 2076487 = 3114731) B3114731
theorem B2336053 : Blo 2075435 2336053 := bbase (se 5 (by rfl) ⟨109502, by rfl⟩ : syracuseStep 2336053 = 219005) (by norm_num)
theorem B3114737 : Blo 2075435 3114737 := bstep (se 2 (by rfl) ⟨1168026, by rfl⟩ : syracuseStep 3114737 = 2336053) B2336053
theorem B2076491 : Blo 2075435 2076491 := bstep (se 1 (by rfl) ⟨1557368, by rfl⟩ : syracuseStep 2076491 = 3114737) B3114737
theorem B2628065 : Blo 2075435 2628065 := bbase (se 2 (by rfl) ⟨985524, by rfl⟩ : syracuseStep 2628065 = 1971049) (by norm_num)
theorem B7008173 : Blo 2075435 7008173 := bstep (se 3 (by rfl) ⟨1314032, by rfl⟩ : syracuseStep 7008173 = 2628065) B2628065
theorem B4672115 : Blo 2075435 4672115 := bstep (se 1 (by rfl) ⟨3504086, by rfl⟩ : syracuseStep 4672115 = 7008173) B7008173
theorem B3114743 : Blo 2075435 3114743 := bstep (se 1 (by rfl) ⟨2336057, by rfl⟩ : syracuseStep 3114743 = 4672115) B4672115
theorem B2076495 : Blo 2075435 2076495 := bstep (se 1 (by rfl) ⟨1557371, by rfl⟩ : syracuseStep 2076495 = 3114743) B3114743
theorem B3114749 : Blo 2075435 3114749 := bbase (se 3 (by rfl) ⟨584015, by rfl⟩ : syracuseStep 3114749 = 1168031) (by norm_num)
theorem B2076499 : Blo 2075435 2076499 := bstep (se 1 (by rfl) ⟨1557374, by rfl⟩ : syracuseStep 2076499 = 3114749) B3114749
theorem B4672133 : Blo 2075435 4672133 := bbase (se 4 (by rfl) ⟨438012, by rfl⟩ : syracuseStep 4672133 = 876025) (by norm_num)
theorem B3114755 : Blo 2075435 3114755 := bstep (se 1 (by rfl) ⟨2336066, by rfl⟩ : syracuseStep 3114755 = 4672133) B4672133
theorem B2076503 : Blo 2075435 2076503 := bstep (se 1 (by rfl) ⟨1557377, by rfl⟩ : syracuseStep 2076503 = 3114755) B3114755
theorem B14207669 : Blo 2075435 14207669 := bbase (se 5 (by rfl) ⟨665984, by rfl⟩ : syracuseStep 14207669 = 1331969) (by norm_num)
theorem B9471779 : Blo 2075435 9471779 := bstep (se 1 (by rfl) ⟨7103834, by rfl⟩ : syracuseStep 9471779 = 14207669) B14207669
theorem B6314519 : Blo 2075435 6314519 := bstep (se 1 (by rfl) ⟨4735889, by rfl⟩ : syracuseStep 6314519 = 9471779) B9471779
theorem B4209679 : Blo 2075435 4209679 := bstep (se 1 (by rfl) ⟨3157259, by rfl⟩ : syracuseStep 4209679 = 6314519) B6314519
theorem B5612905 : Blo 2075435 5612905 := bstep (se 2 (by rfl) ⟨2104839, by rfl⟩ : syracuseStep 5612905 = 4209679) B4209679
theorem B7483873 : Blo 2075435 7483873 := bstep (se 2 (by rfl) ⟨2806452, by rfl⟩ : syracuseStep 7483873 = 5612905) B5612905
theorem B9978497 : Blo 2075435 9978497 := bstep (se 2 (by rfl) ⟨3741936, by rfl⟩ : syracuseStep 9978497 = 7483873) B7483873
theorem B6652331 : Blo 2075435 6652331 := bstep (se 1 (by rfl) ⟨4989248, by rfl⟩ : syracuseStep 6652331 = 9978497) B9978497
theorem B4434887 : Blo 2075435 4434887 := bstep (se 1 (by rfl) ⟨3326165, by rfl⟩ : syracuseStep 4434887 = 6652331) B6652331
theorem B2956591 : Blo 2075435 2956591 := bstep (se 1 (by rfl) ⟨2217443, by rfl⟩ : syracuseStep 2956591 = 4434887) B4434887
theorem B3942121 : Blo 2075435 3942121 := bstep (se 2 (by rfl) ⟨1478295, by rfl⟩ : syracuseStep 3942121 = 2956591) B2956591
theorem B5256161 : Blo 2075435 5256161 := bstep (se 2 (by rfl) ⟨1971060, by rfl⟩ : syracuseStep 5256161 = 3942121) B3942121
theorem B3504107 : Blo 2075435 3504107 := bstep (se 1 (by rfl) ⟨2628080, by rfl⟩ : syracuseStep 3504107 = 5256161) B5256161
theorem B2336071 : Blo 2075435 2336071 := bstep (se 1 (by rfl) ⟨1752053, by rfl⟩ : syracuseStep 2336071 = 3504107) B3504107
theorem B3114761 : Blo 2075435 3114761 := bstep (se 2 (by rfl) ⟨1168035, by rfl⟩ : syracuseStep 3114761 = 2336071) B2336071
theorem B2076507 : Blo 2075435 2076507 := bstep (se 1 (by rfl) ⟨1557380, by rfl⟩ : syracuseStep 2076507 = 3114761) B3114761
theorem B10512341 : Blo 2075435 10512341 := bbase (se 7 (by rfl) ⟨123191, by rfl⟩ : syracuseStep 10512341 = 246383) (by norm_num)
theorem B7008227 : Blo 2075435 7008227 := bstep (se 1 (by rfl) ⟨5256170, by rfl⟩ : syracuseStep 7008227 = 10512341) B10512341
theorem B4672151 : Blo 2075435 4672151 := bstep (se 1 (by rfl) ⟨3504113, by rfl⟩ : syracuseStep 4672151 = 7008227) B7008227
theorem B3114767 : Blo 2075435 3114767 := bstep (se 1 (by rfl) ⟨2336075, by rfl⟩ : syracuseStep 3114767 = 4672151) B4672151
theorem B2076511 : Blo 2075435 2076511 := bstep (se 1 (by rfl) ⟨1557383, by rfl⟩ : syracuseStep 2076511 = 3114767) B3114767
theorem B3114773 : Blo 2075435 3114773 := bbase (se 6 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 3114773 = 146005) (by norm_num)
theorem B2076515 : Blo 2075435 2076515 := bstep (se 1 (by rfl) ⟨1557386, by rfl⟩ : syracuseStep 2076515 = 3114773) B3114773
theorem B182064469 : Blo 2075435 182064469 := bbase (se 14 (by rfl) ⟨16668, by rfl⟩ : syracuseStep 182064469 = 33337) (by norm_num)
theorem B242752625 : Blo 2075435 242752625 := bstep (se 2 (by rfl) ⟨91032234, by rfl⟩ : syracuseStep 242752625 = 182064469) B182064469
theorem B161835083 : Blo 2075435 161835083 := bstep (se 1 (by rfl) ⟨121376312, by rfl⟩ : syracuseStep 161835083 = 242752625) B242752625
theorem B107890055 : Blo 2075435 107890055 := bstep (se 1 (by rfl) ⟨80917541, by rfl⟩ : syracuseStep 107890055 = 161835083) B161835083
theorem B71926703 : Blo 2075435 71926703 := bstep (se 1 (by rfl) ⟨53945027, by rfl⟩ : syracuseStep 71926703 = 107890055) B107890055
theorem B47951135 : Blo 2075435 47951135 := bstep (se 1 (by rfl) ⟨35963351, by rfl⟩ : syracuseStep 47951135 = 71926703) B71926703
theorem B31967423 : Blo 2075435 31967423 := bstep (se 1 (by rfl) ⟨23975567, by rfl⟩ : syracuseStep 31967423 = 47951135) B47951135
theorem B21311615 : Blo 2075435 21311615 := bstep (se 1 (by rfl) ⟨15983711, by rfl⟩ : syracuseStep 21311615 = 31967423) B31967423
theorem B14207743 : Blo 2075435 14207743 := bstep (se 1 (by rfl) ⟨10655807, by rfl⟩ : syracuseStep 14207743 = 21311615) B21311615
theorem B75774629 : Blo 2075435 75774629 := bstep (se 4 (by rfl) ⟨7103871, by rfl⟩ : syracuseStep 75774629 = 14207743) B14207743
theorem B202065677 : Blo 2075435 202065677 := bstep (se 3 (by rfl) ⟨37887314, by rfl⟩ : syracuseStep 202065677 = 75774629) B75774629
theorem B134710451 : Blo 2075435 134710451 := bstep (se 1 (by rfl) ⟨101032838, by rfl⟩ : syracuseStep 134710451 = 202065677) B202065677
theorem B89806967 : Blo 2075435 89806967 := bstep (se 1 (by rfl) ⟨67355225, by rfl⟩ : syracuseStep 89806967 = 134710451) B134710451
theorem B59871311 : Blo 2075435 59871311 := bstep (se 1 (by rfl) ⟨44903483, by rfl⟩ : syracuseStep 59871311 = 89806967) B89806967
theorem B39914207 : Blo 2075435 39914207 := bstep (se 1 (by rfl) ⟨29935655, by rfl⟩ : syracuseStep 39914207 = 59871311) B59871311
theorem B26609471 : Blo 2075435 26609471 := bstep (se 1 (by rfl) ⟨19957103, by rfl⟩ : syracuseStep 26609471 = 39914207) B39914207
theorem B17739647 : Blo 2075435 17739647 := bstep (se 1 (by rfl) ⟨13304735, by rfl⟩ : syracuseStep 17739647 = 26609471) B26609471
theorem B11826431 : Blo 2075435 11826431 := bstep (se 1 (by rfl) ⟨8869823, by rfl⟩ : syracuseStep 11826431 = 17739647) B17739647
theorem B7884287 : Blo 2075435 7884287 := bstep (se 1 (by rfl) ⟨5913215, by rfl⟩ : syracuseStep 7884287 = 11826431) B11826431
theorem B5256191 : Blo 2075435 5256191 := bstep (se 1 (by rfl) ⟨3942143, by rfl⟩ : syracuseStep 5256191 = 7884287) B7884287
theorem B3504127 : Blo 2075435 3504127 := bstep (se 1 (by rfl) ⟨2628095, by rfl⟩ : syracuseStep 3504127 = 5256191) B5256191
theorem B4672169 : Blo 2075435 4672169 := bstep (se 2 (by rfl) ⟨1752063, by rfl⟩ : syracuseStep 4672169 = 3504127) B3504127
theorem B3114779 : Blo 2075435 3114779 := bstep (se 1 (by rfl) ⟨2336084, by rfl⟩ : syracuseStep 3114779 = 4672169) B4672169
theorem B2076519 : Blo 2075435 2076519 := bstep (se 1 (by rfl) ⟨1557389, by rfl⟩ : syracuseStep 2076519 = 3114779) B3114779
theorem B2336089 : Blo 2075435 2336089 := bbase (se 2 (by rfl) ⟨876033, by rfl⟩ : syracuseStep 2336089 = 1752067) (by norm_num)
theorem B3114785 : Blo 2075435 3114785 := bstep (se 2 (by rfl) ⟨1168044, by rfl⟩ : syracuseStep 3114785 = 2336089) B2336089
theorem B2076523 : Blo 2075435 2076523 := bstep (se 1 (by rfl) ⟨1557392, by rfl⟩ : syracuseStep 2076523 = 3114785) B3114785
theorem B3326197 : Blo 2075435 3326197 := bbase (se 5 (by rfl) ⟨155915, by rfl⟩ : syracuseStep 3326197 = 311831) (by norm_num)
theorem B4434929 : Blo 2075435 4434929 := bstep (se 2 (by rfl) ⟨1663098, by rfl⟩ : syracuseStep 4434929 = 3326197) B3326197
theorem B2956619 : Blo 2075435 2956619 := bstep (se 1 (by rfl) ⟨2217464, by rfl⟩ : syracuseStep 2956619 = 4434929) B4434929
theorem B7884317 : Blo 2075435 7884317 := bstep (se 3 (by rfl) ⟨1478309, by rfl⟩ : syracuseStep 7884317 = 2956619) B2956619
theorem B5256211 : Blo 2075435 5256211 := bstep (se 1 (by rfl) ⟨3942158, by rfl⟩ : syracuseStep 5256211 = 7884317) B7884317
theorem B7008281 : Blo 2075435 7008281 := bstep (se 2 (by rfl) ⟨2628105, by rfl⟩ : syracuseStep 7008281 = 5256211) B5256211
theorem B4672187 : Blo 2075435 4672187 := bstep (se 1 (by rfl) ⟨3504140, by rfl⟩ : syracuseStep 4672187 = 7008281) B7008281
theorem B3114791 : Blo 2075435 3114791 := bstep (se 1 (by rfl) ⟨2336093, by rfl⟩ : syracuseStep 3114791 = 4672187) B4672187
theorem B2076527 : Blo 2075435 2076527 := bstep (se 1 (by rfl) ⟨1557395, by rfl⟩ : syracuseStep 2076527 = 3114791) B3114791
theorem B3114797 : Blo 2075435 3114797 := bbase (se 3 (by rfl) ⟨584024, by rfl⟩ : syracuseStep 3114797 = 1168049) (by norm_num)
theorem B2076531 : Blo 2075435 2076531 := bstep (se 1 (by rfl) ⟨1557398, by rfl⟩ : syracuseStep 2076531 = 3114797) B3114797
theorem B4672205 : Blo 2075435 4672205 := bbase (se 3 (by rfl) ⟨876038, by rfl⟩ : syracuseStep 4672205 = 1752077) (by norm_num)
theorem B3114803 : Blo 2075435 3114803 := bstep (se 1 (by rfl) ⟨2336102, by rfl⟩ : syracuseStep 3114803 = 4672205) B4672205
theorem B2076535 : Blo 2075435 2076535 := bstep (se 1 (by rfl) ⟨1557401, by rfl⟩ : syracuseStep 2076535 = 3114803) B3114803
theorem B2628121 : Blo 2075435 2628121 := bbase (se 2 (by rfl) ⟨985545, by rfl⟩ : syracuseStep 2628121 = 1971091) (by norm_num)
theorem B3504161 : Blo 2075435 3504161 := bstep (se 2 (by rfl) ⟨1314060, by rfl⟩ : syracuseStep 3504161 = 2628121) B2628121
theorem B2336107 : Blo 2075435 2336107 := bstep (se 1 (by rfl) ⟨1752080, by rfl⟩ : syracuseStep 2336107 = 3504161) B3504161
theorem B3114809 : Blo 2075435 3114809 := bstep (se 2 (by rfl) ⟨1168053, by rfl⟩ : syracuseStep 3114809 = 2336107) B2336107
theorem B2076539 : Blo 2075435 2076539 := bstep (se 1 (by rfl) ⟨1557404, by rfl⟩ : syracuseStep 2076539 = 3114809) B3114809
theorem B8869925 : Blo 2075435 8869925 := bbase (se 4 (by rfl) ⟨831555, by rfl⟩ : syracuseStep 8869925 = 1663111) (by norm_num)
theorem B23653133 : Blo 2075435 23653133 := bstep (se 3 (by rfl) ⟨4434962, by rfl⟩ : syracuseStep 23653133 = 8869925) B8869925
theorem B15768755 : Blo 2075435 15768755 := bstep (se 1 (by rfl) ⟨11826566, by rfl⟩ : syracuseStep 15768755 = 23653133) B23653133
theorem B10512503 : Blo 2075435 10512503 := bstep (se 1 (by rfl) ⟨7884377, by rfl⟩ : syracuseStep 10512503 = 15768755) B15768755
theorem B7008335 : Blo 2075435 7008335 := bstep (se 1 (by rfl) ⟨5256251, by rfl⟩ : syracuseStep 7008335 = 10512503) B10512503
theorem B4672223 : Blo 2075435 4672223 := bstep (se 1 (by rfl) ⟨3504167, by rfl⟩ : syracuseStep 4672223 = 7008335) B7008335
theorem B3114815 : Blo 2075435 3114815 := bstep (se 1 (by rfl) ⟨2336111, by rfl⟩ : syracuseStep 3114815 = 4672223) B4672223
theorem B2076543 : Blo 2075435 2076543 := bstep (se 1 (by rfl) ⟨1557407, by rfl⟩ : syracuseStep 2076543 = 3114815) B3114815
theorem B3114821 : Blo 2075435 3114821 := bbase (se 4 (by rfl) ⟨292014, by rfl⟩ : syracuseStep 3114821 = 584029) (by norm_num)
theorem B2076547 : Blo 2075435 2076547 := bstep (se 1 (by rfl) ⟨1557410, by rfl⟩ : syracuseStep 2076547 = 3114821) B3114821
theorem B3504181 : Blo 2075435 3504181 := bbase (se 5 (by rfl) ⟨164258, by rfl⟩ : syracuseStep 3504181 = 328517) (by norm_num)
theorem B4672241 : Blo 2075435 4672241 := bstep (se 2 (by rfl) ⟨1752090, by rfl⟩ : syracuseStep 4672241 = 3504181) B3504181
theorem B3114827 : Blo 2075435 3114827 := bstep (se 1 (by rfl) ⟨2336120, by rfl⟩ : syracuseStep 3114827 = 4672241) B4672241
theorem B2076551 : Blo 2075435 2076551 := bstep (se 1 (by rfl) ⟨1557413, by rfl⟩ : syracuseStep 2076551 = 3114827) B3114827
theorem B2336125 : Blo 2075435 2336125 := bbase (se 3 (by rfl) ⟨438023, by rfl⟩ : syracuseStep 2336125 = 876047) (by norm_num)
theorem B3114833 : Blo 2075435 3114833 := bstep (se 2 (by rfl) ⟨1168062, by rfl⟩ : syracuseStep 3114833 = 2336125) B2336125
theorem B2076555 : Blo 2075435 2076555 := bstep (se 1 (by rfl) ⟨1557416, by rfl⟩ : syracuseStep 2076555 = 3114833) B3114833
theorem B7008389 : Blo 2075435 7008389 := bbase (se 4 (by rfl) ⟨657036, by rfl⟩ : syracuseStep 7008389 = 1314073) (by norm_num)
theorem B4672259 : Blo 2075435 4672259 := bstep (se 1 (by rfl) ⟨3504194, by rfl⟩ : syracuseStep 4672259 = 7008389) B7008389
theorem B3114839 : Blo 2075435 3114839 := bstep (se 1 (by rfl) ⟨2336129, by rfl⟩ : syracuseStep 3114839 = 4672259) B4672259
theorem B2076559 : Blo 2075435 2076559 := bstep (se 1 (by rfl) ⟨1557419, by rfl⟩ : syracuseStep 2076559 = 3114839) B3114839
theorem B3114845 : Blo 2075435 3114845 := bbase (se 3 (by rfl) ⟨584033, by rfl⟩ : syracuseStep 3114845 = 1168067) (by norm_num)
theorem B2076563 : Blo 2075435 2076563 := bstep (se 1 (by rfl) ⟨1557422, by rfl⟩ : syracuseStep 2076563 = 3114845) B3114845
theorem B4672277 : Blo 2075435 4672277 := bbase (se 6 (by rfl) ⟨109506, by rfl⟩ : syracuseStep 4672277 = 219013) (by norm_num)
theorem B3114851 : Blo 2075435 3114851 := bstep (se 1 (by rfl) ⟨2336138, by rfl⟩ : syracuseStep 3114851 = 4672277) B4672277
theorem B2076567 : Blo 2075435 2076567 := bstep (se 1 (by rfl) ⟨1557425, by rfl⟩ : syracuseStep 2076567 = 3114851) B3114851
theorem B7884485 : Blo 2075435 7884485 := bbase (se 4 (by rfl) ⟨739170, by rfl⟩ : syracuseStep 7884485 = 1478341) (by norm_num)
theorem B5256323 : Blo 2075435 5256323 := bstep (se 1 (by rfl) ⟨3942242, by rfl⟩ : syracuseStep 5256323 = 7884485) B7884485
theorem B3504215 : Blo 2075435 3504215 := bstep (se 1 (by rfl) ⟨2628161, by rfl⟩ : syracuseStep 3504215 = 5256323) B5256323
theorem B2336143 : Blo 2075435 2336143 := bstep (se 1 (by rfl) ⟨1752107, by rfl⟩ : syracuseStep 2336143 = 3504215) B3504215
theorem B3114857 : Blo 2075435 3114857 := bstep (se 2 (by rfl) ⟨1168071, by rfl⟩ : syracuseStep 3114857 = 2336143) B2336143
theorem B2076571 : Blo 2075435 2076571 := bstep (se 1 (by rfl) ⟨1557428, by rfl⟩ : syracuseStep 2076571 = 3114857) B3114857
theorem B9978821 : Blo 2075435 9978821 := bbase (se 4 (by rfl) ⟨935514, by rfl⟩ : syracuseStep 9978821 = 1871029) (by norm_num)
theorem B6652547 : Blo 2075435 6652547 := bstep (se 1 (by rfl) ⟨4989410, by rfl⟩ : syracuseStep 6652547 = 9978821) B9978821
theorem B4435031 : Blo 2075435 4435031 := bstep (se 1 (by rfl) ⟨3326273, by rfl⟩ : syracuseStep 4435031 = 6652547) B6652547
theorem B11826749 : Blo 2075435 11826749 := bstep (se 3 (by rfl) ⟨2217515, by rfl⟩ : syracuseStep 11826749 = 4435031) B4435031
theorem B7884499 : Blo 2075435 7884499 := bstep (se 1 (by rfl) ⟨5913374, by rfl⟩ : syracuseStep 7884499 = 11826749) B11826749
theorem B10512665 : Blo 2075435 10512665 := bstep (se 2 (by rfl) ⟨3942249, by rfl⟩ : syracuseStep 10512665 = 7884499) B7884499
theorem B7008443 : Blo 2075435 7008443 := bstep (se 1 (by rfl) ⟨5256332, by rfl⟩ : syracuseStep 7008443 = 10512665) B10512665
theorem B4672295 : Blo 2075435 4672295 := bstep (se 1 (by rfl) ⟨3504221, by rfl⟩ : syracuseStep 4672295 = 7008443) B7008443
theorem B3114863 : Blo 2075435 3114863 := bstep (se 1 (by rfl) ⟨2336147, by rfl⟩ : syracuseStep 3114863 = 4672295) B4672295
theorem B2076575 : Blo 2075435 2076575 := bstep (se 1 (by rfl) ⟨1557431, by rfl⟩ : syracuseStep 2076575 = 3114863) B3114863
theorem B3114869 : Blo 2075435 3114869 := bbase (se 5 (by rfl) ⟨146009, by rfl⟩ : syracuseStep 3114869 = 292019) (by norm_num)
theorem B2076579 : Blo 2075435 2076579 := bstep (se 1 (by rfl) ⟨1557434, by rfl⟩ : syracuseStep 2076579 = 3114869) B3114869
theorem B2528753 : Blo 2075435 2528753 := bbase (se 2 (by rfl) ⟨948282, by rfl⟩ : syracuseStep 2528753 = 1896565) (by norm_num)
theorem B6743341 : Blo 2075435 6743341 := bstep (se 3 (by rfl) ⟨1264376, by rfl⟩ : syracuseStep 6743341 = 2528753) B2528753
theorem B35964485 : Blo 2075435 35964485 := bstep (se 4 (by rfl) ⟨3371670, by rfl⟩ : syracuseStep 35964485 = 6743341) B6743341
theorem B23976323 : Blo 2075435 23976323 := bstep (se 1 (by rfl) ⟨17982242, by rfl⟩ : syracuseStep 23976323 = 35964485) B35964485
theorem B15984215 : Blo 2075435 15984215 := bstep (se 1 (by rfl) ⟨11988161, by rfl⟩ : syracuseStep 15984215 = 23976323) B23976323
theorem B10656143 : Blo 2075435 10656143 := bstep (se 1 (by rfl) ⟨7992107, by rfl⟩ : syracuseStep 10656143 = 15984215) B15984215
theorem B7104095 : Blo 2075435 7104095 := bstep (se 1 (by rfl) ⟨5328071, by rfl⟩ : syracuseStep 7104095 = 10656143) B10656143
theorem B4736063 : Blo 2075435 4736063 := bstep (se 1 (by rfl) ⟨3552047, by rfl⟩ : syracuseStep 4736063 = 7104095) B7104095
theorem B3157375 : Blo 2075435 3157375 := bstep (se 1 (by rfl) ⟨2368031, by rfl⟩ : syracuseStep 3157375 = 4736063) B4736063
theorem B4209833 : Blo 2075435 4209833 := bstep (se 2 (by rfl) ⟨1578687, by rfl⟩ : syracuseStep 4209833 = 3157375) B3157375
theorem B11226221 : Blo 2075435 11226221 := bstep (se 3 (by rfl) ⟨2104916, by rfl⟩ : syracuseStep 11226221 = 4209833) B4209833
theorem B7484147 : Blo 2075435 7484147 := bstep (se 1 (by rfl) ⟨5613110, by rfl⟩ : syracuseStep 7484147 = 11226221) B11226221
theorem B4989431 : Blo 2075435 4989431 := bstep (se 1 (by rfl) ⟨3742073, by rfl⟩ : syracuseStep 4989431 = 7484147) B7484147
theorem B3326287 : Blo 2075435 3326287 := bstep (se 1 (by rfl) ⟨2494715, by rfl⟩ : syracuseStep 3326287 = 4989431) B4989431
theorem B4435049 : Blo 2075435 4435049 := bstep (se 2 (by rfl) ⟨1663143, by rfl⟩ : syracuseStep 4435049 = 3326287) B3326287
theorem B2956699 : Blo 2075435 2956699 := bstep (se 1 (by rfl) ⟨2217524, by rfl⟩ : syracuseStep 2956699 = 4435049) B4435049
theorem B3942265 : Blo 2075435 3942265 := bstep (se 2 (by rfl) ⟨1478349, by rfl⟩ : syracuseStep 3942265 = 2956699) B2956699
theorem B5256353 : Blo 2075435 5256353 := bstep (se 2 (by rfl) ⟨1971132, by rfl⟩ : syracuseStep 5256353 = 3942265) B3942265
theorem B3504235 : Blo 2075435 3504235 := bstep (se 1 (by rfl) ⟨2628176, by rfl⟩ : syracuseStep 3504235 = 5256353) B5256353
theorem B4672313 : Blo 2075435 4672313 := bstep (se 2 (by rfl) ⟨1752117, by rfl⟩ : syracuseStep 4672313 = 3504235) B3504235
theorem B3114875 : Blo 2075435 3114875 := bstep (se 1 (by rfl) ⟨2336156, by rfl⟩ : syracuseStep 3114875 = 4672313) B4672313
theorem B2076583 : Blo 2075435 2076583 := bstep (se 1 (by rfl) ⟨1557437, by rfl⟩ : syracuseStep 2076583 = 3114875) B3114875
theorem B2336161 : Blo 2075435 2336161 := bbase (se 2 (by rfl) ⟨876060, by rfl⟩ : syracuseStep 2336161 = 1752121) (by norm_num)
theorem B3114881 : Blo 2075435 3114881 := bstep (se 2 (by rfl) ⟨1168080, by rfl⟩ : syracuseStep 3114881 = 2336161) B2336161
theorem B2076587 : Blo 2075435 2076587 := bstep (se 1 (by rfl) ⟨1557440, by rfl⟩ : syracuseStep 2076587 = 3114881) B3114881
theorem B5256373 : Blo 2075435 5256373 := bbase (se 5 (by rfl) ⟨246392, by rfl⟩ : syracuseStep 5256373 = 492785) (by norm_num)
theorem B7008497 : Blo 2075435 7008497 := bstep (se 2 (by rfl) ⟨2628186, by rfl⟩ : syracuseStep 7008497 = 5256373) B5256373
theorem B4672331 : Blo 2075435 4672331 := bstep (se 1 (by rfl) ⟨3504248, by rfl⟩ : syracuseStep 4672331 = 7008497) B7008497
theorem B3114887 : Blo 2075435 3114887 := bstep (se 1 (by rfl) ⟨2336165, by rfl⟩ : syracuseStep 3114887 = 4672331) B4672331
theorem B2076591 : Blo 2075435 2076591 := bstep (se 1 (by rfl) ⟨1557443, by rfl⟩ : syracuseStep 2076591 = 3114887) B3114887
theorem B3114893 : Blo 2075435 3114893 := bbase (se 3 (by rfl) ⟨584042, by rfl⟩ : syracuseStep 3114893 = 1168085) (by norm_num)
theorem B2076595 : Blo 2075435 2076595 := bstep (se 1 (by rfl) ⟨1557446, by rfl⟩ : syracuseStep 2076595 = 3114893) B3114893
theorem B4672349 : Blo 2075435 4672349 := bbase (se 3 (by rfl) ⟨876065, by rfl⟩ : syracuseStep 4672349 = 1752131) (by norm_num)
theorem B3114899 : Blo 2075435 3114899 := bstep (se 1 (by rfl) ⟨2336174, by rfl⟩ : syracuseStep 3114899 = 4672349) B4672349
theorem B2076599 : Blo 2075435 2076599 := bstep (se 1 (by rfl) ⟨1557449, by rfl⟩ : syracuseStep 2076599 = 3114899) B3114899
theorem B3504269 : Blo 2075435 3504269 := bbase (se 3 (by rfl) ⟨657050, by rfl⟩ : syracuseStep 3504269 = 1314101) (by norm_num)
theorem B2336179 : Blo 2075435 2336179 := bstep (se 1 (by rfl) ⟨1752134, by rfl⟩ : syracuseStep 2336179 = 3504269) B3504269
theorem B3114905 : Blo 2075435 3114905 := bstep (se 2 (by rfl) ⟨1168089, by rfl⟩ : syracuseStep 3114905 = 2336179) B2336179
theorem B2076603 : Blo 2075435 2076603 := bstep (se 1 (by rfl) ⟨1557452, by rfl⟩ : syracuseStep 2076603 = 3114905) B3114905
theorem B9732469 : Blo 2075435 9732469 := bbase (se 5 (by rfl) ⟨456209, by rfl⟩ : syracuseStep 9732469 = 912419) (by norm_num)
theorem B12976625 : Blo 2075435 12976625 := bstep (se 2 (by rfl) ⟨4866234, by rfl⟩ : syracuseStep 12976625 = 9732469) B9732469
theorem B34604333 : Blo 2075435 34604333 := bstep (se 3 (by rfl) ⟨6488312, by rfl⟩ : syracuseStep 34604333 = 12976625) B12976625
theorem B23069555 : Blo 2075435 23069555 := bstep (se 1 (by rfl) ⟨17302166, by rfl⟩ : syracuseStep 23069555 = 34604333) B34604333
theorem B15379703 : Blo 2075435 15379703 := bstep (se 1 (by rfl) ⟨11534777, by rfl⟩ : syracuseStep 15379703 = 23069555) B23069555
theorem B10253135 : Blo 2075435 10253135 := bstep (se 1 (by rfl) ⟨7689851, by rfl⟩ : syracuseStep 10253135 = 15379703) B15379703
theorem B6835423 : Blo 2075435 6835423 := bstep (se 1 (by rfl) ⟨5126567, by rfl⟩ : syracuseStep 6835423 = 10253135) B10253135
theorem B9113897 : Blo 2075435 9113897 := bstep (se 2 (by rfl) ⟨3417711, by rfl⟩ : syracuseStep 9113897 = 6835423) B6835423
theorem B6075931 : Blo 2075435 6075931 := bstep (se 1 (by rfl) ⟨4556948, by rfl⟩ : syracuseStep 6075931 = 9113897) B9113897
theorem B8101241 : Blo 2075435 8101241 := bstep (se 2 (by rfl) ⟨3037965, by rfl⟩ : syracuseStep 8101241 = 6075931) B6075931
theorem B5400827 : Blo 2075435 5400827 := bstep (se 1 (by rfl) ⟨4050620, by rfl⟩ : syracuseStep 5400827 = 8101241) B8101241
theorem B3600551 : Blo 2075435 3600551 := bstep (se 1 (by rfl) ⟨2700413, by rfl⟩ : syracuseStep 3600551 = 5400827) B5400827
theorem B2400367 : Blo 2075435 2400367 := bstep (se 1 (by rfl) ⟨1800275, by rfl⟩ : syracuseStep 2400367 = 3600551) B3600551
theorem B3200489 : Blo 2075435 3200489 := bstep (se 2 (by rfl) ⟨1200183, by rfl⟩ : syracuseStep 3200489 = 2400367) B2400367
theorem B2133659 : Blo 2075435 2133659 := bstep (se 1 (by rfl) ⟨1600244, by rfl⟩ : syracuseStep 2133659 = 3200489) B3200489
theorem B5689757 : Blo 2075435 5689757 := bstep (se 3 (by rfl) ⟨1066829, by rfl⟩ : syracuseStep 5689757 = 2133659) B2133659
theorem B15172685 : Blo 2075435 15172685 := bstep (se 3 (by rfl) ⟨2844878, by rfl⟩ : syracuseStep 15172685 = 5689757) B5689757
theorem B10115123 : Blo 2075435 10115123 := bstep (se 1 (by rfl) ⟨7586342, by rfl⟩ : syracuseStep 10115123 = 15172685) B15172685
theorem B26973661 : Blo 2075435 26973661 := bstep (se 3 (by rfl) ⟨5057561, by rfl⟩ : syracuseStep 26973661 = 10115123) B10115123
theorem B35964881 : Blo 2075435 35964881 := bstep (se 2 (by rfl) ⟨13486830, by rfl⟩ : syracuseStep 35964881 = 26973661) B26973661
theorem B23976587 : Blo 2075435 23976587 := bstep (se 1 (by rfl) ⟨17982440, by rfl⟩ : syracuseStep 23976587 = 35964881) B35964881
theorem B15984391 : Blo 2075435 15984391 := bstep (se 1 (by rfl) ⟨11988293, by rfl⟩ : syracuseStep 15984391 = 23976587) B23976587
theorem B21312521 : Blo 2075435 21312521 := bstep (se 2 (by rfl) ⟨7992195, by rfl⟩ : syracuseStep 21312521 = 15984391) B15984391
theorem B14208347 : Blo 2075435 14208347 := bstep (se 1 (by rfl) ⟨10656260, by rfl⟩ : syracuseStep 14208347 = 21312521) B21312521
theorem B9472231 : Blo 2075435 9472231 := bstep (se 1 (by rfl) ⟨7104173, by rfl⟩ : syracuseStep 9472231 = 14208347) B14208347
theorem B12629641 : Blo 2075435 12629641 := bstep (se 2 (by rfl) ⟨4736115, by rfl⟩ : syracuseStep 12629641 = 9472231) B9472231
theorem B16839521 : Blo 2075435 16839521 := bstep (se 2 (by rfl) ⟨6314820, by rfl⟩ : syracuseStep 16839521 = 12629641) B12629641
theorem B11226347 : Blo 2075435 11226347 := bstep (se 1 (by rfl) ⟨8419760, by rfl⟩ : syracuseStep 11226347 = 16839521) B16839521
theorem B7484231 : Blo 2075435 7484231 := bstep (se 1 (by rfl) ⟨5613173, by rfl⟩ : syracuseStep 7484231 = 11226347) B11226347
theorem B4989487 : Blo 2075435 4989487 := bstep (se 1 (by rfl) ⟨3742115, by rfl⟩ : syracuseStep 4989487 = 7484231) B7484231
theorem B6652649 : Blo 2075435 6652649 := bstep (se 2 (by rfl) ⟨2494743, by rfl⟩ : syracuseStep 6652649 = 4989487) B4989487
theorem B17740397 : Blo 2075435 17740397 := bstep (se 3 (by rfl) ⟨3326324, by rfl⟩ : syracuseStep 17740397 = 6652649) B6652649
theorem B11826931 : Blo 2075435 11826931 := bstep (se 1 (by rfl) ⟨8870198, by rfl⟩ : syracuseStep 11826931 = 17740397) B17740397
theorem B15769241 : Blo 2075435 15769241 := bstep (se 2 (by rfl) ⟨5913465, by rfl⟩ : syracuseStep 15769241 = 11826931) B11826931
theorem B10512827 : Blo 2075435 10512827 := bstep (se 1 (by rfl) ⟨7884620, by rfl⟩ : syracuseStep 10512827 = 15769241) B15769241
theorem B7008551 : Blo 2075435 7008551 := bstep (se 1 (by rfl) ⟨5256413, by rfl⟩ : syracuseStep 7008551 = 10512827) B10512827
theorem B4672367 : Blo 2075435 4672367 := bstep (se 1 (by rfl) ⟨3504275, by rfl⟩ : syracuseStep 4672367 = 7008551) B7008551
theorem B3114911 : Blo 2075435 3114911 := bstep (se 1 (by rfl) ⟨2336183, by rfl⟩ : syracuseStep 3114911 = 4672367) B4672367
theorem B2076607 : Blo 2075435 2076607 := bstep (se 1 (by rfl) ⟨1557455, by rfl⟩ : syracuseStep 2076607 = 3114911) B3114911
theorem B3114917 : Blo 2075435 3114917 := bbase (se 4 (by rfl) ⟨292023, by rfl⟩ : syracuseStep 3114917 = 584047) (by norm_num)
theorem B2076611 : Blo 2075435 2076611 := bstep (se 1 (by rfl) ⟨1557458, by rfl⟩ : syracuseStep 2076611 = 3114917) B3114917
theorem B2628217 : Blo 2075435 2628217 := bbase (se 2 (by rfl) ⟨985581, by rfl⟩ : syracuseStep 2628217 = 1971163) (by norm_num)
theorem B3504289 : Blo 2075435 3504289 := bstep (se 2 (by rfl) ⟨1314108, by rfl⟩ : syracuseStep 3504289 = 2628217) B2628217
theorem B4672385 : Blo 2075435 4672385 := bstep (se 2 (by rfl) ⟨1752144, by rfl⟩ : syracuseStep 4672385 = 3504289) B3504289
theorem B3114923 : Blo 2075435 3114923 := bstep (se 1 (by rfl) ⟨2336192, by rfl⟩ : syracuseStep 3114923 = 4672385) B4672385
theorem B2076615 : Blo 2075435 2076615 := bstep (se 1 (by rfl) ⟨1557461, by rfl⟩ : syracuseStep 2076615 = 3114923) B3114923
theorem B2336197 : Blo 2075435 2336197 := bbase (se 4 (by rfl) ⟨219018, by rfl⟩ : syracuseStep 2336197 = 438037) (by norm_num)
theorem B3114929 : Blo 2075435 3114929 := bstep (se 2 (by rfl) ⟨1168098, by rfl⟩ : syracuseStep 3114929 = 2336197) B2336197
theorem B2076619 : Blo 2075435 2076619 := bstep (se 1 (by rfl) ⟨1557464, by rfl⟩ : syracuseStep 2076619 = 3114929) B3114929
theorem B3942341 : Blo 2075435 3942341 := bbase (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) (by norm_num)
theorem B2628227 : Blo 2075435 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B7008605 : Blo 2075435 7008605 := bstep (se 3 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 7008605 = 2628227) B2628227
theorem B4672403 : Blo 2075435 4672403 := bstep (se 1 (by rfl) ⟨3504302, by rfl⟩ : syracuseStep 4672403 = 7008605) B7008605
theorem B3114935 : Blo 2075435 3114935 := bstep (se 1 (by rfl) ⟨2336201, by rfl⟩ : syracuseStep 3114935 = 4672403) B4672403
theorem B2076623 : Blo 2075435 2076623 := bstep (se 1 (by rfl) ⟨1557467, by rfl⟩ : syracuseStep 2076623 = 3114935) B3114935
theorem B3114941 : Blo 2075435 3114941 := bbase (se 3 (by rfl) ⟨584051, by rfl⟩ : syracuseStep 3114941 = 1168103) (by norm_num)
theorem B2076627 : Blo 2075435 2076627 := bstep (se 1 (by rfl) ⟨1557470, by rfl⟩ : syracuseStep 2076627 = 3114941) B3114941
theorem B4672421 : Blo 2075435 4672421 := bbase (se 4 (by rfl) ⟨438039, by rfl⟩ : syracuseStep 4672421 = 876079) (by norm_num)
theorem B3114947 : Blo 2075435 3114947 := bstep (se 1 (by rfl) ⟨2336210, by rfl⟩ : syracuseStep 3114947 = 4672421) B4672421
theorem B2076631 : Blo 2075435 2076631 := bstep (se 1 (by rfl) ⟨1557473, by rfl⟩ : syracuseStep 2076631 = 3114947) B3114947
theorem B5256485 : Blo 2075435 5256485 := bbase (se 4 (by rfl) ⟨492795, by rfl⟩ : syracuseStep 5256485 = 985591) (by norm_num)
theorem B3504323 : Blo 2075435 3504323 := bstep (se 1 (by rfl) ⟨2628242, by rfl⟩ : syracuseStep 3504323 = 5256485) B5256485
theorem B2336215 : Blo 2075435 2336215 := bstep (se 1 (by rfl) ⟨1752161, by rfl⟩ : syracuseStep 2336215 = 3504323) B3504323
theorem B3114953 : Blo 2075435 3114953 := bstep (se 2 (by rfl) ⟨1168107, by rfl⟩ : syracuseStep 3114953 = 2336215) B2336215
theorem B2076635 : Blo 2075435 2076635 := bstep (se 1 (by rfl) ⟨1557476, by rfl⟩ : syracuseStep 2076635 = 3114953) B3114953
theorem B5913557 : Blo 2075435 5913557 := bbase (se 7 (by rfl) ⟨69299, by rfl⟩ : syracuseStep 5913557 = 138599) (by norm_num)
theorem B3942371 : Blo 2075435 3942371 := bstep (se 1 (by rfl) ⟨2956778, by rfl⟩ : syracuseStep 3942371 = 5913557) B5913557
theorem B10512989 : Blo 2075435 10512989 := bstep (se 3 (by rfl) ⟨1971185, by rfl⟩ : syracuseStep 10512989 = 3942371) B3942371
theorem B7008659 : Blo 2075435 7008659 := bstep (se 1 (by rfl) ⟨5256494, by rfl⟩ : syracuseStep 7008659 = 10512989) B10512989
theorem B4672439 : Blo 2075435 4672439 := bstep (se 1 (by rfl) ⟨3504329, by rfl⟩ : syracuseStep 4672439 = 7008659) B7008659
theorem B3114959 : Blo 2075435 3114959 := bstep (se 1 (by rfl) ⟨2336219, by rfl⟩ : syracuseStep 3114959 = 4672439) B4672439
theorem B2076639 : Blo 2075435 2076639 := bstep (se 1 (by rfl) ⟨1557479, by rfl⟩ : syracuseStep 2076639 = 3114959) B3114959
theorem B3114965 : Blo 2075435 3114965 := bbase (se 7 (by rfl) ⟨36503, by rfl⟩ : syracuseStep 3114965 = 73007) (by norm_num)
theorem B2076643 : Blo 2075435 2076643 := bstep (se 1 (by rfl) ⟨1557482, by rfl⟩ : syracuseStep 2076643 = 3114965) B3114965
theorem B7884773 : Blo 2075435 7884773 := bbase (se 4 (by rfl) ⟨739197, by rfl⟩ : syracuseStep 7884773 = 1478395) (by norm_num)
theorem B5256515 : Blo 2075435 5256515 := bstep (se 1 (by rfl) ⟨3942386, by rfl⟩ : syracuseStep 5256515 = 7884773) B7884773
theorem B3504343 : Blo 2075435 3504343 := bstep (se 1 (by rfl) ⟨2628257, by rfl⟩ : syracuseStep 3504343 = 5256515) B5256515
theorem B4672457 : Blo 2075435 4672457 := bstep (se 2 (by rfl) ⟨1752171, by rfl⟩ : syracuseStep 4672457 = 3504343) B3504343
theorem B3114971 : Blo 2075435 3114971 := bstep (se 1 (by rfl) ⟨2336228, by rfl⟩ : syracuseStep 3114971 = 4672457) B4672457
theorem B2076647 : Blo 2075435 2076647 := bstep (se 1 (by rfl) ⟨1557485, by rfl⟩ : syracuseStep 2076647 = 3114971) B3114971
theorem B2336233 : Blo 2075435 2336233 := bbase (se 2 (by rfl) ⟨876087, by rfl⟩ : syracuseStep 2336233 = 1752175) (by norm_num)
theorem B3114977 : Blo 2075435 3114977 := bstep (se 2 (by rfl) ⟨1168116, by rfl⟩ : syracuseStep 3114977 = 2336233) B2336233
theorem B2076651 : Blo 2075435 2076651 := bstep (se 1 (by rfl) ⟨1557488, by rfl⟩ : syracuseStep 2076651 = 3114977) B3114977
theorem B2217601 : Blo 2075435 2217601 := bbase (se 2 (by rfl) ⟨831600, by rfl⟩ : syracuseStep 2217601 = 1663201) (by norm_num)
theorem B11827205 : Blo 2075435 11827205 := bstep (se 4 (by rfl) ⟨1108800, by rfl⟩ : syracuseStep 11827205 = 2217601) B2217601
theorem B7884803 : Blo 2075435 7884803 := bstep (se 1 (by rfl) ⟨5913602, by rfl⟩ : syracuseStep 7884803 = 11827205) B11827205
theorem B5256535 : Blo 2075435 5256535 := bstep (se 1 (by rfl) ⟨3942401, by rfl⟩ : syracuseStep 5256535 = 7884803) B7884803
theorem B7008713 : Blo 2075435 7008713 := bstep (se 2 (by rfl) ⟨2628267, by rfl⟩ : syracuseStep 7008713 = 5256535) B5256535
theorem B4672475 : Blo 2075435 4672475 := bstep (se 1 (by rfl) ⟨3504356, by rfl⟩ : syracuseStep 4672475 = 7008713) B7008713
theorem B3114983 : Blo 2075435 3114983 := bstep (se 1 (by rfl) ⟨2336237, by rfl⟩ : syracuseStep 3114983 = 4672475) B4672475
theorem B2076655 : Blo 2075435 2076655 := bstep (se 1 (by rfl) ⟨1557491, by rfl⟩ : syracuseStep 2076655 = 3114983) B3114983
theorem B3114989 : Blo 2075435 3114989 := bbase (se 3 (by rfl) ⟨584060, by rfl⟩ : syracuseStep 3114989 = 1168121) (by norm_num)
theorem B2076659 : Blo 2075435 2076659 := bstep (se 1 (by rfl) ⟨1557494, by rfl⟩ : syracuseStep 2076659 = 3114989) B3114989
theorem B4672493 : Blo 2075435 4672493 := bbase (se 3 (by rfl) ⟨876092, by rfl⟩ : syracuseStep 4672493 = 1752185) (by norm_num)
theorem B3114995 : Blo 2075435 3114995 := bstep (se 1 (by rfl) ⟨2336246, by rfl⟩ : syracuseStep 3114995 = 4672493) B4672493
theorem B2076663 : Blo 2075435 2076663 := bstep (se 1 (by rfl) ⟨1557497, by rfl⟩ : syracuseStep 2076663 = 3114995) B3114995
theorem B4435229 : Blo 2075435 4435229 := bbase (se 3 (by rfl) ⟨831605, by rfl⟩ : syracuseStep 4435229 = 1663211) (by norm_num)
theorem B2956819 : Blo 2075435 2956819 := bstep (se 1 (by rfl) ⟨2217614, by rfl⟩ : syracuseStep 2956819 = 4435229) B4435229
theorem B3942425 : Blo 2075435 3942425 := bstep (se 2 (by rfl) ⟨1478409, by rfl⟩ : syracuseStep 3942425 = 2956819) B2956819
theorem B2628283 : Blo 2075435 2628283 := bstep (se 1 (by rfl) ⟨1971212, by rfl⟩ : syracuseStep 2628283 = 3942425) B3942425
theorem B3504377 : Blo 2075435 3504377 := bstep (se 2 (by rfl) ⟨1314141, by rfl⟩ : syracuseStep 3504377 = 2628283) B2628283
theorem B2336251 : Blo 2075435 2336251 := bstep (se 1 (by rfl) ⟨1752188, by rfl⟩ : syracuseStep 2336251 = 3504377) B3504377
theorem B3115001 : Blo 2075435 3115001 := bstep (se 2 (by rfl) ⟨1168125, by rfl⟩ : syracuseStep 3115001 = 2336251) B2336251
theorem B2076667 : Blo 2075435 2076667 := bstep (se 1 (by rfl) ⟨1557500, by rfl⟩ : syracuseStep 2076667 = 3115001) B3115001
theorem B5328293 : Blo 2075435 5328293 := bbase (se 4 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 5328293 = 999055) (by norm_num)
theorem B56835125 : Blo 2075435 56835125 := bstep (se 5 (by rfl) ⟨2664146, by rfl⟩ : syracuseStep 56835125 = 5328293) B5328293
theorem B37890083 : Blo 2075435 37890083 := bstep (se 1 (by rfl) ⟨28417562, by rfl⟩ : syracuseStep 37890083 = 56835125) B56835125
theorem B25260055 : Blo 2075435 25260055 := bstep (se 1 (by rfl) ⟨18945041, by rfl⟩ : syracuseStep 25260055 = 37890083) B37890083
theorem B134720293 : Blo 2075435 134720293 := bstep (se 4 (by rfl) ⟨12630027, by rfl⟩ : syracuseStep 134720293 = 25260055) B25260055
theorem B179627057 : Blo 2075435 179627057 := bstep (se 2 (by rfl) ⟨67360146, by rfl⟩ : syracuseStep 179627057 = 134720293) B134720293
theorem B119751371 : Blo 2075435 119751371 := bstep (se 1 (by rfl) ⟨89813528, by rfl⟩ : syracuseStep 119751371 = 179627057) B179627057
theorem B79834247 : Blo 2075435 79834247 := bstep (se 1 (by rfl) ⟨59875685, by rfl⟩ : syracuseStep 79834247 = 119751371) B119751371
theorem B53222831 : Blo 2075435 53222831 := bstep (se 1 (by rfl) ⟨39917123, by rfl⟩ : syracuseStep 53222831 = 79834247) B79834247
theorem B35481887 : Blo 2075435 35481887 := bstep (se 1 (by rfl) ⟨26611415, by rfl⟩ : syracuseStep 35481887 = 53222831) B53222831
theorem B23654591 : Blo 2075435 23654591 := bstep (se 1 (by rfl) ⟨17740943, by rfl⟩ : syracuseStep 23654591 = 35481887) B35481887
theorem B15769727 : Blo 2075435 15769727 := bstep (se 1 (by rfl) ⟨11827295, by rfl⟩ : syracuseStep 15769727 = 23654591) B23654591
theorem B10513151 : Blo 2075435 10513151 := bstep (se 1 (by rfl) ⟨7884863, by rfl⟩ : syracuseStep 10513151 = 15769727) B15769727
theorem B7008767 : Blo 2075435 7008767 := bstep (se 1 (by rfl) ⟨5256575, by rfl⟩ : syracuseStep 7008767 = 10513151) B10513151
theorem B4672511 : Blo 2075435 4672511 := bstep (se 1 (by rfl) ⟨3504383, by rfl⟩ : syracuseStep 4672511 = 7008767) B7008767
theorem B3115007 : Blo 2075435 3115007 := bstep (se 1 (by rfl) ⟨2336255, by rfl⟩ : syracuseStep 3115007 = 4672511) B4672511
theorem B2076671 : Blo 2075435 2076671 := bstep (se 1 (by rfl) ⟨1557503, by rfl⟩ : syracuseStep 2076671 = 3115007) B3115007
theorem B3115013 : Blo 2075435 3115013 := bbase (se 4 (by rfl) ⟨292032, by rfl⟩ : syracuseStep 3115013 = 584065) (by norm_num)
theorem B2076675 : Blo 2075435 2076675 := bstep (se 1 (by rfl) ⟨1557506, by rfl⟩ : syracuseStep 2076675 = 3115013) B3115013
theorem B3504397 : Blo 2075435 3504397 := bbase (se 3 (by rfl) ⟨657074, by rfl⟩ : syracuseStep 3504397 = 1314149) (by norm_num)
theorem B4672529 : Blo 2075435 4672529 := bstep (se 2 (by rfl) ⟨1752198, by rfl⟩ : syracuseStep 4672529 = 3504397) B3504397
theorem B3115019 : Blo 2075435 3115019 := bstep (se 1 (by rfl) ⟨2336264, by rfl⟩ : syracuseStep 3115019 = 4672529) B4672529
theorem B2076679 : Blo 2075435 2076679 := bstep (se 1 (by rfl) ⟨1557509, by rfl⟩ : syracuseStep 2076679 = 3115019) B3115019
theorem B2336269 : Blo 2075435 2336269 := bbase (se 3 (by rfl) ⟨438050, by rfl⟩ : syracuseStep 2336269 = 876101) (by norm_num)
theorem B3115025 : Blo 2075435 3115025 := bstep (se 2 (by rfl) ⟨1168134, by rfl⟩ : syracuseStep 3115025 = 2336269) B2336269
theorem B2076683 : Blo 2075435 2076683 := bstep (se 1 (by rfl) ⟨1557512, by rfl⟩ : syracuseStep 2076683 = 3115025) B3115025
theorem B7008821 : Blo 2075435 7008821 := bbase (se 5 (by rfl) ⟨328538, by rfl⟩ : syracuseStep 7008821 = 657077) (by norm_num)
theorem B4672547 : Blo 2075435 4672547 := bstep (se 1 (by rfl) ⟨3504410, by rfl⟩ : syracuseStep 4672547 = 7008821) B7008821
theorem B3115031 : Blo 2075435 3115031 := bstep (se 1 (by rfl) ⟨2336273, by rfl⟩ : syracuseStep 3115031 = 4672547) B4672547
theorem B2076687 : Blo 2075435 2076687 := bstep (se 1 (by rfl) ⟨1557515, by rfl⟩ : syracuseStep 2076687 = 3115031) B3115031
theorem B3115037 : Blo 2075435 3115037 := bbase (se 3 (by rfl) ⟨584069, by rfl⟩ : syracuseStep 3115037 = 1168139) (by norm_num)
theorem B2076691 : Blo 2075435 2076691 := bstep (se 1 (by rfl) ⟨1557518, by rfl⟩ : syracuseStep 2076691 = 3115037) B3115037
theorem B4672565 : Blo 2075435 4672565 := bbase (se 5 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 4672565 = 438053) (by norm_num)
theorem B3115043 : Blo 2075435 3115043 := bstep (se 1 (by rfl) ⟨2336282, by rfl⟩ : syracuseStep 3115043 = 4672565) B4672565
theorem B2076695 : Blo 2075435 2076695 := bstep (se 1 (by rfl) ⟨1557521, by rfl⟩ : syracuseStep 2076695 = 3115043) B3115043
theorem B4989709 : Blo 2075435 4989709 := bbase (se 3 (by rfl) ⟨935570, by rfl⟩ : syracuseStep 4989709 = 1871141) (by norm_num)
theorem B6652945 : Blo 2075435 6652945 := bstep (se 2 (by rfl) ⟨2494854, by rfl⟩ : syracuseStep 6652945 = 4989709) B4989709
theorem B8870593 : Blo 2075435 8870593 := bstep (se 2 (by rfl) ⟨3326472, by rfl⟩ : syracuseStep 8870593 = 6652945) B6652945
theorem B11827457 : Blo 2075435 11827457 := bstep (se 2 (by rfl) ⟨4435296, by rfl⟩ : syracuseStep 11827457 = 8870593) B8870593
theorem B7884971 : Blo 2075435 7884971 := bstep (se 1 (by rfl) ⟨5913728, by rfl⟩ : syracuseStep 7884971 = 11827457) B11827457
theorem B5256647 : Blo 2075435 5256647 := bstep (se 1 (by rfl) ⟨3942485, by rfl⟩ : syracuseStep 5256647 = 7884971) B7884971
theorem B3504431 : Blo 2075435 3504431 := bstep (se 1 (by rfl) ⟨2628323, by rfl⟩ : syracuseStep 3504431 = 5256647) B5256647
theorem B2336287 : Blo 2075435 2336287 := bstep (se 1 (by rfl) ⟨1752215, by rfl⟩ : syracuseStep 2336287 = 3504431) B3504431
theorem B3115049 : Blo 2075435 3115049 := bstep (se 2 (by rfl) ⟨1168143, by rfl⟩ : syracuseStep 3115049 = 2336287) B2336287
theorem B2076699 : Blo 2075435 2076699 := bstep (se 1 (by rfl) ⟨1557524, by rfl⟩ : syracuseStep 2076699 = 3115049) B3115049
theorem B2806717 : Blo 2075435 2806717 := bbase (se 3 (by rfl) ⟨526259, by rfl⟩ : syracuseStep 2806717 = 1052519) (by norm_num)
theorem B3742289 : Blo 2075435 3742289 := bstep (se 2 (by rfl) ⟨1403358, by rfl⟩ : syracuseStep 3742289 = 2806717) B2806717
theorem B2494859 : Blo 2075435 2494859 := bstep (se 1 (by rfl) ⟨1871144, by rfl⟩ : syracuseStep 2494859 = 3742289) B3742289
theorem B6652957 : Blo 2075435 6652957 := bstep (se 3 (by rfl) ⟨1247429, by rfl⟩ : syracuseStep 6652957 = 2494859) B2494859
theorem B8870609 : Blo 2075435 8870609 := bstep (se 2 (by rfl) ⟨3326478, by rfl⟩ : syracuseStep 8870609 = 6652957) B6652957
theorem B5913739 : Blo 2075435 5913739 := bstep (se 1 (by rfl) ⟨4435304, by rfl⟩ : syracuseStep 5913739 = 8870609) B8870609
theorem B7884985 : Blo 2075435 7884985 := bstep (se 2 (by rfl) ⟨2956869, by rfl⟩ : syracuseStep 7884985 = 5913739) B5913739
theorem B10513313 : Blo 2075435 10513313 := bstep (se 2 (by rfl) ⟨3942492, by rfl⟩ : syracuseStep 10513313 = 7884985) B7884985
theorem B7008875 : Blo 2075435 7008875 := bstep (se 1 (by rfl) ⟨5256656, by rfl⟩ : syracuseStep 7008875 = 10513313) B10513313
theorem B4672583 : Blo 2075435 4672583 := bstep (se 1 (by rfl) ⟨3504437, by rfl⟩ : syracuseStep 4672583 = 7008875) B7008875
theorem B3115055 : Blo 2075435 3115055 := bstep (se 1 (by rfl) ⟨2336291, by rfl⟩ : syracuseStep 3115055 = 4672583) B4672583
theorem B2076703 : Blo 2075435 2076703 := bstep (se 1 (by rfl) ⟨1557527, by rfl⟩ : syracuseStep 2076703 = 3115055) B3115055
theorem B3115061 : Blo 2075435 3115061 := bbase (se 5 (by rfl) ⟨146018, by rfl⟩ : syracuseStep 3115061 = 292037) (by norm_num)
theorem B2076707 : Blo 2075435 2076707 := bstep (se 1 (by rfl) ⟨1557530, by rfl⟩ : syracuseStep 2076707 = 3115061) B3115061
theorem B5256677 : Blo 2075435 5256677 := bbase (se 4 (by rfl) ⟨492813, by rfl⟩ : syracuseStep 5256677 = 985627) (by norm_num)
theorem B3504451 : Blo 2075435 3504451 := bstep (se 1 (by rfl) ⟨2628338, by rfl⟩ : syracuseStep 3504451 = 5256677) B5256677
theorem B4672601 : Blo 2075435 4672601 := bstep (se 2 (by rfl) ⟨1752225, by rfl⟩ : syracuseStep 4672601 = 3504451) B3504451
theorem B3115067 : Blo 2075435 3115067 := bstep (se 1 (by rfl) ⟨2336300, by rfl⟩ : syracuseStep 3115067 = 4672601) B4672601
theorem B2076711 : Blo 2075435 2076711 := bstep (se 1 (by rfl) ⟨1557533, by rfl⟩ : syracuseStep 2076711 = 3115067) B3115067
theorem B2336305 : Blo 2075435 2336305 := bbase (se 2 (by rfl) ⟨876114, by rfl⟩ : syracuseStep 2336305 = 1752229) (by norm_num)
theorem B3115073 : Blo 2075435 3115073 := bstep (se 2 (by rfl) ⟨1168152, by rfl⟩ : syracuseStep 3115073 = 2336305) B2336305
theorem B2076715 : Blo 2075435 2076715 := bstep (se 1 (by rfl) ⟨1557536, by rfl⟩ : syracuseStep 2076715 = 3115073) B3115073
theorem B4989757 : Blo 2075435 4989757 := bbase (se 3 (by rfl) ⟨935579, by rfl⟩ : syracuseStep 4989757 = 1871159) (by norm_num)
theorem B6653009 : Blo 2075435 6653009 := bstep (se 2 (by rfl) ⟨2494878, by rfl⟩ : syracuseStep 6653009 = 4989757) B4989757
theorem B4435339 : Blo 2075435 4435339 := bstep (se 1 (by rfl) ⟨3326504, by rfl⟩ : syracuseStep 4435339 = 6653009) B6653009
theorem B5913785 : Blo 2075435 5913785 := bstep (se 2 (by rfl) ⟨2217669, by rfl⟩ : syracuseStep 5913785 = 4435339) B4435339
theorem B3942523 : Blo 2075435 3942523 := bstep (se 1 (by rfl) ⟨2956892, by rfl⟩ : syracuseStep 3942523 = 5913785) B5913785
theorem B5256697 : Blo 2075435 5256697 := bstep (se 2 (by rfl) ⟨1971261, by rfl⟩ : syracuseStep 5256697 = 3942523) B3942523
theorem B7008929 : Blo 2075435 7008929 := bstep (se 2 (by rfl) ⟨2628348, by rfl⟩ : syracuseStep 7008929 = 5256697) B5256697
theorem B4672619 : Blo 2075435 4672619 := bstep (se 1 (by rfl) ⟨3504464, by rfl⟩ : syracuseStep 4672619 = 7008929) B7008929
theorem B3115079 : Blo 2075435 3115079 := bstep (se 1 (by rfl) ⟨2336309, by rfl⟩ : syracuseStep 3115079 = 4672619) B4672619
theorem B2076719 : Blo 2075435 2076719 := bstep (se 1 (by rfl) ⟨1557539, by rfl⟩ : syracuseStep 2076719 = 3115079) B3115079
theorem B3115085 : Blo 2075435 3115085 := bbase (se 3 (by rfl) ⟨584078, by rfl⟩ : syracuseStep 3115085 = 1168157) (by norm_num)
theorem B2076723 : Blo 2075435 2076723 := bstep (se 1 (by rfl) ⟨1557542, by rfl⟩ : syracuseStep 2076723 = 3115085) B3115085
theorem B4672637 : Blo 2075435 4672637 := bbase (se 3 (by rfl) ⟨876119, by rfl⟩ : syracuseStep 4672637 = 1752239) (by norm_num)
theorem B3115091 : Blo 2075435 3115091 := bstep (se 1 (by rfl) ⟨2336318, by rfl⟩ : syracuseStep 3115091 = 4672637) B4672637
theorem B2076727 : Blo 2075435 2076727 := bstep (se 1 (by rfl) ⟨1557545, by rfl⟩ : syracuseStep 2076727 = 3115091) B3115091
theorem B3504485 : Blo 2075435 3504485 := bbase (se 4 (by rfl) ⟨328545, by rfl⟩ : syracuseStep 3504485 = 657091) (by norm_num)
theorem B2336323 : Blo 2075435 2336323 := bstep (se 1 (by rfl) ⟨1752242, by rfl⟩ : syracuseStep 2336323 = 3504485) B3504485
theorem B3115097 : Blo 2075435 3115097 := bstep (se 2 (by rfl) ⟨1168161, by rfl⟩ : syracuseStep 3115097 = 2336323) B2336323
theorem B2076731 : Blo 2075435 2076731 := bstep (se 1 (by rfl) ⟨1557548, by rfl⟩ : syracuseStep 2076731 = 3115097) B3115097
theorem B4435373 : Blo 2075435 4435373 := bbase (se 3 (by rfl) ⟨831632, by rfl⟩ : syracuseStep 4435373 = 1663265) (by norm_num)
theorem B2956915 : Blo 2075435 2956915 := bstep (se 1 (by rfl) ⟨2217686, by rfl⟩ : syracuseStep 2956915 = 4435373) B4435373
theorem B15770213 : Blo 2075435 15770213 := bstep (se 4 (by rfl) ⟨1478457, by rfl⟩ : syracuseStep 15770213 = 2956915) B2956915
theorem B10513475 : Blo 2075435 10513475 := bstep (se 1 (by rfl) ⟨7885106, by rfl⟩ : syracuseStep 10513475 = 15770213) B15770213
theorem B7008983 : Blo 2075435 7008983 := bstep (se 1 (by rfl) ⟨5256737, by rfl⟩ : syracuseStep 7008983 = 10513475) B10513475
theorem B4672655 : Blo 2075435 4672655 := bstep (se 1 (by rfl) ⟨3504491, by rfl⟩ : syracuseStep 4672655 = 7008983) B7008983
theorem B3115103 : Blo 2075435 3115103 := bstep (se 1 (by rfl) ⟨2336327, by rfl⟩ : syracuseStep 3115103 = 4672655) B4672655
theorem B2076735 : Blo 2075435 2076735 := bstep (se 1 (by rfl) ⟨1557551, by rfl⟩ : syracuseStep 2076735 = 3115103) B3115103
theorem B3115109 : Blo 2075435 3115109 := bbase (se 4 (by rfl) ⟨292041, by rfl⟩ : syracuseStep 3115109 = 584083) (by norm_num)
theorem B2076739 : Blo 2075435 2076739 := bstep (se 1 (by rfl) ⟨1557554, by rfl⟩ : syracuseStep 2076739 = 3115109) B3115109
theorem B3793421 : Blo 2075435 3793421 := bbase (se 3 (by rfl) ⟨711266, by rfl⟩ : syracuseStep 3793421 = 1422533) (by norm_num)
theorem B2528947 : Blo 2075435 2528947 := bstep (se 1 (by rfl) ⟨1896710, by rfl⟩ : syracuseStep 2528947 = 3793421) B3793421
theorem B13487717 : Blo 2075435 13487717 := bstep (se 4 (by rfl) ⟨1264473, by rfl⟩ : syracuseStep 13487717 = 2528947) B2528947
theorem B8991811 : Blo 2075435 8991811 := bstep (se 1 (by rfl) ⟨6743858, by rfl⟩ : syracuseStep 8991811 = 13487717) B13487717
theorem B11989081 : Blo 2075435 11989081 := bstep (se 2 (by rfl) ⟨4495905, by rfl⟩ : syracuseStep 11989081 = 8991811) B8991811
theorem B15985441 : Blo 2075435 15985441 := bstep (se 2 (by rfl) ⟨5994540, by rfl⟩ : syracuseStep 15985441 = 11989081) B11989081
theorem B85255685 : Blo 2075435 85255685 := bstep (se 4 (by rfl) ⟨7992720, by rfl⟩ : syracuseStep 85255685 = 15985441) B15985441
theorem B56837123 : Blo 2075435 56837123 := bstep (se 1 (by rfl) ⟨42627842, by rfl⟩ : syracuseStep 56837123 = 85255685) B85255685
theorem B37891415 : Blo 2075435 37891415 := bstep (se 1 (by rfl) ⟨28418561, by rfl⟩ : syracuseStep 37891415 = 56837123) B56837123
theorem B25260943 : Blo 2075435 25260943 := bstep (se 1 (by rfl) ⟨18945707, by rfl⟩ : syracuseStep 25260943 = 37891415) B37891415
theorem B33681257 : Blo 2075435 33681257 := bstep (se 2 (by rfl) ⟨12630471, by rfl⟩ : syracuseStep 33681257 = 25260943) B25260943
theorem B22454171 : Blo 2075435 22454171 := bstep (se 1 (by rfl) ⟨16840628, by rfl⟩ : syracuseStep 22454171 = 33681257) B33681257
theorem B14969447 : Blo 2075435 14969447 := bstep (se 1 (by rfl) ⟨11227085, by rfl⟩ : syracuseStep 14969447 = 22454171) B22454171
theorem B9979631 : Blo 2075435 9979631 := bstep (se 1 (by rfl) ⟨7484723, by rfl⟩ : syracuseStep 9979631 = 14969447) B14969447
theorem B6653087 : Blo 2075435 6653087 := bstep (se 1 (by rfl) ⟨4989815, by rfl⟩ : syracuseStep 6653087 = 9979631) B9979631
theorem B4435391 : Blo 2075435 4435391 := bstep (se 1 (by rfl) ⟨3326543, by rfl⟩ : syracuseStep 4435391 = 6653087) B6653087
theorem B2956927 : Blo 2075435 2956927 := bstep (se 1 (by rfl) ⟨2217695, by rfl⟩ : syracuseStep 2956927 = 4435391) B4435391
theorem B3942569 : Blo 2075435 3942569 := bstep (se 2 (by rfl) ⟨1478463, by rfl⟩ : syracuseStep 3942569 = 2956927) B2956927
theorem B2628379 : Blo 2075435 2628379 := bstep (se 1 (by rfl) ⟨1971284, by rfl⟩ : syracuseStep 2628379 = 3942569) B3942569
theorem B3504505 : Blo 2075435 3504505 := bstep (se 2 (by rfl) ⟨1314189, by rfl⟩ : syracuseStep 3504505 = 2628379) B2628379
theorem B4672673 : Blo 2075435 4672673 := bstep (se 2 (by rfl) ⟨1752252, by rfl⟩ : syracuseStep 4672673 = 3504505) B3504505
theorem B3115115 : Blo 2075435 3115115 := bstep (se 1 (by rfl) ⟨2336336, by rfl⟩ : syracuseStep 3115115 = 4672673) B4672673
theorem B2076743 : Blo 2075435 2076743 := bstep (se 1 (by rfl) ⟨1557557, by rfl⟩ : syracuseStep 2076743 = 3115115) B3115115
theorem B2336341 : Blo 2075435 2336341 := bbase (se 8 (by rfl) ⟨13689, by rfl⟩ : syracuseStep 2336341 = 27379) (by norm_num)
theorem B3115121 : Blo 2075435 3115121 := bstep (se 2 (by rfl) ⟨1168170, by rfl⟩ : syracuseStep 3115121 = 2336341) B2336341
theorem B2076747 : Blo 2075435 2076747 := bstep (se 1 (by rfl) ⟨1557560, by rfl⟩ : syracuseStep 2076747 = 3115121) B3115121
theorem B2628389 : Blo 2075435 2628389 := bbase (se 4 (by rfl) ⟨246411, by rfl⟩ : syracuseStep 2628389 = 492823) (by norm_num)
theorem B7009037 : Blo 2075435 7009037 := bstep (se 3 (by rfl) ⟨1314194, by rfl⟩ : syracuseStep 7009037 = 2628389) B2628389
theorem B4672691 : Blo 2075435 4672691 := bstep (se 1 (by rfl) ⟨3504518, by rfl⟩ : syracuseStep 4672691 = 7009037) B7009037
theorem B3115127 : Blo 2075435 3115127 := bstep (se 1 (by rfl) ⟨2336345, by rfl⟩ : syracuseStep 3115127 = 4672691) B4672691
theorem B2076751 : Blo 2075435 2076751 := bstep (se 1 (by rfl) ⟨1557563, by rfl⟩ : syracuseStep 2076751 = 3115127) B3115127
theorem B3115133 : Blo 2075435 3115133 := bbase (se 3 (by rfl) ⟨584087, by rfl⟩ : syracuseStep 3115133 = 1168175) (by norm_num)
theorem B2076755 : Blo 2075435 2076755 := bstep (se 1 (by rfl) ⟨1557566, by rfl⟩ : syracuseStep 2076755 = 3115133) B3115133
theorem B4672709 : Blo 2075435 4672709 := bbase (se 4 (by rfl) ⟨438066, by rfl⟩ : syracuseStep 4672709 = 876133) (by norm_num)
theorem B3115139 : Blo 2075435 3115139 := bstep (se 1 (by rfl) ⟨2336354, by rfl⟩ : syracuseStep 3115139 = 4672709) B4672709
theorem B2076759 : Blo 2075435 2076759 := bstep (se 1 (by rfl) ⟨1557569, by rfl⟩ : syracuseStep 2076759 = 3115139) B3115139
theorem B7104709 : Blo 2075435 7104709 := bbase (se 4 (by rfl) ⟨666066, by rfl⟩ : syracuseStep 7104709 = 1332133) (by norm_num)
theorem B9472945 : Blo 2075435 9472945 := bstep (se 2 (by rfl) ⟨3552354, by rfl⟩ : syracuseStep 9472945 = 7104709) B7104709
theorem B12630593 : Blo 2075435 12630593 := bstep (se 2 (by rfl) ⟨4736472, by rfl⟩ : syracuseStep 12630593 = 9472945) B9472945
theorem B8420395 : Blo 2075435 8420395 := bstep (se 1 (by rfl) ⟨6315296, by rfl⟩ : syracuseStep 8420395 = 12630593) B12630593
theorem B11227193 : Blo 2075435 11227193 := bstep (se 2 (by rfl) ⟨4210197, by rfl⟩ : syracuseStep 11227193 = 8420395) B8420395
theorem B7484795 : Blo 2075435 7484795 := bstep (se 1 (by rfl) ⟨5613596, by rfl⟩ : syracuseStep 7484795 = 11227193) B11227193
theorem B4989863 : Blo 2075435 4989863 := bstep (se 1 (by rfl) ⟨3742397, by rfl⟩ : syracuseStep 4989863 = 7484795) B7484795
theorem B13306301 : Blo 2075435 13306301 := bstep (se 3 (by rfl) ⟨2494931, by rfl⟩ : syracuseStep 13306301 = 4989863) B4989863
theorem B8870867 : Blo 2075435 8870867 := bstep (se 1 (by rfl) ⟨6653150, by rfl⟩ : syracuseStep 8870867 = 13306301) B13306301
theorem B5913911 : Blo 2075435 5913911 := bstep (se 1 (by rfl) ⟨4435433, by rfl⟩ : syracuseStep 5913911 = 8870867) B8870867
theorem B3942607 : Blo 2075435 3942607 := bstep (se 1 (by rfl) ⟨2956955, by rfl⟩ : syracuseStep 3942607 = 5913911) B5913911
theorem B5256809 : Blo 2075435 5256809 := bstep (se 2 (by rfl) ⟨1971303, by rfl⟩ : syracuseStep 5256809 = 3942607) B3942607
theorem B3504539 : Blo 2075435 3504539 := bstep (se 1 (by rfl) ⟨2628404, by rfl⟩ : syracuseStep 3504539 = 5256809) B5256809
theorem B2336359 : Blo 2075435 2336359 := bstep (se 1 (by rfl) ⟨1752269, by rfl⟩ : syracuseStep 2336359 = 3504539) B3504539
theorem B3115145 : Blo 2075435 3115145 := bstep (se 2 (by rfl) ⟨1168179, by rfl⟩ : syracuseStep 3115145 = 2336359) B2336359
theorem B2076763 : Blo 2075435 2076763 := bstep (se 1 (by rfl) ⟨1557572, by rfl⟩ : syracuseStep 2076763 = 3115145) B3115145
theorem B10513637 : Blo 2075435 10513637 := bbase (se 4 (by rfl) ⟨985653, by rfl⟩ : syracuseStep 10513637 = 1971307) (by norm_num)
theorem B7009091 : Blo 2075435 7009091 := bstep (se 1 (by rfl) ⟨5256818, by rfl⟩ : syracuseStep 7009091 = 10513637) B10513637
theorem B4672727 : Blo 2075435 4672727 := bstep (se 1 (by rfl) ⟨3504545, by rfl⟩ : syracuseStep 4672727 = 7009091) B7009091
theorem B3115151 : Blo 2075435 3115151 := bstep (se 1 (by rfl) ⟨2336363, by rfl⟩ : syracuseStep 3115151 = 4672727) B4672727
theorem B2076767 : Blo 2075435 2076767 := bstep (se 1 (by rfl) ⟨1557575, by rfl⟩ : syracuseStep 2076767 = 3115151) B3115151
theorem B3115157 : Blo 2075435 3115157 := bbase (se 6 (by rfl) ⟨73011, by rfl⟩ : syracuseStep 3115157 = 146023) (by norm_num)
theorem B2076771 : Blo 2075435 2076771 := bstep (se 1 (by rfl) ⟨1557578, by rfl⟩ : syracuseStep 2076771 = 3115157) B3115157
theorem B8870917 : Blo 2075435 8870917 := bbase (se 4 (by rfl) ⟨831648, by rfl⟩ : syracuseStep 8870917 = 1663297) (by norm_num)
theorem B11827889 : Blo 2075435 11827889 := bstep (se 2 (by rfl) ⟨4435458, by rfl⟩ : syracuseStep 11827889 = 8870917) B8870917
theorem B7885259 : Blo 2075435 7885259 := bstep (se 1 (by rfl) ⟨5913944, by rfl⟩ : syracuseStep 7885259 = 11827889) B11827889
theorem B5256839 : Blo 2075435 5256839 := bstep (se 1 (by rfl) ⟨3942629, by rfl⟩ : syracuseStep 5256839 = 7885259) B7885259
theorem B3504559 : Blo 2075435 3504559 := bstep (se 1 (by rfl) ⟨2628419, by rfl⟩ : syracuseStep 3504559 = 5256839) B5256839
theorem B4672745 : Blo 2075435 4672745 := bstep (se 2 (by rfl) ⟨1752279, by rfl⟩ : syracuseStep 4672745 = 3504559) B3504559
theorem B3115163 : Blo 2075435 3115163 := bstep (se 1 (by rfl) ⟨2336372, by rfl⟩ : syracuseStep 3115163 = 4672745) B4672745
theorem B2076775 : Blo 2075435 2076775 := bstep (se 1 (by rfl) ⟨1557581, by rfl⟩ : syracuseStep 2076775 = 3115163) B3115163
theorem B2336377 : Blo 2075435 2336377 := bbase (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) (by norm_num)
theorem B3115169 : Blo 2075435 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B2076779 : Blo 2075435 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B4210237 : Blo 2075435 4210237 := bbase (se 3 (by rfl) ⟨789419, by rfl⟩ : syracuseStep 4210237 = 1578839) (by norm_num)
theorem B22454597 : Blo 2075435 22454597 := bstep (se 4 (by rfl) ⟨2105118, by rfl⟩ : syracuseStep 22454597 = 4210237) B4210237
theorem B14969731 : Blo 2075435 14969731 := bstep (se 1 (by rfl) ⟨11227298, by rfl⟩ : syracuseStep 14969731 = 22454597) B22454597
theorem B19959641 : Blo 2075435 19959641 := bstep (se 2 (by rfl) ⟨7484865, by rfl⟩ : syracuseStep 19959641 = 14969731) B14969731
theorem B13306427 : Blo 2075435 13306427 := bstep (se 1 (by rfl) ⟨9979820, by rfl⟩ : syracuseStep 13306427 = 19959641) B19959641
theorem B8870951 : Blo 2075435 8870951 := bstep (se 1 (by rfl) ⟨6653213, by rfl⟩ : syracuseStep 8870951 = 13306427) B13306427
theorem B5913967 : Blo 2075435 5913967 := bstep (se 1 (by rfl) ⟨4435475, by rfl⟩ : syracuseStep 5913967 = 8870951) B8870951
theorem B7885289 : Blo 2075435 7885289 := bstep (se 2 (by rfl) ⟨2956983, by rfl⟩ : syracuseStep 7885289 = 5913967) B5913967
theorem B5256859 : Blo 2075435 5256859 := bstep (se 1 (by rfl) ⟨3942644, by rfl⟩ : syracuseStep 5256859 = 7885289) B7885289
theorem B7009145 : Blo 2075435 7009145 := bstep (se 2 (by rfl) ⟨2628429, by rfl⟩ : syracuseStep 7009145 = 5256859) B5256859
theorem B4672763 : Blo 2075435 4672763 := bstep (se 1 (by rfl) ⟨3504572, by rfl⟩ : syracuseStep 4672763 = 7009145) B7009145
theorem B3115175 : Blo 2075435 3115175 := bstep (se 1 (by rfl) ⟨2336381, by rfl⟩ : syracuseStep 3115175 = 4672763) B4672763
theorem B2076783 : Blo 2075435 2076783 := bstep (se 1 (by rfl) ⟨1557587, by rfl⟩ : syracuseStep 2076783 = 3115175) B3115175
theorem B3115181 : Blo 2075435 3115181 := bbase (se 3 (by rfl) ⟨584096, by rfl⟩ : syracuseStep 3115181 = 1168193) (by norm_num)
theorem B2076787 : Blo 2075435 2076787 := bstep (se 1 (by rfl) ⟨1557590, by rfl⟩ : syracuseStep 2076787 = 3115181) B3115181
theorem B4672781 : Blo 2075435 4672781 := bbase (se 3 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 4672781 = 1752293) (by norm_num)
theorem B3115187 : Blo 2075435 3115187 := bstep (se 1 (by rfl) ⟨2336390, by rfl⟩ : syracuseStep 3115187 = 4672781) B4672781
theorem B2076791 : Blo 2075435 2076791 := bstep (se 1 (by rfl) ⟨1557593, by rfl⟩ : syracuseStep 2076791 = 3115187) B3115187
theorem B2628445 : Blo 2075435 2628445 := bbase (se 3 (by rfl) ⟨492833, by rfl⟩ : syracuseStep 2628445 = 985667) (by norm_num)
theorem B3504593 : Blo 2075435 3504593 := bstep (se 2 (by rfl) ⟨1314222, by rfl⟩ : syracuseStep 3504593 = 2628445) B2628445
theorem B2336395 : Blo 2075435 2336395 := bstep (se 1 (by rfl) ⟨1752296, by rfl⟩ : syracuseStep 2336395 = 3504593) B3504593
theorem B3115193 : Blo 2075435 3115193 := bstep (se 2 (by rfl) ⟨1168197, by rfl⟩ : syracuseStep 3115193 = 2336395) B2336395
theorem B2076795 : Blo 2075435 2076795 := bstep (se 1 (by rfl) ⟨1557596, by rfl⟩ : syracuseStep 2076795 = 3115193) B3115193
theorem B17742037 : Blo 2075435 17742037 := bbase (se 7 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 17742037 = 415829) (by norm_num)
theorem B23656049 : Blo 2075435 23656049 := bstep (se 2 (by rfl) ⟨8871018, by rfl⟩ : syracuseStep 23656049 = 17742037) B17742037
theorem B15770699 : Blo 2075435 15770699 := bstep (se 1 (by rfl) ⟨11828024, by rfl⟩ : syracuseStep 15770699 = 23656049) B23656049
theorem B10513799 : Blo 2075435 10513799 := bstep (se 1 (by rfl) ⟨7885349, by rfl⟩ : syracuseStep 10513799 = 15770699) B15770699
theorem B7009199 : Blo 2075435 7009199 := bstep (se 1 (by rfl) ⟨5256899, by rfl⟩ : syracuseStep 7009199 = 10513799) B10513799
theorem B4672799 : Blo 2075435 4672799 := bstep (se 1 (by rfl) ⟨3504599, by rfl⟩ : syracuseStep 4672799 = 7009199) B7009199
theorem B3115199 : Blo 2075435 3115199 := bstep (se 1 (by rfl) ⟨2336399, by rfl⟩ : syracuseStep 3115199 = 4672799) B4672799
theorem B2076799 : Blo 2075435 2076799 := bstep (se 1 (by rfl) ⟨1557599, by rfl⟩ : syracuseStep 2076799 = 3115199) B3115199
theorem B3115205 : Blo 2075435 3115205 := bbase (se 4 (by rfl) ⟨292050, by rfl⟩ : syracuseStep 3115205 = 584101) (by norm_num)
theorem B2076803 : Blo 2075435 2076803 := bstep (se 1 (by rfl) ⟨1557602, by rfl⟩ : syracuseStep 2076803 = 3115205) B3115205
theorem B3504613 : Blo 2075435 3504613 := bbase (se 4 (by rfl) ⟨328557, by rfl⟩ : syracuseStep 3504613 = 657115) (by norm_num)
theorem B4672817 : Blo 2075435 4672817 := bstep (se 2 (by rfl) ⟨1752306, by rfl⟩ : syracuseStep 4672817 = 3504613) B3504613
theorem B3115211 : Blo 2075435 3115211 := bstep (se 1 (by rfl) ⟨2336408, by rfl⟩ : syracuseStep 3115211 = 4672817) B4672817
theorem B2076807 : Blo 2075435 2076807 := bstep (se 1 (by rfl) ⟨1557605, by rfl⟩ : syracuseStep 2076807 = 3115211) B3115211
theorem B2336413 : Blo 2075435 2336413 := bbase (se 3 (by rfl) ⟨438077, by rfl⟩ : syracuseStep 2336413 = 876155) (by norm_num)
theorem B3115217 : Blo 2075435 3115217 := bstep (se 2 (by rfl) ⟨1168206, by rfl⟩ : syracuseStep 3115217 = 2336413) B2336413
theorem B2076811 : Blo 2075435 2076811 := bstep (se 1 (by rfl) ⟨1557608, by rfl⟩ : syracuseStep 2076811 = 3115217) B3115217
theorem B7009253 : Blo 2075435 7009253 := bbase (se 4 (by rfl) ⟨657117, by rfl⟩ : syracuseStep 7009253 = 1314235) (by norm_num)
theorem B4672835 : Blo 2075435 4672835 := bstep (se 1 (by rfl) ⟨3504626, by rfl⟩ : syracuseStep 4672835 = 7009253) B7009253
theorem B3115223 : Blo 2075435 3115223 := bstep (se 1 (by rfl) ⟨2336417, by rfl⟩ : syracuseStep 3115223 = 4672835) B4672835
theorem B2076815 : Blo 2075435 2076815 := bstep (se 1 (by rfl) ⟨1557611, by rfl⟩ : syracuseStep 2076815 = 3115223) B3115223
theorem B3115229 : Blo 2075435 3115229 := bbase (se 3 (by rfl) ⟨584105, by rfl⟩ : syracuseStep 3115229 = 1168211) (by norm_num)
theorem B2076819 : Blo 2075435 2076819 := bstep (se 1 (by rfl) ⟨1557614, by rfl⟩ : syracuseStep 2076819 = 3115229) B3115229
theorem B4672853 : Blo 2075435 4672853 := bbase (se 11 (by rfl) ⟨3422, by rfl⟩ : syracuseStep 4672853 = 6845) (by norm_num)
theorem B3115235 : Blo 2075435 3115235 := bstep (se 1 (by rfl) ⟨2336426, by rfl⟩ : syracuseStep 3115235 = 4672853) B4672853
theorem B2076823 : Blo 2075435 2076823 := bstep (se 1 (by rfl) ⟨1557617, by rfl⟩ : syracuseStep 2076823 = 3115235) B3115235
theorem B2217785 : Blo 2075435 2217785 := bbase (se 2 (by rfl) ⟨831669, by rfl⟩ : syracuseStep 2217785 = 1663339) (by norm_num)
theorem B5914093 : Blo 2075435 5914093 := bstep (se 3 (by rfl) ⟨1108892, by rfl⟩ : syracuseStep 5914093 = 2217785) B2217785
theorem B7885457 : Blo 2075435 7885457 := bstep (se 2 (by rfl) ⟨2957046, by rfl⟩ : syracuseStep 7885457 = 5914093) B5914093
theorem B5256971 : Blo 2075435 5256971 := bstep (se 1 (by rfl) ⟨3942728, by rfl⟩ : syracuseStep 5256971 = 7885457) B7885457
theorem B3504647 : Blo 2075435 3504647 := bstep (se 1 (by rfl) ⟨2628485, by rfl⟩ : syracuseStep 3504647 = 5256971) B5256971
theorem B2336431 : Blo 2075435 2336431 := bstep (se 1 (by rfl) ⟨1752323, by rfl⟩ : syracuseStep 2336431 = 3504647) B3504647
theorem B3115241 : Blo 2075435 3115241 := bstep (se 2 (by rfl) ⟨1168215, by rfl⟩ : syracuseStep 3115241 = 2336431) B2336431
theorem B2076827 : Blo 2075435 2076827 := bstep (se 1 (by rfl) ⟨1557620, by rfl⟩ : syracuseStep 2076827 = 3115241) B3115241
theorem B14209877 : Blo 2075435 14209877 := bbase (se 9 (by rfl) ⟨41630, by rfl⟩ : syracuseStep 14209877 = 83261) (by norm_num)
theorem B37893005 : Blo 2075435 37893005 := bstep (se 3 (by rfl) ⟨7104938, by rfl⟩ : syracuseStep 37893005 = 14209877) B14209877
theorem B25262003 : Blo 2075435 25262003 := bstep (se 1 (by rfl) ⟨18946502, by rfl⟩ : syracuseStep 25262003 = 37893005) B37893005
theorem B67365341 : Blo 2075435 67365341 := bstep (se 3 (by rfl) ⟨12631001, by rfl⟩ : syracuseStep 67365341 = 25262003) B25262003
theorem B44910227 : Blo 2075435 44910227 := bstep (se 1 (by rfl) ⟨33682670, by rfl⟩ : syracuseStep 44910227 = 67365341) B67365341
theorem B29940151 : Blo 2075435 29940151 := bstep (se 1 (by rfl) ⟨22455113, by rfl⟩ : syracuseStep 29940151 = 44910227) B44910227
theorem B39920201 : Blo 2075435 39920201 := bstep (se 2 (by rfl) ⟨14970075, by rfl⟩ : syracuseStep 39920201 = 29940151) B29940151
theorem B26613467 : Blo 2075435 26613467 := bstep (se 1 (by rfl) ⟨19960100, by rfl⟩ : syracuseStep 26613467 = 39920201) B39920201
theorem B17742311 : Blo 2075435 17742311 := bstep (se 1 (by rfl) ⟨13306733, by rfl⟩ : syracuseStep 17742311 = 26613467) B26613467
theorem B11828207 : Blo 2075435 11828207 := bstep (se 1 (by rfl) ⟨8871155, by rfl⟩ : syracuseStep 11828207 = 17742311) B17742311
theorem B7885471 : Blo 2075435 7885471 := bstep (se 1 (by rfl) ⟨5914103, by rfl⟩ : syracuseStep 7885471 = 11828207) B11828207
theorem B10513961 : Blo 2075435 10513961 := bstep (se 2 (by rfl) ⟨3942735, by rfl⟩ : syracuseStep 10513961 = 7885471) B7885471
theorem B7009307 : Blo 2075435 7009307 := bstep (se 1 (by rfl) ⟨5256980, by rfl⟩ : syracuseStep 7009307 = 10513961) B10513961
theorem B4672871 : Blo 2075435 4672871 := bstep (se 1 (by rfl) ⟨3504653, by rfl⟩ : syracuseStep 4672871 = 7009307) B7009307
theorem B3115247 : Blo 2075435 3115247 := bstep (se 1 (by rfl) ⟨2336435, by rfl⟩ : syracuseStep 3115247 = 4672871) B4672871
theorem B2076831 : Blo 2075435 2076831 := bstep (se 1 (by rfl) ⟨1557623, by rfl⟩ : syracuseStep 2076831 = 3115247) B3115247
theorem B3115253 : Blo 2075435 3115253 := bbase (se 5 (by rfl) ⟨146027, by rfl⟩ : syracuseStep 3115253 = 292055) (by norm_num)
theorem B2076835 : Blo 2075435 2076835 := bstep (se 1 (by rfl) ⟨1557626, by rfl⟩ : syracuseStep 2076835 = 3115253) B3115253
theorem B19960181 : Blo 2075435 19960181 := bbase (se 5 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 19960181 = 1871267) (by norm_num)
theorem B13306787 : Blo 2075435 13306787 := bstep (se 1 (by rfl) ⟨9980090, by rfl⟩ : syracuseStep 13306787 = 19960181) B19960181
theorem B8871191 : Blo 2075435 8871191 := bstep (se 1 (by rfl) ⟨6653393, by rfl⟩ : syracuseStep 8871191 = 13306787) B13306787
theorem B5914127 : Blo 2075435 5914127 := bstep (se 1 (by rfl) ⟨4435595, by rfl⟩ : syracuseStep 5914127 = 8871191) B8871191
theorem B3942751 : Blo 2075435 3942751 := bstep (se 1 (by rfl) ⟨2957063, by rfl⟩ : syracuseStep 3942751 = 5914127) B5914127
theorem B5257001 : Blo 2075435 5257001 := bstep (se 2 (by rfl) ⟨1971375, by rfl⟩ : syracuseStep 5257001 = 3942751) B3942751
theorem B3504667 : Blo 2075435 3504667 := bstep (se 1 (by rfl) ⟨2628500, by rfl⟩ : syracuseStep 3504667 = 5257001) B5257001
theorem B4672889 : Blo 2075435 4672889 := bstep (se 2 (by rfl) ⟨1752333, by rfl⟩ : syracuseStep 4672889 = 3504667) B3504667
theorem B3115259 : Blo 2075435 3115259 := bstep (se 1 (by rfl) ⟨2336444, by rfl⟩ : syracuseStep 3115259 = 4672889) B4672889
theorem B2076839 : Blo 2075435 2076839 := bstep (se 1 (by rfl) ⟨1557629, by rfl⟩ : syracuseStep 2076839 = 3115259) B3115259
theorem B2336449 : Blo 2075435 2336449 := bbase (se 2 (by rfl) ⟨876168, by rfl⟩ : syracuseStep 2336449 = 1752337) (by norm_num)
theorem B3115265 : Blo 2075435 3115265 := bstep (se 2 (by rfl) ⟨1168224, by rfl⟩ : syracuseStep 3115265 = 2336449) B2336449
theorem B2076843 : Blo 2075435 2076843 := bstep (se 1 (by rfl) ⟨1557632, by rfl⟩ : syracuseStep 2076843 = 3115265) B3115265
theorem B5257021 : Blo 2075435 5257021 := bbase (se 3 (by rfl) ⟨985691, by rfl⟩ : syracuseStep 5257021 = 1971383) (by norm_num)
theorem B7009361 : Blo 2075435 7009361 := bstep (se 2 (by rfl) ⟨2628510, by rfl⟩ : syracuseStep 7009361 = 5257021) B5257021
theorem B4672907 : Blo 2075435 4672907 := bstep (se 1 (by rfl) ⟨3504680, by rfl⟩ : syracuseStep 4672907 = 7009361) B7009361
theorem B3115271 : Blo 2075435 3115271 := bstep (se 1 (by rfl) ⟨2336453, by rfl⟩ : syracuseStep 3115271 = 4672907) B4672907
theorem B2076847 : Blo 2075435 2076847 := bstep (se 1 (by rfl) ⟨1557635, by rfl⟩ : syracuseStep 2076847 = 3115271) B3115271
theorem B3115277 : Blo 2075435 3115277 := bbase (se 3 (by rfl) ⟨584114, by rfl⟩ : syracuseStep 3115277 = 1168229) (by norm_num)
theorem B2076851 : Blo 2075435 2076851 := bstep (se 1 (by rfl) ⟨1557638, by rfl⟩ : syracuseStep 2076851 = 3115277) B3115277
theorem B4672925 : Blo 2075435 4672925 := bbase (se 3 (by rfl) ⟨876173, by rfl⟩ : syracuseStep 4672925 = 1752347) (by norm_num)
theorem B3115283 : Blo 2075435 3115283 := bstep (se 1 (by rfl) ⟨2336462, by rfl⟩ : syracuseStep 3115283 = 4672925) B4672925
theorem B2076855 : Blo 2075435 2076855 := bstep (se 1 (by rfl) ⟨1557641, by rfl⟩ : syracuseStep 2076855 = 3115283) B3115283
theorem B3504701 : Blo 2075435 3504701 := bbase (se 3 (by rfl) ⟨657131, by rfl⟩ : syracuseStep 3504701 = 1314263) (by norm_num)
theorem B2336467 : Blo 2075435 2336467 := bstep (se 1 (by rfl) ⟨1752350, by rfl⟩ : syracuseStep 2336467 = 3504701) B3504701
theorem B3115289 : Blo 2075435 3115289 := bstep (se 2 (by rfl) ⟨1168233, by rfl⟩ : syracuseStep 3115289 = 2336467) B2336467
theorem B2076859 : Blo 2075435 2076859 := bstep (se 1 (by rfl) ⟨1557644, by rfl⟩ : syracuseStep 2076859 = 3115289) B3115289
theorem B11227733 : Blo 2075435 11227733 := bbase (se 8 (by rfl) ⟨65787, by rfl⟩ : syracuseStep 11227733 = 131575) (by norm_num)
theorem B7485155 : Blo 2075435 7485155 := bstep (se 1 (by rfl) ⟨5613866, by rfl⟩ : syracuseStep 7485155 = 11227733) B11227733
theorem B4990103 : Blo 2075435 4990103 := bstep (se 1 (by rfl) ⟨3742577, by rfl⟩ : syracuseStep 4990103 = 7485155) B7485155
theorem B3326735 : Blo 2075435 3326735 := bstep (se 1 (by rfl) ⟨2495051, by rfl⟩ : syracuseStep 3326735 = 4990103) B4990103
theorem B2217823 : Blo 2075435 2217823 := bstep (se 1 (by rfl) ⟨1663367, by rfl⟩ : syracuseStep 2217823 = 3326735) B3326735
theorem B11828389 : Blo 2075435 11828389 := bstep (se 4 (by rfl) ⟨1108911, by rfl⟩ : syracuseStep 11828389 = 2217823) B2217823
theorem B15771185 : Blo 2075435 15771185 := bstep (se 2 (by rfl) ⟨5914194, by rfl⟩ : syracuseStep 15771185 = 11828389) B11828389
theorem B10514123 : Blo 2075435 10514123 := bstep (se 1 (by rfl) ⟨7885592, by rfl⟩ : syracuseStep 10514123 = 15771185) B15771185
theorem B7009415 : Blo 2075435 7009415 := bstep (se 1 (by rfl) ⟨5257061, by rfl⟩ : syracuseStep 7009415 = 10514123) B10514123
theorem B4672943 : Blo 2075435 4672943 := bstep (se 1 (by rfl) ⟨3504707, by rfl⟩ : syracuseStep 4672943 = 7009415) B7009415
theorem B3115295 : Blo 2075435 3115295 := bstep (se 1 (by rfl) ⟨2336471, by rfl⟩ : syracuseStep 3115295 = 4672943) B4672943
theorem B2076863 : Blo 2075435 2076863 := bstep (se 1 (by rfl) ⟨1557647, by rfl⟩ : syracuseStep 2076863 = 3115295) B3115295
theorem B3115301 : Blo 2075435 3115301 := bbase (se 4 (by rfl) ⟨292059, by rfl⟩ : syracuseStep 3115301 = 584119) (by norm_num)
theorem B2076867 : Blo 2075435 2076867 := bstep (se 1 (by rfl) ⟨1557650, by rfl⟩ : syracuseStep 2076867 = 3115301) B3115301
theorem B2628541 : Blo 2075435 2628541 := bbase (se 3 (by rfl) ⟨492851, by rfl⟩ : syracuseStep 2628541 = 985703) (by norm_num)
theorem B3504721 : Blo 2075435 3504721 := bstep (se 2 (by rfl) ⟨1314270, by rfl⟩ : syracuseStep 3504721 = 2628541) B2628541
theorem B4672961 : Blo 2075435 4672961 := bstep (se 2 (by rfl) ⟨1752360, by rfl⟩ : syracuseStep 4672961 = 3504721) B3504721
theorem B3115307 : Blo 2075435 3115307 := bstep (se 1 (by rfl) ⟨2336480, by rfl⟩ : syracuseStep 3115307 = 4672961) B4672961
theorem B2076871 : Blo 2075435 2076871 := bstep (se 1 (by rfl) ⟨1557653, by rfl⟩ : syracuseStep 2076871 = 3115307) B3115307
theorem B2336485 : Blo 2075435 2336485 := bbase (se 4 (by rfl) ⟨219045, by rfl⟩ : syracuseStep 2336485 = 438091) (by norm_num)
theorem B3115313 : Blo 2075435 3115313 := bstep (se 2 (by rfl) ⟨1168242, by rfl⟩ : syracuseStep 3115313 = 2336485) B2336485
theorem B2076875 : Blo 2075435 2076875 := bstep (se 1 (by rfl) ⟨1557656, by rfl⟩ : syracuseStep 2076875 = 3115313) B3115313
theorem B2368369 : Blo 2075435 2368369 := bbase (se 2 (by rfl) ⟨888138, by rfl⟩ : syracuseStep 2368369 = 1776277) (by norm_num)
theorem B12631301 : Blo 2075435 12631301 := bstep (se 4 (by rfl) ⟨1184184, by rfl⟩ : syracuseStep 12631301 = 2368369) B2368369
theorem B8420867 : Blo 2075435 8420867 := bstep (se 1 (by rfl) ⟨6315650, by rfl⟩ : syracuseStep 8420867 = 12631301) B12631301
theorem B5613911 : Blo 2075435 5613911 := bstep (se 1 (by rfl) ⟨4210433, by rfl⟩ : syracuseStep 5613911 = 8420867) B8420867
theorem B3742607 : Blo 2075435 3742607 := bstep (se 1 (by rfl) ⟨2806955, by rfl⟩ : syracuseStep 3742607 = 5613911) B5613911
theorem B2495071 : Blo 2075435 2495071 := bstep (se 1 (by rfl) ⟨1871303, by rfl⟩ : syracuseStep 2495071 = 3742607) B3742607
theorem B3326761 : Blo 2075435 3326761 := bstep (se 2 (by rfl) ⟨1247535, by rfl⟩ : syracuseStep 3326761 = 2495071) B2495071
theorem B4435681 : Blo 2075435 4435681 := bstep (se 2 (by rfl) ⟨1663380, by rfl⟩ : syracuseStep 4435681 = 3326761) B3326761
theorem B5914241 : Blo 2075435 5914241 := bstep (se 2 (by rfl) ⟨2217840, by rfl⟩ : syracuseStep 5914241 = 4435681) B4435681
theorem B3942827 : Blo 2075435 3942827 := bstep (se 1 (by rfl) ⟨2957120, by rfl⟩ : syracuseStep 3942827 = 5914241) B5914241
theorem B2628551 : Blo 2075435 2628551 := bstep (se 1 (by rfl) ⟨1971413, by rfl⟩ : syracuseStep 2628551 = 3942827) B3942827
theorem B7009469 : Blo 2075435 7009469 := bstep (se 3 (by rfl) ⟨1314275, by rfl⟩ : syracuseStep 7009469 = 2628551) B2628551
theorem B4672979 : Blo 2075435 4672979 := bstep (se 1 (by rfl) ⟨3504734, by rfl⟩ : syracuseStep 4672979 = 7009469) B7009469
theorem B3115319 : Blo 2075435 3115319 := bstep (se 1 (by rfl) ⟨2336489, by rfl⟩ : syracuseStep 3115319 = 4672979) B4672979
theorem B2076879 : Blo 2075435 2076879 := bstep (se 1 (by rfl) ⟨1557659, by rfl⟩ : syracuseStep 2076879 = 3115319) B3115319
theorem B3115325 : Blo 2075435 3115325 := bbase (se 3 (by rfl) ⟨584123, by rfl⟩ : syracuseStep 3115325 = 1168247) (by norm_num)
theorem B2076883 : Blo 2075435 2076883 := bstep (se 1 (by rfl) ⟨1557662, by rfl⟩ : syracuseStep 2076883 = 3115325) B3115325
theorem B4672997 : Blo 2075435 4672997 := bbase (se 4 (by rfl) ⟨438093, by rfl⟩ : syracuseStep 4672997 = 876187) (by norm_num)
theorem B3115331 : Blo 2075435 3115331 := bstep (se 1 (by rfl) ⟨2336498, by rfl⟩ : syracuseStep 3115331 = 4672997) B4672997
theorem B2076887 : Blo 2075435 2076887 := bstep (se 1 (by rfl) ⟨1557665, by rfl⟩ : syracuseStep 2076887 = 3115331) B3115331
theorem B5257133 : Blo 2075435 5257133 := bbase (se 3 (by rfl) ⟨985712, by rfl⟩ : syracuseStep 5257133 = 1971425) (by norm_num)
theorem B3504755 : Blo 2075435 3504755 := bstep (se 1 (by rfl) ⟨2628566, by rfl⟩ : syracuseStep 3504755 = 5257133) B5257133
theorem B2336503 : Blo 2075435 2336503 := bstep (se 1 (by rfl) ⟨1752377, by rfl⟩ : syracuseStep 2336503 = 3504755) B3504755
theorem B3115337 : Blo 2075435 3115337 := bstep (se 2 (by rfl) ⟨1168251, by rfl⟩ : syracuseStep 3115337 = 2336503) B2336503
theorem B2076891 : Blo 2075435 2076891 := bstep (se 1 (by rfl) ⟨1557668, by rfl⟩ : syracuseStep 2076891 = 3115337) B3115337
theorem B6653573 : Blo 2075435 6653573 := bbase (se 4 (by rfl) ⟨623772, by rfl⟩ : syracuseStep 6653573 = 1247545) (by norm_num)
theorem B4435715 : Blo 2075435 4435715 := bstep (se 1 (by rfl) ⟨3326786, by rfl⟩ : syracuseStep 4435715 = 6653573) B6653573
theorem B2957143 : Blo 2075435 2957143 := bstep (se 1 (by rfl) ⟨2217857, by rfl⟩ : syracuseStep 2957143 = 4435715) B4435715
theorem B3942857 : Blo 2075435 3942857 := bstep (se 2 (by rfl) ⟨1478571, by rfl⟩ : syracuseStep 3942857 = 2957143) B2957143
theorem B10514285 : Blo 2075435 10514285 := bstep (se 3 (by rfl) ⟨1971428, by rfl⟩ : syracuseStep 10514285 = 3942857) B3942857
theorem B7009523 : Blo 2075435 7009523 := bstep (se 1 (by rfl) ⟨5257142, by rfl⟩ : syracuseStep 7009523 = 10514285) B10514285
theorem B4673015 : Blo 2075435 4673015 := bstep (se 1 (by rfl) ⟨3504761, by rfl⟩ : syracuseStep 4673015 = 7009523) B7009523
theorem B3115343 : Blo 2075435 3115343 := bstep (se 1 (by rfl) ⟨2336507, by rfl⟩ : syracuseStep 3115343 = 4673015) B4673015
theorem B2076895 : Blo 2075435 2076895 := bstep (se 1 (by rfl) ⟨1557671, by rfl⟩ : syracuseStep 2076895 = 3115343) B3115343
theorem B3115349 : Blo 2075435 3115349 := bbase (se 10 (by rfl) ⟨4563, by rfl⟩ : syracuseStep 3115349 = 9127) (by norm_num)
theorem B2076899 : Blo 2075435 2076899 := bstep (se 1 (by rfl) ⟨1557674, by rfl⟩ : syracuseStep 2076899 = 3115349) B3115349
theorem B5914309 : Blo 2075435 5914309 := bbase (se 4 (by rfl) ⟨554466, by rfl⟩ : syracuseStep 5914309 = 1108933) (by norm_num)
theorem B7885745 : Blo 2075435 7885745 := bstep (se 2 (by rfl) ⟨2957154, by rfl⟩ : syracuseStep 7885745 = 5914309) B5914309
theorem B5257163 : Blo 2075435 5257163 := bstep (se 1 (by rfl) ⟨3942872, by rfl⟩ : syracuseStep 5257163 = 7885745) B7885745
theorem B3504775 : Blo 2075435 3504775 := bstep (se 1 (by rfl) ⟨2628581, by rfl⟩ : syracuseStep 3504775 = 5257163) B5257163
theorem B4673033 : Blo 2075435 4673033 := bstep (se 2 (by rfl) ⟨1752387, by rfl⟩ : syracuseStep 4673033 = 3504775) B3504775
theorem B3115355 : Blo 2075435 3115355 := bstep (se 1 (by rfl) ⟨2336516, by rfl⟩ : syracuseStep 3115355 = 4673033) B4673033
theorem B2076903 : Blo 2075435 2076903 := bstep (se 1 (by rfl) ⟨1557677, by rfl⟩ : syracuseStep 2076903 = 3115355) B3115355
theorem B2336521 : Blo 2075435 2336521 := bbase (se 2 (by rfl) ⟨876195, by rfl⟩ : syracuseStep 2336521 = 1752391) (by norm_num)
theorem B3115361 : Blo 2075435 3115361 := bstep (se 2 (by rfl) ⟨1168260, by rfl⟩ : syracuseStep 3115361 = 2336521) B2336521
theorem B2076907 : Blo 2075435 2076907 := bstep (se 1 (by rfl) ⟨1557680, by rfl⟩ : syracuseStep 2076907 = 3115361) B3115361
theorem B17985077 : Blo 2075435 17985077 := bbase (se 5 (by rfl) ⟨843050, by rfl⟩ : syracuseStep 17985077 = 1686101) (by norm_num)
theorem B11990051 : Blo 2075435 11990051 := bstep (se 1 (by rfl) ⟨8992538, by rfl⟩ : syracuseStep 11990051 = 17985077) B17985077
theorem B7993367 : Blo 2075435 7993367 := bstep (se 1 (by rfl) ⟨5995025, by rfl⟩ : syracuseStep 7993367 = 11990051) B11990051
theorem B5328911 : Blo 2075435 5328911 := bstep (se 1 (by rfl) ⟨3996683, by rfl⟩ : syracuseStep 5328911 = 7993367) B7993367
theorem B3552607 : Blo 2075435 3552607 := bstep (se 1 (by rfl) ⟨2664455, by rfl⟩ : syracuseStep 3552607 = 5328911) B5328911
theorem B4736809 : Blo 2075435 4736809 := bstep (se 2 (by rfl) ⟨1776303, by rfl⟩ : syracuseStep 4736809 = 3552607) B3552607
theorem B6315745 : Blo 2075435 6315745 := bstep (se 2 (by rfl) ⟨2368404, by rfl⟩ : syracuseStep 6315745 = 4736809) B4736809
theorem B8420993 : Blo 2075435 8420993 := bstep (se 2 (by rfl) ⟨3157872, by rfl⟩ : syracuseStep 8420993 = 6315745) B6315745
theorem B5613995 : Blo 2075435 5613995 := bstep (se 1 (by rfl) ⟨4210496, by rfl⟩ : syracuseStep 5613995 = 8420993) B8420993
theorem B14970653 : Blo 2075435 14970653 := bstep (se 3 (by rfl) ⟨2806997, by rfl⟩ : syracuseStep 14970653 = 5613995) B5613995
theorem B9980435 : Blo 2075435 9980435 := bstep (se 1 (by rfl) ⟨7485326, by rfl⟩ : syracuseStep 9980435 = 14970653) B14970653
theorem B26614493 : Blo 2075435 26614493 := bstep (se 3 (by rfl) ⟨4990217, by rfl⟩ : syracuseStep 26614493 = 9980435) B9980435
theorem B17742995 : Blo 2075435 17742995 := bstep (se 1 (by rfl) ⟨13307246, by rfl⟩ : syracuseStep 17742995 = 26614493) B26614493
theorem B11828663 : Blo 2075435 11828663 := bstep (se 1 (by rfl) ⟨8871497, by rfl⟩ : syracuseStep 11828663 = 17742995) B17742995
theorem B7885775 : Blo 2075435 7885775 := bstep (se 1 (by rfl) ⟨5914331, by rfl⟩ : syracuseStep 7885775 = 11828663) B11828663
theorem B5257183 : Blo 2075435 5257183 := bstep (se 1 (by rfl) ⟨3942887, by rfl⟩ : syracuseStep 5257183 = 7885775) B7885775
theorem B7009577 : Blo 2075435 7009577 := bstep (se 2 (by rfl) ⟨2628591, by rfl⟩ : syracuseStep 7009577 = 5257183) B5257183
theorem B4673051 : Blo 2075435 4673051 := bstep (se 1 (by rfl) ⟨3504788, by rfl⟩ : syracuseStep 4673051 = 7009577) B7009577
theorem B3115367 : Blo 2075435 3115367 := bstep (se 1 (by rfl) ⟨2336525, by rfl⟩ : syracuseStep 3115367 = 4673051) B4673051
theorem B2076911 : Blo 2075435 2076911 := bstep (se 1 (by rfl) ⟨1557683, by rfl⟩ : syracuseStep 2076911 = 3115367) B3115367
theorem B3115373 : Blo 2075435 3115373 := bbase (se 3 (by rfl) ⟨584132, by rfl⟩ : syracuseStep 3115373 = 1168265) (by norm_num)
theorem B2076915 : Blo 2075435 2076915 := bstep (se 1 (by rfl) ⟨1557686, by rfl⟩ : syracuseStep 2076915 = 3115373) B3115373
theorem B4673069 : Blo 2075435 4673069 := bbase (se 3 (by rfl) ⟨876200, by rfl⟩ : syracuseStep 4673069 = 1752401) (by norm_num)
theorem B3115379 : Blo 2075435 3115379 := bstep (se 1 (by rfl) ⟨2336534, by rfl⟩ : syracuseStep 3115379 = 4673069) B4673069
theorem B2076919 : Blo 2075435 2076919 := bstep (se 1 (by rfl) ⟨1557689, by rfl⟩ : syracuseStep 2076919 = 3115379) B3115379
theorem B3372221 : Blo 2075435 3372221 := bbase (se 3 (by rfl) ⟨632291, by rfl⟩ : syracuseStep 3372221 = 1264583) (by norm_num)
theorem B8992589 : Blo 2075435 8992589 := bstep (se 3 (by rfl) ⟨1686110, by rfl⟩ : syracuseStep 8992589 = 3372221) B3372221
theorem B95920949 : Blo 2075435 95920949 := bstep (se 5 (by rfl) ⟨4496294, by rfl⟩ : syracuseStep 95920949 = 8992589) B8992589
theorem B255789197 : Blo 2075435 255789197 := bstep (se 3 (by rfl) ⟨47960474, by rfl⟩ : syracuseStep 255789197 = 95920949) B95920949
theorem B170526131 : Blo 2075435 170526131 := bstep (se 1 (by rfl) ⟨127894598, by rfl⟩ : syracuseStep 170526131 = 255789197) B255789197
theorem B113684087 : Blo 2075435 113684087 := bstep (se 1 (by rfl) ⟨85263065, by rfl⟩ : syracuseStep 113684087 = 170526131) B170526131
theorem B75789391 : Blo 2075435 75789391 := bstep (se 1 (by rfl) ⟨56842043, by rfl⟩ : syracuseStep 75789391 = 113684087) B113684087
theorem B101052521 : Blo 2075435 101052521 := bstep (se 2 (by rfl) ⟨37894695, by rfl⟩ : syracuseStep 101052521 = 75789391) B75789391
theorem B67368347 : Blo 2075435 67368347 := bstep (se 1 (by rfl) ⟨50526260, by rfl⟩ : syracuseStep 67368347 = 101052521) B101052521
theorem B44912231 : Blo 2075435 44912231 := bstep (se 1 (by rfl) ⟨33684173, by rfl⟩ : syracuseStep 44912231 = 67368347) B67368347
theorem B29941487 : Blo 2075435 29941487 := bstep (se 1 (by rfl) ⟨22456115, by rfl⟩ : syracuseStep 29941487 = 44912231) B44912231
theorem B19960991 : Blo 2075435 19960991 := bstep (se 1 (by rfl) ⟨14970743, by rfl⟩ : syracuseStep 19960991 = 29941487) B29941487
theorem B13307327 : Blo 2075435 13307327 := bstep (se 1 (by rfl) ⟨9980495, by rfl⟩ : syracuseStep 13307327 = 19960991) B19960991
theorem B8871551 : Blo 2075435 8871551 := bstep (se 1 (by rfl) ⟨6653663, by rfl⟩ : syracuseStep 8871551 = 13307327) B13307327
theorem B5914367 : Blo 2075435 5914367 := bstep (se 1 (by rfl) ⟨4435775, by rfl⟩ : syracuseStep 5914367 = 8871551) B8871551
theorem B3942911 : Blo 2075435 3942911 := bstep (se 1 (by rfl) ⟨2957183, by rfl⟩ : syracuseStep 3942911 = 5914367) B5914367
theorem B2628607 : Blo 2075435 2628607 := bstep (se 1 (by rfl) ⟨1971455, by rfl⟩ : syracuseStep 2628607 = 3942911) B3942911
theorem B3504809 : Blo 2075435 3504809 := bstep (se 2 (by rfl) ⟨1314303, by rfl⟩ : syracuseStep 3504809 = 2628607) B2628607
theorem B2336539 : Blo 2075435 2336539 := bstep (se 1 (by rfl) ⟨1752404, by rfl⟩ : syracuseStep 2336539 = 3504809) B3504809
theorem B3115385 : Blo 2075435 3115385 := bstep (se 2 (by rfl) ⟨1168269, by rfl⟩ : syracuseStep 3115385 = 2336539) B2336539
theorem B2076923 : Blo 2075435 2076923 := bstep (se 1 (by rfl) ⟨1557692, by rfl⟩ : syracuseStep 2076923 = 3115385) B3115385
theorem B3326837 : Blo 2075435 3326837 := bbase (se 5 (by rfl) ⟨155945, by rfl⟩ : syracuseStep 3326837 = 311891) (by norm_num)
theorem B35486261 : Blo 2075435 35486261 := bstep (se 5 (by rfl) ⟨1663418, by rfl⟩ : syracuseStep 35486261 = 3326837) B3326837
theorem B23657507 : Blo 2075435 23657507 := bstep (se 1 (by rfl) ⟨17743130, by rfl⟩ : syracuseStep 23657507 = 35486261) B35486261
theorem B15771671 : Blo 2075435 15771671 := bstep (se 1 (by rfl) ⟨11828753, by rfl⟩ : syracuseStep 15771671 = 23657507) B23657507
theorem B10514447 : Blo 2075435 10514447 := bstep (se 1 (by rfl) ⟨7885835, by rfl⟩ : syracuseStep 10514447 = 15771671) B15771671
theorem B7009631 : Blo 2075435 7009631 := bstep (se 1 (by rfl) ⟨5257223, by rfl⟩ : syracuseStep 7009631 = 10514447) B10514447
theorem B4673087 : Blo 2075435 4673087 := bstep (se 1 (by rfl) ⟨3504815, by rfl⟩ : syracuseStep 4673087 = 7009631) B7009631
theorem B3115391 : Blo 2075435 3115391 := bstep (se 1 (by rfl) ⟨2336543, by rfl⟩ : syracuseStep 3115391 = 4673087) B4673087
theorem B2076927 : Blo 2075435 2076927 := bstep (se 1 (by rfl) ⟨1557695, by rfl⟩ : syracuseStep 2076927 = 3115391) B3115391
theorem B3115397 : Blo 2075435 3115397 := bbase (se 4 (by rfl) ⟨292068, by rfl⟩ : syracuseStep 3115397 = 584137) (by norm_num)
theorem B2076931 : Blo 2075435 2076931 := bstep (se 1 (by rfl) ⟨1557698, by rfl⟩ : syracuseStep 2076931 = 3115397) B3115397
theorem B3504829 : Blo 2075435 3504829 := bbase (se 3 (by rfl) ⟨657155, by rfl⟩ : syracuseStep 3504829 = 1314311) (by norm_num)
theorem B4673105 : Blo 2075435 4673105 := bstep (se 2 (by rfl) ⟨1752414, by rfl⟩ : syracuseStep 4673105 = 3504829) B3504829
theorem B3115403 : Blo 2075435 3115403 := bstep (se 1 (by rfl) ⟨2336552, by rfl⟩ : syracuseStep 3115403 = 4673105) B4673105
theorem B2076935 : Blo 2075435 2076935 := bstep (se 1 (by rfl) ⟨1557701, by rfl⟩ : syracuseStep 2076935 = 3115403) B3115403
theorem B2336557 : Blo 2075435 2336557 := bbase (se 3 (by rfl) ⟨438104, by rfl⟩ : syracuseStep 2336557 = 876209) (by norm_num)
theorem B3115409 : Blo 2075435 3115409 := bstep (se 2 (by rfl) ⟨1168278, by rfl⟩ : syracuseStep 3115409 = 2336557) B2336557
theorem B2076939 : Blo 2075435 2076939 := bstep (se 1 (by rfl) ⟨1557704, by rfl⟩ : syracuseStep 2076939 = 3115409) B3115409
theorem B7009685 : Blo 2075435 7009685 := bbase (se 6 (by rfl) ⟨164289, by rfl⟩ : syracuseStep 7009685 = 328579) (by norm_num)
theorem B4673123 : Blo 2075435 4673123 := bstep (se 1 (by rfl) ⟨3504842, by rfl⟩ : syracuseStep 4673123 = 7009685) B7009685
theorem B3115415 : Blo 2075435 3115415 := bstep (se 1 (by rfl) ⟨2336561, by rfl⟩ : syracuseStep 3115415 = 4673123) B4673123
theorem B2076943 : Blo 2075435 2076943 := bstep (se 1 (by rfl) ⟨1557707, by rfl⟩ : syracuseStep 2076943 = 3115415) B3115415
theorem B3115421 : Blo 2075435 3115421 := bbase (se 3 (by rfl) ⟨584141, by rfl⟩ : syracuseStep 3115421 = 1168283) (by norm_num)
theorem B2076947 : Blo 2075435 2076947 := bstep (se 1 (by rfl) ⟨1557710, by rfl⟩ : syracuseStep 2076947 = 3115421) B3115421
theorem B4673141 : Blo 2075435 4673141 := bbase (se 5 (by rfl) ⟨219053, by rfl⟩ : syracuseStep 4673141 = 438107) (by norm_num)
theorem B3115427 : Blo 2075435 3115427 := bstep (se 1 (by rfl) ⟨2336570, by rfl⟩ : syracuseStep 3115427 = 4673141) B4673141
theorem B2076951 : Blo 2075435 2076951 := bstep (se 1 (by rfl) ⟨1557713, by rfl⟩ : syracuseStep 2076951 = 3115427) B3115427
theorem B6653765 : Blo 2075435 6653765 := bbase (se 4 (by rfl) ⟨623790, by rfl⟩ : syracuseStep 6653765 = 1247581) (by norm_num)
theorem B17743373 : Blo 2075435 17743373 := bstep (se 3 (by rfl) ⟨3326882, by rfl⟩ : syracuseStep 17743373 = 6653765) B6653765
theorem B11828915 : Blo 2075435 11828915 := bstep (se 1 (by rfl) ⟨8871686, by rfl⟩ : syracuseStep 11828915 = 17743373) B17743373
theorem B7885943 : Blo 2075435 7885943 := bstep (se 1 (by rfl) ⟨5914457, by rfl⟩ : syracuseStep 7885943 = 11828915) B11828915
theorem B5257295 : Blo 2075435 5257295 := bstep (se 1 (by rfl) ⟨3942971, by rfl⟩ : syracuseStep 5257295 = 7885943) B7885943
theorem B3504863 : Blo 2075435 3504863 := bstep (se 1 (by rfl) ⟨2628647, by rfl⟩ : syracuseStep 3504863 = 5257295) B5257295
theorem B2336575 : Blo 2075435 2336575 := bstep (se 1 (by rfl) ⟨1752431, by rfl⟩ : syracuseStep 2336575 = 3504863) B3504863
theorem B3115433 : Blo 2075435 3115433 := bstep (se 2 (by rfl) ⟨1168287, by rfl⟩ : syracuseStep 3115433 = 2336575) B2336575
theorem B2076955 : Blo 2075435 2076955 := bstep (se 1 (by rfl) ⟨1557716, by rfl⟩ : syracuseStep 2076955 = 3115433) B3115433
theorem B7885957 : Blo 2075435 7885957 := bbase (se 4 (by rfl) ⟨739308, by rfl⟩ : syracuseStep 7885957 = 1478617) (by norm_num)
theorem B10514609 : Blo 2075435 10514609 := bstep (se 2 (by rfl) ⟨3942978, by rfl⟩ : syracuseStep 10514609 = 7885957) B7885957
theorem B7009739 : Blo 2075435 7009739 := bstep (se 1 (by rfl) ⟨5257304, by rfl⟩ : syracuseStep 7009739 = 10514609) B10514609
theorem B4673159 : Blo 2075435 4673159 := bstep (se 1 (by rfl) ⟨3504869, by rfl⟩ : syracuseStep 4673159 = 7009739) B7009739
theorem B3115439 : Blo 2075435 3115439 := bstep (se 1 (by rfl) ⟨2336579, by rfl⟩ : syracuseStep 3115439 = 4673159) B4673159
theorem B2076959 : Blo 2075435 2076959 := bstep (se 1 (by rfl) ⟨1557719, by rfl⟩ : syracuseStep 2076959 = 3115439) B3115439
theorem B3115445 : Blo 2075435 3115445 := bbase (se 5 (by rfl) ⟨146036, by rfl⟩ : syracuseStep 3115445 = 292073) (by norm_num)
theorem B2076963 : Blo 2075435 2076963 := bstep (se 1 (by rfl) ⟨1557722, by rfl⟩ : syracuseStep 2076963 = 3115445) B3115445
theorem B5257325 : Blo 2075435 5257325 := bbase (se 3 (by rfl) ⟨985748, by rfl⟩ : syracuseStep 5257325 = 1971497) (by norm_num)
theorem B3504883 : Blo 2075435 3504883 := bstep (se 1 (by rfl) ⟨2628662, by rfl⟩ : syracuseStep 3504883 = 5257325) B5257325
theorem B4673177 : Blo 2075435 4673177 := bstep (se 2 (by rfl) ⟨1752441, by rfl⟩ : syracuseStep 4673177 = 3504883) B3504883
theorem B3115451 : Blo 2075435 3115451 := bstep (se 1 (by rfl) ⟨2336588, by rfl⟩ : syracuseStep 3115451 = 4673177) B4673177
theorem B2076967 : Blo 2075435 2076967 := bstep (se 1 (by rfl) ⟨1557725, by rfl⟩ : syracuseStep 2076967 = 3115451) B3115451
theorem B2336593 : Blo 2075435 2336593 := bbase (se 2 (by rfl) ⟨876222, by rfl⟩ : syracuseStep 2336593 = 1752445) (by norm_num)
theorem B3115457 : Blo 2075435 3115457 := bstep (se 2 (by rfl) ⟨1168296, by rfl⟩ : syracuseStep 3115457 = 2336593) B2336593
theorem B2076971 : Blo 2075435 2076971 := bstep (se 1 (by rfl) ⟨1557728, by rfl⟩ : syracuseStep 2076971 = 3115457) B3115457
theorem B4990373 : Blo 2075435 4990373 := bbase (se 4 (by rfl) ⟨467847, by rfl⟩ : syracuseStep 4990373 = 935695) (by norm_num)
theorem B3326915 : Blo 2075435 3326915 := bstep (se 1 (by rfl) ⟨2495186, by rfl⟩ : syracuseStep 3326915 = 4990373) B4990373
theorem B2217943 : Blo 2075435 2217943 := bstep (se 1 (by rfl) ⟨1663457, by rfl⟩ : syracuseStep 2217943 = 3326915) B3326915
theorem B2957257 : Blo 2075435 2957257 := bstep (se 2 (by rfl) ⟨1108971, by rfl⟩ : syracuseStep 2957257 = 2217943) B2217943
theorem B3943009 : Blo 2075435 3943009 := bstep (se 2 (by rfl) ⟨1478628, by rfl⟩ : syracuseStep 3943009 = 2957257) B2957257
theorem B5257345 : Blo 2075435 5257345 := bstep (se 2 (by rfl) ⟨1971504, by rfl⟩ : syracuseStep 5257345 = 3943009) B3943009
theorem B7009793 : Blo 2075435 7009793 := bstep (se 2 (by rfl) ⟨2628672, by rfl⟩ : syracuseStep 7009793 = 5257345) B5257345
theorem B4673195 : Blo 2075435 4673195 := bstep (se 1 (by rfl) ⟨3504896, by rfl⟩ : syracuseStep 4673195 = 7009793) B7009793
theorem B3115463 : Blo 2075435 3115463 := bstep (se 1 (by rfl) ⟨2336597, by rfl⟩ : syracuseStep 3115463 = 4673195) B4673195
theorem B2076975 : Blo 2075435 2076975 := bstep (se 1 (by rfl) ⟨1557731, by rfl⟩ : syracuseStep 2076975 = 3115463) B3115463
theorem B3115469 : Blo 2075435 3115469 := bbase (se 3 (by rfl) ⟨584150, by rfl⟩ : syracuseStep 3115469 = 1168301) (by norm_num)
theorem B2076979 : Blo 2075435 2076979 := bstep (se 1 (by rfl) ⟨1557734, by rfl⟩ : syracuseStep 2076979 = 3115469) B3115469
theorem B4673213 : Blo 2075435 4673213 := bbase (se 3 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 4673213 = 1752455) (by norm_num)
theorem B3115475 : Blo 2075435 3115475 := bstep (se 1 (by rfl) ⟨2336606, by rfl⟩ : syracuseStep 3115475 = 4673213) B4673213
theorem B2076983 : Blo 2075435 2076983 := bstep (se 1 (by rfl) ⟨1557737, by rfl⟩ : syracuseStep 2076983 = 3115475) B3115475
theorem B3504917 : Blo 2075435 3504917 := bbase (se 6 (by rfl) ⟨82146, by rfl⟩ : syracuseStep 3504917 = 164293) (by norm_num)
theorem B2336611 : Blo 2075435 2336611 := bstep (se 1 (by rfl) ⟨1752458, by rfl⟩ : syracuseStep 2336611 = 3504917) B3504917
theorem B3115481 : Blo 2075435 3115481 := bstep (se 2 (by rfl) ⟨1168305, by rfl⟩ : syracuseStep 3115481 = 2336611) B2336611
theorem B2076987 : Blo 2075435 2076987 := bstep (se 1 (by rfl) ⟨1557740, by rfl⟩ : syracuseStep 2076987 = 3115481) B3115481
theorem B26978645 : Blo 2075435 26978645 := bbase (se 10 (by rfl) ⟨39519, by rfl⟩ : syracuseStep 26978645 = 79039) (by norm_num)
theorem B17985763 : Blo 2075435 17985763 := bstep (se 1 (by rfl) ⟨13489322, by rfl⟩ : syracuseStep 17985763 = 26978645) B26978645
theorem B23981017 : Blo 2075435 23981017 := bstep (se 2 (by rfl) ⟨8992881, by rfl⟩ : syracuseStep 23981017 = 17985763) B17985763
theorem B31974689 : Blo 2075435 31974689 := bstep (se 2 (by rfl) ⟨11990508, by rfl⟩ : syracuseStep 31974689 = 23981017) B23981017
theorem B21316459 : Blo 2075435 21316459 := bstep (se 1 (by rfl) ⟨15987344, by rfl⟩ : syracuseStep 21316459 = 31974689) B31974689
theorem B28421945 : Blo 2075435 28421945 := bstep (se 2 (by rfl) ⟨10658229, by rfl⟩ : syracuseStep 28421945 = 21316459) B21316459
theorem B18947963 : Blo 2075435 18947963 := bstep (se 1 (by rfl) ⟨14210972, by rfl⟩ : syracuseStep 18947963 = 28421945) B28421945
theorem B50527901 : Blo 2075435 50527901 := bstep (se 3 (by rfl) ⟨9473981, by rfl⟩ : syracuseStep 50527901 = 18947963) B18947963
theorem B33685267 : Blo 2075435 33685267 := bstep (se 1 (by rfl) ⟨25263950, by rfl⟩ : syracuseStep 33685267 = 50527901) B50527901
theorem B44913689 : Blo 2075435 44913689 := bstep (se 2 (by rfl) ⟨16842633, by rfl⟩ : syracuseStep 44913689 = 33685267) B33685267
theorem B29942459 : Blo 2075435 29942459 := bstep (se 1 (by rfl) ⟨22456844, by rfl⟩ : syracuseStep 29942459 = 44913689) B44913689
theorem B19961639 : Blo 2075435 19961639 := bstep (se 1 (by rfl) ⟨14971229, by rfl⟩ : syracuseStep 19961639 = 29942459) B29942459
theorem B13307759 : Blo 2075435 13307759 := bstep (se 1 (by rfl) ⟨9980819, by rfl⟩ : syracuseStep 13307759 = 19961639) B19961639
theorem B8871839 : Blo 2075435 8871839 := bstep (se 1 (by rfl) ⟨6653879, by rfl⟩ : syracuseStep 8871839 = 13307759) B13307759
theorem B5914559 : Blo 2075435 5914559 := bstep (se 1 (by rfl) ⟨4435919, by rfl⟩ : syracuseStep 5914559 = 8871839) B8871839
theorem B15772157 : Blo 2075435 15772157 := bstep (se 3 (by rfl) ⟨2957279, by rfl⟩ : syracuseStep 15772157 = 5914559) B5914559
theorem B10514771 : Blo 2075435 10514771 := bstep (se 1 (by rfl) ⟨7886078, by rfl⟩ : syracuseStep 10514771 = 15772157) B15772157
theorem B7009847 : Blo 2075435 7009847 := bstep (se 1 (by rfl) ⟨5257385, by rfl⟩ : syracuseStep 7009847 = 10514771) B10514771
theorem B4673231 : Blo 2075435 4673231 := bstep (se 1 (by rfl) ⟨3504923, by rfl⟩ : syracuseStep 4673231 = 7009847) B7009847
theorem B3115487 : Blo 2075435 3115487 := bstep (se 1 (by rfl) ⟨2336615, by rfl⟩ : syracuseStep 3115487 = 4673231) B4673231
theorem B2076991 : Blo 2075435 2076991 := bstep (se 1 (by rfl) ⟨1557743, by rfl⟩ : syracuseStep 2076991 = 3115487) B3115487
theorem B3115493 : Blo 2075435 3115493 := bbase (se 4 (by rfl) ⟨292077, by rfl⟩ : syracuseStep 3115493 = 584155) (by norm_num)
theorem B2076995 : Blo 2075435 2076995 := bstep (se 1 (by rfl) ⟨1557746, by rfl⟩ : syracuseStep 2076995 = 3115493) B3115493
theorem B2563769 : Blo 2075435 2563769 := bbase (se 2 (by rfl) ⟨961413, by rfl⟩ : syracuseStep 2563769 = 1922827) (by norm_num)
theorem B6836717 : Blo 2075435 6836717 := bstep (se 3 (by rfl) ⟨1281884, by rfl⟩ : syracuseStep 6836717 = 2563769) B2563769
theorem B4557811 : Blo 2075435 4557811 := bstep (se 1 (by rfl) ⟨3418358, by rfl⟩ : syracuseStep 4557811 = 6836717) B6836717
theorem B6077081 : Blo 2075435 6077081 := bstep (se 2 (by rfl) ⟨2278905, by rfl⟩ : syracuseStep 6077081 = 4557811) B4557811
theorem B4051387 : Blo 2075435 4051387 := bstep (se 1 (by rfl) ⟨3038540, by rfl⟩ : syracuseStep 4051387 = 6077081) B6077081
theorem B5401849 : Blo 2075435 5401849 := bstep (se 2 (by rfl) ⟨2025693, by rfl⟩ : syracuseStep 5401849 = 4051387) B4051387
theorem B7202465 : Blo 2075435 7202465 := bstep (se 2 (by rfl) ⟨2700924, by rfl⟩ : syracuseStep 7202465 = 5401849) B5401849
theorem B4801643 : Blo 2075435 4801643 := bstep (se 1 (by rfl) ⟨3601232, by rfl⟩ : syracuseStep 4801643 = 7202465) B7202465
theorem B3201095 : Blo 2075435 3201095 := bstep (se 1 (by rfl) ⟨2400821, by rfl⟩ : syracuseStep 3201095 = 4801643) B4801643
theorem B2134063 : Blo 2075435 2134063 := bstep (se 1 (by rfl) ⟨1600547, by rfl⟩ : syracuseStep 2134063 = 3201095) B3201095
theorem B2845417 : Blo 2075435 2845417 := bstep (se 2 (by rfl) ⟨1067031, by rfl⟩ : syracuseStep 2845417 = 2134063) B2134063
theorem B3793889 : Blo 2075435 3793889 := bstep (se 2 (by rfl) ⟨1422708, by rfl⟩ : syracuseStep 3793889 = 2845417) B2845417
theorem B10117037 : Blo 2075435 10117037 := bstep (se 3 (by rfl) ⟨1896944, by rfl⟩ : syracuseStep 10117037 = 3793889) B3793889
theorem B6744691 : Blo 2075435 6744691 := bstep (se 1 (by rfl) ⟨5058518, by rfl⟩ : syracuseStep 6744691 = 10117037) B10117037
theorem B35971685 : Blo 2075435 35971685 := bstep (se 4 (by rfl) ⟨3372345, by rfl⟩ : syracuseStep 35971685 = 6744691) B6744691
theorem B23981123 : Blo 2075435 23981123 := bstep (se 1 (by rfl) ⟨17985842, by rfl⟩ : syracuseStep 23981123 = 35971685) B35971685
theorem B15987415 : Blo 2075435 15987415 := bstep (se 1 (by rfl) ⟨11990561, by rfl⟩ : syracuseStep 15987415 = 23981123) B23981123
theorem B21316553 : Blo 2075435 21316553 := bstep (se 2 (by rfl) ⟨7993707, by rfl⟩ : syracuseStep 21316553 = 15987415) B15987415
theorem B14211035 : Blo 2075435 14211035 := bstep (se 1 (by rfl) ⟨10658276, by rfl⟩ : syracuseStep 14211035 = 21316553) B21316553
theorem B9474023 : Blo 2075435 9474023 := bstep (se 1 (by rfl) ⟨7105517, by rfl⟩ : syracuseStep 9474023 = 14211035) B14211035
theorem B6316015 : Blo 2075435 6316015 := bstep (se 1 (by rfl) ⟨4737011, by rfl⟩ : syracuseStep 6316015 = 9474023) B9474023
theorem B8421353 : Blo 2075435 8421353 := bstep (se 2 (by rfl) ⟨3158007, by rfl⟩ : syracuseStep 8421353 = 6316015) B6316015
theorem B5614235 : Blo 2075435 5614235 := bstep (se 1 (by rfl) ⟨4210676, by rfl⟩ : syracuseStep 5614235 = 8421353) B8421353
theorem B3742823 : Blo 2075435 3742823 := bstep (se 1 (by rfl) ⟨2807117, by rfl⟩ : syracuseStep 3742823 = 5614235) B5614235
theorem B2495215 : Blo 2075435 2495215 := bstep (se 1 (by rfl) ⟨1871411, by rfl⟩ : syracuseStep 2495215 = 3742823) B3742823
theorem B13307813 : Blo 2075435 13307813 := bstep (se 4 (by rfl) ⟨1247607, by rfl⟩ : syracuseStep 13307813 = 2495215) B2495215
theorem B8871875 : Blo 2075435 8871875 := bstep (se 1 (by rfl) ⟨6653906, by rfl⟩ : syracuseStep 8871875 = 13307813) B13307813
theorem B5914583 : Blo 2075435 5914583 := bstep (se 1 (by rfl) ⟨4435937, by rfl⟩ : syracuseStep 5914583 = 8871875) B8871875
theorem B3943055 : Blo 2075435 3943055 := bstep (se 1 (by rfl) ⟨2957291, by rfl⟩ : syracuseStep 3943055 = 5914583) B5914583
theorem B2628703 : Blo 2075435 2628703 := bstep (se 1 (by rfl) ⟨1971527, by rfl⟩ : syracuseStep 2628703 = 3943055) B3943055
theorem B3504937 : Blo 2075435 3504937 := bstep (se 2 (by rfl) ⟨1314351, by rfl⟩ : syracuseStep 3504937 = 2628703) B2628703
theorem B4673249 : Blo 2075435 4673249 := bstep (se 2 (by rfl) ⟨1752468, by rfl⟩ : syracuseStep 4673249 = 3504937) B3504937
theorem B3115499 : Blo 2075435 3115499 := bstep (se 1 (by rfl) ⟨2336624, by rfl⟩ : syracuseStep 3115499 = 4673249) B4673249
theorem B2076999 : Blo 2075435 2076999 := bstep (se 1 (by rfl) ⟨1557749, by rfl⟩ : syracuseStep 2076999 = 3115499) B3115499
theorem B2336629 : Blo 2075435 2336629 := bbase (se 5 (by rfl) ⟨109529, by rfl⟩ : syracuseStep 2336629 = 219059) (by norm_num)
theorem B3115505 : Blo 2075435 3115505 := bstep (se 2 (by rfl) ⟨1168314, by rfl⟩ : syracuseStep 3115505 = 2336629) B2336629
theorem B2077003 : Blo 2075435 2077003 := bstep (se 1 (by rfl) ⟨1557752, by rfl⟩ : syracuseStep 2077003 = 3115505) B3115505
theorem B2628713 : Blo 2075435 2628713 := bbase (se 2 (by rfl) ⟨985767, by rfl⟩ : syracuseStep 2628713 = 1971535) (by norm_num)
theorem B7009901 : Blo 2075435 7009901 := bstep (se 3 (by rfl) ⟨1314356, by rfl⟩ : syracuseStep 7009901 = 2628713) B2628713
theorem B4673267 : Blo 2075435 4673267 := bstep (se 1 (by rfl) ⟨3504950, by rfl⟩ : syracuseStep 4673267 = 7009901) B7009901
theorem B3115511 : Blo 2075435 3115511 := bstep (se 1 (by rfl) ⟨2336633, by rfl⟩ : syracuseStep 3115511 = 4673267) B4673267
theorem B2077007 : Blo 2075435 2077007 := bstep (se 1 (by rfl) ⟨1557755, by rfl⟩ : syracuseStep 2077007 = 3115511) B3115511
theorem B3115517 : Blo 2075435 3115517 := bbase (se 3 (by rfl) ⟨584159, by rfl⟩ : syracuseStep 3115517 = 1168319) (by norm_num)
theorem B2077011 : Blo 2075435 2077011 := bstep (se 1 (by rfl) ⟨1557758, by rfl⟩ : syracuseStep 2077011 = 3115517) B3115517
theorem B4673285 : Blo 2075435 4673285 := bbase (se 4 (by rfl) ⟨438120, by rfl⟩ : syracuseStep 4673285 = 876241) (by norm_num)
theorem B3115523 : Blo 2075435 3115523 := bstep (se 1 (by rfl) ⟨2336642, by rfl⟩ : syracuseStep 3115523 = 4673285) B4673285
theorem B2077015 : Blo 2075435 2077015 := bstep (se 1 (by rfl) ⟨1557761, by rfl⟩ : syracuseStep 2077015 = 3115523) B3115523
theorem B3943093 : Blo 2075435 3943093 := bbase (se 5 (by rfl) ⟨184832, by rfl⟩ : syracuseStep 3943093 = 369665) (by norm_num)
theorem B5257457 : Blo 2075435 5257457 := bstep (se 2 (by rfl) ⟨1971546, by rfl⟩ : syracuseStep 5257457 = 3943093) B3943093
theorem B3504971 : Blo 2075435 3504971 := bstep (se 1 (by rfl) ⟨2628728, by rfl⟩ : syracuseStep 3504971 = 5257457) B5257457
theorem B2336647 : Blo 2075435 2336647 := bstep (se 1 (by rfl) ⟨1752485, by rfl⟩ : syracuseStep 2336647 = 3504971) B3504971
theorem B3115529 : Blo 2075435 3115529 := bstep (se 2 (by rfl) ⟨1168323, by rfl⟩ : syracuseStep 3115529 = 2336647) B2336647
theorem B2077019 : Blo 2075435 2077019 := bstep (se 1 (by rfl) ⟨1557764, by rfl⟩ : syracuseStep 2077019 = 3115529) B3115529
theorem B10514933 : Blo 2075435 10514933 := bbase (se 5 (by rfl) ⟨492887, by rfl⟩ : syracuseStep 10514933 = 985775) (by norm_num)
theorem B7009955 : Blo 2075435 7009955 := bstep (se 1 (by rfl) ⟨5257466, by rfl⟩ : syracuseStep 7009955 = 10514933) B10514933
theorem B4673303 : Blo 2075435 4673303 := bstep (se 1 (by rfl) ⟨3504977, by rfl⟩ : syracuseStep 4673303 = 7009955) B7009955
theorem B3115535 : Blo 2075435 3115535 := bstep (se 1 (by rfl) ⟨2336651, by rfl⟩ : syracuseStep 3115535 = 4673303) B4673303
theorem B2077023 : Blo 2075435 2077023 := bstep (se 1 (by rfl) ⟨1557767, by rfl⟩ : syracuseStep 2077023 = 3115535) B3115535
theorem B3115541 : Blo 2075435 3115541 := bbase (se 6 (by rfl) ⟨73020, by rfl⟩ : syracuseStep 3115541 = 146041) (by norm_num)
theorem B2077027 : Blo 2075435 2077027 := bstep (se 1 (by rfl) ⟨1557770, by rfl⟩ : syracuseStep 2077027 = 3115541) B3115541
theorem B17744021 : Blo 2075435 17744021 := bbase (se 6 (by rfl) ⟨415875, by rfl⟩ : syracuseStep 17744021 = 831751) (by norm_num)
theorem B11829347 : Blo 2075435 11829347 := bstep (se 1 (by rfl) ⟨8872010, by rfl⟩ : syracuseStep 11829347 = 17744021) B17744021
theorem B7886231 : Blo 2075435 7886231 := bstep (se 1 (by rfl) ⟨5914673, by rfl⟩ : syracuseStep 7886231 = 11829347) B11829347
theorem B5257487 : Blo 2075435 5257487 := bstep (se 1 (by rfl) ⟨3943115, by rfl⟩ : syracuseStep 5257487 = 7886231) B7886231
theorem B3504991 : Blo 2075435 3504991 := bstep (se 1 (by rfl) ⟨2628743, by rfl⟩ : syracuseStep 3504991 = 5257487) B5257487
theorem B4673321 : Blo 2075435 4673321 := bstep (se 2 (by rfl) ⟨1752495, by rfl⟩ : syracuseStep 4673321 = 3504991) B3504991
theorem B3115547 : Blo 2075435 3115547 := bstep (se 1 (by rfl) ⟨2336660, by rfl⟩ : syracuseStep 3115547 = 4673321) B4673321
theorem B2077031 : Blo 2075435 2077031 := bstep (se 1 (by rfl) ⟨1557773, by rfl⟩ : syracuseStep 2077031 = 3115547) B3115547
theorem B2336665 : Blo 2075435 2336665 := bbase (se 2 (by rfl) ⟨876249, by rfl⟩ : syracuseStep 2336665 = 1752499) (by norm_num)
theorem B3115553 : Blo 2075435 3115553 := bstep (se 2 (by rfl) ⟨1168332, by rfl⟩ : syracuseStep 3115553 = 2336665) B2336665
theorem B2077035 : Blo 2075435 2077035 := bstep (se 1 (by rfl) ⟨1557776, by rfl⟩ : syracuseStep 2077035 = 3115553) B3115553
theorem B7886261 : Blo 2075435 7886261 := bbase (se 5 (by rfl) ⟨369668, by rfl⟩ : syracuseStep 7886261 = 739337) (by norm_num)
theorem B5257507 : Blo 2075435 5257507 := bstep (se 1 (by rfl) ⟨3943130, by rfl⟩ : syracuseStep 5257507 = 7886261) B7886261
theorem B7010009 : Blo 2075435 7010009 := bstep (se 2 (by rfl) ⟨2628753, by rfl⟩ : syracuseStep 7010009 = 5257507) B5257507
theorem B4673339 : Blo 2075435 4673339 := bstep (se 1 (by rfl) ⟨3505004, by rfl⟩ : syracuseStep 4673339 = 7010009) B7010009
theorem B3115559 : Blo 2075435 3115559 := bstep (se 1 (by rfl) ⟨2336669, by rfl⟩ : syracuseStep 3115559 = 4673339) B4673339
theorem B2077039 : Blo 2075435 2077039 := bstep (se 1 (by rfl) ⟨1557779, by rfl⟩ : syracuseStep 2077039 = 3115559) B3115559
theorem B3115565 : Blo 2075435 3115565 := bbase (se 3 (by rfl) ⟨584168, by rfl⟩ : syracuseStep 3115565 = 1168337) (by norm_num)
theorem B2077043 : Blo 2075435 2077043 := bstep (se 1 (by rfl) ⟨1557782, by rfl⟩ : syracuseStep 2077043 = 3115565) B3115565
theorem B4673357 : Blo 2075435 4673357 := bbase (se 3 (by rfl) ⟨876254, by rfl⟩ : syracuseStep 4673357 = 1752509) (by norm_num)
theorem B3115571 : Blo 2075435 3115571 := bstep (se 1 (by rfl) ⟨2336678, by rfl⟩ : syracuseStep 3115571 = 4673357) B4673357
theorem B2077047 : Blo 2075435 2077047 := bstep (se 1 (by rfl) ⟨1557785, by rfl⟩ : syracuseStep 2077047 = 3115571) B3115571
theorem B2628769 : Blo 2075435 2628769 := bbase (se 2 (by rfl) ⟨985788, by rfl⟩ : syracuseStep 2628769 = 1971577) (by norm_num)
theorem B3505025 : Blo 2075435 3505025 := bstep (se 2 (by rfl) ⟨1314384, by rfl⟩ : syracuseStep 3505025 = 2628769) B2628769
theorem B2336683 : Blo 2075435 2336683 := bstep (se 1 (by rfl) ⟨1752512, by rfl⟩ : syracuseStep 2336683 = 3505025) B3505025
theorem B3115577 : Blo 2075435 3115577 := bstep (se 2 (by rfl) ⟨1168341, by rfl⟩ : syracuseStep 3115577 = 2336683) B2336683
theorem B2077051 : Blo 2075435 2077051 := bstep (se 1 (by rfl) ⟨1557788, by rfl⟩ : syracuseStep 2077051 = 3115577) B3115577
theorem B23658965 : Blo 2075435 23658965 := bbase (se 7 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 23658965 = 554507) (by norm_num)
theorem B15772643 : Blo 2075435 15772643 := bstep (se 1 (by rfl) ⟨11829482, by rfl⟩ : syracuseStep 15772643 = 23658965) B23658965
theorem B10515095 : Blo 2075435 10515095 := bstep (se 1 (by rfl) ⟨7886321, by rfl⟩ : syracuseStep 10515095 = 15772643) B15772643
theorem B7010063 : Blo 2075435 7010063 := bstep (se 1 (by rfl) ⟨5257547, by rfl⟩ : syracuseStep 7010063 = 10515095) B10515095
theorem B4673375 : Blo 2075435 4673375 := bstep (se 1 (by rfl) ⟨3505031, by rfl⟩ : syracuseStep 4673375 = 7010063) B7010063
theorem B3115583 : Blo 2075435 3115583 := bstep (se 1 (by rfl) ⟨2336687, by rfl⟩ : syracuseStep 3115583 = 4673375) B4673375
theorem B2077055 : Blo 2075435 2077055 := bstep (se 1 (by rfl) ⟨1557791, by rfl⟩ : syracuseStep 2077055 = 3115583) B3115583
theorem B3115589 : Blo 2075435 3115589 := bbase (se 4 (by rfl) ⟨292086, by rfl⟩ : syracuseStep 3115589 = 584173) (by norm_num)
theorem B2077059 : Blo 2075435 2077059 := bstep (se 1 (by rfl) ⟨1557794, by rfl⟩ : syracuseStep 2077059 = 3115589) B3115589
theorem B3505045 : Blo 2075435 3505045 := bbase (se 6 (by rfl) ⟨82149, by rfl⟩ : syracuseStep 3505045 = 164299) (by norm_num)
theorem B4673393 : Blo 2075435 4673393 := bstep (se 2 (by rfl) ⟨1752522, by rfl⟩ : syracuseStep 4673393 = 3505045) B3505045
theorem B3115595 : Blo 2075435 3115595 := bstep (se 1 (by rfl) ⟨2336696, by rfl⟩ : syracuseStep 3115595 = 4673393) B4673393
theorem B2077063 : Blo 2075435 2077063 := bstep (se 1 (by rfl) ⟨1557797, by rfl⟩ : syracuseStep 2077063 = 3115595) B3115595
theorem B2336701 : Blo 2075435 2336701 := bbase (se 3 (by rfl) ⟨438131, by rfl⟩ : syracuseStep 2336701 = 876263) (by norm_num)
theorem B3115601 : Blo 2075435 3115601 := bstep (se 2 (by rfl) ⟨1168350, by rfl⟩ : syracuseStep 3115601 = 2336701) B2336701
theorem B2077067 : Blo 2075435 2077067 := bstep (se 1 (by rfl) ⟨1557800, by rfl⟩ : syracuseStep 2077067 = 3115601) B3115601
theorem B7010117 : Blo 2075435 7010117 := bbase (se 4 (by rfl) ⟨657198, by rfl⟩ : syracuseStep 7010117 = 1314397) (by norm_num)
theorem B4673411 : Blo 2075435 4673411 := bstep (se 1 (by rfl) ⟨3505058, by rfl⟩ : syracuseStep 4673411 = 7010117) B7010117
theorem B3115607 : Blo 2075435 3115607 := bstep (se 1 (by rfl) ⟨2336705, by rfl⟩ : syracuseStep 3115607 = 4673411) B4673411
theorem B2077071 : Blo 2075435 2077071 := bstep (se 1 (by rfl) ⟨1557803, by rfl⟩ : syracuseStep 2077071 = 3115607) B3115607
theorem B3115613 : Blo 2075435 3115613 := bbase (se 3 (by rfl) ⟨584177, by rfl⟩ : syracuseStep 3115613 = 1168355) (by norm_num)
theorem B2077075 : Blo 2075435 2077075 := bstep (se 1 (by rfl) ⟨1557806, by rfl⟩ : syracuseStep 2077075 = 3115613) B3115613
theorem B4673429 : Blo 2075435 4673429 := bbase (se 6 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 4673429 = 219067) (by norm_num)
theorem B3115619 : Blo 2075435 3115619 := bstep (se 1 (by rfl) ⟨2336714, by rfl⟩ : syracuseStep 3115619 = 4673429) B4673429
theorem B2077079 : Blo 2075435 2077079 := bstep (se 1 (by rfl) ⟨1557809, by rfl⟩ : syracuseStep 2077079 = 3115619) B3115619
theorem B4436117 : Blo 2075435 4436117 := bbase (se 6 (by rfl) ⟨103971, by rfl⟩ : syracuseStep 4436117 = 207943) (by norm_num)
theorem B2957411 : Blo 2075435 2957411 := bstep (se 1 (by rfl) ⟨2218058, by rfl⟩ : syracuseStep 2957411 = 4436117) B4436117
theorem B7886429 : Blo 2075435 7886429 := bstep (se 3 (by rfl) ⟨1478705, by rfl⟩ : syracuseStep 7886429 = 2957411) B2957411
theorem B5257619 : Blo 2075435 5257619 := bstep (se 1 (by rfl) ⟨3943214, by rfl⟩ : syracuseStep 5257619 = 7886429) B7886429
theorem B3505079 : Blo 2075435 3505079 := bstep (se 1 (by rfl) ⟨2628809, by rfl⟩ : syracuseStep 3505079 = 5257619) B5257619
theorem B2336719 : Blo 2075435 2336719 := bstep (se 1 (by rfl) ⟨1752539, by rfl⟩ : syracuseStep 2336719 = 3505079) B3505079
theorem B3115625 : Blo 2075435 3115625 := bstep (se 2 (by rfl) ⟨1168359, by rfl⟩ : syracuseStep 3115625 = 2336719) B2336719
theorem B2077083 : Blo 2075435 2077083 := bstep (se 1 (by rfl) ⟨1557812, by rfl⟩ : syracuseStep 2077083 = 3115625) B3115625
theorem B9474421 : Blo 2075435 9474421 := bbase (se 5 (by rfl) ⟨444113, by rfl⟩ : syracuseStep 9474421 = 888227) (by norm_num)
theorem B12632561 : Blo 2075435 12632561 := bstep (se 2 (by rfl) ⟨4737210, by rfl⟩ : syracuseStep 12632561 = 9474421) B9474421
theorem B8421707 : Blo 2075435 8421707 := bstep (se 1 (by rfl) ⟨6316280, by rfl⟩ : syracuseStep 8421707 = 12632561) B12632561
theorem B5614471 : Blo 2075435 5614471 := bstep (se 1 (by rfl) ⟨4210853, by rfl⟩ : syracuseStep 5614471 = 8421707) B8421707
theorem B7485961 : Blo 2075435 7485961 := bstep (se 2 (by rfl) ⟨2807235, by rfl⟩ : syracuseStep 7485961 = 5614471) B5614471
theorem B9981281 : Blo 2075435 9981281 := bstep (se 2 (by rfl) ⟨3742980, by rfl⟩ : syracuseStep 9981281 = 7485961) B7485961
theorem B6654187 : Blo 2075435 6654187 := bstep (se 1 (by rfl) ⟨4990640, by rfl⟩ : syracuseStep 6654187 = 9981281) B9981281
theorem B8872249 : Blo 2075435 8872249 := bstep (se 2 (by rfl) ⟨3327093, by rfl⟩ : syracuseStep 8872249 = 6654187) B6654187
theorem B11829665 : Blo 2075435 11829665 := bstep (se 2 (by rfl) ⟨4436124, by rfl⟩ : syracuseStep 11829665 = 8872249) B8872249
theorem B7886443 : Blo 2075435 7886443 := bstep (se 1 (by rfl) ⟨5914832, by rfl⟩ : syracuseStep 7886443 = 11829665) B11829665
theorem B10515257 : Blo 2075435 10515257 := bstep (se 2 (by rfl) ⟨3943221, by rfl⟩ : syracuseStep 10515257 = 7886443) B7886443
theorem B7010171 : Blo 2075435 7010171 := bstep (se 1 (by rfl) ⟨5257628, by rfl⟩ : syracuseStep 7010171 = 10515257) B10515257
theorem B4673447 : Blo 2075435 4673447 := bstep (se 1 (by rfl) ⟨3505085, by rfl⟩ : syracuseStep 4673447 = 7010171) B7010171
theorem B3115631 : Blo 2075435 3115631 := bstep (se 1 (by rfl) ⟨2336723, by rfl⟩ : syracuseStep 3115631 = 4673447) B4673447
theorem B2077087 : Blo 2075435 2077087 := bstep (se 1 (by rfl) ⟨1557815, by rfl⟩ : syracuseStep 2077087 = 3115631) B3115631
theorem B3115637 : Blo 2075435 3115637 := bbase (se 5 (by rfl) ⟨146045, by rfl⟩ : syracuseStep 3115637 = 292091) (by norm_num)
theorem B2077091 : Blo 2075435 2077091 := bstep (se 1 (by rfl) ⟨1557818, by rfl⟩ : syracuseStep 2077091 = 3115637) B3115637
theorem B3943237 : Blo 2075435 3943237 := bbase (se 4 (by rfl) ⟨369678, by rfl⟩ : syracuseStep 3943237 = 739357) (by norm_num)
theorem B5257649 : Blo 2075435 5257649 := bstep (se 2 (by rfl) ⟨1971618, by rfl⟩ : syracuseStep 5257649 = 3943237) B3943237
theorem B3505099 : Blo 2075435 3505099 := bstep (se 1 (by rfl) ⟨2628824, by rfl⟩ : syracuseStep 3505099 = 5257649) B5257649
theorem B4673465 : Blo 2075435 4673465 := bstep (se 2 (by rfl) ⟨1752549, by rfl⟩ : syracuseStep 4673465 = 3505099) B3505099
theorem B3115643 : Blo 2075435 3115643 := bstep (se 1 (by rfl) ⟨2336732, by rfl⟩ : syracuseStep 3115643 = 4673465) B4673465
theorem B2077095 : Blo 2075435 2077095 := bstep (se 1 (by rfl) ⟨1557821, by rfl⟩ : syracuseStep 2077095 = 3115643) B3115643
theorem B2336737 : Blo 2075435 2336737 := bbase (se 2 (by rfl) ⟨876276, by rfl⟩ : syracuseStep 2336737 = 1752553) (by norm_num)
theorem B3115649 : Blo 2075435 3115649 := bstep (se 2 (by rfl) ⟨1168368, by rfl⟩ : syracuseStep 3115649 = 2336737) B2336737
theorem B2077099 : Blo 2075435 2077099 := bstep (se 1 (by rfl) ⟨1557824, by rfl⟩ : syracuseStep 2077099 = 3115649) B3115649
theorem B5257669 : Blo 2075435 5257669 := bbase (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) (by norm_num)
theorem B7010225 : Blo 2075435 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B4673483 : Blo 2075435 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B3115655 : Blo 2075435 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B2077103 : Blo 2075435 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B3115661 : Blo 2075435 3115661 := bbase (se 3 (by rfl) ⟨584186, by rfl⟩ : syracuseStep 3115661 = 1168373) (by norm_num)
theorem B2077107 : Blo 2075435 2077107 := bstep (se 1 (by rfl) ⟨1557830, by rfl⟩ : syracuseStep 2077107 = 3115661) B3115661
theorem B4673501 : Blo 2075435 4673501 := bbase (se 3 (by rfl) ⟨876281, by rfl⟩ : syracuseStep 4673501 = 1752563) (by norm_num)
theorem B3115667 : Blo 2075435 3115667 := bstep (se 1 (by rfl) ⟨2336750, by rfl⟩ : syracuseStep 3115667 = 4673501) B4673501
theorem B2077111 : Blo 2075435 2077111 := bstep (se 1 (by rfl) ⟨1557833, by rfl⟩ : syracuseStep 2077111 = 3115667) B3115667
theorem B3505133 : Blo 2075435 3505133 := bbase (se 3 (by rfl) ⟨657212, by rfl⟩ : syracuseStep 3505133 = 1314425) (by norm_num)
theorem B2336755 : Blo 2075435 2336755 := bstep (se 1 (by rfl) ⟨1752566, by rfl⟩ : syracuseStep 2336755 = 3505133) B3505133
theorem B3115673 : Blo 2075435 3115673 := bstep (se 2 (by rfl) ⟨1168377, by rfl⟩ : syracuseStep 3115673 = 2336755) B2336755
theorem B2077115 : Blo 2075435 2077115 := bstep (se 1 (by rfl) ⟨1557836, by rfl⟩ : syracuseStep 2077115 = 3115673) B3115673
theorem B4990717 : Blo 2075435 4990717 := bbase (se 3 (by rfl) ⟨935759, by rfl⟩ : syracuseStep 4990717 = 1871519) (by norm_num)
theorem B26617157 : Blo 2075435 26617157 := bstep (se 4 (by rfl) ⟨2495358, by rfl⟩ : syracuseStep 26617157 = 4990717) B4990717
theorem B17744771 : Blo 2075435 17744771 := bstep (se 1 (by rfl) ⟨13308578, by rfl⟩ : syracuseStep 17744771 = 26617157) B26617157
theorem B11829847 : Blo 2075435 11829847 := bstep (se 1 (by rfl) ⟨8872385, by rfl⟩ : syracuseStep 11829847 = 17744771) B17744771
theorem B15773129 : Blo 2075435 15773129 := bstep (se 2 (by rfl) ⟨5914923, by rfl⟩ : syracuseStep 15773129 = 11829847) B11829847
theorem B10515419 : Blo 2075435 10515419 := bstep (se 1 (by rfl) ⟨7886564, by rfl⟩ : syracuseStep 10515419 = 15773129) B15773129
theorem B7010279 : Blo 2075435 7010279 := bstep (se 1 (by rfl) ⟨5257709, by rfl⟩ : syracuseStep 7010279 = 10515419) B10515419
theorem B4673519 : Blo 2075435 4673519 := bstep (se 1 (by rfl) ⟨3505139, by rfl⟩ : syracuseStep 4673519 = 7010279) B7010279
theorem B3115679 : Blo 2075435 3115679 := bstep (se 1 (by rfl) ⟨2336759, by rfl⟩ : syracuseStep 3115679 = 4673519) B4673519
theorem B2077119 : Blo 2075435 2077119 := bstep (se 1 (by rfl) ⟨1557839, by rfl⟩ : syracuseStep 2077119 = 3115679) B3115679
theorem B3115685 : Blo 2075435 3115685 := bbase (se 4 (by rfl) ⟨292095, by rfl⟩ : syracuseStep 3115685 = 584191) (by norm_num)
theorem B2077123 : Blo 2075435 2077123 := bstep (se 1 (by rfl) ⟨1557842, by rfl⟩ : syracuseStep 2077123 = 3115685) B3115685
theorem B2628865 : Blo 2075435 2628865 := bbase (se 2 (by rfl) ⟨985824, by rfl⟩ : syracuseStep 2628865 = 1971649) (by norm_num)
theorem B3505153 : Blo 2075435 3505153 := bstep (se 2 (by rfl) ⟨1314432, by rfl⟩ : syracuseStep 3505153 = 2628865) B2628865
theorem B4673537 : Blo 2075435 4673537 := bstep (se 2 (by rfl) ⟨1752576, by rfl⟩ : syracuseStep 4673537 = 3505153) B3505153
theorem B3115691 : Blo 2075435 3115691 := bstep (se 1 (by rfl) ⟨2336768, by rfl⟩ : syracuseStep 3115691 = 4673537) B4673537
theorem B2077127 : Blo 2075435 2077127 := bstep (se 1 (by rfl) ⟨1557845, by rfl⟩ : syracuseStep 2077127 = 3115691) B3115691
theorem B2336773 : Blo 2075435 2336773 := bbase (se 4 (by rfl) ⟨219072, by rfl⟩ : syracuseStep 2336773 = 438145) (by norm_num)
theorem B3115697 : Blo 2075435 3115697 := bstep (se 2 (by rfl) ⟨1168386, by rfl⟩ : syracuseStep 3115697 = 2336773) B2336773
theorem B2077131 : Blo 2075435 2077131 := bstep (se 1 (by rfl) ⟨1557848, by rfl⟩ : syracuseStep 2077131 = 3115697) B3115697
theorem B2957485 : Blo 2075435 2957485 := bbase (se 3 (by rfl) ⟨554528, by rfl⟩ : syracuseStep 2957485 = 1109057) (by norm_num)
theorem B3943313 : Blo 2075435 3943313 := bstep (se 2 (by rfl) ⟨1478742, by rfl⟩ : syracuseStep 3943313 = 2957485) B2957485
theorem B2628875 : Blo 2075435 2628875 := bstep (se 1 (by rfl) ⟨1971656, by rfl⟩ : syracuseStep 2628875 = 3943313) B3943313
theorem B7010333 : Blo 2075435 7010333 := bstep (se 3 (by rfl) ⟨1314437, by rfl⟩ : syracuseStep 7010333 = 2628875) B2628875
theorem B4673555 : Blo 2075435 4673555 := bstep (se 1 (by rfl) ⟨3505166, by rfl⟩ : syracuseStep 4673555 = 7010333) B7010333
theorem B3115703 : Blo 2075435 3115703 := bstep (se 1 (by rfl) ⟨2336777, by rfl⟩ : syracuseStep 3115703 = 4673555) B4673555
theorem B2077135 : Blo 2075435 2077135 := bstep (se 1 (by rfl) ⟨1557851, by rfl⟩ : syracuseStep 2077135 = 3115703) B3115703
theorem B3115709 : Blo 2075435 3115709 := bbase (se 3 (by rfl) ⟨584195, by rfl⟩ : syracuseStep 3115709 = 1168391) (by norm_num)
theorem B2077139 : Blo 2075435 2077139 := bstep (se 1 (by rfl) ⟨1557854, by rfl⟩ : syracuseStep 2077139 = 3115709) B3115709
theorem B4673573 : Blo 2075435 4673573 := bbase (se 4 (by rfl) ⟨438147, by rfl⟩ : syracuseStep 4673573 = 876295) (by norm_num)
theorem B3115715 : Blo 2075435 3115715 := bstep (se 1 (by rfl) ⟨2336786, by rfl⟩ : syracuseStep 3115715 = 4673573) B4673573
theorem B2077143 : Blo 2075435 2077143 := bstep (se 1 (by rfl) ⟨1557857, by rfl⟩ : syracuseStep 2077143 = 3115715) B3115715
theorem B5257781 : Blo 2075435 5257781 := bbase (se 5 (by rfl) ⟨246458, by rfl⟩ : syracuseStep 5257781 = 492917) (by norm_num)
theorem B3505187 : Blo 2075435 3505187 := bstep (se 1 (by rfl) ⟨2628890, by rfl⟩ : syracuseStep 3505187 = 5257781) B5257781
theorem B2336791 : Blo 2075435 2336791 := bstep (se 1 (by rfl) ⟨1752593, by rfl⟩ : syracuseStep 2336791 = 3505187) B3505187
theorem B3115721 : Blo 2075435 3115721 := bstep (se 2 (by rfl) ⟨1168395, by rfl⟩ : syracuseStep 3115721 = 2336791) B2336791
theorem B2077147 : Blo 2075435 2077147 := bstep (se 1 (by rfl) ⟨1557860, by rfl⟩ : syracuseStep 2077147 = 3115721) B3115721
theorem B9981589 : Blo 2075435 9981589 := bbase (se 6 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 9981589 = 467887) (by norm_num)
theorem B13308785 : Blo 2075435 13308785 := bstep (se 2 (by rfl) ⟨4990794, by rfl⟩ : syracuseStep 13308785 = 9981589) B9981589
theorem B8872523 : Blo 2075435 8872523 := bstep (se 1 (by rfl) ⟨6654392, by rfl⟩ : syracuseStep 8872523 = 13308785) B13308785
theorem B5915015 : Blo 2075435 5915015 := bstep (se 1 (by rfl) ⟨4436261, by rfl⟩ : syracuseStep 5915015 = 8872523) B8872523
theorem B3943343 : Blo 2075435 3943343 := bstep (se 1 (by rfl) ⟨2957507, by rfl⟩ : syracuseStep 3943343 = 5915015) B5915015
theorem B10515581 : Blo 2075435 10515581 := bstep (se 3 (by rfl) ⟨1971671, by rfl⟩ : syracuseStep 10515581 = 3943343) B3943343
theorem B7010387 : Blo 2075435 7010387 := bstep (se 1 (by rfl) ⟨5257790, by rfl⟩ : syracuseStep 7010387 = 10515581) B10515581
theorem B4673591 : Blo 2075435 4673591 := bstep (se 1 (by rfl) ⟨3505193, by rfl⟩ : syracuseStep 4673591 = 7010387) B7010387
theorem B3115727 : Blo 2075435 3115727 := bstep (se 1 (by rfl) ⟨2336795, by rfl⟩ : syracuseStep 3115727 = 4673591) B4673591
theorem B2077151 : Blo 2075435 2077151 := bstep (se 1 (by rfl) ⟨1557863, by rfl⟩ : syracuseStep 2077151 = 3115727) B3115727
theorem B3115733 : Blo 2075435 3115733 := bbase (se 7 (by rfl) ⟨36512, by rfl⟩ : syracuseStep 3115733 = 73025) (by norm_num)
theorem B2077155 : Blo 2075435 2077155 := bstep (se 1 (by rfl) ⟨1557866, by rfl⟩ : syracuseStep 2077155 = 3115733) B3115733
theorem B6316501 : Blo 2075435 6316501 := bbase (se 7 (by rfl) ⟨74021, by rfl⟩ : syracuseStep 6316501 = 148043) (by norm_num)
theorem B8422001 : Blo 2075435 8422001 := bstep (se 2 (by rfl) ⟨3158250, by rfl⟩ : syracuseStep 8422001 = 6316501) B6316501
theorem B5614667 : Blo 2075435 5614667 := bstep (se 1 (by rfl) ⟨4211000, by rfl⟩ : syracuseStep 5614667 = 8422001) B8422001
theorem B3743111 : Blo 2075435 3743111 := bstep (se 1 (by rfl) ⟨2807333, by rfl⟩ : syracuseStep 3743111 = 5614667) B5614667
theorem B9981629 : Blo 2075435 9981629 := bstep (se 3 (by rfl) ⟨1871555, by rfl⟩ : syracuseStep 9981629 = 3743111) B3743111
theorem B6654419 : Blo 2075435 6654419 := bstep (se 1 (by rfl) ⟨4990814, by rfl⟩ : syracuseStep 6654419 = 9981629) B9981629
theorem B4436279 : Blo 2075435 4436279 := bstep (se 1 (by rfl) ⟨3327209, by rfl⟩ : syracuseStep 4436279 = 6654419) B6654419
theorem B2957519 : Blo 2075435 2957519 := bstep (se 1 (by rfl) ⟨2218139, by rfl⟩ : syracuseStep 2957519 = 4436279) B4436279
theorem B7886717 : Blo 2075435 7886717 := bstep (se 3 (by rfl) ⟨1478759, by rfl⟩ : syracuseStep 7886717 = 2957519) B2957519
theorem B5257811 : Blo 2075435 5257811 := bstep (se 1 (by rfl) ⟨3943358, by rfl⟩ : syracuseStep 5257811 = 7886717) B7886717
theorem B3505207 : Blo 2075435 3505207 := bstep (se 1 (by rfl) ⟨2628905, by rfl⟩ : syracuseStep 3505207 = 5257811) B5257811
theorem B4673609 : Blo 2075435 4673609 := bstep (se 2 (by rfl) ⟨1752603, by rfl⟩ : syracuseStep 4673609 = 3505207) B3505207
theorem B3115739 : Blo 2075435 3115739 := bstep (se 1 (by rfl) ⟨2336804, by rfl⟩ : syracuseStep 3115739 = 4673609) B4673609
theorem B2077159 : Blo 2075435 2077159 := bstep (se 1 (by rfl) ⟨1557869, by rfl⟩ : syracuseStep 2077159 = 3115739) B3115739
theorem B2336809 : Blo 2075435 2336809 := bbase (se 2 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 2336809 = 1752607) (by norm_num)
theorem B3115745 : Blo 2075435 3115745 := bstep (se 2 (by rfl) ⟨1168404, by rfl⟩ : syracuseStep 3115745 = 2336809) B2336809
theorem B2077163 : Blo 2075435 2077163 := bstep (se 1 (by rfl) ⟨1557872, by rfl⟩ : syracuseStep 2077163 = 3115745) B3115745
theorem B2192869 : Blo 2075435 2192869 := bbase (se 4 (by rfl) ⟨205581, by rfl⟩ : syracuseStep 2192869 = 411163) (by norm_num)
theorem B2923825 : Blo 2075435 2923825 := bstep (se 2 (by rfl) ⟨1096434, by rfl⟩ : syracuseStep 2923825 = 2192869) B2192869
theorem B3898433 : Blo 2075435 3898433 := bstep (se 2 (by rfl) ⟨1461912, by rfl⟩ : syracuseStep 3898433 = 2923825) B2923825
theorem B10395821 : Blo 2075435 10395821 := bstep (se 3 (by rfl) ⟨1949216, by rfl⟩ : syracuseStep 10395821 = 3898433) B3898433
theorem B27722189 : Blo 2075435 27722189 := bstep (se 3 (by rfl) ⟨5197910, by rfl⟩ : syracuseStep 27722189 = 10395821) B10395821
theorem B18481459 : Blo 2075435 18481459 := bstep (se 1 (by rfl) ⟨13861094, by rfl⟩ : syracuseStep 18481459 = 27722189) B27722189
theorem B24641945 : Blo 2075435 24641945 := bstep (se 2 (by rfl) ⟨9240729, by rfl⟩ : syracuseStep 24641945 = 18481459) B18481459
theorem B16427963 : Blo 2075435 16427963 := bstep (se 1 (by rfl) ⟨12320972, by rfl⟩ : syracuseStep 16427963 = 24641945) B24641945
theorem B10951975 : Blo 2075435 10951975 := bstep (se 1 (by rfl) ⟨8213981, by rfl⟩ : syracuseStep 10951975 = 16427963) B16427963
theorem B58410533 : Blo 2075435 58410533 := bstep (se 4 (by rfl) ⟨5475987, by rfl⟩ : syracuseStep 58410533 = 10951975) B10951975
theorem B38940355 : Blo 2075435 38940355 := bstep (se 1 (by rfl) ⟨29205266, by rfl⟩ : syracuseStep 38940355 = 58410533) B58410533
theorem B51920473 : Blo 2075435 51920473 := bstep (se 2 (by rfl) ⟨19470177, by rfl⟩ : syracuseStep 51920473 = 38940355) B38940355
theorem B69227297 : Blo 2075435 69227297 := bstep (se 2 (by rfl) ⟨25960236, by rfl⟩ : syracuseStep 69227297 = 51920473) B51920473
theorem B46151531 : Blo 2075435 46151531 := bstep (se 1 (by rfl) ⟨34613648, by rfl⟩ : syracuseStep 46151531 = 69227297) B69227297
theorem B30767687 : Blo 2075435 30767687 := bstep (se 1 (by rfl) ⟨23075765, by rfl⟩ : syracuseStep 30767687 = 46151531) B46151531
theorem B20511791 : Blo 2075435 20511791 := bstep (se 1 (by rfl) ⟨15383843, by rfl⟩ : syracuseStep 20511791 = 30767687) B30767687
theorem B13674527 : Blo 2075435 13674527 := bstep (se 1 (by rfl) ⟨10255895, by rfl⟩ : syracuseStep 13674527 = 20511791) B20511791
theorem B9116351 : Blo 2075435 9116351 := bstep (se 1 (by rfl) ⟨6837263, by rfl⟩ : syracuseStep 9116351 = 13674527) B13674527
theorem B6077567 : Blo 2075435 6077567 := bstep (se 1 (by rfl) ⟨4558175, by rfl⟩ : syracuseStep 6077567 = 9116351) B9116351
theorem B4051711 : Blo 2075435 4051711 := bstep (se 1 (by rfl) ⟨3038783, by rfl⟩ : syracuseStep 4051711 = 6077567) B6077567
theorem B21609125 : Blo 2075435 21609125 := bstep (se 4 (by rfl) ⟨2025855, by rfl⟩ : syracuseStep 21609125 = 4051711) B4051711
theorem B14406083 : Blo 2075435 14406083 := bstep (se 1 (by rfl) ⟨10804562, by rfl⟩ : syracuseStep 14406083 = 21609125) B21609125
theorem B9604055 : Blo 2075435 9604055 := bstep (se 1 (by rfl) ⟨7203041, by rfl⟩ : syracuseStep 9604055 = 14406083) B14406083
theorem B25610813 : Blo 2075435 25610813 := bstep (se 3 (by rfl) ⟨4802027, by rfl⟩ : syracuseStep 25610813 = 9604055) B9604055
theorem B17073875 : Blo 2075435 17073875 := bstep (se 1 (by rfl) ⟨12805406, by rfl⟩ : syracuseStep 17073875 = 25610813) B25610813
theorem B45530333 : Blo 2075435 45530333 := bstep (se 3 (by rfl) ⟨8536937, by rfl⟩ : syracuseStep 45530333 = 17073875) B17073875
theorem B30353555 : Blo 2075435 30353555 := bstep (se 1 (by rfl) ⟨22765166, by rfl⟩ : syracuseStep 30353555 = 45530333) B45530333
theorem B20235703 : Blo 2075435 20235703 := bstep (se 1 (by rfl) ⟨15176777, by rfl⟩ : syracuseStep 20235703 = 30353555) B30353555
theorem B26980937 : Blo 2075435 26980937 := bstep (se 2 (by rfl) ⟨10117851, by rfl⟩ : syracuseStep 26980937 = 20235703) B20235703
theorem B17987291 : Blo 2075435 17987291 := bstep (se 1 (by rfl) ⟨13490468, by rfl⟩ : syracuseStep 17987291 = 26980937) B26980937
theorem B11991527 : Blo 2075435 11991527 := bstep (se 1 (by rfl) ⟨8993645, by rfl⟩ : syracuseStep 11991527 = 17987291) B17987291
theorem B7994351 : Blo 2075435 7994351 := bstep (se 1 (by rfl) ⟨5995763, by rfl⟩ : syracuseStep 7994351 = 11991527) B11991527
theorem B5329567 : Blo 2075435 5329567 := bstep (se 1 (by rfl) ⟨3997175, by rfl⟩ : syracuseStep 5329567 = 7994351) B7994351
theorem B28424357 : Blo 2075435 28424357 := bstep (se 4 (by rfl) ⟨2664783, by rfl⟩ : syracuseStep 28424357 = 5329567) B5329567
theorem B18949571 : Blo 2075435 18949571 := bstep (se 1 (by rfl) ⟨14212178, by rfl⟩ : syracuseStep 18949571 = 28424357) B28424357
theorem B12633047 : Blo 2075435 12633047 := bstep (se 1 (by rfl) ⟨9474785, by rfl⟩ : syracuseStep 12633047 = 18949571) B18949571
theorem B8422031 : Blo 2075435 8422031 := bstep (se 1 (by rfl) ⟨6316523, by rfl⟩ : syracuseStep 8422031 = 12633047) B12633047
theorem B5614687 : Blo 2075435 5614687 := bstep (se 1 (by rfl) ⟨4211015, by rfl⟩ : syracuseStep 5614687 = 8422031) B8422031
theorem B29944997 : Blo 2075435 29944997 := bstep (se 4 (by rfl) ⟨2807343, by rfl⟩ : syracuseStep 29944997 = 5614687) B5614687
theorem B19963331 : Blo 2075435 19963331 := bstep (se 1 (by rfl) ⟨14972498, by rfl⟩ : syracuseStep 19963331 = 29944997) B29944997
theorem B13308887 : Blo 2075435 13308887 := bstep (se 1 (by rfl) ⟨9981665, by rfl⟩ : syracuseStep 13308887 = 19963331) B19963331
theorem B8872591 : Blo 2075435 8872591 := bstep (se 1 (by rfl) ⟨6654443, by rfl⟩ : syracuseStep 8872591 = 13308887) B13308887
theorem B11830121 : Blo 2075435 11830121 := bstep (se 2 (by rfl) ⟨4436295, by rfl⟩ : syracuseStep 11830121 = 8872591) B8872591
theorem B7886747 : Blo 2075435 7886747 := bstep (se 1 (by rfl) ⟨5915060, by rfl⟩ : syracuseStep 7886747 = 11830121) B11830121
theorem B5257831 : Blo 2075435 5257831 := bstep (se 1 (by rfl) ⟨3943373, by rfl⟩ : syracuseStep 5257831 = 7886747) B7886747
theorem B7010441 : Blo 2075435 7010441 := bstep (se 2 (by rfl) ⟨2628915, by rfl⟩ : syracuseStep 7010441 = 5257831) B5257831
theorem B4673627 : Blo 2075435 4673627 := bstep (se 1 (by rfl) ⟨3505220, by rfl⟩ : syracuseStep 4673627 = 7010441) B7010441
theorem B3115751 : Blo 2075435 3115751 := bstep (se 1 (by rfl) ⟨2336813, by rfl⟩ : syracuseStep 3115751 = 4673627) B4673627
theorem B2077167 : Blo 2075435 2077167 := bstep (se 1 (by rfl) ⟨1557875, by rfl⟩ : syracuseStep 2077167 = 3115751) B3115751
theorem B3115757 : Blo 2075435 3115757 := bbase (se 3 (by rfl) ⟨584204, by rfl⟩ : syracuseStep 3115757 = 1168409) (by norm_num)
theorem B2077171 : Blo 2075435 2077171 := bstep (se 1 (by rfl) ⟨1557878, by rfl⟩ : syracuseStep 2077171 = 3115757) B3115757
theorem B4673645 : Blo 2075435 4673645 := bbase (se 3 (by rfl) ⟨876308, by rfl⟩ : syracuseStep 4673645 = 1752617) (by norm_num)
theorem B3115763 : Blo 2075435 3115763 := bstep (se 1 (by rfl) ⟨2336822, by rfl⟩ : syracuseStep 3115763 = 4673645) B4673645
theorem B2077175 : Blo 2075435 2077175 := bstep (se 1 (by rfl) ⟨1557881, by rfl⟩ : syracuseStep 2077175 = 3115763) B3115763
theorem B3943397 : Blo 2075435 3943397 := bbase (se 4 (by rfl) ⟨369693, by rfl⟩ : syracuseStep 3943397 = 739387) (by norm_num)
theorem B2628931 : Blo 2075435 2628931 := bstep (se 1 (by rfl) ⟨1971698, by rfl⟩ : syracuseStep 2628931 = 3943397) B3943397
theorem B3505241 : Blo 2075435 3505241 := bstep (se 2 (by rfl) ⟨1314465, by rfl⟩ : syracuseStep 3505241 = 2628931) B2628931
theorem B2336827 : Blo 2075435 2336827 := bstep (se 1 (by rfl) ⟨1752620, by rfl⟩ : syracuseStep 2336827 = 3505241) B3505241
theorem B3115769 : Blo 2075435 3115769 := bstep (se 2 (by rfl) ⟨1168413, by rfl⟩ : syracuseStep 3115769 = 2336827) B2336827
theorem B2077179 : Blo 2075435 2077179 := bstep (se 1 (by rfl) ⟨1557884, by rfl⟩ : syracuseStep 2077179 = 3115769) B3115769
theorem B2807365 : Blo 2075435 2807365 := bbase (se 4 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 2807365 = 526381) (by norm_num)
theorem B3743153 : Blo 2075435 3743153 := bstep (se 2 (by rfl) ⟨1403682, by rfl⟩ : syracuseStep 3743153 = 2807365) B2807365
theorem B39926965 : Blo 2075435 39926965 := bstep (se 5 (by rfl) ⟨1871576, by rfl⟩ : syracuseStep 39926965 = 3743153) B3743153
theorem B53235953 : Blo 2075435 53235953 := bstep (se 2 (by rfl) ⟨19963482, by rfl⟩ : syracuseStep 53235953 = 39926965) B39926965
theorem B35490635 : Blo 2075435 35490635 := bstep (se 1 (by rfl) ⟨26617976, by rfl⟩ : syracuseStep 35490635 = 53235953) B53235953
theorem B23660423 : Blo 2075435 23660423 := bstep (se 1 (by rfl) ⟨17745317, by rfl⟩ : syracuseStep 23660423 = 35490635) B35490635
theorem B15773615 : Blo 2075435 15773615 := bstep (se 1 (by rfl) ⟨11830211, by rfl⟩ : syracuseStep 15773615 = 23660423) B23660423
theorem B10515743 : Blo 2075435 10515743 := bstep (se 1 (by rfl) ⟨7886807, by rfl⟩ : syracuseStep 10515743 = 15773615) B15773615
theorem B7010495 : Blo 2075435 7010495 := bstep (se 1 (by rfl) ⟨5257871, by rfl⟩ : syracuseStep 7010495 = 10515743) B10515743
theorem B4673663 : Blo 2075435 4673663 := bstep (se 1 (by rfl) ⟨3505247, by rfl⟩ : syracuseStep 4673663 = 7010495) B7010495
theorem B3115775 : Blo 2075435 3115775 := bstep (se 1 (by rfl) ⟨2336831, by rfl⟩ : syracuseStep 3115775 = 4673663) B4673663
theorem B2077183 : Blo 2075435 2077183 := bstep (se 1 (by rfl) ⟨1557887, by rfl⟩ : syracuseStep 2077183 = 3115775) B3115775
theorem B3115781 : Blo 2075435 3115781 := bbase (se 4 (by rfl) ⟨292104, by rfl⟩ : syracuseStep 3115781 = 584209) (by norm_num)
theorem B2077187 : Blo 2075435 2077187 := bstep (se 1 (by rfl) ⟨1557890, by rfl⟩ : syracuseStep 2077187 = 3115781) B3115781
theorem B3505261 : Blo 2075435 3505261 := bbase (se 3 (by rfl) ⟨657236, by rfl⟩ : syracuseStep 3505261 = 1314473) (by norm_num)
theorem B4673681 : Blo 2075435 4673681 := bstep (se 2 (by rfl) ⟨1752630, by rfl⟩ : syracuseStep 4673681 = 3505261) B3505261
theorem B3115787 : Blo 2075435 3115787 := bstep (se 1 (by rfl) ⟨2336840, by rfl⟩ : syracuseStep 3115787 = 4673681) B4673681
theorem B2077191 : Blo 2075435 2077191 := bstep (se 1 (by rfl) ⟨1557893, by rfl⟩ : syracuseStep 2077191 = 3115787) B3115787
theorem B2336845 : Blo 2075435 2336845 := bbase (se 3 (by rfl) ⟨438158, by rfl⟩ : syracuseStep 2336845 = 876317) (by norm_num)
theorem B3115793 : Blo 2075435 3115793 := bstep (se 2 (by rfl) ⟨1168422, by rfl⟩ : syracuseStep 3115793 = 2336845) B2336845
theorem B2077195 : Blo 2075435 2077195 := bstep (se 1 (by rfl) ⟨1557896, by rfl⟩ : syracuseStep 2077195 = 3115793) B3115793
theorem B7010549 : Blo 2075435 7010549 := bbase (se 5 (by rfl) ⟨328619, by rfl⟩ : syracuseStep 7010549 = 657239) (by norm_num)
theorem B4673699 : Blo 2075435 4673699 := bstep (se 1 (by rfl) ⟨3505274, by rfl⟩ : syracuseStep 4673699 = 7010549) B7010549
theorem B3115799 : Blo 2075435 3115799 := bstep (se 1 (by rfl) ⟨2336849, by rfl⟩ : syracuseStep 3115799 = 4673699) B4673699
theorem B2077199 : Blo 2075435 2077199 := bstep (se 1 (by rfl) ⟨1557899, by rfl⟩ : syracuseStep 2077199 = 3115799) B3115799
theorem B3115805 : Blo 2075435 3115805 := bbase (se 3 (by rfl) ⟨584213, by rfl⟩ : syracuseStep 3115805 = 1168427) (by norm_num)
theorem B2077203 : Blo 2075435 2077203 := bstep (se 1 (by rfl) ⟨1557902, by rfl⟩ : syracuseStep 2077203 = 3115805) B3115805
theorem B4673717 : Blo 2075435 4673717 := bbase (se 5 (by rfl) ⟨219080, by rfl⟩ : syracuseStep 4673717 = 438161) (by norm_num)
theorem B3115811 : Blo 2075435 3115811 := bstep (se 1 (by rfl) ⟨2336858, by rfl⟩ : syracuseStep 3115811 = 4673717) B4673717
theorem B2077207 : Blo 2075435 2077207 := bstep (se 1 (by rfl) ⟨1557905, by rfl⟩ : syracuseStep 2077207 = 3115811) B3115811
theorem B3327293 : Blo 2075435 3327293 := bbase (se 3 (by rfl) ⟨623867, by rfl⟩ : syracuseStep 3327293 = 1247735) (by norm_num)
theorem B2218195 : Blo 2075435 2218195 := bstep (se 1 (by rfl) ⟨1663646, by rfl⟩ : syracuseStep 2218195 = 3327293) B3327293
theorem B11830373 : Blo 2075435 11830373 := bstep (se 4 (by rfl) ⟨1109097, by rfl⟩ : syracuseStep 11830373 = 2218195) B2218195
theorem B7886915 : Blo 2075435 7886915 := bstep (se 1 (by rfl) ⟨5915186, by rfl⟩ : syracuseStep 7886915 = 11830373) B11830373
theorem B5257943 : Blo 2075435 5257943 := bstep (se 1 (by rfl) ⟨3943457, by rfl⟩ : syracuseStep 5257943 = 7886915) B7886915
theorem B3505295 : Blo 2075435 3505295 := bstep (se 1 (by rfl) ⟨2628971, by rfl⟩ : syracuseStep 3505295 = 5257943) B5257943
theorem B2336863 : Blo 2075435 2336863 := bstep (se 1 (by rfl) ⟨1752647, by rfl⟩ : syracuseStep 2336863 = 3505295) B3505295
theorem B3115817 : Blo 2075435 3115817 := bstep (se 2 (by rfl) ⟨1168431, by rfl⟩ : syracuseStep 3115817 = 2336863) B2336863
theorem B2077211 : Blo 2075435 2077211 := bstep (se 1 (by rfl) ⟨1557908, by rfl⟩ : syracuseStep 2077211 = 3115817) B3115817
theorem B4990949 : Blo 2075435 4990949 := bbase (se 4 (by rfl) ⟨467901, by rfl⟩ : syracuseStep 4990949 = 935803) (by norm_num)
theorem B3327299 : Blo 2075435 3327299 := bstep (se 1 (by rfl) ⟨2495474, by rfl⟩ : syracuseStep 3327299 = 4990949) B4990949
theorem B2218199 : Blo 2075435 2218199 := bstep (se 1 (by rfl) ⟨1663649, by rfl⟩ : syracuseStep 2218199 = 3327299) B3327299
theorem B5915197 : Blo 2075435 5915197 := bstep (se 3 (by rfl) ⟨1109099, by rfl⟩ : syracuseStep 5915197 = 2218199) B2218199
theorem B7886929 : Blo 2075435 7886929 := bstep (se 2 (by rfl) ⟨2957598, by rfl⟩ : syracuseStep 7886929 = 5915197) B5915197
theorem B10515905 : Blo 2075435 10515905 := bstep (se 2 (by rfl) ⟨3943464, by rfl⟩ : syracuseStep 10515905 = 7886929) B7886929
theorem B7010603 : Blo 2075435 7010603 := bstep (se 1 (by rfl) ⟨5257952, by rfl⟩ : syracuseStep 7010603 = 10515905) B10515905
theorem B4673735 : Blo 2075435 4673735 := bstep (se 1 (by rfl) ⟨3505301, by rfl⟩ : syracuseStep 4673735 = 7010603) B7010603
theorem B3115823 : Blo 2075435 3115823 := bstep (se 1 (by rfl) ⟨2336867, by rfl⟩ : syracuseStep 3115823 = 4673735) B4673735
theorem B2077215 : Blo 2075435 2077215 := bstep (se 1 (by rfl) ⟨1557911, by rfl⟩ : syracuseStep 2077215 = 3115823) B3115823
theorem B3115829 : Blo 2075435 3115829 := bbase (se 5 (by rfl) ⟨146054, by rfl⟩ : syracuseStep 3115829 = 292109) (by norm_num)
theorem B2077219 : Blo 2075435 2077219 := bstep (se 1 (by rfl) ⟨1557914, by rfl⟩ : syracuseStep 2077219 = 3115829) B3115829
theorem B5257973 : Blo 2075435 5257973 := bbase (se 5 (by rfl) ⟨246467, by rfl⟩ : syracuseStep 5257973 = 492935) (by norm_num)
theorem B3505315 : Blo 2075435 3505315 := bstep (se 1 (by rfl) ⟨2628986, by rfl⟩ : syracuseStep 3505315 = 5257973) B5257973
theorem B4673753 : Blo 2075435 4673753 := bstep (se 2 (by rfl) ⟨1752657, by rfl⟩ : syracuseStep 4673753 = 3505315) B3505315
theorem B3115835 : Blo 2075435 3115835 := bstep (se 1 (by rfl) ⟨2336876, by rfl⟩ : syracuseStep 3115835 = 4673753) B4673753
theorem B2077223 : Blo 2075435 2077223 := bstep (se 1 (by rfl) ⟨1557917, by rfl⟩ : syracuseStep 2077223 = 3115835) B3115835
theorem B2336881 : Blo 2075435 2336881 := bbase (se 2 (by rfl) ⟨876330, by rfl⟩ : syracuseStep 2336881 = 1752661) (by norm_num)
theorem B3115841 : Blo 2075435 3115841 := bstep (se 2 (by rfl) ⟨1168440, by rfl⟩ : syracuseStep 3115841 = 2336881) B2336881
theorem B2077227 : Blo 2075435 2077227 := bstep (se 1 (by rfl) ⟨1557920, by rfl⟩ : syracuseStep 2077227 = 3115841) B3115841
theorem B2105573 : Blo 2075435 2105573 := bbase (se 4 (by rfl) ⟨197397, by rfl⟩ : syracuseStep 2105573 = 394795) (by norm_num)
theorem B5614861 : Blo 2075435 5614861 := bstep (se 3 (by rfl) ⟨1052786, by rfl⟩ : syracuseStep 5614861 = 2105573) B2105573
theorem B7486481 : Blo 2075435 7486481 := bstep (se 2 (by rfl) ⟨2807430, by rfl⟩ : syracuseStep 7486481 = 5614861) B5614861
theorem B4990987 : Blo 2075435 4990987 := bstep (se 1 (by rfl) ⟨3743240, by rfl⟩ : syracuseStep 4990987 = 7486481) B7486481
theorem B6654649 : Blo 2075435 6654649 := bstep (se 2 (by rfl) ⟨2495493, by rfl⟩ : syracuseStep 6654649 = 4990987) B4990987
theorem B8872865 : Blo 2075435 8872865 := bstep (se 2 (by rfl) ⟨3327324, by rfl⟩ : syracuseStep 8872865 = 6654649) B6654649
theorem B5915243 : Blo 2075435 5915243 := bstep (se 1 (by rfl) ⟨4436432, by rfl⟩ : syracuseStep 5915243 = 8872865) B8872865
theorem B3943495 : Blo 2075435 3943495 := bstep (se 1 (by rfl) ⟨2957621, by rfl⟩ : syracuseStep 3943495 = 5915243) B5915243
theorem B5257993 : Blo 2075435 5257993 := bstep (se 2 (by rfl) ⟨1971747, by rfl⟩ : syracuseStep 5257993 = 3943495) B3943495
theorem B7010657 : Blo 2075435 7010657 := bstep (se 2 (by rfl) ⟨2628996, by rfl⟩ : syracuseStep 7010657 = 5257993) B5257993
theorem B4673771 : Blo 2075435 4673771 := bstep (se 1 (by rfl) ⟨3505328, by rfl⟩ : syracuseStep 4673771 = 7010657) B7010657
theorem B3115847 : Blo 2075435 3115847 := bstep (se 1 (by rfl) ⟨2336885, by rfl⟩ : syracuseStep 3115847 = 4673771) B4673771
theorem B2077231 : Blo 2075435 2077231 := bstep (se 1 (by rfl) ⟨1557923, by rfl⟩ : syracuseStep 2077231 = 3115847) B3115847
theorem B3115853 : Blo 2075435 3115853 := bbase (se 3 (by rfl) ⟨584222, by rfl⟩ : syracuseStep 3115853 = 1168445) (by norm_num)
theorem B2077235 : Blo 2075435 2077235 := bstep (se 1 (by rfl) ⟨1557926, by rfl⟩ : syracuseStep 2077235 = 3115853) B3115853
theorem B4673789 : Blo 2075435 4673789 := bbase (se 3 (by rfl) ⟨876335, by rfl⟩ : syracuseStep 4673789 = 1752671) (by norm_num)
theorem B3115859 : Blo 2075435 3115859 := bstep (se 1 (by rfl) ⟨2336894, by rfl⟩ : syracuseStep 3115859 = 4673789) B4673789
theorem B2077239 : Blo 2075435 2077239 := bstep (se 1 (by rfl) ⟨1557929, by rfl⟩ : syracuseStep 2077239 = 3115859) B3115859
theorem B3505349 : Blo 2075435 3505349 := bbase (se 4 (by rfl) ⟨328626, by rfl⟩ : syracuseStep 3505349 = 657253) (by norm_num)
theorem B2336899 : Blo 2075435 2336899 := bstep (se 1 (by rfl) ⟨1752674, by rfl⟩ : syracuseStep 2336899 = 3505349) B3505349
theorem B3115865 : Blo 2075435 3115865 := bstep (se 2 (by rfl) ⟨1168449, by rfl⟩ : syracuseStep 3115865 = 2336899) B2336899
theorem B2077243 : Blo 2075435 2077243 := bstep (se 1 (by rfl) ⟨1557932, by rfl⟩ : syracuseStep 2077243 = 3115865) B3115865
theorem B15774101 : Blo 2075435 15774101 := bbase (se 6 (by rfl) ⟨369705, by rfl⟩ : syracuseStep 15774101 = 739411) (by norm_num)
theorem B10516067 : Blo 2075435 10516067 := bstep (se 1 (by rfl) ⟨7887050, by rfl⟩ : syracuseStep 10516067 = 15774101) B15774101
theorem B7010711 : Blo 2075435 7010711 := bstep (se 1 (by rfl) ⟨5258033, by rfl⟩ : syracuseStep 7010711 = 10516067) B10516067
theorem B4673807 : Blo 2075435 4673807 := bstep (se 1 (by rfl) ⟨3505355, by rfl⟩ : syracuseStep 4673807 = 7010711) B7010711
theorem B3115871 : Blo 2075435 3115871 := bstep (se 1 (by rfl) ⟨2336903, by rfl⟩ : syracuseStep 3115871 = 4673807) B4673807
theorem B2077247 : Blo 2075435 2077247 := bstep (se 1 (by rfl) ⟨1557935, by rfl⟩ : syracuseStep 2077247 = 3115871) B3115871
theorem B3115877 : Blo 2075435 3115877 := bbase (se 4 (by rfl) ⟨292113, by rfl⟩ : syracuseStep 3115877 = 584227) (by norm_num)
theorem B2077251 : Blo 2075435 2077251 := bstep (se 1 (by rfl) ⟨1557938, by rfl⟩ : syracuseStep 2077251 = 3115877) B3115877
theorem B3943541 : Blo 2075435 3943541 := bbase (se 5 (by rfl) ⟨184853, by rfl⟩ : syracuseStep 3943541 = 369707) (by norm_num)
theorem B2629027 : Blo 2075435 2629027 := bstep (se 1 (by rfl) ⟨1971770, by rfl⟩ : syracuseStep 2629027 = 3943541) B3943541
theorem B3505369 : Blo 2075435 3505369 := bstep (se 2 (by rfl) ⟨1314513, by rfl⟩ : syracuseStep 3505369 = 2629027) B2629027
theorem B4673825 : Blo 2075435 4673825 := bstep (se 2 (by rfl) ⟨1752684, by rfl⟩ : syracuseStep 4673825 = 3505369) B3505369
theorem B3115883 : Blo 2075435 3115883 := bstep (se 1 (by rfl) ⟨2336912, by rfl⟩ : syracuseStep 3115883 = 4673825) B4673825
theorem B2077255 : Blo 2075435 2077255 := bstep (se 1 (by rfl) ⟨1557941, by rfl⟩ : syracuseStep 2077255 = 3115883) B3115883
theorem B2336917 : Blo 2075435 2336917 := bbase (se 6 (by rfl) ⟨54771, by rfl⟩ : syracuseStep 2336917 = 109543) (by norm_num)
theorem B3115889 : Blo 2075435 3115889 := bstep (se 2 (by rfl) ⟨1168458, by rfl⟩ : syracuseStep 3115889 = 2336917) B2336917
theorem B2077259 : Blo 2075435 2077259 := bstep (se 1 (by rfl) ⟨1557944, by rfl⟩ : syracuseStep 2077259 = 3115889) B3115889
theorem B2629037 : Blo 2075435 2629037 := bbase (se 3 (by rfl) ⟨492944, by rfl⟩ : syracuseStep 2629037 = 985889) (by norm_num)
theorem B7010765 : Blo 2075435 7010765 := bstep (se 3 (by rfl) ⟨1314518, by rfl⟩ : syracuseStep 7010765 = 2629037) B2629037
theorem B4673843 : Blo 2075435 4673843 := bstep (se 1 (by rfl) ⟨3505382, by rfl⟩ : syracuseStep 4673843 = 7010765) B7010765
theorem B3115895 : Blo 2075435 3115895 := bstep (se 1 (by rfl) ⟨2336921, by rfl⟩ : syracuseStep 3115895 = 4673843) B4673843
theorem B2077263 : Blo 2075435 2077263 := bstep (se 1 (by rfl) ⟨1557947, by rfl⟩ : syracuseStep 2077263 = 3115895) B3115895
theorem B3115901 : Blo 2075435 3115901 := bbase (se 3 (by rfl) ⟨584231, by rfl⟩ : syracuseStep 3115901 = 1168463) (by norm_num)
theorem B2077267 : Blo 2075435 2077267 := bstep (se 1 (by rfl) ⟨1557950, by rfl⟩ : syracuseStep 2077267 = 3115901) B3115901
theorem B4673861 : Blo 2075435 4673861 := bbase (se 4 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 4673861 = 876349) (by norm_num)
theorem B3115907 : Blo 2075435 3115907 := bstep (se 1 (by rfl) ⟨2336930, by rfl⟩ : syracuseStep 3115907 = 4673861) B4673861
theorem B2077271 : Blo 2075435 2077271 := bstep (se 1 (by rfl) ⟨1557953, by rfl⟩ : syracuseStep 2077271 = 3115907) B3115907
theorem B4268693 : Blo 2075435 4268693 := bbase (se 6 (by rfl) ⟨100047, by rfl⟩ : syracuseStep 4268693 = 200095) (by norm_num)
theorem B2845795 : Blo 2075435 2845795 := bstep (se 1 (by rfl) ⟨2134346, by rfl⟩ : syracuseStep 2845795 = 4268693) B4268693
theorem B3794393 : Blo 2075435 3794393 := bstep (se 2 (by rfl) ⟨1422897, by rfl⟩ : syracuseStep 3794393 = 2845795) B2845795
theorem B2529595 : Blo 2075435 2529595 := bstep (se 1 (by rfl) ⟨1897196, by rfl⟩ : syracuseStep 2529595 = 3794393) B3794393
theorem B13491173 : Blo 2075435 13491173 := bstep (se 4 (by rfl) ⟨1264797, by rfl⟩ : syracuseStep 13491173 = 2529595) B2529595
theorem B8994115 : Blo 2075435 8994115 := bstep (se 1 (by rfl) ⟨6745586, by rfl⟩ : syracuseStep 8994115 = 13491173) B13491173
theorem B11992153 : Blo 2075435 11992153 := bstep (se 2 (by rfl) ⟨4497057, by rfl⟩ : syracuseStep 11992153 = 8994115) B8994115
theorem B15989537 : Blo 2075435 15989537 := bstep (se 2 (by rfl) ⟨5996076, by rfl⟩ : syracuseStep 15989537 = 11992153) B11992153
theorem B10659691 : Blo 2075435 10659691 := bstep (se 1 (by rfl) ⟨7994768, by rfl⟩ : syracuseStep 10659691 = 15989537) B15989537
theorem B14212921 : Blo 2075435 14212921 := bstep (se 2 (by rfl) ⟨5329845, by rfl⟩ : syracuseStep 14212921 = 10659691) B10659691
theorem B18950561 : Blo 2075435 18950561 := bstep (se 2 (by rfl) ⟨7106460, by rfl⟩ : syracuseStep 18950561 = 14212921) B14212921
theorem B12633707 : Blo 2075435 12633707 := bstep (se 1 (by rfl) ⟨9475280, by rfl⟩ : syracuseStep 12633707 = 18950561) B18950561
theorem B8422471 : Blo 2075435 8422471 := bstep (se 1 (by rfl) ⟨6316853, by rfl⟩ : syracuseStep 8422471 = 12633707) B12633707
theorem B11229961 : Blo 2075435 11229961 := bstep (se 2 (by rfl) ⟨4211235, by rfl⟩ : syracuseStep 11229961 = 8422471) B8422471
theorem B14973281 : Blo 2075435 14973281 := bstep (se 2 (by rfl) ⟨5614980, by rfl⟩ : syracuseStep 14973281 = 11229961) B11229961
theorem B9982187 : Blo 2075435 9982187 := bstep (se 1 (by rfl) ⟨7486640, by rfl⟩ : syracuseStep 9982187 = 14973281) B14973281
theorem B6654791 : Blo 2075435 6654791 := bstep (se 1 (by rfl) ⟨4991093, by rfl⟩ : syracuseStep 6654791 = 9982187) B9982187
theorem B4436527 : Blo 2075435 4436527 := bstep (se 1 (by rfl) ⟨3327395, by rfl⟩ : syracuseStep 4436527 = 6654791) B6654791
theorem B5915369 : Blo 2075435 5915369 := bstep (se 2 (by rfl) ⟨2218263, by rfl⟩ : syracuseStep 5915369 = 4436527) B4436527
theorem B3943579 : Blo 2075435 3943579 := bstep (se 1 (by rfl) ⟨2957684, by rfl⟩ : syracuseStep 3943579 = 5915369) B5915369
theorem B5258105 : Blo 2075435 5258105 := bstep (se 2 (by rfl) ⟨1971789, by rfl⟩ : syracuseStep 5258105 = 3943579) B3943579
theorem B3505403 : Blo 2075435 3505403 := bstep (se 1 (by rfl) ⟨2629052, by rfl⟩ : syracuseStep 3505403 = 5258105) B5258105
theorem B2336935 : Blo 2075435 2336935 := bstep (se 1 (by rfl) ⟨1752701, by rfl⟩ : syracuseStep 2336935 = 3505403) B3505403
theorem B3115913 : Blo 2075435 3115913 := bstep (se 2 (by rfl) ⟨1168467, by rfl⟩ : syracuseStep 3115913 = 2336935) B2336935
theorem B2077275 : Blo 2075435 2077275 := bstep (se 1 (by rfl) ⟨1557956, by rfl⟩ : syracuseStep 2077275 = 3115913) B3115913
theorem B10516229 : Blo 2075435 10516229 := bbase (se 4 (by rfl) ⟨985896, by rfl⟩ : syracuseStep 10516229 = 1971793) (by norm_num)
theorem B7010819 : Blo 2075435 7010819 := bstep (se 1 (by rfl) ⟨5258114, by rfl⟩ : syracuseStep 7010819 = 10516229) B10516229
theorem B4673879 : Blo 2075435 4673879 := bstep (se 1 (by rfl) ⟨3505409, by rfl⟩ : syracuseStep 4673879 = 7010819) B7010819
theorem B3115919 : Blo 2075435 3115919 := bstep (se 1 (by rfl) ⟨2336939, by rfl⟩ : syracuseStep 3115919 = 4673879) B4673879
theorem B2077279 : Blo 2075435 2077279 := bstep (se 1 (by rfl) ⟨1557959, by rfl⟩ : syracuseStep 2077279 = 3115919) B3115919
theorem B3115925 : Blo 2075435 3115925 := bbase (se 6 (by rfl) ⟨73029, by rfl⟩ : syracuseStep 3115925 = 146059) (by norm_num)
theorem B2077283 : Blo 2075435 2077283 := bstep (se 1 (by rfl) ⟨1557962, by rfl⟩ : syracuseStep 2077283 = 3115925) B3115925
theorem B11830805 : Blo 2075435 11830805 := bbase (se 6 (by rfl) ⟨277284, by rfl⟩ : syracuseStep 11830805 = 554569) (by norm_num)
theorem B7887203 : Blo 2075435 7887203 := bstep (se 1 (by rfl) ⟨5915402, by rfl⟩ : syracuseStep 7887203 = 11830805) B11830805
theorem B5258135 : Blo 2075435 5258135 := bstep (se 1 (by rfl) ⟨3943601, by rfl⟩ : syracuseStep 5258135 = 7887203) B7887203
theorem B3505423 : Blo 2075435 3505423 := bstep (se 1 (by rfl) ⟨2629067, by rfl⟩ : syracuseStep 3505423 = 5258135) B5258135
theorem B4673897 : Blo 2075435 4673897 := bstep (se 2 (by rfl) ⟨1752711, by rfl⟩ : syracuseStep 4673897 = 3505423) B3505423
theorem B3115931 : Blo 2075435 3115931 := bstep (se 1 (by rfl) ⟨2336948, by rfl⟩ : syracuseStep 3115931 = 4673897) B4673897
theorem B2077287 : Blo 2075435 2077287 := bstep (se 1 (by rfl) ⟨1557965, by rfl⟩ : syracuseStep 2077287 = 3115931) B3115931
theorem B2336953 : Blo 2075435 2336953 := bbase (se 2 (by rfl) ⟨876357, by rfl⟩ : syracuseStep 2336953 = 1752715) (by norm_num)
theorem B3115937 : Blo 2075435 3115937 := bstep (se 2 (by rfl) ⟨1168476, by rfl⟩ : syracuseStep 3115937 = 2336953) B2336953
theorem B2077291 : Blo 2075435 2077291 := bstep (se 1 (by rfl) ⟨1557968, by rfl⟩ : syracuseStep 2077291 = 3115937) B3115937
theorem B4991141 : Blo 2075435 4991141 := bbase (se 4 (by rfl) ⟨467919, by rfl⟩ : syracuseStep 4991141 = 935839) (by norm_num)
theorem B3327427 : Blo 2075435 3327427 := bstep (se 1 (by rfl) ⟨2495570, by rfl⟩ : syracuseStep 3327427 = 4991141) B4991141
theorem B4436569 : Blo 2075435 4436569 := bstep (se 2 (by rfl) ⟨1663713, by rfl⟩ : syracuseStep 4436569 = 3327427) B3327427
theorem B5915425 : Blo 2075435 5915425 := bstep (se 2 (by rfl) ⟨2218284, by rfl⟩ : syracuseStep 5915425 = 4436569) B4436569
theorem B7887233 : Blo 2075435 7887233 := bstep (se 2 (by rfl) ⟨2957712, by rfl⟩ : syracuseStep 7887233 = 5915425) B5915425
theorem B5258155 : Blo 2075435 5258155 := bstep (se 1 (by rfl) ⟨3943616, by rfl⟩ : syracuseStep 5258155 = 7887233) B7887233
theorem B7010873 : Blo 2075435 7010873 := bstep (se 2 (by rfl) ⟨2629077, by rfl⟩ : syracuseStep 7010873 = 5258155) B5258155
theorem B4673915 : Blo 2075435 4673915 := bstep (se 1 (by rfl) ⟨3505436, by rfl⟩ : syracuseStep 4673915 = 7010873) B7010873
theorem B3115943 : Blo 2075435 3115943 := bstep (se 1 (by rfl) ⟨2336957, by rfl⟩ : syracuseStep 3115943 = 4673915) B4673915
theorem B2077295 : Blo 2075435 2077295 := bstep (se 1 (by rfl) ⟨1557971, by rfl⟩ : syracuseStep 2077295 = 3115943) B3115943
theorem B3115949 : Blo 2075435 3115949 := bbase (se 3 (by rfl) ⟨584240, by rfl⟩ : syracuseStep 3115949 = 1168481) (by norm_num)
theorem B2077299 : Blo 2075435 2077299 := bstep (se 1 (by rfl) ⟨1557974, by rfl⟩ : syracuseStep 2077299 = 3115949) B3115949
theorem B4673933 : Blo 2075435 4673933 := bbase (se 3 (by rfl) ⟨876362, by rfl⟩ : syracuseStep 4673933 = 1752725) (by norm_num)
theorem B3115955 : Blo 2075435 3115955 := bstep (se 1 (by rfl) ⟨2336966, by rfl⟩ : syracuseStep 3115955 = 4673933) B4673933
theorem B2077303 : Blo 2075435 2077303 := bstep (se 1 (by rfl) ⟨1557977, by rfl⟩ : syracuseStep 2077303 = 3115955) B3115955
theorem B2629093 : Blo 2075435 2629093 := bbase (se 4 (by rfl) ⟨246477, by rfl⟩ : syracuseStep 2629093 = 492955) (by norm_num)
theorem B3505457 : Blo 2075435 3505457 := bstep (se 2 (by rfl) ⟨1314546, by rfl⟩ : syracuseStep 3505457 = 2629093) B2629093
theorem B2336971 : Blo 2075435 2336971 := bstep (se 1 (by rfl) ⟨1752728, by rfl⟩ : syracuseStep 2336971 = 3505457) B3505457
theorem B3115961 : Blo 2075435 3115961 := bstep (se 2 (by rfl) ⟨1168485, by rfl⟩ : syracuseStep 3115961 = 2336971) B2336971
theorem B2077307 : Blo 2075435 2077307 := bstep (se 1 (by rfl) ⟨1557980, by rfl⟩ : syracuseStep 2077307 = 3115961) B3115961
theorem B9116981 : Blo 2075435 9116981 := bbase (se 5 (by rfl) ⟨427358, by rfl⟩ : syracuseStep 9116981 = 854717) (by norm_num)
theorem B6077987 : Blo 2075435 6077987 := bstep (se 1 (by rfl) ⟨4558490, by rfl⟩ : syracuseStep 6077987 = 9116981) B9116981
theorem B4051991 : Blo 2075435 4051991 := bstep (se 1 (by rfl) ⟨3038993, by rfl⟩ : syracuseStep 4051991 = 6077987) B6077987
theorem B10805309 : Blo 2075435 10805309 := bstep (se 3 (by rfl) ⟨2025995, by rfl⟩ : syracuseStep 10805309 = 4051991) B4051991
theorem B7203539 : Blo 2075435 7203539 := bstep (se 1 (by rfl) ⟨5402654, by rfl⟩ : syracuseStep 7203539 = 10805309) B10805309
theorem B19209437 : Blo 2075435 19209437 := bstep (se 3 (by rfl) ⟨3601769, by rfl⟩ : syracuseStep 19209437 = 7203539) B7203539
theorem B12806291 : Blo 2075435 12806291 := bstep (se 1 (by rfl) ⟨9604718, by rfl⟩ : syracuseStep 12806291 = 19209437) B19209437
theorem B8537527 : Blo 2075435 8537527 := bstep (se 1 (by rfl) ⟨6403145, by rfl⟩ : syracuseStep 8537527 = 12806291) B12806291
theorem B45533477 : Blo 2075435 45533477 := bstep (se 4 (by rfl) ⟨4268763, by rfl⟩ : syracuseStep 45533477 = 8537527) B8537527
theorem B30355651 : Blo 2075435 30355651 := bstep (se 1 (by rfl) ⟨22766738, by rfl⟩ : syracuseStep 30355651 = 45533477) B45533477
theorem B40474201 : Blo 2075435 40474201 := bstep (se 2 (by rfl) ⟨15177825, by rfl⟩ : syracuseStep 40474201 = 30355651) B30355651
theorem B53965601 : Blo 2075435 53965601 := bstep (se 2 (by rfl) ⟨20237100, by rfl⟩ : syracuseStep 53965601 = 40474201) B40474201
theorem B35977067 : Blo 2075435 35977067 := bstep (se 1 (by rfl) ⟨26982800, by rfl⟩ : syracuseStep 35977067 = 53965601) B53965601
theorem B23984711 : Blo 2075435 23984711 := bstep (se 1 (by rfl) ⟨17988533, by rfl⟩ : syracuseStep 23984711 = 35977067) B35977067
theorem B15989807 : Blo 2075435 15989807 := bstep (se 1 (by rfl) ⟨11992355, by rfl⟩ : syracuseStep 15989807 = 23984711) B23984711
theorem B10659871 : Blo 2075435 10659871 := bstep (se 1 (by rfl) ⟨7994903, by rfl⟩ : syracuseStep 10659871 = 15989807) B15989807
theorem B14213161 : Blo 2075435 14213161 := bstep (se 2 (by rfl) ⟨5329935, by rfl⟩ : syracuseStep 14213161 = 10659871) B10659871
theorem B75803525 : Blo 2075435 75803525 := bstep (se 4 (by rfl) ⟨7106580, by rfl⟩ : syracuseStep 75803525 = 14213161) B14213161
theorem B50535683 : Blo 2075435 50535683 := bstep (se 1 (by rfl) ⟨37901762, by rfl⟩ : syracuseStep 50535683 = 75803525) B75803525
theorem B33690455 : Blo 2075435 33690455 := bstep (se 1 (by rfl) ⟨25267841, by rfl⟩ : syracuseStep 33690455 = 50535683) B50535683
theorem B22460303 : Blo 2075435 22460303 := bstep (se 1 (by rfl) ⟨16845227, by rfl⟩ : syracuseStep 22460303 = 33690455) B33690455
theorem B14973535 : Blo 2075435 14973535 := bstep (se 1 (by rfl) ⟨11230151, by rfl⟩ : syracuseStep 14973535 = 22460303) B22460303
theorem B19964713 : Blo 2075435 19964713 := bstep (se 2 (by rfl) ⟨7486767, by rfl⟩ : syracuseStep 19964713 = 14973535) B14973535
theorem B26619617 : Blo 2075435 26619617 := bstep (se 2 (by rfl) ⟨9982356, by rfl⟩ : syracuseStep 26619617 = 19964713) B19964713
theorem B17746411 : Blo 2075435 17746411 := bstep (se 1 (by rfl) ⟨13309808, by rfl⟩ : syracuseStep 17746411 = 26619617) B26619617
theorem B23661881 : Blo 2075435 23661881 := bstep (se 2 (by rfl) ⟨8873205, by rfl⟩ : syracuseStep 23661881 = 17746411) B17746411
theorem B15774587 : Blo 2075435 15774587 := bstep (se 1 (by rfl) ⟨11830940, by rfl⟩ : syracuseStep 15774587 = 23661881) B23661881
theorem B10516391 : Blo 2075435 10516391 := bstep (se 1 (by rfl) ⟨7887293, by rfl⟩ : syracuseStep 10516391 = 15774587) B15774587
theorem B7010927 : Blo 2075435 7010927 := bstep (se 1 (by rfl) ⟨5258195, by rfl⟩ : syracuseStep 7010927 = 10516391) B10516391
theorem B4673951 : Blo 2075435 4673951 := bstep (se 1 (by rfl) ⟨3505463, by rfl⟩ : syracuseStep 4673951 = 7010927) B7010927
theorem B3115967 : Blo 2075435 3115967 := bstep (se 1 (by rfl) ⟨2336975, by rfl⟩ : syracuseStep 3115967 = 4673951) B4673951
theorem B2077311 : Blo 2075435 2077311 := bstep (se 1 (by rfl) ⟨1557983, by rfl⟩ : syracuseStep 2077311 = 3115967) B3115967
theorem B3115973 : Blo 2075435 3115973 := bbase (se 4 (by rfl) ⟨292122, by rfl⟩ : syracuseStep 3115973 = 584245) (by norm_num)
theorem B2077315 : Blo 2075435 2077315 := bstep (se 1 (by rfl) ⟨1557986, by rfl⟩ : syracuseStep 2077315 = 3115973) B3115973
theorem B3505477 : Blo 2075435 3505477 := bbase (se 4 (by rfl) ⟨328638, by rfl⟩ : syracuseStep 3505477 = 657277) (by norm_num)
theorem B4673969 : Blo 2075435 4673969 := bstep (se 2 (by rfl) ⟨1752738, by rfl⟩ : syracuseStep 4673969 = 3505477) B3505477
theorem B3115979 : Blo 2075435 3115979 := bstep (se 1 (by rfl) ⟨2336984, by rfl⟩ : syracuseStep 3115979 = 4673969) B4673969
theorem B2077319 : Blo 2075435 2077319 := bstep (se 1 (by rfl) ⟨1557989, by rfl⟩ : syracuseStep 2077319 = 3115979) B3115979
theorem B2336989 : Blo 2075435 2336989 := bbase (se 3 (by rfl) ⟨438185, by rfl⟩ : syracuseStep 2336989 = 876371) (by norm_num)
theorem B3115985 : Blo 2075435 3115985 := bstep (se 2 (by rfl) ⟨1168494, by rfl⟩ : syracuseStep 3115985 = 2336989) B2336989
theorem B2077323 : Blo 2075435 2077323 := bstep (se 1 (by rfl) ⟨1557992, by rfl⟩ : syracuseStep 2077323 = 3115985) B3115985
theorem B7010981 : Blo 2075435 7010981 := bbase (se 4 (by rfl) ⟨657279, by rfl⟩ : syracuseStep 7010981 = 1314559) (by norm_num)
theorem B4673987 : Blo 2075435 4673987 := bstep (se 1 (by rfl) ⟨3505490, by rfl⟩ : syracuseStep 4673987 = 7010981) B7010981
theorem B3115991 : Blo 2075435 3115991 := bstep (se 1 (by rfl) ⟨2336993, by rfl⟩ : syracuseStep 3115991 = 4673987) B4673987
theorem B2077327 : Blo 2075435 2077327 := bstep (se 1 (by rfl) ⟨1557995, by rfl⟩ : syracuseStep 2077327 = 3115991) B3115991
theorem B3115997 : Blo 2075435 3115997 := bbase (se 3 (by rfl) ⟨584249, by rfl⟩ : syracuseStep 3115997 = 1168499) (by norm_num)
theorem B2077331 : Blo 2075435 2077331 := bstep (se 1 (by rfl) ⟨1557998, by rfl⟩ : syracuseStep 2077331 = 3115997) B3115997
theorem B4674005 : Blo 2075435 4674005 := bbase (se 7 (by rfl) ⟨54773, by rfl⟩ : syracuseStep 4674005 = 109547) (by norm_num)
theorem B3116003 : Blo 2075435 3116003 := bstep (se 1 (by rfl) ⟨2337002, by rfl⟩ : syracuseStep 3116003 = 4674005) B4674005
theorem B2077335 : Blo 2075435 2077335 := bstep (se 1 (by rfl) ⟨1558001, by rfl⟩ : syracuseStep 2077335 = 3116003) B3116003
theorem B5996261 : Blo 2075435 5996261 := bbase (se 4 (by rfl) ⟨562149, by rfl⟩ : syracuseStep 5996261 = 1124299) (by norm_num)
theorem B3997507 : Blo 2075435 3997507 := bstep (se 1 (by rfl) ⟨2998130, by rfl⟩ : syracuseStep 3997507 = 5996261) B5996261
theorem B5330009 : Blo 2075435 5330009 := bstep (se 2 (by rfl) ⟨1998753, by rfl⟩ : syracuseStep 5330009 = 3997507) B3997507
theorem B14213357 : Blo 2075435 14213357 := bstep (se 3 (by rfl) ⟨2665004, by rfl⟩ : syracuseStep 14213357 = 5330009) B5330009
theorem B9475571 : Blo 2075435 9475571 := bstep (se 1 (by rfl) ⟨7106678, by rfl⟩ : syracuseStep 9475571 = 14213357) B14213357
theorem B6317047 : Blo 2075435 6317047 := bstep (se 1 (by rfl) ⟨4737785, by rfl⟩ : syracuseStep 6317047 = 9475571) B9475571
theorem B33690917 : Blo 2075435 33690917 := bstep (se 4 (by rfl) ⟨3158523, by rfl⟩ : syracuseStep 33690917 = 6317047) B6317047
theorem B22460611 : Blo 2075435 22460611 := bstep (se 1 (by rfl) ⟨16845458, by rfl⟩ : syracuseStep 22460611 = 33690917) B33690917
theorem B29947481 : Blo 2075435 29947481 := bstep (se 2 (by rfl) ⟨11230305, by rfl⟩ : syracuseStep 29947481 = 22460611) B22460611
theorem B19964987 : Blo 2075435 19964987 := bstep (se 1 (by rfl) ⟨14973740, by rfl⟩ : syracuseStep 19964987 = 29947481) B29947481
theorem B13309991 : Blo 2075435 13309991 := bstep (se 1 (by rfl) ⟨9982493, by rfl⟩ : syracuseStep 13309991 = 19964987) B19964987
theorem B8873327 : Blo 2075435 8873327 := bstep (se 1 (by rfl) ⟨6654995, by rfl⟩ : syracuseStep 8873327 = 13309991) B13309991
theorem B5915551 : Blo 2075435 5915551 := bstep (se 1 (by rfl) ⟨4436663, by rfl⟩ : syracuseStep 5915551 = 8873327) B8873327
theorem B7887401 : Blo 2075435 7887401 := bstep (se 2 (by rfl) ⟨2957775, by rfl⟩ : syracuseStep 7887401 = 5915551) B5915551
theorem B5258267 : Blo 2075435 5258267 := bstep (se 1 (by rfl) ⟨3943700, by rfl⟩ : syracuseStep 5258267 = 7887401) B7887401
theorem B3505511 : Blo 2075435 3505511 := bstep (se 1 (by rfl) ⟨2629133, by rfl⟩ : syracuseStep 3505511 = 5258267) B5258267
theorem B2337007 : Blo 2075435 2337007 := bstep (se 1 (by rfl) ⟨1752755, by rfl⟩ : syracuseStep 2337007 = 3505511) B3505511
theorem B3116009 : Blo 2075435 3116009 := bstep (se 2 (by rfl) ⟨1168503, by rfl⟩ : syracuseStep 3116009 = 2337007) B2337007
theorem B2077339 : Blo 2075435 2077339 := bstep (se 1 (by rfl) ⟨1558004, by rfl⟩ : syracuseStep 2077339 = 3116009) B3116009
theorem B2529677 : Blo 2075435 2529677 := bbase (se 3 (by rfl) ⟨474314, by rfl⟩ : syracuseStep 2529677 = 948629) (by norm_num)
theorem B6745805 : Blo 2075435 6745805 := bstep (se 3 (by rfl) ⟨1264838, by rfl⟩ : syracuseStep 6745805 = 2529677) B2529677
theorem B4497203 : Blo 2075435 4497203 := bstep (se 1 (by rfl) ⟨3372902, by rfl⟩ : syracuseStep 4497203 = 6745805) B6745805
theorem B11992541 : Blo 2075435 11992541 := bstep (se 3 (by rfl) ⟨2248601, by rfl⟩ : syracuseStep 11992541 = 4497203) B4497203
theorem B31980109 : Blo 2075435 31980109 := bstep (se 3 (by rfl) ⟨5996270, by rfl⟩ : syracuseStep 31980109 = 11992541) B11992541
theorem B42640145 : Blo 2075435 42640145 := bstep (se 2 (by rfl) ⟨15990054, by rfl⟩ : syracuseStep 42640145 = 31980109) B31980109
theorem B28426763 : Blo 2075435 28426763 := bstep (se 1 (by rfl) ⟨21320072, by rfl⟩ : syracuseStep 28426763 = 42640145) B42640145
theorem B18951175 : Blo 2075435 18951175 := bstep (se 1 (by rfl) ⟨14213381, by rfl⟩ : syracuseStep 18951175 = 28426763) B28426763
theorem B25268233 : Blo 2075435 25268233 := bstep (se 2 (by rfl) ⟨9475587, by rfl⟩ : syracuseStep 25268233 = 18951175) B18951175
theorem B33690977 : Blo 2075435 33690977 := bstep (se 2 (by rfl) ⟨12634116, by rfl⟩ : syracuseStep 33690977 = 25268233) B25268233
theorem B22460651 : Blo 2075435 22460651 := bstep (se 1 (by rfl) ⟨16845488, by rfl⟩ : syracuseStep 22460651 = 33690977) B33690977
theorem B14973767 : Blo 2075435 14973767 := bstep (se 1 (by rfl) ⟨11230325, by rfl⟩ : syracuseStep 14973767 = 22460651) B22460651
theorem B9982511 : Blo 2075435 9982511 := bstep (se 1 (by rfl) ⟨7486883, by rfl⟩ : syracuseStep 9982511 = 14973767) B14973767
theorem B6655007 : Blo 2075435 6655007 := bstep (se 1 (by rfl) ⟨4991255, by rfl⟩ : syracuseStep 6655007 = 9982511) B9982511
theorem B17746685 : Blo 2075435 17746685 := bstep (se 3 (by rfl) ⟨3327503, by rfl⟩ : syracuseStep 17746685 = 6655007) B6655007
theorem B11831123 : Blo 2075435 11831123 := bstep (se 1 (by rfl) ⟨8873342, by rfl⟩ : syracuseStep 11831123 = 17746685) B17746685
theorem B7887415 : Blo 2075435 7887415 := bstep (se 1 (by rfl) ⟨5915561, by rfl⟩ : syracuseStep 7887415 = 11831123) B11831123
theorem B10516553 : Blo 2075435 10516553 := bstep (se 2 (by rfl) ⟨3943707, by rfl⟩ : syracuseStep 10516553 = 7887415) B7887415
theorem B7011035 : Blo 2075435 7011035 := bstep (se 1 (by rfl) ⟨5258276, by rfl⟩ : syracuseStep 7011035 = 10516553) B10516553
theorem B4674023 : Blo 2075435 4674023 := bstep (se 1 (by rfl) ⟨3505517, by rfl⟩ : syracuseStep 4674023 = 7011035) B7011035
theorem B3116015 : Blo 2075435 3116015 := bstep (se 1 (by rfl) ⟨2337011, by rfl⟩ : syracuseStep 3116015 = 4674023) B4674023
theorem B2077343 : Blo 2075435 2077343 := bstep (se 1 (by rfl) ⟨1558007, by rfl⟩ : syracuseStep 2077343 = 3116015) B3116015
theorem B3116021 : Blo 2075435 3116021 := bbase (se 5 (by rfl) ⟨146063, by rfl⟩ : syracuseStep 3116021 = 292127) (by norm_num)
theorem B2077347 : Blo 2075435 2077347 := bstep (se 1 (by rfl) ⟨1558010, by rfl⟩ : syracuseStep 2077347 = 3116021) B3116021
theorem B3327517 : Blo 2075435 3327517 := bbase (se 3 (by rfl) ⟨623909, by rfl⟩ : syracuseStep 3327517 = 1247819) (by norm_num)
theorem B4436689 : Blo 2075435 4436689 := bstep (se 2 (by rfl) ⟨1663758, by rfl⟩ : syracuseStep 4436689 = 3327517) B3327517
theorem B5915585 : Blo 2075435 5915585 := bstep (se 2 (by rfl) ⟨2218344, by rfl⟩ : syracuseStep 5915585 = 4436689) B4436689
theorem B3943723 : Blo 2075435 3943723 := bstep (se 1 (by rfl) ⟨2957792, by rfl⟩ : syracuseStep 3943723 = 5915585) B5915585
theorem B5258297 : Blo 2075435 5258297 := bstep (se 2 (by rfl) ⟨1971861, by rfl⟩ : syracuseStep 5258297 = 3943723) B3943723
theorem B3505531 : Blo 2075435 3505531 := bstep (se 1 (by rfl) ⟨2629148, by rfl⟩ : syracuseStep 3505531 = 5258297) B5258297
theorem B4674041 : Blo 2075435 4674041 := bstep (se 2 (by rfl) ⟨1752765, by rfl⟩ : syracuseStep 4674041 = 3505531) B3505531
theorem B3116027 : Blo 2075435 3116027 := bstep (se 1 (by rfl) ⟨2337020, by rfl⟩ : syracuseStep 3116027 = 4674041) B4674041
theorem B2077351 : Blo 2075435 2077351 := bstep (se 1 (by rfl) ⟨1558013, by rfl⟩ : syracuseStep 2077351 = 3116027) B3116027
theorem B2337025 : Blo 2075435 2337025 := bbase (se 2 (by rfl) ⟨876384, by rfl⟩ : syracuseStep 2337025 = 1752769) (by norm_num)
theorem B3116033 : Blo 2075435 3116033 := bstep (se 2 (by rfl) ⟨1168512, by rfl⟩ : syracuseStep 3116033 = 2337025) B2337025
theorem B2077355 : Blo 2075435 2077355 := bstep (se 1 (by rfl) ⟨1558016, by rfl⟩ : syracuseStep 2077355 = 3116033) B3116033
theorem B5258317 : Blo 2075435 5258317 := bbase (se 3 (by rfl) ⟨985934, by rfl⟩ : syracuseStep 5258317 = 1971869) (by norm_num)
theorem B7011089 : Blo 2075435 7011089 := bstep (se 2 (by rfl) ⟨2629158, by rfl⟩ : syracuseStep 7011089 = 5258317) B5258317
theorem B4674059 : Blo 2075435 4674059 := bstep (se 1 (by rfl) ⟨3505544, by rfl⟩ : syracuseStep 4674059 = 7011089) B7011089
theorem B3116039 : Blo 2075435 3116039 := bstep (se 1 (by rfl) ⟨2337029, by rfl⟩ : syracuseStep 3116039 = 4674059) B4674059
theorem B2077359 : Blo 2075435 2077359 := bstep (se 1 (by rfl) ⟨1558019, by rfl⟩ : syracuseStep 2077359 = 3116039) B3116039
theorem B3116045 : Blo 2075435 3116045 := bbase (se 3 (by rfl) ⟨584258, by rfl⟩ : syracuseStep 3116045 = 1168517) (by norm_num)
theorem B2077363 : Blo 2075435 2077363 := bstep (se 1 (by rfl) ⟨1558022, by rfl⟩ : syracuseStep 2077363 = 3116045) B3116045
theorem B4674077 : Blo 2075435 4674077 := bbase (se 3 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 4674077 = 1752779) (by norm_num)
theorem B3116051 : Blo 2075435 3116051 := bstep (se 1 (by rfl) ⟨2337038, by rfl⟩ : syracuseStep 3116051 = 4674077) B4674077
theorem B2077367 : Blo 2075435 2077367 := bstep (se 1 (by rfl) ⟨1558025, by rfl⟩ : syracuseStep 2077367 = 3116051) B3116051
theorem B3505565 : Blo 2075435 3505565 := bbase (se 3 (by rfl) ⟨657293, by rfl⟩ : syracuseStep 3505565 = 1314587) (by norm_num)
theorem B2337043 : Blo 2075435 2337043 := bstep (se 1 (by rfl) ⟨1752782, by rfl⟩ : syracuseStep 2337043 = 3505565) B3505565
theorem B3116057 : Blo 2075435 3116057 := bstep (se 2 (by rfl) ⟨1168521, by rfl⟩ : syracuseStep 3116057 = 2337043) B2337043
theorem B2077371 : Blo 2075435 2077371 := bstep (se 1 (by rfl) ⟨1558028, by rfl⟩ : syracuseStep 2077371 = 3116057) B3116057
theorem B4211437 : Blo 2075435 4211437 := bbase (se 3 (by rfl) ⟨789644, by rfl⟩ : syracuseStep 4211437 = 1579289) (by norm_num)
theorem B5615249 : Blo 2075435 5615249 := bstep (se 2 (by rfl) ⟨2105718, by rfl⟩ : syracuseStep 5615249 = 4211437) B4211437
theorem B14973997 : Blo 2075435 14973997 := bstep (se 3 (by rfl) ⟨2807624, by rfl⟩ : syracuseStep 14973997 = 5615249) B5615249
theorem B19965329 : Blo 2075435 19965329 := bstep (se 2 (by rfl) ⟨7486998, by rfl⟩ : syracuseStep 19965329 = 14973997) B14973997
theorem B13310219 : Blo 2075435 13310219 := bstep (se 1 (by rfl) ⟨9982664, by rfl⟩ : syracuseStep 13310219 = 19965329) B19965329
theorem B8873479 : Blo 2075435 8873479 := bstep (se 1 (by rfl) ⟨6655109, by rfl⟩ : syracuseStep 8873479 = 13310219) B13310219
theorem B11831305 : Blo 2075435 11831305 := bstep (se 2 (by rfl) ⟨4436739, by rfl⟩ : syracuseStep 11831305 = 8873479) B8873479
theorem B15775073 : Blo 2075435 15775073 := bstep (se 2 (by rfl) ⟨5915652, by rfl⟩ : syracuseStep 15775073 = 11831305) B11831305
theorem B10516715 : Blo 2075435 10516715 := bstep (se 1 (by rfl) ⟨7887536, by rfl⟩ : syracuseStep 10516715 = 15775073) B15775073
theorem B7011143 : Blo 2075435 7011143 := bstep (se 1 (by rfl) ⟨5258357, by rfl⟩ : syracuseStep 7011143 = 10516715) B10516715
theorem B4674095 : Blo 2075435 4674095 := bstep (se 1 (by rfl) ⟨3505571, by rfl⟩ : syracuseStep 4674095 = 7011143) B7011143
theorem B3116063 : Blo 2075435 3116063 := bstep (se 1 (by rfl) ⟨2337047, by rfl⟩ : syracuseStep 3116063 = 4674095) B4674095
theorem B2077375 : Blo 2075435 2077375 := bstep (se 1 (by rfl) ⟨1558031, by rfl⟩ : syracuseStep 2077375 = 3116063) B3116063
theorem B3116069 : Blo 2075435 3116069 := bbase (se 4 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 3116069 = 584263) (by norm_num)
theorem B2077379 : Blo 2075435 2077379 := bstep (se 1 (by rfl) ⟨1558034, by rfl⟩ : syracuseStep 2077379 = 3116069) B3116069
theorem B2629189 : Blo 2075435 2629189 := bbase (se 4 (by rfl) ⟨246486, by rfl⟩ : syracuseStep 2629189 = 492973) (by norm_num)
theorem B3505585 : Blo 2075435 3505585 := bstep (se 2 (by rfl) ⟨1314594, by rfl⟩ : syracuseStep 3505585 = 2629189) B2629189
theorem B4674113 : Blo 2075435 4674113 := bstep (se 2 (by rfl) ⟨1752792, by rfl⟩ : syracuseStep 4674113 = 3505585) B3505585
theorem B3116075 : Blo 2075435 3116075 := bstep (se 1 (by rfl) ⟨2337056, by rfl⟩ : syracuseStep 3116075 = 4674113) B4674113
theorem B2077383 : Blo 2075435 2077383 := bstep (se 1 (by rfl) ⟨1558037, by rfl⟩ : syracuseStep 2077383 = 3116075) B3116075
theorem B2337061 : Blo 2075435 2337061 := bbase (se 4 (by rfl) ⟨219099, by rfl⟩ : syracuseStep 2337061 = 438199) (by norm_num)
theorem B3116081 : Blo 2075435 3116081 := bstep (se 2 (by rfl) ⟨1168530, by rfl⟩ : syracuseStep 3116081 = 2337061) B2337061
theorem B2077387 : Blo 2075435 2077387 := bstep (se 1 (by rfl) ⟨1558040, by rfl⟩ : syracuseStep 2077387 = 3116081) B3116081
theorem B3327581 : Blo 2075435 3327581 := bbase (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) (by norm_num)
theorem B8873549 : Blo 2075435 8873549 := bstep (se 3 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 8873549 = 3327581) B3327581
theorem B5915699 : Blo 2075435 5915699 := bstep (se 1 (by rfl) ⟨4436774, by rfl⟩ : syracuseStep 5915699 = 8873549) B8873549
theorem B3943799 : Blo 2075435 3943799 := bstep (se 1 (by rfl) ⟨2957849, by rfl⟩ : syracuseStep 3943799 = 5915699) B5915699
theorem B2629199 : Blo 2075435 2629199 := bstep (se 1 (by rfl) ⟨1971899, by rfl⟩ : syracuseStep 2629199 = 3943799) B3943799
theorem B7011197 : Blo 2075435 7011197 := bstep (se 3 (by rfl) ⟨1314599, by rfl⟩ : syracuseStep 7011197 = 2629199) B2629199
theorem B4674131 : Blo 2075435 4674131 := bstep (se 1 (by rfl) ⟨3505598, by rfl⟩ : syracuseStep 4674131 = 7011197) B7011197
theorem B3116087 : Blo 2075435 3116087 := bstep (se 1 (by rfl) ⟨2337065, by rfl⟩ : syracuseStep 3116087 = 4674131) B4674131
theorem B2077391 : Blo 2075435 2077391 := bstep (se 1 (by rfl) ⟨1558043, by rfl⟩ : syracuseStep 2077391 = 3116087) B3116087
theorem B3116093 : Blo 2075435 3116093 := bbase (se 3 (by rfl) ⟨584267, by rfl⟩ : syracuseStep 3116093 = 1168535) (by norm_num)
theorem B2077395 : Blo 2075435 2077395 := bstep (se 1 (by rfl) ⟨1558046, by rfl⟩ : syracuseStep 2077395 = 3116093) B3116093
theorem B4674149 : Blo 2075435 4674149 := bbase (se 4 (by rfl) ⟨438201, by rfl⟩ : syracuseStep 4674149 = 876403) (by norm_num)
theorem B3116099 : Blo 2075435 3116099 := bstep (se 1 (by rfl) ⟨2337074, by rfl⟩ : syracuseStep 3116099 = 4674149) B4674149
theorem B2077399 : Blo 2075435 2077399 := bstep (se 1 (by rfl) ⟨1558049, by rfl⟩ : syracuseStep 2077399 = 3116099) B3116099
theorem B5258429 : Blo 2075435 5258429 := bbase (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) (by norm_num)
theorem B3505619 : Blo 2075435 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B2337079 : Blo 2075435 2337079 := bstep (se 1 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 2337079 = 3505619) B3505619
theorem B3116105 : Blo 2075435 3116105 := bstep (se 2 (by rfl) ⟨1168539, by rfl⟩ : syracuseStep 3116105 = 2337079) B2337079
theorem B2077403 : Blo 2075435 2077403 := bstep (se 1 (by rfl) ⟨1558052, by rfl⟩ : syracuseStep 2077403 = 3116105) B3116105
theorem B3943829 : Blo 2075435 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B10516877 : Blo 2075435 10516877 := bstep (se 3 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 10516877 = 3943829) B3943829
theorem B7011251 : Blo 2075435 7011251 := bstep (se 1 (by rfl) ⟨5258438, by rfl⟩ : syracuseStep 7011251 = 10516877) B10516877
theorem B4674167 : Blo 2075435 4674167 := bstep (se 1 (by rfl) ⟨3505625, by rfl⟩ : syracuseStep 4674167 = 7011251) B7011251
theorem B3116111 : Blo 2075435 3116111 := bstep (se 1 (by rfl) ⟨2337083, by rfl⟩ : syracuseStep 3116111 = 4674167) B4674167
theorem B2077407 : Blo 2075435 2077407 := bstep (se 1 (by rfl) ⟨1558055, by rfl⟩ : syracuseStep 2077407 = 3116111) B3116111
theorem B3116117 : Blo 2075435 3116117 := bbase (se 8 (by rfl) ⟨18258, by rfl⟩ : syracuseStep 3116117 = 36517) (by norm_num)
theorem B2077411 : Blo 2075435 2077411 := bstep (se 1 (by rfl) ⟨1558058, by rfl⟩ : syracuseStep 2077411 = 3116117) B3116117
theorem B4991429 : Blo 2075435 4991429 := bbase (se 4 (by rfl) ⟨467946, by rfl⟩ : syracuseStep 4991429 = 935893) (by norm_num)
theorem B13310477 : Blo 2075435 13310477 := bstep (se 3 (by rfl) ⟨2495714, by rfl⟩ : syracuseStep 13310477 = 4991429) B4991429
theorem B8873651 : Blo 2075435 8873651 := bstep (se 1 (by rfl) ⟨6655238, by rfl⟩ : syracuseStep 8873651 = 13310477) B13310477
theorem B5915767 : Blo 2075435 5915767 := bstep (se 1 (by rfl) ⟨4436825, by rfl⟩ : syracuseStep 5915767 = 8873651) B8873651
theorem B7887689 : Blo 2075435 7887689 := bstep (se 2 (by rfl) ⟨2957883, by rfl⟩ : syracuseStep 7887689 = 5915767) B5915767
theorem B5258459 : Blo 2075435 5258459 := bstep (se 1 (by rfl) ⟨3943844, by rfl⟩ : syracuseStep 5258459 = 7887689) B7887689
theorem B3505639 : Blo 2075435 3505639 := bstep (se 1 (by rfl) ⟨2629229, by rfl⟩ : syracuseStep 3505639 = 5258459) B5258459
theorem B4674185 : Blo 2075435 4674185 := bstep (se 2 (by rfl) ⟨1752819, by rfl⟩ : syracuseStep 4674185 = 3505639) B3505639
theorem B3116123 : Blo 2075435 3116123 := bstep (se 1 (by rfl) ⟨2337092, by rfl⟩ : syracuseStep 3116123 = 4674185) B4674185
theorem B2077415 : Blo 2075435 2077415 := bstep (se 1 (by rfl) ⟨1558061, by rfl⟩ : syracuseStep 2077415 = 3116123) B3116123
theorem B2337097 : Blo 2075435 2337097 := bbase (se 2 (by rfl) ⟨876411, by rfl⟩ : syracuseStep 2337097 = 1752823) (by norm_num)
theorem B3116129 : Blo 2075435 3116129 := bstep (se 2 (by rfl) ⟨1168548, by rfl⟩ : syracuseStep 3116129 = 2337097) B2337097
theorem B2077419 : Blo 2075435 2077419 := bstep (se 1 (by rfl) ⟨1558064, by rfl⟩ : syracuseStep 2077419 = 3116129) B3116129
theorem B101076821 : Blo 2075435 101076821 := bbase (se 9 (by rfl) ⟨296123, by rfl⟩ : syracuseStep 101076821 = 592247) (by norm_num)
theorem B67384547 : Blo 2075435 67384547 := bstep (se 1 (by rfl) ⟨50538410, by rfl⟩ : syracuseStep 67384547 = 101076821) B101076821
theorem B44923031 : Blo 2075435 44923031 := bstep (se 1 (by rfl) ⟨33692273, by rfl⟩ : syracuseStep 44923031 = 67384547) B67384547
theorem B29948687 : Blo 2075435 29948687 := bstep (se 1 (by rfl) ⟨22461515, by rfl⟩ : syracuseStep 29948687 = 44923031) B44923031
theorem B19965791 : Blo 2075435 19965791 := bstep (se 1 (by rfl) ⟨14974343, by rfl⟩ : syracuseStep 19965791 = 29948687) B29948687
theorem B13310527 : Blo 2075435 13310527 := bstep (se 1 (by rfl) ⟨9982895, by rfl⟩ : syracuseStep 13310527 = 19965791) B19965791
theorem B17747369 : Blo 2075435 17747369 := bstep (se 2 (by rfl) ⟨6655263, by rfl⟩ : syracuseStep 17747369 = 13310527) B13310527
theorem B11831579 : Blo 2075435 11831579 := bstep (se 1 (by rfl) ⟨8873684, by rfl⟩ : syracuseStep 11831579 = 17747369) B17747369
theorem B7887719 : Blo 2075435 7887719 := bstep (se 1 (by rfl) ⟨5915789, by rfl⟩ : syracuseStep 7887719 = 11831579) B11831579
theorem B5258479 : Blo 2075435 5258479 := bstep (se 1 (by rfl) ⟨3943859, by rfl⟩ : syracuseStep 5258479 = 7887719) B7887719
theorem B7011305 : Blo 2075435 7011305 := bstep (se 2 (by rfl) ⟨2629239, by rfl⟩ : syracuseStep 7011305 = 5258479) B5258479
theorem B4674203 : Blo 2075435 4674203 := bstep (se 1 (by rfl) ⟨3505652, by rfl⟩ : syracuseStep 4674203 = 7011305) B7011305
theorem B3116135 : Blo 2075435 3116135 := bstep (se 1 (by rfl) ⟨2337101, by rfl⟩ : syracuseStep 3116135 = 4674203) B4674203
theorem B2077423 : Blo 2075435 2077423 := bstep (se 1 (by rfl) ⟨1558067, by rfl⟩ : syracuseStep 2077423 = 3116135) B3116135
theorem B3116141 : Blo 2075435 3116141 := bbase (se 3 (by rfl) ⟨584276, by rfl⟩ : syracuseStep 3116141 = 1168553) (by norm_num)
theorem B2077427 : Blo 2075435 2077427 := bstep (se 1 (by rfl) ⟨1558070, by rfl⟩ : syracuseStep 2077427 = 3116141) B3116141
theorem B4674221 : Blo 2075435 4674221 := bbase (se 3 (by rfl) ⟨876416, by rfl⟩ : syracuseStep 4674221 = 1752833) (by norm_num)
theorem B3116147 : Blo 2075435 3116147 := bstep (se 1 (by rfl) ⟨2337110, by rfl⟩ : syracuseStep 3116147 = 4674221) B4674221
theorem B2077431 : Blo 2075435 2077431 := bstep (se 1 (by rfl) ⟨1558073, by rfl⟩ : syracuseStep 2077431 = 3116147) B3116147
theorem B4436869 : Blo 2075435 4436869 := bbase (se 4 (by rfl) ⟨415956, by rfl⟩ : syracuseStep 4436869 = 831913) (by norm_num)
theorem B5915825 : Blo 2075435 5915825 := bstep (se 2 (by rfl) ⟨2218434, by rfl⟩ : syracuseStep 5915825 = 4436869) B4436869
theorem B3943883 : Blo 2075435 3943883 := bstep (se 1 (by rfl) ⟨2957912, by rfl⟩ : syracuseStep 3943883 = 5915825) B5915825
theorem B2629255 : Blo 2075435 2629255 := bstep (se 1 (by rfl) ⟨1971941, by rfl⟩ : syracuseStep 2629255 = 3943883) B3943883
theorem B3505673 : Blo 2075435 3505673 := bstep (se 2 (by rfl) ⟨1314627, by rfl⟩ : syracuseStep 3505673 = 2629255) B2629255
theorem B2337115 : Blo 2075435 2337115 := bstep (se 1 (by rfl) ⟨1752836, by rfl⟩ : syracuseStep 2337115 = 3505673) B3505673
theorem B3116153 : Blo 2075435 3116153 := bstep (se 2 (by rfl) ⟨1168557, by rfl⟩ : syracuseStep 3116153 = 2337115) B2337115
theorem B2077435 : Blo 2075435 2077435 := bstep (se 1 (by rfl) ⟨1558076, by rfl⟩ : syracuseStep 2077435 = 3116153) B3116153
theorem C0 (j : ℕ) (h1 : 518858 ≤ j) (h2 : j ≤ 519358) : Blo 2075435 (4 * j + 3) := by
  interval_cases j
  · exact B2075435
  · exact B2075439
  · exact B2075443
  · exact B2075447
  · exact B2075451
  · exact B2075455
  · exact B2075459
  · exact B2075463
  · exact B2075467
  · exact B2075471
  · exact B2075475
  · exact B2075479
  · exact B2075483
  · exact B2075487
  · exact B2075491
  · exact B2075495
  · exact B2075499
  · exact B2075503
  · exact B2075507
  · exact B2075511
  · exact B2075515
  · exact B2075519
  · exact B2075523
  · exact B2075527
  · exact B2075531
  · exact B2075535
  · exact B2075539
  · exact B2075543
  · exact B2075547
  · exact B2075551
  · exact B2075555
  · exact B2075559
  · exact B2075563
  · exact B2075567
  · exact B2075571
  · exact B2075575
  · exact B2075579
  · exact B2075583
  · exact B2075587
  · exact B2075591
  · exact B2075595
  · exact B2075599
  · exact B2075603
  · exact B2075607
  · exact B2075611
  · exact B2075615
  · exact B2075619
  · exact B2075623
  · exact B2075627
  · exact B2075631
  · exact B2075635
  · exact B2075639
  · exact B2075643
  · exact B2075647
  · exact B2075651
  · exact B2075655
  · exact B2075659
  · exact B2075663
  · exact B2075667
  · exact B2075671
  · exact B2075675
  · exact B2075679
  · exact B2075683
  · exact B2075687
  · exact B2075691
  · exact B2075695
  · exact B2075699
  · exact B2075703
  · exact B2075707
  · exact B2075711
  · exact B2075715
  · exact B2075719
  · exact B2075723
  · exact B2075727
  · exact B2075731
  · exact B2075735
  · exact B2075739
  · exact B2075743
  · exact B2075747
  · exact B2075751
  · exact B2075755
  · exact B2075759
  · exact B2075763
  · exact B2075767
  · exact B2075771
  · exact B2075775
  · exact B2075779
  · exact B2075783
  · exact B2075787
  · exact B2075791
  · exact B2075795
  · exact B2075799
  · exact B2075803
  · exact B2075807
  · exact B2075811
  · exact B2075815
  · exact B2075819
  · exact B2075823
  · exact B2075827
  · exact B2075831
  · exact B2075835
  · exact B2075839
  · exact B2075843
  · exact B2075847
  · exact B2075851
  · exact B2075855
  · exact B2075859
  · exact B2075863
  · exact B2075867
  · exact B2075871
  · exact B2075875
  · exact B2075879
  · exact B2075883
  · exact B2075887
  · exact B2075891
  · exact B2075895
  · exact B2075899
  · exact B2075903
  · exact B2075907
  · exact B2075911
  · exact B2075915
  · exact B2075919
  · exact B2075923
  · exact B2075927
  · exact B2075931
  · exact B2075935
  · exact B2075939
  · exact B2075943
  · exact B2075947
  · exact B2075951
  · exact B2075955
  · exact B2075959
  · exact B2075963
  · exact B2075967
  · exact B2075971
  · exact B2075975
  · exact B2075979
  · exact B2075983
  · exact B2075987
  · exact B2075991
  · exact B2075995
  · exact B2075999
  · exact B2076003
  · exact B2076007
  · exact B2076011
  · exact B2076015
  · exact B2076019
  · exact B2076023
  · exact B2076027
  · exact B2076031
  · exact B2076035
  · exact B2076039
  · exact B2076043
  · exact B2076047
  · exact B2076051
  · exact B2076055
  · exact B2076059
  · exact B2076063
  · exact B2076067
  · exact B2076071
  · exact B2076075
  · exact B2076079
  · exact B2076083
  · exact B2076087
  · exact B2076091
  · exact B2076095
  · exact B2076099
  · exact B2076103
  · exact B2076107
  · exact B2076111
  · exact B2076115
  · exact B2076119
  · exact B2076123
  · exact B2076127
  · exact B2076131
  · exact B2076135
  · exact B2076139
  · exact B2076143
  · exact B2076147
  · exact B2076151
  · exact B2076155
  · exact B2076159
  · exact B2076163
  · exact B2076167
  · exact B2076171
  · exact B2076175
  · exact B2076179
  · exact B2076183
  · exact B2076187
  · exact B2076191
  · exact B2076195
  · exact B2076199
  · exact B2076203
  · exact B2076207
  · exact B2076211
  · exact B2076215
  · exact B2076219
  · exact B2076223
  · exact B2076227
  · exact B2076231
  · exact B2076235
  · exact B2076239
  · exact B2076243
  · exact B2076247
  · exact B2076251
  · exact B2076255
  · exact B2076259
  · exact B2076263
  · exact B2076267
  · exact B2076271
  · exact B2076275
  · exact B2076279
  · exact B2076283
  · exact B2076287
  · exact B2076291
  · exact B2076295
  · exact B2076299
  · exact B2076303
  · exact B2076307
  · exact B2076311
  · exact B2076315
  · exact B2076319
  · exact B2076323
  · exact B2076327
  · exact B2076331
  · exact B2076335
  · exact B2076339
  · exact B2076343
  · exact B2076347
  · exact B2076351
  · exact B2076355
  · exact B2076359
  · exact B2076363
  · exact B2076367
  · exact B2076371
  · exact B2076375
  · exact B2076379
  · exact B2076383
  · exact B2076387
  · exact B2076391
  · exact B2076395
  · exact B2076399
  · exact B2076403
  · exact B2076407
  · exact B2076411
  · exact B2076415
  · exact B2076419
  · exact B2076423
  · exact B2076427
  · exact B2076431
  · exact B2076435
  · exact B2076439
  · exact B2076443
  · exact B2076447
  · exact B2076451
  · exact B2076455
  · exact B2076459
  · exact B2076463
  · exact B2076467
  · exact B2076471
  · exact B2076475
  · exact B2076479
  · exact B2076483
  · exact B2076487
  · exact B2076491
  · exact B2076495
  · exact B2076499
  · exact B2076503
  · exact B2076507
  · exact B2076511
  · exact B2076515
  · exact B2076519
  · exact B2076523
  · exact B2076527
  · exact B2076531
  · exact B2076535
  · exact B2076539
  · exact B2076543
  · exact B2076547
  · exact B2076551
  · exact B2076555
  · exact B2076559
  · exact B2076563
  · exact B2076567
  · exact B2076571
  · exact B2076575
  · exact B2076579
  · exact B2076583
  · exact B2076587
  · exact B2076591
  · exact B2076595
  · exact B2076599
  · exact B2076603
  · exact B2076607
  · exact B2076611
  · exact B2076615
  · exact B2076619
  · exact B2076623
  · exact B2076627
  · exact B2076631
  · exact B2076635
  · exact B2076639
  · exact B2076643
  · exact B2076647
  · exact B2076651
  · exact B2076655
  · exact B2076659
  · exact B2076663
  · exact B2076667
  · exact B2076671
  · exact B2076675
  · exact B2076679
  · exact B2076683
  · exact B2076687
  · exact B2076691
  · exact B2076695
  · exact B2076699
  · exact B2076703
  · exact B2076707
  · exact B2076711
  · exact B2076715
  · exact B2076719
  · exact B2076723
  · exact B2076727
  · exact B2076731
  · exact B2076735
  · exact B2076739
  · exact B2076743
  · exact B2076747
  · exact B2076751
  · exact B2076755
  · exact B2076759
  · exact B2076763
  · exact B2076767
  · exact B2076771
  · exact B2076775
  · exact B2076779
  · exact B2076783
  · exact B2076787
  · exact B2076791
  · exact B2076795
  · exact B2076799
  · exact B2076803
  · exact B2076807
  · exact B2076811
  · exact B2076815
  · exact B2076819
  · exact B2076823
  · exact B2076827
  · exact B2076831
  · exact B2076835
  · exact B2076839
  · exact B2076843
  · exact B2076847
  · exact B2076851
  · exact B2076855
  · exact B2076859
  · exact B2076863
  · exact B2076867
  · exact B2076871
  · exact B2076875
  · exact B2076879
  · exact B2076883
  · exact B2076887
  · exact B2076891
  · exact B2076895
  · exact B2076899
  · exact B2076903
  · exact B2076907
  · exact B2076911
  · exact B2076915
  · exact B2076919
  · exact B2076923
  · exact B2076927
  · exact B2076931
  · exact B2076935
  · exact B2076939
  · exact B2076943
  · exact B2076947
  · exact B2076951
  · exact B2076955
  · exact B2076959
  · exact B2076963
  · exact B2076967
  · exact B2076971
  · exact B2076975
  · exact B2076979
  · exact B2076983
  · exact B2076987
  · exact B2076991
  · exact B2076995
  · exact B2076999
  · exact B2077003
  · exact B2077007
  · exact B2077011
  · exact B2077015
  · exact B2077019
  · exact B2077023
  · exact B2077027
  · exact B2077031
  · exact B2077035
  · exact B2077039
  · exact B2077043
  · exact B2077047
  · exact B2077051
  · exact B2077055
  · exact B2077059
  · exact B2077063
  · exact B2077067
  · exact B2077071
  · exact B2077075
  · exact B2077079
  · exact B2077083
  · exact B2077087
  · exact B2077091
  · exact B2077095
  · exact B2077099
  · exact B2077103
  · exact B2077107
  · exact B2077111
  · exact B2077115
  · exact B2077119
  · exact B2077123
  · exact B2077127
  · exact B2077131
  · exact B2077135
  · exact B2077139
  · exact B2077143
  · exact B2077147
  · exact B2077151
  · exact B2077155
  · exact B2077159
  · exact B2077163
  · exact B2077167
  · exact B2077171
  · exact B2077175
  · exact B2077179
  · exact B2077183
  · exact B2077187
  · exact B2077191
  · exact B2077195
  · exact B2077199
  · exact B2077203
  · exact B2077207
  · exact B2077211
  · exact B2077215
  · exact B2077219
  · exact B2077223
  · exact B2077227
  · exact B2077231
  · exact B2077235
  · exact B2077239
  · exact B2077243
  · exact B2077247
  · exact B2077251
  · exact B2077255
  · exact B2077259
  · exact B2077263
  · exact B2077267
  · exact B2077271
  · exact B2077275
  · exact B2077279
  · exact B2077283
  · exact B2077287
  · exact B2077291
  · exact B2077295
  · exact B2077299
  · exact B2077303
  · exact B2077307
  · exact B2077311
  · exact B2077315
  · exact B2077319
  · exact B2077323
  · exact B2077327
  · exact B2077331
  · exact B2077335
  · exact B2077339
  · exact B2077343
  · exact B2077347
  · exact B2077351
  · exact B2077355
  · exact B2077359
  · exact B2077363
  · exact B2077367
  · exact B2077371
  · exact B2077375
  · exact B2077379
  · exact B2077383
  · exact B2077387
  · exact B2077391
  · exact B2077395
  · exact B2077399
  · exact B2077403
  · exact B2077407
  · exact B2077411
  · exact B2077415
  · exact B2077419
  · exact B2077423
  · exact B2077427
  · exact B2077431
  · exact B2077435
theorem solution (m : ℕ) (hlo : 2075435 ≤ m) (hhi : m ≤ 2077435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 518858 ≤ j := by omega
    have hj2 : j ≤ 519358 := by omega
    have hb : Blo 2075435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
