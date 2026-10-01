-- Prove2me | solution 1 for syracuse_descends_range_1971435_1973435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:03.116868+00:00
-- url     : https://prove2.me/submissions/38b6d0c6-53bf-4839-b79d-2c88cbe533ca

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

theorem B2217865 : Blo 1971435 2217865 := bbase (se 2 (by rfl) ⟨831699, by rfl⟩ : syracuseStep 2217865 = 1663399) (by norm_num)
theorem B2957153 : Blo 1971435 2957153 := bstep (se 2 (by rfl) ⟨1108932, by rfl⟩ : syracuseStep 2957153 = 2217865) B2217865
theorem B1971435 : Blo 1971435 1971435 := bstep (se 1 (by rfl) ⟨1478576, by rfl⟩ : syracuseStep 1971435 = 2957153) B2957153
theorem B8992517 : Blo 1971435 8992517 := bbase (se 4 (by rfl) ⟨843048, by rfl⟩ : syracuseStep 8992517 = 1686097) (by norm_num)
theorem B23980045 : Blo 1971435 23980045 := bstep (se 3 (by rfl) ⟨4496258, by rfl⟩ : syracuseStep 23980045 = 8992517) B8992517
theorem B31973393 : Blo 1971435 31973393 := bstep (se 2 (by rfl) ⟨11990022, by rfl⟩ : syracuseStep 31973393 = 23980045) B23980045
theorem B85262381 : Blo 1971435 85262381 := bstep (se 3 (by rfl) ⟨15986696, by rfl⟩ : syracuseStep 85262381 = 31973393) B31973393
theorem B56841587 : Blo 1971435 56841587 := bstep (se 1 (by rfl) ⟨42631190, by rfl⟩ : syracuseStep 56841587 = 85262381) B85262381
theorem B37894391 : Blo 1971435 37894391 := bstep (se 1 (by rfl) ⟨28420793, by rfl⟩ : syracuseStep 37894391 = 56841587) B56841587
theorem B25262927 : Blo 1971435 25262927 := bstep (se 1 (by rfl) ⟨18947195, by rfl⟩ : syracuseStep 25262927 = 37894391) B37894391
theorem B16841951 : Blo 1971435 16841951 := bstep (se 1 (by rfl) ⟨12631463, by rfl⟩ : syracuseStep 16841951 = 25262927) B25262927
theorem B11227967 : Blo 1971435 11227967 := bstep (se 1 (by rfl) ⟨8420975, by rfl⟩ : syracuseStep 11227967 = 16841951) B16841951
theorem B7485311 : Blo 1971435 7485311 := bstep (se 1 (by rfl) ⟨5613983, by rfl⟩ : syracuseStep 7485311 = 11227967) B11227967
theorem B4990207 : Blo 1971435 4990207 := bstep (se 1 (by rfl) ⟨3742655, by rfl⟩ : syracuseStep 4990207 = 7485311) B7485311
theorem B6653609 : Blo 1971435 6653609 := bstep (se 2 (by rfl) ⟨2495103, by rfl⟩ : syracuseStep 6653609 = 4990207) B4990207
theorem B4435739 : Blo 1971435 4435739 := bstep (se 1 (by rfl) ⟨3326804, by rfl⟩ : syracuseStep 4435739 = 6653609) B6653609
theorem B2957159 : Blo 1971435 2957159 := bstep (se 1 (by rfl) ⟨2217869, by rfl⟩ : syracuseStep 2957159 = 4435739) B4435739
theorem B1971439 : Blo 1971435 1971439 := bstep (se 1 (by rfl) ⟨1478579, by rfl⟩ : syracuseStep 1971439 = 2957159) B2957159
theorem B2957165 : Blo 1971435 2957165 := bbase (se 3 (by rfl) ⟨554468, by rfl⟩ : syracuseStep 2957165 = 1108937) (by norm_num)
theorem B1971443 : Blo 1971435 1971443 := bstep (se 1 (by rfl) ⟨1478582, by rfl⟩ : syracuseStep 1971443 = 2957165) B2957165
theorem B4435757 : Blo 1971435 4435757 := bbase (se 3 (by rfl) ⟨831704, by rfl⟩ : syracuseStep 4435757 = 1663409) (by norm_num)
theorem B2957171 : Blo 1971435 2957171 := bstep (se 1 (by rfl) ⟨2217878, by rfl⟩ : syracuseStep 2957171 = 4435757) B4435757
theorem B1971447 : Blo 1971435 1971447 := bstep (se 1 (by rfl) ⟨1478585, by rfl⟩ : syracuseStep 1971447 = 2957171) B2957171
theorem B8421029 : Blo 1971435 8421029 := bbase (se 4 (by rfl) ⟨789471, by rfl⟩ : syracuseStep 8421029 = 1578943) (by norm_num)
theorem B5614019 : Blo 1971435 5614019 := bstep (se 1 (by rfl) ⟨4210514, by rfl⟩ : syracuseStep 5614019 = 8421029) B8421029
theorem B3742679 : Blo 1971435 3742679 := bstep (se 1 (by rfl) ⟨2807009, by rfl⟩ : syracuseStep 3742679 = 5614019) B5614019
theorem B2495119 : Blo 1971435 2495119 := bstep (se 1 (by rfl) ⟨1871339, by rfl⟩ : syracuseStep 2495119 = 3742679) B3742679
theorem B3326825 : Blo 1971435 3326825 := bstep (se 2 (by rfl) ⟨1247559, by rfl⟩ : syracuseStep 3326825 = 2495119) B2495119
theorem B2217883 : Blo 1971435 2217883 := bstep (se 1 (by rfl) ⟨1663412, by rfl⟩ : syracuseStep 2217883 = 3326825) B3326825
theorem B2957177 : Blo 1971435 2957177 := bstep (se 2 (by rfl) ⟨1108941, by rfl⟩ : syracuseStep 2957177 = 2217883) B2217883
theorem B1971451 : Blo 1971435 1971451 := bstep (se 1 (by rfl) ⟨1478588, by rfl⟩ : syracuseStep 1971451 = 2957177) B2957177
theorem B4736837 : Blo 1971435 4736837 := bbase (se 4 (by rfl) ⟨444078, by rfl⟩ : syracuseStep 4736837 = 888157) (by norm_num)
theorem B12631565 : Blo 1971435 12631565 := bstep (se 3 (by rfl) ⟨2368418, by rfl⟩ : syracuseStep 12631565 = 4736837) B4736837
theorem B33684173 : Blo 1971435 33684173 := bstep (se 3 (by rfl) ⟨6315782, by rfl⟩ : syracuseStep 33684173 = 12631565) B12631565
theorem B22456115 : Blo 1971435 22456115 := bstep (se 1 (by rfl) ⟨16842086, by rfl⟩ : syracuseStep 22456115 = 33684173) B33684173
theorem B14970743 : Blo 1971435 14970743 := bstep (se 1 (by rfl) ⟨11228057, by rfl⟩ : syracuseStep 14970743 = 22456115) B22456115
theorem B9980495 : Blo 1971435 9980495 := bstep (se 1 (by rfl) ⟨7485371, by rfl⟩ : syracuseStep 9980495 = 14970743) B14970743
theorem B6653663 : Blo 1971435 6653663 := bstep (se 1 (by rfl) ⟨4990247, by rfl⟩ : syracuseStep 6653663 = 9980495) B9980495
theorem B4435775 : Blo 1971435 4435775 := bstep (se 1 (by rfl) ⟨3326831, by rfl⟩ : syracuseStep 4435775 = 6653663) B6653663
theorem B2957183 : Blo 1971435 2957183 := bstep (se 1 (by rfl) ⟨2217887, by rfl⟩ : syracuseStep 2957183 = 4435775) B4435775
theorem B1971455 : Blo 1971435 1971455 := bstep (se 1 (by rfl) ⟨1478591, by rfl⟩ : syracuseStep 1971455 = 2957183) B2957183
theorem B2957189 : Blo 1971435 2957189 := bbase (se 4 (by rfl) ⟨277236, by rfl⟩ : syracuseStep 2957189 = 554473) (by norm_num)
theorem B1971459 : Blo 1971435 1971459 := bstep (se 1 (by rfl) ⟨1478594, by rfl⟩ : syracuseStep 1971459 = 2957189) B2957189
theorem B3326845 : Blo 1971435 3326845 := bbase (se 3 (by rfl) ⟨623783, by rfl⟩ : syracuseStep 3326845 = 1247567) (by norm_num)
theorem B4435793 : Blo 1971435 4435793 := bstep (se 2 (by rfl) ⟨1663422, by rfl⟩ : syracuseStep 4435793 = 3326845) B3326845
theorem B2957195 : Blo 1971435 2957195 := bstep (se 1 (by rfl) ⟨2217896, by rfl⟩ : syracuseStep 2957195 = 4435793) B4435793
theorem B1971463 : Blo 1971435 1971463 := bstep (se 1 (by rfl) ⟨1478597, by rfl⟩ : syracuseStep 1971463 = 2957195) B2957195
theorem B2217901 : Blo 1971435 2217901 := bbase (se 3 (by rfl) ⟨415856, by rfl⟩ : syracuseStep 2217901 = 831713) (by norm_num)
theorem B2957201 : Blo 1971435 2957201 := bstep (se 2 (by rfl) ⟨1108950, by rfl⟩ : syracuseStep 2957201 = 2217901) B2217901
theorem B1971467 : Blo 1971435 1971467 := bstep (se 1 (by rfl) ⟨1478600, by rfl⟩ : syracuseStep 1971467 = 2957201) B2957201
theorem B6653717 : Blo 1971435 6653717 := bbase (se 6 (by rfl) ⟨155946, by rfl⟩ : syracuseStep 6653717 = 311893) (by norm_num)
theorem B4435811 : Blo 1971435 4435811 := bstep (se 1 (by rfl) ⟨3326858, by rfl⟩ : syracuseStep 4435811 = 6653717) B6653717
theorem B2957207 : Blo 1971435 2957207 := bstep (se 1 (by rfl) ⟨2217905, by rfl⟩ : syracuseStep 2957207 = 4435811) B4435811
theorem B1971471 : Blo 1971435 1971471 := bstep (se 1 (by rfl) ⟨1478603, by rfl⟩ : syracuseStep 1971471 = 2957207) B2957207
theorem B2957213 : Blo 1971435 2957213 := bbase (se 3 (by rfl) ⟨554477, by rfl⟩ : syracuseStep 2957213 = 1108955) (by norm_num)
theorem B1971475 : Blo 1971435 1971475 := bstep (se 1 (by rfl) ⟨1478606, by rfl⟩ : syracuseStep 1971475 = 2957213) B2957213
theorem B4435829 : Blo 1971435 4435829 := bbase (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) (by norm_num)
theorem B2957219 : Blo 1971435 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B1971479 : Blo 1971435 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B3793805 : Blo 1971435 3793805 := bbase (se 3 (by rfl) ⟨711338, by rfl⟩ : syracuseStep 3793805 = 1422677) (by norm_num)
theorem B2529203 : Blo 1971435 2529203 := bstep (se 1 (by rfl) ⟨1896902, by rfl⟩ : syracuseStep 2529203 = 3793805) B3793805
theorem B6744541 : Blo 1971435 6744541 := bstep (se 3 (by rfl) ⟨1264601, by rfl⟩ : syracuseStep 6744541 = 2529203) B2529203
theorem B8992721 : Blo 1971435 8992721 := bstep (se 2 (by rfl) ⟨3372270, by rfl⟩ : syracuseStep 8992721 = 6744541) B6744541
theorem B5995147 : Blo 1971435 5995147 := bstep (se 1 (by rfl) ⟨4496360, by rfl⟩ : syracuseStep 5995147 = 8992721) B8992721
theorem B7993529 : Blo 1971435 7993529 := bstep (se 2 (by rfl) ⟨2997573, by rfl⟩ : syracuseStep 7993529 = 5995147) B5995147
theorem B5329019 : Blo 1971435 5329019 := bstep (se 1 (by rfl) ⟨3996764, by rfl⟩ : syracuseStep 5329019 = 7993529) B7993529
theorem B3552679 : Blo 1971435 3552679 := bstep (se 1 (by rfl) ⟨2664509, by rfl⟩ : syracuseStep 3552679 = 5329019) B5329019
theorem B18947621 : Blo 1971435 18947621 := bstep (se 4 (by rfl) ⟨1776339, by rfl⟩ : syracuseStep 18947621 = 3552679) B3552679
theorem B12631747 : Blo 1971435 12631747 := bstep (se 1 (by rfl) ⟨9473810, by rfl⟩ : syracuseStep 12631747 = 18947621) B18947621
theorem B16842329 : Blo 1971435 16842329 := bstep (se 2 (by rfl) ⟨6315873, by rfl⟩ : syracuseStep 16842329 = 12631747) B12631747
theorem B11228219 : Blo 1971435 11228219 := bstep (se 1 (by rfl) ⟨8421164, by rfl⟩ : syracuseStep 11228219 = 16842329) B16842329
theorem B7485479 : Blo 1971435 7485479 := bstep (se 1 (by rfl) ⟨5614109, by rfl⟩ : syracuseStep 7485479 = 11228219) B11228219
theorem B4990319 : Blo 1971435 4990319 := bstep (se 1 (by rfl) ⟨3742739, by rfl⟩ : syracuseStep 4990319 = 7485479) B7485479
theorem B3326879 : Blo 1971435 3326879 := bstep (se 1 (by rfl) ⟨2495159, by rfl⟩ : syracuseStep 3326879 = 4990319) B4990319
theorem B2217919 : Blo 1971435 2217919 := bstep (se 1 (by rfl) ⟨1663439, by rfl⟩ : syracuseStep 2217919 = 3326879) B3326879
theorem B2957225 : Blo 1971435 2957225 := bstep (se 2 (by rfl) ⟨1108959, by rfl⟩ : syracuseStep 2957225 = 2217919) B2217919
theorem B1971483 : Blo 1971435 1971483 := bstep (se 1 (by rfl) ⟨1478612, by rfl⟩ : syracuseStep 1971483 = 2957225) B2957225
theorem B7485493 : Blo 1971435 7485493 := bbase (se 5 (by rfl) ⟨350882, by rfl⟩ : syracuseStep 7485493 = 701765) (by norm_num)
theorem B9980657 : Blo 1971435 9980657 := bstep (se 2 (by rfl) ⟨3742746, by rfl⟩ : syracuseStep 9980657 = 7485493) B7485493
theorem B6653771 : Blo 1971435 6653771 := bstep (se 1 (by rfl) ⟨4990328, by rfl⟩ : syracuseStep 6653771 = 9980657) B9980657
theorem B4435847 : Blo 1971435 4435847 := bstep (se 1 (by rfl) ⟨3326885, by rfl⟩ : syracuseStep 4435847 = 6653771) B6653771
theorem B2957231 : Blo 1971435 2957231 := bstep (se 1 (by rfl) ⟨2217923, by rfl⟩ : syracuseStep 2957231 = 4435847) B4435847
theorem B1971487 : Blo 1971435 1971487 := bstep (se 1 (by rfl) ⟨1478615, by rfl⟩ : syracuseStep 1971487 = 2957231) B2957231
theorem B2957237 : Blo 1971435 2957237 := bbase (se 5 (by rfl) ⟨138620, by rfl⟩ : syracuseStep 2957237 = 277241) (by norm_num)
theorem B1971491 : Blo 1971435 1971491 := bstep (se 1 (by rfl) ⟨1478618, by rfl⟩ : syracuseStep 1971491 = 2957237) B2957237
theorem B4990349 : Blo 1971435 4990349 := bbase (se 3 (by rfl) ⟨935690, by rfl⟩ : syracuseStep 4990349 = 1871381) (by norm_num)
theorem B3326899 : Blo 1971435 3326899 := bstep (se 1 (by rfl) ⟨2495174, by rfl⟩ : syracuseStep 3326899 = 4990349) B4990349
theorem B4435865 : Blo 1971435 4435865 := bstep (se 2 (by rfl) ⟨1663449, by rfl⟩ : syracuseStep 4435865 = 3326899) B3326899
theorem B2957243 : Blo 1971435 2957243 := bstep (se 1 (by rfl) ⟨2217932, by rfl⟩ : syracuseStep 2957243 = 4435865) B4435865
theorem B1971495 : Blo 1971435 1971495 := bstep (se 1 (by rfl) ⟨1478621, by rfl⟩ : syracuseStep 1971495 = 2957243) B2957243
theorem B2217937 : Blo 1971435 2217937 := bbase (se 2 (by rfl) ⟨831726, by rfl⟩ : syracuseStep 2217937 = 1663453) (by norm_num)
theorem B2957249 : Blo 1971435 2957249 := bstep (se 2 (by rfl) ⟨1108968, by rfl⟩ : syracuseStep 2957249 = 2217937) B2217937
theorem B1971499 : Blo 1971435 1971499 := bstep (se 1 (by rfl) ⟨1478624, by rfl⟩ : syracuseStep 1971499 = 2957249) B2957249
theorem B2368477 : Blo 1971435 2368477 := bbase (se 3 (by rfl) ⟨444089, by rfl⟩ : syracuseStep 2368477 = 888179) (by norm_num)
theorem B3157969 : Blo 1971435 3157969 := bstep (se 2 (by rfl) ⟨1184238, by rfl⟩ : syracuseStep 3157969 = 2368477) B2368477
theorem B4210625 : Blo 1971435 4210625 := bstep (se 2 (by rfl) ⟨1578984, by rfl⟩ : syracuseStep 4210625 = 3157969) B3157969
theorem B2807083 : Blo 1971435 2807083 := bstep (se 1 (by rfl) ⟨2105312, by rfl⟩ : syracuseStep 2807083 = 4210625) B4210625
theorem B3742777 : Blo 1971435 3742777 := bstep (se 2 (by rfl) ⟨1403541, by rfl⟩ : syracuseStep 3742777 = 2807083) B2807083
theorem B4990369 : Blo 1971435 4990369 := bstep (se 2 (by rfl) ⟨1871388, by rfl⟩ : syracuseStep 4990369 = 3742777) B3742777
theorem B6653825 : Blo 1971435 6653825 := bstep (se 2 (by rfl) ⟨2495184, by rfl⟩ : syracuseStep 6653825 = 4990369) B4990369
theorem B4435883 : Blo 1971435 4435883 := bstep (se 1 (by rfl) ⟨3326912, by rfl⟩ : syracuseStep 4435883 = 6653825) B6653825
theorem B2957255 : Blo 1971435 2957255 := bstep (se 1 (by rfl) ⟨2217941, by rfl⟩ : syracuseStep 2957255 = 4435883) B4435883
theorem B1971503 : Blo 1971435 1971503 := bstep (se 1 (by rfl) ⟨1478627, by rfl⟩ : syracuseStep 1971503 = 2957255) B2957255
theorem B2957261 : Blo 1971435 2957261 := bbase (se 3 (by rfl) ⟨554486, by rfl⟩ : syracuseStep 2957261 = 1108973) (by norm_num)
theorem B1971507 : Blo 1971435 1971507 := bstep (se 1 (by rfl) ⟨1478630, by rfl⟩ : syracuseStep 1971507 = 2957261) B2957261
theorem B4435901 : Blo 1971435 4435901 := bbase (se 3 (by rfl) ⟨831731, by rfl⟩ : syracuseStep 4435901 = 1663463) (by norm_num)
theorem B2957267 : Blo 1971435 2957267 := bstep (se 1 (by rfl) ⟨2217950, by rfl⟩ : syracuseStep 2957267 = 4435901) B4435901
theorem B1971511 : Blo 1971435 1971511 := bstep (se 1 (by rfl) ⟨1478633, by rfl⟩ : syracuseStep 1971511 = 2957267) B2957267
theorem B3326933 : Blo 1971435 3326933 := bbase (se 7 (by rfl) ⟨38987, by rfl⟩ : syracuseStep 3326933 = 77975) (by norm_num)
theorem B2217955 : Blo 1971435 2217955 := bstep (se 1 (by rfl) ⟨1663466, by rfl⟩ : syracuseStep 2217955 = 3326933) B3326933
theorem B2957273 : Blo 1971435 2957273 := bstep (se 2 (by rfl) ⟨1108977, by rfl⟩ : syracuseStep 2957273 = 2217955) B2217955
theorem B1971515 : Blo 1971435 1971515 := bstep (se 1 (by rfl) ⟨1478636, by rfl⟩ : syracuseStep 1971515 = 2957273) B2957273
theorem B8421317 : Blo 1971435 8421317 := bbase (se 4 (by rfl) ⟨789498, by rfl⟩ : syracuseStep 8421317 = 1578997) (by norm_num)
theorem B5614211 : Blo 1971435 5614211 := bstep (se 1 (by rfl) ⟨4210658, by rfl⟩ : syracuseStep 5614211 = 8421317) B8421317
theorem B14971229 : Blo 1971435 14971229 := bstep (se 3 (by rfl) ⟨2807105, by rfl⟩ : syracuseStep 14971229 = 5614211) B5614211
theorem B9980819 : Blo 1971435 9980819 := bstep (se 1 (by rfl) ⟨7485614, by rfl⟩ : syracuseStep 9980819 = 14971229) B14971229
theorem B6653879 : Blo 1971435 6653879 := bstep (se 1 (by rfl) ⟨4990409, by rfl⟩ : syracuseStep 6653879 = 9980819) B9980819
theorem B4435919 : Blo 1971435 4435919 := bstep (se 1 (by rfl) ⟨3326939, by rfl⟩ : syracuseStep 4435919 = 6653879) B6653879
theorem B2957279 : Blo 1971435 2957279 := bstep (se 1 (by rfl) ⟨2217959, by rfl⟩ : syracuseStep 2957279 = 4435919) B4435919
theorem B1971519 : Blo 1971435 1971519 := bstep (se 1 (by rfl) ⟨1478639, by rfl⟩ : syracuseStep 1971519 = 2957279) B2957279
theorem B2957285 : Blo 1971435 2957285 := bbase (se 4 (by rfl) ⟨277245, by rfl⟩ : syracuseStep 2957285 = 554491) (by norm_num)
theorem B1971523 : Blo 1971435 1971523 := bstep (se 1 (by rfl) ⟨1478642, by rfl⟩ : syracuseStep 1971523 = 2957285) B2957285
theorem B2563769 : Blo 1971435 2563769 := bbase (se 2 (by rfl) ⟨961413, by rfl⟩ : syracuseStep 2563769 = 1922827) (by norm_num)
theorem B6836717 : Blo 1971435 6836717 := bstep (se 3 (by rfl) ⟨1281884, by rfl⟩ : syracuseStep 6836717 = 2563769) B2563769
theorem B4557811 : Blo 1971435 4557811 := bstep (se 1 (by rfl) ⟨3418358, by rfl⟩ : syracuseStep 4557811 = 6836717) B6836717
theorem B6077081 : Blo 1971435 6077081 := bstep (se 2 (by rfl) ⟨2278905, by rfl⟩ : syracuseStep 6077081 = 4557811) B4557811
theorem B4051387 : Blo 1971435 4051387 := bstep (se 1 (by rfl) ⟨3038540, by rfl⟩ : syracuseStep 4051387 = 6077081) B6077081
theorem B5401849 : Blo 1971435 5401849 := bstep (se 2 (by rfl) ⟨2025693, by rfl⟩ : syracuseStep 5401849 = 4051387) B4051387
theorem B7202465 : Blo 1971435 7202465 := bstep (se 2 (by rfl) ⟨2700924, by rfl⟩ : syracuseStep 7202465 = 5401849) B5401849
theorem B4801643 : Blo 1971435 4801643 := bstep (se 1 (by rfl) ⟨3601232, by rfl⟩ : syracuseStep 4801643 = 7202465) B7202465
theorem B3201095 : Blo 1971435 3201095 := bstep (se 1 (by rfl) ⟨2400821, by rfl⟩ : syracuseStep 3201095 = 4801643) B4801643
theorem B2134063 : Blo 1971435 2134063 := bstep (se 1 (by rfl) ⟨1600547, by rfl⟩ : syracuseStep 2134063 = 3201095) B3201095
theorem B2845417 : Blo 1971435 2845417 := bstep (se 2 (by rfl) ⟨1067031, by rfl⟩ : syracuseStep 2845417 = 2134063) B2134063
theorem B3793889 : Blo 1971435 3793889 := bstep (se 2 (by rfl) ⟨1422708, by rfl⟩ : syracuseStep 3793889 = 2845417) B2845417
theorem B10117037 : Blo 1971435 10117037 := bstep (se 3 (by rfl) ⟨1896944, by rfl⟩ : syracuseStep 10117037 = 3793889) B3793889
theorem B6744691 : Blo 1971435 6744691 := bstep (se 1 (by rfl) ⟨5058518, by rfl⟩ : syracuseStep 6744691 = 10117037) B10117037
theorem B35971685 : Blo 1971435 35971685 := bstep (se 4 (by rfl) ⟨3372345, by rfl⟩ : syracuseStep 35971685 = 6744691) B6744691
theorem B23981123 : Blo 1971435 23981123 := bstep (se 1 (by rfl) ⟨17985842, by rfl⟩ : syracuseStep 23981123 = 35971685) B35971685
theorem B15987415 : Blo 1971435 15987415 := bstep (se 1 (by rfl) ⟨11990561, by rfl⟩ : syracuseStep 15987415 = 23981123) B23981123
theorem B21316553 : Blo 1971435 21316553 := bstep (se 2 (by rfl) ⟨7993707, by rfl⟩ : syracuseStep 21316553 = 15987415) B15987415
theorem B14211035 : Blo 1971435 14211035 := bstep (se 1 (by rfl) ⟨10658276, by rfl⟩ : syracuseStep 14211035 = 21316553) B21316553
theorem B9474023 : Blo 1971435 9474023 := bstep (se 1 (by rfl) ⟨7105517, by rfl⟩ : syracuseStep 9474023 = 14211035) B14211035
theorem B6316015 : Blo 1971435 6316015 := bstep (se 1 (by rfl) ⟨4737011, by rfl⟩ : syracuseStep 6316015 = 9474023) B9474023
theorem B8421353 : Blo 1971435 8421353 := bstep (se 2 (by rfl) ⟨3158007, by rfl⟩ : syracuseStep 8421353 = 6316015) B6316015
theorem B5614235 : Blo 1971435 5614235 := bstep (se 1 (by rfl) ⟨4210676, by rfl⟩ : syracuseStep 5614235 = 8421353) B8421353
theorem B3742823 : Blo 1971435 3742823 := bstep (se 1 (by rfl) ⟨2807117, by rfl⟩ : syracuseStep 3742823 = 5614235) B5614235
theorem B2495215 : Blo 1971435 2495215 := bstep (se 1 (by rfl) ⟨1871411, by rfl⟩ : syracuseStep 2495215 = 3742823) B3742823
theorem B3326953 : Blo 1971435 3326953 := bstep (se 2 (by rfl) ⟨1247607, by rfl⟩ : syracuseStep 3326953 = 2495215) B2495215
theorem B4435937 : Blo 1971435 4435937 := bstep (se 2 (by rfl) ⟨1663476, by rfl⟩ : syracuseStep 4435937 = 3326953) B3326953
theorem B2957291 : Blo 1971435 2957291 := bstep (se 1 (by rfl) ⟨2217968, by rfl⟩ : syracuseStep 2957291 = 4435937) B4435937
theorem B1971527 : Blo 1971435 1971527 := bstep (se 1 (by rfl) ⟨1478645, by rfl⟩ : syracuseStep 1971527 = 2957291) B2957291
theorem B2217973 : Blo 1971435 2217973 := bbase (se 5 (by rfl) ⟨103967, by rfl⟩ : syracuseStep 2217973 = 207935) (by norm_num)
theorem B2957297 : Blo 1971435 2957297 := bstep (se 2 (by rfl) ⟨1108986, by rfl⟩ : syracuseStep 2957297 = 2217973) B2217973
theorem B1971531 : Blo 1971435 1971531 := bstep (se 1 (by rfl) ⟨1478648, by rfl⟩ : syracuseStep 1971531 = 2957297) B2957297
theorem B2495225 : Blo 1971435 2495225 := bbase (se 2 (by rfl) ⟨935709, by rfl⟩ : syracuseStep 2495225 = 1871419) (by norm_num)
theorem B6653933 : Blo 1971435 6653933 := bstep (se 3 (by rfl) ⟨1247612, by rfl⟩ : syracuseStep 6653933 = 2495225) B2495225
theorem B4435955 : Blo 1971435 4435955 := bstep (se 1 (by rfl) ⟨3326966, by rfl⟩ : syracuseStep 4435955 = 6653933) B6653933
theorem B2957303 : Blo 1971435 2957303 := bstep (se 1 (by rfl) ⟨2217977, by rfl⟩ : syracuseStep 2957303 = 4435955) B4435955
theorem B1971535 : Blo 1971435 1971535 := bstep (se 1 (by rfl) ⟨1478651, by rfl⟩ : syracuseStep 1971535 = 2957303) B2957303
theorem B2957309 : Blo 1971435 2957309 := bbase (se 3 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 2957309 = 1108991) (by norm_num)
theorem B1971539 : Blo 1971435 1971539 := bstep (se 1 (by rfl) ⟨1478654, by rfl⟩ : syracuseStep 1971539 = 2957309) B2957309
theorem B4435973 : Blo 1971435 4435973 := bbase (se 4 (by rfl) ⟨415872, by rfl⟩ : syracuseStep 4435973 = 831745) (by norm_num)
theorem B2957315 : Blo 1971435 2957315 := bstep (se 1 (by rfl) ⟨2217986, by rfl⟩ : syracuseStep 2957315 = 4435973) B4435973
theorem B1971543 : Blo 1971435 1971543 := bstep (se 1 (by rfl) ⟨1478657, by rfl⟩ : syracuseStep 1971543 = 2957315) B2957315
theorem B3742861 : Blo 1971435 3742861 := bbase (se 3 (by rfl) ⟨701786, by rfl⟩ : syracuseStep 3742861 = 1403573) (by norm_num)
theorem B4990481 : Blo 1971435 4990481 := bstep (se 2 (by rfl) ⟨1871430, by rfl⟩ : syracuseStep 4990481 = 3742861) B3742861
theorem B3326987 : Blo 1971435 3326987 := bstep (se 1 (by rfl) ⟨2495240, by rfl⟩ : syracuseStep 3326987 = 4990481) B4990481
theorem B2217991 : Blo 1971435 2217991 := bstep (se 1 (by rfl) ⟨1663493, by rfl⟩ : syracuseStep 2217991 = 3326987) B3326987
theorem B2957321 : Blo 1971435 2957321 := bstep (se 2 (by rfl) ⟨1108995, by rfl⟩ : syracuseStep 2957321 = 2217991) B2217991
theorem B1971547 : Blo 1971435 1971547 := bstep (se 1 (by rfl) ⟨1478660, by rfl⟩ : syracuseStep 1971547 = 2957321) B2957321
theorem B9980981 : Blo 1971435 9980981 := bbase (se 5 (by rfl) ⟨467858, by rfl⟩ : syracuseStep 9980981 = 935717) (by norm_num)
theorem B6653987 : Blo 1971435 6653987 := bstep (se 1 (by rfl) ⟨4990490, by rfl⟩ : syracuseStep 6653987 = 9980981) B9980981
theorem B4435991 : Blo 1971435 4435991 := bstep (se 1 (by rfl) ⟨3326993, by rfl⟩ : syracuseStep 4435991 = 6653987) B6653987
theorem B2957327 : Blo 1971435 2957327 := bstep (se 1 (by rfl) ⟨2217995, by rfl⟩ : syracuseStep 2957327 = 4435991) B4435991
theorem B1971551 : Blo 1971435 1971551 := bstep (se 1 (by rfl) ⟨1478663, by rfl⟩ : syracuseStep 1971551 = 2957327) B2957327
theorem B2957333 : Blo 1971435 2957333 := bbase (se 6 (by rfl) ⟨69312, by rfl⟩ : syracuseStep 2957333 = 138625) (by norm_num)
theorem B1971555 : Blo 1971435 1971555 := bstep (se 1 (by rfl) ⟨1478666, by rfl⟩ : syracuseStep 1971555 = 2957333) B2957333
theorem B7691429 : Blo 1971435 7691429 := bbase (se 4 (by rfl) ⟨721071, by rfl⟩ : syracuseStep 7691429 = 1442143) (by norm_num)
theorem B5127619 : Blo 1971435 5127619 := bstep (se 1 (by rfl) ⟨3845714, by rfl⟩ : syracuseStep 5127619 = 7691429) B7691429
theorem B6836825 : Blo 1971435 6836825 := bstep (se 2 (by rfl) ⟨2563809, by rfl⟩ : syracuseStep 6836825 = 5127619) B5127619
theorem B4557883 : Blo 1971435 4557883 := bstep (se 1 (by rfl) ⟨3418412, by rfl⟩ : syracuseStep 4557883 = 6836825) B6836825
theorem B6077177 : Blo 1971435 6077177 := bstep (se 2 (by rfl) ⟨2278941, by rfl⟩ : syracuseStep 6077177 = 4557883) B4557883
theorem B4051451 : Blo 1971435 4051451 := bstep (se 1 (by rfl) ⟨3038588, by rfl⟩ : syracuseStep 4051451 = 6077177) B6077177
theorem B2700967 : Blo 1971435 2700967 := bstep (se 1 (by rfl) ⟨2025725, by rfl⟩ : syracuseStep 2700967 = 4051451) B4051451
theorem B3601289 : Blo 1971435 3601289 := bstep (se 2 (by rfl) ⟨1350483, by rfl⟩ : syracuseStep 3601289 = 2700967) B2700967
theorem B2400859 : Blo 1971435 2400859 := bstep (se 1 (by rfl) ⟨1800644, by rfl⟩ : syracuseStep 2400859 = 3601289) B3601289
theorem B12804581 : Blo 1971435 12804581 := bstep (se 4 (by rfl) ⟨1200429, by rfl⟩ : syracuseStep 12804581 = 2400859) B2400859
theorem B8536387 : Blo 1971435 8536387 := bstep (se 1 (by rfl) ⟨6402290, by rfl⟩ : syracuseStep 8536387 = 12804581) B12804581
theorem B11381849 : Blo 1971435 11381849 := bstep (se 2 (by rfl) ⟨4268193, by rfl⟩ : syracuseStep 11381849 = 8536387) B8536387
theorem B7587899 : Blo 1971435 7587899 := bstep (se 1 (by rfl) ⟨5690924, by rfl⟩ : syracuseStep 7587899 = 11381849) B11381849
theorem B80937589 : Blo 1971435 80937589 := bstep (se 5 (by rfl) ⟨3793949, by rfl⟩ : syracuseStep 80937589 = 7587899) B7587899
theorem B107916785 : Blo 1971435 107916785 := bstep (se 2 (by rfl) ⟨40468794, by rfl⟩ : syracuseStep 107916785 = 80937589) B80937589
theorem B71944523 : Blo 1971435 71944523 := bstep (se 1 (by rfl) ⟨53958392, by rfl⟩ : syracuseStep 71944523 = 107916785) B107916785
theorem B47963015 : Blo 1971435 47963015 := bstep (se 1 (by rfl) ⟨35972261, by rfl⟩ : syracuseStep 47963015 = 71944523) B71944523
theorem B31975343 : Blo 1971435 31975343 := bstep (se 1 (by rfl) ⟨23981507, by rfl⟩ : syracuseStep 31975343 = 47963015) B47963015
theorem B21316895 : Blo 1971435 21316895 := bstep (se 1 (by rfl) ⟨15987671, by rfl⟩ : syracuseStep 21316895 = 31975343) B31975343
theorem B14211263 : Blo 1971435 14211263 := bstep (se 1 (by rfl) ⟨10658447, by rfl⟩ : syracuseStep 14211263 = 21316895) B21316895
theorem B9474175 : Blo 1971435 9474175 := bstep (se 1 (by rfl) ⟨7105631, by rfl⟩ : syracuseStep 9474175 = 14211263) B14211263
theorem B12632233 : Blo 1971435 12632233 := bstep (se 2 (by rfl) ⟨4737087, by rfl⟩ : syracuseStep 12632233 = 9474175) B9474175
theorem B16842977 : Blo 1971435 16842977 := bstep (se 2 (by rfl) ⟨6316116, by rfl⟩ : syracuseStep 16842977 = 12632233) B12632233
theorem B11228651 : Blo 1971435 11228651 := bstep (se 1 (by rfl) ⟨8421488, by rfl⟩ : syracuseStep 11228651 = 16842977) B16842977
theorem B7485767 : Blo 1971435 7485767 := bstep (se 1 (by rfl) ⟨5614325, by rfl⟩ : syracuseStep 7485767 = 11228651) B11228651
theorem B4990511 : Blo 1971435 4990511 := bstep (se 1 (by rfl) ⟨3742883, by rfl⟩ : syracuseStep 4990511 = 7485767) B7485767
theorem B3327007 : Blo 1971435 3327007 := bstep (se 1 (by rfl) ⟨2495255, by rfl⟩ : syracuseStep 3327007 = 4990511) B4990511
theorem B4436009 : Blo 1971435 4436009 := bstep (se 2 (by rfl) ⟨1663503, by rfl⟩ : syracuseStep 4436009 = 3327007) B3327007
theorem B2957339 : Blo 1971435 2957339 := bstep (se 1 (by rfl) ⟨2218004, by rfl⟩ : syracuseStep 2957339 = 4436009) B4436009
theorem B1971559 : Blo 1971435 1971559 := bstep (se 1 (by rfl) ⟨1478669, by rfl⟩ : syracuseStep 1971559 = 2957339) B2957339
theorem B2218009 : Blo 1971435 2218009 := bbase (se 2 (by rfl) ⟨831753, by rfl⟩ : syracuseStep 2218009 = 1663507) (by norm_num)
theorem B2957345 : Blo 1971435 2957345 := bstep (se 2 (by rfl) ⟨1109004, by rfl⟩ : syracuseStep 2957345 = 2218009) B2218009
theorem B1971563 : Blo 1971435 1971563 := bstep (se 1 (by rfl) ⟨1478672, by rfl⟩ : syracuseStep 1971563 = 2957345) B2957345
theorem B7485797 : Blo 1971435 7485797 := bbase (se 4 (by rfl) ⟨701793, by rfl⟩ : syracuseStep 7485797 = 1403587) (by norm_num)
theorem B4990531 : Blo 1971435 4990531 := bstep (se 1 (by rfl) ⟨3742898, by rfl⟩ : syracuseStep 4990531 = 7485797) B7485797
theorem B6654041 : Blo 1971435 6654041 := bstep (se 2 (by rfl) ⟨2495265, by rfl⟩ : syracuseStep 6654041 = 4990531) B4990531
theorem B4436027 : Blo 1971435 4436027 := bstep (se 1 (by rfl) ⟨3327020, by rfl⟩ : syracuseStep 4436027 = 6654041) B6654041
theorem B2957351 : Blo 1971435 2957351 := bstep (se 1 (by rfl) ⟨2218013, by rfl⟩ : syracuseStep 2957351 = 4436027) B4436027
theorem B1971567 : Blo 1971435 1971567 := bstep (se 1 (by rfl) ⟨1478675, by rfl⟩ : syracuseStep 1971567 = 2957351) B2957351
theorem B2957357 : Blo 1971435 2957357 := bbase (se 3 (by rfl) ⟨554504, by rfl⟩ : syracuseStep 2957357 = 1109009) (by norm_num)
theorem B1971571 : Blo 1971435 1971571 := bstep (se 1 (by rfl) ⟨1478678, by rfl⟩ : syracuseStep 1971571 = 2957357) B2957357
theorem B4436045 : Blo 1971435 4436045 := bbase (se 3 (by rfl) ⟨831758, by rfl⟩ : syracuseStep 4436045 = 1663517) (by norm_num)
theorem B2957363 : Blo 1971435 2957363 := bstep (se 1 (by rfl) ⟨2218022, by rfl⟩ : syracuseStep 2957363 = 4436045) B4436045
theorem B1971575 : Blo 1971435 1971575 := bstep (se 1 (by rfl) ⟨1478681, by rfl⟩ : syracuseStep 1971575 = 2957363) B2957363
theorem B2495281 : Blo 1971435 2495281 := bbase (se 2 (by rfl) ⟨935730, by rfl⟩ : syracuseStep 2495281 = 1871461) (by norm_num)
theorem B3327041 : Blo 1971435 3327041 := bstep (se 2 (by rfl) ⟨1247640, by rfl⟩ : syracuseStep 3327041 = 2495281) B2495281
theorem B2218027 : Blo 1971435 2218027 := bstep (se 1 (by rfl) ⟨1663520, by rfl⟩ : syracuseStep 2218027 = 3327041) B3327041
theorem B2957369 : Blo 1971435 2957369 := bstep (se 2 (by rfl) ⟨1109013, by rfl⟩ : syracuseStep 2957369 = 2218027) B2218027
theorem B1971579 : Blo 1971435 1971579 := bstep (se 1 (by rfl) ⟨1478684, by rfl⟩ : syracuseStep 1971579 = 2957369) B2957369
theorem B3793997 : Blo 1971435 3793997 := bbase (se 3 (by rfl) ⟨711374, by rfl⟩ : syracuseStep 3793997 = 1422749) (by norm_num)
theorem B10117325 : Blo 1971435 10117325 := bstep (se 3 (by rfl) ⟨1896998, by rfl⟩ : syracuseStep 10117325 = 3793997) B3793997
theorem B6744883 : Blo 1971435 6744883 := bstep (se 1 (by rfl) ⟨5058662, by rfl⟩ : syracuseStep 6744883 = 10117325) B10117325
theorem B8993177 : Blo 1971435 8993177 := bstep (se 2 (by rfl) ⟨3372441, by rfl⟩ : syracuseStep 8993177 = 6744883) B6744883
theorem B5995451 : Blo 1971435 5995451 := bstep (se 1 (by rfl) ⟨4496588, by rfl⟩ : syracuseStep 5995451 = 8993177) B8993177
theorem B3996967 : Blo 1971435 3996967 := bstep (se 1 (by rfl) ⟨2997725, by rfl⟩ : syracuseStep 3996967 = 5995451) B5995451
theorem B5329289 : Blo 1971435 5329289 := bstep (se 2 (by rfl) ⟨1998483, by rfl⟩ : syracuseStep 5329289 = 3996967) B3996967
theorem B3552859 : Blo 1971435 3552859 := bstep (se 1 (by rfl) ⟨2664644, by rfl⟩ : syracuseStep 3552859 = 5329289) B5329289
theorem B4737145 : Blo 1971435 4737145 := bstep (se 2 (by rfl) ⟨1776429, by rfl⟩ : syracuseStep 4737145 = 3552859) B3552859
theorem B6316193 : Blo 1971435 6316193 := bstep (se 2 (by rfl) ⟨2368572, by rfl⟩ : syracuseStep 6316193 = 4737145) B4737145
theorem B4210795 : Blo 1971435 4210795 := bstep (se 1 (by rfl) ⟨3158096, by rfl⟩ : syracuseStep 4210795 = 6316193) B6316193
theorem B22457573 : Blo 1971435 22457573 := bstep (se 4 (by rfl) ⟨2105397, by rfl⟩ : syracuseStep 22457573 = 4210795) B4210795
theorem B14971715 : Blo 1971435 14971715 := bstep (se 1 (by rfl) ⟨11228786, by rfl⟩ : syracuseStep 14971715 = 22457573) B22457573
theorem B9981143 : Blo 1971435 9981143 := bstep (se 1 (by rfl) ⟨7485857, by rfl⟩ : syracuseStep 9981143 = 14971715) B14971715
theorem B6654095 : Blo 1971435 6654095 := bstep (se 1 (by rfl) ⟨4990571, by rfl⟩ : syracuseStep 6654095 = 9981143) B9981143
theorem B4436063 : Blo 1971435 4436063 := bstep (se 1 (by rfl) ⟨3327047, by rfl⟩ : syracuseStep 4436063 = 6654095) B6654095
theorem B2957375 : Blo 1971435 2957375 := bstep (se 1 (by rfl) ⟨2218031, by rfl⟩ : syracuseStep 2957375 = 4436063) B4436063
theorem B1971583 : Blo 1971435 1971583 := bstep (se 1 (by rfl) ⟨1478687, by rfl⟩ : syracuseStep 1971583 = 2957375) B2957375
theorem B2957381 : Blo 1971435 2957381 := bbase (se 4 (by rfl) ⟨277254, by rfl⟩ : syracuseStep 2957381 = 554509) (by norm_num)
theorem B1971587 : Blo 1971435 1971587 := bstep (se 1 (by rfl) ⟨1478690, by rfl⟩ : syracuseStep 1971587 = 2957381) B2957381
theorem B3327061 : Blo 1971435 3327061 := bbase (se 8 (by rfl) ⟨19494, by rfl⟩ : syracuseStep 3327061 = 38989) (by norm_num)
theorem B4436081 : Blo 1971435 4436081 := bstep (se 2 (by rfl) ⟨1663530, by rfl⟩ : syracuseStep 4436081 = 3327061) B3327061
theorem B2957387 : Blo 1971435 2957387 := bstep (se 1 (by rfl) ⟨2218040, by rfl⟩ : syracuseStep 2957387 = 4436081) B4436081
theorem B1971591 : Blo 1971435 1971591 := bstep (se 1 (by rfl) ⟨1478693, by rfl⟩ : syracuseStep 1971591 = 2957387) B2957387
theorem B2218045 : Blo 1971435 2218045 := bbase (se 3 (by rfl) ⟨415883, by rfl⟩ : syracuseStep 2218045 = 831767) (by norm_num)
theorem B2957393 : Blo 1971435 2957393 := bstep (se 2 (by rfl) ⟨1109022, by rfl⟩ : syracuseStep 2957393 = 2218045) B2218045
theorem B1971595 : Blo 1971435 1971595 := bstep (se 1 (by rfl) ⟨1478696, by rfl⟩ : syracuseStep 1971595 = 2957393) B2957393
theorem B6654149 : Blo 1971435 6654149 := bbase (se 4 (by rfl) ⟨623826, by rfl⟩ : syracuseStep 6654149 = 1247653) (by norm_num)
theorem B4436099 : Blo 1971435 4436099 := bstep (se 1 (by rfl) ⟨3327074, by rfl⟩ : syracuseStep 4436099 = 6654149) B6654149
theorem B2957399 : Blo 1971435 2957399 := bstep (se 1 (by rfl) ⟨2218049, by rfl⟩ : syracuseStep 2957399 = 4436099) B4436099
theorem B1971599 : Blo 1971435 1971599 := bstep (se 1 (by rfl) ⟨1478699, by rfl⟩ : syracuseStep 1971599 = 2957399) B2957399
theorem B2957405 : Blo 1971435 2957405 := bbase (se 3 (by rfl) ⟨554513, by rfl⟩ : syracuseStep 2957405 = 1109027) (by norm_num)
theorem B1971603 : Blo 1971435 1971603 := bstep (se 1 (by rfl) ⟨1478702, by rfl⟩ : syracuseStep 1971603 = 2957405) B2957405
theorem B4436117 : Blo 1971435 4436117 := bbase (se 6 (by rfl) ⟨103971, by rfl⟩ : syracuseStep 4436117 = 207943) (by norm_num)
theorem B2957411 : Blo 1971435 2957411 := bstep (se 1 (by rfl) ⟨2218058, by rfl⟩ : syracuseStep 2957411 = 4436117) B4436117
theorem B1971607 : Blo 1971435 1971607 := bstep (se 1 (by rfl) ⟨1478705, by rfl⟩ : syracuseStep 1971607 = 2957411) B2957411
theorem B2807237 : Blo 1971435 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B7485965 : Blo 1971435 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B4990643 : Blo 1971435 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B3327095 : Blo 1971435 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B2218063 : Blo 1971435 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B2957417 : Blo 1971435 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B1971611 : Blo 1971435 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B9734741 : Blo 1971435 9734741 := bbase (se 8 (by rfl) ⟨57039, by rfl⟩ : syracuseStep 9734741 = 114079) (by norm_num)
theorem B6489827 : Blo 1971435 6489827 := bstep (se 1 (by rfl) ⟨4867370, by rfl⟩ : syracuseStep 6489827 = 9734741) B9734741
theorem B4326551 : Blo 1971435 4326551 := bstep (se 1 (by rfl) ⟨3244913, by rfl⟩ : syracuseStep 4326551 = 6489827) B6489827
theorem B2884367 : Blo 1971435 2884367 := bstep (se 1 (by rfl) ⟨2163275, by rfl⟩ : syracuseStep 2884367 = 4326551) B4326551
theorem B7691645 : Blo 1971435 7691645 := bstep (se 3 (by rfl) ⟨1442183, by rfl⟩ : syracuseStep 7691645 = 2884367) B2884367
theorem B20511053 : Blo 1971435 20511053 := bstep (se 3 (by rfl) ⟨3845822, by rfl⟩ : syracuseStep 20511053 = 7691645) B7691645
theorem B13674035 : Blo 1971435 13674035 := bstep (se 1 (by rfl) ⟨10255526, by rfl⟩ : syracuseStep 13674035 = 20511053) B20511053
theorem B9116023 : Blo 1971435 9116023 := bstep (se 1 (by rfl) ⟨6837017, by rfl⟩ : syracuseStep 9116023 = 13674035) B13674035
theorem B12154697 : Blo 1971435 12154697 := bstep (se 2 (by rfl) ⟨4558011, by rfl⟩ : syracuseStep 12154697 = 9116023) B9116023
theorem B8103131 : Blo 1971435 8103131 := bstep (se 1 (by rfl) ⟨6077348, by rfl⟩ : syracuseStep 8103131 = 12154697) B12154697
theorem B5402087 : Blo 1971435 5402087 := bstep (se 1 (by rfl) ⟨4051565, by rfl⟩ : syracuseStep 5402087 = 8103131) B8103131
theorem B3601391 : Blo 1971435 3601391 := bstep (se 1 (by rfl) ⟨2701043, by rfl⟩ : syracuseStep 3601391 = 5402087) B5402087
theorem B38414837 : Blo 1971435 38414837 := bstep (se 5 (by rfl) ⟨1800695, by rfl⟩ : syracuseStep 38414837 = 3601391) B3601391
theorem B25609891 : Blo 1971435 25609891 := bstep (se 1 (by rfl) ⟨19207418, by rfl⟩ : syracuseStep 25609891 = 38414837) B38414837
theorem B34146521 : Blo 1971435 34146521 := bstep (se 2 (by rfl) ⟨12804945, by rfl⟩ : syracuseStep 34146521 = 25609891) B25609891
theorem B22764347 : Blo 1971435 22764347 := bstep (se 1 (by rfl) ⟨17073260, by rfl⟩ : syracuseStep 22764347 = 34146521) B34146521
theorem B15176231 : Blo 1971435 15176231 := bstep (se 1 (by rfl) ⟨11382173, by rfl⟩ : syracuseStep 15176231 = 22764347) B22764347
theorem B10117487 : Blo 1971435 10117487 := bstep (se 1 (by rfl) ⟨7588115, by rfl⟩ : syracuseStep 10117487 = 15176231) B15176231
theorem B6744991 : Blo 1971435 6744991 := bstep (se 1 (by rfl) ⟨5058743, by rfl⟩ : syracuseStep 6744991 = 10117487) B10117487
theorem B8993321 : Blo 1971435 8993321 := bstep (se 2 (by rfl) ⟨3372495, by rfl⟩ : syracuseStep 8993321 = 6744991) B6744991
theorem B5995547 : Blo 1971435 5995547 := bstep (se 1 (by rfl) ⟨4496660, by rfl⟩ : syracuseStep 5995547 = 8993321) B8993321
theorem B3997031 : Blo 1971435 3997031 := bstep (se 1 (by rfl) ⟨2997773, by rfl⟩ : syracuseStep 3997031 = 5995547) B5995547
theorem B42634997 : Blo 1971435 42634997 := bstep (se 5 (by rfl) ⟨1998515, by rfl⟩ : syracuseStep 42634997 = 3997031) B3997031
theorem B28423331 : Blo 1971435 28423331 := bstep (se 1 (by rfl) ⟨21317498, by rfl⟩ : syracuseStep 28423331 = 42634997) B42634997
theorem B18948887 : Blo 1971435 18948887 := bstep (se 1 (by rfl) ⟨14211665, by rfl⟩ : syracuseStep 18948887 = 28423331) B28423331
theorem B12632591 : Blo 1971435 12632591 := bstep (se 1 (by rfl) ⟨9474443, by rfl⟩ : syracuseStep 12632591 = 18948887) B18948887
theorem B8421727 : Blo 1971435 8421727 := bstep (se 1 (by rfl) ⟨6316295, by rfl⟩ : syracuseStep 8421727 = 12632591) B12632591
theorem B11228969 : Blo 1971435 11228969 := bstep (se 2 (by rfl) ⟨4210863, by rfl⟩ : syracuseStep 11228969 = 8421727) B8421727
theorem B7485979 : Blo 1971435 7485979 := bstep (se 1 (by rfl) ⟨5614484, by rfl⟩ : syracuseStep 7485979 = 11228969) B11228969
theorem B9981305 : Blo 1971435 9981305 := bstep (se 2 (by rfl) ⟨3742989, by rfl⟩ : syracuseStep 9981305 = 7485979) B7485979
theorem B6654203 : Blo 1971435 6654203 := bstep (se 1 (by rfl) ⟨4990652, by rfl⟩ : syracuseStep 6654203 = 9981305) B9981305
theorem B4436135 : Blo 1971435 4436135 := bstep (se 1 (by rfl) ⟨3327101, by rfl⟩ : syracuseStep 4436135 = 6654203) B6654203
theorem B2957423 : Blo 1971435 2957423 := bstep (se 1 (by rfl) ⟨2218067, by rfl⟩ : syracuseStep 2957423 = 4436135) B4436135
theorem B1971615 : Blo 1971435 1971615 := bstep (se 1 (by rfl) ⟨1478711, by rfl⟩ : syracuseStep 1971615 = 2957423) B2957423
theorem B2957429 : Blo 1971435 2957429 := bbase (se 5 (by rfl) ⟨138629, by rfl⟩ : syracuseStep 2957429 = 277259) (by norm_num)
theorem B1971619 : Blo 1971435 1971619 := bstep (se 1 (by rfl) ⟨1478714, by rfl⟩ : syracuseStep 1971619 = 2957429) B2957429
theorem B3743005 : Blo 1971435 3743005 := bbase (se 3 (by rfl) ⟨701813, by rfl⟩ : syracuseStep 3743005 = 1403627) (by norm_num)
theorem B4990673 : Blo 1971435 4990673 := bstep (se 2 (by rfl) ⟨1871502, by rfl⟩ : syracuseStep 4990673 = 3743005) B3743005
theorem B3327115 : Blo 1971435 3327115 := bstep (se 1 (by rfl) ⟨2495336, by rfl⟩ : syracuseStep 3327115 = 4990673) B4990673
theorem B4436153 : Blo 1971435 4436153 := bstep (se 2 (by rfl) ⟨1663557, by rfl⟩ : syracuseStep 4436153 = 3327115) B3327115
theorem B2957435 : Blo 1971435 2957435 := bstep (se 1 (by rfl) ⟨2218076, by rfl⟩ : syracuseStep 2957435 = 4436153) B4436153
theorem B1971623 : Blo 1971435 1971623 := bstep (se 1 (by rfl) ⟨1478717, by rfl⟩ : syracuseStep 1971623 = 2957435) B2957435
theorem B2218081 : Blo 1971435 2218081 := bbase (se 2 (by rfl) ⟨831780, by rfl⟩ : syracuseStep 2218081 = 1663561) (by norm_num)
theorem B2957441 : Blo 1971435 2957441 := bstep (se 2 (by rfl) ⟨1109040, by rfl⟩ : syracuseStep 2957441 = 2218081) B2218081
theorem B1971627 : Blo 1971435 1971627 := bstep (se 1 (by rfl) ⟨1478720, by rfl⟩ : syracuseStep 1971627 = 2957441) B2957441
theorem B4990693 : Blo 1971435 4990693 := bbase (se 4 (by rfl) ⟨467877, by rfl⟩ : syracuseStep 4990693 = 935755) (by norm_num)
theorem B6654257 : Blo 1971435 6654257 := bstep (se 2 (by rfl) ⟨2495346, by rfl⟩ : syracuseStep 6654257 = 4990693) B4990693
theorem B4436171 : Blo 1971435 4436171 := bstep (se 1 (by rfl) ⟨3327128, by rfl⟩ : syracuseStep 4436171 = 6654257) B6654257
theorem B2957447 : Blo 1971435 2957447 := bstep (se 1 (by rfl) ⟨2218085, by rfl⟩ : syracuseStep 2957447 = 4436171) B4436171
theorem B1971631 : Blo 1971435 1971631 := bstep (se 1 (by rfl) ⟨1478723, by rfl⟩ : syracuseStep 1971631 = 2957447) B2957447
theorem B2957453 : Blo 1971435 2957453 := bbase (se 3 (by rfl) ⟨554522, by rfl⟩ : syracuseStep 2957453 = 1109045) (by norm_num)
theorem B1971635 : Blo 1971435 1971635 := bstep (se 1 (by rfl) ⟨1478726, by rfl⟩ : syracuseStep 1971635 = 2957453) B2957453
theorem B4436189 : Blo 1971435 4436189 := bbase (se 3 (by rfl) ⟨831785, by rfl⟩ : syracuseStep 4436189 = 1663571) (by norm_num)
theorem B2957459 : Blo 1971435 2957459 := bstep (se 1 (by rfl) ⟨2218094, by rfl⟩ : syracuseStep 2957459 = 4436189) B4436189
theorem B1971639 : Blo 1971435 1971639 := bstep (se 1 (by rfl) ⟨1478729, by rfl⟩ : syracuseStep 1971639 = 2957459) B2957459
theorem B3327149 : Blo 1971435 3327149 := bbase (se 3 (by rfl) ⟨623840, by rfl⟩ : syracuseStep 3327149 = 1247681) (by norm_num)
theorem B2218099 : Blo 1971435 2218099 := bstep (se 1 (by rfl) ⟨1663574, by rfl⟩ : syracuseStep 2218099 = 3327149) B3327149
theorem B2957465 : Blo 1971435 2957465 := bstep (se 2 (by rfl) ⟨1109049, by rfl⟩ : syracuseStep 2957465 = 2218099) B2218099
theorem B1971643 : Blo 1971435 1971643 := bstep (se 1 (by rfl) ⟨1478732, by rfl⟩ : syracuseStep 1971643 = 2957465) B2957465
theorem B2845589 : Blo 1971435 2845589 := bbase (se 6 (by rfl) ⟨66693, by rfl⟩ : syracuseStep 2845589 = 133387) (by norm_num)
theorem B7588237 : Blo 1971435 7588237 := bstep (se 3 (by rfl) ⟨1422794, by rfl⟩ : syracuseStep 7588237 = 2845589) B2845589
theorem B10117649 : Blo 1971435 10117649 := bstep (se 2 (by rfl) ⟨3794118, by rfl⟩ : syracuseStep 10117649 = 7588237) B7588237
theorem B26980397 : Blo 1971435 26980397 := bstep (se 3 (by rfl) ⟨5058824, by rfl⟩ : syracuseStep 26980397 = 10117649) B10117649
theorem B17986931 : Blo 1971435 17986931 := bstep (se 1 (by rfl) ⟨13490198, by rfl⟩ : syracuseStep 17986931 = 26980397) B26980397
theorem B11991287 : Blo 1971435 11991287 := bstep (se 1 (by rfl) ⟨8993465, by rfl⟩ : syracuseStep 11991287 = 17986931) B17986931
theorem B31976765 : Blo 1971435 31976765 := bstep (se 3 (by rfl) ⟨5995643, by rfl⟩ : syracuseStep 31976765 = 11991287) B11991287
theorem B21317843 : Blo 1971435 21317843 := bstep (se 1 (by rfl) ⟨15988382, by rfl⟩ : syracuseStep 21317843 = 31976765) B31976765
theorem B56847581 : Blo 1971435 56847581 := bstep (se 3 (by rfl) ⟨10658921, by rfl⟩ : syracuseStep 56847581 = 21317843) B21317843
theorem B37898387 : Blo 1971435 37898387 := bstep (se 1 (by rfl) ⟨28423790, by rfl⟩ : syracuseStep 37898387 = 56847581) B56847581
theorem B25265591 : Blo 1971435 25265591 := bstep (se 1 (by rfl) ⟨18949193, by rfl⟩ : syracuseStep 25265591 = 37898387) B37898387
theorem B16843727 : Blo 1971435 16843727 := bstep (se 1 (by rfl) ⟨12632795, by rfl⟩ : syracuseStep 16843727 = 25265591) B25265591
theorem B11229151 : Blo 1971435 11229151 := bstep (se 1 (by rfl) ⟨8421863, by rfl⟩ : syracuseStep 11229151 = 16843727) B16843727
theorem B14972201 : Blo 1971435 14972201 := bstep (se 2 (by rfl) ⟨5614575, by rfl⟩ : syracuseStep 14972201 = 11229151) B11229151
theorem B9981467 : Blo 1971435 9981467 := bstep (se 1 (by rfl) ⟨7486100, by rfl⟩ : syracuseStep 9981467 = 14972201) B14972201
theorem B6654311 : Blo 1971435 6654311 := bstep (se 1 (by rfl) ⟨4990733, by rfl⟩ : syracuseStep 6654311 = 9981467) B9981467
theorem B4436207 : Blo 1971435 4436207 := bstep (se 1 (by rfl) ⟨3327155, by rfl⟩ : syracuseStep 4436207 = 6654311) B6654311
theorem B2957471 : Blo 1971435 2957471 := bstep (se 1 (by rfl) ⟨2218103, by rfl⟩ : syracuseStep 2957471 = 4436207) B4436207
theorem B1971647 : Blo 1971435 1971647 := bstep (se 1 (by rfl) ⟨1478735, by rfl⟩ : syracuseStep 1971647 = 2957471) B2957471
theorem B2957477 : Blo 1971435 2957477 := bbase (se 4 (by rfl) ⟨277263, by rfl⟩ : syracuseStep 2957477 = 554527) (by norm_num)
theorem B1971651 : Blo 1971435 1971651 := bstep (se 1 (by rfl) ⟨1478738, by rfl⟩ : syracuseStep 1971651 = 2957477) B2957477
theorem B2495377 : Blo 1971435 2495377 := bbase (se 2 (by rfl) ⟨935766, by rfl⟩ : syracuseStep 2495377 = 1871533) (by norm_num)
theorem B3327169 : Blo 1971435 3327169 := bstep (se 2 (by rfl) ⟨1247688, by rfl⟩ : syracuseStep 3327169 = 2495377) B2495377
theorem B4436225 : Blo 1971435 4436225 := bstep (se 2 (by rfl) ⟨1663584, by rfl⟩ : syracuseStep 4436225 = 3327169) B3327169
theorem B2957483 : Blo 1971435 2957483 := bstep (se 1 (by rfl) ⟨2218112, by rfl⟩ : syracuseStep 2957483 = 4436225) B4436225
theorem B1971655 : Blo 1971435 1971655 := bstep (se 1 (by rfl) ⟨1478741, by rfl⟩ : syracuseStep 1971655 = 2957483) B2957483
theorem B2218117 : Blo 1971435 2218117 := bbase (se 4 (by rfl) ⟨207948, by rfl⟩ : syracuseStep 2218117 = 415897) (by norm_num)
theorem B2957489 : Blo 1971435 2957489 := bstep (se 2 (by rfl) ⟨1109058, by rfl⟩ : syracuseStep 2957489 = 2218117) B2218117
theorem B1971659 : Blo 1971435 1971659 := bstep (se 1 (by rfl) ⟨1478744, by rfl⟩ : syracuseStep 1971659 = 2957489) B2957489
theorem B9474677 : Blo 1971435 9474677 := bbase (se 5 (by rfl) ⟨444125, by rfl⟩ : syracuseStep 9474677 = 888251) (by norm_num)
theorem B6316451 : Blo 1971435 6316451 := bstep (se 1 (by rfl) ⟨4737338, by rfl⟩ : syracuseStep 6316451 = 9474677) B9474677
theorem B4210967 : Blo 1971435 4210967 := bstep (se 1 (by rfl) ⟨3158225, by rfl⟩ : syracuseStep 4210967 = 6316451) B6316451
theorem B2807311 : Blo 1971435 2807311 := bstep (se 1 (by rfl) ⟨2105483, by rfl⟩ : syracuseStep 2807311 = 4210967) B4210967
theorem B3743081 : Blo 1971435 3743081 := bstep (se 2 (by rfl) ⟨1403655, by rfl⟩ : syracuseStep 3743081 = 2807311) B2807311
theorem B2495387 : Blo 1971435 2495387 := bstep (se 1 (by rfl) ⟨1871540, by rfl⟩ : syracuseStep 2495387 = 3743081) B3743081
theorem B6654365 : Blo 1971435 6654365 := bstep (se 3 (by rfl) ⟨1247693, by rfl⟩ : syracuseStep 6654365 = 2495387) B2495387
theorem B4436243 : Blo 1971435 4436243 := bstep (se 1 (by rfl) ⟨3327182, by rfl⟩ : syracuseStep 4436243 = 6654365) B6654365
theorem B2957495 : Blo 1971435 2957495 := bstep (se 1 (by rfl) ⟨2218121, by rfl⟩ : syracuseStep 2957495 = 4436243) B4436243
theorem B1971663 : Blo 1971435 1971663 := bstep (se 1 (by rfl) ⟨1478747, by rfl⟩ : syracuseStep 1971663 = 2957495) B2957495
theorem B2957501 : Blo 1971435 2957501 := bbase (se 3 (by rfl) ⟨554531, by rfl⟩ : syracuseStep 2957501 = 1109063) (by norm_num)
theorem B1971667 : Blo 1971435 1971667 := bstep (se 1 (by rfl) ⟨1478750, by rfl⟩ : syracuseStep 1971667 = 2957501) B2957501
theorem B4436261 : Blo 1971435 4436261 := bbase (se 4 (by rfl) ⟨415899, by rfl⟩ : syracuseStep 4436261 = 831799) (by norm_num)
theorem B2957507 : Blo 1971435 2957507 := bstep (se 1 (by rfl) ⟨2218130, by rfl⟩ : syracuseStep 2957507 = 4436261) B4436261
theorem B1971671 : Blo 1971435 1971671 := bstep (se 1 (by rfl) ⟨1478753, by rfl⟩ : syracuseStep 1971671 = 2957507) B2957507
theorem B4990805 : Blo 1971435 4990805 := bbase (se 9 (by rfl) ⟨14621, by rfl⟩ : syracuseStep 4990805 = 29243) (by norm_num)
theorem B3327203 : Blo 1971435 3327203 := bstep (se 1 (by rfl) ⟨2495402, by rfl⟩ : syracuseStep 3327203 = 4990805) B4990805
theorem B2218135 : Blo 1971435 2218135 := bstep (se 1 (by rfl) ⟨1663601, by rfl⟩ : syracuseStep 2218135 = 3327203) B3327203
theorem B2957513 : Blo 1971435 2957513 := bstep (se 2 (by rfl) ⟨1109067, by rfl⟩ : syracuseStep 2957513 = 2218135) B2218135
theorem B1971675 : Blo 1971435 1971675 := bstep (se 1 (by rfl) ⟨1478756, by rfl⟩ : syracuseStep 1971675 = 2957513) B2957513
theorem B6316501 : Blo 1971435 6316501 := bbase (se 7 (by rfl) ⟨74021, by rfl⟩ : syracuseStep 6316501 = 148043) (by norm_num)
theorem B8422001 : Blo 1971435 8422001 := bstep (se 2 (by rfl) ⟨3158250, by rfl⟩ : syracuseStep 8422001 = 6316501) B6316501
theorem B5614667 : Blo 1971435 5614667 := bstep (se 1 (by rfl) ⟨4211000, by rfl⟩ : syracuseStep 5614667 = 8422001) B8422001
theorem B3743111 : Blo 1971435 3743111 := bstep (se 1 (by rfl) ⟨2807333, by rfl⟩ : syracuseStep 3743111 = 5614667) B5614667
theorem B9981629 : Blo 1971435 9981629 := bstep (se 3 (by rfl) ⟨1871555, by rfl⟩ : syracuseStep 9981629 = 3743111) B3743111
theorem B6654419 : Blo 1971435 6654419 := bstep (se 1 (by rfl) ⟨4990814, by rfl⟩ : syracuseStep 6654419 = 9981629) B9981629
theorem B4436279 : Blo 1971435 4436279 := bstep (se 1 (by rfl) ⟨3327209, by rfl⟩ : syracuseStep 4436279 = 6654419) B6654419
theorem B2957519 : Blo 1971435 2957519 := bstep (se 1 (by rfl) ⟨2218139, by rfl⟩ : syracuseStep 2957519 = 4436279) B4436279
theorem B1971679 : Blo 1971435 1971679 := bstep (se 1 (by rfl) ⟨1478759, by rfl⟩ : syracuseStep 1971679 = 2957519) B2957519
theorem B2957525 : Blo 1971435 2957525 := bbase (se 7 (by rfl) ⟨34658, by rfl⟩ : syracuseStep 2957525 = 69317) (by norm_num)
theorem B1971683 : Blo 1971435 1971683 := bstep (se 1 (by rfl) ⟨1478762, by rfl⟩ : syracuseStep 1971683 = 2957525) B2957525
theorem B2105509 : Blo 1971435 2105509 := bbase (se 4 (by rfl) ⟨197391, by rfl⟩ : syracuseStep 2105509 = 394783) (by norm_num)
theorem B2807345 : Blo 1971435 2807345 := bstep (se 2 (by rfl) ⟨1052754, by rfl⟩ : syracuseStep 2807345 = 2105509) B2105509
theorem B7486253 : Blo 1971435 7486253 := bstep (se 3 (by rfl) ⟨1403672, by rfl⟩ : syracuseStep 7486253 = 2807345) B2807345
theorem B4990835 : Blo 1971435 4990835 := bstep (se 1 (by rfl) ⟨3743126, by rfl⟩ : syracuseStep 4990835 = 7486253) B7486253
theorem B3327223 : Blo 1971435 3327223 := bstep (se 1 (by rfl) ⟨2495417, by rfl⟩ : syracuseStep 3327223 = 4990835) B4990835
theorem B4436297 : Blo 1971435 4436297 := bstep (se 2 (by rfl) ⟨1663611, by rfl⟩ : syracuseStep 4436297 = 3327223) B3327223
theorem B2957531 : Blo 1971435 2957531 := bstep (se 1 (by rfl) ⟨2218148, by rfl⟩ : syracuseStep 2957531 = 4436297) B4436297
theorem B1971687 : Blo 1971435 1971687 := bstep (se 1 (by rfl) ⟨1478765, by rfl⟩ : syracuseStep 1971687 = 2957531) B2957531
theorem B2218153 : Blo 1971435 2218153 := bbase (se 2 (by rfl) ⟨831807, by rfl⟩ : syracuseStep 2218153 = 1663615) (by norm_num)
theorem B2957537 : Blo 1971435 2957537 := bstep (se 2 (by rfl) ⟨1109076, by rfl⟩ : syracuseStep 2957537 = 2218153) B2218153
theorem B1971691 : Blo 1971435 1971691 := bstep (se 1 (by rfl) ⟨1478768, by rfl⟩ : syracuseStep 1971691 = 2957537) B2957537
theorem B8422069 : Blo 1971435 8422069 := bbase (se 5 (by rfl) ⟨394784, by rfl⟩ : syracuseStep 8422069 = 789569) (by norm_num)
theorem B11229425 : Blo 1971435 11229425 := bstep (se 2 (by rfl) ⟨4211034, by rfl⟩ : syracuseStep 11229425 = 8422069) B8422069
theorem B7486283 : Blo 1971435 7486283 := bstep (se 1 (by rfl) ⟨5614712, by rfl⟩ : syracuseStep 7486283 = 11229425) B11229425
theorem B4990855 : Blo 1971435 4990855 := bstep (se 1 (by rfl) ⟨3743141, by rfl⟩ : syracuseStep 4990855 = 7486283) B7486283
theorem B6654473 : Blo 1971435 6654473 := bstep (se 2 (by rfl) ⟨2495427, by rfl⟩ : syracuseStep 6654473 = 4990855) B4990855
theorem B4436315 : Blo 1971435 4436315 := bstep (se 1 (by rfl) ⟨3327236, by rfl⟩ : syracuseStep 4436315 = 6654473) B6654473
theorem B2957543 : Blo 1971435 2957543 := bstep (se 1 (by rfl) ⟨2218157, by rfl⟩ : syracuseStep 2957543 = 4436315) B4436315
theorem B1971695 : Blo 1971435 1971695 := bstep (se 1 (by rfl) ⟨1478771, by rfl⟩ : syracuseStep 1971695 = 2957543) B2957543
theorem B2957549 : Blo 1971435 2957549 := bbase (se 3 (by rfl) ⟨554540, by rfl⟩ : syracuseStep 2957549 = 1109081) (by norm_num)
theorem B1971699 : Blo 1971435 1971699 := bstep (se 1 (by rfl) ⟨1478774, by rfl⟩ : syracuseStep 1971699 = 2957549) B2957549
theorem B4436333 : Blo 1971435 4436333 := bbase (se 3 (by rfl) ⟨831812, by rfl⟩ : syracuseStep 4436333 = 1663625) (by norm_num)
theorem B2957555 : Blo 1971435 2957555 := bstep (se 1 (by rfl) ⟨2218166, by rfl⟩ : syracuseStep 2957555 = 4436333) B4436333
theorem B1971703 : Blo 1971435 1971703 := bstep (se 1 (by rfl) ⟨1478777, by rfl⟩ : syracuseStep 1971703 = 2957555) B2957555
theorem B3743165 : Blo 1971435 3743165 := bbase (se 3 (by rfl) ⟨701843, by rfl⟩ : syracuseStep 3743165 = 1403687) (by norm_num)
theorem B2495443 : Blo 1971435 2495443 := bstep (se 1 (by rfl) ⟨1871582, by rfl⟩ : syracuseStep 2495443 = 3743165) B3743165
theorem B3327257 : Blo 1971435 3327257 := bstep (se 2 (by rfl) ⟨1247721, by rfl⟩ : syracuseStep 3327257 = 2495443) B2495443
theorem B2218171 : Blo 1971435 2218171 := bstep (se 1 (by rfl) ⟨1663628, by rfl⟩ : syracuseStep 2218171 = 3327257) B3327257
theorem B2957561 : Blo 1971435 2957561 := bstep (se 2 (by rfl) ⟨1109085, by rfl⟩ : syracuseStep 2957561 = 2218171) B2218171
theorem B1971707 : Blo 1971435 1971707 := bstep (se 1 (by rfl) ⟨1478780, by rfl⟩ : syracuseStep 1971707 = 2957561) B2957561
theorem B50532821 : Blo 1971435 50532821 := bbase (se 7 (by rfl) ⟨592181, by rfl⟩ : syracuseStep 50532821 = 1184363) (by norm_num)
theorem B33688547 : Blo 1971435 33688547 := bstep (se 1 (by rfl) ⟨25266410, by rfl⟩ : syracuseStep 33688547 = 50532821) B50532821
theorem B22459031 : Blo 1971435 22459031 := bstep (se 1 (by rfl) ⟨16844273, by rfl⟩ : syracuseStep 22459031 = 33688547) B33688547
theorem B14972687 : Blo 1971435 14972687 := bstep (se 1 (by rfl) ⟨11229515, by rfl⟩ : syracuseStep 14972687 = 22459031) B22459031
theorem B9981791 : Blo 1971435 9981791 := bstep (se 1 (by rfl) ⟨7486343, by rfl⟩ : syracuseStep 9981791 = 14972687) B14972687
theorem B6654527 : Blo 1971435 6654527 := bstep (se 1 (by rfl) ⟨4990895, by rfl⟩ : syracuseStep 6654527 = 9981791) B9981791
theorem B4436351 : Blo 1971435 4436351 := bstep (se 1 (by rfl) ⟨3327263, by rfl⟩ : syracuseStep 4436351 = 6654527) B6654527
theorem B2957567 : Blo 1971435 2957567 := bstep (se 1 (by rfl) ⟨2218175, by rfl⟩ : syracuseStep 2957567 = 4436351) B4436351
theorem B1971711 : Blo 1971435 1971711 := bstep (se 1 (by rfl) ⟨1478783, by rfl⟩ : syracuseStep 1971711 = 2957567) B2957567
theorem B2957573 : Blo 1971435 2957573 := bbase (se 4 (by rfl) ⟨277272, by rfl⟩ : syracuseStep 2957573 = 554545) (by norm_num)
theorem B1971715 : Blo 1971435 1971715 := bstep (se 1 (by rfl) ⟨1478786, by rfl⟩ : syracuseStep 1971715 = 2957573) B2957573
theorem B3327277 : Blo 1971435 3327277 := bbase (se 3 (by rfl) ⟨623864, by rfl⟩ : syracuseStep 3327277 = 1247729) (by norm_num)
theorem B4436369 : Blo 1971435 4436369 := bstep (se 2 (by rfl) ⟨1663638, by rfl⟩ : syracuseStep 4436369 = 3327277) B3327277
theorem B2957579 : Blo 1971435 2957579 := bstep (se 1 (by rfl) ⟨2218184, by rfl⟩ : syracuseStep 2957579 = 4436369) B4436369
theorem B1971719 : Blo 1971435 1971719 := bstep (se 1 (by rfl) ⟨1478789, by rfl⟩ : syracuseStep 1971719 = 2957579) B2957579
theorem B2218189 : Blo 1971435 2218189 := bbase (se 3 (by rfl) ⟨415910, by rfl⟩ : syracuseStep 2218189 = 831821) (by norm_num)
theorem B2957585 : Blo 1971435 2957585 := bstep (se 2 (by rfl) ⟨1109094, by rfl⟩ : syracuseStep 2957585 = 2218189) B2218189
theorem B1971723 : Blo 1971435 1971723 := bstep (se 1 (by rfl) ⟨1478792, by rfl⟩ : syracuseStep 1971723 = 2957585) B2957585
theorem B6654581 : Blo 1971435 6654581 := bbase (se 5 (by rfl) ⟨311933, by rfl⟩ : syracuseStep 6654581 = 623867) (by norm_num)
theorem B4436387 : Blo 1971435 4436387 := bstep (se 1 (by rfl) ⟨3327290, by rfl⟩ : syracuseStep 4436387 = 6654581) B6654581
theorem B2957591 : Blo 1971435 2957591 := bstep (se 1 (by rfl) ⟨2218193, by rfl⟩ : syracuseStep 2957591 = 4436387) B4436387
theorem B1971727 : Blo 1971435 1971727 := bstep (se 1 (by rfl) ⟨1478795, by rfl⟩ : syracuseStep 1971727 = 2957591) B2957591
theorem B2957597 : Blo 1971435 2957597 := bbase (se 3 (by rfl) ⟨554549, by rfl⟩ : syracuseStep 2957597 = 1109099) (by norm_num)
theorem B1971731 : Blo 1971435 1971731 := bstep (se 1 (by rfl) ⟨1478798, by rfl⟩ : syracuseStep 1971731 = 2957597) B2957597
theorem B4436405 : Blo 1971435 4436405 := bbase (se 5 (by rfl) ⟨207956, by rfl⟩ : syracuseStep 4436405 = 415913) (by norm_num)
theorem B2957603 : Blo 1971435 2957603 := bstep (se 1 (by rfl) ⟨2218202, by rfl⟩ : syracuseStep 2957603 = 4436405) B4436405
theorem B1971735 : Blo 1971435 1971735 := bstep (se 1 (by rfl) ⟨1478801, by rfl⟩ : syracuseStep 1971735 = 2957603) B2957603
theorem B3553141 : Blo 1971435 3553141 := bbase (se 5 (by rfl) ⟨166553, by rfl⟩ : syracuseStep 3553141 = 333107) (by norm_num)
theorem B4737521 : Blo 1971435 4737521 := bstep (se 2 (by rfl) ⟨1776570, by rfl⟩ : syracuseStep 4737521 = 3553141) B3553141
theorem B3158347 : Blo 1971435 3158347 := bstep (se 1 (by rfl) ⟨2368760, by rfl⟩ : syracuseStep 3158347 = 4737521) B4737521
theorem B4211129 : Blo 1971435 4211129 := bstep (se 2 (by rfl) ⟨1579173, by rfl⟩ : syracuseStep 4211129 = 3158347) B3158347
theorem B11229677 : Blo 1971435 11229677 := bstep (se 3 (by rfl) ⟨2105564, by rfl⟩ : syracuseStep 11229677 = 4211129) B4211129
theorem B7486451 : Blo 1971435 7486451 := bstep (se 1 (by rfl) ⟨5614838, by rfl⟩ : syracuseStep 7486451 = 11229677) B11229677
theorem B4990967 : Blo 1971435 4990967 := bstep (se 1 (by rfl) ⟨3743225, by rfl⟩ : syracuseStep 4990967 = 7486451) B7486451
theorem B3327311 : Blo 1971435 3327311 := bstep (se 1 (by rfl) ⟨2495483, by rfl⟩ : syracuseStep 3327311 = 4990967) B4990967
theorem B2218207 : Blo 1971435 2218207 := bstep (se 1 (by rfl) ⟨1663655, by rfl⟩ : syracuseStep 2218207 = 3327311) B3327311
theorem B2957609 : Blo 1971435 2957609 := bstep (se 2 (by rfl) ⟨1109103, by rfl⟩ : syracuseStep 2957609 = 2218207) B2218207
theorem B1971739 : Blo 1971435 1971739 := bstep (se 1 (by rfl) ⟨1478804, by rfl⟩ : syracuseStep 1971739 = 2957609) B2957609
theorem B2368765 : Blo 1971435 2368765 := bbase (se 3 (by rfl) ⟨444143, by rfl⟩ : syracuseStep 2368765 = 888287) (by norm_num)
theorem B3158353 : Blo 1971435 3158353 := bstep (se 2 (by rfl) ⟨1184382, by rfl⟩ : syracuseStep 3158353 = 2368765) B2368765
theorem B4211137 : Blo 1971435 4211137 := bstep (se 2 (by rfl) ⟨1579176, by rfl⟩ : syracuseStep 4211137 = 3158353) B3158353
theorem B5614849 : Blo 1971435 5614849 := bstep (se 2 (by rfl) ⟨2105568, by rfl⟩ : syracuseStep 5614849 = 4211137) B4211137
theorem B7486465 : Blo 1971435 7486465 := bstep (se 2 (by rfl) ⟨2807424, by rfl⟩ : syracuseStep 7486465 = 5614849) B5614849
theorem B9981953 : Blo 1971435 9981953 := bstep (se 2 (by rfl) ⟨3743232, by rfl⟩ : syracuseStep 9981953 = 7486465) B7486465
theorem B6654635 : Blo 1971435 6654635 := bstep (se 1 (by rfl) ⟨4990976, by rfl⟩ : syracuseStep 6654635 = 9981953) B9981953
theorem B4436423 : Blo 1971435 4436423 := bstep (se 1 (by rfl) ⟨3327317, by rfl⟩ : syracuseStep 4436423 = 6654635) B6654635
theorem B2957615 : Blo 1971435 2957615 := bstep (se 1 (by rfl) ⟨2218211, by rfl⟩ : syracuseStep 2957615 = 4436423) B4436423
theorem B1971743 : Blo 1971435 1971743 := bstep (se 1 (by rfl) ⟨1478807, by rfl⟩ : syracuseStep 1971743 = 2957615) B2957615
theorem B2957621 : Blo 1971435 2957621 := bbase (se 5 (by rfl) ⟨138638, by rfl⟩ : syracuseStep 2957621 = 277277) (by norm_num)
theorem B1971747 : Blo 1971435 1971747 := bstep (se 1 (by rfl) ⟨1478810, by rfl⟩ : syracuseStep 1971747 = 2957621) B2957621
theorem B4990997 : Blo 1971435 4990997 := bbase (se 6 (by rfl) ⟨116976, by rfl⟩ : syracuseStep 4990997 = 233953) (by norm_num)
theorem B3327331 : Blo 1971435 3327331 := bstep (se 1 (by rfl) ⟨2495498, by rfl⟩ : syracuseStep 3327331 = 4990997) B4990997
theorem B4436441 : Blo 1971435 4436441 := bstep (se 2 (by rfl) ⟨1663665, by rfl⟩ : syracuseStep 4436441 = 3327331) B3327331
theorem B2957627 : Blo 1971435 2957627 := bstep (se 1 (by rfl) ⟨2218220, by rfl⟩ : syracuseStep 2957627 = 4436441) B4436441
theorem B1971751 : Blo 1971435 1971751 := bstep (se 1 (by rfl) ⟨1478813, by rfl⟩ : syracuseStep 1971751 = 2957627) B2957627
theorem B2218225 : Blo 1971435 2218225 := bbase (se 2 (by rfl) ⟨831834, by rfl⟩ : syracuseStep 2218225 = 1663669) (by norm_num)
theorem B2957633 : Blo 1971435 2957633 := bstep (se 2 (by rfl) ⟨1109112, by rfl⟩ : syracuseStep 2957633 = 2218225) B2218225
theorem B1971755 : Blo 1971435 1971755 := bstep (se 1 (by rfl) ⟨1478816, by rfl⟩ : syracuseStep 1971755 = 2957633) B2957633
theorem B17987957 : Blo 1971435 17987957 := bbase (se 5 (by rfl) ⟨843185, by rfl⟩ : syracuseStep 17987957 = 1686371) (by norm_num)
theorem B11991971 : Blo 1971435 11991971 := bstep (se 1 (by rfl) ⟨8993978, by rfl⟩ : syracuseStep 11991971 = 17987957) B17987957
theorem B7994647 : Blo 1971435 7994647 := bstep (se 1 (by rfl) ⟨5995985, by rfl⟩ : syracuseStep 7994647 = 11991971) B11991971
theorem B10659529 : Blo 1971435 10659529 := bstep (se 2 (by rfl) ⟨3997323, by rfl⟩ : syracuseStep 10659529 = 7994647) B7994647
theorem B14212705 : Blo 1971435 14212705 := bstep (se 2 (by rfl) ⟨5329764, by rfl⟩ : syracuseStep 14212705 = 10659529) B10659529
theorem B18950273 : Blo 1971435 18950273 := bstep (se 2 (by rfl) ⟨7106352, by rfl⟩ : syracuseStep 18950273 = 14212705) B14212705
theorem B12633515 : Blo 1971435 12633515 := bstep (se 1 (by rfl) ⟨9475136, by rfl⟩ : syracuseStep 12633515 = 18950273) B18950273
theorem B8422343 : Blo 1971435 8422343 := bstep (se 1 (by rfl) ⟨6316757, by rfl⟩ : syracuseStep 8422343 = 12633515) B12633515
theorem B5614895 : Blo 1971435 5614895 := bstep (se 1 (by rfl) ⟨4211171, by rfl⟩ : syracuseStep 5614895 = 8422343) B8422343
theorem B3743263 : Blo 1971435 3743263 := bstep (se 1 (by rfl) ⟨2807447, by rfl⟩ : syracuseStep 3743263 = 5614895) B5614895
theorem B4991017 : Blo 1971435 4991017 := bstep (se 2 (by rfl) ⟨1871631, by rfl⟩ : syracuseStep 4991017 = 3743263) B3743263
theorem B6654689 : Blo 1971435 6654689 := bstep (se 2 (by rfl) ⟨2495508, by rfl⟩ : syracuseStep 6654689 = 4991017) B4991017
theorem B4436459 : Blo 1971435 4436459 := bstep (se 1 (by rfl) ⟨3327344, by rfl⟩ : syracuseStep 4436459 = 6654689) B6654689
theorem B2957639 : Blo 1971435 2957639 := bstep (se 1 (by rfl) ⟨2218229, by rfl⟩ : syracuseStep 2957639 = 4436459) B4436459
theorem B1971759 : Blo 1971435 1971759 := bstep (se 1 (by rfl) ⟨1478819, by rfl⟩ : syracuseStep 1971759 = 2957639) B2957639
theorem B2957645 : Blo 1971435 2957645 := bbase (se 3 (by rfl) ⟨554558, by rfl⟩ : syracuseStep 2957645 = 1109117) (by norm_num)
theorem B1971763 : Blo 1971435 1971763 := bstep (se 1 (by rfl) ⟨1478822, by rfl⟩ : syracuseStep 1971763 = 2957645) B2957645
theorem B4436477 : Blo 1971435 4436477 := bbase (se 3 (by rfl) ⟨831839, by rfl⟩ : syracuseStep 4436477 = 1663679) (by norm_num)
theorem B2957651 : Blo 1971435 2957651 := bstep (se 1 (by rfl) ⟨2218238, by rfl⟩ : syracuseStep 2957651 = 4436477) B4436477
theorem B1971767 : Blo 1971435 1971767 := bstep (se 1 (by rfl) ⟨1478825, by rfl⟩ : syracuseStep 1971767 = 2957651) B2957651
theorem B3327365 : Blo 1971435 3327365 := bbase (se 4 (by rfl) ⟨311940, by rfl⟩ : syracuseStep 3327365 = 623881) (by norm_num)
theorem B2218243 : Blo 1971435 2218243 := bstep (se 1 (by rfl) ⟨1663682, by rfl⟩ : syracuseStep 2218243 = 3327365) B3327365
theorem B2957657 : Blo 1971435 2957657 := bstep (se 2 (by rfl) ⟨1109121, by rfl⟩ : syracuseStep 2957657 = 2218243) B2218243
theorem B1971771 : Blo 1971435 1971771 := bstep (se 1 (by rfl) ⟨1478828, by rfl⟩ : syracuseStep 1971771 = 2957657) B2957657
theorem B14973173 : Blo 1971435 14973173 := bbase (se 5 (by rfl) ⟨701867, by rfl⟩ : syracuseStep 14973173 = 1403735) (by norm_num)
theorem B9982115 : Blo 1971435 9982115 := bstep (se 1 (by rfl) ⟨7486586, by rfl⟩ : syracuseStep 9982115 = 14973173) B14973173
theorem B6654743 : Blo 1971435 6654743 := bstep (se 1 (by rfl) ⟨4991057, by rfl⟩ : syracuseStep 6654743 = 9982115) B9982115
theorem B4436495 : Blo 1971435 4436495 := bstep (se 1 (by rfl) ⟨3327371, by rfl⟩ : syracuseStep 4436495 = 6654743) B6654743
theorem B2957663 : Blo 1971435 2957663 := bstep (se 1 (by rfl) ⟨2218247, by rfl⟩ : syracuseStep 2957663 = 4436495) B4436495
theorem B1971775 : Blo 1971435 1971775 := bstep (se 1 (by rfl) ⟨1478831, by rfl⟩ : syracuseStep 1971775 = 2957663) B2957663
theorem B2957669 : Blo 1971435 2957669 := bbase (se 4 (by rfl) ⟨277281, by rfl⟩ : syracuseStep 2957669 = 554563) (by norm_num)
theorem B1971779 : Blo 1971435 1971779 := bstep (se 1 (by rfl) ⟨1478834, by rfl⟩ : syracuseStep 1971779 = 2957669) B2957669
theorem B3743309 : Blo 1971435 3743309 := bbase (se 3 (by rfl) ⟨701870, by rfl⟩ : syracuseStep 3743309 = 1403741) (by norm_num)
theorem B2495539 : Blo 1971435 2495539 := bstep (se 1 (by rfl) ⟨1871654, by rfl⟩ : syracuseStep 2495539 = 3743309) B3743309
theorem B3327385 : Blo 1971435 3327385 := bstep (se 2 (by rfl) ⟨1247769, by rfl⟩ : syracuseStep 3327385 = 2495539) B2495539
theorem B4436513 : Blo 1971435 4436513 := bstep (se 2 (by rfl) ⟨1663692, by rfl⟩ : syracuseStep 4436513 = 3327385) B3327385
theorem B2957675 : Blo 1971435 2957675 := bstep (se 1 (by rfl) ⟨2218256, by rfl⟩ : syracuseStep 2957675 = 4436513) B4436513
theorem B1971783 : Blo 1971435 1971783 := bstep (se 1 (by rfl) ⟨1478837, by rfl⟩ : syracuseStep 1971783 = 2957675) B2957675
theorem B2218261 : Blo 1971435 2218261 := bbase (se 6 (by rfl) ⟨51990, by rfl⟩ : syracuseStep 2218261 = 103981) (by norm_num)
theorem B2957681 : Blo 1971435 2957681 := bstep (se 2 (by rfl) ⟨1109130, by rfl⟩ : syracuseStep 2957681 = 2218261) B2218261
theorem B1971787 : Blo 1971435 1971787 := bstep (se 1 (by rfl) ⟨1478840, by rfl⟩ : syracuseStep 1971787 = 2957681) B2957681
theorem B2495549 : Blo 1971435 2495549 := bbase (se 3 (by rfl) ⟨467915, by rfl⟩ : syracuseStep 2495549 = 935831) (by norm_num)
theorem B6654797 : Blo 1971435 6654797 := bstep (se 3 (by rfl) ⟨1247774, by rfl⟩ : syracuseStep 6654797 = 2495549) B2495549
theorem B4436531 : Blo 1971435 4436531 := bstep (se 1 (by rfl) ⟨3327398, by rfl⟩ : syracuseStep 4436531 = 6654797) B6654797
theorem B2957687 : Blo 1971435 2957687 := bstep (se 1 (by rfl) ⟨2218265, by rfl⟩ : syracuseStep 2957687 = 4436531) B4436531
theorem B1971791 : Blo 1971435 1971791 := bstep (se 1 (by rfl) ⟨1478843, by rfl⟩ : syracuseStep 1971791 = 2957687) B2957687
theorem B2957693 : Blo 1971435 2957693 := bbase (se 3 (by rfl) ⟨554567, by rfl⟩ : syracuseStep 2957693 = 1109135) (by norm_num)
theorem B1971795 : Blo 1971435 1971795 := bstep (se 1 (by rfl) ⟨1478846, by rfl⟩ : syracuseStep 1971795 = 2957693) B2957693
theorem B4436549 : Blo 1971435 4436549 := bbase (se 4 (by rfl) ⟨415926, by rfl⟩ : syracuseStep 4436549 = 831853) (by norm_num)
theorem B2957699 : Blo 1971435 2957699 := bstep (se 1 (by rfl) ⟨2218274, by rfl⟩ : syracuseStep 2957699 = 4436549) B4436549
theorem B1971799 : Blo 1971435 1971799 := bstep (se 1 (by rfl) ⟨1478849, by rfl⟩ : syracuseStep 1971799 = 2957699) B2957699
theorem B2105633 : Blo 1971435 2105633 := bbase (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) (by norm_num)
theorem B5615021 : Blo 1971435 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B3743347 : Blo 1971435 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B4991129 : Blo 1971435 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B3327419 : Blo 1971435 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B2218279 : Blo 1971435 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B2957705 : Blo 1971435 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B1971803 : Blo 1971435 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B9982277 : Blo 1971435 9982277 := bbase (se 4 (by rfl) ⟨935838, by rfl⟩ : syracuseStep 9982277 = 1871677) (by norm_num)
theorem B6654851 : Blo 1971435 6654851 := bstep (se 1 (by rfl) ⟨4991138, by rfl⟩ : syracuseStep 6654851 = 9982277) B9982277
theorem B4436567 : Blo 1971435 4436567 := bstep (se 1 (by rfl) ⟨3327425, by rfl⟩ : syracuseStep 4436567 = 6654851) B6654851
theorem B2957711 : Blo 1971435 2957711 := bstep (se 1 (by rfl) ⟨2218283, by rfl⟩ : syracuseStep 2957711 = 4436567) B4436567
theorem B1971807 : Blo 1971435 1971807 := bstep (se 1 (by rfl) ⟨1478855, by rfl⟩ : syracuseStep 1971807 = 2957711) B2957711
theorem B2957717 : Blo 1971435 2957717 := bbase (se 6 (by rfl) ⟨69321, by rfl⟩ : syracuseStep 2957717 = 138643) (by norm_num)
theorem B1971811 : Blo 1971435 1971811 := bstep (se 1 (by rfl) ⟨1478858, by rfl⟩ : syracuseStep 1971811 = 2957717) B2957717
theorem B4268749 : Blo 1971435 4268749 := bbase (se 3 (by rfl) ⟨800390, by rfl⟩ : syracuseStep 4268749 = 1600781) (by norm_num)
theorem B5691665 : Blo 1971435 5691665 := bstep (se 2 (by rfl) ⟨2134374, by rfl⟩ : syracuseStep 5691665 = 4268749) B4268749
theorem B15177773 : Blo 1971435 15177773 := bstep (se 3 (by rfl) ⟨2845832, by rfl⟩ : syracuseStep 15177773 = 5691665) B5691665
theorem B10118515 : Blo 1971435 10118515 := bstep (se 1 (by rfl) ⟨7588886, by rfl⟩ : syracuseStep 10118515 = 15177773) B15177773
theorem B13491353 : Blo 1971435 13491353 := bstep (se 2 (by rfl) ⟨5059257, by rfl⟩ : syracuseStep 13491353 = 10118515) B10118515
theorem B8994235 : Blo 1971435 8994235 := bstep (se 1 (by rfl) ⟨6745676, by rfl⟩ : syracuseStep 8994235 = 13491353) B13491353
theorem B11992313 : Blo 1971435 11992313 := bstep (se 2 (by rfl) ⟨4497117, by rfl⟩ : syracuseStep 11992313 = 8994235) B8994235
theorem B7994875 : Blo 1971435 7994875 := bstep (se 1 (by rfl) ⟨5996156, by rfl⟩ : syracuseStep 7994875 = 11992313) B11992313
theorem B10659833 : Blo 1971435 10659833 := bstep (se 2 (by rfl) ⟨3997437, by rfl⟩ : syracuseStep 10659833 = 7994875) B7994875
theorem B7106555 : Blo 1971435 7106555 := bstep (se 1 (by rfl) ⟨5329916, by rfl⟩ : syracuseStep 7106555 = 10659833) B10659833
theorem B4737703 : Blo 1971435 4737703 := bstep (se 1 (by rfl) ⟨3553277, by rfl⟩ : syracuseStep 4737703 = 7106555) B7106555
theorem B6316937 : Blo 1971435 6316937 := bstep (se 2 (by rfl) ⟨2368851, by rfl⟩ : syracuseStep 6316937 = 4737703) B4737703
theorem B4211291 : Blo 1971435 4211291 := bstep (se 1 (by rfl) ⟨3158468, by rfl⟩ : syracuseStep 4211291 = 6316937) B6316937
theorem B11230109 : Blo 1971435 11230109 := bstep (se 3 (by rfl) ⟨2105645, by rfl⟩ : syracuseStep 11230109 = 4211291) B4211291
theorem B7486739 : Blo 1971435 7486739 := bstep (se 1 (by rfl) ⟨5615054, by rfl⟩ : syracuseStep 7486739 = 11230109) B11230109
theorem B4991159 : Blo 1971435 4991159 := bstep (se 1 (by rfl) ⟨3743369, by rfl⟩ : syracuseStep 4991159 = 7486739) B7486739
theorem B3327439 : Blo 1971435 3327439 := bstep (se 1 (by rfl) ⟨2495579, by rfl⟩ : syracuseStep 3327439 = 4991159) B4991159
theorem B4436585 : Blo 1971435 4436585 := bstep (se 2 (by rfl) ⟨1663719, by rfl⟩ : syracuseStep 4436585 = 3327439) B3327439
theorem B2957723 : Blo 1971435 2957723 := bstep (se 1 (by rfl) ⟨2218292, by rfl⟩ : syracuseStep 2957723 = 4436585) B4436585
theorem B1971815 : Blo 1971435 1971815 := bstep (se 1 (by rfl) ⟨1478861, by rfl⟩ : syracuseStep 1971815 = 2957723) B2957723
theorem B2218297 : Blo 1971435 2218297 := bbase (se 2 (by rfl) ⟨831861, by rfl⟩ : syracuseStep 2218297 = 1663723) (by norm_num)
theorem B2957729 : Blo 1971435 2957729 := bstep (se 2 (by rfl) ⟨1109148, by rfl⟩ : syracuseStep 2957729 = 2218297) B2218297
theorem B1971819 : Blo 1971435 1971819 := bstep (se 1 (by rfl) ⟨1478864, by rfl⟩ : syracuseStep 1971819 = 2957729) B2957729
theorem B5615077 : Blo 1971435 5615077 := bbase (se 4 (by rfl) ⟨526413, by rfl⟩ : syracuseStep 5615077 = 1052827) (by norm_num)
theorem B7486769 : Blo 1971435 7486769 := bstep (se 2 (by rfl) ⟨2807538, by rfl⟩ : syracuseStep 7486769 = 5615077) B5615077
theorem B4991179 : Blo 1971435 4991179 := bstep (se 1 (by rfl) ⟨3743384, by rfl⟩ : syracuseStep 4991179 = 7486769) B7486769
theorem B6654905 : Blo 1971435 6654905 := bstep (se 2 (by rfl) ⟨2495589, by rfl⟩ : syracuseStep 6654905 = 4991179) B4991179
theorem B4436603 : Blo 1971435 4436603 := bstep (se 1 (by rfl) ⟨3327452, by rfl⟩ : syracuseStep 4436603 = 6654905) B6654905
theorem B2957735 : Blo 1971435 2957735 := bstep (se 1 (by rfl) ⟨2218301, by rfl⟩ : syracuseStep 2957735 = 4436603) B4436603
theorem B1971823 : Blo 1971435 1971823 := bstep (se 1 (by rfl) ⟨1478867, by rfl⟩ : syracuseStep 1971823 = 2957735) B2957735
theorem B2957741 : Blo 1971435 2957741 := bbase (se 3 (by rfl) ⟨554576, by rfl⟩ : syracuseStep 2957741 = 1109153) (by norm_num)
theorem B1971827 : Blo 1971435 1971827 := bstep (se 1 (by rfl) ⟨1478870, by rfl⟩ : syracuseStep 1971827 = 2957741) B2957741
theorem B4436621 : Blo 1971435 4436621 := bbase (se 3 (by rfl) ⟨831866, by rfl⟩ : syracuseStep 4436621 = 1663733) (by norm_num)
theorem B2957747 : Blo 1971435 2957747 := bstep (se 1 (by rfl) ⟨2218310, by rfl⟩ : syracuseStep 2957747 = 4436621) B4436621
theorem B1971831 : Blo 1971435 1971831 := bstep (se 1 (by rfl) ⟨1478873, by rfl⟩ : syracuseStep 1971831 = 2957747) B2957747
theorem B2495605 : Blo 1971435 2495605 := bbase (se 5 (by rfl) ⟨116981, by rfl⟩ : syracuseStep 2495605 = 233963) (by norm_num)
theorem B3327473 : Blo 1971435 3327473 := bstep (se 2 (by rfl) ⟨1247802, by rfl⟩ : syracuseStep 3327473 = 2495605) B2495605
theorem B2218315 : Blo 1971435 2218315 := bstep (se 1 (by rfl) ⟨1663736, by rfl⟩ : syracuseStep 2218315 = 3327473) B3327473
theorem B2957753 : Blo 1971435 2957753 := bstep (se 2 (by rfl) ⟨1109157, by rfl⟩ : syracuseStep 2957753 = 2218315) B2218315
theorem B1971835 : Blo 1971435 1971835 := bstep (se 1 (by rfl) ⟨1478876, by rfl⟩ : syracuseStep 1971835 = 2957753) B2957753
theorem B3898733 : Blo 1971435 3898733 := bbase (se 3 (by rfl) ⟨731012, by rfl⟩ : syracuseStep 3898733 = 1462025) (by norm_num)
theorem B10396621 : Blo 1971435 10396621 := bstep (se 3 (by rfl) ⟨1949366, by rfl⟩ : syracuseStep 10396621 = 3898733) B3898733
theorem B13862161 : Blo 1971435 13862161 := bstep (se 2 (by rfl) ⟨5198310, by rfl⟩ : syracuseStep 13862161 = 10396621) B10396621
theorem B73931525 : Blo 1971435 73931525 := bstep (se 4 (by rfl) ⟨6931080, by rfl⟩ : syracuseStep 73931525 = 13862161) B13862161
theorem B49287683 : Blo 1971435 49287683 := bstep (se 1 (by rfl) ⟨36965762, by rfl⟩ : syracuseStep 49287683 = 73931525) B73931525
theorem B32858455 : Blo 1971435 32858455 := bstep (se 1 (by rfl) ⟨24643841, by rfl⟩ : syracuseStep 32858455 = 49287683) B49287683
theorem B43811273 : Blo 1971435 43811273 := bstep (se 2 (by rfl) ⟨16429227, by rfl⟩ : syracuseStep 43811273 = 32858455) B32858455
theorem B29207515 : Blo 1971435 29207515 := bstep (se 1 (by rfl) ⟨21905636, by rfl⟩ : syracuseStep 29207515 = 43811273) B43811273
theorem B38943353 : Blo 1971435 38943353 := bstep (se 2 (by rfl) ⟨14603757, by rfl⟩ : syracuseStep 38943353 = 29207515) B29207515
theorem B103848941 : Blo 1971435 103848941 := bstep (se 3 (by rfl) ⟨19471676, by rfl⟩ : syracuseStep 103848941 = 38943353) B38943353
theorem B69232627 : Blo 1971435 69232627 := bstep (se 1 (by rfl) ⟨51924470, by rfl⟩ : syracuseStep 69232627 = 103848941) B103848941
theorem B369240677 : Blo 1971435 369240677 := bstep (se 4 (by rfl) ⟨34616313, by rfl⟩ : syracuseStep 369240677 = 69232627) B69232627
theorem B246160451 : Blo 1971435 246160451 := bstep (se 1 (by rfl) ⟨184620338, by rfl⟩ : syracuseStep 246160451 = 369240677) B369240677
theorem B164106967 : Blo 1971435 164106967 := bstep (se 1 (by rfl) ⟨123080225, by rfl⟩ : syracuseStep 164106967 = 246160451) B246160451
theorem B218809289 : Blo 1971435 218809289 := bstep (se 2 (by rfl) ⟨82053483, by rfl⟩ : syracuseStep 218809289 = 164106967) B164106967
theorem B145872859 : Blo 1971435 145872859 := bstep (se 1 (by rfl) ⟨109404644, by rfl⟩ : syracuseStep 145872859 = 218809289) B218809289
theorem B194497145 : Blo 1971435 194497145 := bstep (se 2 (by rfl) ⟨72936429, by rfl⟩ : syracuseStep 194497145 = 145872859) B145872859
theorem B129664763 : Blo 1971435 129664763 := bstep (se 1 (by rfl) ⟨97248572, by rfl⟩ : syracuseStep 129664763 = 194497145) B194497145
theorem B86443175 : Blo 1971435 86443175 := bstep (se 1 (by rfl) ⟨64832381, by rfl⟩ : syracuseStep 86443175 = 129664763) B129664763
theorem B57628783 : Blo 1971435 57628783 := bstep (se 1 (by rfl) ⟨43221587, by rfl⟩ : syracuseStep 57628783 = 86443175) B86443175
theorem B76838377 : Blo 1971435 76838377 := bstep (se 2 (by rfl) ⟨28814391, by rfl⟩ : syracuseStep 76838377 = 57628783) B57628783
theorem B102451169 : Blo 1971435 102451169 := bstep (se 2 (by rfl) ⟨38419188, by rfl⟩ : syracuseStep 102451169 = 76838377) B76838377
theorem B273203117 : Blo 1971435 273203117 := bstep (se 3 (by rfl) ⟨51225584, by rfl⟩ : syracuseStep 273203117 = 102451169) B102451169
theorem B182135411 : Blo 1971435 182135411 := bstep (se 1 (by rfl) ⟨136601558, by rfl⟩ : syracuseStep 182135411 = 273203117) B273203117
theorem B121423607 : Blo 1971435 121423607 := bstep (se 1 (by rfl) ⟨91067705, by rfl⟩ : syracuseStep 121423607 = 182135411) B182135411
theorem B80949071 : Blo 1971435 80949071 := bstep (se 1 (by rfl) ⟨60711803, by rfl⟩ : syracuseStep 80949071 = 121423607) B121423607
theorem B53966047 : Blo 1971435 53966047 := bstep (se 1 (by rfl) ⟨40474535, by rfl⟩ : syracuseStep 53966047 = 80949071) B80949071
theorem B71954729 : Blo 1971435 71954729 := bstep (se 2 (by rfl) ⟨26983023, by rfl⟩ : syracuseStep 71954729 = 53966047) B53966047
theorem B47969819 : Blo 1971435 47969819 := bstep (se 1 (by rfl) ⟨35977364, by rfl⟩ : syracuseStep 47969819 = 71954729) B71954729
theorem B31979879 : Blo 1971435 31979879 := bstep (se 1 (by rfl) ⟨23984909, by rfl⟩ : syracuseStep 31979879 = 47969819) B47969819
theorem B21319919 : Blo 1971435 21319919 := bstep (se 1 (by rfl) ⟨15989939, by rfl⟩ : syracuseStep 21319919 = 31979879) B31979879
theorem B14213279 : Blo 1971435 14213279 := bstep (se 1 (by rfl) ⟨10659959, by rfl⟩ : syracuseStep 14213279 = 21319919) B21319919
theorem B37902077 : Blo 1971435 37902077 := bstep (se 3 (by rfl) ⟨7106639, by rfl⟩ : syracuseStep 37902077 = 14213279) B14213279
theorem B25268051 : Blo 1971435 25268051 := bstep (se 1 (by rfl) ⟨18951038, by rfl⟩ : syracuseStep 25268051 = 37902077) B37902077
theorem B16845367 : Blo 1971435 16845367 := bstep (se 1 (by rfl) ⟨12634025, by rfl⟩ : syracuseStep 16845367 = 25268051) B25268051
theorem B22460489 : Blo 1971435 22460489 := bstep (se 2 (by rfl) ⟨8422683, by rfl⟩ : syracuseStep 22460489 = 16845367) B16845367
theorem B14973659 : Blo 1971435 14973659 := bstep (se 1 (by rfl) ⟨11230244, by rfl⟩ : syracuseStep 14973659 = 22460489) B22460489
theorem B9982439 : Blo 1971435 9982439 := bstep (se 1 (by rfl) ⟨7486829, by rfl⟩ : syracuseStep 9982439 = 14973659) B14973659
theorem B6654959 : Blo 1971435 6654959 := bstep (se 1 (by rfl) ⟨4991219, by rfl⟩ : syracuseStep 6654959 = 9982439) B9982439
theorem B4436639 : Blo 1971435 4436639 := bstep (se 1 (by rfl) ⟨3327479, by rfl⟩ : syracuseStep 4436639 = 6654959) B6654959
theorem B2957759 : Blo 1971435 2957759 := bstep (se 1 (by rfl) ⟨2218319, by rfl⟩ : syracuseStep 2957759 = 4436639) B4436639
theorem B1971839 : Blo 1971435 1971839 := bstep (se 1 (by rfl) ⟨1478879, by rfl⟩ : syracuseStep 1971839 = 2957759) B2957759
theorem B2957765 : Blo 1971435 2957765 := bbase (se 4 (by rfl) ⟨277290, by rfl⟩ : syracuseStep 2957765 = 554581) (by norm_num)
theorem B1971843 : Blo 1971435 1971843 := bstep (se 1 (by rfl) ⟨1478882, by rfl⟩ : syracuseStep 1971843 = 2957765) B2957765
theorem B3327493 : Blo 1971435 3327493 := bbase (se 4 (by rfl) ⟨311952, by rfl⟩ : syracuseStep 3327493 = 623905) (by norm_num)
theorem B4436657 : Blo 1971435 4436657 := bstep (se 2 (by rfl) ⟨1663746, by rfl⟩ : syracuseStep 4436657 = 3327493) B3327493
theorem B2957771 : Blo 1971435 2957771 := bstep (se 1 (by rfl) ⟨2218328, by rfl⟩ : syracuseStep 2957771 = 4436657) B4436657
theorem B1971847 : Blo 1971435 1971847 := bstep (se 1 (by rfl) ⟨1478885, by rfl⟩ : syracuseStep 1971847 = 2957771) B2957771
theorem B2218333 : Blo 1971435 2218333 := bbase (se 3 (by rfl) ⟨415937, by rfl⟩ : syracuseStep 2218333 = 831875) (by norm_num)
theorem B2957777 : Blo 1971435 2957777 := bstep (se 2 (by rfl) ⟨1109166, by rfl⟩ : syracuseStep 2957777 = 2218333) B2218333
theorem B1971851 : Blo 1971435 1971851 := bstep (se 1 (by rfl) ⟨1478888, by rfl⟩ : syracuseStep 1971851 = 2957777) B2957777
theorem B6655013 : Blo 1971435 6655013 := bbase (se 4 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 6655013 = 1247815) (by norm_num)
theorem B4436675 : Blo 1971435 4436675 := bstep (se 1 (by rfl) ⟨3327506, by rfl⟩ : syracuseStep 4436675 = 6655013) B6655013
theorem B2957783 : Blo 1971435 2957783 := bstep (se 1 (by rfl) ⟨2218337, by rfl⟩ : syracuseStep 2957783 = 4436675) B4436675
theorem B1971855 : Blo 1971435 1971855 := bstep (se 1 (by rfl) ⟨1478891, by rfl⟩ : syracuseStep 1971855 = 2957783) B2957783
theorem B2957789 : Blo 1971435 2957789 := bbase (se 3 (by rfl) ⟨554585, by rfl⟩ : syracuseStep 2957789 = 1109171) (by norm_num)
theorem B1971859 : Blo 1971435 1971859 := bstep (se 1 (by rfl) ⟨1478894, by rfl⟩ : syracuseStep 1971859 = 2957789) B2957789
theorem B4436693 : Blo 1971435 4436693 := bbase (se 7 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 4436693 = 103985) (by norm_num)
theorem B2957795 : Blo 1971435 2957795 := bstep (se 1 (by rfl) ⟨2218346, by rfl⟩ : syracuseStep 2957795 = 4436693) B4436693
theorem B1971863 : Blo 1971435 1971863 := bstep (se 1 (by rfl) ⟨1478897, by rfl⟩ : syracuseStep 1971863 = 2957795) B2957795
theorem B8422805 : Blo 1971435 8422805 := bbase (se 6 (by rfl) ⟨197409, by rfl⟩ : syracuseStep 8422805 = 394819) (by norm_num)
theorem B5615203 : Blo 1971435 5615203 := bstep (se 1 (by rfl) ⟨4211402, by rfl⟩ : syracuseStep 5615203 = 8422805) B8422805
theorem B7486937 : Blo 1971435 7486937 := bstep (se 2 (by rfl) ⟨2807601, by rfl⟩ : syracuseStep 7486937 = 5615203) B5615203
theorem B4991291 : Blo 1971435 4991291 := bstep (se 1 (by rfl) ⟨3743468, by rfl⟩ : syracuseStep 4991291 = 7486937) B7486937
theorem B3327527 : Blo 1971435 3327527 := bstep (se 1 (by rfl) ⟨2495645, by rfl⟩ : syracuseStep 3327527 = 4991291) B4991291
theorem B2218351 : Blo 1971435 2218351 := bstep (se 1 (by rfl) ⟨1663763, by rfl⟩ : syracuseStep 2218351 = 3327527) B3327527
theorem B2957801 : Blo 1971435 2957801 := bstep (se 2 (by rfl) ⟨1109175, by rfl⟩ : syracuseStep 2957801 = 2218351) B2218351
theorem B1971867 : Blo 1971435 1971867 := bstep (se 1 (by rfl) ⟨1478900, by rfl⟩ : syracuseStep 1971867 = 2957801) B2957801
theorem B4497245 : Blo 1971435 4497245 := bbase (se 3 (by rfl) ⟨843233, by rfl⟩ : syracuseStep 4497245 = 1686467) (by norm_num)
theorem B2998163 : Blo 1971435 2998163 := bstep (se 1 (by rfl) ⟨2248622, by rfl⟩ : syracuseStep 2998163 = 4497245) B4497245
theorem B1998775 : Blo 1971435 1998775 := bstep (se 1 (by rfl) ⟨1499081, by rfl⟩ : syracuseStep 1998775 = 2998163) B2998163
theorem B10660133 : Blo 1971435 10660133 := bstep (se 4 (by rfl) ⟨999387, by rfl⟩ : syracuseStep 10660133 = 1998775) B1998775
theorem B28427021 : Blo 1971435 28427021 := bstep (se 3 (by rfl) ⟨5330066, by rfl⟩ : syracuseStep 28427021 = 10660133) B10660133
theorem B18951347 : Blo 1971435 18951347 := bstep (se 1 (by rfl) ⟨14213510, by rfl⟩ : syracuseStep 18951347 = 28427021) B28427021
theorem B12634231 : Blo 1971435 12634231 := bstep (se 1 (by rfl) ⟨9475673, by rfl⟩ : syracuseStep 12634231 = 18951347) B18951347
theorem B16845641 : Blo 1971435 16845641 := bstep (se 2 (by rfl) ⟨6317115, by rfl⟩ : syracuseStep 16845641 = 12634231) B12634231
theorem B11230427 : Blo 1971435 11230427 := bstep (se 1 (by rfl) ⟨8422820, by rfl⟩ : syracuseStep 11230427 = 16845641) B16845641
theorem B7486951 : Blo 1971435 7486951 := bstep (se 1 (by rfl) ⟨5615213, by rfl⟩ : syracuseStep 7486951 = 11230427) B11230427
theorem B9982601 : Blo 1971435 9982601 := bstep (se 2 (by rfl) ⟨3743475, by rfl⟩ : syracuseStep 9982601 = 7486951) B7486951
theorem B6655067 : Blo 1971435 6655067 := bstep (se 1 (by rfl) ⟨4991300, by rfl⟩ : syracuseStep 6655067 = 9982601) B9982601
theorem B4436711 : Blo 1971435 4436711 := bstep (se 1 (by rfl) ⟨3327533, by rfl⟩ : syracuseStep 4436711 = 6655067) B6655067
theorem B2957807 : Blo 1971435 2957807 := bstep (se 1 (by rfl) ⟨2218355, by rfl⟩ : syracuseStep 2957807 = 4436711) B4436711
theorem B1971871 : Blo 1971435 1971871 := bstep (se 1 (by rfl) ⟨1478903, by rfl⟩ : syracuseStep 1971871 = 2957807) B2957807
theorem B2957813 : Blo 1971435 2957813 := bbase (se 5 (by rfl) ⟨138647, by rfl⟩ : syracuseStep 2957813 = 277295) (by norm_num)
theorem B1971875 : Blo 1971435 1971875 := bstep (se 1 (by rfl) ⟨1478906, by rfl⟩ : syracuseStep 1971875 = 2957813) B2957813
theorem B5615237 : Blo 1971435 5615237 := bbase (se 4 (by rfl) ⟨526428, by rfl⟩ : syracuseStep 5615237 = 1052857) (by norm_num)
theorem B3743491 : Blo 1971435 3743491 := bstep (se 1 (by rfl) ⟨2807618, by rfl⟩ : syracuseStep 3743491 = 5615237) B5615237
theorem B4991321 : Blo 1971435 4991321 := bstep (se 2 (by rfl) ⟨1871745, by rfl⟩ : syracuseStep 4991321 = 3743491) B3743491
theorem B3327547 : Blo 1971435 3327547 := bstep (se 1 (by rfl) ⟨2495660, by rfl⟩ : syracuseStep 3327547 = 4991321) B4991321
theorem B4436729 : Blo 1971435 4436729 := bstep (se 2 (by rfl) ⟨1663773, by rfl⟩ : syracuseStep 4436729 = 3327547) B3327547
theorem B2957819 : Blo 1971435 2957819 := bstep (se 1 (by rfl) ⟨2218364, by rfl⟩ : syracuseStep 2957819 = 4436729) B4436729
theorem B1971879 : Blo 1971435 1971879 := bstep (se 1 (by rfl) ⟨1478909, by rfl⟩ : syracuseStep 1971879 = 2957819) B2957819
theorem B2218369 : Blo 1971435 2218369 := bbase (se 2 (by rfl) ⟨831888, by rfl⟩ : syracuseStep 2218369 = 1663777) (by norm_num)
theorem B2957825 : Blo 1971435 2957825 := bstep (se 2 (by rfl) ⟨1109184, by rfl⟩ : syracuseStep 2957825 = 2218369) B2218369
theorem B1971883 : Blo 1971435 1971883 := bstep (se 1 (by rfl) ⟨1478912, by rfl⟩ : syracuseStep 1971883 = 2957825) B2957825
theorem B4991341 : Blo 1971435 4991341 := bbase (se 3 (by rfl) ⟨935876, by rfl⟩ : syracuseStep 4991341 = 1871753) (by norm_num)
theorem B6655121 : Blo 1971435 6655121 := bstep (se 2 (by rfl) ⟨2495670, by rfl⟩ : syracuseStep 6655121 = 4991341) B4991341
theorem B4436747 : Blo 1971435 4436747 := bstep (se 1 (by rfl) ⟨3327560, by rfl⟩ : syracuseStep 4436747 = 6655121) B6655121
theorem B2957831 : Blo 1971435 2957831 := bstep (se 1 (by rfl) ⟨2218373, by rfl⟩ : syracuseStep 2957831 = 4436747) B4436747
theorem B1971887 : Blo 1971435 1971887 := bstep (se 1 (by rfl) ⟨1478915, by rfl⟩ : syracuseStep 1971887 = 2957831) B2957831
theorem B2957837 : Blo 1971435 2957837 := bbase (se 3 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 2957837 = 1109189) (by norm_num)
theorem B1971891 : Blo 1971435 1971891 := bstep (se 1 (by rfl) ⟨1478918, by rfl⟩ : syracuseStep 1971891 = 2957837) B2957837
theorem B4436765 : Blo 1971435 4436765 := bbase (se 3 (by rfl) ⟨831893, by rfl⟩ : syracuseStep 4436765 = 1663787) (by norm_num)
theorem B2957843 : Blo 1971435 2957843 := bstep (se 1 (by rfl) ⟨2218382, by rfl⟩ : syracuseStep 2957843 = 4436765) B4436765
theorem B1971895 : Blo 1971435 1971895 := bstep (se 1 (by rfl) ⟨1478921, by rfl⟩ : syracuseStep 1971895 = 2957843) B2957843
theorem B3327581 : Blo 1971435 3327581 := bbase (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) (by norm_num)
theorem B2218387 : Blo 1971435 2218387 := bstep (se 1 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 2218387 = 3327581) B3327581
theorem B2957849 : Blo 1971435 2957849 := bstep (se 2 (by rfl) ⟨1109193, by rfl⟩ : syracuseStep 2957849 = 2218387) B2218387
theorem B1971899 : Blo 1971435 1971899 := bstep (se 1 (by rfl) ⟨1478924, by rfl⟩ : syracuseStep 1971899 = 2957849) B2957849
theorem B2368957 : Blo 1971435 2368957 := bbase (se 3 (by rfl) ⟨444179, by rfl⟩ : syracuseStep 2368957 = 888359) (by norm_num)
theorem B3158609 : Blo 1971435 3158609 := bstep (se 2 (by rfl) ⟨1184478, by rfl⟩ : syracuseStep 3158609 = 2368957) B2368957
theorem B8422957 : Blo 1971435 8422957 := bstep (se 3 (by rfl) ⟨1579304, by rfl⟩ : syracuseStep 8422957 = 3158609) B3158609
theorem B11230609 : Blo 1971435 11230609 := bstep (se 2 (by rfl) ⟨4211478, by rfl⟩ : syracuseStep 11230609 = 8422957) B8422957
theorem B14974145 : Blo 1971435 14974145 := bstep (se 2 (by rfl) ⟨5615304, by rfl⟩ : syracuseStep 14974145 = 11230609) B11230609
theorem B9982763 : Blo 1971435 9982763 := bstep (se 1 (by rfl) ⟨7487072, by rfl⟩ : syracuseStep 9982763 = 14974145) B14974145
theorem B6655175 : Blo 1971435 6655175 := bstep (se 1 (by rfl) ⟨4991381, by rfl⟩ : syracuseStep 6655175 = 9982763) B9982763
theorem B4436783 : Blo 1971435 4436783 := bstep (se 1 (by rfl) ⟨3327587, by rfl⟩ : syracuseStep 4436783 = 6655175) B6655175
theorem B2957855 : Blo 1971435 2957855 := bstep (se 1 (by rfl) ⟨2218391, by rfl⟩ : syracuseStep 2957855 = 4436783) B4436783
theorem B1971903 : Blo 1971435 1971903 := bstep (se 1 (by rfl) ⟨1478927, by rfl⟩ : syracuseStep 1971903 = 2957855) B2957855
theorem B2957861 : Blo 1971435 2957861 := bbase (se 4 (by rfl) ⟨277299, by rfl⟩ : syracuseStep 2957861 = 554599) (by norm_num)
theorem B1971907 : Blo 1971435 1971907 := bstep (se 1 (by rfl) ⟨1478930, by rfl⟩ : syracuseStep 1971907 = 2957861) B2957861
theorem B2495701 : Blo 1971435 2495701 := bbase (se 7 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 2495701 = 58493) (by norm_num)
theorem B3327601 : Blo 1971435 3327601 := bstep (se 2 (by rfl) ⟨1247850, by rfl⟩ : syracuseStep 3327601 = 2495701) B2495701
theorem B4436801 : Blo 1971435 4436801 := bstep (se 2 (by rfl) ⟨1663800, by rfl⟩ : syracuseStep 4436801 = 3327601) B3327601
theorem B2957867 : Blo 1971435 2957867 := bstep (se 1 (by rfl) ⟨2218400, by rfl⟩ : syracuseStep 2957867 = 4436801) B4436801
theorem B1971911 : Blo 1971435 1971911 := bstep (se 1 (by rfl) ⟨1478933, by rfl⟩ : syracuseStep 1971911 = 2957867) B2957867
theorem B2218405 : Blo 1971435 2218405 := bbase (se 4 (by rfl) ⟨207975, by rfl⟩ : syracuseStep 2218405 = 415951) (by norm_num)
theorem B2957873 : Blo 1971435 2957873 := bstep (se 2 (by rfl) ⟨1109202, by rfl⟩ : syracuseStep 2957873 = 2218405) B2218405
theorem B1971915 : Blo 1971435 1971915 := bstep (se 1 (by rfl) ⟨1478936, by rfl⟩ : syracuseStep 1971915 = 2957873) B2957873
theorem B2998237 : Blo 1971435 2998237 := bbase (se 3 (by rfl) ⟨562169, by rfl⟩ : syracuseStep 2998237 = 1124339) (by norm_num)
theorem B3997649 : Blo 1971435 3997649 := bstep (se 2 (by rfl) ⟨1499118, by rfl⟩ : syracuseStep 3997649 = 2998237) B2998237
theorem B2665099 : Blo 1971435 2665099 := bstep (se 1 (by rfl) ⟨1998824, by rfl⟩ : syracuseStep 2665099 = 3997649) B3997649
theorem B3553465 : Blo 1971435 3553465 := bstep (se 2 (by rfl) ⟨1332549, by rfl⟩ : syracuseStep 3553465 = 2665099) B2665099
theorem B4737953 : Blo 1971435 4737953 := bstep (se 2 (by rfl) ⟨1776732, by rfl⟩ : syracuseStep 4737953 = 3553465) B3553465
theorem B12634541 : Blo 1971435 12634541 := bstep (se 3 (by rfl) ⟨2368976, by rfl⟩ : syracuseStep 12634541 = 4737953) B4737953
theorem B8423027 : Blo 1971435 8423027 := bstep (se 1 (by rfl) ⟨6317270, by rfl⟩ : syracuseStep 8423027 = 12634541) B12634541
theorem B5615351 : Blo 1971435 5615351 := bstep (se 1 (by rfl) ⟨4211513, by rfl⟩ : syracuseStep 5615351 = 8423027) B8423027
theorem B3743567 : Blo 1971435 3743567 := bstep (se 1 (by rfl) ⟨2807675, by rfl⟩ : syracuseStep 3743567 = 5615351) B5615351
theorem B2495711 : Blo 1971435 2495711 := bstep (se 1 (by rfl) ⟨1871783, by rfl⟩ : syracuseStep 2495711 = 3743567) B3743567
theorem B6655229 : Blo 1971435 6655229 := bstep (se 3 (by rfl) ⟨1247855, by rfl⟩ : syracuseStep 6655229 = 2495711) B2495711
theorem B4436819 : Blo 1971435 4436819 := bstep (se 1 (by rfl) ⟨3327614, by rfl⟩ : syracuseStep 4436819 = 6655229) B6655229
theorem B2957879 : Blo 1971435 2957879 := bstep (se 1 (by rfl) ⟨2218409, by rfl⟩ : syracuseStep 2957879 = 4436819) B4436819
theorem B1971919 : Blo 1971435 1971919 := bstep (se 1 (by rfl) ⟨1478939, by rfl⟩ : syracuseStep 1971919 = 2957879) B2957879
theorem B2957885 : Blo 1971435 2957885 := bbase (se 3 (by rfl) ⟨554603, by rfl⟩ : syracuseStep 2957885 = 1109207) (by norm_num)
theorem B1971923 : Blo 1971435 1971923 := bstep (se 1 (by rfl) ⟨1478942, by rfl⟩ : syracuseStep 1971923 = 2957885) B2957885
theorem B4436837 : Blo 1971435 4436837 := bbase (se 4 (by rfl) ⟨415953, by rfl⟩ : syracuseStep 4436837 = 831907) (by norm_num)
theorem B2957891 : Blo 1971435 2957891 := bstep (se 1 (by rfl) ⟨2218418, by rfl⟩ : syracuseStep 2957891 = 4436837) B4436837
theorem B1971927 : Blo 1971435 1971927 := bstep (se 1 (by rfl) ⟨1478945, by rfl⟩ : syracuseStep 1971927 = 2957891) B2957891
theorem B4991453 : Blo 1971435 4991453 := bbase (se 3 (by rfl) ⟨935897, by rfl⟩ : syracuseStep 4991453 = 1871795) (by norm_num)
theorem B3327635 : Blo 1971435 3327635 := bstep (se 1 (by rfl) ⟨2495726, by rfl⟩ : syracuseStep 3327635 = 4991453) B4991453
theorem B2218423 : Blo 1971435 2218423 := bstep (se 1 (by rfl) ⟨1663817, by rfl⟩ : syracuseStep 2218423 = 3327635) B3327635
theorem B2957897 : Blo 1971435 2957897 := bstep (se 2 (by rfl) ⟨1109211, by rfl⟩ : syracuseStep 2957897 = 2218423) B2218423
theorem B1971931 : Blo 1971435 1971931 := bstep (se 1 (by rfl) ⟨1478948, by rfl⟩ : syracuseStep 1971931 = 2957897) B2957897
theorem B3743597 : Blo 1971435 3743597 := bbase (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) (by norm_num)
theorem B9982925 : Blo 1971435 9982925 := bstep (se 3 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 9982925 = 3743597) B3743597
theorem B6655283 : Blo 1971435 6655283 := bstep (se 1 (by rfl) ⟨4991462, by rfl⟩ : syracuseStep 6655283 = 9982925) B9982925
theorem B4436855 : Blo 1971435 4436855 := bstep (se 1 (by rfl) ⟨3327641, by rfl⟩ : syracuseStep 4436855 = 6655283) B6655283
theorem B2957903 : Blo 1971435 2957903 := bstep (se 1 (by rfl) ⟨2218427, by rfl⟩ : syracuseStep 2957903 = 4436855) B4436855
theorem B1971935 : Blo 1971435 1971935 := bstep (se 1 (by rfl) ⟨1478951, by rfl⟩ : syracuseStep 1971935 = 2957903) B2957903
theorem B2957909 : Blo 1971435 2957909 := bbase (se 8 (by rfl) ⟨17331, by rfl⟩ : syracuseStep 2957909 = 34663) (by norm_num)
theorem B1971939 : Blo 1971435 1971939 := bstep (se 1 (by rfl) ⟨1478954, by rfl⟩ : syracuseStep 1971939 = 2957909) B2957909
theorem B9476021 : Blo 1971435 9476021 := bbase (se 5 (by rfl) ⟨444188, by rfl⟩ : syracuseStep 9476021 = 888377) (by norm_num)
theorem B6317347 : Blo 1971435 6317347 := bstep (se 1 (by rfl) ⟨4738010, by rfl⟩ : syracuseStep 6317347 = 9476021) B9476021
theorem B8423129 : Blo 1971435 8423129 := bstep (se 2 (by rfl) ⟨3158673, by rfl⟩ : syracuseStep 8423129 = 6317347) B6317347
theorem B5615419 : Blo 1971435 5615419 := bstep (se 1 (by rfl) ⟨4211564, by rfl⟩ : syracuseStep 5615419 = 8423129) B8423129
theorem B7487225 : Blo 1971435 7487225 := bstep (se 2 (by rfl) ⟨2807709, by rfl⟩ : syracuseStep 7487225 = 5615419) B5615419
theorem B4991483 : Blo 1971435 4991483 := bstep (se 1 (by rfl) ⟨3743612, by rfl⟩ : syracuseStep 4991483 = 7487225) B7487225
theorem B3327655 : Blo 1971435 3327655 := bstep (se 1 (by rfl) ⟨2495741, by rfl⟩ : syracuseStep 3327655 = 4991483) B4991483
theorem B4436873 : Blo 1971435 4436873 := bstep (se 2 (by rfl) ⟨1663827, by rfl⟩ : syracuseStep 4436873 = 3327655) B3327655
theorem B2957915 : Blo 1971435 2957915 := bstep (se 1 (by rfl) ⟨2218436, by rfl⟩ : syracuseStep 2957915 = 4436873) B4436873
theorem B1971943 : Blo 1971435 1971943 := bstep (se 1 (by rfl) ⟨1478957, by rfl⟩ : syracuseStep 1971943 = 2957915) B2957915
theorem B2218441 : Blo 1971435 2218441 := bbase (se 2 (by rfl) ⟨831915, by rfl⟩ : syracuseStep 2218441 = 1663831) (by norm_num)
theorem B2957921 : Blo 1971435 2957921 := bstep (se 2 (by rfl) ⟨1109220, by rfl⟩ : syracuseStep 2957921 = 2218441) B2218441
theorem B1971947 : Blo 1971435 1971947 := bstep (se 1 (by rfl) ⟨1478960, by rfl⟩ : syracuseStep 1971947 = 2957921) B2957921
theorem B16846325 : Blo 1971435 16846325 := bbase (se 5 (by rfl) ⟨789671, by rfl⟩ : syracuseStep 16846325 = 1579343) (by norm_num)
theorem B11230883 : Blo 1971435 11230883 := bstep (se 1 (by rfl) ⟨8423162, by rfl⟩ : syracuseStep 11230883 = 16846325) B16846325
theorem B7487255 : Blo 1971435 7487255 := bstep (se 1 (by rfl) ⟨5615441, by rfl⟩ : syracuseStep 7487255 = 11230883) B11230883
theorem B4991503 : Blo 1971435 4991503 := bstep (se 1 (by rfl) ⟨3743627, by rfl⟩ : syracuseStep 4991503 = 7487255) B7487255
theorem B6655337 : Blo 1971435 6655337 := bstep (se 2 (by rfl) ⟨2495751, by rfl⟩ : syracuseStep 6655337 = 4991503) B4991503
theorem B4436891 : Blo 1971435 4436891 := bstep (se 1 (by rfl) ⟨3327668, by rfl⟩ : syracuseStep 4436891 = 6655337) B6655337
theorem B2957927 : Blo 1971435 2957927 := bstep (se 1 (by rfl) ⟨2218445, by rfl⟩ : syracuseStep 2957927 = 4436891) B4436891
theorem B1971951 : Blo 1971435 1971951 := bstep (se 1 (by rfl) ⟨1478963, by rfl⟩ : syracuseStep 1971951 = 2957927) B2957927
theorem B2957933 : Blo 1971435 2957933 := bbase (se 3 (by rfl) ⟨554612, by rfl⟩ : syracuseStep 2957933 = 1109225) (by norm_num)
theorem B1971955 : Blo 1971435 1971955 := bstep (se 1 (by rfl) ⟨1478966, by rfl⟩ : syracuseStep 1971955 = 2957933) B2957933
theorem B4436909 : Blo 1971435 4436909 := bbase (se 3 (by rfl) ⟨831920, by rfl⟩ : syracuseStep 4436909 = 1663841) (by norm_num)
theorem B2957939 : Blo 1971435 2957939 := bstep (se 1 (by rfl) ⟨2218454, by rfl⟩ : syracuseStep 2957939 = 4436909) B4436909
theorem B1971959 : Blo 1971435 1971959 := bstep (se 1 (by rfl) ⟨1478969, by rfl⟩ : syracuseStep 1971959 = 2957939) B2957939
theorem B5615477 : Blo 1971435 5615477 := bbase (se 5 (by rfl) ⟨263225, by rfl⟩ : syracuseStep 5615477 = 526451) (by norm_num)
theorem B3743651 : Blo 1971435 3743651 := bstep (se 1 (by rfl) ⟨2807738, by rfl⟩ : syracuseStep 3743651 = 5615477) B5615477
theorem B2495767 : Blo 1971435 2495767 := bstep (se 1 (by rfl) ⟨1871825, by rfl⟩ : syracuseStep 2495767 = 3743651) B3743651
theorem B3327689 : Blo 1971435 3327689 := bstep (se 2 (by rfl) ⟨1247883, by rfl⟩ : syracuseStep 3327689 = 2495767) B2495767
theorem B2218459 : Blo 1971435 2218459 := bstep (se 1 (by rfl) ⟨1663844, by rfl⟩ : syracuseStep 2218459 = 3327689) B3327689
theorem B2957945 : Blo 1971435 2957945 := bstep (se 2 (by rfl) ⟨1109229, by rfl⟩ : syracuseStep 2957945 = 2218459) B2218459
theorem B1971963 : Blo 1971435 1971963 := bstep (se 1 (by rfl) ⟨1478972, by rfl⟩ : syracuseStep 1971963 = 2957945) B2957945
theorem B7204069 : Blo 1971435 7204069 := bbase (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) (by norm_num)
theorem B9605425 : Blo 1971435 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B12807233 : Blo 1971435 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B8538155 : Blo 1971435 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B5692103 : Blo 1971435 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B3794735 : Blo 1971435 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B2529823 : Blo 1971435 2529823 := bstep (se 1 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 2529823 = 3794735) B3794735
theorem B3373097 : Blo 1971435 3373097 := bstep (se 2 (by rfl) ⟨1264911, by rfl⟩ : syracuseStep 3373097 = 2529823) B2529823
theorem B8994925 : Blo 1971435 8994925 := bstep (se 3 (by rfl) ⟨1686548, by rfl⟩ : syracuseStep 8994925 = 3373097) B3373097
theorem B11993233 : Blo 1971435 11993233 := bstep (se 2 (by rfl) ⟨4497462, by rfl⟩ : syracuseStep 11993233 = 8994925) B8994925
theorem B15990977 : Blo 1971435 15990977 := bstep (se 2 (by rfl) ⟨5996616, by rfl⟩ : syracuseStep 15990977 = 11993233) B11993233
theorem B42642605 : Blo 1971435 42642605 := bstep (se 3 (by rfl) ⟨7995488, by rfl⟩ : syracuseStep 42642605 = 15990977) B15990977
theorem B28428403 : Blo 1971435 28428403 := bstep (se 1 (by rfl) ⟨21321302, by rfl⟩ : syracuseStep 28428403 = 42642605) B42642605
theorem B37904537 : Blo 1971435 37904537 := bstep (se 2 (by rfl) ⟨14214201, by rfl⟩ : syracuseStep 37904537 = 28428403) B28428403
theorem B25269691 : Blo 1971435 25269691 := bstep (se 1 (by rfl) ⟨18952268, by rfl⟩ : syracuseStep 25269691 = 37904537) B37904537
theorem B33692921 : Blo 1971435 33692921 := bstep (se 2 (by rfl) ⟨12634845, by rfl⟩ : syracuseStep 33692921 = 25269691) B25269691
theorem B22461947 : Blo 1971435 22461947 := bstep (se 1 (by rfl) ⟨16846460, by rfl⟩ : syracuseStep 22461947 = 33692921) B33692921
theorem B14974631 : Blo 1971435 14974631 := bstep (se 1 (by rfl) ⟨11230973, by rfl⟩ : syracuseStep 14974631 = 22461947) B22461947
theorem B9983087 : Blo 1971435 9983087 := bstep (se 1 (by rfl) ⟨7487315, by rfl⟩ : syracuseStep 9983087 = 14974631) B14974631
theorem B6655391 : Blo 1971435 6655391 := bstep (se 1 (by rfl) ⟨4991543, by rfl⟩ : syracuseStep 6655391 = 9983087) B9983087
theorem B4436927 : Blo 1971435 4436927 := bstep (se 1 (by rfl) ⟨3327695, by rfl⟩ : syracuseStep 4436927 = 6655391) B6655391
theorem B2957951 : Blo 1971435 2957951 := bstep (se 1 (by rfl) ⟨2218463, by rfl⟩ : syracuseStep 2957951 = 4436927) B4436927
theorem B1971967 : Blo 1971435 1971967 := bstep (se 1 (by rfl) ⟨1478975, by rfl⟩ : syracuseStep 1971967 = 2957951) B2957951
theorem B2957957 : Blo 1971435 2957957 := bbase (se 4 (by rfl) ⟨277308, by rfl⟩ : syracuseStep 2957957 = 554617) (by norm_num)
theorem B1971971 : Blo 1971435 1971971 := bstep (se 1 (by rfl) ⟨1478978, by rfl⟩ : syracuseStep 1971971 = 2957957) B2957957
theorem B3327709 : Blo 1971435 3327709 := bbase (se 3 (by rfl) ⟨623945, by rfl⟩ : syracuseStep 3327709 = 1247891) (by norm_num)
theorem B4436945 : Blo 1971435 4436945 := bstep (se 2 (by rfl) ⟨1663854, by rfl⟩ : syracuseStep 4436945 = 3327709) B3327709
theorem B2957963 : Blo 1971435 2957963 := bstep (se 1 (by rfl) ⟨2218472, by rfl⟩ : syracuseStep 2957963 = 4436945) B4436945
theorem B1971975 : Blo 1971435 1971975 := bstep (se 1 (by rfl) ⟨1478981, by rfl⟩ : syracuseStep 1971975 = 2957963) B2957963
theorem B2218477 : Blo 1971435 2218477 := bbase (se 3 (by rfl) ⟨415964, by rfl⟩ : syracuseStep 2218477 = 831929) (by norm_num)
theorem B2957969 : Blo 1971435 2957969 := bstep (se 2 (by rfl) ⟨1109238, by rfl⟩ : syracuseStep 2957969 = 2218477) B2218477
theorem B1971979 : Blo 1971435 1971979 := bstep (se 1 (by rfl) ⟨1478984, by rfl⟩ : syracuseStep 1971979 = 2957969) B2957969
theorem B6655445 : Blo 1971435 6655445 := bbase (se 7 (by rfl) ⟨77993, by rfl⟩ : syracuseStep 6655445 = 155987) (by norm_num)
theorem B4436963 : Blo 1971435 4436963 := bstep (se 1 (by rfl) ⟨3327722, by rfl⟩ : syracuseStep 4436963 = 6655445) B6655445
theorem B2957975 : Blo 1971435 2957975 := bstep (se 1 (by rfl) ⟨2218481, by rfl⟩ : syracuseStep 2957975 = 4436963) B4436963
theorem B1971983 : Blo 1971435 1971983 := bstep (se 1 (by rfl) ⟨1478987, by rfl⟩ : syracuseStep 1971983 = 2957975) B2957975
theorem B2957981 : Blo 1971435 2957981 := bbase (se 3 (by rfl) ⟨554621, by rfl⟩ : syracuseStep 2957981 = 1109243) (by norm_num)
theorem B1971987 : Blo 1971435 1971987 := bstep (se 1 (by rfl) ⟨1478990, by rfl⟩ : syracuseStep 1971987 = 2957981) B2957981
theorem B4436981 : Blo 1971435 4436981 := bbase (se 5 (by rfl) ⟨207983, by rfl⟩ : syracuseStep 4436981 = 415967) (by norm_num)
theorem B2957987 : Blo 1971435 2957987 := bstep (se 1 (by rfl) ⟨2218490, by rfl⟩ : syracuseStep 2957987 = 4436981) B4436981
theorem B1971991 : Blo 1971435 1971991 := bstep (se 1 (by rfl) ⟨1478993, by rfl⟩ : syracuseStep 1971991 = 2957987) B2957987
theorem B12807413 : Blo 1971435 12807413 := bbase (se 5 (by rfl) ⟨600347, by rfl⟩ : syracuseStep 12807413 = 1200695) (by norm_num)
theorem B8538275 : Blo 1971435 8538275 := bstep (se 1 (by rfl) ⟨6403706, by rfl⟩ : syracuseStep 8538275 = 12807413) B12807413
theorem B5692183 : Blo 1971435 5692183 := bstep (se 1 (by rfl) ⟨4269137, by rfl⟩ : syracuseStep 5692183 = 8538275) B8538275
theorem B30358309 : Blo 1971435 30358309 := bstep (se 4 (by rfl) ⟨2846091, by rfl⟩ : syracuseStep 30358309 = 5692183) B5692183
theorem B40477745 : Blo 1971435 40477745 := bstep (se 2 (by rfl) ⟨15179154, by rfl⟩ : syracuseStep 40477745 = 30358309) B30358309
theorem B26985163 : Blo 1971435 26985163 := bstep (se 1 (by rfl) ⟨20238872, by rfl⟩ : syracuseStep 26985163 = 40477745) B40477745
theorem B35980217 : Blo 1971435 35980217 := bstep (se 2 (by rfl) ⟨13492581, by rfl⟩ : syracuseStep 35980217 = 26985163) B26985163
theorem B23986811 : Blo 1971435 23986811 := bstep (se 1 (by rfl) ⟨17990108, by rfl⟩ : syracuseStep 23986811 = 35980217) B35980217
theorem B63964829 : Blo 1971435 63964829 := bstep (se 3 (by rfl) ⟨11993405, by rfl⟩ : syracuseStep 63964829 = 23986811) B23986811
theorem B42643219 : Blo 1971435 42643219 := bstep (se 1 (by rfl) ⟨31982414, by rfl⟩ : syracuseStep 42643219 = 63964829) B63964829
theorem B56857625 : Blo 1971435 56857625 := bstep (se 2 (by rfl) ⟨21321609, by rfl⟩ : syracuseStep 56857625 = 42643219) B42643219
theorem B37905083 : Blo 1971435 37905083 := bstep (se 1 (by rfl) ⟨28428812, by rfl⟩ : syracuseStep 37905083 = 56857625) B56857625
theorem B25270055 : Blo 1971435 25270055 := bstep (se 1 (by rfl) ⟨18952541, by rfl⟩ : syracuseStep 25270055 = 37905083) B37905083
theorem B16846703 : Blo 1971435 16846703 := bstep (se 1 (by rfl) ⟨12635027, by rfl⟩ : syracuseStep 16846703 = 25270055) B25270055
theorem B11231135 : Blo 1971435 11231135 := bstep (se 1 (by rfl) ⟨8423351, by rfl⟩ : syracuseStep 11231135 = 16846703) B16846703
theorem B7487423 : Blo 1971435 7487423 := bstep (se 1 (by rfl) ⟨5615567, by rfl⟩ : syracuseStep 7487423 = 11231135) B11231135
theorem B4991615 : Blo 1971435 4991615 := bstep (se 1 (by rfl) ⟨3743711, by rfl⟩ : syracuseStep 4991615 = 7487423) B7487423
theorem B3327743 : Blo 1971435 3327743 := bstep (se 1 (by rfl) ⟨2495807, by rfl⟩ : syracuseStep 3327743 = 4991615) B4991615
theorem B2218495 : Blo 1971435 2218495 := bstep (se 1 (by rfl) ⟨1663871, by rfl⟩ : syracuseStep 2218495 = 3327743) B3327743
theorem B2957993 : Blo 1971435 2957993 := bstep (se 2 (by rfl) ⟨1109247, by rfl⟩ : syracuseStep 2957993 = 2218495) B2218495
theorem B1971995 : Blo 1971435 1971995 := bstep (se 1 (by rfl) ⟨1478996, by rfl⟩ : syracuseStep 1971995 = 2957993) B2957993
theorem B2807789 : Blo 1971435 2807789 := bbase (se 3 (by rfl) ⟨526460, by rfl⟩ : syracuseStep 2807789 = 1052921) (by norm_num)
theorem B7487437 : Blo 1971435 7487437 := bstep (se 3 (by rfl) ⟨1403894, by rfl⟩ : syracuseStep 7487437 = 2807789) B2807789
theorem B9983249 : Blo 1971435 9983249 := bstep (se 2 (by rfl) ⟨3743718, by rfl⟩ : syracuseStep 9983249 = 7487437) B7487437
theorem B6655499 : Blo 1971435 6655499 := bstep (se 1 (by rfl) ⟨4991624, by rfl⟩ : syracuseStep 6655499 = 9983249) B9983249
theorem B4436999 : Blo 1971435 4436999 := bstep (se 1 (by rfl) ⟨3327749, by rfl⟩ : syracuseStep 4436999 = 6655499) B6655499
theorem B2957999 : Blo 1971435 2957999 := bstep (se 1 (by rfl) ⟨2218499, by rfl⟩ : syracuseStep 2957999 = 4436999) B4436999
theorem B1971999 : Blo 1971435 1971999 := bstep (se 1 (by rfl) ⟨1478999, by rfl⟩ : syracuseStep 1971999 = 2957999) B2957999
theorem B2958005 : Blo 1971435 2958005 := bbase (se 5 (by rfl) ⟨138656, by rfl⟩ : syracuseStep 2958005 = 277313) (by norm_num)
theorem B1972003 : Blo 1971435 1972003 := bstep (se 1 (by rfl) ⟨1479002, by rfl⟩ : syracuseStep 1972003 = 2958005) B2958005
theorem B4991645 : Blo 1971435 4991645 := bbase (se 3 (by rfl) ⟨935933, by rfl⟩ : syracuseStep 4991645 = 1871867) (by norm_num)
theorem B3327763 : Blo 1971435 3327763 := bstep (se 1 (by rfl) ⟨2495822, by rfl⟩ : syracuseStep 3327763 = 4991645) B4991645
theorem B4437017 : Blo 1971435 4437017 := bstep (se 2 (by rfl) ⟨1663881, by rfl⟩ : syracuseStep 4437017 = 3327763) B3327763
theorem B2958011 : Blo 1971435 2958011 := bstep (se 1 (by rfl) ⟨2218508, by rfl⟩ : syracuseStep 2958011 = 4437017) B4437017
theorem B1972007 : Blo 1971435 1972007 := bstep (se 1 (by rfl) ⟨1479005, by rfl⟩ : syracuseStep 1972007 = 2958011) B2958011
theorem B2218513 : Blo 1971435 2218513 := bbase (se 2 (by rfl) ⟨831942, by rfl⟩ : syracuseStep 2218513 = 1663885) (by norm_num)
theorem B2958017 : Blo 1971435 2958017 := bstep (se 2 (by rfl) ⟨1109256, by rfl⟩ : syracuseStep 2958017 = 2218513) B2218513
theorem B1972011 : Blo 1971435 1972011 := bstep (se 1 (by rfl) ⟨1479008, by rfl⟩ : syracuseStep 1972011 = 2958017) B2958017
theorem B3743749 : Blo 1971435 3743749 := bbase (se 4 (by rfl) ⟨350976, by rfl⟩ : syracuseStep 3743749 = 701953) (by norm_num)
theorem B4991665 : Blo 1971435 4991665 := bstep (se 2 (by rfl) ⟨1871874, by rfl⟩ : syracuseStep 4991665 = 3743749) B3743749
theorem B6655553 : Blo 1971435 6655553 := bstep (se 2 (by rfl) ⟨2495832, by rfl⟩ : syracuseStep 6655553 = 4991665) B4991665
theorem B4437035 : Blo 1971435 4437035 := bstep (se 1 (by rfl) ⟨3327776, by rfl⟩ : syracuseStep 4437035 = 6655553) B6655553
theorem B2958023 : Blo 1971435 2958023 := bstep (se 1 (by rfl) ⟨2218517, by rfl⟩ : syracuseStep 2958023 = 4437035) B4437035
theorem B1972015 : Blo 1971435 1972015 := bstep (se 1 (by rfl) ⟨1479011, by rfl⟩ : syracuseStep 1972015 = 2958023) B2958023
theorem B2958029 : Blo 1971435 2958029 := bbase (se 3 (by rfl) ⟨554630, by rfl⟩ : syracuseStep 2958029 = 1109261) (by norm_num)
theorem B1972019 : Blo 1971435 1972019 := bstep (se 1 (by rfl) ⟨1479014, by rfl⟩ : syracuseStep 1972019 = 2958029) B2958029
theorem B4437053 : Blo 1971435 4437053 := bbase (se 3 (by rfl) ⟨831947, by rfl⟩ : syracuseStep 4437053 = 1663895) (by norm_num)
theorem B2958035 : Blo 1971435 2958035 := bstep (se 1 (by rfl) ⟨2218526, by rfl⟩ : syracuseStep 2958035 = 4437053) B4437053
theorem B1972023 : Blo 1971435 1972023 := bstep (se 1 (by rfl) ⟨1479017, by rfl⟩ : syracuseStep 1972023 = 2958035) B2958035
theorem B3327797 : Blo 1971435 3327797 := bbase (se 5 (by rfl) ⟨155990, by rfl⟩ : syracuseStep 3327797 = 311981) (by norm_num)
theorem B2218531 : Blo 1971435 2218531 := bstep (se 1 (by rfl) ⟨1663898, by rfl⟩ : syracuseStep 2218531 = 3327797) B3327797
theorem B2958041 : Blo 1971435 2958041 := bstep (se 2 (by rfl) ⟨1109265, by rfl⟩ : syracuseStep 2958041 = 2218531) B2218531
theorem B1972027 : Blo 1971435 1972027 := bstep (se 1 (by rfl) ⟨1479020, by rfl⟩ : syracuseStep 1972027 = 2958041) B2958041
theorem B5615669 : Blo 1971435 5615669 := bbase (se 5 (by rfl) ⟨263234, by rfl⟩ : syracuseStep 5615669 = 526469) (by norm_num)
theorem B14975117 : Blo 1971435 14975117 := bstep (se 3 (by rfl) ⟨2807834, by rfl⟩ : syracuseStep 14975117 = 5615669) B5615669
theorem B9983411 : Blo 1971435 9983411 := bstep (se 1 (by rfl) ⟨7487558, by rfl⟩ : syracuseStep 9983411 = 14975117) B14975117
theorem B6655607 : Blo 1971435 6655607 := bstep (se 1 (by rfl) ⟨4991705, by rfl⟩ : syracuseStep 6655607 = 9983411) B9983411
theorem B4437071 : Blo 1971435 4437071 := bstep (se 1 (by rfl) ⟨3327803, by rfl⟩ : syracuseStep 4437071 = 6655607) B6655607
theorem B2958047 : Blo 1971435 2958047 := bstep (se 1 (by rfl) ⟨2218535, by rfl⟩ : syracuseStep 2958047 = 4437071) B4437071
theorem B1972031 : Blo 1971435 1972031 := bstep (se 1 (by rfl) ⟨1479023, by rfl⟩ : syracuseStep 1972031 = 2958047) B2958047
theorem B2958053 : Blo 1971435 2958053 := bbase (se 4 (by rfl) ⟨277317, by rfl⟩ : syracuseStep 2958053 = 554635) (by norm_num)
theorem B1972035 : Blo 1971435 1972035 := bstep (se 1 (by rfl) ⟨1479026, by rfl⟩ : syracuseStep 1972035 = 2958053) B2958053
theorem B2105885 : Blo 1971435 2105885 := bbase (se 3 (by rfl) ⟨394853, by rfl⟩ : syracuseStep 2105885 = 789707) (by norm_num)
theorem B5615693 : Blo 1971435 5615693 := bstep (se 3 (by rfl) ⟨1052942, by rfl⟩ : syracuseStep 5615693 = 2105885) B2105885
theorem B3743795 : Blo 1971435 3743795 := bstep (se 1 (by rfl) ⟨2807846, by rfl⟩ : syracuseStep 3743795 = 5615693) B5615693
theorem B2495863 : Blo 1971435 2495863 := bstep (se 1 (by rfl) ⟨1871897, by rfl⟩ : syracuseStep 2495863 = 3743795) B3743795
theorem B3327817 : Blo 1971435 3327817 := bstep (se 2 (by rfl) ⟨1247931, by rfl⟩ : syracuseStep 3327817 = 2495863) B2495863
theorem B4437089 : Blo 1971435 4437089 := bstep (se 2 (by rfl) ⟨1663908, by rfl⟩ : syracuseStep 4437089 = 3327817) B3327817
theorem B2958059 : Blo 1971435 2958059 := bstep (se 1 (by rfl) ⟨2218544, by rfl⟩ : syracuseStep 2958059 = 4437089) B4437089
theorem B1972039 : Blo 1971435 1972039 := bstep (se 1 (by rfl) ⟨1479029, by rfl⟩ : syracuseStep 1972039 = 2958059) B2958059
theorem B2218549 : Blo 1971435 2218549 := bbase (se 5 (by rfl) ⟨103994, by rfl⟩ : syracuseStep 2218549 = 207989) (by norm_num)
theorem B2958065 : Blo 1971435 2958065 := bstep (se 2 (by rfl) ⟨1109274, by rfl⟩ : syracuseStep 2958065 = 2218549) B2218549
theorem B1972043 : Blo 1971435 1972043 := bstep (se 1 (by rfl) ⟨1479032, by rfl⟩ : syracuseStep 1972043 = 2958065) B2958065
theorem B2495873 : Blo 1971435 2495873 := bbase (se 2 (by rfl) ⟨935952, by rfl⟩ : syracuseStep 2495873 = 1871905) (by norm_num)
theorem B6655661 : Blo 1971435 6655661 := bstep (se 3 (by rfl) ⟨1247936, by rfl⟩ : syracuseStep 6655661 = 2495873) B2495873
theorem B4437107 : Blo 1971435 4437107 := bstep (se 1 (by rfl) ⟨3327830, by rfl⟩ : syracuseStep 4437107 = 6655661) B6655661
theorem B2958071 : Blo 1971435 2958071 := bstep (se 1 (by rfl) ⟨2218553, by rfl⟩ : syracuseStep 2958071 = 4437107) B4437107
theorem B1972047 : Blo 1971435 1972047 := bstep (se 1 (by rfl) ⟨1479035, by rfl⟩ : syracuseStep 1972047 = 2958071) B2958071
theorem B2958077 : Blo 1971435 2958077 := bbase (se 3 (by rfl) ⟨554639, by rfl⟩ : syracuseStep 2958077 = 1109279) (by norm_num)
theorem B1972051 : Blo 1971435 1972051 := bstep (se 1 (by rfl) ⟨1479038, by rfl⟩ : syracuseStep 1972051 = 2958077) B2958077
theorem B4437125 : Blo 1971435 4437125 := bbase (se 4 (by rfl) ⟨415980, by rfl⟩ : syracuseStep 4437125 = 831961) (by norm_num)
theorem B2958083 : Blo 1971435 2958083 := bstep (se 1 (by rfl) ⟨2218562, by rfl⟩ : syracuseStep 2958083 = 4437125) B4437125
theorem B1972055 : Blo 1971435 1972055 := bstep (se 1 (by rfl) ⟨1479041, by rfl⟩ : syracuseStep 1972055 = 2958083) B2958083
theorem B4211813 : Blo 1971435 4211813 := bbase (se 4 (by rfl) ⟨394857, by rfl⟩ : syracuseStep 4211813 = 789715) (by norm_num)
theorem B2807875 : Blo 1971435 2807875 := bstep (se 1 (by rfl) ⟨2105906, by rfl⟩ : syracuseStep 2807875 = 4211813) B4211813
theorem B3743833 : Blo 1971435 3743833 := bstep (se 2 (by rfl) ⟨1403937, by rfl⟩ : syracuseStep 3743833 = 2807875) B2807875
theorem B4991777 : Blo 1971435 4991777 := bstep (se 2 (by rfl) ⟨1871916, by rfl⟩ : syracuseStep 4991777 = 3743833) B3743833
theorem B3327851 : Blo 1971435 3327851 := bstep (se 1 (by rfl) ⟨2495888, by rfl⟩ : syracuseStep 3327851 = 4991777) B4991777
theorem B2218567 : Blo 1971435 2218567 := bstep (se 1 (by rfl) ⟨1663925, by rfl⟩ : syracuseStep 2218567 = 3327851) B3327851
theorem B2958089 : Blo 1971435 2958089 := bstep (se 2 (by rfl) ⟨1109283, by rfl⟩ : syracuseStep 2958089 = 2218567) B2218567
theorem B1972059 : Blo 1971435 1972059 := bstep (se 1 (by rfl) ⟨1479044, by rfl⟩ : syracuseStep 1972059 = 2958089) B2958089
theorem B9983573 : Blo 1971435 9983573 := bbase (se 8 (by rfl) ⟨58497, by rfl⟩ : syracuseStep 9983573 = 116995) (by norm_num)
theorem B6655715 : Blo 1971435 6655715 := bstep (se 1 (by rfl) ⟨4991786, by rfl⟩ : syracuseStep 6655715 = 9983573) B9983573
theorem B4437143 : Blo 1971435 4437143 := bstep (se 1 (by rfl) ⟨3327857, by rfl⟩ : syracuseStep 4437143 = 6655715) B6655715
theorem B2958095 : Blo 1971435 2958095 := bstep (se 1 (by rfl) ⟨2218571, by rfl⟩ : syracuseStep 2958095 = 4437143) B4437143
theorem B1972063 : Blo 1971435 1972063 := bstep (se 1 (by rfl) ⟨1479047, by rfl⟩ : syracuseStep 1972063 = 2958095) B2958095
theorem B2958101 : Blo 1971435 2958101 := bbase (se 6 (by rfl) ⟨69330, by rfl⟩ : syracuseStep 2958101 = 138661) (by norm_num)
theorem B1972067 : Blo 1971435 1972067 := bstep (se 1 (by rfl) ⟨1479050, by rfl⟩ : syracuseStep 1972067 = 2958101) B2958101
theorem B2701669 : Blo 1971435 2701669 := bbase (se 4 (by rfl) ⟨253281, by rfl⟩ : syracuseStep 2701669 = 506563) (by norm_num)
theorem B3602225 : Blo 1971435 3602225 := bstep (se 2 (by rfl) ⟨1350834, by rfl⟩ : syracuseStep 3602225 = 2701669) B2701669
theorem B2401483 : Blo 1971435 2401483 := bstep (se 1 (by rfl) ⟨1801112, by rfl⟩ : syracuseStep 2401483 = 3602225) B3602225
theorem B3201977 : Blo 1971435 3201977 := bstep (se 2 (by rfl) ⟨1200741, by rfl⟩ : syracuseStep 3201977 = 2401483) B2401483
theorem B8538605 : Blo 1971435 8538605 := bstep (se 3 (by rfl) ⟨1600988, by rfl⟩ : syracuseStep 8538605 = 3201977) B3201977
theorem B5692403 : Blo 1971435 5692403 := bstep (se 1 (by rfl) ⟨4269302, by rfl⟩ : syracuseStep 5692403 = 8538605) B8538605
theorem B3794935 : Blo 1971435 3794935 := bstep (se 1 (by rfl) ⟨2846201, by rfl⟩ : syracuseStep 3794935 = 5692403) B5692403
theorem B5059913 : Blo 1971435 5059913 := bstep (se 2 (by rfl) ⟨1897467, by rfl⟩ : syracuseStep 5059913 = 3794935) B3794935
theorem B53972405 : Blo 1971435 53972405 := bstep (se 5 (by rfl) ⟨2529956, by rfl⟩ : syracuseStep 53972405 = 5059913) B5059913
theorem B35981603 : Blo 1971435 35981603 := bstep (se 1 (by rfl) ⟨26986202, by rfl⟩ : syracuseStep 35981603 = 53972405) B53972405
theorem B23987735 : Blo 1971435 23987735 := bstep (se 1 (by rfl) ⟨17990801, by rfl⟩ : syracuseStep 23987735 = 35981603) B35981603
theorem B15991823 : Blo 1971435 15991823 := bstep (se 1 (by rfl) ⟨11993867, by rfl⟩ : syracuseStep 15991823 = 23987735) B23987735
theorem B10661215 : Blo 1971435 10661215 := bstep (se 1 (by rfl) ⟨7995911, by rfl⟩ : syracuseStep 10661215 = 15991823) B15991823
theorem B14214953 : Blo 1971435 14214953 := bstep (se 2 (by rfl) ⟨5330607, by rfl⟩ : syracuseStep 14214953 = 10661215) B10661215
theorem B37906541 : Blo 1971435 37906541 := bstep (se 3 (by rfl) ⟨7107476, by rfl⟩ : syracuseStep 37906541 = 14214953) B14214953
theorem B25271027 : Blo 1971435 25271027 := bstep (se 1 (by rfl) ⟨18953270, by rfl⟩ : syracuseStep 25271027 = 37906541) B37906541
theorem B16847351 : Blo 1971435 16847351 := bstep (se 1 (by rfl) ⟨12635513, by rfl⟩ : syracuseStep 16847351 = 25271027) B25271027
theorem B11231567 : Blo 1971435 11231567 := bstep (se 1 (by rfl) ⟨8423675, by rfl⟩ : syracuseStep 11231567 = 16847351) B16847351
theorem B7487711 : Blo 1971435 7487711 := bstep (se 1 (by rfl) ⟨5615783, by rfl⟩ : syracuseStep 7487711 = 11231567) B11231567
theorem B4991807 : Blo 1971435 4991807 := bstep (se 1 (by rfl) ⟨3743855, by rfl⟩ : syracuseStep 4991807 = 7487711) B7487711
theorem B3327871 : Blo 1971435 3327871 := bstep (se 1 (by rfl) ⟨2495903, by rfl⟩ : syracuseStep 3327871 = 4991807) B4991807
theorem B4437161 : Blo 1971435 4437161 := bstep (se 2 (by rfl) ⟨1663935, by rfl⟩ : syracuseStep 4437161 = 3327871) B3327871
theorem B2958107 : Blo 1971435 2958107 := bstep (se 1 (by rfl) ⟨2218580, by rfl⟩ : syracuseStep 2958107 = 4437161) B4437161
theorem B1972071 : Blo 1971435 1972071 := bstep (se 1 (by rfl) ⟨1479053, by rfl⟩ : syracuseStep 1972071 = 2958107) B2958107
theorem B2218585 : Blo 1971435 2218585 := bbase (se 2 (by rfl) ⟨831969, by rfl⟩ : syracuseStep 2218585 = 1663939) (by norm_num)
theorem B2958113 : Blo 1971435 2958113 := bstep (se 2 (by rfl) ⟨1109292, by rfl⟩ : syracuseStep 2958113 = 2218585) B2218585
theorem B1972075 : Blo 1971435 1972075 := bstep (se 1 (by rfl) ⟨1479056, by rfl⟩ : syracuseStep 1972075 = 2958113) B2958113
theorem B3997973 : Blo 1971435 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B2665315 : Blo 1971435 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B14215013 : Blo 1971435 14215013 := bstep (se 4 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 14215013 = 2665315) B2665315
theorem B9476675 : Blo 1971435 9476675 := bstep (se 1 (by rfl) ⟨7107506, by rfl⟩ : syracuseStep 9476675 = 14215013) B14215013
theorem B6317783 : Blo 1971435 6317783 := bstep (se 1 (by rfl) ⟨4738337, by rfl⟩ : syracuseStep 6317783 = 9476675) B9476675
theorem B4211855 : Blo 1971435 4211855 := bstep (se 1 (by rfl) ⟨3158891, by rfl⟩ : syracuseStep 4211855 = 6317783) B6317783
theorem B2807903 : Blo 1971435 2807903 := bstep (se 1 (by rfl) ⟨2105927, by rfl⟩ : syracuseStep 2807903 = 4211855) B4211855
theorem B7487741 : Blo 1971435 7487741 := bstep (se 3 (by rfl) ⟨1403951, by rfl⟩ : syracuseStep 7487741 = 2807903) B2807903
theorem B4991827 : Blo 1971435 4991827 := bstep (se 1 (by rfl) ⟨3743870, by rfl⟩ : syracuseStep 4991827 = 7487741) B7487741
theorem B6655769 : Blo 1971435 6655769 := bstep (se 2 (by rfl) ⟨2495913, by rfl⟩ : syracuseStep 6655769 = 4991827) B4991827
theorem B4437179 : Blo 1971435 4437179 := bstep (se 1 (by rfl) ⟨3327884, by rfl⟩ : syracuseStep 4437179 = 6655769) B6655769
theorem B2958119 : Blo 1971435 2958119 := bstep (se 1 (by rfl) ⟨2218589, by rfl⟩ : syracuseStep 2958119 = 4437179) B4437179
theorem B1972079 : Blo 1971435 1972079 := bstep (se 1 (by rfl) ⟨1479059, by rfl⟩ : syracuseStep 1972079 = 2958119) B2958119
theorem B2958125 : Blo 1971435 2958125 := bbase (se 3 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 2958125 = 1109297) (by norm_num)
theorem B1972083 : Blo 1971435 1972083 := bstep (se 1 (by rfl) ⟨1479062, by rfl⟩ : syracuseStep 1972083 = 2958125) B2958125
theorem B4437197 : Blo 1971435 4437197 := bbase (se 3 (by rfl) ⟨831974, by rfl⟩ : syracuseStep 4437197 = 1663949) (by norm_num)
theorem B2958131 : Blo 1971435 2958131 := bstep (se 1 (by rfl) ⟨2218598, by rfl⟩ : syracuseStep 2958131 = 4437197) B4437197
theorem B1972087 : Blo 1971435 1972087 := bstep (se 1 (by rfl) ⟨1479065, by rfl⟩ : syracuseStep 1972087 = 2958131) B2958131
theorem B2495929 : Blo 1971435 2495929 := bbase (se 2 (by rfl) ⟨935973, by rfl⟩ : syracuseStep 2495929 = 1871947) (by norm_num)
theorem B3327905 : Blo 1971435 3327905 := bstep (se 2 (by rfl) ⟨1247964, by rfl⟩ : syracuseStep 3327905 = 2495929) B2495929
theorem B2218603 : Blo 1971435 2218603 := bstep (se 1 (by rfl) ⟨1663952, by rfl⟩ : syracuseStep 2218603 = 3327905) B3327905
theorem B2958137 : Blo 1971435 2958137 := bstep (se 2 (by rfl) ⟨1109301, by rfl⟩ : syracuseStep 2958137 = 2218603) B2218603
theorem B1972091 : Blo 1971435 1972091 := bstep (se 1 (by rfl) ⟨1479068, by rfl⟩ : syracuseStep 1972091 = 2958137) B2958137
theorem B8538709 : Blo 1971435 8538709 := bbase (se 8 (by rfl) ⟨50031, by rfl⟩ : syracuseStep 8538709 = 100063) (by norm_num)
theorem B11384945 : Blo 1971435 11384945 := bstep (se 2 (by rfl) ⟨4269354, by rfl⟩ : syracuseStep 11384945 = 8538709) B8538709
theorem B7589963 : Blo 1971435 7589963 := bstep (se 1 (by rfl) ⟨5692472, by rfl⟩ : syracuseStep 7589963 = 11384945) B11384945
theorem B20239901 : Blo 1971435 20239901 := bstep (se 3 (by rfl) ⟨3794981, by rfl⟩ : syracuseStep 20239901 = 7589963) B7589963
theorem B13493267 : Blo 1971435 13493267 := bstep (se 1 (by rfl) ⟨10119950, by rfl⟩ : syracuseStep 13493267 = 20239901) B20239901
theorem B8995511 : Blo 1971435 8995511 := bstep (se 1 (by rfl) ⟨6746633, by rfl⟩ : syracuseStep 8995511 = 13493267) B13493267
theorem B5997007 : Blo 1971435 5997007 := bstep (se 1 (by rfl) ⟨4497755, by rfl⟩ : syracuseStep 5997007 = 8995511) B8995511
theorem B7996009 : Blo 1971435 7996009 := bstep (se 2 (by rfl) ⟨2998503, by rfl⟩ : syracuseStep 7996009 = 5997007) B5997007
theorem B10661345 : Blo 1971435 10661345 := bstep (se 2 (by rfl) ⟨3998004, by rfl⟩ : syracuseStep 10661345 = 7996009) B7996009
theorem B7107563 : Blo 1971435 7107563 := bstep (se 1 (by rfl) ⟨5330672, by rfl⟩ : syracuseStep 7107563 = 10661345) B10661345
theorem B4738375 : Blo 1971435 4738375 := bstep (se 1 (by rfl) ⟨3553781, by rfl⟩ : syracuseStep 4738375 = 7107563) B7107563
theorem B6317833 : Blo 1971435 6317833 := bstep (se 2 (by rfl) ⟨2369187, by rfl⟩ : syracuseStep 6317833 = 4738375) B4738375
theorem B8423777 : Blo 1971435 8423777 := bstep (se 2 (by rfl) ⟨3158916, by rfl⟩ : syracuseStep 8423777 = 6317833) B6317833
theorem B22463405 : Blo 1971435 22463405 := bstep (se 3 (by rfl) ⟨4211888, by rfl⟩ : syracuseStep 22463405 = 8423777) B8423777
theorem B14975603 : Blo 1971435 14975603 := bstep (se 1 (by rfl) ⟨11231702, by rfl⟩ : syracuseStep 14975603 = 22463405) B22463405
theorem B9983735 : Blo 1971435 9983735 := bstep (se 1 (by rfl) ⟨7487801, by rfl⟩ : syracuseStep 9983735 = 14975603) B14975603
theorem B6655823 : Blo 1971435 6655823 := bstep (se 1 (by rfl) ⟨4991867, by rfl⟩ : syracuseStep 6655823 = 9983735) B9983735
theorem B4437215 : Blo 1971435 4437215 := bstep (se 1 (by rfl) ⟨3327911, by rfl⟩ : syracuseStep 4437215 = 6655823) B6655823
theorem B2958143 : Blo 1971435 2958143 := bstep (se 1 (by rfl) ⟨2218607, by rfl⟩ : syracuseStep 2958143 = 4437215) B4437215
theorem B1972095 : Blo 1971435 1972095 := bstep (se 1 (by rfl) ⟨1479071, by rfl⟩ : syracuseStep 1972095 = 2958143) B2958143
theorem B2958149 : Blo 1971435 2958149 := bbase (se 4 (by rfl) ⟨277326, by rfl⟩ : syracuseStep 2958149 = 554653) (by norm_num)
theorem B1972099 : Blo 1971435 1972099 := bstep (se 1 (by rfl) ⟨1479074, by rfl⟩ : syracuseStep 1972099 = 2958149) B2958149
theorem B3327925 : Blo 1971435 3327925 := bbase (se 5 (by rfl) ⟨155996, by rfl⟩ : syracuseStep 3327925 = 311993) (by norm_num)
theorem B4437233 : Blo 1971435 4437233 := bstep (se 2 (by rfl) ⟨1663962, by rfl⟩ : syracuseStep 4437233 = 3327925) B3327925
theorem B2958155 : Blo 1971435 2958155 := bstep (se 1 (by rfl) ⟨2218616, by rfl⟩ : syracuseStep 2958155 = 4437233) B4437233
theorem B1972103 : Blo 1971435 1972103 := bstep (se 1 (by rfl) ⟨1479077, by rfl⟩ : syracuseStep 1972103 = 2958155) B2958155
theorem B2218621 : Blo 1971435 2218621 := bbase (se 3 (by rfl) ⟨415991, by rfl⟩ : syracuseStep 2218621 = 831983) (by norm_num)
theorem B2958161 : Blo 1971435 2958161 := bstep (se 2 (by rfl) ⟨1109310, by rfl⟩ : syracuseStep 2958161 = 2218621) B2218621
theorem B1972107 : Blo 1971435 1972107 := bstep (se 1 (by rfl) ⟨1479080, by rfl⟩ : syracuseStep 1972107 = 2958161) B2958161
theorem B6655877 : Blo 1971435 6655877 := bbase (se 4 (by rfl) ⟨623988, by rfl⟩ : syracuseStep 6655877 = 1247977) (by norm_num)
theorem B4437251 : Blo 1971435 4437251 := bstep (se 1 (by rfl) ⟨3327938, by rfl⟩ : syracuseStep 4437251 = 6655877) B6655877
theorem B2958167 : Blo 1971435 2958167 := bstep (se 1 (by rfl) ⟨2218625, by rfl⟩ : syracuseStep 2958167 = 4437251) B4437251
theorem B1972111 : Blo 1971435 1972111 := bstep (se 1 (by rfl) ⟨1479083, by rfl⟩ : syracuseStep 1972111 = 2958167) B2958167
theorem B2958173 : Blo 1971435 2958173 := bbase (se 3 (by rfl) ⟨554657, by rfl⟩ : syracuseStep 2958173 = 1109315) (by norm_num)
theorem B1972115 : Blo 1971435 1972115 := bstep (se 1 (by rfl) ⟨1479086, by rfl⟩ : syracuseStep 1972115 = 2958173) B2958173
theorem B4437269 : Blo 1971435 4437269 := bbase (se 6 (by rfl) ⟨103998, by rfl⟩ : syracuseStep 4437269 = 207997) (by norm_num)
theorem B2958179 : Blo 1971435 2958179 := bstep (se 1 (by rfl) ⟨2218634, by rfl⟩ : syracuseStep 2958179 = 4437269) B4437269
theorem B1972119 : Blo 1971435 1972119 := bstep (se 1 (by rfl) ⟨1479089, by rfl⟩ : syracuseStep 1972119 = 2958179) B2958179
theorem B7487909 : Blo 1971435 7487909 := bbase (se 4 (by rfl) ⟨701991, by rfl⟩ : syracuseStep 7487909 = 1403983) (by norm_num)
theorem B4991939 : Blo 1971435 4991939 := bstep (se 1 (by rfl) ⟨3743954, by rfl⟩ : syracuseStep 4991939 = 7487909) B7487909
theorem B3327959 : Blo 1971435 3327959 := bstep (se 1 (by rfl) ⟨2495969, by rfl⟩ : syracuseStep 3327959 = 4991939) B4991939
theorem B2218639 : Blo 1971435 2218639 := bstep (se 1 (by rfl) ⟨1663979, by rfl⟩ : syracuseStep 2218639 = 3327959) B3327959
theorem B2958185 : Blo 1971435 2958185 := bstep (se 2 (by rfl) ⟨1109319, by rfl⟩ : syracuseStep 2958185 = 2218639) B2218639
theorem B1972123 : Blo 1971435 1972123 := bstep (se 1 (by rfl) ⟨1479092, by rfl⟩ : syracuseStep 1972123 = 2958185) B2958185
theorem B4211957 : Blo 1971435 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B11231885 : Blo 1971435 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B7487923 : Blo 1971435 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B9983897 : Blo 1971435 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B6655931 : Blo 1971435 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B4437287 : Blo 1971435 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B2958191 : Blo 1971435 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B1972127 : Blo 1971435 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B2958197 : Blo 1971435 2958197 := bbase (se 5 (by rfl) ⟨138665, by rfl⟩ : syracuseStep 2958197 = 277331) (by norm_num)
theorem B1972131 : Blo 1971435 1972131 := bstep (se 1 (by rfl) ⟨1479098, by rfl⟩ : syracuseStep 1972131 = 2958197) B2958197
theorem B6746773 : Blo 1971435 6746773 := bbase (se 6 (by rfl) ⟨158127, by rfl⟩ : syracuseStep 6746773 = 316255) (by norm_num)
theorem B8995697 : Blo 1971435 8995697 := bstep (se 2 (by rfl) ⟨3373386, by rfl⟩ : syracuseStep 8995697 = 6746773) B6746773
theorem B5997131 : Blo 1971435 5997131 := bstep (se 1 (by rfl) ⟨4497848, by rfl⟩ : syracuseStep 5997131 = 8995697) B8995697
theorem B3998087 : Blo 1971435 3998087 := bstep (se 1 (by rfl) ⟨2998565, by rfl⟩ : syracuseStep 3998087 = 5997131) B5997131
theorem B2665391 : Blo 1971435 2665391 := bstep (se 1 (by rfl) ⟨1999043, by rfl⟩ : syracuseStep 2665391 = 3998087) B3998087
theorem B7107709 : Blo 1971435 7107709 := bstep (se 3 (by rfl) ⟨1332695, by rfl⟩ : syracuseStep 7107709 = 2665391) B2665391
theorem B9476945 : Blo 1971435 9476945 := bstep (se 2 (by rfl) ⟨3553854, by rfl⟩ : syracuseStep 9476945 = 7107709) B7107709
theorem B6317963 : Blo 1971435 6317963 := bstep (se 1 (by rfl) ⟨4738472, by rfl⟩ : syracuseStep 6317963 = 9476945) B9476945
theorem B4211975 : Blo 1971435 4211975 := bstep (se 1 (by rfl) ⟨3158981, by rfl⟩ : syracuseStep 4211975 = 6317963) B6317963
theorem B2807983 : Blo 1971435 2807983 := bstep (se 1 (by rfl) ⟨2105987, by rfl⟩ : syracuseStep 2807983 = 4211975) B4211975
theorem B3743977 : Blo 1971435 3743977 := bstep (se 2 (by rfl) ⟨1403991, by rfl⟩ : syracuseStep 3743977 = 2807983) B2807983
theorem B4991969 : Blo 1971435 4991969 := bstep (se 2 (by rfl) ⟨1871988, by rfl⟩ : syracuseStep 4991969 = 3743977) B3743977
theorem B3327979 : Blo 1971435 3327979 := bstep (se 1 (by rfl) ⟨2495984, by rfl⟩ : syracuseStep 3327979 = 4991969) B4991969
theorem B4437305 : Blo 1971435 4437305 := bstep (se 2 (by rfl) ⟨1663989, by rfl⟩ : syracuseStep 4437305 = 3327979) B3327979
theorem B2958203 : Blo 1971435 2958203 := bstep (se 1 (by rfl) ⟨2218652, by rfl⟩ : syracuseStep 2958203 = 4437305) B4437305
theorem B1972135 : Blo 1971435 1972135 := bstep (se 1 (by rfl) ⟨1479101, by rfl⟩ : syracuseStep 1972135 = 2958203) B2958203
theorem B2218657 : Blo 1971435 2218657 := bbase (se 2 (by rfl) ⟨831996, by rfl⟩ : syracuseStep 2218657 = 1663993) (by norm_num)
theorem B2958209 : Blo 1971435 2958209 := bstep (se 2 (by rfl) ⟨1109328, by rfl⟩ : syracuseStep 2958209 = 2218657) B2218657
theorem B1972139 : Blo 1971435 1972139 := bstep (se 1 (by rfl) ⟨1479104, by rfl⟩ : syracuseStep 1972139 = 2958209) B2958209
theorem B4991989 : Blo 1971435 4991989 := bbase (se 5 (by rfl) ⟨233999, by rfl⟩ : syracuseStep 4991989 = 467999) (by norm_num)
theorem B6655985 : Blo 1971435 6655985 := bstep (se 2 (by rfl) ⟨2495994, by rfl⟩ : syracuseStep 6655985 = 4991989) B4991989
theorem B4437323 : Blo 1971435 4437323 := bstep (se 1 (by rfl) ⟨3327992, by rfl⟩ : syracuseStep 4437323 = 6655985) B6655985
theorem B2958215 : Blo 1971435 2958215 := bstep (se 1 (by rfl) ⟨2218661, by rfl⟩ : syracuseStep 2958215 = 4437323) B4437323
theorem B1972143 : Blo 1971435 1972143 := bstep (se 1 (by rfl) ⟨1479107, by rfl⟩ : syracuseStep 1972143 = 2958215) B2958215
theorem B2958221 : Blo 1971435 2958221 := bbase (se 3 (by rfl) ⟨554666, by rfl⟩ : syracuseStep 2958221 = 1109333) (by norm_num)
theorem B1972147 : Blo 1971435 1972147 := bstep (se 1 (by rfl) ⟨1479110, by rfl⟩ : syracuseStep 1972147 = 2958221) B2958221
theorem B4437341 : Blo 1971435 4437341 := bbase (se 3 (by rfl) ⟨832001, by rfl⟩ : syracuseStep 4437341 = 1664003) (by norm_num)
theorem B2958227 : Blo 1971435 2958227 := bstep (se 1 (by rfl) ⟨2218670, by rfl⟩ : syracuseStep 2958227 = 4437341) B4437341
theorem B1972151 : Blo 1971435 1972151 := bstep (se 1 (by rfl) ⟨1479113, by rfl⟩ : syracuseStep 1972151 = 2958227) B2958227
theorem B3328013 : Blo 1971435 3328013 := bbase (se 3 (by rfl) ⟨624002, by rfl⟩ : syracuseStep 3328013 = 1248005) (by norm_num)
theorem B2218675 : Blo 1971435 2218675 := bstep (se 1 (by rfl) ⟨1664006, by rfl⟩ : syracuseStep 2218675 = 3328013) B3328013
theorem B2958233 : Blo 1971435 2958233 := bstep (se 2 (by rfl) ⟨1109337, by rfl⟩ : syracuseStep 2958233 = 2218675) B2218675
theorem B1972155 : Blo 1971435 1972155 := bstep (se 1 (by rfl) ⟨1479116, by rfl⟩ : syracuseStep 1972155 = 2958233) B2958233
theorem B5060141 : Blo 1971435 5060141 := bbase (se 3 (by rfl) ⟨948776, by rfl⟩ : syracuseStep 5060141 = 1897553) (by norm_num)
theorem B3373427 : Blo 1971435 3373427 := bstep (se 1 (by rfl) ⟨2530070, by rfl⟩ : syracuseStep 3373427 = 5060141) B5060141
theorem B8995805 : Blo 1971435 8995805 := bstep (se 3 (by rfl) ⟨1686713, by rfl⟩ : syracuseStep 8995805 = 3373427) B3373427
theorem B5997203 : Blo 1971435 5997203 := bstep (se 1 (by rfl) ⟨4497902, by rfl⟩ : syracuseStep 5997203 = 8995805) B8995805
theorem B3998135 : Blo 1971435 3998135 := bstep (se 1 (by rfl) ⟨2998601, by rfl⟩ : syracuseStep 3998135 = 5997203) B5997203
theorem B2665423 : Blo 1971435 2665423 := bstep (se 1 (by rfl) ⟨1999067, by rfl⟩ : syracuseStep 2665423 = 3998135) B3998135
theorem B3553897 : Blo 1971435 3553897 := bstep (se 2 (by rfl) ⟨1332711, by rfl⟩ : syracuseStep 3553897 = 2665423) B2665423
theorem B4738529 : Blo 1971435 4738529 := bstep (se 2 (by rfl) ⟨1776948, by rfl⟩ : syracuseStep 4738529 = 3553897) B3553897
theorem B3159019 : Blo 1971435 3159019 := bstep (se 1 (by rfl) ⟨2369264, by rfl⟩ : syracuseStep 3159019 = 4738529) B4738529
theorem B16848101 : Blo 1971435 16848101 := bstep (se 4 (by rfl) ⟨1579509, by rfl⟩ : syracuseStep 16848101 = 3159019) B3159019
theorem B11232067 : Blo 1971435 11232067 := bstep (se 1 (by rfl) ⟨8424050, by rfl⟩ : syracuseStep 11232067 = 16848101) B16848101
theorem B14976089 : Blo 1971435 14976089 := bstep (se 2 (by rfl) ⟨5616033, by rfl⟩ : syracuseStep 14976089 = 11232067) B11232067
theorem B9984059 : Blo 1971435 9984059 := bstep (se 1 (by rfl) ⟨7488044, by rfl⟩ : syracuseStep 9984059 = 14976089) B14976089
theorem B6656039 : Blo 1971435 6656039 := bstep (se 1 (by rfl) ⟨4992029, by rfl⟩ : syracuseStep 6656039 = 9984059) B9984059
theorem B4437359 : Blo 1971435 4437359 := bstep (se 1 (by rfl) ⟨3328019, by rfl⟩ : syracuseStep 4437359 = 6656039) B6656039
theorem B2958239 : Blo 1971435 2958239 := bstep (se 1 (by rfl) ⟨2218679, by rfl⟩ : syracuseStep 2958239 = 4437359) B4437359
theorem B1972159 : Blo 1971435 1972159 := bstep (se 1 (by rfl) ⟨1479119, by rfl⟩ : syracuseStep 1972159 = 2958239) B2958239
theorem B2958245 : Blo 1971435 2958245 := bbase (se 4 (by rfl) ⟨277335, by rfl⟩ : syracuseStep 2958245 = 554671) (by norm_num)
theorem B1972163 : Blo 1971435 1972163 := bstep (se 1 (by rfl) ⟨1479122, by rfl⟩ : syracuseStep 1972163 = 2958245) B2958245
theorem B2496025 : Blo 1971435 2496025 := bbase (se 2 (by rfl) ⟨936009, by rfl⟩ : syracuseStep 2496025 = 1872019) (by norm_num)
theorem B3328033 : Blo 1971435 3328033 := bstep (se 2 (by rfl) ⟨1248012, by rfl⟩ : syracuseStep 3328033 = 2496025) B2496025
theorem B4437377 : Blo 1971435 4437377 := bstep (se 2 (by rfl) ⟨1664016, by rfl⟩ : syracuseStep 4437377 = 3328033) B3328033
theorem B2958251 : Blo 1971435 2958251 := bstep (se 1 (by rfl) ⟨2218688, by rfl⟩ : syracuseStep 2958251 = 4437377) B4437377
theorem B1972167 : Blo 1971435 1972167 := bstep (se 1 (by rfl) ⟨1479125, by rfl⟩ : syracuseStep 1972167 = 2958251) B2958251
theorem B2218693 : Blo 1971435 2218693 := bbase (se 4 (by rfl) ⟨208002, by rfl⟩ : syracuseStep 2218693 = 416005) (by norm_num)
theorem B2958257 : Blo 1971435 2958257 := bstep (se 2 (by rfl) ⟨1109346, by rfl⟩ : syracuseStep 2958257 = 2218693) B2218693
theorem B1972171 : Blo 1971435 1972171 := bstep (se 1 (by rfl) ⟨1479128, by rfl⟩ : syracuseStep 1972171 = 2958257) B2958257
theorem B3744053 : Blo 1971435 3744053 := bbase (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) (by norm_num)
theorem B2496035 : Blo 1971435 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B6656093 : Blo 1971435 6656093 := bstep (se 3 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 6656093 = 2496035) B2496035
theorem B4437395 : Blo 1971435 4437395 := bstep (se 1 (by rfl) ⟨3328046, by rfl⟩ : syracuseStep 4437395 = 6656093) B6656093
theorem B2958263 : Blo 1971435 2958263 := bstep (se 1 (by rfl) ⟨2218697, by rfl⟩ : syracuseStep 2958263 = 4437395) B4437395
theorem B1972175 : Blo 1971435 1972175 := bstep (se 1 (by rfl) ⟨1479131, by rfl⟩ : syracuseStep 1972175 = 2958263) B2958263
theorem B2958269 : Blo 1971435 2958269 := bbase (se 3 (by rfl) ⟨554675, by rfl⟩ : syracuseStep 2958269 = 1109351) (by norm_num)
theorem B1972179 : Blo 1971435 1972179 := bstep (se 1 (by rfl) ⟨1479134, by rfl⟩ : syracuseStep 1972179 = 2958269) B2958269
theorem B4437413 : Blo 1971435 4437413 := bbase (se 4 (by rfl) ⟨416007, by rfl⟩ : syracuseStep 4437413 = 832015) (by norm_num)
theorem B2958275 : Blo 1971435 2958275 := bstep (se 1 (by rfl) ⟨2218706, by rfl⟩ : syracuseStep 2958275 = 4437413) B4437413
theorem B1972183 : Blo 1971435 1972183 := bstep (se 1 (by rfl) ⟨1479137, by rfl⟩ : syracuseStep 1972183 = 2958275) B2958275
theorem B4992101 : Blo 1971435 4992101 := bbase (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) (by norm_num)
theorem B3328067 : Blo 1971435 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B2218711 : Blo 1971435 2218711 := bstep (se 1 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 2218711 = 3328067) B3328067
theorem B2958281 : Blo 1971435 2958281 := bstep (se 2 (by rfl) ⟨1109355, by rfl⟩ : syracuseStep 2958281 = 2218711) B2218711
theorem B1972187 : Blo 1971435 1972187 := bstep (se 1 (by rfl) ⟨1479140, by rfl⟩ : syracuseStep 1972187 = 2958281) B2958281
theorem B38426069 : Blo 1971435 38426069 := bbase (se 7 (by rfl) ⟨450305, by rfl⟩ : syracuseStep 38426069 = 900611) (by norm_num)
theorem B25617379 : Blo 1971435 25617379 := bstep (se 1 (by rfl) ⟨19213034, by rfl⟩ : syracuseStep 25617379 = 38426069) B38426069
theorem B34156505 : Blo 1971435 34156505 := bstep (se 2 (by rfl) ⟨12808689, by rfl⟩ : syracuseStep 34156505 = 25617379) B25617379
theorem B22771003 : Blo 1971435 22771003 := bstep (se 1 (by rfl) ⟨17078252, by rfl⟩ : syracuseStep 22771003 = 34156505) B34156505
theorem B30361337 : Blo 1971435 30361337 := bstep (se 2 (by rfl) ⟨11385501, by rfl⟩ : syracuseStep 30361337 = 22771003) B22771003
theorem B20240891 : Blo 1971435 20240891 := bstep (se 1 (by rfl) ⟨15180668, by rfl⟩ : syracuseStep 20240891 = 30361337) B30361337
theorem B13493927 : Blo 1971435 13493927 := bstep (se 1 (by rfl) ⟨10120445, by rfl⟩ : syracuseStep 13493927 = 20240891) B20240891
theorem B8995951 : Blo 1971435 8995951 := bstep (se 1 (by rfl) ⟨6746963, by rfl⟩ : syracuseStep 8995951 = 13493927) B13493927
theorem B11994601 : Blo 1971435 11994601 := bstep (se 2 (by rfl) ⟨4497975, by rfl⟩ : syracuseStep 11994601 = 8995951) B8995951
theorem B15992801 : Blo 1971435 15992801 := bstep (se 2 (by rfl) ⟨5997300, by rfl⟩ : syracuseStep 15992801 = 11994601) B11994601
theorem B10661867 : Blo 1971435 10661867 := bstep (se 1 (by rfl) ⟨7996400, by rfl⟩ : syracuseStep 10661867 = 15992801) B15992801
theorem B7107911 : Blo 1971435 7107911 := bstep (se 1 (by rfl) ⟨5330933, by rfl⟩ : syracuseStep 7107911 = 10661867) B10661867
theorem B4738607 : Blo 1971435 4738607 := bstep (se 1 (by rfl) ⟨3553955, by rfl⟩ : syracuseStep 4738607 = 7107911) B7107911
theorem B3159071 : Blo 1971435 3159071 := bstep (se 1 (by rfl) ⟨2369303, by rfl⟩ : syracuseStep 3159071 = 4738607) B4738607
theorem B2106047 : Blo 1971435 2106047 := bstep (se 1 (by rfl) ⟨1579535, by rfl⟩ : syracuseStep 2106047 = 3159071) B3159071
theorem B5616125 : Blo 1971435 5616125 := bstep (se 3 (by rfl) ⟨1053023, by rfl⟩ : syracuseStep 5616125 = 2106047) B2106047
theorem B3744083 : Blo 1971435 3744083 := bstep (se 1 (by rfl) ⟨2808062, by rfl⟩ : syracuseStep 3744083 = 5616125) B5616125
theorem B9984221 : Blo 1971435 9984221 := bstep (se 3 (by rfl) ⟨1872041, by rfl⟩ : syracuseStep 9984221 = 3744083) B3744083
theorem B6656147 : Blo 1971435 6656147 := bstep (se 1 (by rfl) ⟨4992110, by rfl⟩ : syracuseStep 6656147 = 9984221) B9984221
theorem B4437431 : Blo 1971435 4437431 := bstep (se 1 (by rfl) ⟨3328073, by rfl⟩ : syracuseStep 4437431 = 6656147) B6656147
theorem B2958287 : Blo 1971435 2958287 := bstep (se 1 (by rfl) ⟨2218715, by rfl⟩ : syracuseStep 2958287 = 4437431) B4437431
theorem B1972191 : Blo 1971435 1972191 := bstep (se 1 (by rfl) ⟨1479143, by rfl⟩ : syracuseStep 1972191 = 2958287) B2958287
theorem B2958293 : Blo 1971435 2958293 := bbase (se 7 (by rfl) ⟨34667, by rfl⟩ : syracuseStep 2958293 = 69335) (by norm_num)
theorem B1972195 : Blo 1971435 1972195 := bstep (se 1 (by rfl) ⟨1479146, by rfl⟩ : syracuseStep 1972195 = 2958293) B2958293
theorem B7488197 : Blo 1971435 7488197 := bbase (se 4 (by rfl) ⟨702018, by rfl⟩ : syracuseStep 7488197 = 1404037) (by norm_num)
theorem B4992131 : Blo 1971435 4992131 := bstep (se 1 (by rfl) ⟨3744098, by rfl⟩ : syracuseStep 4992131 = 7488197) B7488197
theorem B3328087 : Blo 1971435 3328087 := bstep (se 1 (by rfl) ⟨2496065, by rfl⟩ : syracuseStep 3328087 = 4992131) B4992131
theorem B4437449 : Blo 1971435 4437449 := bstep (se 2 (by rfl) ⟨1664043, by rfl⟩ : syracuseStep 4437449 = 3328087) B3328087
theorem B2958299 : Blo 1971435 2958299 := bstep (se 1 (by rfl) ⟨2218724, by rfl⟩ : syracuseStep 2958299 = 4437449) B4437449
theorem B1972199 : Blo 1971435 1972199 := bstep (se 1 (by rfl) ⟨1479149, by rfl⟩ : syracuseStep 1972199 = 2958299) B2958299
theorem B2218729 : Blo 1971435 2218729 := bbase (se 2 (by rfl) ⟨832023, by rfl⟩ : syracuseStep 2218729 = 1664047) (by norm_num)
theorem B2958305 : Blo 1971435 2958305 := bstep (se 2 (by rfl) ⟨1109364, by rfl⟩ : syracuseStep 2958305 = 2218729) B2218729
theorem B1972203 : Blo 1971435 1972203 := bstep (se 1 (by rfl) ⟨1479152, by rfl⟩ : syracuseStep 1972203 = 2958305) B2958305
theorem B11232341 : Blo 1971435 11232341 := bbase (se 8 (by rfl) ⟨65814, by rfl⟩ : syracuseStep 11232341 = 131629) (by norm_num)
theorem B7488227 : Blo 1971435 7488227 := bstep (se 1 (by rfl) ⟨5616170, by rfl⟩ : syracuseStep 7488227 = 11232341) B11232341
theorem B4992151 : Blo 1971435 4992151 := bstep (se 1 (by rfl) ⟨3744113, by rfl⟩ : syracuseStep 4992151 = 7488227) B7488227
theorem B6656201 : Blo 1971435 6656201 := bstep (se 2 (by rfl) ⟨2496075, by rfl⟩ : syracuseStep 6656201 = 4992151) B4992151
theorem B4437467 : Blo 1971435 4437467 := bstep (se 1 (by rfl) ⟨3328100, by rfl⟩ : syracuseStep 4437467 = 6656201) B6656201
theorem B2958311 : Blo 1971435 2958311 := bstep (se 1 (by rfl) ⟨2218733, by rfl⟩ : syracuseStep 2958311 = 4437467) B4437467
theorem B1972207 : Blo 1971435 1972207 := bstep (se 1 (by rfl) ⟨1479155, by rfl⟩ : syracuseStep 1972207 = 2958311) B2958311
theorem B2958317 : Blo 1971435 2958317 := bbase (se 3 (by rfl) ⟨554684, by rfl⟩ : syracuseStep 2958317 = 1109369) (by norm_num)
theorem B1972211 : Blo 1971435 1972211 := bstep (se 1 (by rfl) ⟨1479158, by rfl⟩ : syracuseStep 1972211 = 2958317) B2958317
theorem B4437485 : Blo 1971435 4437485 := bbase (se 3 (by rfl) ⟨832028, by rfl⟩ : syracuseStep 4437485 = 1664057) (by norm_num)
theorem B2958323 : Blo 1971435 2958323 := bstep (se 1 (by rfl) ⟨2218742, by rfl⟩ : syracuseStep 2958323 = 4437485) B4437485
theorem B1972215 : Blo 1971435 1972215 := bstep (se 1 (by rfl) ⟨1479161, by rfl⟩ : syracuseStep 1972215 = 2958323) B2958323
theorem B1999129 : Blo 1971435 1999129 := bbase (se 2 (by rfl) ⟨749673, by rfl⟩ : syracuseStep 1999129 = 1499347) (by norm_num)
theorem B2665505 : Blo 1971435 2665505 := bstep (se 2 (by rfl) ⟨999564, by rfl⟩ : syracuseStep 2665505 = 1999129) B1999129
theorem B7108013 : Blo 1971435 7108013 := bstep (se 3 (by rfl) ⟨1332752, by rfl⟩ : syracuseStep 7108013 = 2665505) B2665505
theorem B4738675 : Blo 1971435 4738675 := bstep (se 1 (by rfl) ⟨3554006, by rfl⟩ : syracuseStep 4738675 = 7108013) B7108013
theorem B6318233 : Blo 1971435 6318233 := bstep (se 2 (by rfl) ⟨2369337, by rfl⟩ : syracuseStep 6318233 = 4738675) B4738675
theorem B4212155 : Blo 1971435 4212155 := bstep (se 1 (by rfl) ⟨3159116, by rfl⟩ : syracuseStep 4212155 = 6318233) B6318233
theorem B2808103 : Blo 1971435 2808103 := bstep (se 1 (by rfl) ⟨2106077, by rfl⟩ : syracuseStep 2808103 = 4212155) B4212155
theorem B3744137 : Blo 1971435 3744137 := bstep (se 2 (by rfl) ⟨1404051, by rfl⟩ : syracuseStep 3744137 = 2808103) B2808103
theorem B2496091 : Blo 1971435 2496091 := bstep (se 1 (by rfl) ⟨1872068, by rfl⟩ : syracuseStep 2496091 = 3744137) B3744137
theorem B3328121 : Blo 1971435 3328121 := bstep (se 2 (by rfl) ⟨1248045, by rfl⟩ : syracuseStep 3328121 = 2496091) B2496091
theorem B2218747 : Blo 1971435 2218747 := bstep (se 1 (by rfl) ⟨1664060, by rfl⟩ : syracuseStep 2218747 = 3328121) B3328121
theorem B2958329 : Blo 1971435 2958329 := bstep (se 2 (by rfl) ⟨1109373, by rfl⟩ : syracuseStep 2958329 = 2218747) B2218747
theorem B1972219 : Blo 1971435 1972219 := bstep (se 1 (by rfl) ⟨1479164, by rfl⟩ : syracuseStep 1972219 = 2958329) B2958329
theorem B7798997 : Blo 1971435 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B5199331 : Blo 1971435 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B6932441 : Blo 1971435 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B4621627 : Blo 1971435 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B6162169 : Blo 1971435 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B8216225 : Blo 1971435 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B5477483 : Blo 1971435 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B3651655 : Blo 1971435 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B4868873 : Blo 1971435 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B3245915 : Blo 1971435 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B2163943 : Blo 1971435 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B2885257 : Blo 1971435 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B3847009 : Blo 1971435 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B5129345 : Blo 1971435 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B3419563 : Blo 1971435 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B4559417 : Blo 1971435 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B3039611 : Blo 1971435 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B32422517 : Blo 1971435 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B21615011 : Blo 1971435 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B14410007 : Blo 1971435 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B9606671 : Blo 1971435 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B6404447 : Blo 1971435 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B17078525 : Blo 1971435 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B11385683 : Blo 1971435 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B7590455 : Blo 1971435 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B5060303 : Blo 1971435 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B3373535 : Blo 1971435 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B8996093 : Blo 1971435 8996093 := bstep (se 3 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 8996093 = 3373535) B3373535
theorem B5997395 : Blo 1971435 5997395 := bstep (se 1 (by rfl) ⟨4498046, by rfl⟩ : syracuseStep 5997395 = 8996093) B8996093
theorem B15993053 : Blo 1971435 15993053 := bstep (se 3 (by rfl) ⟨2998697, by rfl⟩ : syracuseStep 15993053 = 5997395) B5997395
theorem B10662035 : Blo 1971435 10662035 := bstep (se 1 (by rfl) ⟨7996526, by rfl⟩ : syracuseStep 10662035 = 15993053) B15993053
theorem B113728373 : Blo 1971435 113728373 := bstep (se 5 (by rfl) ⟨5331017, by rfl⟩ : syracuseStep 113728373 = 10662035) B10662035
theorem B75818915 : Blo 1971435 75818915 := bstep (se 1 (by rfl) ⟨56864186, by rfl⟩ : syracuseStep 75818915 = 113728373) B113728373
theorem B50545943 : Blo 1971435 50545943 := bstep (se 1 (by rfl) ⟨37909457, by rfl⟩ : syracuseStep 50545943 = 75818915) B75818915
theorem B33697295 : Blo 1971435 33697295 := bstep (se 1 (by rfl) ⟨25272971, by rfl⟩ : syracuseStep 33697295 = 50545943) B50545943
theorem B22464863 : Blo 1971435 22464863 := bstep (se 1 (by rfl) ⟨16848647, by rfl⟩ : syracuseStep 22464863 = 33697295) B33697295
theorem B14976575 : Blo 1971435 14976575 := bstep (se 1 (by rfl) ⟨11232431, by rfl⟩ : syracuseStep 14976575 = 22464863) B22464863
theorem B9984383 : Blo 1971435 9984383 := bstep (se 1 (by rfl) ⟨7488287, by rfl⟩ : syracuseStep 9984383 = 14976575) B14976575
theorem B6656255 : Blo 1971435 6656255 := bstep (se 1 (by rfl) ⟨4992191, by rfl⟩ : syracuseStep 6656255 = 9984383) B9984383
theorem B4437503 : Blo 1971435 4437503 := bstep (se 1 (by rfl) ⟨3328127, by rfl⟩ : syracuseStep 4437503 = 6656255) B6656255
theorem B2958335 : Blo 1971435 2958335 := bstep (se 1 (by rfl) ⟨2218751, by rfl⟩ : syracuseStep 2958335 = 4437503) B4437503
theorem B1972223 : Blo 1971435 1972223 := bstep (se 1 (by rfl) ⟨1479167, by rfl⟩ : syracuseStep 1972223 = 2958335) B2958335
theorem B2958341 : Blo 1971435 2958341 := bbase (se 4 (by rfl) ⟨277344, by rfl⟩ : syracuseStep 2958341 = 554689) (by norm_num)
theorem B1972227 : Blo 1971435 1972227 := bstep (se 1 (by rfl) ⟨1479170, by rfl⟩ : syracuseStep 1972227 = 2958341) B2958341
theorem B3328141 : Blo 1971435 3328141 := bbase (se 3 (by rfl) ⟨624026, by rfl⟩ : syracuseStep 3328141 = 1248053) (by norm_num)
theorem B4437521 : Blo 1971435 4437521 := bstep (se 2 (by rfl) ⟨1664070, by rfl⟩ : syracuseStep 4437521 = 3328141) B3328141
theorem B2958347 : Blo 1971435 2958347 := bstep (se 1 (by rfl) ⟨2218760, by rfl⟩ : syracuseStep 2958347 = 4437521) B4437521
theorem B1972231 : Blo 1971435 1972231 := bstep (se 1 (by rfl) ⟨1479173, by rfl⟩ : syracuseStep 1972231 = 2958347) B2958347
theorem B2218765 : Blo 1971435 2218765 := bbase (se 3 (by rfl) ⟨416018, by rfl⟩ : syracuseStep 2218765 = 832037) (by norm_num)
theorem B2958353 : Blo 1971435 2958353 := bstep (se 2 (by rfl) ⟨1109382, by rfl⟩ : syracuseStep 2958353 = 2218765) B2218765
theorem B1972235 : Blo 1971435 1972235 := bstep (se 1 (by rfl) ⟨1479176, by rfl⟩ : syracuseStep 1972235 = 2958353) B2958353
theorem B6656309 : Blo 1971435 6656309 := bbase (se 5 (by rfl) ⟨312014, by rfl⟩ : syracuseStep 6656309 = 624029) (by norm_num)
theorem B4437539 : Blo 1971435 4437539 := bstep (se 1 (by rfl) ⟨3328154, by rfl⟩ : syracuseStep 4437539 = 6656309) B6656309
theorem B2958359 : Blo 1971435 2958359 := bstep (se 1 (by rfl) ⟨2218769, by rfl⟩ : syracuseStep 2958359 = 4437539) B4437539
theorem B1972239 : Blo 1971435 1972239 := bstep (se 1 (by rfl) ⟨1479179, by rfl⟩ : syracuseStep 1972239 = 2958359) B2958359
theorem B2958365 : Blo 1971435 2958365 := bbase (se 3 (by rfl) ⟨554693, by rfl⟩ : syracuseStep 2958365 = 1109387) (by norm_num)
theorem B1972243 : Blo 1971435 1972243 := bstep (se 1 (by rfl) ⟨1479182, by rfl⟩ : syracuseStep 1972243 = 2958365) B2958365
theorem B4437557 : Blo 1971435 4437557 := bbase (se 5 (by rfl) ⟨208010, by rfl⟩ : syracuseStep 4437557 = 416021) (by norm_num)
theorem B2958371 : Blo 1971435 2958371 := bstep (se 1 (by rfl) ⟨2218778, by rfl⟩ : syracuseStep 2958371 = 4437557) B4437557
theorem B1972247 : Blo 1971435 1972247 := bstep (se 1 (by rfl) ⟨1479185, by rfl⟩ : syracuseStep 1972247 = 2958371) B2958371
theorem B5770597 : Blo 1971435 5770597 := bbase (se 4 (by rfl) ⟨540993, by rfl⟩ : syracuseStep 5770597 = 1081987) (by norm_num)
theorem B7694129 : Blo 1971435 7694129 := bstep (se 2 (by rfl) ⟨2885298, by rfl⟩ : syracuseStep 7694129 = 5770597) B5770597
theorem B5129419 : Blo 1971435 5129419 := bstep (se 1 (by rfl) ⟨3847064, by rfl⟩ : syracuseStep 5129419 = 7694129) B7694129
theorem B6839225 : Blo 1971435 6839225 := bstep (se 2 (by rfl) ⟨2564709, by rfl⟩ : syracuseStep 6839225 = 5129419) B5129419
theorem B4559483 : Blo 1971435 4559483 := bstep (se 1 (by rfl) ⟨3419612, by rfl⟩ : syracuseStep 4559483 = 6839225) B6839225
theorem B3039655 : Blo 1971435 3039655 := bstep (se 1 (by rfl) ⟨2279741, by rfl⟩ : syracuseStep 3039655 = 4559483) B4559483
theorem B4052873 : Blo 1971435 4052873 := bstep (se 2 (by rfl) ⟨1519827, by rfl⟩ : syracuseStep 4052873 = 3039655) B3039655
theorem B10807661 : Blo 1971435 10807661 := bstep (se 3 (by rfl) ⟨2026436, by rfl⟩ : syracuseStep 10807661 = 4052873) B4052873
theorem B7205107 : Blo 1971435 7205107 := bstep (se 1 (by rfl) ⟨5403830, by rfl⟩ : syracuseStep 7205107 = 10807661) B10807661
theorem B9606809 : Blo 1971435 9606809 := bstep (se 2 (by rfl) ⟨3602553, by rfl⟩ : syracuseStep 9606809 = 7205107) B7205107
theorem B25618157 : Blo 1971435 25618157 := bstep (se 3 (by rfl) ⟨4803404, by rfl⟩ : syracuseStep 25618157 = 9606809) B9606809
theorem B17078771 : Blo 1971435 17078771 := bstep (se 1 (by rfl) ⟨12809078, by rfl⟩ : syracuseStep 17078771 = 25618157) B25618157
theorem B11385847 : Blo 1971435 11385847 := bstep (se 1 (by rfl) ⟨8539385, by rfl⟩ : syracuseStep 11385847 = 17078771) B17078771
theorem B15181129 : Blo 1971435 15181129 := bstep (se 2 (by rfl) ⟨5692923, by rfl⟩ : syracuseStep 15181129 = 11385847) B11385847
theorem B20241505 : Blo 1971435 20241505 := bstep (se 2 (by rfl) ⟨7590564, by rfl⟩ : syracuseStep 20241505 = 15181129) B15181129
theorem B26988673 : Blo 1971435 26988673 := bstep (se 2 (by rfl) ⟨10120752, by rfl⟩ : syracuseStep 26988673 = 20241505) B20241505
theorem B35984897 : Blo 1971435 35984897 := bstep (se 2 (by rfl) ⟨13494336, by rfl⟩ : syracuseStep 35984897 = 26988673) B26988673
theorem B23989931 : Blo 1971435 23989931 := bstep (se 1 (by rfl) ⟨17992448, by rfl⟩ : syracuseStep 23989931 = 35984897) B35984897
theorem B15993287 : Blo 1971435 15993287 := bstep (se 1 (by rfl) ⟨11994965, by rfl⟩ : syracuseStep 15993287 = 23989931) B23989931
theorem B10662191 : Blo 1971435 10662191 := bstep (se 1 (by rfl) ⟨7996643, by rfl⟩ : syracuseStep 10662191 = 15993287) B15993287
theorem B7108127 : Blo 1971435 7108127 := bstep (se 1 (by rfl) ⟨5331095, by rfl⟩ : syracuseStep 7108127 = 10662191) B10662191
theorem B4738751 : Blo 1971435 4738751 := bstep (se 1 (by rfl) ⟨3554063, by rfl⟩ : syracuseStep 4738751 = 7108127) B7108127
theorem B3159167 : Blo 1971435 3159167 := bstep (se 1 (by rfl) ⟨2369375, by rfl⟩ : syracuseStep 3159167 = 4738751) B4738751
theorem B8424445 : Blo 1971435 8424445 := bstep (se 3 (by rfl) ⟨1579583, by rfl⟩ : syracuseStep 8424445 = 3159167) B3159167
theorem B11232593 : Blo 1971435 11232593 := bstep (se 2 (by rfl) ⟨4212222, by rfl⟩ : syracuseStep 11232593 = 8424445) B8424445
theorem B7488395 : Blo 1971435 7488395 := bstep (se 1 (by rfl) ⟨5616296, by rfl⟩ : syracuseStep 7488395 = 11232593) B11232593
theorem B4992263 : Blo 1971435 4992263 := bstep (se 1 (by rfl) ⟨3744197, by rfl⟩ : syracuseStep 4992263 = 7488395) B7488395
theorem B3328175 : Blo 1971435 3328175 := bstep (se 1 (by rfl) ⟨2496131, by rfl⟩ : syracuseStep 3328175 = 4992263) B4992263
theorem B2218783 : Blo 1971435 2218783 := bstep (se 1 (by rfl) ⟨1664087, by rfl⟩ : syracuseStep 2218783 = 3328175) B3328175
theorem B2958377 : Blo 1971435 2958377 := bstep (se 2 (by rfl) ⟨1109391, by rfl⟩ : syracuseStep 2958377 = 2218783) B2218783
theorem B1972251 : Blo 1971435 1972251 := bstep (se 1 (by rfl) ⟨1479188, by rfl⟩ : syracuseStep 1972251 = 2958377) B2958377
theorem B3159173 : Blo 1971435 3159173 := bbase (se 4 (by rfl) ⟨296172, by rfl⟩ : syracuseStep 3159173 = 592345) (by norm_num)
theorem B8424461 : Blo 1971435 8424461 := bstep (se 3 (by rfl) ⟨1579586, by rfl⟩ : syracuseStep 8424461 = 3159173) B3159173
theorem B5616307 : Blo 1971435 5616307 := bstep (se 1 (by rfl) ⟨4212230, by rfl⟩ : syracuseStep 5616307 = 8424461) B8424461
theorem B7488409 : Blo 1971435 7488409 := bstep (se 2 (by rfl) ⟨2808153, by rfl⟩ : syracuseStep 7488409 = 5616307) B5616307
theorem B9984545 : Blo 1971435 9984545 := bstep (se 2 (by rfl) ⟨3744204, by rfl⟩ : syracuseStep 9984545 = 7488409) B7488409
theorem B6656363 : Blo 1971435 6656363 := bstep (se 1 (by rfl) ⟨4992272, by rfl⟩ : syracuseStep 6656363 = 9984545) B9984545
theorem B4437575 : Blo 1971435 4437575 := bstep (se 1 (by rfl) ⟨3328181, by rfl⟩ : syracuseStep 4437575 = 6656363) B6656363
theorem B2958383 : Blo 1971435 2958383 := bstep (se 1 (by rfl) ⟨2218787, by rfl⟩ : syracuseStep 2958383 = 4437575) B4437575
theorem B1972255 : Blo 1971435 1972255 := bstep (se 1 (by rfl) ⟨1479191, by rfl⟩ : syracuseStep 1972255 = 2958383) B2958383
theorem B2958389 : Blo 1971435 2958389 := bbase (se 5 (by rfl) ⟨138674, by rfl⟩ : syracuseStep 2958389 = 277349) (by norm_num)
theorem B1972259 : Blo 1971435 1972259 := bstep (se 1 (by rfl) ⟨1479194, by rfl⟩ : syracuseStep 1972259 = 2958389) B2958389
theorem B4992293 : Blo 1971435 4992293 := bbase (se 4 (by rfl) ⟨468027, by rfl⟩ : syracuseStep 4992293 = 936055) (by norm_num)
theorem B3328195 : Blo 1971435 3328195 := bstep (se 1 (by rfl) ⟨2496146, by rfl⟩ : syracuseStep 3328195 = 4992293) B4992293
theorem B4437593 : Blo 1971435 4437593 := bstep (se 2 (by rfl) ⟨1664097, by rfl⟩ : syracuseStep 4437593 = 3328195) B3328195
theorem B2958395 : Blo 1971435 2958395 := bstep (se 1 (by rfl) ⟨2218796, by rfl⟩ : syracuseStep 2958395 = 4437593) B4437593
theorem B1972263 : Blo 1971435 1972263 := bstep (se 1 (by rfl) ⟨1479197, by rfl⟩ : syracuseStep 1972263 = 2958395) B2958395
theorem B2218801 : Blo 1971435 2218801 := bbase (se 2 (by rfl) ⟨832050, by rfl⟩ : syracuseStep 2218801 = 1664101) (by norm_num)
theorem B2958401 : Blo 1971435 2958401 := bstep (se 2 (by rfl) ⟨1109400, by rfl⟩ : syracuseStep 2958401 = 2218801) B2218801
theorem B1972267 : Blo 1971435 1972267 := bstep (se 1 (by rfl) ⟨1479200, by rfl⟩ : syracuseStep 1972267 = 2958401) B2958401
theorem B22771925 : Blo 1971435 22771925 := bbase (se 7 (by rfl) ⟨266858, by rfl⟩ : syracuseStep 22771925 = 533717) (by norm_num)
theorem B15181283 : Blo 1971435 15181283 := bstep (se 1 (by rfl) ⟨11385962, by rfl⟩ : syracuseStep 15181283 = 22771925) B22771925
theorem B40483421 : Blo 1971435 40483421 := bstep (se 3 (by rfl) ⟨7590641, by rfl⟩ : syracuseStep 40483421 = 15181283) B15181283
theorem B26988947 : Blo 1971435 26988947 := bstep (se 1 (by rfl) ⟨20241710, by rfl⟩ : syracuseStep 26988947 = 40483421) B40483421
theorem B17992631 : Blo 1971435 17992631 := bstep (se 1 (by rfl) ⟨13494473, by rfl⟩ : syracuseStep 17992631 = 26988947) B26988947
theorem B11995087 : Blo 1971435 11995087 := bstep (se 1 (by rfl) ⟨8996315, by rfl⟩ : syracuseStep 11995087 = 17992631) B17992631
theorem B15993449 : Blo 1971435 15993449 := bstep (se 2 (by rfl) ⟨5997543, by rfl⟩ : syracuseStep 15993449 = 11995087) B11995087
theorem B10662299 : Blo 1971435 10662299 := bstep (se 1 (by rfl) ⟨7996724, by rfl⟩ : syracuseStep 10662299 = 15993449) B15993449
theorem B7108199 : Blo 1971435 7108199 := bstep (se 1 (by rfl) ⟨5331149, by rfl⟩ : syracuseStep 7108199 = 10662299) B10662299
theorem B4738799 : Blo 1971435 4738799 := bstep (se 1 (by rfl) ⟨3554099, by rfl⟩ : syracuseStep 4738799 = 7108199) B7108199
theorem B3159199 : Blo 1971435 3159199 := bstep (se 1 (by rfl) ⟨2369399, by rfl⟩ : syracuseStep 3159199 = 4738799) B4738799
theorem B4212265 : Blo 1971435 4212265 := bstep (se 2 (by rfl) ⟨1579599, by rfl⟩ : syracuseStep 4212265 = 3159199) B3159199
theorem B5616353 : Blo 1971435 5616353 := bstep (se 2 (by rfl) ⟨2106132, by rfl⟩ : syracuseStep 5616353 = 4212265) B4212265
theorem B3744235 : Blo 1971435 3744235 := bstep (se 1 (by rfl) ⟨2808176, by rfl⟩ : syracuseStep 3744235 = 5616353) B5616353
theorem B4992313 : Blo 1971435 4992313 := bstep (se 2 (by rfl) ⟨1872117, by rfl⟩ : syracuseStep 4992313 = 3744235) B3744235
theorem B6656417 : Blo 1971435 6656417 := bstep (se 2 (by rfl) ⟨2496156, by rfl⟩ : syracuseStep 6656417 = 4992313) B4992313
theorem B4437611 : Blo 1971435 4437611 := bstep (se 1 (by rfl) ⟨3328208, by rfl⟩ : syracuseStep 4437611 = 6656417) B6656417
theorem B2958407 : Blo 1971435 2958407 := bstep (se 1 (by rfl) ⟨2218805, by rfl⟩ : syracuseStep 2958407 = 4437611) B4437611
theorem B1972271 : Blo 1971435 1972271 := bstep (se 1 (by rfl) ⟨1479203, by rfl⟩ : syracuseStep 1972271 = 2958407) B2958407
theorem B2958413 : Blo 1971435 2958413 := bbase (se 3 (by rfl) ⟨554702, by rfl⟩ : syracuseStep 2958413 = 1109405) (by norm_num)
theorem B1972275 : Blo 1971435 1972275 := bstep (se 1 (by rfl) ⟨1479206, by rfl⟩ : syracuseStep 1972275 = 2958413) B2958413
theorem B4437629 : Blo 1971435 4437629 := bbase (se 3 (by rfl) ⟨832055, by rfl⟩ : syracuseStep 4437629 = 1664111) (by norm_num)
theorem B2958419 : Blo 1971435 2958419 := bstep (se 1 (by rfl) ⟨2218814, by rfl⟩ : syracuseStep 2958419 = 4437629) B4437629
theorem B1972279 : Blo 1971435 1972279 := bstep (se 1 (by rfl) ⟨1479209, by rfl⟩ : syracuseStep 1972279 = 2958419) B2958419
theorem B3328229 : Blo 1971435 3328229 := bbase (se 4 (by rfl) ⟨312021, by rfl⟩ : syracuseStep 3328229 = 624043) (by norm_num)
theorem B2218819 : Blo 1971435 2218819 := bstep (se 1 (by rfl) ⟨1664114, by rfl⟩ : syracuseStep 2218819 = 3328229) B3328229
theorem B2958425 : Blo 1971435 2958425 := bstep (se 2 (by rfl) ⟨1109409, by rfl⟩ : syracuseStep 2958425 = 2218819) B2218819
theorem B1972283 : Blo 1971435 1972283 := bstep (se 1 (by rfl) ⟨1479212, by rfl⟩ : syracuseStep 1972283 = 2958425) B2958425
theorem B4738837 : Blo 1971435 4738837 := bbase (se 6 (by rfl) ⟨111066, by rfl⟩ : syracuseStep 4738837 = 222133) (by norm_num)
theorem B6318449 : Blo 1971435 6318449 := bstep (se 2 (by rfl) ⟨2369418, by rfl⟩ : syracuseStep 6318449 = 4738837) B4738837
theorem B4212299 : Blo 1971435 4212299 := bstep (se 1 (by rfl) ⟨3159224, by rfl⟩ : syracuseStep 4212299 = 6318449) B6318449
theorem B2808199 : Blo 1971435 2808199 := bstep (se 1 (by rfl) ⟨2106149, by rfl⟩ : syracuseStep 2808199 = 4212299) B4212299
theorem B14977061 : Blo 1971435 14977061 := bstep (se 4 (by rfl) ⟨1404099, by rfl⟩ : syracuseStep 14977061 = 2808199) B2808199
theorem B9984707 : Blo 1971435 9984707 := bstep (se 1 (by rfl) ⟨7488530, by rfl⟩ : syracuseStep 9984707 = 14977061) B14977061
theorem B6656471 : Blo 1971435 6656471 := bstep (se 1 (by rfl) ⟨4992353, by rfl⟩ : syracuseStep 6656471 = 9984707) B9984707
theorem B4437647 : Blo 1971435 4437647 := bstep (se 1 (by rfl) ⟨3328235, by rfl⟩ : syracuseStep 4437647 = 6656471) B6656471
theorem B2958431 : Blo 1971435 2958431 := bstep (se 1 (by rfl) ⟨2218823, by rfl⟩ : syracuseStep 2958431 = 4437647) B4437647
theorem B1972287 : Blo 1971435 1972287 := bstep (se 1 (by rfl) ⟨1479215, by rfl⟩ : syracuseStep 1972287 = 2958431) B2958431
theorem B2958437 : Blo 1971435 2958437 := bbase (se 4 (by rfl) ⟨277353, by rfl⟩ : syracuseStep 2958437 = 554707) (by norm_num)
theorem B1972291 : Blo 1971435 1972291 := bstep (se 1 (by rfl) ⟨1479218, by rfl⟩ : syracuseStep 1972291 = 2958437) B2958437
theorem B4212317 : Blo 1971435 4212317 := bbase (se 3 (by rfl) ⟨789809, by rfl⟩ : syracuseStep 4212317 = 1579619) (by norm_num)
theorem B2808211 : Blo 1971435 2808211 := bstep (se 1 (by rfl) ⟨2106158, by rfl⟩ : syracuseStep 2808211 = 4212317) B4212317
theorem B3744281 : Blo 1971435 3744281 := bstep (se 2 (by rfl) ⟨1404105, by rfl⟩ : syracuseStep 3744281 = 2808211) B2808211
theorem B2496187 : Blo 1971435 2496187 := bstep (se 1 (by rfl) ⟨1872140, by rfl⟩ : syracuseStep 2496187 = 3744281) B3744281
theorem B3328249 : Blo 1971435 3328249 := bstep (se 2 (by rfl) ⟨1248093, by rfl⟩ : syracuseStep 3328249 = 2496187) B2496187
theorem B4437665 : Blo 1971435 4437665 := bstep (se 2 (by rfl) ⟨1664124, by rfl⟩ : syracuseStep 4437665 = 3328249) B3328249
theorem B2958443 : Blo 1971435 2958443 := bstep (se 1 (by rfl) ⟨2218832, by rfl⟩ : syracuseStep 2958443 = 4437665) B4437665
theorem B1972295 : Blo 1971435 1972295 := bstep (se 1 (by rfl) ⟨1479221, by rfl⟩ : syracuseStep 1972295 = 2958443) B2958443
theorem B2218837 : Blo 1971435 2218837 := bbase (se 9 (by rfl) ⟨6500, by rfl⟩ : syracuseStep 2218837 = 13001) (by norm_num)
theorem B2958449 : Blo 1971435 2958449 := bstep (se 2 (by rfl) ⟨1109418, by rfl⟩ : syracuseStep 2958449 = 2218837) B2218837
theorem B1972299 : Blo 1971435 1972299 := bstep (se 1 (by rfl) ⟨1479224, by rfl⟩ : syracuseStep 1972299 = 2958449) B2958449
theorem B2496197 : Blo 1971435 2496197 := bbase (se 4 (by rfl) ⟨234018, by rfl⟩ : syracuseStep 2496197 = 468037) (by norm_num)
theorem B6656525 : Blo 1971435 6656525 := bstep (se 3 (by rfl) ⟨1248098, by rfl⟩ : syracuseStep 6656525 = 2496197) B2496197
theorem B4437683 : Blo 1971435 4437683 := bstep (se 1 (by rfl) ⟨3328262, by rfl⟩ : syracuseStep 4437683 = 6656525) B6656525
theorem B2958455 : Blo 1971435 2958455 := bstep (se 1 (by rfl) ⟨2218841, by rfl⟩ : syracuseStep 2958455 = 4437683) B4437683
theorem B1972303 : Blo 1971435 1972303 := bstep (se 1 (by rfl) ⟨1479227, by rfl⟩ : syracuseStep 1972303 = 2958455) B2958455
theorem B2958461 : Blo 1971435 2958461 := bbase (se 3 (by rfl) ⟨554711, by rfl⟩ : syracuseStep 2958461 = 1109423) (by norm_num)
theorem B1972307 : Blo 1971435 1972307 := bstep (se 1 (by rfl) ⟨1479230, by rfl⟩ : syracuseStep 1972307 = 2958461) B2958461
theorem B4437701 : Blo 1971435 4437701 := bbase (se 4 (by rfl) ⟨416034, by rfl⟩ : syracuseStep 4437701 = 832069) (by norm_num)
theorem B2958467 : Blo 1971435 2958467 := bstep (se 1 (by rfl) ⟨2218850, by rfl⟩ : syracuseStep 2958467 = 4437701) B4437701
theorem B1972311 : Blo 1971435 1972311 := bstep (se 1 (by rfl) ⟨1479233, by rfl⟩ : syracuseStep 1972311 = 2958467) B2958467
theorem B28433429 : Blo 1971435 28433429 := bbase (se 6 (by rfl) ⟨666408, by rfl⟩ : syracuseStep 28433429 = 1332817) (by norm_num)
theorem B18955619 : Blo 1971435 18955619 := bstep (se 1 (by rfl) ⟨14216714, by rfl⟩ : syracuseStep 18955619 = 28433429) B28433429
theorem B12637079 : Blo 1971435 12637079 := bstep (se 1 (by rfl) ⟨9477809, by rfl⟩ : syracuseStep 12637079 = 18955619) B18955619
theorem B8424719 : Blo 1971435 8424719 := bstep (se 1 (by rfl) ⟨6318539, by rfl⟩ : syracuseStep 8424719 = 12637079) B12637079
theorem B5616479 : Blo 1971435 5616479 := bstep (se 1 (by rfl) ⟨4212359, by rfl⟩ : syracuseStep 5616479 = 8424719) B8424719
theorem B3744319 : Blo 1971435 3744319 := bstep (se 1 (by rfl) ⟨2808239, by rfl⟩ : syracuseStep 3744319 = 5616479) B5616479
theorem B4992425 : Blo 1971435 4992425 := bstep (se 2 (by rfl) ⟨1872159, by rfl⟩ : syracuseStep 4992425 = 3744319) B3744319
theorem B3328283 : Blo 1971435 3328283 := bstep (se 1 (by rfl) ⟨2496212, by rfl⟩ : syracuseStep 3328283 = 4992425) B4992425
theorem B2218855 : Blo 1971435 2218855 := bstep (se 1 (by rfl) ⟨1664141, by rfl⟩ : syracuseStep 2218855 = 3328283) B3328283
theorem B2958473 : Blo 1971435 2958473 := bstep (se 2 (by rfl) ⟨1109427, by rfl⟩ : syracuseStep 2958473 = 2218855) B2218855
theorem B1972315 : Blo 1971435 1972315 := bstep (se 1 (by rfl) ⟨1479236, by rfl⟩ : syracuseStep 1972315 = 2958473) B2958473
theorem B9984869 : Blo 1971435 9984869 := bbase (se 4 (by rfl) ⟨936081, by rfl⟩ : syracuseStep 9984869 = 1872163) (by norm_num)
theorem B6656579 : Blo 1971435 6656579 := bstep (se 1 (by rfl) ⟨4992434, by rfl⟩ : syracuseStep 6656579 = 9984869) B9984869
theorem B4437719 : Blo 1971435 4437719 := bstep (se 1 (by rfl) ⟨3328289, by rfl⟩ : syracuseStep 4437719 = 6656579) B6656579
theorem B2958479 : Blo 1971435 2958479 := bstep (se 1 (by rfl) ⟨2218859, by rfl⟩ : syracuseStep 2958479 = 4437719) B4437719
theorem B1972319 : Blo 1971435 1972319 := bstep (se 1 (by rfl) ⟨1479239, by rfl⟩ : syracuseStep 1972319 = 2958479) B2958479
theorem B2958485 : Blo 1971435 2958485 := bbase (se 6 (by rfl) ⟨69339, by rfl⟩ : syracuseStep 2958485 = 138679) (by norm_num)
theorem B1972323 : Blo 1971435 1972323 := bstep (se 1 (by rfl) ⟨1479242, by rfl⟩ : syracuseStep 1972323 = 2958485) B2958485
theorem B4738933 : Blo 1971435 4738933 := bbase (se 5 (by rfl) ⟨222137, by rfl⟩ : syracuseStep 4738933 = 444275) (by norm_num)
theorem B6318577 : Blo 1971435 6318577 := bstep (se 2 (by rfl) ⟨2369466, by rfl⟩ : syracuseStep 6318577 = 4738933) B4738933
theorem B8424769 : Blo 1971435 8424769 := bstep (se 2 (by rfl) ⟨3159288, by rfl⟩ : syracuseStep 8424769 = 6318577) B6318577
theorem B11233025 : Blo 1971435 11233025 := bstep (se 2 (by rfl) ⟨4212384, by rfl⟩ : syracuseStep 11233025 = 8424769) B8424769
theorem B7488683 : Blo 1971435 7488683 := bstep (se 1 (by rfl) ⟨5616512, by rfl⟩ : syracuseStep 7488683 = 11233025) B11233025
theorem B4992455 : Blo 1971435 4992455 := bstep (se 1 (by rfl) ⟨3744341, by rfl⟩ : syracuseStep 4992455 = 7488683) B7488683
theorem B3328303 : Blo 1971435 3328303 := bstep (se 1 (by rfl) ⟨2496227, by rfl⟩ : syracuseStep 3328303 = 4992455) B4992455
theorem B4437737 : Blo 1971435 4437737 := bstep (se 2 (by rfl) ⟨1664151, by rfl⟩ : syracuseStep 4437737 = 3328303) B3328303
theorem B2958491 : Blo 1971435 2958491 := bstep (se 1 (by rfl) ⟨2218868, by rfl⟩ : syracuseStep 2958491 = 4437737) B4437737
theorem B1972327 : Blo 1971435 1972327 := bstep (se 1 (by rfl) ⟨1479245, by rfl⟩ : syracuseStep 1972327 = 2958491) B2958491
theorem B2218873 : Blo 1971435 2218873 := bbase (se 2 (by rfl) ⟨832077, by rfl⟩ : syracuseStep 2218873 = 1664155) (by norm_num)
theorem B2958497 : Blo 1971435 2958497 := bstep (se 2 (by rfl) ⟨1109436, by rfl⟩ : syracuseStep 2958497 = 2218873) B2218873
theorem B1972331 : Blo 1971435 1972331 := bstep (se 1 (by rfl) ⟨1479248, by rfl⟩ : syracuseStep 1972331 = 2958497) B2958497
theorem B12637205 : Blo 1971435 12637205 := bbase (se 6 (by rfl) ⟨296184, by rfl⟩ : syracuseStep 12637205 = 592369) (by norm_num)
theorem B8424803 : Blo 1971435 8424803 := bstep (se 1 (by rfl) ⟨6318602, by rfl⟩ : syracuseStep 8424803 = 12637205) B12637205
theorem B5616535 : Blo 1971435 5616535 := bstep (se 1 (by rfl) ⟨4212401, by rfl⟩ : syracuseStep 5616535 = 8424803) B8424803
theorem B7488713 : Blo 1971435 7488713 := bstep (se 2 (by rfl) ⟨2808267, by rfl⟩ : syracuseStep 7488713 = 5616535) B5616535
theorem B4992475 : Blo 1971435 4992475 := bstep (se 1 (by rfl) ⟨3744356, by rfl⟩ : syracuseStep 4992475 = 7488713) B7488713
theorem B6656633 : Blo 1971435 6656633 := bstep (se 2 (by rfl) ⟨2496237, by rfl⟩ : syracuseStep 6656633 = 4992475) B4992475
theorem B4437755 : Blo 1971435 4437755 := bstep (se 1 (by rfl) ⟨3328316, by rfl⟩ : syracuseStep 4437755 = 6656633) B6656633
theorem B2958503 : Blo 1971435 2958503 := bstep (se 1 (by rfl) ⟨2218877, by rfl⟩ : syracuseStep 2958503 = 4437755) B4437755
theorem B1972335 : Blo 1971435 1972335 := bstep (se 1 (by rfl) ⟨1479251, by rfl⟩ : syracuseStep 1972335 = 2958503) B2958503
theorem B2958509 : Blo 1971435 2958509 := bbase (se 3 (by rfl) ⟨554720, by rfl⟩ : syracuseStep 2958509 = 1109441) (by norm_num)
theorem B1972339 : Blo 1971435 1972339 := bstep (se 1 (by rfl) ⟨1479254, by rfl⟩ : syracuseStep 1972339 = 2958509) B2958509
theorem B4437773 : Blo 1971435 4437773 := bbase (se 3 (by rfl) ⟨832082, by rfl⟩ : syracuseStep 4437773 = 1664165) (by norm_num)
theorem B2958515 : Blo 1971435 2958515 := bstep (se 1 (by rfl) ⟨2218886, by rfl⟩ : syracuseStep 2958515 = 4437773) B4437773
theorem B1972343 : Blo 1971435 1972343 := bstep (se 1 (by rfl) ⟨1479257, by rfl⟩ : syracuseStep 1972343 = 2958515) B2958515
theorem B2496253 : Blo 1971435 2496253 := bbase (se 3 (by rfl) ⟨468047, by rfl⟩ : syracuseStep 2496253 = 936095) (by norm_num)
theorem B3328337 : Blo 1971435 3328337 := bstep (se 2 (by rfl) ⟨1248126, by rfl⟩ : syracuseStep 3328337 = 2496253) B2496253
theorem B2218891 : Blo 1971435 2218891 := bstep (se 1 (by rfl) ⟨1664168, by rfl⟩ : syracuseStep 2218891 = 3328337) B3328337
theorem B2958521 : Blo 1971435 2958521 := bstep (se 2 (by rfl) ⟨1109445, by rfl⟩ : syracuseStep 2958521 = 2218891) B2218891
theorem B1972347 : Blo 1971435 1972347 := bstep (se 1 (by rfl) ⟨1479260, by rfl⟩ : syracuseStep 1972347 = 2958521) B2958521
theorem B5331365 : Blo 1971435 5331365 := bbase (se 4 (by rfl) ⟨499815, by rfl⟩ : syracuseStep 5331365 = 999631) (by norm_num)
theorem B3554243 : Blo 1971435 3554243 := bstep (se 1 (by rfl) ⟨2665682, by rfl⟩ : syracuseStep 3554243 = 5331365) B5331365
theorem B2369495 : Blo 1971435 2369495 := bstep (se 1 (by rfl) ⟨1777121, by rfl⟩ : syracuseStep 2369495 = 3554243) B3554243
theorem B6318653 : Blo 1971435 6318653 := bstep (se 3 (by rfl) ⟨1184747, by rfl⟩ : syracuseStep 6318653 = 2369495) B2369495
theorem B16849741 : Blo 1971435 16849741 := bstep (se 3 (by rfl) ⟨3159326, by rfl⟩ : syracuseStep 16849741 = 6318653) B6318653
theorem B22466321 : Blo 1971435 22466321 := bstep (se 2 (by rfl) ⟨8424870, by rfl⟩ : syracuseStep 22466321 = 16849741) B16849741
theorem B14977547 : Blo 1971435 14977547 := bstep (se 1 (by rfl) ⟨11233160, by rfl⟩ : syracuseStep 14977547 = 22466321) B22466321
theorem B9985031 : Blo 1971435 9985031 := bstep (se 1 (by rfl) ⟨7488773, by rfl⟩ : syracuseStep 9985031 = 14977547) B14977547
theorem B6656687 : Blo 1971435 6656687 := bstep (se 1 (by rfl) ⟨4992515, by rfl⟩ : syracuseStep 6656687 = 9985031) B9985031
theorem B4437791 : Blo 1971435 4437791 := bstep (se 1 (by rfl) ⟨3328343, by rfl⟩ : syracuseStep 4437791 = 6656687) B6656687
theorem B2958527 : Blo 1971435 2958527 := bstep (se 1 (by rfl) ⟨2218895, by rfl⟩ : syracuseStep 2958527 = 4437791) B4437791
theorem B1972351 : Blo 1971435 1972351 := bstep (se 1 (by rfl) ⟨1479263, by rfl⟩ : syracuseStep 1972351 = 2958527) B2958527
theorem B2958533 : Blo 1971435 2958533 := bbase (se 4 (by rfl) ⟨277362, by rfl⟩ : syracuseStep 2958533 = 554725) (by norm_num)
theorem B1972355 : Blo 1971435 1972355 := bstep (se 1 (by rfl) ⟨1479266, by rfl⟩ : syracuseStep 1972355 = 2958533) B2958533
theorem B3328357 : Blo 1971435 3328357 := bbase (se 4 (by rfl) ⟨312033, by rfl⟩ : syracuseStep 3328357 = 624067) (by norm_num)
theorem B4437809 : Blo 1971435 4437809 := bstep (se 2 (by rfl) ⟨1664178, by rfl⟩ : syracuseStep 4437809 = 3328357) B3328357
theorem B2958539 : Blo 1971435 2958539 := bstep (se 1 (by rfl) ⟨2218904, by rfl⟩ : syracuseStep 2958539 = 4437809) B4437809
theorem B1972359 : Blo 1971435 1972359 := bstep (se 1 (by rfl) ⟨1479269, by rfl⟩ : syracuseStep 1972359 = 2958539) B2958539
theorem B2218909 : Blo 1971435 2218909 := bbase (se 3 (by rfl) ⟨416045, by rfl⟩ : syracuseStep 2218909 = 832091) (by norm_num)
theorem B2958545 : Blo 1971435 2958545 := bstep (se 2 (by rfl) ⟨1109454, by rfl⟩ : syracuseStep 2958545 = 2218909) B2218909
theorem B1972363 : Blo 1971435 1972363 := bstep (se 1 (by rfl) ⟨1479272, by rfl⟩ : syracuseStep 1972363 = 2958545) B2958545
theorem B6656741 : Blo 1971435 6656741 := bbase (se 4 (by rfl) ⟨624069, by rfl⟩ : syracuseStep 6656741 = 1248139) (by norm_num)
theorem B4437827 : Blo 1971435 4437827 := bstep (se 1 (by rfl) ⟨3328370, by rfl⟩ : syracuseStep 4437827 = 6656741) B6656741
theorem B2958551 : Blo 1971435 2958551 := bstep (se 1 (by rfl) ⟨2218913, by rfl⟩ : syracuseStep 2958551 = 4437827) B4437827
theorem B1972367 : Blo 1971435 1972367 := bstep (se 1 (by rfl) ⟨1479275, by rfl⟩ : syracuseStep 1972367 = 2958551) B2958551
theorem B2958557 : Blo 1971435 2958557 := bbase (se 3 (by rfl) ⟨554729, by rfl⟩ : syracuseStep 2958557 = 1109459) (by norm_num)
theorem B1972371 : Blo 1971435 1972371 := bstep (se 1 (by rfl) ⟨1479278, by rfl⟩ : syracuseStep 1972371 = 2958557) B2958557
theorem B4437845 : Blo 1971435 4437845 := bbase (se 9 (by rfl) ⟨13001, by rfl⟩ : syracuseStep 4437845 = 26003) (by norm_num)
theorem B2958563 : Blo 1971435 2958563 := bstep (se 1 (by rfl) ⟨2218922, by rfl⟩ : syracuseStep 2958563 = 4437845) B4437845
theorem B1972375 : Blo 1971435 1972375 := bstep (se 1 (by rfl) ⟨1479281, by rfl⟩ : syracuseStep 1972375 = 2958563) B2958563
theorem B5616661 : Blo 1971435 5616661 := bbase (se 6 (by rfl) ⟨131640, by rfl⟩ : syracuseStep 5616661 = 263281) (by norm_num)
theorem B7488881 : Blo 1971435 7488881 := bstep (se 2 (by rfl) ⟨2808330, by rfl⟩ : syracuseStep 7488881 = 5616661) B5616661
theorem B4992587 : Blo 1971435 4992587 := bstep (se 1 (by rfl) ⟨3744440, by rfl⟩ : syracuseStep 4992587 = 7488881) B7488881
theorem B3328391 : Blo 1971435 3328391 := bstep (se 1 (by rfl) ⟨2496293, by rfl⟩ : syracuseStep 3328391 = 4992587) B4992587
theorem B2218927 : Blo 1971435 2218927 := bstep (se 1 (by rfl) ⟨1664195, by rfl⟩ : syracuseStep 2218927 = 3328391) B3328391
theorem B2958569 : Blo 1971435 2958569 := bstep (se 2 (by rfl) ⟨1109463, by rfl⟩ : syracuseStep 2958569 = 2218927) B2218927
theorem B1972379 : Blo 1971435 1972379 := bstep (se 1 (by rfl) ⟨1479284, by rfl⟩ : syracuseStep 1972379 = 2958569) B2958569
theorem B4621997 : Blo 1971435 4621997 := bbase (se 3 (by rfl) ⟨866624, by rfl⟩ : syracuseStep 4621997 = 1733249) (by norm_num)
theorem B3081331 : Blo 1971435 3081331 := bstep (se 1 (by rfl) ⟨2310998, by rfl⟩ : syracuseStep 3081331 = 4621997) B4621997
theorem B16433765 : Blo 1971435 16433765 := bstep (se 4 (by rfl) ⟨1540665, by rfl⟩ : syracuseStep 16433765 = 3081331) B3081331
theorem B10955843 : Blo 1971435 10955843 := bstep (se 1 (by rfl) ⟨8216882, by rfl⟩ : syracuseStep 10955843 = 16433765) B16433765
theorem B7303895 : Blo 1971435 7303895 := bstep (se 1 (by rfl) ⟨5477921, by rfl⟩ : syracuseStep 7303895 = 10955843) B10955843
theorem B4869263 : Blo 1971435 4869263 := bstep (se 1 (by rfl) ⟨3651947, by rfl⟩ : syracuseStep 4869263 = 7303895) B7303895
theorem B3246175 : Blo 1971435 3246175 := bstep (se 1 (by rfl) ⟨2434631, by rfl⟩ : syracuseStep 3246175 = 4869263) B4869263
theorem B17312933 : Blo 1971435 17312933 := bstep (se 4 (by rfl) ⟨1623087, by rfl⟩ : syracuseStep 17312933 = 3246175) B3246175
theorem B46167821 : Blo 1971435 46167821 := bstep (se 3 (by rfl) ⟨8656466, by rfl⟩ : syracuseStep 46167821 = 17312933) B17312933
theorem B30778547 : Blo 1971435 30778547 := bstep (se 1 (by rfl) ⟨23083910, by rfl⟩ : syracuseStep 30778547 = 46167821) B46167821
theorem B82076125 : Blo 1971435 82076125 := bstep (se 3 (by rfl) ⟨15389273, by rfl⟩ : syracuseStep 82076125 = 30778547) B30778547
theorem B109434833 : Blo 1971435 109434833 := bstep (se 2 (by rfl) ⟨41038062, by rfl⟩ : syracuseStep 109434833 = 82076125) B82076125
theorem B72956555 : Blo 1971435 72956555 := bstep (se 1 (by rfl) ⟨54717416, by rfl⟩ : syracuseStep 72956555 = 109434833) B109434833
theorem B48637703 : Blo 1971435 48637703 := bstep (se 1 (by rfl) ⟨36478277, by rfl⟩ : syracuseStep 48637703 = 72956555) B72956555
theorem B129700541 : Blo 1971435 129700541 := bstep (se 3 (by rfl) ⟨24318851, by rfl⟩ : syracuseStep 129700541 = 48637703) B48637703
theorem B86467027 : Blo 1971435 86467027 := bstep (se 1 (by rfl) ⟨64850270, by rfl⟩ : syracuseStep 86467027 = 129700541) B129700541
theorem B115289369 : Blo 1971435 115289369 := bstep (se 2 (by rfl) ⟨43233513, by rfl⟩ : syracuseStep 115289369 = 86467027) B86467027
theorem B76859579 : Blo 1971435 76859579 := bstep (se 1 (by rfl) ⟨57644684, by rfl⟩ : syracuseStep 76859579 = 115289369) B115289369
theorem B51239719 : Blo 1971435 51239719 := bstep (se 1 (by rfl) ⟨38429789, by rfl⟩ : syracuseStep 51239719 = 76859579) B76859579
theorem B68319625 : Blo 1971435 68319625 := bstep (se 2 (by rfl) ⟨25619859, by rfl⟩ : syracuseStep 68319625 = 51239719) B51239719
theorem B91092833 : Blo 1971435 91092833 := bstep (se 2 (by rfl) ⟨34159812, by rfl⟩ : syracuseStep 91092833 = 68319625) B68319625
theorem B60728555 : Blo 1971435 60728555 := bstep (se 1 (by rfl) ⟨45546416, by rfl⟩ : syracuseStep 60728555 = 91092833) B91092833
theorem B40485703 : Blo 1971435 40485703 := bstep (se 1 (by rfl) ⟨30364277, by rfl⟩ : syracuseStep 40485703 = 60728555) B60728555
theorem B53980937 : Blo 1971435 53980937 := bstep (se 2 (by rfl) ⟨20242851, by rfl⟩ : syracuseStep 53980937 = 40485703) B40485703
theorem B35987291 : Blo 1971435 35987291 := bstep (se 1 (by rfl) ⟨26990468, by rfl⟩ : syracuseStep 35987291 = 53980937) B53980937
theorem B23991527 : Blo 1971435 23991527 := bstep (se 1 (by rfl) ⟨17993645, by rfl⟩ : syracuseStep 23991527 = 35987291) B35987291
theorem B15994351 : Blo 1971435 15994351 := bstep (se 1 (by rfl) ⟨11995763, by rfl⟩ : syracuseStep 15994351 = 23991527) B23991527
theorem B85303205 : Blo 1971435 85303205 := bstep (se 4 (by rfl) ⟨7997175, by rfl⟩ : syracuseStep 85303205 = 15994351) B15994351
theorem B56868803 : Blo 1971435 56868803 := bstep (se 1 (by rfl) ⟨42651602, by rfl⟩ : syracuseStep 56868803 = 85303205) B85303205
theorem B37912535 : Blo 1971435 37912535 := bstep (se 1 (by rfl) ⟨28434401, by rfl⟩ : syracuseStep 37912535 = 56868803) B56868803
theorem B25275023 : Blo 1971435 25275023 := bstep (se 1 (by rfl) ⟨18956267, by rfl⟩ : syracuseStep 25275023 = 37912535) B37912535
theorem B16850015 : Blo 1971435 16850015 := bstep (se 1 (by rfl) ⟨12637511, by rfl⟩ : syracuseStep 16850015 = 25275023) B25275023
theorem B11233343 : Blo 1971435 11233343 := bstep (se 1 (by rfl) ⟨8425007, by rfl⟩ : syracuseStep 11233343 = 16850015) B16850015
theorem B7488895 : Blo 1971435 7488895 := bstep (se 1 (by rfl) ⟨5616671, by rfl⟩ : syracuseStep 7488895 = 11233343) B11233343
theorem B9985193 : Blo 1971435 9985193 := bstep (se 2 (by rfl) ⟨3744447, by rfl⟩ : syracuseStep 9985193 = 7488895) B7488895
theorem B6656795 : Blo 1971435 6656795 := bstep (se 1 (by rfl) ⟨4992596, by rfl⟩ : syracuseStep 6656795 = 9985193) B9985193
theorem B4437863 : Blo 1971435 4437863 := bstep (se 1 (by rfl) ⟨3328397, by rfl⟩ : syracuseStep 4437863 = 6656795) B6656795
theorem B2958575 : Blo 1971435 2958575 := bstep (se 1 (by rfl) ⟨2218931, by rfl⟩ : syracuseStep 2958575 = 4437863) B4437863
theorem B1972383 : Blo 1971435 1972383 := bstep (se 1 (by rfl) ⟨1479287, by rfl⟩ : syracuseStep 1972383 = 2958575) B2958575
theorem B2958581 : Blo 1971435 2958581 := bbase (se 5 (by rfl) ⟨138683, by rfl⟩ : syracuseStep 2958581 = 277367) (by norm_num)
theorem B1972387 : Blo 1971435 1972387 := bstep (se 1 (by rfl) ⟨1479290, by rfl⟩ : syracuseStep 1972387 = 2958581) B2958581
theorem B15994421 : Blo 1971435 15994421 := bbase (se 5 (by rfl) ⟨749738, by rfl⟩ : syracuseStep 15994421 = 1499477) (by norm_num)
theorem B10662947 : Blo 1971435 10662947 := bstep (se 1 (by rfl) ⟨7997210, by rfl⟩ : syracuseStep 10662947 = 15994421) B15994421
theorem B7108631 : Blo 1971435 7108631 := bstep (se 1 (by rfl) ⟨5331473, by rfl⟩ : syracuseStep 7108631 = 10662947) B10662947
theorem B4739087 : Blo 1971435 4739087 := bstep (se 1 (by rfl) ⟨3554315, by rfl⟩ : syracuseStep 4739087 = 7108631) B7108631
theorem B12637565 : Blo 1971435 12637565 := bstep (se 3 (by rfl) ⟨2369543, by rfl⟩ : syracuseStep 12637565 = 4739087) B4739087
theorem B8425043 : Blo 1971435 8425043 := bstep (se 1 (by rfl) ⟨6318782, by rfl⟩ : syracuseStep 8425043 = 12637565) B12637565
theorem B5616695 : Blo 1971435 5616695 := bstep (se 1 (by rfl) ⟨4212521, by rfl⟩ : syracuseStep 5616695 = 8425043) B8425043
theorem B3744463 : Blo 1971435 3744463 := bstep (se 1 (by rfl) ⟨2808347, by rfl⟩ : syracuseStep 3744463 = 5616695) B5616695
theorem B4992617 : Blo 1971435 4992617 := bstep (se 2 (by rfl) ⟨1872231, by rfl⟩ : syracuseStep 4992617 = 3744463) B3744463
theorem B3328411 : Blo 1971435 3328411 := bstep (se 1 (by rfl) ⟨2496308, by rfl⟩ : syracuseStep 3328411 = 4992617) B4992617
theorem B4437881 : Blo 1971435 4437881 := bstep (se 2 (by rfl) ⟨1664205, by rfl⟩ : syracuseStep 4437881 = 3328411) B3328411
theorem B2958587 : Blo 1971435 2958587 := bstep (se 1 (by rfl) ⟨2218940, by rfl⟩ : syracuseStep 2958587 = 4437881) B4437881
theorem B1972391 : Blo 1971435 1972391 := bstep (se 1 (by rfl) ⟨1479293, by rfl⟩ : syracuseStep 1972391 = 2958587) B2958587
theorem B2218945 : Blo 1971435 2218945 := bbase (se 2 (by rfl) ⟨832104, by rfl⟩ : syracuseStep 2218945 = 1664209) (by norm_num)
theorem B2958593 : Blo 1971435 2958593 := bstep (se 2 (by rfl) ⟨1109472, by rfl⟩ : syracuseStep 2958593 = 2218945) B2218945
theorem B1972395 : Blo 1971435 1972395 := bstep (se 1 (by rfl) ⟨1479296, by rfl⟩ : syracuseStep 1972395 = 2958593) B2958593
theorem B4992637 : Blo 1971435 4992637 := bbase (se 3 (by rfl) ⟨936119, by rfl⟩ : syracuseStep 4992637 = 1872239) (by norm_num)
theorem B6656849 : Blo 1971435 6656849 := bstep (se 2 (by rfl) ⟨2496318, by rfl⟩ : syracuseStep 6656849 = 4992637) B4992637
theorem B4437899 : Blo 1971435 4437899 := bstep (se 1 (by rfl) ⟨3328424, by rfl⟩ : syracuseStep 4437899 = 6656849) B6656849
theorem B2958599 : Blo 1971435 2958599 := bstep (se 1 (by rfl) ⟨2218949, by rfl⟩ : syracuseStep 2958599 = 4437899) B4437899
theorem B1972399 : Blo 1971435 1972399 := bstep (se 1 (by rfl) ⟨1479299, by rfl⟩ : syracuseStep 1972399 = 2958599) B2958599
theorem B2958605 : Blo 1971435 2958605 := bbase (se 3 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 2958605 = 1109477) (by norm_num)
theorem B1972403 : Blo 1971435 1972403 := bstep (se 1 (by rfl) ⟨1479302, by rfl⟩ : syracuseStep 1972403 = 2958605) B2958605
theorem B4437917 : Blo 1971435 4437917 := bbase (se 3 (by rfl) ⟨832109, by rfl⟩ : syracuseStep 4437917 = 1664219) (by norm_num)
theorem B2958611 : Blo 1971435 2958611 := bstep (se 1 (by rfl) ⟨2218958, by rfl⟩ : syracuseStep 2958611 = 4437917) B4437917
theorem B1972407 : Blo 1971435 1972407 := bstep (se 1 (by rfl) ⟨1479305, by rfl⟩ : syracuseStep 1972407 = 2958611) B2958611
theorem B3328445 : Blo 1971435 3328445 := bbase (se 3 (by rfl) ⟨624083, by rfl⟩ : syracuseStep 3328445 = 1248167) (by norm_num)
theorem B2218963 : Blo 1971435 2218963 := bstep (se 1 (by rfl) ⟨1664222, by rfl⟩ : syracuseStep 2218963 = 3328445) B3328445
theorem B2958617 : Blo 1971435 2958617 := bstep (se 2 (by rfl) ⟨1109481, by rfl⟩ : syracuseStep 2958617 = 2218963) B2218963
theorem B1972411 : Blo 1971435 1972411 := bstep (se 1 (by rfl) ⟨1479308, by rfl⟩ : syracuseStep 1972411 = 2958617) B2958617
theorem B11233525 : Blo 1971435 11233525 := bbase (se 5 (by rfl) ⟨526571, by rfl⟩ : syracuseStep 11233525 = 1053143) (by norm_num)
theorem B14978033 : Blo 1971435 14978033 := bstep (se 2 (by rfl) ⟨5616762, by rfl⟩ : syracuseStep 14978033 = 11233525) B11233525
theorem B9985355 : Blo 1971435 9985355 := bstep (se 1 (by rfl) ⟨7489016, by rfl⟩ : syracuseStep 9985355 = 14978033) B14978033
theorem B6656903 : Blo 1971435 6656903 := bstep (se 1 (by rfl) ⟨4992677, by rfl⟩ : syracuseStep 6656903 = 9985355) B9985355
theorem B4437935 : Blo 1971435 4437935 := bstep (se 1 (by rfl) ⟨3328451, by rfl⟩ : syracuseStep 4437935 = 6656903) B6656903
theorem B2958623 : Blo 1971435 2958623 := bstep (se 1 (by rfl) ⟨2218967, by rfl⟩ : syracuseStep 2958623 = 4437935) B4437935
theorem B1972415 : Blo 1971435 1972415 := bstep (se 1 (by rfl) ⟨1479311, by rfl⟩ : syracuseStep 1972415 = 2958623) B2958623
theorem B2958629 : Blo 1971435 2958629 := bbase (se 4 (by rfl) ⟨277371, by rfl⟩ : syracuseStep 2958629 = 554743) (by norm_num)
theorem B1972419 : Blo 1971435 1972419 := bstep (se 1 (by rfl) ⟨1479314, by rfl⟩ : syracuseStep 1972419 = 2958629) B2958629
theorem B2496349 : Blo 1971435 2496349 := bbase (se 3 (by rfl) ⟨468065, by rfl⟩ : syracuseStep 2496349 = 936131) (by norm_num)
theorem B3328465 : Blo 1971435 3328465 := bstep (se 2 (by rfl) ⟨1248174, by rfl⟩ : syracuseStep 3328465 = 2496349) B2496349
theorem B4437953 : Blo 1971435 4437953 := bstep (se 2 (by rfl) ⟨1664232, by rfl⟩ : syracuseStep 4437953 = 3328465) B3328465
theorem B2958635 : Blo 1971435 2958635 := bstep (se 1 (by rfl) ⟨2218976, by rfl⟩ : syracuseStep 2958635 = 4437953) B4437953
theorem B1972423 : Blo 1971435 1972423 := bstep (se 1 (by rfl) ⟨1479317, by rfl⟩ : syracuseStep 1972423 = 2958635) B2958635
theorem B2218981 : Blo 1971435 2218981 := bbase (se 4 (by rfl) ⟨208029, by rfl⟩ : syracuseStep 2218981 = 416059) (by norm_num)
theorem B2958641 : Blo 1971435 2958641 := bstep (se 2 (by rfl) ⟨1109490, by rfl⟩ : syracuseStep 2958641 = 2218981) B2218981
theorem B1972427 : Blo 1971435 1972427 := bstep (se 1 (by rfl) ⟨1479320, by rfl⟩ : syracuseStep 1972427 = 2958641) B2958641
theorem B2135041 : Blo 1971435 2135041 := bbase (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) (by norm_num)
theorem B45547541 : Blo 1971435 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B30365027 : Blo 1971435 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B20243351 : Blo 1971435 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B13495567 : Blo 1971435 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B17994089 : Blo 1971435 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B47984237 : Blo 1971435 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B31989491 : Blo 1971435 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B21326327 : Blo 1971435 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B14217551 : Blo 1971435 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B9478367 : Blo 1971435 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B6318911 : Blo 1971435 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B4212607 : Blo 1971435 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B5616809 : Blo 1971435 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B3744539 : Blo 1971435 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B2496359 : Blo 1971435 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B6656957 : Blo 1971435 6656957 := bstep (se 3 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 6656957 = 2496359) B2496359
theorem B4437971 : Blo 1971435 4437971 := bstep (se 1 (by rfl) ⟨3328478, by rfl⟩ : syracuseStep 4437971 = 6656957) B6656957
theorem B2958647 : Blo 1971435 2958647 := bstep (se 1 (by rfl) ⟨2218985, by rfl⟩ : syracuseStep 2958647 = 4437971) B4437971
theorem B1972431 : Blo 1971435 1972431 := bstep (se 1 (by rfl) ⟨1479323, by rfl⟩ : syracuseStep 1972431 = 2958647) B2958647
theorem B2958653 : Blo 1971435 2958653 := bbase (se 3 (by rfl) ⟨554747, by rfl⟩ : syracuseStep 2958653 = 1109495) (by norm_num)
theorem B1972435 : Blo 1971435 1972435 := bstep (se 1 (by rfl) ⟨1479326, by rfl⟩ : syracuseStep 1972435 = 2958653) B2958653
theorem B4437989 : Blo 1971435 4437989 := bbase (se 4 (by rfl) ⟨416061, by rfl⟩ : syracuseStep 4437989 = 832123) (by norm_num)
theorem B2958659 : Blo 1971435 2958659 := bstep (se 1 (by rfl) ⟨2218994, by rfl⟩ : syracuseStep 2958659 = 4437989) B4437989
theorem B1972439 : Blo 1971435 1972439 := bstep (se 1 (by rfl) ⟨1479329, by rfl⟩ : syracuseStep 1972439 = 2958659) B2958659
theorem B4992749 : Blo 1971435 4992749 := bbase (se 3 (by rfl) ⟨936140, by rfl⟩ : syracuseStep 4992749 = 1872281) (by norm_num)
theorem B3328499 : Blo 1971435 3328499 := bstep (se 1 (by rfl) ⟨2496374, by rfl⟩ : syracuseStep 3328499 = 4992749) B4992749
theorem B2218999 : Blo 1971435 2218999 := bstep (se 1 (by rfl) ⟨1664249, by rfl⟩ : syracuseStep 2218999 = 3328499) B3328499
theorem B2958665 : Blo 1971435 2958665 := bstep (se 2 (by rfl) ⟨1109499, by rfl⟩ : syracuseStep 2958665 = 2218999) B2218999
theorem B1972443 : Blo 1971435 1972443 := bstep (se 1 (by rfl) ⟨1479332, by rfl⟩ : syracuseStep 1972443 = 2958665) B2958665
theorem B2665813 : Blo 1971435 2665813 := bbase (se 11 (by rfl) ⟨1952, by rfl⟩ : syracuseStep 2665813 = 3905) (by norm_num)
theorem B3554417 : Blo 1971435 3554417 := bstep (se 2 (by rfl) ⟨1332906, by rfl⟩ : syracuseStep 3554417 = 2665813) B2665813
theorem B2369611 : Blo 1971435 2369611 := bstep (se 1 (by rfl) ⟨1777208, by rfl⟩ : syracuseStep 2369611 = 3554417) B3554417
theorem B3159481 : Blo 1971435 3159481 := bstep (se 2 (by rfl) ⟨1184805, by rfl⟩ : syracuseStep 3159481 = 2369611) B2369611
theorem B4212641 : Blo 1971435 4212641 := bstep (se 2 (by rfl) ⟨1579740, by rfl⟩ : syracuseStep 4212641 = 3159481) B3159481
theorem B2808427 : Blo 1971435 2808427 := bstep (se 1 (by rfl) ⟨2106320, by rfl⟩ : syracuseStep 2808427 = 4212641) B4212641
theorem B3744569 : Blo 1971435 3744569 := bstep (se 2 (by rfl) ⟨1404213, by rfl⟩ : syracuseStep 3744569 = 2808427) B2808427
theorem B9985517 : Blo 1971435 9985517 := bstep (se 3 (by rfl) ⟨1872284, by rfl⟩ : syracuseStep 9985517 = 3744569) B3744569
theorem B6657011 : Blo 1971435 6657011 := bstep (se 1 (by rfl) ⟨4992758, by rfl⟩ : syracuseStep 6657011 = 9985517) B9985517
theorem B4438007 : Blo 1971435 4438007 := bstep (se 1 (by rfl) ⟨3328505, by rfl⟩ : syracuseStep 4438007 = 6657011) B6657011
theorem B2958671 : Blo 1971435 2958671 := bstep (se 1 (by rfl) ⟨2219003, by rfl⟩ : syracuseStep 2958671 = 4438007) B4438007
theorem B1972447 : Blo 1971435 1972447 := bstep (se 1 (by rfl) ⟨1479335, by rfl⟩ : syracuseStep 1972447 = 2958671) B2958671
theorem B2958677 : Blo 1971435 2958677 := bbase (se 12 (by rfl) ⟨1083, by rfl⟩ : syracuseStep 2958677 = 2167) (by norm_num)
theorem B1972451 : Blo 1971435 1972451 := bstep (se 1 (by rfl) ⟨1479338, by rfl⟩ : syracuseStep 1972451 = 2958677) B2958677
theorem B2106329 : Blo 1971435 2106329 := bbase (se 2 (by rfl) ⟨789873, by rfl⟩ : syracuseStep 2106329 = 1579747) (by norm_num)
theorem B5616877 : Blo 1971435 5616877 := bstep (se 3 (by rfl) ⟨1053164, by rfl⟩ : syracuseStep 5616877 = 2106329) B2106329
theorem B7489169 : Blo 1971435 7489169 := bstep (se 2 (by rfl) ⟨2808438, by rfl⟩ : syracuseStep 7489169 = 5616877) B5616877
theorem B4992779 : Blo 1971435 4992779 := bstep (se 1 (by rfl) ⟨3744584, by rfl⟩ : syracuseStep 4992779 = 7489169) B7489169
theorem B3328519 : Blo 1971435 3328519 := bstep (se 1 (by rfl) ⟨2496389, by rfl⟩ : syracuseStep 3328519 = 4992779) B4992779
theorem B4438025 : Blo 1971435 4438025 := bstep (se 2 (by rfl) ⟨1664259, by rfl⟩ : syracuseStep 4438025 = 3328519) B3328519
theorem B2958683 : Blo 1971435 2958683 := bstep (se 1 (by rfl) ⟨2219012, by rfl⟩ : syracuseStep 2958683 = 4438025) B4438025
theorem B1972455 : Blo 1971435 1972455 := bstep (se 1 (by rfl) ⟨1479341, by rfl⟩ : syracuseStep 1972455 = 2958683) B2958683
theorem B2219017 : Blo 1971435 2219017 := bbase (se 2 (by rfl) ⟨832131, by rfl⟩ : syracuseStep 2219017 = 1664263) (by norm_num)
theorem B2958689 : Blo 1971435 2958689 := bstep (se 2 (by rfl) ⟨1109508, by rfl⟩ : syracuseStep 2958689 = 2219017) B2219017
theorem B1972459 : Blo 1971435 1972459 := bstep (se 1 (by rfl) ⟨1479344, by rfl⟩ : syracuseStep 1972459 = 2958689) B2958689
theorem B6747893 : Blo 1971435 6747893 := bbase (se 5 (by rfl) ⟨316307, by rfl⟩ : syracuseStep 6747893 = 632615) (by norm_num)
theorem B4498595 : Blo 1971435 4498595 := bstep (se 1 (by rfl) ⟨3373946, by rfl⟩ : syracuseStep 4498595 = 6747893) B6747893
theorem B2999063 : Blo 1971435 2999063 := bstep (se 1 (by rfl) ⟨2249297, by rfl⟩ : syracuseStep 2999063 = 4498595) B4498595
theorem B7997501 : Blo 1971435 7997501 := bstep (se 3 (by rfl) ⟨1499531, by rfl⟩ : syracuseStep 7997501 = 2999063) B2999063
theorem B5331667 : Blo 1971435 5331667 := bstep (se 1 (by rfl) ⟨3998750, by rfl⟩ : syracuseStep 5331667 = 7997501) B7997501
theorem B7108889 : Blo 1971435 7108889 := bstep (se 2 (by rfl) ⟨2665833, by rfl⟩ : syracuseStep 7108889 = 5331667) B5331667
theorem B18957037 : Blo 1971435 18957037 := bstep (se 3 (by rfl) ⟨3554444, by rfl⟩ : syracuseStep 18957037 = 7108889) B7108889
theorem B25276049 : Blo 1971435 25276049 := bstep (se 2 (by rfl) ⟨9478518, by rfl⟩ : syracuseStep 25276049 = 18957037) B18957037
theorem B16850699 : Blo 1971435 16850699 := bstep (se 1 (by rfl) ⟨12638024, by rfl⟩ : syracuseStep 16850699 = 25276049) B25276049
theorem B11233799 : Blo 1971435 11233799 := bstep (se 1 (by rfl) ⟨8425349, by rfl⟩ : syracuseStep 11233799 = 16850699) B16850699
theorem B7489199 : Blo 1971435 7489199 := bstep (se 1 (by rfl) ⟨5616899, by rfl⟩ : syracuseStep 7489199 = 11233799) B11233799
theorem B4992799 : Blo 1971435 4992799 := bstep (se 1 (by rfl) ⟨3744599, by rfl⟩ : syracuseStep 4992799 = 7489199) B7489199
theorem B6657065 : Blo 1971435 6657065 := bstep (se 2 (by rfl) ⟨2496399, by rfl⟩ : syracuseStep 6657065 = 4992799) B4992799
theorem B4438043 : Blo 1971435 4438043 := bstep (se 1 (by rfl) ⟨3328532, by rfl⟩ : syracuseStep 4438043 = 6657065) B6657065
theorem B2958695 : Blo 1971435 2958695 := bstep (se 1 (by rfl) ⟨2219021, by rfl⟩ : syracuseStep 2958695 = 4438043) B4438043
theorem B1972463 : Blo 1971435 1972463 := bstep (se 1 (by rfl) ⟨1479347, by rfl⟩ : syracuseStep 1972463 = 2958695) B2958695
theorem B2958701 : Blo 1971435 2958701 := bbase (se 3 (by rfl) ⟨554756, by rfl⟩ : syracuseStep 2958701 = 1109513) (by norm_num)
theorem B1972467 : Blo 1971435 1972467 := bstep (se 1 (by rfl) ⟨1479350, by rfl⟩ : syracuseStep 1972467 = 2958701) B2958701
theorem B4438061 : Blo 1971435 4438061 := bbase (se 3 (by rfl) ⟨832136, by rfl⟩ : syracuseStep 4438061 = 1664273) (by norm_num)
theorem B2958707 : Blo 1971435 2958707 := bstep (se 1 (by rfl) ⟨2219030, by rfl⟩ : syracuseStep 2958707 = 4438061) B4438061
theorem B1972471 : Blo 1971435 1972471 := bstep (se 1 (by rfl) ⟨1479353, by rfl⟩ : syracuseStep 1972471 = 2958707) B2958707
theorem B5331701 : Blo 1971435 5331701 := bbase (se 5 (by rfl) ⟨249923, by rfl⟩ : syracuseStep 5331701 = 499847) (by norm_num)
theorem B14217869 : Blo 1971435 14217869 := bstep (se 3 (by rfl) ⟨2665850, by rfl⟩ : syracuseStep 14217869 = 5331701) B5331701
theorem B9478579 : Blo 1971435 9478579 := bstep (se 1 (by rfl) ⟨7108934, by rfl⟩ : syracuseStep 9478579 = 14217869) B14217869
theorem B12638105 : Blo 1971435 12638105 := bstep (se 2 (by rfl) ⟨4739289, by rfl⟩ : syracuseStep 12638105 = 9478579) B9478579
theorem B8425403 : Blo 1971435 8425403 := bstep (se 1 (by rfl) ⟨6319052, by rfl⟩ : syracuseStep 8425403 = 12638105) B12638105
theorem B5616935 : Blo 1971435 5616935 := bstep (se 1 (by rfl) ⟨4212701, by rfl⟩ : syracuseStep 5616935 = 8425403) B8425403
theorem B3744623 : Blo 1971435 3744623 := bstep (se 1 (by rfl) ⟨2808467, by rfl⟩ : syracuseStep 3744623 = 5616935) B5616935
theorem B2496415 : Blo 1971435 2496415 := bstep (se 1 (by rfl) ⟨1872311, by rfl⟩ : syracuseStep 2496415 = 3744623) B3744623
theorem B3328553 : Blo 1971435 3328553 := bstep (se 2 (by rfl) ⟨1248207, by rfl⟩ : syracuseStep 3328553 = 2496415) B2496415
theorem B2219035 : Blo 1971435 2219035 := bstep (se 1 (by rfl) ⟨1664276, by rfl⟩ : syracuseStep 2219035 = 3328553) B3328553
theorem B2958713 : Blo 1971435 2958713 := bstep (se 2 (by rfl) ⟨1109517, by rfl⟩ : syracuseStep 2958713 = 2219035) B2219035
theorem B1972475 : Blo 1971435 1972475 := bstep (se 1 (by rfl) ⟨1479356, by rfl⟩ : syracuseStep 1972475 = 2958713) B2958713
theorem B2135093 : Blo 1971435 2135093 := bbase (se 5 (by rfl) ⟨100082, by rfl⟩ : syracuseStep 2135093 = 200165) (by norm_num)
theorem B5693581 : Blo 1971435 5693581 := bstep (se 3 (by rfl) ⟨1067546, by rfl⟩ : syracuseStep 5693581 = 2135093) B2135093
theorem B30365765 : Blo 1971435 30365765 := bstep (se 4 (by rfl) ⟨2846790, by rfl⟩ : syracuseStep 30365765 = 5693581) B5693581
theorem B20243843 : Blo 1971435 20243843 := bstep (se 1 (by rfl) ⟨15182882, by rfl⟩ : syracuseStep 20243843 = 30365765) B30365765
theorem B13495895 : Blo 1971435 13495895 := bstep (se 1 (by rfl) ⟨10121921, by rfl⟩ : syracuseStep 13495895 = 20243843) B20243843
theorem B8997263 : Blo 1971435 8997263 := bstep (se 1 (by rfl) ⟨6747947, by rfl⟩ : syracuseStep 8997263 = 13495895) B13495895
theorem B5998175 : Blo 1971435 5998175 := bstep (se 1 (by rfl) ⟨4498631, by rfl⟩ : syracuseStep 5998175 = 8997263) B8997263
theorem B3998783 : Blo 1971435 3998783 := bstep (se 1 (by rfl) ⟨2999087, by rfl⟩ : syracuseStep 3998783 = 5998175) B5998175
theorem B2665855 : Blo 1971435 2665855 := bstep (se 1 (by rfl) ⟨1999391, by rfl⟩ : syracuseStep 2665855 = 3998783) B3998783
theorem B14217893 : Blo 1971435 14217893 := bstep (se 4 (by rfl) ⟨1332927, by rfl⟩ : syracuseStep 14217893 = 2665855) B2665855
theorem B9478595 : Blo 1971435 9478595 := bstep (se 1 (by rfl) ⟨7108946, by rfl⟩ : syracuseStep 9478595 = 14217893) B14217893
theorem B6319063 : Blo 1971435 6319063 := bstep (se 1 (by rfl) ⟨4739297, by rfl⟩ : syracuseStep 6319063 = 9478595) B9478595
theorem B33701669 : Blo 1971435 33701669 := bstep (se 4 (by rfl) ⟨3159531, by rfl⟩ : syracuseStep 33701669 = 6319063) B6319063
theorem B22467779 : Blo 1971435 22467779 := bstep (se 1 (by rfl) ⟨16850834, by rfl⟩ : syracuseStep 22467779 = 33701669) B33701669
theorem B14978519 : Blo 1971435 14978519 := bstep (se 1 (by rfl) ⟨11233889, by rfl⟩ : syracuseStep 14978519 = 22467779) B22467779
theorem B9985679 : Blo 1971435 9985679 := bstep (se 1 (by rfl) ⟨7489259, by rfl⟩ : syracuseStep 9985679 = 14978519) B14978519
theorem B6657119 : Blo 1971435 6657119 := bstep (se 1 (by rfl) ⟨4992839, by rfl⟩ : syracuseStep 6657119 = 9985679) B9985679
theorem B4438079 : Blo 1971435 4438079 := bstep (se 1 (by rfl) ⟨3328559, by rfl⟩ : syracuseStep 4438079 = 6657119) B6657119
theorem B2958719 : Blo 1971435 2958719 := bstep (se 1 (by rfl) ⟨2219039, by rfl⟩ : syracuseStep 2958719 = 4438079) B4438079
theorem B1972479 : Blo 1971435 1972479 := bstep (se 1 (by rfl) ⟨1479359, by rfl⟩ : syracuseStep 1972479 = 2958719) B2958719
theorem B2958725 : Blo 1971435 2958725 := bbase (se 4 (by rfl) ⟨277380, by rfl⟩ : syracuseStep 2958725 = 554761) (by norm_num)
theorem B1972483 : Blo 1971435 1972483 := bstep (se 1 (by rfl) ⟨1479362, by rfl⟩ : syracuseStep 1972483 = 2958725) B2958725
theorem B3328573 : Blo 1971435 3328573 := bbase (se 3 (by rfl) ⟨624107, by rfl⟩ : syracuseStep 3328573 = 1248215) (by norm_num)
theorem B4438097 : Blo 1971435 4438097 := bstep (se 2 (by rfl) ⟨1664286, by rfl⟩ : syracuseStep 4438097 = 3328573) B3328573
theorem B2958731 : Blo 1971435 2958731 := bstep (se 1 (by rfl) ⟨2219048, by rfl⟩ : syracuseStep 2958731 = 4438097) B4438097
theorem B1972487 : Blo 1971435 1972487 := bstep (se 1 (by rfl) ⟨1479365, by rfl⟩ : syracuseStep 1972487 = 2958731) B2958731
theorem B2219053 : Blo 1971435 2219053 := bbase (se 3 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 2219053 = 832145) (by norm_num)
theorem B2958737 : Blo 1971435 2958737 := bstep (se 2 (by rfl) ⟨1109526, by rfl⟩ : syracuseStep 2958737 = 2219053) B2219053
theorem B1972491 : Blo 1971435 1972491 := bstep (se 1 (by rfl) ⟨1479368, by rfl⟩ : syracuseStep 1972491 = 2958737) B2958737
theorem B6657173 : Blo 1971435 6657173 := bbase (se 6 (by rfl) ⟨156027, by rfl⟩ : syracuseStep 6657173 = 312055) (by norm_num)
theorem B4438115 : Blo 1971435 4438115 := bstep (se 1 (by rfl) ⟨3328586, by rfl⟩ : syracuseStep 4438115 = 6657173) B6657173
theorem B2958743 : Blo 1971435 2958743 := bstep (se 1 (by rfl) ⟨2219057, by rfl⟩ : syracuseStep 2958743 = 4438115) B4438115
theorem B1972495 : Blo 1971435 1972495 := bstep (se 1 (by rfl) ⟨1479371, by rfl⟩ : syracuseStep 1972495 = 2958743) B2958743
theorem B2958749 : Blo 1971435 2958749 := bbase (se 3 (by rfl) ⟨554765, by rfl⟩ : syracuseStep 2958749 = 1109531) (by norm_num)
theorem B1972499 : Blo 1971435 1972499 := bstep (se 1 (by rfl) ⟨1479374, by rfl⟩ : syracuseStep 1972499 = 2958749) B2958749
theorem B4438133 : Blo 1971435 4438133 := bbase (se 5 (by rfl) ⟨208037, by rfl⟩ : syracuseStep 4438133 = 416075) (by norm_num)
theorem B2958755 : Blo 1971435 2958755 := bstep (se 1 (by rfl) ⟨2219066, by rfl⟩ : syracuseStep 2958755 = 4438133) B4438133
theorem B1972503 : Blo 1971435 1972503 := bstep (se 1 (by rfl) ⟨1479377, by rfl⟩ : syracuseStep 1972503 = 2958755) B2958755
theorem B3554525 : Blo 1971435 3554525 := bbase (se 3 (by rfl) ⟨666473, by rfl⟩ : syracuseStep 3554525 = 1332947) (by norm_num)
theorem B2369683 : Blo 1971435 2369683 := bstep (se 1 (by rfl) ⟨1777262, by rfl⟩ : syracuseStep 2369683 = 3554525) B3554525
theorem B3159577 : Blo 1971435 3159577 := bstep (se 2 (by rfl) ⟨1184841, by rfl⟩ : syracuseStep 3159577 = 2369683) B2369683
theorem B16851077 : Blo 1971435 16851077 := bstep (se 4 (by rfl) ⟨1579788, by rfl⟩ : syracuseStep 16851077 = 3159577) B3159577
theorem B11234051 : Blo 1971435 11234051 := bstep (se 1 (by rfl) ⟨8425538, by rfl⟩ : syracuseStep 11234051 = 16851077) B16851077
theorem B7489367 : Blo 1971435 7489367 := bstep (se 1 (by rfl) ⟨5617025, by rfl⟩ : syracuseStep 7489367 = 11234051) B11234051
theorem B4992911 : Blo 1971435 4992911 := bstep (se 1 (by rfl) ⟨3744683, by rfl⟩ : syracuseStep 4992911 = 7489367) B7489367
theorem B3328607 : Blo 1971435 3328607 := bstep (se 1 (by rfl) ⟨2496455, by rfl⟩ : syracuseStep 3328607 = 4992911) B4992911
theorem B2219071 : Blo 1971435 2219071 := bstep (se 1 (by rfl) ⟨1664303, by rfl⟩ : syracuseStep 2219071 = 3328607) B3328607
theorem B2958761 : Blo 1971435 2958761 := bstep (se 2 (by rfl) ⟨1109535, by rfl⟩ : syracuseStep 2958761 = 2219071) B2219071
theorem B1972507 : Blo 1971435 1972507 := bstep (se 1 (by rfl) ⟨1479380, by rfl⟩ : syracuseStep 1972507 = 2958761) B2958761
theorem B7489381 : Blo 1971435 7489381 := bbase (se 4 (by rfl) ⟨702129, by rfl⟩ : syracuseStep 7489381 = 1404259) (by norm_num)
theorem B9985841 : Blo 1971435 9985841 := bstep (se 2 (by rfl) ⟨3744690, by rfl⟩ : syracuseStep 9985841 = 7489381) B7489381
theorem B6657227 : Blo 1971435 6657227 := bstep (se 1 (by rfl) ⟨4992920, by rfl⟩ : syracuseStep 6657227 = 9985841) B9985841
theorem B4438151 : Blo 1971435 4438151 := bstep (se 1 (by rfl) ⟨3328613, by rfl⟩ : syracuseStep 4438151 = 6657227) B6657227
theorem B2958767 : Blo 1971435 2958767 := bstep (se 1 (by rfl) ⟨2219075, by rfl⟩ : syracuseStep 2958767 = 4438151) B4438151
theorem B1972511 : Blo 1971435 1972511 := bstep (se 1 (by rfl) ⟨1479383, by rfl⟩ : syracuseStep 1972511 = 2958767) B2958767
theorem B2958773 : Blo 1971435 2958773 := bbase (se 5 (by rfl) ⟨138692, by rfl⟩ : syracuseStep 2958773 = 277385) (by norm_num)
theorem B1972515 : Blo 1971435 1972515 := bstep (se 1 (by rfl) ⟨1479386, by rfl⟩ : syracuseStep 1972515 = 2958773) B2958773
theorem B4992941 : Blo 1971435 4992941 := bbase (se 3 (by rfl) ⟨936176, by rfl⟩ : syracuseStep 4992941 = 1872353) (by norm_num)
theorem B3328627 : Blo 1971435 3328627 := bstep (se 1 (by rfl) ⟨2496470, by rfl⟩ : syracuseStep 3328627 = 4992941) B4992941
theorem B4438169 : Blo 1971435 4438169 := bstep (se 2 (by rfl) ⟨1664313, by rfl⟩ : syracuseStep 4438169 = 3328627) B3328627
theorem B2958779 : Blo 1971435 2958779 := bstep (se 1 (by rfl) ⟨2219084, by rfl⟩ : syracuseStep 2958779 = 4438169) B4438169
theorem B1972519 : Blo 1971435 1972519 := bstep (se 1 (by rfl) ⟨1479389, by rfl⟩ : syracuseStep 1972519 = 2958779) B2958779
theorem B2219089 : Blo 1971435 2219089 := bbase (se 2 (by rfl) ⟨832158, by rfl⟩ : syracuseStep 2219089 = 1664317) (by norm_num)
theorem B2958785 : Blo 1971435 2958785 := bstep (se 2 (by rfl) ⟨1109544, by rfl⟩ : syracuseStep 2958785 = 2219089) B2219089
theorem B1972523 : Blo 1971435 1972523 := bstep (se 1 (by rfl) ⟨1479392, by rfl⟩ : syracuseStep 1972523 = 2958785) B2958785
theorem B2808541 : Blo 1971435 2808541 := bbase (se 3 (by rfl) ⟨526601, by rfl⟩ : syracuseStep 2808541 = 1053203) (by norm_num)
theorem B3744721 : Blo 1971435 3744721 := bstep (se 2 (by rfl) ⟨1404270, by rfl⟩ : syracuseStep 3744721 = 2808541) B2808541
theorem B4992961 : Blo 1971435 4992961 := bstep (se 2 (by rfl) ⟨1872360, by rfl⟩ : syracuseStep 4992961 = 3744721) B3744721
theorem B6657281 : Blo 1971435 6657281 := bstep (se 2 (by rfl) ⟨2496480, by rfl⟩ : syracuseStep 6657281 = 4992961) B4992961
theorem B4438187 : Blo 1971435 4438187 := bstep (se 1 (by rfl) ⟨3328640, by rfl⟩ : syracuseStep 4438187 = 6657281) B6657281
theorem B2958791 : Blo 1971435 2958791 := bstep (se 1 (by rfl) ⟨2219093, by rfl⟩ : syracuseStep 2958791 = 4438187) B4438187
theorem B1972527 : Blo 1971435 1972527 := bstep (se 1 (by rfl) ⟨1479395, by rfl⟩ : syracuseStep 1972527 = 2958791) B2958791
theorem B2958797 : Blo 1971435 2958797 := bbase (se 3 (by rfl) ⟨554774, by rfl⟩ : syracuseStep 2958797 = 1109549) (by norm_num)
theorem B1972531 : Blo 1971435 1972531 := bstep (se 1 (by rfl) ⟨1479398, by rfl⟩ : syracuseStep 1972531 = 2958797) B2958797
theorem B4438205 : Blo 1971435 4438205 := bbase (se 3 (by rfl) ⟨832163, by rfl⟩ : syracuseStep 4438205 = 1664327) (by norm_num)
theorem B2958803 : Blo 1971435 2958803 := bstep (se 1 (by rfl) ⟨2219102, by rfl⟩ : syracuseStep 2958803 = 4438205) B4438205
theorem B1972535 : Blo 1971435 1972535 := bstep (se 1 (by rfl) ⟨1479401, by rfl⟩ : syracuseStep 1972535 = 2958803) B2958803
theorem B3328661 : Blo 1971435 3328661 := bbase (se 6 (by rfl) ⟨78015, by rfl⟩ : syracuseStep 3328661 = 156031) (by norm_num)
theorem B2219107 : Blo 1971435 2219107 := bstep (se 1 (by rfl) ⟨1664330, by rfl⟩ : syracuseStep 2219107 = 3328661) B3328661
theorem B2958809 : Blo 1971435 2958809 := bstep (se 2 (by rfl) ⟨1109553, by rfl⟩ : syracuseStep 2958809 = 2219107) B2219107
theorem B1972539 : Blo 1971435 1972539 := bstep (se 1 (by rfl) ⟨1479404, by rfl⟩ : syracuseStep 1972539 = 2958809) B2958809
theorem B5061125 : Blo 1971435 5061125 := bbase (se 4 (by rfl) ⟨474480, by rfl⟩ : syracuseStep 5061125 = 948961) (by norm_num)
theorem B3374083 : Blo 1971435 3374083 := bstep (se 1 (by rfl) ⟨2530562, by rfl⟩ : syracuseStep 3374083 = 5061125) B5061125
theorem B4498777 : Blo 1971435 4498777 := bstep (se 2 (by rfl) ⟨1687041, by rfl⟩ : syracuseStep 4498777 = 3374083) B3374083
theorem B5998369 : Blo 1971435 5998369 := bstep (se 2 (by rfl) ⟨2249388, by rfl⟩ : syracuseStep 5998369 = 4498777) B4498777
theorem B7997825 : Blo 1971435 7997825 := bstep (se 2 (by rfl) ⟨2999184, by rfl⟩ : syracuseStep 7997825 = 5998369) B5998369
theorem B21327533 : Blo 1971435 21327533 := bstep (se 3 (by rfl) ⟨3998912, by rfl⟩ : syracuseStep 21327533 = 7997825) B7997825
theorem B14218355 : Blo 1971435 14218355 := bstep (se 1 (by rfl) ⟨10663766, by rfl⟩ : syracuseStep 14218355 = 21327533) B21327533
theorem B9478903 : Blo 1971435 9478903 := bstep (se 1 (by rfl) ⟨7109177, by rfl⟩ : syracuseStep 9478903 = 14218355) B14218355
theorem B12638537 : Blo 1971435 12638537 := bstep (se 2 (by rfl) ⟨4739451, by rfl⟩ : syracuseStep 12638537 = 9478903) B9478903
theorem B8425691 : Blo 1971435 8425691 := bstep (se 1 (by rfl) ⟨6319268, by rfl⟩ : syracuseStep 8425691 = 12638537) B12638537
theorem B5617127 : Blo 1971435 5617127 := bstep (se 1 (by rfl) ⟨4212845, by rfl⟩ : syracuseStep 5617127 = 8425691) B8425691
theorem B14979005 : Blo 1971435 14979005 := bstep (se 3 (by rfl) ⟨2808563, by rfl⟩ : syracuseStep 14979005 = 5617127) B5617127
theorem B9986003 : Blo 1971435 9986003 := bstep (se 1 (by rfl) ⟨7489502, by rfl⟩ : syracuseStep 9986003 = 14979005) B14979005
theorem B6657335 : Blo 1971435 6657335 := bstep (se 1 (by rfl) ⟨4993001, by rfl⟩ : syracuseStep 6657335 = 9986003) B9986003
theorem B4438223 : Blo 1971435 4438223 := bstep (se 1 (by rfl) ⟨3328667, by rfl⟩ : syracuseStep 4438223 = 6657335) B6657335
theorem B2958815 : Blo 1971435 2958815 := bstep (se 1 (by rfl) ⟨2219111, by rfl⟩ : syracuseStep 2958815 = 4438223) B4438223
theorem B1972543 : Blo 1971435 1972543 := bstep (se 1 (by rfl) ⟨1479407, by rfl⟩ : syracuseStep 1972543 = 2958815) B2958815
theorem B2958821 : Blo 1971435 2958821 := bbase (se 4 (by rfl) ⟨277389, by rfl⟩ : syracuseStep 2958821 = 554779) (by norm_num)
theorem B1972547 : Blo 1971435 1972547 := bstep (se 1 (by rfl) ⟨1479410, by rfl⟩ : syracuseStep 1972547 = 2958821) B2958821
theorem B3202757 : Blo 1971435 3202757 := bbase (se 4 (by rfl) ⟨300258, by rfl⟩ : syracuseStep 3202757 = 600517) (by norm_num)
theorem B2135171 : Blo 1971435 2135171 := bstep (se 1 (by rfl) ⟨1601378, by rfl⟩ : syracuseStep 2135171 = 3202757) B3202757
theorem B5693789 : Blo 1971435 5693789 := bstep (se 3 (by rfl) ⟨1067585, by rfl⟩ : syracuseStep 5693789 = 2135171) B2135171
theorem B3795859 : Blo 1971435 3795859 := bstep (se 1 (by rfl) ⟨2846894, by rfl⟩ : syracuseStep 3795859 = 5693789) B5693789
theorem B20244581 : Blo 1971435 20244581 := bstep (se 4 (by rfl) ⟨1897929, by rfl⟩ : syracuseStep 20244581 = 3795859) B3795859
theorem B13496387 : Blo 1971435 13496387 := bstep (se 1 (by rfl) ⟨10122290, by rfl⟩ : syracuseStep 13496387 = 20244581) B20244581
theorem B143961461 : Blo 1971435 143961461 := bstep (se 5 (by rfl) ⟨6748193, by rfl⟩ : syracuseStep 143961461 = 13496387) B13496387
theorem B95974307 : Blo 1971435 95974307 := bstep (se 1 (by rfl) ⟨71980730, by rfl⟩ : syracuseStep 95974307 = 143961461) B143961461
theorem B63982871 : Blo 1971435 63982871 := bstep (se 1 (by rfl) ⟨47987153, by rfl⟩ : syracuseStep 63982871 = 95974307) B95974307
theorem B42655247 : Blo 1971435 42655247 := bstep (se 1 (by rfl) ⟨31991435, by rfl⟩ : syracuseStep 42655247 = 63982871) B63982871
theorem B28436831 : Blo 1971435 28436831 := bstep (se 1 (by rfl) ⟨21327623, by rfl⟩ : syracuseStep 28436831 = 42655247) B42655247
theorem B18957887 : Blo 1971435 18957887 := bstep (se 1 (by rfl) ⟨14218415, by rfl⟩ : syracuseStep 18957887 = 28436831) B28436831
theorem B12638591 : Blo 1971435 12638591 := bstep (se 1 (by rfl) ⟨9478943, by rfl⟩ : syracuseStep 12638591 = 18957887) B18957887
theorem B8425727 : Blo 1971435 8425727 := bstep (se 1 (by rfl) ⟨6319295, by rfl⟩ : syracuseStep 8425727 = 12638591) B12638591
theorem B5617151 : Blo 1971435 5617151 := bstep (se 1 (by rfl) ⟨4212863, by rfl⟩ : syracuseStep 5617151 = 8425727) B8425727
theorem B3744767 : Blo 1971435 3744767 := bstep (se 1 (by rfl) ⟨2808575, by rfl⟩ : syracuseStep 3744767 = 5617151) B5617151
theorem B2496511 : Blo 1971435 2496511 := bstep (se 1 (by rfl) ⟨1872383, by rfl⟩ : syracuseStep 2496511 = 3744767) B3744767
theorem B3328681 : Blo 1971435 3328681 := bstep (se 2 (by rfl) ⟨1248255, by rfl⟩ : syracuseStep 3328681 = 2496511) B2496511
theorem B4438241 : Blo 1971435 4438241 := bstep (se 2 (by rfl) ⟨1664340, by rfl⟩ : syracuseStep 4438241 = 3328681) B3328681
theorem B2958827 : Blo 1971435 2958827 := bstep (se 1 (by rfl) ⟨2219120, by rfl⟩ : syracuseStep 2958827 = 4438241) B4438241
theorem B1972551 : Blo 1971435 1972551 := bstep (se 1 (by rfl) ⟨1479413, by rfl⟩ : syracuseStep 1972551 = 2958827) B2958827
theorem B2219125 : Blo 1971435 2219125 := bbase (se 5 (by rfl) ⟨104021, by rfl⟩ : syracuseStep 2219125 = 208043) (by norm_num)
theorem B2958833 : Blo 1971435 2958833 := bstep (se 2 (by rfl) ⟨1109562, by rfl⟩ : syracuseStep 2958833 = 2219125) B2219125
theorem B1972555 : Blo 1971435 1972555 := bstep (se 1 (by rfl) ⟨1479416, by rfl⟩ : syracuseStep 1972555 = 2958833) B2958833
theorem B2496521 : Blo 1971435 2496521 := bbase (se 2 (by rfl) ⟨936195, by rfl⟩ : syracuseStep 2496521 = 1872391) (by norm_num)
theorem B6657389 : Blo 1971435 6657389 := bstep (se 3 (by rfl) ⟨1248260, by rfl⟩ : syracuseStep 6657389 = 2496521) B2496521
theorem B4438259 : Blo 1971435 4438259 := bstep (se 1 (by rfl) ⟨3328694, by rfl⟩ : syracuseStep 4438259 = 6657389) B6657389
theorem B2958839 : Blo 1971435 2958839 := bstep (se 1 (by rfl) ⟨2219129, by rfl⟩ : syracuseStep 2958839 = 4438259) B4438259
theorem B1972559 : Blo 1971435 1972559 := bstep (se 1 (by rfl) ⟨1479419, by rfl⟩ : syracuseStep 1972559 = 2958839) B2958839
theorem B2958845 : Blo 1971435 2958845 := bbase (se 3 (by rfl) ⟨554783, by rfl⟩ : syracuseStep 2958845 = 1109567) (by norm_num)
theorem B1972563 : Blo 1971435 1972563 := bstep (se 1 (by rfl) ⟨1479422, by rfl⟩ : syracuseStep 1972563 = 2958845) B2958845
theorem B4438277 : Blo 1971435 4438277 := bbase (se 4 (by rfl) ⟨416088, by rfl⟩ : syracuseStep 4438277 = 832177) (by norm_num)
theorem B2958851 : Blo 1971435 2958851 := bstep (se 1 (by rfl) ⟨2219138, by rfl⟩ : syracuseStep 2958851 = 4438277) B4438277
theorem B1972567 : Blo 1971435 1972567 := bstep (se 1 (by rfl) ⟨1479425, by rfl⟩ : syracuseStep 1972567 = 2958851) B2958851
theorem B3744805 : Blo 1971435 3744805 := bbase (se 4 (by rfl) ⟨351075, by rfl⟩ : syracuseStep 3744805 = 702151) (by norm_num)
theorem B4993073 : Blo 1971435 4993073 := bstep (se 2 (by rfl) ⟨1872402, by rfl⟩ : syracuseStep 4993073 = 3744805) B3744805
theorem B3328715 : Blo 1971435 3328715 := bstep (se 1 (by rfl) ⟨2496536, by rfl⟩ : syracuseStep 3328715 = 4993073) B4993073
theorem B2219143 : Blo 1971435 2219143 := bstep (se 1 (by rfl) ⟨1664357, by rfl⟩ : syracuseStep 2219143 = 3328715) B3328715
theorem B2958857 : Blo 1971435 2958857 := bstep (se 2 (by rfl) ⟨1109571, by rfl⟩ : syracuseStep 2958857 = 2219143) B2219143
theorem B1972571 : Blo 1971435 1972571 := bstep (se 1 (by rfl) ⟨1479428, by rfl⟩ : syracuseStep 1972571 = 2958857) B2958857
theorem B9986165 : Blo 1971435 9986165 := bbase (se 5 (by rfl) ⟨468101, by rfl⟩ : syracuseStep 9986165 = 936203) (by norm_num)
theorem B6657443 : Blo 1971435 6657443 := bstep (se 1 (by rfl) ⟨4993082, by rfl⟩ : syracuseStep 6657443 = 9986165) B9986165
theorem B4438295 : Blo 1971435 4438295 := bstep (se 1 (by rfl) ⟨3328721, by rfl⟩ : syracuseStep 4438295 = 6657443) B6657443
theorem B2958863 : Blo 1971435 2958863 := bstep (se 1 (by rfl) ⟨2219147, by rfl⟩ : syracuseStep 2958863 = 4438295) B4438295
theorem B1972575 : Blo 1971435 1972575 := bstep (se 1 (by rfl) ⟨1479431, by rfl⟩ : syracuseStep 1972575 = 2958863) B2958863
theorem B2958869 : Blo 1971435 2958869 := bbase (se 6 (by rfl) ⟨69348, by rfl⟩ : syracuseStep 2958869 = 138697) (by norm_num)
theorem B1972579 : Blo 1971435 1972579 := bstep (se 1 (by rfl) ⟨1479434, by rfl⟩ : syracuseStep 1972579 = 2958869) B2958869
theorem B6319397 : Blo 1971435 6319397 := bbase (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) (by norm_num)
theorem B16851725 : Blo 1971435 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B11234483 : Blo 1971435 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B7489655 : Blo 1971435 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B4993103 : Blo 1971435 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B3328735 : Blo 1971435 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B4438313 : Blo 1971435 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B2958875 : Blo 1971435 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B1972583 : Blo 1971435 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B2219161 : Blo 1971435 2219161 := bbase (se 2 (by rfl) ⟨832185, by rfl⟩ : syracuseStep 2219161 = 1664371) (by norm_num)
theorem B2958881 : Blo 1971435 2958881 := bstep (se 2 (by rfl) ⟨1109580, by rfl⟩ : syracuseStep 2958881 = 2219161) B2219161
theorem B1972587 : Blo 1971435 1972587 := bstep (se 1 (by rfl) ⟨1479440, by rfl⟩ : syracuseStep 1972587 = 2958881) B2958881
theorem B7489685 : Blo 1971435 7489685 := bbase (se 6 (by rfl) ⟨175539, by rfl⟩ : syracuseStep 7489685 = 351079) (by norm_num)
theorem B4993123 : Blo 1971435 4993123 := bstep (se 1 (by rfl) ⟨3744842, by rfl⟩ : syracuseStep 4993123 = 7489685) B7489685
theorem B6657497 : Blo 1971435 6657497 := bstep (se 2 (by rfl) ⟨2496561, by rfl⟩ : syracuseStep 6657497 = 4993123) B4993123
theorem B4438331 : Blo 1971435 4438331 := bstep (se 1 (by rfl) ⟨3328748, by rfl⟩ : syracuseStep 4438331 = 6657497) B6657497
theorem B2958887 : Blo 1971435 2958887 := bstep (se 1 (by rfl) ⟨2219165, by rfl⟩ : syracuseStep 2958887 = 4438331) B4438331
theorem B1972591 : Blo 1971435 1972591 := bstep (se 1 (by rfl) ⟨1479443, by rfl⟩ : syracuseStep 1972591 = 2958887) B2958887
theorem B2958893 : Blo 1971435 2958893 := bbase (se 3 (by rfl) ⟨554792, by rfl⟩ : syracuseStep 2958893 = 1109585) (by norm_num)
theorem B1972595 : Blo 1971435 1972595 := bstep (se 1 (by rfl) ⟨1479446, by rfl⟩ : syracuseStep 1972595 = 2958893) B2958893
theorem B4438349 : Blo 1971435 4438349 := bbase (se 3 (by rfl) ⟨832190, by rfl⟩ : syracuseStep 4438349 = 1664381) (by norm_num)
theorem B2958899 : Blo 1971435 2958899 := bstep (se 1 (by rfl) ⟨2219174, by rfl⟩ : syracuseStep 2958899 = 4438349) B4438349
theorem B1972599 : Blo 1971435 1972599 := bstep (se 1 (by rfl) ⟨1479449, by rfl⟩ : syracuseStep 1972599 = 2958899) B2958899
theorem B2496577 : Blo 1971435 2496577 := bbase (se 2 (by rfl) ⟨936216, by rfl⟩ : syracuseStep 2496577 = 1872433) (by norm_num)
theorem B3328769 : Blo 1971435 3328769 := bstep (se 2 (by rfl) ⟨1248288, by rfl⟩ : syracuseStep 3328769 = 2496577) B2496577
theorem B2219179 : Blo 1971435 2219179 := bstep (se 1 (by rfl) ⟨1664384, by rfl⟩ : syracuseStep 2219179 = 3328769) B3328769
theorem B2958905 : Blo 1971435 2958905 := bstep (se 2 (by rfl) ⟨1109589, by rfl⟩ : syracuseStep 2958905 = 2219179) B2219179
theorem B1972603 : Blo 1971435 1972603 := bstep (se 1 (by rfl) ⟨1479452, by rfl⟩ : syracuseStep 1972603 = 2958905) B2958905
theorem B2666029 : Blo 1971435 2666029 := bbase (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) (by norm_num)
theorem B3554705 : Blo 1971435 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B2369803 : Blo 1971435 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B3159737 : Blo 1971435 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B2106491 : Blo 1971435 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B22469237 : Blo 1971435 22469237 := bstep (se 5 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 22469237 = 2106491) B2106491
theorem B14979491 : Blo 1971435 14979491 := bstep (se 1 (by rfl) ⟨11234618, by rfl⟩ : syracuseStep 14979491 = 22469237) B22469237
theorem B9986327 : Blo 1971435 9986327 := bstep (se 1 (by rfl) ⟨7489745, by rfl⟩ : syracuseStep 9986327 = 14979491) B14979491
theorem B6657551 : Blo 1971435 6657551 := bstep (se 1 (by rfl) ⟨4993163, by rfl⟩ : syracuseStep 6657551 = 9986327) B9986327
theorem B4438367 : Blo 1971435 4438367 := bstep (se 1 (by rfl) ⟨3328775, by rfl⟩ : syracuseStep 4438367 = 6657551) B6657551
theorem B2958911 : Blo 1971435 2958911 := bstep (se 1 (by rfl) ⟨2219183, by rfl⟩ : syracuseStep 2958911 = 4438367) B4438367
theorem B1972607 : Blo 1971435 1972607 := bstep (se 1 (by rfl) ⟨1479455, by rfl⟩ : syracuseStep 1972607 = 2958911) B2958911
theorem B2958917 : Blo 1971435 2958917 := bbase (se 4 (by rfl) ⟨277398, by rfl⟩ : syracuseStep 2958917 = 554797) (by norm_num)
theorem B1972611 : Blo 1971435 1972611 := bstep (se 1 (by rfl) ⟨1479458, by rfl⟩ : syracuseStep 1972611 = 2958917) B2958917
theorem B3328789 : Blo 1971435 3328789 := bbase (se 6 (by rfl) ⟨78018, by rfl⟩ : syracuseStep 3328789 = 156037) (by norm_num)
theorem B4438385 : Blo 1971435 4438385 := bstep (se 2 (by rfl) ⟨1664394, by rfl⟩ : syracuseStep 4438385 = 3328789) B3328789
theorem B2958923 : Blo 1971435 2958923 := bstep (se 1 (by rfl) ⟨2219192, by rfl⟩ : syracuseStep 2958923 = 4438385) B4438385
theorem B1972615 : Blo 1971435 1972615 := bstep (se 1 (by rfl) ⟨1479461, by rfl⟩ : syracuseStep 1972615 = 2958923) B2958923
theorem B2219197 : Blo 1971435 2219197 := bbase (se 3 (by rfl) ⟨416099, by rfl⟩ : syracuseStep 2219197 = 832199) (by norm_num)
theorem B2958929 : Blo 1971435 2958929 := bstep (se 2 (by rfl) ⟨1109598, by rfl⟩ : syracuseStep 2958929 = 2219197) B2219197
theorem B1972619 : Blo 1971435 1972619 := bstep (se 1 (by rfl) ⟨1479464, by rfl⟩ : syracuseStep 1972619 = 2958929) B2958929
theorem B6657605 : Blo 1971435 6657605 := bbase (se 4 (by rfl) ⟨624150, by rfl⟩ : syracuseStep 6657605 = 1248301) (by norm_num)
theorem B4438403 : Blo 1971435 4438403 := bstep (se 1 (by rfl) ⟨3328802, by rfl⟩ : syracuseStep 4438403 = 6657605) B6657605
theorem B2958935 : Blo 1971435 2958935 := bstep (se 1 (by rfl) ⟨2219201, by rfl⟩ : syracuseStep 2958935 = 4438403) B4438403
theorem B1972623 : Blo 1971435 1972623 := bstep (se 1 (by rfl) ⟨1479467, by rfl⟩ : syracuseStep 1972623 = 2958935) B2958935
theorem B2958941 : Blo 1971435 2958941 := bbase (se 3 (by rfl) ⟨554801, by rfl⟩ : syracuseStep 2958941 = 1109603) (by norm_num)
theorem B1972627 : Blo 1971435 1972627 := bstep (se 1 (by rfl) ⟨1479470, by rfl⟩ : syracuseStep 1972627 = 2958941) B2958941
theorem B4438421 : Blo 1971435 4438421 := bbase (se 6 (by rfl) ⟨104025, by rfl⟩ : syracuseStep 4438421 = 208051) (by norm_num)
theorem B2958947 : Blo 1971435 2958947 := bstep (se 1 (by rfl) ⟨2219210, by rfl⟩ : syracuseStep 2958947 = 4438421) B4438421
theorem B1972631 : Blo 1971435 1972631 := bstep (se 1 (by rfl) ⟨1479473, by rfl⟩ : syracuseStep 1972631 = 2958947) B2958947
theorem B2369837 : Blo 1971435 2369837 := bbase (se 3 (by rfl) ⟨444344, by rfl⟩ : syracuseStep 2369837 = 888689) (by norm_num)
theorem B6319565 : Blo 1971435 6319565 := bstep (se 3 (by rfl) ⟨1184918, by rfl⟩ : syracuseStep 6319565 = 2369837) B2369837
theorem B4213043 : Blo 1971435 4213043 := bstep (se 1 (by rfl) ⟨3159782, by rfl⟩ : syracuseStep 4213043 = 6319565) B6319565
theorem B2808695 : Blo 1971435 2808695 := bstep (se 1 (by rfl) ⟨2106521, by rfl⟩ : syracuseStep 2808695 = 4213043) B4213043
theorem B7489853 : Blo 1971435 7489853 := bstep (se 3 (by rfl) ⟨1404347, by rfl⟩ : syracuseStep 7489853 = 2808695) B2808695
theorem B4993235 : Blo 1971435 4993235 := bstep (se 1 (by rfl) ⟨3744926, by rfl⟩ : syracuseStep 4993235 = 7489853) B7489853
theorem B3328823 : Blo 1971435 3328823 := bstep (se 1 (by rfl) ⟨2496617, by rfl⟩ : syracuseStep 3328823 = 4993235) B4993235
theorem B2219215 : Blo 1971435 2219215 := bstep (se 1 (by rfl) ⟨1664411, by rfl⟩ : syracuseStep 2219215 = 3328823) B3328823
theorem B2958953 : Blo 1971435 2958953 := bstep (se 2 (by rfl) ⟨1109607, by rfl⟩ : syracuseStep 2958953 = 2219215) B2219215
theorem B1972635 : Blo 1971435 1972635 := bstep (se 1 (by rfl) ⟨1479476, by rfl⟩ : syracuseStep 1972635 = 2958953) B2958953
theorem B8426101 : Blo 1971435 8426101 := bbase (se 5 (by rfl) ⟨394973, by rfl⟩ : syracuseStep 8426101 = 789947) (by norm_num)
theorem B11234801 : Blo 1971435 11234801 := bstep (se 2 (by rfl) ⟨4213050, by rfl⟩ : syracuseStep 11234801 = 8426101) B8426101
theorem B7489867 : Blo 1971435 7489867 := bstep (se 1 (by rfl) ⟨5617400, by rfl⟩ : syracuseStep 7489867 = 11234801) B11234801
theorem B9986489 : Blo 1971435 9986489 := bstep (se 2 (by rfl) ⟨3744933, by rfl⟩ : syracuseStep 9986489 = 7489867) B7489867
theorem B6657659 : Blo 1971435 6657659 := bstep (se 1 (by rfl) ⟨4993244, by rfl⟩ : syracuseStep 6657659 = 9986489) B9986489
theorem B4438439 : Blo 1971435 4438439 := bstep (se 1 (by rfl) ⟨3328829, by rfl⟩ : syracuseStep 4438439 = 6657659) B6657659
theorem B2958959 : Blo 1971435 2958959 := bstep (se 1 (by rfl) ⟨2219219, by rfl⟩ : syracuseStep 2958959 = 4438439) B4438439
theorem B1972639 : Blo 1971435 1972639 := bstep (se 1 (by rfl) ⟨1479479, by rfl⟩ : syracuseStep 1972639 = 2958959) B2958959
theorem B2958965 : Blo 1971435 2958965 := bbase (se 5 (by rfl) ⟨138701, by rfl⟩ : syracuseStep 2958965 = 277403) (by norm_num)
theorem B1972643 : Blo 1971435 1972643 := bstep (se 1 (by rfl) ⟨1479482, by rfl⟩ : syracuseStep 1972643 = 2958965) B2958965
theorem B3744949 : Blo 1971435 3744949 := bbase (se 5 (by rfl) ⟨175544, by rfl⟩ : syracuseStep 3744949 = 351089) (by norm_num)
theorem B4993265 : Blo 1971435 4993265 := bstep (se 2 (by rfl) ⟨1872474, by rfl⟩ : syracuseStep 4993265 = 3744949) B3744949
theorem B3328843 : Blo 1971435 3328843 := bstep (se 1 (by rfl) ⟨2496632, by rfl⟩ : syracuseStep 3328843 = 4993265) B4993265
theorem B4438457 : Blo 1971435 4438457 := bstep (se 2 (by rfl) ⟨1664421, by rfl⟩ : syracuseStep 4438457 = 3328843) B3328843
theorem B2958971 : Blo 1971435 2958971 := bstep (se 1 (by rfl) ⟨2219228, by rfl⟩ : syracuseStep 2958971 = 4438457) B4438457
theorem B1972647 : Blo 1971435 1972647 := bstep (se 1 (by rfl) ⟨1479485, by rfl⟩ : syracuseStep 1972647 = 2958971) B2958971
theorem B2219233 : Blo 1971435 2219233 := bbase (se 2 (by rfl) ⟨832212, by rfl⟩ : syracuseStep 2219233 = 1664425) (by norm_num)
theorem B2958977 : Blo 1971435 2958977 := bstep (se 2 (by rfl) ⟨1109616, by rfl⟩ : syracuseStep 2958977 = 2219233) B2219233
theorem B1972651 : Blo 1971435 1972651 := bstep (se 1 (by rfl) ⟨1479488, by rfl⟩ : syracuseStep 1972651 = 2958977) B2958977
theorem B4993285 : Blo 1971435 4993285 := bbase (se 4 (by rfl) ⟨468120, by rfl⟩ : syracuseStep 4993285 = 936241) (by norm_num)
theorem B6657713 : Blo 1971435 6657713 := bstep (se 2 (by rfl) ⟨2496642, by rfl⟩ : syracuseStep 6657713 = 4993285) B4993285
theorem B4438475 : Blo 1971435 4438475 := bstep (se 1 (by rfl) ⟨3328856, by rfl⟩ : syracuseStep 4438475 = 6657713) B6657713
theorem B2958983 : Blo 1971435 2958983 := bstep (se 1 (by rfl) ⟨2219237, by rfl⟩ : syracuseStep 2958983 = 4438475) B4438475
theorem B1972655 : Blo 1971435 1972655 := bstep (se 1 (by rfl) ⟨1479491, by rfl⟩ : syracuseStep 1972655 = 2958983) B2958983
theorem B2958989 : Blo 1971435 2958989 := bbase (se 3 (by rfl) ⟨554810, by rfl⟩ : syracuseStep 2958989 = 1109621) (by norm_num)
theorem B1972659 : Blo 1971435 1972659 := bstep (se 1 (by rfl) ⟨1479494, by rfl⟩ : syracuseStep 1972659 = 2958989) B2958989
theorem B4438493 : Blo 1971435 4438493 := bbase (se 3 (by rfl) ⟨832217, by rfl⟩ : syracuseStep 4438493 = 1664435) (by norm_num)
theorem B2958995 : Blo 1971435 2958995 := bstep (se 1 (by rfl) ⟨2219246, by rfl⟩ : syracuseStep 2958995 = 4438493) B4438493
theorem B1972663 : Blo 1971435 1972663 := bstep (se 1 (by rfl) ⟨1479497, by rfl⟩ : syracuseStep 1972663 = 2958995) B2958995
theorem B3328877 : Blo 1971435 3328877 := bbase (se 3 (by rfl) ⟨624164, by rfl⟩ : syracuseStep 3328877 = 1248329) (by norm_num)
theorem B2219251 : Blo 1971435 2219251 := bstep (se 1 (by rfl) ⟨1664438, by rfl⟩ : syracuseStep 2219251 = 3328877) B3328877
theorem B2959001 : Blo 1971435 2959001 := bstep (se 2 (by rfl) ⟨1109625, by rfl⟩ : syracuseStep 2959001 = 2219251) B2219251
theorem B1972667 : Blo 1971435 1972667 := bstep (se 1 (by rfl) ⟨1479500, by rfl⟩ : syracuseStep 1972667 = 2959001) B2959001
theorem B13497205 : Blo 1971435 13497205 := bbase (se 5 (by rfl) ⟨632681, by rfl⟩ : syracuseStep 13497205 = 1265363) (by norm_num)
theorem B17996273 : Blo 1971435 17996273 := bstep (se 2 (by rfl) ⟨6748602, by rfl⟩ : syracuseStep 17996273 = 13497205) B13497205
theorem B11997515 : Blo 1971435 11997515 := bstep (se 1 (by rfl) ⟨8998136, by rfl⟩ : syracuseStep 11997515 = 17996273) B17996273
theorem B31993373 : Blo 1971435 31993373 := bstep (se 3 (by rfl) ⟨5998757, by rfl⟩ : syracuseStep 31993373 = 11997515) B11997515
theorem B21328915 : Blo 1971435 21328915 := bstep (se 1 (by rfl) ⟨15996686, by rfl⟩ : syracuseStep 21328915 = 31993373) B31993373
theorem B28438553 : Blo 1971435 28438553 := bstep (se 2 (by rfl) ⟨10664457, by rfl⟩ : syracuseStep 28438553 = 21328915) B21328915
theorem B18959035 : Blo 1971435 18959035 := bstep (se 1 (by rfl) ⟨14219276, by rfl⟩ : syracuseStep 18959035 = 28438553) B28438553
theorem B25278713 : Blo 1971435 25278713 := bstep (se 2 (by rfl) ⟨9479517, by rfl⟩ : syracuseStep 25278713 = 18959035) B18959035
theorem B16852475 : Blo 1971435 16852475 := bstep (se 1 (by rfl) ⟨12639356, by rfl⟩ : syracuseStep 16852475 = 25278713) B25278713
theorem B11234983 : Blo 1971435 11234983 := bstep (se 1 (by rfl) ⟨8426237, by rfl⟩ : syracuseStep 11234983 = 16852475) B16852475
theorem B14979977 : Blo 1971435 14979977 := bstep (se 2 (by rfl) ⟨5617491, by rfl⟩ : syracuseStep 14979977 = 11234983) B11234983
theorem B9986651 : Blo 1971435 9986651 := bstep (se 1 (by rfl) ⟨7489988, by rfl⟩ : syracuseStep 9986651 = 14979977) B14979977
theorem B6657767 : Blo 1971435 6657767 := bstep (se 1 (by rfl) ⟨4993325, by rfl⟩ : syracuseStep 6657767 = 9986651) B9986651
theorem B4438511 : Blo 1971435 4438511 := bstep (se 1 (by rfl) ⟨3328883, by rfl⟩ : syracuseStep 4438511 = 6657767) B6657767
theorem B2959007 : Blo 1971435 2959007 := bstep (se 1 (by rfl) ⟨2219255, by rfl⟩ : syracuseStep 2959007 = 4438511) B4438511
theorem B1972671 : Blo 1971435 1972671 := bstep (se 1 (by rfl) ⟨1479503, by rfl⟩ : syracuseStep 1972671 = 2959007) B2959007
theorem B2959013 : Blo 1971435 2959013 := bbase (se 4 (by rfl) ⟨277407, by rfl⟩ : syracuseStep 2959013 = 554815) (by norm_num)
theorem B1972675 : Blo 1971435 1972675 := bstep (se 1 (by rfl) ⟨1479506, by rfl⟩ : syracuseStep 1972675 = 2959013) B2959013
theorem B2496673 : Blo 1971435 2496673 := bbase (se 2 (by rfl) ⟨936252, by rfl⟩ : syracuseStep 2496673 = 1872505) (by norm_num)
theorem B3328897 : Blo 1971435 3328897 := bstep (se 2 (by rfl) ⟨1248336, by rfl⟩ : syracuseStep 3328897 = 2496673) B2496673
theorem B4438529 : Blo 1971435 4438529 := bstep (se 2 (by rfl) ⟨1664448, by rfl⟩ : syracuseStep 4438529 = 3328897) B3328897
theorem B2959019 : Blo 1971435 2959019 := bstep (se 1 (by rfl) ⟨2219264, by rfl⟩ : syracuseStep 2959019 = 4438529) B4438529
theorem B1972679 : Blo 1971435 1972679 := bstep (se 1 (by rfl) ⟨1479509, by rfl⟩ : syracuseStep 1972679 = 2959019) B2959019
theorem B2219269 : Blo 1971435 2219269 := bbase (se 4 (by rfl) ⟨208056, by rfl⟩ : syracuseStep 2219269 = 416113) (by norm_num)
theorem B2959025 : Blo 1971435 2959025 := bstep (se 2 (by rfl) ⟨1109634, by rfl⟩ : syracuseStep 2959025 = 2219269) B2219269
theorem B1972683 : Blo 1971435 1972683 := bstep (se 1 (by rfl) ⟨1479512, by rfl⟩ : syracuseStep 1972683 = 2959025) B2959025
theorem B2106577 : Blo 1971435 2106577 := bbase (se 2 (by rfl) ⟨789966, by rfl⟩ : syracuseStep 2106577 = 1579933) (by norm_num)
theorem B2808769 : Blo 1971435 2808769 := bstep (se 2 (by rfl) ⟨1053288, by rfl⟩ : syracuseStep 2808769 = 2106577) B2106577
theorem B3745025 : Blo 1971435 3745025 := bstep (se 2 (by rfl) ⟨1404384, by rfl⟩ : syracuseStep 3745025 = 2808769) B2808769
theorem B2496683 : Blo 1971435 2496683 := bstep (se 1 (by rfl) ⟨1872512, by rfl⟩ : syracuseStep 2496683 = 3745025) B3745025
theorem B6657821 : Blo 1971435 6657821 := bstep (se 3 (by rfl) ⟨1248341, by rfl⟩ : syracuseStep 6657821 = 2496683) B2496683
theorem B4438547 : Blo 1971435 4438547 := bstep (se 1 (by rfl) ⟨3328910, by rfl⟩ : syracuseStep 4438547 = 6657821) B6657821
theorem B2959031 : Blo 1971435 2959031 := bstep (se 1 (by rfl) ⟨2219273, by rfl⟩ : syracuseStep 2959031 = 4438547) B4438547
theorem B1972687 : Blo 1971435 1972687 := bstep (se 1 (by rfl) ⟨1479515, by rfl⟩ : syracuseStep 1972687 = 2959031) B2959031
theorem B2959037 : Blo 1971435 2959037 := bbase (se 3 (by rfl) ⟨554819, by rfl⟩ : syracuseStep 2959037 = 1109639) (by norm_num)
theorem B1972691 : Blo 1971435 1972691 := bstep (se 1 (by rfl) ⟨1479518, by rfl⟩ : syracuseStep 1972691 = 2959037) B2959037
theorem B4438565 : Blo 1971435 4438565 := bbase (se 4 (by rfl) ⟨416115, by rfl⟩ : syracuseStep 4438565 = 832231) (by norm_num)
theorem B2959043 : Blo 1971435 2959043 := bstep (se 1 (by rfl) ⟨2219282, by rfl⟩ : syracuseStep 2959043 = 4438565) B4438565
theorem B1972695 : Blo 1971435 1972695 := bstep (se 1 (by rfl) ⟨1479521, by rfl⟩ : syracuseStep 1972695 = 2959043) B2959043
theorem B4993397 : Blo 1971435 4993397 := bbase (se 5 (by rfl) ⟨234065, by rfl⟩ : syracuseStep 4993397 = 468131) (by norm_num)
theorem B3328931 : Blo 1971435 3328931 := bstep (se 1 (by rfl) ⟨2496698, by rfl⟩ : syracuseStep 3328931 = 4993397) B4993397
theorem B2219287 : Blo 1971435 2219287 := bstep (se 1 (by rfl) ⟨1664465, by rfl⟩ : syracuseStep 2219287 = 3328931) B3328931
theorem B2959049 : Blo 1971435 2959049 := bstep (se 2 (by rfl) ⟨1109643, by rfl⟩ : syracuseStep 2959049 = 2219287) B2219287
theorem B1972699 : Blo 1971435 1972699 := bstep (se 1 (by rfl) ⟨1479524, by rfl⟩ : syracuseStep 1972699 = 2959049) B2959049
theorem B14219509 : Blo 1971435 14219509 := bbase (se 5 (by rfl) ⟨666539, by rfl⟩ : syracuseStep 14219509 = 1333079) (by norm_num)
theorem B18959345 : Blo 1971435 18959345 := bstep (se 2 (by rfl) ⟨7109754, by rfl⟩ : syracuseStep 18959345 = 14219509) B14219509
theorem B12639563 : Blo 1971435 12639563 := bstep (se 1 (by rfl) ⟨9479672, by rfl⟩ : syracuseStep 12639563 = 18959345) B18959345
theorem B8426375 : Blo 1971435 8426375 := bstep (se 1 (by rfl) ⟨6319781, by rfl⟩ : syracuseStep 8426375 = 12639563) B12639563
theorem B5617583 : Blo 1971435 5617583 := bstep (se 1 (by rfl) ⟨4213187, by rfl⟩ : syracuseStep 5617583 = 8426375) B8426375
theorem B3745055 : Blo 1971435 3745055 := bstep (se 1 (by rfl) ⟨2808791, by rfl⟩ : syracuseStep 3745055 = 5617583) B5617583
theorem B9986813 : Blo 1971435 9986813 := bstep (se 3 (by rfl) ⟨1872527, by rfl⟩ : syracuseStep 9986813 = 3745055) B3745055
theorem B6657875 : Blo 1971435 6657875 := bstep (se 1 (by rfl) ⟨4993406, by rfl⟩ : syracuseStep 6657875 = 9986813) B9986813
theorem B4438583 : Blo 1971435 4438583 := bstep (se 1 (by rfl) ⟨3328937, by rfl⟩ : syracuseStep 4438583 = 6657875) B6657875
theorem B2959055 : Blo 1971435 2959055 := bstep (se 1 (by rfl) ⟨2219291, by rfl⟩ : syracuseStep 2959055 = 4438583) B4438583
theorem B1972703 : Blo 1971435 1972703 := bstep (se 1 (by rfl) ⟨1479527, by rfl⟩ : syracuseStep 1972703 = 2959055) B2959055
theorem B2959061 : Blo 1971435 2959061 := bbase (se 7 (by rfl) ⟨34676, by rfl⟩ : syracuseStep 2959061 = 69353) (by norm_num)
theorem B1972707 : Blo 1971435 1972707 := bstep (se 1 (by rfl) ⟨1479530, by rfl⟩ : syracuseStep 1972707 = 2959061) B2959061
theorem B4213205 : Blo 1971435 4213205 := bbase (se 7 (by rfl) ⟨49373, by rfl⟩ : syracuseStep 4213205 = 98747) (by norm_num)
theorem B2808803 : Blo 1971435 2808803 := bstep (se 1 (by rfl) ⟨2106602, by rfl⟩ : syracuseStep 2808803 = 4213205) B4213205
theorem B7490141 : Blo 1971435 7490141 := bstep (se 3 (by rfl) ⟨1404401, by rfl⟩ : syracuseStep 7490141 = 2808803) B2808803
theorem B4993427 : Blo 1971435 4993427 := bstep (se 1 (by rfl) ⟨3745070, by rfl⟩ : syracuseStep 4993427 = 7490141) B7490141
theorem B3328951 : Blo 1971435 3328951 := bstep (se 1 (by rfl) ⟨2496713, by rfl⟩ : syracuseStep 3328951 = 4993427) B4993427
theorem B4438601 : Blo 1971435 4438601 := bstep (se 2 (by rfl) ⟨1664475, by rfl⟩ : syracuseStep 4438601 = 3328951) B3328951
theorem B2959067 : Blo 1971435 2959067 := bstep (se 1 (by rfl) ⟨2219300, by rfl⟩ : syracuseStep 2959067 = 4438601) B4438601
theorem B1972711 : Blo 1971435 1972711 := bstep (se 1 (by rfl) ⟨1479533, by rfl⟩ : syracuseStep 1972711 = 2959067) B2959067
theorem B2219305 : Blo 1971435 2219305 := bbase (se 2 (by rfl) ⟨832239, by rfl⟩ : syracuseStep 2219305 = 1664479) (by norm_num)
theorem B2959073 : Blo 1971435 2959073 := bstep (se 2 (by rfl) ⟨1109652, by rfl⟩ : syracuseStep 2959073 = 2219305) B2219305
theorem B1972715 : Blo 1971435 1972715 := bstep (se 1 (by rfl) ⟨1479536, by rfl⟩ : syracuseStep 1972715 = 2959073) B2959073
theorem B9479749 : Blo 1971435 9479749 := bbase (se 4 (by rfl) ⟨888726, by rfl⟩ : syracuseStep 9479749 = 1777453) (by norm_num)
theorem B12639665 : Blo 1971435 12639665 := bstep (se 2 (by rfl) ⟨4739874, by rfl⟩ : syracuseStep 12639665 = 9479749) B9479749
theorem B8426443 : Blo 1971435 8426443 := bstep (se 1 (by rfl) ⟨6319832, by rfl⟩ : syracuseStep 8426443 = 12639665) B12639665
theorem B11235257 : Blo 1971435 11235257 := bstep (se 2 (by rfl) ⟨4213221, by rfl⟩ : syracuseStep 11235257 = 8426443) B8426443
theorem B7490171 : Blo 1971435 7490171 := bstep (se 1 (by rfl) ⟨5617628, by rfl⟩ : syracuseStep 7490171 = 11235257) B11235257
theorem B4993447 : Blo 1971435 4993447 := bstep (se 1 (by rfl) ⟨3745085, by rfl⟩ : syracuseStep 4993447 = 7490171) B7490171
theorem B6657929 : Blo 1971435 6657929 := bstep (se 2 (by rfl) ⟨2496723, by rfl⟩ : syracuseStep 6657929 = 4993447) B4993447
theorem B4438619 : Blo 1971435 4438619 := bstep (se 1 (by rfl) ⟨3328964, by rfl⟩ : syracuseStep 4438619 = 6657929) B6657929
theorem B2959079 : Blo 1971435 2959079 := bstep (se 1 (by rfl) ⟨2219309, by rfl⟩ : syracuseStep 2959079 = 4438619) B4438619
theorem B1972719 : Blo 1971435 1972719 := bstep (se 1 (by rfl) ⟨1479539, by rfl⟩ : syracuseStep 1972719 = 2959079) B2959079
theorem B2959085 : Blo 1971435 2959085 := bbase (se 3 (by rfl) ⟨554828, by rfl⟩ : syracuseStep 2959085 = 1109657) (by norm_num)
theorem B1972723 : Blo 1971435 1972723 := bstep (se 1 (by rfl) ⟨1479542, by rfl⟩ : syracuseStep 1972723 = 2959085) B2959085
theorem B4438637 : Blo 1971435 4438637 := bbase (se 3 (by rfl) ⟨832244, by rfl⟩ : syracuseStep 4438637 = 1664489) (by norm_num)
theorem B2959091 : Blo 1971435 2959091 := bstep (se 1 (by rfl) ⟨2219318, by rfl⟩ : syracuseStep 2959091 = 4438637) B4438637
theorem B1972727 : Blo 1971435 1972727 := bstep (se 1 (by rfl) ⟨1479545, by rfl⟩ : syracuseStep 1972727 = 2959091) B2959091
theorem B3745109 : Blo 1971435 3745109 := bbase (se 12 (by rfl) ⟨1371, by rfl⟩ : syracuseStep 3745109 = 2743) (by norm_num)
theorem B2496739 : Blo 1971435 2496739 := bstep (se 1 (by rfl) ⟨1872554, by rfl⟩ : syracuseStep 2496739 = 3745109) B3745109
theorem B3328985 : Blo 1971435 3328985 := bstep (se 2 (by rfl) ⟨1248369, by rfl⟩ : syracuseStep 3328985 = 2496739) B2496739
theorem B2219323 : Blo 1971435 2219323 := bstep (se 1 (by rfl) ⟨1664492, by rfl⟩ : syracuseStep 2219323 = 3328985) B3328985
theorem B2959097 : Blo 1971435 2959097 := bstep (se 2 (by rfl) ⟨1109661, by rfl⟩ : syracuseStep 2959097 = 2219323) B2219323
theorem B1972731 : Blo 1971435 1972731 := bstep (se 1 (by rfl) ⟨1479548, by rfl⟩ : syracuseStep 1972731 = 2959097) B2959097
theorem B15997205 : Blo 1971435 15997205 := bbase (se 6 (by rfl) ⟨374934, by rfl⟩ : syracuseStep 15997205 = 749869) (by norm_num)
theorem B10664803 : Blo 1971435 10664803 := bstep (se 1 (by rfl) ⟨7998602, by rfl⟩ : syracuseStep 10664803 = 15997205) B15997205
theorem B56878949 : Blo 1971435 56878949 := bstep (se 4 (by rfl) ⟨5332401, by rfl⟩ : syracuseStep 56878949 = 10664803) B10664803
theorem B37919299 : Blo 1971435 37919299 := bstep (se 1 (by rfl) ⟨28439474, by rfl⟩ : syracuseStep 37919299 = 56878949) B56878949
theorem B50559065 : Blo 1971435 50559065 := bstep (se 2 (by rfl) ⟨18959649, by rfl⟩ : syracuseStep 50559065 = 37919299) B37919299
theorem B33706043 : Blo 1971435 33706043 := bstep (se 1 (by rfl) ⟨25279532, by rfl⟩ : syracuseStep 33706043 = 50559065) B50559065
theorem B22470695 : Blo 1971435 22470695 := bstep (se 1 (by rfl) ⟨16853021, by rfl⟩ : syracuseStep 22470695 = 33706043) B33706043
theorem B14980463 : Blo 1971435 14980463 := bstep (se 1 (by rfl) ⟨11235347, by rfl⟩ : syracuseStep 14980463 = 22470695) B22470695
theorem B9986975 : Blo 1971435 9986975 := bstep (se 1 (by rfl) ⟨7490231, by rfl⟩ : syracuseStep 9986975 = 14980463) B14980463
theorem B6657983 : Blo 1971435 6657983 := bstep (se 1 (by rfl) ⟨4993487, by rfl⟩ : syracuseStep 6657983 = 9986975) B9986975
theorem B4438655 : Blo 1971435 4438655 := bstep (se 1 (by rfl) ⟨3328991, by rfl⟩ : syracuseStep 4438655 = 6657983) B6657983
theorem B2959103 : Blo 1971435 2959103 := bstep (se 1 (by rfl) ⟨2219327, by rfl⟩ : syracuseStep 2959103 = 4438655) B4438655
theorem B1972735 : Blo 1971435 1972735 := bstep (se 1 (by rfl) ⟨1479551, by rfl⟩ : syracuseStep 1972735 = 2959103) B2959103
theorem B2959109 : Blo 1971435 2959109 := bbase (se 4 (by rfl) ⟨277416, by rfl⟩ : syracuseStep 2959109 = 554833) (by norm_num)
theorem B1972739 : Blo 1971435 1972739 := bstep (se 1 (by rfl) ⟨1479554, by rfl⟩ : syracuseStep 1972739 = 2959109) B2959109
theorem B3329005 : Blo 1971435 3329005 := bbase (se 3 (by rfl) ⟨624188, by rfl⟩ : syracuseStep 3329005 = 1248377) (by norm_num)
theorem B4438673 : Blo 1971435 4438673 := bstep (se 2 (by rfl) ⟨1664502, by rfl⟩ : syracuseStep 4438673 = 3329005) B3329005
theorem B2959115 : Blo 1971435 2959115 := bstep (se 1 (by rfl) ⟨2219336, by rfl⟩ : syracuseStep 2959115 = 4438673) B4438673
theorem B1972743 : Blo 1971435 1972743 := bstep (se 1 (by rfl) ⟨1479557, by rfl⟩ : syracuseStep 1972743 = 2959115) B2959115
theorem B2219341 : Blo 1971435 2219341 := bbase (se 3 (by rfl) ⟨416126, by rfl⟩ : syracuseStep 2219341 = 832253) (by norm_num)
theorem B2959121 : Blo 1971435 2959121 := bstep (se 2 (by rfl) ⟨1109670, by rfl⟩ : syracuseStep 2959121 = 2219341) B2219341
theorem B1972747 : Blo 1971435 1972747 := bstep (se 1 (by rfl) ⟨1479560, by rfl⟩ : syracuseStep 1972747 = 2959121) B2959121
theorem B6658037 : Blo 1971435 6658037 := bbase (se 5 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 6658037 = 624191) (by norm_num)
theorem B4438691 : Blo 1971435 4438691 := bstep (se 1 (by rfl) ⟨3329018, by rfl⟩ : syracuseStep 4438691 = 6658037) B6658037
theorem B2959127 : Blo 1971435 2959127 := bstep (se 1 (by rfl) ⟨2219345, by rfl⟩ : syracuseStep 2959127 = 4438691) B4438691
theorem B1972751 : Blo 1971435 1972751 := bstep (se 1 (by rfl) ⟨1479563, by rfl⟩ : syracuseStep 1972751 = 2959127) B2959127
theorem B2959133 : Blo 1971435 2959133 := bbase (se 3 (by rfl) ⟨554837, by rfl⟩ : syracuseStep 2959133 = 1109675) (by norm_num)
theorem B1972755 : Blo 1971435 1972755 := bstep (se 1 (by rfl) ⟨1479566, by rfl⟩ : syracuseStep 1972755 = 2959133) B2959133
theorem B4438709 : Blo 1971435 4438709 := bbase (se 5 (by rfl) ⟨208064, by rfl⟩ : syracuseStep 4438709 = 416129) (by norm_num)
theorem B2959139 : Blo 1971435 2959139 := bstep (se 1 (by rfl) ⟨2219354, by rfl⟩ : syracuseStep 2959139 = 4438709) B4438709
theorem B1972759 : Blo 1971435 1972759 := bstep (se 1 (by rfl) ⟨1479569, by rfl⟩ : syracuseStep 1972759 = 2959139) B2959139
theorem B11235509 : Blo 1971435 11235509 := bbase (se 5 (by rfl) ⟨526664, by rfl⟩ : syracuseStep 11235509 = 1053329) (by norm_num)
theorem B7490339 : Blo 1971435 7490339 := bstep (se 1 (by rfl) ⟨5617754, by rfl⟩ : syracuseStep 7490339 = 11235509) B11235509
theorem B4993559 : Blo 1971435 4993559 := bstep (se 1 (by rfl) ⟨3745169, by rfl⟩ : syracuseStep 4993559 = 7490339) B7490339
theorem B3329039 : Blo 1971435 3329039 := bstep (se 1 (by rfl) ⟨2496779, by rfl⟩ : syracuseStep 3329039 = 4993559) B4993559
theorem B2219359 : Blo 1971435 2219359 := bstep (se 1 (by rfl) ⟨1664519, by rfl⟩ : syracuseStep 2219359 = 3329039) B3329039
theorem B2959145 : Blo 1971435 2959145 := bstep (se 2 (by rfl) ⟨1109679, by rfl⟩ : syracuseStep 2959145 = 2219359) B2219359
theorem B1972763 : Blo 1971435 1972763 := bstep (se 1 (by rfl) ⟨1479572, by rfl⟩ : syracuseStep 1972763 = 2959145) B2959145
theorem B5617765 : Blo 1971435 5617765 := bbase (se 4 (by rfl) ⟨526665, by rfl⟩ : syracuseStep 5617765 = 1053331) (by norm_num)
theorem B7490353 : Blo 1971435 7490353 := bstep (se 2 (by rfl) ⟨2808882, by rfl⟩ : syracuseStep 7490353 = 5617765) B5617765
theorem B9987137 : Blo 1971435 9987137 := bstep (se 2 (by rfl) ⟨3745176, by rfl⟩ : syracuseStep 9987137 = 7490353) B7490353
theorem B6658091 : Blo 1971435 6658091 := bstep (se 1 (by rfl) ⟨4993568, by rfl⟩ : syracuseStep 6658091 = 9987137) B9987137
theorem B4438727 : Blo 1971435 4438727 := bstep (se 1 (by rfl) ⟨3329045, by rfl⟩ : syracuseStep 4438727 = 6658091) B6658091
theorem B2959151 : Blo 1971435 2959151 := bstep (se 1 (by rfl) ⟨2219363, by rfl⟩ : syracuseStep 2959151 = 4438727) B4438727
theorem B1972767 : Blo 1971435 1972767 := bstep (se 1 (by rfl) ⟨1479575, by rfl⟩ : syracuseStep 1972767 = 2959151) B2959151
theorem B2959157 : Blo 1971435 2959157 := bbase (se 5 (by rfl) ⟨138710, by rfl⟩ : syracuseStep 2959157 = 277421) (by norm_num)
theorem B1972771 : Blo 1971435 1972771 := bstep (se 1 (by rfl) ⟨1479578, by rfl⟩ : syracuseStep 1972771 = 2959157) B2959157
theorem B4993589 : Blo 1971435 4993589 := bbase (se 5 (by rfl) ⟨234074, by rfl⟩ : syracuseStep 4993589 = 468149) (by norm_num)
theorem B3329059 : Blo 1971435 3329059 := bstep (se 1 (by rfl) ⟨2496794, by rfl⟩ : syracuseStep 3329059 = 4993589) B4993589
theorem B4438745 : Blo 1971435 4438745 := bstep (se 2 (by rfl) ⟨1664529, by rfl⟩ : syracuseStep 4438745 = 3329059) B3329059
theorem B2959163 : Blo 1971435 2959163 := bstep (se 1 (by rfl) ⟨2219372, by rfl⟩ : syracuseStep 2959163 = 4438745) B4438745
theorem B1972775 : Blo 1971435 1972775 := bstep (se 1 (by rfl) ⟨1479581, by rfl⟩ : syracuseStep 1972775 = 2959163) B2959163
theorem B2219377 : Blo 1971435 2219377 := bbase (se 2 (by rfl) ⟨832266, by rfl⟩ : syracuseStep 2219377 = 1664533) (by norm_num)
theorem B2959169 : Blo 1971435 2959169 := bstep (se 2 (by rfl) ⟨1109688, by rfl⟩ : syracuseStep 2959169 = 2219377) B2219377
theorem B1972779 : Blo 1971435 1972779 := bstep (se 1 (by rfl) ⟨1479584, by rfl⟩ : syracuseStep 1972779 = 2959169) B2959169
theorem B4740029 : Blo 1971435 4740029 := bbase (se 3 (by rfl) ⟨888755, by rfl⟩ : syracuseStep 4740029 = 1777511) (by norm_num)
theorem B3160019 : Blo 1971435 3160019 := bstep (se 1 (by rfl) ⟨2370014, by rfl⟩ : syracuseStep 3160019 = 4740029) B4740029
theorem B8426717 : Blo 1971435 8426717 := bstep (se 3 (by rfl) ⟨1580009, by rfl⟩ : syracuseStep 8426717 = 3160019) B3160019
theorem B5617811 : Blo 1971435 5617811 := bstep (se 1 (by rfl) ⟨4213358, by rfl⟩ : syracuseStep 5617811 = 8426717) B8426717
theorem B3745207 : Blo 1971435 3745207 := bstep (se 1 (by rfl) ⟨2808905, by rfl⟩ : syracuseStep 3745207 = 5617811) B5617811
theorem B4993609 : Blo 1971435 4993609 := bstep (se 2 (by rfl) ⟨1872603, by rfl⟩ : syracuseStep 4993609 = 3745207) B3745207
theorem B6658145 : Blo 1971435 6658145 := bstep (se 2 (by rfl) ⟨2496804, by rfl⟩ : syracuseStep 6658145 = 4993609) B4993609
theorem B4438763 : Blo 1971435 4438763 := bstep (se 1 (by rfl) ⟨3329072, by rfl⟩ : syracuseStep 4438763 = 6658145) B6658145
theorem B2959175 : Blo 1971435 2959175 := bstep (se 1 (by rfl) ⟨2219381, by rfl⟩ : syracuseStep 2959175 = 4438763) B4438763
theorem B1972783 : Blo 1971435 1972783 := bstep (se 1 (by rfl) ⟨1479587, by rfl⟩ : syracuseStep 1972783 = 2959175) B2959175
theorem B2959181 : Blo 1971435 2959181 := bbase (se 3 (by rfl) ⟨554846, by rfl⟩ : syracuseStep 2959181 = 1109693) (by norm_num)
theorem B1972787 : Blo 1971435 1972787 := bstep (se 1 (by rfl) ⟨1479590, by rfl⟩ : syracuseStep 1972787 = 2959181) B2959181
theorem B4438781 : Blo 1971435 4438781 := bbase (se 3 (by rfl) ⟨832271, by rfl⟩ : syracuseStep 4438781 = 1664543) (by norm_num)
theorem B2959187 : Blo 1971435 2959187 := bstep (se 1 (by rfl) ⟨2219390, by rfl⟩ : syracuseStep 2959187 = 4438781) B4438781
theorem B1972791 : Blo 1971435 1972791 := bstep (se 1 (by rfl) ⟨1479593, by rfl⟩ : syracuseStep 1972791 = 2959187) B2959187
theorem B3329093 : Blo 1971435 3329093 := bbase (se 4 (by rfl) ⟨312102, by rfl⟩ : syracuseStep 3329093 = 624205) (by norm_num)
theorem B2219395 : Blo 1971435 2219395 := bstep (se 1 (by rfl) ⟨1664546, by rfl⟩ : syracuseStep 2219395 = 3329093) B3329093
theorem B2959193 : Blo 1971435 2959193 := bstep (se 2 (by rfl) ⟨1109697, by rfl⟩ : syracuseStep 2959193 = 2219395) B2219395
theorem B1972795 : Blo 1971435 1972795 := bstep (se 1 (by rfl) ⟨1479596, by rfl⟩ : syracuseStep 1972795 = 2959193) B2959193
theorem B14980949 : Blo 1971435 14980949 := bbase (se 9 (by rfl) ⟨43889, by rfl⟩ : syracuseStep 14980949 = 87779) (by norm_num)
theorem B9987299 : Blo 1971435 9987299 := bstep (se 1 (by rfl) ⟨7490474, by rfl⟩ : syracuseStep 9987299 = 14980949) B14980949
theorem B6658199 : Blo 1971435 6658199 := bstep (se 1 (by rfl) ⟨4993649, by rfl⟩ : syracuseStep 6658199 = 9987299) B9987299
theorem B4438799 : Blo 1971435 4438799 := bstep (se 1 (by rfl) ⟨3329099, by rfl⟩ : syracuseStep 4438799 = 6658199) B6658199
theorem B2959199 : Blo 1971435 2959199 := bstep (se 1 (by rfl) ⟨2219399, by rfl⟩ : syracuseStep 2959199 = 4438799) B4438799
theorem B1972799 : Blo 1971435 1972799 := bstep (se 1 (by rfl) ⟨1479599, by rfl⟩ : syracuseStep 1972799 = 2959199) B2959199
theorem B2959205 : Blo 1971435 2959205 := bbase (se 4 (by rfl) ⟨277425, by rfl⟩ : syracuseStep 2959205 = 554851) (by norm_num)
theorem B1972803 : Blo 1971435 1972803 := bstep (se 1 (by rfl) ⟨1479602, by rfl⟩ : syracuseStep 1972803 = 2959205) B2959205
theorem B3745253 : Blo 1971435 3745253 := bbase (se 4 (by rfl) ⟨351117, by rfl⟩ : syracuseStep 3745253 = 702235) (by norm_num)
theorem B2496835 : Blo 1971435 2496835 := bstep (se 1 (by rfl) ⟨1872626, by rfl⟩ : syracuseStep 2496835 = 3745253) B3745253
theorem B3329113 : Blo 1971435 3329113 := bstep (se 2 (by rfl) ⟨1248417, by rfl⟩ : syracuseStep 3329113 = 2496835) B2496835
theorem B4438817 : Blo 1971435 4438817 := bstep (se 2 (by rfl) ⟨1664556, by rfl⟩ : syracuseStep 4438817 = 3329113) B3329113
theorem B2959211 : Blo 1971435 2959211 := bstep (se 1 (by rfl) ⟨2219408, by rfl⟩ : syracuseStep 2959211 = 4438817) B4438817
theorem B1972807 : Blo 1971435 1972807 := bstep (se 1 (by rfl) ⟨1479605, by rfl⟩ : syracuseStep 1972807 = 2959211) B2959211
theorem B2219413 : Blo 1971435 2219413 := bbase (se 6 (by rfl) ⟨52017, by rfl⟩ : syracuseStep 2219413 = 104035) (by norm_num)
theorem B2959217 : Blo 1971435 2959217 := bstep (se 2 (by rfl) ⟨1109706, by rfl⟩ : syracuseStep 2959217 = 2219413) B2219413
theorem B1972811 : Blo 1971435 1972811 := bstep (se 1 (by rfl) ⟨1479608, by rfl⟩ : syracuseStep 1972811 = 2959217) B2959217
theorem B2496845 : Blo 1971435 2496845 := bbase (se 3 (by rfl) ⟨468158, by rfl⟩ : syracuseStep 2496845 = 936317) (by norm_num)
theorem B6658253 : Blo 1971435 6658253 := bstep (se 3 (by rfl) ⟨1248422, by rfl⟩ : syracuseStep 6658253 = 2496845) B2496845
theorem B4438835 : Blo 1971435 4438835 := bstep (se 1 (by rfl) ⟨3329126, by rfl⟩ : syracuseStep 4438835 = 6658253) B6658253
theorem B2959223 : Blo 1971435 2959223 := bstep (se 1 (by rfl) ⟨2219417, by rfl⟩ : syracuseStep 2959223 = 4438835) B4438835
theorem B1972815 : Blo 1971435 1972815 := bstep (se 1 (by rfl) ⟨1479611, by rfl⟩ : syracuseStep 1972815 = 2959223) B2959223
theorem B2959229 : Blo 1971435 2959229 := bbase (se 3 (by rfl) ⟨554855, by rfl⟩ : syracuseStep 2959229 = 1109711) (by norm_num)
theorem B1972819 : Blo 1971435 1972819 := bstep (se 1 (by rfl) ⟨1479614, by rfl⟩ : syracuseStep 1972819 = 2959229) B2959229
theorem B4438853 : Blo 1971435 4438853 := bbase (se 4 (by rfl) ⟨416142, by rfl⟩ : syracuseStep 4438853 = 832285) (by norm_num)
theorem B2959235 : Blo 1971435 2959235 := bstep (se 1 (by rfl) ⟨2219426, by rfl⟩ : syracuseStep 2959235 = 4438853) B4438853
theorem B1972823 : Blo 1971435 1972823 := bstep (se 1 (by rfl) ⟨1479617, by rfl⟩ : syracuseStep 1972823 = 2959235) B2959235
theorem B4213453 : Blo 1971435 4213453 := bbase (se 3 (by rfl) ⟨790022, by rfl⟩ : syracuseStep 4213453 = 1580045) (by norm_num)
theorem B5617937 : Blo 1971435 5617937 := bstep (se 2 (by rfl) ⟨2106726, by rfl⟩ : syracuseStep 5617937 = 4213453) B4213453
theorem B3745291 : Blo 1971435 3745291 := bstep (se 1 (by rfl) ⟨2808968, by rfl⟩ : syracuseStep 3745291 = 5617937) B5617937
theorem B4993721 : Blo 1971435 4993721 := bstep (se 2 (by rfl) ⟨1872645, by rfl⟩ : syracuseStep 4993721 = 3745291) B3745291
theorem B3329147 : Blo 1971435 3329147 := bstep (se 1 (by rfl) ⟨2496860, by rfl⟩ : syracuseStep 3329147 = 4993721) B4993721
theorem B2219431 : Blo 1971435 2219431 := bstep (se 1 (by rfl) ⟨1664573, by rfl⟩ : syracuseStep 2219431 = 3329147) B3329147
theorem B2959241 : Blo 1971435 2959241 := bstep (se 2 (by rfl) ⟨1109715, by rfl⟩ : syracuseStep 2959241 = 2219431) B2219431
theorem B1972827 : Blo 1971435 1972827 := bstep (se 1 (by rfl) ⟨1479620, by rfl⟩ : syracuseStep 1972827 = 2959241) B2959241
theorem B9987461 : Blo 1971435 9987461 := bbase (se 4 (by rfl) ⟨936324, by rfl⟩ : syracuseStep 9987461 = 1872649) (by norm_num)
theorem B6658307 : Blo 1971435 6658307 := bstep (se 1 (by rfl) ⟨4993730, by rfl⟩ : syracuseStep 6658307 = 9987461) B9987461
theorem B4438871 : Blo 1971435 4438871 := bstep (se 1 (by rfl) ⟨3329153, by rfl⟩ : syracuseStep 4438871 = 6658307) B6658307
theorem B2959247 : Blo 1971435 2959247 := bstep (se 1 (by rfl) ⟨2219435, by rfl⟩ : syracuseStep 2959247 = 4438871) B4438871
theorem B1972831 : Blo 1971435 1972831 := bstep (se 1 (by rfl) ⟨1479623, by rfl⟩ : syracuseStep 1972831 = 2959247) B2959247
theorem B2959253 : Blo 1971435 2959253 := bbase (se 6 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 2959253 = 138715) (by norm_num)
theorem B1972835 : Blo 1971435 1972835 := bstep (se 1 (by rfl) ⟨1479626, by rfl⟩ : syracuseStep 1972835 = 2959253) B2959253
theorem B3160109 : Blo 1971435 3160109 := bbase (se 3 (by rfl) ⟨592520, by rfl⟩ : syracuseStep 3160109 = 1185041) (by norm_num)
theorem B2106739 : Blo 1971435 2106739 := bstep (se 1 (by rfl) ⟨1580054, by rfl⟩ : syracuseStep 2106739 = 3160109) B3160109
theorem B11235941 : Blo 1971435 11235941 := bstep (se 4 (by rfl) ⟨1053369, by rfl⟩ : syracuseStep 11235941 = 2106739) B2106739
theorem B7490627 : Blo 1971435 7490627 := bstep (se 1 (by rfl) ⟨5617970, by rfl⟩ : syracuseStep 7490627 = 11235941) B11235941
theorem B4993751 : Blo 1971435 4993751 := bstep (se 1 (by rfl) ⟨3745313, by rfl⟩ : syracuseStep 4993751 = 7490627) B7490627
theorem B3329167 : Blo 1971435 3329167 := bstep (se 1 (by rfl) ⟨2496875, by rfl⟩ : syracuseStep 3329167 = 4993751) B4993751
theorem B4438889 : Blo 1971435 4438889 := bstep (se 2 (by rfl) ⟨1664583, by rfl⟩ : syracuseStep 4438889 = 3329167) B3329167
theorem B2959259 : Blo 1971435 2959259 := bstep (se 1 (by rfl) ⟨2219444, by rfl⟩ : syracuseStep 2959259 = 4438889) B4438889
theorem B1972839 : Blo 1971435 1972839 := bstep (se 1 (by rfl) ⟨1479629, by rfl⟩ : syracuseStep 1972839 = 2959259) B2959259
theorem B2219449 : Blo 1971435 2219449 := bbase (se 2 (by rfl) ⟨832293, by rfl⟩ : syracuseStep 2219449 = 1664587) (by norm_num)
theorem B2959265 : Blo 1971435 2959265 := bstep (se 2 (by rfl) ⟨1109724, by rfl⟩ : syracuseStep 2959265 = 2219449) B2219449
theorem B1972843 : Blo 1971435 1972843 := bstep (se 1 (by rfl) ⟨1479632, by rfl⟩ : syracuseStep 1972843 = 2959265) B2959265
theorem B1999765 : Blo 1971435 1999765 := bbase (se 6 (by rfl) ⟨46869, by rfl⟩ : syracuseStep 1999765 = 93739) (by norm_num)
theorem B2666353 : Blo 1971435 2666353 := bstep (se 2 (by rfl) ⟨999882, by rfl⟩ : syracuseStep 2666353 = 1999765) B1999765
theorem B3555137 : Blo 1971435 3555137 := bstep (se 2 (by rfl) ⟨1333176, by rfl⟩ : syracuseStep 3555137 = 2666353) B2666353
theorem B9480365 : Blo 1971435 9480365 := bstep (se 3 (by rfl) ⟨1777568, by rfl⟩ : syracuseStep 9480365 = 3555137) B3555137
theorem B6320243 : Blo 1971435 6320243 := bstep (se 1 (by rfl) ⟨4740182, by rfl⟩ : syracuseStep 6320243 = 9480365) B9480365
theorem B4213495 : Blo 1971435 4213495 := bstep (se 1 (by rfl) ⟨3160121, by rfl⟩ : syracuseStep 4213495 = 6320243) B6320243
theorem B5617993 : Blo 1971435 5617993 := bstep (se 2 (by rfl) ⟨2106747, by rfl⟩ : syracuseStep 5617993 = 4213495) B4213495
theorem B7490657 : Blo 1971435 7490657 := bstep (se 2 (by rfl) ⟨2808996, by rfl⟩ : syracuseStep 7490657 = 5617993) B5617993
theorem B4993771 : Blo 1971435 4993771 := bstep (se 1 (by rfl) ⟨3745328, by rfl⟩ : syracuseStep 4993771 = 7490657) B7490657
theorem B6658361 : Blo 1971435 6658361 := bstep (se 2 (by rfl) ⟨2496885, by rfl⟩ : syracuseStep 6658361 = 4993771) B4993771
theorem B4438907 : Blo 1971435 4438907 := bstep (se 1 (by rfl) ⟨3329180, by rfl⟩ : syracuseStep 4438907 = 6658361) B6658361
theorem B2959271 : Blo 1971435 2959271 := bstep (se 1 (by rfl) ⟨2219453, by rfl⟩ : syracuseStep 2959271 = 4438907) B4438907
theorem B1972847 : Blo 1971435 1972847 := bstep (se 1 (by rfl) ⟨1479635, by rfl⟩ : syracuseStep 1972847 = 2959271) B2959271
theorem B2959277 : Blo 1971435 2959277 := bbase (se 3 (by rfl) ⟨554864, by rfl⟩ : syracuseStep 2959277 = 1109729) (by norm_num)
theorem B1972851 : Blo 1971435 1972851 := bstep (se 1 (by rfl) ⟨1479638, by rfl⟩ : syracuseStep 1972851 = 2959277) B2959277
theorem B4438925 : Blo 1971435 4438925 := bbase (se 3 (by rfl) ⟨832298, by rfl⟩ : syracuseStep 4438925 = 1664597) (by norm_num)
theorem B2959283 : Blo 1971435 2959283 := bstep (se 1 (by rfl) ⟨2219462, by rfl⟩ : syracuseStep 2959283 = 4438925) B4438925
theorem B1972855 : Blo 1971435 1972855 := bstep (se 1 (by rfl) ⟨1479641, by rfl⟩ : syracuseStep 1972855 = 2959283) B2959283
theorem B2496901 : Blo 1971435 2496901 := bbase (se 4 (by rfl) ⟨234084, by rfl⟩ : syracuseStep 2496901 = 468169) (by norm_num)
theorem B3329201 : Blo 1971435 3329201 := bstep (se 2 (by rfl) ⟨1248450, by rfl⟩ : syracuseStep 3329201 = 2496901) B2496901
theorem B2219467 : Blo 1971435 2219467 := bstep (se 1 (by rfl) ⟨1664600, by rfl⟩ : syracuseStep 2219467 = 3329201) B3329201
theorem B2959289 : Blo 1971435 2959289 := bstep (se 2 (by rfl) ⟨1109733, by rfl⟩ : syracuseStep 2959289 = 2219467) B2219467
theorem B1972859 : Blo 1971435 1972859 := bstep (se 1 (by rfl) ⟨1479644, by rfl⟩ : syracuseStep 1972859 = 2959289) B2959289
theorem B25281173 : Blo 1971435 25281173 := bbase (se 6 (by rfl) ⟨592527, by rfl⟩ : syracuseStep 25281173 = 1185055) (by norm_num)
theorem B16854115 : Blo 1971435 16854115 := bstep (se 1 (by rfl) ⟨12640586, by rfl⟩ : syracuseStep 16854115 = 25281173) B25281173
theorem B22472153 : Blo 1971435 22472153 := bstep (se 2 (by rfl) ⟨8427057, by rfl⟩ : syracuseStep 22472153 = 16854115) B16854115
theorem B14981435 : Blo 1971435 14981435 := bstep (se 1 (by rfl) ⟨11236076, by rfl⟩ : syracuseStep 14981435 = 22472153) B22472153
theorem B9987623 : Blo 1971435 9987623 := bstep (se 1 (by rfl) ⟨7490717, by rfl⟩ : syracuseStep 9987623 = 14981435) B14981435
theorem B6658415 : Blo 1971435 6658415 := bstep (se 1 (by rfl) ⟨4993811, by rfl⟩ : syracuseStep 6658415 = 9987623) B9987623
theorem B4438943 : Blo 1971435 4438943 := bstep (se 1 (by rfl) ⟨3329207, by rfl⟩ : syracuseStep 4438943 = 6658415) B6658415
theorem B2959295 : Blo 1971435 2959295 := bstep (se 1 (by rfl) ⟨2219471, by rfl⟩ : syracuseStep 2959295 = 4438943) B4438943
theorem B1972863 : Blo 1971435 1972863 := bstep (se 1 (by rfl) ⟨1479647, by rfl⟩ : syracuseStep 1972863 = 2959295) B2959295
theorem B2959301 : Blo 1971435 2959301 := bbase (se 4 (by rfl) ⟨277434, by rfl⟩ : syracuseStep 2959301 = 554869) (by norm_num)
theorem B1972867 : Blo 1971435 1972867 := bstep (se 1 (by rfl) ⟨1479650, by rfl⟩ : syracuseStep 1972867 = 2959301) B2959301
theorem B3329221 : Blo 1971435 3329221 := bbase (se 4 (by rfl) ⟨312114, by rfl⟩ : syracuseStep 3329221 = 624229) (by norm_num)
theorem B4438961 : Blo 1971435 4438961 := bstep (se 2 (by rfl) ⟨1664610, by rfl⟩ : syracuseStep 4438961 = 3329221) B3329221
theorem B2959307 : Blo 1971435 2959307 := bstep (se 1 (by rfl) ⟨2219480, by rfl⟩ : syracuseStep 2959307 = 4438961) B4438961
theorem B1972871 : Blo 1971435 1972871 := bstep (se 1 (by rfl) ⟨1479653, by rfl⟩ : syracuseStep 1972871 = 2959307) B2959307
theorem B2219485 : Blo 1971435 2219485 := bbase (se 3 (by rfl) ⟨416153, by rfl⟩ : syracuseStep 2219485 = 832307) (by norm_num)
theorem B2959313 : Blo 1971435 2959313 := bstep (se 2 (by rfl) ⟨1109742, by rfl⟩ : syracuseStep 2959313 = 2219485) B2219485
theorem B1972875 : Blo 1971435 1972875 := bstep (se 1 (by rfl) ⟨1479656, by rfl⟩ : syracuseStep 1972875 = 2959313) B2959313
theorem B6658469 : Blo 1971435 6658469 := bbase (se 4 (by rfl) ⟨624231, by rfl⟩ : syracuseStep 6658469 = 1248463) (by norm_num)
theorem B4438979 : Blo 1971435 4438979 := bstep (se 1 (by rfl) ⟨3329234, by rfl⟩ : syracuseStep 4438979 = 6658469) B6658469
theorem B2959319 : Blo 1971435 2959319 := bstep (se 1 (by rfl) ⟨2219489, by rfl⟩ : syracuseStep 2959319 = 4438979) B4438979
theorem B1972879 : Blo 1971435 1972879 := bstep (se 1 (by rfl) ⟨1479659, by rfl⟩ : syracuseStep 1972879 = 2959319) B2959319
theorem B2959325 : Blo 1971435 2959325 := bbase (se 3 (by rfl) ⟨554873, by rfl⟩ : syracuseStep 2959325 = 1109747) (by norm_num)
theorem B1972883 : Blo 1971435 1972883 := bstep (se 1 (by rfl) ⟨1479662, by rfl⟩ : syracuseStep 1972883 = 2959325) B2959325
theorem B4438997 : Blo 1971435 4438997 := bbase (se 7 (by rfl) ⟨52019, by rfl⟩ : syracuseStep 4438997 = 104039) (by norm_num)
theorem B2959331 : Blo 1971435 2959331 := bstep (se 1 (by rfl) ⟨2219498, by rfl⟩ : syracuseStep 2959331 = 4438997) B4438997
theorem B1972887 : Blo 1971435 1972887 := bstep (se 1 (by rfl) ⟨1479665, by rfl⟩ : syracuseStep 1972887 = 2959331) B2959331
theorem B5999429 : Blo 1971435 5999429 := bbase (se 4 (by rfl) ⟨562446, by rfl⟩ : syracuseStep 5999429 = 1124893) (by norm_num)
theorem B3999619 : Blo 1971435 3999619 := bstep (se 1 (by rfl) ⟨2999714, by rfl⟩ : syracuseStep 3999619 = 5999429) B5999429
theorem B5332825 : Blo 1971435 5332825 := bstep (se 2 (by rfl) ⟨1999809, by rfl⟩ : syracuseStep 5332825 = 3999619) B3999619
theorem B7110433 : Blo 1971435 7110433 := bstep (se 2 (by rfl) ⟨2666412, by rfl⟩ : syracuseStep 7110433 = 5332825) B5332825
theorem B9480577 : Blo 1971435 9480577 := bstep (se 2 (by rfl) ⟨3555216, by rfl⟩ : syracuseStep 9480577 = 7110433) B7110433
theorem B12640769 : Blo 1971435 12640769 := bstep (se 2 (by rfl) ⟨4740288, by rfl⟩ : syracuseStep 12640769 = 9480577) B9480577
theorem B8427179 : Blo 1971435 8427179 := bstep (se 1 (by rfl) ⟨6320384, by rfl⟩ : syracuseStep 8427179 = 12640769) B12640769
theorem B5618119 : Blo 1971435 5618119 := bstep (se 1 (by rfl) ⟨4213589, by rfl⟩ : syracuseStep 5618119 = 8427179) B8427179
theorem B7490825 : Blo 1971435 7490825 := bstep (se 2 (by rfl) ⟨2809059, by rfl⟩ : syracuseStep 7490825 = 5618119) B5618119
theorem B4993883 : Blo 1971435 4993883 := bstep (se 1 (by rfl) ⟨3745412, by rfl⟩ : syracuseStep 4993883 = 7490825) B7490825
theorem B3329255 : Blo 1971435 3329255 := bstep (se 1 (by rfl) ⟨2496941, by rfl⟩ : syracuseStep 3329255 = 4993883) B4993883
theorem B2219503 : Blo 1971435 2219503 := bstep (se 1 (by rfl) ⟨1664627, by rfl⟩ : syracuseStep 2219503 = 3329255) B3329255
theorem B2959337 : Blo 1971435 2959337 := bstep (se 2 (by rfl) ⟨1109751, by rfl⟩ : syracuseStep 2959337 = 2219503) B2219503
theorem B1972891 : Blo 1971435 1972891 := bstep (se 1 (by rfl) ⟨1479668, by rfl⟩ : syracuseStep 1972891 = 2959337) B2959337
theorem B16854389 : Blo 1971435 16854389 := bbase (se 5 (by rfl) ⟨790049, by rfl⟩ : syracuseStep 16854389 = 1580099) (by norm_num)
theorem B11236259 : Blo 1971435 11236259 := bstep (se 1 (by rfl) ⟨8427194, by rfl⟩ : syracuseStep 11236259 = 16854389) B16854389
theorem B7490839 : Blo 1971435 7490839 := bstep (se 1 (by rfl) ⟨5618129, by rfl⟩ : syracuseStep 7490839 = 11236259) B11236259
theorem B9987785 : Blo 1971435 9987785 := bstep (se 2 (by rfl) ⟨3745419, by rfl⟩ : syracuseStep 9987785 = 7490839) B7490839
theorem B6658523 : Blo 1971435 6658523 := bstep (se 1 (by rfl) ⟨4993892, by rfl⟩ : syracuseStep 6658523 = 9987785) B9987785
theorem B4439015 : Blo 1971435 4439015 := bstep (se 1 (by rfl) ⟨3329261, by rfl⟩ : syracuseStep 4439015 = 6658523) B6658523
theorem B2959343 : Blo 1971435 2959343 := bstep (se 1 (by rfl) ⟨2219507, by rfl⟩ : syracuseStep 2959343 = 4439015) B4439015
theorem B1972895 : Blo 1971435 1972895 := bstep (se 1 (by rfl) ⟨1479671, by rfl⟩ : syracuseStep 1972895 = 2959343) B2959343
theorem B2959349 : Blo 1971435 2959349 := bbase (se 5 (by rfl) ⟨138719, by rfl⟩ : syracuseStep 2959349 = 277439) (by norm_num)
theorem B1972899 : Blo 1971435 1972899 := bstep (se 1 (by rfl) ⟨1479674, by rfl⟩ : syracuseStep 1972899 = 2959349) B2959349
theorem B2402497 : Blo 1971435 2402497 := bbase (se 2 (by rfl) ⟨900936, by rfl⟩ : syracuseStep 2402497 = 1801873) (by norm_num)
theorem B3203329 : Blo 1971435 3203329 := bstep (se 2 (by rfl) ⟨1201248, by rfl⟩ : syracuseStep 3203329 = 2402497) B2402497
theorem B4271105 : Blo 1971435 4271105 := bstep (se 2 (by rfl) ⟨1601664, by rfl⟩ : syracuseStep 4271105 = 3203329) B3203329
theorem B2847403 : Blo 1971435 2847403 := bstep (se 1 (by rfl) ⟨2135552, by rfl⟩ : syracuseStep 2847403 = 4271105) B4271105
theorem B15186149 : Blo 1971435 15186149 := bstep (se 4 (by rfl) ⟨1423701, by rfl⟩ : syracuseStep 15186149 = 2847403) B2847403
theorem B10124099 : Blo 1971435 10124099 := bstep (se 1 (by rfl) ⟨7593074, by rfl⟩ : syracuseStep 10124099 = 15186149) B15186149
theorem B6749399 : Blo 1971435 6749399 := bstep (se 1 (by rfl) ⟨5062049, by rfl⟩ : syracuseStep 6749399 = 10124099) B10124099
theorem B4499599 : Blo 1971435 4499599 := bstep (se 1 (by rfl) ⟨3374699, by rfl⟩ : syracuseStep 4499599 = 6749399) B6749399
theorem B5999465 : Blo 1971435 5999465 := bstep (se 2 (by rfl) ⟨2249799, by rfl⟩ : syracuseStep 5999465 = 4499599) B4499599
theorem B15998573 : Blo 1971435 15998573 := bstep (se 3 (by rfl) ⟨2999732, by rfl⟩ : syracuseStep 15998573 = 5999465) B5999465
theorem B10665715 : Blo 1971435 10665715 := bstep (se 1 (by rfl) ⟨7999286, by rfl⟩ : syracuseStep 10665715 = 15998573) B15998573
theorem B14220953 : Blo 1971435 14220953 := bstep (se 2 (by rfl) ⟨5332857, by rfl⟩ : syracuseStep 14220953 = 10665715) B10665715
theorem B9480635 : Blo 1971435 9480635 := bstep (se 1 (by rfl) ⟨7110476, by rfl⟩ : syracuseStep 9480635 = 14220953) B14220953
theorem B6320423 : Blo 1971435 6320423 := bstep (se 1 (by rfl) ⟨4740317, by rfl⟩ : syracuseStep 6320423 = 9480635) B9480635
theorem B4213615 : Blo 1971435 4213615 := bstep (se 1 (by rfl) ⟨3160211, by rfl⟩ : syracuseStep 4213615 = 6320423) B6320423
theorem B5618153 : Blo 1971435 5618153 := bstep (se 2 (by rfl) ⟨2106807, by rfl⟩ : syracuseStep 5618153 = 4213615) B4213615
theorem B3745435 : Blo 1971435 3745435 := bstep (se 1 (by rfl) ⟨2809076, by rfl⟩ : syracuseStep 3745435 = 5618153) B5618153
theorem B4993913 : Blo 1971435 4993913 := bstep (se 2 (by rfl) ⟨1872717, by rfl⟩ : syracuseStep 4993913 = 3745435) B3745435
theorem B3329275 : Blo 1971435 3329275 := bstep (se 1 (by rfl) ⟨2496956, by rfl⟩ : syracuseStep 3329275 = 4993913) B4993913
theorem B4439033 : Blo 1971435 4439033 := bstep (se 2 (by rfl) ⟨1664637, by rfl⟩ : syracuseStep 4439033 = 3329275) B3329275
theorem B2959355 : Blo 1971435 2959355 := bstep (se 1 (by rfl) ⟨2219516, by rfl⟩ : syracuseStep 2959355 = 4439033) B4439033
theorem B1972903 : Blo 1971435 1972903 := bstep (se 1 (by rfl) ⟨1479677, by rfl⟩ : syracuseStep 1972903 = 2959355) B2959355
theorem B2219521 : Blo 1971435 2219521 := bbase (se 2 (by rfl) ⟨832320, by rfl⟩ : syracuseStep 2219521 = 1664641) (by norm_num)
theorem B2959361 : Blo 1971435 2959361 := bstep (se 2 (by rfl) ⟨1109760, by rfl⟩ : syracuseStep 2959361 = 2219521) B2219521
theorem B1972907 : Blo 1971435 1972907 := bstep (se 1 (by rfl) ⟨1479680, by rfl⟩ : syracuseStep 1972907 = 2959361) B2959361
theorem B4993933 : Blo 1971435 4993933 := bbase (se 3 (by rfl) ⟨936362, by rfl⟩ : syracuseStep 4993933 = 1872725) (by norm_num)
theorem B6658577 : Blo 1971435 6658577 := bstep (se 2 (by rfl) ⟨2496966, by rfl⟩ : syracuseStep 6658577 = 4993933) B4993933
theorem B4439051 : Blo 1971435 4439051 := bstep (se 1 (by rfl) ⟨3329288, by rfl⟩ : syracuseStep 4439051 = 6658577) B6658577
theorem B2959367 : Blo 1971435 2959367 := bstep (se 1 (by rfl) ⟨2219525, by rfl⟩ : syracuseStep 2959367 = 4439051) B4439051
theorem B1972911 : Blo 1971435 1972911 := bstep (se 1 (by rfl) ⟨1479683, by rfl⟩ : syracuseStep 1972911 = 2959367) B2959367
theorem B2959373 : Blo 1971435 2959373 := bbase (se 3 (by rfl) ⟨554882, by rfl⟩ : syracuseStep 2959373 = 1109765) (by norm_num)
theorem B1972915 : Blo 1971435 1972915 := bstep (se 1 (by rfl) ⟨1479686, by rfl⟩ : syracuseStep 1972915 = 2959373) B2959373
theorem B4439069 : Blo 1971435 4439069 := bbase (se 3 (by rfl) ⟨832325, by rfl⟩ : syracuseStep 4439069 = 1664651) (by norm_num)
theorem B2959379 : Blo 1971435 2959379 := bstep (se 1 (by rfl) ⟨2219534, by rfl⟩ : syracuseStep 2959379 = 4439069) B4439069
theorem B1972919 : Blo 1971435 1972919 := bstep (se 1 (by rfl) ⟨1479689, by rfl⟩ : syracuseStep 1972919 = 2959379) B2959379
theorem B3329309 : Blo 1971435 3329309 := bbase (se 3 (by rfl) ⟨624245, by rfl⟩ : syracuseStep 3329309 = 1248491) (by norm_num)
theorem B2219539 : Blo 1971435 2219539 := bstep (se 1 (by rfl) ⟨1664654, by rfl⟩ : syracuseStep 2219539 = 3329309) B3329309
theorem B2959385 : Blo 1971435 2959385 := bstep (se 2 (by rfl) ⟨1109769, by rfl⟩ : syracuseStep 2959385 = 2219539) B2219539
theorem B1972923 : Blo 1971435 1972923 := bstep (se 1 (by rfl) ⟨1479692, by rfl⟩ : syracuseStep 1972923 = 2959385) B2959385
theorem B2666461 : Blo 1971435 2666461 := bbase (se 3 (by rfl) ⟨499961, by rfl⟩ : syracuseStep 2666461 = 999923) (by norm_num)
theorem B3555281 : Blo 1971435 3555281 := bstep (se 2 (by rfl) ⟨1333230, by rfl⟩ : syracuseStep 3555281 = 2666461) B2666461
theorem B2370187 : Blo 1971435 2370187 := bstep (se 1 (by rfl) ⟨1777640, by rfl⟩ : syracuseStep 2370187 = 3555281) B3555281
theorem B12640997 : Blo 1971435 12640997 := bstep (se 4 (by rfl) ⟨1185093, by rfl⟩ : syracuseStep 12640997 = 2370187) B2370187
theorem B8427331 : Blo 1971435 8427331 := bstep (se 1 (by rfl) ⟨6320498, by rfl⟩ : syracuseStep 8427331 = 12640997) B12640997
theorem B11236441 : Blo 1971435 11236441 := bstep (se 2 (by rfl) ⟨4213665, by rfl⟩ : syracuseStep 11236441 = 8427331) B8427331
theorem B14981921 : Blo 1971435 14981921 := bstep (se 2 (by rfl) ⟨5618220, by rfl⟩ : syracuseStep 14981921 = 11236441) B11236441
theorem B9987947 : Blo 1971435 9987947 := bstep (se 1 (by rfl) ⟨7490960, by rfl⟩ : syracuseStep 9987947 = 14981921) B14981921
theorem B6658631 : Blo 1971435 6658631 := bstep (se 1 (by rfl) ⟨4993973, by rfl⟩ : syracuseStep 6658631 = 9987947) B9987947
theorem B4439087 : Blo 1971435 4439087 := bstep (se 1 (by rfl) ⟨3329315, by rfl⟩ : syracuseStep 4439087 = 6658631) B6658631
theorem B2959391 : Blo 1971435 2959391 := bstep (se 1 (by rfl) ⟨2219543, by rfl⟩ : syracuseStep 2959391 = 4439087) B4439087
theorem B1972927 : Blo 1971435 1972927 := bstep (se 1 (by rfl) ⟨1479695, by rfl⟩ : syracuseStep 1972927 = 2959391) B2959391
theorem B2959397 : Blo 1971435 2959397 := bbase (se 4 (by rfl) ⟨277443, by rfl⟩ : syracuseStep 2959397 = 554887) (by norm_num)
theorem B1972931 : Blo 1971435 1972931 := bstep (se 1 (by rfl) ⟨1479698, by rfl⟩ : syracuseStep 1972931 = 2959397) B2959397
theorem B2496997 : Blo 1971435 2496997 := bbase (se 4 (by rfl) ⟨234093, by rfl⟩ : syracuseStep 2496997 = 468187) (by norm_num)
theorem B3329329 : Blo 1971435 3329329 := bstep (se 2 (by rfl) ⟨1248498, by rfl⟩ : syracuseStep 3329329 = 2496997) B2496997
theorem B4439105 : Blo 1971435 4439105 := bstep (se 2 (by rfl) ⟨1664664, by rfl⟩ : syracuseStep 4439105 = 3329329) B3329329
theorem B2959403 : Blo 1971435 2959403 := bstep (se 1 (by rfl) ⟨2219552, by rfl⟩ : syracuseStep 2959403 = 4439105) B4439105
theorem B1972935 : Blo 1971435 1972935 := bstep (se 1 (by rfl) ⟨1479701, by rfl⟩ : syracuseStep 1972935 = 2959403) B2959403
theorem B2219557 : Blo 1971435 2219557 := bbase (se 4 (by rfl) ⟨208083, by rfl⟩ : syracuseStep 2219557 = 416167) (by norm_num)
theorem B2959409 : Blo 1971435 2959409 := bstep (se 2 (by rfl) ⟨1109778, by rfl⟩ : syracuseStep 2959409 = 2219557) B2219557
theorem B1972939 : Blo 1971435 1972939 := bstep (se 1 (by rfl) ⟨1479704, by rfl⟩ : syracuseStep 1972939 = 2959409) B2959409
theorem B2249845 : Blo 1971435 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B11999173 : Blo 1971435 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B15998897 : Blo 1971435 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B10665931 : Blo 1971435 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B14221241 : Blo 1971435 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B9480827 : Blo 1971435 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B6320551 : Blo 1971435 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B8427401 : Blo 1971435 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B5618267 : Blo 1971435 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B3745511 : Blo 1971435 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B2497007 : Blo 1971435 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B6658685 : Blo 1971435 6658685 := bstep (se 3 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 6658685 = 2497007) B2497007
theorem B4439123 : Blo 1971435 4439123 := bstep (se 1 (by rfl) ⟨3329342, by rfl⟩ : syracuseStep 4439123 = 6658685) B6658685
theorem B2959415 : Blo 1971435 2959415 := bstep (se 1 (by rfl) ⟨2219561, by rfl⟩ : syracuseStep 2959415 = 4439123) B4439123
theorem B1972943 : Blo 1971435 1972943 := bstep (se 1 (by rfl) ⟨1479707, by rfl⟩ : syracuseStep 1972943 = 2959415) B2959415
theorem B2959421 : Blo 1971435 2959421 := bbase (se 3 (by rfl) ⟨554891, by rfl⟩ : syracuseStep 2959421 = 1109783) (by norm_num)
theorem B1972947 : Blo 1971435 1972947 := bstep (se 1 (by rfl) ⟨1479710, by rfl⟩ : syracuseStep 1972947 = 2959421) B2959421
theorem B4439141 : Blo 1971435 4439141 := bbase (se 4 (by rfl) ⟨416169, by rfl⟩ : syracuseStep 4439141 = 832339) (by norm_num)
theorem B2959427 : Blo 1971435 2959427 := bstep (se 1 (by rfl) ⟨2219570, by rfl⟩ : syracuseStep 2959427 = 4439141) B4439141
theorem B1972951 : Blo 1971435 1972951 := bstep (se 1 (by rfl) ⟨1479713, by rfl⟩ : syracuseStep 1972951 = 2959427) B2959427
theorem B4994045 : Blo 1971435 4994045 := bbase (se 3 (by rfl) ⟨936383, by rfl⟩ : syracuseStep 4994045 = 1872767) (by norm_num)
theorem B3329363 : Blo 1971435 3329363 := bstep (se 1 (by rfl) ⟨2497022, by rfl⟩ : syracuseStep 3329363 = 4994045) B4994045
theorem B2219575 : Blo 1971435 2219575 := bstep (se 1 (by rfl) ⟨1664681, by rfl⟩ : syracuseStep 2219575 = 3329363) B3329363
theorem B2959433 : Blo 1971435 2959433 := bstep (se 2 (by rfl) ⟨1109787, by rfl⟩ : syracuseStep 2959433 = 2219575) B2219575
theorem B1972955 : Blo 1971435 1972955 := bstep (se 1 (by rfl) ⟨1479716, by rfl⟩ : syracuseStep 1972955 = 2959433) B2959433
theorem B3745541 : Blo 1971435 3745541 := bbase (se 4 (by rfl) ⟨351144, by rfl⟩ : syracuseStep 3745541 = 702289) (by norm_num)
theorem B9988109 : Blo 1971435 9988109 := bstep (se 3 (by rfl) ⟨1872770, by rfl⟩ : syracuseStep 9988109 = 3745541) B3745541
theorem B6658739 : Blo 1971435 6658739 := bstep (se 1 (by rfl) ⟨4994054, by rfl⟩ : syracuseStep 6658739 = 9988109) B9988109
theorem B4439159 : Blo 1971435 4439159 := bstep (se 1 (by rfl) ⟨3329369, by rfl⟩ : syracuseStep 4439159 = 6658739) B6658739
theorem B2959439 : Blo 1971435 2959439 := bstep (se 1 (by rfl) ⟨2219579, by rfl⟩ : syracuseStep 2959439 = 4439159) B4439159
theorem B1972959 : Blo 1971435 1972959 := bstep (se 1 (by rfl) ⟨1479719, by rfl⟩ : syracuseStep 1972959 = 2959439) B2959439
theorem B2959445 : Blo 1971435 2959445 := bbase (se 8 (by rfl) ⟨17340, by rfl⟩ : syracuseStep 2959445 = 34681) (by norm_num)
theorem B1972963 : Blo 1971435 1972963 := bstep (se 1 (by rfl) ⟨1479722, by rfl⟩ : syracuseStep 1972963 = 2959445) B2959445
theorem B47997269 : Blo 1971435 47997269 := bbase (se 10 (by rfl) ⟨70308, by rfl⟩ : syracuseStep 47997269 = 140617) (by norm_num)
theorem B31998179 : Blo 1971435 31998179 := bstep (se 1 (by rfl) ⟨23998634, by rfl⟩ : syracuseStep 31998179 = 47997269) B47997269
theorem B21332119 : Blo 1971435 21332119 := bstep (se 1 (by rfl) ⟨15999089, by rfl⟩ : syracuseStep 21332119 = 31998179) B31998179
theorem B28442825 : Blo 1971435 28442825 := bstep (se 2 (by rfl) ⟨10666059, by rfl⟩ : syracuseStep 28442825 = 21332119) B21332119
theorem B18961883 : Blo 1971435 18961883 := bstep (se 1 (by rfl) ⟨14221412, by rfl⟩ : syracuseStep 18961883 = 28442825) B28442825
theorem B12641255 : Blo 1971435 12641255 := bstep (se 1 (by rfl) ⟨9480941, by rfl⟩ : syracuseStep 12641255 = 18961883) B18961883
theorem B8427503 : Blo 1971435 8427503 := bstep (se 1 (by rfl) ⟨6320627, by rfl⟩ : syracuseStep 8427503 = 12641255) B12641255
theorem B5618335 : Blo 1971435 5618335 := bstep (se 1 (by rfl) ⟨4213751, by rfl⟩ : syracuseStep 5618335 = 8427503) B8427503
theorem B7491113 : Blo 1971435 7491113 := bstep (se 2 (by rfl) ⟨2809167, by rfl⟩ : syracuseStep 7491113 = 5618335) B5618335
theorem B4994075 : Blo 1971435 4994075 := bstep (se 1 (by rfl) ⟨3745556, by rfl⟩ : syracuseStep 4994075 = 7491113) B7491113
theorem B3329383 : Blo 1971435 3329383 := bstep (se 1 (by rfl) ⟨2497037, by rfl⟩ : syracuseStep 3329383 = 4994075) B4994075
theorem B4439177 : Blo 1971435 4439177 := bstep (se 2 (by rfl) ⟨1664691, by rfl⟩ : syracuseStep 4439177 = 3329383) B3329383
theorem B2959451 : Blo 1971435 2959451 := bstep (se 1 (by rfl) ⟨2219588, by rfl⟩ : syracuseStep 2959451 = 4439177) B4439177
theorem B1972967 : Blo 1971435 1972967 := bstep (se 1 (by rfl) ⟨1479725, by rfl⟩ : syracuseStep 1972967 = 2959451) B2959451
theorem B2219593 : Blo 1971435 2219593 := bbase (se 2 (by rfl) ⟨832347, by rfl⟩ : syracuseStep 2219593 = 1664695) (by norm_num)
theorem B2959457 : Blo 1971435 2959457 := bstep (se 2 (by rfl) ⟨1109796, by rfl⟩ : syracuseStep 2959457 = 2219593) B2219593
theorem B1972971 : Blo 1971435 1972971 := bstep (se 1 (by rfl) ⟨1479728, by rfl⟩ : syracuseStep 1972971 = 2959457) B2959457
theorem B8999525 : Blo 1971435 8999525 := bbase (se 4 (by rfl) ⟨843705, by rfl⟩ : syracuseStep 8999525 = 1687411) (by norm_num)
theorem B5999683 : Blo 1971435 5999683 := bstep (se 1 (by rfl) ⟨4499762, by rfl⟩ : syracuseStep 5999683 = 8999525) B8999525
theorem B7999577 : Blo 1971435 7999577 := bstep (se 2 (by rfl) ⟨2999841, by rfl⟩ : syracuseStep 7999577 = 5999683) B5999683
theorem B5333051 : Blo 1971435 5333051 := bstep (se 1 (by rfl) ⟨3999788, by rfl⟩ : syracuseStep 5333051 = 7999577) B7999577
theorem B14221469 : Blo 1971435 14221469 := bstep (se 3 (by rfl) ⟨2666525, by rfl⟩ : syracuseStep 14221469 = 5333051) B5333051
theorem B9480979 : Blo 1971435 9480979 := bstep (se 1 (by rfl) ⟨7110734, by rfl⟩ : syracuseStep 9480979 = 14221469) B14221469
theorem B12641305 : Blo 1971435 12641305 := bstep (se 2 (by rfl) ⟨4740489, by rfl⟩ : syracuseStep 12641305 = 9480979) B9480979
theorem B16855073 : Blo 1971435 16855073 := bstep (se 2 (by rfl) ⟨6320652, by rfl⟩ : syracuseStep 16855073 = 12641305) B12641305
theorem B11236715 : Blo 1971435 11236715 := bstep (se 1 (by rfl) ⟨8427536, by rfl⟩ : syracuseStep 11236715 = 16855073) B16855073
theorem B7491143 : Blo 1971435 7491143 := bstep (se 1 (by rfl) ⟨5618357, by rfl⟩ : syracuseStep 7491143 = 11236715) B11236715
theorem B4994095 : Blo 1971435 4994095 := bstep (se 1 (by rfl) ⟨3745571, by rfl⟩ : syracuseStep 4994095 = 7491143) B7491143
theorem B6658793 : Blo 1971435 6658793 := bstep (se 2 (by rfl) ⟨2497047, by rfl⟩ : syracuseStep 6658793 = 4994095) B4994095
theorem B4439195 : Blo 1971435 4439195 := bstep (se 1 (by rfl) ⟨3329396, by rfl⟩ : syracuseStep 4439195 = 6658793) B6658793
theorem B2959463 : Blo 1971435 2959463 := bstep (se 1 (by rfl) ⟨2219597, by rfl⟩ : syracuseStep 2959463 = 4439195) B4439195
theorem B1972975 : Blo 1971435 1972975 := bstep (se 1 (by rfl) ⟨1479731, by rfl⟩ : syracuseStep 1972975 = 2959463) B2959463
theorem B2959469 : Blo 1971435 2959469 := bbase (se 3 (by rfl) ⟨554900, by rfl⟩ : syracuseStep 2959469 = 1109801) (by norm_num)
theorem B1972979 : Blo 1971435 1972979 := bstep (se 1 (by rfl) ⟨1479734, by rfl⟩ : syracuseStep 1972979 = 2959469) B2959469
theorem B4439213 : Blo 1971435 4439213 := bbase (se 3 (by rfl) ⟨832352, by rfl⟩ : syracuseStep 4439213 = 1664705) (by norm_num)
theorem B2959475 : Blo 1971435 2959475 := bstep (se 1 (by rfl) ⟨2219606, by rfl⟩ : syracuseStep 2959475 = 4439213) B4439213
theorem B1972983 : Blo 1971435 1972983 := bstep (se 1 (by rfl) ⟨1479737, by rfl⟩ : syracuseStep 1972983 = 2959475) B2959475
theorem B6320693 : Blo 1971435 6320693 := bbase (se 5 (by rfl) ⟨296282, by rfl⟩ : syracuseStep 6320693 = 592565) (by norm_num)
theorem B4213795 : Blo 1971435 4213795 := bstep (se 1 (by rfl) ⟨3160346, by rfl⟩ : syracuseStep 4213795 = 6320693) B6320693
theorem B5618393 : Blo 1971435 5618393 := bstep (se 2 (by rfl) ⟨2106897, by rfl⟩ : syracuseStep 5618393 = 4213795) B4213795
theorem B3745595 : Blo 1971435 3745595 := bstep (se 1 (by rfl) ⟨2809196, by rfl⟩ : syracuseStep 3745595 = 5618393) B5618393
theorem B2497063 : Blo 1971435 2497063 := bstep (se 1 (by rfl) ⟨1872797, by rfl⟩ : syracuseStep 2497063 = 3745595) B3745595
theorem B3329417 : Blo 1971435 3329417 := bstep (se 2 (by rfl) ⟨1248531, by rfl⟩ : syracuseStep 3329417 = 2497063) B2497063
theorem B2219611 : Blo 1971435 2219611 := bstep (se 1 (by rfl) ⟨1664708, by rfl⟩ : syracuseStep 2219611 = 3329417) B3329417
theorem B2959481 : Blo 1971435 2959481 := bstep (se 2 (by rfl) ⟨1109805, by rfl⟩ : syracuseStep 2959481 = 2219611) B2219611
theorem B1972987 : Blo 1971435 1972987 := bstep (se 1 (by rfl) ⟨1479740, by rfl⟩ : syracuseStep 1972987 = 2959481) B2959481
theorem B2531137 : Blo 1971435 2531137 := bbase (se 2 (by rfl) ⟨949176, by rfl⟩ : syracuseStep 2531137 = 1898353) (by norm_num)
theorem B3374849 : Blo 1971435 3374849 := bstep (se 2 (by rfl) ⟨1265568, by rfl⟩ : syracuseStep 3374849 = 2531137) B2531137
theorem B2249899 : Blo 1971435 2249899 := bstep (se 1 (by rfl) ⟨1687424, by rfl⟩ : syracuseStep 2249899 = 3374849) B3374849
theorem B47997845 : Blo 1971435 47997845 := bstep (se 6 (by rfl) ⟨1124949, by rfl⟩ : syracuseStep 47997845 = 2249899) B2249899
theorem B31998563 : Blo 1971435 31998563 := bstep (se 1 (by rfl) ⟨23998922, by rfl⟩ : syracuseStep 31998563 = 47997845) B47997845
theorem B21332375 : Blo 1971435 21332375 := bstep (se 1 (by rfl) ⟨15999281, by rfl⟩ : syracuseStep 21332375 = 31998563) B31998563
theorem B14221583 : Blo 1971435 14221583 := bstep (se 1 (by rfl) ⟨10666187, by rfl⟩ : syracuseStep 14221583 = 21332375) B21332375
theorem B9481055 : Blo 1971435 9481055 := bstep (se 1 (by rfl) ⟨7110791, by rfl⟩ : syracuseStep 9481055 = 14221583) B14221583
theorem B25282813 : Blo 1971435 25282813 := bstep (se 3 (by rfl) ⟨4740527, by rfl⟩ : syracuseStep 25282813 = 9481055) B9481055
theorem B33710417 : Blo 1971435 33710417 := bstep (se 2 (by rfl) ⟨12641406, by rfl⟩ : syracuseStep 33710417 = 25282813) B25282813
theorem B22473611 : Blo 1971435 22473611 := bstep (se 1 (by rfl) ⟨16855208, by rfl⟩ : syracuseStep 22473611 = 33710417) B33710417
theorem B14982407 : Blo 1971435 14982407 := bstep (se 1 (by rfl) ⟨11236805, by rfl⟩ : syracuseStep 14982407 = 22473611) B22473611
theorem B9988271 : Blo 1971435 9988271 := bstep (se 1 (by rfl) ⟨7491203, by rfl⟩ : syracuseStep 9988271 = 14982407) B14982407
theorem B6658847 : Blo 1971435 6658847 := bstep (se 1 (by rfl) ⟨4994135, by rfl⟩ : syracuseStep 6658847 = 9988271) B9988271
theorem B4439231 : Blo 1971435 4439231 := bstep (se 1 (by rfl) ⟨3329423, by rfl⟩ : syracuseStep 4439231 = 6658847) B6658847
theorem B2959487 : Blo 1971435 2959487 := bstep (se 1 (by rfl) ⟨2219615, by rfl⟩ : syracuseStep 2959487 = 4439231) B4439231
theorem B1972991 : Blo 1971435 1972991 := bstep (se 1 (by rfl) ⟨1479743, by rfl⟩ : syracuseStep 1972991 = 2959487) B2959487
theorem B2959493 : Blo 1971435 2959493 := bbase (se 4 (by rfl) ⟨277452, by rfl⟩ : syracuseStep 2959493 = 554905) (by norm_num)
theorem B1972995 : Blo 1971435 1972995 := bstep (se 1 (by rfl) ⟨1479746, by rfl⟩ : syracuseStep 1972995 = 2959493) B2959493
theorem B3329437 : Blo 1971435 3329437 := bbase (se 3 (by rfl) ⟨624269, by rfl⟩ : syracuseStep 3329437 = 1248539) (by norm_num)
theorem B4439249 : Blo 1971435 4439249 := bstep (se 2 (by rfl) ⟨1664718, by rfl⟩ : syracuseStep 4439249 = 3329437) B3329437
theorem B2959499 : Blo 1971435 2959499 := bstep (se 1 (by rfl) ⟨2219624, by rfl⟩ : syracuseStep 2959499 = 4439249) B4439249
theorem B1972999 : Blo 1971435 1972999 := bstep (se 1 (by rfl) ⟨1479749, by rfl⟩ : syracuseStep 1972999 = 2959499) B2959499
theorem B2219629 : Blo 1971435 2219629 := bbase (se 3 (by rfl) ⟨416180, by rfl⟩ : syracuseStep 2219629 = 832361) (by norm_num)
theorem B2959505 : Blo 1971435 2959505 := bstep (se 2 (by rfl) ⟨1109814, by rfl⟩ : syracuseStep 2959505 = 2219629) B2219629
theorem B1973003 : Blo 1971435 1973003 := bstep (se 1 (by rfl) ⟨1479752, by rfl⟩ : syracuseStep 1973003 = 2959505) B2959505
theorem B6658901 : Blo 1971435 6658901 := bbase (se 9 (by rfl) ⟨19508, by rfl⟩ : syracuseStep 6658901 = 39017) (by norm_num)
theorem B4439267 : Blo 1971435 4439267 := bstep (se 1 (by rfl) ⟨3329450, by rfl⟩ : syracuseStep 4439267 = 6658901) B6658901
theorem B2959511 : Blo 1971435 2959511 := bstep (se 1 (by rfl) ⟨2219633, by rfl⟩ : syracuseStep 2959511 = 4439267) B4439267
theorem B1973007 : Blo 1971435 1973007 := bstep (se 1 (by rfl) ⟨1479755, by rfl⟩ : syracuseStep 1973007 = 2959511) B2959511
theorem B2959517 : Blo 1971435 2959517 := bbase (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) (by norm_num)
theorem B1973011 : Blo 1971435 1973011 := bstep (se 1 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 1973011 = 2959517) B2959517
theorem B4439285 : Blo 1971435 4439285 := bbase (se 5 (by rfl) ⟨208091, by rfl⟩ : syracuseStep 4439285 = 416183) (by norm_num)
theorem B2959523 : Blo 1971435 2959523 := bstep (se 1 (by rfl) ⟨2219642, by rfl⟩ : syracuseStep 2959523 = 4439285) B4439285
theorem B1973015 : Blo 1971435 1973015 := bstep (se 1 (by rfl) ⟨1479761, by rfl⟩ : syracuseStep 1973015 = 2959523) B2959523
theorem B2531173 : Blo 1971435 2531173 := bbase (se 4 (by rfl) ⟨237297, by rfl⟩ : syracuseStep 2531173 = 474595) (by norm_num)
theorem B3374897 : Blo 1971435 3374897 := bstep (se 2 (by rfl) ⟨1265586, by rfl⟩ : syracuseStep 3374897 = 2531173) B2531173
theorem B35998901 : Blo 1971435 35998901 := bstep (se 5 (by rfl) ⟨1687448, by rfl⟩ : syracuseStep 35998901 = 3374897) B3374897
theorem B23999267 : Blo 1971435 23999267 := bstep (se 1 (by rfl) ⟨17999450, by rfl⟩ : syracuseStep 23999267 = 35998901) B35998901
theorem B63998045 : Blo 1971435 63998045 := bstep (se 3 (by rfl) ⟨11999633, by rfl⟩ : syracuseStep 63998045 = 23999267) B23999267
theorem B42665363 : Blo 1971435 42665363 := bstep (se 1 (by rfl) ⟨31999022, by rfl⟩ : syracuseStep 42665363 = 63998045) B63998045
theorem B28443575 : Blo 1971435 28443575 := bstep (se 1 (by rfl) ⟨21332681, by rfl⟩ : syracuseStep 28443575 = 42665363) B42665363
theorem B18962383 : Blo 1971435 18962383 := bstep (se 1 (by rfl) ⟨14221787, by rfl⟩ : syracuseStep 18962383 = 28443575) B28443575
theorem B25283177 : Blo 1971435 25283177 := bstep (se 2 (by rfl) ⟨9481191, by rfl⟩ : syracuseStep 25283177 = 18962383) B18962383
theorem B16855451 : Blo 1971435 16855451 := bstep (se 1 (by rfl) ⟨12641588, by rfl⟩ : syracuseStep 16855451 = 25283177) B25283177
theorem B11236967 : Blo 1971435 11236967 := bstep (se 1 (by rfl) ⟨8427725, by rfl⟩ : syracuseStep 11236967 = 16855451) B16855451
theorem B7491311 : Blo 1971435 7491311 := bstep (se 1 (by rfl) ⟨5618483, by rfl⟩ : syracuseStep 7491311 = 11236967) B11236967
theorem B4994207 : Blo 1971435 4994207 := bstep (se 1 (by rfl) ⟨3745655, by rfl⟩ : syracuseStep 4994207 = 7491311) B7491311
theorem B3329471 : Blo 1971435 3329471 := bstep (se 1 (by rfl) ⟨2497103, by rfl⟩ : syracuseStep 3329471 = 4994207) B4994207
theorem B2219647 : Blo 1971435 2219647 := bstep (se 1 (by rfl) ⟨1664735, by rfl⟩ : syracuseStep 2219647 = 3329471) B3329471
theorem B2959529 : Blo 1971435 2959529 := bstep (se 2 (by rfl) ⟨1109823, by rfl⟩ : syracuseStep 2959529 = 2219647) B2219647
theorem B1973019 : Blo 1971435 1973019 := bstep (se 1 (by rfl) ⟨1479764, by rfl⟩ : syracuseStep 1973019 = 2959529) B2959529
theorem B2565713 : Blo 1971435 2565713 := bbase (se 2 (by rfl) ⟨962142, by rfl⟩ : syracuseStep 2565713 = 1924285) (by norm_num)
theorem B6841901 : Blo 1971435 6841901 := bstep (se 3 (by rfl) ⟨1282856, by rfl⟩ : syracuseStep 6841901 = 2565713) B2565713
theorem B4561267 : Blo 1971435 4561267 := bstep (se 1 (by rfl) ⟨3420950, by rfl⟩ : syracuseStep 4561267 = 6841901) B6841901
theorem B6081689 : Blo 1971435 6081689 := bstep (se 2 (by rfl) ⟨2280633, by rfl⟩ : syracuseStep 6081689 = 4561267) B4561267
theorem B4054459 : Blo 1971435 4054459 := bstep (se 1 (by rfl) ⟨3040844, by rfl⟩ : syracuseStep 4054459 = 6081689) B6081689
theorem B5405945 : Blo 1971435 5405945 := bstep (se 2 (by rfl) ⟨2027229, by rfl⟩ : syracuseStep 5405945 = 4054459) B4054459
theorem B57663413 : Blo 1971435 57663413 := bstep (se 5 (by rfl) ⟨2702972, by rfl⟩ : syracuseStep 57663413 = 5405945) B5405945
theorem B38442275 : Blo 1971435 38442275 := bstep (se 1 (by rfl) ⟨28831706, by rfl⟩ : syracuseStep 38442275 = 57663413) B57663413
theorem B25628183 : Blo 1971435 25628183 := bstep (se 1 (by rfl) ⟨19221137, by rfl⟩ : syracuseStep 25628183 = 38442275) B38442275
theorem B17085455 : Blo 1971435 17085455 := bstep (se 1 (by rfl) ⟨12814091, by rfl⟩ : syracuseStep 17085455 = 25628183) B25628183
theorem B11390303 : Blo 1971435 11390303 := bstep (se 1 (by rfl) ⟨8542727, by rfl⟩ : syracuseStep 11390303 = 17085455) B17085455
theorem B7593535 : Blo 1971435 7593535 := bstep (se 1 (by rfl) ⟨5695151, by rfl⟩ : syracuseStep 7593535 = 11390303) B11390303
theorem B10124713 : Blo 1971435 10124713 := bstep (se 2 (by rfl) ⟨3796767, by rfl⟩ : syracuseStep 10124713 = 7593535) B7593535
theorem B13499617 : Blo 1971435 13499617 := bstep (se 2 (by rfl) ⟨5062356, by rfl⟩ : syracuseStep 13499617 = 10124713) B10124713
theorem B17999489 : Blo 1971435 17999489 := bstep (se 2 (by rfl) ⟨6749808, by rfl⟩ : syracuseStep 17999489 = 13499617) B13499617
theorem B11999659 : Blo 1971435 11999659 := bstep (se 1 (by rfl) ⟨8999744, by rfl⟩ : syracuseStep 11999659 = 17999489) B17999489
theorem B15999545 : Blo 1971435 15999545 := bstep (se 2 (by rfl) ⟨5999829, by rfl⟩ : syracuseStep 15999545 = 11999659) B11999659
theorem B10666363 : Blo 1971435 10666363 := bstep (se 1 (by rfl) ⟨7999772, by rfl⟩ : syracuseStep 10666363 = 15999545) B15999545
theorem B14221817 : Blo 1971435 14221817 := bstep (se 2 (by rfl) ⟨5333181, by rfl⟩ : syracuseStep 14221817 = 10666363) B10666363
theorem B9481211 : Blo 1971435 9481211 := bstep (se 1 (by rfl) ⟨7110908, by rfl⟩ : syracuseStep 9481211 = 14221817) B14221817
theorem B6320807 : Blo 1971435 6320807 := bstep (se 1 (by rfl) ⟨4740605, by rfl⟩ : syracuseStep 6320807 = 9481211) B9481211
theorem B4213871 : Blo 1971435 4213871 := bstep (se 1 (by rfl) ⟨3160403, by rfl⟩ : syracuseStep 4213871 = 6320807) B6320807
theorem B2809247 : Blo 1971435 2809247 := bstep (se 1 (by rfl) ⟨2106935, by rfl⟩ : syracuseStep 2809247 = 4213871) B4213871
theorem B7491325 : Blo 1971435 7491325 := bstep (se 3 (by rfl) ⟨1404623, by rfl⟩ : syracuseStep 7491325 = 2809247) B2809247
theorem B9988433 : Blo 1971435 9988433 := bstep (se 2 (by rfl) ⟨3745662, by rfl⟩ : syracuseStep 9988433 = 7491325) B7491325
theorem B6658955 : Blo 1971435 6658955 := bstep (se 1 (by rfl) ⟨4994216, by rfl⟩ : syracuseStep 6658955 = 9988433) B9988433
theorem B4439303 : Blo 1971435 4439303 := bstep (se 1 (by rfl) ⟨3329477, by rfl⟩ : syracuseStep 4439303 = 6658955) B6658955
theorem B2959535 : Blo 1971435 2959535 := bstep (se 1 (by rfl) ⟨2219651, by rfl⟩ : syracuseStep 2959535 = 4439303) B4439303
theorem B1973023 : Blo 1971435 1973023 := bstep (se 1 (by rfl) ⟨1479767, by rfl⟩ : syracuseStep 1973023 = 2959535) B2959535
theorem B2959541 : Blo 1971435 2959541 := bbase (se 5 (by rfl) ⟨138728, by rfl⟩ : syracuseStep 2959541 = 277457) (by norm_num)
theorem B1973027 : Blo 1971435 1973027 := bstep (se 1 (by rfl) ⟨1479770, by rfl⟩ : syracuseStep 1973027 = 2959541) B2959541
theorem B4994237 : Blo 1971435 4994237 := bbase (se 3 (by rfl) ⟨936419, by rfl⟩ : syracuseStep 4994237 = 1872839) (by norm_num)
theorem B3329491 : Blo 1971435 3329491 := bstep (se 1 (by rfl) ⟨2497118, by rfl⟩ : syracuseStep 3329491 = 4994237) B4994237
theorem B4439321 : Blo 1971435 4439321 := bstep (se 2 (by rfl) ⟨1664745, by rfl⟩ : syracuseStep 4439321 = 3329491) B3329491
theorem B2959547 : Blo 1971435 2959547 := bstep (se 1 (by rfl) ⟨2219660, by rfl⟩ : syracuseStep 2959547 = 4439321) B4439321
theorem B1973031 : Blo 1971435 1973031 := bstep (se 1 (by rfl) ⟨1479773, by rfl⟩ : syracuseStep 1973031 = 2959547) B2959547
theorem B2219665 : Blo 1971435 2219665 := bbase (se 2 (by rfl) ⟨832374, by rfl⟩ : syracuseStep 2219665 = 1664749) (by norm_num)
theorem B2959553 : Blo 1971435 2959553 := bstep (se 2 (by rfl) ⟨1109832, by rfl⟩ : syracuseStep 2959553 = 2219665) B2219665
theorem B1973035 : Blo 1971435 1973035 := bstep (se 1 (by rfl) ⟨1479776, by rfl⟩ : syracuseStep 1973035 = 2959553) B2959553
theorem B3745693 : Blo 1971435 3745693 := bbase (se 3 (by rfl) ⟨702317, by rfl⟩ : syracuseStep 3745693 = 1404635) (by norm_num)
theorem B4994257 : Blo 1971435 4994257 := bstep (se 2 (by rfl) ⟨1872846, by rfl⟩ : syracuseStep 4994257 = 3745693) B3745693
theorem B6659009 : Blo 1971435 6659009 := bstep (se 2 (by rfl) ⟨2497128, by rfl⟩ : syracuseStep 6659009 = 4994257) B4994257
theorem B4439339 : Blo 1971435 4439339 := bstep (se 1 (by rfl) ⟨3329504, by rfl⟩ : syracuseStep 4439339 = 6659009) B6659009
theorem B2959559 : Blo 1971435 2959559 := bstep (se 1 (by rfl) ⟨2219669, by rfl⟩ : syracuseStep 2959559 = 4439339) B4439339
theorem B1973039 : Blo 1971435 1973039 := bstep (se 1 (by rfl) ⟨1479779, by rfl⟩ : syracuseStep 1973039 = 2959559) B2959559
theorem B2959565 : Blo 1971435 2959565 := bbase (se 3 (by rfl) ⟨554918, by rfl⟩ : syracuseStep 2959565 = 1109837) (by norm_num)
theorem B1973043 : Blo 1971435 1973043 := bstep (se 1 (by rfl) ⟨1479782, by rfl⟩ : syracuseStep 1973043 = 2959565) B2959565
theorem B4439357 : Blo 1971435 4439357 := bbase (se 3 (by rfl) ⟨832379, by rfl⟩ : syracuseStep 4439357 = 1664759) (by norm_num)
theorem B2959571 : Blo 1971435 2959571 := bstep (se 1 (by rfl) ⟨2219678, by rfl⟩ : syracuseStep 2959571 = 4439357) B4439357
theorem B1973047 : Blo 1971435 1973047 := bstep (se 1 (by rfl) ⟨1479785, by rfl⟩ : syracuseStep 1973047 = 2959571) B2959571
theorem B3329525 : Blo 1971435 3329525 := bbase (se 5 (by rfl) ⟨156071, by rfl⟩ : syracuseStep 3329525 = 312143) (by norm_num)
theorem B2219683 : Blo 1971435 2219683 := bstep (se 1 (by rfl) ⟨1664762, by rfl⟩ : syracuseStep 2219683 = 3329525) B3329525
theorem B2959577 : Blo 1971435 2959577 := bstep (se 2 (by rfl) ⟨1109841, by rfl⟩ : syracuseStep 2959577 = 2219683) B2219683
theorem B1973051 : Blo 1971435 1973051 := bstep (se 1 (by rfl) ⟨1479788, by rfl⟩ : syracuseStep 1973051 = 2959577) B2959577
theorem B2370341 : Blo 1971435 2370341 := bbase (se 4 (by rfl) ⟨222219, by rfl⟩ : syracuseStep 2370341 = 444439) (by norm_num)
theorem B6320909 : Blo 1971435 6320909 := bstep (se 3 (by rfl) ⟨1185170, by rfl⟩ : syracuseStep 6320909 = 2370341) B2370341
theorem B4213939 : Blo 1971435 4213939 := bstep (se 1 (by rfl) ⟨3160454, by rfl⟩ : syracuseStep 4213939 = 6320909) B6320909
theorem B5618585 : Blo 1971435 5618585 := bstep (se 2 (by rfl) ⟨2106969, by rfl⟩ : syracuseStep 5618585 = 4213939) B4213939
theorem B14982893 : Blo 1971435 14982893 := bstep (se 3 (by rfl) ⟨2809292, by rfl⟩ : syracuseStep 14982893 = 5618585) B5618585
theorem B9988595 : Blo 1971435 9988595 := bstep (se 1 (by rfl) ⟨7491446, by rfl⟩ : syracuseStep 9988595 = 14982893) B14982893
theorem B6659063 : Blo 1971435 6659063 := bstep (se 1 (by rfl) ⟨4994297, by rfl⟩ : syracuseStep 6659063 = 9988595) B9988595
theorem B4439375 : Blo 1971435 4439375 := bstep (se 1 (by rfl) ⟨3329531, by rfl⟩ : syracuseStep 4439375 = 6659063) B6659063
theorem B2959583 : Blo 1971435 2959583 := bstep (se 1 (by rfl) ⟨2219687, by rfl⟩ : syracuseStep 2959583 = 4439375) B4439375
theorem B1973055 : Blo 1971435 1973055 := bstep (se 1 (by rfl) ⟨1479791, by rfl⟩ : syracuseStep 1973055 = 2959583) B2959583
theorem B2959589 : Blo 1971435 2959589 := bbase (se 4 (by rfl) ⟨277461, by rfl⟩ : syracuseStep 2959589 = 554923) (by norm_num)
theorem B1973059 : Blo 1971435 1973059 := bstep (se 1 (by rfl) ⟨1479794, by rfl⟩ : syracuseStep 1973059 = 2959589) B2959589
theorem B4213957 : Blo 1971435 4213957 := bbase (se 4 (by rfl) ⟨395058, by rfl⟩ : syracuseStep 4213957 = 790117) (by norm_num)
theorem B5618609 : Blo 1971435 5618609 := bstep (se 2 (by rfl) ⟨2106978, by rfl⟩ : syracuseStep 5618609 = 4213957) B4213957
theorem B3745739 : Blo 1971435 3745739 := bstep (se 1 (by rfl) ⟨2809304, by rfl⟩ : syracuseStep 3745739 = 5618609) B5618609
theorem B2497159 : Blo 1971435 2497159 := bstep (se 1 (by rfl) ⟨1872869, by rfl⟩ : syracuseStep 2497159 = 3745739) B3745739
theorem B3329545 : Blo 1971435 3329545 := bstep (se 2 (by rfl) ⟨1248579, by rfl⟩ : syracuseStep 3329545 = 2497159) B2497159
theorem B4439393 : Blo 1971435 4439393 := bstep (se 2 (by rfl) ⟨1664772, by rfl⟩ : syracuseStep 4439393 = 3329545) B3329545
theorem B2959595 : Blo 1971435 2959595 := bstep (se 1 (by rfl) ⟨2219696, by rfl⟩ : syracuseStep 2959595 = 4439393) B4439393
theorem B1973063 : Blo 1971435 1973063 := bstep (se 1 (by rfl) ⟨1479797, by rfl⟩ : syracuseStep 1973063 = 2959595) B2959595
theorem B2219701 : Blo 1971435 2219701 := bbase (se 5 (by rfl) ⟨104048, by rfl⟩ : syracuseStep 2219701 = 208097) (by norm_num)
theorem B2959601 : Blo 1971435 2959601 := bstep (se 2 (by rfl) ⟨1109850, by rfl⟩ : syracuseStep 2959601 = 2219701) B2219701
theorem B1973067 : Blo 1971435 1973067 := bstep (se 1 (by rfl) ⟨1479800, by rfl⟩ : syracuseStep 1973067 = 2959601) B2959601
theorem B2497169 : Blo 1971435 2497169 := bbase (se 2 (by rfl) ⟨936438, by rfl⟩ : syracuseStep 2497169 = 1872877) (by norm_num)
theorem B6659117 : Blo 1971435 6659117 := bstep (se 3 (by rfl) ⟨1248584, by rfl⟩ : syracuseStep 6659117 = 2497169) B2497169
theorem B4439411 : Blo 1971435 4439411 := bstep (se 1 (by rfl) ⟨3329558, by rfl⟩ : syracuseStep 4439411 = 6659117) B6659117
theorem B2959607 : Blo 1971435 2959607 := bstep (se 1 (by rfl) ⟨2219705, by rfl⟩ : syracuseStep 2959607 = 4439411) B4439411
theorem B1973071 : Blo 1971435 1973071 := bstep (se 1 (by rfl) ⟨1479803, by rfl⟩ : syracuseStep 1973071 = 2959607) B2959607
theorem B2959613 : Blo 1971435 2959613 := bbase (se 3 (by rfl) ⟨554927, by rfl⟩ : syracuseStep 2959613 = 1109855) (by norm_num)
theorem B1973075 : Blo 1971435 1973075 := bstep (se 1 (by rfl) ⟨1479806, by rfl⟩ : syracuseStep 1973075 = 2959613) B2959613
theorem B4439429 : Blo 1971435 4439429 := bbase (se 4 (by rfl) ⟨416196, by rfl⟩ : syracuseStep 4439429 = 832393) (by norm_num)
theorem B2959619 : Blo 1971435 2959619 := bstep (se 1 (by rfl) ⟨2219714, by rfl⟩ : syracuseStep 2959619 = 4439429) B4439429
theorem B1973079 : Blo 1971435 1973079 := bstep (se 1 (by rfl) ⟨1479809, by rfl⟩ : syracuseStep 1973079 = 2959619) B2959619
theorem B2809333 : Blo 1971435 2809333 := bbase (se 5 (by rfl) ⟨131687, by rfl⟩ : syracuseStep 2809333 = 263375) (by norm_num)
theorem B3745777 : Blo 1971435 3745777 := bstep (se 2 (by rfl) ⟨1404666, by rfl⟩ : syracuseStep 3745777 = 2809333) B2809333
theorem B4994369 : Blo 1971435 4994369 := bstep (se 2 (by rfl) ⟨1872888, by rfl⟩ : syracuseStep 4994369 = 3745777) B3745777
theorem B3329579 : Blo 1971435 3329579 := bstep (se 1 (by rfl) ⟨2497184, by rfl⟩ : syracuseStep 3329579 = 4994369) B4994369
theorem B2219719 : Blo 1971435 2219719 := bstep (se 1 (by rfl) ⟨1664789, by rfl⟩ : syracuseStep 2219719 = 3329579) B3329579
theorem B2959625 : Blo 1971435 2959625 := bstep (se 2 (by rfl) ⟨1109859, by rfl⟩ : syracuseStep 2959625 = 2219719) B2219719
theorem B1973083 : Blo 1971435 1973083 := bstep (se 1 (by rfl) ⟨1479812, by rfl⟩ : syracuseStep 1973083 = 2959625) B2959625
theorem B9988757 : Blo 1971435 9988757 := bbase (se 6 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 9988757 = 468223) (by norm_num)
theorem B6659171 : Blo 1971435 6659171 := bstep (se 1 (by rfl) ⟨4994378, by rfl⟩ : syracuseStep 6659171 = 9988757) B9988757
theorem B4439447 : Blo 1971435 4439447 := bstep (se 1 (by rfl) ⟨3329585, by rfl⟩ : syracuseStep 4439447 = 6659171) B6659171
theorem B2959631 : Blo 1971435 2959631 := bstep (se 1 (by rfl) ⟨2219723, by rfl⟩ : syracuseStep 2959631 = 4439447) B4439447
theorem B1973087 : Blo 1971435 1973087 := bstep (se 1 (by rfl) ⟨1479815, by rfl⟩ : syracuseStep 1973087 = 2959631) B2959631
theorem B2959637 : Blo 1971435 2959637 := bbase (se 6 (by rfl) ⟨69366, by rfl⟩ : syracuseStep 2959637 = 138733) (by norm_num)
theorem B1973091 : Blo 1971435 1973091 := bstep (se 1 (by rfl) ⟨1479818, by rfl⟩ : syracuseStep 1973091 = 2959637) B2959637
theorem B2370389 : Blo 1971435 2370389 := bbase (se 9 (by rfl) ⟨6944, by rfl⟩ : syracuseStep 2370389 = 13889) (by norm_num)
theorem B25284149 : Blo 1971435 25284149 := bstep (se 5 (by rfl) ⟨1185194, by rfl⟩ : syracuseStep 25284149 = 2370389) B2370389
theorem B16856099 : Blo 1971435 16856099 := bstep (se 1 (by rfl) ⟨12642074, by rfl⟩ : syracuseStep 16856099 = 25284149) B25284149
theorem B11237399 : Blo 1971435 11237399 := bstep (se 1 (by rfl) ⟨8428049, by rfl⟩ : syracuseStep 11237399 = 16856099) B16856099
theorem B7491599 : Blo 1971435 7491599 := bstep (se 1 (by rfl) ⟨5618699, by rfl⟩ : syracuseStep 7491599 = 11237399) B11237399
theorem B4994399 : Blo 1971435 4994399 := bstep (se 1 (by rfl) ⟨3745799, by rfl⟩ : syracuseStep 4994399 = 7491599) B7491599
theorem B3329599 : Blo 1971435 3329599 := bstep (se 1 (by rfl) ⟨2497199, by rfl⟩ : syracuseStep 3329599 = 4994399) B4994399
theorem B4439465 : Blo 1971435 4439465 := bstep (se 2 (by rfl) ⟨1664799, by rfl⟩ : syracuseStep 4439465 = 3329599) B3329599
theorem B2959643 : Blo 1971435 2959643 := bstep (se 1 (by rfl) ⟨2219732, by rfl⟩ : syracuseStep 2959643 = 4439465) B4439465
theorem B1973095 : Blo 1971435 1973095 := bstep (se 1 (by rfl) ⟨1479821, by rfl⟩ : syracuseStep 1973095 = 2959643) B2959643
theorem B2219737 : Blo 1971435 2219737 := bbase (se 2 (by rfl) ⟨832401, by rfl⟩ : syracuseStep 2219737 = 1664803) (by norm_num)
theorem B2959649 : Blo 1971435 2959649 := bstep (se 2 (by rfl) ⟨1109868, by rfl⟩ : syracuseStep 2959649 = 2219737) B2219737
theorem B1973099 : Blo 1971435 1973099 := bstep (se 1 (by rfl) ⟨1479824, by rfl⟩ : syracuseStep 1973099 = 2959649) B2959649
theorem B2107021 : Blo 1971435 2107021 := bbase (se 3 (by rfl) ⟨395066, by rfl⟩ : syracuseStep 2107021 = 790133) (by norm_num)
theorem B2809361 : Blo 1971435 2809361 := bstep (se 2 (by rfl) ⟨1053510, by rfl⟩ : syracuseStep 2809361 = 2107021) B2107021
theorem B7491629 : Blo 1971435 7491629 := bstep (se 3 (by rfl) ⟨1404680, by rfl⟩ : syracuseStep 7491629 = 2809361) B2809361
theorem B4994419 : Blo 1971435 4994419 := bstep (se 1 (by rfl) ⟨3745814, by rfl⟩ : syracuseStep 4994419 = 7491629) B7491629
theorem B6659225 : Blo 1971435 6659225 := bstep (se 2 (by rfl) ⟨2497209, by rfl⟩ : syracuseStep 6659225 = 4994419) B4994419
theorem B4439483 : Blo 1971435 4439483 := bstep (se 1 (by rfl) ⟨3329612, by rfl⟩ : syracuseStep 4439483 = 6659225) B6659225
theorem B2959655 : Blo 1971435 2959655 := bstep (se 1 (by rfl) ⟨2219741, by rfl⟩ : syracuseStep 2959655 = 4439483) B4439483
theorem B1973103 : Blo 1971435 1973103 := bstep (se 1 (by rfl) ⟨1479827, by rfl⟩ : syracuseStep 1973103 = 2959655) B2959655
theorem B2959661 : Blo 1971435 2959661 := bbase (se 3 (by rfl) ⟨554936, by rfl⟩ : syracuseStep 2959661 = 1109873) (by norm_num)
theorem B1973107 : Blo 1971435 1973107 := bstep (se 1 (by rfl) ⟨1479830, by rfl⟩ : syracuseStep 1973107 = 2959661) B2959661
theorem B4439501 : Blo 1971435 4439501 := bbase (se 3 (by rfl) ⟨832406, by rfl⟩ : syracuseStep 4439501 = 1664813) (by norm_num)
theorem B2959667 : Blo 1971435 2959667 := bstep (se 1 (by rfl) ⟨2219750, by rfl⟩ : syracuseStep 2959667 = 4439501) B4439501
theorem B1973111 : Blo 1971435 1973111 := bstep (se 1 (by rfl) ⟨1479833, by rfl⟩ : syracuseStep 1973111 = 2959667) B2959667
theorem B2497225 : Blo 1971435 2497225 := bbase (se 2 (by rfl) ⟨936459, by rfl⟩ : syracuseStep 2497225 = 1872919) (by norm_num)
theorem B3329633 : Blo 1971435 3329633 := bstep (se 2 (by rfl) ⟨1248612, by rfl⟩ : syracuseStep 3329633 = 2497225) B2497225
theorem B2219755 : Blo 1971435 2219755 := bstep (se 1 (by rfl) ⟨1664816, by rfl⟩ : syracuseStep 2219755 = 3329633) B3329633
theorem B2959673 : Blo 1971435 2959673 := bstep (se 2 (by rfl) ⟨1109877, by rfl⟩ : syracuseStep 2959673 = 2219755) B2219755
theorem B1973115 : Blo 1971435 1973115 := bstep (se 1 (by rfl) ⟨1479836, by rfl⟩ : syracuseStep 1973115 = 2959673) B2959673
theorem B7111253 : Blo 1971435 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B18963341 : Blo 1971435 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B12642227 : Blo 1971435 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B8428151 : Blo 1971435 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B22475069 : Blo 1971435 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B14983379 : Blo 1971435 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B9988919 : Blo 1971435 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B6659279 : Blo 1971435 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B4439519 : Blo 1971435 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B2959679 : Blo 1971435 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B1973119 : Blo 1971435 1973119 := bstep (se 1 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 1973119 = 2959679) B2959679
theorem B2959685 : Blo 1971435 2959685 := bbase (se 4 (by rfl) ⟨277470, by rfl⟩ : syracuseStep 2959685 = 554941) (by norm_num)
theorem B1973123 : Blo 1971435 1973123 := bstep (se 1 (by rfl) ⟨1479842, by rfl⟩ : syracuseStep 1973123 = 2959685) B2959685
theorem B3329653 : Blo 1971435 3329653 := bbase (se 5 (by rfl) ⟨156077, by rfl⟩ : syracuseStep 3329653 = 312155) (by norm_num)
theorem B4439537 : Blo 1971435 4439537 := bstep (se 2 (by rfl) ⟨1664826, by rfl⟩ : syracuseStep 4439537 = 3329653) B3329653
theorem B2959691 : Blo 1971435 2959691 := bstep (se 1 (by rfl) ⟨2219768, by rfl⟩ : syracuseStep 2959691 = 4439537) B4439537
theorem B1973127 : Blo 1971435 1973127 := bstep (se 1 (by rfl) ⟨1479845, by rfl⟩ : syracuseStep 1973127 = 2959691) B2959691
theorem B2219773 : Blo 1971435 2219773 := bbase (se 3 (by rfl) ⟨416207, by rfl⟩ : syracuseStep 2219773 = 832415) (by norm_num)
theorem B2959697 : Blo 1971435 2959697 := bstep (se 2 (by rfl) ⟨1109886, by rfl⟩ : syracuseStep 2959697 = 2219773) B2219773
theorem B1973131 : Blo 1971435 1973131 := bstep (se 1 (by rfl) ⟨1479848, by rfl⟩ : syracuseStep 1973131 = 2959697) B2959697
theorem B6659333 : Blo 1971435 6659333 := bbase (se 4 (by rfl) ⟨624312, by rfl⟩ : syracuseStep 6659333 = 1248625) (by norm_num)
theorem B4439555 : Blo 1971435 4439555 := bstep (se 1 (by rfl) ⟨3329666, by rfl⟩ : syracuseStep 4439555 = 6659333) B6659333
theorem B2959703 : Blo 1971435 2959703 := bstep (se 1 (by rfl) ⟨2219777, by rfl⟩ : syracuseStep 2959703 = 4439555) B4439555
theorem B1973135 : Blo 1971435 1973135 := bstep (se 1 (by rfl) ⟨1479851, by rfl⟩ : syracuseStep 1973135 = 2959703) B2959703
theorem B2959709 : Blo 1971435 2959709 := bbase (se 3 (by rfl) ⟨554945, by rfl⟩ : syracuseStep 2959709 = 1109891) (by norm_num)
theorem B1973139 : Blo 1971435 1973139 := bstep (se 1 (by rfl) ⟨1479854, by rfl⟩ : syracuseStep 1973139 = 2959709) B2959709
theorem B4439573 : Blo 1971435 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B2959715 : Blo 1971435 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B1973143 : Blo 1971435 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B7491797 : Blo 1971435 7491797 := bbase (se 7 (by rfl) ⟨87794, by rfl⟩ : syracuseStep 7491797 = 175589) (by norm_num)
theorem B4994531 : Blo 1971435 4994531 := bstep (se 1 (by rfl) ⟨3745898, by rfl⟩ : syracuseStep 4994531 = 7491797) B7491797
theorem B3329687 : Blo 1971435 3329687 := bstep (se 1 (by rfl) ⟨2497265, by rfl⟩ : syracuseStep 3329687 = 4994531) B4994531
theorem B2219791 : Blo 1971435 2219791 := bstep (se 1 (by rfl) ⟨1664843, by rfl⟩ : syracuseStep 2219791 = 3329687) B3329687
theorem B2959721 : Blo 1971435 2959721 := bstep (se 2 (by rfl) ⟨1109895, by rfl⟩ : syracuseStep 2959721 = 2219791) B2219791
theorem B1973147 : Blo 1971435 1973147 := bstep (se 1 (by rfl) ⟨1479860, by rfl⟩ : syracuseStep 1973147 = 2959721) B2959721
theorem B11237717 : Blo 1971435 11237717 := bbase (se 10 (by rfl) ⟨16461, by rfl⟩ : syracuseStep 11237717 = 32923) (by norm_num)
theorem B7491811 : Blo 1971435 7491811 := bstep (se 1 (by rfl) ⟨5618858, by rfl⟩ : syracuseStep 7491811 = 11237717) B11237717
theorem B9989081 : Blo 1971435 9989081 := bstep (se 2 (by rfl) ⟨3745905, by rfl⟩ : syracuseStep 9989081 = 7491811) B7491811
theorem B6659387 : Blo 1971435 6659387 := bstep (se 1 (by rfl) ⟨4994540, by rfl⟩ : syracuseStep 6659387 = 9989081) B9989081
theorem B4439591 : Blo 1971435 4439591 := bstep (se 1 (by rfl) ⟨3329693, by rfl⟩ : syracuseStep 4439591 = 6659387) B6659387
theorem B2959727 : Blo 1971435 2959727 := bstep (se 1 (by rfl) ⟨2219795, by rfl⟩ : syracuseStep 2959727 = 4439591) B4439591
theorem B1973151 : Blo 1971435 1973151 := bstep (se 1 (by rfl) ⟨1479863, by rfl⟩ : syracuseStep 1973151 = 2959727) B2959727
theorem B2959733 : Blo 1971435 2959733 := bbase (se 5 (by rfl) ⟨138737, by rfl⟩ : syracuseStep 2959733 = 277475) (by norm_num)
theorem B1973155 : Blo 1971435 1973155 := bstep (se 1 (by rfl) ⟨1479866, by rfl⟩ : syracuseStep 1973155 = 2959733) B2959733
theorem B2107081 : Blo 1971435 2107081 := bbase (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) (by norm_num)
theorem B2809441 : Blo 1971435 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B3745921 : Blo 1971435 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B4994561 : Blo 1971435 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B3329707 : Blo 1971435 3329707 := bstep (se 1 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 3329707 = 4994561) B4994561
theorem B4439609 : Blo 1971435 4439609 := bstep (se 2 (by rfl) ⟨1664853, by rfl⟩ : syracuseStep 4439609 = 3329707) B3329707
theorem B2959739 : Blo 1971435 2959739 := bstep (se 1 (by rfl) ⟨2219804, by rfl⟩ : syracuseStep 2959739 = 4439609) B4439609
theorem B1973159 : Blo 1971435 1973159 := bstep (se 1 (by rfl) ⟨1479869, by rfl⟩ : syracuseStep 1973159 = 2959739) B2959739
theorem B2219809 : Blo 1971435 2219809 := bbase (se 2 (by rfl) ⟨832428, by rfl⟩ : syracuseStep 2219809 = 1664857) (by norm_num)
theorem B2959745 : Blo 1971435 2959745 := bstep (se 2 (by rfl) ⟨1109904, by rfl⟩ : syracuseStep 2959745 = 2219809) B2219809
theorem B1973163 : Blo 1971435 1973163 := bstep (se 1 (by rfl) ⟨1479872, by rfl⟩ : syracuseStep 1973163 = 2959745) B2959745
theorem B4994581 : Blo 1971435 4994581 := bbase (se 6 (by rfl) ⟨117060, by rfl⟩ : syracuseStep 4994581 = 234121) (by norm_num)
theorem B6659441 : Blo 1971435 6659441 := bstep (se 2 (by rfl) ⟨2497290, by rfl⟩ : syracuseStep 6659441 = 4994581) B4994581
theorem B4439627 : Blo 1971435 4439627 := bstep (se 1 (by rfl) ⟨3329720, by rfl⟩ : syracuseStep 4439627 = 6659441) B6659441
theorem B2959751 : Blo 1971435 2959751 := bstep (se 1 (by rfl) ⟨2219813, by rfl⟩ : syracuseStep 2959751 = 4439627) B4439627
theorem B1973167 : Blo 1971435 1973167 := bstep (se 1 (by rfl) ⟨1479875, by rfl⟩ : syracuseStep 1973167 = 2959751) B2959751
theorem B2959757 : Blo 1971435 2959757 := bbase (se 3 (by rfl) ⟨554954, by rfl⟩ : syracuseStep 2959757 = 1109909) (by norm_num)
theorem B1973171 : Blo 1971435 1973171 := bstep (se 1 (by rfl) ⟨1479878, by rfl⟩ : syracuseStep 1973171 = 2959757) B2959757
theorem B4439645 : Blo 1971435 4439645 := bbase (se 3 (by rfl) ⟨832433, by rfl⟩ : syracuseStep 4439645 = 1664867) (by norm_num)
theorem B2959763 : Blo 1971435 2959763 := bstep (se 1 (by rfl) ⟨2219822, by rfl⟩ : syracuseStep 2959763 = 4439645) B4439645
theorem B1973175 : Blo 1971435 1973175 := bstep (se 1 (by rfl) ⟨1479881, by rfl⟩ : syracuseStep 1973175 = 2959763) B2959763
theorem B3329741 : Blo 1971435 3329741 := bbase (se 3 (by rfl) ⟨624326, by rfl⟩ : syracuseStep 3329741 = 1248653) (by norm_num)
theorem B2219827 : Blo 1971435 2219827 := bstep (se 1 (by rfl) ⟨1664870, by rfl⟩ : syracuseStep 2219827 = 3329741) B3329741
theorem B2959769 : Blo 1971435 2959769 := bstep (se 2 (by rfl) ⟨1109913, by rfl⟩ : syracuseStep 2959769 = 2219827) B2219827
theorem B1973179 : Blo 1971435 1973179 := bstep (se 1 (by rfl) ⟨1479884, by rfl⟩ : syracuseStep 1973179 = 2959769) B2959769
theorem B4740989 : Blo 1971435 4740989 := bbase (se 3 (by rfl) ⟨888935, by rfl⟩ : syracuseStep 4740989 = 1777871) (by norm_num)
theorem B12642637 : Blo 1971435 12642637 := bstep (se 3 (by rfl) ⟨2370494, by rfl⟩ : syracuseStep 12642637 = 4740989) B4740989
theorem B16856849 : Blo 1971435 16856849 := bstep (se 2 (by rfl) ⟨6321318, by rfl⟩ : syracuseStep 16856849 = 12642637) B12642637
theorem B11237899 : Blo 1971435 11237899 := bstep (se 1 (by rfl) ⟨8428424, by rfl⟩ : syracuseStep 11237899 = 16856849) B16856849
theorem B14983865 : Blo 1971435 14983865 := bstep (se 2 (by rfl) ⟨5618949, by rfl⟩ : syracuseStep 14983865 = 11237899) B11237899
theorem B9989243 : Blo 1971435 9989243 := bstep (se 1 (by rfl) ⟨7491932, by rfl⟩ : syracuseStep 9989243 = 14983865) B14983865
theorem B6659495 : Blo 1971435 6659495 := bstep (se 1 (by rfl) ⟨4994621, by rfl⟩ : syracuseStep 6659495 = 9989243) B9989243
theorem B4439663 : Blo 1971435 4439663 := bstep (se 1 (by rfl) ⟨3329747, by rfl⟩ : syracuseStep 4439663 = 6659495) B6659495
theorem B2959775 : Blo 1971435 2959775 := bstep (se 1 (by rfl) ⟨2219831, by rfl⟩ : syracuseStep 2959775 = 4439663) B4439663
theorem B1973183 : Blo 1971435 1973183 := bstep (se 1 (by rfl) ⟨1479887, by rfl⟩ : syracuseStep 1973183 = 2959775) B2959775
theorem B2959781 : Blo 1971435 2959781 := bbase (se 4 (by rfl) ⟨277479, by rfl⟩ : syracuseStep 2959781 = 554959) (by norm_num)
theorem B1973187 : Blo 1971435 1973187 := bstep (se 1 (by rfl) ⟨1479890, by rfl⟩ : syracuseStep 1973187 = 2959781) B2959781
theorem B2497321 : Blo 1971435 2497321 := bbase (se 2 (by rfl) ⟨936495, by rfl⟩ : syracuseStep 2497321 = 1872991) (by norm_num)
theorem B3329761 : Blo 1971435 3329761 := bstep (se 2 (by rfl) ⟨1248660, by rfl⟩ : syracuseStep 3329761 = 2497321) B2497321
theorem B4439681 : Blo 1971435 4439681 := bstep (se 2 (by rfl) ⟨1664880, by rfl⟩ : syracuseStep 4439681 = 3329761) B3329761
theorem B2959787 : Blo 1971435 2959787 := bstep (se 1 (by rfl) ⟨2219840, by rfl⟩ : syracuseStep 2959787 = 4439681) B4439681
theorem B1973191 : Blo 1971435 1973191 := bstep (se 1 (by rfl) ⟨1479893, by rfl⟩ : syracuseStep 1973191 = 2959787) B2959787
theorem B2219845 : Blo 1971435 2219845 := bbase (se 4 (by rfl) ⟨208110, by rfl⟩ : syracuseStep 2219845 = 416221) (by norm_num)
theorem B2959793 : Blo 1971435 2959793 := bstep (se 2 (by rfl) ⟨1109922, by rfl⟩ : syracuseStep 2959793 = 2219845) B2219845
theorem B1973195 : Blo 1971435 1973195 := bstep (se 1 (by rfl) ⟨1479896, by rfl⟩ : syracuseStep 1973195 = 2959793) B2959793
theorem B3745997 : Blo 1971435 3745997 := bbase (se 3 (by rfl) ⟨702374, by rfl⟩ : syracuseStep 3745997 = 1404749) (by norm_num)
theorem B2497331 : Blo 1971435 2497331 := bstep (se 1 (by rfl) ⟨1872998, by rfl⟩ : syracuseStep 2497331 = 3745997) B3745997
theorem B6659549 : Blo 1971435 6659549 := bstep (se 3 (by rfl) ⟨1248665, by rfl⟩ : syracuseStep 6659549 = 2497331) B2497331
theorem B4439699 : Blo 1971435 4439699 := bstep (se 1 (by rfl) ⟨3329774, by rfl⟩ : syracuseStep 4439699 = 6659549) B6659549
theorem B2959799 : Blo 1971435 2959799 := bstep (se 1 (by rfl) ⟨2219849, by rfl⟩ : syracuseStep 2959799 = 4439699) B4439699
theorem B1973199 : Blo 1971435 1973199 := bstep (se 1 (by rfl) ⟨1479899, by rfl⟩ : syracuseStep 1973199 = 2959799) B2959799
theorem B2959805 : Blo 1971435 2959805 := bbase (se 3 (by rfl) ⟨554963, by rfl⟩ : syracuseStep 2959805 = 1109927) (by norm_num)
theorem B1973203 : Blo 1971435 1973203 := bstep (se 1 (by rfl) ⟨1479902, by rfl⟩ : syracuseStep 1973203 = 2959805) B2959805
theorem B4439717 : Blo 1971435 4439717 := bbase (se 4 (by rfl) ⟨416223, by rfl⟩ : syracuseStep 4439717 = 832447) (by norm_num)
theorem B2959811 : Blo 1971435 2959811 := bstep (se 1 (by rfl) ⟨2219858, by rfl⟩ : syracuseStep 2959811 = 4439717) B4439717
theorem B1973207 : Blo 1971435 1973207 := bstep (se 1 (by rfl) ⟨1479905, by rfl⟩ : syracuseStep 1973207 = 2959811) B2959811
theorem B4994693 : Blo 1971435 4994693 := bbase (se 4 (by rfl) ⟨468252, by rfl⟩ : syracuseStep 4994693 = 936505) (by norm_num)
theorem B3329795 : Blo 1971435 3329795 := bstep (se 1 (by rfl) ⟨2497346, by rfl⟩ : syracuseStep 3329795 = 4994693) B4994693
theorem B2219863 : Blo 1971435 2219863 := bstep (se 1 (by rfl) ⟨1664897, by rfl⟩ : syracuseStep 2219863 = 3329795) B3329795
theorem B2959817 : Blo 1971435 2959817 := bstep (se 2 (by rfl) ⟨1109931, by rfl⟩ : syracuseStep 2959817 = 2219863) B2219863
theorem B1973211 : Blo 1971435 1973211 := bstep (se 1 (by rfl) ⟨1479908, by rfl⟩ : syracuseStep 1973211 = 2959817) B2959817
theorem B5333701 : Blo 1971435 5333701 := bbase (se 4 (by rfl) ⟨500034, by rfl⟩ : syracuseStep 5333701 = 1000069) (by norm_num)
theorem B7111601 : Blo 1971435 7111601 := bstep (se 2 (by rfl) ⟨2666850, by rfl⟩ : syracuseStep 7111601 = 5333701) B5333701
theorem B4741067 : Blo 1971435 4741067 := bstep (se 1 (by rfl) ⟨3555800, by rfl⟩ : syracuseStep 4741067 = 7111601) B7111601
theorem B3160711 : Blo 1971435 3160711 := bstep (se 1 (by rfl) ⟨2370533, by rfl⟩ : syracuseStep 3160711 = 4741067) B4741067
theorem B4214281 : Blo 1971435 4214281 := bstep (se 2 (by rfl) ⟨1580355, by rfl⟩ : syracuseStep 4214281 = 3160711) B3160711
theorem B5619041 : Blo 1971435 5619041 := bstep (se 2 (by rfl) ⟨2107140, by rfl⟩ : syracuseStep 5619041 = 4214281) B4214281
theorem B3746027 : Blo 1971435 3746027 := bstep (se 1 (by rfl) ⟨2809520, by rfl⟩ : syracuseStep 3746027 = 5619041) B5619041
theorem B9989405 : Blo 1971435 9989405 := bstep (se 3 (by rfl) ⟨1873013, by rfl⟩ : syracuseStep 9989405 = 3746027) B3746027
theorem B6659603 : Blo 1971435 6659603 := bstep (se 1 (by rfl) ⟨4994702, by rfl⟩ : syracuseStep 6659603 = 9989405) B9989405
theorem B4439735 : Blo 1971435 4439735 := bstep (se 1 (by rfl) ⟨3329801, by rfl⟩ : syracuseStep 4439735 = 6659603) B6659603
theorem B2959823 : Blo 1971435 2959823 := bstep (se 1 (by rfl) ⟨2219867, by rfl⟩ : syracuseStep 2959823 = 4439735) B4439735
theorem B1973215 : Blo 1971435 1973215 := bstep (se 1 (by rfl) ⟨1479911, by rfl⟩ : syracuseStep 1973215 = 2959823) B2959823
theorem B2959829 : Blo 1971435 2959829 := bbase (se 7 (by rfl) ⟨34685, by rfl⟩ : syracuseStep 2959829 = 69371) (by norm_num)
theorem B1973219 : Blo 1971435 1973219 := bstep (se 1 (by rfl) ⟨1479914, by rfl⟩ : syracuseStep 1973219 = 2959829) B2959829
theorem B7492085 : Blo 1971435 7492085 := bbase (se 5 (by rfl) ⟨351191, by rfl⟩ : syracuseStep 7492085 = 702383) (by norm_num)
theorem B4994723 : Blo 1971435 4994723 := bstep (se 1 (by rfl) ⟨3746042, by rfl⟩ : syracuseStep 4994723 = 7492085) B7492085
theorem B3329815 : Blo 1971435 3329815 := bstep (se 1 (by rfl) ⟨2497361, by rfl⟩ : syracuseStep 3329815 = 4994723) B4994723
theorem B4439753 : Blo 1971435 4439753 := bstep (se 2 (by rfl) ⟨1664907, by rfl⟩ : syracuseStep 4439753 = 3329815) B3329815
theorem B2959835 : Blo 1971435 2959835 := bstep (se 1 (by rfl) ⟨2219876, by rfl⟩ : syracuseStep 2959835 = 4439753) B4439753
theorem B1973223 : Blo 1971435 1973223 := bstep (se 1 (by rfl) ⟨1479917, by rfl⟩ : syracuseStep 1973223 = 2959835) B2959835
theorem B2219881 : Blo 1971435 2219881 := bbase (se 2 (by rfl) ⟨832455, by rfl⟩ : syracuseStep 2219881 = 1664911) (by norm_num)
theorem B2959841 : Blo 1971435 2959841 := bstep (se 2 (by rfl) ⟨1109940, by rfl⟩ : syracuseStep 2959841 = 2219881) B2219881
theorem B1973227 : Blo 1971435 1973227 := bstep (se 1 (by rfl) ⟨1479920, by rfl⟩ : syracuseStep 1973227 = 2959841) B2959841
theorem B3555829 : Blo 1971435 3555829 := bbase (se 5 (by rfl) ⟨166679, by rfl⟩ : syracuseStep 3555829 = 333359) (by norm_num)
theorem B4741105 : Blo 1971435 4741105 := bstep (se 2 (by rfl) ⟨1777914, by rfl⟩ : syracuseStep 4741105 = 3555829) B3555829
theorem B6321473 : Blo 1971435 6321473 := bstep (se 2 (by rfl) ⟨2370552, by rfl⟩ : syracuseStep 6321473 = 4741105) B4741105
theorem B4214315 : Blo 1971435 4214315 := bstep (se 1 (by rfl) ⟨3160736, by rfl⟩ : syracuseStep 4214315 = 6321473) B6321473
theorem B11238173 : Blo 1971435 11238173 := bstep (se 3 (by rfl) ⟨2107157, by rfl⟩ : syracuseStep 11238173 = 4214315) B4214315
theorem B7492115 : Blo 1971435 7492115 := bstep (se 1 (by rfl) ⟨5619086, by rfl⟩ : syracuseStep 7492115 = 11238173) B11238173
theorem B4994743 : Blo 1971435 4994743 := bstep (se 1 (by rfl) ⟨3746057, by rfl⟩ : syracuseStep 4994743 = 7492115) B7492115
theorem B6659657 : Blo 1971435 6659657 := bstep (se 2 (by rfl) ⟨2497371, by rfl⟩ : syracuseStep 6659657 = 4994743) B4994743
theorem B4439771 : Blo 1971435 4439771 := bstep (se 1 (by rfl) ⟨3329828, by rfl⟩ : syracuseStep 4439771 = 6659657) B6659657
theorem B2959847 : Blo 1971435 2959847 := bstep (se 1 (by rfl) ⟨2219885, by rfl⟩ : syracuseStep 2959847 = 4439771) B4439771
theorem B1973231 : Blo 1971435 1973231 := bstep (se 1 (by rfl) ⟨1479923, by rfl⟩ : syracuseStep 1973231 = 2959847) B2959847
theorem B2959853 : Blo 1971435 2959853 := bbase (se 3 (by rfl) ⟨554972, by rfl⟩ : syracuseStep 2959853 = 1109945) (by norm_num)
theorem B1973235 : Blo 1971435 1973235 := bstep (se 1 (by rfl) ⟨1479926, by rfl⟩ : syracuseStep 1973235 = 2959853) B2959853
theorem B4439789 : Blo 1971435 4439789 := bbase (se 3 (by rfl) ⟨832460, by rfl⟩ : syracuseStep 4439789 = 1664921) (by norm_num)
theorem B2959859 : Blo 1971435 2959859 := bstep (se 1 (by rfl) ⟨2219894, by rfl⟩ : syracuseStep 2959859 = 4439789) B4439789
theorem B1973239 : Blo 1971435 1973239 := bstep (se 1 (by rfl) ⟨1479929, by rfl⟩ : syracuseStep 1973239 = 2959859) B2959859
theorem B3160757 : Blo 1971435 3160757 := bbase (se 5 (by rfl) ⟨148160, by rfl⟩ : syracuseStep 3160757 = 296321) (by norm_num)
theorem B2107171 : Blo 1971435 2107171 := bstep (se 1 (by rfl) ⟨1580378, by rfl⟩ : syracuseStep 2107171 = 3160757) B3160757
theorem B2809561 : Blo 1971435 2809561 := bstep (se 2 (by rfl) ⟨1053585, by rfl⟩ : syracuseStep 2809561 = 2107171) B2107171
theorem B3746081 : Blo 1971435 3746081 := bstep (se 2 (by rfl) ⟨1404780, by rfl⟩ : syracuseStep 3746081 = 2809561) B2809561
theorem B2497387 : Blo 1971435 2497387 := bstep (se 1 (by rfl) ⟨1873040, by rfl⟩ : syracuseStep 2497387 = 3746081) B3746081
theorem B3329849 : Blo 1971435 3329849 := bstep (se 2 (by rfl) ⟨1248693, by rfl⟩ : syracuseStep 3329849 = 2497387) B2497387
theorem B2219899 : Blo 1971435 2219899 := bstep (se 1 (by rfl) ⟨1664924, by rfl⟩ : syracuseStep 2219899 = 3329849) B3329849
theorem B2959865 : Blo 1971435 2959865 := bstep (se 2 (by rfl) ⟨1109949, by rfl⟩ : syracuseStep 2959865 = 2219899) B2219899
theorem B1973243 : Blo 1971435 1973243 := bstep (se 1 (by rfl) ⟨1479932, by rfl⟩ : syracuseStep 1973243 = 2959865) B2959865
theorem B15188789 : Blo 1971435 15188789 := bbase (se 5 (by rfl) ⟨711974, by rfl⟩ : syracuseStep 15188789 = 1423949) (by norm_num)
theorem B10125859 : Blo 1971435 10125859 := bstep (se 1 (by rfl) ⟨7594394, by rfl⟩ : syracuseStep 10125859 = 15188789) B15188789
theorem B13501145 : Blo 1971435 13501145 := bstep (se 2 (by rfl) ⟨5062929, by rfl⟩ : syracuseStep 13501145 = 10125859) B10125859
theorem B9000763 : Blo 1971435 9000763 := bstep (se 1 (by rfl) ⟨6750572, by rfl⟩ : syracuseStep 9000763 = 13501145) B13501145
theorem B192016277 : Blo 1971435 192016277 := bstep (se 6 (by rfl) ⟨4500381, by rfl⟩ : syracuseStep 192016277 = 9000763) B9000763
theorem B128010851 : Blo 1971435 128010851 := bstep (se 1 (by rfl) ⟨96008138, by rfl⟩ : syracuseStep 128010851 = 192016277) B192016277
theorem B85340567 : Blo 1971435 85340567 := bstep (se 1 (by rfl) ⟨64005425, by rfl⟩ : syracuseStep 85340567 = 128010851) B128010851
theorem B56893711 : Blo 1971435 56893711 := bstep (se 1 (by rfl) ⟨42670283, by rfl⟩ : syracuseStep 56893711 = 85340567) B85340567
theorem B75858281 : Blo 1971435 75858281 := bstep (se 2 (by rfl) ⟨28446855, by rfl⟩ : syracuseStep 75858281 = 56893711) B56893711
theorem B50572187 : Blo 1971435 50572187 := bstep (se 1 (by rfl) ⟨37929140, by rfl⟩ : syracuseStep 50572187 = 75858281) B75858281
theorem B33714791 : Blo 1971435 33714791 := bstep (se 1 (by rfl) ⟨25286093, by rfl⟩ : syracuseStep 33714791 = 50572187) B50572187
theorem B22476527 : Blo 1971435 22476527 := bstep (se 1 (by rfl) ⟨16857395, by rfl⟩ : syracuseStep 22476527 = 33714791) B33714791
theorem B14984351 : Blo 1971435 14984351 := bstep (se 1 (by rfl) ⟨11238263, by rfl⟩ : syracuseStep 14984351 = 22476527) B22476527
theorem B9989567 : Blo 1971435 9989567 := bstep (se 1 (by rfl) ⟨7492175, by rfl⟩ : syracuseStep 9989567 = 14984351) B14984351
theorem B6659711 : Blo 1971435 6659711 := bstep (se 1 (by rfl) ⟨4994783, by rfl⟩ : syracuseStep 6659711 = 9989567) B9989567
theorem B4439807 : Blo 1971435 4439807 := bstep (se 1 (by rfl) ⟨3329855, by rfl⟩ : syracuseStep 4439807 = 6659711) B6659711
theorem B2959871 : Blo 1971435 2959871 := bstep (se 1 (by rfl) ⟨2219903, by rfl⟩ : syracuseStep 2959871 = 4439807) B4439807
theorem B1973247 : Blo 1971435 1973247 := bstep (se 1 (by rfl) ⟨1479935, by rfl⟩ : syracuseStep 1973247 = 2959871) B2959871
theorem B2959877 : Blo 1971435 2959877 := bbase (se 4 (by rfl) ⟨277488, by rfl⟩ : syracuseStep 2959877 = 554977) (by norm_num)
theorem B1973251 : Blo 1971435 1973251 := bstep (se 1 (by rfl) ⟨1479938, by rfl⟩ : syracuseStep 1973251 = 2959877) B2959877
theorem B3329869 : Blo 1971435 3329869 := bbase (se 3 (by rfl) ⟨624350, by rfl⟩ : syracuseStep 3329869 = 1248701) (by norm_num)
theorem B4439825 : Blo 1971435 4439825 := bstep (se 2 (by rfl) ⟨1664934, by rfl⟩ : syracuseStep 4439825 = 3329869) B3329869
theorem B2959883 : Blo 1971435 2959883 := bstep (se 1 (by rfl) ⟨2219912, by rfl⟩ : syracuseStep 2959883 = 4439825) B4439825
theorem B1973255 : Blo 1971435 1973255 := bstep (se 1 (by rfl) ⟨1479941, by rfl⟩ : syracuseStep 1973255 = 2959883) B2959883
theorem B2219917 : Blo 1971435 2219917 := bbase (se 3 (by rfl) ⟨416234, by rfl⟩ : syracuseStep 2219917 = 832469) (by norm_num)
theorem B2959889 : Blo 1971435 2959889 := bstep (se 2 (by rfl) ⟨1109958, by rfl⟩ : syracuseStep 2959889 = 2219917) B2219917
theorem B1973259 : Blo 1971435 1973259 := bstep (se 1 (by rfl) ⟨1479944, by rfl⟩ : syracuseStep 1973259 = 2959889) B2959889
theorem B6659765 : Blo 1971435 6659765 := bbase (se 5 (by rfl) ⟨312176, by rfl⟩ : syracuseStep 6659765 = 624353) (by norm_num)
theorem B4439843 : Blo 1971435 4439843 := bstep (se 1 (by rfl) ⟨3329882, by rfl⟩ : syracuseStep 4439843 = 6659765) B6659765
theorem B2959895 : Blo 1971435 2959895 := bstep (se 1 (by rfl) ⟨2219921, by rfl⟩ : syracuseStep 2959895 = 4439843) B4439843
theorem B1973263 : Blo 1971435 1973263 := bstep (se 1 (by rfl) ⟨1479947, by rfl⟩ : syracuseStep 1973263 = 2959895) B2959895
theorem B2959901 : Blo 1971435 2959901 := bbase (se 3 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 2959901 = 1109963) (by norm_num)
theorem B1973267 : Blo 1971435 1973267 := bstep (se 1 (by rfl) ⟨1479950, by rfl⟩ : syracuseStep 1973267 = 2959901) B2959901
theorem B4439861 : Blo 1971435 4439861 := bbase (se 5 (by rfl) ⟨208118, by rfl⟩ : syracuseStep 4439861 = 416237) (by norm_num)
theorem B2959907 : Blo 1971435 2959907 := bstep (se 1 (by rfl) ⟨2219930, by rfl⟩ : syracuseStep 2959907 = 4439861) B4439861
theorem B1973271 : Blo 1971435 1973271 := bstep (se 1 (by rfl) ⟨1479953, by rfl⟩ : syracuseStep 1973271 = 2959907) B2959907
theorem B3247645 : Blo 1971435 3247645 := bbase (se 3 (by rfl) ⟨608933, by rfl⟩ : syracuseStep 3247645 = 1217867) (by norm_num)
theorem B4330193 : Blo 1971435 4330193 := bstep (se 2 (by rfl) ⟨1623822, by rfl⟩ : syracuseStep 4330193 = 3247645) B3247645
theorem B11547181 : Blo 1971435 11547181 := bstep (se 3 (by rfl) ⟨2165096, by rfl⟩ : syracuseStep 11547181 = 4330193) B4330193
theorem B15396241 : Blo 1971435 15396241 := bstep (se 2 (by rfl) ⟨5773590, by rfl⟩ : syracuseStep 15396241 = 11547181) B11547181
theorem B20528321 : Blo 1971435 20528321 := bstep (se 2 (by rfl) ⟨7698120, by rfl⟩ : syracuseStep 20528321 = 15396241) B15396241
theorem B54742189 : Blo 1971435 54742189 := bstep (se 3 (by rfl) ⟨10264160, by rfl⟩ : syracuseStep 54742189 = 20528321) B20528321
theorem B72989585 : Blo 1971435 72989585 := bstep (se 2 (by rfl) ⟨27371094, by rfl⟩ : syracuseStep 72989585 = 54742189) B54742189
theorem B48659723 : Blo 1971435 48659723 := bstep (se 1 (by rfl) ⟨36494792, by rfl⟩ : syracuseStep 48659723 = 72989585) B72989585
theorem B32439815 : Blo 1971435 32439815 := bstep (se 1 (by rfl) ⟨24329861, by rfl⟩ : syracuseStep 32439815 = 48659723) B48659723
theorem B21626543 : Blo 1971435 21626543 := bstep (se 1 (by rfl) ⟨16219907, by rfl⟩ : syracuseStep 21626543 = 32439815) B32439815
theorem B14417695 : Blo 1971435 14417695 := bstep (se 1 (by rfl) ⟨10813271, by rfl⟩ : syracuseStep 14417695 = 21626543) B21626543
theorem B76894373 : Blo 1971435 76894373 := bstep (se 4 (by rfl) ⟨7208847, by rfl⟩ : syracuseStep 76894373 = 14417695) B14417695
theorem B51262915 : Blo 1971435 51262915 := bstep (se 1 (by rfl) ⟨38447186, by rfl⟩ : syracuseStep 51262915 = 76894373) B76894373
theorem B68350553 : Blo 1971435 68350553 := bstep (se 2 (by rfl) ⟨25631457, by rfl⟩ : syracuseStep 68350553 = 51262915) B51262915
theorem B45567035 : Blo 1971435 45567035 := bstep (se 1 (by rfl) ⟨34175276, by rfl⟩ : syracuseStep 45567035 = 68350553) B68350553
theorem B30378023 : Blo 1971435 30378023 := bstep (se 1 (by rfl) ⟨22783517, by rfl⟩ : syracuseStep 30378023 = 45567035) B45567035
theorem B20252015 : Blo 1971435 20252015 := bstep (se 1 (by rfl) ⟨15189011, by rfl⟩ : syracuseStep 20252015 = 30378023) B30378023
theorem B13501343 : Blo 1971435 13501343 := bstep (se 1 (by rfl) ⟨10126007, by rfl⟩ : syracuseStep 13501343 = 20252015) B20252015
theorem B9000895 : Blo 1971435 9000895 := bstep (se 1 (by rfl) ⟨6750671, by rfl⟩ : syracuseStep 9000895 = 13501343) B13501343
theorem B12001193 : Blo 1971435 12001193 := bstep (se 2 (by rfl) ⟨4500447, by rfl⟩ : syracuseStep 12001193 = 9000895) B9000895
theorem B8000795 : Blo 1971435 8000795 := bstep (se 1 (by rfl) ⟨6000596, by rfl⟩ : syracuseStep 8000795 = 12001193) B12001193
theorem B5333863 : Blo 1971435 5333863 := bstep (se 1 (by rfl) ⟨4000397, by rfl⟩ : syracuseStep 5333863 = 8000795) B8000795
theorem B7111817 : Blo 1971435 7111817 := bstep (se 2 (by rfl) ⟨2666931, by rfl⟩ : syracuseStep 7111817 = 5333863) B5333863
theorem B4741211 : Blo 1971435 4741211 := bstep (se 1 (by rfl) ⟨3555908, by rfl⟩ : syracuseStep 4741211 = 7111817) B7111817
theorem B12643229 : Blo 1971435 12643229 := bstep (se 3 (by rfl) ⟨2370605, by rfl⟩ : syracuseStep 12643229 = 4741211) B4741211
theorem B8428819 : Blo 1971435 8428819 := bstep (se 1 (by rfl) ⟨6321614, by rfl⟩ : syracuseStep 8428819 = 12643229) B12643229
theorem B11238425 : Blo 1971435 11238425 := bstep (se 2 (by rfl) ⟨4214409, by rfl⟩ : syracuseStep 11238425 = 8428819) B8428819
theorem B7492283 : Blo 1971435 7492283 := bstep (se 1 (by rfl) ⟨5619212, by rfl⟩ : syracuseStep 7492283 = 11238425) B11238425
theorem B4994855 : Blo 1971435 4994855 := bstep (se 1 (by rfl) ⟨3746141, by rfl⟩ : syracuseStep 4994855 = 7492283) B7492283
theorem B3329903 : Blo 1971435 3329903 := bstep (se 1 (by rfl) ⟨2497427, by rfl⟩ : syracuseStep 3329903 = 4994855) B4994855
theorem B2219935 : Blo 1971435 2219935 := bstep (se 1 (by rfl) ⟨1664951, by rfl⟩ : syracuseStep 2219935 = 3329903) B3329903
theorem B2959913 : Blo 1971435 2959913 := bstep (se 2 (by rfl) ⟨1109967, by rfl⟩ : syracuseStep 2959913 = 2219935) B2219935
theorem B1973275 : Blo 1971435 1973275 := bstep (se 1 (by rfl) ⟨1479956, by rfl⟩ : syracuseStep 1973275 = 2959913) B2959913
theorem B12643253 : Blo 1971435 12643253 := bbase (se 5 (by rfl) ⟨592652, by rfl⟩ : syracuseStep 12643253 = 1185305) (by norm_num)
theorem B8428835 : Blo 1971435 8428835 := bstep (se 1 (by rfl) ⟨6321626, by rfl⟩ : syracuseStep 8428835 = 12643253) B12643253
theorem B5619223 : Blo 1971435 5619223 := bstep (se 1 (by rfl) ⟨4214417, by rfl⟩ : syracuseStep 5619223 = 8428835) B8428835
theorem B7492297 : Blo 1971435 7492297 := bstep (se 2 (by rfl) ⟨2809611, by rfl⟩ : syracuseStep 7492297 = 5619223) B5619223
theorem B9989729 : Blo 1971435 9989729 := bstep (se 2 (by rfl) ⟨3746148, by rfl⟩ : syracuseStep 9989729 = 7492297) B7492297
theorem B6659819 : Blo 1971435 6659819 := bstep (se 1 (by rfl) ⟨4994864, by rfl⟩ : syracuseStep 6659819 = 9989729) B9989729
theorem B4439879 : Blo 1971435 4439879 := bstep (se 1 (by rfl) ⟨3329909, by rfl⟩ : syracuseStep 4439879 = 6659819) B6659819
theorem B2959919 : Blo 1971435 2959919 := bstep (se 1 (by rfl) ⟨2219939, by rfl⟩ : syracuseStep 2959919 = 4439879) B4439879
theorem B1973279 : Blo 1971435 1973279 := bstep (se 1 (by rfl) ⟨1479959, by rfl⟩ : syracuseStep 1973279 = 2959919) B2959919
theorem B2959925 : Blo 1971435 2959925 := bbase (se 5 (by rfl) ⟨138746, by rfl⟩ : syracuseStep 2959925 = 277493) (by norm_num)
theorem B1973283 : Blo 1971435 1973283 := bstep (se 1 (by rfl) ⟨1479962, by rfl⟩ : syracuseStep 1973283 = 2959925) B2959925
theorem B4994885 : Blo 1971435 4994885 := bbase (se 4 (by rfl) ⟨468270, by rfl⟩ : syracuseStep 4994885 = 936541) (by norm_num)
theorem B3329923 : Blo 1971435 3329923 := bstep (se 1 (by rfl) ⟨2497442, by rfl⟩ : syracuseStep 3329923 = 4994885) B4994885
theorem B4439897 : Blo 1971435 4439897 := bstep (se 2 (by rfl) ⟨1664961, by rfl⟩ : syracuseStep 4439897 = 3329923) B3329923
theorem B2959931 : Blo 1971435 2959931 := bstep (se 1 (by rfl) ⟨2219948, by rfl⟩ : syracuseStep 2959931 = 4439897) B4439897
theorem B1973287 : Blo 1971435 1973287 := bstep (se 1 (by rfl) ⟨1479965, by rfl⟩ : syracuseStep 1973287 = 2959931) B2959931
theorem B2219953 : Blo 1971435 2219953 := bbase (se 2 (by rfl) ⟨832482, by rfl⟩ : syracuseStep 2219953 = 1664965) (by norm_num)
theorem B2959937 : Blo 1971435 2959937 := bstep (se 2 (by rfl) ⟨1109976, by rfl⟩ : syracuseStep 2959937 = 2219953) B2219953
theorem B1973291 : Blo 1971435 1973291 := bstep (se 1 (by rfl) ⟨1479968, by rfl⟩ : syracuseStep 1973291 = 2959937) B2959937
theorem B5619269 : Blo 1971435 5619269 := bbase (se 4 (by rfl) ⟨526806, by rfl⟩ : syracuseStep 5619269 = 1053613) (by norm_num)
theorem B3746179 : Blo 1971435 3746179 := bstep (se 1 (by rfl) ⟨2809634, by rfl⟩ : syracuseStep 3746179 = 5619269) B5619269
theorem B4994905 : Blo 1971435 4994905 := bstep (se 2 (by rfl) ⟨1873089, by rfl⟩ : syracuseStep 4994905 = 3746179) B3746179
theorem B6659873 : Blo 1971435 6659873 := bstep (se 2 (by rfl) ⟨2497452, by rfl⟩ : syracuseStep 6659873 = 4994905) B4994905
theorem B4439915 : Blo 1971435 4439915 := bstep (se 1 (by rfl) ⟨3329936, by rfl⟩ : syracuseStep 4439915 = 6659873) B6659873
theorem B2959943 : Blo 1971435 2959943 := bstep (se 1 (by rfl) ⟨2219957, by rfl⟩ : syracuseStep 2959943 = 4439915) B4439915
theorem B1973295 : Blo 1971435 1973295 := bstep (se 1 (by rfl) ⟨1479971, by rfl⟩ : syracuseStep 1973295 = 2959943) B2959943
theorem B2959949 : Blo 1971435 2959949 := bbase (se 3 (by rfl) ⟨554990, by rfl⟩ : syracuseStep 2959949 = 1109981) (by norm_num)
theorem B1973299 : Blo 1971435 1973299 := bstep (se 1 (by rfl) ⟨1479974, by rfl⟩ : syracuseStep 1973299 = 2959949) B2959949
theorem B4439933 : Blo 1971435 4439933 := bbase (se 3 (by rfl) ⟨832487, by rfl⟩ : syracuseStep 4439933 = 1664975) (by norm_num)
theorem B2959955 : Blo 1971435 2959955 := bstep (se 1 (by rfl) ⟨2219966, by rfl⟩ : syracuseStep 2959955 = 4439933) B4439933
theorem B1973303 : Blo 1971435 1973303 := bstep (se 1 (by rfl) ⟨1479977, by rfl⟩ : syracuseStep 1973303 = 2959955) B2959955
theorem B3329957 : Blo 1971435 3329957 := bbase (se 4 (by rfl) ⟨312183, by rfl⟩ : syracuseStep 3329957 = 624367) (by norm_num)
theorem B2219971 : Blo 1971435 2219971 := bstep (se 1 (by rfl) ⟨1664978, by rfl⟩ : syracuseStep 2219971 = 3329957) B3329957
theorem B2959961 : Blo 1971435 2959961 := bstep (se 2 (by rfl) ⟨1109985, by rfl⟩ : syracuseStep 2959961 = 2219971) B2219971
theorem B1973307 : Blo 1971435 1973307 := bstep (se 1 (by rfl) ⟨1479980, by rfl⟩ : syracuseStep 1973307 = 2959961) B2959961
theorem B2370649 : Blo 1971435 2370649 := bbase (se 2 (by rfl) ⟨888993, by rfl⟩ : syracuseStep 2370649 = 1777987) (by norm_num)
theorem B3160865 : Blo 1971435 3160865 := bstep (se 2 (by rfl) ⟨1185324, by rfl⟩ : syracuseStep 3160865 = 2370649) B2370649
theorem B2107243 : Blo 1971435 2107243 := bstep (se 1 (by rfl) ⟨1580432, by rfl⟩ : syracuseStep 2107243 = 3160865) B3160865
theorem B2809657 : Blo 1971435 2809657 := bstep (se 2 (by rfl) ⟨1053621, by rfl⟩ : syracuseStep 2809657 = 2107243) B2107243
theorem B14984837 : Blo 1971435 14984837 := bstep (se 4 (by rfl) ⟨1404828, by rfl⟩ : syracuseStep 14984837 = 2809657) B2809657
theorem B9989891 : Blo 1971435 9989891 := bstep (se 1 (by rfl) ⟨7492418, by rfl⟩ : syracuseStep 9989891 = 14984837) B14984837
theorem B6659927 : Blo 1971435 6659927 := bstep (se 1 (by rfl) ⟨4994945, by rfl⟩ : syracuseStep 6659927 = 9989891) B9989891
theorem B4439951 : Blo 1971435 4439951 := bstep (se 1 (by rfl) ⟨3329963, by rfl⟩ : syracuseStep 4439951 = 6659927) B6659927
theorem B2959967 : Blo 1971435 2959967 := bstep (se 1 (by rfl) ⟨2219975, by rfl⟩ : syracuseStep 2959967 = 4439951) B4439951
theorem B1973311 : Blo 1971435 1973311 := bstep (se 1 (by rfl) ⟨1479983, by rfl⟩ : syracuseStep 1973311 = 2959967) B2959967
theorem B2959973 : Blo 1971435 2959973 := bbase (se 4 (by rfl) ⟨277497, by rfl⟩ : syracuseStep 2959973 = 554995) (by norm_num)
theorem B1973315 : Blo 1971435 1973315 := bstep (se 1 (by rfl) ⟨1479986, by rfl⟩ : syracuseStep 1973315 = 2959973) B2959973
theorem B2809669 : Blo 1971435 2809669 := bbase (se 4 (by rfl) ⟨263406, by rfl⟩ : syracuseStep 2809669 = 526813) (by norm_num)
theorem B3746225 : Blo 1971435 3746225 := bstep (se 2 (by rfl) ⟨1404834, by rfl⟩ : syracuseStep 3746225 = 2809669) B2809669
theorem B2497483 : Blo 1971435 2497483 := bstep (se 1 (by rfl) ⟨1873112, by rfl⟩ : syracuseStep 2497483 = 3746225) B3746225
theorem B3329977 : Blo 1971435 3329977 := bstep (se 2 (by rfl) ⟨1248741, by rfl⟩ : syracuseStep 3329977 = 2497483) B2497483
theorem B4439969 : Blo 1971435 4439969 := bstep (se 2 (by rfl) ⟨1664988, by rfl⟩ : syracuseStep 4439969 = 3329977) B3329977
theorem B2959979 : Blo 1971435 2959979 := bstep (se 1 (by rfl) ⟨2219984, by rfl⟩ : syracuseStep 2959979 = 4439969) B4439969
theorem B1973319 : Blo 1971435 1973319 := bstep (se 1 (by rfl) ⟨1479989, by rfl⟩ : syracuseStep 1973319 = 2959979) B2959979
theorem B2219989 : Blo 1971435 2219989 := bbase (se 7 (by rfl) ⟨26015, by rfl⟩ : syracuseStep 2219989 = 52031) (by norm_num)
theorem B2959985 : Blo 1971435 2959985 := bstep (se 2 (by rfl) ⟨1109994, by rfl⟩ : syracuseStep 2959985 = 2219989) B2219989
theorem B1973323 : Blo 1971435 1973323 := bstep (se 1 (by rfl) ⟨1479992, by rfl⟩ : syracuseStep 1973323 = 2959985) B2959985
theorem B2497493 : Blo 1971435 2497493 := bbase (se 7 (by rfl) ⟨29267, by rfl⟩ : syracuseStep 2497493 = 58535) (by norm_num)
theorem B6659981 : Blo 1971435 6659981 := bstep (se 3 (by rfl) ⟨1248746, by rfl⟩ : syracuseStep 6659981 = 2497493) B2497493
theorem B4439987 : Blo 1971435 4439987 := bstep (se 1 (by rfl) ⟨3329990, by rfl⟩ : syracuseStep 4439987 = 6659981) B6659981
theorem B2959991 : Blo 1971435 2959991 := bstep (se 1 (by rfl) ⟨2219993, by rfl⟩ : syracuseStep 2959991 = 4439987) B4439987
theorem B1973327 : Blo 1971435 1973327 := bstep (se 1 (by rfl) ⟨1479995, by rfl⟩ : syracuseStep 1973327 = 2959991) B2959991
theorem B2959997 : Blo 1971435 2959997 := bbase (se 3 (by rfl) ⟨554999, by rfl⟩ : syracuseStep 2959997 = 1109999) (by norm_num)
theorem B1973331 : Blo 1971435 1973331 := bstep (se 1 (by rfl) ⟨1479998, by rfl⟩ : syracuseStep 1973331 = 2959997) B2959997
theorem B4440005 : Blo 1971435 4440005 := bbase (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) (by norm_num)
theorem B2960003 : Blo 1971435 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B1973335 : Blo 1971435 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B8429093 : Blo 1971435 8429093 := bbase (se 4 (by rfl) ⟨790227, by rfl⟩ : syracuseStep 8429093 = 1580455) (by norm_num)
theorem B5619395 : Blo 1971435 5619395 := bstep (se 1 (by rfl) ⟨4214546, by rfl⟩ : syracuseStep 5619395 = 8429093) B8429093
theorem B3746263 : Blo 1971435 3746263 := bstep (se 1 (by rfl) ⟨2809697, by rfl⟩ : syracuseStep 3746263 = 5619395) B5619395
theorem B4995017 : Blo 1971435 4995017 := bstep (se 2 (by rfl) ⟨1873131, by rfl⟩ : syracuseStep 4995017 = 3746263) B3746263
theorem B3330011 : Blo 1971435 3330011 := bstep (se 1 (by rfl) ⟨2497508, by rfl⟩ : syracuseStep 3330011 = 4995017) B4995017
theorem B2220007 : Blo 1971435 2220007 := bstep (se 1 (by rfl) ⟨1665005, by rfl⟩ : syracuseStep 2220007 = 3330011) B3330011
theorem B2960009 : Blo 1971435 2960009 := bstep (se 2 (by rfl) ⟨1110003, by rfl⟩ : syracuseStep 2960009 = 2220007) B2220007
theorem B1973339 : Blo 1971435 1973339 := bstep (se 1 (by rfl) ⟨1480004, by rfl⟩ : syracuseStep 1973339 = 2960009) B2960009
theorem B9990053 : Blo 1971435 9990053 := bbase (se 4 (by rfl) ⟨936567, by rfl⟩ : syracuseStep 9990053 = 1873135) (by norm_num)
theorem B6660035 : Blo 1971435 6660035 := bstep (se 1 (by rfl) ⟨4995026, by rfl⟩ : syracuseStep 6660035 = 9990053) B9990053
theorem B4440023 : Blo 1971435 4440023 := bstep (se 1 (by rfl) ⟨3330017, by rfl⟩ : syracuseStep 4440023 = 6660035) B6660035
theorem B2960015 : Blo 1971435 2960015 := bstep (se 1 (by rfl) ⟨2220011, by rfl⟩ : syracuseStep 2960015 = 4440023) B4440023
theorem B1973343 : Blo 1971435 1973343 := bstep (se 1 (by rfl) ⟨1480007, by rfl⟩ : syracuseStep 1973343 = 2960015) B2960015
theorem B2960021 : Blo 1971435 2960021 := bbase (se 6 (by rfl) ⟨69375, by rfl⟩ : syracuseStep 2960021 = 138751) (by norm_num)
theorem B1973347 : Blo 1971435 1973347 := bstep (se 1 (by rfl) ⟨1480010, by rfl⟩ : syracuseStep 1973347 = 2960021) B2960021
theorem B3556045 : Blo 1971435 3556045 := bbase (se 3 (by rfl) ⟨666758, by rfl⟩ : syracuseStep 3556045 = 1333517) (by norm_num)
theorem B18965573 : Blo 1971435 18965573 := bstep (se 4 (by rfl) ⟨1778022, by rfl⟩ : syracuseStep 18965573 = 3556045) B3556045
theorem B12643715 : Blo 1971435 12643715 := bstep (se 1 (by rfl) ⟨9482786, by rfl⟩ : syracuseStep 12643715 = 18965573) B18965573
theorem B8429143 : Blo 1971435 8429143 := bstep (se 1 (by rfl) ⟨6321857, by rfl⟩ : syracuseStep 8429143 = 12643715) B12643715
theorem B11238857 : Blo 1971435 11238857 := bstep (se 2 (by rfl) ⟨4214571, by rfl⟩ : syracuseStep 11238857 = 8429143) B8429143
theorem B7492571 : Blo 1971435 7492571 := bstep (se 1 (by rfl) ⟨5619428, by rfl⟩ : syracuseStep 7492571 = 11238857) B11238857
theorem B4995047 : Blo 1971435 4995047 := bstep (se 1 (by rfl) ⟨3746285, by rfl⟩ : syracuseStep 4995047 = 7492571) B7492571
theorem B3330031 : Blo 1971435 3330031 := bstep (se 1 (by rfl) ⟨2497523, by rfl⟩ : syracuseStep 3330031 = 4995047) B4995047
theorem B4440041 : Blo 1971435 4440041 := bstep (se 2 (by rfl) ⟨1665015, by rfl⟩ : syracuseStep 4440041 = 3330031) B3330031
theorem B2960027 : Blo 1971435 2960027 := bstep (se 1 (by rfl) ⟨2220020, by rfl⟩ : syracuseStep 2960027 = 4440041) B4440041
theorem B1973351 : Blo 1971435 1973351 := bstep (se 1 (by rfl) ⟨1480013, by rfl⟩ : syracuseStep 1973351 = 2960027) B2960027
theorem B2220025 : Blo 1971435 2220025 := bbase (se 2 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 2220025 = 1665019) (by norm_num)
theorem B2960033 : Blo 1971435 2960033 := bstep (se 2 (by rfl) ⟨1110012, by rfl⟩ : syracuseStep 2960033 = 2220025) B2220025
theorem B1973355 : Blo 1971435 1973355 := bstep (se 1 (by rfl) ⟨1480016, by rfl⟩ : syracuseStep 1973355 = 2960033) B2960033
theorem B2848061 : Blo 1971435 2848061 := bbase (se 3 (by rfl) ⟨534011, by rfl⟩ : syracuseStep 2848061 = 1068023) (by norm_num)
theorem B7594829 : Blo 1971435 7594829 := bstep (se 3 (by rfl) ⟨1424030, by rfl⟩ : syracuseStep 7594829 = 2848061) B2848061
theorem B5063219 : Blo 1971435 5063219 := bstep (se 1 (by rfl) ⟨3797414, by rfl⟩ : syracuseStep 5063219 = 7594829) B7594829
theorem B3375479 : Blo 1971435 3375479 := bstep (se 1 (by rfl) ⟨2531609, by rfl⟩ : syracuseStep 3375479 = 5063219) B5063219
theorem B9001277 : Blo 1971435 9001277 := bstep (se 3 (by rfl) ⟨1687739, by rfl⟩ : syracuseStep 9001277 = 3375479) B3375479
theorem B6000851 : Blo 1971435 6000851 := bstep (se 1 (by rfl) ⟨4500638, by rfl⟩ : syracuseStep 6000851 = 9001277) B9001277
theorem B16002269 : Blo 1971435 16002269 := bstep (se 3 (by rfl) ⟨3000425, by rfl⟩ : syracuseStep 16002269 = 6000851) B6000851
theorem B10668179 : Blo 1971435 10668179 := bstep (se 1 (by rfl) ⟨8001134, by rfl⟩ : syracuseStep 10668179 = 16002269) B16002269
theorem B7112119 : Blo 1971435 7112119 := bstep (se 1 (by rfl) ⟨5334089, by rfl⟩ : syracuseStep 7112119 = 10668179) B10668179
theorem B9482825 : Blo 1971435 9482825 := bstep (se 2 (by rfl) ⟨3556059, by rfl⟩ : syracuseStep 9482825 = 7112119) B7112119
theorem B6321883 : Blo 1971435 6321883 := bstep (se 1 (by rfl) ⟨4741412, by rfl⟩ : syracuseStep 6321883 = 9482825) B9482825
theorem B8429177 : Blo 1971435 8429177 := bstep (se 2 (by rfl) ⟨3160941, by rfl⟩ : syracuseStep 8429177 = 6321883) B6321883
theorem B5619451 : Blo 1971435 5619451 := bstep (se 1 (by rfl) ⟨4214588, by rfl⟩ : syracuseStep 5619451 = 8429177) B8429177
theorem B7492601 : Blo 1971435 7492601 := bstep (se 2 (by rfl) ⟨2809725, by rfl⟩ : syracuseStep 7492601 = 5619451) B5619451
theorem B4995067 : Blo 1971435 4995067 := bstep (se 1 (by rfl) ⟨3746300, by rfl⟩ : syracuseStep 4995067 = 7492601) B7492601
theorem B6660089 : Blo 1971435 6660089 := bstep (se 2 (by rfl) ⟨2497533, by rfl⟩ : syracuseStep 6660089 = 4995067) B4995067
theorem B4440059 : Blo 1971435 4440059 := bstep (se 1 (by rfl) ⟨3330044, by rfl⟩ : syracuseStep 4440059 = 6660089) B6660089
theorem B2960039 : Blo 1971435 2960039 := bstep (se 1 (by rfl) ⟨2220029, by rfl⟩ : syracuseStep 2960039 = 4440059) B4440059
theorem B1973359 : Blo 1971435 1973359 := bstep (se 1 (by rfl) ⟨1480019, by rfl⟩ : syracuseStep 1973359 = 2960039) B2960039
theorem B2960045 : Blo 1971435 2960045 := bbase (se 3 (by rfl) ⟨555008, by rfl⟩ : syracuseStep 2960045 = 1110017) (by norm_num)
theorem B1973363 : Blo 1971435 1973363 := bstep (se 1 (by rfl) ⟨1480022, by rfl⟩ : syracuseStep 1973363 = 2960045) B2960045
theorem B4440077 : Blo 1971435 4440077 := bbase (se 3 (by rfl) ⟨832514, by rfl⟩ : syracuseStep 4440077 = 1665029) (by norm_num)
theorem B2960051 : Blo 1971435 2960051 := bstep (se 1 (by rfl) ⟨2220038, by rfl⟩ : syracuseStep 2960051 = 4440077) B4440077
theorem B1973367 : Blo 1971435 1973367 := bstep (se 1 (by rfl) ⟨1480025, by rfl⟩ : syracuseStep 1973367 = 2960051) B2960051
theorem B2497549 : Blo 1971435 2497549 := bbase (se 3 (by rfl) ⟨468290, by rfl⟩ : syracuseStep 2497549 = 936581) (by norm_num)
theorem B3330065 : Blo 1971435 3330065 := bstep (se 2 (by rfl) ⟨1248774, by rfl⟩ : syracuseStep 3330065 = 2497549) B2497549
theorem B2220043 : Blo 1971435 2220043 := bstep (se 1 (by rfl) ⟨1665032, by rfl⟩ : syracuseStep 2220043 = 3330065) B3330065
theorem B2960057 : Blo 1971435 2960057 := bstep (se 2 (by rfl) ⟨1110021, by rfl⟩ : syracuseStep 2960057 = 2220043) B2220043
theorem B1973371 : Blo 1971435 1973371 := bstep (se 1 (by rfl) ⟨1480028, by rfl⟩ : syracuseStep 1973371 = 2960057) B2960057
theorem B12816373 : Blo 1971435 12816373 := bbase (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) (by norm_num)
theorem B17088497 : Blo 1971435 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B11392331 : Blo 1971435 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B30379549 : Blo 1971435 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B40506065 : Blo 1971435 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B27004043 : Blo 1971435 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B72010781 : Blo 1971435 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B48007187 : Blo 1971435 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B32004791 : Blo 1971435 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B21336527 : Blo 1971435 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B14224351 : Blo 1971435 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B18965801 : Blo 1971435 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B12643867 : Blo 1971435 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B16858489 : Blo 1971435 16858489 := bstep (se 2 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 16858489 = 12643867) B12643867
theorem B22477985 : Blo 1971435 22477985 := bstep (se 2 (by rfl) ⟨8429244, by rfl⟩ : syracuseStep 22477985 = 16858489) B16858489
theorem B14985323 : Blo 1971435 14985323 := bstep (se 1 (by rfl) ⟨11238992, by rfl⟩ : syracuseStep 14985323 = 22477985) B22477985
theorem B9990215 : Blo 1971435 9990215 := bstep (se 1 (by rfl) ⟨7492661, by rfl⟩ : syracuseStep 9990215 = 14985323) B14985323
theorem B6660143 : Blo 1971435 6660143 := bstep (se 1 (by rfl) ⟨4995107, by rfl⟩ : syracuseStep 6660143 = 9990215) B9990215
theorem B4440095 : Blo 1971435 4440095 := bstep (se 1 (by rfl) ⟨3330071, by rfl⟩ : syracuseStep 4440095 = 6660143) B6660143
theorem B2960063 : Blo 1971435 2960063 := bstep (se 1 (by rfl) ⟨2220047, by rfl⟩ : syracuseStep 2960063 = 4440095) B4440095
theorem B1973375 : Blo 1971435 1973375 := bstep (se 1 (by rfl) ⟨1480031, by rfl⟩ : syracuseStep 1973375 = 2960063) B2960063
theorem B2960069 : Blo 1971435 2960069 := bbase (se 4 (by rfl) ⟨277506, by rfl⟩ : syracuseStep 2960069 = 555013) (by norm_num)
theorem B1973379 : Blo 1971435 1973379 := bstep (se 1 (by rfl) ⟨1480034, by rfl⟩ : syracuseStep 1973379 = 2960069) B2960069
theorem B3330085 : Blo 1971435 3330085 := bbase (se 4 (by rfl) ⟨312195, by rfl⟩ : syracuseStep 3330085 = 624391) (by norm_num)
theorem B4440113 : Blo 1971435 4440113 := bstep (se 2 (by rfl) ⟨1665042, by rfl⟩ : syracuseStep 4440113 = 3330085) B3330085
theorem B2960075 : Blo 1971435 2960075 := bstep (se 1 (by rfl) ⟨2220056, by rfl⟩ : syracuseStep 2960075 = 4440113) B4440113
theorem B1973383 : Blo 1971435 1973383 := bstep (se 1 (by rfl) ⟨1480037, by rfl⟩ : syracuseStep 1973383 = 2960075) B2960075
theorem B2220061 : Blo 1971435 2220061 := bbase (se 3 (by rfl) ⟨416261, by rfl⟩ : syracuseStep 2220061 = 832523) (by norm_num)
theorem B2960081 : Blo 1971435 2960081 := bstep (se 2 (by rfl) ⟨1110030, by rfl⟩ : syracuseStep 2960081 = 2220061) B2220061
theorem B1973387 : Blo 1971435 1973387 := bstep (se 1 (by rfl) ⟨1480040, by rfl⟩ : syracuseStep 1973387 = 2960081) B2960081
theorem B6660197 : Blo 1971435 6660197 := bbase (se 4 (by rfl) ⟨624393, by rfl⟩ : syracuseStep 6660197 = 1248787) (by norm_num)
theorem B4440131 : Blo 1971435 4440131 := bstep (se 1 (by rfl) ⟨3330098, by rfl⟩ : syracuseStep 4440131 = 6660197) B6660197
theorem B2960087 : Blo 1971435 2960087 := bstep (se 1 (by rfl) ⟨2220065, by rfl⟩ : syracuseStep 2960087 = 4440131) B4440131
theorem B1973391 : Blo 1971435 1973391 := bstep (se 1 (by rfl) ⟨1480043, by rfl⟩ : syracuseStep 1973391 = 2960087) B2960087
theorem B2960093 : Blo 1971435 2960093 := bbase (se 3 (by rfl) ⟨555017, by rfl⟩ : syracuseStep 2960093 = 1110035) (by norm_num)
theorem B1973395 : Blo 1971435 1973395 := bstep (se 1 (by rfl) ⟨1480046, by rfl⟩ : syracuseStep 1973395 = 2960093) B2960093
theorem B4440149 : Blo 1971435 4440149 := bbase (se 8 (by rfl) ⟨26016, by rfl⟩ : syracuseStep 4440149 = 52033) (by norm_num)
theorem B2960099 : Blo 1971435 2960099 := bstep (se 1 (by rfl) ⟨2220074, by rfl⟩ : syracuseStep 2960099 = 4440149) B4440149
theorem B1973399 : Blo 1971435 1973399 := bstep (se 1 (by rfl) ⟨1480049, by rfl⟩ : syracuseStep 1973399 = 2960099) B2960099
theorem B3000493 : Blo 1971435 3000493 := bbase (se 3 (by rfl) ⟨562592, by rfl⟩ : syracuseStep 3000493 = 1125185) (by norm_num)
theorem B16002629 : Blo 1971435 16002629 := bstep (se 4 (by rfl) ⟨1500246, by rfl⟩ : syracuseStep 16002629 = 3000493) B3000493
theorem B10668419 : Blo 1971435 10668419 := bstep (se 1 (by rfl) ⟨8001314, by rfl⟩ : syracuseStep 10668419 = 16002629) B16002629
theorem B7112279 : Blo 1971435 7112279 := bstep (se 1 (by rfl) ⟨5334209, by rfl⟩ : syracuseStep 7112279 = 10668419) B10668419
theorem B4741519 : Blo 1971435 4741519 := bstep (se 1 (by rfl) ⟨3556139, by rfl⟩ : syracuseStep 4741519 = 7112279) B7112279
theorem B6322025 : Blo 1971435 6322025 := bstep (se 2 (by rfl) ⟨2370759, by rfl⟩ : syracuseStep 6322025 = 4741519) B4741519
theorem B4214683 : Blo 1971435 4214683 := bstep (se 1 (by rfl) ⟨3161012, by rfl⟩ : syracuseStep 4214683 = 6322025) B6322025
theorem B5619577 : Blo 1971435 5619577 := bstep (se 2 (by rfl) ⟨2107341, by rfl⟩ : syracuseStep 5619577 = 4214683) B4214683
theorem B7492769 : Blo 1971435 7492769 := bstep (se 2 (by rfl) ⟨2809788, by rfl⟩ : syracuseStep 7492769 = 5619577) B5619577
theorem B4995179 : Blo 1971435 4995179 := bstep (se 1 (by rfl) ⟨3746384, by rfl⟩ : syracuseStep 4995179 = 7492769) B7492769
theorem B3330119 : Blo 1971435 3330119 := bstep (se 1 (by rfl) ⟨2497589, by rfl⟩ : syracuseStep 3330119 = 4995179) B4995179
theorem B2220079 : Blo 1971435 2220079 := bstep (se 1 (by rfl) ⟨1665059, by rfl⟩ : syracuseStep 2220079 = 3330119) B3330119
theorem B2960105 : Blo 1971435 2960105 := bstep (se 2 (by rfl) ⟨1110039, by rfl⟩ : syracuseStep 2960105 = 2220079) B2220079
theorem B1973403 : Blo 1971435 1973403 := bstep (se 1 (by rfl) ⟨1480052, by rfl⟩ : syracuseStep 1973403 = 2960105) B2960105
theorem B10668437 : Blo 1971435 10668437 := bbase (se 6 (by rfl) ⟨250041, by rfl⟩ : syracuseStep 10668437 = 500083) (by norm_num)
theorem B7112291 : Blo 1971435 7112291 := bstep (se 1 (by rfl) ⟨5334218, by rfl⟩ : syracuseStep 7112291 = 10668437) B10668437
theorem B18966109 : Blo 1971435 18966109 := bstep (se 3 (by rfl) ⟨3556145, by rfl⟩ : syracuseStep 18966109 = 7112291) B7112291
theorem B25288145 : Blo 1971435 25288145 := bstep (se 2 (by rfl) ⟨9483054, by rfl⟩ : syracuseStep 25288145 = 18966109) B18966109
theorem B16858763 : Blo 1971435 16858763 := bstep (se 1 (by rfl) ⟨12644072, by rfl⟩ : syracuseStep 16858763 = 25288145) B25288145
theorem B11239175 : Blo 1971435 11239175 := bstep (se 1 (by rfl) ⟨8429381, by rfl⟩ : syracuseStep 11239175 = 16858763) B16858763
theorem B7492783 : Blo 1971435 7492783 := bstep (se 1 (by rfl) ⟨5619587, by rfl⟩ : syracuseStep 7492783 = 11239175) B11239175
theorem B9990377 : Blo 1971435 9990377 := bstep (se 2 (by rfl) ⟨3746391, by rfl⟩ : syracuseStep 9990377 = 7492783) B7492783
theorem B6660251 : Blo 1971435 6660251 := bstep (se 1 (by rfl) ⟨4995188, by rfl⟩ : syracuseStep 6660251 = 9990377) B9990377
theorem B4440167 : Blo 1971435 4440167 := bstep (se 1 (by rfl) ⟨3330125, by rfl⟩ : syracuseStep 4440167 = 6660251) B6660251
theorem B2960111 : Blo 1971435 2960111 := bstep (se 1 (by rfl) ⟨2220083, by rfl⟩ : syracuseStep 2960111 = 4440167) B4440167
theorem B1973407 : Blo 1971435 1973407 := bstep (se 1 (by rfl) ⟨1480055, by rfl⟩ : syracuseStep 1973407 = 2960111) B2960111
theorem B2960117 : Blo 1971435 2960117 := bbase (se 5 (by rfl) ⟨138755, by rfl⟩ : syracuseStep 2960117 = 277511) (by norm_num)
theorem B1973411 : Blo 1971435 1973411 := bstep (se 1 (by rfl) ⟨1480058, by rfl⟩ : syracuseStep 1973411 = 2960117) B2960117
theorem B17088853 : Blo 1971435 17088853 := bbase (se 10 (by rfl) ⟨25032, by rfl⟩ : syracuseStep 17088853 = 50065) (by norm_num)
theorem B22785137 : Blo 1971435 22785137 := bstep (se 2 (by rfl) ⟨8544426, by rfl⟩ : syracuseStep 22785137 = 17088853) B17088853
theorem B15190091 : Blo 1971435 15190091 := bstep (se 1 (by rfl) ⟨11392568, by rfl⟩ : syracuseStep 15190091 = 22785137) B22785137
theorem B10126727 : Blo 1971435 10126727 := bstep (se 1 (by rfl) ⟨7595045, by rfl⟩ : syracuseStep 10126727 = 15190091) B15190091
theorem B6751151 : Blo 1971435 6751151 := bstep (se 1 (by rfl) ⟨5063363, by rfl⟩ : syracuseStep 6751151 = 10126727) B10126727
theorem B4500767 : Blo 1971435 4500767 := bstep (se 1 (by rfl) ⟨3375575, by rfl⟩ : syracuseStep 4500767 = 6751151) B6751151
theorem B3000511 : Blo 1971435 3000511 := bstep (se 1 (by rfl) ⟨2250383, by rfl⟩ : syracuseStep 3000511 = 4500767) B4500767
theorem B4000681 : Blo 1971435 4000681 := bstep (se 2 (by rfl) ⟨1500255, by rfl⟩ : syracuseStep 4000681 = 3000511) B3000511
theorem B21336965 : Blo 1971435 21336965 := bstep (se 4 (by rfl) ⟨2000340, by rfl⟩ : syracuseStep 21336965 = 4000681) B4000681
theorem B14224643 : Blo 1971435 14224643 := bstep (se 1 (by rfl) ⟨10668482, by rfl⟩ : syracuseStep 14224643 = 21336965) B21336965
theorem B9483095 : Blo 1971435 9483095 := bstep (se 1 (by rfl) ⟨7112321, by rfl⟩ : syracuseStep 9483095 = 14224643) B14224643
theorem B6322063 : Blo 1971435 6322063 := bstep (se 1 (by rfl) ⟨4741547, by rfl⟩ : syracuseStep 6322063 = 9483095) B9483095
theorem B8429417 : Blo 1971435 8429417 := bstep (se 2 (by rfl) ⟨3161031, by rfl⟩ : syracuseStep 8429417 = 6322063) B6322063
theorem B5619611 : Blo 1971435 5619611 := bstep (se 1 (by rfl) ⟨4214708, by rfl⟩ : syracuseStep 5619611 = 8429417) B8429417
theorem B3746407 : Blo 1971435 3746407 := bstep (se 1 (by rfl) ⟨2809805, by rfl⟩ : syracuseStep 3746407 = 5619611) B5619611
theorem B4995209 : Blo 1971435 4995209 := bstep (se 2 (by rfl) ⟨1873203, by rfl⟩ : syracuseStep 4995209 = 3746407) B3746407
theorem B3330139 : Blo 1971435 3330139 := bstep (se 1 (by rfl) ⟨2497604, by rfl⟩ : syracuseStep 3330139 = 4995209) B4995209
theorem B4440185 : Blo 1971435 4440185 := bstep (se 2 (by rfl) ⟨1665069, by rfl⟩ : syracuseStep 4440185 = 3330139) B3330139
theorem B2960123 : Blo 1971435 2960123 := bstep (se 1 (by rfl) ⟨2220092, by rfl⟩ : syracuseStep 2960123 = 4440185) B4440185
theorem B1973415 : Blo 1971435 1973415 := bstep (se 1 (by rfl) ⟨1480061, by rfl⟩ : syracuseStep 1973415 = 2960123) B2960123
theorem B2220097 : Blo 1971435 2220097 := bbase (se 2 (by rfl) ⟨832536, by rfl⟩ : syracuseStep 2220097 = 1665073) (by norm_num)
theorem B2960129 : Blo 1971435 2960129 := bstep (se 2 (by rfl) ⟨1110048, by rfl⟩ : syracuseStep 2960129 = 2220097) B2220097
theorem B1973419 : Blo 1971435 1973419 := bstep (se 1 (by rfl) ⟨1480064, by rfl⟩ : syracuseStep 1973419 = 2960129) B2960129
theorem B4995229 : Blo 1971435 4995229 := bbase (se 3 (by rfl) ⟨936605, by rfl⟩ : syracuseStep 4995229 = 1873211) (by norm_num)
theorem B6660305 : Blo 1971435 6660305 := bstep (se 2 (by rfl) ⟨2497614, by rfl⟩ : syracuseStep 6660305 = 4995229) B4995229
theorem B4440203 : Blo 1971435 4440203 := bstep (se 1 (by rfl) ⟨3330152, by rfl⟩ : syracuseStep 4440203 = 6660305) B6660305
theorem B2960135 : Blo 1971435 2960135 := bstep (se 1 (by rfl) ⟨2220101, by rfl⟩ : syracuseStep 2960135 = 4440203) B4440203
theorem B1973423 : Blo 1971435 1973423 := bstep (se 1 (by rfl) ⟨1480067, by rfl⟩ : syracuseStep 1973423 = 2960135) B2960135
theorem B2960141 : Blo 1971435 2960141 := bbase (se 3 (by rfl) ⟨555026, by rfl⟩ : syracuseStep 2960141 = 1110053) (by norm_num)
theorem B1973427 : Blo 1971435 1973427 := bstep (se 1 (by rfl) ⟨1480070, by rfl⟩ : syracuseStep 1973427 = 2960141) B2960141
theorem B4440221 : Blo 1971435 4440221 := bbase (se 3 (by rfl) ⟨832541, by rfl⟩ : syracuseStep 4440221 = 1665083) (by norm_num)
theorem B2960147 : Blo 1971435 2960147 := bstep (se 1 (by rfl) ⟨2220110, by rfl⟩ : syracuseStep 2960147 = 4440221) B4440221
theorem B1973431 : Blo 1971435 1973431 := bstep (se 1 (by rfl) ⟨1480073, by rfl⟩ : syracuseStep 1973431 = 2960147) B2960147
theorem B3330173 : Blo 1971435 3330173 := bbase (se 3 (by rfl) ⟨624407, by rfl⟩ : syracuseStep 3330173 = 1248815) (by norm_num)
theorem B2220115 : Blo 1971435 2220115 := bstep (se 1 (by rfl) ⟨1665086, by rfl⟩ : syracuseStep 2220115 = 3330173) B3330173
theorem B2960153 : Blo 1971435 2960153 := bstep (se 2 (by rfl) ⟨1110057, by rfl⟩ : syracuseStep 2960153 = 2220115) B2220115
theorem B1973435 : Blo 1971435 1973435 := bstep (se 1 (by rfl) ⟨1480076, by rfl⟩ : syracuseStep 1973435 = 2960153) B2960153
theorem C0 (j : ℕ) (h1 : 492858 ≤ j) (h2 : j ≤ 493358) : Blo 1971435 (4 * j + 3) := by
  interval_cases j
  · exact B1971435
  · exact B1971439
  · exact B1971443
  · exact B1971447
  · exact B1971451
  · exact B1971455
  · exact B1971459
  · exact B1971463
  · exact B1971467
  · exact B1971471
  · exact B1971475
  · exact B1971479
  · exact B1971483
  · exact B1971487
  · exact B1971491
  · exact B1971495
  · exact B1971499
  · exact B1971503
  · exact B1971507
  · exact B1971511
  · exact B1971515
  · exact B1971519
  · exact B1971523
  · exact B1971527
  · exact B1971531
  · exact B1971535
  · exact B1971539
  · exact B1971543
  · exact B1971547
  · exact B1971551
  · exact B1971555
  · exact B1971559
  · exact B1971563
  · exact B1971567
  · exact B1971571
  · exact B1971575
  · exact B1971579
  · exact B1971583
  · exact B1971587
  · exact B1971591
  · exact B1971595
  · exact B1971599
  · exact B1971603
  · exact B1971607
  · exact B1971611
  · exact B1971615
  · exact B1971619
  · exact B1971623
  · exact B1971627
  · exact B1971631
  · exact B1971635
  · exact B1971639
  · exact B1971643
  · exact B1971647
  · exact B1971651
  · exact B1971655
  · exact B1971659
  · exact B1971663
  · exact B1971667
  · exact B1971671
  · exact B1971675
  · exact B1971679
  · exact B1971683
  · exact B1971687
  · exact B1971691
  · exact B1971695
  · exact B1971699
  · exact B1971703
  · exact B1971707
  · exact B1971711
  · exact B1971715
  · exact B1971719
  · exact B1971723
  · exact B1971727
  · exact B1971731
  · exact B1971735
  · exact B1971739
  · exact B1971743
  · exact B1971747
  · exact B1971751
  · exact B1971755
  · exact B1971759
  · exact B1971763
  · exact B1971767
  · exact B1971771
  · exact B1971775
  · exact B1971779
  · exact B1971783
  · exact B1971787
  · exact B1971791
  · exact B1971795
  · exact B1971799
  · exact B1971803
  · exact B1971807
  · exact B1971811
  · exact B1971815
  · exact B1971819
  · exact B1971823
  · exact B1971827
  · exact B1971831
  · exact B1971835
  · exact B1971839
  · exact B1971843
  · exact B1971847
  · exact B1971851
  · exact B1971855
  · exact B1971859
  · exact B1971863
  · exact B1971867
  · exact B1971871
  · exact B1971875
  · exact B1971879
  · exact B1971883
  · exact B1971887
  · exact B1971891
  · exact B1971895
  · exact B1971899
  · exact B1971903
  · exact B1971907
  · exact B1971911
  · exact B1971915
  · exact B1971919
  · exact B1971923
  · exact B1971927
  · exact B1971931
  · exact B1971935
  · exact B1971939
  · exact B1971943
  · exact B1971947
  · exact B1971951
  · exact B1971955
  · exact B1971959
  · exact B1971963
  · exact B1971967
  · exact B1971971
  · exact B1971975
  · exact B1971979
  · exact B1971983
  · exact B1971987
  · exact B1971991
  · exact B1971995
  · exact B1971999
  · exact B1972003
  · exact B1972007
  · exact B1972011
  · exact B1972015
  · exact B1972019
  · exact B1972023
  · exact B1972027
  · exact B1972031
  · exact B1972035
  · exact B1972039
  · exact B1972043
  · exact B1972047
  · exact B1972051
  · exact B1972055
  · exact B1972059
  · exact B1972063
  · exact B1972067
  · exact B1972071
  · exact B1972075
  · exact B1972079
  · exact B1972083
  · exact B1972087
  · exact B1972091
  · exact B1972095
  · exact B1972099
  · exact B1972103
  · exact B1972107
  · exact B1972111
  · exact B1972115
  · exact B1972119
  · exact B1972123
  · exact B1972127
  · exact B1972131
  · exact B1972135
  · exact B1972139
  · exact B1972143
  · exact B1972147
  · exact B1972151
  · exact B1972155
  · exact B1972159
  · exact B1972163
  · exact B1972167
  · exact B1972171
  · exact B1972175
  · exact B1972179
  · exact B1972183
  · exact B1972187
  · exact B1972191
  · exact B1972195
  · exact B1972199
  · exact B1972203
  · exact B1972207
  · exact B1972211
  · exact B1972215
  · exact B1972219
  · exact B1972223
  · exact B1972227
  · exact B1972231
  · exact B1972235
  · exact B1972239
  · exact B1972243
  · exact B1972247
  · exact B1972251
  · exact B1972255
  · exact B1972259
  · exact B1972263
  · exact B1972267
  · exact B1972271
  · exact B1972275
  · exact B1972279
  · exact B1972283
  · exact B1972287
  · exact B1972291
  · exact B1972295
  · exact B1972299
  · exact B1972303
  · exact B1972307
  · exact B1972311
  · exact B1972315
  · exact B1972319
  · exact B1972323
  · exact B1972327
  · exact B1972331
  · exact B1972335
  · exact B1972339
  · exact B1972343
  · exact B1972347
  · exact B1972351
  · exact B1972355
  · exact B1972359
  · exact B1972363
  · exact B1972367
  · exact B1972371
  · exact B1972375
  · exact B1972379
  · exact B1972383
  · exact B1972387
  · exact B1972391
  · exact B1972395
  · exact B1972399
  · exact B1972403
  · exact B1972407
  · exact B1972411
  · exact B1972415
  · exact B1972419
  · exact B1972423
  · exact B1972427
  · exact B1972431
  · exact B1972435
  · exact B1972439
  · exact B1972443
  · exact B1972447
  · exact B1972451
  · exact B1972455
  · exact B1972459
  · exact B1972463
  · exact B1972467
  · exact B1972471
  · exact B1972475
  · exact B1972479
  · exact B1972483
  · exact B1972487
  · exact B1972491
  · exact B1972495
  · exact B1972499
  · exact B1972503
  · exact B1972507
  · exact B1972511
  · exact B1972515
  · exact B1972519
  · exact B1972523
  · exact B1972527
  · exact B1972531
  · exact B1972535
  · exact B1972539
  · exact B1972543
  · exact B1972547
  · exact B1972551
  · exact B1972555
  · exact B1972559
  · exact B1972563
  · exact B1972567
  · exact B1972571
  · exact B1972575
  · exact B1972579
  · exact B1972583
  · exact B1972587
  · exact B1972591
  · exact B1972595
  · exact B1972599
  · exact B1972603
  · exact B1972607
  · exact B1972611
  · exact B1972615
  · exact B1972619
  · exact B1972623
  · exact B1972627
  · exact B1972631
  · exact B1972635
  · exact B1972639
  · exact B1972643
  · exact B1972647
  · exact B1972651
  · exact B1972655
  · exact B1972659
  · exact B1972663
  · exact B1972667
  · exact B1972671
  · exact B1972675
  · exact B1972679
  · exact B1972683
  · exact B1972687
  · exact B1972691
  · exact B1972695
  · exact B1972699
  · exact B1972703
  · exact B1972707
  · exact B1972711
  · exact B1972715
  · exact B1972719
  · exact B1972723
  · exact B1972727
  · exact B1972731
  · exact B1972735
  · exact B1972739
  · exact B1972743
  · exact B1972747
  · exact B1972751
  · exact B1972755
  · exact B1972759
  · exact B1972763
  · exact B1972767
  · exact B1972771
  · exact B1972775
  · exact B1972779
  · exact B1972783
  · exact B1972787
  · exact B1972791
  · exact B1972795
  · exact B1972799
  · exact B1972803
  · exact B1972807
  · exact B1972811
  · exact B1972815
  · exact B1972819
  · exact B1972823
  · exact B1972827
  · exact B1972831
  · exact B1972835
  · exact B1972839
  · exact B1972843
  · exact B1972847
  · exact B1972851
  · exact B1972855
  · exact B1972859
  · exact B1972863
  · exact B1972867
  · exact B1972871
  · exact B1972875
  · exact B1972879
  · exact B1972883
  · exact B1972887
  · exact B1972891
  · exact B1972895
  · exact B1972899
  · exact B1972903
  · exact B1972907
  · exact B1972911
  · exact B1972915
  · exact B1972919
  · exact B1972923
  · exact B1972927
  · exact B1972931
  · exact B1972935
  · exact B1972939
  · exact B1972943
  · exact B1972947
  · exact B1972951
  · exact B1972955
  · exact B1972959
  · exact B1972963
  · exact B1972967
  · exact B1972971
  · exact B1972975
  · exact B1972979
  · exact B1972983
  · exact B1972987
  · exact B1972991
  · exact B1972995
  · exact B1972999
  · exact B1973003
  · exact B1973007
  · exact B1973011
  · exact B1973015
  · exact B1973019
  · exact B1973023
  · exact B1973027
  · exact B1973031
  · exact B1973035
  · exact B1973039
  · exact B1973043
  · exact B1973047
  · exact B1973051
  · exact B1973055
  · exact B1973059
  · exact B1973063
  · exact B1973067
  · exact B1973071
  · exact B1973075
  · exact B1973079
  · exact B1973083
  · exact B1973087
  · exact B1973091
  · exact B1973095
  · exact B1973099
  · exact B1973103
  · exact B1973107
  · exact B1973111
  · exact B1973115
  · exact B1973119
  · exact B1973123
  · exact B1973127
  · exact B1973131
  · exact B1973135
  · exact B1973139
  · exact B1973143
  · exact B1973147
  · exact B1973151
  · exact B1973155
  · exact B1973159
  · exact B1973163
  · exact B1973167
  · exact B1973171
  · exact B1973175
  · exact B1973179
  · exact B1973183
  · exact B1973187
  · exact B1973191
  · exact B1973195
  · exact B1973199
  · exact B1973203
  · exact B1973207
  · exact B1973211
  · exact B1973215
  · exact B1973219
  · exact B1973223
  · exact B1973227
  · exact B1973231
  · exact B1973235
  · exact B1973239
  · exact B1973243
  · exact B1973247
  · exact B1973251
  · exact B1973255
  · exact B1973259
  · exact B1973263
  · exact B1973267
  · exact B1973271
  · exact B1973275
  · exact B1973279
  · exact B1973283
  · exact B1973287
  · exact B1973291
  · exact B1973295
  · exact B1973299
  · exact B1973303
  · exact B1973307
  · exact B1973311
  · exact B1973315
  · exact B1973319
  · exact B1973323
  · exact B1973327
  · exact B1973331
  · exact B1973335
  · exact B1973339
  · exact B1973343
  · exact B1973347
  · exact B1973351
  · exact B1973355
  · exact B1973359
  · exact B1973363
  · exact B1973367
  · exact B1973371
  · exact B1973375
  · exact B1973379
  · exact B1973383
  · exact B1973387
  · exact B1973391
  · exact B1973395
  · exact B1973399
  · exact B1973403
  · exact B1973407
  · exact B1973411
  · exact B1973415
  · exact B1973419
  · exact B1973423
  · exact B1973427
  · exact B1973431
  · exact B1973435
theorem solution (m : ℕ) (hlo : 1971435 ≤ m) (hhi : m ≤ 1973435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 492858 ≤ j := by omega
    have hj2 : j ≤ 493358 := by omega
    have hb : Blo 1971435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
