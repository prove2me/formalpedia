-- Prove2me | solution 1 for syracuse_descends_range_1923435_1925435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:14.227158+00:00
-- url     : https://prove2.me/submissions/292185de-0292-477e-95cf-57b2d3f4a7dd

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

theorem B2163865 : Blo 1923435 2163865 := bbase (se 2 (by rfl) ⟨811449, by rfl⟩ : syracuseStep 2163865 = 1622899) (by norm_num)
theorem B2885153 : Blo 1923435 2885153 := bstep (se 2 (by rfl) ⟨1081932, by rfl⟩ : syracuseStep 2885153 = 2163865) B2163865
theorem B1923435 : Blo 1923435 1923435 := bstep (se 1 (by rfl) ⟨1442576, by rfl⟩ : syracuseStep 1923435 = 2885153) B2885153
theorem B7303061 : Blo 1923435 7303061 := bbase (se 6 (by rfl) ⟨171165, by rfl⟩ : syracuseStep 7303061 = 342331) (by norm_num)
theorem B4868707 : Blo 1923435 4868707 := bstep (se 1 (by rfl) ⟨3651530, by rfl⟩ : syracuseStep 4868707 = 7303061) B7303061
theorem B6491609 : Blo 1923435 6491609 := bstep (se 2 (by rfl) ⟨2434353, by rfl⟩ : syracuseStep 6491609 = 4868707) B4868707
theorem B4327739 : Blo 1923435 4327739 := bstep (se 1 (by rfl) ⟨3245804, by rfl⟩ : syracuseStep 4327739 = 6491609) B6491609
theorem B2885159 : Blo 1923435 2885159 := bstep (se 1 (by rfl) ⟨2163869, by rfl⟩ : syracuseStep 2885159 = 4327739) B4327739
theorem B1923439 : Blo 1923435 1923439 := bstep (se 1 (by rfl) ⟨1442579, by rfl⟩ : syracuseStep 1923439 = 2885159) B2885159
theorem B2885165 : Blo 1923435 2885165 := bbase (se 3 (by rfl) ⟨540968, by rfl⟩ : syracuseStep 2885165 = 1081937) (by norm_num)
theorem B1923443 : Blo 1923435 1923443 := bstep (se 1 (by rfl) ⟨1442582, by rfl⟩ : syracuseStep 1923443 = 2885165) B2885165
theorem B4327757 : Blo 1923435 4327757 := bbase (se 3 (by rfl) ⟨811454, by rfl⟩ : syracuseStep 4327757 = 1622909) (by norm_num)
theorem B2885171 : Blo 1923435 2885171 := bstep (se 1 (by rfl) ⟨2163878, by rfl⟩ : syracuseStep 2885171 = 4327757) B4327757
theorem B1923447 : Blo 1923435 1923447 := bstep (se 1 (by rfl) ⟨1442585, by rfl⟩ : syracuseStep 1923447 = 2885171) B2885171
theorem B2434369 : Blo 1923435 2434369 := bbase (se 2 (by rfl) ⟨912888, by rfl⟩ : syracuseStep 2434369 = 1825777) (by norm_num)
theorem B3245825 : Blo 1923435 3245825 := bstep (se 2 (by rfl) ⟨1217184, by rfl⟩ : syracuseStep 3245825 = 2434369) B2434369
theorem B2163883 : Blo 1923435 2163883 := bstep (se 1 (by rfl) ⟨1622912, by rfl⟩ : syracuseStep 2163883 = 3245825) B3245825
theorem B2885177 : Blo 1923435 2885177 := bstep (se 2 (by rfl) ⟨1081941, by rfl⟩ : syracuseStep 2885177 = 2163883) B2163883
theorem B1923451 : Blo 1923435 1923451 := bstep (se 1 (by rfl) ⟨1442588, by rfl⟩ : syracuseStep 1923451 = 2885177) B2885177
theorem B3081005 : Blo 1923435 3081005 := bbase (se 3 (by rfl) ⟨577688, by rfl⟩ : syracuseStep 3081005 = 1155377) (by norm_num)
theorem B2054003 : Blo 1923435 2054003 := bstep (se 1 (by rfl) ⟨1540502, by rfl⟩ : syracuseStep 2054003 = 3081005) B3081005
theorem B21909365 : Blo 1923435 21909365 := bstep (se 5 (by rfl) ⟨1027001, by rfl⟩ : syracuseStep 21909365 = 2054003) B2054003
theorem B14606243 : Blo 1923435 14606243 := bstep (se 1 (by rfl) ⟨10954682, by rfl⟩ : syracuseStep 14606243 = 21909365) B21909365
theorem B9737495 : Blo 1923435 9737495 := bstep (se 1 (by rfl) ⟨7303121, by rfl⟩ : syracuseStep 9737495 = 14606243) B14606243
theorem B6491663 : Blo 1923435 6491663 := bstep (se 1 (by rfl) ⟨4868747, by rfl⟩ : syracuseStep 6491663 = 9737495) B9737495
theorem B4327775 : Blo 1923435 4327775 := bstep (se 1 (by rfl) ⟨3245831, by rfl⟩ : syracuseStep 4327775 = 6491663) B6491663
theorem B2885183 : Blo 1923435 2885183 := bstep (se 1 (by rfl) ⟨2163887, by rfl⟩ : syracuseStep 2885183 = 4327775) B4327775
theorem B1923455 : Blo 1923435 1923455 := bstep (se 1 (by rfl) ⟨1442591, by rfl⟩ : syracuseStep 1923455 = 2885183) B2885183
theorem B2885189 : Blo 1923435 2885189 := bbase (se 4 (by rfl) ⟨270486, by rfl⟩ : syracuseStep 2885189 = 540973) (by norm_num)
theorem B1923459 : Blo 1923435 1923459 := bstep (se 1 (by rfl) ⟨1442594, by rfl⟩ : syracuseStep 1923459 = 2885189) B2885189
theorem B3245845 : Blo 1923435 3245845 := bbase (se 6 (by rfl) ⟨76074, by rfl⟩ : syracuseStep 3245845 = 152149) (by norm_num)
theorem B4327793 : Blo 1923435 4327793 := bstep (se 2 (by rfl) ⟨1622922, by rfl⟩ : syracuseStep 4327793 = 3245845) B3245845
theorem B2885195 : Blo 1923435 2885195 := bstep (se 1 (by rfl) ⟨2163896, by rfl⟩ : syracuseStep 2885195 = 4327793) B4327793
theorem B1923463 : Blo 1923435 1923463 := bstep (se 1 (by rfl) ⟨1442597, by rfl⟩ : syracuseStep 1923463 = 2885195) B2885195
theorem B2163901 : Blo 1923435 2163901 := bbase (se 3 (by rfl) ⟨405731, by rfl⟩ : syracuseStep 2163901 = 811463) (by norm_num)
theorem B2885201 : Blo 1923435 2885201 := bstep (se 2 (by rfl) ⟨1081950, by rfl⟩ : syracuseStep 2885201 = 2163901) B2163901
theorem B1923467 : Blo 1923435 1923467 := bstep (se 1 (by rfl) ⟨1442600, by rfl⟩ : syracuseStep 1923467 = 2885201) B2885201
theorem B6491717 : Blo 1923435 6491717 := bbase (se 4 (by rfl) ⟨608598, by rfl⟩ : syracuseStep 6491717 = 1217197) (by norm_num)
theorem B4327811 : Blo 1923435 4327811 := bstep (se 1 (by rfl) ⟨3245858, by rfl⟩ : syracuseStep 4327811 = 6491717) B6491717
theorem B2885207 : Blo 1923435 2885207 := bstep (se 1 (by rfl) ⟨2163905, by rfl⟩ : syracuseStep 2885207 = 4327811) B4327811
theorem B1923471 : Blo 1923435 1923471 := bstep (se 1 (by rfl) ⟨1442603, by rfl⟩ : syracuseStep 1923471 = 2885207) B2885207
theorem B2885213 : Blo 1923435 2885213 := bbase (se 3 (by rfl) ⟨540977, by rfl⟩ : syracuseStep 2885213 = 1081955) (by norm_num)
theorem B1923475 : Blo 1923435 1923475 := bstep (se 1 (by rfl) ⟨1442606, by rfl⟩ : syracuseStep 1923475 = 2885213) B2885213
theorem B4327829 : Blo 1923435 4327829 := bbase (se 6 (by rfl) ⟨101433, by rfl⟩ : syracuseStep 4327829 = 202867) (by norm_num)
theorem B2885219 : Blo 1923435 2885219 := bstep (se 1 (by rfl) ⟨2163914, by rfl⟩ : syracuseStep 2885219 = 4327829) B4327829
theorem B1923479 : Blo 1923435 1923479 := bstep (se 1 (by rfl) ⟨1442609, by rfl⟩ : syracuseStep 1923479 = 2885219) B2885219
theorem B6162101 : Blo 1923435 6162101 := bbase (se 5 (by rfl) ⟨288848, by rfl⟩ : syracuseStep 6162101 = 577697) (by norm_num)
theorem B4108067 : Blo 1923435 4108067 := bstep (se 1 (by rfl) ⟨3081050, by rfl⟩ : syracuseStep 4108067 = 6162101) B6162101
theorem B2738711 : Blo 1923435 2738711 := bstep (se 1 (by rfl) ⟨2054033, by rfl⟩ : syracuseStep 2738711 = 4108067) B4108067
theorem B7303229 : Blo 1923435 7303229 := bstep (se 3 (by rfl) ⟨1369355, by rfl⟩ : syracuseStep 7303229 = 2738711) B2738711
theorem B4868819 : Blo 1923435 4868819 := bstep (se 1 (by rfl) ⟨3651614, by rfl⟩ : syracuseStep 4868819 = 7303229) B7303229
theorem B3245879 : Blo 1923435 3245879 := bstep (se 1 (by rfl) ⟨2434409, by rfl⟩ : syracuseStep 3245879 = 4868819) B4868819
theorem B2163919 : Blo 1923435 2163919 := bstep (se 1 (by rfl) ⟨1622939, by rfl⟩ : syracuseStep 2163919 = 3245879) B3245879
theorem B2885225 : Blo 1923435 2885225 := bstep (se 2 (by rfl) ⟨1081959, by rfl⟩ : syracuseStep 2885225 = 2163919) B2163919
theorem B1923483 : Blo 1923435 1923483 := bstep (se 1 (by rfl) ⟨1442612, by rfl⟩ : syracuseStep 1923483 = 2885225) B2885225
theorem B8216149 : Blo 1923435 8216149 := bbase (se 8 (by rfl) ⟨48141, by rfl⟩ : syracuseStep 8216149 = 96283) (by norm_num)
theorem B10954865 : Blo 1923435 10954865 := bstep (se 2 (by rfl) ⟨4108074, by rfl⟩ : syracuseStep 10954865 = 8216149) B8216149
theorem B7303243 : Blo 1923435 7303243 := bstep (se 1 (by rfl) ⟨5477432, by rfl⟩ : syracuseStep 7303243 = 10954865) B10954865
theorem B9737657 : Blo 1923435 9737657 := bstep (se 2 (by rfl) ⟨3651621, by rfl⟩ : syracuseStep 9737657 = 7303243) B7303243
theorem B6491771 : Blo 1923435 6491771 := bstep (se 1 (by rfl) ⟨4868828, by rfl⟩ : syracuseStep 6491771 = 9737657) B9737657
theorem B4327847 : Blo 1923435 4327847 := bstep (se 1 (by rfl) ⟨3245885, by rfl⟩ : syracuseStep 4327847 = 6491771) B6491771
theorem B2885231 : Blo 1923435 2885231 := bstep (se 1 (by rfl) ⟨2163923, by rfl⟩ : syracuseStep 2885231 = 4327847) B4327847
theorem B1923487 : Blo 1923435 1923487 := bstep (se 1 (by rfl) ⟨1442615, by rfl⟩ : syracuseStep 1923487 = 2885231) B2885231
theorem B2885237 : Blo 1923435 2885237 := bbase (se 5 (by rfl) ⟨135245, by rfl⟩ : syracuseStep 2885237 = 270491) (by norm_num)
theorem B1923491 : Blo 1923435 1923491 := bstep (se 1 (by rfl) ⟨1442618, by rfl⟩ : syracuseStep 1923491 = 2885237) B2885237
theorem B3651637 : Blo 1923435 3651637 := bbase (se 5 (by rfl) ⟨171170, by rfl⟩ : syracuseStep 3651637 = 342341) (by norm_num)
theorem B4868849 : Blo 1923435 4868849 := bstep (se 2 (by rfl) ⟨1825818, by rfl⟩ : syracuseStep 4868849 = 3651637) B3651637
theorem B3245899 : Blo 1923435 3245899 := bstep (se 1 (by rfl) ⟨2434424, by rfl⟩ : syracuseStep 3245899 = 4868849) B4868849
theorem B4327865 : Blo 1923435 4327865 := bstep (se 2 (by rfl) ⟨1622949, by rfl⟩ : syracuseStep 4327865 = 3245899) B3245899
theorem B2885243 : Blo 1923435 2885243 := bstep (se 1 (by rfl) ⟨2163932, by rfl⟩ : syracuseStep 2885243 = 4327865) B4327865
theorem B1923495 : Blo 1923435 1923495 := bstep (se 1 (by rfl) ⟨1442621, by rfl⟩ : syracuseStep 1923495 = 2885243) B2885243
theorem B2163937 : Blo 1923435 2163937 := bbase (se 2 (by rfl) ⟨811476, by rfl⟩ : syracuseStep 2163937 = 1622953) (by norm_num)
theorem B2885249 : Blo 1923435 2885249 := bstep (se 2 (by rfl) ⟨1081968, by rfl⟩ : syracuseStep 2885249 = 2163937) B2163937
theorem B1923499 : Blo 1923435 1923499 := bstep (se 1 (by rfl) ⟨1442624, by rfl⟩ : syracuseStep 1923499 = 2885249) B2885249
theorem B4868869 : Blo 1923435 4868869 := bbase (se 4 (by rfl) ⟨456456, by rfl⟩ : syracuseStep 4868869 = 912913) (by norm_num)
theorem B6491825 : Blo 1923435 6491825 := bstep (se 2 (by rfl) ⟨2434434, by rfl⟩ : syracuseStep 6491825 = 4868869) B4868869
theorem B4327883 : Blo 1923435 4327883 := bstep (se 1 (by rfl) ⟨3245912, by rfl⟩ : syracuseStep 4327883 = 6491825) B6491825
theorem B2885255 : Blo 1923435 2885255 := bstep (se 1 (by rfl) ⟨2163941, by rfl⟩ : syracuseStep 2885255 = 4327883) B4327883
theorem B1923503 : Blo 1923435 1923503 := bstep (se 1 (by rfl) ⟨1442627, by rfl⟩ : syracuseStep 1923503 = 2885255) B2885255
theorem B2885261 : Blo 1923435 2885261 := bbase (se 3 (by rfl) ⟨540986, by rfl⟩ : syracuseStep 2885261 = 1081973) (by norm_num)
theorem B1923507 : Blo 1923435 1923507 := bstep (se 1 (by rfl) ⟨1442630, by rfl⟩ : syracuseStep 1923507 = 2885261) B2885261
theorem B4327901 : Blo 1923435 4327901 := bbase (se 3 (by rfl) ⟨811481, by rfl⟩ : syracuseStep 4327901 = 1622963) (by norm_num)
theorem B2885267 : Blo 1923435 2885267 := bstep (se 1 (by rfl) ⟨2163950, by rfl⟩ : syracuseStep 2885267 = 4327901) B4327901
theorem B1923511 : Blo 1923435 1923511 := bstep (se 1 (by rfl) ⟨1442633, by rfl⟩ : syracuseStep 1923511 = 2885267) B2885267
theorem B3245933 : Blo 1923435 3245933 := bbase (se 3 (by rfl) ⟨608612, by rfl⟩ : syracuseStep 3245933 = 1217225) (by norm_num)
theorem B2163955 : Blo 1923435 2163955 := bstep (se 1 (by rfl) ⟨1622966, by rfl⟩ : syracuseStep 2163955 = 3245933) B3245933
theorem B2885273 : Blo 1923435 2885273 := bstep (se 2 (by rfl) ⟨1081977, by rfl⟩ : syracuseStep 2885273 = 2163955) B2163955
theorem B1923515 : Blo 1923435 1923515 := bstep (se 1 (by rfl) ⟨1442636, by rfl⟩ : syracuseStep 1923515 = 2885273) B2885273
theorem B2924645 : Blo 1923435 2924645 := bbase (se 4 (by rfl) ⟨274185, by rfl⟩ : syracuseStep 2924645 = 548371) (by norm_num)
theorem B7799053 : Blo 1923435 7799053 := bstep (se 3 (by rfl) ⟨1462322, by rfl⟩ : syracuseStep 7799053 = 2924645) B2924645
theorem B10398737 : Blo 1923435 10398737 := bstep (se 2 (by rfl) ⟨3899526, by rfl⟩ : syracuseStep 10398737 = 7799053) B7799053
theorem B27729965 : Blo 1923435 27729965 := bstep (se 3 (by rfl) ⟨5199368, by rfl⟩ : syracuseStep 27729965 = 10398737) B10398737
theorem B18486643 : Blo 1923435 18486643 := bstep (se 1 (by rfl) ⟨13864982, by rfl⟩ : syracuseStep 18486643 = 27729965) B27729965
theorem B24648857 : Blo 1923435 24648857 := bstep (se 2 (by rfl) ⟨9243321, by rfl⟩ : syracuseStep 24648857 = 18486643) B18486643
theorem B16432571 : Blo 1923435 16432571 := bstep (se 1 (by rfl) ⟨12324428, by rfl⟩ : syracuseStep 16432571 = 24648857) B24648857
theorem B10955047 : Blo 1923435 10955047 := bstep (se 1 (by rfl) ⟨8216285, by rfl⟩ : syracuseStep 10955047 = 16432571) B16432571
theorem B14606729 : Blo 1923435 14606729 := bstep (se 2 (by rfl) ⟨5477523, by rfl⟩ : syracuseStep 14606729 = 10955047) B10955047
theorem B9737819 : Blo 1923435 9737819 := bstep (se 1 (by rfl) ⟨7303364, by rfl⟩ : syracuseStep 9737819 = 14606729) B14606729
theorem B6491879 : Blo 1923435 6491879 := bstep (se 1 (by rfl) ⟨4868909, by rfl⟩ : syracuseStep 6491879 = 9737819) B9737819
theorem B4327919 : Blo 1923435 4327919 := bstep (se 1 (by rfl) ⟨3245939, by rfl⟩ : syracuseStep 4327919 = 6491879) B6491879
theorem B2885279 : Blo 1923435 2885279 := bstep (se 1 (by rfl) ⟨2163959, by rfl⟩ : syracuseStep 2885279 = 4327919) B4327919
theorem B1923519 : Blo 1923435 1923519 := bstep (se 1 (by rfl) ⟨1442639, by rfl⟩ : syracuseStep 1923519 = 2885279) B2885279
theorem B2885285 : Blo 1923435 2885285 := bbase (se 4 (by rfl) ⟨270495, by rfl⟩ : syracuseStep 2885285 = 540991) (by norm_num)
theorem B1923523 : Blo 1923435 1923523 := bstep (se 1 (by rfl) ⟨1442642, by rfl⟩ : syracuseStep 1923523 = 2885285) B2885285
theorem B2434465 : Blo 1923435 2434465 := bbase (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) (by norm_num)
theorem B3245953 : Blo 1923435 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B4327937 : Blo 1923435 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B2885291 : Blo 1923435 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B1923527 : Blo 1923435 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B2163973 : Blo 1923435 2163973 := bbase (se 4 (by rfl) ⟨202872, by rfl⟩ : syracuseStep 2163973 = 405745) (by norm_num)
theorem B2885297 : Blo 1923435 2885297 := bstep (se 2 (by rfl) ⟨1081986, by rfl⟩ : syracuseStep 2885297 = 2163973) B2163973
theorem B1923531 : Blo 1923435 1923531 := bstep (se 1 (by rfl) ⟨1442648, by rfl⟩ : syracuseStep 1923531 = 2885297) B2885297
theorem B2054089 : Blo 1923435 2054089 := bbase (se 2 (by rfl) ⟨770283, by rfl⟩ : syracuseStep 2054089 = 1540567) (by norm_num)
theorem B2738785 : Blo 1923435 2738785 := bstep (se 2 (by rfl) ⟨1027044, by rfl⟩ : syracuseStep 2738785 = 2054089) B2054089
theorem B3651713 : Blo 1923435 3651713 := bstep (se 2 (by rfl) ⟨1369392, by rfl⟩ : syracuseStep 3651713 = 2738785) B2738785
theorem B2434475 : Blo 1923435 2434475 := bstep (se 1 (by rfl) ⟨1825856, by rfl⟩ : syracuseStep 2434475 = 3651713) B3651713
theorem B6491933 : Blo 1923435 6491933 := bstep (se 3 (by rfl) ⟨1217237, by rfl⟩ : syracuseStep 6491933 = 2434475) B2434475
theorem B4327955 : Blo 1923435 4327955 := bstep (se 1 (by rfl) ⟨3245966, by rfl⟩ : syracuseStep 4327955 = 6491933) B6491933
theorem B2885303 : Blo 1923435 2885303 := bstep (se 1 (by rfl) ⟨2163977, by rfl⟩ : syracuseStep 2885303 = 4327955) B4327955
theorem B1923535 : Blo 1923435 1923535 := bstep (se 1 (by rfl) ⟨1442651, by rfl⟩ : syracuseStep 1923535 = 2885303) B2885303
theorem B2885309 : Blo 1923435 2885309 := bbase (se 3 (by rfl) ⟨540995, by rfl⟩ : syracuseStep 2885309 = 1081991) (by norm_num)
theorem B1923539 : Blo 1923435 1923539 := bstep (se 1 (by rfl) ⟨1442654, by rfl⟩ : syracuseStep 1923539 = 2885309) B2885309
theorem B4327973 : Blo 1923435 4327973 := bbase (se 4 (by rfl) ⟨405747, by rfl⟩ : syracuseStep 4327973 = 811495) (by norm_num)
theorem B2885315 : Blo 1923435 2885315 := bstep (se 1 (by rfl) ⟨2163986, by rfl⟩ : syracuseStep 2885315 = 4327973) B4327973
theorem B1923543 : Blo 1923435 1923543 := bstep (se 1 (by rfl) ⟨1442657, by rfl⟩ : syracuseStep 1923543 = 2885315) B2885315
theorem B4868981 : Blo 1923435 4868981 := bbase (se 5 (by rfl) ⟨228233, by rfl⟩ : syracuseStep 4868981 = 456467) (by norm_num)
theorem B3245987 : Blo 1923435 3245987 := bstep (se 1 (by rfl) ⟨2434490, by rfl⟩ : syracuseStep 3245987 = 4868981) B4868981
theorem B2163991 : Blo 1923435 2163991 := bstep (se 1 (by rfl) ⟨1622993, by rfl⟩ : syracuseStep 2163991 = 3245987) B3245987
theorem B2885321 : Blo 1923435 2885321 := bstep (se 2 (by rfl) ⟨1081995, by rfl⟩ : syracuseStep 2885321 = 2163991) B2163991
theorem B1923547 : Blo 1923435 1923547 := bstep (se 1 (by rfl) ⟨1442660, by rfl⟩ : syracuseStep 1923547 = 2885321) B2885321
theorem B9369589 : Blo 1923435 9369589 := bbase (se 5 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 9369589 = 878399) (by norm_num)
theorem B12492785 : Blo 1923435 12492785 := bstep (se 2 (by rfl) ⟨4684794, by rfl⟩ : syracuseStep 12492785 = 9369589) B9369589
theorem B33314093 : Blo 1923435 33314093 := bstep (se 3 (by rfl) ⟨6246392, by rfl⟩ : syracuseStep 33314093 = 12492785) B12492785
theorem B22209395 : Blo 1923435 22209395 := bstep (se 1 (by rfl) ⟨16657046, by rfl⟩ : syracuseStep 22209395 = 33314093) B33314093
theorem B236900213 : Blo 1923435 236900213 := bstep (se 5 (by rfl) ⟨11104697, by rfl⟩ : syracuseStep 236900213 = 22209395) B22209395
theorem B157933475 : Blo 1923435 157933475 := bstep (se 1 (by rfl) ⟨118450106, by rfl⟩ : syracuseStep 157933475 = 236900213) B236900213
theorem B105288983 : Blo 1923435 105288983 := bstep (se 1 (by rfl) ⟨78966737, by rfl⟩ : syracuseStep 105288983 = 157933475) B157933475
theorem B70192655 : Blo 1923435 70192655 := bstep (se 1 (by rfl) ⟨52644491, by rfl⟩ : syracuseStep 70192655 = 105288983) B105288983
theorem B46795103 : Blo 1923435 46795103 := bstep (se 1 (by rfl) ⟨35096327, by rfl⟩ : syracuseStep 46795103 = 70192655) B70192655
theorem B31196735 : Blo 1923435 31196735 := bstep (se 1 (by rfl) ⟨23397551, by rfl⟩ : syracuseStep 31196735 = 46795103) B46795103
theorem B20797823 : Blo 1923435 20797823 := bstep (se 1 (by rfl) ⟨15598367, by rfl⟩ : syracuseStep 20797823 = 31196735) B31196735
theorem B13865215 : Blo 1923435 13865215 := bstep (se 1 (by rfl) ⟨10398911, by rfl⟩ : syracuseStep 13865215 = 20797823) B20797823
theorem B18486953 : Blo 1923435 18486953 := bstep (se 2 (by rfl) ⟨6932607, by rfl⟩ : syracuseStep 18486953 = 13865215) B13865215
theorem B12324635 : Blo 1923435 12324635 := bstep (se 1 (by rfl) ⟨9243476, by rfl⟩ : syracuseStep 12324635 = 18486953) B18486953
theorem B8216423 : Blo 1923435 8216423 := bstep (se 1 (by rfl) ⟨6162317, by rfl⟩ : syracuseStep 8216423 = 12324635) B12324635
theorem B5477615 : Blo 1923435 5477615 := bstep (se 1 (by rfl) ⟨4108211, by rfl⟩ : syracuseStep 5477615 = 8216423) B8216423
theorem B3651743 : Blo 1923435 3651743 := bstep (se 1 (by rfl) ⟨2738807, by rfl⟩ : syracuseStep 3651743 = 5477615) B5477615
theorem B9737981 : Blo 1923435 9737981 := bstep (se 3 (by rfl) ⟨1825871, by rfl⟩ : syracuseStep 9737981 = 3651743) B3651743
theorem B6491987 : Blo 1923435 6491987 := bstep (se 1 (by rfl) ⟨4868990, by rfl⟩ : syracuseStep 6491987 = 9737981) B9737981
theorem B4327991 : Blo 1923435 4327991 := bstep (se 1 (by rfl) ⟨3245993, by rfl⟩ : syracuseStep 4327991 = 6491987) B6491987
theorem B2885327 : Blo 1923435 2885327 := bstep (se 1 (by rfl) ⟨2163995, by rfl⟩ : syracuseStep 2885327 = 4327991) B4327991
theorem B1923551 : Blo 1923435 1923551 := bstep (se 1 (by rfl) ⟨1442663, by rfl⟩ : syracuseStep 1923551 = 2885327) B2885327
theorem B2885333 : Blo 1923435 2885333 := bbase (se 7 (by rfl) ⟨33812, by rfl⟩ : syracuseStep 2885333 = 67625) (by norm_num)
theorem B1923555 : Blo 1923435 1923555 := bstep (se 1 (by rfl) ⟨1442666, by rfl⟩ : syracuseStep 1923555 = 2885333) B2885333
theorem B4108229 : Blo 1923435 4108229 := bbase (se 4 (by rfl) ⟨385146, by rfl⟩ : syracuseStep 4108229 = 770293) (by norm_num)
theorem B2738819 : Blo 1923435 2738819 := bstep (se 1 (by rfl) ⟨2054114, by rfl⟩ : syracuseStep 2738819 = 4108229) B4108229
theorem B7303517 : Blo 1923435 7303517 := bstep (se 3 (by rfl) ⟨1369409, by rfl⟩ : syracuseStep 7303517 = 2738819) B2738819
theorem B4869011 : Blo 1923435 4869011 := bstep (se 1 (by rfl) ⟨3651758, by rfl⟩ : syracuseStep 4869011 = 7303517) B7303517
theorem B3246007 : Blo 1923435 3246007 := bstep (se 1 (by rfl) ⟨2434505, by rfl⟩ : syracuseStep 3246007 = 4869011) B4869011
theorem B4328009 : Blo 1923435 4328009 := bstep (se 2 (by rfl) ⟨1623003, by rfl⟩ : syracuseStep 4328009 = 3246007) B3246007
theorem B2885339 : Blo 1923435 2885339 := bstep (se 1 (by rfl) ⟨2164004, by rfl⟩ : syracuseStep 2885339 = 4328009) B4328009
theorem B1923559 : Blo 1923435 1923559 := bstep (se 1 (by rfl) ⟨1442669, by rfl⟩ : syracuseStep 1923559 = 2885339) B2885339
theorem B2164009 : Blo 1923435 2164009 := bbase (se 2 (by rfl) ⟨811503, by rfl⟩ : syracuseStep 2164009 = 1623007) (by norm_num)
theorem B2885345 : Blo 1923435 2885345 := bstep (se 2 (by rfl) ⟨1082004, by rfl⟩ : syracuseStep 2885345 = 2164009) B2164009
theorem B1923563 : Blo 1923435 1923563 := bstep (se 1 (by rfl) ⟨1442672, by rfl⟩ : syracuseStep 1923563 = 2885345) B2885345
theorem B3290309 : Blo 1923435 3290309 := bbase (se 4 (by rfl) ⟨308466, by rfl⟩ : syracuseStep 3290309 = 616933) (by norm_num)
theorem B2193539 : Blo 1923435 2193539 := bstep (se 1 (by rfl) ⟨1645154, by rfl⟩ : syracuseStep 2193539 = 3290309) B3290309
theorem B5849437 : Blo 1923435 5849437 := bstep (se 3 (by rfl) ⟨1096769, by rfl⟩ : syracuseStep 5849437 = 2193539) B2193539
theorem B7799249 : Blo 1923435 7799249 := bstep (se 2 (by rfl) ⟨2924718, by rfl⟩ : syracuseStep 7799249 = 5849437) B5849437
theorem B5199499 : Blo 1923435 5199499 := bstep (se 1 (by rfl) ⟨3899624, by rfl⟩ : syracuseStep 5199499 = 7799249) B7799249
theorem B6932665 : Blo 1923435 6932665 := bstep (se 2 (by rfl) ⟨2599749, by rfl⟩ : syracuseStep 6932665 = 5199499) B5199499
theorem B9243553 : Blo 1923435 9243553 := bstep (se 2 (by rfl) ⟨3466332, by rfl⟩ : syracuseStep 9243553 = 6932665) B6932665
theorem B12324737 : Blo 1923435 12324737 := bstep (se 2 (by rfl) ⟨4621776, by rfl⟩ : syracuseStep 12324737 = 9243553) B9243553
theorem B8216491 : Blo 1923435 8216491 := bstep (se 1 (by rfl) ⟨6162368, by rfl⟩ : syracuseStep 8216491 = 12324737) B12324737
theorem B10955321 : Blo 1923435 10955321 := bstep (se 2 (by rfl) ⟨4108245, by rfl⟩ : syracuseStep 10955321 = 8216491) B8216491
theorem B7303547 : Blo 1923435 7303547 := bstep (se 1 (by rfl) ⟨5477660, by rfl⟩ : syracuseStep 7303547 = 10955321) B10955321
theorem B4869031 : Blo 1923435 4869031 := bstep (se 1 (by rfl) ⟨3651773, by rfl⟩ : syracuseStep 4869031 = 7303547) B7303547
theorem B6492041 : Blo 1923435 6492041 := bstep (se 2 (by rfl) ⟨2434515, by rfl⟩ : syracuseStep 6492041 = 4869031) B4869031
theorem B4328027 : Blo 1923435 4328027 := bstep (se 1 (by rfl) ⟨3246020, by rfl⟩ : syracuseStep 4328027 = 6492041) B6492041
theorem B2885351 : Blo 1923435 2885351 := bstep (se 1 (by rfl) ⟨2164013, by rfl⟩ : syracuseStep 2885351 = 4328027) B4328027
theorem B1923567 : Blo 1923435 1923567 := bstep (se 1 (by rfl) ⟨1442675, by rfl⟩ : syracuseStep 1923567 = 2885351) B2885351
theorem B2885357 : Blo 1923435 2885357 := bbase (se 3 (by rfl) ⟨541004, by rfl⟩ : syracuseStep 2885357 = 1082009) (by norm_num)
theorem B1923571 : Blo 1923435 1923571 := bstep (se 1 (by rfl) ⟨1442678, by rfl⟩ : syracuseStep 1923571 = 2885357) B2885357
theorem B4328045 : Blo 1923435 4328045 := bbase (se 3 (by rfl) ⟨811508, by rfl⟩ : syracuseStep 4328045 = 1623017) (by norm_num)
theorem B2885363 : Blo 1923435 2885363 := bstep (se 1 (by rfl) ⟨2164022, by rfl⟩ : syracuseStep 2885363 = 4328045) B4328045
theorem B1923575 : Blo 1923435 1923575 := bstep (se 1 (by rfl) ⟨1442681, by rfl⟩ : syracuseStep 1923575 = 2885363) B2885363
theorem B3651797 : Blo 1923435 3651797 := bbase (se 7 (by rfl) ⟨42794, by rfl⟩ : syracuseStep 3651797 = 85589) (by norm_num)
theorem B2434531 : Blo 1923435 2434531 := bstep (se 1 (by rfl) ⟨1825898, by rfl⟩ : syracuseStep 2434531 = 3651797) B3651797
theorem B3246041 : Blo 1923435 3246041 := bstep (se 2 (by rfl) ⟨1217265, by rfl⟩ : syracuseStep 3246041 = 2434531) B2434531
theorem B2164027 : Blo 1923435 2164027 := bstep (se 1 (by rfl) ⟨1623020, by rfl⟩ : syracuseStep 2164027 = 3246041) B3246041
theorem B2885369 : Blo 1923435 2885369 := bstep (se 2 (by rfl) ⟨1082013, by rfl⟩ : syracuseStep 2885369 = 2164027) B2164027
theorem B1923579 : Blo 1923435 1923579 := bstep (se 1 (by rfl) ⟨1442684, by rfl⟩ : syracuseStep 1923579 = 2885369) B2885369
theorem B20798165 : Blo 1923435 20798165 := bbase (se 7 (by rfl) ⟨243728, by rfl⟩ : syracuseStep 20798165 = 487457) (by norm_num)
theorem B55461773 : Blo 1923435 55461773 := bstep (se 3 (by rfl) ⟨10399082, by rfl⟩ : syracuseStep 55461773 = 20798165) B20798165
theorem B36974515 : Blo 1923435 36974515 := bstep (se 1 (by rfl) ⟨27730886, by rfl⟩ : syracuseStep 36974515 = 55461773) B55461773
theorem B49299353 : Blo 1923435 49299353 := bstep (se 2 (by rfl) ⟨18487257, by rfl⟩ : syracuseStep 49299353 = 36974515) B36974515
theorem B32866235 : Blo 1923435 32866235 := bstep (se 1 (by rfl) ⟨24649676, by rfl⟩ : syracuseStep 32866235 = 49299353) B49299353
theorem B21910823 : Blo 1923435 21910823 := bstep (se 1 (by rfl) ⟨16433117, by rfl⟩ : syracuseStep 21910823 = 32866235) B32866235
theorem B14607215 : Blo 1923435 14607215 := bstep (se 1 (by rfl) ⟨10955411, by rfl⟩ : syracuseStep 14607215 = 21910823) B21910823
theorem B9738143 : Blo 1923435 9738143 := bstep (se 1 (by rfl) ⟨7303607, by rfl⟩ : syracuseStep 9738143 = 14607215) B14607215
theorem B6492095 : Blo 1923435 6492095 := bstep (se 1 (by rfl) ⟨4869071, by rfl⟩ : syracuseStep 6492095 = 9738143) B9738143
theorem B4328063 : Blo 1923435 4328063 := bstep (se 1 (by rfl) ⟨3246047, by rfl⟩ : syracuseStep 4328063 = 6492095) B6492095
theorem B2885375 : Blo 1923435 2885375 := bstep (se 1 (by rfl) ⟨2164031, by rfl⟩ : syracuseStep 2885375 = 4328063) B4328063
theorem B1923583 : Blo 1923435 1923583 := bstep (se 1 (by rfl) ⟨1442687, by rfl⟩ : syracuseStep 1923583 = 2885375) B2885375
theorem B2885381 : Blo 1923435 2885381 := bbase (se 4 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 2885381 = 541009) (by norm_num)
theorem B1923587 : Blo 1923435 1923587 := bstep (se 1 (by rfl) ⟨1442690, by rfl⟩ : syracuseStep 1923587 = 2885381) B2885381
theorem B3246061 : Blo 1923435 3246061 := bbase (se 3 (by rfl) ⟨608636, by rfl⟩ : syracuseStep 3246061 = 1217273) (by norm_num)
theorem B4328081 : Blo 1923435 4328081 := bstep (se 2 (by rfl) ⟨1623030, by rfl⟩ : syracuseStep 4328081 = 3246061) B3246061
theorem B2885387 : Blo 1923435 2885387 := bstep (se 1 (by rfl) ⟨2164040, by rfl⟩ : syracuseStep 2885387 = 4328081) B4328081
theorem B1923591 : Blo 1923435 1923591 := bstep (se 1 (by rfl) ⟨1442693, by rfl⟩ : syracuseStep 1923591 = 2885387) B2885387
theorem B2164045 : Blo 1923435 2164045 := bbase (se 3 (by rfl) ⟨405758, by rfl⟩ : syracuseStep 2164045 = 811517) (by norm_num)
theorem B2885393 : Blo 1923435 2885393 := bstep (se 2 (by rfl) ⟨1082022, by rfl⟩ : syracuseStep 2885393 = 2164045) B2164045
theorem B1923595 : Blo 1923435 1923595 := bstep (se 1 (by rfl) ⟨1442696, by rfl⟩ : syracuseStep 1923595 = 2885393) B2885393
theorem B6492149 : Blo 1923435 6492149 := bbase (se 5 (by rfl) ⟨304319, by rfl⟩ : syracuseStep 6492149 = 608639) (by norm_num)
theorem B4328099 : Blo 1923435 4328099 := bstep (se 1 (by rfl) ⟨3246074, by rfl⟩ : syracuseStep 4328099 = 6492149) B6492149
theorem B2885399 : Blo 1923435 2885399 := bstep (se 1 (by rfl) ⟨2164049, by rfl⟩ : syracuseStep 2885399 = 4328099) B4328099
theorem B1923599 : Blo 1923435 1923599 := bstep (se 1 (by rfl) ⟨1442699, by rfl⟩ : syracuseStep 1923599 = 2885399) B2885399
theorem B2885405 : Blo 1923435 2885405 := bbase (se 3 (by rfl) ⟨541013, by rfl⟩ : syracuseStep 2885405 = 1082027) (by norm_num)
theorem B1923603 : Blo 1923435 1923603 := bstep (se 1 (by rfl) ⟨1442702, by rfl⟩ : syracuseStep 1923603 = 2885405) B2885405
theorem B4328117 : Blo 1923435 4328117 := bbase (se 5 (by rfl) ⟨202880, by rfl⟩ : syracuseStep 4328117 = 405761) (by norm_num)
theorem B2885411 : Blo 1923435 2885411 := bstep (se 1 (by rfl) ⟨2164058, by rfl⟩ : syracuseStep 2885411 = 4328117) B4328117
theorem B1923607 : Blo 1923435 1923607 := bstep (se 1 (by rfl) ⟨1442705, by rfl⟩ : syracuseStep 1923607 = 2885411) B2885411
theorem B10955573 : Blo 1923435 10955573 := bbase (se 5 (by rfl) ⟨513542, by rfl⟩ : syracuseStep 10955573 = 1027085) (by norm_num)
theorem B7303715 : Blo 1923435 7303715 := bstep (se 1 (by rfl) ⟨5477786, by rfl⟩ : syracuseStep 7303715 = 10955573) B10955573
theorem B4869143 : Blo 1923435 4869143 := bstep (se 1 (by rfl) ⟨3651857, by rfl⟩ : syracuseStep 4869143 = 7303715) B7303715
theorem B3246095 : Blo 1923435 3246095 := bstep (se 1 (by rfl) ⟨2434571, by rfl⟩ : syracuseStep 3246095 = 4869143) B4869143
theorem B2164063 : Blo 1923435 2164063 := bstep (se 1 (by rfl) ⟨1623047, by rfl⟩ : syracuseStep 2164063 = 3246095) B3246095
theorem B2885417 : Blo 1923435 2885417 := bstep (se 2 (by rfl) ⟨1082031, by rfl⟩ : syracuseStep 2885417 = 2164063) B2164063
theorem B1923611 : Blo 1923435 1923611 := bstep (se 1 (by rfl) ⟨1442708, by rfl⟩ : syracuseStep 1923611 = 2885417) B2885417
theorem B5477797 : Blo 1923435 5477797 := bbase (se 4 (by rfl) ⟨513543, by rfl⟩ : syracuseStep 5477797 = 1027087) (by norm_num)
theorem B7303729 : Blo 1923435 7303729 := bstep (se 2 (by rfl) ⟨2738898, by rfl⟩ : syracuseStep 7303729 = 5477797) B5477797
theorem B9738305 : Blo 1923435 9738305 := bstep (se 2 (by rfl) ⟨3651864, by rfl⟩ : syracuseStep 9738305 = 7303729) B7303729
theorem B6492203 : Blo 1923435 6492203 := bstep (se 1 (by rfl) ⟨4869152, by rfl⟩ : syracuseStep 6492203 = 9738305) B9738305
theorem B4328135 : Blo 1923435 4328135 := bstep (se 1 (by rfl) ⟨3246101, by rfl⟩ : syracuseStep 4328135 = 6492203) B6492203
theorem B2885423 : Blo 1923435 2885423 := bstep (se 1 (by rfl) ⟨2164067, by rfl⟩ : syracuseStep 2885423 = 4328135) B4328135
theorem B1923615 : Blo 1923435 1923615 := bstep (se 1 (by rfl) ⟨1442711, by rfl⟩ : syracuseStep 1923615 = 2885423) B2885423
theorem B2885429 : Blo 1923435 2885429 := bbase (se 5 (by rfl) ⟨135254, by rfl⟩ : syracuseStep 2885429 = 270509) (by norm_num)
theorem B1923619 : Blo 1923435 1923619 := bstep (se 1 (by rfl) ⟨1442714, by rfl⟩ : syracuseStep 1923619 = 2885429) B2885429
theorem B4869173 : Blo 1923435 4869173 := bbase (se 5 (by rfl) ⟨228242, by rfl⟩ : syracuseStep 4869173 = 456485) (by norm_num)
theorem B3246115 : Blo 1923435 3246115 := bstep (se 1 (by rfl) ⟨2434586, by rfl⟩ : syracuseStep 3246115 = 4869173) B4869173
theorem B4328153 : Blo 1923435 4328153 := bstep (se 2 (by rfl) ⟨1623057, by rfl⟩ : syracuseStep 4328153 = 3246115) B3246115
theorem B2885435 : Blo 1923435 2885435 := bstep (se 1 (by rfl) ⟨2164076, by rfl⟩ : syracuseStep 2885435 = 4328153) B4328153
theorem B1923623 : Blo 1923435 1923623 := bstep (se 1 (by rfl) ⟨1442717, by rfl⟩ : syracuseStep 1923623 = 2885435) B2885435
theorem B2164081 : Blo 1923435 2164081 := bbase (se 2 (by rfl) ⟨811530, by rfl⟩ : syracuseStep 2164081 = 1623061) (by norm_num)
theorem B2885441 : Blo 1923435 2885441 := bstep (se 2 (by rfl) ⟨1082040, by rfl⟩ : syracuseStep 2885441 = 2164081) B2164081
theorem B1923627 : Blo 1923435 1923627 := bstep (se 1 (by rfl) ⟨1442720, by rfl⟩ : syracuseStep 1923627 = 2885441) B2885441
theorem B4935629 : Blo 1923435 4935629 := bbase (se 3 (by rfl) ⟨925430, by rfl⟩ : syracuseStep 4935629 = 1850861) (by norm_num)
theorem B3290419 : Blo 1923435 3290419 := bstep (se 1 (by rfl) ⟨2467814, by rfl⟩ : syracuseStep 3290419 = 4935629) B4935629
theorem B4387225 : Blo 1923435 4387225 := bstep (se 2 (by rfl) ⟨1645209, by rfl⟩ : syracuseStep 4387225 = 3290419) B3290419
theorem B5849633 : Blo 1923435 5849633 := bstep (se 2 (by rfl) ⟨2193612, by rfl⟩ : syracuseStep 5849633 = 4387225) B4387225
theorem B3899755 : Blo 1923435 3899755 := bstep (se 1 (by rfl) ⟨2924816, by rfl⟩ : syracuseStep 3899755 = 5849633) B5849633
theorem B5199673 : Blo 1923435 5199673 := bstep (se 2 (by rfl) ⟨1949877, by rfl⟩ : syracuseStep 5199673 = 3899755) B3899755
theorem B6932897 : Blo 1923435 6932897 := bstep (se 2 (by rfl) ⟨2599836, by rfl⟩ : syracuseStep 6932897 = 5199673) B5199673
theorem B4621931 : Blo 1923435 4621931 := bstep (se 1 (by rfl) ⟨3466448, by rfl⟩ : syracuseStep 4621931 = 6932897) B6932897
theorem B3081287 : Blo 1923435 3081287 := bstep (se 1 (by rfl) ⟨2310965, by rfl⟩ : syracuseStep 3081287 = 4621931) B4621931
theorem B8216765 : Blo 1923435 8216765 := bstep (se 3 (by rfl) ⟨1540643, by rfl⟩ : syracuseStep 8216765 = 3081287) B3081287
theorem B5477843 : Blo 1923435 5477843 := bstep (se 1 (by rfl) ⟨4108382, by rfl⟩ : syracuseStep 5477843 = 8216765) B8216765
theorem B3651895 : Blo 1923435 3651895 := bstep (se 1 (by rfl) ⟨2738921, by rfl⟩ : syracuseStep 3651895 = 5477843) B5477843
theorem B4869193 : Blo 1923435 4869193 := bstep (se 2 (by rfl) ⟨1825947, by rfl⟩ : syracuseStep 4869193 = 3651895) B3651895
theorem B6492257 : Blo 1923435 6492257 := bstep (se 2 (by rfl) ⟨2434596, by rfl⟩ : syracuseStep 6492257 = 4869193) B4869193
theorem B4328171 : Blo 1923435 4328171 := bstep (se 1 (by rfl) ⟨3246128, by rfl⟩ : syracuseStep 4328171 = 6492257) B6492257
theorem B2885447 : Blo 1923435 2885447 := bstep (se 1 (by rfl) ⟨2164085, by rfl⟩ : syracuseStep 2885447 = 4328171) B4328171
theorem B1923631 : Blo 1923435 1923631 := bstep (se 1 (by rfl) ⟨1442723, by rfl⟩ : syracuseStep 1923631 = 2885447) B2885447
theorem B2885453 : Blo 1923435 2885453 := bbase (se 3 (by rfl) ⟨541022, by rfl⟩ : syracuseStep 2885453 = 1082045) (by norm_num)
theorem B1923635 : Blo 1923435 1923635 := bstep (se 1 (by rfl) ⟨1442726, by rfl⟩ : syracuseStep 1923635 = 2885453) B2885453
theorem B4328189 : Blo 1923435 4328189 := bbase (se 3 (by rfl) ⟨811535, by rfl⟩ : syracuseStep 4328189 = 1623071) (by norm_num)
theorem B2885459 : Blo 1923435 2885459 := bstep (se 1 (by rfl) ⟨2164094, by rfl⟩ : syracuseStep 2885459 = 4328189) B4328189
theorem B1923639 : Blo 1923435 1923639 := bstep (se 1 (by rfl) ⟨1442729, by rfl⟩ : syracuseStep 1923639 = 2885459) B2885459
theorem B3246149 : Blo 1923435 3246149 := bbase (se 4 (by rfl) ⟨304326, by rfl⟩ : syracuseStep 3246149 = 608653) (by norm_num)
theorem B2164099 : Blo 1923435 2164099 := bstep (se 1 (by rfl) ⟨1623074, by rfl⟩ : syracuseStep 2164099 = 3246149) B3246149
theorem B2885465 : Blo 1923435 2885465 := bstep (se 2 (by rfl) ⟨1082049, by rfl⟩ : syracuseStep 2885465 = 2164099) B2164099
theorem B1923643 : Blo 1923435 1923643 := bstep (se 1 (by rfl) ⟨1442732, by rfl⟩ : syracuseStep 1923643 = 2885465) B2885465
theorem B14607701 : Blo 1923435 14607701 := bbase (se 12 (by rfl) ⟨5349, by rfl⟩ : syracuseStep 14607701 = 10699) (by norm_num)
theorem B9738467 : Blo 1923435 9738467 := bstep (se 1 (by rfl) ⟨7303850, by rfl⟩ : syracuseStep 9738467 = 14607701) B14607701
theorem B6492311 : Blo 1923435 6492311 := bstep (se 1 (by rfl) ⟨4869233, by rfl⟩ : syracuseStep 6492311 = 9738467) B9738467
theorem B4328207 : Blo 1923435 4328207 := bstep (se 1 (by rfl) ⟨3246155, by rfl⟩ : syracuseStep 4328207 = 6492311) B6492311
theorem B2885471 : Blo 1923435 2885471 := bstep (se 1 (by rfl) ⟨2164103, by rfl⟩ : syracuseStep 2885471 = 4328207) B4328207
theorem B1923647 : Blo 1923435 1923647 := bstep (se 1 (by rfl) ⟨1442735, by rfl⟩ : syracuseStep 1923647 = 2885471) B2885471
theorem B2885477 : Blo 1923435 2885477 := bbase (se 4 (by rfl) ⟨270513, by rfl⟩ : syracuseStep 2885477 = 541027) (by norm_num)
theorem B1923651 : Blo 1923435 1923651 := bstep (se 1 (by rfl) ⟨1442738, by rfl⟩ : syracuseStep 1923651 = 2885477) B2885477
theorem B3651941 : Blo 1923435 3651941 := bbase (se 4 (by rfl) ⟨342369, by rfl⟩ : syracuseStep 3651941 = 684739) (by norm_num)
theorem B2434627 : Blo 1923435 2434627 := bstep (se 1 (by rfl) ⟨1825970, by rfl⟩ : syracuseStep 2434627 = 3651941) B3651941
theorem B3246169 : Blo 1923435 3246169 := bstep (se 2 (by rfl) ⟨1217313, by rfl⟩ : syracuseStep 3246169 = 2434627) B2434627
theorem B4328225 : Blo 1923435 4328225 := bstep (se 2 (by rfl) ⟨1623084, by rfl⟩ : syracuseStep 4328225 = 3246169) B3246169
theorem B2885483 : Blo 1923435 2885483 := bstep (se 1 (by rfl) ⟨2164112, by rfl⟩ : syracuseStep 2885483 = 4328225) B4328225
theorem B1923655 : Blo 1923435 1923655 := bstep (se 1 (by rfl) ⟨1442741, by rfl⟩ : syracuseStep 1923655 = 2885483) B2885483
theorem B2164117 : Blo 1923435 2164117 := bbase (se 6 (by rfl) ⟨50721, by rfl⟩ : syracuseStep 2164117 = 101443) (by norm_num)
theorem B2885489 : Blo 1923435 2885489 := bstep (se 2 (by rfl) ⟨1082058, by rfl⟩ : syracuseStep 2885489 = 2164117) B2164117
theorem B1923659 : Blo 1923435 1923659 := bstep (se 1 (by rfl) ⟨1442744, by rfl⟩ : syracuseStep 1923659 = 2885489) B2885489
theorem B2434637 : Blo 1923435 2434637 := bbase (se 3 (by rfl) ⟨456494, by rfl⟩ : syracuseStep 2434637 = 912989) (by norm_num)
theorem B6492365 : Blo 1923435 6492365 := bstep (se 3 (by rfl) ⟨1217318, by rfl⟩ : syracuseStep 6492365 = 2434637) B2434637
theorem B4328243 : Blo 1923435 4328243 := bstep (se 1 (by rfl) ⟨3246182, by rfl⟩ : syracuseStep 4328243 = 6492365) B6492365
theorem B2885495 : Blo 1923435 2885495 := bstep (se 1 (by rfl) ⟨2164121, by rfl⟩ : syracuseStep 2885495 = 4328243) B4328243
theorem B1923663 : Blo 1923435 1923663 := bstep (se 1 (by rfl) ⟨1442747, by rfl⟩ : syracuseStep 1923663 = 2885495) B2885495
theorem B2885501 : Blo 1923435 2885501 := bbase (se 3 (by rfl) ⟨541031, by rfl⟩ : syracuseStep 2885501 = 1082063) (by norm_num)
theorem B1923667 : Blo 1923435 1923667 := bstep (se 1 (by rfl) ⟨1442750, by rfl⟩ : syracuseStep 1923667 = 2885501) B2885501
theorem B4328261 : Blo 1923435 4328261 := bbase (se 4 (by rfl) ⟨405774, by rfl⟩ : syracuseStep 4328261 = 811549) (by norm_num)
theorem B2885507 : Blo 1923435 2885507 := bstep (se 1 (by rfl) ⟨2164130, by rfl⟩ : syracuseStep 2885507 = 4328261) B4328261
theorem B1923671 : Blo 1923435 1923671 := bstep (se 1 (by rfl) ⟨1442753, by rfl⟩ : syracuseStep 1923671 = 2885507) B2885507
theorem B4108477 : Blo 1923435 4108477 := bbase (se 3 (by rfl) ⟨770339, by rfl⟩ : syracuseStep 4108477 = 1540679) (by norm_num)
theorem B5477969 : Blo 1923435 5477969 := bstep (se 2 (by rfl) ⟨2054238, by rfl⟩ : syracuseStep 5477969 = 4108477) B4108477
theorem B3651979 : Blo 1923435 3651979 := bstep (se 1 (by rfl) ⟨2738984, by rfl⟩ : syracuseStep 3651979 = 5477969) B5477969
theorem B4869305 : Blo 1923435 4869305 := bstep (se 2 (by rfl) ⟨1825989, by rfl⟩ : syracuseStep 4869305 = 3651979) B3651979
theorem B3246203 : Blo 1923435 3246203 := bstep (se 1 (by rfl) ⟨2434652, by rfl⟩ : syracuseStep 3246203 = 4869305) B4869305
theorem B2164135 : Blo 1923435 2164135 := bstep (se 1 (by rfl) ⟨1623101, by rfl⟩ : syracuseStep 2164135 = 3246203) B3246203
theorem B2885513 : Blo 1923435 2885513 := bstep (se 2 (by rfl) ⟨1082067, by rfl⟩ : syracuseStep 2885513 = 2164135) B2164135
theorem B1923675 : Blo 1923435 1923675 := bstep (se 1 (by rfl) ⟨1442756, by rfl⟩ : syracuseStep 1923675 = 2885513) B2885513
theorem B9738629 : Blo 1923435 9738629 := bbase (se 4 (by rfl) ⟨912996, by rfl⟩ : syracuseStep 9738629 = 1825993) (by norm_num)
theorem B6492419 : Blo 1923435 6492419 := bstep (se 1 (by rfl) ⟨4869314, by rfl⟩ : syracuseStep 6492419 = 9738629) B9738629
theorem B4328279 : Blo 1923435 4328279 := bstep (se 1 (by rfl) ⟨3246209, by rfl⟩ : syracuseStep 4328279 = 6492419) B6492419
theorem B2885519 : Blo 1923435 2885519 := bstep (se 1 (by rfl) ⟨2164139, by rfl⟩ : syracuseStep 2885519 = 4328279) B4328279
theorem B1923679 : Blo 1923435 1923679 := bstep (se 1 (by rfl) ⟨1442759, by rfl⟩ : syracuseStep 1923679 = 2885519) B2885519
theorem B2885525 : Blo 1923435 2885525 := bbase (se 6 (by rfl) ⟨67629, by rfl⟩ : syracuseStep 2885525 = 135259) (by norm_num)
theorem B1923683 : Blo 1923435 1923683 := bstep (se 1 (by rfl) ⟨1442762, by rfl⟩ : syracuseStep 1923683 = 2885525) B2885525
theorem B2311033 : Blo 1923435 2311033 := bbase (se 2 (by rfl) ⟨866637, by rfl⟩ : syracuseStep 2311033 = 1733275) (by norm_num)
theorem B3081377 : Blo 1923435 3081377 := bstep (se 2 (by rfl) ⟨1155516, by rfl⟩ : syracuseStep 3081377 = 2311033) B2311033
theorem B2054251 : Blo 1923435 2054251 := bstep (se 1 (by rfl) ⟨1540688, by rfl⟩ : syracuseStep 2054251 = 3081377) B3081377
theorem B10956005 : Blo 1923435 10956005 := bstep (se 4 (by rfl) ⟨1027125, by rfl⟩ : syracuseStep 10956005 = 2054251) B2054251
theorem B7304003 : Blo 1923435 7304003 := bstep (se 1 (by rfl) ⟨5478002, by rfl⟩ : syracuseStep 7304003 = 10956005) B10956005
theorem B4869335 : Blo 1923435 4869335 := bstep (se 1 (by rfl) ⟨3652001, by rfl⟩ : syracuseStep 4869335 = 7304003) B7304003
theorem B3246223 : Blo 1923435 3246223 := bstep (se 1 (by rfl) ⟨2434667, by rfl⟩ : syracuseStep 3246223 = 4869335) B4869335
theorem B4328297 : Blo 1923435 4328297 := bstep (se 2 (by rfl) ⟨1623111, by rfl⟩ : syracuseStep 4328297 = 3246223) B3246223
theorem B2885531 : Blo 1923435 2885531 := bstep (se 1 (by rfl) ⟨2164148, by rfl⟩ : syracuseStep 2885531 = 4328297) B4328297
theorem B1923687 : Blo 1923435 1923687 := bstep (se 1 (by rfl) ⟨1442765, by rfl⟩ : syracuseStep 1923687 = 2885531) B2885531
theorem B2164153 : Blo 1923435 2164153 := bbase (se 2 (by rfl) ⟨811557, by rfl⟩ : syracuseStep 2164153 = 1623115) (by norm_num)
theorem B2885537 : Blo 1923435 2885537 := bstep (se 2 (by rfl) ⟨1082076, by rfl⟩ : syracuseStep 2885537 = 2164153) B2164153
theorem B1923691 : Blo 1923435 1923691 := bstep (se 1 (by rfl) ⟨1442768, by rfl⟩ : syracuseStep 1923691 = 2885537) B2885537
theorem B2193685 : Blo 1923435 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B11699653 : Blo 1923435 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B15599537 : Blo 1923435 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B10399691 : Blo 1923435 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B6933127 : Blo 1923435 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B9244169 : Blo 1923435 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B6162779 : Blo 1923435 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B4108519 : Blo 1923435 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B5478025 : Blo 1923435 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B7304033 : Blo 1923435 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B4869355 : Blo 1923435 4869355 := bstep (se 1 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 4869355 = 7304033) B7304033
theorem B6492473 : Blo 1923435 6492473 := bstep (se 2 (by rfl) ⟨2434677, by rfl⟩ : syracuseStep 6492473 = 4869355) B4869355
theorem B4328315 : Blo 1923435 4328315 := bstep (se 1 (by rfl) ⟨3246236, by rfl⟩ : syracuseStep 4328315 = 6492473) B6492473
theorem B2885543 : Blo 1923435 2885543 := bstep (se 1 (by rfl) ⟨2164157, by rfl⟩ : syracuseStep 2885543 = 4328315) B4328315
theorem B1923695 : Blo 1923435 1923695 := bstep (se 1 (by rfl) ⟨1442771, by rfl⟩ : syracuseStep 1923695 = 2885543) B2885543
theorem B2885549 : Blo 1923435 2885549 := bbase (se 3 (by rfl) ⟨541040, by rfl⟩ : syracuseStep 2885549 = 1082081) (by norm_num)
theorem B1923699 : Blo 1923435 1923699 := bstep (se 1 (by rfl) ⟨1442774, by rfl⟩ : syracuseStep 1923699 = 2885549) B2885549
theorem B4328333 : Blo 1923435 4328333 := bbase (se 3 (by rfl) ⟨811562, by rfl⟩ : syracuseStep 4328333 = 1623125) (by norm_num)
theorem B2885555 : Blo 1923435 2885555 := bstep (se 1 (by rfl) ⟨2164166, by rfl⟩ : syracuseStep 2885555 = 4328333) B4328333
theorem B1923703 : Blo 1923435 1923703 := bstep (se 1 (by rfl) ⟨1442777, by rfl⟩ : syracuseStep 1923703 = 2885555) B2885555
theorem B2434693 : Blo 1923435 2434693 := bbase (se 4 (by rfl) ⟨228252, by rfl⟩ : syracuseStep 2434693 = 456505) (by norm_num)
theorem B3246257 : Blo 1923435 3246257 := bstep (se 2 (by rfl) ⟨1217346, by rfl⟩ : syracuseStep 3246257 = 2434693) B2434693
theorem B2164171 : Blo 1923435 2164171 := bstep (se 1 (by rfl) ⟨1623128, by rfl⟩ : syracuseStep 2164171 = 3246257) B3246257
theorem B2885561 : Blo 1923435 2885561 := bstep (se 2 (by rfl) ⟨1082085, by rfl⟩ : syracuseStep 2885561 = 2164171) B2164171
theorem B1923707 : Blo 1923435 1923707 := bstep (se 1 (by rfl) ⟨1442780, by rfl⟩ : syracuseStep 1923707 = 2885561) B2885561
theorem B2311061 : Blo 1923435 2311061 := bbase (se 6 (by rfl) ⟨54165, by rfl⟩ : syracuseStep 2311061 = 108331) (by norm_num)
theorem B24651317 : Blo 1923435 24651317 := bstep (se 5 (by rfl) ⟨1155530, by rfl⟩ : syracuseStep 24651317 = 2311061) B2311061
theorem B16434211 : Blo 1923435 16434211 := bstep (se 1 (by rfl) ⟨12325658, by rfl⟩ : syracuseStep 16434211 = 24651317) B24651317
theorem B21912281 : Blo 1923435 21912281 := bstep (se 2 (by rfl) ⟨8217105, by rfl⟩ : syracuseStep 21912281 = 16434211) B16434211
theorem B14608187 : Blo 1923435 14608187 := bstep (se 1 (by rfl) ⟨10956140, by rfl⟩ : syracuseStep 14608187 = 21912281) B21912281
theorem B9738791 : Blo 1923435 9738791 := bstep (se 1 (by rfl) ⟨7304093, by rfl⟩ : syracuseStep 9738791 = 14608187) B14608187
theorem B6492527 : Blo 1923435 6492527 := bstep (se 1 (by rfl) ⟨4869395, by rfl⟩ : syracuseStep 6492527 = 9738791) B9738791
theorem B4328351 : Blo 1923435 4328351 := bstep (se 1 (by rfl) ⟨3246263, by rfl⟩ : syracuseStep 4328351 = 6492527) B6492527
theorem B2885567 : Blo 1923435 2885567 := bstep (se 1 (by rfl) ⟨2164175, by rfl⟩ : syracuseStep 2885567 = 4328351) B4328351
theorem B1923711 : Blo 1923435 1923711 := bstep (se 1 (by rfl) ⟨1442783, by rfl⟩ : syracuseStep 1923711 = 2885567) B2885567
theorem B2885573 : Blo 1923435 2885573 := bbase (se 4 (by rfl) ⟨270522, by rfl⟩ : syracuseStep 2885573 = 541045) (by norm_num)
theorem B1923715 : Blo 1923435 1923715 := bstep (se 1 (by rfl) ⟨1442786, by rfl⟩ : syracuseStep 1923715 = 2885573) B2885573
theorem B3246277 : Blo 1923435 3246277 := bbase (se 4 (by rfl) ⟨304338, by rfl⟩ : syracuseStep 3246277 = 608677) (by norm_num)
theorem B4328369 : Blo 1923435 4328369 := bstep (se 2 (by rfl) ⟨1623138, by rfl⟩ : syracuseStep 4328369 = 3246277) B3246277
theorem B2885579 : Blo 1923435 2885579 := bstep (se 1 (by rfl) ⟨2164184, by rfl⟩ : syracuseStep 2885579 = 4328369) B4328369
theorem B1923719 : Blo 1923435 1923719 := bstep (se 1 (by rfl) ⟨1442789, by rfl⟩ : syracuseStep 1923719 = 2885579) B2885579
theorem B2164189 : Blo 1923435 2164189 := bbase (se 3 (by rfl) ⟨405785, by rfl⟩ : syracuseStep 2164189 = 811571) (by norm_num)
theorem B2885585 : Blo 1923435 2885585 := bstep (se 2 (by rfl) ⟨1082094, by rfl⟩ : syracuseStep 2885585 = 2164189) B2164189
theorem B1923723 : Blo 1923435 1923723 := bstep (se 1 (by rfl) ⟨1442792, by rfl⟩ : syracuseStep 1923723 = 2885585) B2885585
theorem B6492581 : Blo 1923435 6492581 := bbase (se 4 (by rfl) ⟨608679, by rfl⟩ : syracuseStep 6492581 = 1217359) (by norm_num)
theorem B4328387 : Blo 1923435 4328387 := bstep (se 1 (by rfl) ⟨3246290, by rfl⟩ : syracuseStep 4328387 = 6492581) B6492581
theorem B2885591 : Blo 1923435 2885591 := bstep (se 1 (by rfl) ⟨2164193, by rfl⟩ : syracuseStep 2885591 = 4328387) B4328387
theorem B1923727 : Blo 1923435 1923727 := bstep (se 1 (by rfl) ⟨1442795, by rfl⟩ : syracuseStep 1923727 = 2885591) B2885591
theorem B2885597 : Blo 1923435 2885597 := bbase (se 3 (by rfl) ⟨541049, by rfl⟩ : syracuseStep 2885597 = 1082099) (by norm_num)
theorem B1923731 : Blo 1923435 1923731 := bstep (se 1 (by rfl) ⟨1442798, by rfl⟩ : syracuseStep 1923731 = 2885597) B2885597
theorem B4328405 : Blo 1923435 4328405 := bbase (se 7 (by rfl) ⟨50723, by rfl⟩ : syracuseStep 4328405 = 101447) (by norm_num)
theorem B2885603 : Blo 1923435 2885603 := bstep (se 1 (by rfl) ⟨2164202, by rfl⟩ : syracuseStep 2885603 = 4328405) B4328405
theorem B1923735 : Blo 1923435 1923735 := bstep (se 1 (by rfl) ⟨1442801, by rfl⟩ : syracuseStep 1923735 = 2885603) B2885603
theorem B2924981 : Blo 1923435 2924981 := bbase (se 5 (by rfl) ⟨137108, by rfl⟩ : syracuseStep 2924981 = 274217) (by norm_num)
theorem B1949987 : Blo 1923435 1949987 := bstep (se 1 (by rfl) ⟨1462490, by rfl⟩ : syracuseStep 1949987 = 2924981) B2924981
theorem B5199965 : Blo 1923435 5199965 := bstep (se 3 (by rfl) ⟨974993, by rfl⟩ : syracuseStep 5199965 = 1949987) B1949987
theorem B3466643 : Blo 1923435 3466643 := bstep (se 1 (by rfl) ⟨2599982, by rfl⟩ : syracuseStep 3466643 = 5199965) B5199965
theorem B9244381 : Blo 1923435 9244381 := bstep (se 3 (by rfl) ⟨1733321, by rfl⟩ : syracuseStep 9244381 = 3466643) B3466643
theorem B12325841 : Blo 1923435 12325841 := bstep (se 2 (by rfl) ⟨4622190, by rfl⟩ : syracuseStep 12325841 = 9244381) B9244381
theorem B8217227 : Blo 1923435 8217227 := bstep (se 1 (by rfl) ⟨6162920, by rfl⟩ : syracuseStep 8217227 = 12325841) B12325841
theorem B5478151 : Blo 1923435 5478151 := bstep (se 1 (by rfl) ⟨4108613, by rfl⟩ : syracuseStep 5478151 = 8217227) B8217227
theorem B7304201 : Blo 1923435 7304201 := bstep (se 2 (by rfl) ⟨2739075, by rfl⟩ : syracuseStep 7304201 = 5478151) B5478151
theorem B4869467 : Blo 1923435 4869467 := bstep (se 1 (by rfl) ⟨3652100, by rfl⟩ : syracuseStep 4869467 = 7304201) B7304201
theorem B3246311 : Blo 1923435 3246311 := bstep (se 1 (by rfl) ⟨2434733, by rfl⟩ : syracuseStep 3246311 = 4869467) B4869467
theorem B2164207 : Blo 1923435 2164207 := bstep (se 1 (by rfl) ⟨1623155, by rfl⟩ : syracuseStep 2164207 = 3246311) B3246311
theorem B2885609 : Blo 1923435 2885609 := bstep (se 2 (by rfl) ⟨1082103, by rfl⟩ : syracuseStep 2885609 = 2164207) B2164207
theorem B1923739 : Blo 1923435 1923739 := bstep (se 1 (by rfl) ⟨1442804, by rfl⟩ : syracuseStep 1923739 = 2885609) B2885609
theorem B16434485 : Blo 1923435 16434485 := bbase (se 5 (by rfl) ⟨770366, by rfl⟩ : syracuseStep 16434485 = 1540733) (by norm_num)
theorem B10956323 : Blo 1923435 10956323 := bstep (se 1 (by rfl) ⟨8217242, by rfl⟩ : syracuseStep 10956323 = 16434485) B16434485
theorem B7304215 : Blo 1923435 7304215 := bstep (se 1 (by rfl) ⟨5478161, by rfl⟩ : syracuseStep 7304215 = 10956323) B10956323
theorem B9738953 : Blo 1923435 9738953 := bstep (se 2 (by rfl) ⟨3652107, by rfl⟩ : syracuseStep 9738953 = 7304215) B7304215
theorem B6492635 : Blo 1923435 6492635 := bstep (se 1 (by rfl) ⟨4869476, by rfl⟩ : syracuseStep 6492635 = 9738953) B9738953
theorem B4328423 : Blo 1923435 4328423 := bstep (se 1 (by rfl) ⟨3246317, by rfl⟩ : syracuseStep 4328423 = 6492635) B6492635
theorem B2885615 : Blo 1923435 2885615 := bstep (se 1 (by rfl) ⟨2164211, by rfl⟩ : syracuseStep 2885615 = 4328423) B4328423
theorem B1923743 : Blo 1923435 1923743 := bstep (se 1 (by rfl) ⟨1442807, by rfl⟩ : syracuseStep 1923743 = 2885615) B2885615
theorem B2885621 : Blo 1923435 2885621 := bbase (se 5 (by rfl) ⟨135263, by rfl⟩ : syracuseStep 2885621 = 270527) (by norm_num)
theorem B1923747 : Blo 1923435 1923747 := bstep (se 1 (by rfl) ⟨1442810, by rfl⟩ : syracuseStep 1923747 = 2885621) B2885621
theorem B2082349 : Blo 1923435 2082349 := bbase (se 3 (by rfl) ⟨390440, by rfl⟩ : syracuseStep 2082349 = 780881) (by norm_num)
theorem B2776465 : Blo 1923435 2776465 := bstep (se 2 (by rfl) ⟨1041174, by rfl⟩ : syracuseStep 2776465 = 2082349) B2082349
theorem B3701953 : Blo 1923435 3701953 := bstep (se 2 (by rfl) ⟨1388232, by rfl⟩ : syracuseStep 3701953 = 2776465) B2776465
theorem B4935937 : Blo 1923435 4935937 := bstep (se 2 (by rfl) ⟨1850976, by rfl⟩ : syracuseStep 4935937 = 3701953) B3701953
theorem B6581249 : Blo 1923435 6581249 := bstep (se 2 (by rfl) ⟨2467968, by rfl⟩ : syracuseStep 6581249 = 4935937) B4935937
theorem B4387499 : Blo 1923435 4387499 := bstep (se 1 (by rfl) ⟨3290624, by rfl⟩ : syracuseStep 4387499 = 6581249) B6581249
theorem B2924999 : Blo 1923435 2924999 := bstep (se 1 (by rfl) ⟨2193749, by rfl⟩ : syracuseStep 2924999 = 4387499) B4387499
theorem B1949999 : Blo 1923435 1949999 := bstep (se 1 (by rfl) ⟨1462499, by rfl⟩ : syracuseStep 1949999 = 2924999) B2924999
theorem B20799989 : Blo 1923435 20799989 := bstep (se 5 (by rfl) ⟨974999, by rfl⟩ : syracuseStep 20799989 = 1949999) B1949999
theorem B13866659 : Blo 1923435 13866659 := bstep (se 1 (by rfl) ⟨10399994, by rfl⟩ : syracuseStep 13866659 = 20799989) B20799989
theorem B9244439 : Blo 1923435 9244439 := bstep (se 1 (by rfl) ⟨6933329, by rfl⟩ : syracuseStep 9244439 = 13866659) B13866659
theorem B6162959 : Blo 1923435 6162959 := bstep (se 1 (by rfl) ⟨4622219, by rfl⟩ : syracuseStep 6162959 = 9244439) B9244439
theorem B4108639 : Blo 1923435 4108639 := bstep (se 1 (by rfl) ⟨3081479, by rfl⟩ : syracuseStep 4108639 = 6162959) B6162959
theorem B5478185 : Blo 1923435 5478185 := bstep (se 2 (by rfl) ⟨2054319, by rfl⟩ : syracuseStep 5478185 = 4108639) B4108639
theorem B3652123 : Blo 1923435 3652123 := bstep (se 1 (by rfl) ⟨2739092, by rfl⟩ : syracuseStep 3652123 = 5478185) B5478185
theorem B4869497 : Blo 1923435 4869497 := bstep (se 2 (by rfl) ⟨1826061, by rfl⟩ : syracuseStep 4869497 = 3652123) B3652123
theorem B3246331 : Blo 1923435 3246331 := bstep (se 1 (by rfl) ⟨2434748, by rfl⟩ : syracuseStep 3246331 = 4869497) B4869497
theorem B4328441 : Blo 1923435 4328441 := bstep (se 2 (by rfl) ⟨1623165, by rfl⟩ : syracuseStep 4328441 = 3246331) B3246331
theorem B2885627 : Blo 1923435 2885627 := bstep (se 1 (by rfl) ⟨2164220, by rfl⟩ : syracuseStep 2885627 = 4328441) B4328441
theorem B1923751 : Blo 1923435 1923751 := bstep (se 1 (by rfl) ⟨1442813, by rfl⟩ : syracuseStep 1923751 = 2885627) B2885627
theorem B2164225 : Blo 1923435 2164225 := bbase (se 2 (by rfl) ⟨811584, by rfl⟩ : syracuseStep 2164225 = 1623169) (by norm_num)
theorem B2885633 : Blo 1923435 2885633 := bstep (se 2 (by rfl) ⟨1082112, by rfl⟩ : syracuseStep 2885633 = 2164225) B2164225
theorem B1923755 : Blo 1923435 1923755 := bstep (se 1 (by rfl) ⟨1442816, by rfl⟩ : syracuseStep 1923755 = 2885633) B2885633
theorem B4869517 : Blo 1923435 4869517 := bbase (se 3 (by rfl) ⟨913034, by rfl⟩ : syracuseStep 4869517 = 1826069) (by norm_num)
theorem B6492689 : Blo 1923435 6492689 := bstep (se 2 (by rfl) ⟨2434758, by rfl⟩ : syracuseStep 6492689 = 4869517) B4869517
theorem B4328459 : Blo 1923435 4328459 := bstep (se 1 (by rfl) ⟨3246344, by rfl⟩ : syracuseStep 4328459 = 6492689) B6492689
theorem B2885639 : Blo 1923435 2885639 := bstep (se 1 (by rfl) ⟨2164229, by rfl⟩ : syracuseStep 2885639 = 4328459) B4328459
theorem B1923759 : Blo 1923435 1923759 := bstep (se 1 (by rfl) ⟨1442819, by rfl⟩ : syracuseStep 1923759 = 2885639) B2885639
theorem B2885645 : Blo 1923435 2885645 := bbase (se 3 (by rfl) ⟨541058, by rfl⟩ : syracuseStep 2885645 = 1082117) (by norm_num)
theorem B1923763 : Blo 1923435 1923763 := bstep (se 1 (by rfl) ⟨1442822, by rfl⟩ : syracuseStep 1923763 = 2885645) B2885645
theorem B4328477 : Blo 1923435 4328477 := bbase (se 3 (by rfl) ⟨811589, by rfl⟩ : syracuseStep 4328477 = 1623179) (by norm_num)
theorem B2885651 : Blo 1923435 2885651 := bstep (se 1 (by rfl) ⟨2164238, by rfl⟩ : syracuseStep 2885651 = 4328477) B4328477
theorem B1923767 : Blo 1923435 1923767 := bstep (se 1 (by rfl) ⟨1442825, by rfl⟩ : syracuseStep 1923767 = 2885651) B2885651
theorem B3246365 : Blo 1923435 3246365 := bbase (se 3 (by rfl) ⟨608693, by rfl⟩ : syracuseStep 3246365 = 1217387) (by norm_num)
theorem B2164243 : Blo 1923435 2164243 := bstep (se 1 (by rfl) ⟨1623182, by rfl⟩ : syracuseStep 2164243 = 3246365) B3246365
theorem B2885657 : Blo 1923435 2885657 := bstep (se 2 (by rfl) ⟨1082121, by rfl⟩ : syracuseStep 2885657 = 2164243) B2164243
theorem B1923771 : Blo 1923435 1923771 := bstep (se 1 (by rfl) ⟨1442828, by rfl⟩ : syracuseStep 1923771 = 2885657) B2885657
theorem B12326069 : Blo 1923435 12326069 := bbase (se 5 (by rfl) ⟨577784, by rfl⟩ : syracuseStep 12326069 = 1155569) (by norm_num)
theorem B8217379 : Blo 1923435 8217379 := bstep (se 1 (by rfl) ⟨6163034, by rfl⟩ : syracuseStep 8217379 = 12326069) B12326069
theorem B10956505 : Blo 1923435 10956505 := bstep (se 2 (by rfl) ⟨4108689, by rfl⟩ : syracuseStep 10956505 = 8217379) B8217379
theorem B14608673 : Blo 1923435 14608673 := bstep (se 2 (by rfl) ⟨5478252, by rfl⟩ : syracuseStep 14608673 = 10956505) B10956505
theorem B9739115 : Blo 1923435 9739115 := bstep (se 1 (by rfl) ⟨7304336, by rfl⟩ : syracuseStep 9739115 = 14608673) B14608673
theorem B6492743 : Blo 1923435 6492743 := bstep (se 1 (by rfl) ⟨4869557, by rfl⟩ : syracuseStep 6492743 = 9739115) B9739115
theorem B4328495 : Blo 1923435 4328495 := bstep (se 1 (by rfl) ⟨3246371, by rfl⟩ : syracuseStep 4328495 = 6492743) B6492743
theorem B2885663 : Blo 1923435 2885663 := bstep (se 1 (by rfl) ⟨2164247, by rfl⟩ : syracuseStep 2885663 = 4328495) B4328495
theorem B1923775 : Blo 1923435 1923775 := bstep (se 1 (by rfl) ⟨1442831, by rfl⟩ : syracuseStep 1923775 = 2885663) B2885663
theorem B2885669 : Blo 1923435 2885669 := bbase (se 4 (by rfl) ⟨270531, by rfl⟩ : syracuseStep 2885669 = 541063) (by norm_num)
theorem B1923779 : Blo 1923435 1923779 := bstep (se 1 (by rfl) ⟨1442834, by rfl⟩ : syracuseStep 1923779 = 2885669) B2885669
theorem B2434789 : Blo 1923435 2434789 := bbase (se 4 (by rfl) ⟨228261, by rfl⟩ : syracuseStep 2434789 = 456523) (by norm_num)
theorem B3246385 : Blo 1923435 3246385 := bstep (se 2 (by rfl) ⟨1217394, by rfl⟩ : syracuseStep 3246385 = 2434789) B2434789
theorem B4328513 : Blo 1923435 4328513 := bstep (se 2 (by rfl) ⟨1623192, by rfl⟩ : syracuseStep 4328513 = 3246385) B3246385
theorem B2885675 : Blo 1923435 2885675 := bstep (se 1 (by rfl) ⟨2164256, by rfl⟩ : syracuseStep 2885675 = 4328513) B4328513
theorem B1923783 : Blo 1923435 1923783 := bstep (se 1 (by rfl) ⟨1442837, by rfl⟩ : syracuseStep 1923783 = 2885675) B2885675
theorem B2164261 : Blo 1923435 2164261 := bbase (se 4 (by rfl) ⟨202899, by rfl⟩ : syracuseStep 2164261 = 405799) (by norm_num)
theorem B2885681 : Blo 1923435 2885681 := bstep (se 2 (by rfl) ⟨1082130, by rfl⟩ : syracuseStep 2885681 = 2164261) B2164261
theorem B1923787 : Blo 1923435 1923787 := bstep (se 1 (by rfl) ⟨1442840, by rfl⟩ : syracuseStep 1923787 = 2885681) B2885681
theorem B3702029 : Blo 1923435 3702029 := bbase (se 3 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 3702029 = 1388261) (by norm_num)
theorem B9872077 : Blo 1923435 9872077 := bstep (se 3 (by rfl) ⟨1851014, by rfl⟩ : syracuseStep 9872077 = 3702029) B3702029
theorem B13162769 : Blo 1923435 13162769 := bstep (se 2 (by rfl) ⟨4936038, by rfl⟩ : syracuseStep 13162769 = 9872077) B9872077
theorem B8775179 : Blo 1923435 8775179 := bstep (se 1 (by rfl) ⟨6581384, by rfl⟩ : syracuseStep 8775179 = 13162769) B13162769
theorem B5850119 : Blo 1923435 5850119 := bstep (se 1 (by rfl) ⟨4387589, by rfl⟩ : syracuseStep 5850119 = 8775179) B8775179
theorem B3900079 : Blo 1923435 3900079 := bstep (se 1 (by rfl) ⟨2925059, by rfl⟩ : syracuseStep 3900079 = 5850119) B5850119
theorem B20800421 : Blo 1923435 20800421 := bstep (se 4 (by rfl) ⟨1950039, by rfl⟩ : syracuseStep 20800421 = 3900079) B3900079
theorem B13866947 : Blo 1923435 13866947 := bstep (se 1 (by rfl) ⟨10400210, by rfl⟩ : syracuseStep 13866947 = 20800421) B20800421
theorem B9244631 : Blo 1923435 9244631 := bstep (se 1 (by rfl) ⟨6933473, by rfl⟩ : syracuseStep 9244631 = 13866947) B13866947
theorem B6163087 : Blo 1923435 6163087 := bstep (se 1 (by rfl) ⟨4622315, by rfl⟩ : syracuseStep 6163087 = 9244631) B9244631
theorem B8217449 : Blo 1923435 8217449 := bstep (se 2 (by rfl) ⟨3081543, by rfl⟩ : syracuseStep 8217449 = 6163087) B6163087
theorem B5478299 : Blo 1923435 5478299 := bstep (se 1 (by rfl) ⟨4108724, by rfl⟩ : syracuseStep 5478299 = 8217449) B8217449
theorem B3652199 : Blo 1923435 3652199 := bstep (se 1 (by rfl) ⟨2739149, by rfl⟩ : syracuseStep 3652199 = 5478299) B5478299
theorem B2434799 : Blo 1923435 2434799 := bstep (se 1 (by rfl) ⟨1826099, by rfl⟩ : syracuseStep 2434799 = 3652199) B3652199
theorem B6492797 : Blo 1923435 6492797 := bstep (se 3 (by rfl) ⟨1217399, by rfl⟩ : syracuseStep 6492797 = 2434799) B2434799
theorem B4328531 : Blo 1923435 4328531 := bstep (se 1 (by rfl) ⟨3246398, by rfl⟩ : syracuseStep 4328531 = 6492797) B6492797
theorem B2885687 : Blo 1923435 2885687 := bstep (se 1 (by rfl) ⟨2164265, by rfl⟩ : syracuseStep 2885687 = 4328531) B4328531
theorem B1923791 : Blo 1923435 1923791 := bstep (se 1 (by rfl) ⟨1442843, by rfl⟩ : syracuseStep 1923791 = 2885687) B2885687
theorem B2885693 : Blo 1923435 2885693 := bbase (se 3 (by rfl) ⟨541067, by rfl⟩ : syracuseStep 2885693 = 1082135) (by norm_num)
theorem B1923795 : Blo 1923435 1923795 := bstep (se 1 (by rfl) ⟨1442846, by rfl⟩ : syracuseStep 1923795 = 2885693) B2885693
theorem B4328549 : Blo 1923435 4328549 := bbase (se 4 (by rfl) ⟨405801, by rfl⟩ : syracuseStep 4328549 = 811603) (by norm_num)
theorem B2885699 : Blo 1923435 2885699 := bstep (se 1 (by rfl) ⟨2164274, by rfl⟩ : syracuseStep 2885699 = 4328549) B4328549
theorem B1923799 : Blo 1923435 1923799 := bstep (se 1 (by rfl) ⟨1442849, by rfl⟩ : syracuseStep 1923799 = 2885699) B2885699
theorem B4869629 : Blo 1923435 4869629 := bbase (se 3 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 4869629 = 1826111) (by norm_num)
theorem B3246419 : Blo 1923435 3246419 := bstep (se 1 (by rfl) ⟨2434814, by rfl⟩ : syracuseStep 3246419 = 4869629) B4869629
theorem B2164279 : Blo 1923435 2164279 := bstep (se 1 (by rfl) ⟨1623209, by rfl⟩ : syracuseStep 2164279 = 3246419) B3246419
theorem B2885705 : Blo 1923435 2885705 := bstep (se 2 (by rfl) ⟨1082139, by rfl⟩ : syracuseStep 2885705 = 2164279) B2164279
theorem B1923803 : Blo 1923435 1923803 := bstep (se 1 (by rfl) ⟨1442852, by rfl⟩ : syracuseStep 1923803 = 2885705) B2885705
theorem B3652229 : Blo 1923435 3652229 := bbase (se 4 (by rfl) ⟨342396, by rfl⟩ : syracuseStep 3652229 = 684793) (by norm_num)
theorem B9739277 : Blo 1923435 9739277 := bstep (se 3 (by rfl) ⟨1826114, by rfl⟩ : syracuseStep 9739277 = 3652229) B3652229
theorem B6492851 : Blo 1923435 6492851 := bstep (se 1 (by rfl) ⟨4869638, by rfl⟩ : syracuseStep 6492851 = 9739277) B9739277
theorem B4328567 : Blo 1923435 4328567 := bstep (se 1 (by rfl) ⟨3246425, by rfl⟩ : syracuseStep 4328567 = 6492851) B6492851
theorem B2885711 : Blo 1923435 2885711 := bstep (se 1 (by rfl) ⟨2164283, by rfl⟩ : syracuseStep 2885711 = 4328567) B4328567
theorem B1923807 : Blo 1923435 1923807 := bstep (se 1 (by rfl) ⟨1442855, by rfl⟩ : syracuseStep 1923807 = 2885711) B2885711
theorem B2885717 : Blo 1923435 2885717 := bbase (se 8 (by rfl) ⟨16908, by rfl⟩ : syracuseStep 2885717 = 33817) (by norm_num)
theorem B1923811 : Blo 1923435 1923811 := bstep (se 1 (by rfl) ⟨1442858, by rfl⟩ : syracuseStep 1923811 = 2885717) B2885717
theorem B7404149 : Blo 1923435 7404149 := bbase (se 5 (by rfl) ⟨347069, by rfl⟩ : syracuseStep 7404149 = 694139) (by norm_num)
theorem B19744397 : Blo 1923435 19744397 := bstep (se 3 (by rfl) ⟨3702074, by rfl⟩ : syracuseStep 19744397 = 7404149) B7404149
theorem B13162931 : Blo 1923435 13162931 := bstep (se 1 (by rfl) ⟨9872198, by rfl⟩ : syracuseStep 13162931 = 19744397) B19744397
theorem B8775287 : Blo 1923435 8775287 := bstep (se 1 (by rfl) ⟨6581465, by rfl⟩ : syracuseStep 8775287 = 13162931) B13162931
theorem B5850191 : Blo 1923435 5850191 := bstep (se 1 (by rfl) ⟨4387643, by rfl⟩ : syracuseStep 5850191 = 8775287) B8775287
theorem B15600509 : Blo 1923435 15600509 := bstep (se 3 (by rfl) ⟨2925095, by rfl⟩ : syracuseStep 15600509 = 5850191) B5850191
theorem B10400339 : Blo 1923435 10400339 := bstep (se 1 (by rfl) ⟨7800254, by rfl⟩ : syracuseStep 10400339 = 15600509) B15600509
theorem B27734237 : Blo 1923435 27734237 := bstep (se 3 (by rfl) ⟨5200169, by rfl⟩ : syracuseStep 27734237 = 10400339) B10400339
theorem B18489491 : Blo 1923435 18489491 := bstep (se 1 (by rfl) ⟨13867118, by rfl⟩ : syracuseStep 18489491 = 27734237) B27734237
theorem B12326327 : Blo 1923435 12326327 := bstep (se 1 (by rfl) ⟨9244745, by rfl⟩ : syracuseStep 12326327 = 18489491) B18489491
theorem B8217551 : Blo 1923435 8217551 := bstep (se 1 (by rfl) ⟨6163163, by rfl⟩ : syracuseStep 8217551 = 12326327) B12326327
theorem B5478367 : Blo 1923435 5478367 := bstep (se 1 (by rfl) ⟨4108775, by rfl⟩ : syracuseStep 5478367 = 8217551) B8217551
theorem B7304489 : Blo 1923435 7304489 := bstep (se 2 (by rfl) ⟨2739183, by rfl⟩ : syracuseStep 7304489 = 5478367) B5478367
theorem B4869659 : Blo 1923435 4869659 := bstep (se 1 (by rfl) ⟨3652244, by rfl⟩ : syracuseStep 4869659 = 7304489) B7304489
theorem B3246439 : Blo 1923435 3246439 := bstep (se 1 (by rfl) ⟨2434829, by rfl⟩ : syracuseStep 3246439 = 4869659) B4869659
theorem B4328585 : Blo 1923435 4328585 := bstep (se 2 (by rfl) ⟨1623219, by rfl⟩ : syracuseStep 4328585 = 3246439) B3246439
theorem B2885723 : Blo 1923435 2885723 := bstep (se 1 (by rfl) ⟨2164292, by rfl⟩ : syracuseStep 2885723 = 4328585) B4328585
theorem B1923815 : Blo 1923435 1923815 := bstep (se 1 (by rfl) ⟨1442861, by rfl⟩ : syracuseStep 1923815 = 2885723) B2885723
theorem B2164297 : Blo 1923435 2164297 := bbase (se 2 (by rfl) ⟨811611, by rfl⟩ : syracuseStep 2164297 = 1623223) (by norm_num)
theorem B2885729 : Blo 1923435 2885729 := bstep (se 2 (by rfl) ⟨1082148, by rfl⟩ : syracuseStep 2885729 = 2164297) B2164297
theorem B1923819 : Blo 1923435 1923819 := bstep (se 1 (by rfl) ⟨1442864, by rfl⟩ : syracuseStep 1923819 = 2885729) B2885729
theorem B7906709 : Blo 1923435 7906709 := bbase (se 6 (by rfl) ⟨185313, by rfl⟩ : syracuseStep 7906709 = 370627) (by norm_num)
theorem B5271139 : Blo 1923435 5271139 := bstep (se 1 (by rfl) ⟨3953354, by rfl⟩ : syracuseStep 5271139 = 7906709) B7906709
theorem B28112741 : Blo 1923435 28112741 := bstep (se 4 (by rfl) ⟨2635569, by rfl⟩ : syracuseStep 28112741 = 5271139) B5271139
theorem B18741827 : Blo 1923435 18741827 := bstep (se 1 (by rfl) ⟨14056370, by rfl⟩ : syracuseStep 18741827 = 28112741) B28112741
theorem B49978205 : Blo 1923435 49978205 := bstep (se 3 (by rfl) ⟨9370913, by rfl⟩ : syracuseStep 49978205 = 18741827) B18741827
theorem B33318803 : Blo 1923435 33318803 := bstep (se 1 (by rfl) ⟨24989102, by rfl⟩ : syracuseStep 33318803 = 49978205) B49978205
theorem B88850141 : Blo 1923435 88850141 := bstep (se 3 (by rfl) ⟨16659401, by rfl⟩ : syracuseStep 88850141 = 33318803) B33318803
theorem B59233427 : Blo 1923435 59233427 := bstep (se 1 (by rfl) ⟨44425070, by rfl⟩ : syracuseStep 59233427 = 88850141) B88850141
theorem B39488951 : Blo 1923435 39488951 := bstep (se 1 (by rfl) ⟨29616713, by rfl⟩ : syracuseStep 39488951 = 59233427) B59233427
theorem B26325967 : Blo 1923435 26325967 := bstep (se 1 (by rfl) ⟨19744475, by rfl⟩ : syracuseStep 26325967 = 39488951) B39488951
theorem B35101289 : Blo 1923435 35101289 := bstep (se 2 (by rfl) ⟨13162983, by rfl⟩ : syracuseStep 35101289 = 26325967) B26325967
theorem B23400859 : Blo 1923435 23400859 := bstep (se 1 (by rfl) ⟨17550644, by rfl⟩ : syracuseStep 23400859 = 35101289) B35101289
theorem B31201145 : Blo 1923435 31201145 := bstep (se 2 (by rfl) ⟨11700429, by rfl⟩ : syracuseStep 31201145 = 23400859) B23400859
theorem B20800763 : Blo 1923435 20800763 := bstep (se 1 (by rfl) ⟨15600572, by rfl⟩ : syracuseStep 20800763 = 31201145) B31201145
theorem B13867175 : Blo 1923435 13867175 := bstep (se 1 (by rfl) ⟨10400381, by rfl⟩ : syracuseStep 13867175 = 20800763) B20800763
theorem B9244783 : Blo 1923435 9244783 := bstep (se 1 (by rfl) ⟨6933587, by rfl⟩ : syracuseStep 9244783 = 13867175) B13867175
theorem B12326377 : Blo 1923435 12326377 := bstep (se 2 (by rfl) ⟨4622391, by rfl⟩ : syracuseStep 12326377 = 9244783) B9244783
theorem B16435169 : Blo 1923435 16435169 := bstep (se 2 (by rfl) ⟨6163188, by rfl⟩ : syracuseStep 16435169 = 12326377) B12326377
theorem B10956779 : Blo 1923435 10956779 := bstep (se 1 (by rfl) ⟨8217584, by rfl⟩ : syracuseStep 10956779 = 16435169) B16435169
theorem B7304519 : Blo 1923435 7304519 := bstep (se 1 (by rfl) ⟨5478389, by rfl⟩ : syracuseStep 7304519 = 10956779) B10956779
theorem B4869679 : Blo 1923435 4869679 := bstep (se 1 (by rfl) ⟨3652259, by rfl⟩ : syracuseStep 4869679 = 7304519) B7304519
theorem B6492905 : Blo 1923435 6492905 := bstep (se 2 (by rfl) ⟨2434839, by rfl⟩ : syracuseStep 6492905 = 4869679) B4869679
theorem B4328603 : Blo 1923435 4328603 := bstep (se 1 (by rfl) ⟨3246452, by rfl⟩ : syracuseStep 4328603 = 6492905) B6492905
theorem B2885735 : Blo 1923435 2885735 := bstep (se 1 (by rfl) ⟨2164301, by rfl⟩ : syracuseStep 2885735 = 4328603) B4328603
theorem B1923823 : Blo 1923435 1923823 := bstep (se 1 (by rfl) ⟨1442867, by rfl⟩ : syracuseStep 1923823 = 2885735) B2885735
theorem B2885741 : Blo 1923435 2885741 := bbase (se 3 (by rfl) ⟨541076, by rfl⟩ : syracuseStep 2885741 = 1082153) (by norm_num)
theorem B1923827 : Blo 1923435 1923827 := bstep (se 1 (by rfl) ⟨1442870, by rfl⟩ : syracuseStep 1923827 = 2885741) B2885741
theorem B4328621 : Blo 1923435 4328621 := bbase (se 3 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 4328621 = 1623233) (by norm_num)
theorem B2885747 : Blo 1923435 2885747 := bstep (se 1 (by rfl) ⟨2164310, by rfl⟩ : syracuseStep 2885747 = 4328621) B4328621
theorem B1923831 : Blo 1923435 1923831 := bstep (se 1 (by rfl) ⟨1442873, by rfl⟩ : syracuseStep 1923831 = 2885747) B2885747
theorem B1950085 : Blo 1923435 1950085 := bbase (se 4 (by rfl) ⟨182820, by rfl⟩ : syracuseStep 1950085 = 365641) (by norm_num)
theorem B2600113 : Blo 1923435 2600113 := bstep (se 2 (by rfl) ⟨975042, by rfl⟩ : syracuseStep 2600113 = 1950085) B1950085
theorem B3466817 : Blo 1923435 3466817 := bstep (se 2 (by rfl) ⟨1300056, by rfl⟩ : syracuseStep 3466817 = 2600113) B2600113
theorem B2311211 : Blo 1923435 2311211 := bstep (se 1 (by rfl) ⟨1733408, by rfl⟩ : syracuseStep 2311211 = 3466817) B3466817
theorem B6163229 : Blo 1923435 6163229 := bstep (se 3 (by rfl) ⟨1155605, by rfl⟩ : syracuseStep 6163229 = 2311211) B2311211
theorem B4108819 : Blo 1923435 4108819 := bstep (se 1 (by rfl) ⟨3081614, by rfl⟩ : syracuseStep 4108819 = 6163229) B6163229
theorem B5478425 : Blo 1923435 5478425 := bstep (se 2 (by rfl) ⟨2054409, by rfl⟩ : syracuseStep 5478425 = 4108819) B4108819
theorem B3652283 : Blo 1923435 3652283 := bstep (se 1 (by rfl) ⟨2739212, by rfl⟩ : syracuseStep 3652283 = 5478425) B5478425
theorem B2434855 : Blo 1923435 2434855 := bstep (se 1 (by rfl) ⟨1826141, by rfl⟩ : syracuseStep 2434855 = 3652283) B3652283
theorem B3246473 : Blo 1923435 3246473 := bstep (se 2 (by rfl) ⟨1217427, by rfl⟩ : syracuseStep 3246473 = 2434855) B2434855
theorem B2164315 : Blo 1923435 2164315 := bstep (se 1 (by rfl) ⟨1623236, by rfl⟩ : syracuseStep 2164315 = 3246473) B3246473
theorem B2885753 : Blo 1923435 2885753 := bstep (se 2 (by rfl) ⟨1082157, by rfl⟩ : syracuseStep 2885753 = 2164315) B2164315
theorem B1923835 : Blo 1923435 1923835 := bstep (se 1 (by rfl) ⟨1442876, by rfl⟩ : syracuseStep 1923835 = 2885753) B2885753
theorem B13163093 : Blo 1923435 13163093 := bbase (se 8 (by rfl) ⟨77127, by rfl⟩ : syracuseStep 13163093 = 154255) (by norm_num)
theorem B8775395 : Blo 1923435 8775395 := bstep (se 1 (by rfl) ⟨6581546, by rfl⟩ : syracuseStep 8775395 = 13163093) B13163093
theorem B5850263 : Blo 1923435 5850263 := bstep (se 1 (by rfl) ⟨4387697, by rfl⟩ : syracuseStep 5850263 = 8775395) B8775395
theorem B15600701 : Blo 1923435 15600701 := bstep (se 3 (by rfl) ⟨2925131, by rfl⟩ : syracuseStep 15600701 = 5850263) B5850263
theorem B10400467 : Blo 1923435 10400467 := bstep (se 1 (by rfl) ⟨7800350, by rfl⟩ : syracuseStep 10400467 = 15600701) B15600701
theorem B13867289 : Blo 1923435 13867289 := bstep (se 2 (by rfl) ⟨5200233, by rfl⟩ : syracuseStep 13867289 = 10400467) B10400467
theorem B9244859 : Blo 1923435 9244859 := bstep (se 1 (by rfl) ⟨6933644, by rfl⟩ : syracuseStep 9244859 = 13867289) B13867289
theorem B24652957 : Blo 1923435 24652957 := bstep (se 3 (by rfl) ⟨4622429, by rfl⟩ : syracuseStep 24652957 = 9244859) B9244859
theorem B32870609 : Blo 1923435 32870609 := bstep (se 2 (by rfl) ⟨12326478, by rfl⟩ : syracuseStep 32870609 = 24652957) B24652957
theorem B21913739 : Blo 1923435 21913739 := bstep (se 1 (by rfl) ⟨16435304, by rfl⟩ : syracuseStep 21913739 = 32870609) B32870609
theorem B14609159 : Blo 1923435 14609159 := bstep (se 1 (by rfl) ⟨10956869, by rfl⟩ : syracuseStep 14609159 = 21913739) B21913739
theorem B9739439 : Blo 1923435 9739439 := bstep (se 1 (by rfl) ⟨7304579, by rfl⟩ : syracuseStep 9739439 = 14609159) B14609159
theorem B6492959 : Blo 1923435 6492959 := bstep (se 1 (by rfl) ⟨4869719, by rfl⟩ : syracuseStep 6492959 = 9739439) B9739439
theorem B4328639 : Blo 1923435 4328639 := bstep (se 1 (by rfl) ⟨3246479, by rfl⟩ : syracuseStep 4328639 = 6492959) B6492959
theorem B2885759 : Blo 1923435 2885759 := bstep (se 1 (by rfl) ⟨2164319, by rfl⟩ : syracuseStep 2885759 = 4328639) B4328639
theorem B1923839 : Blo 1923435 1923839 := bstep (se 1 (by rfl) ⟨1442879, by rfl⟩ : syracuseStep 1923839 = 2885759) B2885759
theorem B2885765 : Blo 1923435 2885765 := bbase (se 4 (by rfl) ⟨270540, by rfl⟩ : syracuseStep 2885765 = 541081) (by norm_num)
theorem B1923843 : Blo 1923435 1923843 := bstep (se 1 (by rfl) ⟨1442882, by rfl⟩ : syracuseStep 1923843 = 2885765) B2885765
theorem B3246493 : Blo 1923435 3246493 := bbase (se 3 (by rfl) ⟨608717, by rfl⟩ : syracuseStep 3246493 = 1217435) (by norm_num)
theorem B4328657 : Blo 1923435 4328657 := bstep (se 2 (by rfl) ⟨1623246, by rfl⟩ : syracuseStep 4328657 = 3246493) B3246493
theorem B2885771 : Blo 1923435 2885771 := bstep (se 1 (by rfl) ⟨2164328, by rfl⟩ : syracuseStep 2885771 = 4328657) B4328657
theorem B1923847 : Blo 1923435 1923847 := bstep (se 1 (by rfl) ⟨1442885, by rfl⟩ : syracuseStep 1923847 = 2885771) B2885771
theorem B2164333 : Blo 1923435 2164333 := bbase (se 3 (by rfl) ⟨405812, by rfl⟩ : syracuseStep 2164333 = 811625) (by norm_num)
theorem B2885777 : Blo 1923435 2885777 := bstep (se 2 (by rfl) ⟨1082166, by rfl⟩ : syracuseStep 2885777 = 2164333) B2164333
theorem B1923851 : Blo 1923435 1923851 := bstep (se 1 (by rfl) ⟨1442888, by rfl⟩ : syracuseStep 1923851 = 2885777) B2885777
theorem B6493013 : Blo 1923435 6493013 := bbase (se 9 (by rfl) ⟨19022, by rfl⟩ : syracuseStep 6493013 = 38045) (by norm_num)
theorem B4328675 : Blo 1923435 4328675 := bstep (se 1 (by rfl) ⟨3246506, by rfl⟩ : syracuseStep 4328675 = 6493013) B6493013
theorem B2885783 : Blo 1923435 2885783 := bstep (se 1 (by rfl) ⟨2164337, by rfl⟩ : syracuseStep 2885783 = 4328675) B4328675
theorem B1923855 : Blo 1923435 1923855 := bstep (se 1 (by rfl) ⟨1442891, by rfl⟩ : syracuseStep 1923855 = 2885783) B2885783
theorem B2885789 : Blo 1923435 2885789 := bbase (se 3 (by rfl) ⟨541085, by rfl⟩ : syracuseStep 2885789 = 1082171) (by norm_num)
theorem B1923859 : Blo 1923435 1923859 := bstep (se 1 (by rfl) ⟨1442894, by rfl⟩ : syracuseStep 1923859 = 2885789) B2885789
theorem B4328693 : Blo 1923435 4328693 := bbase (se 5 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 4328693 = 405815) (by norm_num)
theorem B2885795 : Blo 1923435 2885795 := bstep (se 1 (by rfl) ⟨2164346, by rfl⟩ : syracuseStep 2885795 = 4328693) B4328693
theorem B1923863 : Blo 1923435 1923863 := bstep (se 1 (by rfl) ⟨1442897, by rfl⟩ : syracuseStep 1923863 = 2885795) B2885795
theorem B2193881 : Blo 1923435 2193881 := bbase (se 2 (by rfl) ⟨822705, by rfl⟩ : syracuseStep 2193881 = 1645411) (by norm_num)
theorem B5850349 : Blo 1923435 5850349 := bstep (se 3 (by rfl) ⟨1096940, by rfl⟩ : syracuseStep 5850349 = 2193881) B2193881
theorem B31201861 : Blo 1923435 31201861 := bstep (se 4 (by rfl) ⟨2925174, by rfl⟩ : syracuseStep 31201861 = 5850349) B5850349
theorem B41602481 : Blo 1923435 41602481 := bstep (se 2 (by rfl) ⟨15600930, by rfl⟩ : syracuseStep 41602481 = 31201861) B31201861
theorem B27734987 : Blo 1923435 27734987 := bstep (se 1 (by rfl) ⟨20801240, by rfl⟩ : syracuseStep 27734987 = 41602481) B41602481
theorem B18489991 : Blo 1923435 18489991 := bstep (se 1 (by rfl) ⟨13867493, by rfl⟩ : syracuseStep 18489991 = 27734987) B27734987
theorem B24653321 : Blo 1923435 24653321 := bstep (se 2 (by rfl) ⟨9244995, by rfl⟩ : syracuseStep 24653321 = 18489991) B18489991
theorem B16435547 : Blo 1923435 16435547 := bstep (se 1 (by rfl) ⟨12326660, by rfl⟩ : syracuseStep 16435547 = 24653321) B24653321
theorem B10957031 : Blo 1923435 10957031 := bstep (se 1 (by rfl) ⟨8217773, by rfl⟩ : syracuseStep 10957031 = 16435547) B16435547
theorem B7304687 : Blo 1923435 7304687 := bstep (se 1 (by rfl) ⟨5478515, by rfl⟩ : syracuseStep 7304687 = 10957031) B10957031
theorem B4869791 : Blo 1923435 4869791 := bstep (se 1 (by rfl) ⟨3652343, by rfl⟩ : syracuseStep 4869791 = 7304687) B7304687
theorem B3246527 : Blo 1923435 3246527 := bstep (se 1 (by rfl) ⟨2434895, by rfl⟩ : syracuseStep 3246527 = 4869791) B4869791
theorem B2164351 : Blo 1923435 2164351 := bstep (se 1 (by rfl) ⟨1623263, by rfl⟩ : syracuseStep 2164351 = 3246527) B3246527
theorem B2885801 : Blo 1923435 2885801 := bstep (se 2 (by rfl) ⟨1082175, by rfl⟩ : syracuseStep 2885801 = 2164351) B2164351
theorem B1923867 : Blo 1923435 1923867 := bstep (se 1 (by rfl) ⟨1442900, by rfl⟩ : syracuseStep 1923867 = 2885801) B2885801
theorem B2925181 : Blo 1923435 2925181 := bbase (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) (by norm_num)
theorem B3900241 : Blo 1923435 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B20801285 : Blo 1923435 20801285 := bstep (se 4 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 20801285 = 3900241) B3900241
theorem B13867523 : Blo 1923435 13867523 := bstep (se 1 (by rfl) ⟨10400642, by rfl⟩ : syracuseStep 13867523 = 20801285) B20801285
theorem B9245015 : Blo 1923435 9245015 := bstep (se 1 (by rfl) ⟨6933761, by rfl⟩ : syracuseStep 9245015 = 13867523) B13867523
theorem B6163343 : Blo 1923435 6163343 := bstep (se 1 (by rfl) ⟨4622507, by rfl⟩ : syracuseStep 6163343 = 9245015) B9245015
theorem B4108895 : Blo 1923435 4108895 := bstep (se 1 (by rfl) ⟨3081671, by rfl⟩ : syracuseStep 4108895 = 6163343) B6163343
theorem B2739263 : Blo 1923435 2739263 := bstep (se 1 (by rfl) ⟨2054447, by rfl⟩ : syracuseStep 2739263 = 4108895) B4108895
theorem B7304701 : Blo 1923435 7304701 := bstep (se 3 (by rfl) ⟨1369631, by rfl⟩ : syracuseStep 7304701 = 2739263) B2739263
theorem B9739601 : Blo 1923435 9739601 := bstep (se 2 (by rfl) ⟨3652350, by rfl⟩ : syracuseStep 9739601 = 7304701) B7304701
theorem B6493067 : Blo 1923435 6493067 := bstep (se 1 (by rfl) ⟨4869800, by rfl⟩ : syracuseStep 6493067 = 9739601) B9739601
theorem B4328711 : Blo 1923435 4328711 := bstep (se 1 (by rfl) ⟨3246533, by rfl⟩ : syracuseStep 4328711 = 6493067) B6493067
theorem B2885807 : Blo 1923435 2885807 := bstep (se 1 (by rfl) ⟨2164355, by rfl⟩ : syracuseStep 2885807 = 4328711) B4328711
theorem B1923871 : Blo 1923435 1923871 := bstep (se 1 (by rfl) ⟨1442903, by rfl⟩ : syracuseStep 1923871 = 2885807) B2885807
theorem B2885813 : Blo 1923435 2885813 := bbase (se 5 (by rfl) ⟨135272, by rfl⟩ : syracuseStep 2885813 = 270545) (by norm_num)
theorem B1923875 : Blo 1923435 1923875 := bstep (se 1 (by rfl) ⟨1442906, by rfl⟩ : syracuseStep 1923875 = 2885813) B2885813
theorem B4869821 : Blo 1923435 4869821 := bbase (se 3 (by rfl) ⟨913091, by rfl⟩ : syracuseStep 4869821 = 1826183) (by norm_num)
theorem B3246547 : Blo 1923435 3246547 := bstep (se 1 (by rfl) ⟨2434910, by rfl⟩ : syracuseStep 3246547 = 4869821) B4869821
theorem B4328729 : Blo 1923435 4328729 := bstep (se 2 (by rfl) ⟨1623273, by rfl⟩ : syracuseStep 4328729 = 3246547) B3246547
theorem B2885819 : Blo 1923435 2885819 := bstep (se 1 (by rfl) ⟨2164364, by rfl⟩ : syracuseStep 2885819 = 4328729) B4328729
theorem B1923879 : Blo 1923435 1923879 := bstep (se 1 (by rfl) ⟨1442909, by rfl⟩ : syracuseStep 1923879 = 2885819) B2885819
theorem B2164369 : Blo 1923435 2164369 := bbase (se 2 (by rfl) ⟨811638, by rfl⟩ : syracuseStep 2164369 = 1623277) (by norm_num)
theorem B2885825 : Blo 1923435 2885825 := bstep (se 2 (by rfl) ⟨1082184, by rfl⟩ : syracuseStep 2885825 = 2164369) B2164369
theorem B1923883 : Blo 1923435 1923883 := bstep (se 1 (by rfl) ⟨1442912, by rfl⟩ : syracuseStep 1923883 = 2885825) B2885825
theorem B3652381 : Blo 1923435 3652381 := bbase (se 3 (by rfl) ⟨684821, by rfl⟩ : syracuseStep 3652381 = 1369643) (by norm_num)
theorem B4869841 : Blo 1923435 4869841 := bstep (se 2 (by rfl) ⟨1826190, by rfl⟩ : syracuseStep 4869841 = 3652381) B3652381
theorem B6493121 : Blo 1923435 6493121 := bstep (se 2 (by rfl) ⟨2434920, by rfl⟩ : syracuseStep 6493121 = 4869841) B4869841
theorem B4328747 : Blo 1923435 4328747 := bstep (se 1 (by rfl) ⟨3246560, by rfl⟩ : syracuseStep 4328747 = 6493121) B6493121
theorem B2885831 : Blo 1923435 2885831 := bstep (se 1 (by rfl) ⟨2164373, by rfl⟩ : syracuseStep 2885831 = 4328747) B4328747
theorem B1923887 : Blo 1923435 1923887 := bstep (se 1 (by rfl) ⟨1442915, by rfl⟩ : syracuseStep 1923887 = 2885831) B2885831
theorem B2885837 : Blo 1923435 2885837 := bbase (se 3 (by rfl) ⟨541094, by rfl⟩ : syracuseStep 2885837 = 1082189) (by norm_num)
theorem B1923891 : Blo 1923435 1923891 := bstep (se 1 (by rfl) ⟨1442918, by rfl⟩ : syracuseStep 1923891 = 2885837) B2885837
theorem B4328765 : Blo 1923435 4328765 := bbase (se 3 (by rfl) ⟨811643, by rfl⟩ : syracuseStep 4328765 = 1623287) (by norm_num)
theorem B2885843 : Blo 1923435 2885843 := bstep (se 1 (by rfl) ⟨2164382, by rfl⟩ : syracuseStep 2885843 = 4328765) B4328765
theorem B1923895 : Blo 1923435 1923895 := bstep (se 1 (by rfl) ⟨1442921, by rfl⟩ : syracuseStep 1923895 = 2885843) B2885843
theorem B3246581 : Blo 1923435 3246581 := bbase (se 5 (by rfl) ⟨152183, by rfl⟩ : syracuseStep 3246581 = 304367) (by norm_num)
theorem B2164387 : Blo 1923435 2164387 := bstep (se 1 (by rfl) ⟨1623290, by rfl⟩ : syracuseStep 2164387 = 3246581) B3246581
theorem B2885849 : Blo 1923435 2885849 := bstep (se 2 (by rfl) ⟨1082193, by rfl⟩ : syracuseStep 2885849 = 2164387) B2164387
theorem B1923899 : Blo 1923435 1923899 := bstep (se 1 (by rfl) ⟨1442924, by rfl⟩ : syracuseStep 1923899 = 2885849) B2885849
theorem B6163445 : Blo 1923435 6163445 := bbase (se 5 (by rfl) ⟨288911, by rfl⟩ : syracuseStep 6163445 = 577823) (by norm_num)
theorem B4108963 : Blo 1923435 4108963 := bstep (se 1 (by rfl) ⟨3081722, by rfl⟩ : syracuseStep 4108963 = 6163445) B6163445
theorem B5478617 : Blo 1923435 5478617 := bstep (se 2 (by rfl) ⟨2054481, by rfl⟩ : syracuseStep 5478617 = 4108963) B4108963
theorem B14609645 : Blo 1923435 14609645 := bstep (se 3 (by rfl) ⟨2739308, by rfl⟩ : syracuseStep 14609645 = 5478617) B5478617
theorem B9739763 : Blo 1923435 9739763 := bstep (se 1 (by rfl) ⟨7304822, by rfl⟩ : syracuseStep 9739763 = 14609645) B14609645
theorem B6493175 : Blo 1923435 6493175 := bstep (se 1 (by rfl) ⟨4869881, by rfl⟩ : syracuseStep 6493175 = 9739763) B9739763
theorem B4328783 : Blo 1923435 4328783 := bstep (se 1 (by rfl) ⟨3246587, by rfl⟩ : syracuseStep 4328783 = 6493175) B6493175
theorem B2885855 : Blo 1923435 2885855 := bstep (se 1 (by rfl) ⟨2164391, by rfl⟩ : syracuseStep 2885855 = 4328783) B4328783
theorem B1923903 : Blo 1923435 1923903 := bstep (se 1 (by rfl) ⟨1442927, by rfl⟩ : syracuseStep 1923903 = 2885855) B2885855
theorem B2885861 : Blo 1923435 2885861 := bbase (se 4 (by rfl) ⟨270549, by rfl⟩ : syracuseStep 2885861 = 541099) (by norm_num)
theorem B1923907 : Blo 1923435 1923907 := bstep (se 1 (by rfl) ⟨1442930, by rfl⟩ : syracuseStep 1923907 = 2885861) B2885861
theorem B4108981 : Blo 1923435 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B5478641 : Blo 1923435 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B3652427 : Blo 1923435 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B2434951 : Blo 1923435 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B3246601 : Blo 1923435 3246601 := bstep (se 2 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 3246601 = 2434951) B2434951
theorem B4328801 : Blo 1923435 4328801 := bstep (se 2 (by rfl) ⟨1623300, by rfl⟩ : syracuseStep 4328801 = 3246601) B3246601
theorem B2885867 : Blo 1923435 2885867 := bstep (se 1 (by rfl) ⟨2164400, by rfl⟩ : syracuseStep 2885867 = 4328801) B4328801
theorem B1923911 : Blo 1923435 1923911 := bstep (se 1 (by rfl) ⟨1442933, by rfl⟩ : syracuseStep 1923911 = 2885867) B2885867
theorem B2164405 : Blo 1923435 2164405 := bbase (se 5 (by rfl) ⟨101456, by rfl⟩ : syracuseStep 2164405 = 202913) (by norm_num)
theorem B2885873 : Blo 1923435 2885873 := bstep (se 2 (by rfl) ⟨1082202, by rfl⟩ : syracuseStep 2885873 = 2164405) B2164405
theorem B1923915 : Blo 1923435 1923915 := bstep (se 1 (by rfl) ⟨1442936, by rfl⟩ : syracuseStep 1923915 = 2885873) B2885873
theorem B2434961 : Blo 1923435 2434961 := bbase (se 2 (by rfl) ⟨913110, by rfl⟩ : syracuseStep 2434961 = 1826221) (by norm_num)
theorem B6493229 : Blo 1923435 6493229 := bstep (se 3 (by rfl) ⟨1217480, by rfl⟩ : syracuseStep 6493229 = 2434961) B2434961
theorem B4328819 : Blo 1923435 4328819 := bstep (se 1 (by rfl) ⟨3246614, by rfl⟩ : syracuseStep 4328819 = 6493229) B6493229
theorem B2885879 : Blo 1923435 2885879 := bstep (se 1 (by rfl) ⟨2164409, by rfl⟩ : syracuseStep 2885879 = 4328819) B4328819
theorem B1923919 : Blo 1923435 1923919 := bstep (se 1 (by rfl) ⟨1442939, by rfl⟩ : syracuseStep 1923919 = 2885879) B2885879
theorem B2885885 : Blo 1923435 2885885 := bbase (se 3 (by rfl) ⟨541103, by rfl⟩ : syracuseStep 2885885 = 1082207) (by norm_num)
theorem B1923923 : Blo 1923435 1923923 := bstep (se 1 (by rfl) ⟨1442942, by rfl⟩ : syracuseStep 1923923 = 2885885) B2885885
theorem B4328837 : Blo 1923435 4328837 := bbase (se 4 (by rfl) ⟨405828, by rfl⟩ : syracuseStep 4328837 = 811657) (by norm_num)
theorem B2885891 : Blo 1923435 2885891 := bstep (se 1 (by rfl) ⟨2164418, by rfl⟩ : syracuseStep 2885891 = 4328837) B4328837
theorem B1923927 : Blo 1923435 1923927 := bstep (se 1 (by rfl) ⟨1442945, by rfl⟩ : syracuseStep 1923927 = 2885891) B2885891
theorem B2739349 : Blo 1923435 2739349 := bbase (se 6 (by rfl) ⟨64203, by rfl⟩ : syracuseStep 2739349 = 128407) (by norm_num)
theorem B3652465 : Blo 1923435 3652465 := bstep (se 2 (by rfl) ⟨1369674, by rfl⟩ : syracuseStep 3652465 = 2739349) B2739349
theorem B4869953 : Blo 1923435 4869953 := bstep (se 2 (by rfl) ⟨1826232, by rfl⟩ : syracuseStep 4869953 = 3652465) B3652465
theorem B3246635 : Blo 1923435 3246635 := bstep (se 1 (by rfl) ⟨2434976, by rfl⟩ : syracuseStep 3246635 = 4869953) B4869953
theorem B2164423 : Blo 1923435 2164423 := bstep (se 1 (by rfl) ⟨1623317, by rfl⟩ : syracuseStep 2164423 = 3246635) B3246635
theorem B2885897 : Blo 1923435 2885897 := bstep (se 2 (by rfl) ⟨1082211, by rfl⟩ : syracuseStep 2885897 = 2164423) B2164423
theorem B1923931 : Blo 1923435 1923931 := bstep (se 1 (by rfl) ⟨1442948, by rfl⟩ : syracuseStep 1923931 = 2885897) B2885897
theorem B9739925 : Blo 1923435 9739925 := bbase (se 6 (by rfl) ⟨228279, by rfl⟩ : syracuseStep 9739925 = 456559) (by norm_num)
theorem B6493283 : Blo 1923435 6493283 := bstep (se 1 (by rfl) ⟨4869962, by rfl⟩ : syracuseStep 6493283 = 9739925) B9739925
theorem B4328855 : Blo 1923435 4328855 := bstep (se 1 (by rfl) ⟨3246641, by rfl⟩ : syracuseStep 4328855 = 6493283) B6493283
theorem B2885903 : Blo 1923435 2885903 := bstep (se 1 (by rfl) ⟨2164427, by rfl⟩ : syracuseStep 2885903 = 4328855) B4328855
theorem B1923935 : Blo 1923435 1923935 := bstep (se 1 (by rfl) ⟨1442951, by rfl⟩ : syracuseStep 1923935 = 2885903) B2885903
theorem B2885909 : Blo 1923435 2885909 := bbase (se 6 (by rfl) ⟨67638, by rfl⟩ : syracuseStep 2885909 = 135277) (by norm_num)
theorem B1923939 : Blo 1923435 1923939 := bstep (se 1 (by rfl) ⟨1442954, by rfl⟩ : syracuseStep 1923939 = 2885909) B2885909
theorem B24654293 : Blo 1923435 24654293 := bbase (se 7 (by rfl) ⟨288917, by rfl⟩ : syracuseStep 24654293 = 577835) (by norm_num)
theorem B16436195 : Blo 1923435 16436195 := bstep (se 1 (by rfl) ⟨12327146, by rfl⟩ : syracuseStep 16436195 = 24654293) B24654293
theorem B10957463 : Blo 1923435 10957463 := bstep (se 1 (by rfl) ⟨8218097, by rfl⟩ : syracuseStep 10957463 = 16436195) B16436195
theorem B7304975 : Blo 1923435 7304975 := bstep (se 1 (by rfl) ⟨5478731, by rfl⟩ : syracuseStep 7304975 = 10957463) B10957463
theorem B4869983 : Blo 1923435 4869983 := bstep (se 1 (by rfl) ⟨3652487, by rfl⟩ : syracuseStep 4869983 = 7304975) B7304975
theorem B3246655 : Blo 1923435 3246655 := bstep (se 1 (by rfl) ⟨2434991, by rfl⟩ : syracuseStep 3246655 = 4869983) B4869983
theorem B4328873 : Blo 1923435 4328873 := bstep (se 2 (by rfl) ⟨1623327, by rfl⟩ : syracuseStep 4328873 = 3246655) B3246655
theorem B2885915 : Blo 1923435 2885915 := bstep (se 1 (by rfl) ⟨2164436, by rfl⟩ : syracuseStep 2885915 = 4328873) B4328873
theorem B1923943 : Blo 1923435 1923943 := bstep (se 1 (by rfl) ⟨1442957, by rfl⟩ : syracuseStep 1923943 = 2885915) B2885915
theorem B2164441 : Blo 1923435 2164441 := bbase (se 2 (by rfl) ⟨811665, by rfl⟩ : syracuseStep 2164441 = 1623331) (by norm_num)
theorem B2885921 : Blo 1923435 2885921 := bstep (se 2 (by rfl) ⟨1082220, by rfl⟩ : syracuseStep 2885921 = 2164441) B2164441
theorem B1923947 : Blo 1923435 1923947 := bstep (se 1 (by rfl) ⟨1442960, by rfl⟩ : syracuseStep 1923947 = 2885921) B2885921
theorem B2054533 : Blo 1923435 2054533 := bbase (se 4 (by rfl) ⟨192612, by rfl⟩ : syracuseStep 2054533 = 385225) (by norm_num)
theorem B2739377 : Blo 1923435 2739377 := bstep (se 2 (by rfl) ⟨1027266, by rfl⟩ : syracuseStep 2739377 = 2054533) B2054533
theorem B7305005 : Blo 1923435 7305005 := bstep (se 3 (by rfl) ⟨1369688, by rfl⟩ : syracuseStep 7305005 = 2739377) B2739377
theorem B4870003 : Blo 1923435 4870003 := bstep (se 1 (by rfl) ⟨3652502, by rfl⟩ : syracuseStep 4870003 = 7305005) B7305005
theorem B6493337 : Blo 1923435 6493337 := bstep (se 2 (by rfl) ⟨2435001, by rfl⟩ : syracuseStep 6493337 = 4870003) B4870003
theorem B4328891 : Blo 1923435 4328891 := bstep (se 1 (by rfl) ⟨3246668, by rfl⟩ : syracuseStep 4328891 = 6493337) B6493337
theorem B2885927 : Blo 1923435 2885927 := bstep (se 1 (by rfl) ⟨2164445, by rfl⟩ : syracuseStep 2885927 = 4328891) B4328891
theorem B1923951 : Blo 1923435 1923951 := bstep (se 1 (by rfl) ⟨1442963, by rfl⟩ : syracuseStep 1923951 = 2885927) B2885927
theorem B2885933 : Blo 1923435 2885933 := bbase (se 3 (by rfl) ⟨541112, by rfl⟩ : syracuseStep 2885933 = 1082225) (by norm_num)
theorem B1923955 : Blo 1923435 1923955 := bstep (se 1 (by rfl) ⟨1442966, by rfl⟩ : syracuseStep 1923955 = 2885933) B2885933
theorem B4328909 : Blo 1923435 4328909 := bbase (se 3 (by rfl) ⟨811670, by rfl⟩ : syracuseStep 4328909 = 1623341) (by norm_num)
theorem B2885939 : Blo 1923435 2885939 := bstep (se 1 (by rfl) ⟨2164454, by rfl⟩ : syracuseStep 2885939 = 4328909) B4328909
theorem B1923959 : Blo 1923435 1923959 := bstep (se 1 (by rfl) ⟨1442969, by rfl⟩ : syracuseStep 1923959 = 2885939) B2885939
theorem B2435017 : Blo 1923435 2435017 := bbase (se 2 (by rfl) ⟨913131, by rfl⟩ : syracuseStep 2435017 = 1826263) (by norm_num)
theorem B3246689 : Blo 1923435 3246689 := bstep (se 2 (by rfl) ⟨1217508, by rfl⟩ : syracuseStep 3246689 = 2435017) B2435017
theorem B2164459 : Blo 1923435 2164459 := bstep (se 1 (by rfl) ⟨1623344, by rfl⟩ : syracuseStep 2164459 = 3246689) B3246689
theorem B2885945 : Blo 1923435 2885945 := bstep (se 2 (by rfl) ⟨1082229, by rfl⟩ : syracuseStep 2885945 = 2164459) B2164459
theorem B1923963 : Blo 1923435 1923963 := bstep (se 1 (by rfl) ⟨1442972, by rfl⟩ : syracuseStep 1923963 = 2885945) B2885945
theorem B3467053 : Blo 1923435 3467053 := bbase (se 3 (by rfl) ⟨650072, by rfl⟩ : syracuseStep 3467053 = 1300145) (by norm_num)
theorem B18490949 : Blo 1923435 18490949 := bstep (se 4 (by rfl) ⟨1733526, by rfl⟩ : syracuseStep 18490949 = 3467053) B3467053
theorem B12327299 : Blo 1923435 12327299 := bstep (se 1 (by rfl) ⟨9245474, by rfl⟩ : syracuseStep 12327299 = 18490949) B18490949
theorem B8218199 : Blo 1923435 8218199 := bstep (se 1 (by rfl) ⟨6163649, by rfl⟩ : syracuseStep 8218199 = 12327299) B12327299
theorem B21915197 : Blo 1923435 21915197 := bstep (se 3 (by rfl) ⟨4109099, by rfl⟩ : syracuseStep 21915197 = 8218199) B8218199
theorem B14610131 : Blo 1923435 14610131 := bstep (se 1 (by rfl) ⟨10957598, by rfl⟩ : syracuseStep 14610131 = 21915197) B21915197
theorem B9740087 : Blo 1923435 9740087 := bstep (se 1 (by rfl) ⟨7305065, by rfl⟩ : syracuseStep 9740087 = 14610131) B14610131
theorem B6493391 : Blo 1923435 6493391 := bstep (se 1 (by rfl) ⟨4870043, by rfl⟩ : syracuseStep 6493391 = 9740087) B9740087
theorem B4328927 : Blo 1923435 4328927 := bstep (se 1 (by rfl) ⟨3246695, by rfl⟩ : syracuseStep 4328927 = 6493391) B6493391
theorem B2885951 : Blo 1923435 2885951 := bstep (se 1 (by rfl) ⟨2164463, by rfl⟩ : syracuseStep 2885951 = 4328927) B4328927
theorem B1923967 : Blo 1923435 1923967 := bstep (se 1 (by rfl) ⟨1442975, by rfl⟩ : syracuseStep 1923967 = 2885951) B2885951
theorem B2885957 : Blo 1923435 2885957 := bbase (se 4 (by rfl) ⟨270558, by rfl⟩ : syracuseStep 2885957 = 541117) (by norm_num)
theorem B1923971 : Blo 1923435 1923971 := bstep (se 1 (by rfl) ⟨1442978, by rfl⟩ : syracuseStep 1923971 = 2885957) B2885957
theorem B3246709 : Blo 1923435 3246709 := bbase (se 5 (by rfl) ⟨152189, by rfl⟩ : syracuseStep 3246709 = 304379) (by norm_num)
theorem B4328945 : Blo 1923435 4328945 := bstep (se 2 (by rfl) ⟨1623354, by rfl⟩ : syracuseStep 4328945 = 3246709) B3246709
theorem B2885963 : Blo 1923435 2885963 := bstep (se 1 (by rfl) ⟨2164472, by rfl⟩ : syracuseStep 2885963 = 4328945) B4328945
theorem B1923975 : Blo 1923435 1923975 := bstep (se 1 (by rfl) ⟨1442981, by rfl⟩ : syracuseStep 1923975 = 2885963) B2885963
theorem B2164477 : Blo 1923435 2164477 := bbase (se 3 (by rfl) ⟨405839, by rfl⟩ : syracuseStep 2164477 = 811679) (by norm_num)
theorem B2885969 : Blo 1923435 2885969 := bstep (se 2 (by rfl) ⟨1082238, by rfl⟩ : syracuseStep 2885969 = 2164477) B2164477
theorem B1923979 : Blo 1923435 1923979 := bstep (se 1 (by rfl) ⟨1442984, by rfl⟩ : syracuseStep 1923979 = 2885969) B2885969
theorem B6493445 : Blo 1923435 6493445 := bbase (se 4 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 6493445 = 1217521) (by norm_num)
theorem B4328963 : Blo 1923435 4328963 := bstep (se 1 (by rfl) ⟨3246722, by rfl⟩ : syracuseStep 4328963 = 6493445) B6493445
theorem B2885975 : Blo 1923435 2885975 := bstep (se 1 (by rfl) ⟨2164481, by rfl⟩ : syracuseStep 2885975 = 4328963) B4328963
theorem B1923983 : Blo 1923435 1923983 := bstep (se 1 (by rfl) ⟨1442987, by rfl⟩ : syracuseStep 1923983 = 2885975) B2885975
theorem B2885981 : Blo 1923435 2885981 := bbase (se 3 (by rfl) ⟨541121, by rfl⟩ : syracuseStep 2885981 = 1082243) (by norm_num)
theorem B1923987 : Blo 1923435 1923987 := bstep (se 1 (by rfl) ⟨1442990, by rfl⟩ : syracuseStep 1923987 = 2885981) B2885981
theorem B4328981 : Blo 1923435 4328981 := bbase (se 6 (by rfl) ⟨101460, by rfl⟩ : syracuseStep 4328981 = 202921) (by norm_num)
theorem B2885987 : Blo 1923435 2885987 := bstep (se 1 (by rfl) ⟨2164490, by rfl⟩ : syracuseStep 2885987 = 4328981) B4328981
theorem B1923991 : Blo 1923435 1923991 := bstep (se 1 (by rfl) ⟨1442993, by rfl⟩ : syracuseStep 1923991 = 2885987) B2885987
theorem B7305173 : Blo 1923435 7305173 := bbase (se 7 (by rfl) ⟨85607, by rfl⟩ : syracuseStep 7305173 = 171215) (by norm_num)
theorem B4870115 : Blo 1923435 4870115 := bstep (se 1 (by rfl) ⟨3652586, by rfl⟩ : syracuseStep 4870115 = 7305173) B7305173
theorem B3246743 : Blo 1923435 3246743 := bstep (se 1 (by rfl) ⟨2435057, by rfl⟩ : syracuseStep 3246743 = 4870115) B4870115
theorem B2164495 : Blo 1923435 2164495 := bstep (se 1 (by rfl) ⟨1623371, by rfl⟩ : syracuseStep 2164495 = 3246743) B3246743
theorem B2885993 : Blo 1923435 2885993 := bstep (se 2 (by rfl) ⟨1082247, by rfl⟩ : syracuseStep 2885993 = 2164495) B2164495
theorem B1923995 : Blo 1923435 1923995 := bstep (se 1 (by rfl) ⟨1442996, by rfl⟩ : syracuseStep 1923995 = 2885993) B2885993
theorem B10957781 : Blo 1923435 10957781 := bbase (se 7 (by rfl) ⟨128411, by rfl⟩ : syracuseStep 10957781 = 256823) (by norm_num)
theorem B7305187 : Blo 1923435 7305187 := bstep (se 1 (by rfl) ⟨5478890, by rfl⟩ : syracuseStep 7305187 = 10957781) B10957781
theorem B9740249 : Blo 1923435 9740249 := bstep (se 2 (by rfl) ⟨3652593, by rfl⟩ : syracuseStep 9740249 = 7305187) B7305187
theorem B6493499 : Blo 1923435 6493499 := bstep (se 1 (by rfl) ⟨4870124, by rfl⟩ : syracuseStep 6493499 = 9740249) B9740249
theorem B4328999 : Blo 1923435 4328999 := bstep (se 1 (by rfl) ⟨3246749, by rfl⟩ : syracuseStep 4328999 = 6493499) B6493499
theorem B2885999 : Blo 1923435 2885999 := bstep (se 1 (by rfl) ⟨2164499, by rfl⟩ : syracuseStep 2885999 = 4328999) B4328999
theorem B1923999 : Blo 1923435 1923999 := bstep (se 1 (by rfl) ⟨1442999, by rfl⟩ : syracuseStep 1923999 = 2885999) B2885999
theorem B2886005 : Blo 1923435 2886005 := bbase (se 5 (by rfl) ⟨135281, by rfl⟩ : syracuseStep 2886005 = 270563) (by norm_num)
theorem B1924003 : Blo 1923435 1924003 := bstep (se 1 (by rfl) ⟨1443002, by rfl⟩ : syracuseStep 1924003 = 2886005) B2886005
theorem B2054593 : Blo 1923435 2054593 := bbase (se 2 (by rfl) ⟨770472, by rfl⟩ : syracuseStep 2054593 = 1540945) (by norm_num)
theorem B2739457 : Blo 1923435 2739457 := bstep (se 2 (by rfl) ⟨1027296, by rfl⟩ : syracuseStep 2739457 = 2054593) B2054593
theorem B3652609 : Blo 1923435 3652609 := bstep (se 2 (by rfl) ⟨1369728, by rfl⟩ : syracuseStep 3652609 = 2739457) B2739457
theorem B4870145 : Blo 1923435 4870145 := bstep (se 2 (by rfl) ⟨1826304, by rfl⟩ : syracuseStep 4870145 = 3652609) B3652609
theorem B3246763 : Blo 1923435 3246763 := bstep (se 1 (by rfl) ⟨2435072, by rfl⟩ : syracuseStep 3246763 = 4870145) B4870145
theorem B4329017 : Blo 1923435 4329017 := bstep (se 2 (by rfl) ⟨1623381, by rfl⟩ : syracuseStep 4329017 = 3246763) B3246763
theorem B2886011 : Blo 1923435 2886011 := bstep (se 1 (by rfl) ⟨2164508, by rfl⟩ : syracuseStep 2886011 = 4329017) B4329017
theorem B1924007 : Blo 1923435 1924007 := bstep (se 1 (by rfl) ⟨1443005, by rfl⟩ : syracuseStep 1924007 = 2886011) B2886011
theorem B2164513 : Blo 1923435 2164513 := bbase (se 2 (by rfl) ⟨811692, by rfl⟩ : syracuseStep 2164513 = 1623385) (by norm_num)
theorem B2886017 : Blo 1923435 2886017 := bstep (se 2 (by rfl) ⟨1082256, by rfl⟩ : syracuseStep 2886017 = 2164513) B2164513
theorem B1924011 : Blo 1923435 1924011 := bstep (se 1 (by rfl) ⟨1443008, by rfl⟩ : syracuseStep 1924011 = 2886017) B2886017
theorem B4870165 : Blo 1923435 4870165 := bbase (se 6 (by rfl) ⟨114144, by rfl⟩ : syracuseStep 4870165 = 228289) (by norm_num)
theorem B6493553 : Blo 1923435 6493553 := bstep (se 2 (by rfl) ⟨2435082, by rfl⟩ : syracuseStep 6493553 = 4870165) B4870165
theorem B4329035 : Blo 1923435 4329035 := bstep (se 1 (by rfl) ⟨3246776, by rfl⟩ : syracuseStep 4329035 = 6493553) B6493553
theorem B2886023 : Blo 1923435 2886023 := bstep (se 1 (by rfl) ⟨2164517, by rfl⟩ : syracuseStep 2886023 = 4329035) B4329035
theorem B1924015 : Blo 1923435 1924015 := bstep (se 1 (by rfl) ⟨1443011, by rfl⟩ : syracuseStep 1924015 = 2886023) B2886023
theorem B2886029 : Blo 1923435 2886029 := bbase (se 3 (by rfl) ⟨541130, by rfl⟩ : syracuseStep 2886029 = 1082261) (by norm_num)
theorem B1924019 : Blo 1923435 1924019 := bstep (se 1 (by rfl) ⟨1443014, by rfl⟩ : syracuseStep 1924019 = 2886029) B2886029
theorem B4329053 : Blo 1923435 4329053 := bbase (se 3 (by rfl) ⟨811697, by rfl⟩ : syracuseStep 4329053 = 1623395) (by norm_num)
theorem B2886035 : Blo 1923435 2886035 := bstep (se 1 (by rfl) ⟨2164526, by rfl⟩ : syracuseStep 2886035 = 4329053) B4329053
theorem B1924023 : Blo 1923435 1924023 := bstep (se 1 (by rfl) ⟨1443017, by rfl⟩ : syracuseStep 1924023 = 2886035) B2886035
theorem B3246797 : Blo 1923435 3246797 := bbase (se 3 (by rfl) ⟨608774, by rfl⟩ : syracuseStep 3246797 = 1217549) (by norm_num)
theorem B2164531 : Blo 1923435 2164531 := bstep (se 1 (by rfl) ⟨1623398, by rfl⟩ : syracuseStep 2164531 = 3246797) B3246797
theorem B2886041 : Blo 1923435 2886041 := bstep (se 2 (by rfl) ⟨1082265, by rfl⟩ : syracuseStep 2886041 = 2164531) B2164531
theorem B1924027 : Blo 1923435 1924027 := bstep (se 1 (by rfl) ⟨1443020, by rfl⟩ : syracuseStep 1924027 = 2886041) B2886041
theorem B3900565 : Blo 1923435 3900565 := bbase (se 6 (by rfl) ⟨91419, by rfl⟩ : syracuseStep 3900565 = 182839) (by norm_num)
theorem B5200753 : Blo 1923435 5200753 := bstep (se 2 (by rfl) ⟨1950282, by rfl⟩ : syracuseStep 5200753 = 3900565) B3900565
theorem B6934337 : Blo 1923435 6934337 := bstep (se 2 (by rfl) ⟨2600376, by rfl⟩ : syracuseStep 6934337 = 5200753) B5200753
theorem B4622891 : Blo 1923435 4622891 := bstep (se 1 (by rfl) ⟨3467168, by rfl⟩ : syracuseStep 4622891 = 6934337) B6934337
theorem B12327709 : Blo 1923435 12327709 := bstep (se 3 (by rfl) ⟨2311445, by rfl⟩ : syracuseStep 12327709 = 4622891) B4622891
theorem B16436945 : Blo 1923435 16436945 := bstep (se 2 (by rfl) ⟨6163854, by rfl⟩ : syracuseStep 16436945 = 12327709) B12327709
theorem B10957963 : Blo 1923435 10957963 := bstep (se 1 (by rfl) ⟨8218472, by rfl⟩ : syracuseStep 10957963 = 16436945) B16436945
theorem B14610617 : Blo 1923435 14610617 := bstep (se 2 (by rfl) ⟨5478981, by rfl⟩ : syracuseStep 14610617 = 10957963) B10957963
theorem B9740411 : Blo 1923435 9740411 := bstep (se 1 (by rfl) ⟨7305308, by rfl⟩ : syracuseStep 9740411 = 14610617) B14610617
theorem B6493607 : Blo 1923435 6493607 := bstep (se 1 (by rfl) ⟨4870205, by rfl⟩ : syracuseStep 6493607 = 9740411) B9740411
theorem B4329071 : Blo 1923435 4329071 := bstep (se 1 (by rfl) ⟨3246803, by rfl⟩ : syracuseStep 4329071 = 6493607) B6493607
theorem B2886047 : Blo 1923435 2886047 := bstep (se 1 (by rfl) ⟨2164535, by rfl⟩ : syracuseStep 2886047 = 4329071) B4329071
theorem B1924031 : Blo 1923435 1924031 := bstep (se 1 (by rfl) ⟨1443023, by rfl⟩ : syracuseStep 1924031 = 2886047) B2886047
theorem B2886053 : Blo 1923435 2886053 := bbase (se 4 (by rfl) ⟨270567, by rfl⟩ : syracuseStep 2886053 = 541135) (by norm_num)
theorem B1924035 : Blo 1923435 1924035 := bstep (se 1 (by rfl) ⟨1443026, by rfl⟩ : syracuseStep 1924035 = 2886053) B2886053
theorem B2435113 : Blo 1923435 2435113 := bbase (se 2 (by rfl) ⟨913167, by rfl⟩ : syracuseStep 2435113 = 1826335) (by norm_num)
theorem B3246817 : Blo 1923435 3246817 := bstep (se 2 (by rfl) ⟨1217556, by rfl⟩ : syracuseStep 3246817 = 2435113) B2435113
theorem B4329089 : Blo 1923435 4329089 := bstep (se 2 (by rfl) ⟨1623408, by rfl⟩ : syracuseStep 4329089 = 3246817) B3246817
theorem B2886059 : Blo 1923435 2886059 := bstep (se 1 (by rfl) ⟨2164544, by rfl⟩ : syracuseStep 2886059 = 4329089) B4329089
theorem B1924039 : Blo 1923435 1924039 := bstep (se 1 (by rfl) ⟨1443029, by rfl⟩ : syracuseStep 1924039 = 2886059) B2886059
theorem B2164549 : Blo 1923435 2164549 := bbase (se 4 (by rfl) ⟨202926, by rfl⟩ : syracuseStep 2164549 = 405853) (by norm_num)
theorem B2886065 : Blo 1923435 2886065 := bstep (se 2 (by rfl) ⟨1082274, by rfl⟩ : syracuseStep 2886065 = 2164549) B2164549
theorem B1924043 : Blo 1923435 1924043 := bstep (se 1 (by rfl) ⟨1443032, by rfl⟩ : syracuseStep 1924043 = 2886065) B2886065
theorem B3652685 : Blo 1923435 3652685 := bbase (se 3 (by rfl) ⟨684878, by rfl⟩ : syracuseStep 3652685 = 1369757) (by norm_num)
theorem B2435123 : Blo 1923435 2435123 := bstep (se 1 (by rfl) ⟨1826342, by rfl⟩ : syracuseStep 2435123 = 3652685) B3652685
theorem B6493661 : Blo 1923435 6493661 := bstep (se 3 (by rfl) ⟨1217561, by rfl⟩ : syracuseStep 6493661 = 2435123) B2435123
theorem B4329107 : Blo 1923435 4329107 := bstep (se 1 (by rfl) ⟨3246830, by rfl⟩ : syracuseStep 4329107 = 6493661) B6493661
theorem B2886071 : Blo 1923435 2886071 := bstep (se 1 (by rfl) ⟨2164553, by rfl⟩ : syracuseStep 2886071 = 4329107) B4329107
theorem B1924047 : Blo 1923435 1924047 := bstep (se 1 (by rfl) ⟨1443035, by rfl⟩ : syracuseStep 1924047 = 2886071) B2886071
theorem B2886077 : Blo 1923435 2886077 := bbase (se 3 (by rfl) ⟨541139, by rfl⟩ : syracuseStep 2886077 = 1082279) (by norm_num)
theorem B1924051 : Blo 1923435 1924051 := bstep (se 1 (by rfl) ⟨1443038, by rfl⟩ : syracuseStep 1924051 = 2886077) B2886077
theorem B4329125 : Blo 1923435 4329125 := bbase (se 4 (by rfl) ⟨405855, by rfl⟩ : syracuseStep 4329125 = 811711) (by norm_num)
theorem B2886083 : Blo 1923435 2886083 := bstep (se 1 (by rfl) ⟨2164562, by rfl⟩ : syracuseStep 2886083 = 4329125) B4329125
theorem B1924055 : Blo 1923435 1924055 := bstep (se 1 (by rfl) ⟨1443041, by rfl⟩ : syracuseStep 1924055 = 2886083) B2886083
theorem B4870277 : Blo 1923435 4870277 := bbase (se 4 (by rfl) ⟨456588, by rfl⟩ : syracuseStep 4870277 = 913177) (by norm_num)
theorem B3246851 : Blo 1923435 3246851 := bstep (se 1 (by rfl) ⟨2435138, by rfl⟩ : syracuseStep 3246851 = 4870277) B4870277
theorem B2164567 : Blo 1923435 2164567 := bstep (se 1 (by rfl) ⟨1623425, by rfl⟩ : syracuseStep 2164567 = 3246851) B3246851
theorem B2886089 : Blo 1923435 2886089 := bstep (se 2 (by rfl) ⟨1082283, by rfl⟩ : syracuseStep 2886089 = 2164567) B2164567
theorem B1924059 : Blo 1923435 1924059 := bstep (se 1 (by rfl) ⟨1443044, by rfl⟩ : syracuseStep 1924059 = 2886089) B2886089
theorem B8776421 : Blo 1923435 8776421 := bbase (se 4 (by rfl) ⟨822789, by rfl⟩ : syracuseStep 8776421 = 1645579) (by norm_num)
theorem B5850947 : Blo 1923435 5850947 := bstep (se 1 (by rfl) ⟨4388210, by rfl⟩ : syracuseStep 5850947 = 8776421) B8776421
theorem B3900631 : Blo 1923435 3900631 := bstep (se 1 (by rfl) ⟨2925473, by rfl⟩ : syracuseStep 3900631 = 5850947) B5850947
theorem B5200841 : Blo 1923435 5200841 := bstep (se 2 (by rfl) ⟨1950315, by rfl⟩ : syracuseStep 5200841 = 3900631) B3900631
theorem B3467227 : Blo 1923435 3467227 := bstep (se 1 (by rfl) ⟨2600420, by rfl⟩ : syracuseStep 3467227 = 5200841) B5200841
theorem B4622969 : Blo 1923435 4622969 := bstep (se 2 (by rfl) ⟨1733613, by rfl⟩ : syracuseStep 4622969 = 3467227) B3467227
theorem B3081979 : Blo 1923435 3081979 := bstep (se 1 (by rfl) ⟨2311484, by rfl⟩ : syracuseStep 3081979 = 4622969) B4622969
theorem B4109305 : Blo 1923435 4109305 := bstep (se 2 (by rfl) ⟨1540989, by rfl⟩ : syracuseStep 4109305 = 3081979) B3081979
theorem B5479073 : Blo 1923435 5479073 := bstep (se 2 (by rfl) ⟨2054652, by rfl⟩ : syracuseStep 5479073 = 4109305) B4109305
theorem B3652715 : Blo 1923435 3652715 := bstep (se 1 (by rfl) ⟨2739536, by rfl⟩ : syracuseStep 3652715 = 5479073) B5479073
theorem B9740573 : Blo 1923435 9740573 := bstep (se 3 (by rfl) ⟨1826357, by rfl⟩ : syracuseStep 9740573 = 3652715) B3652715
theorem B6493715 : Blo 1923435 6493715 := bstep (se 1 (by rfl) ⟨4870286, by rfl⟩ : syracuseStep 6493715 = 9740573) B9740573
theorem B4329143 : Blo 1923435 4329143 := bstep (se 1 (by rfl) ⟨3246857, by rfl⟩ : syracuseStep 4329143 = 6493715) B6493715
theorem B2886095 : Blo 1923435 2886095 := bstep (se 1 (by rfl) ⟨2164571, by rfl⟩ : syracuseStep 2886095 = 4329143) B4329143
theorem B1924063 : Blo 1923435 1924063 := bstep (se 1 (by rfl) ⟨1443047, by rfl⟩ : syracuseStep 1924063 = 2886095) B2886095
theorem B2886101 : Blo 1923435 2886101 := bbase (se 7 (by rfl) ⟨33821, by rfl⟩ : syracuseStep 2886101 = 67643) (by norm_num)
theorem B1924067 : Blo 1923435 1924067 := bstep (se 1 (by rfl) ⟨1443050, by rfl⟩ : syracuseStep 1924067 = 2886101) B2886101
theorem B7305461 : Blo 1923435 7305461 := bbase (se 5 (by rfl) ⟨342443, by rfl⟩ : syracuseStep 7305461 = 684887) (by norm_num)
theorem B4870307 : Blo 1923435 4870307 := bstep (se 1 (by rfl) ⟨3652730, by rfl⟩ : syracuseStep 4870307 = 7305461) B7305461
theorem B3246871 : Blo 1923435 3246871 := bstep (se 1 (by rfl) ⟨2435153, by rfl⟩ : syracuseStep 3246871 = 4870307) B4870307
theorem B4329161 : Blo 1923435 4329161 := bstep (se 2 (by rfl) ⟨1623435, by rfl⟩ : syracuseStep 4329161 = 3246871) B3246871
theorem B2886107 : Blo 1923435 2886107 := bstep (se 1 (by rfl) ⟨2164580, by rfl⟩ : syracuseStep 2886107 = 4329161) B4329161
theorem B1924071 : Blo 1923435 1924071 := bstep (se 1 (by rfl) ⟨1443053, by rfl⟩ : syracuseStep 1924071 = 2886107) B2886107
theorem B2164585 : Blo 1923435 2164585 := bbase (se 2 (by rfl) ⟨811719, by rfl⟩ : syracuseStep 2164585 = 1623439) (by norm_num)
theorem B2886113 : Blo 1923435 2886113 := bstep (se 2 (by rfl) ⟨1082292, by rfl⟩ : syracuseStep 2886113 = 2164585) B2164585
theorem B1924075 : Blo 1923435 1924075 := bstep (se 1 (by rfl) ⟨1443056, by rfl⟩ : syracuseStep 1924075 = 2886113) B2886113
theorem B7029125 : Blo 1923435 7029125 := bbase (se 4 (by rfl) ⟨658980, by rfl⟩ : syracuseStep 7029125 = 1317961) (by norm_num)
theorem B4686083 : Blo 1923435 4686083 := bstep (se 1 (by rfl) ⟨3514562, by rfl⟩ : syracuseStep 4686083 = 7029125) B7029125
theorem B3124055 : Blo 1923435 3124055 := bstep (se 1 (by rfl) ⟨2343041, by rfl⟩ : syracuseStep 3124055 = 4686083) B4686083
theorem B2082703 : Blo 1923435 2082703 := bstep (se 1 (by rfl) ⟨1562027, by rfl⟩ : syracuseStep 2082703 = 3124055) B3124055
theorem B2776937 : Blo 1923435 2776937 := bstep (se 2 (by rfl) ⟨1041351, by rfl⟩ : syracuseStep 2776937 = 2082703) B2082703
theorem B7405165 : Blo 1923435 7405165 := bstep (se 3 (by rfl) ⟨1388468, by rfl⟩ : syracuseStep 7405165 = 2776937) B2776937
theorem B39494213 : Blo 1923435 39494213 := bstep (se 4 (by rfl) ⟨3702582, by rfl⟩ : syracuseStep 39494213 = 7405165) B7405165
theorem B26329475 : Blo 1923435 26329475 := bstep (se 1 (by rfl) ⟨19747106, by rfl⟩ : syracuseStep 26329475 = 39494213) B39494213
theorem B17552983 : Blo 1923435 17552983 := bstep (se 1 (by rfl) ⟨13164737, by rfl⟩ : syracuseStep 17552983 = 26329475) B26329475
theorem B23403977 : Blo 1923435 23403977 := bstep (se 2 (by rfl) ⟨8776491, by rfl⟩ : syracuseStep 23403977 = 17552983) B17552983
theorem B15602651 : Blo 1923435 15602651 := bstep (se 1 (by rfl) ⟨11701988, by rfl⟩ : syracuseStep 15602651 = 23403977) B23403977
theorem B10401767 : Blo 1923435 10401767 := bstep (se 1 (by rfl) ⟨7801325, by rfl⟩ : syracuseStep 10401767 = 15602651) B15602651
theorem B6934511 : Blo 1923435 6934511 := bstep (se 1 (by rfl) ⟨5200883, by rfl⟩ : syracuseStep 6934511 = 10401767) B10401767
theorem B4623007 : Blo 1923435 4623007 := bstep (se 1 (by rfl) ⟨3467255, by rfl⟩ : syracuseStep 4623007 = 6934511) B6934511
theorem B6164009 : Blo 1923435 6164009 := bstep (se 2 (by rfl) ⟨2311503, by rfl⟩ : syracuseStep 6164009 = 4623007) B4623007
theorem B4109339 : Blo 1923435 4109339 := bstep (se 1 (by rfl) ⟨3082004, by rfl⟩ : syracuseStep 4109339 = 6164009) B6164009
theorem B10958237 : Blo 1923435 10958237 := bstep (se 3 (by rfl) ⟨2054669, by rfl⟩ : syracuseStep 10958237 = 4109339) B4109339
theorem B7305491 : Blo 1923435 7305491 := bstep (se 1 (by rfl) ⟨5479118, by rfl⟩ : syracuseStep 7305491 = 10958237) B10958237
theorem B4870327 : Blo 1923435 4870327 := bstep (se 1 (by rfl) ⟨3652745, by rfl⟩ : syracuseStep 4870327 = 7305491) B7305491
theorem B6493769 : Blo 1923435 6493769 := bstep (se 2 (by rfl) ⟨2435163, by rfl⟩ : syracuseStep 6493769 = 4870327) B4870327
theorem B4329179 : Blo 1923435 4329179 := bstep (se 1 (by rfl) ⟨3246884, by rfl⟩ : syracuseStep 4329179 = 6493769) B6493769
theorem B2886119 : Blo 1923435 2886119 := bstep (se 1 (by rfl) ⟨2164589, by rfl⟩ : syracuseStep 2886119 = 4329179) B4329179
theorem B1924079 : Blo 1923435 1924079 := bstep (se 1 (by rfl) ⟨1443059, by rfl⟩ : syracuseStep 1924079 = 2886119) B2886119
theorem B2886125 : Blo 1923435 2886125 := bbase (se 3 (by rfl) ⟨541148, by rfl⟩ : syracuseStep 2886125 = 1082297) (by norm_num)
theorem B1924083 : Blo 1923435 1924083 := bstep (se 1 (by rfl) ⟨1443062, by rfl⟩ : syracuseStep 1924083 = 2886125) B2886125
theorem B4329197 : Blo 1923435 4329197 := bbase (se 3 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 4329197 = 1623449) (by norm_num)
theorem B2886131 : Blo 1923435 2886131 := bstep (se 1 (by rfl) ⟨2164598, by rfl⟩ : syracuseStep 2886131 = 4329197) B4329197
theorem B1924087 : Blo 1923435 1924087 := bstep (se 1 (by rfl) ⟨1443065, by rfl⟩ : syracuseStep 1924087 = 2886131) B2886131
theorem B11702069 : Blo 1923435 11702069 := bbase (se 5 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 11702069 = 1097069) (by norm_num)
theorem B7801379 : Blo 1923435 7801379 := bstep (se 1 (by rfl) ⟨5851034, by rfl⟩ : syracuseStep 7801379 = 11702069) B11702069
theorem B5200919 : Blo 1923435 5200919 := bstep (se 1 (by rfl) ⟨3900689, by rfl⟩ : syracuseStep 5200919 = 7801379) B7801379
theorem B3467279 : Blo 1923435 3467279 := bstep (se 1 (by rfl) ⟨2600459, by rfl⟩ : syracuseStep 3467279 = 5200919) B5200919
theorem B2311519 : Blo 1923435 2311519 := bstep (se 1 (by rfl) ⟨1733639, by rfl⟩ : syracuseStep 2311519 = 3467279) B3467279
theorem B3082025 : Blo 1923435 3082025 := bstep (se 2 (by rfl) ⟨1155759, by rfl⟩ : syracuseStep 3082025 = 2311519) B2311519
theorem B2054683 : Blo 1923435 2054683 := bstep (se 1 (by rfl) ⟨1541012, by rfl⟩ : syracuseStep 2054683 = 3082025) B3082025
theorem B2739577 : Blo 1923435 2739577 := bstep (se 2 (by rfl) ⟨1027341, by rfl⟩ : syracuseStep 2739577 = 2054683) B2054683
theorem B3652769 : Blo 1923435 3652769 := bstep (se 2 (by rfl) ⟨1369788, by rfl⟩ : syracuseStep 3652769 = 2739577) B2739577
theorem B2435179 : Blo 1923435 2435179 := bstep (se 1 (by rfl) ⟨1826384, by rfl⟩ : syracuseStep 2435179 = 3652769) B3652769
theorem B3246905 : Blo 1923435 3246905 := bstep (se 2 (by rfl) ⟨1217589, by rfl⟩ : syracuseStep 3246905 = 2435179) B2435179
theorem B2164603 : Blo 1923435 2164603 := bstep (se 1 (by rfl) ⟨1623452, by rfl⟩ : syracuseStep 2164603 = 3246905) B3246905
theorem B2886137 : Blo 1923435 2886137 := bstep (se 2 (by rfl) ⟨1082301, by rfl⟩ : syracuseStep 2886137 = 2164603) B2164603
theorem B1924091 : Blo 1923435 1924091 := bstep (se 1 (by rfl) ⟨1443068, by rfl⟩ : syracuseStep 1924091 = 2886137) B2886137
theorem B16889077 : Blo 1923435 16889077 := bbase (se 5 (by rfl) ⟨791675, by rfl⟩ : syracuseStep 16889077 = 1583351) (by norm_num)
theorem B22518769 : Blo 1923435 22518769 := bstep (se 2 (by rfl) ⟨8444538, by rfl⟩ : syracuseStep 22518769 = 16889077) B16889077
theorem B30025025 : Blo 1923435 30025025 := bstep (se 2 (by rfl) ⟨11259384, by rfl⟩ : syracuseStep 30025025 = 22518769) B22518769
theorem B20016683 : Blo 1923435 20016683 := bstep (se 1 (by rfl) ⟨15012512, by rfl⟩ : syracuseStep 20016683 = 30025025) B30025025
theorem B13344455 : Blo 1923435 13344455 := bstep (se 1 (by rfl) ⟨10008341, by rfl⟩ : syracuseStep 13344455 = 20016683) B20016683
theorem B8896303 : Blo 1923435 8896303 := bstep (se 1 (by rfl) ⟨6672227, by rfl⟩ : syracuseStep 8896303 = 13344455) B13344455
theorem B11861737 : Blo 1923435 11861737 := bstep (se 2 (by rfl) ⟨4448151, by rfl⟩ : syracuseStep 11861737 = 8896303) B8896303
theorem B253050389 : Blo 1923435 253050389 := bstep (se 6 (by rfl) ⟨5930868, by rfl⟩ : syracuseStep 253050389 = 11861737) B11861737
theorem B168700259 : Blo 1923435 168700259 := bstep (se 1 (by rfl) ⟨126525194, by rfl⟩ : syracuseStep 168700259 = 253050389) B253050389
theorem B112466839 : Blo 1923435 112466839 := bstep (se 1 (by rfl) ⟨84350129, by rfl⟩ : syracuseStep 112466839 = 168700259) B168700259
theorem B149955785 : Blo 1923435 149955785 := bstep (se 2 (by rfl) ⟨56233419, by rfl⟩ : syracuseStep 149955785 = 112466839) B112466839
theorem B99970523 : Blo 1923435 99970523 := bstep (se 1 (by rfl) ⟨74977892, by rfl⟩ : syracuseStep 99970523 = 149955785) B149955785
theorem B66647015 : Blo 1923435 66647015 := bstep (se 1 (by rfl) ⟨49985261, by rfl⟩ : syracuseStep 66647015 = 99970523) B99970523
theorem B44431343 : Blo 1923435 44431343 := bstep (se 1 (by rfl) ⟨33323507, by rfl⟩ : syracuseStep 44431343 = 66647015) B66647015
theorem B29620895 : Blo 1923435 29620895 := bstep (se 1 (by rfl) ⟨22215671, by rfl⟩ : syracuseStep 29620895 = 44431343) B44431343
theorem B78989053 : Blo 1923435 78989053 := bstep (se 3 (by rfl) ⟨14810447, by rfl⟩ : syracuseStep 78989053 = 29620895) B29620895
theorem B105318737 : Blo 1923435 105318737 := bstep (se 2 (by rfl) ⟨39494526, by rfl⟩ : syracuseStep 105318737 = 78989053) B78989053
theorem B70212491 : Blo 1923435 70212491 := bstep (se 1 (by rfl) ⟨52659368, by rfl⟩ : syracuseStep 70212491 = 105318737) B105318737
theorem B46808327 : Blo 1923435 46808327 := bstep (se 1 (by rfl) ⟨35106245, by rfl⟩ : syracuseStep 46808327 = 70212491) B70212491
theorem B124822205 : Blo 1923435 124822205 := bstep (se 3 (by rfl) ⟨23404163, by rfl⟩ : syracuseStep 124822205 = 46808327) B46808327
theorem B83214803 : Blo 1923435 83214803 := bstep (se 1 (by rfl) ⟨62411102, by rfl⟩ : syracuseStep 83214803 = 124822205) B124822205
theorem B55476535 : Blo 1923435 55476535 := bstep (se 1 (by rfl) ⟨41607401, by rfl⟩ : syracuseStep 55476535 = 83214803) B83214803
theorem B73968713 : Blo 1923435 73968713 := bstep (se 2 (by rfl) ⟨27738267, by rfl⟩ : syracuseStep 73968713 = 55476535) B55476535
theorem B49312475 : Blo 1923435 49312475 := bstep (se 1 (by rfl) ⟨36984356, by rfl⟩ : syracuseStep 49312475 = 73968713) B73968713
theorem B32874983 : Blo 1923435 32874983 := bstep (se 1 (by rfl) ⟨24656237, by rfl⟩ : syracuseStep 32874983 = 49312475) B49312475
theorem B21916655 : Blo 1923435 21916655 := bstep (se 1 (by rfl) ⟨16437491, by rfl⟩ : syracuseStep 21916655 = 32874983) B32874983
theorem B14611103 : Blo 1923435 14611103 := bstep (se 1 (by rfl) ⟨10958327, by rfl⟩ : syracuseStep 14611103 = 21916655) B21916655
theorem B9740735 : Blo 1923435 9740735 := bstep (se 1 (by rfl) ⟨7305551, by rfl⟩ : syracuseStep 9740735 = 14611103) B14611103
theorem B6493823 : Blo 1923435 6493823 := bstep (se 1 (by rfl) ⟨4870367, by rfl⟩ : syracuseStep 6493823 = 9740735) B9740735
theorem B4329215 : Blo 1923435 4329215 := bstep (se 1 (by rfl) ⟨3246911, by rfl⟩ : syracuseStep 4329215 = 6493823) B6493823
theorem B2886143 : Blo 1923435 2886143 := bstep (se 1 (by rfl) ⟨2164607, by rfl⟩ : syracuseStep 2886143 = 4329215) B4329215
theorem B1924095 : Blo 1923435 1924095 := bstep (se 1 (by rfl) ⟨1443071, by rfl⟩ : syracuseStep 1924095 = 2886143) B2886143
theorem B2886149 : Blo 1923435 2886149 := bbase (se 4 (by rfl) ⟨270576, by rfl⟩ : syracuseStep 2886149 = 541153) (by norm_num)
theorem B1924099 : Blo 1923435 1924099 := bstep (se 1 (by rfl) ⟨1443074, by rfl⟩ : syracuseStep 1924099 = 2886149) B2886149
theorem B3246925 : Blo 1923435 3246925 := bbase (se 3 (by rfl) ⟨608798, by rfl⟩ : syracuseStep 3246925 = 1217597) (by norm_num)
theorem B4329233 : Blo 1923435 4329233 := bstep (se 2 (by rfl) ⟨1623462, by rfl⟩ : syracuseStep 4329233 = 3246925) B3246925
theorem B2886155 : Blo 1923435 2886155 := bstep (se 1 (by rfl) ⟨2164616, by rfl⟩ : syracuseStep 2886155 = 4329233) B4329233
theorem B1924103 : Blo 1923435 1924103 := bstep (se 1 (by rfl) ⟨1443077, by rfl⟩ : syracuseStep 1924103 = 2886155) B2886155
theorem B2164621 : Blo 1923435 2164621 := bbase (se 3 (by rfl) ⟨405866, by rfl⟩ : syracuseStep 2164621 = 811733) (by norm_num)
theorem B2886161 : Blo 1923435 2886161 := bstep (se 2 (by rfl) ⟨1082310, by rfl⟩ : syracuseStep 2886161 = 2164621) B2164621
theorem B1924107 : Blo 1923435 1924107 := bstep (se 1 (by rfl) ⟨1443080, by rfl⟩ : syracuseStep 1924107 = 2886161) B2886161
theorem B6493877 : Blo 1923435 6493877 := bbase (se 5 (by rfl) ⟨304400, by rfl⟩ : syracuseStep 6493877 = 608801) (by norm_num)
theorem B4329251 : Blo 1923435 4329251 := bstep (se 1 (by rfl) ⟨3246938, by rfl⟩ : syracuseStep 4329251 = 6493877) B6493877
theorem B2886167 : Blo 1923435 2886167 := bstep (se 1 (by rfl) ⟨2164625, by rfl⟩ : syracuseStep 2886167 = 4329251) B4329251
theorem B1924111 : Blo 1923435 1924111 := bstep (se 1 (by rfl) ⟨1443083, by rfl⟩ : syracuseStep 1924111 = 2886167) B2886167
theorem B2886173 : Blo 1923435 2886173 := bbase (se 3 (by rfl) ⟨541157, by rfl⟩ : syracuseStep 2886173 = 1082315) (by norm_num)
theorem B1924115 : Blo 1923435 1924115 := bstep (se 1 (by rfl) ⟨1443086, by rfl⟩ : syracuseStep 1924115 = 2886173) B2886173
theorem B4329269 : Blo 1923435 4329269 := bbase (se 5 (by rfl) ⟨202934, by rfl⟩ : syracuseStep 4329269 = 405869) (by norm_num)
theorem B2886179 : Blo 1923435 2886179 := bstep (se 1 (by rfl) ⟨2164634, by rfl⟩ : syracuseStep 2886179 = 4329269) B4329269
theorem B1924119 : Blo 1923435 1924119 := bstep (se 1 (by rfl) ⟨1443089, by rfl⟩ : syracuseStep 1924119 = 2886179) B2886179
theorem B17792885 : Blo 1923435 17792885 := bbase (se 5 (by rfl) ⟨834041, by rfl⟩ : syracuseStep 17792885 = 1668083) (by norm_num)
theorem B11861923 : Blo 1923435 11861923 := bstep (se 1 (by rfl) ⟨8896442, by rfl⟩ : syracuseStep 11861923 = 17792885) B17792885
theorem B15815897 : Blo 1923435 15815897 := bstep (se 2 (by rfl) ⟨5930961, by rfl⟩ : syracuseStep 15815897 = 11861923) B11861923
theorem B10543931 : Blo 1923435 10543931 := bstep (se 1 (by rfl) ⟨7907948, by rfl⟩ : syracuseStep 10543931 = 15815897) B15815897
theorem B7029287 : Blo 1923435 7029287 := bstep (se 1 (by rfl) ⟨5271965, by rfl⟩ : syracuseStep 7029287 = 10543931) B10543931
theorem B4686191 : Blo 1923435 4686191 := bstep (se 1 (by rfl) ⟨3514643, by rfl⟩ : syracuseStep 4686191 = 7029287) B7029287
theorem B3124127 : Blo 1923435 3124127 := bstep (se 1 (by rfl) ⟨2343095, by rfl⟩ : syracuseStep 3124127 = 4686191) B4686191
theorem B8331005 : Blo 1923435 8331005 := bstep (se 3 (by rfl) ⟨1562063, by rfl⟩ : syracuseStep 8331005 = 3124127) B3124127
theorem B5554003 : Blo 1923435 5554003 := bstep (se 1 (by rfl) ⟨4165502, by rfl⟩ : syracuseStep 5554003 = 8331005) B8331005
theorem B7405337 : Blo 1923435 7405337 := bstep (se 2 (by rfl) ⟨2777001, by rfl⟩ : syracuseStep 7405337 = 5554003) B5554003
theorem B4936891 : Blo 1923435 4936891 := bstep (se 1 (by rfl) ⟨3702668, by rfl⟩ : syracuseStep 4936891 = 7405337) B7405337
theorem B6582521 : Blo 1923435 6582521 := bstep (se 2 (by rfl) ⟨2468445, by rfl⟩ : syracuseStep 6582521 = 4936891) B4936891
theorem B4388347 : Blo 1923435 4388347 := bstep (se 1 (by rfl) ⟨3291260, by rfl⟩ : syracuseStep 4388347 = 6582521) B6582521
theorem B5851129 : Blo 1923435 5851129 := bstep (se 2 (by rfl) ⟨2194173, by rfl⟩ : syracuseStep 5851129 = 4388347) B4388347
theorem B7801505 : Blo 1923435 7801505 := bstep (se 2 (by rfl) ⟨2925564, by rfl⟩ : syracuseStep 7801505 = 5851129) B5851129
theorem B5201003 : Blo 1923435 5201003 := bstep (se 1 (by rfl) ⟨3900752, by rfl⟩ : syracuseStep 5201003 = 7801505) B7801505
theorem B3467335 : Blo 1923435 3467335 := bstep (se 1 (by rfl) ⟨2600501, by rfl⟩ : syracuseStep 3467335 = 5201003) B5201003
theorem B4623113 : Blo 1923435 4623113 := bstep (se 2 (by rfl) ⟨1733667, by rfl⟩ : syracuseStep 4623113 = 3467335) B3467335
theorem B12328301 : Blo 1923435 12328301 := bstep (se 3 (by rfl) ⟨2311556, by rfl⟩ : syracuseStep 12328301 = 4623113) B4623113
theorem B8218867 : Blo 1923435 8218867 := bstep (se 1 (by rfl) ⟨6164150, by rfl⟩ : syracuseStep 8218867 = 12328301) B12328301
theorem B10958489 : Blo 1923435 10958489 := bstep (se 2 (by rfl) ⟨4109433, by rfl⟩ : syracuseStep 10958489 = 8218867) B8218867
theorem B7305659 : Blo 1923435 7305659 := bstep (se 1 (by rfl) ⟨5479244, by rfl⟩ : syracuseStep 7305659 = 10958489) B10958489
theorem B4870439 : Blo 1923435 4870439 := bstep (se 1 (by rfl) ⟨3652829, by rfl⟩ : syracuseStep 4870439 = 7305659) B7305659
theorem B3246959 : Blo 1923435 3246959 := bstep (se 1 (by rfl) ⟨2435219, by rfl⟩ : syracuseStep 3246959 = 4870439) B4870439
theorem B2164639 : Blo 1923435 2164639 := bstep (se 1 (by rfl) ⟨1623479, by rfl⟩ : syracuseStep 2164639 = 3246959) B3246959
theorem B2886185 : Blo 1923435 2886185 := bstep (se 2 (by rfl) ⟨1082319, by rfl⟩ : syracuseStep 2886185 = 2164639) B2164639
theorem B1924123 : Blo 1923435 1924123 := bstep (se 1 (by rfl) ⟨1443092, by rfl⟩ : syracuseStep 1924123 = 2886185) B2886185
theorem B2311561 : Blo 1923435 2311561 := bbase (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) (by norm_num)
theorem B12328325 : Blo 1923435 12328325 := bstep (se 4 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 12328325 = 2311561) B2311561
theorem B8218883 : Blo 1923435 8218883 := bstep (se 1 (by rfl) ⟨6164162, by rfl⟩ : syracuseStep 8218883 = 12328325) B12328325
theorem B5479255 : Blo 1923435 5479255 := bstep (se 1 (by rfl) ⟨4109441, by rfl⟩ : syracuseStep 5479255 = 8218883) B8218883
theorem B7305673 : Blo 1923435 7305673 := bstep (se 2 (by rfl) ⟨2739627, by rfl⟩ : syracuseStep 7305673 = 5479255) B5479255
theorem B9740897 : Blo 1923435 9740897 := bstep (se 2 (by rfl) ⟨3652836, by rfl⟩ : syracuseStep 9740897 = 7305673) B7305673
theorem B6493931 : Blo 1923435 6493931 := bstep (se 1 (by rfl) ⟨4870448, by rfl⟩ : syracuseStep 6493931 = 9740897) B9740897
theorem B4329287 : Blo 1923435 4329287 := bstep (se 1 (by rfl) ⟨3246965, by rfl⟩ : syracuseStep 4329287 = 6493931) B6493931
theorem B2886191 : Blo 1923435 2886191 := bstep (se 1 (by rfl) ⟨2164643, by rfl⟩ : syracuseStep 2886191 = 4329287) B4329287
theorem B1924127 : Blo 1923435 1924127 := bstep (se 1 (by rfl) ⟨1443095, by rfl⟩ : syracuseStep 1924127 = 2886191) B2886191
theorem B2886197 : Blo 1923435 2886197 := bbase (se 5 (by rfl) ⟨135290, by rfl⟩ : syracuseStep 2886197 = 270581) (by norm_num)
theorem B1924131 : Blo 1923435 1924131 := bstep (se 1 (by rfl) ⟨1443098, by rfl⟩ : syracuseStep 1924131 = 2886197) B2886197
theorem B4870469 : Blo 1923435 4870469 := bbase (se 4 (by rfl) ⟨456606, by rfl⟩ : syracuseStep 4870469 = 913213) (by norm_num)
theorem B3246979 : Blo 1923435 3246979 := bstep (se 1 (by rfl) ⟨2435234, by rfl⟩ : syracuseStep 3246979 = 4870469) B4870469
theorem B4329305 : Blo 1923435 4329305 := bstep (se 2 (by rfl) ⟨1623489, by rfl⟩ : syracuseStep 4329305 = 3246979) B3246979
theorem B2886203 : Blo 1923435 2886203 := bstep (se 1 (by rfl) ⟨2164652, by rfl⟩ : syracuseStep 2886203 = 4329305) B4329305
theorem B1924135 : Blo 1923435 1924135 := bstep (se 1 (by rfl) ⟨1443101, by rfl⟩ : syracuseStep 1924135 = 2886203) B2886203
theorem B2164657 : Blo 1923435 2164657 := bbase (se 2 (by rfl) ⟨811746, by rfl⟩ : syracuseStep 2164657 = 1623493) (by norm_num)
theorem B2886209 : Blo 1923435 2886209 := bstep (se 2 (by rfl) ⟨1082328, by rfl⟩ : syracuseStep 2886209 = 2164657) B2164657
theorem B1924139 : Blo 1923435 1924139 := bstep (se 1 (by rfl) ⟨1443104, by rfl⟩ : syracuseStep 1924139 = 2886209) B2886209
theorem B5479301 : Blo 1923435 5479301 := bbase (se 4 (by rfl) ⟨513684, by rfl⟩ : syracuseStep 5479301 = 1027369) (by norm_num)
theorem B3652867 : Blo 1923435 3652867 := bstep (se 1 (by rfl) ⟨2739650, by rfl⟩ : syracuseStep 3652867 = 5479301) B5479301
theorem B4870489 : Blo 1923435 4870489 := bstep (se 2 (by rfl) ⟨1826433, by rfl⟩ : syracuseStep 4870489 = 3652867) B3652867
theorem B6493985 : Blo 1923435 6493985 := bstep (se 2 (by rfl) ⟨2435244, by rfl⟩ : syracuseStep 6493985 = 4870489) B4870489
theorem B4329323 : Blo 1923435 4329323 := bstep (se 1 (by rfl) ⟨3246992, by rfl⟩ : syracuseStep 4329323 = 6493985) B6493985
theorem B2886215 : Blo 1923435 2886215 := bstep (se 1 (by rfl) ⟨2164661, by rfl⟩ : syracuseStep 2886215 = 4329323) B4329323
theorem B1924143 : Blo 1923435 1924143 := bstep (se 1 (by rfl) ⟨1443107, by rfl⟩ : syracuseStep 1924143 = 2886215) B2886215
theorem B2886221 : Blo 1923435 2886221 := bbase (se 3 (by rfl) ⟨541166, by rfl⟩ : syracuseStep 2886221 = 1082333) (by norm_num)
theorem B1924147 : Blo 1923435 1924147 := bstep (se 1 (by rfl) ⟨1443110, by rfl⟩ : syracuseStep 1924147 = 2886221) B2886221
theorem B4329341 : Blo 1923435 4329341 := bbase (se 3 (by rfl) ⟨811751, by rfl⟩ : syracuseStep 4329341 = 1623503) (by norm_num)
theorem B2886227 : Blo 1923435 2886227 := bstep (se 1 (by rfl) ⟨2164670, by rfl⟩ : syracuseStep 2886227 = 4329341) B4329341
theorem B1924151 : Blo 1923435 1924151 := bstep (se 1 (by rfl) ⟨1443113, by rfl⟩ : syracuseStep 1924151 = 2886227) B2886227
theorem B3247013 : Blo 1923435 3247013 := bbase (se 4 (by rfl) ⟨304407, by rfl⟩ : syracuseStep 3247013 = 608815) (by norm_num)
theorem B2164675 : Blo 1923435 2164675 := bstep (se 1 (by rfl) ⟨1623506, by rfl⟩ : syracuseStep 2164675 = 3247013) B3247013
theorem B2886233 : Blo 1923435 2886233 := bstep (se 2 (by rfl) ⟨1082337, by rfl⟩ : syracuseStep 2886233 = 2164675) B2164675
theorem B1924155 : Blo 1923435 1924155 := bstep (se 1 (by rfl) ⟨1443116, by rfl⟩ : syracuseStep 1924155 = 2886233) B2886233
theorem B3082133 : Blo 1923435 3082133 := bbase (se 6 (by rfl) ⟨72237, by rfl⟩ : syracuseStep 3082133 = 144475) (by norm_num)
theorem B2054755 : Blo 1923435 2054755 := bstep (se 1 (by rfl) ⟨1541066, by rfl⟩ : syracuseStep 2054755 = 3082133) B3082133
theorem B2739673 : Blo 1923435 2739673 := bstep (se 2 (by rfl) ⟨1027377, by rfl⟩ : syracuseStep 2739673 = 2054755) B2054755
theorem B14611589 : Blo 1923435 14611589 := bstep (se 4 (by rfl) ⟨1369836, by rfl⟩ : syracuseStep 14611589 = 2739673) B2739673
theorem B9741059 : Blo 1923435 9741059 := bstep (se 1 (by rfl) ⟨7305794, by rfl⟩ : syracuseStep 9741059 = 14611589) B14611589
theorem B6494039 : Blo 1923435 6494039 := bstep (se 1 (by rfl) ⟨4870529, by rfl⟩ : syracuseStep 6494039 = 9741059) B9741059
theorem B4329359 : Blo 1923435 4329359 := bstep (se 1 (by rfl) ⟨3247019, by rfl⟩ : syracuseStep 4329359 = 6494039) B6494039
theorem B2886239 : Blo 1923435 2886239 := bstep (se 1 (by rfl) ⟨2164679, by rfl⟩ : syracuseStep 2886239 = 4329359) B4329359
theorem B1924159 : Blo 1923435 1924159 := bstep (se 1 (by rfl) ⟨1443119, by rfl⟩ : syracuseStep 1924159 = 2886239) B2886239
theorem B2886245 : Blo 1923435 2886245 := bbase (se 4 (by rfl) ⟨270585, by rfl⟩ : syracuseStep 2886245 = 541171) (by norm_num)
theorem B1924163 : Blo 1923435 1924163 := bstep (se 1 (by rfl) ⟨1443122, by rfl⟩ : syracuseStep 1924163 = 2886245) B2886245
theorem B2739685 : Blo 1923435 2739685 := bbase (se 4 (by rfl) ⟨256845, by rfl⟩ : syracuseStep 2739685 = 513691) (by norm_num)
theorem B3652913 : Blo 1923435 3652913 := bstep (se 2 (by rfl) ⟨1369842, by rfl⟩ : syracuseStep 3652913 = 2739685) B2739685
theorem B2435275 : Blo 1923435 2435275 := bstep (se 1 (by rfl) ⟨1826456, by rfl⟩ : syracuseStep 2435275 = 3652913) B3652913
theorem B3247033 : Blo 1923435 3247033 := bstep (se 2 (by rfl) ⟨1217637, by rfl⟩ : syracuseStep 3247033 = 2435275) B2435275
theorem B4329377 : Blo 1923435 4329377 := bstep (se 2 (by rfl) ⟨1623516, by rfl⟩ : syracuseStep 4329377 = 3247033) B3247033
theorem B2886251 : Blo 1923435 2886251 := bstep (se 1 (by rfl) ⟨2164688, by rfl⟩ : syracuseStep 2886251 = 4329377) B4329377
theorem B1924167 : Blo 1923435 1924167 := bstep (se 1 (by rfl) ⟨1443125, by rfl⟩ : syracuseStep 1924167 = 2886251) B2886251
theorem B2164693 : Blo 1923435 2164693 := bbase (se 7 (by rfl) ⟨25367, by rfl⟩ : syracuseStep 2164693 = 50735) (by norm_num)
theorem B2886257 : Blo 1923435 2886257 := bstep (se 2 (by rfl) ⟨1082346, by rfl⟩ : syracuseStep 2886257 = 2164693) B2164693
theorem B1924171 : Blo 1923435 1924171 := bstep (se 1 (by rfl) ⟨1443128, by rfl⟩ : syracuseStep 1924171 = 2886257) B2886257
theorem B2435285 : Blo 1923435 2435285 := bbase (se 7 (by rfl) ⟨28538, by rfl⟩ : syracuseStep 2435285 = 57077) (by norm_num)
theorem B6494093 : Blo 1923435 6494093 := bstep (se 3 (by rfl) ⟨1217642, by rfl⟩ : syracuseStep 6494093 = 2435285) B2435285
theorem B4329395 : Blo 1923435 4329395 := bstep (se 1 (by rfl) ⟨3247046, by rfl⟩ : syracuseStep 4329395 = 6494093) B6494093
theorem B2886263 : Blo 1923435 2886263 := bstep (se 1 (by rfl) ⟨2164697, by rfl⟩ : syracuseStep 2886263 = 4329395) B4329395
theorem B1924175 : Blo 1923435 1924175 := bstep (se 1 (by rfl) ⟨1443131, by rfl⟩ : syracuseStep 1924175 = 2886263) B2886263
theorem B2886269 : Blo 1923435 2886269 := bbase (se 3 (by rfl) ⟨541175, by rfl⟩ : syracuseStep 2886269 = 1082351) (by norm_num)
theorem B1924179 : Blo 1923435 1924179 := bstep (se 1 (by rfl) ⟨1443134, by rfl⟩ : syracuseStep 1924179 = 2886269) B2886269
theorem B4329413 : Blo 1923435 4329413 := bbase (se 4 (by rfl) ⟨405882, by rfl⟩ : syracuseStep 4329413 = 811765) (by norm_num)
theorem B2886275 : Blo 1923435 2886275 := bstep (se 1 (by rfl) ⟨2164706, by rfl⟩ : syracuseStep 2886275 = 4329413) B4329413
theorem B1924183 : Blo 1923435 1924183 := bstep (se 1 (by rfl) ⟨1443137, by rfl⟩ : syracuseStep 1924183 = 2886275) B2886275
theorem B8219141 : Blo 1923435 8219141 := bbase (se 4 (by rfl) ⟨770544, by rfl⟩ : syracuseStep 8219141 = 1541089) (by norm_num)
theorem B5479427 : Blo 1923435 5479427 := bstep (se 1 (by rfl) ⟨4109570, by rfl⟩ : syracuseStep 5479427 = 8219141) B8219141
theorem B3652951 : Blo 1923435 3652951 := bstep (se 1 (by rfl) ⟨2739713, by rfl⟩ : syracuseStep 3652951 = 5479427) B5479427
theorem B4870601 : Blo 1923435 4870601 := bstep (se 2 (by rfl) ⟨1826475, by rfl⟩ : syracuseStep 4870601 = 3652951) B3652951
theorem B3247067 : Blo 1923435 3247067 := bstep (se 1 (by rfl) ⟨2435300, by rfl⟩ : syracuseStep 3247067 = 4870601) B4870601
theorem B2164711 : Blo 1923435 2164711 := bstep (se 1 (by rfl) ⟨1623533, by rfl⟩ : syracuseStep 2164711 = 3247067) B3247067
theorem B2886281 : Blo 1923435 2886281 := bstep (se 2 (by rfl) ⟨1082355, by rfl⟩ : syracuseStep 2886281 = 2164711) B2164711
theorem B1924187 : Blo 1923435 1924187 := bstep (se 1 (by rfl) ⟨1443140, by rfl⟩ : syracuseStep 1924187 = 2886281) B2886281
theorem B9741221 : Blo 1923435 9741221 := bbase (se 4 (by rfl) ⟨913239, by rfl⟩ : syracuseStep 9741221 = 1826479) (by norm_num)
theorem B6494147 : Blo 1923435 6494147 := bstep (se 1 (by rfl) ⟨4870610, by rfl⟩ : syracuseStep 6494147 = 9741221) B9741221
theorem B4329431 : Blo 1923435 4329431 := bstep (se 1 (by rfl) ⟨3247073, by rfl⟩ : syracuseStep 4329431 = 6494147) B6494147
theorem B2886287 : Blo 1923435 2886287 := bstep (se 1 (by rfl) ⟨2164715, by rfl⟩ : syracuseStep 2886287 = 4329431) B4329431
theorem B1924191 : Blo 1923435 1924191 := bstep (se 1 (by rfl) ⟨1443143, by rfl⟩ : syracuseStep 1924191 = 2886287) B2886287
theorem B2886293 : Blo 1923435 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B1924195 : Blo 1923435 1924195 := bstep (se 1 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 1924195 = 2886293) B2886293
theorem B40035541 : Blo 1923435 40035541 := bbase (se 7 (by rfl) ⟨469166, by rfl⟩ : syracuseStep 40035541 = 938333) (by norm_num)
theorem B53380721 : Blo 1923435 53380721 := bstep (se 2 (by rfl) ⟨20017770, by rfl⟩ : syracuseStep 53380721 = 40035541) B40035541
theorem B35587147 : Blo 1923435 35587147 := bstep (se 1 (by rfl) ⟨26690360, by rfl⟩ : syracuseStep 35587147 = 53380721) B53380721
theorem B47449529 : Blo 1923435 47449529 := bstep (se 2 (by rfl) ⟨17793573, by rfl⟩ : syracuseStep 47449529 = 35587147) B35587147
theorem B31633019 : Blo 1923435 31633019 := bstep (se 1 (by rfl) ⟨23724764, by rfl⟩ : syracuseStep 31633019 = 47449529) B47449529
theorem B21088679 : Blo 1923435 21088679 := bstep (se 1 (by rfl) ⟨15816509, by rfl⟩ : syracuseStep 21088679 = 31633019) B31633019
theorem B56236477 : Blo 1923435 56236477 := bstep (se 3 (by rfl) ⟨10544339, by rfl⟩ : syracuseStep 56236477 = 21088679) B21088679
theorem B74981969 : Blo 1923435 74981969 := bstep (se 2 (by rfl) ⟨28118238, by rfl⟩ : syracuseStep 74981969 = 56236477) B56236477
theorem B49987979 : Blo 1923435 49987979 := bstep (se 1 (by rfl) ⟨37490984, by rfl⟩ : syracuseStep 49987979 = 74981969) B74981969
theorem B33325319 : Blo 1923435 33325319 := bstep (se 1 (by rfl) ⟨24993989, by rfl⟩ : syracuseStep 33325319 = 49987979) B49987979
theorem B22216879 : Blo 1923435 22216879 := bstep (se 1 (by rfl) ⟨16662659, by rfl⟩ : syracuseStep 22216879 = 33325319) B33325319
theorem B29622505 : Blo 1923435 29622505 := bstep (se 2 (by rfl) ⟨11108439, by rfl⟩ : syracuseStep 29622505 = 22216879) B22216879
theorem B39496673 : Blo 1923435 39496673 := bstep (se 2 (by rfl) ⟨14811252, by rfl⟩ : syracuseStep 39496673 = 29622505) B29622505
theorem B26331115 : Blo 1923435 26331115 := bstep (se 1 (by rfl) ⟨19748336, by rfl⟩ : syracuseStep 26331115 = 39496673) B39496673
theorem B35108153 : Blo 1923435 35108153 := bstep (se 2 (by rfl) ⟨13165557, by rfl⟩ : syracuseStep 35108153 = 26331115) B26331115
theorem B23405435 : Blo 1923435 23405435 := bstep (se 1 (by rfl) ⟨17554076, by rfl⟩ : syracuseStep 23405435 = 35108153) B35108153
theorem B15603623 : Blo 1923435 15603623 := bstep (se 1 (by rfl) ⟨11702717, by rfl⟩ : syracuseStep 15603623 = 23405435) B23405435
theorem B10402415 : Blo 1923435 10402415 := bstep (se 1 (by rfl) ⟨7801811, by rfl⟩ : syracuseStep 10402415 = 15603623) B15603623
theorem B6934943 : Blo 1923435 6934943 := bstep (se 1 (by rfl) ⟨5201207, by rfl⟩ : syracuseStep 6934943 = 10402415) B10402415
theorem B18493181 : Blo 1923435 18493181 := bstep (se 3 (by rfl) ⟨3467471, by rfl⟩ : syracuseStep 18493181 = 6934943) B6934943
theorem B12328787 : Blo 1923435 12328787 := bstep (se 1 (by rfl) ⟨9246590, by rfl⟩ : syracuseStep 12328787 = 18493181) B18493181
theorem B8219191 : Blo 1923435 8219191 := bstep (se 1 (by rfl) ⟨6164393, by rfl⟩ : syracuseStep 8219191 = 12328787) B12328787
theorem B10958921 : Blo 1923435 10958921 := bstep (se 2 (by rfl) ⟨4109595, by rfl⟩ : syracuseStep 10958921 = 8219191) B8219191
theorem B7305947 : Blo 1923435 7305947 := bstep (se 1 (by rfl) ⟨5479460, by rfl⟩ : syracuseStep 7305947 = 10958921) B10958921
theorem B4870631 : Blo 1923435 4870631 := bstep (se 1 (by rfl) ⟨3652973, by rfl⟩ : syracuseStep 4870631 = 7305947) B7305947
theorem B3247087 : Blo 1923435 3247087 := bstep (se 1 (by rfl) ⟨2435315, by rfl⟩ : syracuseStep 3247087 = 4870631) B4870631
theorem B4329449 : Blo 1923435 4329449 := bstep (se 2 (by rfl) ⟨1623543, by rfl⟩ : syracuseStep 4329449 = 3247087) B3247087
theorem B2886299 : Blo 1923435 2886299 := bstep (se 1 (by rfl) ⟨2164724, by rfl⟩ : syracuseStep 2886299 = 4329449) B4329449
theorem B1924199 : Blo 1923435 1924199 := bstep (se 1 (by rfl) ⟨1443149, by rfl⟩ : syracuseStep 1924199 = 2886299) B2886299
theorem B2164729 : Blo 1923435 2164729 := bbase (se 2 (by rfl) ⟨811773, by rfl⟩ : syracuseStep 2164729 = 1623547) (by norm_num)
theorem B2886305 : Blo 1923435 2886305 := bstep (se 2 (by rfl) ⟨1082364, by rfl⟩ : syracuseStep 2886305 = 2164729) B2164729
theorem B1924203 : Blo 1923435 1924203 := bstep (se 1 (by rfl) ⟨1443152, by rfl⟩ : syracuseStep 1924203 = 2886305) B2886305
theorem B9246629 : Blo 1923435 9246629 := bbase (se 4 (by rfl) ⟨866871, by rfl⟩ : syracuseStep 9246629 = 1733743) (by norm_num)
theorem B6164419 : Blo 1923435 6164419 := bstep (se 1 (by rfl) ⟨4623314, by rfl⟩ : syracuseStep 6164419 = 9246629) B9246629
theorem B8219225 : Blo 1923435 8219225 := bstep (se 2 (by rfl) ⟨3082209, by rfl⟩ : syracuseStep 8219225 = 6164419) B6164419
theorem B5479483 : Blo 1923435 5479483 := bstep (se 1 (by rfl) ⟨4109612, by rfl⟩ : syracuseStep 5479483 = 8219225) B8219225
theorem B7305977 : Blo 1923435 7305977 := bstep (se 2 (by rfl) ⟨2739741, by rfl⟩ : syracuseStep 7305977 = 5479483) B5479483
theorem B4870651 : Blo 1923435 4870651 := bstep (se 1 (by rfl) ⟨3652988, by rfl⟩ : syracuseStep 4870651 = 7305977) B7305977
theorem B6494201 : Blo 1923435 6494201 := bstep (se 2 (by rfl) ⟨2435325, by rfl⟩ : syracuseStep 6494201 = 4870651) B4870651
theorem B4329467 : Blo 1923435 4329467 := bstep (se 1 (by rfl) ⟨3247100, by rfl⟩ : syracuseStep 4329467 = 6494201) B6494201
theorem B2886311 : Blo 1923435 2886311 := bstep (se 1 (by rfl) ⟨2164733, by rfl⟩ : syracuseStep 2886311 = 4329467) B4329467
theorem B1924207 : Blo 1923435 1924207 := bstep (se 1 (by rfl) ⟨1443155, by rfl⟩ : syracuseStep 1924207 = 2886311) B2886311
theorem B2886317 : Blo 1923435 2886317 := bbase (se 3 (by rfl) ⟨541184, by rfl⟩ : syracuseStep 2886317 = 1082369) (by norm_num)
theorem B1924211 : Blo 1923435 1924211 := bstep (se 1 (by rfl) ⟨1443158, by rfl⟩ : syracuseStep 1924211 = 2886317) B2886317
theorem B4329485 : Blo 1923435 4329485 := bbase (se 3 (by rfl) ⟨811778, by rfl⟩ : syracuseStep 4329485 = 1623557) (by norm_num)
theorem B2886323 : Blo 1923435 2886323 := bstep (se 1 (by rfl) ⟨2164742, by rfl⟩ : syracuseStep 2886323 = 4329485) B4329485
theorem B1924215 : Blo 1923435 1924215 := bstep (se 1 (by rfl) ⟨1443161, by rfl⟩ : syracuseStep 1924215 = 2886323) B2886323
theorem B2435341 : Blo 1923435 2435341 := bbase (se 3 (by rfl) ⟨456626, by rfl⟩ : syracuseStep 2435341 = 913253) (by norm_num)
theorem B3247121 : Blo 1923435 3247121 := bstep (se 2 (by rfl) ⟨1217670, by rfl⟩ : syracuseStep 3247121 = 2435341) B2435341
theorem B2164747 : Blo 1923435 2164747 := bstep (se 1 (by rfl) ⟨1623560, by rfl⟩ : syracuseStep 2164747 = 3247121) B3247121
theorem B2886329 : Blo 1923435 2886329 := bstep (se 2 (by rfl) ⟨1082373, by rfl⟩ : syracuseStep 2886329 = 2164747) B2164747
theorem B1924219 : Blo 1923435 1924219 := bstep (se 1 (by rfl) ⟨1443164, by rfl⟩ : syracuseStep 1924219 = 2886329) B2886329
theorem B2502253 : Blo 1923435 2502253 := bbase (se 3 (by rfl) ⟨469172, by rfl⟩ : syracuseStep 2502253 = 938345) (by norm_num)
theorem B3336337 : Blo 1923435 3336337 := bstep (se 2 (by rfl) ⟨1251126, by rfl⟩ : syracuseStep 3336337 = 2502253) B2502253
theorem B4448449 : Blo 1923435 4448449 := bstep (se 2 (by rfl) ⟨1668168, by rfl⟩ : syracuseStep 4448449 = 3336337) B3336337
theorem B5931265 : Blo 1923435 5931265 := bstep (se 2 (by rfl) ⟨2224224, by rfl⟩ : syracuseStep 5931265 = 4448449) B4448449
theorem B7908353 : Blo 1923435 7908353 := bstep (se 2 (by rfl) ⟨2965632, by rfl⟩ : syracuseStep 7908353 = 5931265) B5931265
theorem B5272235 : Blo 1923435 5272235 := bstep (se 1 (by rfl) ⟨3954176, by rfl⟩ : syracuseStep 5272235 = 7908353) B7908353
theorem B3514823 : Blo 1923435 3514823 := bstep (se 1 (by rfl) ⟨2636117, by rfl⟩ : syracuseStep 3514823 = 5272235) B5272235
theorem B37491445 : Blo 1923435 37491445 := bstep (se 5 (by rfl) ⟨1757411, by rfl⟩ : syracuseStep 37491445 = 3514823) B3514823
theorem B49988593 : Blo 1923435 49988593 := bstep (se 2 (by rfl) ⟨18745722, by rfl⟩ : syracuseStep 49988593 = 37491445) B37491445
theorem B66651457 : Blo 1923435 66651457 := bstep (se 2 (by rfl) ⟨24994296, by rfl⟩ : syracuseStep 66651457 = 49988593) B49988593
theorem B88868609 : Blo 1923435 88868609 := bstep (se 2 (by rfl) ⟨33325728, by rfl⟩ : syracuseStep 88868609 = 66651457) B66651457
theorem B59245739 : Blo 1923435 59245739 := bstep (se 1 (by rfl) ⟨44434304, by rfl⟩ : syracuseStep 59245739 = 88868609) B88868609
theorem B39497159 : Blo 1923435 39497159 := bstep (se 1 (by rfl) ⟨29622869, by rfl⟩ : syracuseStep 39497159 = 59245739) B59245739
theorem B26331439 : Blo 1923435 26331439 := bstep (se 1 (by rfl) ⟨19748579, by rfl⟩ : syracuseStep 26331439 = 39497159) B39497159
theorem B35108585 : Blo 1923435 35108585 := bstep (se 2 (by rfl) ⟨13165719, by rfl⟩ : syracuseStep 35108585 = 26331439) B26331439
theorem B23405723 : Blo 1923435 23405723 := bstep (se 1 (by rfl) ⟨17554292, by rfl⟩ : syracuseStep 23405723 = 35108585) B35108585
theorem B15603815 : Blo 1923435 15603815 := bstep (se 1 (by rfl) ⟨11702861, by rfl⟩ : syracuseStep 15603815 = 23405723) B23405723
theorem B10402543 : Blo 1923435 10402543 := bstep (se 1 (by rfl) ⟨7801907, by rfl⟩ : syracuseStep 10402543 = 15603815) B15603815
theorem B13870057 : Blo 1923435 13870057 := bstep (se 2 (by rfl) ⟨5201271, by rfl⟩ : syracuseStep 13870057 = 10402543) B10402543
theorem B18493409 : Blo 1923435 18493409 := bstep (se 2 (by rfl) ⟨6935028, by rfl⟩ : syracuseStep 18493409 = 13870057) B13870057
theorem B12328939 : Blo 1923435 12328939 := bstep (se 1 (by rfl) ⟨9246704, by rfl⟩ : syracuseStep 12328939 = 18493409) B18493409
theorem B16438585 : Blo 1923435 16438585 := bstep (se 2 (by rfl) ⟨6164469, by rfl⟩ : syracuseStep 16438585 = 12328939) B12328939
theorem B21918113 : Blo 1923435 21918113 := bstep (se 2 (by rfl) ⟨8219292, by rfl⟩ : syracuseStep 21918113 = 16438585) B16438585
theorem B14612075 : Blo 1923435 14612075 := bstep (se 1 (by rfl) ⟨10959056, by rfl⟩ : syracuseStep 14612075 = 21918113) B21918113
theorem B9741383 : Blo 1923435 9741383 := bstep (se 1 (by rfl) ⟨7306037, by rfl⟩ : syracuseStep 9741383 = 14612075) B14612075
theorem B6494255 : Blo 1923435 6494255 := bstep (se 1 (by rfl) ⟨4870691, by rfl⟩ : syracuseStep 6494255 = 9741383) B9741383
theorem B4329503 : Blo 1923435 4329503 := bstep (se 1 (by rfl) ⟨3247127, by rfl⟩ : syracuseStep 4329503 = 6494255) B6494255
theorem B2886335 : Blo 1923435 2886335 := bstep (se 1 (by rfl) ⟨2164751, by rfl⟩ : syracuseStep 2886335 = 4329503) B4329503
theorem B1924223 : Blo 1923435 1924223 := bstep (se 1 (by rfl) ⟨1443167, by rfl⟩ : syracuseStep 1924223 = 2886335) B2886335
theorem B2886341 : Blo 1923435 2886341 := bbase (se 4 (by rfl) ⟨270594, by rfl⟩ : syracuseStep 2886341 = 541189) (by norm_num)
theorem B1924227 : Blo 1923435 1924227 := bstep (se 1 (by rfl) ⟨1443170, by rfl⟩ : syracuseStep 1924227 = 2886341) B2886341
theorem B3247141 : Blo 1923435 3247141 := bbase (se 4 (by rfl) ⟨304419, by rfl⟩ : syracuseStep 3247141 = 608839) (by norm_num)
theorem B4329521 : Blo 1923435 4329521 := bstep (se 2 (by rfl) ⟨1623570, by rfl⟩ : syracuseStep 4329521 = 3247141) B3247141
theorem B2886347 : Blo 1923435 2886347 := bstep (se 1 (by rfl) ⟨2164760, by rfl⟩ : syracuseStep 2886347 = 4329521) B4329521
theorem B1924231 : Blo 1923435 1924231 := bstep (se 1 (by rfl) ⟨1443173, by rfl⟩ : syracuseStep 1924231 = 2886347) B2886347
theorem B2164765 : Blo 1923435 2164765 := bbase (se 3 (by rfl) ⟨405893, by rfl⟩ : syracuseStep 2164765 = 811787) (by norm_num)
theorem B2886353 : Blo 1923435 2886353 := bstep (se 2 (by rfl) ⟨1082382, by rfl⟩ : syracuseStep 2886353 = 2164765) B2164765
theorem B1924235 : Blo 1923435 1924235 := bstep (se 1 (by rfl) ⟨1443176, by rfl⟩ : syracuseStep 1924235 = 2886353) B2886353
theorem B6494309 : Blo 1923435 6494309 := bbase (se 4 (by rfl) ⟨608841, by rfl⟩ : syracuseStep 6494309 = 1217683) (by norm_num)
theorem B4329539 : Blo 1923435 4329539 := bstep (se 1 (by rfl) ⟨3247154, by rfl⟩ : syracuseStep 4329539 = 6494309) B6494309
theorem B2886359 : Blo 1923435 2886359 := bstep (se 1 (by rfl) ⟨2164769, by rfl⟩ : syracuseStep 2886359 = 4329539) B4329539
theorem B1924239 : Blo 1923435 1924239 := bstep (se 1 (by rfl) ⟨1443179, by rfl⟩ : syracuseStep 1924239 = 2886359) B2886359
theorem B2886365 : Blo 1923435 2886365 := bbase (se 3 (by rfl) ⟨541193, by rfl⟩ : syracuseStep 2886365 = 1082387) (by norm_num)
theorem B1924243 : Blo 1923435 1924243 := bstep (se 1 (by rfl) ⟨1443182, by rfl⟩ : syracuseStep 1924243 = 2886365) B2886365
theorem B4329557 : Blo 1923435 4329557 := bbase (se 8 (by rfl) ⟨25368, by rfl⟩ : syracuseStep 4329557 = 50737) (by norm_num)
theorem B2886371 : Blo 1923435 2886371 := bstep (se 1 (by rfl) ⟨2164778, by rfl⟩ : syracuseStep 2886371 = 4329557) B4329557
theorem B1924247 : Blo 1923435 1924247 := bstep (se 1 (by rfl) ⟨1443185, by rfl⟩ : syracuseStep 1924247 = 2886371) B2886371
theorem B4623421 : Blo 1923435 4623421 := bbase (se 3 (by rfl) ⟨866891, by rfl⟩ : syracuseStep 4623421 = 1733783) (by norm_num)
theorem B6164561 : Blo 1923435 6164561 := bstep (se 2 (by rfl) ⟨2311710, by rfl⟩ : syracuseStep 6164561 = 4623421) B4623421
theorem B4109707 : Blo 1923435 4109707 := bstep (se 1 (by rfl) ⟨3082280, by rfl⟩ : syracuseStep 4109707 = 6164561) B6164561
theorem B5479609 : Blo 1923435 5479609 := bstep (se 2 (by rfl) ⟨2054853, by rfl⟩ : syracuseStep 5479609 = 4109707) B4109707
theorem B7306145 : Blo 1923435 7306145 := bstep (se 2 (by rfl) ⟨2739804, by rfl⟩ : syracuseStep 7306145 = 5479609) B5479609
theorem B4870763 : Blo 1923435 4870763 := bstep (se 1 (by rfl) ⟨3653072, by rfl⟩ : syracuseStep 4870763 = 7306145) B7306145
theorem B3247175 : Blo 1923435 3247175 := bstep (se 1 (by rfl) ⟨2435381, by rfl⟩ : syracuseStep 3247175 = 4870763) B4870763
theorem B2164783 : Blo 1923435 2164783 := bstep (se 1 (by rfl) ⟨1623587, by rfl⟩ : syracuseStep 2164783 = 3247175) B3247175
theorem B2886377 : Blo 1923435 2886377 := bstep (se 2 (by rfl) ⟨1082391, by rfl⟩ : syracuseStep 2886377 = 2164783) B2164783
theorem B1924251 : Blo 1923435 1924251 := bstep (se 1 (by rfl) ⟨1443188, by rfl⟩ : syracuseStep 1924251 = 2886377) B2886377
theorem B18493717 : Blo 1923435 18493717 := bbase (se 6 (by rfl) ⟨433446, by rfl⟩ : syracuseStep 18493717 = 866893) (by norm_num)
theorem B24658289 : Blo 1923435 24658289 := bstep (se 2 (by rfl) ⟨9246858, by rfl⟩ : syracuseStep 24658289 = 18493717) B18493717
theorem B16438859 : Blo 1923435 16438859 := bstep (se 1 (by rfl) ⟨12329144, by rfl⟩ : syracuseStep 16438859 = 24658289) B24658289
theorem B10959239 : Blo 1923435 10959239 := bstep (se 1 (by rfl) ⟨8219429, by rfl⟩ : syracuseStep 10959239 = 16438859) B16438859
theorem B7306159 : Blo 1923435 7306159 := bstep (se 1 (by rfl) ⟨5479619, by rfl⟩ : syracuseStep 7306159 = 10959239) B10959239
theorem B9741545 : Blo 1923435 9741545 := bstep (se 2 (by rfl) ⟨3653079, by rfl⟩ : syracuseStep 9741545 = 7306159) B7306159
theorem B6494363 : Blo 1923435 6494363 := bstep (se 1 (by rfl) ⟨4870772, by rfl⟩ : syracuseStep 6494363 = 9741545) B9741545
theorem B4329575 : Blo 1923435 4329575 := bstep (se 1 (by rfl) ⟨3247181, by rfl⟩ : syracuseStep 4329575 = 6494363) B6494363
theorem B2886383 : Blo 1923435 2886383 := bstep (se 1 (by rfl) ⟨2164787, by rfl⟩ : syracuseStep 2886383 = 4329575) B4329575
theorem B1924255 : Blo 1923435 1924255 := bstep (se 1 (by rfl) ⟨1443191, by rfl⟩ : syracuseStep 1924255 = 2886383) B2886383
theorem B2886389 : Blo 1923435 2886389 := bbase (se 5 (by rfl) ⟨135299, by rfl⟩ : syracuseStep 2886389 = 270599) (by norm_num)
theorem B1924259 : Blo 1923435 1924259 := bstep (se 1 (by rfl) ⟨1443194, by rfl⟩ : syracuseStep 1924259 = 2886389) B2886389
theorem B5201381 : Blo 1923435 5201381 := bbase (se 4 (by rfl) ⟨487629, by rfl⟩ : syracuseStep 5201381 = 975259) (by norm_num)
theorem B13870349 : Blo 1923435 13870349 := bstep (se 3 (by rfl) ⟨2600690, by rfl⟩ : syracuseStep 13870349 = 5201381) B5201381
theorem B9246899 : Blo 1923435 9246899 := bstep (se 1 (by rfl) ⟨6935174, by rfl⟩ : syracuseStep 9246899 = 13870349) B13870349
theorem B6164599 : Blo 1923435 6164599 := bstep (se 1 (by rfl) ⟨4623449, by rfl⟩ : syracuseStep 6164599 = 9246899) B9246899
theorem B8219465 : Blo 1923435 8219465 := bstep (se 2 (by rfl) ⟨3082299, by rfl⟩ : syracuseStep 8219465 = 6164599) B6164599
theorem B5479643 : Blo 1923435 5479643 := bstep (se 1 (by rfl) ⟨4109732, by rfl⟩ : syracuseStep 5479643 = 8219465) B8219465
theorem B3653095 : Blo 1923435 3653095 := bstep (se 1 (by rfl) ⟨2739821, by rfl⟩ : syracuseStep 3653095 = 5479643) B5479643
theorem B4870793 : Blo 1923435 4870793 := bstep (se 2 (by rfl) ⟨1826547, by rfl⟩ : syracuseStep 4870793 = 3653095) B3653095
theorem B3247195 : Blo 1923435 3247195 := bstep (se 1 (by rfl) ⟨2435396, by rfl⟩ : syracuseStep 3247195 = 4870793) B4870793
theorem B4329593 : Blo 1923435 4329593 := bstep (se 2 (by rfl) ⟨1623597, by rfl⟩ : syracuseStep 4329593 = 3247195) B3247195
theorem B2886395 : Blo 1923435 2886395 := bstep (se 1 (by rfl) ⟨2164796, by rfl⟩ : syracuseStep 2886395 = 4329593) B4329593
theorem B1924263 : Blo 1923435 1924263 := bstep (se 1 (by rfl) ⟨1443197, by rfl⟩ : syracuseStep 1924263 = 2886395) B2886395
theorem B2164801 : Blo 1923435 2164801 := bbase (se 2 (by rfl) ⟨811800, by rfl⟩ : syracuseStep 2164801 = 1623601) (by norm_num)
theorem B2886401 : Blo 1923435 2886401 := bstep (se 2 (by rfl) ⟨1082400, by rfl⟩ : syracuseStep 2886401 = 2164801) B2164801
theorem B1924267 : Blo 1923435 1924267 := bstep (se 1 (by rfl) ⟨1443200, by rfl⟩ : syracuseStep 1924267 = 2886401) B2886401
theorem B4870813 : Blo 1923435 4870813 := bbase (se 3 (by rfl) ⟨913277, by rfl⟩ : syracuseStep 4870813 = 1826555) (by norm_num)
theorem B6494417 : Blo 1923435 6494417 := bstep (se 2 (by rfl) ⟨2435406, by rfl⟩ : syracuseStep 6494417 = 4870813) B4870813
theorem B4329611 : Blo 1923435 4329611 := bstep (se 1 (by rfl) ⟨3247208, by rfl⟩ : syracuseStep 4329611 = 6494417) B6494417
theorem B2886407 : Blo 1923435 2886407 := bstep (se 1 (by rfl) ⟨2164805, by rfl⟩ : syracuseStep 2886407 = 4329611) B4329611
theorem B1924271 : Blo 1923435 1924271 := bstep (se 1 (by rfl) ⟨1443203, by rfl⟩ : syracuseStep 1924271 = 2886407) B2886407
theorem B2886413 : Blo 1923435 2886413 := bbase (se 3 (by rfl) ⟨541202, by rfl⟩ : syracuseStep 2886413 = 1082405) (by norm_num)
theorem B1924275 : Blo 1923435 1924275 := bstep (se 1 (by rfl) ⟨1443206, by rfl⟩ : syracuseStep 1924275 = 2886413) B2886413
theorem B4329629 : Blo 1923435 4329629 := bbase (se 3 (by rfl) ⟨811805, by rfl⟩ : syracuseStep 4329629 = 1623611) (by norm_num)
theorem B2886419 : Blo 1923435 2886419 := bstep (se 1 (by rfl) ⟨2164814, by rfl⟩ : syracuseStep 2886419 = 4329629) B4329629
theorem B1924279 : Blo 1923435 1924279 := bstep (se 1 (by rfl) ⟨1443209, by rfl⟩ : syracuseStep 1924279 = 2886419) B2886419
theorem B3247229 : Blo 1923435 3247229 := bbase (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) (by norm_num)
theorem B2164819 : Blo 1923435 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B2886425 : Blo 1923435 2886425 := bstep (se 2 (by rfl) ⟨1082409, by rfl⟩ : syracuseStep 2886425 = 2164819) B2164819
theorem B1924283 : Blo 1923435 1924283 := bstep (se 1 (by rfl) ⟨1443212, by rfl⟩ : syracuseStep 1924283 = 2886425) B2886425
theorem B9247013 : Blo 1923435 9247013 := bbase (se 4 (by rfl) ⟨866907, by rfl⟩ : syracuseStep 9247013 = 1733815) (by norm_num)
theorem B6164675 : Blo 1923435 6164675 := bstep (se 1 (by rfl) ⟨4623506, by rfl⟩ : syracuseStep 6164675 = 9247013) B9247013
theorem B4109783 : Blo 1923435 4109783 := bstep (se 1 (by rfl) ⟨3082337, by rfl⟩ : syracuseStep 4109783 = 6164675) B6164675
theorem B10959421 : Blo 1923435 10959421 := bstep (se 3 (by rfl) ⟨2054891, by rfl⟩ : syracuseStep 10959421 = 4109783) B4109783
theorem B14612561 : Blo 1923435 14612561 := bstep (se 2 (by rfl) ⟨5479710, by rfl⟩ : syracuseStep 14612561 = 10959421) B10959421
theorem B9741707 : Blo 1923435 9741707 := bstep (se 1 (by rfl) ⟨7306280, by rfl⟩ : syracuseStep 9741707 = 14612561) B14612561
theorem B6494471 : Blo 1923435 6494471 := bstep (se 1 (by rfl) ⟨4870853, by rfl⟩ : syracuseStep 6494471 = 9741707) B9741707
theorem B4329647 : Blo 1923435 4329647 := bstep (se 1 (by rfl) ⟨3247235, by rfl⟩ : syracuseStep 4329647 = 6494471) B6494471
theorem B2886431 : Blo 1923435 2886431 := bstep (se 1 (by rfl) ⟨2164823, by rfl⟩ : syracuseStep 2886431 = 4329647) B4329647
theorem B1924287 : Blo 1923435 1924287 := bstep (se 1 (by rfl) ⟨1443215, by rfl⟩ : syracuseStep 1924287 = 2886431) B2886431
theorem B2886437 : Blo 1923435 2886437 := bbase (se 4 (by rfl) ⟨270603, by rfl⟩ : syracuseStep 2886437 = 541207) (by norm_num)
theorem B1924291 : Blo 1923435 1924291 := bstep (se 1 (by rfl) ⟨1443218, by rfl⟩ : syracuseStep 1924291 = 2886437) B2886437
theorem B2435437 : Blo 1923435 2435437 := bbase (se 3 (by rfl) ⟨456644, by rfl⟩ : syracuseStep 2435437 = 913289) (by norm_num)
theorem B3247249 : Blo 1923435 3247249 := bstep (se 2 (by rfl) ⟨1217718, by rfl⟩ : syracuseStep 3247249 = 2435437) B2435437
theorem B4329665 : Blo 1923435 4329665 := bstep (se 2 (by rfl) ⟨1623624, by rfl⟩ : syracuseStep 4329665 = 3247249) B3247249
theorem B2886443 : Blo 1923435 2886443 := bstep (se 1 (by rfl) ⟨2164832, by rfl⟩ : syracuseStep 2886443 = 4329665) B4329665
theorem B1924295 : Blo 1923435 1924295 := bstep (se 1 (by rfl) ⟨1443221, by rfl⟩ : syracuseStep 1924295 = 2886443) B2886443
theorem B2164837 : Blo 1923435 2164837 := bbase (se 4 (by rfl) ⟨202953, by rfl⟩ : syracuseStep 2164837 = 405907) (by norm_num)
theorem B2886449 : Blo 1923435 2886449 := bstep (se 2 (by rfl) ⟨1082418, by rfl⟩ : syracuseStep 2886449 = 2164837) B2164837
theorem B1924299 : Blo 1923435 1924299 := bstep (se 1 (by rfl) ⟨1443224, by rfl⟩ : syracuseStep 1924299 = 2886449) B2886449
theorem B2054909 : Blo 1923435 2054909 := bbase (se 3 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 2054909 = 770591) (by norm_num)
theorem B5479757 : Blo 1923435 5479757 := bstep (se 3 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 5479757 = 2054909) B2054909
theorem B3653171 : Blo 1923435 3653171 := bstep (se 1 (by rfl) ⟨2739878, by rfl⟩ : syracuseStep 3653171 = 5479757) B5479757
theorem B2435447 : Blo 1923435 2435447 := bstep (se 1 (by rfl) ⟨1826585, by rfl⟩ : syracuseStep 2435447 = 3653171) B3653171
theorem B6494525 : Blo 1923435 6494525 := bstep (se 3 (by rfl) ⟨1217723, by rfl⟩ : syracuseStep 6494525 = 2435447) B2435447
theorem B4329683 : Blo 1923435 4329683 := bstep (se 1 (by rfl) ⟨3247262, by rfl⟩ : syracuseStep 4329683 = 6494525) B6494525
theorem B2886455 : Blo 1923435 2886455 := bstep (se 1 (by rfl) ⟨2164841, by rfl⟩ : syracuseStep 2886455 = 4329683) B4329683
theorem B1924303 : Blo 1923435 1924303 := bstep (se 1 (by rfl) ⟨1443227, by rfl⟩ : syracuseStep 1924303 = 2886455) B2886455
theorem B2886461 : Blo 1923435 2886461 := bbase (se 3 (by rfl) ⟨541211, by rfl⟩ : syracuseStep 2886461 = 1082423) (by norm_num)
theorem B1924307 : Blo 1923435 1924307 := bstep (se 1 (by rfl) ⟨1443230, by rfl⟩ : syracuseStep 1924307 = 2886461) B2886461
theorem B4329701 : Blo 1923435 4329701 := bbase (se 4 (by rfl) ⟨405909, by rfl⟩ : syracuseStep 4329701 = 811819) (by norm_num)
theorem B2886467 : Blo 1923435 2886467 := bstep (se 1 (by rfl) ⟨2164850, by rfl⟩ : syracuseStep 2886467 = 4329701) B4329701
theorem B1924311 : Blo 1923435 1924311 := bstep (se 1 (by rfl) ⟨1443233, by rfl⟩ : syracuseStep 1924311 = 2886467) B2886467
theorem B4870925 : Blo 1923435 4870925 := bbase (se 3 (by rfl) ⟨913298, by rfl⟩ : syracuseStep 4870925 = 1826597) (by norm_num)
theorem B3247283 : Blo 1923435 3247283 := bstep (se 1 (by rfl) ⟨2435462, by rfl⟩ : syracuseStep 3247283 = 4870925) B4870925
theorem B2164855 : Blo 1923435 2164855 := bstep (se 1 (by rfl) ⟨1623641, by rfl⟩ : syracuseStep 2164855 = 3247283) B3247283
theorem B2886473 : Blo 1923435 2886473 := bstep (se 2 (by rfl) ⟨1082427, by rfl⟩ : syracuseStep 2886473 = 2164855) B2164855
theorem B1924315 : Blo 1923435 1924315 := bstep (se 1 (by rfl) ⟨1443236, by rfl⟩ : syracuseStep 1924315 = 2886473) B2886473
theorem B2739901 : Blo 1923435 2739901 := bbase (se 3 (by rfl) ⟨513731, by rfl⟩ : syracuseStep 2739901 = 1027463) (by norm_num)
theorem B3653201 : Blo 1923435 3653201 := bstep (se 2 (by rfl) ⟨1369950, by rfl⟩ : syracuseStep 3653201 = 2739901) B2739901
theorem B9741869 : Blo 1923435 9741869 := bstep (se 3 (by rfl) ⟨1826600, by rfl⟩ : syracuseStep 9741869 = 3653201) B3653201
theorem B6494579 : Blo 1923435 6494579 := bstep (se 1 (by rfl) ⟨4870934, by rfl⟩ : syracuseStep 6494579 = 9741869) B9741869
theorem B4329719 : Blo 1923435 4329719 := bstep (se 1 (by rfl) ⟨3247289, by rfl⟩ : syracuseStep 4329719 = 6494579) B6494579
theorem B2886479 : Blo 1923435 2886479 := bstep (se 1 (by rfl) ⟨2164859, by rfl⟩ : syracuseStep 2886479 = 4329719) B4329719
theorem B1924319 : Blo 1923435 1924319 := bstep (se 1 (by rfl) ⟨1443239, by rfl⟩ : syracuseStep 1924319 = 2886479) B2886479
theorem B2886485 : Blo 1923435 2886485 := bbase (se 9 (by rfl) ⟨8456, by rfl⟩ : syracuseStep 2886485 = 16913) (by norm_num)
theorem B1924323 : Blo 1923435 1924323 := bstep (se 1 (by rfl) ⟨1443242, by rfl⟩ : syracuseStep 1924323 = 2886485) B2886485
theorem B4109869 : Blo 1923435 4109869 := bbase (se 3 (by rfl) ⟨770600, by rfl⟩ : syracuseStep 4109869 = 1541201) (by norm_num)
theorem B5479825 : Blo 1923435 5479825 := bstep (se 2 (by rfl) ⟨2054934, by rfl⟩ : syracuseStep 5479825 = 4109869) B4109869
theorem B7306433 : Blo 1923435 7306433 := bstep (se 2 (by rfl) ⟨2739912, by rfl⟩ : syracuseStep 7306433 = 5479825) B5479825
theorem B4870955 : Blo 1923435 4870955 := bstep (se 1 (by rfl) ⟨3653216, by rfl⟩ : syracuseStep 4870955 = 7306433) B7306433
theorem B3247303 : Blo 1923435 3247303 := bstep (se 1 (by rfl) ⟨2435477, by rfl⟩ : syracuseStep 3247303 = 4870955) B4870955
theorem B4329737 : Blo 1923435 4329737 := bstep (se 2 (by rfl) ⟨1623651, by rfl⟩ : syracuseStep 4329737 = 3247303) B3247303
theorem B2886491 : Blo 1923435 2886491 := bstep (se 1 (by rfl) ⟨2164868, by rfl⟩ : syracuseStep 2886491 = 4329737) B4329737
theorem B1924327 : Blo 1923435 1924327 := bstep (se 1 (by rfl) ⟨1443245, by rfl⟩ : syracuseStep 1924327 = 2886491) B2886491
theorem B2164873 : Blo 1923435 2164873 := bbase (se 2 (by rfl) ⟨811827, by rfl⟩ : syracuseStep 2164873 = 1623655) (by norm_num)
theorem B2886497 : Blo 1923435 2886497 := bstep (se 2 (by rfl) ⟨1082436, by rfl⟩ : syracuseStep 2886497 = 2164873) B2164873
theorem B1924331 : Blo 1923435 1924331 := bstep (se 1 (by rfl) ⟨1443248, by rfl⟩ : syracuseStep 1924331 = 2886497) B2886497
theorem B3901181 : Blo 1923435 3901181 := bbase (se 3 (by rfl) ⟨731471, by rfl⟩ : syracuseStep 3901181 = 1462943) (by norm_num)
theorem B10403149 : Blo 1923435 10403149 := bstep (se 3 (by rfl) ⟨1950590, by rfl⟩ : syracuseStep 10403149 = 3901181) B3901181
theorem B13870865 : Blo 1923435 13870865 := bstep (se 2 (by rfl) ⟨5201574, by rfl⟩ : syracuseStep 13870865 = 10403149) B10403149
theorem B36988973 : Blo 1923435 36988973 := bstep (se 3 (by rfl) ⟨6935432, by rfl⟩ : syracuseStep 36988973 = 13870865) B13870865
theorem B24659315 : Blo 1923435 24659315 := bstep (se 1 (by rfl) ⟨18494486, by rfl⟩ : syracuseStep 24659315 = 36988973) B36988973
theorem B16439543 : Blo 1923435 16439543 := bstep (se 1 (by rfl) ⟨12329657, by rfl⟩ : syracuseStep 16439543 = 24659315) B24659315
theorem B10959695 : Blo 1923435 10959695 := bstep (se 1 (by rfl) ⟨8219771, by rfl⟩ : syracuseStep 10959695 = 16439543) B16439543
theorem B7306463 : Blo 1923435 7306463 := bstep (se 1 (by rfl) ⟨5479847, by rfl⟩ : syracuseStep 7306463 = 10959695) B10959695
theorem B4870975 : Blo 1923435 4870975 := bstep (se 1 (by rfl) ⟨3653231, by rfl⟩ : syracuseStep 4870975 = 7306463) B7306463
theorem B6494633 : Blo 1923435 6494633 := bstep (se 2 (by rfl) ⟨2435487, by rfl⟩ : syracuseStep 6494633 = 4870975) B4870975
theorem B4329755 : Blo 1923435 4329755 := bstep (se 1 (by rfl) ⟨3247316, by rfl⟩ : syracuseStep 4329755 = 6494633) B6494633
theorem B2886503 : Blo 1923435 2886503 := bstep (se 1 (by rfl) ⟨2164877, by rfl⟩ : syracuseStep 2886503 = 4329755) B4329755
theorem B1924335 : Blo 1923435 1924335 := bstep (se 1 (by rfl) ⟨1443251, by rfl⟩ : syracuseStep 1924335 = 2886503) B2886503
theorem B2886509 : Blo 1923435 2886509 := bbase (se 3 (by rfl) ⟨541220, by rfl⟩ : syracuseStep 2886509 = 1082441) (by norm_num)
theorem B1924339 : Blo 1923435 1924339 := bstep (se 1 (by rfl) ⟨1443254, by rfl⟩ : syracuseStep 1924339 = 2886509) B2886509
theorem B4329773 : Blo 1923435 4329773 := bbase (se 3 (by rfl) ⟨811832, by rfl⟩ : syracuseStep 4329773 = 1623665) (by norm_num)
theorem B2886515 : Blo 1923435 2886515 := bstep (se 1 (by rfl) ⟨2164886, by rfl⟩ : syracuseStep 2886515 = 4329773) B4329773
theorem B1924343 : Blo 1923435 1924343 := bstep (se 1 (by rfl) ⟨1443257, by rfl⟩ : syracuseStep 1924343 = 2886515) B2886515
theorem B6164869 : Blo 1923435 6164869 := bbase (se 4 (by rfl) ⟨577956, by rfl⟩ : syracuseStep 6164869 = 1155913) (by norm_num)
theorem B8219825 : Blo 1923435 8219825 := bstep (se 2 (by rfl) ⟨3082434, by rfl⟩ : syracuseStep 8219825 = 6164869) B6164869
theorem B5479883 : Blo 1923435 5479883 := bstep (se 1 (by rfl) ⟨4109912, by rfl⟩ : syracuseStep 5479883 = 8219825) B8219825
theorem B3653255 : Blo 1923435 3653255 := bstep (se 1 (by rfl) ⟨2739941, by rfl⟩ : syracuseStep 3653255 = 5479883) B5479883
theorem B2435503 : Blo 1923435 2435503 := bstep (se 1 (by rfl) ⟨1826627, by rfl⟩ : syracuseStep 2435503 = 3653255) B3653255
theorem B3247337 : Blo 1923435 3247337 := bstep (se 2 (by rfl) ⟨1217751, by rfl⟩ : syracuseStep 3247337 = 2435503) B2435503
theorem B2164891 : Blo 1923435 2164891 := bstep (se 1 (by rfl) ⟨1623668, by rfl⟩ : syracuseStep 2164891 = 3247337) B3247337
theorem B2886521 : Blo 1923435 2886521 := bstep (se 2 (by rfl) ⟨1082445, by rfl⟩ : syracuseStep 2886521 = 2164891) B2164891
theorem B1924347 : Blo 1923435 1924347 := bstep (se 1 (by rfl) ⟨1443260, by rfl⟩ : syracuseStep 1924347 = 2886521) B2886521
theorem B2082997 : Blo 1923435 2082997 := bbase (se 5 (by rfl) ⟨97640, by rfl⟩ : syracuseStep 2082997 = 195281) (by norm_num)
theorem B2777329 : Blo 1923435 2777329 := bstep (se 2 (by rfl) ⟨1041498, by rfl⟩ : syracuseStep 2777329 = 2082997) B2082997
theorem B3703105 : Blo 1923435 3703105 := bstep (se 2 (by rfl) ⟨1388664, by rfl⟩ : syracuseStep 3703105 = 2777329) B2777329
theorem B4937473 : Blo 1923435 4937473 := bstep (se 2 (by rfl) ⟨1851552, by rfl⟩ : syracuseStep 4937473 = 3703105) B3703105
theorem B26333189 : Blo 1923435 26333189 := bstep (se 4 (by rfl) ⟨2468736, by rfl⟩ : syracuseStep 26333189 = 4937473) B4937473
theorem B17555459 : Blo 1923435 17555459 := bstep (se 1 (by rfl) ⟨13166594, by rfl⟩ : syracuseStep 17555459 = 26333189) B26333189
theorem B46814557 : Blo 1923435 46814557 := bstep (se 3 (by rfl) ⟨8777729, by rfl⟩ : syracuseStep 46814557 = 17555459) B17555459
theorem B62419409 : Blo 1923435 62419409 := bstep (se 2 (by rfl) ⟨23407278, by rfl⟩ : syracuseStep 62419409 = 46814557) B46814557
theorem B41612939 : Blo 1923435 41612939 := bstep (se 1 (by rfl) ⟨31209704, by rfl⟩ : syracuseStep 41612939 = 62419409) B62419409
theorem B27741959 : Blo 1923435 27741959 := bstep (se 1 (by rfl) ⟨20806469, by rfl⟩ : syracuseStep 27741959 = 41612939) B41612939
theorem B18494639 : Blo 1923435 18494639 := bstep (se 1 (by rfl) ⟨13870979, by rfl⟩ : syracuseStep 18494639 = 27741959) B27741959
theorem B12329759 : Blo 1923435 12329759 := bstep (se 1 (by rfl) ⟨9247319, by rfl⟩ : syracuseStep 12329759 = 18494639) B18494639
theorem B32879357 : Blo 1923435 32879357 := bstep (se 3 (by rfl) ⟨6164879, by rfl⟩ : syracuseStep 32879357 = 12329759) B12329759
theorem B21919571 : Blo 1923435 21919571 := bstep (se 1 (by rfl) ⟨16439678, by rfl⟩ : syracuseStep 21919571 = 32879357) B32879357
theorem B14613047 : Blo 1923435 14613047 := bstep (se 1 (by rfl) ⟨10959785, by rfl⟩ : syracuseStep 14613047 = 21919571) B21919571
theorem B9742031 : Blo 1923435 9742031 := bstep (se 1 (by rfl) ⟨7306523, by rfl⟩ : syracuseStep 9742031 = 14613047) B14613047
theorem B6494687 : Blo 1923435 6494687 := bstep (se 1 (by rfl) ⟨4871015, by rfl⟩ : syracuseStep 6494687 = 9742031) B9742031
theorem B4329791 : Blo 1923435 4329791 := bstep (se 1 (by rfl) ⟨3247343, by rfl⟩ : syracuseStep 4329791 = 6494687) B6494687
theorem B2886527 : Blo 1923435 2886527 := bstep (se 1 (by rfl) ⟨2164895, by rfl⟩ : syracuseStep 2886527 = 4329791) B4329791
theorem B1924351 : Blo 1923435 1924351 := bstep (se 1 (by rfl) ⟨1443263, by rfl⟩ : syracuseStep 1924351 = 2886527) B2886527
theorem B2886533 : Blo 1923435 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B1924355 : Blo 1923435 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B3247357 : Blo 1923435 3247357 := bbase (se 3 (by rfl) ⟨608879, by rfl⟩ : syracuseStep 3247357 = 1217759) (by norm_num)
theorem B4329809 : Blo 1923435 4329809 := bstep (se 2 (by rfl) ⟨1623678, by rfl⟩ : syracuseStep 4329809 = 3247357) B3247357
theorem B2886539 : Blo 1923435 2886539 := bstep (se 1 (by rfl) ⟨2164904, by rfl⟩ : syracuseStep 2886539 = 4329809) B4329809
theorem B1924359 : Blo 1923435 1924359 := bstep (se 1 (by rfl) ⟨1443269, by rfl⟩ : syracuseStep 1924359 = 2886539) B2886539
theorem B2164909 : Blo 1923435 2164909 := bbase (se 3 (by rfl) ⟨405920, by rfl⟩ : syracuseStep 2164909 = 811841) (by norm_num)
theorem B2886545 : Blo 1923435 2886545 := bstep (se 2 (by rfl) ⟨1082454, by rfl⟩ : syracuseStep 2886545 = 2164909) B2164909
theorem B1924363 : Blo 1923435 1924363 := bstep (se 1 (by rfl) ⟨1443272, by rfl⟩ : syracuseStep 1924363 = 2886545) B2886545
theorem B6494741 : Blo 1923435 6494741 := bbase (se 6 (by rfl) ⟨152220, by rfl⟩ : syracuseStep 6494741 = 304441) (by norm_num)
theorem B4329827 : Blo 1923435 4329827 := bstep (se 1 (by rfl) ⟨3247370, by rfl⟩ : syracuseStep 4329827 = 6494741) B6494741
theorem B2886551 : Blo 1923435 2886551 := bstep (se 1 (by rfl) ⟨2164913, by rfl⟩ : syracuseStep 2886551 = 4329827) B4329827
theorem B1924367 : Blo 1923435 1924367 := bstep (se 1 (by rfl) ⟨1443275, by rfl⟩ : syracuseStep 1924367 = 2886551) B2886551
theorem B2886557 : Blo 1923435 2886557 := bbase (se 3 (by rfl) ⟨541229, by rfl⟩ : syracuseStep 2886557 = 1082459) (by norm_num)
theorem B1924371 : Blo 1923435 1924371 := bstep (se 1 (by rfl) ⟨1443278, by rfl⟩ : syracuseStep 1924371 = 2886557) B2886557
theorem B4329845 : Blo 1923435 4329845 := bbase (se 5 (by rfl) ⟨202961, by rfl⟩ : syracuseStep 4329845 = 405923) (by norm_num)
theorem B2886563 : Blo 1923435 2886563 := bstep (se 1 (by rfl) ⟨2164922, by rfl⟩ : syracuseStep 2886563 = 4329845) B4329845
theorem B1924375 : Blo 1923435 1924375 := bstep (se 1 (by rfl) ⟨1443281, by rfl⟩ : syracuseStep 1924375 = 2886563) B2886563
theorem B12329941 : Blo 1923435 12329941 := bbase (se 7 (by rfl) ⟨144491, by rfl⟩ : syracuseStep 12329941 = 288983) (by norm_num)
theorem B16439921 : Blo 1923435 16439921 := bstep (se 2 (by rfl) ⟨6164970, by rfl⟩ : syracuseStep 16439921 = 12329941) B12329941
theorem B10959947 : Blo 1923435 10959947 := bstep (se 1 (by rfl) ⟨8219960, by rfl⟩ : syracuseStep 10959947 = 16439921) B16439921
theorem B7306631 : Blo 1923435 7306631 := bstep (se 1 (by rfl) ⟨5479973, by rfl⟩ : syracuseStep 7306631 = 10959947) B10959947
theorem B4871087 : Blo 1923435 4871087 := bstep (se 1 (by rfl) ⟨3653315, by rfl⟩ : syracuseStep 4871087 = 7306631) B7306631
theorem B3247391 : Blo 1923435 3247391 := bstep (se 1 (by rfl) ⟨2435543, by rfl⟩ : syracuseStep 3247391 = 4871087) B4871087
theorem B2164927 : Blo 1923435 2164927 := bstep (se 1 (by rfl) ⟨1623695, by rfl⟩ : syracuseStep 2164927 = 3247391) B3247391
theorem B2886569 : Blo 1923435 2886569 := bstep (se 2 (by rfl) ⟨1082463, by rfl⟩ : syracuseStep 2886569 = 2164927) B2164927
theorem B1924379 : Blo 1923435 1924379 := bstep (se 1 (by rfl) ⟨1443284, by rfl⟩ : syracuseStep 1924379 = 2886569) B2886569
theorem B7306645 : Blo 1923435 7306645 := bbase (se 6 (by rfl) ⟨171249, by rfl⟩ : syracuseStep 7306645 = 342499) (by norm_num)
theorem B9742193 : Blo 1923435 9742193 := bstep (se 2 (by rfl) ⟨3653322, by rfl⟩ : syracuseStep 9742193 = 7306645) B7306645
theorem B6494795 : Blo 1923435 6494795 := bstep (se 1 (by rfl) ⟨4871096, by rfl⟩ : syracuseStep 6494795 = 9742193) B9742193
theorem B4329863 : Blo 1923435 4329863 := bstep (se 1 (by rfl) ⟨3247397, by rfl⟩ : syracuseStep 4329863 = 6494795) B6494795
theorem B2886575 : Blo 1923435 2886575 := bstep (se 1 (by rfl) ⟨2164931, by rfl⟩ : syracuseStep 2886575 = 4329863) B4329863
theorem B1924383 : Blo 1923435 1924383 := bstep (se 1 (by rfl) ⟨1443287, by rfl⟩ : syracuseStep 1924383 = 2886575) B2886575
theorem B2886581 : Blo 1923435 2886581 := bbase (se 5 (by rfl) ⟨135308, by rfl⟩ : syracuseStep 2886581 = 270617) (by norm_num)
theorem B1924387 : Blo 1923435 1924387 := bstep (se 1 (by rfl) ⟨1443290, by rfl⟩ : syracuseStep 1924387 = 2886581) B2886581
theorem B4871117 : Blo 1923435 4871117 := bbase (se 3 (by rfl) ⟨913334, by rfl⟩ : syracuseStep 4871117 = 1826669) (by norm_num)
theorem B3247411 : Blo 1923435 3247411 := bstep (se 1 (by rfl) ⟨2435558, by rfl⟩ : syracuseStep 3247411 = 4871117) B4871117
theorem B4329881 : Blo 1923435 4329881 := bstep (se 2 (by rfl) ⟨1623705, by rfl⟩ : syracuseStep 4329881 = 3247411) B3247411
theorem B2886587 : Blo 1923435 2886587 := bstep (se 1 (by rfl) ⟨2164940, by rfl⟩ : syracuseStep 2886587 = 4329881) B4329881
theorem B1924391 : Blo 1923435 1924391 := bstep (se 1 (by rfl) ⟨1443293, by rfl⟩ : syracuseStep 1924391 = 2886587) B2886587
theorem B2164945 : Blo 1923435 2164945 := bbase (se 2 (by rfl) ⟨811854, by rfl⟩ : syracuseStep 2164945 = 1623709) (by norm_num)
theorem B2886593 : Blo 1923435 2886593 := bstep (se 2 (by rfl) ⟨1082472, by rfl⟩ : syracuseStep 2886593 = 2164945) B2164945
theorem B1924395 : Blo 1923435 1924395 := bstep (se 1 (by rfl) ⟨1443296, by rfl⟩ : syracuseStep 1924395 = 2886593) B2886593
theorem B5201749 : Blo 1923435 5201749 := bbase (se 9 (by rfl) ⟨15239, by rfl⟩ : syracuseStep 5201749 = 30479) (by norm_num)
theorem B6935665 : Blo 1923435 6935665 := bstep (se 2 (by rfl) ⟨2600874, by rfl⟩ : syracuseStep 6935665 = 5201749) B5201749
theorem B9247553 : Blo 1923435 9247553 := bstep (se 2 (by rfl) ⟨3467832, by rfl⟩ : syracuseStep 9247553 = 6935665) B6935665
theorem B6165035 : Blo 1923435 6165035 := bstep (se 1 (by rfl) ⟨4623776, by rfl⟩ : syracuseStep 6165035 = 9247553) B9247553
theorem B4110023 : Blo 1923435 4110023 := bstep (se 1 (by rfl) ⟨3082517, by rfl⟩ : syracuseStep 4110023 = 6165035) B6165035
theorem B2740015 : Blo 1923435 2740015 := bstep (se 1 (by rfl) ⟨2055011, by rfl⟩ : syracuseStep 2740015 = 4110023) B4110023
theorem B3653353 : Blo 1923435 3653353 := bstep (se 2 (by rfl) ⟨1370007, by rfl⟩ : syracuseStep 3653353 = 2740015) B2740015
theorem B4871137 : Blo 1923435 4871137 := bstep (se 2 (by rfl) ⟨1826676, by rfl⟩ : syracuseStep 4871137 = 3653353) B3653353
theorem B6494849 : Blo 1923435 6494849 := bstep (se 2 (by rfl) ⟨2435568, by rfl⟩ : syracuseStep 6494849 = 4871137) B4871137
theorem B4329899 : Blo 1923435 4329899 := bstep (se 1 (by rfl) ⟨3247424, by rfl⟩ : syracuseStep 4329899 = 6494849) B6494849
theorem B2886599 : Blo 1923435 2886599 := bstep (se 1 (by rfl) ⟨2164949, by rfl⟩ : syracuseStep 2886599 = 4329899) B4329899
theorem B1924399 : Blo 1923435 1924399 := bstep (se 1 (by rfl) ⟨1443299, by rfl⟩ : syracuseStep 1924399 = 2886599) B2886599
theorem B2886605 : Blo 1923435 2886605 := bbase (se 3 (by rfl) ⟨541238, by rfl⟩ : syracuseStep 2886605 = 1082477) (by norm_num)
theorem B1924403 : Blo 1923435 1924403 := bstep (se 1 (by rfl) ⟨1443302, by rfl⟩ : syracuseStep 1924403 = 2886605) B2886605
theorem B4329917 : Blo 1923435 4329917 := bbase (se 3 (by rfl) ⟨811859, by rfl⟩ : syracuseStep 4329917 = 1623719) (by norm_num)
theorem B2886611 : Blo 1923435 2886611 := bstep (se 1 (by rfl) ⟨2164958, by rfl⟩ : syracuseStep 2886611 = 4329917) B4329917
theorem B1924407 : Blo 1923435 1924407 := bstep (se 1 (by rfl) ⟨1443305, by rfl⟩ : syracuseStep 1924407 = 2886611) B2886611
theorem B3247445 : Blo 1923435 3247445 := bbase (se 11 (by rfl) ⟨2378, by rfl⟩ : syracuseStep 3247445 = 4757) (by norm_num)
theorem B2164963 : Blo 1923435 2164963 := bstep (se 1 (by rfl) ⟨1623722, by rfl⟩ : syracuseStep 2164963 = 3247445) B3247445
theorem B2886617 : Blo 1923435 2886617 := bstep (se 2 (by rfl) ⟨1082481, by rfl⟩ : syracuseStep 2886617 = 2164963) B2164963
theorem B1924411 : Blo 1923435 1924411 := bstep (se 1 (by rfl) ⟨1443308, by rfl⟩ : syracuseStep 1924411 = 2886617) B2886617
theorem B3467861 : Blo 1923435 3467861 := bbase (se 8 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 3467861 = 40639) (by norm_num)
theorem B2311907 : Blo 1923435 2311907 := bstep (se 1 (by rfl) ⟨1733930, by rfl⟩ : syracuseStep 2311907 = 3467861) B3467861
theorem B6165085 : Blo 1923435 6165085 := bstep (se 3 (by rfl) ⟨1155953, by rfl⟩ : syracuseStep 6165085 = 2311907) B2311907
theorem B8220113 : Blo 1923435 8220113 := bstep (se 2 (by rfl) ⟨3082542, by rfl⟩ : syracuseStep 8220113 = 6165085) B6165085
theorem B5480075 : Blo 1923435 5480075 := bstep (se 1 (by rfl) ⟨4110056, by rfl⟩ : syracuseStep 5480075 = 8220113) B8220113
theorem B14613533 : Blo 1923435 14613533 := bstep (se 3 (by rfl) ⟨2740037, by rfl⟩ : syracuseStep 14613533 = 5480075) B5480075
theorem B9742355 : Blo 1923435 9742355 := bstep (se 1 (by rfl) ⟨7306766, by rfl⟩ : syracuseStep 9742355 = 14613533) B14613533
theorem B6494903 : Blo 1923435 6494903 := bstep (se 1 (by rfl) ⟨4871177, by rfl⟩ : syracuseStep 6494903 = 9742355) B9742355
theorem B4329935 : Blo 1923435 4329935 := bstep (se 1 (by rfl) ⟨3247451, by rfl⟩ : syracuseStep 4329935 = 6494903) B6494903
theorem B2886623 : Blo 1923435 2886623 := bstep (se 1 (by rfl) ⟨2164967, by rfl⟩ : syracuseStep 2886623 = 4329935) B4329935
theorem B1924415 : Blo 1923435 1924415 := bstep (se 1 (by rfl) ⟨1443311, by rfl⟩ : syracuseStep 1924415 = 2886623) B2886623
theorem B2886629 : Blo 1923435 2886629 := bbase (se 4 (by rfl) ⟨270621, by rfl⟩ : syracuseStep 2886629 = 541243) (by norm_num)
theorem B1924419 : Blo 1923435 1924419 := bstep (se 1 (by rfl) ⟨1443314, by rfl⟩ : syracuseStep 1924419 = 2886629) B2886629
theorem B8220149 : Blo 1923435 8220149 := bbase (se 5 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 8220149 = 770639) (by norm_num)
theorem B5480099 : Blo 1923435 5480099 := bstep (se 1 (by rfl) ⟨4110074, by rfl⟩ : syracuseStep 5480099 = 8220149) B8220149
theorem B3653399 : Blo 1923435 3653399 := bstep (se 1 (by rfl) ⟨2740049, by rfl⟩ : syracuseStep 3653399 = 5480099) B5480099
theorem B2435599 : Blo 1923435 2435599 := bstep (se 1 (by rfl) ⟨1826699, by rfl⟩ : syracuseStep 2435599 = 3653399) B3653399
theorem B3247465 : Blo 1923435 3247465 := bstep (se 2 (by rfl) ⟨1217799, by rfl⟩ : syracuseStep 3247465 = 2435599) B2435599
theorem B4329953 : Blo 1923435 4329953 := bstep (se 2 (by rfl) ⟨1623732, by rfl⟩ : syracuseStep 4329953 = 3247465) B3247465
theorem B2886635 : Blo 1923435 2886635 := bstep (se 1 (by rfl) ⟨2164976, by rfl⟩ : syracuseStep 2886635 = 4329953) B4329953
theorem B1924423 : Blo 1923435 1924423 := bstep (se 1 (by rfl) ⟨1443317, by rfl⟩ : syracuseStep 1924423 = 2886635) B2886635
theorem B2164981 : Blo 1923435 2164981 := bbase (se 5 (by rfl) ⟨101483, by rfl⟩ : syracuseStep 2164981 = 202967) (by norm_num)
theorem B2886641 : Blo 1923435 2886641 := bstep (se 2 (by rfl) ⟨1082490, by rfl⟩ : syracuseStep 2886641 = 2164981) B2164981
theorem B1924427 : Blo 1923435 1924427 := bstep (se 1 (by rfl) ⟨1443320, by rfl⟩ : syracuseStep 1924427 = 2886641) B2886641
theorem B2435609 : Blo 1923435 2435609 := bbase (se 2 (by rfl) ⟨913353, by rfl⟩ : syracuseStep 2435609 = 1826707) (by norm_num)
theorem B6494957 : Blo 1923435 6494957 := bstep (se 3 (by rfl) ⟨1217804, by rfl⟩ : syracuseStep 6494957 = 2435609) B2435609
theorem B4329971 : Blo 1923435 4329971 := bstep (se 1 (by rfl) ⟨3247478, by rfl⟩ : syracuseStep 4329971 = 6494957) B6494957
theorem B2886647 : Blo 1923435 2886647 := bstep (se 1 (by rfl) ⟨2164985, by rfl⟩ : syracuseStep 2886647 = 4329971) B4329971
theorem B1924431 : Blo 1923435 1924431 := bstep (se 1 (by rfl) ⟨1443323, by rfl⟩ : syracuseStep 1924431 = 2886647) B2886647
theorem B2886653 : Blo 1923435 2886653 := bbase (se 3 (by rfl) ⟨541247, by rfl⟩ : syracuseStep 2886653 = 1082495) (by norm_num)
theorem B1924435 : Blo 1923435 1924435 := bstep (se 1 (by rfl) ⟨1443326, by rfl⟩ : syracuseStep 1924435 = 2886653) B2886653
theorem B4329989 : Blo 1923435 4329989 := bbase (se 4 (by rfl) ⟨405936, by rfl⟩ : syracuseStep 4329989 = 811873) (by norm_num)
theorem B2886659 : Blo 1923435 2886659 := bstep (se 1 (by rfl) ⟨2164994, by rfl⟩ : syracuseStep 2886659 = 4329989) B4329989
theorem B1924439 : Blo 1923435 1924439 := bstep (se 1 (by rfl) ⟨1443329, by rfl⟩ : syracuseStep 1924439 = 2886659) B2886659
theorem B3653437 : Blo 1923435 3653437 := bbase (se 3 (by rfl) ⟨685019, by rfl⟩ : syracuseStep 3653437 = 1370039) (by norm_num)
theorem B4871249 : Blo 1923435 4871249 := bstep (se 2 (by rfl) ⟨1826718, by rfl⟩ : syracuseStep 4871249 = 3653437) B3653437
theorem B3247499 : Blo 1923435 3247499 := bstep (se 1 (by rfl) ⟨2435624, by rfl⟩ : syracuseStep 3247499 = 4871249) B4871249
theorem B2164999 : Blo 1923435 2164999 := bstep (se 1 (by rfl) ⟨1623749, by rfl⟩ : syracuseStep 2164999 = 3247499) B3247499
theorem B2886665 : Blo 1923435 2886665 := bstep (se 2 (by rfl) ⟨1082499, by rfl⟩ : syracuseStep 2886665 = 2164999) B2164999
theorem B1924443 : Blo 1923435 1924443 := bstep (se 1 (by rfl) ⟨1443332, by rfl⟩ : syracuseStep 1924443 = 2886665) B2886665
theorem B9742517 : Blo 1923435 9742517 := bbase (se 5 (by rfl) ⟨456680, by rfl⟩ : syracuseStep 9742517 = 913361) (by norm_num)
theorem B6495011 : Blo 1923435 6495011 := bstep (se 1 (by rfl) ⟨4871258, by rfl⟩ : syracuseStep 6495011 = 9742517) B9742517
theorem B4330007 : Blo 1923435 4330007 := bstep (se 1 (by rfl) ⟨3247505, by rfl⟩ : syracuseStep 4330007 = 6495011) B6495011
theorem B2886671 : Blo 1923435 2886671 := bstep (se 1 (by rfl) ⟨2165003, by rfl⟩ : syracuseStep 2886671 = 4330007) B4330007
theorem B1924447 : Blo 1923435 1924447 := bstep (se 1 (by rfl) ⟨1443335, by rfl⟩ : syracuseStep 1924447 = 2886671) B2886671
theorem B2886677 : Blo 1923435 2886677 := bbase (se 6 (by rfl) ⟨67656, by rfl⟩ : syracuseStep 2886677 = 135313) (by norm_num)
theorem B1924451 : Blo 1923435 1924451 := bstep (se 1 (by rfl) ⟨1443338, by rfl⟩ : syracuseStep 1924451 = 2886677) B2886677
theorem B2224493 : Blo 1923435 2224493 := bbase (se 3 (by rfl) ⟨417092, by rfl⟩ : syracuseStep 2224493 = 834185) (by norm_num)
theorem B23727925 : Blo 1923435 23727925 := bstep (se 5 (by rfl) ⟨1112246, by rfl⟩ : syracuseStep 23727925 = 2224493) B2224493
theorem B31637233 : Blo 1923435 31637233 := bstep (se 2 (by rfl) ⟨11863962, by rfl⟩ : syracuseStep 31637233 = 23727925) B23727925
theorem B42182977 : Blo 1923435 42182977 := bstep (se 2 (by rfl) ⟨15818616, by rfl⟩ : syracuseStep 42182977 = 31637233) B31637233
theorem B56243969 : Blo 1923435 56243969 := bstep (se 2 (by rfl) ⟨21091488, by rfl⟩ : syracuseStep 56243969 = 42182977) B42182977
theorem B37495979 : Blo 1923435 37495979 := bstep (se 1 (by rfl) ⟨28121984, by rfl⟩ : syracuseStep 37495979 = 56243969) B56243969
theorem B24997319 : Blo 1923435 24997319 := bstep (se 1 (by rfl) ⟨18747989, by rfl⟩ : syracuseStep 24997319 = 37495979) B37495979
theorem B16664879 : Blo 1923435 16664879 := bstep (se 1 (by rfl) ⟨12498659, by rfl⟩ : syracuseStep 16664879 = 24997319) B24997319
theorem B11109919 : Blo 1923435 11109919 := bstep (se 1 (by rfl) ⟨8332439, by rfl⟩ : syracuseStep 11109919 = 16664879) B16664879
theorem B14813225 : Blo 1923435 14813225 := bstep (se 2 (by rfl) ⟨5554959, by rfl⟩ : syracuseStep 14813225 = 11109919) B11109919
theorem B9875483 : Blo 1923435 9875483 := bstep (se 1 (by rfl) ⟨7406612, by rfl⟩ : syracuseStep 9875483 = 14813225) B14813225
theorem B6583655 : Blo 1923435 6583655 := bstep (se 1 (by rfl) ⟨4937741, by rfl⟩ : syracuseStep 6583655 = 9875483) B9875483
theorem B4389103 : Blo 1923435 4389103 := bstep (se 1 (by rfl) ⟨3291827, by rfl⟩ : syracuseStep 4389103 = 6583655) B6583655
theorem B5852137 : Blo 1923435 5852137 := bstep (se 2 (by rfl) ⟨2194551, by rfl⟩ : syracuseStep 5852137 = 4389103) B4389103
theorem B7802849 : Blo 1923435 7802849 := bstep (se 2 (by rfl) ⟨2926068, by rfl⟩ : syracuseStep 7802849 = 5852137) B5852137
theorem B20807597 : Blo 1923435 20807597 := bstep (se 3 (by rfl) ⟨3901424, by rfl⟩ : syracuseStep 20807597 = 7802849) B7802849
theorem B13871731 : Blo 1923435 13871731 := bstep (se 1 (by rfl) ⟨10403798, by rfl⟩ : syracuseStep 13871731 = 20807597) B20807597
theorem B18495641 : Blo 1923435 18495641 := bstep (se 2 (by rfl) ⟨6935865, by rfl⟩ : syracuseStep 18495641 = 13871731) B13871731
theorem B12330427 : Blo 1923435 12330427 := bstep (se 1 (by rfl) ⟨9247820, by rfl⟩ : syracuseStep 12330427 = 18495641) B18495641
theorem B16440569 : Blo 1923435 16440569 := bstep (se 2 (by rfl) ⟨6165213, by rfl⟩ : syracuseStep 16440569 = 12330427) B12330427
theorem B10960379 : Blo 1923435 10960379 := bstep (se 1 (by rfl) ⟨8220284, by rfl⟩ : syracuseStep 10960379 = 16440569) B16440569
theorem B7306919 : Blo 1923435 7306919 := bstep (se 1 (by rfl) ⟨5480189, by rfl⟩ : syracuseStep 7306919 = 10960379) B10960379
theorem B4871279 : Blo 1923435 4871279 := bstep (se 1 (by rfl) ⟨3653459, by rfl⟩ : syracuseStep 4871279 = 7306919) B7306919
theorem B3247519 : Blo 1923435 3247519 := bstep (se 1 (by rfl) ⟨2435639, by rfl⟩ : syracuseStep 3247519 = 4871279) B4871279
theorem B4330025 : Blo 1923435 4330025 := bstep (se 2 (by rfl) ⟨1623759, by rfl⟩ : syracuseStep 4330025 = 3247519) B3247519
theorem B2886683 : Blo 1923435 2886683 := bstep (se 1 (by rfl) ⟨2165012, by rfl⟩ : syracuseStep 2886683 = 4330025) B4330025
theorem B1924455 : Blo 1923435 1924455 := bstep (se 1 (by rfl) ⟨1443341, by rfl⟩ : syracuseStep 1924455 = 2886683) B2886683
theorem B2165017 : Blo 1923435 2165017 := bbase (se 2 (by rfl) ⟨811881, by rfl⟩ : syracuseStep 2165017 = 1623763) (by norm_num)
theorem B2886689 : Blo 1923435 2886689 := bstep (se 2 (by rfl) ⟨1082508, by rfl⟩ : syracuseStep 2886689 = 2165017) B2165017
theorem B1924459 : Blo 1923435 1924459 := bstep (se 1 (by rfl) ⟨1443344, by rfl⟩ : syracuseStep 1924459 = 2886689) B2886689
theorem B7306949 : Blo 1923435 7306949 := bbase (se 4 (by rfl) ⟨685026, by rfl⟩ : syracuseStep 7306949 = 1370053) (by norm_num)
theorem B4871299 : Blo 1923435 4871299 := bstep (se 1 (by rfl) ⟨3653474, by rfl⟩ : syracuseStep 4871299 = 7306949) B7306949
theorem B6495065 : Blo 1923435 6495065 := bstep (se 2 (by rfl) ⟨2435649, by rfl⟩ : syracuseStep 6495065 = 4871299) B4871299
theorem B4330043 : Blo 1923435 4330043 := bstep (se 1 (by rfl) ⟨3247532, by rfl⟩ : syracuseStep 4330043 = 6495065) B6495065
theorem B2886695 : Blo 1923435 2886695 := bstep (se 1 (by rfl) ⟨2165021, by rfl⟩ : syracuseStep 2886695 = 4330043) B4330043
theorem B1924463 : Blo 1923435 1924463 := bstep (se 1 (by rfl) ⟨1443347, by rfl⟩ : syracuseStep 1924463 = 2886695) B2886695
theorem B2886701 : Blo 1923435 2886701 := bbase (se 3 (by rfl) ⟨541256, by rfl⟩ : syracuseStep 2886701 = 1082513) (by norm_num)
theorem B1924467 : Blo 1923435 1924467 := bstep (se 1 (by rfl) ⟨1443350, by rfl⟩ : syracuseStep 1924467 = 2886701) B2886701
theorem B4330061 : Blo 1923435 4330061 := bbase (se 3 (by rfl) ⟨811886, by rfl⟩ : syracuseStep 4330061 = 1623773) (by norm_num)
theorem B2886707 : Blo 1923435 2886707 := bstep (se 1 (by rfl) ⟨2165030, by rfl⟩ : syracuseStep 2886707 = 4330061) B4330061
theorem B1924471 : Blo 1923435 1924471 := bstep (se 1 (by rfl) ⟨1443353, by rfl⟩ : syracuseStep 1924471 = 2886707) B2886707
theorem B2435665 : Blo 1923435 2435665 := bbase (se 2 (by rfl) ⟨913374, by rfl⟩ : syracuseStep 2435665 = 1826749) (by norm_num)
theorem B3247553 : Blo 1923435 3247553 := bstep (se 2 (by rfl) ⟨1217832, by rfl⟩ : syracuseStep 3247553 = 2435665) B2435665
theorem B2165035 : Blo 1923435 2165035 := bstep (se 1 (by rfl) ⟨1623776, by rfl⟩ : syracuseStep 2165035 = 3247553) B3247553
theorem B2886713 : Blo 1923435 2886713 := bstep (se 2 (by rfl) ⟨1082517, by rfl⟩ : syracuseStep 2886713 = 2165035) B2165035
theorem B1924475 : Blo 1923435 1924475 := bstep (se 1 (by rfl) ⟨1443356, by rfl⟩ : syracuseStep 1924475 = 2886713) B2886713
theorem B3082645 : Blo 1923435 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B4110193 : Blo 1923435 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B21921029 : Blo 1923435 21921029 := bstep (se 4 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 21921029 = 4110193) B4110193
theorem B14614019 : Blo 1923435 14614019 := bstep (se 1 (by rfl) ⟨10960514, by rfl⟩ : syracuseStep 14614019 = 21921029) B21921029
theorem B9742679 : Blo 1923435 9742679 := bstep (se 1 (by rfl) ⟨7307009, by rfl⟩ : syracuseStep 9742679 = 14614019) B14614019
theorem B6495119 : Blo 1923435 6495119 := bstep (se 1 (by rfl) ⟨4871339, by rfl⟩ : syracuseStep 6495119 = 9742679) B9742679
theorem B4330079 : Blo 1923435 4330079 := bstep (se 1 (by rfl) ⟨3247559, by rfl⟩ : syracuseStep 4330079 = 6495119) B6495119
theorem B2886719 : Blo 1923435 2886719 := bstep (se 1 (by rfl) ⟨2165039, by rfl⟩ : syracuseStep 2886719 = 4330079) B4330079
theorem B1924479 : Blo 1923435 1924479 := bstep (se 1 (by rfl) ⟨1443359, by rfl⟩ : syracuseStep 1924479 = 2886719) B2886719
theorem B2886725 : Blo 1923435 2886725 := bbase (se 4 (by rfl) ⟨270630, by rfl⟩ : syracuseStep 2886725 = 541261) (by norm_num)
theorem B1924483 : Blo 1923435 1924483 := bstep (se 1 (by rfl) ⟨1443362, by rfl⟩ : syracuseStep 1924483 = 2886725) B2886725
theorem B3247573 : Blo 1923435 3247573 := bbase (se 7 (by rfl) ⟨38057, by rfl⟩ : syracuseStep 3247573 = 76115) (by norm_num)
theorem B4330097 : Blo 1923435 4330097 := bstep (se 2 (by rfl) ⟨1623786, by rfl⟩ : syracuseStep 4330097 = 3247573) B3247573
theorem B2886731 : Blo 1923435 2886731 := bstep (se 1 (by rfl) ⟨2165048, by rfl⟩ : syracuseStep 2886731 = 4330097) B4330097
theorem B1924487 : Blo 1923435 1924487 := bstep (se 1 (by rfl) ⟨1443365, by rfl⟩ : syracuseStep 1924487 = 2886731) B2886731
theorem B2165053 : Blo 1923435 2165053 := bbase (se 3 (by rfl) ⟨405947, by rfl⟩ : syracuseStep 2165053 = 811895) (by norm_num)
theorem B2886737 : Blo 1923435 2886737 := bstep (se 2 (by rfl) ⟨1082526, by rfl⟩ : syracuseStep 2886737 = 2165053) B2165053
theorem B1924491 : Blo 1923435 1924491 := bstep (se 1 (by rfl) ⟨1443368, by rfl⟩ : syracuseStep 1924491 = 2886737) B2886737
theorem B6495173 : Blo 1923435 6495173 := bbase (se 4 (by rfl) ⟨608922, by rfl⟩ : syracuseStep 6495173 = 1217845) (by norm_num)
theorem B4330115 : Blo 1923435 4330115 := bstep (se 1 (by rfl) ⟨3247586, by rfl⟩ : syracuseStep 4330115 = 6495173) B6495173
theorem B2886743 : Blo 1923435 2886743 := bstep (se 1 (by rfl) ⟨2165057, by rfl⟩ : syracuseStep 2886743 = 4330115) B4330115
theorem B1924495 : Blo 1923435 1924495 := bstep (se 1 (by rfl) ⟨1443371, by rfl⟩ : syracuseStep 1924495 = 2886743) B2886743
theorem B2886749 : Blo 1923435 2886749 := bbase (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) (by norm_num)
theorem B1924499 : Blo 1923435 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B4330133 : Blo 1923435 4330133 := bbase (se 6 (by rfl) ⟨101487, by rfl⟩ : syracuseStep 4330133 = 202975) (by norm_num)
theorem B2886755 : Blo 1923435 2886755 := bstep (se 1 (by rfl) ⟨2165066, by rfl⟩ : syracuseStep 2886755 = 4330133) B4330133
theorem B1924503 : Blo 1923435 1924503 := bstep (se 1 (by rfl) ⟨1443377, by rfl⟩ : syracuseStep 1924503 = 2886755) B2886755
theorem B4624037 : Blo 1923435 4624037 := bbase (se 4 (by rfl) ⟨433503, by rfl⟩ : syracuseStep 4624037 = 867007) (by norm_num)
theorem B3082691 : Blo 1923435 3082691 := bstep (se 1 (by rfl) ⟨2312018, by rfl⟩ : syracuseStep 3082691 = 4624037) B4624037
theorem B2055127 : Blo 1923435 2055127 := bstep (se 1 (by rfl) ⟨1541345, by rfl⟩ : syracuseStep 2055127 = 3082691) B3082691
theorem B2740169 : Blo 1923435 2740169 := bstep (se 2 (by rfl) ⟨1027563, by rfl⟩ : syracuseStep 2740169 = 2055127) B2055127
theorem B7307117 : Blo 1923435 7307117 := bstep (se 3 (by rfl) ⟨1370084, by rfl⟩ : syracuseStep 7307117 = 2740169) B2740169
theorem B4871411 : Blo 1923435 4871411 := bstep (se 1 (by rfl) ⟨3653558, by rfl⟩ : syracuseStep 4871411 = 7307117) B7307117
theorem B3247607 : Blo 1923435 3247607 := bstep (se 1 (by rfl) ⟨2435705, by rfl⟩ : syracuseStep 3247607 = 4871411) B4871411
theorem B2165071 : Blo 1923435 2165071 := bstep (se 1 (by rfl) ⟨1623803, by rfl⟩ : syracuseStep 2165071 = 3247607) B3247607
theorem B2886761 : Blo 1923435 2886761 := bstep (se 2 (by rfl) ⟨1082535, by rfl⟩ : syracuseStep 2886761 = 2165071) B2165071
theorem B1924507 : Blo 1923435 1924507 := bstep (se 1 (by rfl) ⟨1443380, by rfl⟩ : syracuseStep 1924507 = 2886761) B2886761
theorem B1950769 : Blo 1923435 1950769 := bbase (se 2 (by rfl) ⟨731538, by rfl⟩ : syracuseStep 1950769 = 1463077) (by norm_num)
theorem B10404101 : Blo 1923435 10404101 := bstep (se 4 (by rfl) ⟨975384, by rfl⟩ : syracuseStep 10404101 = 1950769) B1950769
theorem B6936067 : Blo 1923435 6936067 := bstep (se 1 (by rfl) ⟨5202050, by rfl⟩ : syracuseStep 6936067 = 10404101) B10404101
theorem B9248089 : Blo 1923435 9248089 := bstep (se 2 (by rfl) ⟨3468033, by rfl⟩ : syracuseStep 9248089 = 6936067) B6936067
theorem B12330785 : Blo 1923435 12330785 := bstep (se 2 (by rfl) ⟨4624044, by rfl⟩ : syracuseStep 12330785 = 9248089) B9248089
theorem B8220523 : Blo 1923435 8220523 := bstep (se 1 (by rfl) ⟨6165392, by rfl⟩ : syracuseStep 8220523 = 12330785) B12330785
theorem B10960697 : Blo 1923435 10960697 := bstep (se 2 (by rfl) ⟨4110261, by rfl⟩ : syracuseStep 10960697 = 8220523) B8220523
theorem B7307131 : Blo 1923435 7307131 := bstep (se 1 (by rfl) ⟨5480348, by rfl⟩ : syracuseStep 7307131 = 10960697) B10960697
theorem B9742841 : Blo 1923435 9742841 := bstep (se 2 (by rfl) ⟨3653565, by rfl⟩ : syracuseStep 9742841 = 7307131) B7307131
theorem B6495227 : Blo 1923435 6495227 := bstep (se 1 (by rfl) ⟨4871420, by rfl⟩ : syracuseStep 6495227 = 9742841) B9742841
theorem B4330151 : Blo 1923435 4330151 := bstep (se 1 (by rfl) ⟨3247613, by rfl⟩ : syracuseStep 4330151 = 6495227) B6495227
theorem B2886767 : Blo 1923435 2886767 := bstep (se 1 (by rfl) ⟨2165075, by rfl⟩ : syracuseStep 2886767 = 4330151) B4330151
theorem B1924511 : Blo 1923435 1924511 := bstep (se 1 (by rfl) ⟨1443383, by rfl⟩ : syracuseStep 1924511 = 2886767) B2886767
theorem B2886773 : Blo 1923435 2886773 := bbase (se 5 (by rfl) ⟨135317, by rfl⟩ : syracuseStep 2886773 = 270635) (by norm_num)
theorem B1924515 : Blo 1923435 1924515 := bstep (se 1 (by rfl) ⟨1443386, by rfl⟩ : syracuseStep 1924515 = 2886773) B2886773
theorem B3653581 : Blo 1923435 3653581 := bbase (se 3 (by rfl) ⟨685046, by rfl⟩ : syracuseStep 3653581 = 1370093) (by norm_num)
theorem B4871441 : Blo 1923435 4871441 := bstep (se 2 (by rfl) ⟨1826790, by rfl⟩ : syracuseStep 4871441 = 3653581) B3653581
theorem B3247627 : Blo 1923435 3247627 := bstep (se 1 (by rfl) ⟨2435720, by rfl⟩ : syracuseStep 3247627 = 4871441) B4871441
theorem B4330169 : Blo 1923435 4330169 := bstep (se 2 (by rfl) ⟨1623813, by rfl⟩ : syracuseStep 4330169 = 3247627) B3247627
theorem B2886779 : Blo 1923435 2886779 := bstep (se 1 (by rfl) ⟨2165084, by rfl⟩ : syracuseStep 2886779 = 4330169) B4330169
theorem B1924519 : Blo 1923435 1924519 := bstep (se 1 (by rfl) ⟨1443389, by rfl⟩ : syracuseStep 1924519 = 2886779) B2886779
theorem B2165089 : Blo 1923435 2165089 := bbase (se 2 (by rfl) ⟨811908, by rfl⟩ : syracuseStep 2165089 = 1623817) (by norm_num)
theorem B2886785 : Blo 1923435 2886785 := bstep (se 2 (by rfl) ⟨1082544, by rfl⟩ : syracuseStep 2886785 = 2165089) B2165089
theorem B1924523 : Blo 1923435 1924523 := bstep (se 1 (by rfl) ⟨1443392, by rfl⟩ : syracuseStep 1924523 = 2886785) B2886785
theorem B4871461 : Blo 1923435 4871461 := bbase (se 4 (by rfl) ⟨456699, by rfl⟩ : syracuseStep 4871461 = 913399) (by norm_num)
theorem B6495281 : Blo 1923435 6495281 := bstep (se 2 (by rfl) ⟨2435730, by rfl⟩ : syracuseStep 6495281 = 4871461) B4871461
theorem B4330187 : Blo 1923435 4330187 := bstep (se 1 (by rfl) ⟨3247640, by rfl⟩ : syracuseStep 4330187 = 6495281) B6495281
theorem B2886791 : Blo 1923435 2886791 := bstep (se 1 (by rfl) ⟨2165093, by rfl⟩ : syracuseStep 2886791 = 4330187) B4330187
theorem B1924527 : Blo 1923435 1924527 := bstep (se 1 (by rfl) ⟨1443395, by rfl⟩ : syracuseStep 1924527 = 2886791) B2886791
theorem B2886797 : Blo 1923435 2886797 := bbase (se 3 (by rfl) ⟨541274, by rfl⟩ : syracuseStep 2886797 = 1082549) (by norm_num)
theorem B1924531 : Blo 1923435 1924531 := bstep (se 1 (by rfl) ⟨1443398, by rfl⟩ : syracuseStep 1924531 = 2886797) B2886797
theorem B4330205 : Blo 1923435 4330205 := bbase (se 3 (by rfl) ⟨811913, by rfl⟩ : syracuseStep 4330205 = 1623827) (by norm_num)
theorem B2886803 : Blo 1923435 2886803 := bstep (se 1 (by rfl) ⟨2165102, by rfl⟩ : syracuseStep 2886803 = 4330205) B4330205
theorem B1924535 : Blo 1923435 1924535 := bstep (se 1 (by rfl) ⟨1443401, by rfl⟩ : syracuseStep 1924535 = 2886803) B2886803
theorem B3247661 : Blo 1923435 3247661 := bbase (se 3 (by rfl) ⟨608936, by rfl⟩ : syracuseStep 3247661 = 1217873) (by norm_num)
theorem B2165107 : Blo 1923435 2165107 := bstep (se 1 (by rfl) ⟨1623830, by rfl⟩ : syracuseStep 2165107 = 3247661) B3247661
theorem B2886809 : Blo 1923435 2886809 := bstep (se 2 (by rfl) ⟨1082553, by rfl⟩ : syracuseStep 2886809 = 2165107) B2165107
theorem B1924539 : Blo 1923435 1924539 := bstep (se 1 (by rfl) ⟨1443404, by rfl⟩ : syracuseStep 1924539 = 2886809) B2886809
theorem B2343605 : Blo 1923435 2343605 := bbase (se 5 (by rfl) ⟨109856, by rfl⟩ : syracuseStep 2343605 = 219713) (by norm_num)
theorem B24998453 : Blo 1923435 24998453 := bstep (se 5 (by rfl) ⟨1171802, by rfl⟩ : syracuseStep 24998453 = 2343605) B2343605
theorem B16665635 : Blo 1923435 16665635 := bstep (se 1 (by rfl) ⟨12499226, by rfl⟩ : syracuseStep 16665635 = 24998453) B24998453
theorem B44441693 : Blo 1923435 44441693 := bstep (se 3 (by rfl) ⟨8332817, by rfl⟩ : syracuseStep 44441693 = 16665635) B16665635
theorem B29627795 : Blo 1923435 29627795 := bstep (se 1 (by rfl) ⟨22220846, by rfl⟩ : syracuseStep 29627795 = 44441693) B44441693
theorem B19751863 : Blo 1923435 19751863 := bstep (se 1 (by rfl) ⟨14813897, by rfl⟩ : syracuseStep 19751863 = 29627795) B29627795
theorem B26335817 : Blo 1923435 26335817 := bstep (se 2 (by rfl) ⟨9875931, by rfl⟩ : syracuseStep 26335817 = 19751863) B19751863
theorem B17557211 : Blo 1923435 17557211 := bstep (se 1 (by rfl) ⟨13167908, by rfl⟩ : syracuseStep 17557211 = 26335817) B26335817
theorem B11704807 : Blo 1923435 11704807 := bstep (se 1 (by rfl) ⟨8778605, by rfl⟩ : syracuseStep 11704807 = 17557211) B17557211
theorem B62425637 : Blo 1923435 62425637 := bstep (se 4 (by rfl) ⟨5852403, by rfl⟩ : syracuseStep 62425637 = 11704807) B11704807
theorem B41617091 : Blo 1923435 41617091 := bstep (se 1 (by rfl) ⟨31212818, by rfl⟩ : syracuseStep 41617091 = 62425637) B62425637
theorem B27744727 : Blo 1923435 27744727 := bstep (se 1 (by rfl) ⟨20808545, by rfl⟩ : syracuseStep 27744727 = 41617091) B41617091
theorem B36992969 : Blo 1923435 36992969 := bstep (se 2 (by rfl) ⟨13872363, by rfl⟩ : syracuseStep 36992969 = 27744727) B27744727
theorem B24661979 : Blo 1923435 24661979 := bstep (se 1 (by rfl) ⟨18496484, by rfl⟩ : syracuseStep 24661979 = 36992969) B36992969
theorem B16441319 : Blo 1923435 16441319 := bstep (se 1 (by rfl) ⟨12330989, by rfl⟩ : syracuseStep 16441319 = 24661979) B24661979
theorem B10960879 : Blo 1923435 10960879 := bstep (se 1 (by rfl) ⟨8220659, by rfl⟩ : syracuseStep 10960879 = 16441319) B16441319
theorem B14614505 : Blo 1923435 14614505 := bstep (se 2 (by rfl) ⟨5480439, by rfl⟩ : syracuseStep 14614505 = 10960879) B10960879
theorem B9743003 : Blo 1923435 9743003 := bstep (se 1 (by rfl) ⟨7307252, by rfl⟩ : syracuseStep 9743003 = 14614505) B14614505
theorem B6495335 : Blo 1923435 6495335 := bstep (se 1 (by rfl) ⟨4871501, by rfl⟩ : syracuseStep 6495335 = 9743003) B9743003
theorem B4330223 : Blo 1923435 4330223 := bstep (se 1 (by rfl) ⟨3247667, by rfl⟩ : syracuseStep 4330223 = 6495335) B6495335
theorem B2886815 : Blo 1923435 2886815 := bstep (se 1 (by rfl) ⟨2165111, by rfl⟩ : syracuseStep 2886815 = 4330223) B4330223
theorem B1924543 : Blo 1923435 1924543 := bstep (se 1 (by rfl) ⟨1443407, by rfl⟩ : syracuseStep 1924543 = 2886815) B2886815
theorem B2886821 : Blo 1923435 2886821 := bbase (se 4 (by rfl) ⟨270639, by rfl⟩ : syracuseStep 2886821 = 541279) (by norm_num)
theorem B1924547 : Blo 1923435 1924547 := bstep (se 1 (by rfl) ⟨1443410, by rfl⟩ : syracuseStep 1924547 = 2886821) B2886821
theorem B2435761 : Blo 1923435 2435761 := bbase (se 2 (by rfl) ⟨913410, by rfl⟩ : syracuseStep 2435761 = 1826821) (by norm_num)
theorem B3247681 : Blo 1923435 3247681 := bstep (se 2 (by rfl) ⟨1217880, by rfl⟩ : syracuseStep 3247681 = 2435761) B2435761
theorem B4330241 : Blo 1923435 4330241 := bstep (se 2 (by rfl) ⟨1623840, by rfl⟩ : syracuseStep 4330241 = 3247681) B3247681
theorem B2886827 : Blo 1923435 2886827 := bstep (se 1 (by rfl) ⟨2165120, by rfl⟩ : syracuseStep 2886827 = 4330241) B4330241
theorem B1924551 : Blo 1923435 1924551 := bstep (se 1 (by rfl) ⟨1443413, by rfl⟩ : syracuseStep 1924551 = 2886827) B2886827
theorem B2165125 : Blo 1923435 2165125 := bbase (se 4 (by rfl) ⟨202980, by rfl⟩ : syracuseStep 2165125 = 405961) (by norm_num)
theorem B2886833 : Blo 1923435 2886833 := bstep (se 2 (by rfl) ⟨1082562, by rfl⟩ : syracuseStep 2886833 = 2165125) B2165125
theorem B1924555 : Blo 1923435 1924555 := bstep (se 1 (by rfl) ⟨1443416, by rfl⟩ : syracuseStep 1924555 = 2886833) B2886833
theorem B4110365 : Blo 1923435 4110365 := bbase (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) (by norm_num)
theorem B2740243 : Blo 1923435 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B3653657 : Blo 1923435 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B2435771 : Blo 1923435 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B6495389 : Blo 1923435 6495389 := bstep (se 3 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 6495389 = 2435771) B2435771
theorem B4330259 : Blo 1923435 4330259 := bstep (se 1 (by rfl) ⟨3247694, by rfl⟩ : syracuseStep 4330259 = 6495389) B6495389
theorem B2886839 : Blo 1923435 2886839 := bstep (se 1 (by rfl) ⟨2165129, by rfl⟩ : syracuseStep 2886839 = 4330259) B4330259
theorem B1924559 : Blo 1923435 1924559 := bstep (se 1 (by rfl) ⟨1443419, by rfl⟩ : syracuseStep 1924559 = 2886839) B2886839
theorem B2886845 : Blo 1923435 2886845 := bbase (se 3 (by rfl) ⟨541283, by rfl⟩ : syracuseStep 2886845 = 1082567) (by norm_num)
theorem B1924563 : Blo 1923435 1924563 := bstep (se 1 (by rfl) ⟨1443422, by rfl⟩ : syracuseStep 1924563 = 2886845) B2886845
theorem B4330277 : Blo 1923435 4330277 := bbase (se 4 (by rfl) ⟨405963, by rfl⟩ : syracuseStep 4330277 = 811927) (by norm_num)
theorem B2886851 : Blo 1923435 2886851 := bstep (se 1 (by rfl) ⟨2165138, by rfl⟩ : syracuseStep 2886851 = 4330277) B4330277
theorem B1924567 : Blo 1923435 1924567 := bstep (se 1 (by rfl) ⟨1443425, by rfl⟩ : syracuseStep 1924567 = 2886851) B2886851
theorem B4871573 : Blo 1923435 4871573 := bbase (se 6 (by rfl) ⟨114177, by rfl⟩ : syracuseStep 4871573 = 228355) (by norm_num)
theorem B3247715 : Blo 1923435 3247715 := bstep (se 1 (by rfl) ⟨2435786, by rfl⟩ : syracuseStep 3247715 = 4871573) B4871573
theorem B2165143 : Blo 1923435 2165143 := bstep (se 1 (by rfl) ⟨1623857, by rfl⟩ : syracuseStep 2165143 = 3247715) B3247715
theorem B2886857 : Blo 1923435 2886857 := bstep (se 2 (by rfl) ⟨1082571, by rfl⟩ : syracuseStep 2886857 = 2165143) B2165143
theorem B1924571 : Blo 1923435 1924571 := bstep (se 1 (by rfl) ⟨1443428, by rfl⟩ : syracuseStep 1924571 = 2886857) B2886857
theorem B2469025 : Blo 1923435 2469025 := bbase (se 2 (by rfl) ⟨925884, by rfl⟩ : syracuseStep 2469025 = 1851769) (by norm_num)
theorem B13168133 : Blo 1923435 13168133 := bstep (se 4 (by rfl) ⟨1234512, by rfl⟩ : syracuseStep 13168133 = 2469025) B2469025
theorem B8778755 : Blo 1923435 8778755 := bstep (se 1 (by rfl) ⟨6584066, by rfl⟩ : syracuseStep 8778755 = 13168133) B13168133
theorem B5852503 : Blo 1923435 5852503 := bstep (se 1 (by rfl) ⟨4389377, by rfl⟩ : syracuseStep 5852503 = 8778755) B8778755
theorem B7803337 : Blo 1923435 7803337 := bstep (se 2 (by rfl) ⟨2926251, by rfl⟩ : syracuseStep 7803337 = 5852503) B5852503
theorem B10404449 : Blo 1923435 10404449 := bstep (se 2 (by rfl) ⟨3901668, by rfl⟩ : syracuseStep 10404449 = 7803337) B7803337
theorem B6936299 : Blo 1923435 6936299 := bstep (se 1 (by rfl) ⟨5202224, by rfl⟩ : syracuseStep 6936299 = 10404449) B10404449
theorem B4624199 : Blo 1923435 4624199 := bstep (se 1 (by rfl) ⟨3468149, by rfl⟩ : syracuseStep 4624199 = 6936299) B6936299
theorem B3082799 : Blo 1923435 3082799 := bstep (se 1 (by rfl) ⟨2312099, by rfl⟩ : syracuseStep 3082799 = 4624199) B4624199
theorem B8220797 : Blo 1923435 8220797 := bstep (se 3 (by rfl) ⟨1541399, by rfl⟩ : syracuseStep 8220797 = 3082799) B3082799
theorem B5480531 : Blo 1923435 5480531 := bstep (se 1 (by rfl) ⟨4110398, by rfl⟩ : syracuseStep 5480531 = 8220797) B8220797
theorem B3653687 : Blo 1923435 3653687 := bstep (se 1 (by rfl) ⟨2740265, by rfl⟩ : syracuseStep 3653687 = 5480531) B5480531
theorem B9743165 : Blo 1923435 9743165 := bstep (se 3 (by rfl) ⟨1826843, by rfl⟩ : syracuseStep 9743165 = 3653687) B3653687
theorem B6495443 : Blo 1923435 6495443 := bstep (se 1 (by rfl) ⟨4871582, by rfl⟩ : syracuseStep 6495443 = 9743165) B9743165
theorem B4330295 : Blo 1923435 4330295 := bstep (se 1 (by rfl) ⟨3247721, by rfl⟩ : syracuseStep 4330295 = 6495443) B6495443
theorem B2886863 : Blo 1923435 2886863 := bstep (se 1 (by rfl) ⟨2165147, by rfl⟩ : syracuseStep 2886863 = 4330295) B4330295
theorem B1924575 : Blo 1923435 1924575 := bstep (se 1 (by rfl) ⟨1443431, by rfl⟩ : syracuseStep 1924575 = 2886863) B2886863
theorem B2886869 : Blo 1923435 2886869 := bbase (se 7 (by rfl) ⟨33830, by rfl⟩ : syracuseStep 2886869 = 67661) (by norm_num)
theorem B1924579 : Blo 1923435 1924579 := bstep (se 1 (by rfl) ⟨1443434, by rfl⟩ : syracuseStep 1924579 = 2886869) B2886869
theorem B2740277 : Blo 1923435 2740277 := bbase (se 5 (by rfl) ⟨128450, by rfl⟩ : syracuseStep 2740277 = 256901) (by norm_num)
theorem B7307405 : Blo 1923435 7307405 := bstep (se 3 (by rfl) ⟨1370138, by rfl⟩ : syracuseStep 7307405 = 2740277) B2740277
theorem B4871603 : Blo 1923435 4871603 := bstep (se 1 (by rfl) ⟨3653702, by rfl⟩ : syracuseStep 4871603 = 7307405) B7307405
theorem B3247735 : Blo 1923435 3247735 := bstep (se 1 (by rfl) ⟨2435801, by rfl⟩ : syracuseStep 3247735 = 4871603) B4871603
theorem B4330313 : Blo 1923435 4330313 := bstep (se 2 (by rfl) ⟨1623867, by rfl⟩ : syracuseStep 4330313 = 3247735) B3247735
theorem B2886875 : Blo 1923435 2886875 := bstep (se 1 (by rfl) ⟨2165156, by rfl⟩ : syracuseStep 2886875 = 4330313) B4330313
theorem B1924583 : Blo 1923435 1924583 := bstep (se 1 (by rfl) ⟨1443437, by rfl⟩ : syracuseStep 1924583 = 2886875) B2886875
theorem B2165161 : Blo 1923435 2165161 := bbase (se 2 (by rfl) ⟨811935, by rfl⟩ : syracuseStep 2165161 = 1623871) (by norm_num)
theorem B2886881 : Blo 1923435 2886881 := bstep (se 2 (by rfl) ⟨1082580, by rfl⟩ : syracuseStep 2886881 = 2165161) B2165161
theorem B1924587 : Blo 1923435 1924587 := bstep (se 1 (by rfl) ⟨1443440, by rfl⟩ : syracuseStep 1924587 = 2886881) B2886881
theorem B4624237 : Blo 1923435 4624237 := bbase (se 3 (by rfl) ⟨867044, by rfl⟩ : syracuseStep 4624237 = 1734089) (by norm_num)
theorem B6165649 : Blo 1923435 6165649 := bstep (se 2 (by rfl) ⟨2312118, by rfl⟩ : syracuseStep 6165649 = 4624237) B4624237
theorem B8220865 : Blo 1923435 8220865 := bstep (se 2 (by rfl) ⟨3082824, by rfl⟩ : syracuseStep 8220865 = 6165649) B6165649
theorem B10961153 : Blo 1923435 10961153 := bstep (se 2 (by rfl) ⟨4110432, by rfl⟩ : syracuseStep 10961153 = 8220865) B8220865
theorem B7307435 : Blo 1923435 7307435 := bstep (se 1 (by rfl) ⟨5480576, by rfl⟩ : syracuseStep 7307435 = 10961153) B10961153
theorem B4871623 : Blo 1923435 4871623 := bstep (se 1 (by rfl) ⟨3653717, by rfl⟩ : syracuseStep 4871623 = 7307435) B7307435
theorem B6495497 : Blo 1923435 6495497 := bstep (se 2 (by rfl) ⟨2435811, by rfl⟩ : syracuseStep 6495497 = 4871623) B4871623
theorem B4330331 : Blo 1923435 4330331 := bstep (se 1 (by rfl) ⟨3247748, by rfl⟩ : syracuseStep 4330331 = 6495497) B6495497
theorem B2886887 : Blo 1923435 2886887 := bstep (se 1 (by rfl) ⟨2165165, by rfl⟩ : syracuseStep 2886887 = 4330331) B4330331
theorem B1924591 : Blo 1923435 1924591 := bstep (se 1 (by rfl) ⟨1443443, by rfl⟩ : syracuseStep 1924591 = 2886887) B2886887
theorem B2886893 : Blo 1923435 2886893 := bbase (se 3 (by rfl) ⟨541292, by rfl⟩ : syracuseStep 2886893 = 1082585) (by norm_num)
theorem B1924595 : Blo 1923435 1924595 := bstep (se 1 (by rfl) ⟨1443446, by rfl⟩ : syracuseStep 1924595 = 2886893) B2886893
theorem B4330349 : Blo 1923435 4330349 := bbase (se 3 (by rfl) ⟨811940, by rfl⟩ : syracuseStep 4330349 = 1623881) (by norm_num)
theorem B2886899 : Blo 1923435 2886899 := bstep (se 1 (by rfl) ⟨2165174, by rfl⟩ : syracuseStep 2886899 = 4330349) B4330349
theorem B1924599 : Blo 1923435 1924599 := bstep (se 1 (by rfl) ⟨1443449, by rfl⟩ : syracuseStep 1924599 = 2886899) B2886899
theorem B3653741 : Blo 1923435 3653741 := bbase (se 3 (by rfl) ⟨685076, by rfl⟩ : syracuseStep 3653741 = 1370153) (by norm_num)
theorem B2435827 : Blo 1923435 2435827 := bstep (se 1 (by rfl) ⟨1826870, by rfl⟩ : syracuseStep 2435827 = 3653741) B3653741
theorem B3247769 : Blo 1923435 3247769 := bstep (se 2 (by rfl) ⟨1217913, by rfl⟩ : syracuseStep 3247769 = 2435827) B2435827
theorem B2165179 : Blo 1923435 2165179 := bstep (se 1 (by rfl) ⟨1623884, by rfl⟩ : syracuseStep 2165179 = 3247769) B3247769
theorem B2886905 : Blo 1923435 2886905 := bstep (se 2 (by rfl) ⟨1082589, by rfl⟩ : syracuseStep 2886905 = 2165179) B2165179
theorem B1924603 : Blo 1923435 1924603 := bstep (se 1 (by rfl) ⟨1443452, by rfl⟩ : syracuseStep 1924603 = 2886905) B2886905
theorem B20809237 : Blo 1923435 20809237 := bbase (se 6 (by rfl) ⟨487716, by rfl⟩ : syracuseStep 20809237 = 975433) (by norm_num)
theorem B27745649 : Blo 1923435 27745649 := bstep (se 2 (by rfl) ⟨10404618, by rfl⟩ : syracuseStep 27745649 = 20809237) B20809237
theorem B18497099 : Blo 1923435 18497099 := bstep (se 1 (by rfl) ⟨13872824, by rfl⟩ : syracuseStep 18497099 = 27745649) B27745649
theorem B49325597 : Blo 1923435 49325597 := bstep (se 3 (by rfl) ⟨9248549, by rfl⟩ : syracuseStep 49325597 = 18497099) B18497099
theorem B32883731 : Blo 1923435 32883731 := bstep (se 1 (by rfl) ⟨24662798, by rfl⟩ : syracuseStep 32883731 = 49325597) B49325597
theorem B21922487 : Blo 1923435 21922487 := bstep (se 1 (by rfl) ⟨16441865, by rfl⟩ : syracuseStep 21922487 = 32883731) B32883731
theorem B14614991 : Blo 1923435 14614991 := bstep (se 1 (by rfl) ⟨10961243, by rfl⟩ : syracuseStep 14614991 = 21922487) B21922487
theorem B9743327 : Blo 1923435 9743327 := bstep (se 1 (by rfl) ⟨7307495, by rfl⟩ : syracuseStep 9743327 = 14614991) B14614991
theorem B6495551 : Blo 1923435 6495551 := bstep (se 1 (by rfl) ⟨4871663, by rfl⟩ : syracuseStep 6495551 = 9743327) B9743327
theorem B4330367 : Blo 1923435 4330367 := bstep (se 1 (by rfl) ⟨3247775, by rfl⟩ : syracuseStep 4330367 = 6495551) B6495551
theorem B2886911 : Blo 1923435 2886911 := bstep (se 1 (by rfl) ⟨2165183, by rfl⟩ : syracuseStep 2886911 = 4330367) B4330367
theorem B1924607 : Blo 1923435 1924607 := bstep (se 1 (by rfl) ⟨1443455, by rfl⟩ : syracuseStep 1924607 = 2886911) B2886911
theorem B2886917 : Blo 1923435 2886917 := bbase (se 4 (by rfl) ⟨270648, by rfl⟩ : syracuseStep 2886917 = 541297) (by norm_num)
theorem B1924611 : Blo 1923435 1924611 := bstep (se 1 (by rfl) ⟨1443458, by rfl⟩ : syracuseStep 1924611 = 2886917) B2886917
theorem B3247789 : Blo 1923435 3247789 := bbase (se 3 (by rfl) ⟨608960, by rfl⟩ : syracuseStep 3247789 = 1217921) (by norm_num)
theorem B4330385 : Blo 1923435 4330385 := bstep (se 2 (by rfl) ⟨1623894, by rfl⟩ : syracuseStep 4330385 = 3247789) B3247789
theorem B2886923 : Blo 1923435 2886923 := bstep (se 1 (by rfl) ⟨2165192, by rfl⟩ : syracuseStep 2886923 = 4330385) B4330385
theorem B1924615 : Blo 1923435 1924615 := bstep (se 1 (by rfl) ⟨1443461, by rfl⟩ : syracuseStep 1924615 = 2886923) B2886923
theorem B2165197 : Blo 1923435 2165197 := bbase (se 3 (by rfl) ⟨405974, by rfl⟩ : syracuseStep 2165197 = 811949) (by norm_num)
theorem B2886929 : Blo 1923435 2886929 := bstep (se 2 (by rfl) ⟨1082598, by rfl⟩ : syracuseStep 2886929 = 2165197) B2165197
theorem B1924619 : Blo 1923435 1924619 := bstep (se 1 (by rfl) ⟨1443464, by rfl⟩ : syracuseStep 1924619 = 2886929) B2886929
theorem B6495605 : Blo 1923435 6495605 := bbase (se 5 (by rfl) ⟨304481, by rfl⟩ : syracuseStep 6495605 = 608963) (by norm_num)
theorem B4330403 : Blo 1923435 4330403 := bstep (se 1 (by rfl) ⟨3247802, by rfl⟩ : syracuseStep 4330403 = 6495605) B6495605
theorem B2886935 : Blo 1923435 2886935 := bstep (se 1 (by rfl) ⟨2165201, by rfl⟩ : syracuseStep 2886935 = 4330403) B4330403
theorem B1924623 : Blo 1923435 1924623 := bstep (se 1 (by rfl) ⟨1443467, by rfl⟩ : syracuseStep 1924623 = 2886935) B2886935
theorem B2886941 : Blo 1923435 2886941 := bbase (se 3 (by rfl) ⟨541301, by rfl⟩ : syracuseStep 2886941 = 1082603) (by norm_num)
theorem B1924627 : Blo 1923435 1924627 := bstep (se 1 (by rfl) ⟨1443470, by rfl⟩ : syracuseStep 1924627 = 2886941) B2886941
theorem B4330421 : Blo 1923435 4330421 := bbase (se 5 (by rfl) ⟨202988, by rfl⟩ : syracuseStep 4330421 = 405977) (by norm_num)
theorem B2886947 : Blo 1923435 2886947 := bstep (se 1 (by rfl) ⟨2165210, by rfl⟩ : syracuseStep 2886947 = 4330421) B4330421
theorem B1924631 : Blo 1923435 1924631 := bstep (se 1 (by rfl) ⟨1443473, by rfl⟩ : syracuseStep 1924631 = 2886947) B2886947
theorem B2194757 : Blo 1923435 2194757 := bbase (se 4 (by rfl) ⟨205758, by rfl⟩ : syracuseStep 2194757 = 411517) (by norm_num)
theorem B23410741 : Blo 1923435 23410741 := bstep (se 5 (by rfl) ⟨1097378, by rfl⟩ : syracuseStep 23410741 = 2194757) B2194757
theorem B31214321 : Blo 1923435 31214321 := bstep (se 2 (by rfl) ⟨11705370, by rfl⟩ : syracuseStep 31214321 = 23410741) B23410741
theorem B20809547 : Blo 1923435 20809547 := bstep (se 1 (by rfl) ⟨15607160, by rfl⟩ : syracuseStep 20809547 = 31214321) B31214321
theorem B13873031 : Blo 1923435 13873031 := bstep (se 1 (by rfl) ⟨10404773, by rfl⟩ : syracuseStep 13873031 = 20809547) B20809547
theorem B9248687 : Blo 1923435 9248687 := bstep (se 1 (by rfl) ⟨6936515, by rfl⟩ : syracuseStep 9248687 = 13873031) B13873031
theorem B6165791 : Blo 1923435 6165791 := bstep (se 1 (by rfl) ⟨4624343, by rfl⟩ : syracuseStep 6165791 = 9248687) B9248687
theorem B4110527 : Blo 1923435 4110527 := bstep (se 1 (by rfl) ⟨3082895, by rfl⟩ : syracuseStep 4110527 = 6165791) B6165791
theorem B10961405 : Blo 1923435 10961405 := bstep (se 3 (by rfl) ⟨2055263, by rfl⟩ : syracuseStep 10961405 = 4110527) B4110527
theorem B7307603 : Blo 1923435 7307603 := bstep (se 1 (by rfl) ⟨5480702, by rfl⟩ : syracuseStep 7307603 = 10961405) B10961405
theorem B4871735 : Blo 1923435 4871735 := bstep (se 1 (by rfl) ⟨3653801, by rfl⟩ : syracuseStep 4871735 = 7307603) B7307603
theorem B3247823 : Blo 1923435 3247823 := bstep (se 1 (by rfl) ⟨2435867, by rfl⟩ : syracuseStep 3247823 = 4871735) B4871735
theorem B2165215 : Blo 1923435 2165215 := bstep (se 1 (by rfl) ⟨1623911, by rfl⟩ : syracuseStep 2165215 = 3247823) B3247823
theorem B2886953 : Blo 1923435 2886953 := bstep (se 2 (by rfl) ⟨1082607, by rfl⟩ : syracuseStep 2886953 = 2165215) B2165215
theorem B1924635 : Blo 1923435 1924635 := bstep (se 1 (by rfl) ⟨1443476, by rfl⟩ : syracuseStep 1924635 = 2886953) B2886953
theorem B2926349 : Blo 1923435 2926349 := bbase (se 3 (by rfl) ⟨548690, by rfl⟩ : syracuseStep 2926349 = 1097381) (by norm_num)
theorem B1950899 : Blo 1923435 1950899 := bstep (se 1 (by rfl) ⟨1463174, by rfl⟩ : syracuseStep 1950899 = 2926349) B2926349
theorem B5202397 : Blo 1923435 5202397 := bstep (se 3 (by rfl) ⟨975449, by rfl⟩ : syracuseStep 5202397 = 1950899) B1950899
theorem B6936529 : Blo 1923435 6936529 := bstep (se 2 (by rfl) ⟨2601198, by rfl⟩ : syracuseStep 6936529 = 5202397) B5202397
theorem B9248705 : Blo 1923435 9248705 := bstep (se 2 (by rfl) ⟨3468264, by rfl⟩ : syracuseStep 9248705 = 6936529) B6936529
theorem B6165803 : Blo 1923435 6165803 := bstep (se 1 (by rfl) ⟨4624352, by rfl⟩ : syracuseStep 6165803 = 9248705) B9248705
theorem B4110535 : Blo 1923435 4110535 := bstep (se 1 (by rfl) ⟨3082901, by rfl⟩ : syracuseStep 4110535 = 6165803) B6165803
theorem B5480713 : Blo 1923435 5480713 := bstep (se 2 (by rfl) ⟨2055267, by rfl⟩ : syracuseStep 5480713 = 4110535) B4110535
theorem B7307617 : Blo 1923435 7307617 := bstep (se 2 (by rfl) ⟨2740356, by rfl⟩ : syracuseStep 7307617 = 5480713) B5480713
theorem B9743489 : Blo 1923435 9743489 := bstep (se 2 (by rfl) ⟨3653808, by rfl⟩ : syracuseStep 9743489 = 7307617) B7307617
theorem B6495659 : Blo 1923435 6495659 := bstep (se 1 (by rfl) ⟨4871744, by rfl⟩ : syracuseStep 6495659 = 9743489) B9743489
theorem B4330439 : Blo 1923435 4330439 := bstep (se 1 (by rfl) ⟨3247829, by rfl⟩ : syracuseStep 4330439 = 6495659) B6495659
theorem B2886959 : Blo 1923435 2886959 := bstep (se 1 (by rfl) ⟨2165219, by rfl⟩ : syracuseStep 2886959 = 4330439) B4330439
theorem B1924639 : Blo 1923435 1924639 := bstep (se 1 (by rfl) ⟨1443479, by rfl⟩ : syracuseStep 1924639 = 2886959) B2886959
theorem B2886965 : Blo 1923435 2886965 := bbase (se 5 (by rfl) ⟨135326, by rfl⟩ : syracuseStep 2886965 = 270653) (by norm_num)
theorem B1924643 : Blo 1923435 1924643 := bstep (se 1 (by rfl) ⟨1443482, by rfl⟩ : syracuseStep 1924643 = 2886965) B2886965
theorem B4871765 : Blo 1923435 4871765 := bbase (se 8 (by rfl) ⟨28545, by rfl⟩ : syracuseStep 4871765 = 57091) (by norm_num)
theorem B3247843 : Blo 1923435 3247843 := bstep (se 1 (by rfl) ⟨2435882, by rfl⟩ : syracuseStep 3247843 = 4871765) B4871765
theorem B4330457 : Blo 1923435 4330457 := bstep (se 2 (by rfl) ⟨1623921, by rfl⟩ : syracuseStep 4330457 = 3247843) B3247843
theorem B2886971 : Blo 1923435 2886971 := bstep (se 1 (by rfl) ⟨2165228, by rfl⟩ : syracuseStep 2886971 = 4330457) B4330457
theorem B1924647 : Blo 1923435 1924647 := bstep (se 1 (by rfl) ⟨1443485, by rfl⟩ : syracuseStep 1924647 = 2886971) B2886971
theorem B2165233 : Blo 1923435 2165233 := bbase (se 2 (by rfl) ⟨811962, by rfl⟩ : syracuseStep 2165233 = 1623925) (by norm_num)
theorem B2886977 : Blo 1923435 2886977 := bstep (se 2 (by rfl) ⟨1082616, by rfl⟩ : syracuseStep 2886977 = 2165233) B2165233
theorem B1924651 : Blo 1923435 1924651 := bstep (se 1 (by rfl) ⟨1443488, by rfl⟩ : syracuseStep 1924651 = 2886977) B2886977
theorem B2926373 : Blo 1923435 2926373 := bbase (se 4 (by rfl) ⟨274347, by rfl⟩ : syracuseStep 2926373 = 548695) (by norm_num)
theorem B7803661 : Blo 1923435 7803661 := bstep (se 3 (by rfl) ⟨1463186, by rfl⟩ : syracuseStep 7803661 = 2926373) B2926373
theorem B10404881 : Blo 1923435 10404881 := bstep (se 2 (by rfl) ⟨3901830, by rfl⟩ : syracuseStep 10404881 = 7803661) B7803661
theorem B6936587 : Blo 1923435 6936587 := bstep (se 1 (by rfl) ⟨5202440, by rfl⟩ : syracuseStep 6936587 = 10404881) B10404881
theorem B4624391 : Blo 1923435 4624391 := bstep (se 1 (by rfl) ⟨3468293, by rfl⟩ : syracuseStep 4624391 = 6936587) B6936587
theorem B12331709 : Blo 1923435 12331709 := bstep (se 3 (by rfl) ⟨2312195, by rfl⟩ : syracuseStep 12331709 = 4624391) B4624391
theorem B8221139 : Blo 1923435 8221139 := bstep (se 1 (by rfl) ⟨6165854, by rfl⟩ : syracuseStep 8221139 = 12331709) B12331709
theorem B5480759 : Blo 1923435 5480759 := bstep (se 1 (by rfl) ⟨4110569, by rfl⟩ : syracuseStep 5480759 = 8221139) B8221139
theorem B3653839 : Blo 1923435 3653839 := bstep (se 1 (by rfl) ⟨2740379, by rfl⟩ : syracuseStep 3653839 = 5480759) B5480759
theorem B4871785 : Blo 1923435 4871785 := bstep (se 2 (by rfl) ⟨1826919, by rfl⟩ : syracuseStep 4871785 = 3653839) B3653839
theorem B6495713 : Blo 1923435 6495713 := bstep (se 2 (by rfl) ⟨2435892, by rfl⟩ : syracuseStep 6495713 = 4871785) B4871785
theorem B4330475 : Blo 1923435 4330475 := bstep (se 1 (by rfl) ⟨3247856, by rfl⟩ : syracuseStep 4330475 = 6495713) B6495713
theorem B2886983 : Blo 1923435 2886983 := bstep (se 1 (by rfl) ⟨2165237, by rfl⟩ : syracuseStep 2886983 = 4330475) B4330475
theorem B1924655 : Blo 1923435 1924655 := bstep (se 1 (by rfl) ⟨1443491, by rfl⟩ : syracuseStep 1924655 = 2886983) B2886983
theorem B2886989 : Blo 1923435 2886989 := bbase (se 3 (by rfl) ⟨541310, by rfl⟩ : syracuseStep 2886989 = 1082621) (by norm_num)
theorem B1924659 : Blo 1923435 1924659 := bstep (se 1 (by rfl) ⟨1443494, by rfl⟩ : syracuseStep 1924659 = 2886989) B2886989
theorem B4330493 : Blo 1923435 4330493 := bbase (se 3 (by rfl) ⟨811967, by rfl⟩ : syracuseStep 4330493 = 1623935) (by norm_num)
theorem B2886995 : Blo 1923435 2886995 := bstep (se 1 (by rfl) ⟨2165246, by rfl⟩ : syracuseStep 2886995 = 4330493) B4330493
theorem B1924663 : Blo 1923435 1924663 := bstep (se 1 (by rfl) ⟨1443497, by rfl⟩ : syracuseStep 1924663 = 2886995) B2886995
theorem B3247877 : Blo 1923435 3247877 := bbase (se 4 (by rfl) ⟨304488, by rfl⟩ : syracuseStep 3247877 = 608977) (by norm_num)
theorem B2165251 : Blo 1923435 2165251 := bstep (se 1 (by rfl) ⟨1623938, by rfl⟩ : syracuseStep 2165251 = 3247877) B3247877
theorem B2887001 : Blo 1923435 2887001 := bstep (se 2 (by rfl) ⟨1082625, by rfl⟩ : syracuseStep 2887001 = 2165251) B2165251
theorem B1924667 : Blo 1923435 1924667 := bstep (se 1 (by rfl) ⟨1443500, by rfl⟩ : syracuseStep 1924667 = 2887001) B2887001
theorem B14615477 : Blo 1923435 14615477 := bbase (se 5 (by rfl) ⟨685100, by rfl⟩ : syracuseStep 14615477 = 1370201) (by norm_num)
theorem B9743651 : Blo 1923435 9743651 := bstep (se 1 (by rfl) ⟨7307738, by rfl⟩ : syracuseStep 9743651 = 14615477) B14615477
theorem B6495767 : Blo 1923435 6495767 := bstep (se 1 (by rfl) ⟨4871825, by rfl⟩ : syracuseStep 6495767 = 9743651) B9743651
theorem B4330511 : Blo 1923435 4330511 := bstep (se 1 (by rfl) ⟨3247883, by rfl⟩ : syracuseStep 4330511 = 6495767) B6495767
theorem B2887007 : Blo 1923435 2887007 := bstep (se 1 (by rfl) ⟨2165255, by rfl⟩ : syracuseStep 2887007 = 4330511) B4330511
theorem B1924671 : Blo 1923435 1924671 := bstep (se 1 (by rfl) ⟨1443503, by rfl⟩ : syracuseStep 1924671 = 2887007) B2887007
theorem B2887013 : Blo 1923435 2887013 := bbase (se 4 (by rfl) ⟨270657, by rfl⟩ : syracuseStep 2887013 = 541315) (by norm_num)
theorem B1924675 : Blo 1923435 1924675 := bstep (se 1 (by rfl) ⟨1443506, by rfl⟩ : syracuseStep 1924675 = 2887013) B2887013
theorem B3653885 : Blo 1923435 3653885 := bbase (se 3 (by rfl) ⟨685103, by rfl⟩ : syracuseStep 3653885 = 1370207) (by norm_num)
theorem B2435923 : Blo 1923435 2435923 := bstep (se 1 (by rfl) ⟨1826942, by rfl⟩ : syracuseStep 2435923 = 3653885) B3653885
theorem B3247897 : Blo 1923435 3247897 := bstep (se 2 (by rfl) ⟨1217961, by rfl⟩ : syracuseStep 3247897 = 2435923) B2435923
theorem B4330529 : Blo 1923435 4330529 := bstep (se 2 (by rfl) ⟨1623948, by rfl⟩ : syracuseStep 4330529 = 3247897) B3247897
theorem B2887019 : Blo 1923435 2887019 := bstep (se 1 (by rfl) ⟨2165264, by rfl⟩ : syracuseStep 2887019 = 4330529) B4330529
theorem B1924679 : Blo 1923435 1924679 := bstep (se 1 (by rfl) ⟨1443509, by rfl⟩ : syracuseStep 1924679 = 2887019) B2887019
theorem B2165269 : Blo 1923435 2165269 := bbase (se 6 (by rfl) ⟨50748, by rfl⟩ : syracuseStep 2165269 = 101497) (by norm_num)
theorem B2887025 : Blo 1923435 2887025 := bstep (se 2 (by rfl) ⟨1082634, by rfl⟩ : syracuseStep 2887025 = 2165269) B2165269
theorem B1924683 : Blo 1923435 1924683 := bstep (se 1 (by rfl) ⟨1443512, by rfl⟩ : syracuseStep 1924683 = 2887025) B2887025
theorem B2435933 : Blo 1923435 2435933 := bbase (se 3 (by rfl) ⟨456737, by rfl⟩ : syracuseStep 2435933 = 913475) (by norm_num)
theorem B6495821 : Blo 1923435 6495821 := bstep (se 3 (by rfl) ⟨1217966, by rfl⟩ : syracuseStep 6495821 = 2435933) B2435933
theorem B4330547 : Blo 1923435 4330547 := bstep (se 1 (by rfl) ⟨3247910, by rfl⟩ : syracuseStep 4330547 = 6495821) B6495821
theorem B2887031 : Blo 1923435 2887031 := bstep (se 1 (by rfl) ⟨2165273, by rfl⟩ : syracuseStep 2887031 = 4330547) B4330547
theorem B1924687 : Blo 1923435 1924687 := bstep (se 1 (by rfl) ⟨1443515, by rfl⟩ : syracuseStep 1924687 = 2887031) B2887031
theorem B2887037 : Blo 1923435 2887037 := bbase (se 3 (by rfl) ⟨541319, by rfl⟩ : syracuseStep 2887037 = 1082639) (by norm_num)
theorem B1924691 : Blo 1923435 1924691 := bstep (se 1 (by rfl) ⟨1443518, by rfl⟩ : syracuseStep 1924691 = 2887037) B2887037
theorem B4330565 : Blo 1923435 4330565 := bbase (se 4 (by rfl) ⟨405990, by rfl⟩ : syracuseStep 4330565 = 811981) (by norm_num)
theorem B2887043 : Blo 1923435 2887043 := bstep (se 1 (by rfl) ⟨2165282, by rfl⟩ : syracuseStep 2887043 = 4330565) B4330565
theorem B1924695 : Blo 1923435 1924695 := bstep (se 1 (by rfl) ⟨1443521, by rfl⟩ : syracuseStep 1924695 = 2887043) B2887043
theorem B5480885 : Blo 1923435 5480885 := bbase (se 5 (by rfl) ⟨256916, by rfl⟩ : syracuseStep 5480885 = 513833) (by norm_num)
theorem B3653923 : Blo 1923435 3653923 := bstep (se 1 (by rfl) ⟨2740442, by rfl⟩ : syracuseStep 3653923 = 5480885) B5480885
theorem B4871897 : Blo 1923435 4871897 := bstep (se 2 (by rfl) ⟨1826961, by rfl⟩ : syracuseStep 4871897 = 3653923) B3653923
theorem B3247931 : Blo 1923435 3247931 := bstep (se 1 (by rfl) ⟨2435948, by rfl⟩ : syracuseStep 3247931 = 4871897) B4871897
theorem B2165287 : Blo 1923435 2165287 := bstep (se 1 (by rfl) ⟨1623965, by rfl⟩ : syracuseStep 2165287 = 3247931) B3247931
theorem B2887049 : Blo 1923435 2887049 := bstep (se 2 (by rfl) ⟨1082643, by rfl⟩ : syracuseStep 2887049 = 2165287) B2165287
theorem B1924699 : Blo 1923435 1924699 := bstep (se 1 (by rfl) ⟨1443524, by rfl⟩ : syracuseStep 1924699 = 2887049) B2887049
theorem B9743813 : Blo 1923435 9743813 := bbase (se 4 (by rfl) ⟨913482, by rfl⟩ : syracuseStep 9743813 = 1826965) (by norm_num)
theorem B6495875 : Blo 1923435 6495875 := bstep (se 1 (by rfl) ⟨4871906, by rfl⟩ : syracuseStep 6495875 = 9743813) B9743813
theorem B4330583 : Blo 1923435 4330583 := bstep (se 1 (by rfl) ⟨3247937, by rfl⟩ : syracuseStep 4330583 = 6495875) B6495875
theorem B2887055 : Blo 1923435 2887055 := bstep (se 1 (by rfl) ⟨2165291, by rfl⟩ : syracuseStep 2887055 = 4330583) B4330583
theorem B1924703 : Blo 1923435 1924703 := bstep (se 1 (by rfl) ⟨1443527, by rfl⟩ : syracuseStep 1924703 = 2887055) B2887055
theorem B2887061 : Blo 1923435 2887061 := bbase (se 6 (by rfl) ⟨67665, by rfl⟩ : syracuseStep 2887061 = 135331) (by norm_num)
theorem B1924707 : Blo 1923435 1924707 := bstep (se 1 (by rfl) ⟨1443530, by rfl⟩ : syracuseStep 1924707 = 2887061) B2887061
theorem B13018997 : Blo 1923435 13018997 := bbase (se 5 (by rfl) ⟨610265, by rfl⟩ : syracuseStep 13018997 = 1220531) (by norm_num)
theorem B8679331 : Blo 1923435 8679331 := bstep (se 1 (by rfl) ⟨6509498, by rfl⟩ : syracuseStep 8679331 = 13018997) B13018997
theorem B46289765 : Blo 1923435 46289765 := bstep (se 4 (by rfl) ⟨4339665, by rfl⟩ : syracuseStep 46289765 = 8679331) B8679331
theorem B123439373 : Blo 1923435 123439373 := bstep (se 3 (by rfl) ⟨23144882, by rfl⟩ : syracuseStep 123439373 = 46289765) B46289765
theorem B82292915 : Blo 1923435 82292915 := bstep (se 1 (by rfl) ⟨61719686, by rfl⟩ : syracuseStep 82292915 = 123439373) B123439373
theorem B54861943 : Blo 1923435 54861943 := bstep (se 1 (by rfl) ⟨41146457, by rfl⟩ : syracuseStep 54861943 = 82292915) B82292915
theorem B73149257 : Blo 1923435 73149257 := bstep (se 2 (by rfl) ⟨27430971, by rfl⟩ : syracuseStep 73149257 = 54861943) B54861943
theorem B48766171 : Blo 1923435 48766171 := bstep (se 1 (by rfl) ⟨36574628, by rfl⟩ : syracuseStep 48766171 = 73149257) B73149257
theorem B65021561 : Blo 1923435 65021561 := bstep (se 2 (by rfl) ⟨24383085, by rfl⟩ : syracuseStep 65021561 = 48766171) B48766171
theorem B43347707 : Blo 1923435 43347707 := bstep (se 1 (by rfl) ⟨32510780, by rfl⟩ : syracuseStep 43347707 = 65021561) B65021561
theorem B28898471 : Blo 1923435 28898471 := bstep (se 1 (by rfl) ⟨21673853, by rfl⟩ : syracuseStep 28898471 = 43347707) B43347707
theorem B77062589 : Blo 1923435 77062589 := bstep (se 3 (by rfl) ⟨14449235, by rfl⟩ : syracuseStep 77062589 = 28898471) B28898471
theorem B51375059 : Blo 1923435 51375059 := bstep (se 1 (by rfl) ⟨38531294, by rfl⟩ : syracuseStep 51375059 = 77062589) B77062589
theorem B34250039 : Blo 1923435 34250039 := bstep (se 1 (by rfl) ⟨25687529, by rfl⟩ : syracuseStep 34250039 = 51375059) B51375059
theorem B22833359 : Blo 1923435 22833359 := bstep (se 1 (by rfl) ⟨17125019, by rfl⟩ : syracuseStep 22833359 = 34250039) B34250039
theorem B15222239 : Blo 1923435 15222239 := bstep (se 1 (by rfl) ⟨11416679, by rfl⟩ : syracuseStep 15222239 = 22833359) B22833359
theorem B10148159 : Blo 1923435 10148159 := bstep (se 1 (by rfl) ⟨7611119, by rfl⟩ : syracuseStep 10148159 = 15222239) B15222239
theorem B6765439 : Blo 1923435 6765439 := bstep (se 1 (by rfl) ⟨5074079, by rfl⟩ : syracuseStep 6765439 = 10148159) B10148159
theorem B9020585 : Blo 1923435 9020585 := bstep (se 2 (by rfl) ⟨3382719, by rfl⟩ : syracuseStep 9020585 = 6765439) B6765439
theorem B6013723 : Blo 1923435 6013723 := bstep (se 1 (by rfl) ⟨4510292, by rfl⟩ : syracuseStep 6013723 = 9020585) B9020585
theorem B8018297 : Blo 1923435 8018297 := bstep (se 2 (by rfl) ⟨3006861, by rfl⟩ : syracuseStep 8018297 = 6013723) B6013723
theorem B5345531 : Blo 1923435 5345531 := bstep (se 1 (by rfl) ⟨4009148, by rfl⟩ : syracuseStep 5345531 = 8018297) B8018297
theorem B3563687 : Blo 1923435 3563687 := bstep (se 1 (by rfl) ⟨2672765, by rfl⟩ : syracuseStep 3563687 = 5345531) B5345531
theorem B9503165 : Blo 1923435 9503165 := bstep (se 3 (by rfl) ⟨1781843, by rfl⟩ : syracuseStep 9503165 = 3563687) B3563687
theorem B6335443 : Blo 1923435 6335443 := bstep (se 1 (by rfl) ⟨4751582, by rfl⟩ : syracuseStep 6335443 = 9503165) B9503165
theorem B8447257 : Blo 1923435 8447257 := bstep (se 2 (by rfl) ⟨3167721, by rfl⟩ : syracuseStep 8447257 = 6335443) B6335443
theorem B11263009 : Blo 1923435 11263009 := bstep (se 2 (by rfl) ⟨4223628, by rfl⟩ : syracuseStep 11263009 = 8447257) B8447257
theorem B15017345 : Blo 1923435 15017345 := bstep (se 2 (by rfl) ⟨5631504, by rfl⟩ : syracuseStep 15017345 = 11263009) B11263009
theorem B10011563 : Blo 1923435 10011563 := bstep (se 1 (by rfl) ⟨7508672, by rfl⟩ : syracuseStep 10011563 = 15017345) B15017345
theorem B6674375 : Blo 1923435 6674375 := bstep (se 1 (by rfl) ⟨5005781, by rfl⟩ : syracuseStep 6674375 = 10011563) B10011563
theorem B4449583 : Blo 1923435 4449583 := bstep (se 1 (by rfl) ⟨3337187, by rfl⟩ : syracuseStep 4449583 = 6674375) B6674375
theorem B5932777 : Blo 1923435 5932777 := bstep (se 2 (by rfl) ⟨2224791, by rfl⟩ : syracuseStep 5932777 = 4449583) B4449583
theorem B7910369 : Blo 1923435 7910369 := bstep (se 2 (by rfl) ⟨2966388, by rfl⟩ : syracuseStep 7910369 = 5932777) B5932777
theorem B5273579 : Blo 1923435 5273579 := bstep (se 1 (by rfl) ⟨3955184, by rfl⟩ : syracuseStep 5273579 = 7910369) B7910369
theorem B3515719 : Blo 1923435 3515719 := bstep (se 1 (by rfl) ⟨2636789, by rfl⟩ : syracuseStep 3515719 = 5273579) B5273579
theorem B4687625 : Blo 1923435 4687625 := bstep (se 2 (by rfl) ⟨1757859, by rfl⟩ : syracuseStep 4687625 = 3515719) B3515719
theorem B3125083 : Blo 1923435 3125083 := bstep (se 1 (by rfl) ⟨2343812, by rfl⟩ : syracuseStep 3125083 = 4687625) B4687625
theorem B4166777 : Blo 1923435 4166777 := bstep (se 2 (by rfl) ⟨1562541, by rfl⟩ : syracuseStep 4166777 = 3125083) B3125083
theorem B2777851 : Blo 1923435 2777851 := bstep (se 1 (by rfl) ⟨2083388, by rfl⟩ : syracuseStep 2777851 = 4166777) B4166777
theorem B3703801 : Blo 1923435 3703801 := bstep (se 2 (by rfl) ⟨1388925, by rfl⟩ : syracuseStep 3703801 = 2777851) B2777851
theorem B4938401 : Blo 1923435 4938401 := bstep (se 2 (by rfl) ⟨1851900, by rfl⟩ : syracuseStep 4938401 = 3703801) B3703801
theorem B3292267 : Blo 1923435 3292267 := bstep (se 1 (by rfl) ⟨2469200, by rfl⟩ : syracuseStep 3292267 = 4938401) B4938401
theorem B4389689 : Blo 1923435 4389689 := bstep (se 2 (by rfl) ⟨1646133, by rfl⟩ : syracuseStep 4389689 = 3292267) B3292267
theorem B2926459 : Blo 1923435 2926459 := bstep (se 1 (by rfl) ⟨2194844, by rfl⟩ : syracuseStep 2926459 = 4389689) B4389689
theorem B3901945 : Blo 1923435 3901945 := bstep (se 2 (by rfl) ⟨1463229, by rfl⟩ : syracuseStep 3901945 = 2926459) B2926459
theorem B5202593 : Blo 1923435 5202593 := bstep (se 2 (by rfl) ⟨1950972, by rfl⟩ : syracuseStep 5202593 = 3901945) B3901945
theorem B3468395 : Blo 1923435 3468395 := bstep (se 1 (by rfl) ⟨2601296, by rfl⟩ : syracuseStep 3468395 = 5202593) B5202593
theorem B2312263 : Blo 1923435 2312263 := bstep (se 1 (by rfl) ⟨1734197, by rfl⟩ : syracuseStep 2312263 = 3468395) B3468395
theorem B3083017 : Blo 1923435 3083017 := bstep (se 2 (by rfl) ⟨1156131, by rfl⟩ : syracuseStep 3083017 = 2312263) B2312263
theorem B4110689 : Blo 1923435 4110689 := bstep (se 2 (by rfl) ⟨1541508, by rfl⟩ : syracuseStep 4110689 = 3083017) B3083017
theorem B10961837 : Blo 1923435 10961837 := bstep (se 3 (by rfl) ⟨2055344, by rfl⟩ : syracuseStep 10961837 = 4110689) B4110689
theorem B7307891 : Blo 1923435 7307891 := bstep (se 1 (by rfl) ⟨5480918, by rfl⟩ : syracuseStep 7307891 = 10961837) B10961837
theorem B4871927 : Blo 1923435 4871927 := bstep (se 1 (by rfl) ⟨3653945, by rfl⟩ : syracuseStep 4871927 = 7307891) B7307891
theorem B3247951 : Blo 1923435 3247951 := bstep (se 1 (by rfl) ⟨2435963, by rfl⟩ : syracuseStep 3247951 = 4871927) B4871927
theorem B4330601 : Blo 1923435 4330601 := bstep (se 2 (by rfl) ⟨1623975, by rfl⟩ : syracuseStep 4330601 = 3247951) B3247951
theorem B2887067 : Blo 1923435 2887067 := bstep (se 1 (by rfl) ⟨2165300, by rfl⟩ : syracuseStep 2887067 = 4330601) B4330601
theorem B1924711 : Blo 1923435 1924711 := bstep (se 1 (by rfl) ⟨1443533, by rfl⟩ : syracuseStep 1924711 = 2887067) B2887067
theorem B2165305 : Blo 1923435 2165305 := bbase (se 2 (by rfl) ⟨811989, by rfl⟩ : syracuseStep 2165305 = 1623979) (by norm_num)
theorem B2887073 : Blo 1923435 2887073 := bstep (se 2 (by rfl) ⟨1082652, by rfl⟩ : syracuseStep 2887073 = 2165305) B2165305
theorem B1924715 : Blo 1923435 1924715 := bstep (se 1 (by rfl) ⟨1443536, by rfl⟩ : syracuseStep 1924715 = 2887073) B2887073
theorem B2055353 : Blo 1923435 2055353 := bbase (se 2 (by rfl) ⟨770757, by rfl⟩ : syracuseStep 2055353 = 1541515) (by norm_num)
theorem B5480941 : Blo 1923435 5480941 := bstep (se 3 (by rfl) ⟨1027676, by rfl⟩ : syracuseStep 5480941 = 2055353) B2055353
theorem B7307921 : Blo 1923435 7307921 := bstep (se 2 (by rfl) ⟨2740470, by rfl⟩ : syracuseStep 7307921 = 5480941) B5480941
theorem B4871947 : Blo 1923435 4871947 := bstep (se 1 (by rfl) ⟨3653960, by rfl⟩ : syracuseStep 4871947 = 7307921) B7307921
theorem B6495929 : Blo 1923435 6495929 := bstep (se 2 (by rfl) ⟨2435973, by rfl⟩ : syracuseStep 6495929 = 4871947) B4871947
theorem B4330619 : Blo 1923435 4330619 := bstep (se 1 (by rfl) ⟨3247964, by rfl⟩ : syracuseStep 4330619 = 6495929) B6495929
theorem B2887079 : Blo 1923435 2887079 := bstep (se 1 (by rfl) ⟨2165309, by rfl⟩ : syracuseStep 2887079 = 4330619) B4330619
theorem B1924719 : Blo 1923435 1924719 := bstep (se 1 (by rfl) ⟨1443539, by rfl⟩ : syracuseStep 1924719 = 2887079) B2887079
theorem B2887085 : Blo 1923435 2887085 := bbase (se 3 (by rfl) ⟨541328, by rfl⟩ : syracuseStep 2887085 = 1082657) (by norm_num)
theorem B1924723 : Blo 1923435 1924723 := bstep (se 1 (by rfl) ⟨1443542, by rfl⟩ : syracuseStep 1924723 = 2887085) B2887085
theorem B4330637 : Blo 1923435 4330637 := bbase (se 3 (by rfl) ⟨811994, by rfl⟩ : syracuseStep 4330637 = 1623989) (by norm_num)
theorem B2887091 : Blo 1923435 2887091 := bstep (se 1 (by rfl) ⟨2165318, by rfl⟩ : syracuseStep 2887091 = 4330637) B4330637
theorem B1924727 : Blo 1923435 1924727 := bstep (se 1 (by rfl) ⟨1443545, by rfl⟩ : syracuseStep 1924727 = 2887091) B2887091
theorem B2435989 : Blo 1923435 2435989 := bbase (se 6 (by rfl) ⟨57093, by rfl⟩ : syracuseStep 2435989 = 114187) (by norm_num)
theorem B3247985 : Blo 1923435 3247985 := bstep (se 2 (by rfl) ⟨1217994, by rfl⟩ : syracuseStep 3247985 = 2435989) B2435989
theorem B2165323 : Blo 1923435 2165323 := bstep (se 1 (by rfl) ⟨1623992, by rfl⟩ : syracuseStep 2165323 = 3247985) B3247985
theorem B2887097 : Blo 1923435 2887097 := bstep (se 2 (by rfl) ⟨1082661, by rfl⟩ : syracuseStep 2887097 = 2165323) B2165323
theorem B1924731 : Blo 1923435 1924731 := bstep (se 1 (by rfl) ⟨1443548, by rfl⟩ : syracuseStep 1924731 = 2887097) B2887097
theorem B9876917 : Blo 1923435 9876917 := bbase (se 5 (by rfl) ⟨462980, by rfl⟩ : syracuseStep 9876917 = 925961) (by norm_num)
theorem B26338445 : Blo 1923435 26338445 := bstep (se 3 (by rfl) ⟨4938458, by rfl⟩ : syracuseStep 26338445 = 9876917) B9876917
theorem B17558963 : Blo 1923435 17558963 := bstep (se 1 (by rfl) ⟨13169222, by rfl⟩ : syracuseStep 17558963 = 26338445) B26338445
theorem B11705975 : Blo 1923435 11705975 := bstep (se 1 (by rfl) ⟨8779481, by rfl⟩ : syracuseStep 11705975 = 17558963) B17558963
theorem B7803983 : Blo 1923435 7803983 := bstep (se 1 (by rfl) ⟨5852987, by rfl⟩ : syracuseStep 7803983 = 11705975) B11705975
theorem B20810621 : Blo 1923435 20810621 := bstep (se 3 (by rfl) ⟨3901991, by rfl⟩ : syracuseStep 20810621 = 7803983) B7803983
theorem B55494989 : Blo 1923435 55494989 := bstep (se 3 (by rfl) ⟨10405310, by rfl⟩ : syracuseStep 55494989 = 20810621) B20810621
theorem B36996659 : Blo 1923435 36996659 := bstep (se 1 (by rfl) ⟨27747494, by rfl⟩ : syracuseStep 36996659 = 55494989) B55494989
theorem B24664439 : Blo 1923435 24664439 := bstep (se 1 (by rfl) ⟨18498329, by rfl⟩ : syracuseStep 24664439 = 36996659) B36996659
theorem B16442959 : Blo 1923435 16442959 := bstep (se 1 (by rfl) ⟨12332219, by rfl⟩ : syracuseStep 16442959 = 24664439) B24664439
theorem B21923945 : Blo 1923435 21923945 := bstep (se 2 (by rfl) ⟨8221479, by rfl⟩ : syracuseStep 21923945 = 16442959) B16442959
theorem B14615963 : Blo 1923435 14615963 := bstep (se 1 (by rfl) ⟨10961972, by rfl⟩ : syracuseStep 14615963 = 21923945) B21923945
theorem B9743975 : Blo 1923435 9743975 := bstep (se 1 (by rfl) ⟨7307981, by rfl⟩ : syracuseStep 9743975 = 14615963) B14615963
theorem B6495983 : Blo 1923435 6495983 := bstep (se 1 (by rfl) ⟨4871987, by rfl⟩ : syracuseStep 6495983 = 9743975) B9743975
theorem B4330655 : Blo 1923435 4330655 := bstep (se 1 (by rfl) ⟨3247991, by rfl⟩ : syracuseStep 4330655 = 6495983) B6495983
theorem B2887103 : Blo 1923435 2887103 := bstep (se 1 (by rfl) ⟨2165327, by rfl⟩ : syracuseStep 2887103 = 4330655) B4330655
theorem B1924735 : Blo 1923435 1924735 := bstep (se 1 (by rfl) ⟨1443551, by rfl⟩ : syracuseStep 1924735 = 2887103) B2887103
theorem B2887109 : Blo 1923435 2887109 := bbase (se 4 (by rfl) ⟨270666, by rfl⟩ : syracuseStep 2887109 = 541333) (by norm_num)
theorem B1924739 : Blo 1923435 1924739 := bstep (se 1 (by rfl) ⟨1443554, by rfl⟩ : syracuseStep 1924739 = 2887109) B2887109
theorem B3248005 : Blo 1923435 3248005 := bbase (se 4 (by rfl) ⟨304500, by rfl⟩ : syracuseStep 3248005 = 609001) (by norm_num)
theorem B4330673 : Blo 1923435 4330673 := bstep (se 2 (by rfl) ⟨1624002, by rfl⟩ : syracuseStep 4330673 = 3248005) B3248005
theorem B2887115 : Blo 1923435 2887115 := bstep (se 1 (by rfl) ⟨2165336, by rfl⟩ : syracuseStep 2887115 = 4330673) B4330673
theorem B1924743 : Blo 1923435 1924743 := bstep (se 1 (by rfl) ⟨1443557, by rfl⟩ : syracuseStep 1924743 = 2887115) B2887115
theorem B2165341 : Blo 1923435 2165341 := bbase (se 3 (by rfl) ⟨406001, by rfl⟩ : syracuseStep 2165341 = 812003) (by norm_num)
theorem B2887121 : Blo 1923435 2887121 := bstep (se 2 (by rfl) ⟨1082670, by rfl⟩ : syracuseStep 2887121 = 2165341) B2165341
theorem B1924747 : Blo 1923435 1924747 := bstep (se 1 (by rfl) ⟨1443560, by rfl⟩ : syracuseStep 1924747 = 2887121) B2887121
theorem B6496037 : Blo 1923435 6496037 := bbase (se 4 (by rfl) ⟨609003, by rfl⟩ : syracuseStep 6496037 = 1218007) (by norm_num)
theorem B4330691 : Blo 1923435 4330691 := bstep (se 1 (by rfl) ⟨3248018, by rfl⟩ : syracuseStep 4330691 = 6496037) B6496037
theorem B2887127 : Blo 1923435 2887127 := bstep (se 1 (by rfl) ⟨2165345, by rfl⟩ : syracuseStep 2887127 = 4330691) B4330691
theorem B1924751 : Blo 1923435 1924751 := bstep (se 1 (by rfl) ⟨1443563, by rfl⟩ : syracuseStep 1924751 = 2887127) B2887127
theorem B2887133 : Blo 1923435 2887133 := bbase (se 3 (by rfl) ⟨541337, by rfl⟩ : syracuseStep 2887133 = 1082675) (by norm_num)
theorem B1924755 : Blo 1923435 1924755 := bstep (se 1 (by rfl) ⟨1443566, by rfl⟩ : syracuseStep 1924755 = 2887133) B2887133
theorem B4330709 : Blo 1923435 4330709 := bbase (se 7 (by rfl) ⟨50750, by rfl⟩ : syracuseStep 4330709 = 101501) (by norm_num)
theorem B2887139 : Blo 1923435 2887139 := bstep (se 1 (by rfl) ⟨2165354, by rfl⟩ : syracuseStep 2887139 = 4330709) B4330709
theorem B1924759 : Blo 1923435 1924759 := bstep (se 1 (by rfl) ⟨1443569, by rfl⟩ : syracuseStep 1924759 = 2887139) B2887139
theorem B1951025 : Blo 1923435 1951025 := bbase (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) (by norm_num)
theorem B5202733 : Blo 1923435 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B6936977 : Blo 1923435 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B4624651 : Blo 1923435 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B6166201 : Blo 1923435 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B8221601 : Blo 1923435 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B5481067 : Blo 1923435 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B7308089 : Blo 1923435 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B4872059 : Blo 1923435 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B3248039 : Blo 1923435 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B2165359 : Blo 1923435 2165359 := bstep (se 1 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 2165359 = 3248039) B3248039
theorem B2887145 : Blo 1923435 2887145 := bstep (se 2 (by rfl) ⟨1082679, by rfl⟩ : syracuseStep 2887145 = 2165359) B2165359
theorem B1924763 : Blo 1923435 1924763 := bstep (se 1 (by rfl) ⟨1443572, by rfl⟩ : syracuseStep 1924763 = 2887145) B2887145
theorem B5555861 : Blo 1923435 5555861 := bbase (se 6 (by rfl) ⟨130215, by rfl⟩ : syracuseStep 5555861 = 260431) (by norm_num)
theorem B3703907 : Blo 1923435 3703907 := bstep (se 1 (by rfl) ⟨2777930, by rfl⟩ : syracuseStep 3703907 = 5555861) B5555861
theorem B2469271 : Blo 1923435 2469271 := bstep (se 1 (by rfl) ⟨1851953, by rfl⟩ : syracuseStep 2469271 = 3703907) B3703907
theorem B3292361 : Blo 1923435 3292361 := bstep (se 2 (by rfl) ⟨1234635, by rfl⟩ : syracuseStep 3292361 = 2469271) B2469271
theorem B2194907 : Blo 1923435 2194907 := bstep (se 1 (by rfl) ⟨1646180, by rfl⟩ : syracuseStep 2194907 = 3292361) B3292361
theorem B23412341 : Blo 1923435 23412341 := bstep (se 5 (by rfl) ⟨1097453, by rfl⟩ : syracuseStep 23412341 = 2194907) B2194907
theorem B15608227 : Blo 1923435 15608227 := bstep (se 1 (by rfl) ⟨11706170, by rfl⟩ : syracuseStep 15608227 = 23412341) B23412341
theorem B20810969 : Blo 1923435 20810969 := bstep (se 2 (by rfl) ⟨7804113, by rfl⟩ : syracuseStep 20810969 = 15608227) B15608227
theorem B13873979 : Blo 1923435 13873979 := bstep (se 1 (by rfl) ⟨10405484, by rfl⟩ : syracuseStep 13873979 = 20810969) B20810969
theorem B9249319 : Blo 1923435 9249319 := bstep (se 1 (by rfl) ⟨6936989, by rfl⟩ : syracuseStep 9249319 = 13873979) B13873979
theorem B12332425 : Blo 1923435 12332425 := bstep (se 2 (by rfl) ⟨4624659, by rfl⟩ : syracuseStep 12332425 = 9249319) B9249319
theorem B16443233 : Blo 1923435 16443233 := bstep (se 2 (by rfl) ⟨6166212, by rfl⟩ : syracuseStep 16443233 = 12332425) B12332425
theorem B10962155 : Blo 1923435 10962155 := bstep (se 1 (by rfl) ⟨8221616, by rfl⟩ : syracuseStep 10962155 = 16443233) B16443233
theorem B7308103 : Blo 1923435 7308103 := bstep (se 1 (by rfl) ⟨5481077, by rfl⟩ : syracuseStep 7308103 = 10962155) B10962155
theorem B9744137 : Blo 1923435 9744137 := bstep (se 2 (by rfl) ⟨3654051, by rfl⟩ : syracuseStep 9744137 = 7308103) B7308103
theorem B6496091 : Blo 1923435 6496091 := bstep (se 1 (by rfl) ⟨4872068, by rfl⟩ : syracuseStep 6496091 = 9744137) B9744137
theorem B4330727 : Blo 1923435 4330727 := bstep (se 1 (by rfl) ⟨3248045, by rfl⟩ : syracuseStep 4330727 = 6496091) B6496091
theorem B2887151 : Blo 1923435 2887151 := bstep (se 1 (by rfl) ⟨2165363, by rfl⟩ : syracuseStep 2887151 = 4330727) B4330727
theorem B1924767 : Blo 1923435 1924767 := bstep (se 1 (by rfl) ⟨1443575, by rfl⟩ : syracuseStep 1924767 = 2887151) B2887151
theorem B2887157 : Blo 1923435 2887157 := bbase (se 5 (by rfl) ⟨135335, by rfl⟩ : syracuseStep 2887157 = 270671) (by norm_num)
theorem B1924771 : Blo 1923435 1924771 := bstep (se 1 (by rfl) ⟨1443578, by rfl⟩ : syracuseStep 1924771 = 2887157) B2887157
theorem B2055413 : Blo 1923435 2055413 := bbase (se 5 (by rfl) ⟨96347, by rfl⟩ : syracuseStep 2055413 = 192695) (by norm_num)
theorem B5481101 : Blo 1923435 5481101 := bstep (se 3 (by rfl) ⟨1027706, by rfl⟩ : syracuseStep 5481101 = 2055413) B2055413
theorem B3654067 : Blo 1923435 3654067 := bstep (se 1 (by rfl) ⟨2740550, by rfl⟩ : syracuseStep 3654067 = 5481101) B5481101
theorem B4872089 : Blo 1923435 4872089 := bstep (se 2 (by rfl) ⟨1827033, by rfl⟩ : syracuseStep 4872089 = 3654067) B3654067
theorem B3248059 : Blo 1923435 3248059 := bstep (se 1 (by rfl) ⟨2436044, by rfl⟩ : syracuseStep 3248059 = 4872089) B4872089
theorem B4330745 : Blo 1923435 4330745 := bstep (se 2 (by rfl) ⟨1624029, by rfl⟩ : syracuseStep 4330745 = 3248059) B3248059
theorem B2887163 : Blo 1923435 2887163 := bstep (se 1 (by rfl) ⟨2165372, by rfl⟩ : syracuseStep 2887163 = 4330745) B4330745
theorem B1924775 : Blo 1923435 1924775 := bstep (se 1 (by rfl) ⟨1443581, by rfl⟩ : syracuseStep 1924775 = 2887163) B2887163
theorem B2165377 : Blo 1923435 2165377 := bbase (se 2 (by rfl) ⟨812016, by rfl⟩ : syracuseStep 2165377 = 1624033) (by norm_num)
theorem B2887169 : Blo 1923435 2887169 := bstep (se 2 (by rfl) ⟨1082688, by rfl⟩ : syracuseStep 2887169 = 2165377) B2165377
theorem B1924779 : Blo 1923435 1924779 := bstep (se 1 (by rfl) ⟨1443584, by rfl⟩ : syracuseStep 1924779 = 2887169) B2887169
theorem B4872109 : Blo 1923435 4872109 := bbase (se 3 (by rfl) ⟨913520, by rfl⟩ : syracuseStep 4872109 = 1827041) (by norm_num)
theorem B6496145 : Blo 1923435 6496145 := bstep (se 2 (by rfl) ⟨2436054, by rfl⟩ : syracuseStep 6496145 = 4872109) B4872109
theorem B4330763 : Blo 1923435 4330763 := bstep (se 1 (by rfl) ⟨3248072, by rfl⟩ : syracuseStep 4330763 = 6496145) B6496145
theorem B2887175 : Blo 1923435 2887175 := bstep (se 1 (by rfl) ⟨2165381, by rfl⟩ : syracuseStep 2887175 = 4330763) B4330763
theorem B1924783 : Blo 1923435 1924783 := bstep (se 1 (by rfl) ⟨1443587, by rfl⟩ : syracuseStep 1924783 = 2887175) B2887175
theorem B2887181 : Blo 1923435 2887181 := bbase (se 3 (by rfl) ⟨541346, by rfl⟩ : syracuseStep 2887181 = 1082693) (by norm_num)
theorem B1924787 : Blo 1923435 1924787 := bstep (se 1 (by rfl) ⟨1443590, by rfl⟩ : syracuseStep 1924787 = 2887181) B2887181
theorem B4330781 : Blo 1923435 4330781 := bbase (se 3 (by rfl) ⟨812021, by rfl⟩ : syracuseStep 4330781 = 1624043) (by norm_num)
theorem B2887187 : Blo 1923435 2887187 := bstep (se 1 (by rfl) ⟨2165390, by rfl⟩ : syracuseStep 2887187 = 4330781) B4330781
theorem B1924791 : Blo 1923435 1924791 := bstep (se 1 (by rfl) ⟨1443593, by rfl⟩ : syracuseStep 1924791 = 2887187) B2887187
theorem B3248093 : Blo 1923435 3248093 := bbase (se 3 (by rfl) ⟨609017, by rfl⟩ : syracuseStep 3248093 = 1218035) (by norm_num)
theorem B2165395 : Blo 1923435 2165395 := bstep (se 1 (by rfl) ⟨1624046, by rfl⟩ : syracuseStep 2165395 = 3248093) B3248093
theorem B2887193 : Blo 1923435 2887193 := bstep (se 2 (by rfl) ⟨1082697, by rfl⟩ : syracuseStep 2887193 = 2165395) B2165395
theorem B1924795 : Blo 1923435 1924795 := bstep (se 1 (by rfl) ⟨1443596, by rfl⟩ : syracuseStep 1924795 = 2887193) B2887193
theorem B1951061 : Blo 1923435 1951061 := bbase (se 12 (by rfl) ⟨714, by rfl⟩ : syracuseStep 1951061 = 1429) (by norm_num)
theorem B5202829 : Blo 1923435 5202829 := bstep (se 3 (by rfl) ⟨975530, by rfl⟩ : syracuseStep 5202829 = 1951061) B1951061
theorem B6937105 : Blo 1923435 6937105 := bstep (se 2 (by rfl) ⟨2601414, by rfl⟩ : syracuseStep 6937105 = 5202829) B5202829
theorem B9249473 : Blo 1923435 9249473 := bstep (se 2 (by rfl) ⟨3468552, by rfl⟩ : syracuseStep 9249473 = 6937105) B6937105
theorem B6166315 : Blo 1923435 6166315 := bstep (se 1 (by rfl) ⟨4624736, by rfl⟩ : syracuseStep 6166315 = 9249473) B9249473
theorem B8221753 : Blo 1923435 8221753 := bstep (se 2 (by rfl) ⟨3083157, by rfl⟩ : syracuseStep 8221753 = 6166315) B6166315
theorem B10962337 : Blo 1923435 10962337 := bstep (se 2 (by rfl) ⟨4110876, by rfl⟩ : syracuseStep 10962337 = 8221753) B8221753
theorem B14616449 : Blo 1923435 14616449 := bstep (se 2 (by rfl) ⟨5481168, by rfl⟩ : syracuseStep 14616449 = 10962337) B10962337
theorem B9744299 : Blo 1923435 9744299 := bstep (se 1 (by rfl) ⟨7308224, by rfl⟩ : syracuseStep 9744299 = 14616449) B14616449
theorem B6496199 : Blo 1923435 6496199 := bstep (se 1 (by rfl) ⟨4872149, by rfl⟩ : syracuseStep 6496199 = 9744299) B9744299
theorem B4330799 : Blo 1923435 4330799 := bstep (se 1 (by rfl) ⟨3248099, by rfl⟩ : syracuseStep 4330799 = 6496199) B6496199
theorem B2887199 : Blo 1923435 2887199 := bstep (se 1 (by rfl) ⟨2165399, by rfl⟩ : syracuseStep 2887199 = 4330799) B4330799
theorem B1924799 : Blo 1923435 1924799 := bstep (se 1 (by rfl) ⟨1443599, by rfl⟩ : syracuseStep 1924799 = 2887199) B2887199
theorem B2887205 : Blo 1923435 2887205 := bbase (se 4 (by rfl) ⟨270675, by rfl⟩ : syracuseStep 2887205 = 541351) (by norm_num)
theorem B1924803 : Blo 1923435 1924803 := bstep (se 1 (by rfl) ⟨1443602, by rfl⟩ : syracuseStep 1924803 = 2887205) B2887205
theorem B2436085 : Blo 1923435 2436085 := bbase (se 5 (by rfl) ⟨114191, by rfl⟩ : syracuseStep 2436085 = 228383) (by norm_num)
theorem B3248113 : Blo 1923435 3248113 := bstep (se 2 (by rfl) ⟨1218042, by rfl⟩ : syracuseStep 3248113 = 2436085) B2436085
theorem B4330817 : Blo 1923435 4330817 := bstep (se 2 (by rfl) ⟨1624056, by rfl⟩ : syracuseStep 4330817 = 3248113) B3248113
theorem B2887211 : Blo 1923435 2887211 := bstep (se 1 (by rfl) ⟨2165408, by rfl⟩ : syracuseStep 2887211 = 4330817) B4330817
theorem B1924807 : Blo 1923435 1924807 := bstep (se 1 (by rfl) ⟨1443605, by rfl⟩ : syracuseStep 1924807 = 2887211) B2887211
theorem B2165413 : Blo 1923435 2165413 := bbase (se 4 (by rfl) ⟨203007, by rfl⟩ : syracuseStep 2165413 = 406015) (by norm_num)
theorem B2887217 : Blo 1923435 2887217 := bstep (se 2 (by rfl) ⟨1082706, by rfl⟩ : syracuseStep 2887217 = 2165413) B2165413
theorem B1924811 : Blo 1923435 1924811 := bstep (se 1 (by rfl) ⟨1443608, by rfl⟩ : syracuseStep 1924811 = 2887217) B2887217
theorem B9375749 : Blo 1923435 9375749 := bbase (se 4 (by rfl) ⟨878976, by rfl⟩ : syracuseStep 9375749 = 1757953) (by norm_num)
theorem B6250499 : Blo 1923435 6250499 := bstep (se 1 (by rfl) ⟨4687874, by rfl⟩ : syracuseStep 6250499 = 9375749) B9375749
theorem B4166999 : Blo 1923435 4166999 := bstep (se 1 (by rfl) ⟨3125249, by rfl⟩ : syracuseStep 4166999 = 6250499) B6250499
theorem B2777999 : Blo 1923435 2777999 := bstep (se 1 (by rfl) ⟨2083499, by rfl⟩ : syracuseStep 2777999 = 4166999) B4166999
theorem B7407997 : Blo 1923435 7407997 := bstep (se 3 (by rfl) ⟨1388999, by rfl⟩ : syracuseStep 7407997 = 2777999) B2777999
theorem B39509317 : Blo 1923435 39509317 := bstep (se 4 (by rfl) ⟨3703998, by rfl⟩ : syracuseStep 39509317 = 7407997) B7407997
theorem B52679089 : Blo 1923435 52679089 := bstep (se 2 (by rfl) ⟨19754658, by rfl⟩ : syracuseStep 52679089 = 39509317) B39509317
theorem B70238785 : Blo 1923435 70238785 := bstep (se 2 (by rfl) ⟨26339544, by rfl⟩ : syracuseStep 70238785 = 52679089) B52679089
theorem B93651713 : Blo 1923435 93651713 := bstep (se 2 (by rfl) ⟨35119392, by rfl⟩ : syracuseStep 93651713 = 70238785) B70238785
theorem B62434475 : Blo 1923435 62434475 := bstep (se 1 (by rfl) ⟨46825856, by rfl⟩ : syracuseStep 62434475 = 93651713) B93651713
theorem B41622983 : Blo 1923435 41622983 := bstep (se 1 (by rfl) ⟨31217237, by rfl⟩ : syracuseStep 41622983 = 62434475) B62434475
theorem B27748655 : Blo 1923435 27748655 := bstep (se 1 (by rfl) ⟨20811491, by rfl⟩ : syracuseStep 27748655 = 41622983) B41622983
theorem B18499103 : Blo 1923435 18499103 := bstep (se 1 (by rfl) ⟨13874327, by rfl⟩ : syracuseStep 18499103 = 27748655) B27748655
theorem B12332735 : Blo 1923435 12332735 := bstep (se 1 (by rfl) ⟨9249551, by rfl⟩ : syracuseStep 12332735 = 18499103) B18499103
theorem B8221823 : Blo 1923435 8221823 := bstep (se 1 (by rfl) ⟨6166367, by rfl⟩ : syracuseStep 8221823 = 12332735) B12332735
theorem B5481215 : Blo 1923435 5481215 := bstep (se 1 (by rfl) ⟨4110911, by rfl⟩ : syracuseStep 5481215 = 8221823) B8221823
theorem B3654143 : Blo 1923435 3654143 := bstep (se 1 (by rfl) ⟨2740607, by rfl⟩ : syracuseStep 3654143 = 5481215) B5481215
theorem B2436095 : Blo 1923435 2436095 := bstep (se 1 (by rfl) ⟨1827071, by rfl⟩ : syracuseStep 2436095 = 3654143) B3654143
theorem B6496253 : Blo 1923435 6496253 := bstep (se 3 (by rfl) ⟨1218047, by rfl⟩ : syracuseStep 6496253 = 2436095) B2436095
theorem B4330835 : Blo 1923435 4330835 := bstep (se 1 (by rfl) ⟨3248126, by rfl⟩ : syracuseStep 4330835 = 6496253) B6496253
theorem B2887223 : Blo 1923435 2887223 := bstep (se 1 (by rfl) ⟨2165417, by rfl⟩ : syracuseStep 2887223 = 4330835) B4330835
theorem B1924815 : Blo 1923435 1924815 := bstep (se 1 (by rfl) ⟨1443611, by rfl⟩ : syracuseStep 1924815 = 2887223) B2887223
theorem B2887229 : Blo 1923435 2887229 := bbase (se 3 (by rfl) ⟨541355, by rfl⟩ : syracuseStep 2887229 = 1082711) (by norm_num)
theorem B1924819 : Blo 1923435 1924819 := bstep (se 1 (by rfl) ⟨1443614, by rfl⟩ : syracuseStep 1924819 = 2887229) B2887229
theorem B4330853 : Blo 1923435 4330853 := bbase (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) (by norm_num)
theorem B2887235 : Blo 1923435 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B1924823 : Blo 1923435 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B4872221 : Blo 1923435 4872221 := bbase (se 3 (by rfl) ⟨913541, by rfl⟩ : syracuseStep 4872221 = 1827083) (by norm_num)
theorem B3248147 : Blo 1923435 3248147 := bstep (se 1 (by rfl) ⟨2436110, by rfl⟩ : syracuseStep 3248147 = 4872221) B4872221
theorem B2165431 : Blo 1923435 2165431 := bstep (se 1 (by rfl) ⟨1624073, by rfl⟩ : syracuseStep 2165431 = 3248147) B3248147
theorem B2887241 : Blo 1923435 2887241 := bstep (se 2 (by rfl) ⟨1082715, by rfl⟩ : syracuseStep 2887241 = 2165431) B2165431
theorem B1924827 : Blo 1923435 1924827 := bstep (se 1 (by rfl) ⟨1443620, by rfl⟩ : syracuseStep 1924827 = 2887241) B2887241
theorem B3654173 : Blo 1923435 3654173 := bbase (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) (by norm_num)
theorem B9744461 : Blo 1923435 9744461 := bstep (se 3 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 9744461 = 3654173) B3654173
theorem B6496307 : Blo 1923435 6496307 := bstep (se 1 (by rfl) ⟨4872230, by rfl⟩ : syracuseStep 6496307 = 9744461) B9744461
theorem B4330871 : Blo 1923435 4330871 := bstep (se 1 (by rfl) ⟨3248153, by rfl⟩ : syracuseStep 4330871 = 6496307) B6496307
theorem B2887247 : Blo 1923435 2887247 := bstep (se 1 (by rfl) ⟨2165435, by rfl⟩ : syracuseStep 2887247 = 4330871) B4330871
theorem B1924831 : Blo 1923435 1924831 := bstep (se 1 (by rfl) ⟨1443623, by rfl⟩ : syracuseStep 1924831 = 2887247) B2887247
theorem B2887253 : Blo 1923435 2887253 := bbase (se 8 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 2887253 = 33835) (by norm_num)
theorem B1924835 : Blo 1923435 1924835 := bstep (se 1 (by rfl) ⟨1443626, by rfl⟩ : syracuseStep 1924835 = 2887253) B2887253
theorem B8221925 : Blo 1923435 8221925 := bbase (se 4 (by rfl) ⟨770805, by rfl⟩ : syracuseStep 8221925 = 1541611) (by norm_num)
theorem B5481283 : Blo 1923435 5481283 := bstep (se 1 (by rfl) ⟨4110962, by rfl⟩ : syracuseStep 5481283 = 8221925) B8221925
theorem B7308377 : Blo 1923435 7308377 := bstep (se 2 (by rfl) ⟨2740641, by rfl⟩ : syracuseStep 7308377 = 5481283) B5481283
theorem B4872251 : Blo 1923435 4872251 := bstep (se 1 (by rfl) ⟨3654188, by rfl⟩ : syracuseStep 4872251 = 7308377) B7308377
theorem B3248167 : Blo 1923435 3248167 := bstep (se 1 (by rfl) ⟨2436125, by rfl⟩ : syracuseStep 3248167 = 4872251) B4872251
theorem B4330889 : Blo 1923435 4330889 := bstep (se 2 (by rfl) ⟨1624083, by rfl⟩ : syracuseStep 4330889 = 3248167) B3248167
theorem B2887259 : Blo 1923435 2887259 := bstep (se 1 (by rfl) ⟨2165444, by rfl⟩ : syracuseStep 2887259 = 4330889) B4330889
theorem B1924839 : Blo 1923435 1924839 := bstep (se 1 (by rfl) ⟨1443629, by rfl⟩ : syracuseStep 1924839 = 2887259) B2887259
theorem B2165449 : Blo 1923435 2165449 := bbase (se 2 (by rfl) ⟨812043, by rfl⟩ : syracuseStep 2165449 = 1624087) (by norm_num)
theorem B2887265 : Blo 1923435 2887265 := bstep (se 2 (by rfl) ⟨1082724, by rfl⟩ : syracuseStep 2887265 = 2165449) B2165449
theorem B1924843 : Blo 1923435 1924843 := bstep (se 1 (by rfl) ⟨1443632, by rfl⟩ : syracuseStep 1924843 = 2887265) B2887265
theorem B6166469 : Blo 1923435 6166469 := bbase (se 4 (by rfl) ⟨578106, by rfl⟩ : syracuseStep 6166469 = 1156213) (by norm_num)
theorem B16443917 : Blo 1923435 16443917 := bstep (se 3 (by rfl) ⟨3083234, by rfl⟩ : syracuseStep 16443917 = 6166469) B6166469
theorem B10962611 : Blo 1923435 10962611 := bstep (se 1 (by rfl) ⟨8221958, by rfl⟩ : syracuseStep 10962611 = 16443917) B16443917
theorem B7308407 : Blo 1923435 7308407 := bstep (se 1 (by rfl) ⟨5481305, by rfl⟩ : syracuseStep 7308407 = 10962611) B10962611
theorem B4872271 : Blo 1923435 4872271 := bstep (se 1 (by rfl) ⟨3654203, by rfl⟩ : syracuseStep 4872271 = 7308407) B7308407
theorem B6496361 : Blo 1923435 6496361 := bstep (se 2 (by rfl) ⟨2436135, by rfl⟩ : syracuseStep 6496361 = 4872271) B4872271
theorem B4330907 : Blo 1923435 4330907 := bstep (se 1 (by rfl) ⟨3248180, by rfl⟩ : syracuseStep 4330907 = 6496361) B6496361
theorem B2887271 : Blo 1923435 2887271 := bstep (se 1 (by rfl) ⟨2165453, by rfl⟩ : syracuseStep 2887271 = 4330907) B4330907
theorem B1924847 : Blo 1923435 1924847 := bstep (se 1 (by rfl) ⟨1443635, by rfl⟩ : syracuseStep 1924847 = 2887271) B2887271
theorem B2887277 : Blo 1923435 2887277 := bbase (se 3 (by rfl) ⟨541364, by rfl⟩ : syracuseStep 2887277 = 1082729) (by norm_num)
theorem B1924851 : Blo 1923435 1924851 := bstep (se 1 (by rfl) ⟨1443638, by rfl⟩ : syracuseStep 1924851 = 2887277) B2887277
theorem B4330925 : Blo 1923435 4330925 := bbase (se 3 (by rfl) ⟨812048, by rfl⟩ : syracuseStep 4330925 = 1624097) (by norm_num)
theorem B2887283 : Blo 1923435 2887283 := bstep (se 1 (by rfl) ⟨2165462, by rfl⟩ : syracuseStep 2887283 = 4330925) B4330925
theorem B1924855 : Blo 1923435 1924855 := bstep (se 1 (by rfl) ⟨1443641, by rfl⟩ : syracuseStep 1924855 = 2887283) B2887283
theorem B2926685 : Blo 1923435 2926685 := bbase (se 3 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 2926685 = 1097507) (by norm_num)
theorem B1951123 : Blo 1923435 1951123 := bstep (se 1 (by rfl) ⟨1463342, by rfl⟩ : syracuseStep 1951123 = 2926685) B2926685
theorem B2601497 : Blo 1923435 2601497 := bstep (se 2 (by rfl) ⟨975561, by rfl⟩ : syracuseStep 2601497 = 1951123) B1951123
theorem B6937325 : Blo 1923435 6937325 := bstep (se 3 (by rfl) ⟨1300748, by rfl⟩ : syracuseStep 6937325 = 2601497) B2601497
theorem B4624883 : Blo 1923435 4624883 := bstep (se 1 (by rfl) ⟨3468662, by rfl⟩ : syracuseStep 4624883 = 6937325) B6937325
theorem B3083255 : Blo 1923435 3083255 := bstep (se 1 (by rfl) ⟨2312441, by rfl⟩ : syracuseStep 3083255 = 4624883) B4624883
theorem B2055503 : Blo 1923435 2055503 := bstep (se 1 (by rfl) ⟨1541627, by rfl⟩ : syracuseStep 2055503 = 3083255) B3083255
theorem B5481341 : Blo 1923435 5481341 := bstep (se 3 (by rfl) ⟨1027751, by rfl⟩ : syracuseStep 5481341 = 2055503) B2055503
theorem B3654227 : Blo 1923435 3654227 := bstep (se 1 (by rfl) ⟨2740670, by rfl⟩ : syracuseStep 3654227 = 5481341) B5481341
theorem B2436151 : Blo 1923435 2436151 := bstep (se 1 (by rfl) ⟨1827113, by rfl⟩ : syracuseStep 2436151 = 3654227) B3654227
theorem B3248201 : Blo 1923435 3248201 := bstep (se 2 (by rfl) ⟨1218075, by rfl⟩ : syracuseStep 3248201 = 2436151) B2436151
theorem B2165467 : Blo 1923435 2165467 := bstep (se 1 (by rfl) ⟨1624100, by rfl⟩ : syracuseStep 2165467 = 3248201) B3248201
theorem B2887289 : Blo 1923435 2887289 := bstep (se 2 (by rfl) ⟨1082733, by rfl⟩ : syracuseStep 2887289 = 2165467) B2165467
theorem B1924859 : Blo 1923435 1924859 := bstep (se 1 (by rfl) ⟨1443644, by rfl⟩ : syracuseStep 1924859 = 2887289) B2887289
theorem B9877573 : Blo 1923435 9877573 := bbase (se 4 (by rfl) ⟨926022, by rfl⟩ : syracuseStep 9877573 = 1852045) (by norm_num)
theorem B13170097 : Blo 1923435 13170097 := bstep (se 2 (by rfl) ⟨4938786, by rfl⟩ : syracuseStep 13170097 = 9877573) B9877573
theorem B70240517 : Blo 1923435 70240517 := bstep (se 4 (by rfl) ⟨6585048, by rfl⟩ : syracuseStep 70240517 = 13170097) B13170097
theorem B46827011 : Blo 1923435 46827011 := bstep (se 1 (by rfl) ⟨35120258, by rfl⟩ : syracuseStep 46827011 = 70240517) B70240517
theorem B124872029 : Blo 1923435 124872029 := bstep (se 3 (by rfl) ⟨23413505, by rfl⟩ : syracuseStep 124872029 = 46827011) B46827011
theorem B83248019 : Blo 1923435 83248019 := bstep (se 1 (by rfl) ⟨62436014, by rfl⟩ : syracuseStep 83248019 = 124872029) B124872029
theorem B55498679 : Blo 1923435 55498679 := bstep (se 1 (by rfl) ⟨41624009, by rfl⟩ : syracuseStep 55498679 = 83248019) B83248019
theorem B36999119 : Blo 1923435 36999119 := bstep (se 1 (by rfl) ⟨27749339, by rfl⟩ : syracuseStep 36999119 = 55498679) B55498679
theorem B24666079 : Blo 1923435 24666079 := bstep (se 1 (by rfl) ⟨18499559, by rfl⟩ : syracuseStep 24666079 = 36999119) B36999119
theorem B32888105 : Blo 1923435 32888105 := bstep (se 2 (by rfl) ⟨12333039, by rfl⟩ : syracuseStep 32888105 = 24666079) B24666079
theorem B21925403 : Blo 1923435 21925403 := bstep (se 1 (by rfl) ⟨16444052, by rfl⟩ : syracuseStep 21925403 = 32888105) B32888105
theorem B14616935 : Blo 1923435 14616935 := bstep (se 1 (by rfl) ⟨10962701, by rfl⟩ : syracuseStep 14616935 = 21925403) B21925403
theorem B9744623 : Blo 1923435 9744623 := bstep (se 1 (by rfl) ⟨7308467, by rfl⟩ : syracuseStep 9744623 = 14616935) B14616935
theorem B6496415 : Blo 1923435 6496415 := bstep (se 1 (by rfl) ⟨4872311, by rfl⟩ : syracuseStep 6496415 = 9744623) B9744623
theorem B4330943 : Blo 1923435 4330943 := bstep (se 1 (by rfl) ⟨3248207, by rfl⟩ : syracuseStep 4330943 = 6496415) B6496415
theorem B2887295 : Blo 1923435 2887295 := bstep (se 1 (by rfl) ⟨2165471, by rfl⟩ : syracuseStep 2887295 = 4330943) B4330943
theorem B1924863 : Blo 1923435 1924863 := bstep (se 1 (by rfl) ⟨1443647, by rfl⟩ : syracuseStep 1924863 = 2887295) B2887295
theorem B2887301 : Blo 1923435 2887301 := bbase (se 4 (by rfl) ⟨270684, by rfl⟩ : syracuseStep 2887301 = 541369) (by norm_num)
theorem B1924867 : Blo 1923435 1924867 := bstep (se 1 (by rfl) ⟨1443650, by rfl⟩ : syracuseStep 1924867 = 2887301) B2887301
theorem B3248221 : Blo 1923435 3248221 := bbase (se 3 (by rfl) ⟨609041, by rfl⟩ : syracuseStep 3248221 = 1218083) (by norm_num)
theorem B4330961 : Blo 1923435 4330961 := bstep (se 2 (by rfl) ⟨1624110, by rfl⟩ : syracuseStep 4330961 = 3248221) B3248221
theorem B2887307 : Blo 1923435 2887307 := bstep (se 1 (by rfl) ⟨2165480, by rfl⟩ : syracuseStep 2887307 = 4330961) B4330961
theorem B1924871 : Blo 1923435 1924871 := bstep (se 1 (by rfl) ⟨1443653, by rfl⟩ : syracuseStep 1924871 = 2887307) B2887307
theorem B2165485 : Blo 1923435 2165485 := bbase (se 3 (by rfl) ⟨406028, by rfl⟩ : syracuseStep 2165485 = 812057) (by norm_num)
theorem B2887313 : Blo 1923435 2887313 := bstep (se 2 (by rfl) ⟨1082742, by rfl⟩ : syracuseStep 2887313 = 2165485) B2165485
theorem B1924875 : Blo 1923435 1924875 := bstep (se 1 (by rfl) ⟨1443656, by rfl⟩ : syracuseStep 1924875 = 2887313) B2887313
theorem B6496469 : Blo 1923435 6496469 := bbase (se 7 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 6496469 = 152261) (by norm_num)
theorem B4330979 : Blo 1923435 4330979 := bstep (se 1 (by rfl) ⟨3248234, by rfl⟩ : syracuseStep 4330979 = 6496469) B6496469
theorem B2887319 : Blo 1923435 2887319 := bstep (se 1 (by rfl) ⟨2165489, by rfl⟩ : syracuseStep 2887319 = 4330979) B4330979
theorem B1924879 : Blo 1923435 1924879 := bstep (se 1 (by rfl) ⟨1443659, by rfl⟩ : syracuseStep 1924879 = 2887319) B2887319
theorem B2887325 : Blo 1923435 2887325 := bbase (se 3 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 2887325 = 1082747) (by norm_num)
theorem B1924883 : Blo 1923435 1924883 := bstep (se 1 (by rfl) ⟨1443662, by rfl⟩ : syracuseStep 1924883 = 2887325) B2887325
theorem B4330997 : Blo 1923435 4330997 := bbase (se 5 (by rfl) ⟨203015, by rfl⟩ : syracuseStep 4330997 = 406031) (by norm_num)
theorem B2887331 : Blo 1923435 2887331 := bstep (se 1 (by rfl) ⟨2165498, by rfl⟩ : syracuseStep 2887331 = 4330997) B4330997
theorem B1924887 : Blo 1923435 1924887 := bstep (se 1 (by rfl) ⟨1443665, by rfl⟩ : syracuseStep 1924887 = 2887331) B2887331
theorem B3902309 : Blo 1923435 3902309 := bbase (se 4 (by rfl) ⟨365841, by rfl⟩ : syracuseStep 3902309 = 731683) (by norm_num)
theorem B2601539 : Blo 1923435 2601539 := bstep (se 1 (by rfl) ⟨1951154, by rfl⟩ : syracuseStep 2601539 = 3902309) B3902309
theorem B27749749 : Blo 1923435 27749749 := bstep (se 5 (by rfl) ⟨1300769, by rfl⟩ : syracuseStep 27749749 = 2601539) B2601539
theorem B36999665 : Blo 1923435 36999665 := bstep (se 2 (by rfl) ⟨13874874, by rfl⟩ : syracuseStep 36999665 = 27749749) B27749749
theorem B24666443 : Blo 1923435 24666443 := bstep (se 1 (by rfl) ⟨18499832, by rfl⟩ : syracuseStep 24666443 = 36999665) B36999665
theorem B16444295 : Blo 1923435 16444295 := bstep (se 1 (by rfl) ⟨12333221, by rfl⟩ : syracuseStep 16444295 = 24666443) B24666443
theorem B10962863 : Blo 1923435 10962863 := bstep (se 1 (by rfl) ⟨8222147, by rfl⟩ : syracuseStep 10962863 = 16444295) B16444295
theorem B7308575 : Blo 1923435 7308575 := bstep (se 1 (by rfl) ⟨5481431, by rfl⟩ : syracuseStep 7308575 = 10962863) B10962863
theorem B4872383 : Blo 1923435 4872383 := bstep (se 1 (by rfl) ⟨3654287, by rfl⟩ : syracuseStep 4872383 = 7308575) B7308575
theorem B3248255 : Blo 1923435 3248255 := bstep (se 1 (by rfl) ⟨2436191, by rfl⟩ : syracuseStep 3248255 = 4872383) B4872383
theorem B2165503 : Blo 1923435 2165503 := bstep (se 1 (by rfl) ⟨1624127, by rfl⟩ : syracuseStep 2165503 = 3248255) B3248255
theorem B2887337 : Blo 1923435 2887337 := bstep (se 2 (by rfl) ⟨1082751, by rfl⟩ : syracuseStep 2887337 = 2165503) B2165503
theorem B1924891 : Blo 1923435 1924891 := bstep (se 1 (by rfl) ⟨1443668, by rfl⟩ : syracuseStep 1924891 = 2887337) B2887337
theorem B2055541 : Blo 1923435 2055541 := bbase (se 5 (by rfl) ⟨96353, by rfl⟩ : syracuseStep 2055541 = 192707) (by norm_num)
theorem B2740721 : Blo 1923435 2740721 := bstep (se 2 (by rfl) ⟨1027770, by rfl⟩ : syracuseStep 2740721 = 2055541) B2055541
theorem B7308589 : Blo 1923435 7308589 := bstep (se 3 (by rfl) ⟨1370360, by rfl⟩ : syracuseStep 7308589 = 2740721) B2740721
theorem B9744785 : Blo 1923435 9744785 := bstep (se 2 (by rfl) ⟨3654294, by rfl⟩ : syracuseStep 9744785 = 7308589) B7308589
theorem B6496523 : Blo 1923435 6496523 := bstep (se 1 (by rfl) ⟨4872392, by rfl⟩ : syracuseStep 6496523 = 9744785) B9744785
theorem B4331015 : Blo 1923435 4331015 := bstep (se 1 (by rfl) ⟨3248261, by rfl⟩ : syracuseStep 4331015 = 6496523) B6496523
theorem B2887343 : Blo 1923435 2887343 := bstep (se 1 (by rfl) ⟨2165507, by rfl⟩ : syracuseStep 2887343 = 4331015) B4331015
theorem B1924895 : Blo 1923435 1924895 := bstep (se 1 (by rfl) ⟨1443671, by rfl⟩ : syracuseStep 1924895 = 2887343) B2887343
theorem B2887349 : Blo 1923435 2887349 := bbase (se 5 (by rfl) ⟨135344, by rfl⟩ : syracuseStep 2887349 = 270689) (by norm_num)
theorem B1924899 : Blo 1923435 1924899 := bstep (se 1 (by rfl) ⟨1443674, by rfl⟩ : syracuseStep 1924899 = 2887349) B2887349
theorem B4872413 : Blo 1923435 4872413 := bbase (se 3 (by rfl) ⟨913577, by rfl⟩ : syracuseStep 4872413 = 1827155) (by norm_num)
theorem B3248275 : Blo 1923435 3248275 := bstep (se 1 (by rfl) ⟨2436206, by rfl⟩ : syracuseStep 3248275 = 4872413) B4872413
theorem B4331033 : Blo 1923435 4331033 := bstep (se 2 (by rfl) ⟨1624137, by rfl⟩ : syracuseStep 4331033 = 3248275) B3248275
theorem B2887355 : Blo 1923435 2887355 := bstep (se 1 (by rfl) ⟨2165516, by rfl⟩ : syracuseStep 2887355 = 4331033) B4331033
theorem B1924903 : Blo 1923435 1924903 := bstep (se 1 (by rfl) ⟨1443677, by rfl⟩ : syracuseStep 1924903 = 2887355) B2887355
theorem B2165521 : Blo 1923435 2165521 := bbase (se 2 (by rfl) ⟨812070, by rfl⟩ : syracuseStep 2165521 = 1624141) (by norm_num)
theorem B2887361 : Blo 1923435 2887361 := bstep (se 2 (by rfl) ⟨1082760, by rfl⟩ : syracuseStep 2887361 = 2165521) B2165521
theorem B1924907 : Blo 1923435 1924907 := bstep (se 1 (by rfl) ⟨1443680, by rfl⟩ : syracuseStep 1924907 = 2887361) B2887361
theorem B3654325 : Blo 1923435 3654325 := bbase (se 5 (by rfl) ⟨171296, by rfl⟩ : syracuseStep 3654325 = 342593) (by norm_num)
theorem B4872433 : Blo 1923435 4872433 := bstep (se 2 (by rfl) ⟨1827162, by rfl⟩ : syracuseStep 4872433 = 3654325) B3654325
theorem B6496577 : Blo 1923435 6496577 := bstep (se 2 (by rfl) ⟨2436216, by rfl⟩ : syracuseStep 6496577 = 4872433) B4872433
theorem B4331051 : Blo 1923435 4331051 := bstep (se 1 (by rfl) ⟨3248288, by rfl⟩ : syracuseStep 4331051 = 6496577) B6496577
theorem B2887367 : Blo 1923435 2887367 := bstep (se 1 (by rfl) ⟨2165525, by rfl⟩ : syracuseStep 2887367 = 4331051) B4331051
theorem B1924911 : Blo 1923435 1924911 := bstep (se 1 (by rfl) ⟨1443683, by rfl⟩ : syracuseStep 1924911 = 2887367) B2887367
theorem B2887373 : Blo 1923435 2887373 := bbase (se 3 (by rfl) ⟨541382, by rfl⟩ : syracuseStep 2887373 = 1082765) (by norm_num)
theorem B1924915 : Blo 1923435 1924915 := bstep (se 1 (by rfl) ⟨1443686, by rfl⟩ : syracuseStep 1924915 = 2887373) B2887373
theorem B4331069 : Blo 1923435 4331069 := bbase (se 3 (by rfl) ⟨812075, by rfl⟩ : syracuseStep 4331069 = 1624151) (by norm_num)
theorem B2887379 : Blo 1923435 2887379 := bstep (se 1 (by rfl) ⟨2165534, by rfl⟩ : syracuseStep 2887379 = 4331069) B4331069
theorem B1924919 : Blo 1923435 1924919 := bstep (se 1 (by rfl) ⟨1443689, by rfl⟩ : syracuseStep 1924919 = 2887379) B2887379
theorem B3248309 : Blo 1923435 3248309 := bbase (se 5 (by rfl) ⟨152264, by rfl⟩ : syracuseStep 3248309 = 304529) (by norm_num)
theorem B2165539 : Blo 1923435 2165539 := bstep (se 1 (by rfl) ⟨1624154, by rfl⟩ : syracuseStep 2165539 = 3248309) B3248309
theorem B2887385 : Blo 1923435 2887385 := bstep (se 2 (by rfl) ⟨1082769, by rfl⟩ : syracuseStep 2887385 = 2165539) B2165539
theorem B1924923 : Blo 1923435 1924923 := bstep (se 1 (by rfl) ⟨1443692, by rfl⟩ : syracuseStep 1924923 = 2887385) B2887385
theorem B4625045 : Blo 1923435 4625045 := bbase (se 6 (by rfl) ⟨108399, by rfl⟩ : syracuseStep 4625045 = 216799) (by norm_num)
theorem B3083363 : Blo 1923435 3083363 := bstep (se 1 (by rfl) ⟨2312522, by rfl⟩ : syracuseStep 3083363 = 4625045) B4625045
theorem B2055575 : Blo 1923435 2055575 := bstep (se 1 (by rfl) ⟨1541681, by rfl⟩ : syracuseStep 2055575 = 3083363) B3083363
theorem B5481533 : Blo 1923435 5481533 := bstep (se 3 (by rfl) ⟨1027787, by rfl⟩ : syracuseStep 5481533 = 2055575) B2055575
theorem B14617421 : Blo 1923435 14617421 := bstep (se 3 (by rfl) ⟨2740766, by rfl⟩ : syracuseStep 14617421 = 5481533) B5481533
theorem B9744947 : Blo 1923435 9744947 := bstep (se 1 (by rfl) ⟨7308710, by rfl⟩ : syracuseStep 9744947 = 14617421) B14617421
theorem B6496631 : Blo 1923435 6496631 := bstep (se 1 (by rfl) ⟨4872473, by rfl⟩ : syracuseStep 6496631 = 9744947) B9744947
theorem B4331087 : Blo 1923435 4331087 := bstep (se 1 (by rfl) ⟨3248315, by rfl⟩ : syracuseStep 4331087 = 6496631) B6496631
theorem B2887391 : Blo 1923435 2887391 := bstep (se 1 (by rfl) ⟨2165543, by rfl⟩ : syracuseStep 2887391 = 4331087) B4331087
theorem B1924927 : Blo 1923435 1924927 := bstep (se 1 (by rfl) ⟨1443695, by rfl⟩ : syracuseStep 1924927 = 2887391) B2887391
theorem B2887397 : Blo 1923435 2887397 := bbase (se 4 (by rfl) ⟨270693, by rfl⟩ : syracuseStep 2887397 = 541387) (by norm_num)
theorem B1924931 : Blo 1923435 1924931 := bstep (se 1 (by rfl) ⟨1443698, by rfl⟩ : syracuseStep 1924931 = 2887397) B2887397
theorem B5481557 : Blo 1923435 5481557 := bbase (se 8 (by rfl) ⟨32118, by rfl⟩ : syracuseStep 5481557 = 64237) (by norm_num)
theorem B3654371 : Blo 1923435 3654371 := bstep (se 1 (by rfl) ⟨2740778, by rfl⟩ : syracuseStep 3654371 = 5481557) B5481557
theorem B2436247 : Blo 1923435 2436247 := bstep (se 1 (by rfl) ⟨1827185, by rfl⟩ : syracuseStep 2436247 = 3654371) B3654371
theorem B3248329 : Blo 1923435 3248329 := bstep (se 2 (by rfl) ⟨1218123, by rfl⟩ : syracuseStep 3248329 = 2436247) B2436247
theorem B4331105 : Blo 1923435 4331105 := bstep (se 2 (by rfl) ⟨1624164, by rfl⟩ : syracuseStep 4331105 = 3248329) B3248329
theorem B2887403 : Blo 1923435 2887403 := bstep (se 1 (by rfl) ⟨2165552, by rfl⟩ : syracuseStep 2887403 = 4331105) B4331105
theorem B1924935 : Blo 1923435 1924935 := bstep (se 1 (by rfl) ⟨1443701, by rfl⟩ : syracuseStep 1924935 = 2887403) B2887403
theorem B2165557 : Blo 1923435 2165557 := bbase (se 5 (by rfl) ⟨101510, by rfl⟩ : syracuseStep 2165557 = 203021) (by norm_num)
theorem B2887409 : Blo 1923435 2887409 := bstep (se 2 (by rfl) ⟨1082778, by rfl⟩ : syracuseStep 2887409 = 2165557) B2165557
theorem B1924939 : Blo 1923435 1924939 := bstep (se 1 (by rfl) ⟨1443704, by rfl⟩ : syracuseStep 1924939 = 2887409) B2887409
theorem B2436257 : Blo 1923435 2436257 := bbase (se 2 (by rfl) ⟨913596, by rfl⟩ : syracuseStep 2436257 = 1827193) (by norm_num)
theorem B6496685 : Blo 1923435 6496685 := bstep (se 3 (by rfl) ⟨1218128, by rfl⟩ : syracuseStep 6496685 = 2436257) B2436257
theorem B4331123 : Blo 1923435 4331123 := bstep (se 1 (by rfl) ⟨3248342, by rfl⟩ : syracuseStep 4331123 = 6496685) B6496685
theorem B2887415 : Blo 1923435 2887415 := bstep (se 1 (by rfl) ⟨2165561, by rfl⟩ : syracuseStep 2887415 = 4331123) B4331123
theorem B1924943 : Blo 1923435 1924943 := bstep (se 1 (by rfl) ⟨1443707, by rfl⟩ : syracuseStep 1924943 = 2887415) B2887415
theorem B2887421 : Blo 1923435 2887421 := bbase (se 3 (by rfl) ⟨541391, by rfl⟩ : syracuseStep 2887421 = 1082783) (by norm_num)
theorem B1924947 : Blo 1923435 1924947 := bstep (se 1 (by rfl) ⟨1443710, by rfl⟩ : syracuseStep 1924947 = 2887421) B2887421
theorem B4331141 : Blo 1923435 4331141 := bbase (se 4 (by rfl) ⟨406044, by rfl⟩ : syracuseStep 4331141 = 812089) (by norm_num)
theorem B2887427 : Blo 1923435 2887427 := bstep (se 1 (by rfl) ⟨2165570, by rfl⟩ : syracuseStep 2887427 = 4331141) B4331141
theorem B1924951 : Blo 1923435 1924951 := bstep (se 1 (by rfl) ⟨1443713, by rfl⟩ : syracuseStep 1924951 = 2887427) B2887427
theorem B5203253 : Blo 1923435 5203253 := bbase (se 5 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 5203253 = 487805) (by norm_num)
theorem B3468835 : Blo 1923435 3468835 := bstep (se 1 (by rfl) ⟨2601626, by rfl⟩ : syracuseStep 3468835 = 5203253) B5203253
theorem B4625113 : Blo 1923435 4625113 := bstep (se 2 (by rfl) ⟨1734417, by rfl⟩ : syracuseStep 4625113 = 3468835) B3468835
theorem B6166817 : Blo 1923435 6166817 := bstep (se 2 (by rfl) ⟨2312556, by rfl⟩ : syracuseStep 6166817 = 4625113) B4625113
theorem B4111211 : Blo 1923435 4111211 := bstep (se 1 (by rfl) ⟨3083408, by rfl⟩ : syracuseStep 4111211 = 6166817) B6166817
theorem B2740807 : Blo 1923435 2740807 := bstep (se 1 (by rfl) ⟨2055605, by rfl⟩ : syracuseStep 2740807 = 4111211) B4111211
theorem B3654409 : Blo 1923435 3654409 := bstep (se 2 (by rfl) ⟨1370403, by rfl⟩ : syracuseStep 3654409 = 2740807) B2740807
theorem B4872545 : Blo 1923435 4872545 := bstep (se 2 (by rfl) ⟨1827204, by rfl⟩ : syracuseStep 4872545 = 3654409) B3654409
theorem B3248363 : Blo 1923435 3248363 := bstep (se 1 (by rfl) ⟨2436272, by rfl⟩ : syracuseStep 3248363 = 4872545) B4872545
theorem B2165575 : Blo 1923435 2165575 := bstep (se 1 (by rfl) ⟨1624181, by rfl⟩ : syracuseStep 2165575 = 3248363) B3248363
theorem B2887433 : Blo 1923435 2887433 := bstep (se 2 (by rfl) ⟨1082787, by rfl⟩ : syracuseStep 2887433 = 2165575) B2165575
theorem B1924955 : Blo 1923435 1924955 := bstep (se 1 (by rfl) ⟨1443716, by rfl⟩ : syracuseStep 1924955 = 2887433) B2887433
theorem B9745109 : Blo 1923435 9745109 := bbase (se 7 (by rfl) ⟨114200, by rfl⟩ : syracuseStep 9745109 = 228401) (by norm_num)
theorem B6496739 : Blo 1923435 6496739 := bstep (se 1 (by rfl) ⟨4872554, by rfl⟩ : syracuseStep 6496739 = 9745109) B9745109
theorem B4331159 : Blo 1923435 4331159 := bstep (se 1 (by rfl) ⟨3248369, by rfl⟩ : syracuseStep 4331159 = 6496739) B6496739
theorem B2887439 : Blo 1923435 2887439 := bstep (se 1 (by rfl) ⟨2165579, by rfl⟩ : syracuseStep 2887439 = 4331159) B4331159
theorem B1924959 : Blo 1923435 1924959 := bstep (se 1 (by rfl) ⟨1443719, by rfl⟩ : syracuseStep 1924959 = 2887439) B2887439
theorem B2887445 : Blo 1923435 2887445 := bbase (se 6 (by rfl) ⟨67674, by rfl⟩ : syracuseStep 2887445 = 135349) (by norm_num)
theorem B1924963 : Blo 1923435 1924963 := bstep (se 1 (by rfl) ⟨1443722, by rfl⟩ : syracuseStep 1924963 = 2887445) B2887445
theorem B3383165 : Blo 1923435 3383165 := bbase (se 3 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 3383165 = 1268687) (by norm_num)
theorem B9021773 : Blo 1923435 9021773 := bstep (se 3 (by rfl) ⟨1691582, by rfl⟩ : syracuseStep 9021773 = 3383165) B3383165
theorem B6014515 : Blo 1923435 6014515 := bstep (se 1 (by rfl) ⟨4510886, by rfl⟩ : syracuseStep 6014515 = 9021773) B9021773
theorem B8019353 : Blo 1923435 8019353 := bstep (se 2 (by rfl) ⟨3007257, by rfl⟩ : syracuseStep 8019353 = 6014515) B6014515
theorem B5346235 : Blo 1923435 5346235 := bstep (se 1 (by rfl) ⟨4009676, by rfl⟩ : syracuseStep 5346235 = 8019353) B8019353
theorem B7128313 : Blo 1923435 7128313 := bstep (se 2 (by rfl) ⟨2673117, by rfl⟩ : syracuseStep 7128313 = 5346235) B5346235
theorem B38017669 : Blo 1923435 38017669 := bstep (se 4 (by rfl) ⟨3564156, by rfl⟩ : syracuseStep 38017669 = 7128313) B7128313
theorem B50690225 : Blo 1923435 50690225 := bstep (se 2 (by rfl) ⟨19008834, by rfl⟩ : syracuseStep 50690225 = 38017669) B38017669
theorem B33793483 : Blo 1923435 33793483 := bstep (se 1 (by rfl) ⟨25345112, by rfl⟩ : syracuseStep 33793483 = 50690225) B50690225
theorem B45057977 : Blo 1923435 45057977 := bstep (se 2 (by rfl) ⟨16896741, by rfl⟩ : syracuseStep 45057977 = 33793483) B33793483
theorem B30038651 : Blo 1923435 30038651 := bstep (se 1 (by rfl) ⟨22528988, by rfl⟩ : syracuseStep 30038651 = 45057977) B45057977
theorem B20025767 : Blo 1923435 20025767 := bstep (se 1 (by rfl) ⟨15019325, by rfl⟩ : syracuseStep 20025767 = 30038651) B30038651
theorem B13350511 : Blo 1923435 13350511 := bstep (se 1 (by rfl) ⟨10012883, by rfl⟩ : syracuseStep 13350511 = 20025767) B20025767
theorem B17800681 : Blo 1923435 17800681 := bstep (se 2 (by rfl) ⟨6675255, by rfl⟩ : syracuseStep 17800681 = 13350511) B13350511
theorem B23734241 : Blo 1923435 23734241 := bstep (se 2 (by rfl) ⟨8900340, by rfl⟩ : syracuseStep 23734241 = 17800681) B17800681
theorem B15822827 : Blo 1923435 15822827 := bstep (se 1 (by rfl) ⟨11867120, by rfl⟩ : syracuseStep 15822827 = 23734241) B23734241
theorem B10548551 : Blo 1923435 10548551 := bstep (se 1 (by rfl) ⟨7911413, by rfl⟩ : syracuseStep 10548551 = 15822827) B15822827
theorem B7032367 : Blo 1923435 7032367 := bstep (se 1 (by rfl) ⟨5274275, by rfl⟩ : syracuseStep 7032367 = 10548551) B10548551
theorem B9376489 : Blo 1923435 9376489 := bstep (se 2 (by rfl) ⟨3516183, by rfl⟩ : syracuseStep 9376489 = 7032367) B7032367
theorem B50007941 : Blo 1923435 50007941 := bstep (se 4 (by rfl) ⟨4688244, by rfl⟩ : syracuseStep 50007941 = 9376489) B9376489
theorem B33338627 : Blo 1923435 33338627 := bstep (se 1 (by rfl) ⟨25003970, by rfl⟩ : syracuseStep 33338627 = 50007941) B50007941
theorem B22225751 : Blo 1923435 22225751 := bstep (se 1 (by rfl) ⟨16669313, by rfl⟩ : syracuseStep 22225751 = 33338627) B33338627
theorem B14817167 : Blo 1923435 14817167 := bstep (se 1 (by rfl) ⟨11112875, by rfl⟩ : syracuseStep 14817167 = 22225751) B22225751
theorem B9878111 : Blo 1923435 9878111 := bstep (se 1 (by rfl) ⟨7408583, by rfl⟩ : syracuseStep 9878111 = 14817167) B14817167
theorem B6585407 : Blo 1923435 6585407 := bstep (se 1 (by rfl) ⟨4939055, by rfl⟩ : syracuseStep 6585407 = 9878111) B9878111
theorem B4390271 : Blo 1923435 4390271 := bstep (se 1 (by rfl) ⟨3292703, by rfl⟩ : syracuseStep 4390271 = 6585407) B6585407
theorem B2926847 : Blo 1923435 2926847 := bstep (se 1 (by rfl) ⟨2195135, by rfl⟩ : syracuseStep 2926847 = 4390271) B4390271
theorem B7804925 : Blo 1923435 7804925 := bstep (se 3 (by rfl) ⟨1463423, by rfl⟩ : syracuseStep 7804925 = 2926847) B2926847
theorem B5203283 : Blo 1923435 5203283 := bstep (se 1 (by rfl) ⟨3902462, by rfl⟩ : syracuseStep 5203283 = 7804925) B7804925
theorem B55501685 : Blo 1923435 55501685 := bstep (se 5 (by rfl) ⟨2601641, by rfl⟩ : syracuseStep 55501685 = 5203283) B5203283
theorem B37001123 : Blo 1923435 37001123 := bstep (se 1 (by rfl) ⟨27750842, by rfl⟩ : syracuseStep 37001123 = 55501685) B55501685
theorem B24667415 : Blo 1923435 24667415 := bstep (se 1 (by rfl) ⟨18500561, by rfl⟩ : syracuseStep 24667415 = 37001123) B37001123
theorem B16444943 : Blo 1923435 16444943 := bstep (se 1 (by rfl) ⟨12333707, by rfl⟩ : syracuseStep 16444943 = 24667415) B24667415
theorem B10963295 : Blo 1923435 10963295 := bstep (se 1 (by rfl) ⟨8222471, by rfl⟩ : syracuseStep 10963295 = 16444943) B16444943
theorem B7308863 : Blo 1923435 7308863 := bstep (se 1 (by rfl) ⟨5481647, by rfl⟩ : syracuseStep 7308863 = 10963295) B10963295
theorem B4872575 : Blo 1923435 4872575 := bstep (se 1 (by rfl) ⟨3654431, by rfl⟩ : syracuseStep 4872575 = 7308863) B7308863
theorem B3248383 : Blo 1923435 3248383 := bstep (se 1 (by rfl) ⟨2436287, by rfl⟩ : syracuseStep 3248383 = 4872575) B4872575
theorem B4331177 : Blo 1923435 4331177 := bstep (se 2 (by rfl) ⟨1624191, by rfl⟩ : syracuseStep 4331177 = 3248383) B3248383
theorem B2887451 : Blo 1923435 2887451 := bstep (se 1 (by rfl) ⟨2165588, by rfl⟩ : syracuseStep 2887451 = 4331177) B4331177
theorem B1924967 : Blo 1923435 1924967 := bstep (se 1 (by rfl) ⟨1443725, by rfl⟩ : syracuseStep 1924967 = 2887451) B2887451
theorem B2165593 : Blo 1923435 2165593 := bbase (se 2 (by rfl) ⟨812097, by rfl⟩ : syracuseStep 2165593 = 1624195) (by norm_num)
theorem B2887457 : Blo 1923435 2887457 := bstep (se 2 (by rfl) ⟨1082796, by rfl⟩ : syracuseStep 2887457 = 2165593) B2165593
theorem B1924971 : Blo 1923435 1924971 := bstep (se 1 (by rfl) ⟨1443728, by rfl⟩ : syracuseStep 1924971 = 2887457) B2887457
theorem B4111253 : Blo 1923435 4111253 := bbase (se 6 (by rfl) ⟨96357, by rfl⟩ : syracuseStep 4111253 = 192715) (by norm_num)
theorem B2740835 : Blo 1923435 2740835 := bstep (se 1 (by rfl) ⟨2055626, by rfl⟩ : syracuseStep 2740835 = 4111253) B4111253
theorem B7308893 : Blo 1923435 7308893 := bstep (se 3 (by rfl) ⟨1370417, by rfl⟩ : syracuseStep 7308893 = 2740835) B2740835
theorem B4872595 : Blo 1923435 4872595 := bstep (se 1 (by rfl) ⟨3654446, by rfl⟩ : syracuseStep 4872595 = 7308893) B7308893
theorem B6496793 : Blo 1923435 6496793 := bstep (se 2 (by rfl) ⟨2436297, by rfl⟩ : syracuseStep 6496793 = 4872595) B4872595
theorem B4331195 : Blo 1923435 4331195 := bstep (se 1 (by rfl) ⟨3248396, by rfl⟩ : syracuseStep 4331195 = 6496793) B6496793
theorem B2887463 : Blo 1923435 2887463 := bstep (se 1 (by rfl) ⟨2165597, by rfl⟩ : syracuseStep 2887463 = 4331195) B4331195
theorem B1924975 : Blo 1923435 1924975 := bstep (se 1 (by rfl) ⟨1443731, by rfl⟩ : syracuseStep 1924975 = 2887463) B2887463
theorem B2887469 : Blo 1923435 2887469 := bbase (se 3 (by rfl) ⟨541400, by rfl⟩ : syracuseStep 2887469 = 1082801) (by norm_num)
theorem B1924979 : Blo 1923435 1924979 := bstep (se 1 (by rfl) ⟨1443734, by rfl⟩ : syracuseStep 1924979 = 2887469) B2887469
theorem B4331213 : Blo 1923435 4331213 := bbase (se 3 (by rfl) ⟨812102, by rfl⟩ : syracuseStep 4331213 = 1624205) (by norm_num)
theorem B2887475 : Blo 1923435 2887475 := bstep (se 1 (by rfl) ⟨2165606, by rfl⟩ : syracuseStep 2887475 = 4331213) B4331213
theorem B1924983 : Blo 1923435 1924983 := bstep (se 1 (by rfl) ⟨1443737, by rfl⟩ : syracuseStep 1924983 = 2887475) B2887475
theorem B2436313 : Blo 1923435 2436313 := bbase (se 2 (by rfl) ⟨913617, by rfl⟩ : syracuseStep 2436313 = 1827235) (by norm_num)
theorem B3248417 : Blo 1923435 3248417 := bstep (se 2 (by rfl) ⟨1218156, by rfl⟩ : syracuseStep 3248417 = 2436313) B2436313
theorem B2165611 : Blo 1923435 2165611 := bstep (se 1 (by rfl) ⟨1624208, by rfl⟩ : syracuseStep 2165611 = 3248417) B3248417
theorem B2887481 : Blo 1923435 2887481 := bstep (se 2 (by rfl) ⟨1082805, by rfl⟩ : syracuseStep 2887481 = 2165611) B2165611
theorem B1924987 : Blo 1923435 1924987 := bstep (se 1 (by rfl) ⟨1443740, by rfl⟩ : syracuseStep 1924987 = 2887481) B2887481
theorem B5203349 : Blo 1923435 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B3468899 : Blo 1923435 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B2312599 : Blo 1923435 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B3083465 : Blo 1923435 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B8222573 : Blo 1923435 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B21926861 : Blo 1923435 21926861 := bstep (se 3 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 21926861 = 8222573) B8222573
theorem B14617907 : Blo 1923435 14617907 := bstep (se 1 (by rfl) ⟨10963430, by rfl⟩ : syracuseStep 14617907 = 21926861) B21926861
theorem B9745271 : Blo 1923435 9745271 := bstep (se 1 (by rfl) ⟨7308953, by rfl⟩ : syracuseStep 9745271 = 14617907) B14617907
theorem B6496847 : Blo 1923435 6496847 := bstep (se 1 (by rfl) ⟨4872635, by rfl⟩ : syracuseStep 6496847 = 9745271) B9745271
theorem B4331231 : Blo 1923435 4331231 := bstep (se 1 (by rfl) ⟨3248423, by rfl⟩ : syracuseStep 4331231 = 6496847) B6496847
theorem B2887487 : Blo 1923435 2887487 := bstep (se 1 (by rfl) ⟨2165615, by rfl⟩ : syracuseStep 2887487 = 4331231) B4331231
theorem B1924991 : Blo 1923435 1924991 := bstep (se 1 (by rfl) ⟨1443743, by rfl⟩ : syracuseStep 1924991 = 2887487) B2887487
theorem B2887493 : Blo 1923435 2887493 := bbase (se 4 (by rfl) ⟨270702, by rfl⟩ : syracuseStep 2887493 = 541405) (by norm_num)
theorem B1924995 : Blo 1923435 1924995 := bstep (se 1 (by rfl) ⟨1443746, by rfl⟩ : syracuseStep 1924995 = 2887493) B2887493
theorem B3248437 : Blo 1923435 3248437 := bbase (se 5 (by rfl) ⟨152270, by rfl⟩ : syracuseStep 3248437 = 304541) (by norm_num)
theorem B4331249 : Blo 1923435 4331249 := bstep (se 2 (by rfl) ⟨1624218, by rfl⟩ : syracuseStep 4331249 = 3248437) B3248437
theorem B2887499 : Blo 1923435 2887499 := bstep (se 1 (by rfl) ⟨2165624, by rfl⟩ : syracuseStep 2887499 = 4331249) B4331249
theorem B1924999 : Blo 1923435 1924999 := bstep (se 1 (by rfl) ⟨1443749, by rfl⟩ : syracuseStep 1924999 = 2887499) B2887499
theorem B2165629 : Blo 1923435 2165629 := bbase (se 3 (by rfl) ⟨406055, by rfl⟩ : syracuseStep 2165629 = 812111) (by norm_num)
theorem B2887505 : Blo 1923435 2887505 := bstep (se 2 (by rfl) ⟨1082814, by rfl⟩ : syracuseStep 2887505 = 2165629) B2165629
theorem B1925003 : Blo 1923435 1925003 := bstep (se 1 (by rfl) ⟨1443752, by rfl⟩ : syracuseStep 1925003 = 2887505) B2887505
theorem B6496901 : Blo 1923435 6496901 := bbase (se 4 (by rfl) ⟨609084, by rfl⟩ : syracuseStep 6496901 = 1218169) (by norm_num)
theorem B4331267 : Blo 1923435 4331267 := bstep (se 1 (by rfl) ⟨3248450, by rfl⟩ : syracuseStep 4331267 = 6496901) B6496901
theorem B2887511 : Blo 1923435 2887511 := bstep (se 1 (by rfl) ⟨2165633, by rfl⟩ : syracuseStep 2887511 = 4331267) B4331267
theorem B1925007 : Blo 1923435 1925007 := bstep (se 1 (by rfl) ⟨1443755, by rfl⟩ : syracuseStep 1925007 = 2887511) B2887511
theorem B2887517 : Blo 1923435 2887517 := bbase (se 3 (by rfl) ⟨541409, by rfl⟩ : syracuseStep 2887517 = 1082819) (by norm_num)
theorem B1925011 : Blo 1923435 1925011 := bstep (se 1 (by rfl) ⟨1443758, by rfl⟩ : syracuseStep 1925011 = 2887517) B2887517
theorem B4331285 : Blo 1923435 4331285 := bbase (se 6 (by rfl) ⟨101514, by rfl⟩ : syracuseStep 4331285 = 203029) (by norm_num)
theorem B2887523 : Blo 1923435 2887523 := bstep (se 1 (by rfl) ⟨2165642, by rfl⟩ : syracuseStep 2887523 = 4331285) B4331285
theorem B1925015 : Blo 1923435 1925015 := bstep (se 1 (by rfl) ⟨1443761, by rfl⟩ : syracuseStep 1925015 = 2887523) B2887523
theorem B7309061 : Blo 1923435 7309061 := bbase (se 4 (by rfl) ⟨685224, by rfl⟩ : syracuseStep 7309061 = 1370449) (by norm_num)
theorem B4872707 : Blo 1923435 4872707 := bstep (se 1 (by rfl) ⟨3654530, by rfl⟩ : syracuseStep 4872707 = 7309061) B7309061
theorem B3248471 : Blo 1923435 3248471 := bstep (se 1 (by rfl) ⟨2436353, by rfl⟩ : syracuseStep 3248471 = 4872707) B4872707
theorem B2165647 : Blo 1923435 2165647 := bstep (se 1 (by rfl) ⟨1624235, by rfl⟩ : syracuseStep 2165647 = 3248471) B3248471
theorem B2887529 : Blo 1923435 2887529 := bstep (se 2 (by rfl) ⟨1082823, by rfl⟩ : syracuseStep 2887529 = 2165647) B2165647
theorem B1925019 : Blo 1923435 1925019 := bstep (se 1 (by rfl) ⟨1443764, by rfl⟩ : syracuseStep 1925019 = 2887529) B2887529
theorem B9634373 : Blo 1923435 9634373 := bbase (se 4 (by rfl) ⟨903222, by rfl⟩ : syracuseStep 9634373 = 1806445) (by norm_num)
theorem B6422915 : Blo 1923435 6422915 := bstep (se 1 (by rfl) ⟨4817186, by rfl⟩ : syracuseStep 6422915 = 9634373) B9634373
theorem B4281943 : Blo 1923435 4281943 := bstep (se 1 (by rfl) ⟨3211457, by rfl⟩ : syracuseStep 4281943 = 6422915) B6422915
theorem B5709257 : Blo 1923435 5709257 := bstep (se 2 (by rfl) ⟨2140971, by rfl⟩ : syracuseStep 5709257 = 4281943) B4281943
theorem B3806171 : Blo 1923435 3806171 := bstep (se 1 (by rfl) ⟨2854628, by rfl⟩ : syracuseStep 3806171 = 5709257) B5709257
theorem B2537447 : Blo 1923435 2537447 := bstep (se 1 (by rfl) ⟨1903085, by rfl⟩ : syracuseStep 2537447 = 3806171) B3806171
theorem B6766525 : Blo 1923435 6766525 := bstep (se 3 (by rfl) ⟨1268723, by rfl⟩ : syracuseStep 6766525 = 2537447) B2537447
theorem B9022033 : Blo 1923435 9022033 := bstep (se 2 (by rfl) ⟨3383262, by rfl⟩ : syracuseStep 9022033 = 6766525) B6766525
theorem B48117509 : Blo 1923435 48117509 := bstep (se 4 (by rfl) ⟨4511016, by rfl⟩ : syracuseStep 48117509 = 9022033) B9022033
theorem B32078339 : Blo 1923435 32078339 := bstep (se 1 (by rfl) ⟨24058754, by rfl⟩ : syracuseStep 32078339 = 48117509) B48117509
theorem B21385559 : Blo 1923435 21385559 := bstep (se 1 (by rfl) ⟨16039169, by rfl⟩ : syracuseStep 21385559 = 32078339) B32078339
theorem B57028157 : Blo 1923435 57028157 := bstep (se 3 (by rfl) ⟨10692779, by rfl⟩ : syracuseStep 57028157 = 21385559) B21385559
theorem B38018771 : Blo 1923435 38018771 := bstep (se 1 (by rfl) ⟨28514078, by rfl⟩ : syracuseStep 38018771 = 57028157) B57028157
theorem B25345847 : Blo 1923435 25345847 := bstep (se 1 (by rfl) ⟨19009385, by rfl⟩ : syracuseStep 25345847 = 38018771) B38018771
theorem B16897231 : Blo 1923435 16897231 := bstep (se 1 (by rfl) ⟨12672923, by rfl⟩ : syracuseStep 16897231 = 25345847) B25345847
theorem B90118565 : Blo 1923435 90118565 := bstep (se 4 (by rfl) ⟨8448615, by rfl⟩ : syracuseStep 90118565 = 16897231) B16897231
theorem B60079043 : Blo 1923435 60079043 := bstep (se 1 (by rfl) ⟨45059282, by rfl⟩ : syracuseStep 60079043 = 90118565) B90118565
theorem B160210781 : Blo 1923435 160210781 := bstep (se 3 (by rfl) ⟨30039521, by rfl⟩ : syracuseStep 160210781 = 60079043) B60079043
theorem B106807187 : Blo 1923435 106807187 := bstep (se 1 (by rfl) ⟨80105390, by rfl⟩ : syracuseStep 106807187 = 160210781) B160210781
theorem B71204791 : Blo 1923435 71204791 := bstep (se 1 (by rfl) ⟨53403593, by rfl⟩ : syracuseStep 71204791 = 106807187) B106807187
theorem B94939721 : Blo 1923435 94939721 := bstep (se 2 (by rfl) ⟨35602395, by rfl⟩ : syracuseStep 94939721 = 71204791) B71204791
theorem B63293147 : Blo 1923435 63293147 := bstep (se 1 (by rfl) ⟨47469860, by rfl⟩ : syracuseStep 63293147 = 94939721) B94939721
theorem B42195431 : Blo 1923435 42195431 := bstep (se 1 (by rfl) ⟨31646573, by rfl⟩ : syracuseStep 42195431 = 63293147) B63293147
theorem B112521149 : Blo 1923435 112521149 := bstep (se 3 (by rfl) ⟨21097715, by rfl⟩ : syracuseStep 112521149 = 42195431) B42195431
theorem B75014099 : Blo 1923435 75014099 := bstep (se 1 (by rfl) ⟨56260574, by rfl⟩ : syracuseStep 75014099 = 112521149) B112521149
theorem B50009399 : Blo 1923435 50009399 := bstep (se 1 (by rfl) ⟨37507049, by rfl⟩ : syracuseStep 50009399 = 75014099) B75014099
theorem B33339599 : Blo 1923435 33339599 := bstep (se 1 (by rfl) ⟨25004699, by rfl⟩ : syracuseStep 33339599 = 50009399) B50009399
theorem B22226399 : Blo 1923435 22226399 := bstep (se 1 (by rfl) ⟨16669799, by rfl⟩ : syracuseStep 22226399 = 33339599) B33339599
theorem B14817599 : Blo 1923435 14817599 := bstep (se 1 (by rfl) ⟨11113199, by rfl⟩ : syracuseStep 14817599 = 22226399) B22226399
theorem B9878399 : Blo 1923435 9878399 := bstep (se 1 (by rfl) ⟨7408799, by rfl⟩ : syracuseStep 9878399 = 14817599) B14817599
theorem B6585599 : Blo 1923435 6585599 := bstep (se 1 (by rfl) ⟨4939199, by rfl⟩ : syracuseStep 6585599 = 9878399) B9878399
theorem B4390399 : Blo 1923435 4390399 := bstep (se 1 (by rfl) ⟨3292799, by rfl⟩ : syracuseStep 4390399 = 6585599) B6585599
theorem B5853865 : Blo 1923435 5853865 := bstep (se 2 (by rfl) ⟨2195199, by rfl⟩ : syracuseStep 5853865 = 4390399) B4390399
theorem B7805153 : Blo 1923435 7805153 := bstep (se 2 (by rfl) ⟨2926932, by rfl⟩ : syracuseStep 7805153 = 5853865) B5853865
theorem B5203435 : Blo 1923435 5203435 := bstep (se 1 (by rfl) ⟨3902576, by rfl⟩ : syracuseStep 5203435 = 7805153) B7805153
theorem B6937913 : Blo 1923435 6937913 := bstep (se 2 (by rfl) ⟨2601717, by rfl⟩ : syracuseStep 6937913 = 5203435) B5203435
theorem B4625275 : Blo 1923435 4625275 := bstep (se 1 (by rfl) ⟨3468956, by rfl⟩ : syracuseStep 4625275 = 6937913) B6937913
theorem B6167033 : Blo 1923435 6167033 := bstep (se 2 (by rfl) ⟨2312637, by rfl⟩ : syracuseStep 6167033 = 4625275) B4625275
theorem B4111355 : Blo 1923435 4111355 := bstep (se 1 (by rfl) ⟨3083516, by rfl⟩ : syracuseStep 4111355 = 6167033) B6167033
theorem B10963613 : Blo 1923435 10963613 := bstep (se 3 (by rfl) ⟨2055677, by rfl⟩ : syracuseStep 10963613 = 4111355) B4111355
theorem B7309075 : Blo 1923435 7309075 := bstep (se 1 (by rfl) ⟨5481806, by rfl⟩ : syracuseStep 7309075 = 10963613) B10963613
theorem B9745433 : Blo 1923435 9745433 := bstep (se 2 (by rfl) ⟨3654537, by rfl⟩ : syracuseStep 9745433 = 7309075) B7309075
theorem B6496955 : Blo 1923435 6496955 := bstep (se 1 (by rfl) ⟨4872716, by rfl⟩ : syracuseStep 6496955 = 9745433) B9745433
theorem B4331303 : Blo 1923435 4331303 := bstep (se 1 (by rfl) ⟨3248477, by rfl⟩ : syracuseStep 4331303 = 6496955) B6496955
theorem B2887535 : Blo 1923435 2887535 := bstep (se 1 (by rfl) ⟨2165651, by rfl⟩ : syracuseStep 2887535 = 4331303) B4331303
theorem B1925023 : Blo 1923435 1925023 := bstep (se 1 (by rfl) ⟨1443767, by rfl⟩ : syracuseStep 1925023 = 2887535) B2887535
theorem B2887541 : Blo 1923435 2887541 := bbase (se 5 (by rfl) ⟨135353, by rfl⟩ : syracuseStep 2887541 = 270707) (by norm_num)
theorem B1925027 : Blo 1923435 1925027 := bstep (se 1 (by rfl) ⟨1443770, by rfl⟩ : syracuseStep 1925027 = 2887541) B2887541
theorem B4111373 : Blo 1923435 4111373 := bbase (se 3 (by rfl) ⟨770882, by rfl⟩ : syracuseStep 4111373 = 1541765) (by norm_num)
theorem B2740915 : Blo 1923435 2740915 := bstep (se 1 (by rfl) ⟨2055686, by rfl⟩ : syracuseStep 2740915 = 4111373) B4111373
theorem B3654553 : Blo 1923435 3654553 := bstep (se 2 (by rfl) ⟨1370457, by rfl⟩ : syracuseStep 3654553 = 2740915) B2740915
theorem B4872737 : Blo 1923435 4872737 := bstep (se 2 (by rfl) ⟨1827276, by rfl⟩ : syracuseStep 4872737 = 3654553) B3654553
theorem B3248491 : Blo 1923435 3248491 := bstep (se 1 (by rfl) ⟨2436368, by rfl⟩ : syracuseStep 3248491 = 4872737) B4872737
theorem B4331321 : Blo 1923435 4331321 := bstep (se 2 (by rfl) ⟨1624245, by rfl⟩ : syracuseStep 4331321 = 3248491) B3248491
theorem B2887547 : Blo 1923435 2887547 := bstep (se 1 (by rfl) ⟨2165660, by rfl⟩ : syracuseStep 2887547 = 4331321) B4331321
theorem B1925031 : Blo 1923435 1925031 := bstep (se 1 (by rfl) ⟨1443773, by rfl⟩ : syracuseStep 1925031 = 2887547) B2887547
theorem B2165665 : Blo 1923435 2165665 := bbase (se 2 (by rfl) ⟨812124, by rfl⟩ : syracuseStep 2165665 = 1624249) (by norm_num)
theorem B2887553 : Blo 1923435 2887553 := bstep (se 2 (by rfl) ⟨1082832, by rfl⟩ : syracuseStep 2887553 = 2165665) B2165665
theorem B1925035 : Blo 1923435 1925035 := bstep (se 1 (by rfl) ⟨1443776, by rfl⟩ : syracuseStep 1925035 = 2887553) B2887553
theorem B4872757 : Blo 1923435 4872757 := bbase (se 5 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 4872757 = 456821) (by norm_num)
theorem B6497009 : Blo 1923435 6497009 := bstep (se 2 (by rfl) ⟨2436378, by rfl⟩ : syracuseStep 6497009 = 4872757) B4872757
theorem B4331339 : Blo 1923435 4331339 := bstep (se 1 (by rfl) ⟨3248504, by rfl⟩ : syracuseStep 4331339 = 6497009) B6497009
theorem B2887559 : Blo 1923435 2887559 := bstep (se 1 (by rfl) ⟨2165669, by rfl⟩ : syracuseStep 2887559 = 4331339) B4331339
theorem B1925039 : Blo 1923435 1925039 := bstep (se 1 (by rfl) ⟨1443779, by rfl⟩ : syracuseStep 1925039 = 2887559) B2887559
theorem B2887565 : Blo 1923435 2887565 := bbase (se 3 (by rfl) ⟨541418, by rfl⟩ : syracuseStep 2887565 = 1082837) (by norm_num)
theorem B1925043 : Blo 1923435 1925043 := bstep (se 1 (by rfl) ⟨1443782, by rfl⟩ : syracuseStep 1925043 = 2887565) B2887565
theorem B4331357 : Blo 1923435 4331357 := bbase (se 3 (by rfl) ⟨812129, by rfl⟩ : syracuseStep 4331357 = 1624259) (by norm_num)
theorem B2887571 : Blo 1923435 2887571 := bstep (se 1 (by rfl) ⟨2165678, by rfl⟩ : syracuseStep 2887571 = 4331357) B4331357
theorem B1925047 : Blo 1923435 1925047 := bstep (se 1 (by rfl) ⟨1443785, by rfl⟩ : syracuseStep 1925047 = 2887571) B2887571
theorem B3248525 : Blo 1923435 3248525 := bbase (se 3 (by rfl) ⟨609098, by rfl⟩ : syracuseStep 3248525 = 1218197) (by norm_num)
theorem B2165683 : Blo 1923435 2165683 := bstep (se 1 (by rfl) ⟨1624262, by rfl⟩ : syracuseStep 2165683 = 3248525) B3248525
theorem B2887577 : Blo 1923435 2887577 := bstep (se 2 (by rfl) ⟨1082841, by rfl⟩ : syracuseStep 2887577 = 2165683) B2165683
theorem B1925051 : Blo 1923435 1925051 := bstep (se 1 (by rfl) ⟨1443788, by rfl⟩ : syracuseStep 1925051 = 2887577) B2887577
theorem B5274517 : Blo 1923435 5274517 := bbase (se 6 (by rfl) ⟨123621, by rfl⟩ : syracuseStep 5274517 = 247243) (by norm_num)
theorem B7032689 : Blo 1923435 7032689 := bstep (se 2 (by rfl) ⟨2637258, by rfl⟩ : syracuseStep 7032689 = 5274517) B5274517
theorem B4688459 : Blo 1923435 4688459 := bstep (se 1 (by rfl) ⟨3516344, by rfl⟩ : syracuseStep 4688459 = 7032689) B7032689
theorem B3125639 : Blo 1923435 3125639 := bstep (se 1 (by rfl) ⟨2344229, by rfl⟩ : syracuseStep 3125639 = 4688459) B4688459
theorem B8335037 : Blo 1923435 8335037 := bstep (se 3 (by rfl) ⟨1562819, by rfl⟩ : syracuseStep 8335037 = 3125639) B3125639
theorem B5556691 : Blo 1923435 5556691 := bstep (se 1 (by rfl) ⟨4167518, by rfl⟩ : syracuseStep 5556691 = 8335037) B8335037
theorem B7408921 : Blo 1923435 7408921 := bstep (se 2 (by rfl) ⟨2778345, by rfl⟩ : syracuseStep 7408921 = 5556691) B5556691
theorem B9878561 : Blo 1923435 9878561 := bstep (se 2 (by rfl) ⟨3704460, by rfl⟩ : syracuseStep 9878561 = 7408921) B7408921
theorem B6585707 : Blo 1923435 6585707 := bstep (se 1 (by rfl) ⟨4939280, by rfl⟩ : syracuseStep 6585707 = 9878561) B9878561
theorem B4390471 : Blo 1923435 4390471 := bstep (se 1 (by rfl) ⟨3292853, by rfl⟩ : syracuseStep 4390471 = 6585707) B6585707
theorem B5853961 : Blo 1923435 5853961 := bstep (se 2 (by rfl) ⟨2195235, by rfl⟩ : syracuseStep 5853961 = 4390471) B4390471
theorem B31221125 : Blo 1923435 31221125 := bstep (se 4 (by rfl) ⟨2926980, by rfl⟩ : syracuseStep 31221125 = 5853961) B5853961
theorem B20814083 : Blo 1923435 20814083 := bstep (se 1 (by rfl) ⟨15610562, by rfl⟩ : syracuseStep 20814083 = 31221125) B31221125
theorem B13876055 : Blo 1923435 13876055 := bstep (se 1 (by rfl) ⟨10407041, by rfl⟩ : syracuseStep 13876055 = 20814083) B20814083
theorem B9250703 : Blo 1923435 9250703 := bstep (se 1 (by rfl) ⟨6938027, by rfl⟩ : syracuseStep 9250703 = 13876055) B13876055
theorem B6167135 : Blo 1923435 6167135 := bstep (se 1 (by rfl) ⟨4625351, by rfl⟩ : syracuseStep 6167135 = 9250703) B9250703
theorem B16445693 : Blo 1923435 16445693 := bstep (se 3 (by rfl) ⟨3083567, by rfl⟩ : syracuseStep 16445693 = 6167135) B6167135
theorem B10963795 : Blo 1923435 10963795 := bstep (se 1 (by rfl) ⟨8222846, by rfl⟩ : syracuseStep 10963795 = 16445693) B16445693
theorem B14618393 : Blo 1923435 14618393 := bstep (se 2 (by rfl) ⟨5481897, by rfl⟩ : syracuseStep 14618393 = 10963795) B10963795
theorem B9745595 : Blo 1923435 9745595 := bstep (se 1 (by rfl) ⟨7309196, by rfl⟩ : syracuseStep 9745595 = 14618393) B14618393
theorem B6497063 : Blo 1923435 6497063 := bstep (se 1 (by rfl) ⟨4872797, by rfl⟩ : syracuseStep 6497063 = 9745595) B9745595
theorem B4331375 : Blo 1923435 4331375 := bstep (se 1 (by rfl) ⟨3248531, by rfl⟩ : syracuseStep 4331375 = 6497063) B6497063
theorem B2887583 : Blo 1923435 2887583 := bstep (se 1 (by rfl) ⟨2165687, by rfl⟩ : syracuseStep 2887583 = 4331375) B4331375
theorem B1925055 : Blo 1923435 1925055 := bstep (se 1 (by rfl) ⟨1443791, by rfl⟩ : syracuseStep 1925055 = 2887583) B2887583
theorem B2887589 : Blo 1923435 2887589 := bbase (se 4 (by rfl) ⟨270711, by rfl⟩ : syracuseStep 2887589 = 541423) (by norm_num)
theorem B1925059 : Blo 1923435 1925059 := bstep (se 1 (by rfl) ⟨1443794, by rfl⟩ : syracuseStep 1925059 = 2887589) B2887589
theorem B2436409 : Blo 1923435 2436409 := bbase (se 2 (by rfl) ⟨913653, by rfl⟩ : syracuseStep 2436409 = 1827307) (by norm_num)
theorem B3248545 : Blo 1923435 3248545 := bstep (se 2 (by rfl) ⟨1218204, by rfl⟩ : syracuseStep 3248545 = 2436409) B2436409
theorem B4331393 : Blo 1923435 4331393 := bstep (se 2 (by rfl) ⟨1624272, by rfl⟩ : syracuseStep 4331393 = 3248545) B3248545
theorem B2887595 : Blo 1923435 2887595 := bstep (se 1 (by rfl) ⟨2165696, by rfl⟩ : syracuseStep 2887595 = 4331393) B4331393
theorem B1925063 : Blo 1923435 1925063 := bstep (se 1 (by rfl) ⟨1443797, by rfl⟩ : syracuseStep 1925063 = 2887595) B2887595
theorem B2165701 : Blo 1923435 2165701 := bbase (se 4 (by rfl) ⟨203034, by rfl⟩ : syracuseStep 2165701 = 406069) (by norm_num)
theorem B2887601 : Blo 1923435 2887601 := bstep (se 2 (by rfl) ⟨1082850, by rfl⟩ : syracuseStep 2887601 = 2165701) B2165701
theorem B1925067 : Blo 1923435 1925067 := bstep (se 1 (by rfl) ⟨1443800, by rfl⟩ : syracuseStep 1925067 = 2887601) B2887601
theorem B3654629 : Blo 1923435 3654629 := bbase (se 4 (by rfl) ⟨342621, by rfl⟩ : syracuseStep 3654629 = 685243) (by norm_num)
theorem B2436419 : Blo 1923435 2436419 := bstep (se 1 (by rfl) ⟨1827314, by rfl⟩ : syracuseStep 2436419 = 3654629) B3654629
theorem B6497117 : Blo 1923435 6497117 := bstep (se 3 (by rfl) ⟨1218209, by rfl⟩ : syracuseStep 6497117 = 2436419) B2436419
theorem B4331411 : Blo 1923435 4331411 := bstep (se 1 (by rfl) ⟨3248558, by rfl⟩ : syracuseStep 4331411 = 6497117) B6497117
theorem B2887607 : Blo 1923435 2887607 := bstep (se 1 (by rfl) ⟨2165705, by rfl⟩ : syracuseStep 2887607 = 4331411) B4331411
theorem B1925071 : Blo 1923435 1925071 := bstep (se 1 (by rfl) ⟨1443803, by rfl⟩ : syracuseStep 1925071 = 2887607) B2887607
theorem B2887613 : Blo 1923435 2887613 := bbase (se 3 (by rfl) ⟨541427, by rfl⟩ : syracuseStep 2887613 = 1082855) (by norm_num)
theorem B1925075 : Blo 1923435 1925075 := bstep (se 1 (by rfl) ⟨1443806, by rfl⟩ : syracuseStep 1925075 = 2887613) B2887613
theorem B4331429 : Blo 1923435 4331429 := bbase (se 4 (by rfl) ⟨406071, by rfl⟩ : syracuseStep 4331429 = 812143) (by norm_num)
theorem B2887619 : Blo 1923435 2887619 := bstep (se 1 (by rfl) ⟨2165714, by rfl⟩ : syracuseStep 2887619 = 4331429) B4331429
theorem B1925079 : Blo 1923435 1925079 := bstep (se 1 (by rfl) ⟨1443809, by rfl⟩ : syracuseStep 1925079 = 2887619) B2887619
theorem B4872869 : Blo 1923435 4872869 := bbase (se 4 (by rfl) ⟨456831, by rfl⟩ : syracuseStep 4872869 = 913663) (by norm_num)
theorem B3248579 : Blo 1923435 3248579 := bstep (se 1 (by rfl) ⟨2436434, by rfl⟩ : syracuseStep 3248579 = 4872869) B4872869
theorem B2165719 : Blo 1923435 2165719 := bstep (se 1 (by rfl) ⟨1624289, by rfl⟩ : syracuseStep 2165719 = 3248579) B3248579
theorem B2887625 : Blo 1923435 2887625 := bstep (se 2 (by rfl) ⟨1082859, by rfl⟩ : syracuseStep 2887625 = 2165719) B2165719
theorem B1925083 : Blo 1923435 1925083 := bstep (se 1 (by rfl) ⟨1443812, by rfl⟩ : syracuseStep 1925083 = 2887625) B2887625
theorem B5481989 : Blo 1923435 5481989 := bbase (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) (by norm_num)
theorem B3654659 : Blo 1923435 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B9745757 : Blo 1923435 9745757 := bstep (se 3 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 9745757 = 3654659) B3654659
theorem B6497171 : Blo 1923435 6497171 := bstep (se 1 (by rfl) ⟨4872878, by rfl⟩ : syracuseStep 6497171 = 9745757) B9745757
theorem B4331447 : Blo 1923435 4331447 := bstep (se 1 (by rfl) ⟨3248585, by rfl⟩ : syracuseStep 4331447 = 6497171) B6497171
theorem B2887631 : Blo 1923435 2887631 := bstep (se 1 (by rfl) ⟨2165723, by rfl⟩ : syracuseStep 2887631 = 4331447) B4331447
theorem B1925087 : Blo 1923435 1925087 := bstep (se 1 (by rfl) ⟨1443815, by rfl⟩ : syracuseStep 1925087 = 2887631) B2887631
theorem B2887637 : Blo 1923435 2887637 := bbase (se 7 (by rfl) ⟨33839, by rfl⟩ : syracuseStep 2887637 = 67679) (by norm_num)
theorem B1925091 : Blo 1923435 1925091 := bstep (se 1 (by rfl) ⟨1443818, by rfl⟩ : syracuseStep 1925091 = 2887637) B2887637
theorem B7309349 : Blo 1923435 7309349 := bbase (se 4 (by rfl) ⟨685251, by rfl⟩ : syracuseStep 7309349 = 1370503) (by norm_num)
theorem B4872899 : Blo 1923435 4872899 := bstep (se 1 (by rfl) ⟨3654674, by rfl⟩ : syracuseStep 4872899 = 7309349) B7309349
theorem B3248599 : Blo 1923435 3248599 := bstep (se 1 (by rfl) ⟨2436449, by rfl⟩ : syracuseStep 3248599 = 4872899) B4872899
theorem B4331465 : Blo 1923435 4331465 := bstep (se 2 (by rfl) ⟨1624299, by rfl⟩ : syracuseStep 4331465 = 3248599) B3248599
theorem B2887643 : Blo 1923435 2887643 := bstep (se 1 (by rfl) ⟨2165732, by rfl⟩ : syracuseStep 2887643 = 4331465) B4331465
theorem B1925095 : Blo 1923435 1925095 := bstep (se 1 (by rfl) ⟨1443821, by rfl⟩ : syracuseStep 1925095 = 2887643) B2887643
theorem B2165737 : Blo 1923435 2165737 := bbase (se 2 (by rfl) ⟨812151, by rfl⟩ : syracuseStep 2165737 = 1624303) (by norm_num)
theorem B2887649 : Blo 1923435 2887649 := bstep (se 2 (by rfl) ⟨1082868, by rfl⟩ : syracuseStep 2887649 = 2165737) B2165737
theorem B1925099 : Blo 1923435 1925099 := bstep (se 1 (by rfl) ⟨1443824, by rfl⟩ : syracuseStep 1925099 = 2887649) B2887649
theorem B3083645 : Blo 1923435 3083645 := bbase (se 3 (by rfl) ⟨578183, by rfl⟩ : syracuseStep 3083645 = 1156367) (by norm_num)
theorem B2055763 : Blo 1923435 2055763 := bstep (se 1 (by rfl) ⟨1541822, by rfl⟩ : syracuseStep 2055763 = 3083645) B3083645
theorem B10964069 : Blo 1923435 10964069 := bstep (se 4 (by rfl) ⟨1027881, by rfl⟩ : syracuseStep 10964069 = 2055763) B2055763
theorem B7309379 : Blo 1923435 7309379 := bstep (se 1 (by rfl) ⟨5482034, by rfl⟩ : syracuseStep 7309379 = 10964069) B10964069
theorem B4872919 : Blo 1923435 4872919 := bstep (se 1 (by rfl) ⟨3654689, by rfl⟩ : syracuseStep 4872919 = 7309379) B7309379
theorem B6497225 : Blo 1923435 6497225 := bstep (se 2 (by rfl) ⟨2436459, by rfl⟩ : syracuseStep 6497225 = 4872919) B4872919
theorem B4331483 : Blo 1923435 4331483 := bstep (se 1 (by rfl) ⟨3248612, by rfl⟩ : syracuseStep 4331483 = 6497225) B6497225
theorem B2887655 : Blo 1923435 2887655 := bstep (se 1 (by rfl) ⟨2165741, by rfl⟩ : syracuseStep 2887655 = 4331483) B4331483
theorem B1925103 : Blo 1923435 1925103 := bstep (se 1 (by rfl) ⟨1443827, by rfl⟩ : syracuseStep 1925103 = 2887655) B2887655
theorem B2887661 : Blo 1923435 2887661 := bbase (se 3 (by rfl) ⟨541436, by rfl⟩ : syracuseStep 2887661 = 1082873) (by norm_num)
theorem B1925107 : Blo 1923435 1925107 := bstep (se 1 (by rfl) ⟨1443830, by rfl⟩ : syracuseStep 1925107 = 2887661) B2887661
theorem B4331501 : Blo 1923435 4331501 := bbase (se 3 (by rfl) ⟨812156, by rfl⟩ : syracuseStep 4331501 = 1624313) (by norm_num)
theorem B2887667 : Blo 1923435 2887667 := bstep (se 1 (by rfl) ⟨2165750, by rfl⟩ : syracuseStep 2887667 = 4331501) B4331501
theorem B1925111 : Blo 1923435 1925111 := bstep (se 1 (by rfl) ⟨1443833, by rfl⟩ : syracuseStep 1925111 = 2887667) B2887667
theorem B2312749 : Blo 1923435 2312749 := bbase (se 3 (by rfl) ⟨433640, by rfl⟩ : syracuseStep 2312749 = 867281) (by norm_num)
theorem B3083665 : Blo 1923435 3083665 := bstep (se 2 (by rfl) ⟨1156374, by rfl⟩ : syracuseStep 3083665 = 2312749) B2312749
theorem B4111553 : Blo 1923435 4111553 := bstep (se 2 (by rfl) ⟨1541832, by rfl⟩ : syracuseStep 4111553 = 3083665) B3083665
theorem B2741035 : Blo 1923435 2741035 := bstep (se 1 (by rfl) ⟨2055776, by rfl⟩ : syracuseStep 2741035 = 4111553) B4111553
theorem B3654713 : Blo 1923435 3654713 := bstep (se 2 (by rfl) ⟨1370517, by rfl⟩ : syracuseStep 3654713 = 2741035) B2741035
theorem B2436475 : Blo 1923435 2436475 := bstep (se 1 (by rfl) ⟨1827356, by rfl⟩ : syracuseStep 2436475 = 3654713) B3654713
theorem B3248633 : Blo 1923435 3248633 := bstep (se 2 (by rfl) ⟨1218237, by rfl⟩ : syracuseStep 3248633 = 2436475) B2436475
theorem B2165755 : Blo 1923435 2165755 := bstep (se 1 (by rfl) ⟨1624316, by rfl⟩ : syracuseStep 2165755 = 3248633) B3248633
theorem B2887673 : Blo 1923435 2887673 := bstep (se 2 (by rfl) ⟨1082877, by rfl⟩ : syracuseStep 2887673 = 2165755) B2165755
theorem B1925115 : Blo 1923435 1925115 := bstep (se 1 (by rfl) ⟨1443836, by rfl⟩ : syracuseStep 1925115 = 2887673) B2887673
theorem B2778437 : Blo 1923435 2778437 := bbase (se 4 (by rfl) ⟨260478, by rfl⟩ : syracuseStep 2778437 = 520957) (by norm_num)
theorem B7409165 : Blo 1923435 7409165 := bstep (se 3 (by rfl) ⟨1389218, by rfl⟩ : syracuseStep 7409165 = 2778437) B2778437
theorem B19757773 : Blo 1923435 19757773 := bstep (se 3 (by rfl) ⟨3704582, by rfl⟩ : syracuseStep 19757773 = 7409165) B7409165
theorem B26343697 : Blo 1923435 26343697 := bstep (se 2 (by rfl) ⟨9878886, by rfl⟩ : syracuseStep 26343697 = 19757773) B19757773
theorem B35124929 : Blo 1923435 35124929 := bstep (se 2 (by rfl) ⟨13171848, by rfl⟩ : syracuseStep 35124929 = 26343697) B26343697
theorem B23416619 : Blo 1923435 23416619 := bstep (se 1 (by rfl) ⟨17562464, by rfl⟩ : syracuseStep 23416619 = 35124929) B35124929
theorem B249777269 : Blo 1923435 249777269 := bstep (se 5 (by rfl) ⟨11708309, by rfl⟩ : syracuseStep 249777269 = 23416619) B23416619
theorem B166518179 : Blo 1923435 166518179 := bstep (se 1 (by rfl) ⟨124888634, by rfl⟩ : syracuseStep 166518179 = 249777269) B249777269
theorem B111012119 : Blo 1923435 111012119 := bstep (se 1 (by rfl) ⟨83259089, by rfl⟩ : syracuseStep 111012119 = 166518179) B166518179
theorem B74008079 : Blo 1923435 74008079 := bstep (se 1 (by rfl) ⟨55506059, by rfl⟩ : syracuseStep 74008079 = 111012119) B111012119
theorem B49338719 : Blo 1923435 49338719 := bstep (se 1 (by rfl) ⟨37004039, by rfl⟩ : syracuseStep 49338719 = 74008079) B74008079
theorem B32892479 : Blo 1923435 32892479 := bstep (se 1 (by rfl) ⟨24669359, by rfl⟩ : syracuseStep 32892479 = 49338719) B49338719
theorem B21928319 : Blo 1923435 21928319 := bstep (se 1 (by rfl) ⟨16446239, by rfl⟩ : syracuseStep 21928319 = 32892479) B32892479
theorem B14618879 : Blo 1923435 14618879 := bstep (se 1 (by rfl) ⟨10964159, by rfl⟩ : syracuseStep 14618879 = 21928319) B21928319
theorem B9745919 : Blo 1923435 9745919 := bstep (se 1 (by rfl) ⟨7309439, by rfl⟩ : syracuseStep 9745919 = 14618879) B14618879
theorem B6497279 : Blo 1923435 6497279 := bstep (se 1 (by rfl) ⟨4872959, by rfl⟩ : syracuseStep 6497279 = 9745919) B9745919
theorem B4331519 : Blo 1923435 4331519 := bstep (se 1 (by rfl) ⟨3248639, by rfl⟩ : syracuseStep 4331519 = 6497279) B6497279
theorem B2887679 : Blo 1923435 2887679 := bstep (se 1 (by rfl) ⟨2165759, by rfl⟩ : syracuseStep 2887679 = 4331519) B4331519
theorem B1925119 : Blo 1923435 1925119 := bstep (se 1 (by rfl) ⟨1443839, by rfl⟩ : syracuseStep 1925119 = 2887679) B2887679
theorem B2887685 : Blo 1923435 2887685 := bbase (se 4 (by rfl) ⟨270720, by rfl⟩ : syracuseStep 2887685 = 541441) (by norm_num)
theorem B1925123 : Blo 1923435 1925123 := bstep (se 1 (by rfl) ⟨1443842, by rfl⟩ : syracuseStep 1925123 = 2887685) B2887685
theorem B3248653 : Blo 1923435 3248653 := bbase (se 3 (by rfl) ⟨609122, by rfl⟩ : syracuseStep 3248653 = 1218245) (by norm_num)
theorem B4331537 : Blo 1923435 4331537 := bstep (se 2 (by rfl) ⟨1624326, by rfl⟩ : syracuseStep 4331537 = 3248653) B3248653
theorem B2887691 : Blo 1923435 2887691 := bstep (se 1 (by rfl) ⟨2165768, by rfl⟩ : syracuseStep 2887691 = 4331537) B4331537
theorem B1925127 : Blo 1923435 1925127 := bstep (se 1 (by rfl) ⟨1443845, by rfl⟩ : syracuseStep 1925127 = 2887691) B2887691
theorem B2165773 : Blo 1923435 2165773 := bbase (se 3 (by rfl) ⟨406082, by rfl⟩ : syracuseStep 2165773 = 812165) (by norm_num)
theorem B2887697 : Blo 1923435 2887697 := bstep (se 2 (by rfl) ⟨1082886, by rfl⟩ : syracuseStep 2887697 = 2165773) B2165773
theorem B1925131 : Blo 1923435 1925131 := bstep (se 1 (by rfl) ⟨1443848, by rfl⟩ : syracuseStep 1925131 = 2887697) B2887697
theorem B6497333 : Blo 1923435 6497333 := bbase (se 5 (by rfl) ⟨304562, by rfl⟩ : syracuseStep 6497333 = 609125) (by norm_num)
theorem B4331555 : Blo 1923435 4331555 := bstep (se 1 (by rfl) ⟨3248666, by rfl⟩ : syracuseStep 4331555 = 6497333) B6497333
theorem B2887703 : Blo 1923435 2887703 := bstep (se 1 (by rfl) ⟨2165777, by rfl⟩ : syracuseStep 2887703 = 4331555) B4331555
theorem B1925135 : Blo 1923435 1925135 := bstep (se 1 (by rfl) ⟨1443851, by rfl⟩ : syracuseStep 1925135 = 2887703) B2887703
theorem B2887709 : Blo 1923435 2887709 := bbase (se 3 (by rfl) ⟨541445, by rfl⟩ : syracuseStep 2887709 = 1082891) (by norm_num)
theorem B1925139 : Blo 1923435 1925139 := bstep (se 1 (by rfl) ⟨1443854, by rfl⟩ : syracuseStep 1925139 = 2887709) B2887709
theorem B4331573 : Blo 1923435 4331573 := bbase (se 5 (by rfl) ⟨203042, by rfl⟩ : syracuseStep 4331573 = 406085) (by norm_num)
theorem B2887715 : Blo 1923435 2887715 := bstep (se 1 (by rfl) ⟨2165786, by rfl⟩ : syracuseStep 2887715 = 4331573) B4331573
theorem B1925143 : Blo 1923435 1925143 := bstep (se 1 (by rfl) ⟨1443857, by rfl⟩ : syracuseStep 1925143 = 2887715) B2887715
theorem B10407541 : Blo 1923435 10407541 := bbase (se 5 (by rfl) ⟨487853, by rfl⟩ : syracuseStep 10407541 = 975707) (by norm_num)
theorem B13876721 : Blo 1923435 13876721 := bstep (se 2 (by rfl) ⟨5203770, by rfl⟩ : syracuseStep 13876721 = 10407541) B10407541
theorem B9251147 : Blo 1923435 9251147 := bstep (se 1 (by rfl) ⟨6938360, by rfl⟩ : syracuseStep 9251147 = 13876721) B13876721
theorem B6167431 : Blo 1923435 6167431 := bstep (se 1 (by rfl) ⟨4625573, by rfl⟩ : syracuseStep 6167431 = 9251147) B9251147
theorem B8223241 : Blo 1923435 8223241 := bstep (se 2 (by rfl) ⟨3083715, by rfl⟩ : syracuseStep 8223241 = 6167431) B6167431
theorem B10964321 : Blo 1923435 10964321 := bstep (se 2 (by rfl) ⟨4111620, by rfl⟩ : syracuseStep 10964321 = 8223241) B8223241
theorem B7309547 : Blo 1923435 7309547 := bstep (se 1 (by rfl) ⟨5482160, by rfl⟩ : syracuseStep 7309547 = 10964321) B10964321
theorem B4873031 : Blo 1923435 4873031 := bstep (se 1 (by rfl) ⟨3654773, by rfl⟩ : syracuseStep 4873031 = 7309547) B7309547
theorem B3248687 : Blo 1923435 3248687 := bstep (se 1 (by rfl) ⟨2436515, by rfl⟩ : syracuseStep 3248687 = 4873031) B4873031
theorem B2165791 : Blo 1923435 2165791 := bstep (se 1 (by rfl) ⟨1624343, by rfl⟩ : syracuseStep 2165791 = 3248687) B3248687
theorem B2887721 : Blo 1923435 2887721 := bstep (se 2 (by rfl) ⟨1082895, by rfl⟩ : syracuseStep 2887721 = 2165791) B2165791
theorem B1925147 : Blo 1923435 1925147 := bstep (se 1 (by rfl) ⟨1443860, by rfl⟩ : syracuseStep 1925147 = 2887721) B2887721
theorem B5203781 : Blo 1923435 5203781 := bbase (se 4 (by rfl) ⟨487854, by rfl⟩ : syracuseStep 5203781 = 975709) (by norm_num)
theorem B3469187 : Blo 1923435 3469187 := bstep (se 1 (by rfl) ⟨2601890, by rfl⟩ : syracuseStep 3469187 = 5203781) B5203781
theorem B9251165 : Blo 1923435 9251165 := bstep (se 3 (by rfl) ⟨1734593, by rfl⟩ : syracuseStep 9251165 = 3469187) B3469187
theorem B6167443 : Blo 1923435 6167443 := bstep (se 1 (by rfl) ⟨4625582, by rfl⟩ : syracuseStep 6167443 = 9251165) B9251165
theorem B8223257 : Blo 1923435 8223257 := bstep (se 2 (by rfl) ⟨3083721, by rfl⟩ : syracuseStep 8223257 = 6167443) B6167443
theorem B5482171 : Blo 1923435 5482171 := bstep (se 1 (by rfl) ⟨4111628, by rfl⟩ : syracuseStep 5482171 = 8223257) B8223257
theorem B7309561 : Blo 1923435 7309561 := bstep (se 2 (by rfl) ⟨2741085, by rfl⟩ : syracuseStep 7309561 = 5482171) B5482171
theorem B9746081 : Blo 1923435 9746081 := bstep (se 2 (by rfl) ⟨3654780, by rfl⟩ : syracuseStep 9746081 = 7309561) B7309561
theorem B6497387 : Blo 1923435 6497387 := bstep (se 1 (by rfl) ⟨4873040, by rfl⟩ : syracuseStep 6497387 = 9746081) B9746081
theorem B4331591 : Blo 1923435 4331591 := bstep (se 1 (by rfl) ⟨3248693, by rfl⟩ : syracuseStep 4331591 = 6497387) B6497387
theorem B2887727 : Blo 1923435 2887727 := bstep (se 1 (by rfl) ⟨2165795, by rfl⟩ : syracuseStep 2887727 = 4331591) B4331591
theorem B1925151 : Blo 1923435 1925151 := bstep (se 1 (by rfl) ⟨1443863, by rfl⟩ : syracuseStep 1925151 = 2887727) B2887727
theorem B2887733 : Blo 1923435 2887733 := bbase (se 5 (by rfl) ⟨135362, by rfl⟩ : syracuseStep 2887733 = 270725) (by norm_num)
theorem B1925155 : Blo 1923435 1925155 := bstep (se 1 (by rfl) ⟨1443866, by rfl⟩ : syracuseStep 1925155 = 2887733) B2887733
theorem B4873061 : Blo 1923435 4873061 := bbase (se 4 (by rfl) ⟨456849, by rfl⟩ : syracuseStep 4873061 = 913699) (by norm_num)
theorem B3248707 : Blo 1923435 3248707 := bstep (se 1 (by rfl) ⟨2436530, by rfl⟩ : syracuseStep 3248707 = 4873061) B4873061
theorem B4331609 : Blo 1923435 4331609 := bstep (se 2 (by rfl) ⟨1624353, by rfl⟩ : syracuseStep 4331609 = 3248707) B3248707
theorem B2887739 : Blo 1923435 2887739 := bstep (se 1 (by rfl) ⟨2165804, by rfl⟩ : syracuseStep 2887739 = 4331609) B4331609
theorem B1925159 : Blo 1923435 1925159 := bstep (se 1 (by rfl) ⟨1443869, by rfl⟩ : syracuseStep 1925159 = 2887739) B2887739
theorem B2165809 : Blo 1923435 2165809 := bbase (se 2 (by rfl) ⟨812178, by rfl⟩ : syracuseStep 2165809 = 1624357) (by norm_num)
theorem B2887745 : Blo 1923435 2887745 := bstep (se 2 (by rfl) ⟨1082904, by rfl⟩ : syracuseStep 2887745 = 2165809) B2165809
theorem B1925163 : Blo 1923435 1925163 := bstep (se 1 (by rfl) ⟨1443872, by rfl⟩ : syracuseStep 1925163 = 2887745) B2887745
theorem B12503285 : Blo 1923435 12503285 := bbase (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) (by norm_num)
theorem B8335523 : Blo 1923435 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B5557015 : Blo 1923435 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B29637413 : Blo 1923435 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B19758275 : Blo 1923435 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B13172183 : Blo 1923435 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B8781455 : Blo 1923435 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B5854303 : Blo 1923435 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B7805737 : Blo 1923435 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B10407649 : Blo 1923435 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B13876865 : Blo 1923435 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B9251243 : Blo 1923435 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B6167495 : Blo 1923435 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B4111663 : Blo 1923435 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B5482217 : Blo 1923435 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B3654811 : Blo 1923435 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B4873081 : Blo 1923435 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B6497441 : Blo 1923435 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B4331627 : Blo 1923435 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B2887751 : Blo 1923435 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B1925167 : Blo 1923435 1925167 := bstep (se 1 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 1925167 = 2887751) B2887751
theorem B2887757 : Blo 1923435 2887757 := bbase (se 3 (by rfl) ⟨541454, by rfl⟩ : syracuseStep 2887757 = 1082909) (by norm_num)
theorem B1925171 : Blo 1923435 1925171 := bstep (se 1 (by rfl) ⟨1443878, by rfl⟩ : syracuseStep 1925171 = 2887757) B2887757
theorem B4331645 : Blo 1923435 4331645 := bbase (se 3 (by rfl) ⟨812183, by rfl⟩ : syracuseStep 4331645 = 1624367) (by norm_num)
theorem B2887763 : Blo 1923435 2887763 := bstep (se 1 (by rfl) ⟨2165822, by rfl⟩ : syracuseStep 2887763 = 4331645) B4331645
theorem B1925175 : Blo 1923435 1925175 := bstep (se 1 (by rfl) ⟨1443881, by rfl⟩ : syracuseStep 1925175 = 2887763) B2887763
theorem B3248741 : Blo 1923435 3248741 := bbase (se 4 (by rfl) ⟨304569, by rfl⟩ : syracuseStep 3248741 = 609139) (by norm_num)
theorem B2165827 : Blo 1923435 2165827 := bstep (se 1 (by rfl) ⟨1624370, by rfl⟩ : syracuseStep 2165827 = 3248741) B3248741
theorem B2887769 : Blo 1923435 2887769 := bstep (se 2 (by rfl) ⟨1082913, by rfl⟩ : syracuseStep 2887769 = 2165827) B2165827
theorem B1925179 : Blo 1923435 1925179 := bstep (se 1 (by rfl) ⟨1443884, by rfl⟩ : syracuseStep 1925179 = 2887769) B2887769
theorem B3083773 : Blo 1923435 3083773 := bbase (se 3 (by rfl) ⟨578207, by rfl⟩ : syracuseStep 3083773 = 1156415) (by norm_num)
theorem B4111697 : Blo 1923435 4111697 := bstep (se 2 (by rfl) ⟨1541886, by rfl⟩ : syracuseStep 4111697 = 3083773) B3083773
theorem B2741131 : Blo 1923435 2741131 := bstep (se 1 (by rfl) ⟨2055848, by rfl⟩ : syracuseStep 2741131 = 4111697) B4111697
theorem B14619365 : Blo 1923435 14619365 := bstep (se 4 (by rfl) ⟨1370565, by rfl⟩ : syracuseStep 14619365 = 2741131) B2741131
theorem B9746243 : Blo 1923435 9746243 := bstep (se 1 (by rfl) ⟨7309682, by rfl⟩ : syracuseStep 9746243 = 14619365) B14619365
theorem B6497495 : Blo 1923435 6497495 := bstep (se 1 (by rfl) ⟨4873121, by rfl⟩ : syracuseStep 6497495 = 9746243) B9746243
theorem B4331663 : Blo 1923435 4331663 := bstep (se 1 (by rfl) ⟨3248747, by rfl⟩ : syracuseStep 4331663 = 6497495) B6497495
theorem B2887775 : Blo 1923435 2887775 := bstep (se 1 (by rfl) ⟨2165831, by rfl⟩ : syracuseStep 2887775 = 4331663) B4331663
theorem B1925183 : Blo 1923435 1925183 := bstep (se 1 (by rfl) ⟨1443887, by rfl⟩ : syracuseStep 1925183 = 2887775) B2887775
theorem B2887781 : Blo 1923435 2887781 := bbase (se 4 (by rfl) ⟨270729, by rfl⟩ : syracuseStep 2887781 = 541459) (by norm_num)
theorem B1925187 : Blo 1923435 1925187 := bstep (se 1 (by rfl) ⟨1443890, by rfl⟩ : syracuseStep 1925187 = 2887781) B2887781
theorem B6167573 : Blo 1923435 6167573 := bbase (se 6 (by rfl) ⟨144552, by rfl⟩ : syracuseStep 6167573 = 289105) (by norm_num)
theorem B4111715 : Blo 1923435 4111715 := bstep (se 1 (by rfl) ⟨3083786, by rfl⟩ : syracuseStep 4111715 = 6167573) B6167573
theorem B2741143 : Blo 1923435 2741143 := bstep (se 1 (by rfl) ⟨2055857, by rfl⟩ : syracuseStep 2741143 = 4111715) B4111715
theorem B3654857 : Blo 1923435 3654857 := bstep (se 2 (by rfl) ⟨1370571, by rfl⟩ : syracuseStep 3654857 = 2741143) B2741143
theorem B2436571 : Blo 1923435 2436571 := bstep (se 1 (by rfl) ⟨1827428, by rfl⟩ : syracuseStep 2436571 = 3654857) B3654857
theorem B3248761 : Blo 1923435 3248761 := bstep (se 2 (by rfl) ⟨1218285, by rfl⟩ : syracuseStep 3248761 = 2436571) B2436571
theorem B4331681 : Blo 1923435 4331681 := bstep (se 2 (by rfl) ⟨1624380, by rfl⟩ : syracuseStep 4331681 = 3248761) B3248761
theorem B2887787 : Blo 1923435 2887787 := bstep (se 1 (by rfl) ⟨2165840, by rfl⟩ : syracuseStep 2887787 = 4331681) B4331681
theorem B1925191 : Blo 1923435 1925191 := bstep (se 1 (by rfl) ⟨1443893, by rfl⟩ : syracuseStep 1925191 = 2887787) B2887787
theorem B2165845 : Blo 1923435 2165845 := bbase (se 8 (by rfl) ⟨12690, by rfl⟩ : syracuseStep 2165845 = 25381) (by norm_num)
theorem B2887793 : Blo 1923435 2887793 := bstep (se 2 (by rfl) ⟨1082922, by rfl⟩ : syracuseStep 2887793 = 2165845) B2165845
theorem B1925195 : Blo 1923435 1925195 := bstep (se 1 (by rfl) ⟨1443896, by rfl⟩ : syracuseStep 1925195 = 2887793) B2887793
theorem B2436581 : Blo 1923435 2436581 := bbase (se 4 (by rfl) ⟨228429, by rfl⟩ : syracuseStep 2436581 = 456859) (by norm_num)
theorem B6497549 : Blo 1923435 6497549 := bstep (se 3 (by rfl) ⟨1218290, by rfl⟩ : syracuseStep 6497549 = 2436581) B2436581
theorem B4331699 : Blo 1923435 4331699 := bstep (se 1 (by rfl) ⟨3248774, by rfl⟩ : syracuseStep 4331699 = 6497549) B6497549
theorem B2887799 : Blo 1923435 2887799 := bstep (se 1 (by rfl) ⟨2165849, by rfl⟩ : syracuseStep 2887799 = 4331699) B4331699
theorem B1925199 : Blo 1923435 1925199 := bstep (se 1 (by rfl) ⟨1443899, by rfl⟩ : syracuseStep 1925199 = 2887799) B2887799
theorem B2887805 : Blo 1923435 2887805 := bbase (se 3 (by rfl) ⟨541463, by rfl⟩ : syracuseStep 2887805 = 1082927) (by norm_num)
theorem B1925203 : Blo 1923435 1925203 := bstep (se 1 (by rfl) ⟨1443902, by rfl⟩ : syracuseStep 1925203 = 2887805) B2887805
theorem B4331717 : Blo 1923435 4331717 := bbase (se 4 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 4331717 = 812197) (by norm_num)
theorem B2887811 : Blo 1923435 2887811 := bstep (se 1 (by rfl) ⟨2165858, by rfl⟩ : syracuseStep 2887811 = 4331717) B4331717
theorem B1925207 : Blo 1923435 1925207 := bstep (se 1 (by rfl) ⟨1443905, by rfl⟩ : syracuseStep 1925207 = 2887811) B2887811
theorem B9505621 : Blo 1923435 9505621 := bbase (se 9 (by rfl) ⟨27848, by rfl⟩ : syracuseStep 9505621 = 55697) (by norm_num)
theorem B12674161 : Blo 1923435 12674161 := bstep (se 2 (by rfl) ⟨4752810, by rfl⟩ : syracuseStep 12674161 = 9505621) B9505621
theorem B16898881 : Blo 1923435 16898881 := bstep (se 2 (by rfl) ⟨6337080, by rfl⟩ : syracuseStep 16898881 = 12674161) B12674161
theorem B22531841 : Blo 1923435 22531841 := bstep (se 2 (by rfl) ⟨8449440, by rfl⟩ : syracuseStep 22531841 = 16898881) B16898881
theorem B15021227 : Blo 1923435 15021227 := bstep (se 1 (by rfl) ⟨11265920, by rfl⟩ : syracuseStep 15021227 = 22531841) B22531841
theorem B40056605 : Blo 1923435 40056605 := bstep (se 3 (by rfl) ⟨7510613, by rfl⟩ : syracuseStep 40056605 = 15021227) B15021227
theorem B26704403 : Blo 1923435 26704403 := bstep (se 1 (by rfl) ⟨20028302, by rfl⟩ : syracuseStep 26704403 = 40056605) B40056605
theorem B17802935 : Blo 1923435 17802935 := bstep (se 1 (by rfl) ⟨13352201, by rfl⟩ : syracuseStep 17802935 = 26704403) B26704403
theorem B11868623 : Blo 1923435 11868623 := bstep (se 1 (by rfl) ⟨8901467, by rfl⟩ : syracuseStep 11868623 = 17802935) B17802935
theorem B7912415 : Blo 1923435 7912415 := bstep (se 1 (by rfl) ⟨5934311, by rfl⟩ : syracuseStep 7912415 = 11868623) B11868623
theorem B5274943 : Blo 1923435 5274943 := bstep (se 1 (by rfl) ⟨3956207, by rfl⟩ : syracuseStep 5274943 = 7912415) B7912415
theorem B28133029 : Blo 1923435 28133029 := bstep (se 4 (by rfl) ⟨2637471, by rfl⟩ : syracuseStep 28133029 = 5274943) B5274943
theorem B37510705 : Blo 1923435 37510705 := bstep (se 2 (by rfl) ⟨14066514, by rfl⟩ : syracuseStep 37510705 = 28133029) B28133029
theorem B50014273 : Blo 1923435 50014273 := bstep (se 2 (by rfl) ⟨18755352, by rfl⟩ : syracuseStep 50014273 = 37510705) B37510705
theorem B66685697 : Blo 1923435 66685697 := bstep (se 2 (by rfl) ⟨25007136, by rfl⟩ : syracuseStep 66685697 = 50014273) B50014273
theorem B44457131 : Blo 1923435 44457131 := bstep (se 1 (by rfl) ⟨33342848, by rfl⟩ : syracuseStep 44457131 = 66685697) B66685697
theorem B118552349 : Blo 1923435 118552349 := bstep (se 3 (by rfl) ⟨22228565, by rfl⟩ : syracuseStep 118552349 = 44457131) B44457131
theorem B79034899 : Blo 1923435 79034899 := bstep (se 1 (by rfl) ⟨59276174, by rfl⟩ : syracuseStep 79034899 = 118552349) B118552349
theorem B105379865 : Blo 1923435 105379865 := bstep (se 2 (by rfl) ⟨39517449, by rfl⟩ : syracuseStep 105379865 = 79034899) B79034899
theorem B70253243 : Blo 1923435 70253243 := bstep (se 1 (by rfl) ⟨52689932, by rfl⟩ : syracuseStep 70253243 = 105379865) B105379865
theorem B46835495 : Blo 1923435 46835495 := bstep (se 1 (by rfl) ⟨35126621, by rfl⟩ : syracuseStep 46835495 = 70253243) B70253243
theorem B31223663 : Blo 1923435 31223663 := bstep (se 1 (by rfl) ⟨23417747, by rfl⟩ : syracuseStep 31223663 = 46835495) B46835495
theorem B20815775 : Blo 1923435 20815775 := bstep (se 1 (by rfl) ⟨15611831, by rfl⟩ : syracuseStep 20815775 = 31223663) B31223663
theorem B13877183 : Blo 1923435 13877183 := bstep (se 1 (by rfl) ⟨10407887, by rfl⟩ : syracuseStep 13877183 = 20815775) B20815775
theorem B9251455 : Blo 1923435 9251455 := bstep (se 1 (by rfl) ⟨6938591, by rfl⟩ : syracuseStep 9251455 = 13877183) B13877183
theorem B12335273 : Blo 1923435 12335273 := bstep (se 2 (by rfl) ⟨4625727, by rfl⟩ : syracuseStep 12335273 = 9251455) B9251455
theorem B8223515 : Blo 1923435 8223515 := bstep (se 1 (by rfl) ⟨6167636, by rfl⟩ : syracuseStep 8223515 = 12335273) B12335273
theorem B5482343 : Blo 1923435 5482343 := bstep (se 1 (by rfl) ⟨4111757, by rfl⟩ : syracuseStep 5482343 = 8223515) B8223515
theorem B3654895 : Blo 1923435 3654895 := bstep (se 1 (by rfl) ⟨2741171, by rfl⟩ : syracuseStep 3654895 = 5482343) B5482343
theorem B4873193 : Blo 1923435 4873193 := bstep (se 2 (by rfl) ⟨1827447, by rfl⟩ : syracuseStep 4873193 = 3654895) B3654895
theorem B3248795 : Blo 1923435 3248795 := bstep (se 1 (by rfl) ⟨2436596, by rfl⟩ : syracuseStep 3248795 = 4873193) B4873193
theorem B2165863 : Blo 1923435 2165863 := bstep (se 1 (by rfl) ⟨1624397, by rfl⟩ : syracuseStep 2165863 = 3248795) B3248795
theorem B2887817 : Blo 1923435 2887817 := bstep (se 2 (by rfl) ⟨1082931, by rfl⟩ : syracuseStep 2887817 = 2165863) B2165863
theorem B1925211 : Blo 1923435 1925211 := bstep (se 1 (by rfl) ⟨1443908, by rfl⟩ : syracuseStep 1925211 = 2887817) B2887817
theorem B9746405 : Blo 1923435 9746405 := bbase (se 4 (by rfl) ⟨913725, by rfl⟩ : syracuseStep 9746405 = 1827451) (by norm_num)
theorem B6497603 : Blo 1923435 6497603 := bstep (se 1 (by rfl) ⟨4873202, by rfl⟩ : syracuseStep 6497603 = 9746405) B9746405
theorem B4331735 : Blo 1923435 4331735 := bstep (se 1 (by rfl) ⟨3248801, by rfl⟩ : syracuseStep 4331735 = 6497603) B6497603
theorem B2887823 : Blo 1923435 2887823 := bstep (se 1 (by rfl) ⟨2165867, by rfl⟩ : syracuseStep 2887823 = 4331735) B4331735
theorem B1925215 : Blo 1923435 1925215 := bstep (se 1 (by rfl) ⟨1443911, by rfl⟩ : syracuseStep 1925215 = 2887823) B2887823
theorem B2887829 : Blo 1923435 2887829 := bbase (se 6 (by rfl) ⟨67683, by rfl⟩ : syracuseStep 2887829 = 135367) (by norm_num)
theorem B1925219 : Blo 1923435 1925219 := bstep (se 1 (by rfl) ⟨1443914, by rfl⟩ : syracuseStep 1925219 = 2887829) B2887829
theorem B3083837 : Blo 1923435 3083837 := bbase (se 3 (by rfl) ⟨578219, by rfl⟩ : syracuseStep 3083837 = 1156439) (by norm_num)
theorem B8223565 : Blo 1923435 8223565 := bstep (se 3 (by rfl) ⟨1541918, by rfl⟩ : syracuseStep 8223565 = 3083837) B3083837
theorem B10964753 : Blo 1923435 10964753 := bstep (se 2 (by rfl) ⟨4111782, by rfl⟩ : syracuseStep 10964753 = 8223565) B8223565
theorem B7309835 : Blo 1923435 7309835 := bstep (se 1 (by rfl) ⟨5482376, by rfl⟩ : syracuseStep 7309835 = 10964753) B10964753
theorem B4873223 : Blo 1923435 4873223 := bstep (se 1 (by rfl) ⟨3654917, by rfl⟩ : syracuseStep 4873223 = 7309835) B7309835
theorem B3248815 : Blo 1923435 3248815 := bstep (se 1 (by rfl) ⟨2436611, by rfl⟩ : syracuseStep 3248815 = 4873223) B4873223
theorem B4331753 : Blo 1923435 4331753 := bstep (se 2 (by rfl) ⟨1624407, by rfl⟩ : syracuseStep 4331753 = 3248815) B3248815
theorem B2887835 : Blo 1923435 2887835 := bstep (se 1 (by rfl) ⟨2165876, by rfl⟩ : syracuseStep 2887835 = 4331753) B4331753
theorem B1925223 : Blo 1923435 1925223 := bstep (se 1 (by rfl) ⟨1443917, by rfl⟩ : syracuseStep 1925223 = 2887835) B2887835
theorem B2165881 : Blo 1923435 2165881 := bbase (se 2 (by rfl) ⟨812205, by rfl⟩ : syracuseStep 2165881 = 1624411) (by norm_num)
theorem B2887841 : Blo 1923435 2887841 := bstep (se 2 (by rfl) ⟨1082940, by rfl⟩ : syracuseStep 2887841 = 2165881) B2165881
theorem B1925227 : Blo 1923435 1925227 := bstep (se 1 (by rfl) ⟨1443920, by rfl⟩ : syracuseStep 1925227 = 2887841) B2887841
theorem B6586309 : Blo 1923435 6586309 := bbase (se 4 (by rfl) ⟨617466, by rfl⟩ : syracuseStep 6586309 = 1234933) (by norm_num)
theorem B8781745 : Blo 1923435 8781745 := bstep (se 2 (by rfl) ⟨3293154, by rfl⟩ : syracuseStep 8781745 = 6586309) B6586309
theorem B11708993 : Blo 1923435 11708993 := bstep (se 2 (by rfl) ⟨4390872, by rfl⟩ : syracuseStep 11708993 = 8781745) B8781745
theorem B31223981 : Blo 1923435 31223981 := bstep (se 3 (by rfl) ⟨5854496, by rfl⟩ : syracuseStep 31223981 = 11708993) B11708993
theorem B20815987 : Blo 1923435 20815987 := bstep (se 1 (by rfl) ⟨15611990, by rfl⟩ : syracuseStep 20815987 = 31223981) B31223981
theorem B27754649 : Blo 1923435 27754649 := bstep (se 2 (by rfl) ⟨10407993, by rfl⟩ : syracuseStep 27754649 = 20815987) B20815987
theorem B18503099 : Blo 1923435 18503099 := bstep (se 1 (by rfl) ⟨13877324, by rfl⟩ : syracuseStep 18503099 = 27754649) B27754649
theorem B12335399 : Blo 1923435 12335399 := bstep (se 1 (by rfl) ⟨9251549, by rfl⟩ : syracuseStep 12335399 = 18503099) B18503099
theorem B8223599 : Blo 1923435 8223599 := bstep (se 1 (by rfl) ⟨6167699, by rfl⟩ : syracuseStep 8223599 = 12335399) B12335399
theorem B5482399 : Blo 1923435 5482399 := bstep (se 1 (by rfl) ⟨4111799, by rfl⟩ : syracuseStep 5482399 = 8223599) B8223599
theorem B7309865 : Blo 1923435 7309865 := bstep (se 2 (by rfl) ⟨2741199, by rfl⟩ : syracuseStep 7309865 = 5482399) B5482399
theorem B4873243 : Blo 1923435 4873243 := bstep (se 1 (by rfl) ⟨3654932, by rfl⟩ : syracuseStep 4873243 = 7309865) B7309865
theorem B6497657 : Blo 1923435 6497657 := bstep (se 2 (by rfl) ⟨2436621, by rfl⟩ : syracuseStep 6497657 = 4873243) B4873243
theorem B4331771 : Blo 1923435 4331771 := bstep (se 1 (by rfl) ⟨3248828, by rfl⟩ : syracuseStep 4331771 = 6497657) B6497657
theorem B2887847 : Blo 1923435 2887847 := bstep (se 1 (by rfl) ⟨2165885, by rfl⟩ : syracuseStep 2887847 = 4331771) B4331771
theorem B1925231 : Blo 1923435 1925231 := bstep (se 1 (by rfl) ⟨1443923, by rfl⟩ : syracuseStep 1925231 = 2887847) B2887847
theorem B2887853 : Blo 1923435 2887853 := bbase (se 3 (by rfl) ⟨541472, by rfl⟩ : syracuseStep 2887853 = 1082945) (by norm_num)
theorem B1925235 : Blo 1923435 1925235 := bstep (se 1 (by rfl) ⟨1443926, by rfl⟩ : syracuseStep 1925235 = 2887853) B2887853
theorem B4331789 : Blo 1923435 4331789 := bbase (se 3 (by rfl) ⟨812210, by rfl⟩ : syracuseStep 4331789 = 1624421) (by norm_num)
theorem B2887859 : Blo 1923435 2887859 := bstep (se 1 (by rfl) ⟨2165894, by rfl⟩ : syracuseStep 2887859 = 4331789) B4331789
theorem B1925239 : Blo 1923435 1925239 := bstep (se 1 (by rfl) ⟨1443929, by rfl⟩ : syracuseStep 1925239 = 2887859) B2887859
theorem B2436637 : Blo 1923435 2436637 := bbase (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) (by norm_num)
theorem B3248849 : Blo 1923435 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B2165899 : Blo 1923435 2165899 := bstep (se 1 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 2165899 = 3248849) B3248849
theorem B2887865 : Blo 1923435 2887865 := bstep (se 2 (by rfl) ⟨1082949, by rfl⟩ : syracuseStep 2887865 = 2165899) B2165899
theorem B1925243 : Blo 1923435 1925243 := bstep (se 1 (by rfl) ⟨1443932, by rfl⟩ : syracuseStep 1925243 = 2887865) B2887865
theorem B4625813 : Blo 1923435 4625813 := bbase (se 6 (by rfl) ⟨108417, by rfl⟩ : syracuseStep 4625813 = 216835) (by norm_num)
theorem B3083875 : Blo 1923435 3083875 := bstep (se 1 (by rfl) ⟨2312906, by rfl⟩ : syracuseStep 3083875 = 4625813) B4625813
theorem B16447333 : Blo 1923435 16447333 := bstep (se 4 (by rfl) ⟨1541937, by rfl⟩ : syracuseStep 16447333 = 3083875) B3083875
theorem B21929777 : Blo 1923435 21929777 := bstep (se 2 (by rfl) ⟨8223666, by rfl⟩ : syracuseStep 21929777 = 16447333) B16447333
theorem B14619851 : Blo 1923435 14619851 := bstep (se 1 (by rfl) ⟨10964888, by rfl⟩ : syracuseStep 14619851 = 21929777) B21929777
theorem B9746567 : Blo 1923435 9746567 := bstep (se 1 (by rfl) ⟨7309925, by rfl⟩ : syracuseStep 9746567 = 14619851) B14619851
theorem B6497711 : Blo 1923435 6497711 := bstep (se 1 (by rfl) ⟨4873283, by rfl⟩ : syracuseStep 6497711 = 9746567) B9746567
theorem B4331807 : Blo 1923435 4331807 := bstep (se 1 (by rfl) ⟨3248855, by rfl⟩ : syracuseStep 4331807 = 6497711) B6497711
theorem B2887871 : Blo 1923435 2887871 := bstep (se 1 (by rfl) ⟨2165903, by rfl⟩ : syracuseStep 2887871 = 4331807) B4331807
theorem B1925247 : Blo 1923435 1925247 := bstep (se 1 (by rfl) ⟨1443935, by rfl⟩ : syracuseStep 1925247 = 2887871) B2887871
theorem B2887877 : Blo 1923435 2887877 := bbase (se 4 (by rfl) ⟨270738, by rfl⟩ : syracuseStep 2887877 = 541477) (by norm_num)
theorem B1925251 : Blo 1923435 1925251 := bstep (se 1 (by rfl) ⟨1443938, by rfl⟩ : syracuseStep 1925251 = 2887877) B2887877
theorem B3248869 : Blo 1923435 3248869 := bbase (se 4 (by rfl) ⟨304581, by rfl⟩ : syracuseStep 3248869 = 609163) (by norm_num)
theorem B4331825 : Blo 1923435 4331825 := bstep (se 2 (by rfl) ⟨1624434, by rfl⟩ : syracuseStep 4331825 = 3248869) B3248869
theorem B2887883 : Blo 1923435 2887883 := bstep (se 1 (by rfl) ⟨2165912, by rfl⟩ : syracuseStep 2887883 = 4331825) B4331825
theorem B1925255 : Blo 1923435 1925255 := bstep (se 1 (by rfl) ⟨1443941, by rfl⟩ : syracuseStep 1925255 = 2887883) B2887883
theorem B2165917 : Blo 1923435 2165917 := bbase (se 3 (by rfl) ⟨406109, by rfl⟩ : syracuseStep 2165917 = 812219) (by norm_num)
theorem B2887889 : Blo 1923435 2887889 := bstep (se 2 (by rfl) ⟨1082958, by rfl⟩ : syracuseStep 2887889 = 2165917) B2165917
theorem B1925259 : Blo 1923435 1925259 := bstep (se 1 (by rfl) ⟨1443944, by rfl⟩ : syracuseStep 1925259 = 2887889) B2887889
theorem B6497765 : Blo 1923435 6497765 := bbase (se 4 (by rfl) ⟨609165, by rfl⟩ : syracuseStep 6497765 = 1218331) (by norm_num)
theorem B4331843 : Blo 1923435 4331843 := bstep (se 1 (by rfl) ⟨3248882, by rfl⟩ : syracuseStep 4331843 = 6497765) B6497765
theorem B2887895 : Blo 1923435 2887895 := bstep (se 1 (by rfl) ⟨2165921, by rfl⟩ : syracuseStep 2887895 = 4331843) B4331843
theorem B1925263 : Blo 1923435 1925263 := bstep (se 1 (by rfl) ⟨1443947, by rfl⟩ : syracuseStep 1925263 = 2887895) B2887895
theorem B2887901 : Blo 1923435 2887901 := bbase (se 3 (by rfl) ⟨541481, by rfl⟩ : syracuseStep 2887901 = 1082963) (by norm_num)
theorem B1925267 : Blo 1923435 1925267 := bstep (se 1 (by rfl) ⟨1443950, by rfl⟩ : syracuseStep 1925267 = 2887901) B2887901
theorem B4331861 : Blo 1923435 4331861 := bbase (se 10 (by rfl) ⟨6345, by rfl⟩ : syracuseStep 4331861 = 12691) (by norm_num)
theorem B2887907 : Blo 1923435 2887907 := bstep (se 1 (by rfl) ⟨2165930, by rfl⟩ : syracuseStep 2887907 = 4331861) B4331861
theorem B1925271 : Blo 1923435 1925271 := bstep (se 1 (by rfl) ⟨1443953, by rfl⟩ : syracuseStep 1925271 = 2887907) B2887907
theorem B2312941 : Blo 1923435 2312941 := bbase (se 3 (by rfl) ⟨433676, by rfl⟩ : syracuseStep 2312941 = 867353) (by norm_num)
theorem B3083921 : Blo 1923435 3083921 := bstep (se 2 (by rfl) ⟨1156470, by rfl⟩ : syracuseStep 3083921 = 2312941) B2312941
theorem B2055947 : Blo 1923435 2055947 := bstep (se 1 (by rfl) ⟨1541960, by rfl⟩ : syracuseStep 2055947 = 3083921) B3083921
theorem B5482525 : Blo 1923435 5482525 := bstep (se 3 (by rfl) ⟨1027973, by rfl⟩ : syracuseStep 5482525 = 2055947) B2055947
theorem B7310033 : Blo 1923435 7310033 := bstep (se 2 (by rfl) ⟨2741262, by rfl⟩ : syracuseStep 7310033 = 5482525) B5482525
theorem B4873355 : Blo 1923435 4873355 := bstep (se 1 (by rfl) ⟨3655016, by rfl⟩ : syracuseStep 4873355 = 7310033) B7310033
theorem B3248903 : Blo 1923435 3248903 := bstep (se 1 (by rfl) ⟨2436677, by rfl⟩ : syracuseStep 3248903 = 4873355) B4873355
theorem B2165935 : Blo 1923435 2165935 := bstep (se 1 (by rfl) ⟨1624451, by rfl⟩ : syracuseStep 2165935 = 3248903) B3248903
theorem B2887913 : Blo 1923435 2887913 := bstep (se 2 (by rfl) ⟨1082967, by rfl⟩ : syracuseStep 2887913 = 2165935) B2165935
theorem B1925275 : Blo 1923435 1925275 := bstep (se 1 (by rfl) ⟨1443956, by rfl⟩ : syracuseStep 1925275 = 2887913) B2887913
theorem B3293237 : Blo 1923435 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B8781965 : Blo 1923435 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B5854643 : Blo 1923435 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B3903095 : Blo 1923435 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B2602063 : Blo 1923435 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B13877669 : Blo 1923435 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B37007117 : Blo 1923435 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B24671411 : Blo 1923435 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B16447607 : Blo 1923435 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B10965071 : Blo 1923435 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B7310047 : Blo 1923435 7310047 := bstep (se 1 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 7310047 = 10965071) B10965071
theorem B9746729 : Blo 1923435 9746729 := bstep (se 2 (by rfl) ⟨3655023, by rfl⟩ : syracuseStep 9746729 = 7310047) B7310047
theorem B6497819 : Blo 1923435 6497819 := bstep (se 1 (by rfl) ⟨4873364, by rfl⟩ : syracuseStep 6497819 = 9746729) B9746729
theorem B4331879 : Blo 1923435 4331879 := bstep (se 1 (by rfl) ⟨3248909, by rfl⟩ : syracuseStep 4331879 = 6497819) B6497819
theorem B2887919 : Blo 1923435 2887919 := bstep (se 1 (by rfl) ⟨2165939, by rfl⟩ : syracuseStep 2887919 = 4331879) B4331879
theorem B1925279 : Blo 1923435 1925279 := bstep (se 1 (by rfl) ⟨1443959, by rfl⟩ : syracuseStep 1925279 = 2887919) B2887919
theorem B2887925 : Blo 1923435 2887925 := bbase (se 5 (by rfl) ⟨135371, by rfl⟩ : syracuseStep 2887925 = 270743) (by norm_num)
theorem B1925283 : Blo 1923435 1925283 := bstep (se 1 (by rfl) ⟨1443962, by rfl⟩ : syracuseStep 1925283 = 2887925) B2887925
theorem B26346005 : Blo 1923435 26346005 := bbase (se 6 (by rfl) ⟨617484, by rfl⟩ : syracuseStep 26346005 = 1234969) (by norm_num)
theorem B17564003 : Blo 1923435 17564003 := bstep (se 1 (by rfl) ⟨13173002, by rfl⟩ : syracuseStep 17564003 = 26346005) B26346005
theorem B11709335 : Blo 1923435 11709335 := bstep (se 1 (by rfl) ⟨8782001, by rfl⟩ : syracuseStep 11709335 = 17564003) B17564003
theorem B7806223 : Blo 1923435 7806223 := bstep (se 1 (by rfl) ⟨5854667, by rfl⟩ : syracuseStep 7806223 = 11709335) B11709335
theorem B41633189 : Blo 1923435 41633189 := bstep (se 4 (by rfl) ⟨3903111, by rfl⟩ : syracuseStep 41633189 = 7806223) B7806223
theorem B27755459 : Blo 1923435 27755459 := bstep (se 1 (by rfl) ⟨20816594, by rfl⟩ : syracuseStep 27755459 = 41633189) B41633189
theorem B18503639 : Blo 1923435 18503639 := bstep (se 1 (by rfl) ⟨13877729, by rfl⟩ : syracuseStep 18503639 = 27755459) B27755459
theorem B12335759 : Blo 1923435 12335759 := bstep (se 1 (by rfl) ⟨9251819, by rfl⟩ : syracuseStep 12335759 = 18503639) B18503639
theorem B8223839 : Blo 1923435 8223839 := bstep (se 1 (by rfl) ⟨6167879, by rfl⟩ : syracuseStep 8223839 = 12335759) B12335759
theorem B5482559 : Blo 1923435 5482559 := bstep (se 1 (by rfl) ⟨4111919, by rfl⟩ : syracuseStep 5482559 = 8223839) B8223839
theorem B3655039 : Blo 1923435 3655039 := bstep (se 1 (by rfl) ⟨2741279, by rfl⟩ : syracuseStep 3655039 = 5482559) B5482559
theorem B4873385 : Blo 1923435 4873385 := bstep (se 2 (by rfl) ⟨1827519, by rfl⟩ : syracuseStep 4873385 = 3655039) B3655039
theorem B3248923 : Blo 1923435 3248923 := bstep (se 1 (by rfl) ⟨2436692, by rfl⟩ : syracuseStep 3248923 = 4873385) B4873385
theorem B4331897 : Blo 1923435 4331897 := bstep (se 2 (by rfl) ⟨1624461, by rfl⟩ : syracuseStep 4331897 = 3248923) B3248923
theorem B2887931 : Blo 1923435 2887931 := bstep (se 1 (by rfl) ⟨2165948, by rfl⟩ : syracuseStep 2887931 = 4331897) B4331897
theorem B1925287 : Blo 1923435 1925287 := bstep (se 1 (by rfl) ⟨1443965, by rfl⟩ : syracuseStep 1925287 = 2887931) B2887931
theorem B2165953 : Blo 1923435 2165953 := bbase (se 2 (by rfl) ⟨812232, by rfl⟩ : syracuseStep 2165953 = 1624465) (by norm_num)
theorem B2887937 : Blo 1923435 2887937 := bstep (se 2 (by rfl) ⟨1082976, by rfl⟩ : syracuseStep 2887937 = 2165953) B2165953
theorem B1925291 : Blo 1923435 1925291 := bstep (se 1 (by rfl) ⟨1443968, by rfl⟩ : syracuseStep 1925291 = 2887937) B2887937
theorem B4873405 : Blo 1923435 4873405 := bbase (se 3 (by rfl) ⟨913763, by rfl⟩ : syracuseStep 4873405 = 1827527) (by norm_num)
theorem B6497873 : Blo 1923435 6497873 := bstep (se 2 (by rfl) ⟨2436702, by rfl⟩ : syracuseStep 6497873 = 4873405) B4873405
theorem B4331915 : Blo 1923435 4331915 := bstep (se 1 (by rfl) ⟨3248936, by rfl⟩ : syracuseStep 4331915 = 6497873) B6497873
theorem B2887943 : Blo 1923435 2887943 := bstep (se 1 (by rfl) ⟨2165957, by rfl⟩ : syracuseStep 2887943 = 4331915) B4331915
theorem B1925295 : Blo 1923435 1925295 := bstep (se 1 (by rfl) ⟨1443971, by rfl⟩ : syracuseStep 1925295 = 2887943) B2887943
theorem B2887949 : Blo 1923435 2887949 := bbase (se 3 (by rfl) ⟨541490, by rfl⟩ : syracuseStep 2887949 = 1082981) (by norm_num)
theorem B1925299 : Blo 1923435 1925299 := bstep (se 1 (by rfl) ⟨1443974, by rfl⟩ : syracuseStep 1925299 = 2887949) B2887949
theorem B4331933 : Blo 1923435 4331933 := bbase (se 3 (by rfl) ⟨812237, by rfl⟩ : syracuseStep 4331933 = 1624475) (by norm_num)
theorem B2887955 : Blo 1923435 2887955 := bstep (se 1 (by rfl) ⟨2165966, by rfl⟩ : syracuseStep 2887955 = 4331933) B4331933
theorem B1925303 : Blo 1923435 1925303 := bstep (se 1 (by rfl) ⟨1443977, by rfl⟩ : syracuseStep 1925303 = 2887955) B2887955
theorem B3248957 : Blo 1923435 3248957 := bbase (se 3 (by rfl) ⟨609179, by rfl⟩ : syracuseStep 3248957 = 1218359) (by norm_num)
theorem B2165971 : Blo 1923435 2165971 := bstep (se 1 (by rfl) ⟨1624478, by rfl⟩ : syracuseStep 2165971 = 3248957) B3248957
theorem B2887961 : Blo 1923435 2887961 := bstep (se 2 (by rfl) ⟨1082985, by rfl⟩ : syracuseStep 2887961 = 2165971) B2165971
theorem B1925307 : Blo 1923435 1925307 := bstep (se 1 (by rfl) ⟨1443980, by rfl⟩ : syracuseStep 1925307 = 2887961) B2887961
theorem B2055985 : Blo 1923435 2055985 := bbase (se 2 (by rfl) ⟨770994, by rfl⟩ : syracuseStep 2055985 = 1541989) (by norm_num)
theorem B10965253 : Blo 1923435 10965253 := bstep (se 4 (by rfl) ⟨1027992, by rfl⟩ : syracuseStep 10965253 = 2055985) B2055985
theorem B14620337 : Blo 1923435 14620337 := bstep (se 2 (by rfl) ⟨5482626, by rfl⟩ : syracuseStep 14620337 = 10965253) B10965253
theorem B9746891 : Blo 1923435 9746891 := bstep (se 1 (by rfl) ⟨7310168, by rfl⟩ : syracuseStep 9746891 = 14620337) B14620337
theorem B6497927 : Blo 1923435 6497927 := bstep (se 1 (by rfl) ⟨4873445, by rfl⟩ : syracuseStep 6497927 = 9746891) B9746891
theorem B4331951 : Blo 1923435 4331951 := bstep (se 1 (by rfl) ⟨3248963, by rfl⟩ : syracuseStep 4331951 = 6497927) B6497927
theorem B2887967 : Blo 1923435 2887967 := bstep (se 1 (by rfl) ⟨2165975, by rfl⟩ : syracuseStep 2887967 = 4331951) B4331951
theorem B1925311 : Blo 1923435 1925311 := bstep (se 1 (by rfl) ⟨1443983, by rfl⟩ : syracuseStep 1925311 = 2887967) B2887967
theorem B2887973 : Blo 1923435 2887973 := bbase (se 4 (by rfl) ⟨270747, by rfl⟩ : syracuseStep 2887973 = 541495) (by norm_num)
theorem B1925315 : Blo 1923435 1925315 := bstep (se 1 (by rfl) ⟨1443986, by rfl⟩ : syracuseStep 1925315 = 2887973) B2887973
theorem B2436733 : Blo 1923435 2436733 := bbase (se 3 (by rfl) ⟨456887, by rfl⟩ : syracuseStep 2436733 = 913775) (by norm_num)
theorem B3248977 : Blo 1923435 3248977 := bstep (se 2 (by rfl) ⟨1218366, by rfl⟩ : syracuseStep 3248977 = 2436733) B2436733
theorem B4331969 : Blo 1923435 4331969 := bstep (se 2 (by rfl) ⟨1624488, by rfl⟩ : syracuseStep 4331969 = 3248977) B3248977
theorem B2887979 : Blo 1923435 2887979 := bstep (se 1 (by rfl) ⟨2165984, by rfl⟩ : syracuseStep 2887979 = 4331969) B4331969
theorem B1925319 : Blo 1923435 1925319 := bstep (se 1 (by rfl) ⟨1443989, by rfl⟩ : syracuseStep 1925319 = 2887979) B2887979
theorem B2165989 : Blo 1923435 2165989 := bbase (se 4 (by rfl) ⟨203061, by rfl⟩ : syracuseStep 2165989 = 406123) (by norm_num)
theorem B2887985 : Blo 1923435 2887985 := bstep (se 2 (by rfl) ⟨1082994, by rfl⟩ : syracuseStep 2887985 = 2165989) B2165989
theorem B1925323 : Blo 1923435 1925323 := bstep (se 1 (by rfl) ⟨1443992, by rfl⟩ : syracuseStep 1925323 = 2887985) B2887985
theorem B4112005 : Blo 1923435 4112005 := bbase (se 4 (by rfl) ⟨385500, by rfl⟩ : syracuseStep 4112005 = 771001) (by norm_num)
theorem B5482673 : Blo 1923435 5482673 := bstep (se 2 (by rfl) ⟨2056002, by rfl⟩ : syracuseStep 5482673 = 4112005) B4112005
theorem B3655115 : Blo 1923435 3655115 := bstep (se 1 (by rfl) ⟨2741336, by rfl⟩ : syracuseStep 3655115 = 5482673) B5482673
theorem B2436743 : Blo 1923435 2436743 := bstep (se 1 (by rfl) ⟨1827557, by rfl⟩ : syracuseStep 2436743 = 3655115) B3655115
theorem B6497981 : Blo 1923435 6497981 := bstep (se 3 (by rfl) ⟨1218371, by rfl⟩ : syracuseStep 6497981 = 2436743) B2436743
theorem B4331987 : Blo 1923435 4331987 := bstep (se 1 (by rfl) ⟨3248990, by rfl⟩ : syracuseStep 4331987 = 6497981) B6497981
theorem B2887991 : Blo 1923435 2887991 := bstep (se 1 (by rfl) ⟨2165993, by rfl⟩ : syracuseStep 2887991 = 4331987) B4331987
theorem B1925327 : Blo 1923435 1925327 := bstep (se 1 (by rfl) ⟨1443995, by rfl⟩ : syracuseStep 1925327 = 2887991) B2887991
theorem B2887997 : Blo 1923435 2887997 := bbase (se 3 (by rfl) ⟨541499, by rfl⟩ : syracuseStep 2887997 = 1082999) (by norm_num)
theorem B1925331 : Blo 1923435 1925331 := bstep (se 1 (by rfl) ⟨1443998, by rfl⟩ : syracuseStep 1925331 = 2887997) B2887997
theorem B4332005 : Blo 1923435 4332005 := bbase (se 4 (by rfl) ⟨406125, by rfl⟩ : syracuseStep 4332005 = 812251) (by norm_num)
theorem B2888003 : Blo 1923435 2888003 := bstep (se 1 (by rfl) ⟨2166002, by rfl⟩ : syracuseStep 2888003 = 4332005) B4332005
theorem B1925335 : Blo 1923435 1925335 := bstep (se 1 (by rfl) ⟨1444001, by rfl⟩ : syracuseStep 1925335 = 2888003) B2888003
theorem B4873517 : Blo 1923435 4873517 := bbase (se 3 (by rfl) ⟨913784, by rfl⟩ : syracuseStep 4873517 = 1827569) (by norm_num)
theorem B3249011 : Blo 1923435 3249011 := bstep (se 1 (by rfl) ⟨2436758, by rfl⟩ : syracuseStep 3249011 = 4873517) B4873517
theorem B2166007 : Blo 1923435 2166007 := bstep (se 1 (by rfl) ⟨1624505, by rfl⟩ : syracuseStep 2166007 = 3249011) B3249011
theorem B2888009 : Blo 1923435 2888009 := bstep (se 2 (by rfl) ⟨1083003, by rfl⟩ : syracuseStep 2888009 = 2166007) B2166007
theorem B1925339 : Blo 1923435 1925339 := bstep (se 1 (by rfl) ⟨1444004, by rfl⟩ : syracuseStep 1925339 = 2888009) B2888009
theorem B4940021 : Blo 1923435 4940021 := bbase (se 5 (by rfl) ⟨231563, by rfl⟩ : syracuseStep 4940021 = 463127) (by norm_num)
theorem B3293347 : Blo 1923435 3293347 := bstep (se 1 (by rfl) ⟨2470010, by rfl⟩ : syracuseStep 3293347 = 4940021) B4940021
theorem B4391129 : Blo 1923435 4391129 := bstep (se 2 (by rfl) ⟨1646673, by rfl⟩ : syracuseStep 4391129 = 3293347) B3293347
theorem B11709677 : Blo 1923435 11709677 := bstep (se 3 (by rfl) ⟨2195564, by rfl⟩ : syracuseStep 11709677 = 4391129) B4391129
theorem B7806451 : Blo 1923435 7806451 := bstep (se 1 (by rfl) ⟨5854838, by rfl⟩ : syracuseStep 7806451 = 11709677) B11709677
theorem B10408601 : Blo 1923435 10408601 := bstep (se 2 (by rfl) ⟨3903225, by rfl⟩ : syracuseStep 10408601 = 7806451) B7806451
theorem B6939067 : Blo 1923435 6939067 := bstep (se 1 (by rfl) ⟨5204300, by rfl⟩ : syracuseStep 6939067 = 10408601) B10408601
theorem B9252089 : Blo 1923435 9252089 := bstep (se 2 (by rfl) ⟨3469533, by rfl⟩ : syracuseStep 9252089 = 6939067) B6939067
theorem B6168059 : Blo 1923435 6168059 := bstep (se 1 (by rfl) ⟨4626044, by rfl⟩ : syracuseStep 6168059 = 9252089) B9252089
theorem B4112039 : Blo 1923435 4112039 := bstep (se 1 (by rfl) ⟨3084029, by rfl⟩ : syracuseStep 4112039 = 6168059) B6168059
theorem B2741359 : Blo 1923435 2741359 := bstep (se 1 (by rfl) ⟨2056019, by rfl⟩ : syracuseStep 2741359 = 4112039) B4112039
theorem B3655145 : Blo 1923435 3655145 := bstep (se 2 (by rfl) ⟨1370679, by rfl⟩ : syracuseStep 3655145 = 2741359) B2741359
theorem B9747053 : Blo 1923435 9747053 := bstep (se 3 (by rfl) ⟨1827572, by rfl⟩ : syracuseStep 9747053 = 3655145) B3655145
theorem B6498035 : Blo 1923435 6498035 := bstep (se 1 (by rfl) ⟨4873526, by rfl⟩ : syracuseStep 6498035 = 9747053) B9747053
theorem B4332023 : Blo 1923435 4332023 := bstep (se 1 (by rfl) ⟨3249017, by rfl⟩ : syracuseStep 4332023 = 6498035) B6498035
theorem B2888015 : Blo 1923435 2888015 := bstep (se 1 (by rfl) ⟨2166011, by rfl⟩ : syracuseStep 2888015 = 4332023) B4332023
theorem B1925343 : Blo 1923435 1925343 := bstep (se 1 (by rfl) ⟨1444007, by rfl⟩ : syracuseStep 1925343 = 2888015) B2888015
theorem B2888021 : Blo 1923435 2888021 := bbase (se 10 (by rfl) ⟨4230, by rfl⟩ : syracuseStep 2888021 = 8461) (by norm_num)
theorem B1925347 : Blo 1923435 1925347 := bstep (se 1 (by rfl) ⟨1444010, by rfl⟩ : syracuseStep 1925347 = 2888021) B2888021
theorem B5482741 : Blo 1923435 5482741 := bbase (se 5 (by rfl) ⟨257003, by rfl⟩ : syracuseStep 5482741 = 514007) (by norm_num)
theorem B7310321 : Blo 1923435 7310321 := bstep (se 2 (by rfl) ⟨2741370, by rfl⟩ : syracuseStep 7310321 = 5482741) B5482741
theorem B4873547 : Blo 1923435 4873547 := bstep (se 1 (by rfl) ⟨3655160, by rfl⟩ : syracuseStep 4873547 = 7310321) B7310321
theorem B3249031 : Blo 1923435 3249031 := bstep (se 1 (by rfl) ⟨2436773, by rfl⟩ : syracuseStep 3249031 = 4873547) B4873547
theorem B4332041 : Blo 1923435 4332041 := bstep (se 2 (by rfl) ⟨1624515, by rfl⟩ : syracuseStep 4332041 = 3249031) B3249031
theorem B2888027 : Blo 1923435 2888027 := bstep (se 1 (by rfl) ⟨2166020, by rfl⟩ : syracuseStep 2888027 = 4332041) B4332041
theorem B1925351 : Blo 1923435 1925351 := bstep (se 1 (by rfl) ⟨1444013, by rfl⟩ : syracuseStep 1925351 = 2888027) B2888027
theorem B2166025 : Blo 1923435 2166025 := bbase (se 2 (by rfl) ⟨812259, by rfl⟩ : syracuseStep 2166025 = 1624519) (by norm_num)
theorem B2888033 : Blo 1923435 2888033 := bstep (se 2 (by rfl) ⟨1083012, by rfl⟩ : syracuseStep 2888033 = 2166025) B2166025
theorem B1925355 : Blo 1923435 1925355 := bstep (se 1 (by rfl) ⟨1444016, by rfl⟩ : syracuseStep 1925355 = 2888033) B2888033
theorem B2313041 : Blo 1923435 2313041 := bbase (se 2 (by rfl) ⟨867390, by rfl⟩ : syracuseStep 2313041 = 1734781) (by norm_num)
theorem B24672437 : Blo 1923435 24672437 := bstep (se 5 (by rfl) ⟨1156520, by rfl⟩ : syracuseStep 24672437 = 2313041) B2313041
theorem B16448291 : Blo 1923435 16448291 := bstep (se 1 (by rfl) ⟨12336218, by rfl⟩ : syracuseStep 16448291 = 24672437) B24672437
theorem B10965527 : Blo 1923435 10965527 := bstep (se 1 (by rfl) ⟨8224145, by rfl⟩ : syracuseStep 10965527 = 16448291) B16448291
theorem B7310351 : Blo 1923435 7310351 := bstep (se 1 (by rfl) ⟨5482763, by rfl⟩ : syracuseStep 7310351 = 10965527) B10965527
theorem B4873567 : Blo 1923435 4873567 := bstep (se 1 (by rfl) ⟨3655175, by rfl⟩ : syracuseStep 4873567 = 7310351) B7310351
theorem B6498089 : Blo 1923435 6498089 := bstep (se 2 (by rfl) ⟨2436783, by rfl⟩ : syracuseStep 6498089 = 4873567) B4873567
theorem B4332059 : Blo 1923435 4332059 := bstep (se 1 (by rfl) ⟨3249044, by rfl⟩ : syracuseStep 4332059 = 6498089) B6498089
theorem B2888039 : Blo 1923435 2888039 := bstep (se 1 (by rfl) ⟨2166029, by rfl⟩ : syracuseStep 2888039 = 4332059) B4332059
theorem B1925359 : Blo 1923435 1925359 := bstep (se 1 (by rfl) ⟨1444019, by rfl⟩ : syracuseStep 1925359 = 2888039) B2888039
theorem B2888045 : Blo 1923435 2888045 := bbase (se 3 (by rfl) ⟨541508, by rfl⟩ : syracuseStep 2888045 = 1083017) (by norm_num)
theorem B1925363 : Blo 1923435 1925363 := bstep (se 1 (by rfl) ⟨1444022, by rfl⟩ : syracuseStep 1925363 = 2888045) B2888045
theorem B4332077 : Blo 1923435 4332077 := bbase (se 3 (by rfl) ⟨812264, by rfl⟩ : syracuseStep 4332077 = 1624529) (by norm_num)
theorem B2888051 : Blo 1923435 2888051 := bstep (se 1 (by rfl) ⟨2166038, by rfl⟩ : syracuseStep 2888051 = 4332077) B4332077
theorem B1925367 : Blo 1923435 1925367 := bstep (se 1 (by rfl) ⟨1444025, by rfl⟩ : syracuseStep 1925367 = 2888051) B2888051
theorem B7806565 : Blo 1923435 7806565 := bbase (se 4 (by rfl) ⟨731865, by rfl⟩ : syracuseStep 7806565 = 1463731) (by norm_num)
theorem B10408753 : Blo 1923435 10408753 := bstep (se 2 (by rfl) ⟨3903282, by rfl⟩ : syracuseStep 10408753 = 7806565) B7806565
theorem B13878337 : Blo 1923435 13878337 := bstep (se 2 (by rfl) ⟨5204376, by rfl⟩ : syracuseStep 13878337 = 10408753) B10408753
theorem B18504449 : Blo 1923435 18504449 := bstep (se 2 (by rfl) ⟨6939168, by rfl⟩ : syracuseStep 18504449 = 13878337) B13878337
theorem B12336299 : Blo 1923435 12336299 := bstep (se 1 (by rfl) ⟨9252224, by rfl⟩ : syracuseStep 12336299 = 18504449) B18504449
theorem B8224199 : Blo 1923435 8224199 := bstep (se 1 (by rfl) ⟨6168149, by rfl⟩ : syracuseStep 8224199 = 12336299) B12336299
theorem B5482799 : Blo 1923435 5482799 := bstep (se 1 (by rfl) ⟨4112099, by rfl⟩ : syracuseStep 5482799 = 8224199) B8224199
theorem B3655199 : Blo 1923435 3655199 := bstep (se 1 (by rfl) ⟨2741399, by rfl⟩ : syracuseStep 3655199 = 5482799) B5482799
theorem B2436799 : Blo 1923435 2436799 := bstep (se 1 (by rfl) ⟨1827599, by rfl⟩ : syracuseStep 2436799 = 3655199) B3655199
theorem B3249065 : Blo 1923435 3249065 := bstep (se 2 (by rfl) ⟨1218399, by rfl⟩ : syracuseStep 3249065 = 2436799) B2436799
theorem B2166043 : Blo 1923435 2166043 := bstep (se 1 (by rfl) ⟨1624532, by rfl⟩ : syracuseStep 2166043 = 3249065) B3249065
theorem B2888057 : Blo 1923435 2888057 := bstep (se 2 (by rfl) ⟨1083021, by rfl⟩ : syracuseStep 2888057 = 2166043) B2166043
theorem B1925371 : Blo 1923435 1925371 := bstep (se 1 (by rfl) ⟨1444028, by rfl⟩ : syracuseStep 1925371 = 2888057) B2888057
theorem B32896853 : Blo 1923435 32896853 := bbase (se 9 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 32896853 = 192755) (by norm_num)
theorem B21931235 : Blo 1923435 21931235 := bstep (se 1 (by rfl) ⟨16448426, by rfl⟩ : syracuseStep 21931235 = 32896853) B32896853
theorem B14620823 : Blo 1923435 14620823 := bstep (se 1 (by rfl) ⟨10965617, by rfl⟩ : syracuseStep 14620823 = 21931235) B21931235
theorem B9747215 : Blo 1923435 9747215 := bstep (se 1 (by rfl) ⟨7310411, by rfl⟩ : syracuseStep 9747215 = 14620823) B14620823
theorem B6498143 : Blo 1923435 6498143 := bstep (se 1 (by rfl) ⟨4873607, by rfl⟩ : syracuseStep 6498143 = 9747215) B9747215
theorem B4332095 : Blo 1923435 4332095 := bstep (se 1 (by rfl) ⟨3249071, by rfl⟩ : syracuseStep 4332095 = 6498143) B6498143
theorem B2888063 : Blo 1923435 2888063 := bstep (se 1 (by rfl) ⟨2166047, by rfl⟩ : syracuseStep 2888063 = 4332095) B4332095
theorem B1925375 : Blo 1923435 1925375 := bstep (se 1 (by rfl) ⟨1444031, by rfl⟩ : syracuseStep 1925375 = 2888063) B2888063
theorem B2888069 : Blo 1923435 2888069 := bbase (se 4 (by rfl) ⟨270756, by rfl⟩ : syracuseStep 2888069 = 541513) (by norm_num)
theorem B1925379 : Blo 1923435 1925379 := bstep (se 1 (by rfl) ⟨1444034, by rfl⟩ : syracuseStep 1925379 = 2888069) B2888069
theorem B3249085 : Blo 1923435 3249085 := bbase (se 3 (by rfl) ⟨609203, by rfl⟩ : syracuseStep 3249085 = 1218407) (by norm_num)
theorem B4332113 : Blo 1923435 4332113 := bstep (se 2 (by rfl) ⟨1624542, by rfl⟩ : syracuseStep 4332113 = 3249085) B3249085
theorem B2888075 : Blo 1923435 2888075 := bstep (se 1 (by rfl) ⟨2166056, by rfl⟩ : syracuseStep 2888075 = 4332113) B4332113
theorem B1925383 : Blo 1923435 1925383 := bstep (se 1 (by rfl) ⟨1444037, by rfl⟩ : syracuseStep 1925383 = 2888075) B2888075
theorem B2166061 : Blo 1923435 2166061 := bbase (se 3 (by rfl) ⟨406136, by rfl⟩ : syracuseStep 2166061 = 812273) (by norm_num)
theorem B2888081 : Blo 1923435 2888081 := bstep (se 2 (by rfl) ⟨1083030, by rfl⟩ : syracuseStep 2888081 = 2166061) B2166061
theorem B1925387 : Blo 1923435 1925387 := bstep (se 1 (by rfl) ⟨1444040, by rfl⟩ : syracuseStep 1925387 = 2888081) B2888081
theorem B6498197 : Blo 1923435 6498197 := bbase (se 6 (by rfl) ⟨152301, by rfl⟩ : syracuseStep 6498197 = 304603) (by norm_num)
theorem B4332131 : Blo 1923435 4332131 := bstep (se 1 (by rfl) ⟨3249098, by rfl⟩ : syracuseStep 4332131 = 6498197) B6498197
theorem B2888087 : Blo 1923435 2888087 := bstep (se 1 (by rfl) ⟨2166065, by rfl⟩ : syracuseStep 2888087 = 4332131) B4332131
theorem B1925391 : Blo 1923435 1925391 := bstep (se 1 (by rfl) ⟨1444043, by rfl⟩ : syracuseStep 1925391 = 2888087) B2888087
theorem B2888093 : Blo 1923435 2888093 := bbase (se 3 (by rfl) ⟨541517, by rfl⟩ : syracuseStep 2888093 = 1083035) (by norm_num)
theorem B1925395 : Blo 1923435 1925395 := bstep (se 1 (by rfl) ⟨1444046, by rfl⟩ : syracuseStep 1925395 = 2888093) B2888093
theorem B4332149 : Blo 1923435 4332149 := bbase (se 5 (by rfl) ⟨203069, by rfl⟩ : syracuseStep 4332149 = 406139) (by norm_num)
theorem B2888099 : Blo 1923435 2888099 := bstep (se 1 (by rfl) ⟨2166074, by rfl⟩ : syracuseStep 2888099 = 4332149) B4332149
theorem B1925399 : Blo 1923435 1925399 := bstep (se 1 (by rfl) ⟨1444049, by rfl⟩ : syracuseStep 1925399 = 2888099) B2888099
theorem B2195633 : Blo 1923435 2195633 := bbase (se 2 (by rfl) ⟨823362, by rfl⟩ : syracuseStep 2195633 = 1646725) (by norm_num)
theorem B5855021 : Blo 1923435 5855021 := bstep (se 3 (by rfl) ⟨1097816, by rfl⟩ : syracuseStep 5855021 = 2195633) B2195633
theorem B3903347 : Blo 1923435 3903347 := bstep (se 1 (by rfl) ⟨2927510, by rfl⟩ : syracuseStep 3903347 = 5855021) B5855021
theorem B10408925 : Blo 1923435 10408925 := bstep (se 3 (by rfl) ⟨1951673, by rfl⟩ : syracuseStep 10408925 = 3903347) B3903347
theorem B6939283 : Blo 1923435 6939283 := bstep (se 1 (by rfl) ⟨5204462, by rfl⟩ : syracuseStep 6939283 = 10408925) B10408925
theorem B9252377 : Blo 1923435 9252377 := bstep (se 2 (by rfl) ⟨3469641, by rfl⟩ : syracuseStep 9252377 = 6939283) B6939283
theorem B6168251 : Blo 1923435 6168251 := bstep (se 1 (by rfl) ⟨4626188, by rfl⟩ : syracuseStep 6168251 = 9252377) B9252377
theorem B16448669 : Blo 1923435 16448669 := bstep (se 3 (by rfl) ⟨3084125, by rfl⟩ : syracuseStep 16448669 = 6168251) B6168251
theorem B10965779 : Blo 1923435 10965779 := bstep (se 1 (by rfl) ⟨8224334, by rfl⟩ : syracuseStep 10965779 = 16448669) B16448669
theorem B7310519 : Blo 1923435 7310519 := bstep (se 1 (by rfl) ⟨5482889, by rfl⟩ : syracuseStep 7310519 = 10965779) B10965779
theorem B4873679 : Blo 1923435 4873679 := bstep (se 1 (by rfl) ⟨3655259, by rfl⟩ : syracuseStep 4873679 = 7310519) B7310519
theorem B3249119 : Blo 1923435 3249119 := bstep (se 1 (by rfl) ⟨2436839, by rfl⟩ : syracuseStep 3249119 = 4873679) B4873679
theorem B2166079 : Blo 1923435 2166079 := bstep (se 1 (by rfl) ⟨1624559, by rfl⟩ : syracuseStep 2166079 = 3249119) B3249119
theorem B2888105 : Blo 1923435 2888105 := bstep (se 2 (by rfl) ⟨1083039, by rfl⟩ : syracuseStep 2888105 = 2166079) B2166079
theorem B1925403 : Blo 1923435 1925403 := bstep (se 1 (by rfl) ⟨1444052, by rfl⟩ : syracuseStep 1925403 = 2888105) B2888105
theorem B7310533 : Blo 1923435 7310533 := bbase (se 4 (by rfl) ⟨685362, by rfl⟩ : syracuseStep 7310533 = 1370725) (by norm_num)
theorem B9747377 : Blo 1923435 9747377 := bstep (se 2 (by rfl) ⟨3655266, by rfl⟩ : syracuseStep 9747377 = 7310533) B7310533
theorem B6498251 : Blo 1923435 6498251 := bstep (se 1 (by rfl) ⟨4873688, by rfl⟩ : syracuseStep 6498251 = 9747377) B9747377
theorem B4332167 : Blo 1923435 4332167 := bstep (se 1 (by rfl) ⟨3249125, by rfl⟩ : syracuseStep 4332167 = 6498251) B6498251
theorem B2888111 : Blo 1923435 2888111 := bstep (se 1 (by rfl) ⟨2166083, by rfl⟩ : syracuseStep 2888111 = 4332167) B4332167
theorem B1925407 : Blo 1923435 1925407 := bstep (se 1 (by rfl) ⟨1444055, by rfl⟩ : syracuseStep 1925407 = 2888111) B2888111
theorem B2888117 : Blo 1923435 2888117 := bbase (se 5 (by rfl) ⟨135380, by rfl⟩ : syracuseStep 2888117 = 270761) (by norm_num)
theorem B1925411 : Blo 1923435 1925411 := bstep (se 1 (by rfl) ⟨1444058, by rfl⟩ : syracuseStep 1925411 = 2888117) B2888117
theorem B4873709 : Blo 1923435 4873709 := bbase (se 3 (by rfl) ⟨913820, by rfl⟩ : syracuseStep 4873709 = 1827641) (by norm_num)
theorem B3249139 : Blo 1923435 3249139 := bstep (se 1 (by rfl) ⟨2436854, by rfl⟩ : syracuseStep 3249139 = 4873709) B4873709
theorem B4332185 : Blo 1923435 4332185 := bstep (se 2 (by rfl) ⟨1624569, by rfl⟩ : syracuseStep 4332185 = 3249139) B3249139
theorem B2888123 : Blo 1923435 2888123 := bstep (se 1 (by rfl) ⟨2166092, by rfl⟩ : syracuseStep 2888123 = 4332185) B4332185
theorem B1925415 : Blo 1923435 1925415 := bstep (se 1 (by rfl) ⟨1444061, by rfl⟩ : syracuseStep 1925415 = 2888123) B2888123
theorem B2166097 : Blo 1923435 2166097 := bbase (se 2 (by rfl) ⟨812286, by rfl⟩ : syracuseStep 2166097 = 1624573) (by norm_num)
theorem B2888129 : Blo 1923435 2888129 := bstep (se 2 (by rfl) ⟨1083048, by rfl⟩ : syracuseStep 2888129 = 2166097) B2166097
theorem B1925419 : Blo 1923435 1925419 := bstep (se 1 (by rfl) ⟨1444064, by rfl⟩ : syracuseStep 1925419 = 2888129) B2888129
theorem B2056105 : Blo 1923435 2056105 := bbase (se 2 (by rfl) ⟨771039, by rfl⟩ : syracuseStep 2056105 = 1542079) (by norm_num)
theorem B2741473 : Blo 1923435 2741473 := bstep (se 2 (by rfl) ⟨1028052, by rfl⟩ : syracuseStep 2741473 = 2056105) B2056105
theorem B3655297 : Blo 1923435 3655297 := bstep (se 2 (by rfl) ⟨1370736, by rfl⟩ : syracuseStep 3655297 = 2741473) B2741473
theorem B4873729 : Blo 1923435 4873729 := bstep (se 2 (by rfl) ⟨1827648, by rfl⟩ : syracuseStep 4873729 = 3655297) B3655297
theorem B6498305 : Blo 1923435 6498305 := bstep (se 2 (by rfl) ⟨2436864, by rfl⟩ : syracuseStep 6498305 = 4873729) B4873729
theorem B4332203 : Blo 1923435 4332203 := bstep (se 1 (by rfl) ⟨3249152, by rfl⟩ : syracuseStep 4332203 = 6498305) B6498305
theorem B2888135 : Blo 1923435 2888135 := bstep (se 1 (by rfl) ⟨2166101, by rfl⟩ : syracuseStep 2888135 = 4332203) B4332203
theorem B1925423 : Blo 1923435 1925423 := bstep (se 1 (by rfl) ⟨1444067, by rfl⟩ : syracuseStep 1925423 = 2888135) B2888135
theorem B2888141 : Blo 1923435 2888141 := bbase (se 3 (by rfl) ⟨541526, by rfl⟩ : syracuseStep 2888141 = 1083053) (by norm_num)
theorem B1925427 : Blo 1923435 1925427 := bstep (se 1 (by rfl) ⟨1444070, by rfl⟩ : syracuseStep 1925427 = 2888141) B2888141
theorem B4332221 : Blo 1923435 4332221 := bbase (se 3 (by rfl) ⟨812291, by rfl⟩ : syracuseStep 4332221 = 1624583) (by norm_num)
theorem B2888147 : Blo 1923435 2888147 := bstep (se 1 (by rfl) ⟨2166110, by rfl⟩ : syracuseStep 2888147 = 4332221) B4332221
theorem B1925431 : Blo 1923435 1925431 := bstep (se 1 (by rfl) ⟨1444073, by rfl⟩ : syracuseStep 1925431 = 2888147) B2888147
theorem B3249173 : Blo 1923435 3249173 := bbase (se 6 (by rfl) ⟨76152, by rfl⟩ : syracuseStep 3249173 = 152305) (by norm_num)
theorem B2166115 : Blo 1923435 2166115 := bstep (se 1 (by rfl) ⟨1624586, by rfl⟩ : syracuseStep 2166115 = 3249173) B3249173
theorem B2888153 : Blo 1923435 2888153 := bstep (se 2 (by rfl) ⟨1083057, by rfl⟩ : syracuseStep 2888153 = 2166115) B2166115
theorem B1925435 : Blo 1923435 1925435 := bstep (se 1 (by rfl) ⟨1444076, by rfl⟩ : syracuseStep 1925435 = 2888153) B2888153
theorem C0 (j : ℕ) (h1 : 480858 ≤ j) (h2 : j ≤ 481358) : Blo 1923435 (4 * j + 3) := by
  interval_cases j
  · exact B1923435
  · exact B1923439
  · exact B1923443
  · exact B1923447
  · exact B1923451
  · exact B1923455
  · exact B1923459
  · exact B1923463
  · exact B1923467
  · exact B1923471
  · exact B1923475
  · exact B1923479
  · exact B1923483
  · exact B1923487
  · exact B1923491
  · exact B1923495
  · exact B1923499
  · exact B1923503
  · exact B1923507
  · exact B1923511
  · exact B1923515
  · exact B1923519
  · exact B1923523
  · exact B1923527
  · exact B1923531
  · exact B1923535
  · exact B1923539
  · exact B1923543
  · exact B1923547
  · exact B1923551
  · exact B1923555
  · exact B1923559
  · exact B1923563
  · exact B1923567
  · exact B1923571
  · exact B1923575
  · exact B1923579
  · exact B1923583
  · exact B1923587
  · exact B1923591
  · exact B1923595
  · exact B1923599
  · exact B1923603
  · exact B1923607
  · exact B1923611
  · exact B1923615
  · exact B1923619
  · exact B1923623
  · exact B1923627
  · exact B1923631
  · exact B1923635
  · exact B1923639
  · exact B1923643
  · exact B1923647
  · exact B1923651
  · exact B1923655
  · exact B1923659
  · exact B1923663
  · exact B1923667
  · exact B1923671
  · exact B1923675
  · exact B1923679
  · exact B1923683
  · exact B1923687
  · exact B1923691
  · exact B1923695
  · exact B1923699
  · exact B1923703
  · exact B1923707
  · exact B1923711
  · exact B1923715
  · exact B1923719
  · exact B1923723
  · exact B1923727
  · exact B1923731
  · exact B1923735
  · exact B1923739
  · exact B1923743
  · exact B1923747
  · exact B1923751
  · exact B1923755
  · exact B1923759
  · exact B1923763
  · exact B1923767
  · exact B1923771
  · exact B1923775
  · exact B1923779
  · exact B1923783
  · exact B1923787
  · exact B1923791
  · exact B1923795
  · exact B1923799
  · exact B1923803
  · exact B1923807
  · exact B1923811
  · exact B1923815
  · exact B1923819
  · exact B1923823
  · exact B1923827
  · exact B1923831
  · exact B1923835
  · exact B1923839
  · exact B1923843
  · exact B1923847
  · exact B1923851
  · exact B1923855
  · exact B1923859
  · exact B1923863
  · exact B1923867
  · exact B1923871
  · exact B1923875
  · exact B1923879
  · exact B1923883
  · exact B1923887
  · exact B1923891
  · exact B1923895
  · exact B1923899
  · exact B1923903
  · exact B1923907
  · exact B1923911
  · exact B1923915
  · exact B1923919
  · exact B1923923
  · exact B1923927
  · exact B1923931
  · exact B1923935
  · exact B1923939
  · exact B1923943
  · exact B1923947
  · exact B1923951
  · exact B1923955
  · exact B1923959
  · exact B1923963
  · exact B1923967
  · exact B1923971
  · exact B1923975
  · exact B1923979
  · exact B1923983
  · exact B1923987
  · exact B1923991
  · exact B1923995
  · exact B1923999
  · exact B1924003
  · exact B1924007
  · exact B1924011
  · exact B1924015
  · exact B1924019
  · exact B1924023
  · exact B1924027
  · exact B1924031
  · exact B1924035
  · exact B1924039
  · exact B1924043
  · exact B1924047
  · exact B1924051
  · exact B1924055
  · exact B1924059
  · exact B1924063
  · exact B1924067
  · exact B1924071
  · exact B1924075
  · exact B1924079
  · exact B1924083
  · exact B1924087
  · exact B1924091
  · exact B1924095
  · exact B1924099
  · exact B1924103
  · exact B1924107
  · exact B1924111
  · exact B1924115
  · exact B1924119
  · exact B1924123
  · exact B1924127
  · exact B1924131
  · exact B1924135
  · exact B1924139
  · exact B1924143
  · exact B1924147
  · exact B1924151
  · exact B1924155
  · exact B1924159
  · exact B1924163
  · exact B1924167
  · exact B1924171
  · exact B1924175
  · exact B1924179
  · exact B1924183
  · exact B1924187
  · exact B1924191
  · exact B1924195
  · exact B1924199
  · exact B1924203
  · exact B1924207
  · exact B1924211
  · exact B1924215
  · exact B1924219
  · exact B1924223
  · exact B1924227
  · exact B1924231
  · exact B1924235
  · exact B1924239
  · exact B1924243
  · exact B1924247
  · exact B1924251
  · exact B1924255
  · exact B1924259
  · exact B1924263
  · exact B1924267
  · exact B1924271
  · exact B1924275
  · exact B1924279
  · exact B1924283
  · exact B1924287
  · exact B1924291
  · exact B1924295
  · exact B1924299
  · exact B1924303
  · exact B1924307
  · exact B1924311
  · exact B1924315
  · exact B1924319
  · exact B1924323
  · exact B1924327
  · exact B1924331
  · exact B1924335
  · exact B1924339
  · exact B1924343
  · exact B1924347
  · exact B1924351
  · exact B1924355
  · exact B1924359
  · exact B1924363
  · exact B1924367
  · exact B1924371
  · exact B1924375
  · exact B1924379
  · exact B1924383
  · exact B1924387
  · exact B1924391
  · exact B1924395
  · exact B1924399
  · exact B1924403
  · exact B1924407
  · exact B1924411
  · exact B1924415
  · exact B1924419
  · exact B1924423
  · exact B1924427
  · exact B1924431
  · exact B1924435
  · exact B1924439
  · exact B1924443
  · exact B1924447
  · exact B1924451
  · exact B1924455
  · exact B1924459
  · exact B1924463
  · exact B1924467
  · exact B1924471
  · exact B1924475
  · exact B1924479
  · exact B1924483
  · exact B1924487
  · exact B1924491
  · exact B1924495
  · exact B1924499
  · exact B1924503
  · exact B1924507
  · exact B1924511
  · exact B1924515
  · exact B1924519
  · exact B1924523
  · exact B1924527
  · exact B1924531
  · exact B1924535
  · exact B1924539
  · exact B1924543
  · exact B1924547
  · exact B1924551
  · exact B1924555
  · exact B1924559
  · exact B1924563
  · exact B1924567
  · exact B1924571
  · exact B1924575
  · exact B1924579
  · exact B1924583
  · exact B1924587
  · exact B1924591
  · exact B1924595
  · exact B1924599
  · exact B1924603
  · exact B1924607
  · exact B1924611
  · exact B1924615
  · exact B1924619
  · exact B1924623
  · exact B1924627
  · exact B1924631
  · exact B1924635
  · exact B1924639
  · exact B1924643
  · exact B1924647
  · exact B1924651
  · exact B1924655
  · exact B1924659
  · exact B1924663
  · exact B1924667
  · exact B1924671
  · exact B1924675
  · exact B1924679
  · exact B1924683
  · exact B1924687
  · exact B1924691
  · exact B1924695
  · exact B1924699
  · exact B1924703
  · exact B1924707
  · exact B1924711
  · exact B1924715
  · exact B1924719
  · exact B1924723
  · exact B1924727
  · exact B1924731
  · exact B1924735
  · exact B1924739
  · exact B1924743
  · exact B1924747
  · exact B1924751
  · exact B1924755
  · exact B1924759
  · exact B1924763
  · exact B1924767
  · exact B1924771
  · exact B1924775
  · exact B1924779
  · exact B1924783
  · exact B1924787
  · exact B1924791
  · exact B1924795
  · exact B1924799
  · exact B1924803
  · exact B1924807
  · exact B1924811
  · exact B1924815
  · exact B1924819
  · exact B1924823
  · exact B1924827
  · exact B1924831
  · exact B1924835
  · exact B1924839
  · exact B1924843
  · exact B1924847
  · exact B1924851
  · exact B1924855
  · exact B1924859
  · exact B1924863
  · exact B1924867
  · exact B1924871
  · exact B1924875
  · exact B1924879
  · exact B1924883
  · exact B1924887
  · exact B1924891
  · exact B1924895
  · exact B1924899
  · exact B1924903
  · exact B1924907
  · exact B1924911
  · exact B1924915
  · exact B1924919
  · exact B1924923
  · exact B1924927
  · exact B1924931
  · exact B1924935
  · exact B1924939
  · exact B1924943
  · exact B1924947
  · exact B1924951
  · exact B1924955
  · exact B1924959
  · exact B1924963
  · exact B1924967
  · exact B1924971
  · exact B1924975
  · exact B1924979
  · exact B1924983
  · exact B1924987
  · exact B1924991
  · exact B1924995
  · exact B1924999
  · exact B1925003
  · exact B1925007
  · exact B1925011
  · exact B1925015
  · exact B1925019
  · exact B1925023
  · exact B1925027
  · exact B1925031
  · exact B1925035
  · exact B1925039
  · exact B1925043
  · exact B1925047
  · exact B1925051
  · exact B1925055
  · exact B1925059
  · exact B1925063
  · exact B1925067
  · exact B1925071
  · exact B1925075
  · exact B1925079
  · exact B1925083
  · exact B1925087
  · exact B1925091
  · exact B1925095
  · exact B1925099
  · exact B1925103
  · exact B1925107
  · exact B1925111
  · exact B1925115
  · exact B1925119
  · exact B1925123
  · exact B1925127
  · exact B1925131
  · exact B1925135
  · exact B1925139
  · exact B1925143
  · exact B1925147
  · exact B1925151
  · exact B1925155
  · exact B1925159
  · exact B1925163
  · exact B1925167
  · exact B1925171
  · exact B1925175
  · exact B1925179
  · exact B1925183
  · exact B1925187
  · exact B1925191
  · exact B1925195
  · exact B1925199
  · exact B1925203
  · exact B1925207
  · exact B1925211
  · exact B1925215
  · exact B1925219
  · exact B1925223
  · exact B1925227
  · exact B1925231
  · exact B1925235
  · exact B1925239
  · exact B1925243
  · exact B1925247
  · exact B1925251
  · exact B1925255
  · exact B1925259
  · exact B1925263
  · exact B1925267
  · exact B1925271
  · exact B1925275
  · exact B1925279
  · exact B1925283
  · exact B1925287
  · exact B1925291
  · exact B1925295
  · exact B1925299
  · exact B1925303
  · exact B1925307
  · exact B1925311
  · exact B1925315
  · exact B1925319
  · exact B1925323
  · exact B1925327
  · exact B1925331
  · exact B1925335
  · exact B1925339
  · exact B1925343
  · exact B1925347
  · exact B1925351
  · exact B1925355
  · exact B1925359
  · exact B1925363
  · exact B1925367
  · exact B1925371
  · exact B1925375
  · exact B1925379
  · exact B1925383
  · exact B1925387
  · exact B1925391
  · exact B1925395
  · exact B1925399
  · exact B1925403
  · exact B1925407
  · exact B1925411
  · exact B1925415
  · exact B1925419
  · exact B1925423
  · exact B1925427
  · exact B1925431
  · exact B1925435
theorem solution (m : ℕ) (hlo : 1923435 ≤ m) (hhi : m ≤ 1925435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 480858 ≤ j := by omega
    have hj2 : j ≤ 481358 := by omega
    have hb : Blo 1923435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
