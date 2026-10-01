-- Prove2me | solution 1 for syracuse_descends_range_2025435_2027435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:56.372045+00:00
-- url     : https://prove2.me/submissions/38cb3cc1-f1d2-4796-8812-9d01a144ecce

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

theorem B5126885 : Blo 2025435 5126885 := bbase (se 4 (by rfl) ⟨480645, by rfl⟩ : syracuseStep 5126885 = 961291) (by norm_num)
theorem B3417923 : Blo 2025435 3417923 := bstep (se 1 (by rfl) ⟨2563442, by rfl⟩ : syracuseStep 3417923 = 5126885) B5126885
theorem B2278615 : Blo 2025435 2278615 := bstep (se 1 (by rfl) ⟨1708961, by rfl⟩ : syracuseStep 2278615 = 3417923) B3417923
theorem B3038153 : Blo 2025435 3038153 := bstep (se 2 (by rfl) ⟨1139307, by rfl⟩ : syracuseStep 3038153 = 2278615) B2278615
theorem B2025435 : Blo 2025435 2025435 := bstep (se 1 (by rfl) ⟨1519076, by rfl⟩ : syracuseStep 2025435 = 3038153) B3038153
theorem B2162909 : Blo 2025435 2162909 := bbase (se 3 (by rfl) ⟨405545, by rfl⟩ : syracuseStep 2162909 = 811091) (by norm_num)
theorem B5767757 : Blo 2025435 5767757 := bstep (se 3 (by rfl) ⟨1081454, by rfl⟩ : syracuseStep 5767757 = 2162909) B2162909
theorem B3845171 : Blo 2025435 3845171 := bstep (se 1 (by rfl) ⟨2883878, by rfl⟩ : syracuseStep 3845171 = 5767757) B5767757
theorem B10253789 : Blo 2025435 10253789 := bstep (se 3 (by rfl) ⟨1922585, by rfl⟩ : syracuseStep 10253789 = 3845171) B3845171
theorem B6835859 : Blo 2025435 6835859 := bstep (se 1 (by rfl) ⟨5126894, by rfl⟩ : syracuseStep 6835859 = 10253789) B10253789
theorem B4557239 : Blo 2025435 4557239 := bstep (se 1 (by rfl) ⟨3417929, by rfl⟩ : syracuseStep 4557239 = 6835859) B6835859
theorem B3038159 : Blo 2025435 3038159 := bstep (se 1 (by rfl) ⟨2278619, by rfl⟩ : syracuseStep 3038159 = 4557239) B4557239
theorem B2025439 : Blo 2025435 2025439 := bstep (se 1 (by rfl) ⟨1519079, by rfl⟩ : syracuseStep 2025439 = 3038159) B3038159
theorem B3038165 : Blo 2025435 3038165 := bbase (se 7 (by rfl) ⟨35603, by rfl⟩ : syracuseStep 3038165 = 71207) (by norm_num)
theorem B2025443 : Blo 2025435 2025443 := bstep (se 1 (by rfl) ⟨1519082, by rfl⟩ : syracuseStep 2025443 = 3038165) B3038165
theorem B7690373 : Blo 2025435 7690373 := bbase (se 4 (by rfl) ⟨720972, by rfl⟩ : syracuseStep 7690373 = 1441945) (by norm_num)
theorem B5126915 : Blo 2025435 5126915 := bstep (se 1 (by rfl) ⟨3845186, by rfl⟩ : syracuseStep 5126915 = 7690373) B7690373
theorem B3417943 : Blo 2025435 3417943 := bstep (se 1 (by rfl) ⟨2563457, by rfl⟩ : syracuseStep 3417943 = 5126915) B5126915
theorem B4557257 : Blo 2025435 4557257 := bstep (se 2 (by rfl) ⟨1708971, by rfl⟩ : syracuseStep 4557257 = 3417943) B3417943
theorem B3038171 : Blo 2025435 3038171 := bstep (se 1 (by rfl) ⟨2278628, by rfl⟩ : syracuseStep 3038171 = 4557257) B4557257
theorem B2025447 : Blo 2025435 2025447 := bstep (se 1 (by rfl) ⟨1519085, by rfl⟩ : syracuseStep 2025447 = 3038171) B3038171
theorem B2278633 : Blo 2025435 2278633 := bbase (se 2 (by rfl) ⟨854487, by rfl⟩ : syracuseStep 2278633 = 1708975) (by norm_num)
theorem B3038177 : Blo 2025435 3038177 := bstep (se 2 (by rfl) ⟨1139316, by rfl⟩ : syracuseStep 3038177 = 2278633) B2278633
theorem B2025451 : Blo 2025435 2025451 := bstep (se 1 (by rfl) ⟨1519088, by rfl⟩ : syracuseStep 2025451 = 3038177) B3038177
theorem B11535605 : Blo 2025435 11535605 := bbase (se 5 (by rfl) ⟨540731, by rfl⟩ : syracuseStep 11535605 = 1081463) (by norm_num)
theorem B7690403 : Blo 2025435 7690403 := bstep (se 1 (by rfl) ⟨5767802, by rfl⟩ : syracuseStep 7690403 = 11535605) B11535605
theorem B5126935 : Blo 2025435 5126935 := bstep (se 1 (by rfl) ⟨3845201, by rfl⟩ : syracuseStep 5126935 = 7690403) B7690403
theorem B6835913 : Blo 2025435 6835913 := bstep (se 2 (by rfl) ⟨2563467, by rfl⟩ : syracuseStep 6835913 = 5126935) B5126935
theorem B4557275 : Blo 2025435 4557275 := bstep (se 1 (by rfl) ⟨3417956, by rfl⟩ : syracuseStep 4557275 = 6835913) B6835913
theorem B3038183 : Blo 2025435 3038183 := bstep (se 1 (by rfl) ⟨2278637, by rfl⟩ : syracuseStep 3038183 = 4557275) B4557275
theorem B2025455 : Blo 2025435 2025455 := bstep (se 1 (by rfl) ⟨1519091, by rfl⟩ : syracuseStep 2025455 = 3038183) B3038183
theorem B3038189 : Blo 2025435 3038189 := bbase (se 3 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 3038189 = 1139321) (by norm_num)
theorem B2025459 : Blo 2025435 2025459 := bstep (se 1 (by rfl) ⟨1519094, by rfl⟩ : syracuseStep 2025459 = 3038189) B3038189
theorem B4557293 : Blo 2025435 4557293 := bbase (se 3 (by rfl) ⟨854492, by rfl⟩ : syracuseStep 4557293 = 1708985) (by norm_num)
theorem B3038195 : Blo 2025435 3038195 := bstep (se 1 (by rfl) ⟨2278646, by rfl⟩ : syracuseStep 3038195 = 4557293) B4557293
theorem B2025463 : Blo 2025435 2025463 := bstep (se 1 (by rfl) ⟨1519097, by rfl⟩ : syracuseStep 2025463 = 3038195) B3038195
theorem B4384901 : Blo 2025435 4384901 := bbase (se 4 (by rfl) ⟨411084, by rfl⟩ : syracuseStep 4384901 = 822169) (by norm_num)
theorem B11693069 : Blo 2025435 11693069 := bstep (se 3 (by rfl) ⟨2192450, by rfl⟩ : syracuseStep 11693069 = 4384901) B4384901
theorem B7795379 : Blo 2025435 7795379 := bstep (se 1 (by rfl) ⟨5846534, by rfl⟩ : syracuseStep 7795379 = 11693069) B11693069
theorem B20787677 : Blo 2025435 20787677 := bstep (se 3 (by rfl) ⟨3897689, by rfl⟩ : syracuseStep 20787677 = 7795379) B7795379
theorem B13858451 : Blo 2025435 13858451 := bstep (se 1 (by rfl) ⟨10393838, by rfl⟩ : syracuseStep 13858451 = 20787677) B20787677
theorem B9238967 : Blo 2025435 9238967 := bstep (se 1 (by rfl) ⟨6929225, by rfl⟩ : syracuseStep 9238967 = 13858451) B13858451
theorem B6159311 : Blo 2025435 6159311 := bstep (se 1 (by rfl) ⟨4619483, by rfl⟩ : syracuseStep 6159311 = 9238967) B9238967
theorem B4106207 : Blo 2025435 4106207 := bstep (se 1 (by rfl) ⟨3079655, by rfl⟩ : syracuseStep 4106207 = 6159311) B6159311
theorem B2737471 : Blo 2025435 2737471 := bstep (se 1 (by rfl) ⟨2053103, by rfl⟩ : syracuseStep 2737471 = 4106207) B4106207
theorem B3649961 : Blo 2025435 3649961 := bstep (se 2 (by rfl) ⟨1368735, by rfl⟩ : syracuseStep 3649961 = 2737471) B2737471
theorem B9733229 : Blo 2025435 9733229 := bstep (se 3 (by rfl) ⟨1824980, by rfl⟩ : syracuseStep 9733229 = 3649961) B3649961
theorem B6488819 : Blo 2025435 6488819 := bstep (se 1 (by rfl) ⟨4866614, by rfl⟩ : syracuseStep 6488819 = 9733229) B9733229
theorem B4325879 : Blo 2025435 4325879 := bstep (se 1 (by rfl) ⟨3244409, by rfl⟩ : syracuseStep 4325879 = 6488819) B6488819
theorem B2883919 : Blo 2025435 2883919 := bstep (se 1 (by rfl) ⟨2162939, by rfl⟩ : syracuseStep 2883919 = 4325879) B4325879
theorem B3845225 : Blo 2025435 3845225 := bstep (se 2 (by rfl) ⟨1441959, by rfl⟩ : syracuseStep 3845225 = 2883919) B2883919
theorem B2563483 : Blo 2025435 2563483 := bstep (se 1 (by rfl) ⟨1922612, by rfl⟩ : syracuseStep 2563483 = 3845225) B3845225
theorem B3417977 : Blo 2025435 3417977 := bstep (se 2 (by rfl) ⟨1281741, by rfl⟩ : syracuseStep 3417977 = 2563483) B2563483
theorem B2278651 : Blo 2025435 2278651 := bstep (se 1 (by rfl) ⟨1708988, by rfl⟩ : syracuseStep 2278651 = 3417977) B3417977
theorem B3038201 : Blo 2025435 3038201 := bstep (se 2 (by rfl) ⟨1139325, by rfl⟩ : syracuseStep 3038201 = 2278651) B2278651
theorem B2025467 : Blo 2025435 2025467 := bstep (se 1 (by rfl) ⟨1519100, by rfl⟩ : syracuseStep 2025467 = 3038201) B3038201
theorem B5196925 : Blo 2025435 5196925 := bbase (se 3 (by rfl) ⟨974423, by rfl⟩ : syracuseStep 5196925 = 1948847) (by norm_num)
theorem B6929233 : Blo 2025435 6929233 := bstep (se 2 (by rfl) ⟨2598462, by rfl⟩ : syracuseStep 6929233 = 5196925) B5196925
theorem B36955909 : Blo 2025435 36955909 := bstep (se 4 (by rfl) ⟨3464616, by rfl⟩ : syracuseStep 36955909 = 6929233) B6929233
theorem B197098181 : Blo 2025435 197098181 := bstep (se 4 (by rfl) ⟨18477954, by rfl⟩ : syracuseStep 197098181 = 36955909) B36955909
theorem B131398787 : Blo 2025435 131398787 := bstep (se 1 (by rfl) ⟨98549090, by rfl⟩ : syracuseStep 131398787 = 197098181) B197098181
theorem B87599191 : Blo 2025435 87599191 := bstep (se 1 (by rfl) ⟨65699393, by rfl⟩ : syracuseStep 87599191 = 131398787) B131398787
theorem B116798921 : Blo 2025435 116798921 := bstep (se 2 (by rfl) ⟨43799595, by rfl⟩ : syracuseStep 116798921 = 87599191) B87599191
theorem B77865947 : Blo 2025435 77865947 := bstep (se 1 (by rfl) ⟨58399460, by rfl⟩ : syracuseStep 77865947 = 116798921) B116798921
theorem B51910631 : Blo 2025435 51910631 := bstep (se 1 (by rfl) ⟨38932973, by rfl⟩ : syracuseStep 51910631 = 77865947) B77865947
theorem B34607087 : Blo 2025435 34607087 := bstep (se 1 (by rfl) ⟨25955315, by rfl⟩ : syracuseStep 34607087 = 51910631) B51910631
theorem B23071391 : Blo 2025435 23071391 := bstep (se 1 (by rfl) ⟨17303543, by rfl⟩ : syracuseStep 23071391 = 34607087) B34607087
theorem B15380927 : Blo 2025435 15380927 := bstep (se 1 (by rfl) ⟨11535695, by rfl⟩ : syracuseStep 15380927 = 23071391) B23071391
theorem B10253951 : Blo 2025435 10253951 := bstep (se 1 (by rfl) ⟨7690463, by rfl⟩ : syracuseStep 10253951 = 15380927) B15380927
theorem B6835967 : Blo 2025435 6835967 := bstep (se 1 (by rfl) ⟨5126975, by rfl⟩ : syracuseStep 6835967 = 10253951) B10253951
theorem B4557311 : Blo 2025435 4557311 := bstep (se 1 (by rfl) ⟨3417983, by rfl⟩ : syracuseStep 4557311 = 6835967) B6835967
theorem B3038207 : Blo 2025435 3038207 := bstep (se 1 (by rfl) ⟨2278655, by rfl⟩ : syracuseStep 3038207 = 4557311) B4557311
theorem B2025471 : Blo 2025435 2025471 := bstep (se 1 (by rfl) ⟨1519103, by rfl⟩ : syracuseStep 2025471 = 3038207) B3038207
theorem B3038213 : Blo 2025435 3038213 := bbase (se 4 (by rfl) ⟨284832, by rfl⟩ : syracuseStep 3038213 = 569665) (by norm_num)
theorem B2025475 : Blo 2025435 2025475 := bstep (se 1 (by rfl) ⟨1519106, by rfl⟩ : syracuseStep 2025475 = 3038213) B3038213
theorem B3417997 : Blo 2025435 3417997 := bbase (se 3 (by rfl) ⟨640874, by rfl⟩ : syracuseStep 3417997 = 1281749) (by norm_num)
theorem B4557329 : Blo 2025435 4557329 := bstep (se 2 (by rfl) ⟨1708998, by rfl⟩ : syracuseStep 4557329 = 3417997) B3417997
theorem B3038219 : Blo 2025435 3038219 := bstep (se 1 (by rfl) ⟨2278664, by rfl⟩ : syracuseStep 3038219 = 4557329) B4557329
theorem B2025479 : Blo 2025435 2025479 := bstep (se 1 (by rfl) ⟨1519109, by rfl⟩ : syracuseStep 2025479 = 3038219) B3038219
theorem B2278669 : Blo 2025435 2278669 := bbase (se 3 (by rfl) ⟨427250, by rfl⟩ : syracuseStep 2278669 = 854501) (by norm_num)
theorem B3038225 : Blo 2025435 3038225 := bstep (se 2 (by rfl) ⟨1139334, by rfl⟩ : syracuseStep 3038225 = 2278669) B2278669
theorem B2025483 : Blo 2025435 2025483 := bstep (se 1 (by rfl) ⟨1519112, by rfl⟩ : syracuseStep 2025483 = 3038225) B3038225
theorem B6836021 : Blo 2025435 6836021 := bbase (se 5 (by rfl) ⟨320438, by rfl⟩ : syracuseStep 6836021 = 640877) (by norm_num)
theorem B4557347 : Blo 2025435 4557347 := bstep (se 1 (by rfl) ⟨3418010, by rfl⟩ : syracuseStep 4557347 = 6836021) B6836021
theorem B3038231 : Blo 2025435 3038231 := bstep (se 1 (by rfl) ⟨2278673, by rfl⟩ : syracuseStep 3038231 = 4557347) B4557347
theorem B2025487 : Blo 2025435 2025487 := bstep (se 1 (by rfl) ⟨1519115, by rfl⟩ : syracuseStep 2025487 = 3038231) B3038231
theorem B3038237 : Blo 2025435 3038237 := bbase (se 3 (by rfl) ⟨569669, by rfl⟩ : syracuseStep 3038237 = 1139339) (by norm_num)
theorem B2025491 : Blo 2025435 2025491 := bstep (se 1 (by rfl) ⟨1519118, by rfl⟩ : syracuseStep 2025491 = 3038237) B3038237
theorem B4557365 : Blo 2025435 4557365 := bbase (se 5 (by rfl) ⟨213626, by rfl⟩ : syracuseStep 4557365 = 427253) (by norm_num)
theorem B3038243 : Blo 2025435 3038243 := bstep (se 1 (by rfl) ⟨2278682, by rfl⟩ : syracuseStep 3038243 = 4557365) B4557365
theorem B2025495 : Blo 2025435 2025495 := bstep (se 1 (by rfl) ⟨1519121, by rfl⟩ : syracuseStep 2025495 = 3038243) B3038243
theorem B8651893 : Blo 2025435 8651893 := bbase (se 5 (by rfl) ⟨405557, by rfl⟩ : syracuseStep 8651893 = 811115) (by norm_num)
theorem B11535857 : Blo 2025435 11535857 := bstep (se 2 (by rfl) ⟨4325946, by rfl⟩ : syracuseStep 11535857 = 8651893) B8651893
theorem B7690571 : Blo 2025435 7690571 := bstep (se 1 (by rfl) ⟨5767928, by rfl⟩ : syracuseStep 7690571 = 11535857) B11535857
theorem B5127047 : Blo 2025435 5127047 := bstep (se 1 (by rfl) ⟨3845285, by rfl⟩ : syracuseStep 5127047 = 7690571) B7690571
theorem B3418031 : Blo 2025435 3418031 := bstep (se 1 (by rfl) ⟨2563523, by rfl⟩ : syracuseStep 3418031 = 5127047) B5127047
theorem B2278687 : Blo 2025435 2278687 := bstep (se 1 (by rfl) ⟨1709015, by rfl⟩ : syracuseStep 2278687 = 3418031) B3418031
theorem B3038249 : Blo 2025435 3038249 := bstep (se 2 (by rfl) ⟨1139343, by rfl⟩ : syracuseStep 3038249 = 2278687) B2278687
theorem B2025499 : Blo 2025435 2025499 := bstep (se 1 (by rfl) ⟨1519124, by rfl⟩ : syracuseStep 2025499 = 3038249) B3038249
theorem B8651909 : Blo 2025435 8651909 := bbase (se 4 (by rfl) ⟨811116, by rfl⟩ : syracuseStep 8651909 = 1622233) (by norm_num)
theorem B5767939 : Blo 2025435 5767939 := bstep (se 1 (by rfl) ⟨4325954, by rfl⟩ : syracuseStep 5767939 = 8651909) B8651909
theorem B7690585 : Blo 2025435 7690585 := bstep (se 2 (by rfl) ⟨2883969, by rfl⟩ : syracuseStep 7690585 = 5767939) B5767939
theorem B10254113 : Blo 2025435 10254113 := bstep (se 2 (by rfl) ⟨3845292, by rfl⟩ : syracuseStep 10254113 = 7690585) B7690585
theorem B6836075 : Blo 2025435 6836075 := bstep (se 1 (by rfl) ⟨5127056, by rfl⟩ : syracuseStep 6836075 = 10254113) B10254113
theorem B4557383 : Blo 2025435 4557383 := bstep (se 1 (by rfl) ⟨3418037, by rfl⟩ : syracuseStep 4557383 = 6836075) B6836075
theorem B3038255 : Blo 2025435 3038255 := bstep (se 1 (by rfl) ⟨2278691, by rfl⟩ : syracuseStep 3038255 = 4557383) B4557383
theorem B2025503 : Blo 2025435 2025503 := bstep (se 1 (by rfl) ⟨1519127, by rfl⟩ : syracuseStep 2025503 = 3038255) B3038255
theorem B3038261 : Blo 2025435 3038261 := bbase (se 5 (by rfl) ⟨142418, by rfl⟩ : syracuseStep 3038261 = 284837) (by norm_num)
theorem B2025507 : Blo 2025435 2025507 := bstep (se 1 (by rfl) ⟨1519130, by rfl⟩ : syracuseStep 2025507 = 3038261) B3038261
theorem B5127077 : Blo 2025435 5127077 := bbase (se 4 (by rfl) ⟨480663, by rfl⟩ : syracuseStep 5127077 = 961327) (by norm_num)
theorem B3418051 : Blo 2025435 3418051 := bstep (se 1 (by rfl) ⟨2563538, by rfl⟩ : syracuseStep 3418051 = 5127077) B5127077
theorem B4557401 : Blo 2025435 4557401 := bstep (se 2 (by rfl) ⟨1709025, by rfl⟩ : syracuseStep 4557401 = 3418051) B3418051
theorem B3038267 : Blo 2025435 3038267 := bstep (se 1 (by rfl) ⟨2278700, by rfl⟩ : syracuseStep 3038267 = 4557401) B4557401
theorem B2025511 : Blo 2025435 2025511 := bstep (se 1 (by rfl) ⟨1519133, by rfl⟩ : syracuseStep 2025511 = 3038267) B3038267
theorem B2278705 : Blo 2025435 2278705 := bbase (se 2 (by rfl) ⟨854514, by rfl⟩ : syracuseStep 2278705 = 1709029) (by norm_num)
theorem B3038273 : Blo 2025435 3038273 := bstep (se 2 (by rfl) ⟨1139352, by rfl⟩ : syracuseStep 3038273 = 2278705) B2278705
theorem B2025515 : Blo 2025435 2025515 := bstep (se 1 (by rfl) ⟨1519136, by rfl⟩ : syracuseStep 2025515 = 3038273) B3038273
theorem B4325989 : Blo 2025435 4325989 := bbase (se 4 (by rfl) ⟨405561, by rfl⟩ : syracuseStep 4325989 = 811123) (by norm_num)
theorem B5767985 : Blo 2025435 5767985 := bstep (se 2 (by rfl) ⟨2162994, by rfl⟩ : syracuseStep 5767985 = 4325989) B4325989
theorem B3845323 : Blo 2025435 3845323 := bstep (se 1 (by rfl) ⟨2883992, by rfl⟩ : syracuseStep 3845323 = 5767985) B5767985
theorem B5127097 : Blo 2025435 5127097 := bstep (se 2 (by rfl) ⟨1922661, by rfl⟩ : syracuseStep 5127097 = 3845323) B3845323
theorem B6836129 : Blo 2025435 6836129 := bstep (se 2 (by rfl) ⟨2563548, by rfl⟩ : syracuseStep 6836129 = 5127097) B5127097
theorem B4557419 : Blo 2025435 4557419 := bstep (se 1 (by rfl) ⟨3418064, by rfl⟩ : syracuseStep 4557419 = 6836129) B6836129
theorem B3038279 : Blo 2025435 3038279 := bstep (se 1 (by rfl) ⟨2278709, by rfl⟩ : syracuseStep 3038279 = 4557419) B4557419
theorem B2025519 : Blo 2025435 2025519 := bstep (se 1 (by rfl) ⟨1519139, by rfl⟩ : syracuseStep 2025519 = 3038279) B3038279
theorem B3038285 : Blo 2025435 3038285 := bbase (se 3 (by rfl) ⟨569678, by rfl⟩ : syracuseStep 3038285 = 1139357) (by norm_num)
theorem B2025523 : Blo 2025435 2025523 := bstep (se 1 (by rfl) ⟨1519142, by rfl⟩ : syracuseStep 2025523 = 3038285) B3038285
theorem B4557437 : Blo 2025435 4557437 := bbase (se 3 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 4557437 = 1709039) (by norm_num)
theorem B3038291 : Blo 2025435 3038291 := bstep (se 1 (by rfl) ⟨2278718, by rfl⟩ : syracuseStep 3038291 = 4557437) B4557437
theorem B2025527 : Blo 2025435 2025527 := bstep (se 1 (by rfl) ⟨1519145, by rfl⟩ : syracuseStep 2025527 = 3038291) B3038291
theorem B3418085 : Blo 2025435 3418085 := bbase (se 4 (by rfl) ⟨320445, by rfl⟩ : syracuseStep 3418085 = 640891) (by norm_num)
theorem B2278723 : Blo 2025435 2278723 := bstep (se 1 (by rfl) ⟨1709042, by rfl⟩ : syracuseStep 2278723 = 3418085) B3418085
theorem B3038297 : Blo 2025435 3038297 := bstep (se 2 (by rfl) ⟨1139361, by rfl⟩ : syracuseStep 3038297 = 2278723) B2278723
theorem B2025531 : Blo 2025435 2025531 := bstep (se 1 (by rfl) ⟨1519148, by rfl⟩ : syracuseStep 2025531 = 3038297) B3038297
theorem B7300165 : Blo 2025435 7300165 := bbase (se 4 (by rfl) ⟨684390, by rfl⟩ : syracuseStep 7300165 = 1368781) (by norm_num)
theorem B9733553 : Blo 2025435 9733553 := bstep (se 2 (by rfl) ⟨3650082, by rfl⟩ : syracuseStep 9733553 = 7300165) B7300165
theorem B6489035 : Blo 2025435 6489035 := bstep (se 1 (by rfl) ⟨4866776, by rfl⟩ : syracuseStep 6489035 = 9733553) B9733553
theorem B4326023 : Blo 2025435 4326023 := bstep (se 1 (by rfl) ⟨3244517, by rfl⟩ : syracuseStep 4326023 = 6489035) B6489035
theorem B2884015 : Blo 2025435 2884015 := bstep (se 1 (by rfl) ⟨2163011, by rfl⟩ : syracuseStep 2884015 = 4326023) B4326023
theorem B15381413 : Blo 2025435 15381413 := bstep (se 4 (by rfl) ⟨1442007, by rfl⟩ : syracuseStep 15381413 = 2884015) B2884015
theorem B10254275 : Blo 2025435 10254275 := bstep (se 1 (by rfl) ⟨7690706, by rfl⟩ : syracuseStep 10254275 = 15381413) B15381413
theorem B6836183 : Blo 2025435 6836183 := bstep (se 1 (by rfl) ⟨5127137, by rfl⟩ : syracuseStep 6836183 = 10254275) B10254275
theorem B4557455 : Blo 2025435 4557455 := bstep (se 1 (by rfl) ⟨3418091, by rfl⟩ : syracuseStep 4557455 = 6836183) B6836183
theorem B3038303 : Blo 2025435 3038303 := bstep (se 1 (by rfl) ⟨2278727, by rfl⟩ : syracuseStep 3038303 = 4557455) B4557455
theorem B2025535 : Blo 2025435 2025535 := bstep (se 1 (by rfl) ⟨1519151, by rfl⟩ : syracuseStep 2025535 = 3038303) B3038303
theorem B3038309 : Blo 2025435 3038309 := bbase (se 4 (by rfl) ⟨284841, by rfl⟩ : syracuseStep 3038309 = 569683) (by norm_num)
theorem B2025539 : Blo 2025435 2025539 := bstep (se 1 (by rfl) ⟨1519154, by rfl⟩ : syracuseStep 2025539 = 3038309) B3038309
theorem B4866797 : Blo 2025435 4866797 := bbase (se 3 (by rfl) ⟨912524, by rfl⟩ : syracuseStep 4866797 = 1825049) (by norm_num)
theorem B3244531 : Blo 2025435 3244531 := bstep (se 1 (by rfl) ⟨2433398, by rfl⟩ : syracuseStep 3244531 = 4866797) B4866797
theorem B4326041 : Blo 2025435 4326041 := bstep (se 2 (by rfl) ⟨1622265, by rfl⟩ : syracuseStep 4326041 = 3244531) B3244531
theorem B2884027 : Blo 2025435 2884027 := bstep (se 1 (by rfl) ⟨2163020, by rfl⟩ : syracuseStep 2884027 = 4326041) B4326041
theorem B3845369 : Blo 2025435 3845369 := bstep (se 2 (by rfl) ⟨1442013, by rfl⟩ : syracuseStep 3845369 = 2884027) B2884027
theorem B2563579 : Blo 2025435 2563579 := bstep (se 1 (by rfl) ⟨1922684, by rfl⟩ : syracuseStep 2563579 = 3845369) B3845369
theorem B3418105 : Blo 2025435 3418105 := bstep (se 2 (by rfl) ⟨1281789, by rfl⟩ : syracuseStep 3418105 = 2563579) B2563579
theorem B4557473 : Blo 2025435 4557473 := bstep (se 2 (by rfl) ⟨1709052, by rfl⟩ : syracuseStep 4557473 = 3418105) B3418105
theorem B3038315 : Blo 2025435 3038315 := bstep (se 1 (by rfl) ⟨2278736, by rfl⟩ : syracuseStep 3038315 = 4557473) B4557473
theorem B2025543 : Blo 2025435 2025543 := bstep (se 1 (by rfl) ⟨1519157, by rfl⟩ : syracuseStep 2025543 = 3038315) B3038315
theorem B2278741 : Blo 2025435 2278741 := bbase (se 12 (by rfl) ⟨834, by rfl⟩ : syracuseStep 2278741 = 1669) (by norm_num)
theorem B3038321 : Blo 2025435 3038321 := bstep (se 2 (by rfl) ⟨1139370, by rfl⟩ : syracuseStep 3038321 = 2278741) B2278741
theorem B2025547 : Blo 2025435 2025547 := bstep (se 1 (by rfl) ⟨1519160, by rfl⟩ : syracuseStep 2025547 = 3038321) B3038321
theorem B2563589 : Blo 2025435 2563589 := bbase (se 4 (by rfl) ⟨240336, by rfl⟩ : syracuseStep 2563589 = 480673) (by norm_num)
theorem B6836237 : Blo 2025435 6836237 := bstep (se 3 (by rfl) ⟨1281794, by rfl⟩ : syracuseStep 6836237 = 2563589) B2563589
theorem B4557491 : Blo 2025435 4557491 := bstep (se 1 (by rfl) ⟨3418118, by rfl⟩ : syracuseStep 4557491 = 6836237) B6836237
theorem B3038327 : Blo 2025435 3038327 := bstep (se 1 (by rfl) ⟨2278745, by rfl⟩ : syracuseStep 3038327 = 4557491) B4557491
theorem B2025551 : Blo 2025435 2025551 := bstep (se 1 (by rfl) ⟨1519163, by rfl⟩ : syracuseStep 2025551 = 3038327) B3038327
theorem B3038333 : Blo 2025435 3038333 := bbase (se 3 (by rfl) ⟨569687, by rfl⟩ : syracuseStep 3038333 = 1139375) (by norm_num)
theorem B2025555 : Blo 2025435 2025555 := bstep (se 1 (by rfl) ⟨1519166, by rfl⟩ : syracuseStep 2025555 = 3038333) B3038333
theorem B4557509 : Blo 2025435 4557509 := bbase (se 4 (by rfl) ⟨427266, by rfl⟩ : syracuseStep 4557509 = 854533) (by norm_num)
theorem B3038339 : Blo 2025435 3038339 := bstep (se 1 (by rfl) ⟨2278754, by rfl⟩ : syracuseStep 3038339 = 4557509) B4557509
theorem B2025559 : Blo 2025435 2025559 := bstep (se 1 (by rfl) ⟨1519169, by rfl⟩ : syracuseStep 2025559 = 3038339) B3038339
theorem B14600533 : Blo 2025435 14600533 := bbase (se 10 (by rfl) ⟨21387, by rfl⟩ : syracuseStep 14600533 = 42775) (by norm_num)
theorem B19467377 : Blo 2025435 19467377 := bstep (se 2 (by rfl) ⟨7300266, by rfl⟩ : syracuseStep 19467377 = 14600533) B14600533
theorem B12978251 : Blo 2025435 12978251 := bstep (se 1 (by rfl) ⟨9733688, by rfl⟩ : syracuseStep 12978251 = 19467377) B19467377
theorem B8652167 : Blo 2025435 8652167 := bstep (se 1 (by rfl) ⟨6489125, by rfl⟩ : syracuseStep 8652167 = 12978251) B12978251
theorem B5768111 : Blo 2025435 5768111 := bstep (se 1 (by rfl) ⟨4326083, by rfl⟩ : syracuseStep 5768111 = 8652167) B8652167
theorem B3845407 : Blo 2025435 3845407 := bstep (se 1 (by rfl) ⟨2884055, by rfl⟩ : syracuseStep 3845407 = 5768111) B5768111
theorem B5127209 : Blo 2025435 5127209 := bstep (se 2 (by rfl) ⟨1922703, by rfl⟩ : syracuseStep 5127209 = 3845407) B3845407
theorem B3418139 : Blo 2025435 3418139 := bstep (se 1 (by rfl) ⟨2563604, by rfl⟩ : syracuseStep 3418139 = 5127209) B5127209
theorem B2278759 : Blo 2025435 2278759 := bstep (se 1 (by rfl) ⟨1709069, by rfl⟩ : syracuseStep 2278759 = 3418139) B3418139
theorem B3038345 : Blo 2025435 3038345 := bstep (se 2 (by rfl) ⟨1139379, by rfl⟩ : syracuseStep 3038345 = 2278759) B2278759
theorem B2025563 : Blo 2025435 2025563 := bstep (se 1 (by rfl) ⟨1519172, by rfl⟩ : syracuseStep 2025563 = 3038345) B3038345
theorem B10254437 : Blo 2025435 10254437 := bbase (se 4 (by rfl) ⟨961353, by rfl⟩ : syracuseStep 10254437 = 1922707) (by norm_num)
theorem B6836291 : Blo 2025435 6836291 := bstep (se 1 (by rfl) ⟨5127218, by rfl⟩ : syracuseStep 6836291 = 10254437) B10254437
theorem B4557527 : Blo 2025435 4557527 := bstep (se 1 (by rfl) ⟨3418145, by rfl⟩ : syracuseStep 4557527 = 6836291) B6836291
theorem B3038351 : Blo 2025435 3038351 := bstep (se 1 (by rfl) ⟨2278763, by rfl⟩ : syracuseStep 3038351 = 4557527) B4557527
theorem B2025567 : Blo 2025435 2025567 := bstep (se 1 (by rfl) ⟨1519175, by rfl⟩ : syracuseStep 2025567 = 3038351) B3038351
theorem B3038357 : Blo 2025435 3038357 := bbase (se 6 (by rfl) ⟨71211, by rfl⟩ : syracuseStep 3038357 = 142423) (by norm_num)
theorem B2025571 : Blo 2025435 2025571 := bstep (se 1 (by rfl) ⟨1519178, by rfl⟩ : syracuseStep 2025571 = 3038357) B3038357
theorem B7300309 : Blo 2025435 7300309 := bbase (se 7 (by rfl) ⟨85550, by rfl⟩ : syracuseStep 7300309 = 171101) (by norm_num)
theorem B9733745 : Blo 2025435 9733745 := bstep (se 2 (by rfl) ⟨3650154, by rfl⟩ : syracuseStep 9733745 = 7300309) B7300309
theorem B6489163 : Blo 2025435 6489163 := bstep (se 1 (by rfl) ⟨4866872, by rfl⟩ : syracuseStep 6489163 = 9733745) B9733745
theorem B8652217 : Blo 2025435 8652217 := bstep (se 2 (by rfl) ⟨3244581, by rfl⟩ : syracuseStep 8652217 = 6489163) B6489163
theorem B11536289 : Blo 2025435 11536289 := bstep (se 2 (by rfl) ⟨4326108, by rfl⟩ : syracuseStep 11536289 = 8652217) B8652217
theorem B7690859 : Blo 2025435 7690859 := bstep (se 1 (by rfl) ⟨5768144, by rfl⟩ : syracuseStep 7690859 = 11536289) B11536289
theorem B5127239 : Blo 2025435 5127239 := bstep (se 1 (by rfl) ⟨3845429, by rfl⟩ : syracuseStep 5127239 = 7690859) B7690859
theorem B3418159 : Blo 2025435 3418159 := bstep (se 1 (by rfl) ⟨2563619, by rfl⟩ : syracuseStep 3418159 = 5127239) B5127239
theorem B4557545 : Blo 2025435 4557545 := bstep (se 2 (by rfl) ⟨1709079, by rfl⟩ : syracuseStep 4557545 = 3418159) B3418159
theorem B3038363 : Blo 2025435 3038363 := bstep (se 1 (by rfl) ⟨2278772, by rfl⟩ : syracuseStep 3038363 = 4557545) B4557545
theorem B2025575 : Blo 2025435 2025575 := bstep (se 1 (by rfl) ⟨1519181, by rfl⟩ : syracuseStep 2025575 = 3038363) B3038363
theorem B2278777 : Blo 2025435 2278777 := bbase (se 2 (by rfl) ⟨854541, by rfl⟩ : syracuseStep 2278777 = 1709083) (by norm_num)
theorem B3038369 : Blo 2025435 3038369 := bstep (se 2 (by rfl) ⟨1139388, by rfl⟩ : syracuseStep 3038369 = 2278777) B2278777
theorem B2025579 : Blo 2025435 2025579 := bstep (se 1 (by rfl) ⟨1519184, by rfl⟩ : syracuseStep 2025579 = 3038369) B3038369
theorem B21901013 : Blo 2025435 21901013 := bbase (se 7 (by rfl) ⟨256652, by rfl⟩ : syracuseStep 21901013 = 513305) (by norm_num)
theorem B14600675 : Blo 2025435 14600675 := bstep (se 1 (by rfl) ⟨10950506, by rfl⟩ : syracuseStep 14600675 = 21901013) B21901013
theorem B9733783 : Blo 2025435 9733783 := bstep (se 1 (by rfl) ⟨7300337, by rfl⟩ : syracuseStep 9733783 = 14600675) B14600675
theorem B12978377 : Blo 2025435 12978377 := bstep (se 2 (by rfl) ⟨4866891, by rfl⟩ : syracuseStep 12978377 = 9733783) B9733783
theorem B8652251 : Blo 2025435 8652251 := bstep (se 1 (by rfl) ⟨6489188, by rfl⟩ : syracuseStep 8652251 = 12978377) B12978377
theorem B5768167 : Blo 2025435 5768167 := bstep (se 1 (by rfl) ⟨4326125, by rfl⟩ : syracuseStep 5768167 = 8652251) B8652251
theorem B7690889 : Blo 2025435 7690889 := bstep (se 2 (by rfl) ⟨2884083, by rfl⟩ : syracuseStep 7690889 = 5768167) B5768167
theorem B5127259 : Blo 2025435 5127259 := bstep (se 1 (by rfl) ⟨3845444, by rfl⟩ : syracuseStep 5127259 = 7690889) B7690889
theorem B6836345 : Blo 2025435 6836345 := bstep (se 2 (by rfl) ⟨2563629, by rfl⟩ : syracuseStep 6836345 = 5127259) B5127259
theorem B4557563 : Blo 2025435 4557563 := bstep (se 1 (by rfl) ⟨3418172, by rfl⟩ : syracuseStep 4557563 = 6836345) B6836345
theorem B3038375 : Blo 2025435 3038375 := bstep (se 1 (by rfl) ⟨2278781, by rfl⟩ : syracuseStep 3038375 = 4557563) B4557563
theorem B2025583 : Blo 2025435 2025583 := bstep (se 1 (by rfl) ⟨1519187, by rfl⟩ : syracuseStep 2025583 = 3038375) B3038375
theorem B3038381 : Blo 2025435 3038381 := bbase (se 3 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 3038381 = 1139393) (by norm_num)
theorem B2025587 : Blo 2025435 2025587 := bstep (se 1 (by rfl) ⟨1519190, by rfl⟩ : syracuseStep 2025587 = 3038381) B3038381
theorem B4557581 : Blo 2025435 4557581 := bbase (se 3 (by rfl) ⟨854546, by rfl⟩ : syracuseStep 4557581 = 1709093) (by norm_num)
theorem B3038387 : Blo 2025435 3038387 := bstep (se 1 (by rfl) ⟨2278790, by rfl⟩ : syracuseStep 3038387 = 4557581) B4557581
theorem B2025591 : Blo 2025435 2025591 := bstep (se 1 (by rfl) ⟨1519193, by rfl⟩ : syracuseStep 2025591 = 3038387) B3038387
theorem B2563645 : Blo 2025435 2563645 := bbase (se 3 (by rfl) ⟨480683, by rfl⟩ : syracuseStep 2563645 = 961367) (by norm_num)
theorem B3418193 : Blo 2025435 3418193 := bstep (se 2 (by rfl) ⟨1281822, by rfl⟩ : syracuseStep 3418193 = 2563645) B2563645
theorem B2278795 : Blo 2025435 2278795 := bstep (se 1 (by rfl) ⟨1709096, by rfl⟩ : syracuseStep 2278795 = 3418193) B3418193
theorem B3038393 : Blo 2025435 3038393 := bstep (se 2 (by rfl) ⟨1139397, by rfl⟩ : syracuseStep 3038393 = 2278795) B2278795
theorem B2025595 : Blo 2025435 2025595 := bstep (se 1 (by rfl) ⟨1519196, by rfl⟩ : syracuseStep 2025595 = 3038393) B3038393
theorem B14600789 : Blo 2025435 14600789 := bbase (se 8 (by rfl) ⟨85551, by rfl⟩ : syracuseStep 14600789 = 171103) (by norm_num)
theorem B9733859 : Blo 2025435 9733859 := bstep (se 1 (by rfl) ⟨7300394, by rfl⟩ : syracuseStep 9733859 = 14600789) B14600789
theorem B6489239 : Blo 2025435 6489239 := bstep (se 1 (by rfl) ⟨4866929, by rfl⟩ : syracuseStep 6489239 = 9733859) B9733859
theorem B17304637 : Blo 2025435 17304637 := bstep (se 3 (by rfl) ⟨3244619, by rfl⟩ : syracuseStep 17304637 = 6489239) B6489239
theorem B23072849 : Blo 2025435 23072849 := bstep (se 2 (by rfl) ⟨8652318, by rfl⟩ : syracuseStep 23072849 = 17304637) B17304637
theorem B15381899 : Blo 2025435 15381899 := bstep (se 1 (by rfl) ⟨11536424, by rfl⟩ : syracuseStep 15381899 = 23072849) B23072849
theorem B10254599 : Blo 2025435 10254599 := bstep (se 1 (by rfl) ⟨7690949, by rfl⟩ : syracuseStep 10254599 = 15381899) B15381899
theorem B6836399 : Blo 2025435 6836399 := bstep (se 1 (by rfl) ⟨5127299, by rfl⟩ : syracuseStep 6836399 = 10254599) B10254599
theorem B4557599 : Blo 2025435 4557599 := bstep (se 1 (by rfl) ⟨3418199, by rfl⟩ : syracuseStep 4557599 = 6836399) B6836399
theorem B3038399 : Blo 2025435 3038399 := bstep (se 1 (by rfl) ⟨2278799, by rfl⟩ : syracuseStep 3038399 = 4557599) B4557599
theorem B2025599 : Blo 2025435 2025599 := bstep (se 1 (by rfl) ⟨1519199, by rfl⟩ : syracuseStep 2025599 = 3038399) B3038399
theorem B3038405 : Blo 2025435 3038405 := bbase (se 4 (by rfl) ⟨284850, by rfl⟩ : syracuseStep 3038405 = 569701) (by norm_num)
theorem B2025603 : Blo 2025435 2025603 := bstep (se 1 (by rfl) ⟨1519202, by rfl⟩ : syracuseStep 2025603 = 3038405) B3038405
theorem B3418213 : Blo 2025435 3418213 := bbase (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) (by norm_num)
theorem B4557617 : Blo 2025435 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B3038411 : Blo 2025435 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B2025607 : Blo 2025435 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B2278813 : Blo 2025435 2278813 := bbase (se 3 (by rfl) ⟨427277, by rfl⟩ : syracuseStep 2278813 = 854555) (by norm_num)
theorem B3038417 : Blo 2025435 3038417 := bstep (se 2 (by rfl) ⟨1139406, by rfl⟩ : syracuseStep 3038417 = 2278813) B2278813
theorem B2025611 : Blo 2025435 2025611 := bstep (se 1 (by rfl) ⟨1519208, by rfl⟩ : syracuseStep 2025611 = 3038417) B3038417
theorem B6836453 : Blo 2025435 6836453 := bbase (se 4 (by rfl) ⟨640917, by rfl⟩ : syracuseStep 6836453 = 1281835) (by norm_num)
theorem B4557635 : Blo 2025435 4557635 := bstep (se 1 (by rfl) ⟨3418226, by rfl⟩ : syracuseStep 4557635 = 6836453) B6836453
theorem B3038423 : Blo 2025435 3038423 := bstep (se 1 (by rfl) ⟨2278817, by rfl⟩ : syracuseStep 3038423 = 4557635) B4557635
theorem B2025615 : Blo 2025435 2025615 := bstep (se 1 (by rfl) ⟨1519211, by rfl⟩ : syracuseStep 2025615 = 3038423) B3038423
theorem B3038429 : Blo 2025435 3038429 := bbase (se 3 (by rfl) ⟨569705, by rfl⟩ : syracuseStep 3038429 = 1139411) (by norm_num)
theorem B2025619 : Blo 2025435 2025619 := bstep (se 1 (by rfl) ⟨1519214, by rfl⟩ : syracuseStep 2025619 = 3038429) B3038429
theorem B4557653 : Blo 2025435 4557653 := bbase (se 9 (by rfl) ⟨13352, by rfl⟩ : syracuseStep 4557653 = 26705) (by norm_num)
theorem B3038435 : Blo 2025435 3038435 := bstep (se 1 (by rfl) ⟨2278826, by rfl⟩ : syracuseStep 3038435 = 4557653) B4557653
theorem B2025623 : Blo 2025435 2025623 := bstep (se 1 (by rfl) ⟨1519217, by rfl⟩ : syracuseStep 2025623 = 3038435) B3038435
theorem B5768293 : Blo 2025435 5768293 := bbase (se 4 (by rfl) ⟨540777, by rfl⟩ : syracuseStep 5768293 = 1081555) (by norm_num)
theorem B7691057 : Blo 2025435 7691057 := bstep (se 2 (by rfl) ⟨2884146, by rfl⟩ : syracuseStep 7691057 = 5768293) B5768293
theorem B5127371 : Blo 2025435 5127371 := bstep (se 1 (by rfl) ⟨3845528, by rfl⟩ : syracuseStep 5127371 = 7691057) B7691057
theorem B3418247 : Blo 2025435 3418247 := bstep (se 1 (by rfl) ⟨2563685, by rfl⟩ : syracuseStep 3418247 = 5127371) B5127371
theorem B2278831 : Blo 2025435 2278831 := bstep (se 1 (by rfl) ⟨1709123, by rfl⟩ : syracuseStep 2278831 = 3418247) B3418247
theorem B3038441 : Blo 2025435 3038441 := bstep (se 2 (by rfl) ⟨1139415, by rfl⟩ : syracuseStep 3038441 = 2278831) B2278831
theorem B2025627 : Blo 2025435 2025627 := bstep (se 1 (by rfl) ⟨1519220, by rfl⟩ : syracuseStep 2025627 = 3038441) B3038441
theorem B3288941 : Blo 2025435 3288941 := bbase (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) (by norm_num)
theorem B2192627 : Blo 2025435 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B5847005 : Blo 2025435 5847005 := bstep (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) B2192627
theorem B3898003 : Blo 2025435 3898003 := bstep (se 1 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 3898003 = 5847005) B5847005
theorem B5197337 : Blo 2025435 5197337 := bstep (se 2 (by rfl) ⟨1949001, by rfl⟩ : syracuseStep 5197337 = 3898003) B3898003
theorem B3464891 : Blo 2025435 3464891 := bstep (se 1 (by rfl) ⟨2598668, by rfl⟩ : syracuseStep 3464891 = 5197337) B5197337
theorem B2309927 : Blo 2025435 2309927 := bstep (se 1 (by rfl) ⟨1732445, by rfl⟩ : syracuseStep 2309927 = 3464891) B3464891
theorem B24639221 : Blo 2025435 24639221 := bstep (se 5 (by rfl) ⟨1154963, by rfl⟩ : syracuseStep 24639221 = 2309927) B2309927
theorem B16426147 : Blo 2025435 16426147 := bstep (se 1 (by rfl) ⟨12319610, by rfl⟩ : syracuseStep 16426147 = 24639221) B24639221
theorem B21901529 : Blo 2025435 21901529 := bstep (se 2 (by rfl) ⟨8213073, by rfl⟩ : syracuseStep 21901529 = 16426147) B16426147
theorem B58404077 : Blo 2025435 58404077 := bstep (se 3 (by rfl) ⟨10950764, by rfl⟩ : syracuseStep 58404077 = 21901529) B21901529
theorem B38936051 : Blo 2025435 38936051 := bstep (se 1 (by rfl) ⟨29202038, by rfl⟩ : syracuseStep 38936051 = 58404077) B58404077
theorem B25957367 : Blo 2025435 25957367 := bstep (se 1 (by rfl) ⟨19468025, by rfl⟩ : syracuseStep 25957367 = 38936051) B38936051
theorem B17304911 : Blo 2025435 17304911 := bstep (se 1 (by rfl) ⟨12978683, by rfl⟩ : syracuseStep 17304911 = 25957367) B25957367
theorem B11536607 : Blo 2025435 11536607 := bstep (se 1 (by rfl) ⟨8652455, by rfl⟩ : syracuseStep 11536607 = 17304911) B17304911
theorem B7691071 : Blo 2025435 7691071 := bstep (se 1 (by rfl) ⟨5768303, by rfl⟩ : syracuseStep 7691071 = 11536607) B11536607
theorem B10254761 : Blo 2025435 10254761 := bstep (se 2 (by rfl) ⟨3845535, by rfl⟩ : syracuseStep 10254761 = 7691071) B7691071
theorem B6836507 : Blo 2025435 6836507 := bstep (se 1 (by rfl) ⟨5127380, by rfl⟩ : syracuseStep 6836507 = 10254761) B10254761
theorem B4557671 : Blo 2025435 4557671 := bstep (se 1 (by rfl) ⟨3418253, by rfl⟩ : syracuseStep 4557671 = 6836507) B6836507
theorem B3038447 : Blo 2025435 3038447 := bstep (se 1 (by rfl) ⟨2278835, by rfl⟩ : syracuseStep 3038447 = 4557671) B4557671
theorem B2025631 : Blo 2025435 2025631 := bstep (se 1 (by rfl) ⟨1519223, by rfl⟩ : syracuseStep 2025631 = 3038447) B3038447
theorem B3038453 : Blo 2025435 3038453 := bbase (se 5 (by rfl) ⟨142427, by rfl⟩ : syracuseStep 3038453 = 284855) (by norm_num)
theorem B2025635 : Blo 2025435 2025635 := bstep (se 1 (by rfl) ⟨1519226, by rfl⟩ : syracuseStep 2025635 = 3038453) B3038453
theorem B9734053 : Blo 2025435 9734053 := bbase (se 4 (by rfl) ⟨912567, by rfl⟩ : syracuseStep 9734053 = 1825135) (by norm_num)
theorem B12978737 : Blo 2025435 12978737 := bstep (se 2 (by rfl) ⟨4867026, by rfl⟩ : syracuseStep 12978737 = 9734053) B9734053
theorem B8652491 : Blo 2025435 8652491 := bstep (se 1 (by rfl) ⟨6489368, by rfl⟩ : syracuseStep 8652491 = 12978737) B12978737
theorem B5768327 : Blo 2025435 5768327 := bstep (se 1 (by rfl) ⟨4326245, by rfl⟩ : syracuseStep 5768327 = 8652491) B8652491
theorem B3845551 : Blo 2025435 3845551 := bstep (se 1 (by rfl) ⟨2884163, by rfl⟩ : syracuseStep 3845551 = 5768327) B5768327
theorem B5127401 : Blo 2025435 5127401 := bstep (se 2 (by rfl) ⟨1922775, by rfl⟩ : syracuseStep 5127401 = 3845551) B3845551
theorem B3418267 : Blo 2025435 3418267 := bstep (se 1 (by rfl) ⟨2563700, by rfl⟩ : syracuseStep 3418267 = 5127401) B5127401
theorem B4557689 : Blo 2025435 4557689 := bstep (se 2 (by rfl) ⟨1709133, by rfl⟩ : syracuseStep 4557689 = 3418267) B3418267
theorem B3038459 : Blo 2025435 3038459 := bstep (se 1 (by rfl) ⟨2278844, by rfl⟩ : syracuseStep 3038459 = 4557689) B4557689
theorem B2025639 : Blo 2025435 2025639 := bstep (se 1 (by rfl) ⟨1519229, by rfl⟩ : syracuseStep 2025639 = 3038459) B3038459
theorem B2278849 : Blo 2025435 2278849 := bbase (se 2 (by rfl) ⟨854568, by rfl⟩ : syracuseStep 2278849 = 1709137) (by norm_num)
theorem B3038465 : Blo 2025435 3038465 := bstep (se 2 (by rfl) ⟨1139424, by rfl⟩ : syracuseStep 3038465 = 2278849) B2278849
theorem B2025643 : Blo 2025435 2025643 := bstep (se 1 (by rfl) ⟨1519232, by rfl⟩ : syracuseStep 2025643 = 3038465) B3038465
theorem B5127421 : Blo 2025435 5127421 := bbase (se 3 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 5127421 = 1922783) (by norm_num)
theorem B6836561 : Blo 2025435 6836561 := bstep (se 2 (by rfl) ⟨2563710, by rfl⟩ : syracuseStep 6836561 = 5127421) B5127421
theorem B4557707 : Blo 2025435 4557707 := bstep (se 1 (by rfl) ⟨3418280, by rfl⟩ : syracuseStep 4557707 = 6836561) B6836561
theorem B3038471 : Blo 2025435 3038471 := bstep (se 1 (by rfl) ⟨2278853, by rfl⟩ : syracuseStep 3038471 = 4557707) B4557707
theorem B2025647 : Blo 2025435 2025647 := bstep (se 1 (by rfl) ⟨1519235, by rfl⟩ : syracuseStep 2025647 = 3038471) B3038471
theorem B3038477 : Blo 2025435 3038477 := bbase (se 3 (by rfl) ⟨569714, by rfl⟩ : syracuseStep 3038477 = 1139429) (by norm_num)
theorem B2025651 : Blo 2025435 2025651 := bstep (se 1 (by rfl) ⟨1519238, by rfl⟩ : syracuseStep 2025651 = 3038477) B3038477
theorem B4557725 : Blo 2025435 4557725 := bbase (se 3 (by rfl) ⟨854573, by rfl⟩ : syracuseStep 4557725 = 1709147) (by norm_num)
theorem B3038483 : Blo 2025435 3038483 := bstep (se 1 (by rfl) ⟨2278862, by rfl⟩ : syracuseStep 3038483 = 4557725) B4557725
theorem B2025655 : Blo 2025435 2025655 := bstep (se 1 (by rfl) ⟨1519241, by rfl⟩ : syracuseStep 2025655 = 3038483) B3038483
theorem B3418301 : Blo 2025435 3418301 := bbase (se 3 (by rfl) ⟨640931, by rfl⟩ : syracuseStep 3418301 = 1281863) (by norm_num)
theorem B2278867 : Blo 2025435 2278867 := bstep (se 1 (by rfl) ⟨1709150, by rfl⟩ : syracuseStep 2278867 = 3418301) B3418301
theorem B3038489 : Blo 2025435 3038489 := bstep (se 2 (by rfl) ⟨1139433, by rfl⟩ : syracuseStep 3038489 = 2278867) B2278867
theorem B2025659 : Blo 2025435 2025659 := bstep (se 1 (by rfl) ⟨1519244, by rfl⟩ : syracuseStep 2025659 = 3038489) B3038489
theorem B11536789 : Blo 2025435 11536789 := bbase (se 6 (by rfl) ⟨270393, by rfl⟩ : syracuseStep 11536789 = 540787) (by norm_num)
theorem B15382385 : Blo 2025435 15382385 := bstep (se 2 (by rfl) ⟨5768394, by rfl⟩ : syracuseStep 15382385 = 11536789) B11536789
theorem B10254923 : Blo 2025435 10254923 := bstep (se 1 (by rfl) ⟨7691192, by rfl⟩ : syracuseStep 10254923 = 15382385) B15382385
theorem B6836615 : Blo 2025435 6836615 := bstep (se 1 (by rfl) ⟨5127461, by rfl⟩ : syracuseStep 6836615 = 10254923) B10254923
theorem B4557743 : Blo 2025435 4557743 := bstep (se 1 (by rfl) ⟨3418307, by rfl⟩ : syracuseStep 4557743 = 6836615) B6836615
theorem B3038495 : Blo 2025435 3038495 := bstep (se 1 (by rfl) ⟨2278871, by rfl⟩ : syracuseStep 3038495 = 4557743) B4557743
theorem B2025663 : Blo 2025435 2025663 := bstep (se 1 (by rfl) ⟨1519247, by rfl⟩ : syracuseStep 2025663 = 3038495) B3038495
theorem B3038501 : Blo 2025435 3038501 := bbase (se 4 (by rfl) ⟨284859, by rfl⟩ : syracuseStep 3038501 = 569719) (by norm_num)
theorem B2025667 : Blo 2025435 2025667 := bstep (se 1 (by rfl) ⟨1519250, by rfl⟩ : syracuseStep 2025667 = 3038501) B3038501
theorem B2563741 : Blo 2025435 2563741 := bbase (se 3 (by rfl) ⟨480701, by rfl⟩ : syracuseStep 2563741 = 961403) (by norm_num)
theorem B3418321 : Blo 2025435 3418321 := bstep (se 2 (by rfl) ⟨1281870, by rfl⟩ : syracuseStep 3418321 = 2563741) B2563741
theorem B4557761 : Blo 2025435 4557761 := bstep (se 2 (by rfl) ⟨1709160, by rfl⟩ : syracuseStep 4557761 = 3418321) B3418321
theorem B3038507 : Blo 2025435 3038507 := bstep (se 1 (by rfl) ⟨2278880, by rfl⟩ : syracuseStep 3038507 = 4557761) B4557761
theorem B2025671 : Blo 2025435 2025671 := bstep (se 1 (by rfl) ⟨1519253, by rfl⟩ : syracuseStep 2025671 = 3038507) B3038507
theorem B2278885 : Blo 2025435 2278885 := bbase (se 4 (by rfl) ⟨213645, by rfl⟩ : syracuseStep 2278885 = 427291) (by norm_num)
theorem B3038513 : Blo 2025435 3038513 := bstep (se 2 (by rfl) ⟨1139442, by rfl⟩ : syracuseStep 3038513 = 2278885) B2278885
theorem B2025675 : Blo 2025435 2025675 := bstep (se 1 (by rfl) ⟨1519256, by rfl⟩ : syracuseStep 2025675 = 3038513) B3038513
theorem B2737757 : Blo 2025435 2737757 := bbase (se 3 (by rfl) ⟨513329, by rfl⟩ : syracuseStep 2737757 = 1026659) (by norm_num)
theorem B7300685 : Blo 2025435 7300685 := bstep (se 3 (by rfl) ⟨1368878, by rfl⟩ : syracuseStep 7300685 = 2737757) B2737757
theorem B4867123 : Blo 2025435 4867123 := bstep (se 1 (by rfl) ⟨3650342, by rfl⟩ : syracuseStep 4867123 = 7300685) B7300685
theorem B6489497 : Blo 2025435 6489497 := bstep (se 2 (by rfl) ⟨2433561, by rfl⟩ : syracuseStep 6489497 = 4867123) B4867123
theorem B4326331 : Blo 2025435 4326331 := bstep (se 1 (by rfl) ⟨3244748, by rfl⟩ : syracuseStep 4326331 = 6489497) B6489497
theorem B5768441 : Blo 2025435 5768441 := bstep (se 2 (by rfl) ⟨2163165, by rfl⟩ : syracuseStep 5768441 = 4326331) B4326331
theorem B3845627 : Blo 2025435 3845627 := bstep (se 1 (by rfl) ⟨2884220, by rfl⟩ : syracuseStep 3845627 = 5768441) B5768441
theorem B2563751 : Blo 2025435 2563751 := bstep (se 1 (by rfl) ⟨1922813, by rfl⟩ : syracuseStep 2563751 = 3845627) B3845627
theorem B6836669 : Blo 2025435 6836669 := bstep (se 3 (by rfl) ⟨1281875, by rfl⟩ : syracuseStep 6836669 = 2563751) B2563751
theorem B4557779 : Blo 2025435 4557779 := bstep (se 1 (by rfl) ⟨3418334, by rfl⟩ : syracuseStep 4557779 = 6836669) B6836669
theorem B3038519 : Blo 2025435 3038519 := bstep (se 1 (by rfl) ⟨2278889, by rfl⟩ : syracuseStep 3038519 = 4557779) B4557779
theorem B2025679 : Blo 2025435 2025679 := bstep (se 1 (by rfl) ⟨1519259, by rfl⟩ : syracuseStep 2025679 = 3038519) B3038519
theorem B3038525 : Blo 2025435 3038525 := bbase (se 3 (by rfl) ⟨569723, by rfl⟩ : syracuseStep 3038525 = 1139447) (by norm_num)
theorem B2025683 : Blo 2025435 2025683 := bstep (se 1 (by rfl) ⟨1519262, by rfl⟩ : syracuseStep 2025683 = 3038525) B3038525
theorem B4557797 : Blo 2025435 4557797 := bbase (se 4 (by rfl) ⟨427293, by rfl⟩ : syracuseStep 4557797 = 854587) (by norm_num)
theorem B3038531 : Blo 2025435 3038531 := bstep (se 1 (by rfl) ⟨2278898, by rfl⟩ : syracuseStep 3038531 = 4557797) B4557797
theorem B2025687 : Blo 2025435 2025687 := bstep (se 1 (by rfl) ⟨1519265, by rfl⟩ : syracuseStep 2025687 = 3038531) B3038531
theorem B5127533 : Blo 2025435 5127533 := bbase (se 3 (by rfl) ⟨961412, by rfl⟩ : syracuseStep 5127533 = 1922825) (by norm_num)
theorem B3418355 : Blo 2025435 3418355 := bstep (se 1 (by rfl) ⟨2563766, by rfl⟩ : syracuseStep 3418355 = 5127533) B5127533
theorem B2278903 : Blo 2025435 2278903 := bstep (se 1 (by rfl) ⟨1709177, by rfl⟩ : syracuseStep 2278903 = 3418355) B3418355
theorem B3038537 : Blo 2025435 3038537 := bstep (se 2 (by rfl) ⟨1139451, by rfl⟩ : syracuseStep 3038537 = 2278903) B2278903
theorem B2025691 : Blo 2025435 2025691 := bstep (se 1 (by rfl) ⟨1519268, by rfl⟩ : syracuseStep 2025691 = 3038537) B3038537
theorem B4326365 : Blo 2025435 4326365 := bbase (se 3 (by rfl) ⟨811193, by rfl⟩ : syracuseStep 4326365 = 1622387) (by norm_num)
theorem B2884243 : Blo 2025435 2884243 := bstep (se 1 (by rfl) ⟨2163182, by rfl⟩ : syracuseStep 2884243 = 4326365) B4326365
theorem B3845657 : Blo 2025435 3845657 := bstep (se 2 (by rfl) ⟨1442121, by rfl⟩ : syracuseStep 3845657 = 2884243) B2884243
theorem B10255085 : Blo 2025435 10255085 := bstep (se 3 (by rfl) ⟨1922828, by rfl⟩ : syracuseStep 10255085 = 3845657) B3845657
theorem B6836723 : Blo 2025435 6836723 := bstep (se 1 (by rfl) ⟨5127542, by rfl⟩ : syracuseStep 6836723 = 10255085) B10255085
theorem B4557815 : Blo 2025435 4557815 := bstep (se 1 (by rfl) ⟨3418361, by rfl⟩ : syracuseStep 4557815 = 6836723) B6836723
theorem B3038543 : Blo 2025435 3038543 := bstep (se 1 (by rfl) ⟨2278907, by rfl⟩ : syracuseStep 3038543 = 4557815) B4557815
theorem B2025695 : Blo 2025435 2025695 := bstep (se 1 (by rfl) ⟨1519271, by rfl⟩ : syracuseStep 2025695 = 3038543) B3038543
theorem B3038549 : Blo 2025435 3038549 := bbase (se 11 (by rfl) ⟨2225, by rfl⟩ : syracuseStep 3038549 = 4451) (by norm_num)
theorem B2025699 : Blo 2025435 2025699 := bstep (se 1 (by rfl) ⟨1519274, by rfl⟩ : syracuseStep 2025699 = 3038549) B3038549
theorem B4867181 : Blo 2025435 4867181 := bbase (se 3 (by rfl) ⟨912596, by rfl⟩ : syracuseStep 4867181 = 1825193) (by norm_num)
theorem B3244787 : Blo 2025435 3244787 := bstep (se 1 (by rfl) ⟨2433590, by rfl⟩ : syracuseStep 3244787 = 4867181) B4867181
theorem B2163191 : Blo 2025435 2163191 := bstep (se 1 (by rfl) ⟨1622393, by rfl⟩ : syracuseStep 2163191 = 3244787) B3244787
theorem B5768509 : Blo 2025435 5768509 := bstep (se 3 (by rfl) ⟨1081595, by rfl⟩ : syracuseStep 5768509 = 2163191) B2163191
theorem B7691345 : Blo 2025435 7691345 := bstep (se 2 (by rfl) ⟨2884254, by rfl⟩ : syracuseStep 7691345 = 5768509) B5768509
theorem B5127563 : Blo 2025435 5127563 := bstep (se 1 (by rfl) ⟨3845672, by rfl⟩ : syracuseStep 5127563 = 7691345) B7691345
theorem B3418375 : Blo 2025435 3418375 := bstep (se 1 (by rfl) ⟨2563781, by rfl⟩ : syracuseStep 3418375 = 5127563) B5127563
theorem B4557833 : Blo 2025435 4557833 := bstep (se 2 (by rfl) ⟨1709187, by rfl⟩ : syracuseStep 4557833 = 3418375) B3418375
theorem B3038555 : Blo 2025435 3038555 := bstep (se 1 (by rfl) ⟨2278916, by rfl⟩ : syracuseStep 3038555 = 4557833) B4557833
theorem B2025703 : Blo 2025435 2025703 := bstep (se 1 (by rfl) ⟨1519277, by rfl⟩ : syracuseStep 2025703 = 3038555) B3038555
theorem B2278921 : Blo 2025435 2278921 := bbase (se 2 (by rfl) ⟨854595, by rfl⟩ : syracuseStep 2278921 = 1709191) (by norm_num)
theorem B3038561 : Blo 2025435 3038561 := bstep (se 2 (by rfl) ⟨1139460, by rfl⟩ : syracuseStep 3038561 = 2278921) B2278921
theorem B2025707 : Blo 2025435 2025707 := bstep (se 1 (by rfl) ⟨1519280, by rfl⟩ : syracuseStep 2025707 = 3038561) B3038561
theorem B2192713 : Blo 2025435 2192713 := bbase (se 2 (by rfl) ⟨822267, by rfl⟩ : syracuseStep 2192713 = 1644535) (by norm_num)
theorem B11694469 : Blo 2025435 11694469 := bstep (se 4 (by rfl) ⟨1096356, by rfl⟩ : syracuseStep 11694469 = 2192713) B2192713
theorem B15592625 : Blo 2025435 15592625 := bstep (se 2 (by rfl) ⟨5847234, by rfl⟩ : syracuseStep 15592625 = 11694469) B11694469
theorem B10395083 : Blo 2025435 10395083 := bstep (se 1 (by rfl) ⟨7796312, by rfl⟩ : syracuseStep 10395083 = 15592625) B15592625
theorem B6930055 : Blo 2025435 6930055 := bstep (se 1 (by rfl) ⟨5197541, by rfl⟩ : syracuseStep 6930055 = 10395083) B10395083
theorem B36960293 : Blo 2025435 36960293 := bstep (se 4 (by rfl) ⟨3465027, by rfl⟩ : syracuseStep 36960293 = 6930055) B6930055
theorem B24640195 : Blo 2025435 24640195 := bstep (se 1 (by rfl) ⟨18480146, by rfl⟩ : syracuseStep 24640195 = 36960293) B36960293
theorem B32853593 : Blo 2025435 32853593 := bstep (se 2 (by rfl) ⟨12320097, by rfl⟩ : syracuseStep 32853593 = 24640195) B24640195
theorem B21902395 : Blo 2025435 21902395 := bstep (se 1 (by rfl) ⟨16426796, by rfl⟩ : syracuseStep 21902395 = 32853593) B32853593
theorem B29203193 : Blo 2025435 29203193 := bstep (se 2 (by rfl) ⟨10951197, by rfl⟩ : syracuseStep 29203193 = 21902395) B21902395
theorem B19468795 : Blo 2025435 19468795 := bstep (se 1 (by rfl) ⟨14601596, by rfl⟩ : syracuseStep 19468795 = 29203193) B29203193
theorem B25958393 : Blo 2025435 25958393 := bstep (se 2 (by rfl) ⟨9734397, by rfl⟩ : syracuseStep 25958393 = 19468795) B19468795
theorem B17305595 : Blo 2025435 17305595 := bstep (se 1 (by rfl) ⟨12979196, by rfl⟩ : syracuseStep 17305595 = 25958393) B25958393
theorem B11537063 : Blo 2025435 11537063 := bstep (se 1 (by rfl) ⟨8652797, by rfl⟩ : syracuseStep 11537063 = 17305595) B17305595
theorem B7691375 : Blo 2025435 7691375 := bstep (se 1 (by rfl) ⟨5768531, by rfl⟩ : syracuseStep 7691375 = 11537063) B11537063
theorem B5127583 : Blo 2025435 5127583 := bstep (se 1 (by rfl) ⟨3845687, by rfl⟩ : syracuseStep 5127583 = 7691375) B7691375
theorem B6836777 : Blo 2025435 6836777 := bstep (se 2 (by rfl) ⟨2563791, by rfl⟩ : syracuseStep 6836777 = 5127583) B5127583
theorem B4557851 : Blo 2025435 4557851 := bstep (se 1 (by rfl) ⟨3418388, by rfl⟩ : syracuseStep 4557851 = 6836777) B6836777
theorem B3038567 : Blo 2025435 3038567 := bstep (se 1 (by rfl) ⟨2278925, by rfl⟩ : syracuseStep 3038567 = 4557851) B4557851
theorem B2025711 : Blo 2025435 2025711 := bstep (se 1 (by rfl) ⟨1519283, by rfl⟩ : syracuseStep 2025711 = 3038567) B3038567
theorem B3038573 : Blo 2025435 3038573 := bbase (se 3 (by rfl) ⟨569732, by rfl⟩ : syracuseStep 3038573 = 1139465) (by norm_num)
theorem B2025715 : Blo 2025435 2025715 := bstep (se 1 (by rfl) ⟨1519286, by rfl⟩ : syracuseStep 2025715 = 3038573) B3038573
theorem B4557869 : Blo 2025435 4557869 := bbase (se 3 (by rfl) ⟨854600, by rfl⟩ : syracuseStep 4557869 = 1709201) (by norm_num)
theorem B3038579 : Blo 2025435 3038579 := bstep (se 1 (by rfl) ⟨2278934, by rfl⟩ : syracuseStep 3038579 = 4557869) B4557869
theorem B2025719 : Blo 2025435 2025719 := bstep (se 1 (by rfl) ⟨1519289, by rfl⟩ : syracuseStep 2025719 = 3038579) B3038579
theorem B4867229 : Blo 2025435 4867229 := bbase (se 3 (by rfl) ⟨912605, by rfl⟩ : syracuseStep 4867229 = 1825211) (by norm_num)
theorem B12979277 : Blo 2025435 12979277 := bstep (se 3 (by rfl) ⟨2433614, by rfl⟩ : syracuseStep 12979277 = 4867229) B4867229
theorem B8652851 : Blo 2025435 8652851 := bstep (se 1 (by rfl) ⟨6489638, by rfl⟩ : syracuseStep 8652851 = 12979277) B12979277
theorem B5768567 : Blo 2025435 5768567 := bstep (se 1 (by rfl) ⟨4326425, by rfl⟩ : syracuseStep 5768567 = 8652851) B8652851
theorem B3845711 : Blo 2025435 3845711 := bstep (se 1 (by rfl) ⟨2884283, by rfl⟩ : syracuseStep 3845711 = 5768567) B5768567
theorem B2563807 : Blo 2025435 2563807 := bstep (se 1 (by rfl) ⟨1922855, by rfl⟩ : syracuseStep 2563807 = 3845711) B3845711
theorem B3418409 : Blo 2025435 3418409 := bstep (se 2 (by rfl) ⟨1281903, by rfl⟩ : syracuseStep 3418409 = 2563807) B2563807
theorem B2278939 : Blo 2025435 2278939 := bstep (se 1 (by rfl) ⟨1709204, by rfl⟩ : syracuseStep 2278939 = 3418409) B3418409
theorem B3038585 : Blo 2025435 3038585 := bstep (se 2 (by rfl) ⟨1139469, by rfl⟩ : syracuseStep 3038585 = 2278939) B2278939
theorem B2025723 : Blo 2025435 2025723 := bstep (se 1 (by rfl) ⟨1519292, by rfl⟩ : syracuseStep 2025723 = 3038585) B3038585
theorem B4867237 : Blo 2025435 4867237 := bbase (se 4 (by rfl) ⟨456303, by rfl⟩ : syracuseStep 4867237 = 912607) (by norm_num)
theorem B6489649 : Blo 2025435 6489649 := bstep (se 2 (by rfl) ⟨2433618, by rfl⟩ : syracuseStep 6489649 = 4867237) B4867237
theorem B34611461 : Blo 2025435 34611461 := bstep (se 4 (by rfl) ⟨3244824, by rfl⟩ : syracuseStep 34611461 = 6489649) B6489649
theorem B23074307 : Blo 2025435 23074307 := bstep (se 1 (by rfl) ⟨17305730, by rfl⟩ : syracuseStep 23074307 = 34611461) B34611461
theorem B15382871 : Blo 2025435 15382871 := bstep (se 1 (by rfl) ⟨11537153, by rfl⟩ : syracuseStep 15382871 = 23074307) B23074307
theorem B10255247 : Blo 2025435 10255247 := bstep (se 1 (by rfl) ⟨7691435, by rfl⟩ : syracuseStep 10255247 = 15382871) B15382871
theorem B6836831 : Blo 2025435 6836831 := bstep (se 1 (by rfl) ⟨5127623, by rfl⟩ : syracuseStep 6836831 = 10255247) B10255247
theorem B4557887 : Blo 2025435 4557887 := bstep (se 1 (by rfl) ⟨3418415, by rfl⟩ : syracuseStep 4557887 = 6836831) B6836831
theorem B3038591 : Blo 2025435 3038591 := bstep (se 1 (by rfl) ⟨2278943, by rfl⟩ : syracuseStep 3038591 = 4557887) B4557887
theorem B2025727 : Blo 2025435 2025727 := bstep (se 1 (by rfl) ⟨1519295, by rfl⟩ : syracuseStep 2025727 = 3038591) B3038591
theorem B3038597 : Blo 2025435 3038597 := bbase (se 4 (by rfl) ⟨284868, by rfl⟩ : syracuseStep 3038597 = 569737) (by norm_num)
theorem B2025731 : Blo 2025435 2025731 := bstep (se 1 (by rfl) ⟨1519298, by rfl⟩ : syracuseStep 2025731 = 3038597) B3038597
theorem B3418429 : Blo 2025435 3418429 := bbase (se 3 (by rfl) ⟨640955, by rfl⟩ : syracuseStep 3418429 = 1281911) (by norm_num)
theorem B4557905 : Blo 2025435 4557905 := bstep (se 2 (by rfl) ⟨1709214, by rfl⟩ : syracuseStep 4557905 = 3418429) B3418429
theorem B3038603 : Blo 2025435 3038603 := bstep (se 1 (by rfl) ⟨2278952, by rfl⟩ : syracuseStep 3038603 = 4557905) B4557905
theorem B2025735 : Blo 2025435 2025735 := bstep (se 1 (by rfl) ⟨1519301, by rfl⟩ : syracuseStep 2025735 = 3038603) B3038603
theorem B2278957 : Blo 2025435 2278957 := bbase (se 3 (by rfl) ⟨427304, by rfl⟩ : syracuseStep 2278957 = 854609) (by norm_num)
theorem B3038609 : Blo 2025435 3038609 := bstep (se 2 (by rfl) ⟨1139478, by rfl⟩ : syracuseStep 3038609 = 2278957) B2278957
theorem B2025739 : Blo 2025435 2025739 := bstep (se 1 (by rfl) ⟨1519304, by rfl⟩ : syracuseStep 2025739 = 3038609) B3038609
theorem B6836885 : Blo 2025435 6836885 := bbase (se 6 (by rfl) ⟨160239, by rfl⟩ : syracuseStep 6836885 = 320479) (by norm_num)
theorem B4557923 : Blo 2025435 4557923 := bstep (se 1 (by rfl) ⟨3418442, by rfl⟩ : syracuseStep 4557923 = 6836885) B6836885
theorem B3038615 : Blo 2025435 3038615 := bstep (se 1 (by rfl) ⟨2278961, by rfl⟩ : syracuseStep 3038615 = 4557923) B4557923
theorem B2025743 : Blo 2025435 2025743 := bstep (se 1 (by rfl) ⟨1519307, by rfl⟩ : syracuseStep 2025743 = 3038615) B3038615
theorem B3038621 : Blo 2025435 3038621 := bbase (se 3 (by rfl) ⟨569741, by rfl⟩ : syracuseStep 3038621 = 1139483) (by norm_num)
theorem B2025747 : Blo 2025435 2025747 := bstep (se 1 (by rfl) ⟨1519310, by rfl⟩ : syracuseStep 2025747 = 3038621) B3038621
theorem B4557941 : Blo 2025435 4557941 := bbase (se 5 (by rfl) ⟨213653, by rfl⟩ : syracuseStep 4557941 = 427307) (by norm_num)
theorem B3038627 : Blo 2025435 3038627 := bstep (se 1 (by rfl) ⟨2278970, by rfl⟩ : syracuseStep 3038627 = 4557941) B4557941
theorem B2025751 : Blo 2025435 2025751 := bstep (se 1 (by rfl) ⟨1519313, by rfl⟩ : syracuseStep 2025751 = 3038627) B3038627
theorem B17305973 : Blo 2025435 17305973 := bbase (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) (by norm_num)
theorem B11537315 : Blo 2025435 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B7691543 : Blo 2025435 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B5127695 : Blo 2025435 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B3418463 : Blo 2025435 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B2278975 : Blo 2025435 2278975 := bstep (se 1 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 2278975 = 3418463) B3418463
theorem B3038633 : Blo 2025435 3038633 := bstep (se 2 (by rfl) ⟨1139487, by rfl⟩ : syracuseStep 3038633 = 2278975) B2278975
theorem B2025755 : Blo 2025435 2025755 := bstep (se 1 (by rfl) ⟨1519316, by rfl⟩ : syracuseStep 2025755 = 3038633) B3038633
theorem B7691557 : Blo 2025435 7691557 := bbase (se 4 (by rfl) ⟨721083, by rfl⟩ : syracuseStep 7691557 = 1442167) (by norm_num)
theorem B10255409 : Blo 2025435 10255409 := bstep (se 2 (by rfl) ⟨3845778, by rfl⟩ : syracuseStep 10255409 = 7691557) B7691557
theorem B6836939 : Blo 2025435 6836939 := bstep (se 1 (by rfl) ⟨5127704, by rfl⟩ : syracuseStep 6836939 = 10255409) B10255409
theorem B4557959 : Blo 2025435 4557959 := bstep (se 1 (by rfl) ⟨3418469, by rfl⟩ : syracuseStep 4557959 = 6836939) B6836939
theorem B3038639 : Blo 2025435 3038639 := bstep (se 1 (by rfl) ⟨2278979, by rfl⟩ : syracuseStep 3038639 = 4557959) B4557959
theorem B2025759 : Blo 2025435 2025759 := bstep (se 1 (by rfl) ⟨1519319, by rfl⟩ : syracuseStep 2025759 = 3038639) B3038639
theorem B3038645 : Blo 2025435 3038645 := bbase (se 5 (by rfl) ⟨142436, by rfl⟩ : syracuseStep 3038645 = 284873) (by norm_num)
theorem B2025763 : Blo 2025435 2025763 := bstep (se 1 (by rfl) ⟨1519322, by rfl⟩ : syracuseStep 2025763 = 3038645) B3038645
theorem B5127725 : Blo 2025435 5127725 := bbase (se 3 (by rfl) ⟨961448, by rfl⟩ : syracuseStep 5127725 = 1922897) (by norm_num)
theorem B3418483 : Blo 2025435 3418483 := bstep (se 1 (by rfl) ⟨2563862, by rfl⟩ : syracuseStep 3418483 = 5127725) B5127725
theorem B4557977 : Blo 2025435 4557977 := bstep (se 2 (by rfl) ⟨1709241, by rfl⟩ : syracuseStep 4557977 = 3418483) B3418483
theorem B3038651 : Blo 2025435 3038651 := bstep (se 1 (by rfl) ⟨2278988, by rfl⟩ : syracuseStep 3038651 = 4557977) B4557977
theorem B2025767 : Blo 2025435 2025767 := bstep (se 1 (by rfl) ⟨1519325, by rfl⟩ : syracuseStep 2025767 = 3038651) B3038651
theorem B2278993 : Blo 2025435 2278993 := bbase (se 2 (by rfl) ⟨854622, by rfl⟩ : syracuseStep 2278993 = 1709245) (by norm_num)
theorem B3038657 : Blo 2025435 3038657 := bstep (se 2 (by rfl) ⟨1139496, by rfl⟩ : syracuseStep 3038657 = 2278993) B2278993
theorem B2025771 : Blo 2025435 2025771 := bstep (se 1 (by rfl) ⟨1519328, by rfl⟩ : syracuseStep 2025771 = 3038657) B3038657
theorem B2884357 : Blo 2025435 2884357 := bbase (se 4 (by rfl) ⟨270408, by rfl⟩ : syracuseStep 2884357 = 540817) (by norm_num)
theorem B3845809 : Blo 2025435 3845809 := bstep (se 2 (by rfl) ⟨1442178, by rfl⟩ : syracuseStep 3845809 = 2884357) B2884357
theorem B5127745 : Blo 2025435 5127745 := bstep (se 2 (by rfl) ⟨1922904, by rfl⟩ : syracuseStep 5127745 = 3845809) B3845809
theorem B6836993 : Blo 2025435 6836993 := bstep (se 2 (by rfl) ⟨2563872, by rfl⟩ : syracuseStep 6836993 = 5127745) B5127745
theorem B4557995 : Blo 2025435 4557995 := bstep (se 1 (by rfl) ⟨3418496, by rfl⟩ : syracuseStep 4557995 = 6836993) B6836993
theorem B3038663 : Blo 2025435 3038663 := bstep (se 1 (by rfl) ⟨2278997, by rfl⟩ : syracuseStep 3038663 = 4557995) B4557995
theorem B2025775 : Blo 2025435 2025775 := bstep (se 1 (by rfl) ⟨1519331, by rfl⟩ : syracuseStep 2025775 = 3038663) B3038663
theorem B3038669 : Blo 2025435 3038669 := bbase (se 3 (by rfl) ⟨569750, by rfl⟩ : syracuseStep 3038669 = 1139501) (by norm_num)
theorem B2025779 : Blo 2025435 2025779 := bstep (se 1 (by rfl) ⟨1519334, by rfl⟩ : syracuseStep 2025779 = 3038669) B3038669
theorem B4558013 : Blo 2025435 4558013 := bbase (se 3 (by rfl) ⟨854627, by rfl⟩ : syracuseStep 4558013 = 1709255) (by norm_num)
theorem B3038675 : Blo 2025435 3038675 := bstep (se 1 (by rfl) ⟨2279006, by rfl⟩ : syracuseStep 3038675 = 4558013) B4558013
theorem B2025783 : Blo 2025435 2025783 := bstep (se 1 (by rfl) ⟨1519337, by rfl⟩ : syracuseStep 2025783 = 3038675) B3038675
theorem B3418517 : Blo 2025435 3418517 := bbase (se 6 (by rfl) ⟨80121, by rfl⟩ : syracuseStep 3418517 = 160243) (by norm_num)
theorem B2279011 : Blo 2025435 2279011 := bstep (se 1 (by rfl) ⟨1709258, by rfl⟩ : syracuseStep 2279011 = 3418517) B3418517
theorem B3038681 : Blo 2025435 3038681 := bstep (se 2 (by rfl) ⟨1139505, by rfl⟩ : syracuseStep 3038681 = 2279011) B2279011
theorem B2025787 : Blo 2025435 2025787 := bstep (se 1 (by rfl) ⟨1519340, by rfl⟩ : syracuseStep 2025787 = 3038681) B3038681
theorem B2923733 : Blo 2025435 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B7796621 : Blo 2025435 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B20790989 : Blo 2025435 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B13860659 : Blo 2025435 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B36961757 : Blo 2025435 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B24641171 : Blo 2025435 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B16427447 : Blo 2025435 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B10951631 : Blo 2025435 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B7301087 : Blo 2025435 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B4867391 : Blo 2025435 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B12979709 : Blo 2025435 12979709 := bstep (se 3 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 12979709 = 4867391) B4867391
theorem B8653139 : Blo 2025435 8653139 := bstep (se 1 (by rfl) ⟨6489854, by rfl⟩ : syracuseStep 8653139 = 12979709) B12979709
theorem B5768759 : Blo 2025435 5768759 := bstep (se 1 (by rfl) ⟨4326569, by rfl⟩ : syracuseStep 5768759 = 8653139) B8653139
theorem B15383357 : Blo 2025435 15383357 := bstep (se 3 (by rfl) ⟨2884379, by rfl⟩ : syracuseStep 15383357 = 5768759) B5768759
theorem B10255571 : Blo 2025435 10255571 := bstep (se 1 (by rfl) ⟨7691678, by rfl⟩ : syracuseStep 10255571 = 15383357) B15383357
theorem B6837047 : Blo 2025435 6837047 := bstep (se 1 (by rfl) ⟨5127785, by rfl⟩ : syracuseStep 6837047 = 10255571) B10255571
theorem B4558031 : Blo 2025435 4558031 := bstep (se 1 (by rfl) ⟨3418523, by rfl⟩ : syracuseStep 4558031 = 6837047) B6837047
theorem B3038687 : Blo 2025435 3038687 := bstep (se 1 (by rfl) ⟨2279015, by rfl⟩ : syracuseStep 3038687 = 4558031) B4558031
theorem B2025791 : Blo 2025435 2025791 := bstep (se 1 (by rfl) ⟨1519343, by rfl⟩ : syracuseStep 2025791 = 3038687) B3038687
theorem B3038693 : Blo 2025435 3038693 := bbase (se 4 (by rfl) ⟨284877, by rfl⟩ : syracuseStep 3038693 = 569755) (by norm_num)
theorem B2025795 : Blo 2025435 2025795 := bstep (se 1 (by rfl) ⟨1519346, by rfl⟩ : syracuseStep 2025795 = 3038693) B3038693
theorem B7217909 : Blo 2025435 7217909 := bbase (se 5 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 7217909 = 676679) (by norm_num)
theorem B4811939 : Blo 2025435 4811939 := bstep (se 1 (by rfl) ⟨3608954, by rfl⟩ : syracuseStep 4811939 = 7217909) B7217909
theorem B3207959 : Blo 2025435 3207959 := bstep (se 1 (by rfl) ⟨2405969, by rfl⟩ : syracuseStep 3207959 = 4811939) B4811939
theorem B136872917 : Blo 2025435 136872917 := bstep (se 7 (by rfl) ⟨1603979, by rfl⟩ : syracuseStep 136872917 = 3207959) B3207959
theorem B91248611 : Blo 2025435 91248611 := bstep (se 1 (by rfl) ⟨68436458, by rfl⟩ : syracuseStep 91248611 = 136872917) B136872917
theorem B243329629 : Blo 2025435 243329629 := bstep (se 3 (by rfl) ⟨45624305, by rfl⟩ : syracuseStep 243329629 = 91248611) B91248611
theorem B324439505 : Blo 2025435 324439505 := bstep (se 2 (by rfl) ⟨121664814, by rfl⟩ : syracuseStep 324439505 = 243329629) B243329629
theorem B216293003 : Blo 2025435 216293003 := bstep (se 1 (by rfl) ⟨162219752, by rfl⟩ : syracuseStep 216293003 = 324439505) B324439505
theorem B144195335 : Blo 2025435 144195335 := bstep (se 1 (by rfl) ⟨108146501, by rfl⟩ : syracuseStep 144195335 = 216293003) B216293003
theorem B96130223 : Blo 2025435 96130223 := bstep (se 1 (by rfl) ⟨72097667, by rfl⟩ : syracuseStep 96130223 = 144195335) B144195335
theorem B64086815 : Blo 2025435 64086815 := bstep (se 1 (by rfl) ⟨48065111, by rfl⟩ : syracuseStep 64086815 = 96130223) B96130223
theorem B170898173 : Blo 2025435 170898173 := bstep (se 3 (by rfl) ⟨32043407, by rfl⟩ : syracuseStep 170898173 = 64086815) B64086815
theorem B113932115 : Blo 2025435 113932115 := bstep (se 1 (by rfl) ⟨85449086, by rfl⟩ : syracuseStep 113932115 = 170898173) B170898173
theorem B75954743 : Blo 2025435 75954743 := bstep (se 1 (by rfl) ⟨56966057, by rfl⟩ : syracuseStep 75954743 = 113932115) B113932115
theorem B50636495 : Blo 2025435 50636495 := bstep (se 1 (by rfl) ⟨37977371, by rfl⟩ : syracuseStep 50636495 = 75954743) B75954743
theorem B33757663 : Blo 2025435 33757663 := bstep (se 1 (by rfl) ⟨25318247, by rfl⟩ : syracuseStep 33757663 = 50636495) B50636495
theorem B45010217 : Blo 2025435 45010217 := bstep (se 2 (by rfl) ⟨16878831, by rfl⟩ : syracuseStep 45010217 = 33757663) B33757663
theorem B30006811 : Blo 2025435 30006811 := bstep (se 1 (by rfl) ⟨22505108, by rfl⟩ : syracuseStep 30006811 = 45010217) B45010217
theorem B40009081 : Blo 2025435 40009081 := bstep (se 2 (by rfl) ⟨15003405, by rfl⟩ : syracuseStep 40009081 = 30006811) B30006811
theorem B53345441 : Blo 2025435 53345441 := bstep (se 2 (by rfl) ⟨20004540, by rfl⟩ : syracuseStep 53345441 = 40009081) B40009081
theorem B35563627 : Blo 2025435 35563627 := bstep (se 1 (by rfl) ⟨26672720, by rfl⟩ : syracuseStep 35563627 = 53345441) B53345441
theorem B47418169 : Blo 2025435 47418169 := bstep (se 2 (by rfl) ⟨17781813, by rfl⟩ : syracuseStep 47418169 = 35563627) B35563627
theorem B63224225 : Blo 2025435 63224225 := bstep (se 2 (by rfl) ⟨23709084, by rfl⟩ : syracuseStep 63224225 = 47418169) B47418169
theorem B42149483 : Blo 2025435 42149483 := bstep (se 1 (by rfl) ⟨31612112, by rfl⟩ : syracuseStep 42149483 = 63224225) B63224225
theorem B28099655 : Blo 2025435 28099655 := bstep (se 1 (by rfl) ⟨21074741, by rfl⟩ : syracuseStep 28099655 = 42149483) B42149483
theorem B18733103 : Blo 2025435 18733103 := bstep (se 1 (by rfl) ⟨14049827, by rfl⟩ : syracuseStep 18733103 = 28099655) B28099655
theorem B12488735 : Blo 2025435 12488735 := bstep (se 1 (by rfl) ⟨9366551, by rfl⟩ : syracuseStep 12488735 = 18733103) B18733103
theorem B8325823 : Blo 2025435 8325823 := bstep (se 1 (by rfl) ⟨6244367, by rfl⟩ : syracuseStep 8325823 = 12488735) B12488735
theorem B11101097 : Blo 2025435 11101097 := bstep (se 2 (by rfl) ⟨4162911, by rfl⟩ : syracuseStep 11101097 = 8325823) B8325823
theorem B29602925 : Blo 2025435 29602925 := bstep (se 3 (by rfl) ⟨5550548, by rfl⟩ : syracuseStep 29602925 = 11101097) B11101097
theorem B19735283 : Blo 2025435 19735283 := bstep (se 1 (by rfl) ⟨14801462, by rfl⟩ : syracuseStep 19735283 = 29602925) B29602925
theorem B52627421 : Blo 2025435 52627421 := bstep (se 3 (by rfl) ⟨9867641, by rfl⟩ : syracuseStep 52627421 = 19735283) B19735283
theorem B35084947 : Blo 2025435 35084947 := bstep (se 1 (by rfl) ⟨26313710, by rfl⟩ : syracuseStep 35084947 = 52627421) B52627421
theorem B46779929 : Blo 2025435 46779929 := bstep (se 2 (by rfl) ⟨17542473, by rfl⟩ : syracuseStep 46779929 = 35084947) B35084947
theorem B31186619 : Blo 2025435 31186619 := bstep (se 1 (by rfl) ⟨23389964, by rfl⟩ : syracuseStep 31186619 = 46779929) B46779929
theorem B20791079 : Blo 2025435 20791079 := bstep (se 1 (by rfl) ⟨15593309, by rfl⟩ : syracuseStep 20791079 = 31186619) B31186619
theorem B13860719 : Blo 2025435 13860719 := bstep (se 1 (by rfl) ⟨10395539, by rfl⟩ : syracuseStep 13860719 = 20791079) B20791079
theorem B9240479 : Blo 2025435 9240479 := bstep (se 1 (by rfl) ⟨6930359, by rfl⟩ : syracuseStep 9240479 = 13860719) B13860719
theorem B6160319 : Blo 2025435 6160319 := bstep (se 1 (by rfl) ⟨4620239, by rfl⟩ : syracuseStep 6160319 = 9240479) B9240479
theorem B4106879 : Blo 2025435 4106879 := bstep (se 1 (by rfl) ⟨3080159, by rfl⟩ : syracuseStep 4106879 = 6160319) B6160319
theorem B2737919 : Blo 2025435 2737919 := bstep (se 1 (by rfl) ⟨2053439, by rfl⟩ : syracuseStep 2737919 = 4106879) B4106879
theorem B7301117 : Blo 2025435 7301117 := bstep (se 3 (by rfl) ⟨1368959, by rfl⟩ : syracuseStep 7301117 = 2737919) B2737919
theorem B19469645 : Blo 2025435 19469645 := bstep (se 3 (by rfl) ⟨3650558, by rfl⟩ : syracuseStep 19469645 = 7301117) B7301117
theorem B12979763 : Blo 2025435 12979763 := bstep (se 1 (by rfl) ⟨9734822, by rfl⟩ : syracuseStep 12979763 = 19469645) B19469645
theorem B8653175 : Blo 2025435 8653175 := bstep (se 1 (by rfl) ⟨6489881, by rfl⟩ : syracuseStep 8653175 = 12979763) B12979763
theorem B5768783 : Blo 2025435 5768783 := bstep (se 1 (by rfl) ⟨4326587, by rfl⟩ : syracuseStep 5768783 = 8653175) B8653175
theorem B3845855 : Blo 2025435 3845855 := bstep (se 1 (by rfl) ⟨2884391, by rfl⟩ : syracuseStep 3845855 = 5768783) B5768783
theorem B2563903 : Blo 2025435 2563903 := bstep (se 1 (by rfl) ⟨1922927, by rfl⟩ : syracuseStep 2563903 = 3845855) B3845855
theorem B3418537 : Blo 2025435 3418537 := bstep (se 2 (by rfl) ⟨1281951, by rfl⟩ : syracuseStep 3418537 = 2563903) B2563903
theorem B4558049 : Blo 2025435 4558049 := bstep (se 2 (by rfl) ⟨1709268, by rfl⟩ : syracuseStep 4558049 = 3418537) B3418537
theorem B3038699 : Blo 2025435 3038699 := bstep (se 1 (by rfl) ⟨2279024, by rfl⟩ : syracuseStep 3038699 = 4558049) B4558049
theorem B2025799 : Blo 2025435 2025799 := bstep (se 1 (by rfl) ⟨1519349, by rfl⟩ : syracuseStep 2025799 = 3038699) B3038699
theorem B2279029 : Blo 2025435 2279029 := bbase (se 5 (by rfl) ⟨106829, by rfl⟩ : syracuseStep 2279029 = 213659) (by norm_num)
theorem B3038705 : Blo 2025435 3038705 := bstep (se 2 (by rfl) ⟨1139514, by rfl⟩ : syracuseStep 3038705 = 2279029) B2279029
theorem B2025803 : Blo 2025435 2025803 := bstep (se 1 (by rfl) ⟨1519352, by rfl⟩ : syracuseStep 2025803 = 3038705) B3038705
theorem B2563913 : Blo 2025435 2563913 := bbase (se 2 (by rfl) ⟨961467, by rfl⟩ : syracuseStep 2563913 = 1922935) (by norm_num)
theorem B6837101 : Blo 2025435 6837101 := bstep (se 3 (by rfl) ⟨1281956, by rfl⟩ : syracuseStep 6837101 = 2563913) B2563913
theorem B4558067 : Blo 2025435 4558067 := bstep (se 1 (by rfl) ⟨3418550, by rfl⟩ : syracuseStep 4558067 = 6837101) B6837101
theorem B3038711 : Blo 2025435 3038711 := bstep (se 1 (by rfl) ⟨2279033, by rfl⟩ : syracuseStep 3038711 = 4558067) B4558067
theorem B2025807 : Blo 2025435 2025807 := bstep (se 1 (by rfl) ⟨1519355, by rfl⟩ : syracuseStep 2025807 = 3038711) B3038711
theorem B3038717 : Blo 2025435 3038717 := bbase (se 3 (by rfl) ⟨569759, by rfl⟩ : syracuseStep 3038717 = 1139519) (by norm_num)
theorem B2025811 : Blo 2025435 2025811 := bstep (se 1 (by rfl) ⟨1519358, by rfl⟩ : syracuseStep 2025811 = 3038717) B3038717
theorem B4558085 : Blo 2025435 4558085 := bbase (se 4 (by rfl) ⟨427320, by rfl⟩ : syracuseStep 4558085 = 854641) (by norm_num)
theorem B3038723 : Blo 2025435 3038723 := bstep (se 1 (by rfl) ⟨2279042, by rfl⟩ : syracuseStep 3038723 = 4558085) B4558085
theorem B2025815 : Blo 2025435 2025815 := bstep (se 1 (by rfl) ⟨1519361, by rfl⟩ : syracuseStep 2025815 = 3038723) B3038723
theorem B3845893 : Blo 2025435 3845893 := bbase (se 4 (by rfl) ⟨360552, by rfl⟩ : syracuseStep 3845893 = 721105) (by norm_num)
theorem B5127857 : Blo 2025435 5127857 := bstep (se 2 (by rfl) ⟨1922946, by rfl⟩ : syracuseStep 5127857 = 3845893) B3845893
theorem B3418571 : Blo 2025435 3418571 := bstep (se 1 (by rfl) ⟨2563928, by rfl⟩ : syracuseStep 3418571 = 5127857) B5127857
theorem B2279047 : Blo 2025435 2279047 := bstep (se 1 (by rfl) ⟨1709285, by rfl⟩ : syracuseStep 2279047 = 3418571) B3418571
theorem B3038729 : Blo 2025435 3038729 := bstep (se 2 (by rfl) ⟨1139523, by rfl⟩ : syracuseStep 3038729 = 2279047) B2279047
theorem B2025819 : Blo 2025435 2025819 := bstep (se 1 (by rfl) ⟨1519364, by rfl⟩ : syracuseStep 2025819 = 3038729) B3038729
theorem B10255733 : Blo 2025435 10255733 := bbase (se 5 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 10255733 = 961475) (by norm_num)
theorem B6837155 : Blo 2025435 6837155 := bstep (se 1 (by rfl) ⟨5127866, by rfl⟩ : syracuseStep 6837155 = 10255733) B10255733
theorem B4558103 : Blo 2025435 4558103 := bstep (se 1 (by rfl) ⟨3418577, by rfl⟩ : syracuseStep 4558103 = 6837155) B6837155
theorem B3038735 : Blo 2025435 3038735 := bstep (se 1 (by rfl) ⟨2279051, by rfl⟩ : syracuseStep 3038735 = 4558103) B4558103
theorem B2025823 : Blo 2025435 2025823 := bstep (se 1 (by rfl) ⟨1519367, by rfl⟩ : syracuseStep 2025823 = 3038735) B3038735
theorem B3038741 : Blo 2025435 3038741 := bbase (se 6 (by rfl) ⟨71220, by rfl⟩ : syracuseStep 3038741 = 142441) (by norm_num)
theorem B2025827 : Blo 2025435 2025827 := bstep (se 1 (by rfl) ⟨1519370, by rfl⟩ : syracuseStep 2025827 = 3038741) B3038741
theorem B10827029 : Blo 2025435 10827029 := bbase (se 6 (by rfl) ⟨253758, by rfl⟩ : syracuseStep 10827029 = 507517) (by norm_num)
theorem B7218019 : Blo 2025435 7218019 := bstep (se 1 (by rfl) ⟨5413514, by rfl⟩ : syracuseStep 7218019 = 10827029) B10827029
theorem B9624025 : Blo 2025435 9624025 := bstep (se 2 (by rfl) ⟨3609009, by rfl⟩ : syracuseStep 9624025 = 7218019) B7218019
theorem B12832033 : Blo 2025435 12832033 := bstep (se 2 (by rfl) ⟨4812012, by rfl⟩ : syracuseStep 12832033 = 9624025) B9624025
theorem B17109377 : Blo 2025435 17109377 := bstep (se 2 (by rfl) ⟨6416016, by rfl⟩ : syracuseStep 17109377 = 12832033) B12832033
theorem B11406251 : Blo 2025435 11406251 := bstep (se 1 (by rfl) ⟨8554688, by rfl⟩ : syracuseStep 11406251 = 17109377) B17109377
theorem B7604167 : Blo 2025435 7604167 := bstep (se 1 (by rfl) ⟨5703125, by rfl⟩ : syracuseStep 7604167 = 11406251) B11406251
theorem B10138889 : Blo 2025435 10138889 := bstep (se 2 (by rfl) ⟨3802083, by rfl⟩ : syracuseStep 10138889 = 7604167) B7604167
theorem B27037037 : Blo 2025435 27037037 := bstep (se 3 (by rfl) ⟨5069444, by rfl⟩ : syracuseStep 27037037 = 10138889) B10138889
theorem B72098765 : Blo 2025435 72098765 := bstep (se 3 (by rfl) ⟨13518518, by rfl⟩ : syracuseStep 72098765 = 27037037) B27037037
theorem B48065843 : Blo 2025435 48065843 := bstep (se 1 (by rfl) ⟨36049382, by rfl⟩ : syracuseStep 48065843 = 72098765) B72098765
theorem B128175581 : Blo 2025435 128175581 := bstep (se 3 (by rfl) ⟨24032921, by rfl⟩ : syracuseStep 128175581 = 48065843) B48065843
theorem B341801549 : Blo 2025435 341801549 := bstep (se 3 (by rfl) ⟨64087790, by rfl⟩ : syracuseStep 341801549 = 128175581) B128175581
theorem B227867699 : Blo 2025435 227867699 := bstep (se 1 (by rfl) ⟨170900774, by rfl⟩ : syracuseStep 227867699 = 341801549) B341801549
theorem B607647197 : Blo 2025435 607647197 := bstep (se 3 (by rfl) ⟨113933849, by rfl⟩ : syracuseStep 607647197 = 227867699) B227867699
theorem B405098131 : Blo 2025435 405098131 := bstep (se 1 (by rfl) ⟨303823598, by rfl⟩ : syracuseStep 405098131 = 607647197) B607647197
theorem B540130841 : Blo 2025435 540130841 := bstep (se 2 (by rfl) ⟨202549065, by rfl⟩ : syracuseStep 540130841 = 405098131) B405098131
theorem B360087227 : Blo 2025435 360087227 := bstep (se 1 (by rfl) ⟨270065420, by rfl⟩ : syracuseStep 360087227 = 540130841) B540130841
theorem B240058151 : Blo 2025435 240058151 := bstep (se 1 (by rfl) ⟨180043613, by rfl⟩ : syracuseStep 240058151 = 360087227) B360087227
theorem B160038767 : Blo 2025435 160038767 := bstep (se 1 (by rfl) ⟨120029075, by rfl⟩ : syracuseStep 160038767 = 240058151) B240058151
theorem B106692511 : Blo 2025435 106692511 := bstep (se 1 (by rfl) ⟨80019383, by rfl⟩ : syracuseStep 106692511 = 160038767) B160038767
theorem B142256681 : Blo 2025435 142256681 := bstep (se 2 (by rfl) ⟨53346255, by rfl⟩ : syracuseStep 142256681 = 106692511) B106692511
theorem B94837787 : Blo 2025435 94837787 := bstep (se 1 (by rfl) ⟨71128340, by rfl⟩ : syracuseStep 94837787 = 142256681) B142256681
theorem B63225191 : Blo 2025435 63225191 := bstep (se 1 (by rfl) ⟨47418893, by rfl⟩ : syracuseStep 63225191 = 94837787) B94837787
theorem B42150127 : Blo 2025435 42150127 := bstep (se 1 (by rfl) ⟨31612595, by rfl⟩ : syracuseStep 42150127 = 63225191) B63225191
theorem B56200169 : Blo 2025435 56200169 := bstep (se 2 (by rfl) ⟨21075063, by rfl⟩ : syracuseStep 56200169 = 42150127) B42150127
theorem B37466779 : Blo 2025435 37466779 := bstep (se 1 (by rfl) ⟨28100084, by rfl⟩ : syracuseStep 37466779 = 56200169) B56200169
theorem B49955705 : Blo 2025435 49955705 := bstep (se 2 (by rfl) ⟨18733389, by rfl⟩ : syracuseStep 49955705 = 37466779) B37466779
theorem B33303803 : Blo 2025435 33303803 := bstep (se 1 (by rfl) ⟨24977852, by rfl⟩ : syracuseStep 33303803 = 49955705) B49955705
theorem B88810141 : Blo 2025435 88810141 := bstep (se 3 (by rfl) ⟨16651901, by rfl⟩ : syracuseStep 88810141 = 33303803) B33303803
theorem B118413521 : Blo 2025435 118413521 := bstep (se 2 (by rfl) ⟨44405070, by rfl⟩ : syracuseStep 118413521 = 88810141) B88810141
theorem B78942347 : Blo 2025435 78942347 := bstep (se 1 (by rfl) ⟨59206760, by rfl⟩ : syracuseStep 78942347 = 118413521) B118413521
theorem B52628231 : Blo 2025435 52628231 := bstep (se 1 (by rfl) ⟨39471173, by rfl⟩ : syracuseStep 52628231 = 78942347) B78942347
theorem B35085487 : Blo 2025435 35085487 := bstep (se 1 (by rfl) ⟨26314115, by rfl⟩ : syracuseStep 35085487 = 52628231) B52628231
theorem B46780649 : Blo 2025435 46780649 := bstep (se 2 (by rfl) ⟨17542743, by rfl⟩ : syracuseStep 46780649 = 35085487) B35085487
theorem B31187099 : Blo 2025435 31187099 := bstep (se 1 (by rfl) ⟨23390324, by rfl⟩ : syracuseStep 31187099 = 46780649) B46780649
theorem B20791399 : Blo 2025435 20791399 := bstep (se 1 (by rfl) ⟨15593549, by rfl⟩ : syracuseStep 20791399 = 31187099) B31187099
theorem B27721865 : Blo 2025435 27721865 := bstep (se 2 (by rfl) ⟨10395699, by rfl⟩ : syracuseStep 27721865 = 20791399) B20791399
theorem B73924973 : Blo 2025435 73924973 := bstep (se 3 (by rfl) ⟨13860932, by rfl⟩ : syracuseStep 73924973 = 27721865) B27721865
theorem B49283315 : Blo 2025435 49283315 := bstep (se 1 (by rfl) ⟨36962486, by rfl⟩ : syracuseStep 49283315 = 73924973) B73924973
theorem B32855543 : Blo 2025435 32855543 := bstep (se 1 (by rfl) ⟨24641657, by rfl⟩ : syracuseStep 32855543 = 49283315) B49283315
theorem B21903695 : Blo 2025435 21903695 := bstep (se 1 (by rfl) ⟨16427771, by rfl⟩ : syracuseStep 21903695 = 32855543) B32855543
theorem B14602463 : Blo 2025435 14602463 := bstep (se 1 (by rfl) ⟨10951847, by rfl⟩ : syracuseStep 14602463 = 21903695) B21903695
theorem B9734975 : Blo 2025435 9734975 := bstep (se 1 (by rfl) ⟨7301231, by rfl⟩ : syracuseStep 9734975 = 14602463) B14602463
theorem B6489983 : Blo 2025435 6489983 := bstep (se 1 (by rfl) ⟨4867487, by rfl⟩ : syracuseStep 6489983 = 9734975) B9734975
theorem B17306621 : Blo 2025435 17306621 := bstep (se 3 (by rfl) ⟨3244991, by rfl⟩ : syracuseStep 17306621 = 6489983) B6489983
theorem B11537747 : Blo 2025435 11537747 := bstep (se 1 (by rfl) ⟨8653310, by rfl⟩ : syracuseStep 11537747 = 17306621) B17306621
theorem B7691831 : Blo 2025435 7691831 := bstep (se 1 (by rfl) ⟨5768873, by rfl⟩ : syracuseStep 7691831 = 11537747) B11537747
theorem B5127887 : Blo 2025435 5127887 := bstep (se 1 (by rfl) ⟨3845915, by rfl⟩ : syracuseStep 5127887 = 7691831) B7691831
theorem B3418591 : Blo 2025435 3418591 := bstep (se 1 (by rfl) ⟨2563943, by rfl⟩ : syracuseStep 3418591 = 5127887) B5127887
theorem B4558121 : Blo 2025435 4558121 := bstep (se 2 (by rfl) ⟨1709295, by rfl⟩ : syracuseStep 4558121 = 3418591) B3418591
theorem B3038747 : Blo 2025435 3038747 := bstep (se 1 (by rfl) ⟨2279060, by rfl⟩ : syracuseStep 3038747 = 4558121) B4558121
theorem B2025831 : Blo 2025435 2025831 := bstep (se 1 (by rfl) ⟨1519373, by rfl⟩ : syracuseStep 2025831 = 3038747) B3038747
theorem B2279065 : Blo 2025435 2279065 := bbase (se 2 (by rfl) ⟨854649, by rfl⟩ : syracuseStep 2279065 = 1709299) (by norm_num)
theorem B3038753 : Blo 2025435 3038753 := bstep (se 2 (by rfl) ⟨1139532, by rfl⟩ : syracuseStep 3038753 = 2279065) B2279065
theorem B2025835 : Blo 2025435 2025835 := bstep (se 1 (by rfl) ⟨1519376, by rfl⟩ : syracuseStep 2025835 = 3038753) B3038753
theorem B7691861 : Blo 2025435 7691861 := bbase (se 8 (by rfl) ⟨45069, by rfl⟩ : syracuseStep 7691861 = 90139) (by norm_num)
theorem B5127907 : Blo 2025435 5127907 := bstep (se 1 (by rfl) ⟨3845930, by rfl⟩ : syracuseStep 5127907 = 7691861) B7691861
theorem B6837209 : Blo 2025435 6837209 := bstep (se 2 (by rfl) ⟨2563953, by rfl⟩ : syracuseStep 6837209 = 5127907) B5127907
theorem B4558139 : Blo 2025435 4558139 := bstep (se 1 (by rfl) ⟨3418604, by rfl⟩ : syracuseStep 4558139 = 6837209) B6837209
theorem B3038759 : Blo 2025435 3038759 := bstep (se 1 (by rfl) ⟨2279069, by rfl⟩ : syracuseStep 3038759 = 4558139) B4558139
theorem B2025839 : Blo 2025435 2025839 := bstep (se 1 (by rfl) ⟨1519379, by rfl⟩ : syracuseStep 2025839 = 3038759) B3038759
theorem B3038765 : Blo 2025435 3038765 := bbase (se 3 (by rfl) ⟨569768, by rfl⟩ : syracuseStep 3038765 = 1139537) (by norm_num)
theorem B2025843 : Blo 2025435 2025843 := bstep (se 1 (by rfl) ⟨1519382, by rfl⟩ : syracuseStep 2025843 = 3038765) B3038765
theorem B4558157 : Blo 2025435 4558157 := bbase (se 3 (by rfl) ⟨854654, by rfl⟩ : syracuseStep 4558157 = 1709309) (by norm_num)
theorem B3038771 : Blo 2025435 3038771 := bstep (se 1 (by rfl) ⟨2279078, by rfl⟩ : syracuseStep 3038771 = 4558157) B4558157
theorem B2025847 : Blo 2025435 2025847 := bstep (se 1 (by rfl) ⟨1519385, by rfl⟩ : syracuseStep 2025847 = 3038771) B3038771
theorem B2563969 : Blo 2025435 2563969 := bbase (se 2 (by rfl) ⟨961488, by rfl⟩ : syracuseStep 2563969 = 1922977) (by norm_num)
theorem B3418625 : Blo 2025435 3418625 := bstep (se 2 (by rfl) ⟨1281984, by rfl⟩ : syracuseStep 3418625 = 2563969) B2563969
theorem B2279083 : Blo 2025435 2279083 := bstep (se 1 (by rfl) ⟨1709312, by rfl⟩ : syracuseStep 2279083 = 3418625) B3418625
theorem B3038777 : Blo 2025435 3038777 := bstep (se 2 (by rfl) ⟨1139541, by rfl⟩ : syracuseStep 3038777 = 2279083) B2279083
theorem B2025851 : Blo 2025435 2025851 := bstep (se 1 (by rfl) ⟨1519388, by rfl⟩ : syracuseStep 2025851 = 3038777) B3038777
theorem B2163353 : Blo 2025435 2163353 := bbase (se 2 (by rfl) ⟨811257, by rfl⟩ : syracuseStep 2163353 = 1622515) (by norm_num)
theorem B23075765 : Blo 2025435 23075765 := bstep (se 5 (by rfl) ⟨1081676, by rfl⟩ : syracuseStep 23075765 = 2163353) B2163353
theorem B15383843 : Blo 2025435 15383843 := bstep (se 1 (by rfl) ⟨11537882, by rfl⟩ : syracuseStep 15383843 = 23075765) B23075765
theorem B10255895 : Blo 2025435 10255895 := bstep (se 1 (by rfl) ⟨7691921, by rfl⟩ : syracuseStep 10255895 = 15383843) B15383843
theorem B6837263 : Blo 2025435 6837263 := bstep (se 1 (by rfl) ⟨5127947, by rfl⟩ : syracuseStep 6837263 = 10255895) B10255895
theorem B4558175 : Blo 2025435 4558175 := bstep (se 1 (by rfl) ⟨3418631, by rfl⟩ : syracuseStep 4558175 = 6837263) B6837263
theorem B3038783 : Blo 2025435 3038783 := bstep (se 1 (by rfl) ⟨2279087, by rfl⟩ : syracuseStep 3038783 = 4558175) B4558175
theorem B2025855 : Blo 2025435 2025855 := bstep (se 1 (by rfl) ⟨1519391, by rfl⟩ : syracuseStep 2025855 = 3038783) B3038783
theorem B3038789 : Blo 2025435 3038789 := bbase (se 4 (by rfl) ⟨284886, by rfl⟩ : syracuseStep 3038789 = 569773) (by norm_num)
theorem B2025859 : Blo 2025435 2025859 := bstep (se 1 (by rfl) ⟨1519394, by rfl⟩ : syracuseStep 2025859 = 3038789) B3038789
theorem B3418645 : Blo 2025435 3418645 := bbase (se 6 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 3418645 = 160249) (by norm_num)
theorem B4558193 : Blo 2025435 4558193 := bstep (se 2 (by rfl) ⟨1709322, by rfl⟩ : syracuseStep 4558193 = 3418645) B3418645
theorem B3038795 : Blo 2025435 3038795 := bstep (se 1 (by rfl) ⟨2279096, by rfl⟩ : syracuseStep 3038795 = 4558193) B4558193
theorem B2025863 : Blo 2025435 2025863 := bstep (se 1 (by rfl) ⟨1519397, by rfl⟩ : syracuseStep 2025863 = 3038795) B3038795
theorem B2279101 : Blo 2025435 2279101 := bbase (se 3 (by rfl) ⟨427331, by rfl⟩ : syracuseStep 2279101 = 854663) (by norm_num)
theorem B3038801 : Blo 2025435 3038801 := bstep (se 2 (by rfl) ⟨1139550, by rfl⟩ : syracuseStep 3038801 = 2279101) B2279101
theorem B2025867 : Blo 2025435 2025867 := bstep (se 1 (by rfl) ⟨1519400, by rfl⟩ : syracuseStep 2025867 = 3038801) B3038801
theorem B6837317 : Blo 2025435 6837317 := bbase (se 4 (by rfl) ⟨640998, by rfl⟩ : syracuseStep 6837317 = 1281997) (by norm_num)
theorem B4558211 : Blo 2025435 4558211 := bstep (se 1 (by rfl) ⟨3418658, by rfl⟩ : syracuseStep 4558211 = 6837317) B6837317
theorem B3038807 : Blo 2025435 3038807 := bstep (se 1 (by rfl) ⟨2279105, by rfl⟩ : syracuseStep 3038807 = 4558211) B4558211
theorem B2025871 : Blo 2025435 2025871 := bstep (se 1 (by rfl) ⟨1519403, by rfl⟩ : syracuseStep 2025871 = 3038807) B3038807
theorem B3038813 : Blo 2025435 3038813 := bbase (se 3 (by rfl) ⟨569777, by rfl⟩ : syracuseStep 3038813 = 1139555) (by norm_num)
theorem B2025875 : Blo 2025435 2025875 := bstep (se 1 (by rfl) ⟨1519406, by rfl⟩ : syracuseStep 2025875 = 3038813) B3038813
theorem B4558229 : Blo 2025435 4558229 := bbase (se 6 (by rfl) ⟨106833, by rfl⟩ : syracuseStep 4558229 = 213667) (by norm_num)
theorem B3038819 : Blo 2025435 3038819 := bstep (se 1 (by rfl) ⟨2279114, by rfl⟩ : syracuseStep 3038819 = 4558229) B4558229
theorem B2025879 : Blo 2025435 2025879 := bstep (se 1 (by rfl) ⟨1519409, by rfl⟩ : syracuseStep 2025879 = 3038819) B3038819
theorem B3512605 : Blo 2025435 3512605 := bbase (se 3 (by rfl) ⟨658613, by rfl⟩ : syracuseStep 3512605 = 1317227) (by norm_num)
theorem B4683473 : Blo 2025435 4683473 := bstep (se 2 (by rfl) ⟨1756302, by rfl⟩ : syracuseStep 4683473 = 3512605) B3512605
theorem B3122315 : Blo 2025435 3122315 := bstep (se 1 (by rfl) ⟨2341736, by rfl⟩ : syracuseStep 3122315 = 4683473) B4683473
theorem B2081543 : Blo 2025435 2081543 := bstep (se 1 (by rfl) ⟨1561157, by rfl⟩ : syracuseStep 2081543 = 3122315) B3122315
theorem B5550781 : Blo 2025435 5550781 := bstep (se 3 (by rfl) ⟨1040771, by rfl⟩ : syracuseStep 5550781 = 2081543) B2081543
theorem B7401041 : Blo 2025435 7401041 := bstep (se 2 (by rfl) ⟨2775390, by rfl⟩ : syracuseStep 7401041 = 5550781) B5550781
theorem B4934027 : Blo 2025435 4934027 := bstep (se 1 (by rfl) ⟨3700520, by rfl⟩ : syracuseStep 4934027 = 7401041) B7401041
theorem B3289351 : Blo 2025435 3289351 := bstep (se 1 (by rfl) ⟨2467013, by rfl⟩ : syracuseStep 3289351 = 4934027) B4934027
theorem B4385801 : Blo 2025435 4385801 := bstep (se 2 (by rfl) ⟨1644675, by rfl⟩ : syracuseStep 4385801 = 3289351) B3289351
theorem B2923867 : Blo 2025435 2923867 := bstep (se 1 (by rfl) ⟨2192900, by rfl⟩ : syracuseStep 2923867 = 4385801) B4385801
theorem B15593957 : Blo 2025435 15593957 := bstep (se 4 (by rfl) ⟨1461933, by rfl⟩ : syracuseStep 15593957 = 2923867) B2923867
theorem B10395971 : Blo 2025435 10395971 := bstep (se 1 (by rfl) ⟨7796978, by rfl⟩ : syracuseStep 10395971 = 15593957) B15593957
theorem B6930647 : Blo 2025435 6930647 := bstep (se 1 (by rfl) ⟨5197985, by rfl⟩ : syracuseStep 6930647 = 10395971) B10395971
theorem B4620431 : Blo 2025435 4620431 := bstep (se 1 (by rfl) ⟨3465323, by rfl⟩ : syracuseStep 4620431 = 6930647) B6930647
theorem B3080287 : Blo 2025435 3080287 := bstep (se 1 (by rfl) ⟨2310215, by rfl⟩ : syracuseStep 3080287 = 4620431) B4620431
theorem B16428197 : Blo 2025435 16428197 := bstep (se 4 (by rfl) ⟨1540143, by rfl⟩ : syracuseStep 16428197 = 3080287) B3080287
theorem B10952131 : Blo 2025435 10952131 := bstep (se 1 (by rfl) ⟨8214098, by rfl⟩ : syracuseStep 10952131 = 16428197) B16428197
theorem B14602841 : Blo 2025435 14602841 := bstep (se 2 (by rfl) ⟨5476065, by rfl⟩ : syracuseStep 14602841 = 10952131) B10952131
theorem B9735227 : Blo 2025435 9735227 := bstep (se 1 (by rfl) ⟨7301420, by rfl⟩ : syracuseStep 9735227 = 14602841) B14602841
theorem B6490151 : Blo 2025435 6490151 := bstep (se 1 (by rfl) ⟨4867613, by rfl⟩ : syracuseStep 6490151 = 9735227) B9735227
theorem B4326767 : Blo 2025435 4326767 := bstep (se 1 (by rfl) ⟨3245075, by rfl⟩ : syracuseStep 4326767 = 6490151) B6490151
theorem B2884511 : Blo 2025435 2884511 := bstep (se 1 (by rfl) ⟨2163383, by rfl⟩ : syracuseStep 2884511 = 4326767) B4326767
theorem B7692029 : Blo 2025435 7692029 := bstep (se 3 (by rfl) ⟨1442255, by rfl⟩ : syracuseStep 7692029 = 2884511) B2884511
theorem B5128019 : Blo 2025435 5128019 := bstep (se 1 (by rfl) ⟨3846014, by rfl⟩ : syracuseStep 5128019 = 7692029) B7692029
theorem B3418679 : Blo 2025435 3418679 := bstep (se 1 (by rfl) ⟨2564009, by rfl⟩ : syracuseStep 3418679 = 5128019) B5128019
theorem B2279119 : Blo 2025435 2279119 := bstep (se 1 (by rfl) ⟨1709339, by rfl⟩ : syracuseStep 2279119 = 3418679) B3418679
theorem B3038825 : Blo 2025435 3038825 := bstep (se 2 (by rfl) ⟨1139559, by rfl⟩ : syracuseStep 3038825 = 2279119) B2279119
theorem B2025883 : Blo 2025435 2025883 := bstep (se 1 (by rfl) ⟨1519412, by rfl⟩ : syracuseStep 2025883 = 3038825) B3038825
theorem B3650717 : Blo 2025435 3650717 := bbase (se 3 (by rfl) ⟨684509, by rfl⟩ : syracuseStep 3650717 = 1369019) (by norm_num)
theorem B2433811 : Blo 2025435 2433811 := bstep (se 1 (by rfl) ⟨1825358, by rfl⟩ : syracuseStep 2433811 = 3650717) B3650717
theorem B3245081 : Blo 2025435 3245081 := bstep (se 2 (by rfl) ⟨1216905, by rfl⟩ : syracuseStep 3245081 = 2433811) B2433811
theorem B8653549 : Blo 2025435 8653549 := bstep (se 3 (by rfl) ⟨1622540, by rfl⟩ : syracuseStep 8653549 = 3245081) B3245081
theorem B11538065 : Blo 2025435 11538065 := bstep (se 2 (by rfl) ⟨4326774, by rfl⟩ : syracuseStep 11538065 = 8653549) B8653549
theorem B7692043 : Blo 2025435 7692043 := bstep (se 1 (by rfl) ⟨5769032, by rfl⟩ : syracuseStep 7692043 = 11538065) B11538065
theorem B10256057 : Blo 2025435 10256057 := bstep (se 2 (by rfl) ⟨3846021, by rfl⟩ : syracuseStep 10256057 = 7692043) B7692043
theorem B6837371 : Blo 2025435 6837371 := bstep (se 1 (by rfl) ⟨5128028, by rfl⟩ : syracuseStep 6837371 = 10256057) B10256057
theorem B4558247 : Blo 2025435 4558247 := bstep (se 1 (by rfl) ⟨3418685, by rfl⟩ : syracuseStep 4558247 = 6837371) B6837371
theorem B3038831 : Blo 2025435 3038831 := bstep (se 1 (by rfl) ⟨2279123, by rfl⟩ : syracuseStep 3038831 = 4558247) B4558247
theorem B2025887 : Blo 2025435 2025887 := bstep (se 1 (by rfl) ⟨1519415, by rfl⟩ : syracuseStep 2025887 = 3038831) B3038831
theorem B3038837 : Blo 2025435 3038837 := bbase (se 5 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 3038837 = 284891) (by norm_num)
theorem B2025891 : Blo 2025435 2025891 := bstep (se 1 (by rfl) ⟨1519418, by rfl⟩ : syracuseStep 2025891 = 3038837) B3038837
theorem B3846037 : Blo 2025435 3846037 := bbase (se 6 (by rfl) ⟨90141, by rfl⟩ : syracuseStep 3846037 = 180283) (by norm_num)
theorem B5128049 : Blo 2025435 5128049 := bstep (se 2 (by rfl) ⟨1923018, by rfl⟩ : syracuseStep 5128049 = 3846037) B3846037
theorem B3418699 : Blo 2025435 3418699 := bstep (se 1 (by rfl) ⟨2564024, by rfl⟩ : syracuseStep 3418699 = 5128049) B5128049
theorem B4558265 : Blo 2025435 4558265 := bstep (se 2 (by rfl) ⟨1709349, by rfl⟩ : syracuseStep 4558265 = 3418699) B3418699
theorem B3038843 : Blo 2025435 3038843 := bstep (se 1 (by rfl) ⟨2279132, by rfl⟩ : syracuseStep 3038843 = 4558265) B4558265
theorem B2025895 : Blo 2025435 2025895 := bstep (se 1 (by rfl) ⟨1519421, by rfl⟩ : syracuseStep 2025895 = 3038843) B3038843
theorem B2279137 : Blo 2025435 2279137 := bbase (se 2 (by rfl) ⟨854676, by rfl⟩ : syracuseStep 2279137 = 1709353) (by norm_num)
theorem B3038849 : Blo 2025435 3038849 := bstep (se 2 (by rfl) ⟨1139568, by rfl⟩ : syracuseStep 3038849 = 2279137) B2279137
theorem B2025899 : Blo 2025435 2025899 := bstep (se 1 (by rfl) ⟨1519424, by rfl⟩ : syracuseStep 2025899 = 3038849) B3038849
theorem B5128069 : Blo 2025435 5128069 := bbase (se 4 (by rfl) ⟨480756, by rfl⟩ : syracuseStep 5128069 = 961513) (by norm_num)
theorem B6837425 : Blo 2025435 6837425 := bstep (se 2 (by rfl) ⟨2564034, by rfl⟩ : syracuseStep 6837425 = 5128069) B5128069
theorem B4558283 : Blo 2025435 4558283 := bstep (se 1 (by rfl) ⟨3418712, by rfl⟩ : syracuseStep 4558283 = 6837425) B6837425
theorem B3038855 : Blo 2025435 3038855 := bstep (se 1 (by rfl) ⟨2279141, by rfl⟩ : syracuseStep 3038855 = 4558283) B4558283
theorem B2025903 : Blo 2025435 2025903 := bstep (se 1 (by rfl) ⟨1519427, by rfl⟩ : syracuseStep 2025903 = 3038855) B3038855
theorem B3038861 : Blo 2025435 3038861 := bbase (se 3 (by rfl) ⟨569786, by rfl⟩ : syracuseStep 3038861 = 1139573) (by norm_num)
theorem B2025907 : Blo 2025435 2025907 := bstep (se 1 (by rfl) ⟨1519430, by rfl⟩ : syracuseStep 2025907 = 3038861) B3038861
theorem B4558301 : Blo 2025435 4558301 := bbase (se 3 (by rfl) ⟨854681, by rfl⟩ : syracuseStep 4558301 = 1709363) (by norm_num)
theorem B3038867 : Blo 2025435 3038867 := bstep (se 1 (by rfl) ⟨2279150, by rfl⟩ : syracuseStep 3038867 = 4558301) B4558301
theorem B2025911 : Blo 2025435 2025911 := bstep (se 1 (by rfl) ⟨1519433, by rfl⟩ : syracuseStep 2025911 = 3038867) B3038867
theorem B3418733 : Blo 2025435 3418733 := bbase (se 3 (by rfl) ⟨641012, by rfl⟩ : syracuseStep 3418733 = 1282025) (by norm_num)
theorem B2279155 : Blo 2025435 2279155 := bstep (se 1 (by rfl) ⟨1709366, by rfl⟩ : syracuseStep 2279155 = 3418733) B3418733
theorem B3038873 : Blo 2025435 3038873 := bstep (se 2 (by rfl) ⟨1139577, by rfl⟩ : syracuseStep 3038873 = 2279155) B2279155
theorem B2025915 : Blo 2025435 2025915 := bstep (se 1 (by rfl) ⟨1519436, by rfl⟩ : syracuseStep 2025915 = 3038873) B3038873
theorem B6759557 : Blo 2025435 6759557 := bbase (se 4 (by rfl) ⟨633708, by rfl⟩ : syracuseStep 6759557 = 1267417) (by norm_num)
theorem B4506371 : Blo 2025435 4506371 := bstep (se 1 (by rfl) ⟨3379778, by rfl⟩ : syracuseStep 4506371 = 6759557) B6759557
theorem B3004247 : Blo 2025435 3004247 := bstep (se 1 (by rfl) ⟨2253185, by rfl⟩ : syracuseStep 3004247 = 4506371) B4506371
theorem B8011325 : Blo 2025435 8011325 := bstep (se 3 (by rfl) ⟨1502123, by rfl⟩ : syracuseStep 8011325 = 3004247) B3004247
theorem B21363533 : Blo 2025435 21363533 := bstep (se 3 (by rfl) ⟨4005662, by rfl⟩ : syracuseStep 21363533 = 8011325) B8011325
theorem B14242355 : Blo 2025435 14242355 := bstep (se 1 (by rfl) ⟨10681766, by rfl⟩ : syracuseStep 14242355 = 21363533) B21363533
theorem B9494903 : Blo 2025435 9494903 := bstep (se 1 (by rfl) ⟨7121177, by rfl⟩ : syracuseStep 9494903 = 14242355) B14242355
theorem B6329935 : Blo 2025435 6329935 := bstep (se 1 (by rfl) ⟨4747451, by rfl⟩ : syracuseStep 6329935 = 9494903) B9494903
theorem B8439913 : Blo 2025435 8439913 := bstep (se 2 (by rfl) ⟨3164967, by rfl⟩ : syracuseStep 8439913 = 6329935) B6329935
theorem B11253217 : Blo 2025435 11253217 := bstep (se 2 (by rfl) ⟨4219956, by rfl⟩ : syracuseStep 11253217 = 8439913) B8439913
theorem B15004289 : Blo 2025435 15004289 := bstep (se 2 (by rfl) ⟨5626608, by rfl⟩ : syracuseStep 15004289 = 11253217) B11253217
theorem B10002859 : Blo 2025435 10002859 := bstep (se 1 (by rfl) ⟨7502144, by rfl⟩ : syracuseStep 10002859 = 15004289) B15004289
theorem B53348581 : Blo 2025435 53348581 := bstep (se 4 (by rfl) ⟨5001429, by rfl⟩ : syracuseStep 53348581 = 10002859) B10002859
theorem B71131441 : Blo 2025435 71131441 := bstep (se 2 (by rfl) ⟨26674290, by rfl⟩ : syracuseStep 71131441 = 53348581) B53348581
theorem B94841921 : Blo 2025435 94841921 := bstep (se 2 (by rfl) ⟨35565720, by rfl⟩ : syracuseStep 94841921 = 71131441) B71131441
theorem B63227947 : Blo 2025435 63227947 := bstep (se 1 (by rfl) ⟨47420960, by rfl⟩ : syracuseStep 63227947 = 94841921) B94841921
theorem B84303929 : Blo 2025435 84303929 := bstep (se 2 (by rfl) ⟨31613973, by rfl⟩ : syracuseStep 84303929 = 63227947) B63227947
theorem B56202619 : Blo 2025435 56202619 := bstep (se 1 (by rfl) ⟨42151964, by rfl⟩ : syracuseStep 56202619 = 84303929) B84303929
theorem B74936825 : Blo 2025435 74936825 := bstep (se 2 (by rfl) ⟨28101309, by rfl⟩ : syracuseStep 74936825 = 56202619) B56202619
theorem B49957883 : Blo 2025435 49957883 := bstep (se 1 (by rfl) ⟨37468412, by rfl⟩ : syracuseStep 49957883 = 74936825) B74936825
theorem B33305255 : Blo 2025435 33305255 := bstep (se 1 (by rfl) ⟨24978941, by rfl⟩ : syracuseStep 33305255 = 49957883) B49957883
theorem B22203503 : Blo 2025435 22203503 := bstep (se 1 (by rfl) ⟨16652627, by rfl⟩ : syracuseStep 22203503 = 33305255) B33305255
theorem B14802335 : Blo 2025435 14802335 := bstep (se 1 (by rfl) ⟨11101751, by rfl⟩ : syracuseStep 14802335 = 22203503) B22203503
theorem B9868223 : Blo 2025435 9868223 := bstep (se 1 (by rfl) ⟨7401167, by rfl⟩ : syracuseStep 9868223 = 14802335) B14802335
theorem B6578815 : Blo 2025435 6578815 := bstep (se 1 (by rfl) ⟨4934111, by rfl⟩ : syracuseStep 6578815 = 9868223) B9868223
theorem B8771753 : Blo 2025435 8771753 := bstep (se 2 (by rfl) ⟨3289407, by rfl⟩ : syracuseStep 8771753 = 6578815) B6578815
theorem B23391341 : Blo 2025435 23391341 := bstep (se 3 (by rfl) ⟨4385876, by rfl⟩ : syracuseStep 23391341 = 8771753) B8771753
theorem B15594227 : Blo 2025435 15594227 := bstep (se 1 (by rfl) ⟨11695670, by rfl⟩ : syracuseStep 15594227 = 23391341) B23391341
theorem B10396151 : Blo 2025435 10396151 := bstep (se 1 (by rfl) ⟨7797113, by rfl⟩ : syracuseStep 10396151 = 15594227) B15594227
theorem B6930767 : Blo 2025435 6930767 := bstep (se 1 (by rfl) ⟨5198075, by rfl⟩ : syracuseStep 6930767 = 10396151) B10396151
theorem B4620511 : Blo 2025435 4620511 := bstep (se 1 (by rfl) ⟨3465383, by rfl⟩ : syracuseStep 4620511 = 6930767) B6930767
theorem B6160681 : Blo 2025435 6160681 := bstep (se 2 (by rfl) ⟨2310255, by rfl⟩ : syracuseStep 6160681 = 4620511) B4620511
theorem B32856965 : Blo 2025435 32856965 := bstep (se 4 (by rfl) ⟨3080340, by rfl⟩ : syracuseStep 32856965 = 6160681) B6160681
theorem B21904643 : Blo 2025435 21904643 := bstep (se 1 (by rfl) ⟨16428482, by rfl⟩ : syracuseStep 21904643 = 32856965) B32856965
theorem B14603095 : Blo 2025435 14603095 := bstep (se 1 (by rfl) ⟨10952321, by rfl⟩ : syracuseStep 14603095 = 21904643) B21904643
theorem B19470793 : Blo 2025435 19470793 := bstep (se 2 (by rfl) ⟨7301547, by rfl⟩ : syracuseStep 19470793 = 14603095) B14603095
theorem B25961057 : Blo 2025435 25961057 := bstep (se 2 (by rfl) ⟨9735396, by rfl⟩ : syracuseStep 25961057 = 19470793) B19470793
theorem B17307371 : Blo 2025435 17307371 := bstep (se 1 (by rfl) ⟨12980528, by rfl⟩ : syracuseStep 17307371 = 25961057) B25961057
theorem B11538247 : Blo 2025435 11538247 := bstep (se 1 (by rfl) ⟨8653685, by rfl⟩ : syracuseStep 11538247 = 17307371) B17307371
theorem B15384329 : Blo 2025435 15384329 := bstep (se 2 (by rfl) ⟨5769123, by rfl⟩ : syracuseStep 15384329 = 11538247) B11538247
theorem B10256219 : Blo 2025435 10256219 := bstep (se 1 (by rfl) ⟨7692164, by rfl⟩ : syracuseStep 10256219 = 15384329) B15384329
theorem B6837479 : Blo 2025435 6837479 := bstep (se 1 (by rfl) ⟨5128109, by rfl⟩ : syracuseStep 6837479 = 10256219) B10256219
theorem B4558319 : Blo 2025435 4558319 := bstep (se 1 (by rfl) ⟨3418739, by rfl⟩ : syracuseStep 4558319 = 6837479) B6837479
theorem B3038879 : Blo 2025435 3038879 := bstep (se 1 (by rfl) ⟨2279159, by rfl⟩ : syracuseStep 3038879 = 4558319) B4558319
theorem B2025919 : Blo 2025435 2025919 := bstep (se 1 (by rfl) ⟨1519439, by rfl⟩ : syracuseStep 2025919 = 3038879) B3038879
theorem B3038885 : Blo 2025435 3038885 := bbase (se 4 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 3038885 = 569791) (by norm_num)
theorem B2025923 : Blo 2025435 2025923 := bstep (se 1 (by rfl) ⟨1519442, by rfl⟩ : syracuseStep 2025923 = 3038885) B3038885
theorem B2564065 : Blo 2025435 2564065 := bbase (se 2 (by rfl) ⟨961524, by rfl⟩ : syracuseStep 2564065 = 1923049) (by norm_num)
theorem B3418753 : Blo 2025435 3418753 := bstep (se 2 (by rfl) ⟨1282032, by rfl⟩ : syracuseStep 3418753 = 2564065) B2564065
theorem B4558337 : Blo 2025435 4558337 := bstep (se 2 (by rfl) ⟨1709376, by rfl⟩ : syracuseStep 4558337 = 3418753) B3418753
theorem B3038891 : Blo 2025435 3038891 := bstep (se 1 (by rfl) ⟨2279168, by rfl⟩ : syracuseStep 3038891 = 4558337) B4558337
theorem B2025927 : Blo 2025435 2025927 := bstep (se 1 (by rfl) ⟨1519445, by rfl⟩ : syracuseStep 2025927 = 3038891) B3038891
theorem B2279173 : Blo 2025435 2279173 := bbase (se 4 (by rfl) ⟨213672, by rfl⟩ : syracuseStep 2279173 = 427345) (by norm_num)
theorem B3038897 : Blo 2025435 3038897 := bstep (se 2 (by rfl) ⟨1139586, by rfl⟩ : syracuseStep 3038897 = 2279173) B2279173
theorem B2025931 : Blo 2025435 2025931 := bstep (se 1 (by rfl) ⟨1519448, by rfl⟩ : syracuseStep 2025931 = 3038897) B3038897
theorem B6244789 : Blo 2025435 6244789 := bbase (se 5 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 6244789 = 585449) (by norm_num)
theorem B8326385 : Blo 2025435 8326385 := bstep (se 2 (by rfl) ⟨3122394, by rfl⟩ : syracuseStep 8326385 = 6244789) B6244789
theorem B5550923 : Blo 2025435 5550923 := bstep (se 1 (by rfl) ⟨4163192, by rfl⟩ : syracuseStep 5550923 = 8326385) B8326385
theorem B3700615 : Blo 2025435 3700615 := bstep (se 1 (by rfl) ⟨2775461, by rfl⟩ : syracuseStep 3700615 = 5550923) B5550923
theorem B4934153 : Blo 2025435 4934153 := bstep (se 2 (by rfl) ⟨1850307, by rfl⟩ : syracuseStep 4934153 = 3700615) B3700615
theorem B13157741 : Blo 2025435 13157741 := bstep (se 3 (by rfl) ⟨2467076, by rfl⟩ : syracuseStep 13157741 = 4934153) B4934153
theorem B8771827 : Blo 2025435 8771827 := bstep (se 1 (by rfl) ⟨6578870, by rfl⟩ : syracuseStep 8771827 = 13157741) B13157741
theorem B11695769 : Blo 2025435 11695769 := bstep (se 2 (by rfl) ⟨4385913, by rfl⟩ : syracuseStep 11695769 = 8771827) B8771827
theorem B7797179 : Blo 2025435 7797179 := bstep (se 1 (by rfl) ⟨5847884, by rfl⟩ : syracuseStep 7797179 = 11695769) B11695769
theorem B20792477 : Blo 2025435 20792477 := bstep (se 3 (by rfl) ⟨3898589, by rfl⟩ : syracuseStep 20792477 = 7797179) B7797179
theorem B13861651 : Blo 2025435 13861651 := bstep (se 1 (by rfl) ⟨10396238, by rfl⟩ : syracuseStep 13861651 = 20792477) B20792477
theorem B18482201 : Blo 2025435 18482201 := bstep (se 2 (by rfl) ⟨6930825, by rfl⟩ : syracuseStep 18482201 = 13861651) B13861651
theorem B12321467 : Blo 2025435 12321467 := bstep (se 1 (by rfl) ⟨9241100, by rfl⟩ : syracuseStep 12321467 = 18482201) B18482201
theorem B8214311 : Blo 2025435 8214311 := bstep (se 1 (by rfl) ⟨6160733, by rfl⟩ : syracuseStep 8214311 = 12321467) B12321467
theorem B5476207 : Blo 2025435 5476207 := bstep (se 1 (by rfl) ⟨4107155, by rfl⟩ : syracuseStep 5476207 = 8214311) B8214311
theorem B7301609 : Blo 2025435 7301609 := bstep (se 2 (by rfl) ⟨2738103, by rfl⟩ : syracuseStep 7301609 = 5476207) B5476207
theorem B4867739 : Blo 2025435 4867739 := bstep (se 1 (by rfl) ⟨3650804, by rfl⟩ : syracuseStep 4867739 = 7301609) B7301609
theorem B3245159 : Blo 2025435 3245159 := bstep (se 1 (by rfl) ⟨2433869, by rfl⟩ : syracuseStep 3245159 = 4867739) B4867739
theorem B2163439 : Blo 2025435 2163439 := bstep (se 1 (by rfl) ⟨1622579, by rfl⟩ : syracuseStep 2163439 = 3245159) B3245159
theorem B2884585 : Blo 2025435 2884585 := bstep (se 2 (by rfl) ⟨1081719, by rfl⟩ : syracuseStep 2884585 = 2163439) B2163439
theorem B3846113 : Blo 2025435 3846113 := bstep (se 2 (by rfl) ⟨1442292, by rfl⟩ : syracuseStep 3846113 = 2884585) B2884585
theorem B2564075 : Blo 2025435 2564075 := bstep (se 1 (by rfl) ⟨1923056, by rfl⟩ : syracuseStep 2564075 = 3846113) B3846113
theorem B6837533 : Blo 2025435 6837533 := bstep (se 3 (by rfl) ⟨1282037, by rfl⟩ : syracuseStep 6837533 = 2564075) B2564075
theorem B4558355 : Blo 2025435 4558355 := bstep (se 1 (by rfl) ⟨3418766, by rfl⟩ : syracuseStep 4558355 = 6837533) B6837533
theorem B3038903 : Blo 2025435 3038903 := bstep (se 1 (by rfl) ⟨2279177, by rfl⟩ : syracuseStep 3038903 = 4558355) B4558355
theorem B2025935 : Blo 2025435 2025935 := bstep (se 1 (by rfl) ⟨1519451, by rfl⟩ : syracuseStep 2025935 = 3038903) B3038903
theorem B3038909 : Blo 2025435 3038909 := bbase (se 3 (by rfl) ⟨569795, by rfl⟩ : syracuseStep 3038909 = 1139591) (by norm_num)
theorem B2025939 : Blo 2025435 2025939 := bstep (se 1 (by rfl) ⟨1519454, by rfl⟩ : syracuseStep 2025939 = 3038909) B3038909
theorem B4558373 : Blo 2025435 4558373 := bbase (se 4 (by rfl) ⟨427347, by rfl⟩ : syracuseStep 4558373 = 854695) (by norm_num)
theorem B3038915 : Blo 2025435 3038915 := bstep (se 1 (by rfl) ⟨2279186, by rfl⟩ : syracuseStep 3038915 = 4558373) B4558373
theorem B2025943 : Blo 2025435 2025943 := bstep (se 1 (by rfl) ⟨1519457, by rfl⟩ : syracuseStep 2025943 = 3038915) B3038915
theorem B5128181 : Blo 2025435 5128181 := bbase (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) (by norm_num)
theorem B3418787 : Blo 2025435 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B2279191 : Blo 2025435 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B3038921 : Blo 2025435 3038921 := bstep (se 2 (by rfl) ⟨1139595, by rfl⟩ : syracuseStep 3038921 = 2279191) B2279191
theorem B2025947 : Blo 2025435 2025947 := bstep (se 1 (by rfl) ⟨1519460, by rfl⟩ : syracuseStep 2025947 = 3038921) B3038921
theorem B54077269 : Blo 2025435 54077269 := bbase (se 9 (by rfl) ⟨158429, by rfl⟩ : syracuseStep 54077269 = 316859) (by norm_num)
theorem B72103025 : Blo 2025435 72103025 := bstep (se 2 (by rfl) ⟨27038634, by rfl⟩ : syracuseStep 72103025 = 54077269) B54077269
theorem B48068683 : Blo 2025435 48068683 := bstep (se 1 (by rfl) ⟨36051512, by rfl⟩ : syracuseStep 48068683 = 72103025) B72103025
theorem B256366309 : Blo 2025435 256366309 := bstep (se 4 (by rfl) ⟨24034341, by rfl⟩ : syracuseStep 256366309 = 48068683) B48068683
theorem B341821745 : Blo 2025435 341821745 := bstep (se 2 (by rfl) ⟨128183154, by rfl⟩ : syracuseStep 341821745 = 256366309) B256366309
theorem B227881163 : Blo 2025435 227881163 := bstep (se 1 (by rfl) ⟨170910872, by rfl⟩ : syracuseStep 227881163 = 341821745) B341821745
theorem B151920775 : Blo 2025435 151920775 := bstep (se 1 (by rfl) ⟨113940581, by rfl⟩ : syracuseStep 151920775 = 227881163) B227881163
theorem B810244133 : Blo 2025435 810244133 := bstep (se 4 (by rfl) ⟨75960387, by rfl⟩ : syracuseStep 810244133 = 151920775) B151920775
theorem B540162755 : Blo 2025435 540162755 := bstep (se 1 (by rfl) ⟨405122066, by rfl⟩ : syracuseStep 540162755 = 810244133) B810244133
theorem B360108503 : Blo 2025435 360108503 := bstep (se 1 (by rfl) ⟨270081377, by rfl⟩ : syracuseStep 360108503 = 540162755) B540162755
theorem B240072335 : Blo 2025435 240072335 := bstep (se 1 (by rfl) ⟨180054251, by rfl⟩ : syracuseStep 240072335 = 360108503) B360108503
theorem B160048223 : Blo 2025435 160048223 := bstep (se 1 (by rfl) ⟨120036167, by rfl⟩ : syracuseStep 160048223 = 240072335) B240072335
theorem B106698815 : Blo 2025435 106698815 := bstep (se 1 (by rfl) ⟨80024111, by rfl⟩ : syracuseStep 106698815 = 160048223) B160048223
theorem B71132543 : Blo 2025435 71132543 := bstep (se 1 (by rfl) ⟨53349407, by rfl⟩ : syracuseStep 71132543 = 106698815) B106698815
theorem B47421695 : Blo 2025435 47421695 := bstep (se 1 (by rfl) ⟨35566271, by rfl⟩ : syracuseStep 47421695 = 71132543) B71132543
theorem B126457853 : Blo 2025435 126457853 := bstep (se 3 (by rfl) ⟨23710847, by rfl⟩ : syracuseStep 126457853 = 47421695) B47421695
theorem B337220941 : Blo 2025435 337220941 := bstep (se 3 (by rfl) ⟨63228926, by rfl⟩ : syracuseStep 337220941 = 126457853) B126457853
theorem B449627921 : Blo 2025435 449627921 := bstep (se 2 (by rfl) ⟨168610470, by rfl⟩ : syracuseStep 449627921 = 337220941) B337220941
theorem B299751947 : Blo 2025435 299751947 := bstep (se 1 (by rfl) ⟨224813960, by rfl⟩ : syracuseStep 299751947 = 449627921) B449627921
theorem B199834631 : Blo 2025435 199834631 := bstep (se 1 (by rfl) ⟨149875973, by rfl⟩ : syracuseStep 199834631 = 299751947) B299751947
theorem B133223087 : Blo 2025435 133223087 := bstep (se 1 (by rfl) ⟨99917315, by rfl⟩ : syracuseStep 133223087 = 199834631) B199834631
theorem B355261565 : Blo 2025435 355261565 := bstep (se 3 (by rfl) ⟨66611543, by rfl⟩ : syracuseStep 355261565 = 133223087) B133223087
theorem B236841043 : Blo 2025435 236841043 := bstep (se 1 (by rfl) ⟨177630782, by rfl⟩ : syracuseStep 236841043 = 355261565) B355261565
theorem B315788057 : Blo 2025435 315788057 := bstep (se 2 (by rfl) ⟨118420521, by rfl⟩ : syracuseStep 315788057 = 236841043) B236841043
theorem B210525371 : Blo 2025435 210525371 := bstep (se 1 (by rfl) ⟨157894028, by rfl⟩ : syracuseStep 210525371 = 315788057) B315788057
theorem B140350247 : Blo 2025435 140350247 := bstep (se 1 (by rfl) ⟨105262685, by rfl⟩ : syracuseStep 140350247 = 210525371) B210525371
theorem B93566831 : Blo 2025435 93566831 := bstep (se 1 (by rfl) ⟨70175123, by rfl⟩ : syracuseStep 93566831 = 140350247) B140350247
theorem B249511549 : Blo 2025435 249511549 := bstep (se 3 (by rfl) ⟨46783415, by rfl⟩ : syracuseStep 249511549 = 93566831) B93566831
theorem B332682065 : Blo 2025435 332682065 := bstep (se 2 (by rfl) ⟨124755774, by rfl⟩ : syracuseStep 332682065 = 249511549) B249511549
theorem B221788043 : Blo 2025435 221788043 := bstep (se 1 (by rfl) ⟨166341032, by rfl⟩ : syracuseStep 221788043 = 332682065) B332682065
theorem B147858695 : Blo 2025435 147858695 := bstep (se 1 (by rfl) ⟨110894021, by rfl⟩ : syracuseStep 147858695 = 221788043) B221788043
theorem B98572463 : Blo 2025435 98572463 := bstep (se 1 (by rfl) ⟨73929347, by rfl⟩ : syracuseStep 98572463 = 147858695) B147858695
theorem B65714975 : Blo 2025435 65714975 := bstep (se 1 (by rfl) ⟨49286231, by rfl⟩ : syracuseStep 65714975 = 98572463) B98572463
theorem B43809983 : Blo 2025435 43809983 := bstep (se 1 (by rfl) ⟨32857487, by rfl⟩ : syracuseStep 43809983 = 65714975) B65714975
theorem B29206655 : Blo 2025435 29206655 := bstep (se 1 (by rfl) ⟨21904991, by rfl⟩ : syracuseStep 29206655 = 43809983) B43809983
theorem B19471103 : Blo 2025435 19471103 := bstep (se 1 (by rfl) ⟨14603327, by rfl⟩ : syracuseStep 19471103 = 29206655) B29206655
theorem B12980735 : Blo 2025435 12980735 := bstep (se 1 (by rfl) ⟨9735551, by rfl⟩ : syracuseStep 12980735 = 19471103) B19471103
theorem B8653823 : Blo 2025435 8653823 := bstep (se 1 (by rfl) ⟨6490367, by rfl⟩ : syracuseStep 8653823 = 12980735) B12980735
theorem B5769215 : Blo 2025435 5769215 := bstep (se 1 (by rfl) ⟨4326911, by rfl⟩ : syracuseStep 5769215 = 8653823) B8653823
theorem B3846143 : Blo 2025435 3846143 := bstep (se 1 (by rfl) ⟨2884607, by rfl⟩ : syracuseStep 3846143 = 5769215) B5769215
theorem B10256381 : Blo 2025435 10256381 := bstep (se 3 (by rfl) ⟨1923071, by rfl⟩ : syracuseStep 10256381 = 3846143) B3846143
theorem B6837587 : Blo 2025435 6837587 := bstep (se 1 (by rfl) ⟨5128190, by rfl⟩ : syracuseStep 6837587 = 10256381) B10256381
theorem B4558391 : Blo 2025435 4558391 := bstep (se 1 (by rfl) ⟨3418793, by rfl⟩ : syracuseStep 4558391 = 6837587) B6837587
theorem B3038927 : Blo 2025435 3038927 := bstep (se 1 (by rfl) ⟨2279195, by rfl⟩ : syracuseStep 3038927 = 4558391) B4558391
theorem B2025951 : Blo 2025435 2025951 := bstep (se 1 (by rfl) ⟨1519463, by rfl⟩ : syracuseStep 2025951 = 3038927) B3038927
theorem B3038933 : Blo 2025435 3038933 := bbase (se 7 (by rfl) ⟨35612, by rfl⟩ : syracuseStep 3038933 = 71225) (by norm_num)
theorem B2025955 : Blo 2025435 2025955 := bstep (se 1 (by rfl) ⟨1519466, by rfl⟩ : syracuseStep 2025955 = 3038933) B3038933
theorem B3245197 : Blo 2025435 3245197 := bbase (se 3 (by rfl) ⟨608474, by rfl⟩ : syracuseStep 3245197 = 1216949) (by norm_num)
theorem B4326929 : Blo 2025435 4326929 := bstep (se 2 (by rfl) ⟨1622598, by rfl⟩ : syracuseStep 4326929 = 3245197) B3245197
theorem B2884619 : Blo 2025435 2884619 := bstep (se 1 (by rfl) ⟨2163464, by rfl⟩ : syracuseStep 2884619 = 4326929) B4326929
theorem B7692317 : Blo 2025435 7692317 := bstep (se 3 (by rfl) ⟨1442309, by rfl⟩ : syracuseStep 7692317 = 2884619) B2884619
theorem B5128211 : Blo 2025435 5128211 := bstep (se 1 (by rfl) ⟨3846158, by rfl⟩ : syracuseStep 5128211 = 7692317) B7692317
theorem B3418807 : Blo 2025435 3418807 := bstep (se 1 (by rfl) ⟨2564105, by rfl⟩ : syracuseStep 3418807 = 5128211) B5128211
theorem B4558409 : Blo 2025435 4558409 := bstep (se 2 (by rfl) ⟨1709403, by rfl⟩ : syracuseStep 4558409 = 3418807) B3418807
theorem B3038939 : Blo 2025435 3038939 := bstep (se 1 (by rfl) ⟨2279204, by rfl⟩ : syracuseStep 3038939 = 4558409) B4558409
theorem B2025959 : Blo 2025435 2025959 := bstep (se 1 (by rfl) ⟨1519469, by rfl⟩ : syracuseStep 2025959 = 3038939) B3038939
theorem B2279209 : Blo 2025435 2279209 := bbase (se 2 (by rfl) ⟨854703, by rfl⟩ : syracuseStep 2279209 = 1709407) (by norm_num)
theorem B3038945 : Blo 2025435 3038945 := bstep (se 2 (by rfl) ⟨1139604, by rfl⟩ : syracuseStep 3038945 = 2279209) B2279209
theorem B2025963 : Blo 2025435 2025963 := bstep (se 1 (by rfl) ⟨1519472, by rfl⟩ : syracuseStep 2025963 = 3038945) B3038945
theorem B3650861 : Blo 2025435 3650861 := bbase (se 3 (by rfl) ⟨684536, by rfl⟩ : syracuseStep 3650861 = 1369073) (by norm_num)
theorem B2433907 : Blo 2025435 2433907 := bstep (se 1 (by rfl) ⟨1825430, by rfl⟩ : syracuseStep 2433907 = 3650861) B3650861
theorem B12980837 : Blo 2025435 12980837 := bstep (se 4 (by rfl) ⟨1216953, by rfl⟩ : syracuseStep 12980837 = 2433907) B2433907
theorem B8653891 : Blo 2025435 8653891 := bstep (se 1 (by rfl) ⟨6490418, by rfl⟩ : syracuseStep 8653891 = 12980837) B12980837
theorem B11538521 : Blo 2025435 11538521 := bstep (se 2 (by rfl) ⟨4326945, by rfl⟩ : syracuseStep 11538521 = 8653891) B8653891
theorem B7692347 : Blo 2025435 7692347 := bstep (se 1 (by rfl) ⟨5769260, by rfl⟩ : syracuseStep 7692347 = 11538521) B11538521
theorem B5128231 : Blo 2025435 5128231 := bstep (se 1 (by rfl) ⟨3846173, by rfl⟩ : syracuseStep 5128231 = 7692347) B7692347
theorem B6837641 : Blo 2025435 6837641 := bstep (se 2 (by rfl) ⟨2564115, by rfl⟩ : syracuseStep 6837641 = 5128231) B5128231
theorem B4558427 : Blo 2025435 4558427 := bstep (se 1 (by rfl) ⟨3418820, by rfl⟩ : syracuseStep 4558427 = 6837641) B6837641
theorem B3038951 : Blo 2025435 3038951 := bstep (se 1 (by rfl) ⟨2279213, by rfl⟩ : syracuseStep 3038951 = 4558427) B4558427
theorem B2025967 : Blo 2025435 2025967 := bstep (se 1 (by rfl) ⟨1519475, by rfl⟩ : syracuseStep 2025967 = 3038951) B3038951
theorem B3038957 : Blo 2025435 3038957 := bbase (se 3 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 3038957 = 1139609) (by norm_num)
theorem B2025971 : Blo 2025435 2025971 := bstep (se 1 (by rfl) ⟨1519478, by rfl⟩ : syracuseStep 2025971 = 3038957) B3038957
theorem B4558445 : Blo 2025435 4558445 := bbase (se 3 (by rfl) ⟨854708, by rfl⟩ : syracuseStep 4558445 = 1709417) (by norm_num)
theorem B3038963 : Blo 2025435 3038963 := bstep (se 1 (by rfl) ⟨2279222, by rfl⟩ : syracuseStep 3038963 = 4558445) B4558445
theorem B2025975 : Blo 2025435 2025975 := bstep (se 1 (by rfl) ⟨1519481, by rfl⟩ : syracuseStep 2025975 = 3038963) B3038963
theorem B3846197 : Blo 2025435 3846197 := bbase (se 5 (by rfl) ⟨180290, by rfl⟩ : syracuseStep 3846197 = 360581) (by norm_num)
theorem B2564131 : Blo 2025435 2564131 := bstep (se 1 (by rfl) ⟨1923098, by rfl⟩ : syracuseStep 2564131 = 3846197) B3846197
theorem B3418841 : Blo 2025435 3418841 := bstep (se 2 (by rfl) ⟨1282065, by rfl⟩ : syracuseStep 3418841 = 2564131) B2564131
theorem B2279227 : Blo 2025435 2279227 := bstep (se 1 (by rfl) ⟨1709420, by rfl⟩ : syracuseStep 2279227 = 3418841) B3418841
theorem B3038969 : Blo 2025435 3038969 := bstep (se 2 (by rfl) ⟨1139613, by rfl⟩ : syracuseStep 3038969 = 2279227) B2279227
theorem B2025979 : Blo 2025435 2025979 := bstep (se 1 (by rfl) ⟨1519484, by rfl⟩ : syracuseStep 2025979 = 3038969) B3038969
theorem B6244933 : Blo 2025435 6244933 := bbase (se 4 (by rfl) ⟨585462, by rfl⟩ : syracuseStep 6244933 = 1170925) (by norm_num)
theorem B8326577 : Blo 2025435 8326577 := bstep (se 2 (by rfl) ⟨3122466, by rfl⟩ : syracuseStep 8326577 = 6244933) B6244933
theorem B5551051 : Blo 2025435 5551051 := bstep (se 1 (by rfl) ⟨4163288, by rfl⟩ : syracuseStep 5551051 = 8326577) B8326577
theorem B7401401 : Blo 2025435 7401401 := bstep (se 2 (by rfl) ⟨2775525, by rfl⟩ : syracuseStep 7401401 = 5551051) B5551051
theorem B4934267 : Blo 2025435 4934267 := bstep (se 1 (by rfl) ⟨3700700, by rfl⟩ : syracuseStep 4934267 = 7401401) B7401401
theorem B3289511 : Blo 2025435 3289511 := bstep (se 1 (by rfl) ⟨2467133, by rfl⟩ : syracuseStep 3289511 = 4934267) B4934267
theorem B8772029 : Blo 2025435 8772029 := bstep (se 3 (by rfl) ⟨1644755, by rfl⟩ : syracuseStep 8772029 = 3289511) B3289511
theorem B5848019 : Blo 2025435 5848019 := bstep (se 1 (by rfl) ⟨4386014, by rfl⟩ : syracuseStep 5848019 = 8772029) B8772029
theorem B3898679 : Blo 2025435 3898679 := bstep (se 1 (by rfl) ⟨2924009, by rfl⟩ : syracuseStep 3898679 = 5848019) B5848019
theorem B10396477 : Blo 2025435 10396477 := bstep (se 3 (by rfl) ⟨1949339, by rfl⟩ : syracuseStep 10396477 = 3898679) B3898679
theorem B55447877 : Blo 2025435 55447877 := bstep (se 4 (by rfl) ⟨5198238, by rfl⟩ : syracuseStep 55447877 = 10396477) B10396477
theorem B36965251 : Blo 2025435 36965251 := bstep (se 1 (by rfl) ⟨27723938, by rfl⟩ : syracuseStep 36965251 = 55447877) B55447877
theorem B197148005 : Blo 2025435 197148005 := bstep (se 4 (by rfl) ⟨18482625, by rfl⟩ : syracuseStep 197148005 = 36965251) B36965251
theorem B131432003 : Blo 2025435 131432003 := bstep (se 1 (by rfl) ⟨98574002, by rfl⟩ : syracuseStep 131432003 = 197148005) B197148005
theorem B87621335 : Blo 2025435 87621335 := bstep (se 1 (by rfl) ⟨65716001, by rfl⟩ : syracuseStep 87621335 = 131432003) B131432003
theorem B58414223 : Blo 2025435 58414223 := bstep (se 1 (by rfl) ⟨43810667, by rfl⟩ : syracuseStep 58414223 = 87621335) B87621335
theorem B38942815 : Blo 2025435 38942815 := bstep (se 1 (by rfl) ⟨29207111, by rfl⟩ : syracuseStep 38942815 = 58414223) B58414223
theorem B51923753 : Blo 2025435 51923753 := bstep (se 2 (by rfl) ⟨19471407, by rfl⟩ : syracuseStep 51923753 = 38942815) B38942815
theorem B34615835 : Blo 2025435 34615835 := bstep (se 1 (by rfl) ⟨25961876, by rfl⟩ : syracuseStep 34615835 = 51923753) B51923753
theorem B23077223 : Blo 2025435 23077223 := bstep (se 1 (by rfl) ⟨17307917, by rfl⟩ : syracuseStep 23077223 = 34615835) B34615835
theorem B15384815 : Blo 2025435 15384815 := bstep (se 1 (by rfl) ⟨11538611, by rfl⟩ : syracuseStep 15384815 = 23077223) B23077223
theorem B10256543 : Blo 2025435 10256543 := bstep (se 1 (by rfl) ⟨7692407, by rfl⟩ : syracuseStep 10256543 = 15384815) B15384815
theorem B6837695 : Blo 2025435 6837695 := bstep (se 1 (by rfl) ⟨5128271, by rfl⟩ : syracuseStep 6837695 = 10256543) B10256543
theorem B4558463 : Blo 2025435 4558463 := bstep (se 1 (by rfl) ⟨3418847, by rfl⟩ : syracuseStep 4558463 = 6837695) B6837695
theorem B3038975 : Blo 2025435 3038975 := bstep (se 1 (by rfl) ⟨2279231, by rfl⟩ : syracuseStep 3038975 = 4558463) B4558463
theorem B2025983 : Blo 2025435 2025983 := bstep (se 1 (by rfl) ⟨1519487, by rfl⟩ : syracuseStep 2025983 = 3038975) B3038975
theorem B3038981 : Blo 2025435 3038981 := bbase (se 4 (by rfl) ⟨284904, by rfl⟩ : syracuseStep 3038981 = 569809) (by norm_num)
theorem B2025987 : Blo 2025435 2025987 := bstep (se 1 (by rfl) ⟨1519490, by rfl⟩ : syracuseStep 2025987 = 3038981) B3038981
theorem B3418861 : Blo 2025435 3418861 := bbase (se 3 (by rfl) ⟨641036, by rfl⟩ : syracuseStep 3418861 = 1282073) (by norm_num)
theorem B4558481 : Blo 2025435 4558481 := bstep (se 2 (by rfl) ⟨1709430, by rfl⟩ : syracuseStep 4558481 = 3418861) B3418861
theorem B3038987 : Blo 2025435 3038987 := bstep (se 1 (by rfl) ⟨2279240, by rfl⟩ : syracuseStep 3038987 = 4558481) B4558481
theorem B2025991 : Blo 2025435 2025991 := bstep (se 1 (by rfl) ⟨1519493, by rfl⟩ : syracuseStep 2025991 = 3038987) B3038987
theorem B2279245 : Blo 2025435 2279245 := bbase (se 3 (by rfl) ⟨427358, by rfl⟩ : syracuseStep 2279245 = 854717) (by norm_num)
theorem B3038993 : Blo 2025435 3038993 := bstep (se 2 (by rfl) ⟨1139622, by rfl⟩ : syracuseStep 3038993 = 2279245) B2279245
theorem B2025995 : Blo 2025435 2025995 := bstep (se 1 (by rfl) ⟨1519496, by rfl⟩ : syracuseStep 2025995 = 3038993) B3038993
theorem B6837749 : Blo 2025435 6837749 := bbase (se 5 (by rfl) ⟨320519, by rfl⟩ : syracuseStep 6837749 = 641039) (by norm_num)
theorem B4558499 : Blo 2025435 4558499 := bstep (se 1 (by rfl) ⟨3418874, by rfl⟩ : syracuseStep 4558499 = 6837749) B6837749
theorem B3038999 : Blo 2025435 3038999 := bstep (se 1 (by rfl) ⟨2279249, by rfl⟩ : syracuseStep 3038999 = 4558499) B4558499
theorem B2025999 : Blo 2025435 2025999 := bstep (se 1 (by rfl) ⟨1519499, by rfl⟩ : syracuseStep 2025999 = 3038999) B3038999
theorem B3039005 : Blo 2025435 3039005 := bbase (se 3 (by rfl) ⟨569813, by rfl⟩ : syracuseStep 3039005 = 1139627) (by norm_num)
theorem B2026003 : Blo 2025435 2026003 := bstep (se 1 (by rfl) ⟨1519502, by rfl⟩ : syracuseStep 2026003 = 3039005) B3039005
theorem B4558517 : Blo 2025435 4558517 := bbase (se 5 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 4558517 = 427361) (by norm_num)
theorem B3039011 : Blo 2025435 3039011 := bstep (se 1 (by rfl) ⟨2279258, by rfl⟩ : syracuseStep 3039011 = 4558517) B4558517
theorem B2026007 : Blo 2025435 2026007 := bstep (se 1 (by rfl) ⟨1519505, by rfl⟩ : syracuseStep 2026007 = 3039011) B3039011
theorem B11538773 : Blo 2025435 11538773 := bbase (se 10 (by rfl) ⟨16902, by rfl⟩ : syracuseStep 11538773 = 33805) (by norm_num)
theorem B7692515 : Blo 2025435 7692515 := bstep (se 1 (by rfl) ⟨5769386, by rfl⟩ : syracuseStep 7692515 = 11538773) B11538773
theorem B5128343 : Blo 2025435 5128343 := bstep (se 1 (by rfl) ⟨3846257, by rfl⟩ : syracuseStep 5128343 = 7692515) B7692515
theorem B3418895 : Blo 2025435 3418895 := bstep (se 1 (by rfl) ⟨2564171, by rfl⟩ : syracuseStep 3418895 = 5128343) B5128343
theorem B2279263 : Blo 2025435 2279263 := bstep (se 1 (by rfl) ⟨1709447, by rfl⟩ : syracuseStep 2279263 = 3418895) B3418895
theorem B3039017 : Blo 2025435 3039017 := bstep (se 2 (by rfl) ⟨1139631, by rfl⟩ : syracuseStep 3039017 = 2279263) B2279263
theorem B2026011 : Blo 2025435 2026011 := bstep (se 1 (by rfl) ⟨1519508, by rfl⟩ : syracuseStep 2026011 = 3039017) B3039017
theorem B5769397 : Blo 2025435 5769397 := bbase (se 5 (by rfl) ⟨270440, by rfl⟩ : syracuseStep 5769397 = 540881) (by norm_num)
theorem B7692529 : Blo 2025435 7692529 := bstep (se 2 (by rfl) ⟨2884698, by rfl⟩ : syracuseStep 7692529 = 5769397) B5769397
theorem B10256705 : Blo 2025435 10256705 := bstep (se 2 (by rfl) ⟨3846264, by rfl⟩ : syracuseStep 10256705 = 7692529) B7692529
theorem B6837803 : Blo 2025435 6837803 := bstep (se 1 (by rfl) ⟨5128352, by rfl⟩ : syracuseStep 6837803 = 10256705) B10256705
theorem B4558535 : Blo 2025435 4558535 := bstep (se 1 (by rfl) ⟨3418901, by rfl⟩ : syracuseStep 4558535 = 6837803) B6837803
theorem B3039023 : Blo 2025435 3039023 := bstep (se 1 (by rfl) ⟨2279267, by rfl⟩ : syracuseStep 3039023 = 4558535) B4558535
theorem B2026015 : Blo 2025435 2026015 := bstep (se 1 (by rfl) ⟨1519511, by rfl⟩ : syracuseStep 2026015 = 3039023) B3039023
theorem B3039029 : Blo 2025435 3039029 := bbase (se 5 (by rfl) ⟨142454, by rfl⟩ : syracuseStep 3039029 = 284909) (by norm_num)
theorem B2026019 : Blo 2025435 2026019 := bstep (se 1 (by rfl) ⟨1519514, by rfl⟩ : syracuseStep 2026019 = 3039029) B3039029
theorem B5128373 : Blo 2025435 5128373 := bbase (se 5 (by rfl) ⟨240392, by rfl⟩ : syracuseStep 5128373 = 480785) (by norm_num)
theorem B3418915 : Blo 2025435 3418915 := bstep (se 1 (by rfl) ⟨2564186, by rfl⟩ : syracuseStep 3418915 = 5128373) B5128373
theorem B4558553 : Blo 2025435 4558553 := bstep (se 2 (by rfl) ⟨1709457, by rfl⟩ : syracuseStep 4558553 = 3418915) B3418915
theorem B3039035 : Blo 2025435 3039035 := bstep (se 1 (by rfl) ⟨2279276, by rfl⟩ : syracuseStep 3039035 = 4558553) B4558553
theorem B2026023 : Blo 2025435 2026023 := bstep (se 1 (by rfl) ⟨1519517, by rfl⟩ : syracuseStep 2026023 = 3039035) B3039035
theorem B2279281 : Blo 2025435 2279281 := bbase (se 2 (by rfl) ⟨854730, by rfl⟩ : syracuseStep 2279281 = 1709461) (by norm_num)
theorem B3039041 : Blo 2025435 3039041 := bstep (se 2 (by rfl) ⟨1139640, by rfl⟩ : syracuseStep 3039041 = 2279281) B2279281
theorem B2026027 : Blo 2025435 2026027 := bstep (se 1 (by rfl) ⟨1519520, by rfl⟩ : syracuseStep 2026027 = 3039041) B3039041
theorem B8654165 : Blo 2025435 8654165 := bbase (se 11 (by rfl) ⟨6338, by rfl⟩ : syracuseStep 8654165 = 12677) (by norm_num)
theorem B5769443 : Blo 2025435 5769443 := bstep (se 1 (by rfl) ⟨4327082, by rfl⟩ : syracuseStep 5769443 = 8654165) B8654165
theorem B3846295 : Blo 2025435 3846295 := bstep (se 1 (by rfl) ⟨2884721, by rfl⟩ : syracuseStep 3846295 = 5769443) B5769443
theorem B5128393 : Blo 2025435 5128393 := bstep (se 2 (by rfl) ⟨1923147, by rfl⟩ : syracuseStep 5128393 = 3846295) B3846295
theorem B6837857 : Blo 2025435 6837857 := bstep (se 2 (by rfl) ⟨2564196, by rfl⟩ : syracuseStep 6837857 = 5128393) B5128393
theorem B4558571 : Blo 2025435 4558571 := bstep (se 1 (by rfl) ⟨3418928, by rfl⟩ : syracuseStep 4558571 = 6837857) B6837857
theorem B3039047 : Blo 2025435 3039047 := bstep (se 1 (by rfl) ⟨2279285, by rfl⟩ : syracuseStep 3039047 = 4558571) B4558571
theorem B2026031 : Blo 2025435 2026031 := bstep (se 1 (by rfl) ⟨1519523, by rfl⟩ : syracuseStep 2026031 = 3039047) B3039047
theorem B3039053 : Blo 2025435 3039053 := bbase (se 3 (by rfl) ⟨569822, by rfl⟩ : syracuseStep 3039053 = 1139645) (by norm_num)
theorem B2026035 : Blo 2025435 2026035 := bstep (se 1 (by rfl) ⟨1519526, by rfl⟩ : syracuseStep 2026035 = 3039053) B3039053
theorem B4558589 : Blo 2025435 4558589 := bbase (se 3 (by rfl) ⟨854735, by rfl⟩ : syracuseStep 4558589 = 1709471) (by norm_num)
theorem B3039059 : Blo 2025435 3039059 := bstep (se 1 (by rfl) ⟨2279294, by rfl⟩ : syracuseStep 3039059 = 4558589) B4558589
theorem B2026039 : Blo 2025435 2026039 := bstep (se 1 (by rfl) ⟨1519529, by rfl⟩ : syracuseStep 2026039 = 3039059) B3039059
theorem B3418949 : Blo 2025435 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B2279299 : Blo 2025435 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B3039065 : Blo 2025435 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B2026043 : Blo 2025435 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B15385301 : Blo 2025435 15385301 := bbase (se 7 (by rfl) ⟨180296, by rfl⟩ : syracuseStep 15385301 = 360593) (by norm_num)
theorem B10256867 : Blo 2025435 10256867 := bstep (se 1 (by rfl) ⟨7692650, by rfl⟩ : syracuseStep 10256867 = 15385301) B15385301
theorem B6837911 : Blo 2025435 6837911 := bstep (se 1 (by rfl) ⟨5128433, by rfl⟩ : syracuseStep 6837911 = 10256867) B10256867
theorem B4558607 : Blo 2025435 4558607 := bstep (se 1 (by rfl) ⟨3418955, by rfl⟩ : syracuseStep 4558607 = 6837911) B6837911
theorem B3039071 : Blo 2025435 3039071 := bstep (se 1 (by rfl) ⟨2279303, by rfl⟩ : syracuseStep 3039071 = 4558607) B4558607
theorem B2026047 : Blo 2025435 2026047 := bstep (se 1 (by rfl) ⟨1519535, by rfl⟩ : syracuseStep 2026047 = 3039071) B3039071
theorem B3039077 : Blo 2025435 3039077 := bbase (se 4 (by rfl) ⟨284913, by rfl⟩ : syracuseStep 3039077 = 569827) (by norm_num)
theorem B2026051 : Blo 2025435 2026051 := bstep (se 1 (by rfl) ⟨1519538, by rfl⟩ : syracuseStep 2026051 = 3039077) B3039077
theorem B3846341 : Blo 2025435 3846341 := bbase (se 4 (by rfl) ⟨360594, by rfl⟩ : syracuseStep 3846341 = 721189) (by norm_num)
theorem B2564227 : Blo 2025435 2564227 := bstep (se 1 (by rfl) ⟨1923170, by rfl⟩ : syracuseStep 2564227 = 3846341) B3846341
theorem B3418969 : Blo 2025435 3418969 := bstep (se 2 (by rfl) ⟨1282113, by rfl⟩ : syracuseStep 3418969 = 2564227) B2564227
theorem B4558625 : Blo 2025435 4558625 := bstep (se 2 (by rfl) ⟨1709484, by rfl⟩ : syracuseStep 4558625 = 3418969) B3418969
theorem B3039083 : Blo 2025435 3039083 := bstep (se 1 (by rfl) ⟨2279312, by rfl⟩ : syracuseStep 3039083 = 4558625) B4558625
theorem B2026055 : Blo 2025435 2026055 := bstep (se 1 (by rfl) ⟨1519541, by rfl⟩ : syracuseStep 2026055 = 3039083) B3039083
theorem B2279317 : Blo 2025435 2279317 := bbase (se 6 (by rfl) ⟨53421, by rfl⟩ : syracuseStep 2279317 = 106843) (by norm_num)
theorem B3039089 : Blo 2025435 3039089 := bstep (se 2 (by rfl) ⟨1139658, by rfl⟩ : syracuseStep 3039089 = 2279317) B2279317
theorem B2026059 : Blo 2025435 2026059 := bstep (se 1 (by rfl) ⟨1519544, by rfl⟩ : syracuseStep 2026059 = 3039089) B3039089
theorem B2564237 : Blo 2025435 2564237 := bbase (se 3 (by rfl) ⟨480794, by rfl⟩ : syracuseStep 2564237 = 961589) (by norm_num)
theorem B6837965 : Blo 2025435 6837965 := bstep (se 3 (by rfl) ⟨1282118, by rfl⟩ : syracuseStep 6837965 = 2564237) B2564237
theorem B4558643 : Blo 2025435 4558643 := bstep (se 1 (by rfl) ⟨3418982, by rfl⟩ : syracuseStep 4558643 = 6837965) B6837965
theorem B3039095 : Blo 2025435 3039095 := bstep (se 1 (by rfl) ⟨2279321, by rfl⟩ : syracuseStep 3039095 = 4558643) B4558643
theorem B2026063 : Blo 2025435 2026063 := bstep (se 1 (by rfl) ⟨1519547, by rfl⟩ : syracuseStep 2026063 = 3039095) B3039095
theorem B3039101 : Blo 2025435 3039101 := bbase (se 3 (by rfl) ⟨569831, by rfl⟩ : syracuseStep 3039101 = 1139663) (by norm_num)
theorem B2026067 : Blo 2025435 2026067 := bstep (se 1 (by rfl) ⟨1519550, by rfl⟩ : syracuseStep 2026067 = 3039101) B3039101
theorem B4558661 : Blo 2025435 4558661 := bbase (se 4 (by rfl) ⟨427374, by rfl⟩ : syracuseStep 4558661 = 854749) (by norm_num)
theorem B3039107 : Blo 2025435 3039107 := bstep (se 1 (by rfl) ⟨2279330, by rfl⟩ : syracuseStep 3039107 = 4558661) B4558661
theorem B2026071 : Blo 2025435 2026071 := bstep (se 1 (by rfl) ⟨1519553, by rfl⟩ : syracuseStep 2026071 = 3039107) B3039107
theorem B24980885 : Blo 2025435 24980885 := bbase (se 6 (by rfl) ⟨585489, by rfl⟩ : syracuseStep 24980885 = 1170979) (by norm_num)
theorem B16653923 : Blo 2025435 16653923 := bstep (se 1 (by rfl) ⟨12490442, by rfl⟩ : syracuseStep 16653923 = 24980885) B24980885
theorem B11102615 : Blo 2025435 11102615 := bstep (se 1 (by rfl) ⟨8326961, by rfl⟩ : syracuseStep 11102615 = 16653923) B16653923
theorem B7401743 : Blo 2025435 7401743 := bstep (se 1 (by rfl) ⟨5551307, by rfl⟩ : syracuseStep 7401743 = 11102615) B11102615
theorem B4934495 : Blo 2025435 4934495 := bstep (se 1 (by rfl) ⟨3700871, by rfl⟩ : syracuseStep 4934495 = 7401743) B7401743
theorem B3289663 : Blo 2025435 3289663 := bstep (se 1 (by rfl) ⟨2467247, by rfl⟩ : syracuseStep 3289663 = 4934495) B4934495
theorem B4386217 : Blo 2025435 4386217 := bstep (se 2 (by rfl) ⟨1644831, by rfl⟩ : syracuseStep 4386217 = 3289663) B3289663
theorem B5848289 : Blo 2025435 5848289 := bstep (se 2 (by rfl) ⟨2193108, by rfl⟩ : syracuseStep 5848289 = 4386217) B4386217
theorem B3898859 : Blo 2025435 3898859 := bstep (se 1 (by rfl) ⟨2924144, by rfl⟩ : syracuseStep 3898859 = 5848289) B5848289
theorem B10396957 : Blo 2025435 10396957 := bstep (se 3 (by rfl) ⟨1949429, by rfl⟩ : syracuseStep 10396957 = 3898859) B3898859
theorem B13862609 : Blo 2025435 13862609 := bstep (se 2 (by rfl) ⟨5198478, by rfl⟩ : syracuseStep 13862609 = 10396957) B10396957
theorem B9241739 : Blo 2025435 9241739 := bstep (se 1 (by rfl) ⟨6931304, by rfl⟩ : syracuseStep 9241739 = 13862609) B13862609
theorem B6161159 : Blo 2025435 6161159 := bstep (se 1 (by rfl) ⟨4620869, by rfl⟩ : syracuseStep 6161159 = 9241739) B9241739
theorem B4107439 : Blo 2025435 4107439 := bstep (se 1 (by rfl) ⟨3080579, by rfl⟩ : syracuseStep 4107439 = 6161159) B6161159
theorem B5476585 : Blo 2025435 5476585 := bstep (se 2 (by rfl) ⟨2053719, by rfl⟩ : syracuseStep 5476585 = 4107439) B4107439
theorem B7302113 : Blo 2025435 7302113 := bstep (se 2 (by rfl) ⟨2738292, by rfl⟩ : syracuseStep 7302113 = 5476585) B5476585
theorem B4868075 : Blo 2025435 4868075 := bstep (se 1 (by rfl) ⟨3651056, by rfl⟩ : syracuseStep 4868075 = 7302113) B7302113
theorem B3245383 : Blo 2025435 3245383 := bstep (se 1 (by rfl) ⟨2434037, by rfl⟩ : syracuseStep 3245383 = 4868075) B4868075
theorem B4327177 : Blo 2025435 4327177 := bstep (se 2 (by rfl) ⟨1622691, by rfl⟩ : syracuseStep 4327177 = 3245383) B3245383
theorem B5769569 : Blo 2025435 5769569 := bstep (se 2 (by rfl) ⟨2163588, by rfl⟩ : syracuseStep 5769569 = 4327177) B4327177
theorem B3846379 : Blo 2025435 3846379 := bstep (se 1 (by rfl) ⟨2884784, by rfl⟩ : syracuseStep 3846379 = 5769569) B5769569
theorem B5128505 : Blo 2025435 5128505 := bstep (se 2 (by rfl) ⟨1923189, by rfl⟩ : syracuseStep 5128505 = 3846379) B3846379
theorem B3419003 : Blo 2025435 3419003 := bstep (se 1 (by rfl) ⟨2564252, by rfl⟩ : syracuseStep 3419003 = 5128505) B5128505
theorem B2279335 : Blo 2025435 2279335 := bstep (se 1 (by rfl) ⟨1709501, by rfl⟩ : syracuseStep 2279335 = 3419003) B3419003
theorem B3039113 : Blo 2025435 3039113 := bstep (se 2 (by rfl) ⟨1139667, by rfl⟩ : syracuseStep 3039113 = 2279335) B2279335
theorem B2026075 : Blo 2025435 2026075 := bstep (se 1 (by rfl) ⟨1519556, by rfl⟩ : syracuseStep 2026075 = 3039113) B3039113
theorem B10257029 : Blo 2025435 10257029 := bbase (se 4 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 10257029 = 1923193) (by norm_num)
theorem B6838019 : Blo 2025435 6838019 := bstep (se 1 (by rfl) ⟨5128514, by rfl⟩ : syracuseStep 6838019 = 10257029) B10257029
theorem B4558679 : Blo 2025435 4558679 := bstep (se 1 (by rfl) ⟨3419009, by rfl⟩ : syracuseStep 4558679 = 6838019) B6838019
theorem B3039119 : Blo 2025435 3039119 := bstep (se 1 (by rfl) ⟨2279339, by rfl⟩ : syracuseStep 3039119 = 4558679) B4558679
theorem B2026079 : Blo 2025435 2026079 := bstep (se 1 (by rfl) ⟨1519559, by rfl⟩ : syracuseStep 2026079 = 3039119) B3039119
theorem B3039125 : Blo 2025435 3039125 := bbase (se 6 (by rfl) ⟨71229, by rfl⟩ : syracuseStep 3039125 = 142459) (by norm_num)
theorem B2026083 : Blo 2025435 2026083 := bstep (se 1 (by rfl) ⟨1519562, by rfl⟩ : syracuseStep 2026083 = 3039125) B3039125
theorem B2163601 : Blo 2025435 2163601 := bbase (se 2 (by rfl) ⟨811350, by rfl⟩ : syracuseStep 2163601 = 1622701) (by norm_num)
theorem B11539205 : Blo 2025435 11539205 := bstep (se 4 (by rfl) ⟨1081800, by rfl⟩ : syracuseStep 11539205 = 2163601) B2163601
theorem B7692803 : Blo 2025435 7692803 := bstep (se 1 (by rfl) ⟨5769602, by rfl⟩ : syracuseStep 7692803 = 11539205) B11539205
theorem B5128535 : Blo 2025435 5128535 := bstep (se 1 (by rfl) ⟨3846401, by rfl⟩ : syracuseStep 5128535 = 7692803) B7692803
theorem B3419023 : Blo 2025435 3419023 := bstep (se 1 (by rfl) ⟨2564267, by rfl⟩ : syracuseStep 3419023 = 5128535) B5128535
theorem B4558697 : Blo 2025435 4558697 := bstep (se 2 (by rfl) ⟨1709511, by rfl⟩ : syracuseStep 4558697 = 3419023) B3419023
theorem B3039131 : Blo 2025435 3039131 := bstep (se 1 (by rfl) ⟨2279348, by rfl⟩ : syracuseStep 3039131 = 4558697) B4558697
theorem B2026087 : Blo 2025435 2026087 := bstep (se 1 (by rfl) ⟨1519565, by rfl⟩ : syracuseStep 2026087 = 3039131) B3039131
theorem B2279353 : Blo 2025435 2279353 := bbase (se 2 (by rfl) ⟨854757, by rfl⟩ : syracuseStep 2279353 = 1709515) (by norm_num)
theorem B3039137 : Blo 2025435 3039137 := bstep (se 2 (by rfl) ⟨1139676, by rfl⟩ : syracuseStep 3039137 = 2279353) B2279353
theorem B2026091 : Blo 2025435 2026091 := bstep (se 1 (by rfl) ⟨1519568, by rfl⟩ : syracuseStep 2026091 = 3039137) B3039137
theorem B2434061 : Blo 2025435 2434061 := bbase (se 3 (by rfl) ⟨456386, by rfl⟩ : syracuseStep 2434061 = 912773) (by norm_num)
theorem B6490829 : Blo 2025435 6490829 := bstep (se 3 (by rfl) ⟨1217030, by rfl⟩ : syracuseStep 6490829 = 2434061) B2434061
theorem B4327219 : Blo 2025435 4327219 := bstep (se 1 (by rfl) ⟨3245414, by rfl⟩ : syracuseStep 4327219 = 6490829) B6490829
theorem B5769625 : Blo 2025435 5769625 := bstep (se 2 (by rfl) ⟨2163609, by rfl⟩ : syracuseStep 5769625 = 4327219) B4327219
theorem B7692833 : Blo 2025435 7692833 := bstep (se 2 (by rfl) ⟨2884812, by rfl⟩ : syracuseStep 7692833 = 5769625) B5769625
theorem B5128555 : Blo 2025435 5128555 := bstep (se 1 (by rfl) ⟨3846416, by rfl⟩ : syracuseStep 5128555 = 7692833) B7692833
theorem B6838073 : Blo 2025435 6838073 := bstep (se 2 (by rfl) ⟨2564277, by rfl⟩ : syracuseStep 6838073 = 5128555) B5128555
theorem B4558715 : Blo 2025435 4558715 := bstep (se 1 (by rfl) ⟨3419036, by rfl⟩ : syracuseStep 4558715 = 6838073) B6838073
theorem B3039143 : Blo 2025435 3039143 := bstep (se 1 (by rfl) ⟨2279357, by rfl⟩ : syracuseStep 3039143 = 4558715) B4558715
theorem B2026095 : Blo 2025435 2026095 := bstep (se 1 (by rfl) ⟨1519571, by rfl⟩ : syracuseStep 2026095 = 3039143) B3039143
theorem B3039149 : Blo 2025435 3039149 := bbase (se 3 (by rfl) ⟨569840, by rfl⟩ : syracuseStep 3039149 = 1139681) (by norm_num)
theorem B2026099 : Blo 2025435 2026099 := bstep (se 1 (by rfl) ⟨1519574, by rfl⟩ : syracuseStep 2026099 = 3039149) B3039149
theorem B4558733 : Blo 2025435 4558733 := bbase (se 3 (by rfl) ⟨854762, by rfl⟩ : syracuseStep 4558733 = 1709525) (by norm_num)
theorem B3039155 : Blo 2025435 3039155 := bstep (se 1 (by rfl) ⟨2279366, by rfl⟩ : syracuseStep 3039155 = 4558733) B4558733
theorem B2026103 : Blo 2025435 2026103 := bstep (se 1 (by rfl) ⟨1519577, by rfl⟩ : syracuseStep 2026103 = 3039155) B3039155
theorem B2564293 : Blo 2025435 2564293 := bbase (se 4 (by rfl) ⟨240402, by rfl⟩ : syracuseStep 2564293 = 480805) (by norm_num)
theorem B3419057 : Blo 2025435 3419057 := bstep (se 2 (by rfl) ⟨1282146, by rfl⟩ : syracuseStep 3419057 = 2564293) B2564293
theorem B2279371 : Blo 2025435 2279371 := bstep (se 1 (by rfl) ⟨1709528, by rfl⟩ : syracuseStep 2279371 = 3419057) B3419057
theorem B3039161 : Blo 2025435 3039161 := bstep (se 2 (by rfl) ⟨1139685, by rfl⟩ : syracuseStep 3039161 = 2279371) B2279371
theorem B2026107 : Blo 2025435 2026107 := bstep (se 1 (by rfl) ⟨1519580, by rfl⟩ : syracuseStep 2026107 = 3039161) B3039161
theorem B3751429 : Blo 2025435 3751429 := bbase (se 4 (by rfl) ⟨351696, by rfl⟩ : syracuseStep 3751429 = 703393) (by norm_num)
theorem B5001905 : Blo 2025435 5001905 := bstep (se 2 (by rfl) ⟨1875714, by rfl⟩ : syracuseStep 5001905 = 3751429) B3751429
theorem B3334603 : Blo 2025435 3334603 := bstep (se 1 (by rfl) ⟨2500952, by rfl⟩ : syracuseStep 3334603 = 5001905) B5001905
theorem B4446137 : Blo 2025435 4446137 := bstep (se 2 (by rfl) ⟨1667301, by rfl⟩ : syracuseStep 4446137 = 3334603) B3334603
theorem B11856365 : Blo 2025435 11856365 := bstep (se 3 (by rfl) ⟨2223068, by rfl⟩ : syracuseStep 11856365 = 4446137) B4446137
theorem B7904243 : Blo 2025435 7904243 := bstep (se 1 (by rfl) ⟨5928182, by rfl⟩ : syracuseStep 7904243 = 11856365) B11856365
theorem B5269495 : Blo 2025435 5269495 := bstep (se 1 (by rfl) ⟨3952121, by rfl⟩ : syracuseStep 5269495 = 7904243) B7904243
theorem B7025993 : Blo 2025435 7025993 := bstep (se 2 (by rfl) ⟨2634747, by rfl⟩ : syracuseStep 7025993 = 5269495) B5269495
theorem B4683995 : Blo 2025435 4683995 := bstep (se 1 (by rfl) ⟨3512996, by rfl⟩ : syracuseStep 4683995 = 7025993) B7025993
theorem B3122663 : Blo 2025435 3122663 := bstep (se 1 (by rfl) ⟨2341997, by rfl⟩ : syracuseStep 3122663 = 4683995) B4683995
theorem B33308405 : Blo 2025435 33308405 := bstep (se 5 (by rfl) ⟨1561331, by rfl⟩ : syracuseStep 33308405 = 3122663) B3122663
theorem B22205603 : Blo 2025435 22205603 := bstep (se 1 (by rfl) ⟨16654202, by rfl⟩ : syracuseStep 22205603 = 33308405) B33308405
theorem B14803735 : Blo 2025435 14803735 := bstep (se 1 (by rfl) ⟨11102801, by rfl⟩ : syracuseStep 14803735 = 22205603) B22205603
theorem B19738313 : Blo 2025435 19738313 := bstep (se 2 (by rfl) ⟨7401867, by rfl⟩ : syracuseStep 19738313 = 14803735) B14803735
theorem B13158875 : Blo 2025435 13158875 := bstep (se 1 (by rfl) ⟨9869156, by rfl⟩ : syracuseStep 13158875 = 19738313) B19738313
theorem B8772583 : Blo 2025435 8772583 := bstep (se 1 (by rfl) ⟨6579437, by rfl⟩ : syracuseStep 8772583 = 13158875) B13158875
theorem B11696777 : Blo 2025435 11696777 := bstep (se 2 (by rfl) ⟨4386291, by rfl⟩ : syracuseStep 11696777 = 8772583) B8772583
theorem B7797851 : Blo 2025435 7797851 := bstep (se 1 (by rfl) ⟨5848388, by rfl⟩ : syracuseStep 7797851 = 11696777) B11696777
theorem B83177077 : Blo 2025435 83177077 := bstep (se 5 (by rfl) ⟨3898925, by rfl⟩ : syracuseStep 83177077 = 7797851) B7797851
theorem B110902769 : Blo 2025435 110902769 := bstep (se 2 (by rfl) ⟨41588538, by rfl⟩ : syracuseStep 110902769 = 83177077) B83177077
theorem B73935179 : Blo 2025435 73935179 := bstep (se 1 (by rfl) ⟨55451384, by rfl⟩ : syracuseStep 73935179 = 110902769) B110902769
theorem B49290119 : Blo 2025435 49290119 := bstep (se 1 (by rfl) ⟨36967589, by rfl⟩ : syracuseStep 49290119 = 73935179) B73935179
theorem B32860079 : Blo 2025435 32860079 := bstep (se 1 (by rfl) ⟨24645059, by rfl⟩ : syracuseStep 32860079 = 49290119) B49290119
theorem B21906719 : Blo 2025435 21906719 := bstep (se 1 (by rfl) ⟨16430039, by rfl⟩ : syracuseStep 21906719 = 32860079) B32860079
theorem B14604479 : Blo 2025435 14604479 := bstep (se 1 (by rfl) ⟨10953359, by rfl⟩ : syracuseStep 14604479 = 21906719) B21906719
theorem B9736319 : Blo 2025435 9736319 := bstep (se 1 (by rfl) ⟨7302239, by rfl⟩ : syracuseStep 9736319 = 14604479) B14604479
theorem B25963517 : Blo 2025435 25963517 := bstep (se 3 (by rfl) ⟨4868159, by rfl⟩ : syracuseStep 25963517 = 9736319) B9736319
theorem B17309011 : Blo 2025435 17309011 := bstep (se 1 (by rfl) ⟨12981758, by rfl⟩ : syracuseStep 17309011 = 25963517) B25963517
theorem B23078681 : Blo 2025435 23078681 := bstep (se 2 (by rfl) ⟨8654505, by rfl⟩ : syracuseStep 23078681 = 17309011) B17309011
theorem B15385787 : Blo 2025435 15385787 := bstep (se 1 (by rfl) ⟨11539340, by rfl⟩ : syracuseStep 15385787 = 23078681) B23078681
theorem B10257191 : Blo 2025435 10257191 := bstep (se 1 (by rfl) ⟨7692893, by rfl⟩ : syracuseStep 10257191 = 15385787) B15385787
theorem B6838127 : Blo 2025435 6838127 := bstep (se 1 (by rfl) ⟨5128595, by rfl⟩ : syracuseStep 6838127 = 10257191) B10257191
theorem B4558751 : Blo 2025435 4558751 := bstep (se 1 (by rfl) ⟨3419063, by rfl⟩ : syracuseStep 4558751 = 6838127) B6838127
theorem B3039167 : Blo 2025435 3039167 := bstep (se 1 (by rfl) ⟨2279375, by rfl⟩ : syracuseStep 3039167 = 4558751) B4558751
theorem B2026111 : Blo 2025435 2026111 := bstep (se 1 (by rfl) ⟨1519583, by rfl⟩ : syracuseStep 2026111 = 3039167) B3039167
theorem B3039173 : Blo 2025435 3039173 := bbase (se 4 (by rfl) ⟨284922, by rfl⟩ : syracuseStep 3039173 = 569845) (by norm_num)
theorem B2026115 : Blo 2025435 2026115 := bstep (se 1 (by rfl) ⟨1519586, by rfl⟩ : syracuseStep 2026115 = 3039173) B3039173
theorem B3419077 : Blo 2025435 3419077 := bbase (se 4 (by rfl) ⟨320538, by rfl⟩ : syracuseStep 3419077 = 641077) (by norm_num)
theorem B4558769 : Blo 2025435 4558769 := bstep (se 2 (by rfl) ⟨1709538, by rfl⟩ : syracuseStep 4558769 = 3419077) B3419077
theorem B3039179 : Blo 2025435 3039179 := bstep (se 1 (by rfl) ⟨2279384, by rfl⟩ : syracuseStep 3039179 = 4558769) B4558769
theorem B2026119 : Blo 2025435 2026119 := bstep (se 1 (by rfl) ⟨1519589, by rfl⟩ : syracuseStep 2026119 = 3039179) B3039179
theorem B2279389 : Blo 2025435 2279389 := bbase (se 3 (by rfl) ⟨427385, by rfl⟩ : syracuseStep 2279389 = 854771) (by norm_num)
theorem B3039185 : Blo 2025435 3039185 := bstep (se 2 (by rfl) ⟨1139694, by rfl⟩ : syracuseStep 3039185 = 2279389) B2279389
theorem B2026123 : Blo 2025435 2026123 := bstep (se 1 (by rfl) ⟨1519592, by rfl⟩ : syracuseStep 2026123 = 3039185) B3039185
theorem B6838181 : Blo 2025435 6838181 := bbase (se 4 (by rfl) ⟨641079, by rfl⟩ : syracuseStep 6838181 = 1282159) (by norm_num)
theorem B4558787 : Blo 2025435 4558787 := bstep (se 1 (by rfl) ⟨3419090, by rfl⟩ : syracuseStep 4558787 = 6838181) B6838181
theorem B3039191 : Blo 2025435 3039191 := bstep (se 1 (by rfl) ⟨2279393, by rfl⟩ : syracuseStep 3039191 = 4558787) B4558787
theorem B2026127 : Blo 2025435 2026127 := bstep (se 1 (by rfl) ⟨1519595, by rfl⟩ : syracuseStep 2026127 = 3039191) B3039191
theorem B3039197 : Blo 2025435 3039197 := bbase (se 3 (by rfl) ⟨569849, by rfl⟩ : syracuseStep 3039197 = 1139699) (by norm_num)
theorem B2026131 : Blo 2025435 2026131 := bstep (se 1 (by rfl) ⟨1519598, by rfl⟩ : syracuseStep 2026131 = 3039197) B3039197
theorem B4558805 : Blo 2025435 4558805 := bbase (se 7 (by rfl) ⟨53423, by rfl⟩ : syracuseStep 4558805 = 106847) (by norm_num)
theorem B3039203 : Blo 2025435 3039203 := bstep (se 1 (by rfl) ⟨2279402, by rfl⟩ : syracuseStep 3039203 = 4558805) B4558805
theorem B2026135 : Blo 2025435 2026135 := bstep (se 1 (by rfl) ⟨1519601, by rfl⟩ : syracuseStep 2026135 = 3039203) B3039203
theorem B12981941 : Blo 2025435 12981941 := bbase (se 5 (by rfl) ⟨608528, by rfl⟩ : syracuseStep 12981941 = 1217057) (by norm_num)
theorem B8654627 : Blo 2025435 8654627 := bstep (se 1 (by rfl) ⟨6490970, by rfl⟩ : syracuseStep 8654627 = 12981941) B12981941
theorem B5769751 : Blo 2025435 5769751 := bstep (se 1 (by rfl) ⟨4327313, by rfl⟩ : syracuseStep 5769751 = 8654627) B8654627
theorem B7693001 : Blo 2025435 7693001 := bstep (se 2 (by rfl) ⟨2884875, by rfl⟩ : syracuseStep 7693001 = 5769751) B5769751
theorem B5128667 : Blo 2025435 5128667 := bstep (se 1 (by rfl) ⟨3846500, by rfl⟩ : syracuseStep 5128667 = 7693001) B7693001
theorem B3419111 : Blo 2025435 3419111 := bstep (se 1 (by rfl) ⟨2564333, by rfl⟩ : syracuseStep 3419111 = 5128667) B5128667
theorem B2279407 : Blo 2025435 2279407 := bstep (se 1 (by rfl) ⟨1709555, by rfl⟩ : syracuseStep 2279407 = 3419111) B3419111
theorem B3039209 : Blo 2025435 3039209 := bstep (se 2 (by rfl) ⟨1139703, by rfl⟩ : syracuseStep 3039209 = 2279407) B2279407
theorem B2026139 : Blo 2025435 2026139 := bstep (se 1 (by rfl) ⟨1519604, by rfl⟩ : syracuseStep 2026139 = 3039209) B3039209
theorem B4868237 : Blo 2025435 4868237 := bbase (se 3 (by rfl) ⟨912794, by rfl⟩ : syracuseStep 4868237 = 1825589) (by norm_num)
theorem B3245491 : Blo 2025435 3245491 := bstep (se 1 (by rfl) ⟨2434118, by rfl⟩ : syracuseStep 3245491 = 4868237) B4868237
theorem B17309285 : Blo 2025435 17309285 := bstep (se 4 (by rfl) ⟨1622745, by rfl⟩ : syracuseStep 17309285 = 3245491) B3245491
theorem B11539523 : Blo 2025435 11539523 := bstep (se 1 (by rfl) ⟨8654642, by rfl⟩ : syracuseStep 11539523 = 17309285) B17309285
theorem B7693015 : Blo 2025435 7693015 := bstep (se 1 (by rfl) ⟨5769761, by rfl⟩ : syracuseStep 7693015 = 11539523) B11539523
theorem B10257353 : Blo 2025435 10257353 := bstep (se 2 (by rfl) ⟨3846507, by rfl⟩ : syracuseStep 10257353 = 7693015) B7693015
theorem B6838235 : Blo 2025435 6838235 := bstep (se 1 (by rfl) ⟨5128676, by rfl⟩ : syracuseStep 6838235 = 10257353) B10257353
theorem B4558823 : Blo 2025435 4558823 := bstep (se 1 (by rfl) ⟨3419117, by rfl⟩ : syracuseStep 4558823 = 6838235) B6838235
theorem B3039215 : Blo 2025435 3039215 := bstep (se 1 (by rfl) ⟨2279411, by rfl⟩ : syracuseStep 3039215 = 4558823) B4558823
theorem B2026143 : Blo 2025435 2026143 := bstep (se 1 (by rfl) ⟨1519607, by rfl⟩ : syracuseStep 2026143 = 3039215) B3039215
theorem B3039221 : Blo 2025435 3039221 := bbase (se 5 (by rfl) ⟨142463, by rfl⟩ : syracuseStep 3039221 = 284927) (by norm_num)
theorem B2026147 : Blo 2025435 2026147 := bstep (se 1 (by rfl) ⟨1519610, by rfl⟩ : syracuseStep 2026147 = 3039221) B3039221
theorem B2599337 : Blo 2025435 2599337 := bbase (se 2 (by rfl) ⟨974751, by rfl⟩ : syracuseStep 2599337 = 1949503) (by norm_num)
theorem B6931565 : Blo 2025435 6931565 := bstep (se 3 (by rfl) ⟨1299668, by rfl⟩ : syracuseStep 6931565 = 2599337) B2599337
theorem B4621043 : Blo 2025435 4621043 := bstep (se 1 (by rfl) ⟨3465782, by rfl⟩ : syracuseStep 4621043 = 6931565) B6931565
theorem B3080695 : Blo 2025435 3080695 := bstep (se 1 (by rfl) ⟨2310521, by rfl⟩ : syracuseStep 3080695 = 4621043) B4621043
theorem B4107593 : Blo 2025435 4107593 := bstep (se 2 (by rfl) ⟨1540347, by rfl⟩ : syracuseStep 4107593 = 3080695) B3080695
theorem B2738395 : Blo 2025435 2738395 := bstep (se 1 (by rfl) ⟨2053796, by rfl⟩ : syracuseStep 2738395 = 4107593) B4107593
theorem B3651193 : Blo 2025435 3651193 := bstep (se 2 (by rfl) ⟨1369197, by rfl⟩ : syracuseStep 3651193 = 2738395) B2738395
theorem B4868257 : Blo 2025435 4868257 := bstep (se 2 (by rfl) ⟨1825596, by rfl⟩ : syracuseStep 4868257 = 3651193) B3651193
theorem B6491009 : Blo 2025435 6491009 := bstep (se 2 (by rfl) ⟨2434128, by rfl⟩ : syracuseStep 6491009 = 4868257) B4868257
theorem B4327339 : Blo 2025435 4327339 := bstep (se 1 (by rfl) ⟨3245504, by rfl⟩ : syracuseStep 4327339 = 6491009) B6491009
theorem B5769785 : Blo 2025435 5769785 := bstep (se 2 (by rfl) ⟨2163669, by rfl⟩ : syracuseStep 5769785 = 4327339) B4327339
theorem B3846523 : Blo 2025435 3846523 := bstep (se 1 (by rfl) ⟨2884892, by rfl⟩ : syracuseStep 3846523 = 5769785) B5769785
theorem B5128697 : Blo 2025435 5128697 := bstep (se 2 (by rfl) ⟨1923261, by rfl⟩ : syracuseStep 5128697 = 3846523) B3846523
theorem B3419131 : Blo 2025435 3419131 := bstep (se 1 (by rfl) ⟨2564348, by rfl⟩ : syracuseStep 3419131 = 5128697) B5128697
theorem B4558841 : Blo 2025435 4558841 := bstep (se 2 (by rfl) ⟨1709565, by rfl⟩ : syracuseStep 4558841 = 3419131) B3419131
theorem B3039227 : Blo 2025435 3039227 := bstep (se 1 (by rfl) ⟨2279420, by rfl⟩ : syracuseStep 3039227 = 4558841) B4558841
theorem B2026151 : Blo 2025435 2026151 := bstep (se 1 (by rfl) ⟨1519613, by rfl⟩ : syracuseStep 2026151 = 3039227) B3039227
theorem B2279425 : Blo 2025435 2279425 := bbase (se 2 (by rfl) ⟨854784, by rfl⟩ : syracuseStep 2279425 = 1709569) (by norm_num)
theorem B3039233 : Blo 2025435 3039233 := bstep (se 2 (by rfl) ⟨1139712, by rfl⟩ : syracuseStep 3039233 = 2279425) B2279425
theorem B2026155 : Blo 2025435 2026155 := bstep (se 1 (by rfl) ⟨1519616, by rfl⟩ : syracuseStep 2026155 = 3039233) B3039233
theorem B5128717 : Blo 2025435 5128717 := bbase (se 3 (by rfl) ⟨961634, by rfl⟩ : syracuseStep 5128717 = 1923269) (by norm_num)
theorem B6838289 : Blo 2025435 6838289 := bstep (se 2 (by rfl) ⟨2564358, by rfl⟩ : syracuseStep 6838289 = 5128717) B5128717
theorem B4558859 : Blo 2025435 4558859 := bstep (se 1 (by rfl) ⟨3419144, by rfl⟩ : syracuseStep 4558859 = 6838289) B6838289
theorem B3039239 : Blo 2025435 3039239 := bstep (se 1 (by rfl) ⟨2279429, by rfl⟩ : syracuseStep 3039239 = 4558859) B4558859
theorem B2026159 : Blo 2025435 2026159 := bstep (se 1 (by rfl) ⟨1519619, by rfl⟩ : syracuseStep 2026159 = 3039239) B3039239
theorem B3039245 : Blo 2025435 3039245 := bbase (se 3 (by rfl) ⟨569858, by rfl⟩ : syracuseStep 3039245 = 1139717) (by norm_num)
theorem B2026163 : Blo 2025435 2026163 := bstep (se 1 (by rfl) ⟨1519622, by rfl⟩ : syracuseStep 2026163 = 3039245) B3039245
theorem B4558877 : Blo 2025435 4558877 := bbase (se 3 (by rfl) ⟨854789, by rfl⟩ : syracuseStep 4558877 = 1709579) (by norm_num)
theorem B3039251 : Blo 2025435 3039251 := bstep (se 1 (by rfl) ⟨2279438, by rfl⟩ : syracuseStep 3039251 = 4558877) B4558877
theorem B2026167 : Blo 2025435 2026167 := bstep (se 1 (by rfl) ⟨1519625, by rfl⟩ : syracuseStep 2026167 = 3039251) B3039251
theorem B3419165 : Blo 2025435 3419165 := bbase (se 3 (by rfl) ⟨641093, by rfl⟩ : syracuseStep 3419165 = 1282187) (by norm_num)
theorem B2279443 : Blo 2025435 2279443 := bstep (se 1 (by rfl) ⟨1709582, by rfl⟩ : syracuseStep 2279443 = 3419165) B3419165
theorem B3039257 : Blo 2025435 3039257 := bstep (se 2 (by rfl) ⟨1139721, by rfl⟩ : syracuseStep 3039257 = 2279443) B2279443
theorem B2026171 : Blo 2025435 2026171 := bstep (se 1 (by rfl) ⟨1519628, by rfl⟩ : syracuseStep 2026171 = 3039257) B3039257
theorem B5476853 : Blo 2025435 5476853 := bbase (se 5 (by rfl) ⟨256727, by rfl⟩ : syracuseStep 5476853 = 513455) (by norm_num)
theorem B14604941 : Blo 2025435 14604941 := bstep (se 3 (by rfl) ⟨2738426, by rfl⟩ : syracuseStep 14604941 = 5476853) B5476853
theorem B9736627 : Blo 2025435 9736627 := bstep (se 1 (by rfl) ⟨7302470, by rfl⟩ : syracuseStep 9736627 = 14604941) B14604941
theorem B12982169 : Blo 2025435 12982169 := bstep (se 2 (by rfl) ⟨4868313, by rfl⟩ : syracuseStep 12982169 = 9736627) B9736627
theorem B8654779 : Blo 2025435 8654779 := bstep (se 1 (by rfl) ⟨6491084, by rfl⟩ : syracuseStep 8654779 = 12982169) B12982169
theorem B11539705 : Blo 2025435 11539705 := bstep (se 2 (by rfl) ⟨4327389, by rfl⟩ : syracuseStep 11539705 = 8654779) B8654779
theorem B15386273 : Blo 2025435 15386273 := bstep (se 2 (by rfl) ⟨5769852, by rfl⟩ : syracuseStep 15386273 = 11539705) B11539705
theorem B10257515 : Blo 2025435 10257515 := bstep (se 1 (by rfl) ⟨7693136, by rfl⟩ : syracuseStep 10257515 = 15386273) B15386273
theorem B6838343 : Blo 2025435 6838343 := bstep (se 1 (by rfl) ⟨5128757, by rfl⟩ : syracuseStep 6838343 = 10257515) B10257515
theorem B4558895 : Blo 2025435 4558895 := bstep (se 1 (by rfl) ⟨3419171, by rfl⟩ : syracuseStep 4558895 = 6838343) B6838343
theorem B3039263 : Blo 2025435 3039263 := bstep (se 1 (by rfl) ⟨2279447, by rfl⟩ : syracuseStep 3039263 = 4558895) B4558895
theorem B2026175 : Blo 2025435 2026175 := bstep (se 1 (by rfl) ⟨1519631, by rfl⟩ : syracuseStep 2026175 = 3039263) B3039263
theorem B3039269 : Blo 2025435 3039269 := bbase (se 4 (by rfl) ⟨284931, by rfl⟩ : syracuseStep 3039269 = 569863) (by norm_num)
theorem B2026179 : Blo 2025435 2026179 := bstep (se 1 (by rfl) ⟨1519634, by rfl⟩ : syracuseStep 2026179 = 3039269) B3039269
theorem B2564389 : Blo 2025435 2564389 := bbase (se 4 (by rfl) ⟨240411, by rfl⟩ : syracuseStep 2564389 = 480823) (by norm_num)
theorem B3419185 : Blo 2025435 3419185 := bstep (se 2 (by rfl) ⟨1282194, by rfl⟩ : syracuseStep 3419185 = 2564389) B2564389
theorem B4558913 : Blo 2025435 4558913 := bstep (se 2 (by rfl) ⟨1709592, by rfl⟩ : syracuseStep 4558913 = 3419185) B3419185
theorem B3039275 : Blo 2025435 3039275 := bstep (se 1 (by rfl) ⟨2279456, by rfl⟩ : syracuseStep 3039275 = 4558913) B4558913
theorem B2026183 : Blo 2025435 2026183 := bstep (se 1 (by rfl) ⟨1519637, by rfl⟩ : syracuseStep 2026183 = 3039275) B3039275
theorem B2279461 : Blo 2025435 2279461 := bbase (se 4 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 2279461 = 427399) (by norm_num)
theorem B3039281 : Blo 2025435 3039281 := bstep (se 2 (by rfl) ⟨1139730, by rfl⟩ : syracuseStep 3039281 = 2279461) B2279461
theorem B2026187 : Blo 2025435 2026187 := bstep (se 1 (by rfl) ⟨1519640, by rfl⟩ : syracuseStep 2026187 = 3039281) B3039281
theorem B2053837 : Blo 2025435 2053837 := bbase (se 3 (by rfl) ⟨385094, by rfl⟩ : syracuseStep 2053837 = 770189) (by norm_num)
theorem B2738449 : Blo 2025435 2738449 := bstep (se 2 (by rfl) ⟨1026918, by rfl⟩ : syracuseStep 2738449 = 2053837) B2053837
theorem B3651265 : Blo 2025435 3651265 := bstep (se 2 (by rfl) ⟨1369224, by rfl⟩ : syracuseStep 3651265 = 2738449) B2738449
theorem B4868353 : Blo 2025435 4868353 := bstep (se 2 (by rfl) ⟨1825632, by rfl⟩ : syracuseStep 4868353 = 3651265) B3651265
theorem B6491137 : Blo 2025435 6491137 := bstep (se 2 (by rfl) ⟨2434176, by rfl⟩ : syracuseStep 6491137 = 4868353) B4868353
theorem B8654849 : Blo 2025435 8654849 := bstep (se 2 (by rfl) ⟨3245568, by rfl⟩ : syracuseStep 8654849 = 6491137) B6491137
theorem B5769899 : Blo 2025435 5769899 := bstep (se 1 (by rfl) ⟨4327424, by rfl⟩ : syracuseStep 5769899 = 8654849) B8654849
theorem B3846599 : Blo 2025435 3846599 := bstep (se 1 (by rfl) ⟨2884949, by rfl⟩ : syracuseStep 3846599 = 5769899) B5769899
theorem B2564399 : Blo 2025435 2564399 := bstep (se 1 (by rfl) ⟨1923299, by rfl⟩ : syracuseStep 2564399 = 3846599) B3846599
theorem B6838397 : Blo 2025435 6838397 := bstep (se 3 (by rfl) ⟨1282199, by rfl⟩ : syracuseStep 6838397 = 2564399) B2564399
theorem B4558931 : Blo 2025435 4558931 := bstep (se 1 (by rfl) ⟨3419198, by rfl⟩ : syracuseStep 4558931 = 6838397) B6838397
theorem B3039287 : Blo 2025435 3039287 := bstep (se 1 (by rfl) ⟨2279465, by rfl⟩ : syracuseStep 3039287 = 4558931) B4558931
theorem B2026191 : Blo 2025435 2026191 := bstep (se 1 (by rfl) ⟨1519643, by rfl⟩ : syracuseStep 2026191 = 3039287) B3039287
theorem B3039293 : Blo 2025435 3039293 := bbase (se 3 (by rfl) ⟨569867, by rfl⟩ : syracuseStep 3039293 = 1139735) (by norm_num)
theorem B2026195 : Blo 2025435 2026195 := bstep (se 1 (by rfl) ⟨1519646, by rfl⟩ : syracuseStep 2026195 = 3039293) B3039293
theorem B4558949 : Blo 2025435 4558949 := bbase (se 4 (by rfl) ⟨427401, by rfl⟩ : syracuseStep 4558949 = 854803) (by norm_num)
theorem B3039299 : Blo 2025435 3039299 := bstep (se 1 (by rfl) ⟨2279474, by rfl⟩ : syracuseStep 3039299 = 4558949) B4558949
theorem B2026199 : Blo 2025435 2026199 := bstep (se 1 (by rfl) ⟨1519649, by rfl⟩ : syracuseStep 2026199 = 3039299) B3039299
theorem B5128829 : Blo 2025435 5128829 := bbase (se 3 (by rfl) ⟨961655, by rfl⟩ : syracuseStep 5128829 = 1923311) (by norm_num)
theorem B3419219 : Blo 2025435 3419219 := bstep (se 1 (by rfl) ⟨2564414, by rfl⟩ : syracuseStep 3419219 = 5128829) B5128829
theorem B2279479 : Blo 2025435 2279479 := bstep (se 1 (by rfl) ⟨1709609, by rfl⟩ : syracuseStep 2279479 = 3419219) B3419219
theorem B3039305 : Blo 2025435 3039305 := bstep (se 2 (by rfl) ⟨1139739, by rfl⟩ : syracuseStep 3039305 = 2279479) B2279479
theorem B2026203 : Blo 2025435 2026203 := bstep (se 1 (by rfl) ⟨1519652, by rfl⟩ : syracuseStep 2026203 = 3039305) B3039305
theorem B3846629 : Blo 2025435 3846629 := bbase (se 4 (by rfl) ⟨360621, by rfl⟩ : syracuseStep 3846629 = 721243) (by norm_num)
theorem B10257677 : Blo 2025435 10257677 := bstep (se 3 (by rfl) ⟨1923314, by rfl⟩ : syracuseStep 10257677 = 3846629) B3846629
theorem B6838451 : Blo 2025435 6838451 := bstep (se 1 (by rfl) ⟨5128838, by rfl⟩ : syracuseStep 6838451 = 10257677) B10257677
theorem B4558967 : Blo 2025435 4558967 := bstep (se 1 (by rfl) ⟨3419225, by rfl⟩ : syracuseStep 4558967 = 6838451) B6838451
theorem B3039311 : Blo 2025435 3039311 := bstep (se 1 (by rfl) ⟨2279483, by rfl⟩ : syracuseStep 3039311 = 4558967) B4558967
theorem B2026207 : Blo 2025435 2026207 := bstep (se 1 (by rfl) ⟨1519655, by rfl⟩ : syracuseStep 2026207 = 3039311) B3039311
theorem B3039317 : Blo 2025435 3039317 := bbase (se 8 (by rfl) ⟨17808, by rfl⟩ : syracuseStep 3039317 = 35617) (by norm_num)
theorem B2026211 : Blo 2025435 2026211 := bstep (se 1 (by rfl) ⟨1519658, by rfl⟩ : syracuseStep 2026211 = 3039317) B3039317
theorem B36969493 : Blo 2025435 36969493 := bbase (se 6 (by rfl) ⟨866472, by rfl⟩ : syracuseStep 36969493 = 1732945) (by norm_num)
theorem B49292657 : Blo 2025435 49292657 := bstep (se 2 (by rfl) ⟨18484746, by rfl⟩ : syracuseStep 49292657 = 36969493) B36969493
theorem B32861771 : Blo 2025435 32861771 := bstep (se 1 (by rfl) ⟨24646328, by rfl⟩ : syracuseStep 32861771 = 49292657) B49292657
theorem B21907847 : Blo 2025435 21907847 := bstep (se 1 (by rfl) ⟨16430885, by rfl⟩ : syracuseStep 21907847 = 32861771) B32861771
theorem B14605231 : Blo 2025435 14605231 := bstep (se 1 (by rfl) ⟨10953923, by rfl⟩ : syracuseStep 14605231 = 21907847) B21907847
theorem B19473641 : Blo 2025435 19473641 := bstep (se 2 (by rfl) ⟨7302615, by rfl⟩ : syracuseStep 19473641 = 14605231) B14605231
theorem B12982427 : Blo 2025435 12982427 := bstep (se 1 (by rfl) ⟨9736820, by rfl⟩ : syracuseStep 12982427 = 19473641) B19473641
theorem B8654951 : Blo 2025435 8654951 := bstep (se 1 (by rfl) ⟨6491213, by rfl⟩ : syracuseStep 8654951 = 12982427) B12982427
theorem B5769967 : Blo 2025435 5769967 := bstep (se 1 (by rfl) ⟨4327475, by rfl⟩ : syracuseStep 5769967 = 8654951) B8654951
theorem B7693289 : Blo 2025435 7693289 := bstep (se 2 (by rfl) ⟨2884983, by rfl⟩ : syracuseStep 7693289 = 5769967) B5769967
theorem B5128859 : Blo 2025435 5128859 := bstep (se 1 (by rfl) ⟨3846644, by rfl⟩ : syracuseStep 5128859 = 7693289) B7693289
theorem B3419239 : Blo 2025435 3419239 := bstep (se 1 (by rfl) ⟨2564429, by rfl⟩ : syracuseStep 3419239 = 5128859) B5128859
theorem B4558985 : Blo 2025435 4558985 := bstep (se 2 (by rfl) ⟨1709619, by rfl⟩ : syracuseStep 4558985 = 3419239) B3419239
theorem B3039323 : Blo 2025435 3039323 := bstep (se 1 (by rfl) ⟨2279492, by rfl⟩ : syracuseStep 3039323 = 4558985) B4558985
theorem B2026215 : Blo 2025435 2026215 := bstep (se 1 (by rfl) ⟨1519661, by rfl⟩ : syracuseStep 2026215 = 3039323) B3039323
theorem B2279497 : Blo 2025435 2279497 := bbase (se 2 (by rfl) ⟨854811, by rfl⟩ : syracuseStep 2279497 = 1709623) (by norm_num)
theorem B3039329 : Blo 2025435 3039329 := bstep (se 2 (by rfl) ⟨1139748, by rfl⟩ : syracuseStep 3039329 = 2279497) B2279497
theorem B2026219 : Blo 2025435 2026219 := bstep (se 1 (by rfl) ⟨1519664, by rfl⟩ : syracuseStep 2026219 = 3039329) B3039329
theorem B4868429 : Blo 2025435 4868429 := bbase (se 3 (by rfl) ⟨912830, by rfl⟩ : syracuseStep 4868429 = 1825661) (by norm_num)
theorem B12982477 : Blo 2025435 12982477 := bstep (se 3 (by rfl) ⟨2434214, by rfl⟩ : syracuseStep 12982477 = 4868429) B4868429
theorem B17309969 : Blo 2025435 17309969 := bstep (se 2 (by rfl) ⟨6491238, by rfl⟩ : syracuseStep 17309969 = 12982477) B12982477
theorem B11539979 : Blo 2025435 11539979 := bstep (se 1 (by rfl) ⟨8654984, by rfl⟩ : syracuseStep 11539979 = 17309969) B17309969
theorem B7693319 : Blo 2025435 7693319 := bstep (se 1 (by rfl) ⟨5769989, by rfl⟩ : syracuseStep 7693319 = 11539979) B11539979
theorem B5128879 : Blo 2025435 5128879 := bstep (se 1 (by rfl) ⟨3846659, by rfl⟩ : syracuseStep 5128879 = 7693319) B7693319
theorem B6838505 : Blo 2025435 6838505 := bstep (se 2 (by rfl) ⟨2564439, by rfl⟩ : syracuseStep 6838505 = 5128879) B5128879
theorem B4559003 : Blo 2025435 4559003 := bstep (se 1 (by rfl) ⟨3419252, by rfl⟩ : syracuseStep 4559003 = 6838505) B6838505
theorem B3039335 : Blo 2025435 3039335 := bstep (se 1 (by rfl) ⟨2279501, by rfl⟩ : syracuseStep 3039335 = 4559003) B4559003
theorem B2026223 : Blo 2025435 2026223 := bstep (se 1 (by rfl) ⟨1519667, by rfl⟩ : syracuseStep 2026223 = 3039335) B3039335
theorem B3039341 : Blo 2025435 3039341 := bbase (se 3 (by rfl) ⟨569876, by rfl⟩ : syracuseStep 3039341 = 1139753) (by norm_num)
theorem B2026227 : Blo 2025435 2026227 := bstep (se 1 (by rfl) ⟨1519670, by rfl⟩ : syracuseStep 2026227 = 3039341) B3039341
theorem B4559021 : Blo 2025435 4559021 := bbase (se 3 (by rfl) ⟨854816, by rfl⟩ : syracuseStep 4559021 = 1709633) (by norm_num)
theorem B3039347 : Blo 2025435 3039347 := bstep (se 1 (by rfl) ⟨2279510, by rfl⟩ : syracuseStep 3039347 = 4559021) B4559021
theorem B2026231 : Blo 2025435 2026231 := bstep (se 1 (by rfl) ⟨1519673, by rfl⟩ : syracuseStep 2026231 = 3039347) B3039347
theorem B2310617 : Blo 2025435 2310617 := bbase (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) (by norm_num)
theorem B6161645 : Blo 2025435 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B4107763 : Blo 2025435 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B21908069 : Blo 2025435 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B14605379 : Blo 2025435 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B9736919 : Blo 2025435 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B6491279 : Blo 2025435 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B4327519 : Blo 2025435 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B5770025 : Blo 2025435 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B3846683 : Blo 2025435 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B2564455 : Blo 2025435 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B3419273 : Blo 2025435 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B2279515 : Blo 2025435 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B3039353 : Blo 2025435 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B2026235 : Blo 2025435 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B2053885 : Blo 2025435 2053885 := bbase (se 3 (by rfl) ⟨385103, by rfl⟩ : syracuseStep 2053885 = 770207) (by norm_num)
theorem B2738513 : Blo 2025435 2738513 := bstep (se 2 (by rfl) ⟨1026942, by rfl⟩ : syracuseStep 2738513 = 2053885) B2053885
theorem B7302701 : Blo 2025435 7302701 := bstep (se 3 (by rfl) ⟨1369256, by rfl⟩ : syracuseStep 7302701 = 2738513) B2738513
theorem B4868467 : Blo 2025435 4868467 := bstep (se 1 (by rfl) ⟨3651350, by rfl⟩ : syracuseStep 4868467 = 7302701) B7302701
theorem B25965157 : Blo 2025435 25965157 := bstep (se 4 (by rfl) ⟨2434233, by rfl⟩ : syracuseStep 25965157 = 4868467) B4868467
theorem B34620209 : Blo 2025435 34620209 := bstep (se 2 (by rfl) ⟨12982578, by rfl⟩ : syracuseStep 34620209 = 25965157) B25965157
theorem B23080139 : Blo 2025435 23080139 := bstep (se 1 (by rfl) ⟨17310104, by rfl⟩ : syracuseStep 23080139 = 34620209) B34620209
theorem B15386759 : Blo 2025435 15386759 := bstep (se 1 (by rfl) ⟨11540069, by rfl⟩ : syracuseStep 15386759 = 23080139) B23080139
theorem B10257839 : Blo 2025435 10257839 := bstep (se 1 (by rfl) ⟨7693379, by rfl⟩ : syracuseStep 10257839 = 15386759) B15386759
theorem B6838559 : Blo 2025435 6838559 := bstep (se 1 (by rfl) ⟨5128919, by rfl⟩ : syracuseStep 6838559 = 10257839) B10257839
theorem B4559039 : Blo 2025435 4559039 := bstep (se 1 (by rfl) ⟨3419279, by rfl⟩ : syracuseStep 4559039 = 6838559) B6838559
theorem B3039359 : Blo 2025435 3039359 := bstep (se 1 (by rfl) ⟨2279519, by rfl⟩ : syracuseStep 3039359 = 4559039) B4559039
theorem B2026239 : Blo 2025435 2026239 := bstep (se 1 (by rfl) ⟨1519679, by rfl⟩ : syracuseStep 2026239 = 3039359) B3039359
theorem B3039365 : Blo 2025435 3039365 := bbase (se 4 (by rfl) ⟨284940, by rfl⟩ : syracuseStep 3039365 = 569881) (by norm_num)
theorem B2026243 : Blo 2025435 2026243 := bstep (se 1 (by rfl) ⟨1519682, by rfl⟩ : syracuseStep 2026243 = 3039365) B3039365
theorem B3419293 : Blo 2025435 3419293 := bbase (se 3 (by rfl) ⟨641117, by rfl⟩ : syracuseStep 3419293 = 1282235) (by norm_num)
theorem B4559057 : Blo 2025435 4559057 := bstep (se 2 (by rfl) ⟨1709646, by rfl⟩ : syracuseStep 4559057 = 3419293) B3419293
theorem B3039371 : Blo 2025435 3039371 := bstep (se 1 (by rfl) ⟨2279528, by rfl⟩ : syracuseStep 3039371 = 4559057) B4559057
theorem B2026247 : Blo 2025435 2026247 := bstep (se 1 (by rfl) ⟨1519685, by rfl⟩ : syracuseStep 2026247 = 3039371) B3039371
theorem B2279533 : Blo 2025435 2279533 := bbase (se 3 (by rfl) ⟨427412, by rfl⟩ : syracuseStep 2279533 = 854825) (by norm_num)
theorem B3039377 : Blo 2025435 3039377 := bstep (se 2 (by rfl) ⟨1139766, by rfl⟩ : syracuseStep 3039377 = 2279533) B2279533
theorem B2026251 : Blo 2025435 2026251 := bstep (se 1 (by rfl) ⟨1519688, by rfl⟩ : syracuseStep 2026251 = 3039377) B3039377
theorem B6838613 : Blo 2025435 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B4559075 : Blo 2025435 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B3039383 : Blo 2025435 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B2026255 : Blo 2025435 2026255 := bstep (se 1 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 2026255 = 3039383) B3039383
theorem B3039389 : Blo 2025435 3039389 := bbase (se 3 (by rfl) ⟨569885, by rfl⟩ : syracuseStep 3039389 = 1139771) (by norm_num)
theorem B2026259 : Blo 2025435 2026259 := bstep (se 1 (by rfl) ⟨1519694, by rfl⟩ : syracuseStep 2026259 = 3039389) B3039389
theorem B4559093 : Blo 2025435 4559093 := bbase (se 5 (by rfl) ⟨213707, by rfl⟩ : syracuseStep 4559093 = 427415) (by norm_num)
theorem B3039395 : Blo 2025435 3039395 := bstep (se 1 (by rfl) ⟨2279546, by rfl⟩ : syracuseStep 3039395 = 4559093) B4559093
theorem B2026263 : Blo 2025435 2026263 := bstep (se 1 (by rfl) ⟨1519697, by rfl⟩ : syracuseStep 2026263 = 3039395) B3039395
theorem B2310653 : Blo 2025435 2310653 := bbase (se 3 (by rfl) ⟨433247, by rfl⟩ : syracuseStep 2310653 = 866495) (by norm_num)
theorem B6161741 : Blo 2025435 6161741 := bstep (se 3 (by rfl) ⟨1155326, by rfl⟩ : syracuseStep 6161741 = 2310653) B2310653
theorem B4107827 : Blo 2025435 4107827 := bstep (se 1 (by rfl) ⟨3080870, by rfl⟩ : syracuseStep 4107827 = 6161741) B6161741
theorem B10954205 : Blo 2025435 10954205 := bstep (se 3 (by rfl) ⟨2053913, by rfl⟩ : syracuseStep 10954205 = 4107827) B4107827
theorem B7302803 : Blo 2025435 7302803 := bstep (se 1 (by rfl) ⟨5477102, by rfl⟩ : syracuseStep 7302803 = 10954205) B10954205
theorem B19474141 : Blo 2025435 19474141 := bstep (se 3 (by rfl) ⟨3651401, by rfl⟩ : syracuseStep 19474141 = 7302803) B7302803
theorem B25965521 : Blo 2025435 25965521 := bstep (se 2 (by rfl) ⟨9737070, by rfl⟩ : syracuseStep 25965521 = 19474141) B19474141
theorem B17310347 : Blo 2025435 17310347 := bstep (se 1 (by rfl) ⟨12982760, by rfl⟩ : syracuseStep 17310347 = 25965521) B25965521
theorem B11540231 : Blo 2025435 11540231 := bstep (se 1 (by rfl) ⟨8655173, by rfl⟩ : syracuseStep 11540231 = 17310347) B17310347
theorem B7693487 : Blo 2025435 7693487 := bstep (se 1 (by rfl) ⟨5770115, by rfl⟩ : syracuseStep 7693487 = 11540231) B11540231
theorem B5128991 : Blo 2025435 5128991 := bstep (se 1 (by rfl) ⟨3846743, by rfl⟩ : syracuseStep 5128991 = 7693487) B7693487
theorem B3419327 : Blo 2025435 3419327 := bstep (se 1 (by rfl) ⟨2564495, by rfl⟩ : syracuseStep 3419327 = 5128991) B5128991
theorem B2279551 : Blo 2025435 2279551 := bstep (se 1 (by rfl) ⟨1709663, by rfl⟩ : syracuseStep 2279551 = 3419327) B3419327
theorem B3039401 : Blo 2025435 3039401 := bstep (se 2 (by rfl) ⟨1139775, by rfl⟩ : syracuseStep 3039401 = 2279551) B2279551
theorem B2026267 : Blo 2025435 2026267 := bstep (se 1 (by rfl) ⟨1519700, by rfl⟩ : syracuseStep 2026267 = 3039401) B3039401
theorem B2738557 : Blo 2025435 2738557 := bbase (se 3 (by rfl) ⟨513479, by rfl⟩ : syracuseStep 2738557 = 1026959) (by norm_num)
theorem B3651409 : Blo 2025435 3651409 := bstep (se 2 (by rfl) ⟨1369278, by rfl⟩ : syracuseStep 3651409 = 2738557) B2738557
theorem B4868545 : Blo 2025435 4868545 := bstep (se 2 (by rfl) ⟨1825704, by rfl⟩ : syracuseStep 4868545 = 3651409) B3651409
theorem B6491393 : Blo 2025435 6491393 := bstep (se 2 (by rfl) ⟨2434272, by rfl⟩ : syracuseStep 6491393 = 4868545) B4868545
theorem B4327595 : Blo 2025435 4327595 := bstep (se 1 (by rfl) ⟨3245696, by rfl⟩ : syracuseStep 4327595 = 6491393) B6491393
theorem B2885063 : Blo 2025435 2885063 := bstep (se 1 (by rfl) ⟨2163797, by rfl⟩ : syracuseStep 2885063 = 4327595) B4327595
theorem B7693501 : Blo 2025435 7693501 := bstep (se 3 (by rfl) ⟨1442531, by rfl⟩ : syracuseStep 7693501 = 2885063) B2885063
theorem B10258001 : Blo 2025435 10258001 := bstep (se 2 (by rfl) ⟨3846750, by rfl⟩ : syracuseStep 10258001 = 7693501) B7693501
theorem B6838667 : Blo 2025435 6838667 := bstep (se 1 (by rfl) ⟨5129000, by rfl⟩ : syracuseStep 6838667 = 10258001) B10258001
theorem B4559111 : Blo 2025435 4559111 := bstep (se 1 (by rfl) ⟨3419333, by rfl⟩ : syracuseStep 4559111 = 6838667) B6838667
theorem B3039407 : Blo 2025435 3039407 := bstep (se 1 (by rfl) ⟨2279555, by rfl⟩ : syracuseStep 3039407 = 4559111) B4559111
theorem B2026271 : Blo 2025435 2026271 := bstep (se 1 (by rfl) ⟨1519703, by rfl⟩ : syracuseStep 2026271 = 3039407) B3039407
theorem B3039413 : Blo 2025435 3039413 := bbase (se 5 (by rfl) ⟨142472, by rfl⟩ : syracuseStep 3039413 = 284945) (by norm_num)
theorem B2026275 : Blo 2025435 2026275 := bstep (se 1 (by rfl) ⟨1519706, by rfl⟩ : syracuseStep 2026275 = 3039413) B3039413
theorem B5129021 : Blo 2025435 5129021 := bbase (se 3 (by rfl) ⟨961691, by rfl⟩ : syracuseStep 5129021 = 1923383) (by norm_num)
theorem B3419347 : Blo 2025435 3419347 := bstep (se 1 (by rfl) ⟨2564510, by rfl⟩ : syracuseStep 3419347 = 5129021) B5129021
theorem B4559129 : Blo 2025435 4559129 := bstep (se 2 (by rfl) ⟨1709673, by rfl⟩ : syracuseStep 4559129 = 3419347) B3419347
theorem B3039419 : Blo 2025435 3039419 := bstep (se 1 (by rfl) ⟨2279564, by rfl⟩ : syracuseStep 3039419 = 4559129) B4559129
theorem B2026279 : Blo 2025435 2026279 := bstep (se 1 (by rfl) ⟨1519709, by rfl⟩ : syracuseStep 2026279 = 3039419) B3039419
theorem B2279569 : Blo 2025435 2279569 := bbase (se 2 (by rfl) ⟨854838, by rfl⟩ : syracuseStep 2279569 = 1709677) (by norm_num)
theorem B3039425 : Blo 2025435 3039425 := bstep (se 2 (by rfl) ⟨1139784, by rfl⟩ : syracuseStep 3039425 = 2279569) B2279569
theorem B2026283 : Blo 2025435 2026283 := bstep (se 1 (by rfl) ⟨1519712, by rfl⟩ : syracuseStep 2026283 = 3039425) B3039425
theorem B3846781 : Blo 2025435 3846781 := bbase (se 3 (by rfl) ⟨721271, by rfl⟩ : syracuseStep 3846781 = 1442543) (by norm_num)
theorem B5129041 : Blo 2025435 5129041 := bstep (se 2 (by rfl) ⟨1923390, by rfl⟩ : syracuseStep 5129041 = 3846781) B3846781
theorem B6838721 : Blo 2025435 6838721 := bstep (se 2 (by rfl) ⟨2564520, by rfl⟩ : syracuseStep 6838721 = 5129041) B5129041
theorem B4559147 : Blo 2025435 4559147 := bstep (se 1 (by rfl) ⟨3419360, by rfl⟩ : syracuseStep 4559147 = 6838721) B6838721
theorem B3039431 : Blo 2025435 3039431 := bstep (se 1 (by rfl) ⟨2279573, by rfl⟩ : syracuseStep 3039431 = 4559147) B4559147
theorem B2026287 : Blo 2025435 2026287 := bstep (se 1 (by rfl) ⟨1519715, by rfl⟩ : syracuseStep 2026287 = 3039431) B3039431
theorem B3039437 : Blo 2025435 3039437 := bbase (se 3 (by rfl) ⟨569894, by rfl⟩ : syracuseStep 3039437 = 1139789) (by norm_num)
theorem B2026291 : Blo 2025435 2026291 := bstep (se 1 (by rfl) ⟨1519718, by rfl⟩ : syracuseStep 2026291 = 3039437) B3039437
theorem B4559165 : Blo 2025435 4559165 := bbase (se 3 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 4559165 = 1709687) (by norm_num)
theorem B3039443 : Blo 2025435 3039443 := bstep (se 1 (by rfl) ⟨2279582, by rfl⟩ : syracuseStep 3039443 = 4559165) B4559165
theorem B2026295 : Blo 2025435 2026295 := bstep (se 1 (by rfl) ⟨1519721, by rfl⟩ : syracuseStep 2026295 = 3039443) B3039443
theorem B3419381 : Blo 2025435 3419381 := bbase (se 5 (by rfl) ⟨160283, by rfl⟩ : syracuseStep 3419381 = 320567) (by norm_num)
theorem B2279587 : Blo 2025435 2279587 := bstep (se 1 (by rfl) ⟨1709690, by rfl⟩ : syracuseStep 2279587 = 3419381) B3419381
theorem B3039449 : Blo 2025435 3039449 := bstep (se 2 (by rfl) ⟨1139793, by rfl⟩ : syracuseStep 3039449 = 2279587) B2279587
theorem B2026299 : Blo 2025435 2026299 := bstep (se 1 (by rfl) ⟨1519724, by rfl⟩ : syracuseStep 2026299 = 3039449) B3039449
theorem B10539989 : Blo 2025435 10539989 := bbase (se 7 (by rfl) ⟨123515, by rfl⟩ : syracuseStep 10539989 = 247031) (by norm_num)
theorem B7026659 : Blo 2025435 7026659 := bstep (se 1 (by rfl) ⟨5269994, by rfl⟩ : syracuseStep 7026659 = 10539989) B10539989
theorem B4684439 : Blo 2025435 4684439 := bstep (se 1 (by rfl) ⟨3513329, by rfl⟩ : syracuseStep 4684439 = 7026659) B7026659
theorem B12491837 : Blo 2025435 12491837 := bstep (se 3 (by rfl) ⟨2342219, by rfl⟩ : syracuseStep 12491837 = 4684439) B4684439
theorem B8327891 : Blo 2025435 8327891 := bstep (se 1 (by rfl) ⟨6245918, by rfl⟩ : syracuseStep 8327891 = 12491837) B12491837
theorem B5551927 : Blo 2025435 5551927 := bstep (se 1 (by rfl) ⟨4163945, by rfl⟩ : syracuseStep 5551927 = 8327891) B8327891
theorem B118441109 : Blo 2025435 118441109 := bstep (se 6 (by rfl) ⟨2775963, by rfl⟩ : syracuseStep 118441109 = 5551927) B5551927
theorem B78960739 : Blo 2025435 78960739 := bstep (se 1 (by rfl) ⟨59220554, by rfl⟩ : syracuseStep 78960739 = 118441109) B118441109
theorem B105280985 : Blo 2025435 105280985 := bstep (se 2 (by rfl) ⟨39480369, by rfl⟩ : syracuseStep 105280985 = 78960739) B78960739
theorem B70187323 : Blo 2025435 70187323 := bstep (se 1 (by rfl) ⟨52640492, by rfl⟩ : syracuseStep 70187323 = 105280985) B105280985
theorem B93583097 : Blo 2025435 93583097 := bstep (se 2 (by rfl) ⟨35093661, by rfl⟩ : syracuseStep 93583097 = 70187323) B70187323
theorem B62388731 : Blo 2025435 62388731 := bstep (se 1 (by rfl) ⟨46791548, by rfl⟩ : syracuseStep 62388731 = 93583097) B93583097
theorem B41592487 : Blo 2025435 41592487 := bstep (se 1 (by rfl) ⟨31194365, by rfl⟩ : syracuseStep 41592487 = 62388731) B62388731
theorem B55456649 : Blo 2025435 55456649 := bstep (se 2 (by rfl) ⟨20796243, by rfl⟩ : syracuseStep 55456649 = 41592487) B41592487
theorem B36971099 : Blo 2025435 36971099 := bstep (se 1 (by rfl) ⟨27728324, by rfl⟩ : syracuseStep 36971099 = 55456649) B55456649
theorem B24647399 : Blo 2025435 24647399 := bstep (se 1 (by rfl) ⟨18485549, by rfl⟩ : syracuseStep 24647399 = 36971099) B36971099
theorem B16431599 : Blo 2025435 16431599 := bstep (se 1 (by rfl) ⟨12323699, by rfl⟩ : syracuseStep 16431599 = 24647399) B24647399
theorem B10954399 : Blo 2025435 10954399 := bstep (se 1 (by rfl) ⟨8215799, by rfl⟩ : syracuseStep 10954399 = 16431599) B16431599
theorem B14605865 : Blo 2025435 14605865 := bstep (se 2 (by rfl) ⟨5477199, by rfl⟩ : syracuseStep 14605865 = 10954399) B10954399
theorem B9737243 : Blo 2025435 9737243 := bstep (se 1 (by rfl) ⟨7302932, by rfl⟩ : syracuseStep 9737243 = 14605865) B14605865
theorem B6491495 : Blo 2025435 6491495 := bstep (se 1 (by rfl) ⟨4868621, by rfl⟩ : syracuseStep 6491495 = 9737243) B9737243
theorem B4327663 : Blo 2025435 4327663 := bstep (se 1 (by rfl) ⟨3245747, by rfl⟩ : syracuseStep 4327663 = 6491495) B6491495
theorem B5770217 : Blo 2025435 5770217 := bstep (se 2 (by rfl) ⟨2163831, by rfl⟩ : syracuseStep 5770217 = 4327663) B4327663
theorem B15387245 : Blo 2025435 15387245 := bstep (se 3 (by rfl) ⟨2885108, by rfl⟩ : syracuseStep 15387245 = 5770217) B5770217
theorem B10258163 : Blo 2025435 10258163 := bstep (se 1 (by rfl) ⟨7693622, by rfl⟩ : syracuseStep 10258163 = 15387245) B15387245
theorem B6838775 : Blo 2025435 6838775 := bstep (se 1 (by rfl) ⟨5129081, by rfl⟩ : syracuseStep 6838775 = 10258163) B10258163
theorem B4559183 : Blo 2025435 4559183 := bstep (se 1 (by rfl) ⟨3419387, by rfl⟩ : syracuseStep 4559183 = 6838775) B6838775
theorem B3039455 : Blo 2025435 3039455 := bstep (se 1 (by rfl) ⟨2279591, by rfl⟩ : syracuseStep 3039455 = 4559183) B4559183
theorem B2026303 : Blo 2025435 2026303 := bstep (se 1 (by rfl) ⟨1519727, by rfl⟩ : syracuseStep 2026303 = 3039455) B3039455
theorem B3039461 : Blo 2025435 3039461 := bbase (se 4 (by rfl) ⟨284949, by rfl⟩ : syracuseStep 3039461 = 569899) (by norm_num)
theorem B2026307 : Blo 2025435 2026307 := bstep (se 1 (by rfl) ⟨1519730, by rfl⟩ : syracuseStep 2026307 = 3039461) B3039461
theorem B2434321 : Blo 2025435 2434321 := bbase (se 2 (by rfl) ⟨912870, by rfl⟩ : syracuseStep 2434321 = 1825741) (by norm_num)
theorem B3245761 : Blo 2025435 3245761 := bstep (se 2 (by rfl) ⟨1217160, by rfl⟩ : syracuseStep 3245761 = 2434321) B2434321
theorem B4327681 : Blo 2025435 4327681 := bstep (se 2 (by rfl) ⟨1622880, by rfl⟩ : syracuseStep 4327681 = 3245761) B3245761
theorem B5770241 : Blo 2025435 5770241 := bstep (se 2 (by rfl) ⟨2163840, by rfl⟩ : syracuseStep 5770241 = 4327681) B4327681
theorem B3846827 : Blo 2025435 3846827 := bstep (se 1 (by rfl) ⟨2885120, by rfl⟩ : syracuseStep 3846827 = 5770241) B5770241
theorem B2564551 : Blo 2025435 2564551 := bstep (se 1 (by rfl) ⟨1923413, by rfl⟩ : syracuseStep 2564551 = 3846827) B3846827
theorem B3419401 : Blo 2025435 3419401 := bstep (se 2 (by rfl) ⟨1282275, by rfl⟩ : syracuseStep 3419401 = 2564551) B2564551
theorem B4559201 : Blo 2025435 4559201 := bstep (se 2 (by rfl) ⟨1709700, by rfl⟩ : syracuseStep 4559201 = 3419401) B3419401
theorem B3039467 : Blo 2025435 3039467 := bstep (se 1 (by rfl) ⟨2279600, by rfl⟩ : syracuseStep 3039467 = 4559201) B4559201
theorem B2026311 : Blo 2025435 2026311 := bstep (se 1 (by rfl) ⟨1519733, by rfl⟩ : syracuseStep 2026311 = 3039467) B3039467
theorem B2279605 : Blo 2025435 2279605 := bbase (se 5 (by rfl) ⟨106856, by rfl⟩ : syracuseStep 2279605 = 213713) (by norm_num)
theorem B3039473 : Blo 2025435 3039473 := bstep (se 2 (by rfl) ⟨1139802, by rfl⟩ : syracuseStep 3039473 = 2279605) B2279605
theorem B2026315 : Blo 2025435 2026315 := bstep (se 1 (by rfl) ⟨1519736, by rfl⟩ : syracuseStep 2026315 = 3039473) B3039473
theorem B2564561 : Blo 2025435 2564561 := bbase (se 2 (by rfl) ⟨961710, by rfl⟩ : syracuseStep 2564561 = 1923421) (by norm_num)
theorem B6838829 : Blo 2025435 6838829 := bstep (se 3 (by rfl) ⟨1282280, by rfl⟩ : syracuseStep 6838829 = 2564561) B2564561
theorem B4559219 : Blo 2025435 4559219 := bstep (se 1 (by rfl) ⟨3419414, by rfl⟩ : syracuseStep 4559219 = 6838829) B6838829
theorem B3039479 : Blo 2025435 3039479 := bstep (se 1 (by rfl) ⟨2279609, by rfl⟩ : syracuseStep 3039479 = 4559219) B4559219
theorem B2026319 : Blo 2025435 2026319 := bstep (se 1 (by rfl) ⟨1519739, by rfl⟩ : syracuseStep 2026319 = 3039479) B3039479
theorem B3039485 : Blo 2025435 3039485 := bbase (se 3 (by rfl) ⟨569903, by rfl⟩ : syracuseStep 3039485 = 1139807) (by norm_num)
theorem B2026323 : Blo 2025435 2026323 := bstep (se 1 (by rfl) ⟨1519742, by rfl⟩ : syracuseStep 2026323 = 3039485) B3039485
theorem B4559237 : Blo 2025435 4559237 := bbase (se 4 (by rfl) ⟨427428, by rfl⟩ : syracuseStep 4559237 = 854857) (by norm_num)
theorem B3039491 : Blo 2025435 3039491 := bstep (se 1 (by rfl) ⟨2279618, by rfl⟩ : syracuseStep 3039491 = 4559237) B4559237
theorem B2026327 : Blo 2025435 2026327 := bstep (se 1 (by rfl) ⟨1519745, by rfl⟩ : syracuseStep 2026327 = 3039491) B3039491
theorem B2885149 : Blo 2025435 2885149 := bbase (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) (by norm_num)
theorem B3846865 : Blo 2025435 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B5129153 : Blo 2025435 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B3419435 : Blo 2025435 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B2279623 : Blo 2025435 2279623 := bstep (se 1 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 2279623 = 3419435) B3419435
theorem B3039497 : Blo 2025435 3039497 := bstep (se 2 (by rfl) ⟨1139811, by rfl⟩ : syracuseStep 3039497 = 2279623) B2279623
theorem B2026331 : Blo 2025435 2026331 := bstep (se 1 (by rfl) ⟨1519748, by rfl⟩ : syracuseStep 2026331 = 3039497) B3039497
theorem B10258325 : Blo 2025435 10258325 := bbase (se 6 (by rfl) ⟨240429, by rfl⟩ : syracuseStep 10258325 = 480859) (by norm_num)
theorem B6838883 : Blo 2025435 6838883 := bstep (se 1 (by rfl) ⟨5129162, by rfl⟩ : syracuseStep 6838883 = 10258325) B10258325
theorem B4559255 : Blo 2025435 4559255 := bstep (se 1 (by rfl) ⟨3419441, by rfl⟩ : syracuseStep 4559255 = 6838883) B6838883
theorem B3039503 : Blo 2025435 3039503 := bstep (se 1 (by rfl) ⟨2279627, by rfl⟩ : syracuseStep 3039503 = 4559255) B4559255
theorem B2026335 : Blo 2025435 2026335 := bstep (se 1 (by rfl) ⟨1519751, by rfl⟩ : syracuseStep 2026335 = 3039503) B3039503
theorem B3039509 : Blo 2025435 3039509 := bbase (se 6 (by rfl) ⟨71238, by rfl⟩ : syracuseStep 3039509 = 142477) (by norm_num)
theorem B2026339 : Blo 2025435 2026339 := bstep (se 1 (by rfl) ⟨1519754, by rfl⟩ : syracuseStep 2026339 = 3039509) B3039509
theorem B3466109 : Blo 2025435 3466109 := bbase (se 3 (by rfl) ⟨649895, by rfl⟩ : syracuseStep 3466109 = 1299791) (by norm_num)
theorem B9242957 : Blo 2025435 9242957 := bstep (se 3 (by rfl) ⟨1733054, by rfl⟩ : syracuseStep 9242957 = 3466109) B3466109
theorem B24647885 : Blo 2025435 24647885 := bstep (se 3 (by rfl) ⟨4621478, by rfl⟩ : syracuseStep 24647885 = 9242957) B9242957
theorem B16431923 : Blo 2025435 16431923 := bstep (se 1 (by rfl) ⟨12323942, by rfl⟩ : syracuseStep 16431923 = 24647885) B24647885
theorem B10954615 : Blo 2025435 10954615 := bstep (se 1 (by rfl) ⟨8215961, by rfl⟩ : syracuseStep 10954615 = 16431923) B16431923
theorem B14606153 : Blo 2025435 14606153 := bstep (se 2 (by rfl) ⟨5477307, by rfl⟩ : syracuseStep 14606153 = 10954615) B10954615
theorem B9737435 : Blo 2025435 9737435 := bstep (se 1 (by rfl) ⟨7303076, by rfl⟩ : syracuseStep 9737435 = 14606153) B14606153
theorem B25966493 : Blo 2025435 25966493 := bstep (se 3 (by rfl) ⟨4868717, by rfl⟩ : syracuseStep 25966493 = 9737435) B9737435
theorem B17310995 : Blo 2025435 17310995 := bstep (se 1 (by rfl) ⟨12983246, by rfl⟩ : syracuseStep 17310995 = 25966493) B25966493
theorem B11540663 : Blo 2025435 11540663 := bstep (se 1 (by rfl) ⟨8655497, by rfl⟩ : syracuseStep 11540663 = 17310995) B17310995
theorem B7693775 : Blo 2025435 7693775 := bstep (se 1 (by rfl) ⟨5770331, by rfl⟩ : syracuseStep 7693775 = 11540663) B11540663
theorem B5129183 : Blo 2025435 5129183 := bstep (se 1 (by rfl) ⟨3846887, by rfl⟩ : syracuseStep 5129183 = 7693775) B7693775
theorem B3419455 : Blo 2025435 3419455 := bstep (se 1 (by rfl) ⟨2564591, by rfl⟩ : syracuseStep 3419455 = 5129183) B5129183
theorem B4559273 : Blo 2025435 4559273 := bstep (se 2 (by rfl) ⟨1709727, by rfl⟩ : syracuseStep 4559273 = 3419455) B3419455
theorem B3039515 : Blo 2025435 3039515 := bstep (se 1 (by rfl) ⟨2279636, by rfl⟩ : syracuseStep 3039515 = 4559273) B4559273
theorem B2026343 : Blo 2025435 2026343 := bstep (se 1 (by rfl) ⟨1519757, by rfl⟩ : syracuseStep 2026343 = 3039515) B3039515
theorem B2279641 : Blo 2025435 2279641 := bbase (se 2 (by rfl) ⟨854865, by rfl⟩ : syracuseStep 2279641 = 1709731) (by norm_num)
theorem B3039521 : Blo 2025435 3039521 := bstep (se 2 (by rfl) ⟨1139820, by rfl⟩ : syracuseStep 3039521 = 2279641) B2279641
theorem B2026347 : Blo 2025435 2026347 := bstep (se 1 (by rfl) ⟨1519760, by rfl⟩ : syracuseStep 2026347 = 3039521) B3039521
theorem B2434369 : Blo 2025435 2434369 := bbase (se 2 (by rfl) ⟨912888, by rfl⟩ : syracuseStep 2434369 = 1825777) (by norm_num)
theorem B3245825 : Blo 2025435 3245825 := bstep (se 2 (by rfl) ⟨1217184, by rfl⟩ : syracuseStep 3245825 = 2434369) B2434369
theorem B2163883 : Blo 2025435 2163883 := bstep (se 1 (by rfl) ⟨1622912, by rfl⟩ : syracuseStep 2163883 = 3245825) B3245825
theorem B2885177 : Blo 2025435 2885177 := bstep (se 2 (by rfl) ⟨1081941, by rfl⟩ : syracuseStep 2885177 = 2163883) B2163883
theorem B7693805 : Blo 2025435 7693805 := bstep (se 3 (by rfl) ⟨1442588, by rfl⟩ : syracuseStep 7693805 = 2885177) B2885177
theorem B5129203 : Blo 2025435 5129203 := bstep (se 1 (by rfl) ⟨3846902, by rfl⟩ : syracuseStep 5129203 = 7693805) B7693805
theorem B6838937 : Blo 2025435 6838937 := bstep (se 2 (by rfl) ⟨2564601, by rfl⟩ : syracuseStep 6838937 = 5129203) B5129203
theorem B4559291 : Blo 2025435 4559291 := bstep (se 1 (by rfl) ⟨3419468, by rfl⟩ : syracuseStep 4559291 = 6838937) B6838937
theorem B3039527 : Blo 2025435 3039527 := bstep (se 1 (by rfl) ⟨2279645, by rfl⟩ : syracuseStep 3039527 = 4559291) B4559291
theorem B2026351 : Blo 2025435 2026351 := bstep (se 1 (by rfl) ⟨1519763, by rfl⟩ : syracuseStep 2026351 = 3039527) B3039527
theorem B3039533 : Blo 2025435 3039533 := bbase (se 3 (by rfl) ⟨569912, by rfl⟩ : syracuseStep 3039533 = 1139825) (by norm_num)
theorem B2026355 : Blo 2025435 2026355 := bstep (se 1 (by rfl) ⟨1519766, by rfl⟩ : syracuseStep 2026355 = 3039533) B3039533
theorem B4559309 : Blo 2025435 4559309 := bbase (se 3 (by rfl) ⟨854870, by rfl⟩ : syracuseStep 4559309 = 1709741) (by norm_num)
theorem B3039539 : Blo 2025435 3039539 := bstep (se 1 (by rfl) ⟨2279654, by rfl⟩ : syracuseStep 3039539 = 4559309) B4559309
theorem B2026359 : Blo 2025435 2026359 := bstep (se 1 (by rfl) ⟨1519769, by rfl⟩ : syracuseStep 2026359 = 3039539) B3039539
theorem B2564617 : Blo 2025435 2564617 := bbase (se 2 (by rfl) ⟨961731, by rfl⟩ : syracuseStep 2564617 = 1923463) (by norm_num)
theorem B3419489 : Blo 2025435 3419489 := bstep (se 2 (by rfl) ⟨1282308, by rfl⟩ : syracuseStep 3419489 = 2564617) B2564617
theorem B2279659 : Blo 2025435 2279659 := bstep (se 1 (by rfl) ⟨1709744, by rfl⟩ : syracuseStep 2279659 = 3419489) B3419489
theorem B3039545 : Blo 2025435 3039545 := bstep (se 2 (by rfl) ⟨1139829, by rfl⟩ : syracuseStep 3039545 = 2279659) B2279659
theorem B2026363 : Blo 2025435 2026363 := bstep (se 1 (by rfl) ⟨1519772, by rfl⟩ : syracuseStep 2026363 = 3039545) B3039545
theorem B4164077 : Blo 2025435 4164077 := bbase (se 3 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 4164077 = 1561529) (by norm_num)
theorem B2776051 : Blo 2025435 2776051 := bstep (se 1 (by rfl) ⟨2082038, by rfl⟩ : syracuseStep 2776051 = 4164077) B4164077
theorem B14805605 : Blo 2025435 14805605 := bstep (se 4 (by rfl) ⟨1388025, by rfl⟩ : syracuseStep 14805605 = 2776051) B2776051
theorem B9870403 : Blo 2025435 9870403 := bstep (se 1 (by rfl) ⟨7402802, by rfl⟩ : syracuseStep 9870403 = 14805605) B14805605
theorem B13160537 : Blo 2025435 13160537 := bstep (se 2 (by rfl) ⟨4935201, by rfl⟩ : syracuseStep 13160537 = 9870403) B9870403
theorem B8773691 : Blo 2025435 8773691 := bstep (se 1 (by rfl) ⟨6580268, by rfl⟩ : syracuseStep 8773691 = 13160537) B13160537
theorem B23396509 : Blo 2025435 23396509 := bstep (se 3 (by rfl) ⟨4386845, by rfl⟩ : syracuseStep 23396509 = 8773691) B8773691
theorem B124781381 : Blo 2025435 124781381 := bstep (se 4 (by rfl) ⟨11698254, by rfl⟩ : syracuseStep 124781381 = 23396509) B23396509
theorem B83187587 : Blo 2025435 83187587 := bstep (se 1 (by rfl) ⟨62390690, by rfl⟩ : syracuseStep 83187587 = 124781381) B124781381
theorem B55458391 : Blo 2025435 55458391 := bstep (se 1 (by rfl) ⟨41593793, by rfl⟩ : syracuseStep 55458391 = 83187587) B83187587
theorem B73944521 : Blo 2025435 73944521 := bstep (se 2 (by rfl) ⟨27729195, by rfl⟩ : syracuseStep 73944521 = 55458391) B55458391
theorem B49296347 : Blo 2025435 49296347 := bstep (se 1 (by rfl) ⟨36972260, by rfl⟩ : syracuseStep 49296347 = 73944521) B73944521
theorem B32864231 : Blo 2025435 32864231 := bstep (se 1 (by rfl) ⟨24648173, by rfl⟩ : syracuseStep 32864231 = 49296347) B49296347
theorem B21909487 : Blo 2025435 21909487 := bstep (se 1 (by rfl) ⟨16432115, by rfl⟩ : syracuseStep 21909487 = 32864231) B32864231
theorem B29212649 : Blo 2025435 29212649 := bstep (se 2 (by rfl) ⟨10954743, by rfl⟩ : syracuseStep 29212649 = 21909487) B21909487
theorem B19475099 : Blo 2025435 19475099 := bstep (se 1 (by rfl) ⟨14606324, by rfl⟩ : syracuseStep 19475099 = 29212649) B29212649
theorem B12983399 : Blo 2025435 12983399 := bstep (se 1 (by rfl) ⟨9737549, by rfl⟩ : syracuseStep 12983399 = 19475099) B19475099
theorem B8655599 : Blo 2025435 8655599 := bstep (se 1 (by rfl) ⟨6491699, by rfl⟩ : syracuseStep 8655599 = 12983399) B12983399
theorem B23081597 : Blo 2025435 23081597 := bstep (se 3 (by rfl) ⟨4327799, by rfl⟩ : syracuseStep 23081597 = 8655599) B8655599
theorem B15387731 : Blo 2025435 15387731 := bstep (se 1 (by rfl) ⟨11540798, by rfl⟩ : syracuseStep 15387731 = 23081597) B23081597
theorem B10258487 : Blo 2025435 10258487 := bstep (se 1 (by rfl) ⟨7693865, by rfl⟩ : syracuseStep 10258487 = 15387731) B15387731
theorem B6838991 : Blo 2025435 6838991 := bstep (se 1 (by rfl) ⟨5129243, by rfl⟩ : syracuseStep 6838991 = 10258487) B10258487
theorem B4559327 : Blo 2025435 4559327 := bstep (se 1 (by rfl) ⟨3419495, by rfl⟩ : syracuseStep 4559327 = 6838991) B6838991
theorem B3039551 : Blo 2025435 3039551 := bstep (se 1 (by rfl) ⟨2279663, by rfl⟩ : syracuseStep 3039551 = 4559327) B4559327
theorem B2026367 : Blo 2025435 2026367 := bstep (se 1 (by rfl) ⟨1519775, by rfl⟩ : syracuseStep 2026367 = 3039551) B3039551
theorem B3039557 : Blo 2025435 3039557 := bbase (se 4 (by rfl) ⟨284958, by rfl⟩ : syracuseStep 3039557 = 569917) (by norm_num)
theorem B2026371 : Blo 2025435 2026371 := bstep (se 1 (by rfl) ⟨1519778, by rfl⟩ : syracuseStep 2026371 = 3039557) B3039557
theorem B3419509 : Blo 2025435 3419509 := bbase (se 5 (by rfl) ⟨160289, by rfl⟩ : syracuseStep 3419509 = 320579) (by norm_num)
theorem B4559345 : Blo 2025435 4559345 := bstep (se 2 (by rfl) ⟨1709754, by rfl⟩ : syracuseStep 4559345 = 3419509) B3419509
theorem B3039563 : Blo 2025435 3039563 := bstep (se 1 (by rfl) ⟨2279672, by rfl⟩ : syracuseStep 3039563 = 4559345) B4559345
theorem B2026375 : Blo 2025435 2026375 := bstep (se 1 (by rfl) ⟨1519781, by rfl⟩ : syracuseStep 2026375 = 3039563) B3039563
theorem B2279677 : Blo 2025435 2279677 := bbase (se 3 (by rfl) ⟨427439, by rfl⟩ : syracuseStep 2279677 = 854879) (by norm_num)
theorem B3039569 : Blo 2025435 3039569 := bstep (se 2 (by rfl) ⟨1139838, by rfl⟩ : syracuseStep 3039569 = 2279677) B2279677
theorem B2026379 : Blo 2025435 2026379 := bstep (se 1 (by rfl) ⟨1519784, by rfl⟩ : syracuseStep 2026379 = 3039569) B3039569
theorem B6839045 : Blo 2025435 6839045 := bbase (se 4 (by rfl) ⟨641160, by rfl⟩ : syracuseStep 6839045 = 1282321) (by norm_num)
theorem B4559363 : Blo 2025435 4559363 := bstep (se 1 (by rfl) ⟨3419522, by rfl⟩ : syracuseStep 4559363 = 6839045) B6839045
theorem B3039575 : Blo 2025435 3039575 := bstep (se 1 (by rfl) ⟨2279681, by rfl⟩ : syracuseStep 3039575 = 4559363) B4559363
theorem B2026383 : Blo 2025435 2026383 := bstep (se 1 (by rfl) ⟨1519787, by rfl⟩ : syracuseStep 2026383 = 3039575) B3039575
theorem B3039581 : Blo 2025435 3039581 := bbase (se 3 (by rfl) ⟨569921, by rfl⟩ : syracuseStep 3039581 = 1139843) (by norm_num)
theorem B2026387 : Blo 2025435 2026387 := bstep (se 1 (by rfl) ⟨1519790, by rfl⟩ : syracuseStep 2026387 = 3039581) B3039581
theorem B4559381 : Blo 2025435 4559381 := bbase (se 6 (by rfl) ⟨106860, by rfl⟩ : syracuseStep 4559381 = 213721) (by norm_num)
theorem B3039587 : Blo 2025435 3039587 := bstep (se 1 (by rfl) ⟨2279690, by rfl⟩ : syracuseStep 3039587 = 4559381) B4559381
theorem B2026391 : Blo 2025435 2026391 := bstep (se 1 (by rfl) ⟨1519793, by rfl⟩ : syracuseStep 2026391 = 3039587) B3039587
theorem B7693973 : Blo 2025435 7693973 := bbase (se 6 (by rfl) ⟨180327, by rfl⟩ : syracuseStep 7693973 = 360655) (by norm_num)
theorem B5129315 : Blo 2025435 5129315 := bstep (se 1 (by rfl) ⟨3846986, by rfl⟩ : syracuseStep 5129315 = 7693973) B7693973
theorem B3419543 : Blo 2025435 3419543 := bstep (se 1 (by rfl) ⟨2564657, by rfl⟩ : syracuseStep 3419543 = 5129315) B5129315
theorem B2279695 : Blo 2025435 2279695 := bstep (se 1 (by rfl) ⟨1709771, by rfl⟩ : syracuseStep 2279695 = 3419543) B3419543
theorem B3039593 : Blo 2025435 3039593 := bstep (se 2 (by rfl) ⟨1139847, by rfl⟩ : syracuseStep 3039593 = 2279695) B2279695
theorem B2026395 : Blo 2025435 2026395 := bstep (se 1 (by rfl) ⟨1519796, by rfl⟩ : syracuseStep 2026395 = 3039593) B3039593
theorem B11540981 : Blo 2025435 11540981 := bbase (se 5 (by rfl) ⟨540983, by rfl⟩ : syracuseStep 11540981 = 1081967) (by norm_num)
theorem B7693987 : Blo 2025435 7693987 := bstep (se 1 (by rfl) ⟨5770490, by rfl⟩ : syracuseStep 7693987 = 11540981) B11540981
theorem B10258649 : Blo 2025435 10258649 := bstep (se 2 (by rfl) ⟨3846993, by rfl⟩ : syracuseStep 10258649 = 7693987) B7693987
theorem B6839099 : Blo 2025435 6839099 := bstep (se 1 (by rfl) ⟨5129324, by rfl⟩ : syracuseStep 6839099 = 10258649) B10258649
theorem B4559399 : Blo 2025435 4559399 := bstep (se 1 (by rfl) ⟨3419549, by rfl⟩ : syracuseStep 4559399 = 6839099) B6839099
theorem B3039599 : Blo 2025435 3039599 := bstep (se 1 (by rfl) ⟨2279699, by rfl⟩ : syracuseStep 3039599 = 4559399) B4559399
theorem B2026399 : Blo 2025435 2026399 := bstep (se 1 (by rfl) ⟨1519799, by rfl⟩ : syracuseStep 2026399 = 3039599) B3039599
theorem B3039605 : Blo 2025435 3039605 := bbase (se 5 (by rfl) ⟨142481, by rfl⟩ : syracuseStep 3039605 = 284963) (by norm_num)
theorem B2026403 : Blo 2025435 2026403 := bstep (se 1 (by rfl) ⟨1519802, by rfl⟩ : syracuseStep 2026403 = 3039605) B3039605
theorem B7798997 : Blo 2025435 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B5199331 : Blo 2025435 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B6932441 : Blo 2025435 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B4621627 : Blo 2025435 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B6162169 : Blo 2025435 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B8216225 : Blo 2025435 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B5477483 : Blo 2025435 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B3651655 : Blo 2025435 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B4868873 : Blo 2025435 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B3245915 : Blo 2025435 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B2163943 : Blo 2025435 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B2885257 : Blo 2025435 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B3847009 : Blo 2025435 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B5129345 : Blo 2025435 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B3419563 : Blo 2025435 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B4559417 : Blo 2025435 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B3039611 : Blo 2025435 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B2026407 : Blo 2025435 2026407 := bstep (se 1 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 2026407 = 3039611) B3039611
theorem B2279713 : Blo 2025435 2279713 := bbase (se 2 (by rfl) ⟨854892, by rfl⟩ : syracuseStep 2279713 = 1709785) (by norm_num)
theorem B3039617 : Blo 2025435 3039617 := bstep (se 2 (by rfl) ⟨1139856, by rfl⟩ : syracuseStep 3039617 = 2279713) B2279713
theorem B2026411 : Blo 2025435 2026411 := bstep (se 1 (by rfl) ⟨1519808, by rfl⟩ : syracuseStep 2026411 = 3039617) B3039617
theorem B5129365 : Blo 2025435 5129365 := bbase (se 6 (by rfl) ⟨120219, by rfl⟩ : syracuseStep 5129365 = 240439) (by norm_num)
theorem B6839153 : Blo 2025435 6839153 := bstep (se 2 (by rfl) ⟨2564682, by rfl⟩ : syracuseStep 6839153 = 5129365) B5129365
theorem B4559435 : Blo 2025435 4559435 := bstep (se 1 (by rfl) ⟨3419576, by rfl⟩ : syracuseStep 4559435 = 6839153) B6839153
theorem B3039623 : Blo 2025435 3039623 := bstep (se 1 (by rfl) ⟨2279717, by rfl⟩ : syracuseStep 3039623 = 4559435) B4559435
theorem B2026415 : Blo 2025435 2026415 := bstep (se 1 (by rfl) ⟨1519811, by rfl⟩ : syracuseStep 2026415 = 3039623) B3039623
theorem B3039629 : Blo 2025435 3039629 := bbase (se 3 (by rfl) ⟨569930, by rfl⟩ : syracuseStep 3039629 = 1139861) (by norm_num)
theorem B2026419 : Blo 2025435 2026419 := bstep (se 1 (by rfl) ⟨1519814, by rfl⟩ : syracuseStep 2026419 = 3039629) B3039629
theorem B4559453 : Blo 2025435 4559453 := bbase (se 3 (by rfl) ⟨854897, by rfl⟩ : syracuseStep 4559453 = 1709795) (by norm_num)
theorem B3039635 : Blo 2025435 3039635 := bstep (se 1 (by rfl) ⟨2279726, by rfl⟩ : syracuseStep 3039635 = 4559453) B4559453
theorem B2026423 : Blo 2025435 2026423 := bstep (se 1 (by rfl) ⟨1519817, by rfl⟩ : syracuseStep 2026423 = 3039635) B3039635
theorem B3419597 : Blo 2025435 3419597 := bbase (se 3 (by rfl) ⟨641174, by rfl⟩ : syracuseStep 3419597 = 1282349) (by norm_num)
theorem B2279731 : Blo 2025435 2279731 := bstep (se 1 (by rfl) ⟨1709798, by rfl⟩ : syracuseStep 2279731 = 3419597) B3419597
theorem B3039641 : Blo 2025435 3039641 := bstep (se 2 (by rfl) ⟨1139865, by rfl⟩ : syracuseStep 3039641 = 2279731) B2279731
theorem B2026427 : Blo 2025435 2026427 := bstep (se 1 (by rfl) ⟨1519820, by rfl⟩ : syracuseStep 2026427 = 3039641) B3039641
theorem B3473509 : Blo 2025435 3473509 := bbase (se 4 (by rfl) ⟨325641, by rfl⟩ : syracuseStep 3473509 = 651283) (by norm_num)
theorem B4631345 : Blo 2025435 4631345 := bstep (se 2 (by rfl) ⟨1736754, by rfl⟩ : syracuseStep 4631345 = 3473509) B3473509
theorem B3087563 : Blo 2025435 3087563 := bstep (se 1 (by rfl) ⟨2315672, by rfl⟩ : syracuseStep 3087563 = 4631345) B4631345
theorem B8233501 : Blo 2025435 8233501 := bstep (se 3 (by rfl) ⟨1543781, by rfl⟩ : syracuseStep 8233501 = 3087563) B3087563
theorem B10978001 : Blo 2025435 10978001 := bstep (se 2 (by rfl) ⟨4116750, by rfl⟩ : syracuseStep 10978001 = 8233501) B8233501
theorem B7318667 : Blo 2025435 7318667 := bstep (se 1 (by rfl) ⟨5489000, by rfl⟩ : syracuseStep 7318667 = 10978001) B10978001
theorem B19516445 : Blo 2025435 19516445 := bstep (se 3 (by rfl) ⟨3659333, by rfl⟩ : syracuseStep 19516445 = 7318667) B7318667
theorem B13010963 : Blo 2025435 13010963 := bstep (se 1 (by rfl) ⟨9758222, by rfl⟩ : syracuseStep 13010963 = 19516445) B19516445
theorem B34695901 : Blo 2025435 34695901 := bstep (se 3 (by rfl) ⟨6505481, by rfl⟩ : syracuseStep 34695901 = 13010963) B13010963
theorem B46261201 : Blo 2025435 46261201 := bstep (se 2 (by rfl) ⟨17347950, by rfl⟩ : syracuseStep 46261201 = 34695901) B34695901
theorem B61681601 : Blo 2025435 61681601 := bstep (se 2 (by rfl) ⟨23130600, by rfl⟩ : syracuseStep 61681601 = 46261201) B46261201
theorem B164484269 : Blo 2025435 164484269 := bstep (se 3 (by rfl) ⟨30840800, by rfl⟩ : syracuseStep 164484269 = 61681601) B61681601
theorem B109656179 : Blo 2025435 109656179 := bstep (se 1 (by rfl) ⟨82242134, by rfl⟩ : syracuseStep 109656179 = 164484269) B164484269
theorem B73104119 : Blo 2025435 73104119 := bstep (se 1 (by rfl) ⟨54828089, by rfl⟩ : syracuseStep 73104119 = 109656179) B109656179
theorem B48736079 : Blo 2025435 48736079 := bstep (se 1 (by rfl) ⟨36552059, by rfl⟩ : syracuseStep 48736079 = 73104119) B73104119
theorem B32490719 : Blo 2025435 32490719 := bstep (se 1 (by rfl) ⟨24368039, by rfl⟩ : syracuseStep 32490719 = 48736079) B48736079
theorem B21660479 : Blo 2025435 21660479 := bstep (se 1 (by rfl) ⟨16245359, by rfl⟩ : syracuseStep 21660479 = 32490719) B32490719
theorem B14440319 : Blo 2025435 14440319 := bstep (se 1 (by rfl) ⟨10830239, by rfl⟩ : syracuseStep 14440319 = 21660479) B21660479
theorem B9626879 : Blo 2025435 9626879 := bstep (se 1 (by rfl) ⟨7220159, by rfl⟩ : syracuseStep 9626879 = 14440319) B14440319
theorem B6417919 : Blo 2025435 6417919 := bstep (se 1 (by rfl) ⟨4813439, by rfl⟩ : syracuseStep 6417919 = 9626879) B9626879
theorem B34228901 : Blo 2025435 34228901 := bstep (se 4 (by rfl) ⟨3208959, by rfl⟩ : syracuseStep 34228901 = 6417919) B6417919
theorem B22819267 : Blo 2025435 22819267 := bstep (se 1 (by rfl) ⟨17114450, by rfl⟩ : syracuseStep 22819267 = 34228901) B34228901
theorem B121702757 : Blo 2025435 121702757 := bstep (se 4 (by rfl) ⟨11409633, by rfl⟩ : syracuseStep 121702757 = 22819267) B22819267
theorem B324540685 : Blo 2025435 324540685 := bstep (se 3 (by rfl) ⟨60851378, by rfl⟩ : syracuseStep 324540685 = 121702757) B121702757
theorem B432720913 : Blo 2025435 432720913 := bstep (se 2 (by rfl) ⟨162270342, by rfl⟩ : syracuseStep 432720913 = 324540685) B324540685
theorem B576961217 : Blo 2025435 576961217 := bstep (se 2 (by rfl) ⟨216360456, by rfl⟩ : syracuseStep 576961217 = 432720913) B432720913
theorem B384640811 : Blo 2025435 384640811 := bstep (se 1 (by rfl) ⟨288480608, by rfl⟩ : syracuseStep 384640811 = 576961217) B576961217
theorem B256427207 : Blo 2025435 256427207 := bstep (se 1 (by rfl) ⟨192320405, by rfl⟩ : syracuseStep 256427207 = 384640811) B384640811
theorem B170951471 : Blo 2025435 170951471 := bstep (se 1 (by rfl) ⟨128213603, by rfl⟩ : syracuseStep 170951471 = 256427207) B256427207
theorem B113967647 : Blo 2025435 113967647 := bstep (se 1 (by rfl) ⟨85475735, by rfl⟩ : syracuseStep 113967647 = 170951471) B170951471
theorem B75978431 : Blo 2025435 75978431 := bstep (se 1 (by rfl) ⟨56983823, by rfl⟩ : syracuseStep 75978431 = 113967647) B113967647
theorem B50652287 : Blo 2025435 50652287 := bstep (se 1 (by rfl) ⟨37989215, by rfl⟩ : syracuseStep 50652287 = 75978431) B75978431
theorem B33768191 : Blo 2025435 33768191 := bstep (se 1 (by rfl) ⟨25326143, by rfl⟩ : syracuseStep 33768191 = 50652287) B50652287
theorem B90048509 : Blo 2025435 90048509 := bstep (se 3 (by rfl) ⟨16884095, by rfl⟩ : syracuseStep 90048509 = 33768191) B33768191
theorem B60032339 : Blo 2025435 60032339 := bstep (se 1 (by rfl) ⟨45024254, by rfl⟩ : syracuseStep 60032339 = 90048509) B90048509
theorem B40021559 : Blo 2025435 40021559 := bstep (se 1 (by rfl) ⟨30016169, by rfl⟩ : syracuseStep 40021559 = 60032339) B60032339
theorem B26681039 : Blo 2025435 26681039 := bstep (se 1 (by rfl) ⟨20010779, by rfl⟩ : syracuseStep 26681039 = 40021559) B40021559
theorem B17787359 : Blo 2025435 17787359 := bstep (se 1 (by rfl) ⟨13340519, by rfl⟩ : syracuseStep 17787359 = 26681039) B26681039
theorem B11858239 : Blo 2025435 11858239 := bstep (se 1 (by rfl) ⟨8893679, by rfl⟩ : syracuseStep 11858239 = 17787359) B17787359
theorem B15810985 : Blo 2025435 15810985 := bstep (se 2 (by rfl) ⟨5929119, by rfl⟩ : syracuseStep 15810985 = 11858239) B11858239
theorem B21081313 : Blo 2025435 21081313 := bstep (se 2 (by rfl) ⟨7905492, by rfl⟩ : syracuseStep 21081313 = 15810985) B15810985
theorem B28108417 : Blo 2025435 28108417 := bstep (se 2 (by rfl) ⟨10540656, by rfl⟩ : syracuseStep 28108417 = 21081313) B21081313
theorem B37477889 : Blo 2025435 37477889 := bstep (se 2 (by rfl) ⟨14054208, by rfl⟩ : syracuseStep 37477889 = 28108417) B28108417
theorem B24985259 : Blo 2025435 24985259 := bstep (se 1 (by rfl) ⟨18738944, by rfl⟩ : syracuseStep 24985259 = 37477889) B37477889
theorem B16656839 : Blo 2025435 16656839 := bstep (se 1 (by rfl) ⟨12492629, by rfl⟩ : syracuseStep 16656839 = 24985259) B24985259
theorem B11104559 : Blo 2025435 11104559 := bstep (se 1 (by rfl) ⟨8328419, by rfl⟩ : syracuseStep 11104559 = 16656839) B16656839
theorem B7403039 : Blo 2025435 7403039 := bstep (se 1 (by rfl) ⟨5552279, by rfl⟩ : syracuseStep 7403039 = 11104559) B11104559
theorem B4935359 : Blo 2025435 4935359 := bstep (se 1 (by rfl) ⟨3701519, by rfl⟩ : syracuseStep 4935359 = 7403039) B7403039
theorem B3290239 : Blo 2025435 3290239 := bstep (se 1 (by rfl) ⟨2467679, by rfl⟩ : syracuseStep 3290239 = 4935359) B4935359
theorem B17547941 : Blo 2025435 17547941 := bstep (se 4 (by rfl) ⟨1645119, by rfl⟩ : syracuseStep 17547941 = 3290239) B3290239
theorem B46794509 : Blo 2025435 46794509 := bstep (se 3 (by rfl) ⟨8773970, by rfl⟩ : syracuseStep 46794509 = 17547941) B17547941
theorem B31196339 : Blo 2025435 31196339 := bstep (se 1 (by rfl) ⟨23397254, by rfl⟩ : syracuseStep 31196339 = 46794509) B46794509
theorem B20797559 : Blo 2025435 20797559 := bstep (se 1 (by rfl) ⟨15598169, by rfl⟩ : syracuseStep 20797559 = 31196339) B31196339
theorem B13865039 : Blo 2025435 13865039 := bstep (se 1 (by rfl) ⟨10398779, by rfl⟩ : syracuseStep 13865039 = 20797559) B20797559
theorem B9243359 : Blo 2025435 9243359 := bstep (se 1 (by rfl) ⟨6932519, by rfl⟩ : syracuseStep 9243359 = 13865039) B13865039
theorem B6162239 : Blo 2025435 6162239 := bstep (se 1 (by rfl) ⟨4621679, by rfl⟩ : syracuseStep 6162239 = 9243359) B9243359
theorem B4108159 : Blo 2025435 4108159 := bstep (se 1 (by rfl) ⟨3081119, by rfl⟩ : syracuseStep 4108159 = 6162239) B6162239
theorem B5477545 : Blo 2025435 5477545 := bstep (se 2 (by rfl) ⟨2054079, by rfl⟩ : syracuseStep 5477545 = 4108159) B4108159
theorem B7303393 : Blo 2025435 7303393 := bstep (se 2 (by rfl) ⟨2738772, by rfl⟩ : syracuseStep 7303393 = 5477545) B5477545
theorem B9737857 : Blo 2025435 9737857 := bstep (se 2 (by rfl) ⟨3651696, by rfl⟩ : syracuseStep 9737857 = 7303393) B7303393
theorem B12983809 : Blo 2025435 12983809 := bstep (se 2 (by rfl) ⟨4868928, by rfl⟩ : syracuseStep 12983809 = 9737857) B9737857
theorem B17311745 : Blo 2025435 17311745 := bstep (se 2 (by rfl) ⟨6491904, by rfl⟩ : syracuseStep 17311745 = 12983809) B12983809
theorem B11541163 : Blo 2025435 11541163 := bstep (se 1 (by rfl) ⟨8655872, by rfl⟩ : syracuseStep 11541163 = 17311745) B17311745
theorem B15388217 : Blo 2025435 15388217 := bstep (se 2 (by rfl) ⟨5770581, by rfl⟩ : syracuseStep 15388217 = 11541163) B11541163
theorem B10258811 : Blo 2025435 10258811 := bstep (se 1 (by rfl) ⟨7694108, by rfl⟩ : syracuseStep 10258811 = 15388217) B15388217
theorem B6839207 : Blo 2025435 6839207 := bstep (se 1 (by rfl) ⟨5129405, by rfl⟩ : syracuseStep 6839207 = 10258811) B10258811
theorem B4559471 : Blo 2025435 4559471 := bstep (se 1 (by rfl) ⟨3419603, by rfl⟩ : syracuseStep 4559471 = 6839207) B6839207
theorem B3039647 : Blo 2025435 3039647 := bstep (se 1 (by rfl) ⟨2279735, by rfl⟩ : syracuseStep 3039647 = 4559471) B4559471
theorem B2026431 : Blo 2025435 2026431 := bstep (se 1 (by rfl) ⟨1519823, by rfl⟩ : syracuseStep 2026431 = 3039647) B3039647
theorem B3039653 : Blo 2025435 3039653 := bbase (se 4 (by rfl) ⟨284967, by rfl⟩ : syracuseStep 3039653 = 569935) (by norm_num)
theorem B2026435 : Blo 2025435 2026435 := bstep (se 1 (by rfl) ⟨1519826, by rfl⟩ : syracuseStep 2026435 = 3039653) B3039653
theorem B2564713 : Blo 2025435 2564713 := bbase (se 2 (by rfl) ⟨961767, by rfl⟩ : syracuseStep 2564713 = 1923535) (by norm_num)
theorem B3419617 : Blo 2025435 3419617 := bstep (se 2 (by rfl) ⟨1282356, by rfl⟩ : syracuseStep 3419617 = 2564713) B2564713
theorem B4559489 : Blo 2025435 4559489 := bstep (se 2 (by rfl) ⟨1709808, by rfl⟩ : syracuseStep 4559489 = 3419617) B3419617
theorem B3039659 : Blo 2025435 3039659 := bstep (se 1 (by rfl) ⟨2279744, by rfl⟩ : syracuseStep 3039659 = 4559489) B4559489
theorem B2026439 : Blo 2025435 2026439 := bstep (se 1 (by rfl) ⟨1519829, by rfl⟩ : syracuseStep 2026439 = 3039659) B3039659
theorem B2279749 : Blo 2025435 2279749 := bbase (se 4 (by rfl) ⟨213726, by rfl⟩ : syracuseStep 2279749 = 427453) (by norm_num)
theorem B3039665 : Blo 2025435 3039665 := bstep (se 2 (by rfl) ⟨1139874, by rfl⟩ : syracuseStep 3039665 = 2279749) B2279749
theorem B2026443 : Blo 2025435 2026443 := bstep (se 1 (by rfl) ⟨1519832, by rfl⟩ : syracuseStep 2026443 = 3039665) B3039665
theorem B3847085 : Blo 2025435 3847085 := bbase (se 3 (by rfl) ⟨721328, by rfl⟩ : syracuseStep 3847085 = 1442657) (by norm_num)
theorem B2564723 : Blo 2025435 2564723 := bstep (se 1 (by rfl) ⟨1923542, by rfl⟩ : syracuseStep 2564723 = 3847085) B3847085
theorem B6839261 : Blo 2025435 6839261 := bstep (se 3 (by rfl) ⟨1282361, by rfl⟩ : syracuseStep 6839261 = 2564723) B2564723
theorem B4559507 : Blo 2025435 4559507 := bstep (se 1 (by rfl) ⟨3419630, by rfl⟩ : syracuseStep 4559507 = 6839261) B6839261
theorem B3039671 : Blo 2025435 3039671 := bstep (se 1 (by rfl) ⟨2279753, by rfl⟩ : syracuseStep 3039671 = 4559507) B4559507
theorem B2026447 : Blo 2025435 2026447 := bstep (se 1 (by rfl) ⟨1519835, by rfl⟩ : syracuseStep 2026447 = 3039671) B3039671
theorem B3039677 : Blo 2025435 3039677 := bbase (se 3 (by rfl) ⟨569939, by rfl⟩ : syracuseStep 3039677 = 1139879) (by norm_num)
theorem B2026451 : Blo 2025435 2026451 := bstep (se 1 (by rfl) ⟨1519838, by rfl⟩ : syracuseStep 2026451 = 3039677) B3039677
theorem B4559525 : Blo 2025435 4559525 := bbase (se 4 (by rfl) ⟨427455, by rfl⟩ : syracuseStep 4559525 = 854911) (by norm_num)
theorem B3039683 : Blo 2025435 3039683 := bstep (se 1 (by rfl) ⟨2279762, by rfl⟩ : syracuseStep 3039683 = 4559525) B4559525
theorem B2026455 : Blo 2025435 2026455 := bstep (se 1 (by rfl) ⟨1519841, by rfl⟩ : syracuseStep 2026455 = 3039683) B3039683
theorem B5129477 : Blo 2025435 5129477 := bbase (se 4 (by rfl) ⟨480888, by rfl⟩ : syracuseStep 5129477 = 961777) (by norm_num)
theorem B3419651 : Blo 2025435 3419651 := bstep (se 1 (by rfl) ⟨2564738, by rfl⟩ : syracuseStep 3419651 = 5129477) B5129477
theorem B2279767 : Blo 2025435 2279767 := bstep (se 1 (by rfl) ⟨1709825, by rfl⟩ : syracuseStep 2279767 = 3419651) B3419651
theorem B3039689 : Blo 2025435 3039689 := bstep (se 2 (by rfl) ⟨1139883, by rfl⟩ : syracuseStep 3039689 = 2279767) B2279767
theorem B2026459 : Blo 2025435 2026459 := bstep (se 1 (by rfl) ⟨1519844, by rfl⟩ : syracuseStep 2026459 = 3039689) B3039689
theorem B4328005 : Blo 2025435 4328005 := bbase (se 4 (by rfl) ⟨405750, by rfl⟩ : syracuseStep 4328005 = 811501) (by norm_num)
theorem B5770673 : Blo 2025435 5770673 := bstep (se 2 (by rfl) ⟨2164002, by rfl⟩ : syracuseStep 5770673 = 4328005) B4328005
theorem B3847115 : Blo 2025435 3847115 := bstep (se 1 (by rfl) ⟨2885336, by rfl⟩ : syracuseStep 3847115 = 5770673) B5770673
theorem B10258973 : Blo 2025435 10258973 := bstep (se 3 (by rfl) ⟨1923557, by rfl⟩ : syracuseStep 10258973 = 3847115) B3847115
theorem B6839315 : Blo 2025435 6839315 := bstep (se 1 (by rfl) ⟨5129486, by rfl⟩ : syracuseStep 6839315 = 10258973) B10258973
theorem B4559543 : Blo 2025435 4559543 := bstep (se 1 (by rfl) ⟨3419657, by rfl⟩ : syracuseStep 4559543 = 6839315) B6839315
theorem B3039695 : Blo 2025435 3039695 := bstep (se 1 (by rfl) ⟨2279771, by rfl⟩ : syracuseStep 3039695 = 4559543) B4559543
theorem B2026463 : Blo 2025435 2026463 := bstep (se 1 (by rfl) ⟨1519847, by rfl⟩ : syracuseStep 2026463 = 3039695) B3039695
theorem B3039701 : Blo 2025435 3039701 := bbase (se 7 (by rfl) ⟨35621, by rfl⟩ : syracuseStep 3039701 = 71243) (by norm_num)
theorem B2026467 : Blo 2025435 2026467 := bstep (se 1 (by rfl) ⟨1519850, by rfl⟩ : syracuseStep 2026467 = 3039701) B3039701
theorem B7694261 : Blo 2025435 7694261 := bbase (se 5 (by rfl) ⟨360668, by rfl⟩ : syracuseStep 7694261 = 721337) (by norm_num)
theorem B5129507 : Blo 2025435 5129507 := bstep (se 1 (by rfl) ⟨3847130, by rfl⟩ : syracuseStep 5129507 = 7694261) B7694261
theorem B3419671 : Blo 2025435 3419671 := bstep (se 1 (by rfl) ⟨2564753, by rfl⟩ : syracuseStep 3419671 = 5129507) B5129507
theorem B4559561 : Blo 2025435 4559561 := bstep (se 2 (by rfl) ⟨1709835, by rfl⟩ : syracuseStep 4559561 = 3419671) B3419671
theorem B3039707 : Blo 2025435 3039707 := bstep (se 1 (by rfl) ⟨2279780, by rfl⟩ : syracuseStep 3039707 = 4559561) B4559561
theorem B2026471 : Blo 2025435 2026471 := bstep (se 1 (by rfl) ⟨1519853, by rfl⟩ : syracuseStep 2026471 = 3039707) B3039707
theorem B2279785 : Blo 2025435 2279785 := bbase (se 2 (by rfl) ⟨854919, by rfl⟩ : syracuseStep 2279785 = 1709839) (by norm_num)
theorem B3039713 : Blo 2025435 3039713 := bstep (se 2 (by rfl) ⟨1139892, by rfl⟩ : syracuseStep 3039713 = 2279785) B2279785
theorem B2026475 : Blo 2025435 2026475 := bstep (se 1 (by rfl) ⟨1519856, by rfl⟩ : syracuseStep 2026475 = 3039713) B3039713
theorem B4621789 : Blo 2025435 4621789 := bbase (se 3 (by rfl) ⟨866585, by rfl⟩ : syracuseStep 4621789 = 1733171) (by norm_num)
theorem B24649541 : Blo 2025435 24649541 := bstep (se 4 (by rfl) ⟨2310894, by rfl⟩ : syracuseStep 24649541 = 4621789) B4621789
theorem B16433027 : Blo 2025435 16433027 := bstep (se 1 (by rfl) ⟨12324770, by rfl⟩ : syracuseStep 16433027 = 24649541) B24649541
theorem B10955351 : Blo 2025435 10955351 := bstep (se 1 (by rfl) ⟨8216513, by rfl⟩ : syracuseStep 10955351 = 16433027) B16433027
theorem B7303567 : Blo 2025435 7303567 := bstep (se 1 (by rfl) ⟨5477675, by rfl⟩ : syracuseStep 7303567 = 10955351) B10955351
theorem B9738089 : Blo 2025435 9738089 := bstep (se 2 (by rfl) ⟨3651783, by rfl⟩ : syracuseStep 9738089 = 7303567) B7303567
theorem B6492059 : Blo 2025435 6492059 := bstep (se 1 (by rfl) ⟨4869044, by rfl⟩ : syracuseStep 6492059 = 9738089) B9738089
theorem B4328039 : Blo 2025435 4328039 := bstep (se 1 (by rfl) ⟨3246029, by rfl⟩ : syracuseStep 4328039 = 6492059) B6492059
theorem B11541437 : Blo 2025435 11541437 := bstep (se 3 (by rfl) ⟨2164019, by rfl⟩ : syracuseStep 11541437 = 4328039) B4328039
theorem B7694291 : Blo 2025435 7694291 := bstep (se 1 (by rfl) ⟨5770718, by rfl⟩ : syracuseStep 7694291 = 11541437) B11541437
theorem B5129527 : Blo 2025435 5129527 := bstep (se 1 (by rfl) ⟨3847145, by rfl⟩ : syracuseStep 5129527 = 7694291) B7694291
theorem B6839369 : Blo 2025435 6839369 := bstep (se 2 (by rfl) ⟨2564763, by rfl⟩ : syracuseStep 6839369 = 5129527) B5129527
theorem B4559579 : Blo 2025435 4559579 := bstep (se 1 (by rfl) ⟨3419684, by rfl⟩ : syracuseStep 4559579 = 6839369) B6839369
theorem B3039719 : Blo 2025435 3039719 := bstep (se 1 (by rfl) ⟨2279789, by rfl⟩ : syracuseStep 3039719 = 4559579) B4559579
theorem B2026479 : Blo 2025435 2026479 := bstep (se 1 (by rfl) ⟨1519859, by rfl⟩ : syracuseStep 2026479 = 3039719) B3039719
theorem B3039725 : Blo 2025435 3039725 := bbase (se 3 (by rfl) ⟨569948, by rfl⟩ : syracuseStep 3039725 = 1139897) (by norm_num)
theorem B2026483 : Blo 2025435 2026483 := bstep (se 1 (by rfl) ⟨1519862, by rfl⟩ : syracuseStep 2026483 = 3039725) B3039725
theorem B4559597 : Blo 2025435 4559597 := bbase (se 3 (by rfl) ⟨854924, by rfl⟩ : syracuseStep 4559597 = 1709849) (by norm_num)
theorem B3039731 : Blo 2025435 3039731 := bstep (se 1 (by rfl) ⟨2279798, by rfl⟩ : syracuseStep 3039731 = 4559597) B4559597
theorem B2026487 : Blo 2025435 2026487 := bstep (se 1 (by rfl) ⟨1519865, by rfl⟩ : syracuseStep 2026487 = 3039731) B3039731
theorem B2164033 : Blo 2025435 2164033 := bbase (se 2 (by rfl) ⟨811512, by rfl⟩ : syracuseStep 2164033 = 1623025) (by norm_num)
theorem B2885377 : Blo 2025435 2885377 := bstep (se 2 (by rfl) ⟨1082016, by rfl⟩ : syracuseStep 2885377 = 2164033) B2164033
theorem B3847169 : Blo 2025435 3847169 := bstep (se 2 (by rfl) ⟨1442688, by rfl⟩ : syracuseStep 3847169 = 2885377) B2885377
theorem B2564779 : Blo 2025435 2564779 := bstep (se 1 (by rfl) ⟨1923584, by rfl⟩ : syracuseStep 2564779 = 3847169) B3847169
theorem B3419705 : Blo 2025435 3419705 := bstep (se 2 (by rfl) ⟨1282389, by rfl⟩ : syracuseStep 3419705 = 2564779) B2564779
theorem B2279803 : Blo 2025435 2279803 := bstep (se 1 (by rfl) ⟨1709852, by rfl⟩ : syracuseStep 2279803 = 3419705) B3419705
theorem B3039737 : Blo 2025435 3039737 := bstep (se 2 (by rfl) ⟨1139901, by rfl⟩ : syracuseStep 3039737 = 2279803) B2279803
theorem B2026491 : Blo 2025435 2026491 := bstep (se 1 (by rfl) ⟨1519868, by rfl⟩ : syracuseStep 2026491 = 3039737) B3039737
theorem B8774245 : Blo 2025435 8774245 := bbase (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) (by norm_num)
theorem B11698993 : Blo 2025435 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B15598657 : Blo 2025435 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B20798209 : Blo 2025435 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B27730945 : Blo 2025435 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B36974593 : Blo 2025435 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B49299457 : Blo 2025435 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B65732609 : Blo 2025435 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B43821739 : Blo 2025435 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B58428985 : Blo 2025435 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B77905313 : Blo 2025435 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B51936875 : Blo 2025435 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B34624583 : Blo 2025435 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B23083055 : Blo 2025435 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B15388703 : Blo 2025435 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B10259135 : Blo 2025435 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B6839423 : Blo 2025435 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B4559615 : Blo 2025435 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B3039743 : Blo 2025435 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B2026495 : Blo 2025435 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B3039749 : Blo 2025435 3039749 := bbase (se 4 (by rfl) ⟨284976, by rfl⟩ : syracuseStep 3039749 = 569953) (by norm_num)
theorem B2026499 : Blo 2025435 2026499 := bstep (se 1 (by rfl) ⟨1519874, by rfl⟩ : syracuseStep 2026499 = 3039749) B3039749
theorem B3419725 : Blo 2025435 3419725 := bbase (se 3 (by rfl) ⟨641198, by rfl⟩ : syracuseStep 3419725 = 1282397) (by norm_num)
theorem B4559633 : Blo 2025435 4559633 := bstep (se 2 (by rfl) ⟨1709862, by rfl⟩ : syracuseStep 4559633 = 3419725) B3419725
theorem B3039755 : Blo 2025435 3039755 := bstep (se 1 (by rfl) ⟨2279816, by rfl⟩ : syracuseStep 3039755 = 4559633) B4559633
theorem B2026503 : Blo 2025435 2026503 := bstep (se 1 (by rfl) ⟨1519877, by rfl⟩ : syracuseStep 2026503 = 3039755) B3039755
theorem B2279821 : Blo 2025435 2279821 := bbase (se 3 (by rfl) ⟨427466, by rfl⟩ : syracuseStep 2279821 = 854933) (by norm_num)
theorem B3039761 : Blo 2025435 3039761 := bstep (se 2 (by rfl) ⟨1139910, by rfl⟩ : syracuseStep 3039761 = 2279821) B2279821
theorem B2026507 : Blo 2025435 2026507 := bstep (se 1 (by rfl) ⟨1519880, by rfl⟩ : syracuseStep 2026507 = 3039761) B3039761
theorem B6839477 : Blo 2025435 6839477 := bbase (se 5 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 6839477 = 641201) (by norm_num)
theorem B4559651 : Blo 2025435 4559651 := bstep (se 1 (by rfl) ⟨3419738, by rfl⟩ : syracuseStep 4559651 = 6839477) B6839477
theorem B3039767 : Blo 2025435 3039767 := bstep (se 1 (by rfl) ⟨2279825, by rfl⟩ : syracuseStep 3039767 = 4559651) B4559651
theorem B2026511 : Blo 2025435 2026511 := bstep (se 1 (by rfl) ⟨1519883, by rfl⟩ : syracuseStep 2026511 = 3039767) B3039767
theorem B3039773 : Blo 2025435 3039773 := bbase (se 3 (by rfl) ⟨569957, by rfl⟩ : syracuseStep 3039773 = 1139915) (by norm_num)
theorem B2026515 : Blo 2025435 2026515 := bstep (se 1 (by rfl) ⟨1519886, by rfl⟩ : syracuseStep 2026515 = 3039773) B3039773
theorem B4559669 : Blo 2025435 4559669 := bbase (se 5 (by rfl) ⟨213734, by rfl⟩ : syracuseStep 4559669 = 427469) (by norm_num)
theorem B3039779 : Blo 2025435 3039779 := bstep (se 1 (by rfl) ⟨2279834, by rfl⟩ : syracuseStep 3039779 = 4559669) B4559669
theorem B2026519 : Blo 2025435 2026519 := bstep (se 1 (by rfl) ⟨1519889, by rfl⟩ : syracuseStep 2026519 = 3039779) B3039779
theorem B8216693 : Blo 2025435 8216693 := bbase (se 5 (by rfl) ⟨385157, by rfl⟩ : syracuseStep 8216693 = 770315) (by norm_num)
theorem B5477795 : Blo 2025435 5477795 := bstep (se 1 (by rfl) ⟨4108346, by rfl⟩ : syracuseStep 5477795 = 8216693) B8216693
theorem B3651863 : Blo 2025435 3651863 := bstep (se 1 (by rfl) ⟨2738897, by rfl⟩ : syracuseStep 3651863 = 5477795) B5477795
theorem B9738301 : Blo 2025435 9738301 := bstep (se 3 (by rfl) ⟨1825931, by rfl⟩ : syracuseStep 9738301 = 3651863) B3651863
theorem B12984401 : Blo 2025435 12984401 := bstep (se 2 (by rfl) ⟨4869150, by rfl⟩ : syracuseStep 12984401 = 9738301) B9738301
theorem B8656267 : Blo 2025435 8656267 := bstep (se 1 (by rfl) ⟨6492200, by rfl⟩ : syracuseStep 8656267 = 12984401) B12984401
theorem B11541689 : Blo 2025435 11541689 := bstep (se 2 (by rfl) ⟨4328133, by rfl⟩ : syracuseStep 11541689 = 8656267) B8656267
theorem B7694459 : Blo 2025435 7694459 := bstep (se 1 (by rfl) ⟨5770844, by rfl⟩ : syracuseStep 7694459 = 11541689) B11541689
theorem B5129639 : Blo 2025435 5129639 := bstep (se 1 (by rfl) ⟨3847229, by rfl⟩ : syracuseStep 5129639 = 7694459) B7694459
theorem B3419759 : Blo 2025435 3419759 := bstep (se 1 (by rfl) ⟨2564819, by rfl⟩ : syracuseStep 3419759 = 5129639) B5129639
theorem B2279839 : Blo 2025435 2279839 := bstep (se 1 (by rfl) ⟨1709879, by rfl⟩ : syracuseStep 2279839 = 3419759) B3419759
theorem B3039785 : Blo 2025435 3039785 := bstep (se 2 (by rfl) ⟨1139919, by rfl⟩ : syracuseStep 3039785 = 2279839) B2279839
theorem B2026523 : Blo 2025435 2026523 := bstep (se 1 (by rfl) ⟨1519892, by rfl⟩ : syracuseStep 2026523 = 3039785) B3039785
theorem B2310949 : Blo 2025435 2310949 := bbase (se 4 (by rfl) ⟨216651, by rfl⟩ : syracuseStep 2310949 = 433303) (by norm_num)
theorem B12325061 : Blo 2025435 12325061 := bstep (se 4 (by rfl) ⟨1155474, by rfl⟩ : syracuseStep 12325061 = 2310949) B2310949
theorem B32866829 : Blo 2025435 32866829 := bstep (se 3 (by rfl) ⟨6162530, by rfl⟩ : syracuseStep 32866829 = 12325061) B12325061
theorem B21911219 : Blo 2025435 21911219 := bstep (se 1 (by rfl) ⟨16433414, by rfl⟩ : syracuseStep 21911219 = 32866829) B32866829
theorem B14607479 : Blo 2025435 14607479 := bstep (se 1 (by rfl) ⟨10955609, by rfl⟩ : syracuseStep 14607479 = 21911219) B21911219
theorem B9738319 : Blo 2025435 9738319 := bstep (se 1 (by rfl) ⟨7303739, by rfl⟩ : syracuseStep 9738319 = 14607479) B14607479
theorem B12984425 : Blo 2025435 12984425 := bstep (se 2 (by rfl) ⟨4869159, by rfl⟩ : syracuseStep 12984425 = 9738319) B9738319
theorem B8656283 : Blo 2025435 8656283 := bstep (se 1 (by rfl) ⟨6492212, by rfl⟩ : syracuseStep 8656283 = 12984425) B12984425
theorem B5770855 : Blo 2025435 5770855 := bstep (se 1 (by rfl) ⟨4328141, by rfl⟩ : syracuseStep 5770855 = 8656283) B8656283
theorem B7694473 : Blo 2025435 7694473 := bstep (se 2 (by rfl) ⟨2885427, by rfl⟩ : syracuseStep 7694473 = 5770855) B5770855
theorem B10259297 : Blo 2025435 10259297 := bstep (se 2 (by rfl) ⟨3847236, by rfl⟩ : syracuseStep 10259297 = 7694473) B7694473
theorem B6839531 : Blo 2025435 6839531 := bstep (se 1 (by rfl) ⟨5129648, by rfl⟩ : syracuseStep 6839531 = 10259297) B10259297
theorem B4559687 : Blo 2025435 4559687 := bstep (se 1 (by rfl) ⟨3419765, by rfl⟩ : syracuseStep 4559687 = 6839531) B6839531
theorem B3039791 : Blo 2025435 3039791 := bstep (se 1 (by rfl) ⟨2279843, by rfl⟩ : syracuseStep 3039791 = 4559687) B4559687
theorem B2026527 : Blo 2025435 2026527 := bstep (se 1 (by rfl) ⟨1519895, by rfl⟩ : syracuseStep 2026527 = 3039791) B3039791
theorem B3039797 : Blo 2025435 3039797 := bbase (se 5 (by rfl) ⟨142490, by rfl⟩ : syracuseStep 3039797 = 284981) (by norm_num)
theorem B2026531 : Blo 2025435 2026531 := bstep (se 1 (by rfl) ⟨1519898, by rfl⟩ : syracuseStep 2026531 = 3039797) B3039797
theorem B5129669 : Blo 2025435 5129669 := bbase (se 4 (by rfl) ⟨480906, by rfl⟩ : syracuseStep 5129669 = 961813) (by norm_num)
theorem B3419779 : Blo 2025435 3419779 := bstep (se 1 (by rfl) ⟨2564834, by rfl⟩ : syracuseStep 3419779 = 5129669) B5129669
theorem B4559705 : Blo 2025435 4559705 := bstep (se 2 (by rfl) ⟨1709889, by rfl⟩ : syracuseStep 4559705 = 3419779) B3419779
theorem B3039803 : Blo 2025435 3039803 := bstep (se 1 (by rfl) ⟨2279852, by rfl⟩ : syracuseStep 3039803 = 4559705) B4559705
theorem B2026535 : Blo 2025435 2026535 := bstep (se 1 (by rfl) ⟨1519901, by rfl⟩ : syracuseStep 2026535 = 3039803) B3039803
theorem B2279857 : Blo 2025435 2279857 := bbase (se 2 (by rfl) ⟨854946, by rfl⟩ : syracuseStep 2279857 = 1709893) (by norm_num)
theorem B3039809 : Blo 2025435 3039809 := bstep (se 2 (by rfl) ⟨1139928, by rfl⟩ : syracuseStep 3039809 = 2279857) B2279857
theorem B2026539 : Blo 2025435 2026539 := bstep (se 1 (by rfl) ⟨1519904, by rfl⟩ : syracuseStep 2026539 = 3039809) B3039809
theorem B5770901 : Blo 2025435 5770901 := bbase (se 6 (by rfl) ⟨135255, by rfl⟩ : syracuseStep 5770901 = 270511) (by norm_num)
theorem B3847267 : Blo 2025435 3847267 := bstep (se 1 (by rfl) ⟨2885450, by rfl⟩ : syracuseStep 3847267 = 5770901) B5770901
theorem B5129689 : Blo 2025435 5129689 := bstep (se 2 (by rfl) ⟨1923633, by rfl⟩ : syracuseStep 5129689 = 3847267) B3847267
theorem B6839585 : Blo 2025435 6839585 := bstep (se 2 (by rfl) ⟨2564844, by rfl⟩ : syracuseStep 6839585 = 5129689) B5129689
theorem B4559723 : Blo 2025435 4559723 := bstep (se 1 (by rfl) ⟨3419792, by rfl⟩ : syracuseStep 4559723 = 6839585) B6839585
theorem B3039815 : Blo 2025435 3039815 := bstep (se 1 (by rfl) ⟨2279861, by rfl⟩ : syracuseStep 3039815 = 4559723) B4559723
theorem B2026543 : Blo 2025435 2026543 := bstep (se 1 (by rfl) ⟨1519907, by rfl⟩ : syracuseStep 2026543 = 3039815) B3039815
theorem B3039821 : Blo 2025435 3039821 := bbase (se 3 (by rfl) ⟨569966, by rfl⟩ : syracuseStep 3039821 = 1139933) (by norm_num)
theorem B2026547 : Blo 2025435 2026547 := bstep (se 1 (by rfl) ⟨1519910, by rfl⟩ : syracuseStep 2026547 = 3039821) B3039821
theorem B4559741 : Blo 2025435 4559741 := bbase (se 3 (by rfl) ⟨854951, by rfl⟩ : syracuseStep 4559741 = 1709903) (by norm_num)
theorem B3039827 : Blo 2025435 3039827 := bstep (se 1 (by rfl) ⟨2279870, by rfl⟩ : syracuseStep 3039827 = 4559741) B4559741
theorem B2026551 : Blo 2025435 2026551 := bstep (se 1 (by rfl) ⟨1519913, by rfl⟩ : syracuseStep 2026551 = 3039827) B3039827
theorem B3419813 : Blo 2025435 3419813 := bbase (se 4 (by rfl) ⟨320607, by rfl⟩ : syracuseStep 3419813 = 641215) (by norm_num)
theorem B2279875 : Blo 2025435 2279875 := bstep (se 1 (by rfl) ⟨1709906, by rfl⟩ : syracuseStep 2279875 = 3419813) B3419813
theorem B3039833 : Blo 2025435 3039833 := bstep (se 2 (by rfl) ⟨1139937, by rfl⟩ : syracuseStep 3039833 = 2279875) B2279875
theorem B2026555 : Blo 2025435 2026555 := bstep (se 1 (by rfl) ⟨1519916, by rfl⟩ : syracuseStep 2026555 = 3039833) B3039833
theorem B2164105 : Blo 2025435 2164105 := bbase (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) (by norm_num)
theorem B2885473 : Blo 2025435 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B15389189 : Blo 2025435 15389189 := bstep (se 4 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 15389189 = 2885473) B2885473
theorem B10259459 : Blo 2025435 10259459 := bstep (se 1 (by rfl) ⟨7694594, by rfl⟩ : syracuseStep 10259459 = 15389189) B15389189
theorem B6839639 : Blo 2025435 6839639 := bstep (se 1 (by rfl) ⟨5129729, by rfl⟩ : syracuseStep 6839639 = 10259459) B10259459
theorem B4559759 : Blo 2025435 4559759 := bstep (se 1 (by rfl) ⟨3419819, by rfl⟩ : syracuseStep 4559759 = 6839639) B6839639
theorem B3039839 : Blo 2025435 3039839 := bstep (se 1 (by rfl) ⟨2279879, by rfl⟩ : syracuseStep 3039839 = 4559759) B4559759
theorem B2026559 : Blo 2025435 2026559 := bstep (se 1 (by rfl) ⟨1519919, by rfl⟩ : syracuseStep 2026559 = 3039839) B3039839
theorem B3039845 : Blo 2025435 3039845 := bbase (se 4 (by rfl) ⟨284985, by rfl⟩ : syracuseStep 3039845 = 569971) (by norm_num)
theorem B2026563 : Blo 2025435 2026563 := bstep (se 1 (by rfl) ⟨1519922, by rfl⟩ : syracuseStep 2026563 = 3039845) B3039845
theorem B2885485 : Blo 2025435 2885485 := bbase (se 3 (by rfl) ⟨541028, by rfl⟩ : syracuseStep 2885485 = 1082057) (by norm_num)
theorem B3847313 : Blo 2025435 3847313 := bstep (se 2 (by rfl) ⟨1442742, by rfl⟩ : syracuseStep 3847313 = 2885485) B2885485
theorem B2564875 : Blo 2025435 2564875 := bstep (se 1 (by rfl) ⟨1923656, by rfl⟩ : syracuseStep 2564875 = 3847313) B3847313
theorem B3419833 : Blo 2025435 3419833 := bstep (se 2 (by rfl) ⟨1282437, by rfl⟩ : syracuseStep 3419833 = 2564875) B2564875
theorem B4559777 : Blo 2025435 4559777 := bstep (se 2 (by rfl) ⟨1709916, by rfl⟩ : syracuseStep 4559777 = 3419833) B3419833
theorem B3039851 : Blo 2025435 3039851 := bstep (se 1 (by rfl) ⟨2279888, by rfl⟩ : syracuseStep 3039851 = 4559777) B4559777
theorem B2026567 : Blo 2025435 2026567 := bstep (se 1 (by rfl) ⟨1519925, by rfl⟩ : syracuseStep 2026567 = 3039851) B3039851
theorem B2279893 : Blo 2025435 2279893 := bbase (se 7 (by rfl) ⟨26717, by rfl⟩ : syracuseStep 2279893 = 53435) (by norm_num)
theorem B3039857 : Blo 2025435 3039857 := bstep (se 2 (by rfl) ⟨1139946, by rfl⟩ : syracuseStep 3039857 = 2279893) B2279893
theorem B2026571 : Blo 2025435 2026571 := bstep (se 1 (by rfl) ⟨1519928, by rfl⟩ : syracuseStep 2026571 = 3039857) B3039857
theorem B2564885 : Blo 2025435 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B6839693 : Blo 2025435 6839693 := bstep (se 3 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 6839693 = 2564885) B2564885
theorem B4559795 : Blo 2025435 4559795 := bstep (se 1 (by rfl) ⟨3419846, by rfl⟩ : syracuseStep 4559795 = 6839693) B6839693
theorem B3039863 : Blo 2025435 3039863 := bstep (se 1 (by rfl) ⟨2279897, by rfl⟩ : syracuseStep 3039863 = 4559795) B4559795
theorem B2026575 : Blo 2025435 2026575 := bstep (se 1 (by rfl) ⟨1519931, by rfl⟩ : syracuseStep 2026575 = 3039863) B3039863
theorem B3039869 : Blo 2025435 3039869 := bbase (se 3 (by rfl) ⟨569975, by rfl⟩ : syracuseStep 3039869 = 1139951) (by norm_num)
theorem B2026579 : Blo 2025435 2026579 := bstep (se 1 (by rfl) ⟨1519934, by rfl⟩ : syracuseStep 2026579 = 3039869) B3039869
theorem B4559813 : Blo 2025435 4559813 := bbase (se 4 (by rfl) ⟨427482, by rfl⟩ : syracuseStep 4559813 = 854965) (by norm_num)
theorem B3039875 : Blo 2025435 3039875 := bstep (se 1 (by rfl) ⟨2279906, by rfl⟩ : syracuseStep 3039875 = 4559813) B4559813
theorem B2026583 : Blo 2025435 2026583 := bstep (se 1 (by rfl) ⟨1519937, by rfl⟩ : syracuseStep 2026583 = 3039875) B3039875
theorem B4108477 : Blo 2025435 4108477 := bbase (se 3 (by rfl) ⟨770339, by rfl⟩ : syracuseStep 4108477 = 1540679) (by norm_num)
theorem B5477969 : Blo 2025435 5477969 := bstep (se 2 (by rfl) ⟨2054238, by rfl⟩ : syracuseStep 5477969 = 4108477) B4108477
theorem B3651979 : Blo 2025435 3651979 := bstep (se 1 (by rfl) ⟨2738984, by rfl⟩ : syracuseStep 3651979 = 5477969) B5477969
theorem B4869305 : Blo 2025435 4869305 := bstep (se 2 (by rfl) ⟨1825989, by rfl⟩ : syracuseStep 4869305 = 3651979) B3651979
theorem B3246203 : Blo 2025435 3246203 := bstep (se 1 (by rfl) ⟨2434652, by rfl⟩ : syracuseStep 3246203 = 4869305) B4869305
theorem B8656541 : Blo 2025435 8656541 := bstep (se 3 (by rfl) ⟨1623101, by rfl⟩ : syracuseStep 8656541 = 3246203) B3246203
theorem B5771027 : Blo 2025435 5771027 := bstep (se 1 (by rfl) ⟨4328270, by rfl⟩ : syracuseStep 5771027 = 8656541) B8656541
theorem B3847351 : Blo 2025435 3847351 := bstep (se 1 (by rfl) ⟨2885513, by rfl⟩ : syracuseStep 3847351 = 5771027) B5771027
theorem B5129801 : Blo 2025435 5129801 := bstep (se 2 (by rfl) ⟨1923675, by rfl⟩ : syracuseStep 5129801 = 3847351) B3847351
theorem B3419867 : Blo 2025435 3419867 := bstep (se 1 (by rfl) ⟨2564900, by rfl⟩ : syracuseStep 3419867 = 5129801) B5129801
theorem B2279911 : Blo 2025435 2279911 := bstep (se 1 (by rfl) ⟨1709933, by rfl⟩ : syracuseStep 2279911 = 3419867) B3419867
theorem B3039881 : Blo 2025435 3039881 := bstep (se 2 (by rfl) ⟨1139955, by rfl⟩ : syracuseStep 3039881 = 2279911) B2279911
theorem B2026587 : Blo 2025435 2026587 := bstep (se 1 (by rfl) ⟨1519940, by rfl⟩ : syracuseStep 2026587 = 3039881) B3039881
theorem B10259621 : Blo 2025435 10259621 := bbase (se 4 (by rfl) ⟨961839, by rfl⟩ : syracuseStep 10259621 = 1923679) (by norm_num)
theorem B6839747 : Blo 2025435 6839747 := bstep (se 1 (by rfl) ⟨5129810, by rfl⟩ : syracuseStep 6839747 = 10259621) B10259621
theorem B4559831 : Blo 2025435 4559831 := bstep (se 1 (by rfl) ⟨3419873, by rfl⟩ : syracuseStep 4559831 = 6839747) B6839747
theorem B3039887 : Blo 2025435 3039887 := bstep (se 1 (by rfl) ⟨2279915, by rfl⟩ : syracuseStep 3039887 = 4559831) B4559831
theorem B2026591 : Blo 2025435 2026591 := bstep (se 1 (by rfl) ⟨1519943, by rfl⟩ : syracuseStep 2026591 = 3039887) B3039887
theorem B3039893 : Blo 2025435 3039893 := bbase (se 6 (by rfl) ⟨71247, by rfl⟩ : syracuseStep 3039893 = 142495) (by norm_num)
theorem B2026595 : Blo 2025435 2026595 := bstep (se 1 (by rfl) ⟨1519946, by rfl⟩ : syracuseStep 2026595 = 3039893) B3039893
theorem B4387349 : Blo 2025435 4387349 := bbase (se 6 (by rfl) ⟨102828, by rfl⟩ : syracuseStep 4387349 = 205657) (by norm_num)
theorem B2924899 : Blo 2025435 2924899 := bstep (se 1 (by rfl) ⟨2193674, by rfl⟩ : syracuseStep 2924899 = 4387349) B4387349
theorem B15599461 : Blo 2025435 15599461 := bstep (se 4 (by rfl) ⟨1462449, by rfl⟩ : syracuseStep 15599461 = 2924899) B2924899
theorem B20799281 : Blo 2025435 20799281 := bstep (se 2 (by rfl) ⟨7799730, by rfl⟩ : syracuseStep 20799281 = 15599461) B15599461
theorem B55464749 : Blo 2025435 55464749 := bstep (se 3 (by rfl) ⟨10399640, by rfl⟩ : syracuseStep 55464749 = 20799281) B20799281
theorem B36976499 : Blo 2025435 36976499 := bstep (se 1 (by rfl) ⟨27732374, by rfl⟩ : syracuseStep 36976499 = 55464749) B55464749
theorem B24650999 : Blo 2025435 24650999 := bstep (se 1 (by rfl) ⟨18488249, by rfl⟩ : syracuseStep 24650999 = 36976499) B36976499
theorem B16433999 : Blo 2025435 16433999 := bstep (se 1 (by rfl) ⟨12325499, by rfl⟩ : syracuseStep 16433999 = 24650999) B24650999
theorem B10955999 : Blo 2025435 10955999 := bstep (se 1 (by rfl) ⟨8216999, by rfl⟩ : syracuseStep 10955999 = 16433999) B16433999
theorem B29215997 : Blo 2025435 29215997 := bstep (se 3 (by rfl) ⟨5477999, by rfl⟩ : syracuseStep 29215997 = 10955999) B10955999
theorem B19477331 : Blo 2025435 19477331 := bstep (se 1 (by rfl) ⟨14607998, by rfl⟩ : syracuseStep 19477331 = 29215997) B29215997
theorem B12984887 : Blo 2025435 12984887 := bstep (se 1 (by rfl) ⟨9738665, by rfl⟩ : syracuseStep 12984887 = 19477331) B19477331
theorem B8656591 : Blo 2025435 8656591 := bstep (se 1 (by rfl) ⟨6492443, by rfl⟩ : syracuseStep 8656591 = 12984887) B12984887
theorem B11542121 : Blo 2025435 11542121 := bstep (se 2 (by rfl) ⟨4328295, by rfl⟩ : syracuseStep 11542121 = 8656591) B8656591
theorem B7694747 : Blo 2025435 7694747 := bstep (se 1 (by rfl) ⟨5771060, by rfl⟩ : syracuseStep 7694747 = 11542121) B11542121
theorem B5129831 : Blo 2025435 5129831 := bstep (se 1 (by rfl) ⟨3847373, by rfl⟩ : syracuseStep 5129831 = 7694747) B7694747
theorem B3419887 : Blo 2025435 3419887 := bstep (se 1 (by rfl) ⟨2564915, by rfl⟩ : syracuseStep 3419887 = 5129831) B5129831
theorem B4559849 : Blo 2025435 4559849 := bstep (se 2 (by rfl) ⟨1709943, by rfl⟩ : syracuseStep 4559849 = 3419887) B3419887
theorem B3039899 : Blo 2025435 3039899 := bstep (se 1 (by rfl) ⟨2279924, by rfl⟩ : syracuseStep 3039899 = 4559849) B4559849
theorem B2026599 : Blo 2025435 2026599 := bstep (se 1 (by rfl) ⟨1519949, by rfl⟩ : syracuseStep 2026599 = 3039899) B3039899
theorem B2279929 : Blo 2025435 2279929 := bbase (se 2 (by rfl) ⟨854973, by rfl⟩ : syracuseStep 2279929 = 1709947) (by norm_num)
theorem B3039905 : Blo 2025435 3039905 := bstep (se 2 (by rfl) ⟨1139964, by rfl⟩ : syracuseStep 3039905 = 2279929) B2279929
theorem B2026603 : Blo 2025435 2026603 := bstep (se 1 (by rfl) ⟨1519952, by rfl⟩ : syracuseStep 2026603 = 3039905) B3039905
theorem B6492469 : Blo 2025435 6492469 := bbase (se 5 (by rfl) ⟨304334, by rfl⟩ : syracuseStep 6492469 = 608669) (by norm_num)
theorem B8656625 : Blo 2025435 8656625 := bstep (se 2 (by rfl) ⟨3246234, by rfl⟩ : syracuseStep 8656625 = 6492469) B6492469
theorem B5771083 : Blo 2025435 5771083 := bstep (se 1 (by rfl) ⟨4328312, by rfl⟩ : syracuseStep 5771083 = 8656625) B8656625
theorem B7694777 : Blo 2025435 7694777 := bstep (se 2 (by rfl) ⟨2885541, by rfl⟩ : syracuseStep 7694777 = 5771083) B5771083
theorem B5129851 : Blo 2025435 5129851 := bstep (se 1 (by rfl) ⟨3847388, by rfl⟩ : syracuseStep 5129851 = 7694777) B7694777
theorem B6839801 : Blo 2025435 6839801 := bstep (se 2 (by rfl) ⟨2564925, by rfl⟩ : syracuseStep 6839801 = 5129851) B5129851
theorem B4559867 : Blo 2025435 4559867 := bstep (se 1 (by rfl) ⟨3419900, by rfl⟩ : syracuseStep 4559867 = 6839801) B6839801
theorem B3039911 : Blo 2025435 3039911 := bstep (se 1 (by rfl) ⟨2279933, by rfl⟩ : syracuseStep 3039911 = 4559867) B4559867
theorem B2026607 : Blo 2025435 2026607 := bstep (se 1 (by rfl) ⟨1519955, by rfl⟩ : syracuseStep 2026607 = 3039911) B3039911
theorem B3039917 : Blo 2025435 3039917 := bbase (se 3 (by rfl) ⟨569984, by rfl⟩ : syracuseStep 3039917 = 1139969) (by norm_num)
theorem B2026611 : Blo 2025435 2026611 := bstep (se 1 (by rfl) ⟨1519958, by rfl⟩ : syracuseStep 2026611 = 3039917) B3039917
theorem B4559885 : Blo 2025435 4559885 := bbase (se 3 (by rfl) ⟨854978, by rfl⟩ : syracuseStep 4559885 = 1709957) (by norm_num)
theorem B3039923 : Blo 2025435 3039923 := bstep (se 1 (by rfl) ⟨2279942, by rfl⟩ : syracuseStep 3039923 = 4559885) B4559885
theorem B2026615 : Blo 2025435 2026615 := bstep (se 1 (by rfl) ⟨1519961, by rfl⟩ : syracuseStep 2026615 = 3039923) B3039923
theorem B2564941 : Blo 2025435 2564941 := bbase (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) (by norm_num)
theorem B3419921 : Blo 2025435 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B2279947 : Blo 2025435 2279947 := bstep (se 1 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 2279947 = 3419921) B3419921
theorem B3039929 : Blo 2025435 3039929 := bstep (se 2 (by rfl) ⟨1139973, by rfl⟩ : syracuseStep 3039929 = 2279947) B2279947
theorem B2026619 : Blo 2025435 2026619 := bstep (se 1 (by rfl) ⟨1519964, by rfl⟩ : syracuseStep 2026619 = 3039929) B3039929
theorem B2467913 : Blo 2025435 2467913 := bbase (se 2 (by rfl) ⟨925467, by rfl⟩ : syracuseStep 2467913 = 1850935) (by norm_num)
theorem B6581101 : Blo 2025435 6581101 := bstep (se 3 (by rfl) ⟨1233956, by rfl⟩ : syracuseStep 6581101 = 2467913) B2467913
theorem B8774801 : Blo 2025435 8774801 := bstep (se 2 (by rfl) ⟨3290550, by rfl⟩ : syracuseStep 8774801 = 6581101) B6581101
theorem B5849867 : Blo 2025435 5849867 := bstep (se 1 (by rfl) ⟨4387400, by rfl⟩ : syracuseStep 5849867 = 8774801) B8774801
theorem B3899911 : Blo 2025435 3899911 := bstep (se 1 (by rfl) ⟨2924933, by rfl⟩ : syracuseStep 3899911 = 5849867) B5849867
theorem B5199881 : Blo 2025435 5199881 := bstep (se 2 (by rfl) ⟨1949955, by rfl⟩ : syracuseStep 5199881 = 3899911) B3899911
theorem B55465397 : Blo 2025435 55465397 := bstep (se 5 (by rfl) ⟨2599940, by rfl⟩ : syracuseStep 55465397 = 5199881) B5199881
theorem B36976931 : Blo 2025435 36976931 := bstep (se 1 (by rfl) ⟨27732698, by rfl⟩ : syracuseStep 36976931 = 55465397) B55465397
theorem B24651287 : Blo 2025435 24651287 := bstep (se 1 (by rfl) ⟨18488465, by rfl⟩ : syracuseStep 24651287 = 36976931) B36976931
theorem B16434191 : Blo 2025435 16434191 := bstep (se 1 (by rfl) ⟨12325643, by rfl⟩ : syracuseStep 16434191 = 24651287) B24651287
theorem B43824509 : Blo 2025435 43824509 := bstep (se 3 (by rfl) ⟨8217095, by rfl⟩ : syracuseStep 43824509 = 16434191) B16434191
theorem B29216339 : Blo 2025435 29216339 := bstep (se 1 (by rfl) ⟨21912254, by rfl⟩ : syracuseStep 29216339 = 43824509) B43824509
theorem B19477559 : Blo 2025435 19477559 := bstep (se 1 (by rfl) ⟨14608169, by rfl⟩ : syracuseStep 19477559 = 29216339) B29216339
theorem B12985039 : Blo 2025435 12985039 := bstep (se 1 (by rfl) ⟨9738779, by rfl⟩ : syracuseStep 12985039 = 19477559) B19477559
theorem B17313385 : Blo 2025435 17313385 := bstep (se 2 (by rfl) ⟨6492519, by rfl⟩ : syracuseStep 17313385 = 12985039) B12985039
theorem B23084513 : Blo 2025435 23084513 := bstep (se 2 (by rfl) ⟨8656692, by rfl⟩ : syracuseStep 23084513 = 17313385) B17313385
theorem B15389675 : Blo 2025435 15389675 := bstep (se 1 (by rfl) ⟨11542256, by rfl⟩ : syracuseStep 15389675 = 23084513) B23084513
theorem B10259783 : Blo 2025435 10259783 := bstep (se 1 (by rfl) ⟨7694837, by rfl⟩ : syracuseStep 10259783 = 15389675) B15389675
theorem B6839855 : Blo 2025435 6839855 := bstep (se 1 (by rfl) ⟨5129891, by rfl⟩ : syracuseStep 6839855 = 10259783) B10259783
theorem B4559903 : Blo 2025435 4559903 := bstep (se 1 (by rfl) ⟨3419927, by rfl⟩ : syracuseStep 4559903 = 6839855) B6839855
theorem B3039935 : Blo 2025435 3039935 := bstep (se 1 (by rfl) ⟨2279951, by rfl⟩ : syracuseStep 3039935 = 4559903) B4559903
theorem B2026623 : Blo 2025435 2026623 := bstep (se 1 (by rfl) ⟨1519967, by rfl⟩ : syracuseStep 2026623 = 3039935) B3039935
theorem B3039941 : Blo 2025435 3039941 := bbase (se 4 (by rfl) ⟨284994, by rfl⟩ : syracuseStep 3039941 = 569989) (by norm_num)
theorem B2026627 : Blo 2025435 2026627 := bstep (se 1 (by rfl) ⟨1519970, by rfl⟩ : syracuseStep 2026627 = 3039941) B3039941
theorem B3419941 : Blo 2025435 3419941 := bbase (se 4 (by rfl) ⟨320619, by rfl⟩ : syracuseStep 3419941 = 641239) (by norm_num)
theorem B4559921 : Blo 2025435 4559921 := bstep (se 2 (by rfl) ⟨1709970, by rfl⟩ : syracuseStep 4559921 = 3419941) B3419941
theorem B3039947 : Blo 2025435 3039947 := bstep (se 1 (by rfl) ⟨2279960, by rfl⟩ : syracuseStep 3039947 = 4559921) B4559921
theorem B2026631 : Blo 2025435 2026631 := bstep (se 1 (by rfl) ⟨1519973, by rfl⟩ : syracuseStep 2026631 = 3039947) B3039947
theorem B2279965 : Blo 2025435 2279965 := bbase (se 3 (by rfl) ⟨427493, by rfl⟩ : syracuseStep 2279965 = 854987) (by norm_num)
theorem B3039953 : Blo 2025435 3039953 := bstep (se 2 (by rfl) ⟨1139982, by rfl⟩ : syracuseStep 3039953 = 2279965) B2279965
theorem B2026635 : Blo 2025435 2026635 := bstep (se 1 (by rfl) ⟨1519976, by rfl⟩ : syracuseStep 2026635 = 3039953) B3039953
theorem B6839909 : Blo 2025435 6839909 := bbase (se 4 (by rfl) ⟨641241, by rfl⟩ : syracuseStep 6839909 = 1282483) (by norm_num)
theorem B4559939 : Blo 2025435 4559939 := bstep (se 1 (by rfl) ⟨3419954, by rfl⟩ : syracuseStep 4559939 = 6839909) B6839909
theorem B3039959 : Blo 2025435 3039959 := bstep (se 1 (by rfl) ⟨2279969, by rfl⟩ : syracuseStep 3039959 = 4559939) B4559939
theorem B2026639 : Blo 2025435 2026639 := bstep (se 1 (by rfl) ⟨1519979, by rfl⟩ : syracuseStep 2026639 = 3039959) B3039959
theorem B3039965 : Blo 2025435 3039965 := bbase (se 3 (by rfl) ⟨569993, by rfl⟩ : syracuseStep 3039965 = 1139987) (by norm_num)
theorem B2026643 : Blo 2025435 2026643 := bstep (se 1 (by rfl) ⟨1519982, by rfl⟩ : syracuseStep 2026643 = 3039965) B3039965
theorem B4559957 : Blo 2025435 4559957 := bbase (se 8 (by rfl) ⟨26718, by rfl⟩ : syracuseStep 4559957 = 53437) (by norm_num)
theorem B3039971 : Blo 2025435 3039971 := bstep (se 1 (by rfl) ⟨2279978, by rfl⟩ : syracuseStep 3039971 = 4559957) B4559957
theorem B2026647 : Blo 2025435 2026647 := bstep (se 1 (by rfl) ⟨1519985, by rfl⟩ : syracuseStep 2026647 = 3039971) B3039971
theorem B9738917 : Blo 2025435 9738917 := bbase (se 4 (by rfl) ⟨913023, by rfl⟩ : syracuseStep 9738917 = 1826047) (by norm_num)
theorem B6492611 : Blo 2025435 6492611 := bstep (se 1 (by rfl) ⟨4869458, by rfl⟩ : syracuseStep 6492611 = 9738917) B9738917
theorem B4328407 : Blo 2025435 4328407 := bstep (se 1 (by rfl) ⟨3246305, by rfl⟩ : syracuseStep 4328407 = 6492611) B6492611
theorem B5771209 : Blo 2025435 5771209 := bstep (se 2 (by rfl) ⟨2164203, by rfl⟩ : syracuseStep 5771209 = 4328407) B4328407
theorem B7694945 : Blo 2025435 7694945 := bstep (se 2 (by rfl) ⟨2885604, by rfl⟩ : syracuseStep 7694945 = 5771209) B5771209
theorem B5129963 : Blo 2025435 5129963 := bstep (se 1 (by rfl) ⟨3847472, by rfl⟩ : syracuseStep 5129963 = 7694945) B7694945
theorem B3419975 : Blo 2025435 3419975 := bstep (se 1 (by rfl) ⟨2564981, by rfl⟩ : syracuseStep 3419975 = 5129963) B5129963
theorem B2279983 : Blo 2025435 2279983 := bstep (se 1 (by rfl) ⟨1709987, by rfl⟩ : syracuseStep 2279983 = 3419975) B3419975
theorem B3039977 : Blo 2025435 3039977 := bstep (se 2 (by rfl) ⟨1139991, by rfl⟩ : syracuseStep 3039977 = 2279983) B2279983
theorem B2026651 : Blo 2025435 2026651 := bstep (se 1 (by rfl) ⟨1519988, by rfl⟩ : syracuseStep 2026651 = 3039977) B3039977
theorem B3381005 : Blo 2025435 3381005 := bbase (se 3 (by rfl) ⟨633938, by rfl⟩ : syracuseStep 3381005 = 1267877) (by norm_num)
theorem B2254003 : Blo 2025435 2254003 := bstep (se 1 (by rfl) ⟨1690502, by rfl⟩ : syracuseStep 2254003 = 3381005) B3381005
theorem B48085397 : Blo 2025435 48085397 := bstep (se 6 (by rfl) ⟨1127001, by rfl⟩ : syracuseStep 48085397 = 2254003) B2254003
theorem B32056931 : Blo 2025435 32056931 := bstep (se 1 (by rfl) ⟨24042698, by rfl⟩ : syracuseStep 32056931 = 48085397) B48085397
theorem B85485149 : Blo 2025435 85485149 := bstep (se 3 (by rfl) ⟨16028465, by rfl⟩ : syracuseStep 85485149 = 32056931) B32056931
theorem B56990099 : Blo 2025435 56990099 := bstep (se 1 (by rfl) ⟨42742574, by rfl⟩ : syracuseStep 56990099 = 85485149) B85485149
theorem B151973597 : Blo 2025435 151973597 := bstep (se 3 (by rfl) ⟨28495049, by rfl⟩ : syracuseStep 151973597 = 56990099) B56990099
theorem B405262925 : Blo 2025435 405262925 := bstep (se 3 (by rfl) ⟨75986798, by rfl⟩ : syracuseStep 405262925 = 151973597) B151973597
theorem B270175283 : Blo 2025435 270175283 := bstep (se 1 (by rfl) ⟨202631462, by rfl⟩ : syracuseStep 270175283 = 405262925) B405262925
theorem B180116855 : Blo 2025435 180116855 := bstep (se 1 (by rfl) ⟨135087641, by rfl⟩ : syracuseStep 180116855 = 270175283) B270175283
theorem B120077903 : Blo 2025435 120077903 := bstep (se 1 (by rfl) ⟨90058427, by rfl⟩ : syracuseStep 120077903 = 180116855) B180116855
theorem B80051935 : Blo 2025435 80051935 := bstep (se 1 (by rfl) ⟨60038951, by rfl⟩ : syracuseStep 80051935 = 120077903) B120077903
theorem B106735913 : Blo 2025435 106735913 := bstep (se 2 (by rfl) ⟨40025967, by rfl⟩ : syracuseStep 106735913 = 80051935) B80051935
theorem B71157275 : Blo 2025435 71157275 := bstep (se 1 (by rfl) ⟨53367956, by rfl⟩ : syracuseStep 71157275 = 106735913) B106735913
theorem B47438183 : Blo 2025435 47438183 := bstep (se 1 (by rfl) ⟨35578637, by rfl⟩ : syracuseStep 47438183 = 71157275) B71157275
theorem B126501821 : Blo 2025435 126501821 := bstep (se 3 (by rfl) ⟨23719091, by rfl⟩ : syracuseStep 126501821 = 47438183) B47438183
theorem B84334547 : Blo 2025435 84334547 := bstep (se 1 (by rfl) ⟨63250910, by rfl⟩ : syracuseStep 84334547 = 126501821) B126501821
theorem B56223031 : Blo 2025435 56223031 := bstep (se 1 (by rfl) ⟨42167273, by rfl⟩ : syracuseStep 56223031 = 84334547) B84334547
theorem B74964041 : Blo 2025435 74964041 := bstep (se 2 (by rfl) ⟨28111515, by rfl⟩ : syracuseStep 74964041 = 56223031) B56223031
theorem B49976027 : Blo 2025435 49976027 := bstep (se 1 (by rfl) ⟨37482020, by rfl⟩ : syracuseStep 49976027 = 74964041) B74964041
theorem B33317351 : Blo 2025435 33317351 := bstep (se 1 (by rfl) ⟨24988013, by rfl⟩ : syracuseStep 33317351 = 49976027) B49976027
theorem B22211567 : Blo 2025435 22211567 := bstep (se 1 (by rfl) ⟨16658675, by rfl⟩ : syracuseStep 22211567 = 33317351) B33317351
theorem B14807711 : Blo 2025435 14807711 := bstep (se 1 (by rfl) ⟨11105783, by rfl⟩ : syracuseStep 14807711 = 22211567) B22211567
theorem B9871807 : Blo 2025435 9871807 := bstep (se 1 (by rfl) ⟨7403855, by rfl⟩ : syracuseStep 9871807 = 14807711) B14807711
theorem B13162409 : Blo 2025435 13162409 := bstep (se 2 (by rfl) ⟨4935903, by rfl⟩ : syracuseStep 13162409 = 9871807) B9871807
theorem B8774939 : Blo 2025435 8774939 := bstep (se 1 (by rfl) ⟨6581204, by rfl⟩ : syracuseStep 8774939 = 13162409) B13162409
theorem B23399837 : Blo 2025435 23399837 := bstep (se 3 (by rfl) ⟨4387469, by rfl⟩ : syracuseStep 23399837 = 8774939) B8774939
theorem B15599891 : Blo 2025435 15599891 := bstep (se 1 (by rfl) ⟨11699918, by rfl⟩ : syracuseStep 15599891 = 23399837) B23399837
theorem B10399927 : Blo 2025435 10399927 := bstep (se 1 (by rfl) ⟨7799945, by rfl⟩ : syracuseStep 10399927 = 15599891) B15599891
theorem B13866569 : Blo 2025435 13866569 := bstep (se 2 (by rfl) ⟨5199963, by rfl⟩ : syracuseStep 13866569 = 10399927) B10399927
theorem B9244379 : Blo 2025435 9244379 := bstep (se 1 (by rfl) ⟨6933284, by rfl⟩ : syracuseStep 9244379 = 13866569) B13866569
theorem B24651677 : Blo 2025435 24651677 := bstep (se 3 (by rfl) ⟨4622189, by rfl⟩ : syracuseStep 24651677 = 9244379) B9244379
theorem B16434451 : Blo 2025435 16434451 := bstep (se 1 (by rfl) ⟨12325838, by rfl⟩ : syracuseStep 16434451 = 24651677) B24651677
theorem B21912601 : Blo 2025435 21912601 := bstep (se 2 (by rfl) ⟨8217225, by rfl⟩ : syracuseStep 21912601 = 16434451) B16434451
theorem B29216801 : Blo 2025435 29216801 := bstep (se 2 (by rfl) ⟨10956300, by rfl⟩ : syracuseStep 29216801 = 21912601) B21912601
theorem B19477867 : Blo 2025435 19477867 := bstep (se 1 (by rfl) ⟨14608400, by rfl⟩ : syracuseStep 19477867 = 29216801) B29216801
theorem B25970489 : Blo 2025435 25970489 := bstep (se 2 (by rfl) ⟨9738933, by rfl⟩ : syracuseStep 25970489 = 19477867) B19477867
theorem B17313659 : Blo 2025435 17313659 := bstep (se 1 (by rfl) ⟨12985244, by rfl⟩ : syracuseStep 17313659 = 25970489) B25970489
theorem B11542439 : Blo 2025435 11542439 := bstep (se 1 (by rfl) ⟨8656829, by rfl⟩ : syracuseStep 11542439 = 17313659) B17313659
theorem B7694959 : Blo 2025435 7694959 := bstep (se 1 (by rfl) ⟨5771219, by rfl⟩ : syracuseStep 7694959 = 11542439) B11542439
theorem B10259945 : Blo 2025435 10259945 := bstep (se 2 (by rfl) ⟨3847479, by rfl⟩ : syracuseStep 10259945 = 7694959) B7694959
theorem B6839963 : Blo 2025435 6839963 := bstep (se 1 (by rfl) ⟨5129972, by rfl⟩ : syracuseStep 6839963 = 10259945) B10259945
theorem B4559975 : Blo 2025435 4559975 := bstep (se 1 (by rfl) ⟨3419981, by rfl⟩ : syracuseStep 4559975 = 6839963) B6839963
theorem B3039983 : Blo 2025435 3039983 := bstep (se 1 (by rfl) ⟨2279987, by rfl⟩ : syracuseStep 3039983 = 4559975) B4559975
theorem B2026655 : Blo 2025435 2026655 := bstep (se 1 (by rfl) ⟨1519991, by rfl⟩ : syracuseStep 2026655 = 3039983) B3039983
theorem B3039989 : Blo 2025435 3039989 := bbase (se 5 (by rfl) ⟨142499, by rfl⟩ : syracuseStep 3039989 = 284999) (by norm_num)
theorem B2026659 : Blo 2025435 2026659 := bstep (se 1 (by rfl) ⟨1519994, by rfl⟩ : syracuseStep 2026659 = 3039989) B3039989
theorem B2599993 : Blo 2025435 2599993 := bbase (se 2 (by rfl) ⟨974997, by rfl⟩ : syracuseStep 2599993 = 1949995) (by norm_num)
theorem B3466657 : Blo 2025435 3466657 := bstep (se 2 (by rfl) ⟨1299996, by rfl⟩ : syracuseStep 3466657 = 2599993) B2599993
theorem B18488837 : Blo 2025435 18488837 := bstep (se 4 (by rfl) ⟨1733328, by rfl⟩ : syracuseStep 18488837 = 3466657) B3466657
theorem B12325891 : Blo 2025435 12325891 := bstep (se 1 (by rfl) ⟨9244418, by rfl⟩ : syracuseStep 12325891 = 18488837) B18488837
theorem B16434521 : Blo 2025435 16434521 := bstep (se 2 (by rfl) ⟨6162945, by rfl⟩ : syracuseStep 16434521 = 12325891) B12325891
theorem B10956347 : Blo 2025435 10956347 := bstep (se 1 (by rfl) ⟨8217260, by rfl⟩ : syracuseStep 10956347 = 16434521) B16434521
theorem B7304231 : Blo 2025435 7304231 := bstep (se 1 (by rfl) ⟨5478173, by rfl⟩ : syracuseStep 7304231 = 10956347) B10956347
theorem B4869487 : Blo 2025435 4869487 := bstep (se 1 (by rfl) ⟨3652115, by rfl⟩ : syracuseStep 4869487 = 7304231) B7304231
theorem B6492649 : Blo 2025435 6492649 := bstep (se 2 (by rfl) ⟨2434743, by rfl⟩ : syracuseStep 6492649 = 4869487) B4869487
theorem B8656865 : Blo 2025435 8656865 := bstep (se 2 (by rfl) ⟨3246324, by rfl⟩ : syracuseStep 8656865 = 6492649) B6492649
theorem B5771243 : Blo 2025435 5771243 := bstep (se 1 (by rfl) ⟨4328432, by rfl⟩ : syracuseStep 5771243 = 8656865) B8656865
theorem B3847495 : Blo 2025435 3847495 := bstep (se 1 (by rfl) ⟨2885621, by rfl⟩ : syracuseStep 3847495 = 5771243) B5771243
theorem B5129993 : Blo 2025435 5129993 := bstep (se 2 (by rfl) ⟨1923747, by rfl⟩ : syracuseStep 5129993 = 3847495) B3847495
theorem B3419995 : Blo 2025435 3419995 := bstep (se 1 (by rfl) ⟨2564996, by rfl⟩ : syracuseStep 3419995 = 5129993) B5129993
theorem B4559993 : Blo 2025435 4559993 := bstep (se 2 (by rfl) ⟨1709997, by rfl⟩ : syracuseStep 4559993 = 3419995) B3419995
theorem B3039995 : Blo 2025435 3039995 := bstep (se 1 (by rfl) ⟨2279996, by rfl⟩ : syracuseStep 3039995 = 4559993) B4559993
theorem B2026663 : Blo 2025435 2026663 := bstep (se 1 (by rfl) ⟨1519997, by rfl⟩ : syracuseStep 2026663 = 3039995) B3039995
theorem B2280001 : Blo 2025435 2280001 := bbase (se 2 (by rfl) ⟨855000, by rfl⟩ : syracuseStep 2280001 = 1710001) (by norm_num)
theorem B3040001 : Blo 2025435 3040001 := bstep (se 2 (by rfl) ⟨1140000, by rfl⟩ : syracuseStep 3040001 = 2280001) B2280001
theorem B2026667 : Blo 2025435 2026667 := bstep (se 1 (by rfl) ⟨1520000, by rfl⟩ : syracuseStep 2026667 = 3040001) B3040001
theorem B5130013 : Blo 2025435 5130013 := bbase (se 3 (by rfl) ⟨961877, by rfl⟩ : syracuseStep 5130013 = 1923755) (by norm_num)
theorem B6840017 : Blo 2025435 6840017 := bstep (se 2 (by rfl) ⟨2565006, by rfl⟩ : syracuseStep 6840017 = 5130013) B5130013
theorem B4560011 : Blo 2025435 4560011 := bstep (se 1 (by rfl) ⟨3420008, by rfl⟩ : syracuseStep 4560011 = 6840017) B6840017
theorem B3040007 : Blo 2025435 3040007 := bstep (se 1 (by rfl) ⟨2280005, by rfl⟩ : syracuseStep 3040007 = 4560011) B4560011
theorem B2026671 : Blo 2025435 2026671 := bstep (se 1 (by rfl) ⟨1520003, by rfl⟩ : syracuseStep 2026671 = 3040007) B3040007
theorem B3040013 : Blo 2025435 3040013 := bbase (se 3 (by rfl) ⟨570002, by rfl⟩ : syracuseStep 3040013 = 1140005) (by norm_num)
theorem B2026675 : Blo 2025435 2026675 := bstep (se 1 (by rfl) ⟨1520006, by rfl⟩ : syracuseStep 2026675 = 3040013) B3040013
theorem B4560029 : Blo 2025435 4560029 := bbase (se 3 (by rfl) ⟨855005, by rfl⟩ : syracuseStep 4560029 = 1710011) (by norm_num)
theorem B3040019 : Blo 2025435 3040019 := bstep (se 1 (by rfl) ⟨2280014, by rfl⟩ : syracuseStep 3040019 = 4560029) B4560029
theorem B2026679 : Blo 2025435 2026679 := bstep (se 1 (by rfl) ⟨1520009, by rfl⟩ : syracuseStep 2026679 = 3040019) B3040019
theorem B3420029 : Blo 2025435 3420029 := bbase (se 3 (by rfl) ⟨641255, by rfl⟩ : syracuseStep 3420029 = 1282511) (by norm_num)
theorem B2280019 : Blo 2025435 2280019 := bstep (se 1 (by rfl) ⟨1710014, by rfl⟩ : syracuseStep 2280019 = 3420029) B3420029
theorem B3040025 : Blo 2025435 3040025 := bstep (se 2 (by rfl) ⟨1140009, by rfl⟩ : syracuseStep 3040025 = 2280019) B2280019
theorem B2026683 : Blo 2025435 2026683 := bstep (se 1 (by rfl) ⟨1520012, by rfl⟩ : syracuseStep 2026683 = 3040025) B3040025
theorem B6492725 : Blo 2025435 6492725 := bbase (se 5 (by rfl) ⟨304346, by rfl⟩ : syracuseStep 6492725 = 608693) (by norm_num)
theorem B4328483 : Blo 2025435 4328483 := bstep (se 1 (by rfl) ⟨3246362, by rfl⟩ : syracuseStep 4328483 = 6492725) B6492725
theorem B11542621 : Blo 2025435 11542621 := bstep (se 3 (by rfl) ⟨2164241, by rfl⟩ : syracuseStep 11542621 = 4328483) B4328483
theorem B15390161 : Blo 2025435 15390161 := bstep (se 2 (by rfl) ⟨5771310, by rfl⟩ : syracuseStep 15390161 = 11542621) B11542621
theorem B10260107 : Blo 2025435 10260107 := bstep (se 1 (by rfl) ⟨7695080, by rfl⟩ : syracuseStep 10260107 = 15390161) B15390161
theorem B6840071 : Blo 2025435 6840071 := bstep (se 1 (by rfl) ⟨5130053, by rfl⟩ : syracuseStep 6840071 = 10260107) B10260107
theorem B4560047 : Blo 2025435 4560047 := bstep (se 1 (by rfl) ⟨3420035, by rfl⟩ : syracuseStep 4560047 = 6840071) B6840071
theorem B3040031 : Blo 2025435 3040031 := bstep (se 1 (by rfl) ⟨2280023, by rfl⟩ : syracuseStep 3040031 = 4560047) B4560047
theorem B2026687 : Blo 2025435 2026687 := bstep (se 1 (by rfl) ⟨1520015, by rfl⟩ : syracuseStep 2026687 = 3040031) B3040031
theorem B3040037 : Blo 2025435 3040037 := bbase (se 4 (by rfl) ⟨285003, by rfl⟩ : syracuseStep 3040037 = 570007) (by norm_num)
theorem B2026691 : Blo 2025435 2026691 := bstep (se 1 (by rfl) ⟨1520018, by rfl⟩ : syracuseStep 2026691 = 3040037) B3040037
theorem B2565037 : Blo 2025435 2565037 := bbase (se 3 (by rfl) ⟨480944, by rfl⟩ : syracuseStep 2565037 = 961889) (by norm_num)
theorem B3420049 : Blo 2025435 3420049 := bstep (se 2 (by rfl) ⟨1282518, by rfl⟩ : syracuseStep 3420049 = 2565037) B2565037
theorem B4560065 : Blo 2025435 4560065 := bstep (se 2 (by rfl) ⟨1710024, by rfl⟩ : syracuseStep 4560065 = 3420049) B3420049
theorem B3040043 : Blo 2025435 3040043 := bstep (se 1 (by rfl) ⟨2280032, by rfl⟩ : syracuseStep 3040043 = 4560065) B4560065
theorem B2026695 : Blo 2025435 2026695 := bstep (se 1 (by rfl) ⟨1520021, by rfl⟩ : syracuseStep 2026695 = 3040043) B3040043
theorem B2280037 : Blo 2025435 2280037 := bbase (se 4 (by rfl) ⟨213753, by rfl⟩ : syracuseStep 2280037 = 427507) (by norm_num)
theorem B3040049 : Blo 2025435 3040049 := bstep (se 2 (by rfl) ⟨1140018, by rfl⟩ : syracuseStep 3040049 = 2280037) B2280037
theorem B2026699 : Blo 2025435 2026699 := bstep (se 1 (by rfl) ⟨1520024, by rfl⟩ : syracuseStep 2026699 = 3040049) B3040049
theorem B3246389 : Blo 2025435 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B2164259 : Blo 2025435 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B5771357 : Blo 2025435 5771357 := bstep (se 3 (by rfl) ⟨1082129, by rfl⟩ : syracuseStep 5771357 = 2164259) B2164259
theorem B3847571 : Blo 2025435 3847571 := bstep (se 1 (by rfl) ⟨2885678, by rfl⟩ : syracuseStep 3847571 = 5771357) B5771357
theorem B2565047 : Blo 2025435 2565047 := bstep (se 1 (by rfl) ⟨1923785, by rfl⟩ : syracuseStep 2565047 = 3847571) B3847571
theorem B6840125 : Blo 2025435 6840125 := bstep (se 3 (by rfl) ⟨1282523, by rfl⟩ : syracuseStep 6840125 = 2565047) B2565047
theorem B4560083 : Blo 2025435 4560083 := bstep (se 1 (by rfl) ⟨3420062, by rfl⟩ : syracuseStep 4560083 = 6840125) B6840125
theorem B3040055 : Blo 2025435 3040055 := bstep (se 1 (by rfl) ⟨2280041, by rfl⟩ : syracuseStep 3040055 = 4560083) B4560083
theorem B2026703 : Blo 2025435 2026703 := bstep (se 1 (by rfl) ⟨1520027, by rfl⟩ : syracuseStep 2026703 = 3040055) B3040055
theorem B3040061 : Blo 2025435 3040061 := bbase (se 3 (by rfl) ⟨570011, by rfl⟩ : syracuseStep 3040061 = 1140023) (by norm_num)
theorem B2026707 : Blo 2025435 2026707 := bstep (se 1 (by rfl) ⟨1520030, by rfl⟩ : syracuseStep 2026707 = 3040061) B3040061
theorem B4560101 : Blo 2025435 4560101 := bbase (se 4 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 4560101 = 855019) (by norm_num)
theorem B3040067 : Blo 2025435 3040067 := bstep (se 1 (by rfl) ⟨2280050, by rfl⟩ : syracuseStep 3040067 = 4560101) B4560101
theorem B2026711 : Blo 2025435 2026711 := bstep (se 1 (by rfl) ⟨1520033, by rfl⟩ : syracuseStep 2026711 = 3040067) B3040067
theorem B5130125 : Blo 2025435 5130125 := bbase (se 3 (by rfl) ⟨961898, by rfl⟩ : syracuseStep 5130125 = 1923797) (by norm_num)
theorem B3420083 : Blo 2025435 3420083 := bstep (se 1 (by rfl) ⟨2565062, by rfl⟩ : syracuseStep 3420083 = 5130125) B5130125
theorem B2280055 : Blo 2025435 2280055 := bstep (se 1 (by rfl) ⟨1710041, by rfl⟩ : syracuseStep 2280055 = 3420083) B3420083
theorem B3040073 : Blo 2025435 3040073 := bstep (se 2 (by rfl) ⟨1140027, by rfl⟩ : syracuseStep 3040073 = 2280055) B2280055
theorem B2026715 : Blo 2025435 2026715 := bstep (se 1 (by rfl) ⟨1520036, by rfl⟩ : syracuseStep 2026715 = 3040073) B3040073
theorem B2885701 : Blo 2025435 2885701 := bbase (se 4 (by rfl) ⟨270534, by rfl⟩ : syracuseStep 2885701 = 541069) (by norm_num)
theorem B3847601 : Blo 2025435 3847601 := bstep (se 2 (by rfl) ⟨1442850, by rfl⟩ : syracuseStep 3847601 = 2885701) B2885701
theorem B10260269 : Blo 2025435 10260269 := bstep (se 3 (by rfl) ⟨1923800, by rfl⟩ : syracuseStep 10260269 = 3847601) B3847601
theorem B6840179 : Blo 2025435 6840179 := bstep (se 1 (by rfl) ⟨5130134, by rfl⟩ : syracuseStep 6840179 = 10260269) B10260269
theorem B4560119 : Blo 2025435 4560119 := bstep (se 1 (by rfl) ⟨3420089, by rfl⟩ : syracuseStep 4560119 = 6840179) B6840179
theorem B3040079 : Blo 2025435 3040079 := bstep (se 1 (by rfl) ⟨2280059, by rfl⟩ : syracuseStep 3040079 = 4560119) B4560119
theorem B2026719 : Blo 2025435 2026719 := bstep (se 1 (by rfl) ⟨1520039, by rfl⟩ : syracuseStep 2026719 = 3040079) B3040079
theorem B3040085 : Blo 2025435 3040085 := bbase (se 9 (by rfl) ⟨8906, by rfl⟩ : syracuseStep 3040085 = 17813) (by norm_num)
theorem B2026723 : Blo 2025435 2026723 := bstep (se 1 (by rfl) ⟨1520042, by rfl⟩ : syracuseStep 2026723 = 3040085) B3040085
theorem B6163141 : Blo 2025435 6163141 := bbase (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) (by norm_num)
theorem B8217521 : Blo 2025435 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B5478347 : Blo 2025435 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B3652231 : Blo 2025435 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B4869641 : Blo 2025435 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B3246427 : Blo 2025435 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B4328569 : Blo 2025435 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B5771425 : Blo 2025435 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B7695233 : Blo 2025435 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B5130155 : Blo 2025435 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B3420103 : Blo 2025435 3420103 := bstep (se 1 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 3420103 = 5130155) B5130155
theorem B4560137 : Blo 2025435 4560137 := bstep (se 2 (by rfl) ⟨1710051, by rfl⟩ : syracuseStep 4560137 = 3420103) B3420103
theorem B3040091 : Blo 2025435 3040091 := bstep (se 1 (by rfl) ⟨2280068, by rfl⟩ : syracuseStep 3040091 = 4560137) B4560137
theorem B2026727 : Blo 2025435 2026727 := bstep (se 1 (by rfl) ⟨1520045, by rfl⟩ : syracuseStep 2026727 = 3040091) B3040091
theorem B2280073 : Blo 2025435 2280073 := bbase (se 2 (by rfl) ⟨855027, by rfl⟩ : syracuseStep 2280073 = 1710055) (by norm_num)
theorem B3040097 : Blo 2025435 3040097 := bstep (se 2 (by rfl) ⟨1140036, by rfl⟩ : syracuseStep 3040097 = 2280073) B2280073
theorem B2026731 : Blo 2025435 2026731 := bstep (se 1 (by rfl) ⟨1520048, by rfl⟩ : syracuseStep 2026731 = 3040097) B3040097
theorem B7404149 : Blo 2025435 7404149 := bbase (se 5 (by rfl) ⟨347069, by rfl⟩ : syracuseStep 7404149 = 694139) (by norm_num)
theorem B19744397 : Blo 2025435 19744397 := bstep (se 3 (by rfl) ⟨3702074, by rfl⟩ : syracuseStep 19744397 = 7404149) B7404149
theorem B13162931 : Blo 2025435 13162931 := bstep (se 1 (by rfl) ⟨9872198, by rfl⟩ : syracuseStep 13162931 = 19744397) B19744397
theorem B8775287 : Blo 2025435 8775287 := bstep (se 1 (by rfl) ⟨6581465, by rfl⟩ : syracuseStep 8775287 = 13162931) B13162931
theorem B5850191 : Blo 2025435 5850191 := bstep (se 1 (by rfl) ⟨4387643, by rfl⟩ : syracuseStep 5850191 = 8775287) B8775287
theorem B15600509 : Blo 2025435 15600509 := bstep (se 3 (by rfl) ⟨2925095, by rfl⟩ : syracuseStep 15600509 = 5850191) B5850191
theorem B10400339 : Blo 2025435 10400339 := bstep (se 1 (by rfl) ⟨7800254, by rfl⟩ : syracuseStep 10400339 = 15600509) B15600509
theorem B6933559 : Blo 2025435 6933559 := bstep (se 1 (by rfl) ⟨5200169, by rfl⟩ : syracuseStep 6933559 = 10400339) B10400339
theorem B9244745 : Blo 2025435 9244745 := bstep (se 2 (by rfl) ⟨3466779, by rfl⟩ : syracuseStep 9244745 = 6933559) B6933559
theorem B6163163 : Blo 2025435 6163163 := bstep (se 1 (by rfl) ⟨4622372, by rfl⟩ : syracuseStep 6163163 = 9244745) B9244745
theorem B4108775 : Blo 2025435 4108775 := bstep (se 1 (by rfl) ⟨3081581, by rfl⟩ : syracuseStep 4108775 = 6163163) B6163163
theorem B43826933 : Blo 2025435 43826933 := bstep (se 5 (by rfl) ⟨2054387, by rfl⟩ : syracuseStep 43826933 = 4108775) B4108775
theorem B29217955 : Blo 2025435 29217955 := bstep (se 1 (by rfl) ⟨21913466, by rfl⟩ : syracuseStep 29217955 = 43826933) B43826933
theorem B38957273 : Blo 2025435 38957273 := bstep (se 2 (by rfl) ⟨14608977, by rfl⟩ : syracuseStep 38957273 = 29217955) B29217955
theorem B25971515 : Blo 2025435 25971515 := bstep (se 1 (by rfl) ⟨19478636, by rfl⟩ : syracuseStep 25971515 = 38957273) B38957273
theorem B17314343 : Blo 2025435 17314343 := bstep (se 1 (by rfl) ⟨12985757, by rfl⟩ : syracuseStep 17314343 = 25971515) B25971515
theorem B11542895 : Blo 2025435 11542895 := bstep (se 1 (by rfl) ⟨8657171, by rfl⟩ : syracuseStep 11542895 = 17314343) B17314343
theorem B7695263 : Blo 2025435 7695263 := bstep (se 1 (by rfl) ⟨5771447, by rfl⟩ : syracuseStep 7695263 = 11542895) B11542895
theorem B5130175 : Blo 2025435 5130175 := bstep (se 1 (by rfl) ⟨3847631, by rfl⟩ : syracuseStep 5130175 = 7695263) B7695263
theorem B6840233 : Blo 2025435 6840233 := bstep (se 2 (by rfl) ⟨2565087, by rfl⟩ : syracuseStep 6840233 = 5130175) B5130175
theorem B4560155 : Blo 2025435 4560155 := bstep (se 1 (by rfl) ⟨3420116, by rfl⟩ : syracuseStep 4560155 = 6840233) B6840233
theorem B3040103 : Blo 2025435 3040103 := bstep (se 1 (by rfl) ⟨2280077, by rfl⟩ : syracuseStep 3040103 = 4560155) B4560155
theorem B2026735 : Blo 2025435 2026735 := bstep (se 1 (by rfl) ⟨1520051, by rfl⟩ : syracuseStep 2026735 = 3040103) B3040103
theorem B3040109 : Blo 2025435 3040109 := bbase (se 3 (by rfl) ⟨570020, by rfl⟩ : syracuseStep 3040109 = 1140041) (by norm_num)
theorem B2026739 : Blo 2025435 2026739 := bstep (se 1 (by rfl) ⟨1520054, by rfl⟩ : syracuseStep 2026739 = 3040109) B3040109
theorem B4560173 : Blo 2025435 4560173 := bbase (se 3 (by rfl) ⟨855032, by rfl⟩ : syracuseStep 4560173 = 1710065) (by norm_num)
theorem B3040115 : Blo 2025435 3040115 := bstep (se 1 (by rfl) ⟨2280086, by rfl⟩ : syracuseStep 3040115 = 4560173) B4560173
theorem B2026743 : Blo 2025435 2026743 := bstep (se 1 (by rfl) ⟨1520057, by rfl⟩ : syracuseStep 2026743 = 3040115) B3040115
theorem B2311201 : Blo 2025435 2311201 := bbase (se 2 (by rfl) ⟨866700, by rfl⟩ : syracuseStep 2311201 = 1733401) (by norm_num)
theorem B3081601 : Blo 2025435 3081601 := bstep (se 2 (by rfl) ⟨1155600, by rfl⟩ : syracuseStep 3081601 = 2311201) B2311201
theorem B4108801 : Blo 2025435 4108801 := bstep (se 2 (by rfl) ⟨1540800, by rfl⟩ : syracuseStep 4108801 = 3081601) B3081601
theorem B5478401 : Blo 2025435 5478401 := bstep (se 2 (by rfl) ⟨2054400, by rfl⟩ : syracuseStep 5478401 = 4108801) B4108801
theorem B14609069 : Blo 2025435 14609069 := bstep (se 3 (by rfl) ⟨2739200, by rfl⟩ : syracuseStep 14609069 = 5478401) B5478401
theorem B9739379 : Blo 2025435 9739379 := bstep (se 1 (by rfl) ⟨7304534, by rfl⟩ : syracuseStep 9739379 = 14609069) B14609069
theorem B6492919 : Blo 2025435 6492919 := bstep (se 1 (by rfl) ⟨4869689, by rfl⟩ : syracuseStep 6492919 = 9739379) B9739379
theorem B8657225 : Blo 2025435 8657225 := bstep (se 2 (by rfl) ⟨3246459, by rfl⟩ : syracuseStep 8657225 = 6492919) B6492919
theorem B5771483 : Blo 2025435 5771483 := bstep (se 1 (by rfl) ⟨4328612, by rfl⟩ : syracuseStep 5771483 = 8657225) B8657225
theorem B3847655 : Blo 2025435 3847655 := bstep (se 1 (by rfl) ⟨2885741, by rfl⟩ : syracuseStep 3847655 = 5771483) B5771483
theorem B2565103 : Blo 2025435 2565103 := bstep (se 1 (by rfl) ⟨1923827, by rfl⟩ : syracuseStep 2565103 = 3847655) B3847655
theorem B3420137 : Blo 2025435 3420137 := bstep (se 2 (by rfl) ⟨1282551, by rfl⟩ : syracuseStep 3420137 = 2565103) B2565103
theorem B2280091 : Blo 2025435 2280091 := bstep (se 1 (by rfl) ⟨1710068, by rfl⟩ : syracuseStep 2280091 = 3420137) B3420137
theorem B3040121 : Blo 2025435 3040121 := bstep (se 2 (by rfl) ⟨1140045, by rfl⟩ : syracuseStep 3040121 = 2280091) B2280091
theorem B2026747 : Blo 2025435 2026747 := bstep (se 1 (by rfl) ⟨1520060, by rfl⟩ : syracuseStep 2026747 = 3040121) B3040121
theorem B2739205 : Blo 2025435 2739205 := bbase (se 4 (by rfl) ⟨256800, by rfl⟩ : syracuseStep 2739205 = 513601) (by norm_num)
theorem B3652273 : Blo 2025435 3652273 := bstep (se 2 (by rfl) ⟨1369602, by rfl⟩ : syracuseStep 3652273 = 2739205) B2739205
theorem B19478789 : Blo 2025435 19478789 := bstep (se 4 (by rfl) ⟨1826136, by rfl⟩ : syracuseStep 19478789 = 3652273) B3652273
theorem B12985859 : Blo 2025435 12985859 := bstep (se 1 (by rfl) ⟨9739394, by rfl⟩ : syracuseStep 12985859 = 19478789) B19478789
theorem B34628957 : Blo 2025435 34628957 := bstep (se 3 (by rfl) ⟨6492929, by rfl⟩ : syracuseStep 34628957 = 12985859) B12985859
theorem B23085971 : Blo 2025435 23085971 := bstep (se 1 (by rfl) ⟨17314478, by rfl⟩ : syracuseStep 23085971 = 34628957) B34628957
theorem B15390647 : Blo 2025435 15390647 := bstep (se 1 (by rfl) ⟨11542985, by rfl⟩ : syracuseStep 15390647 = 23085971) B23085971
theorem B10260431 : Blo 2025435 10260431 := bstep (se 1 (by rfl) ⟨7695323, by rfl⟩ : syracuseStep 10260431 = 15390647) B15390647
theorem B6840287 : Blo 2025435 6840287 := bstep (se 1 (by rfl) ⟨5130215, by rfl⟩ : syracuseStep 6840287 = 10260431) B10260431
theorem B4560191 : Blo 2025435 4560191 := bstep (se 1 (by rfl) ⟨3420143, by rfl⟩ : syracuseStep 4560191 = 6840287) B6840287
theorem B3040127 : Blo 2025435 3040127 := bstep (se 1 (by rfl) ⟨2280095, by rfl⟩ : syracuseStep 3040127 = 4560191) B4560191
theorem B2026751 : Blo 2025435 2026751 := bstep (se 1 (by rfl) ⟨1520063, by rfl⟩ : syracuseStep 2026751 = 3040127) B3040127
theorem B3040133 : Blo 2025435 3040133 := bbase (se 4 (by rfl) ⟨285012, by rfl⟩ : syracuseStep 3040133 = 570025) (by norm_num)
theorem B2026755 : Blo 2025435 2026755 := bstep (se 1 (by rfl) ⟨1520066, by rfl⟩ : syracuseStep 2026755 = 3040133) B3040133
theorem B3420157 : Blo 2025435 3420157 := bbase (se 3 (by rfl) ⟨641279, by rfl⟩ : syracuseStep 3420157 = 1282559) (by norm_num)
theorem B4560209 : Blo 2025435 4560209 := bstep (se 2 (by rfl) ⟨1710078, by rfl⟩ : syracuseStep 4560209 = 3420157) B3420157
theorem B3040139 : Blo 2025435 3040139 := bstep (se 1 (by rfl) ⟨2280104, by rfl⟩ : syracuseStep 3040139 = 4560209) B4560209
theorem B2026759 : Blo 2025435 2026759 := bstep (se 1 (by rfl) ⟨1520069, by rfl⟩ : syracuseStep 2026759 = 3040139) B3040139
theorem B2280109 : Blo 2025435 2280109 := bbase (se 3 (by rfl) ⟨427520, by rfl⟩ : syracuseStep 2280109 = 855041) (by norm_num)
theorem B3040145 : Blo 2025435 3040145 := bstep (se 2 (by rfl) ⟨1140054, by rfl⟩ : syracuseStep 3040145 = 2280109) B2280109
theorem B2026763 : Blo 2025435 2026763 := bstep (se 1 (by rfl) ⟨1520072, by rfl⟩ : syracuseStep 2026763 = 3040145) B3040145
theorem B6840341 : Blo 2025435 6840341 := bbase (se 6 (by rfl) ⟨160320, by rfl⟩ : syracuseStep 6840341 = 320641) (by norm_num)
theorem B4560227 : Blo 2025435 4560227 := bstep (se 1 (by rfl) ⟨3420170, by rfl⟩ : syracuseStep 4560227 = 6840341) B6840341
theorem B3040151 : Blo 2025435 3040151 := bstep (se 1 (by rfl) ⟨2280113, by rfl⟩ : syracuseStep 3040151 = 4560227) B4560227
theorem B2026767 : Blo 2025435 2026767 := bstep (se 1 (by rfl) ⟨1520075, by rfl⟩ : syracuseStep 2026767 = 3040151) B3040151
theorem B3040157 : Blo 2025435 3040157 := bbase (se 3 (by rfl) ⟨570029, by rfl⟩ : syracuseStep 3040157 = 1140059) (by norm_num)
theorem B2026771 : Blo 2025435 2026771 := bstep (se 1 (by rfl) ⟨1520078, by rfl⟩ : syracuseStep 2026771 = 3040157) B3040157
theorem B4560245 : Blo 2025435 4560245 := bbase (se 5 (by rfl) ⟨213761, by rfl⟩ : syracuseStep 4560245 = 427523) (by norm_num)
theorem B3040163 : Blo 2025435 3040163 := bstep (se 1 (by rfl) ⟨2280122, by rfl⟩ : syracuseStep 3040163 = 4560245) B4560245
theorem B2026775 : Blo 2025435 2026775 := bstep (se 1 (by rfl) ⟨1520081, by rfl⟩ : syracuseStep 2026775 = 3040163) B3040163
theorem B2311237 : Blo 2025435 2311237 := bbase (se 4 (by rfl) ⟨216678, by rfl⟩ : syracuseStep 2311237 = 433357) (by norm_num)
theorem B3081649 : Blo 2025435 3081649 := bstep (se 2 (by rfl) ⟨1155618, by rfl⟩ : syracuseStep 3081649 = 2311237) B2311237
theorem B4108865 : Blo 2025435 4108865 := bstep (se 2 (by rfl) ⟨1540824, by rfl⟩ : syracuseStep 4108865 = 3081649) B3081649
theorem B10956973 : Blo 2025435 10956973 := bstep (se 3 (by rfl) ⟨2054432, by rfl⟩ : syracuseStep 10956973 = 4108865) B4108865
theorem B14609297 : Blo 2025435 14609297 := bstep (se 2 (by rfl) ⟨5478486, by rfl⟩ : syracuseStep 14609297 = 10956973) B10956973
theorem B9739531 : Blo 2025435 9739531 := bstep (se 1 (by rfl) ⟨7304648, by rfl⟩ : syracuseStep 9739531 = 14609297) B14609297
theorem B12986041 : Blo 2025435 12986041 := bstep (se 2 (by rfl) ⟨4869765, by rfl⟩ : syracuseStep 12986041 = 9739531) B9739531
theorem B17314721 : Blo 2025435 17314721 := bstep (se 2 (by rfl) ⟨6493020, by rfl⟩ : syracuseStep 17314721 = 12986041) B12986041
theorem B11543147 : Blo 2025435 11543147 := bstep (se 1 (by rfl) ⟨8657360, by rfl⟩ : syracuseStep 11543147 = 17314721) B17314721
theorem B7695431 : Blo 2025435 7695431 := bstep (se 1 (by rfl) ⟨5771573, by rfl⟩ : syracuseStep 7695431 = 11543147) B11543147
theorem B5130287 : Blo 2025435 5130287 := bstep (se 1 (by rfl) ⟨3847715, by rfl⟩ : syracuseStep 5130287 = 7695431) B7695431
theorem B3420191 : Blo 2025435 3420191 := bstep (se 1 (by rfl) ⟨2565143, by rfl⟩ : syracuseStep 3420191 = 5130287) B5130287
theorem B2280127 : Blo 2025435 2280127 := bstep (se 1 (by rfl) ⟨1710095, by rfl⟩ : syracuseStep 2280127 = 3420191) B3420191
theorem B3040169 : Blo 2025435 3040169 := bstep (se 2 (by rfl) ⟨1140063, by rfl⟩ : syracuseStep 3040169 = 2280127) B2280127
theorem B2026779 : Blo 2025435 2026779 := bstep (se 1 (by rfl) ⟨1520084, by rfl⟩ : syracuseStep 2026779 = 3040169) B3040169
theorem B7695445 : Blo 2025435 7695445 := bbase (se 8 (by rfl) ⟨45090, by rfl⟩ : syracuseStep 7695445 = 90181) (by norm_num)
theorem B10260593 : Blo 2025435 10260593 := bstep (se 2 (by rfl) ⟨3847722, by rfl⟩ : syracuseStep 10260593 = 7695445) B7695445
theorem B6840395 : Blo 2025435 6840395 := bstep (se 1 (by rfl) ⟨5130296, by rfl⟩ : syracuseStep 6840395 = 10260593) B10260593
theorem B4560263 : Blo 2025435 4560263 := bstep (se 1 (by rfl) ⟨3420197, by rfl⟩ : syracuseStep 4560263 = 6840395) B6840395
theorem B3040175 : Blo 2025435 3040175 := bstep (se 1 (by rfl) ⟨2280131, by rfl⟩ : syracuseStep 3040175 = 4560263) B4560263
theorem B2026783 : Blo 2025435 2026783 := bstep (se 1 (by rfl) ⟨1520087, by rfl⟩ : syracuseStep 2026783 = 3040175) B3040175
theorem B3040181 : Blo 2025435 3040181 := bbase (se 5 (by rfl) ⟨142508, by rfl⟩ : syracuseStep 3040181 = 285017) (by norm_num)
theorem B2026787 : Blo 2025435 2026787 := bstep (se 1 (by rfl) ⟨1520090, by rfl⟩ : syracuseStep 2026787 = 3040181) B3040181
theorem B5130317 : Blo 2025435 5130317 := bbase (se 3 (by rfl) ⟨961934, by rfl⟩ : syracuseStep 5130317 = 1923869) (by norm_num)
theorem B3420211 : Blo 2025435 3420211 := bstep (se 1 (by rfl) ⟨2565158, by rfl⟩ : syracuseStep 3420211 = 5130317) B5130317
theorem B4560281 : Blo 2025435 4560281 := bstep (se 2 (by rfl) ⟨1710105, by rfl⟩ : syracuseStep 4560281 = 3420211) B3420211
theorem B3040187 : Blo 2025435 3040187 := bstep (se 1 (by rfl) ⟨2280140, by rfl⟩ : syracuseStep 3040187 = 4560281) B4560281
theorem B2026791 : Blo 2025435 2026791 := bstep (se 1 (by rfl) ⟨1520093, by rfl⟩ : syracuseStep 2026791 = 3040187) B3040187
theorem B2280145 : Blo 2025435 2280145 := bbase (se 2 (by rfl) ⟨855054, by rfl⟩ : syracuseStep 2280145 = 1710109) (by norm_num)
theorem B3040193 : Blo 2025435 3040193 := bstep (se 2 (by rfl) ⟨1140072, by rfl⟩ : syracuseStep 3040193 = 2280145) B2280145
theorem B2026795 : Blo 2025435 2026795 := bstep (se 1 (by rfl) ⟨1520096, by rfl⟩ : syracuseStep 2026795 = 3040193) B3040193
theorem B3900253 : Blo 2025435 3900253 := bbase (se 3 (by rfl) ⟨731297, by rfl⟩ : syracuseStep 3900253 = 1462595) (by norm_num)
theorem B5200337 : Blo 2025435 5200337 := bstep (se 2 (by rfl) ⟨1950126, by rfl⟩ : syracuseStep 5200337 = 3900253) B3900253
theorem B3466891 : Blo 2025435 3466891 := bstep (se 1 (by rfl) ⟨2600168, by rfl⟩ : syracuseStep 3466891 = 5200337) B5200337
theorem B4622521 : Blo 2025435 4622521 := bstep (se 2 (by rfl) ⟨1733445, by rfl⟩ : syracuseStep 4622521 = 3466891) B3466891
theorem B6163361 : Blo 2025435 6163361 := bstep (se 2 (by rfl) ⟨2311260, by rfl⟩ : syracuseStep 6163361 = 4622521) B4622521
theorem B4108907 : Blo 2025435 4108907 := bstep (se 1 (by rfl) ⟨3081680, by rfl⟩ : syracuseStep 4108907 = 6163361) B6163361
theorem B2739271 : Blo 2025435 2739271 := bstep (se 1 (by rfl) ⟨2054453, by rfl⟩ : syracuseStep 2739271 = 4108907) B4108907
theorem B3652361 : Blo 2025435 3652361 := bstep (se 2 (by rfl) ⟨1369635, by rfl⟩ : syracuseStep 3652361 = 2739271) B2739271
theorem B2434907 : Blo 2025435 2434907 := bstep (se 1 (by rfl) ⟨1826180, by rfl⟩ : syracuseStep 2434907 = 3652361) B3652361
theorem B6493085 : Blo 2025435 6493085 := bstep (se 3 (by rfl) ⟨1217453, by rfl⟩ : syracuseStep 6493085 = 2434907) B2434907
theorem B4328723 : Blo 2025435 4328723 := bstep (se 1 (by rfl) ⟨3246542, by rfl⟩ : syracuseStep 4328723 = 6493085) B6493085
theorem B2885815 : Blo 2025435 2885815 := bstep (se 1 (by rfl) ⟨2164361, by rfl⟩ : syracuseStep 2885815 = 4328723) B4328723
theorem B3847753 : Blo 2025435 3847753 := bstep (se 2 (by rfl) ⟨1442907, by rfl⟩ : syracuseStep 3847753 = 2885815) B2885815
theorem B5130337 : Blo 2025435 5130337 := bstep (se 2 (by rfl) ⟨1923876, by rfl⟩ : syracuseStep 5130337 = 3847753) B3847753
theorem B6840449 : Blo 2025435 6840449 := bstep (se 2 (by rfl) ⟨2565168, by rfl⟩ : syracuseStep 6840449 = 5130337) B5130337
theorem B4560299 : Blo 2025435 4560299 := bstep (se 1 (by rfl) ⟨3420224, by rfl⟩ : syracuseStep 4560299 = 6840449) B6840449
theorem B3040199 : Blo 2025435 3040199 := bstep (se 1 (by rfl) ⟨2280149, by rfl⟩ : syracuseStep 3040199 = 4560299) B4560299
theorem B2026799 : Blo 2025435 2026799 := bstep (se 1 (by rfl) ⟨1520099, by rfl⟩ : syracuseStep 2026799 = 3040199) B3040199
theorem B3040205 : Blo 2025435 3040205 := bbase (se 3 (by rfl) ⟨570038, by rfl⟩ : syracuseStep 3040205 = 1140077) (by norm_num)
theorem B2026803 : Blo 2025435 2026803 := bstep (se 1 (by rfl) ⟨1520102, by rfl⟩ : syracuseStep 2026803 = 3040205) B3040205
theorem B4560317 : Blo 2025435 4560317 := bbase (se 3 (by rfl) ⟨855059, by rfl⟩ : syracuseStep 4560317 = 1710119) (by norm_num)
theorem B3040211 : Blo 2025435 3040211 := bstep (se 1 (by rfl) ⟨2280158, by rfl⟩ : syracuseStep 3040211 = 4560317) B4560317
theorem B2026807 : Blo 2025435 2026807 := bstep (se 1 (by rfl) ⟨1520105, by rfl⟩ : syracuseStep 2026807 = 3040211) B3040211
theorem B3420245 : Blo 2025435 3420245 := bbase (se 8 (by rfl) ⟨20040, by rfl⟩ : syracuseStep 3420245 = 40081) (by norm_num)
theorem B2280163 : Blo 2025435 2280163 := bstep (se 1 (by rfl) ⟨1710122, by rfl⟩ : syracuseStep 2280163 = 3420245) B3420245
theorem B3040217 : Blo 2025435 3040217 := bstep (se 2 (by rfl) ⟨1140081, by rfl⟩ : syracuseStep 3040217 = 2280163) B2280163
theorem B2026811 : Blo 2025435 2026811 := bstep (se 1 (by rfl) ⟨1520108, by rfl⟩ : syracuseStep 2026811 = 3040217) B3040217
theorem B28113749 : Blo 2025435 28113749 := bbase (se 9 (by rfl) ⟨82364, by rfl⟩ : syracuseStep 28113749 = 164729) (by norm_num)
theorem B18742499 : Blo 2025435 18742499 := bstep (se 1 (by rfl) ⟨14056874, by rfl⟩ : syracuseStep 18742499 = 28113749) B28113749
theorem B12494999 : Blo 2025435 12494999 := bstep (se 1 (by rfl) ⟨9371249, by rfl⟩ : syracuseStep 12494999 = 18742499) B18742499
theorem B8329999 : Blo 2025435 8329999 := bstep (se 1 (by rfl) ⟨6247499, by rfl⟩ : syracuseStep 8329999 = 12494999) B12494999
theorem B11106665 : Blo 2025435 11106665 := bstep (se 2 (by rfl) ⟨4164999, by rfl⟩ : syracuseStep 11106665 = 8329999) B8329999
theorem B7404443 : Blo 2025435 7404443 := bstep (se 1 (by rfl) ⟨5553332, by rfl⟩ : syracuseStep 7404443 = 11106665) B11106665
theorem B4936295 : Blo 2025435 4936295 := bstep (se 1 (by rfl) ⟨3702221, by rfl⟩ : syracuseStep 4936295 = 7404443) B7404443
theorem B3290863 : Blo 2025435 3290863 := bstep (se 1 (by rfl) ⟨2468147, by rfl⟩ : syracuseStep 3290863 = 4936295) B4936295
theorem B4387817 : Blo 2025435 4387817 := bstep (se 2 (by rfl) ⟨1645431, by rfl⟩ : syracuseStep 4387817 = 3290863) B3290863
theorem B11700845 : Blo 2025435 11700845 := bstep (se 3 (by rfl) ⟨2193908, by rfl⟩ : syracuseStep 11700845 = 4387817) B4387817
theorem B7800563 : Blo 2025435 7800563 := bstep (se 1 (by rfl) ⟨5850422, by rfl⟩ : syracuseStep 7800563 = 11700845) B11700845
theorem B5200375 : Blo 2025435 5200375 := bstep (se 1 (by rfl) ⟨3900281, by rfl⟩ : syracuseStep 5200375 = 7800563) B7800563
theorem B6933833 : Blo 2025435 6933833 := bstep (se 2 (by rfl) ⟨2600187, by rfl⟩ : syracuseStep 6933833 = 5200375) B5200375
theorem B4622555 : Blo 2025435 4622555 := bstep (se 1 (by rfl) ⟨3466916, by rfl⟩ : syracuseStep 4622555 = 6933833) B6933833
theorem B12326813 : Blo 2025435 12326813 := bstep (se 3 (by rfl) ⟨2311277, by rfl⟩ : syracuseStep 12326813 = 4622555) B4622555
theorem B8217875 : Blo 2025435 8217875 := bstep (se 1 (by rfl) ⟨6163406, by rfl⟩ : syracuseStep 8217875 = 12326813) B12326813
theorem B21914333 : Blo 2025435 21914333 := bstep (se 3 (by rfl) ⟨4108937, by rfl⟩ : syracuseStep 21914333 = 8217875) B8217875
theorem B14609555 : Blo 2025435 14609555 := bstep (se 1 (by rfl) ⟨10957166, by rfl⟩ : syracuseStep 14609555 = 21914333) B21914333
theorem B9739703 : Blo 2025435 9739703 := bstep (se 1 (by rfl) ⟨7304777, by rfl⟩ : syracuseStep 9739703 = 14609555) B14609555
theorem B6493135 : Blo 2025435 6493135 := bstep (se 1 (by rfl) ⟨4869851, by rfl⟩ : syracuseStep 6493135 = 9739703) B9739703
theorem B8657513 : Blo 2025435 8657513 := bstep (se 2 (by rfl) ⟨3246567, by rfl⟩ : syracuseStep 8657513 = 6493135) B6493135
theorem B5771675 : Blo 2025435 5771675 := bstep (se 1 (by rfl) ⟨4328756, by rfl⟩ : syracuseStep 5771675 = 8657513) B8657513
theorem B15391133 : Blo 2025435 15391133 := bstep (se 3 (by rfl) ⟨2885837, by rfl⟩ : syracuseStep 15391133 = 5771675) B5771675
theorem B10260755 : Blo 2025435 10260755 := bstep (se 1 (by rfl) ⟨7695566, by rfl⟩ : syracuseStep 10260755 = 15391133) B15391133
theorem B6840503 : Blo 2025435 6840503 := bstep (se 1 (by rfl) ⟨5130377, by rfl⟩ : syracuseStep 6840503 = 10260755) B10260755
theorem B4560335 : Blo 2025435 4560335 := bstep (se 1 (by rfl) ⟨3420251, by rfl⟩ : syracuseStep 4560335 = 6840503) B6840503
theorem B3040223 : Blo 2025435 3040223 := bstep (se 1 (by rfl) ⟨2280167, by rfl⟩ : syracuseStep 3040223 = 4560335) B4560335
theorem B2026815 : Blo 2025435 2026815 := bstep (se 1 (by rfl) ⟨1520111, by rfl⟩ : syracuseStep 2026815 = 3040223) B3040223
theorem B3040229 : Blo 2025435 3040229 := bbase (se 4 (by rfl) ⟨285021, by rfl⟩ : syracuseStep 3040229 = 570043) (by norm_num)
theorem B2026819 : Blo 2025435 2026819 := bstep (se 1 (by rfl) ⟨1520114, by rfl⟩ : syracuseStep 2026819 = 3040229) B3040229
theorem B3246581 : Blo 2025435 3246581 := bbase (se 5 (by rfl) ⟨152183, by rfl⟩ : syracuseStep 3246581 = 304367) (by norm_num)
theorem B8657549 : Blo 2025435 8657549 := bstep (se 3 (by rfl) ⟨1623290, by rfl⟩ : syracuseStep 8657549 = 3246581) B3246581
theorem B5771699 : Blo 2025435 5771699 := bstep (se 1 (by rfl) ⟨4328774, by rfl⟩ : syracuseStep 5771699 = 8657549) B8657549
theorem B3847799 : Blo 2025435 3847799 := bstep (se 1 (by rfl) ⟨2885849, by rfl⟩ : syracuseStep 3847799 = 5771699) B5771699
theorem B2565199 : Blo 2025435 2565199 := bstep (se 1 (by rfl) ⟨1923899, by rfl⟩ : syracuseStep 2565199 = 3847799) B3847799
theorem B3420265 : Blo 2025435 3420265 := bstep (se 2 (by rfl) ⟨1282599, by rfl⟩ : syracuseStep 3420265 = 2565199) B2565199
theorem B4560353 : Blo 2025435 4560353 := bstep (se 2 (by rfl) ⟨1710132, by rfl⟩ : syracuseStep 4560353 = 3420265) B3420265
theorem B3040235 : Blo 2025435 3040235 := bstep (se 1 (by rfl) ⟨2280176, by rfl⟩ : syracuseStep 3040235 = 4560353) B4560353
theorem B2026823 : Blo 2025435 2026823 := bstep (se 1 (by rfl) ⟨1520117, by rfl⟩ : syracuseStep 2026823 = 3040235) B3040235
theorem B2280181 : Blo 2025435 2280181 := bbase (se 5 (by rfl) ⟨106883, by rfl⟩ : syracuseStep 2280181 = 213767) (by norm_num)
theorem B3040241 : Blo 2025435 3040241 := bstep (se 2 (by rfl) ⟨1140090, by rfl⟩ : syracuseStep 3040241 = 2280181) B2280181
theorem B2026827 : Blo 2025435 2026827 := bstep (se 1 (by rfl) ⟨1520120, by rfl⟩ : syracuseStep 2026827 = 3040241) B3040241
theorem B2565209 : Blo 2025435 2565209 := bbase (se 2 (by rfl) ⟨961953, by rfl⟩ : syracuseStep 2565209 = 1923907) (by norm_num)
theorem B6840557 : Blo 2025435 6840557 := bstep (se 3 (by rfl) ⟨1282604, by rfl⟩ : syracuseStep 6840557 = 2565209) B2565209
theorem B4560371 : Blo 2025435 4560371 := bstep (se 1 (by rfl) ⟨3420278, by rfl⟩ : syracuseStep 4560371 = 6840557) B6840557
theorem B3040247 : Blo 2025435 3040247 := bstep (se 1 (by rfl) ⟨2280185, by rfl⟩ : syracuseStep 3040247 = 4560371) B4560371
theorem B2026831 : Blo 2025435 2026831 := bstep (se 1 (by rfl) ⟨1520123, by rfl⟩ : syracuseStep 2026831 = 3040247) B3040247
theorem B3040253 : Blo 2025435 3040253 := bbase (se 3 (by rfl) ⟨570047, by rfl⟩ : syracuseStep 3040253 = 1140095) (by norm_num)
theorem B2026835 : Blo 2025435 2026835 := bstep (se 1 (by rfl) ⟨1520126, by rfl⟩ : syracuseStep 2026835 = 3040253) B3040253
theorem B4560389 : Blo 2025435 4560389 := bbase (se 4 (by rfl) ⟨427536, by rfl⟩ : syracuseStep 4560389 = 855073) (by norm_num)
theorem B3040259 : Blo 2025435 3040259 := bstep (se 1 (by rfl) ⟨2280194, by rfl⟩ : syracuseStep 3040259 = 4560389) B4560389
theorem B2026839 : Blo 2025435 2026839 := bstep (se 1 (by rfl) ⟨1520129, by rfl⟩ : syracuseStep 2026839 = 3040259) B3040259
theorem B3847837 : Blo 2025435 3847837 := bbase (se 3 (by rfl) ⟨721469, by rfl⟩ : syracuseStep 3847837 = 1442939) (by norm_num)
theorem B5130449 : Blo 2025435 5130449 := bstep (se 2 (by rfl) ⟨1923918, by rfl⟩ : syracuseStep 5130449 = 3847837) B3847837
theorem B3420299 : Blo 2025435 3420299 := bstep (se 1 (by rfl) ⟨2565224, by rfl⟩ : syracuseStep 3420299 = 5130449) B5130449
theorem B2280199 : Blo 2025435 2280199 := bstep (se 1 (by rfl) ⟨1710149, by rfl⟩ : syracuseStep 2280199 = 3420299) B3420299
theorem B3040265 : Blo 2025435 3040265 := bstep (se 2 (by rfl) ⟨1140099, by rfl⟩ : syracuseStep 3040265 = 2280199) B2280199
theorem B2026843 : Blo 2025435 2026843 := bstep (se 1 (by rfl) ⟨1520132, by rfl⟩ : syracuseStep 2026843 = 3040265) B3040265
theorem B10260917 : Blo 2025435 10260917 := bbase (se 5 (by rfl) ⟨480980, by rfl⟩ : syracuseStep 10260917 = 961961) (by norm_num)
theorem B6840611 : Blo 2025435 6840611 := bstep (se 1 (by rfl) ⟨5130458, by rfl⟩ : syracuseStep 6840611 = 10260917) B10260917
theorem B4560407 : Blo 2025435 4560407 := bstep (se 1 (by rfl) ⟨3420305, by rfl⟩ : syracuseStep 4560407 = 6840611) B6840611
theorem B3040271 : Blo 2025435 3040271 := bstep (se 1 (by rfl) ⟨2280203, by rfl⟩ : syracuseStep 3040271 = 4560407) B4560407
theorem B2026847 : Blo 2025435 2026847 := bstep (se 1 (by rfl) ⟨1520135, by rfl⟩ : syracuseStep 2026847 = 3040271) B3040271
theorem B3040277 : Blo 2025435 3040277 := bbase (se 6 (by rfl) ⟨71256, by rfl⟩ : syracuseStep 3040277 = 142513) (by norm_num)
theorem B2026851 : Blo 2025435 2026851 := bstep (se 1 (by rfl) ⟨1520138, by rfl⟩ : syracuseStep 2026851 = 3040277) B3040277
theorem B21085717 : Blo 2025435 21085717 := bbase (se 6 (by rfl) ⟨494196, by rfl⟩ : syracuseStep 21085717 = 988393) (by norm_num)
theorem B28114289 : Blo 2025435 28114289 := bstep (se 2 (by rfl) ⟨10542858, by rfl⟩ : syracuseStep 28114289 = 21085717) B21085717
theorem B18742859 : Blo 2025435 18742859 := bstep (se 1 (by rfl) ⟨14057144, by rfl⟩ : syracuseStep 18742859 = 28114289) B28114289
theorem B12495239 : Blo 2025435 12495239 := bstep (se 1 (by rfl) ⟨9371429, by rfl⟩ : syracuseStep 12495239 = 18742859) B18742859
theorem B8330159 : Blo 2025435 8330159 := bstep (se 1 (by rfl) ⟨6247619, by rfl⟩ : syracuseStep 8330159 = 12495239) B12495239
theorem B22213757 : Blo 2025435 22213757 := bstep (se 3 (by rfl) ⟨4165079, by rfl⟩ : syracuseStep 22213757 = 8330159) B8330159
theorem B14809171 : Blo 2025435 14809171 := bstep (se 1 (by rfl) ⟨11106878, by rfl⟩ : syracuseStep 14809171 = 22213757) B22213757
theorem B19745561 : Blo 2025435 19745561 := bstep (se 2 (by rfl) ⟨7404585, by rfl⟩ : syracuseStep 19745561 = 14809171) B14809171
theorem B13163707 : Blo 2025435 13163707 := bstep (se 1 (by rfl) ⟨9872780, by rfl⟩ : syracuseStep 13163707 = 19745561) B19745561
theorem B17551609 : Blo 2025435 17551609 := bstep (se 2 (by rfl) ⟨6581853, by rfl⟩ : syracuseStep 17551609 = 13163707) B13163707
theorem B374434325 : Blo 2025435 374434325 := bstep (se 6 (by rfl) ⟨8775804, by rfl⟩ : syracuseStep 374434325 = 17551609) B17551609
theorem B249622883 : Blo 2025435 249622883 := bstep (se 1 (by rfl) ⟨187217162, by rfl⟩ : syracuseStep 249622883 = 374434325) B374434325
theorem B166415255 : Blo 2025435 166415255 := bstep (se 1 (by rfl) ⟨124811441, by rfl⟩ : syracuseStep 166415255 = 249622883) B249622883
theorem B110943503 : Blo 2025435 110943503 := bstep (se 1 (by rfl) ⟨83207627, by rfl⟩ : syracuseStep 110943503 = 166415255) B166415255
theorem B73962335 : Blo 2025435 73962335 := bstep (se 1 (by rfl) ⟨55471751, by rfl⟩ : syracuseStep 73962335 = 110943503) B110943503
theorem B49308223 : Blo 2025435 49308223 := bstep (se 1 (by rfl) ⟨36981167, by rfl⟩ : syracuseStep 49308223 = 73962335) B73962335
theorem B65744297 : Blo 2025435 65744297 := bstep (se 2 (by rfl) ⟨24654111, by rfl⟩ : syracuseStep 65744297 = 49308223) B49308223
theorem B43829531 : Blo 2025435 43829531 := bstep (se 1 (by rfl) ⟨32872148, by rfl⟩ : syracuseStep 43829531 = 65744297) B65744297
theorem B29219687 : Blo 2025435 29219687 := bstep (se 1 (by rfl) ⟨21914765, by rfl⟩ : syracuseStep 29219687 = 43829531) B43829531
theorem B19479791 : Blo 2025435 19479791 := bstep (se 1 (by rfl) ⟨14609843, by rfl⟩ : syracuseStep 19479791 = 29219687) B29219687
theorem B12986527 : Blo 2025435 12986527 := bstep (se 1 (by rfl) ⟨9739895, by rfl⟩ : syracuseStep 12986527 = 19479791) B19479791
theorem B17315369 : Blo 2025435 17315369 := bstep (se 2 (by rfl) ⟨6493263, by rfl⟩ : syracuseStep 17315369 = 12986527) B12986527
theorem B11543579 : Blo 2025435 11543579 := bstep (se 1 (by rfl) ⟨8657684, by rfl⟩ : syracuseStep 11543579 = 17315369) B17315369
theorem B7695719 : Blo 2025435 7695719 := bstep (se 1 (by rfl) ⟨5771789, by rfl⟩ : syracuseStep 7695719 = 11543579) B11543579
theorem B5130479 : Blo 2025435 5130479 := bstep (se 1 (by rfl) ⟨3847859, by rfl⟩ : syracuseStep 5130479 = 7695719) B7695719
theorem B3420319 : Blo 2025435 3420319 := bstep (se 1 (by rfl) ⟨2565239, by rfl⟩ : syracuseStep 3420319 = 5130479) B5130479
theorem B4560425 : Blo 2025435 4560425 := bstep (se 2 (by rfl) ⟨1710159, by rfl⟩ : syracuseStep 4560425 = 3420319) B3420319
theorem B3040283 : Blo 2025435 3040283 := bstep (se 1 (by rfl) ⟨2280212, by rfl⟩ : syracuseStep 3040283 = 4560425) B4560425
theorem B2026855 : Blo 2025435 2026855 := bstep (se 1 (by rfl) ⟨1520141, by rfl⟩ : syracuseStep 2026855 = 3040283) B3040283
theorem B2280217 : Blo 2025435 2280217 := bbase (se 2 (by rfl) ⟨855081, by rfl⟩ : syracuseStep 2280217 = 1710163) (by norm_num)
theorem B3040289 : Blo 2025435 3040289 := bstep (se 2 (by rfl) ⟨1140108, by rfl⟩ : syracuseStep 3040289 = 2280217) B2280217
theorem B2026859 : Blo 2025435 2026859 := bstep (se 1 (by rfl) ⟨1520144, by rfl⟩ : syracuseStep 2026859 = 3040289) B3040289
theorem B7695749 : Blo 2025435 7695749 := bbase (se 4 (by rfl) ⟨721476, by rfl⟩ : syracuseStep 7695749 = 1442953) (by norm_num)
theorem B5130499 : Blo 2025435 5130499 := bstep (se 1 (by rfl) ⟨3847874, by rfl⟩ : syracuseStep 5130499 = 7695749) B7695749
theorem B6840665 : Blo 2025435 6840665 := bstep (se 2 (by rfl) ⟨2565249, by rfl⟩ : syracuseStep 6840665 = 5130499) B5130499
theorem B4560443 : Blo 2025435 4560443 := bstep (se 1 (by rfl) ⟨3420332, by rfl⟩ : syracuseStep 4560443 = 6840665) B6840665
theorem B3040295 : Blo 2025435 3040295 := bstep (se 1 (by rfl) ⟨2280221, by rfl⟩ : syracuseStep 3040295 = 4560443) B4560443
theorem B2026863 : Blo 2025435 2026863 := bstep (se 1 (by rfl) ⟨1520147, by rfl⟩ : syracuseStep 2026863 = 3040295) B3040295
theorem B3040301 : Blo 2025435 3040301 := bbase (se 3 (by rfl) ⟨570056, by rfl⟩ : syracuseStep 3040301 = 1140113) (by norm_num)
theorem B2026867 : Blo 2025435 2026867 := bstep (se 1 (by rfl) ⟨1520150, by rfl⟩ : syracuseStep 2026867 = 3040301) B3040301
theorem B4560461 : Blo 2025435 4560461 := bbase (se 3 (by rfl) ⟨855086, by rfl⟩ : syracuseStep 4560461 = 1710173) (by norm_num)
theorem B3040307 : Blo 2025435 3040307 := bstep (se 1 (by rfl) ⟨2280230, by rfl⟩ : syracuseStep 3040307 = 4560461) B4560461
theorem B2026871 : Blo 2025435 2026871 := bstep (se 1 (by rfl) ⟨1520153, by rfl⟩ : syracuseStep 2026871 = 3040307) B3040307
theorem B2565265 : Blo 2025435 2565265 := bbase (se 2 (by rfl) ⟨961974, by rfl⟩ : syracuseStep 2565265 = 1923949) (by norm_num)
theorem B3420353 : Blo 2025435 3420353 := bstep (se 2 (by rfl) ⟨1282632, by rfl⟩ : syracuseStep 3420353 = 2565265) B2565265
theorem B2280235 : Blo 2025435 2280235 := bstep (se 1 (by rfl) ⟨1710176, by rfl⟩ : syracuseStep 2280235 = 3420353) B3420353
theorem B3040313 : Blo 2025435 3040313 := bstep (se 2 (by rfl) ⟨1140117, by rfl⟩ : syracuseStep 3040313 = 2280235) B2280235
theorem B2026875 : Blo 2025435 2026875 := bstep (se 1 (by rfl) ⟨1520156, by rfl⟩ : syracuseStep 2026875 = 3040313) B3040313
theorem B4328893 : Blo 2025435 4328893 := bbase (se 3 (by rfl) ⟨811667, by rfl⟩ : syracuseStep 4328893 = 1623335) (by norm_num)
theorem B23087429 : Blo 2025435 23087429 := bstep (se 4 (by rfl) ⟨2164446, by rfl⟩ : syracuseStep 23087429 = 4328893) B4328893
theorem B15391619 : Blo 2025435 15391619 := bstep (se 1 (by rfl) ⟨11543714, by rfl⟩ : syracuseStep 15391619 = 23087429) B23087429
theorem B10261079 : Blo 2025435 10261079 := bstep (se 1 (by rfl) ⟨7695809, by rfl⟩ : syracuseStep 10261079 = 15391619) B15391619
theorem B6840719 : Blo 2025435 6840719 := bstep (se 1 (by rfl) ⟨5130539, by rfl⟩ : syracuseStep 6840719 = 10261079) B10261079
theorem B4560479 : Blo 2025435 4560479 := bstep (se 1 (by rfl) ⟨3420359, by rfl⟩ : syracuseStep 4560479 = 6840719) B6840719
theorem B3040319 : Blo 2025435 3040319 := bstep (se 1 (by rfl) ⟨2280239, by rfl⟩ : syracuseStep 3040319 = 4560479) B4560479
theorem B2026879 : Blo 2025435 2026879 := bstep (se 1 (by rfl) ⟨1520159, by rfl⟩ : syracuseStep 2026879 = 3040319) B3040319
theorem B3040325 : Blo 2025435 3040325 := bbase (se 4 (by rfl) ⟨285030, by rfl⟩ : syracuseStep 3040325 = 570061) (by norm_num)
theorem B2026883 : Blo 2025435 2026883 := bstep (se 1 (by rfl) ⟨1520162, by rfl⟩ : syracuseStep 2026883 = 3040325) B3040325
theorem B3420373 : Blo 2025435 3420373 := bbase (se 7 (by rfl) ⟨40082, by rfl⟩ : syracuseStep 3420373 = 80165) (by norm_num)
theorem B4560497 : Blo 2025435 4560497 := bstep (se 2 (by rfl) ⟨1710186, by rfl⟩ : syracuseStep 4560497 = 3420373) B3420373
theorem B3040331 : Blo 2025435 3040331 := bstep (se 1 (by rfl) ⟨2280248, by rfl⟩ : syracuseStep 3040331 = 4560497) B4560497
theorem B2026887 : Blo 2025435 2026887 := bstep (se 1 (by rfl) ⟨1520165, by rfl⟩ : syracuseStep 2026887 = 3040331) B3040331
theorem B2280253 : Blo 2025435 2280253 := bbase (se 3 (by rfl) ⟨427547, by rfl⟩ : syracuseStep 2280253 = 855095) (by norm_num)
theorem B3040337 : Blo 2025435 3040337 := bstep (se 2 (by rfl) ⟨1140126, by rfl⟩ : syracuseStep 3040337 = 2280253) B2280253
theorem B2026891 : Blo 2025435 2026891 := bstep (se 1 (by rfl) ⟨1520168, by rfl⟩ : syracuseStep 2026891 = 3040337) B3040337
theorem B6840773 : Blo 2025435 6840773 := bbase (se 4 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 6840773 = 1282645) (by norm_num)
theorem B4560515 : Blo 2025435 4560515 := bstep (se 1 (by rfl) ⟨3420386, by rfl⟩ : syracuseStep 4560515 = 6840773) B6840773
theorem B3040343 : Blo 2025435 3040343 := bstep (se 1 (by rfl) ⟨2280257, by rfl⟩ : syracuseStep 3040343 = 4560515) B4560515
theorem B2026895 : Blo 2025435 2026895 := bstep (se 1 (by rfl) ⟨1520171, by rfl⟩ : syracuseStep 2026895 = 3040343) B3040343
theorem B3040349 : Blo 2025435 3040349 := bbase (se 3 (by rfl) ⟨570065, by rfl⟩ : syracuseStep 3040349 = 1140131) (by norm_num)
theorem B2026899 : Blo 2025435 2026899 := bstep (se 1 (by rfl) ⟨1520174, by rfl⟩ : syracuseStep 2026899 = 3040349) B3040349
theorem B4560533 : Blo 2025435 4560533 := bbase (se 6 (by rfl) ⟨106887, by rfl⟩ : syracuseStep 4560533 = 213775) (by norm_num)
theorem B3040355 : Blo 2025435 3040355 := bstep (se 1 (by rfl) ⟨2280266, by rfl⟩ : syracuseStep 3040355 = 4560533) B4560533
theorem B2026903 : Blo 2025435 2026903 := bstep (se 1 (by rfl) ⟨1520177, by rfl⟩ : syracuseStep 2026903 = 3040355) B3040355
theorem B2164477 : Blo 2025435 2164477 := bbase (se 3 (by rfl) ⟨405839, by rfl⟩ : syracuseStep 2164477 = 811679) (by norm_num)
theorem B2885969 : Blo 2025435 2885969 := bstep (se 2 (by rfl) ⟨1082238, by rfl⟩ : syracuseStep 2885969 = 2164477) B2164477
theorem B7695917 : Blo 2025435 7695917 := bstep (se 3 (by rfl) ⟨1442984, by rfl⟩ : syracuseStep 7695917 = 2885969) B2885969
theorem B5130611 : Blo 2025435 5130611 := bstep (se 1 (by rfl) ⟨3847958, by rfl⟩ : syracuseStep 5130611 = 7695917) B7695917
theorem B3420407 : Blo 2025435 3420407 := bstep (se 1 (by rfl) ⟨2565305, by rfl⟩ : syracuseStep 3420407 = 5130611) B5130611
theorem B2280271 : Blo 2025435 2280271 := bstep (se 1 (by rfl) ⟨1710203, by rfl⟩ : syracuseStep 2280271 = 3420407) B3420407
theorem B3040361 : Blo 2025435 3040361 := bstep (se 2 (by rfl) ⟨1140135, by rfl⟩ : syracuseStep 3040361 = 2280271) B2280271
theorem B2026907 : Blo 2025435 2026907 := bstep (se 1 (by rfl) ⟨1520180, by rfl⟩ : syracuseStep 2026907 = 3040361) B3040361
theorem B2435041 : Blo 2025435 2435041 := bbase (se 2 (by rfl) ⟨913140, by rfl⟩ : syracuseStep 2435041 = 1826281) (by norm_num)
theorem B12986885 : Blo 2025435 12986885 := bstep (se 4 (by rfl) ⟨1217520, by rfl⟩ : syracuseStep 12986885 = 2435041) B2435041
theorem B8657923 : Blo 2025435 8657923 := bstep (se 1 (by rfl) ⟨6493442, by rfl⟩ : syracuseStep 8657923 = 12986885) B12986885
theorem B11543897 : Blo 2025435 11543897 := bstep (se 2 (by rfl) ⟨4328961, by rfl⟩ : syracuseStep 11543897 = 8657923) B8657923
theorem B7695931 : Blo 2025435 7695931 := bstep (se 1 (by rfl) ⟨5771948, by rfl⟩ : syracuseStep 7695931 = 11543897) B11543897
theorem B10261241 : Blo 2025435 10261241 := bstep (se 2 (by rfl) ⟨3847965, by rfl⟩ : syracuseStep 10261241 = 7695931) B7695931
theorem B6840827 : Blo 2025435 6840827 := bstep (se 1 (by rfl) ⟨5130620, by rfl⟩ : syracuseStep 6840827 = 10261241) B10261241
theorem B4560551 : Blo 2025435 4560551 := bstep (se 1 (by rfl) ⟨3420413, by rfl⟩ : syracuseStep 4560551 = 6840827) B6840827
theorem B3040367 : Blo 2025435 3040367 := bstep (se 1 (by rfl) ⟨2280275, by rfl⟩ : syracuseStep 3040367 = 4560551) B4560551
theorem B2026911 : Blo 2025435 2026911 := bstep (se 1 (by rfl) ⟨1520183, by rfl⟩ : syracuseStep 2026911 = 3040367) B3040367
theorem B3040373 : Blo 2025435 3040373 := bbase (se 5 (by rfl) ⟨142517, by rfl⟩ : syracuseStep 3040373 = 285035) (by norm_num)
theorem B2026915 : Blo 2025435 2026915 := bstep (se 1 (by rfl) ⟨1520186, by rfl⟩ : syracuseStep 2026915 = 3040373) B3040373
theorem B3847981 : Blo 2025435 3847981 := bbase (se 3 (by rfl) ⟨721496, by rfl⟩ : syracuseStep 3847981 = 1442993) (by norm_num)
theorem B5130641 : Blo 2025435 5130641 := bstep (se 2 (by rfl) ⟨1923990, by rfl⟩ : syracuseStep 5130641 = 3847981) B3847981
theorem B3420427 : Blo 2025435 3420427 := bstep (se 1 (by rfl) ⟨2565320, by rfl⟩ : syracuseStep 3420427 = 5130641) B5130641
theorem B4560569 : Blo 2025435 4560569 := bstep (se 2 (by rfl) ⟨1710213, by rfl⟩ : syracuseStep 4560569 = 3420427) B3420427
theorem B3040379 : Blo 2025435 3040379 := bstep (se 1 (by rfl) ⟨2280284, by rfl⟩ : syracuseStep 3040379 = 4560569) B4560569
theorem B2026919 : Blo 2025435 2026919 := bstep (se 1 (by rfl) ⟨1520189, by rfl⟩ : syracuseStep 2026919 = 3040379) B3040379
theorem B2280289 : Blo 2025435 2280289 := bbase (se 2 (by rfl) ⟨855108, by rfl⟩ : syracuseStep 2280289 = 1710217) (by norm_num)
theorem B3040385 : Blo 2025435 3040385 := bstep (se 2 (by rfl) ⟨1140144, by rfl⟩ : syracuseStep 3040385 = 2280289) B2280289
theorem B2026923 : Blo 2025435 2026923 := bstep (se 1 (by rfl) ⟨1520192, by rfl⟩ : syracuseStep 2026923 = 3040385) B3040385
theorem B5130661 : Blo 2025435 5130661 := bbase (se 4 (by rfl) ⟨480999, by rfl⟩ : syracuseStep 5130661 = 961999) (by norm_num)
theorem B6840881 : Blo 2025435 6840881 := bstep (se 2 (by rfl) ⟨2565330, by rfl⟩ : syracuseStep 6840881 = 5130661) B5130661
theorem B4560587 : Blo 2025435 4560587 := bstep (se 1 (by rfl) ⟨3420440, by rfl⟩ : syracuseStep 4560587 = 6840881) B6840881
theorem B3040391 : Blo 2025435 3040391 := bstep (se 1 (by rfl) ⟨2280293, by rfl⟩ : syracuseStep 3040391 = 4560587) B4560587
theorem B2026927 : Blo 2025435 2026927 := bstep (se 1 (by rfl) ⟨1520195, by rfl⟩ : syracuseStep 2026927 = 3040391) B3040391
theorem B3040397 : Blo 2025435 3040397 := bbase (se 3 (by rfl) ⟨570074, by rfl⟩ : syracuseStep 3040397 = 1140149) (by norm_num)
theorem B2026931 : Blo 2025435 2026931 := bstep (se 1 (by rfl) ⟨1520198, by rfl⟩ : syracuseStep 2026931 = 3040397) B3040397
theorem B4560605 : Blo 2025435 4560605 := bbase (se 3 (by rfl) ⟨855113, by rfl⟩ : syracuseStep 4560605 = 1710227) (by norm_num)
theorem B3040403 : Blo 2025435 3040403 := bstep (se 1 (by rfl) ⟨2280302, by rfl⟩ : syracuseStep 3040403 = 4560605) B4560605
theorem B2026935 : Blo 2025435 2026935 := bstep (se 1 (by rfl) ⟨1520201, by rfl⟩ : syracuseStep 2026935 = 3040403) B3040403
theorem B3420461 : Blo 2025435 3420461 := bbase (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) (by norm_num)
theorem B2280307 : Blo 2025435 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B3040409 : Blo 2025435 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B2026939 : Blo 2025435 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B4109197 : Blo 2025435 4109197 := bbase (se 3 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 4109197 = 1540949) (by norm_num)
theorem B5478929 : Blo 2025435 5478929 := bstep (se 2 (by rfl) ⟨2054598, by rfl⟩ : syracuseStep 5478929 = 4109197) B4109197
theorem B3652619 : Blo 2025435 3652619 := bstep (se 1 (by rfl) ⟨2739464, by rfl⟩ : syracuseStep 3652619 = 5478929) B5478929
theorem B38961269 : Blo 2025435 38961269 := bstep (se 5 (by rfl) ⟨1826309, by rfl⟩ : syracuseStep 38961269 = 3652619) B3652619
theorem B25974179 : Blo 2025435 25974179 := bstep (se 1 (by rfl) ⟨19480634, by rfl⟩ : syracuseStep 25974179 = 38961269) B38961269
theorem B17316119 : Blo 2025435 17316119 := bstep (se 1 (by rfl) ⟨12987089, by rfl⟩ : syracuseStep 17316119 = 25974179) B25974179
theorem B11544079 : Blo 2025435 11544079 := bstep (se 1 (by rfl) ⟨8658059, by rfl⟩ : syracuseStep 11544079 = 17316119) B17316119
theorem B15392105 : Blo 2025435 15392105 := bstep (se 2 (by rfl) ⟨5772039, by rfl⟩ : syracuseStep 15392105 = 11544079) B11544079
theorem B10261403 : Blo 2025435 10261403 := bstep (se 1 (by rfl) ⟨7696052, by rfl⟩ : syracuseStep 10261403 = 15392105) B15392105
theorem B6840935 : Blo 2025435 6840935 := bstep (se 1 (by rfl) ⟨5130701, by rfl⟩ : syracuseStep 6840935 = 10261403) B10261403
theorem B4560623 : Blo 2025435 4560623 := bstep (se 1 (by rfl) ⟨3420467, by rfl⟩ : syracuseStep 4560623 = 6840935) B6840935
theorem B3040415 : Blo 2025435 3040415 := bstep (se 1 (by rfl) ⟨2280311, by rfl⟩ : syracuseStep 3040415 = 4560623) B4560623
theorem B2026943 : Blo 2025435 2026943 := bstep (se 1 (by rfl) ⟨1520207, by rfl⟩ : syracuseStep 2026943 = 3040415) B3040415
theorem B3040421 : Blo 2025435 3040421 := bbase (se 4 (by rfl) ⟨285039, by rfl⟩ : syracuseStep 3040421 = 570079) (by norm_num)
theorem B2026947 : Blo 2025435 2026947 := bstep (se 1 (by rfl) ⟨1520210, by rfl⟩ : syracuseStep 2026947 = 3040421) B3040421
theorem B2565361 : Blo 2025435 2565361 := bbase (se 2 (by rfl) ⟨962010, by rfl⟩ : syracuseStep 2565361 = 1924021) (by norm_num)
theorem B3420481 : Blo 2025435 3420481 := bstep (se 2 (by rfl) ⟨1282680, by rfl⟩ : syracuseStep 3420481 = 2565361) B2565361
theorem B4560641 : Blo 2025435 4560641 := bstep (se 2 (by rfl) ⟨1710240, by rfl⟩ : syracuseStep 4560641 = 3420481) B3420481
theorem B3040427 : Blo 2025435 3040427 := bstep (se 1 (by rfl) ⟨2280320, by rfl⟩ : syracuseStep 3040427 = 4560641) B4560641
theorem B2026951 : Blo 2025435 2026951 := bstep (se 1 (by rfl) ⟨1520213, by rfl⟩ : syracuseStep 2026951 = 3040427) B3040427
theorem B2280325 : Blo 2025435 2280325 := bbase (se 4 (by rfl) ⟨213780, by rfl⟩ : syracuseStep 2280325 = 427561) (by norm_num)
theorem B3040433 : Blo 2025435 3040433 := bstep (se 2 (by rfl) ⟨1140162, by rfl⟩ : syracuseStep 3040433 = 2280325) B2280325
theorem B2026955 : Blo 2025435 2026955 := bstep (se 1 (by rfl) ⟨1520216, by rfl⟩ : syracuseStep 2026955 = 3040433) B3040433
theorem B10401493 : Blo 2025435 10401493 := bbase (se 7 (by rfl) ⟨121892, by rfl⟩ : syracuseStep 10401493 = 243785) (by norm_num)
theorem B13868657 : Blo 2025435 13868657 := bstep (se 2 (by rfl) ⟨5200746, by rfl⟩ : syracuseStep 13868657 = 10401493) B10401493
theorem B9245771 : Blo 2025435 9245771 := bstep (se 1 (by rfl) ⟨6934328, by rfl⟩ : syracuseStep 9245771 = 13868657) B13868657
theorem B6163847 : Blo 2025435 6163847 := bstep (se 1 (by rfl) ⟨4622885, by rfl⟩ : syracuseStep 6163847 = 9245771) B9245771
theorem B4109231 : Blo 2025435 4109231 := bstep (se 1 (by rfl) ⟨3081923, by rfl⟩ : syracuseStep 4109231 = 6163847) B6163847
theorem B10957949 : Blo 2025435 10957949 := bstep (se 3 (by rfl) ⟨2054615, by rfl⟩ : syracuseStep 10957949 = 4109231) B4109231
theorem B7305299 : Blo 2025435 7305299 := bstep (se 1 (by rfl) ⟨5478974, by rfl⟩ : syracuseStep 7305299 = 10957949) B10957949
theorem B4870199 : Blo 2025435 4870199 := bstep (se 1 (by rfl) ⟨3652649, by rfl⟩ : syracuseStep 4870199 = 7305299) B7305299
theorem B3246799 : Blo 2025435 3246799 := bstep (se 1 (by rfl) ⟨2435099, by rfl⟩ : syracuseStep 3246799 = 4870199) B4870199
theorem B4329065 : Blo 2025435 4329065 := bstep (se 2 (by rfl) ⟨1623399, by rfl⟩ : syracuseStep 4329065 = 3246799) B3246799
theorem B2886043 : Blo 2025435 2886043 := bstep (se 1 (by rfl) ⟨2164532, by rfl⟩ : syracuseStep 2886043 = 4329065) B4329065
theorem B3848057 : Blo 2025435 3848057 := bstep (se 2 (by rfl) ⟨1443021, by rfl⟩ : syracuseStep 3848057 = 2886043) B2886043
theorem B2565371 : Blo 2025435 2565371 := bstep (se 1 (by rfl) ⟨1924028, by rfl⟩ : syracuseStep 2565371 = 3848057) B3848057
theorem B6840989 : Blo 2025435 6840989 := bstep (se 3 (by rfl) ⟨1282685, by rfl⟩ : syracuseStep 6840989 = 2565371) B2565371
theorem B4560659 : Blo 2025435 4560659 := bstep (se 1 (by rfl) ⟨3420494, by rfl⟩ : syracuseStep 4560659 = 6840989) B6840989
theorem B3040439 : Blo 2025435 3040439 := bstep (se 1 (by rfl) ⟨2280329, by rfl⟩ : syracuseStep 3040439 = 4560659) B4560659
theorem B2026959 : Blo 2025435 2026959 := bstep (se 1 (by rfl) ⟨1520219, by rfl⟩ : syracuseStep 2026959 = 3040439) B3040439
theorem B3040445 : Blo 2025435 3040445 := bbase (se 3 (by rfl) ⟨570083, by rfl⟩ : syracuseStep 3040445 = 1140167) (by norm_num)
theorem B2026963 : Blo 2025435 2026963 := bstep (se 1 (by rfl) ⟨1520222, by rfl⟩ : syracuseStep 2026963 = 3040445) B3040445
theorem B4560677 : Blo 2025435 4560677 := bbase (se 4 (by rfl) ⟨427563, by rfl⟩ : syracuseStep 4560677 = 855127) (by norm_num)
theorem B3040451 : Blo 2025435 3040451 := bstep (se 1 (by rfl) ⟨2280338, by rfl⟩ : syracuseStep 3040451 = 4560677) B4560677
theorem B2026967 : Blo 2025435 2026967 := bstep (se 1 (by rfl) ⟨1520225, by rfl⟩ : syracuseStep 2026967 = 3040451) B3040451
theorem B5130773 : Blo 2025435 5130773 := bbase (se 6 (by rfl) ⟨120252, by rfl⟩ : syracuseStep 5130773 = 240505) (by norm_num)
theorem B3420515 : Blo 2025435 3420515 := bstep (se 1 (by rfl) ⟨2565386, by rfl⟩ : syracuseStep 3420515 = 5130773) B5130773
theorem B2280343 : Blo 2025435 2280343 := bstep (se 1 (by rfl) ⟨1710257, by rfl⟩ : syracuseStep 2280343 = 3420515) B3420515
theorem B3040457 : Blo 2025435 3040457 := bstep (se 2 (by rfl) ⟨1140171, by rfl⟩ : syracuseStep 3040457 = 2280343) B2280343
theorem B2026971 : Blo 2025435 2026971 := bstep (se 1 (by rfl) ⟨1520228, by rfl⟩ : syracuseStep 2026971 = 3040457) B3040457
theorem B8658197 : Blo 2025435 8658197 := bbase (se 6 (by rfl) ⟨202926, by rfl⟩ : syracuseStep 8658197 = 405853) (by norm_num)
theorem B5772131 : Blo 2025435 5772131 := bstep (se 1 (by rfl) ⟨4329098, by rfl⟩ : syracuseStep 5772131 = 8658197) B8658197
theorem B3848087 : Blo 2025435 3848087 := bstep (se 1 (by rfl) ⟨2886065, by rfl⟩ : syracuseStep 3848087 = 5772131) B5772131
theorem B10261565 : Blo 2025435 10261565 := bstep (se 3 (by rfl) ⟨1924043, by rfl⟩ : syracuseStep 10261565 = 3848087) B3848087
theorem B6841043 : Blo 2025435 6841043 := bstep (se 1 (by rfl) ⟨5130782, by rfl⟩ : syracuseStep 6841043 = 10261565) B10261565
theorem B4560695 : Blo 2025435 4560695 := bstep (se 1 (by rfl) ⟨3420521, by rfl⟩ : syracuseStep 4560695 = 6841043) B6841043
theorem B3040463 : Blo 2025435 3040463 := bstep (se 1 (by rfl) ⟨2280347, by rfl⟩ : syracuseStep 3040463 = 4560695) B4560695
theorem B2026975 : Blo 2025435 2026975 := bstep (se 1 (by rfl) ⟨1520231, by rfl⟩ : syracuseStep 2026975 = 3040463) B3040463
theorem B3040469 : Blo 2025435 3040469 := bbase (se 7 (by rfl) ⟨35630, by rfl⟩ : syracuseStep 3040469 = 71261) (by norm_num)
theorem B2026979 : Blo 2025435 2026979 := bstep (se 1 (by rfl) ⟨1520234, by rfl⟩ : syracuseStep 2026979 = 3040469) B3040469
theorem B2886077 : Blo 2025435 2886077 := bbase (se 3 (by rfl) ⟨541139, by rfl⟩ : syracuseStep 2886077 = 1082279) (by norm_num)
theorem B7696205 : Blo 2025435 7696205 := bstep (se 3 (by rfl) ⟨1443038, by rfl⟩ : syracuseStep 7696205 = 2886077) B2886077
theorem B5130803 : Blo 2025435 5130803 := bstep (se 1 (by rfl) ⟨3848102, by rfl⟩ : syracuseStep 5130803 = 7696205) B7696205
theorem B3420535 : Blo 2025435 3420535 := bstep (se 1 (by rfl) ⟨2565401, by rfl⟩ : syracuseStep 3420535 = 5130803) B5130803
theorem B4560713 : Blo 2025435 4560713 := bstep (se 2 (by rfl) ⟨1710267, by rfl⟩ : syracuseStep 4560713 = 3420535) B3420535
theorem B3040475 : Blo 2025435 3040475 := bstep (se 1 (by rfl) ⟨2280356, by rfl⟩ : syracuseStep 3040475 = 4560713) B4560713
theorem B2026983 : Blo 2025435 2026983 := bstep (se 1 (by rfl) ⟨1520237, by rfl⟩ : syracuseStep 2026983 = 3040475) B3040475
theorem B2280361 : Blo 2025435 2280361 := bbase (se 2 (by rfl) ⟨855135, by rfl⟩ : syracuseStep 2280361 = 1710271) (by norm_num)
theorem B3040481 : Blo 2025435 3040481 := bstep (se 2 (by rfl) ⟨1140180, by rfl⟩ : syracuseStep 3040481 = 2280361) B2280361
theorem B2026987 : Blo 2025435 2026987 := bstep (se 1 (by rfl) ⟨1520240, by rfl⟩ : syracuseStep 2026987 = 3040481) B3040481
theorem B9740549 : Blo 2025435 9740549 := bbase (se 4 (by rfl) ⟨913176, by rfl⟩ : syracuseStep 9740549 = 1826353) (by norm_num)
theorem B6493699 : Blo 2025435 6493699 := bstep (se 1 (by rfl) ⟨4870274, by rfl⟩ : syracuseStep 6493699 = 9740549) B9740549
theorem B8658265 : Blo 2025435 8658265 := bstep (se 2 (by rfl) ⟨3246849, by rfl⟩ : syracuseStep 8658265 = 6493699) B6493699
theorem B11544353 : Blo 2025435 11544353 := bstep (se 2 (by rfl) ⟨4329132, by rfl⟩ : syracuseStep 11544353 = 8658265) B8658265
theorem B7696235 : Blo 2025435 7696235 := bstep (se 1 (by rfl) ⟨5772176, by rfl⟩ : syracuseStep 7696235 = 11544353) B11544353
theorem B5130823 : Blo 2025435 5130823 := bstep (se 1 (by rfl) ⟨3848117, by rfl⟩ : syracuseStep 5130823 = 7696235) B7696235
theorem B6841097 : Blo 2025435 6841097 := bstep (se 2 (by rfl) ⟨2565411, by rfl⟩ : syracuseStep 6841097 = 5130823) B5130823
theorem B4560731 : Blo 2025435 4560731 := bstep (se 1 (by rfl) ⟨3420548, by rfl⟩ : syracuseStep 4560731 = 6841097) B6841097
theorem B3040487 : Blo 2025435 3040487 := bstep (se 1 (by rfl) ⟨2280365, by rfl⟩ : syracuseStep 3040487 = 4560731) B4560731
theorem B2026991 : Blo 2025435 2026991 := bstep (se 1 (by rfl) ⟨1520243, by rfl⟩ : syracuseStep 2026991 = 3040487) B3040487
theorem B3040493 : Blo 2025435 3040493 := bbase (se 3 (by rfl) ⟨570092, by rfl⟩ : syracuseStep 3040493 = 1140185) (by norm_num)
theorem B2026995 : Blo 2025435 2026995 := bstep (se 1 (by rfl) ⟨1520246, by rfl⟩ : syracuseStep 2026995 = 3040493) B3040493
theorem B4560749 : Blo 2025435 4560749 := bbase (se 3 (by rfl) ⟨855140, by rfl⟩ : syracuseStep 4560749 = 1710281) (by norm_num)
theorem B3040499 : Blo 2025435 3040499 := bstep (se 1 (by rfl) ⟨2280374, by rfl⟩ : syracuseStep 3040499 = 4560749) B4560749
theorem B2026999 : Blo 2025435 2026999 := bstep (se 1 (by rfl) ⟨1520249, by rfl⟩ : syracuseStep 2026999 = 3040499) B3040499
theorem B3848141 : Blo 2025435 3848141 := bbase (se 3 (by rfl) ⟨721526, by rfl⟩ : syracuseStep 3848141 = 1443053) (by norm_num)
theorem B2565427 : Blo 2025435 2565427 := bstep (se 1 (by rfl) ⟨1924070, by rfl⟩ : syracuseStep 2565427 = 3848141) B3848141
theorem B3420569 : Blo 2025435 3420569 := bstep (se 2 (by rfl) ⟨1282713, by rfl⟩ : syracuseStep 3420569 = 2565427) B2565427
theorem B2280379 : Blo 2025435 2280379 := bstep (se 1 (by rfl) ⟨1710284, by rfl⟩ : syracuseStep 2280379 = 3420569) B3420569
theorem B3040505 : Blo 2025435 3040505 := bstep (se 2 (by rfl) ⟨1140189, by rfl⟩ : syracuseStep 3040505 = 2280379) B2280379
theorem B2027003 : Blo 2025435 2027003 := bstep (se 1 (by rfl) ⟨1520252, by rfl⟩ : syracuseStep 2027003 = 3040505) B3040505
theorem B10401733 : Blo 2025435 10401733 := bbase (se 4 (by rfl) ⟨975162, by rfl⟩ : syracuseStep 10401733 = 1950325) (by norm_num)
theorem B13868977 : Blo 2025435 13868977 := bstep (se 2 (by rfl) ⟨5200866, by rfl⟩ : syracuseStep 13868977 = 10401733) B10401733
theorem B18491969 : Blo 2025435 18491969 := bstep (se 2 (by rfl) ⟨6934488, by rfl⟩ : syracuseStep 18491969 = 13868977) B13868977
theorem B12327979 : Blo 2025435 12327979 := bstep (se 1 (by rfl) ⟨9245984, by rfl⟩ : syracuseStep 12327979 = 18491969) B18491969
theorem B16437305 : Blo 2025435 16437305 := bstep (se 2 (by rfl) ⟨6163989, by rfl⟩ : syracuseStep 16437305 = 12327979) B12327979
theorem B10958203 : Blo 2025435 10958203 := bstep (se 1 (by rfl) ⟨8218652, by rfl⟩ : syracuseStep 10958203 = 16437305) B16437305
theorem B14610937 : Blo 2025435 14610937 := bstep (se 2 (by rfl) ⟨5479101, by rfl⟩ : syracuseStep 14610937 = 10958203) B10958203
theorem B19481249 : Blo 2025435 19481249 := bstep (se 2 (by rfl) ⟨7305468, by rfl⟩ : syracuseStep 19481249 = 14610937) B14610937
theorem B51949997 : Blo 2025435 51949997 := bstep (se 3 (by rfl) ⟨9740624, by rfl⟩ : syracuseStep 51949997 = 19481249) B19481249
theorem B34633331 : Blo 2025435 34633331 := bstep (se 1 (by rfl) ⟨25974998, by rfl⟩ : syracuseStep 34633331 = 51949997) B51949997
theorem B23088887 : Blo 2025435 23088887 := bstep (se 1 (by rfl) ⟨17316665, by rfl⟩ : syracuseStep 23088887 = 34633331) B34633331
theorem B15392591 : Blo 2025435 15392591 := bstep (se 1 (by rfl) ⟨11544443, by rfl⟩ : syracuseStep 15392591 = 23088887) B23088887
theorem B10261727 : Blo 2025435 10261727 := bstep (se 1 (by rfl) ⟨7696295, by rfl⟩ : syracuseStep 10261727 = 15392591) B15392591
theorem B6841151 : Blo 2025435 6841151 := bstep (se 1 (by rfl) ⟨5130863, by rfl⟩ : syracuseStep 6841151 = 10261727) B10261727
theorem B4560767 : Blo 2025435 4560767 := bstep (se 1 (by rfl) ⟨3420575, by rfl⟩ : syracuseStep 4560767 = 6841151) B6841151
theorem B3040511 : Blo 2025435 3040511 := bstep (se 1 (by rfl) ⟨2280383, by rfl⟩ : syracuseStep 3040511 = 4560767) B4560767
theorem B2027007 : Blo 2025435 2027007 := bstep (se 1 (by rfl) ⟨1520255, by rfl⟩ : syracuseStep 2027007 = 3040511) B3040511
theorem B3040517 : Blo 2025435 3040517 := bbase (se 4 (by rfl) ⟨285048, by rfl⟩ : syracuseStep 3040517 = 570097) (by norm_num)
theorem B2027011 : Blo 2025435 2027011 := bstep (se 1 (by rfl) ⟨1520258, by rfl⟩ : syracuseStep 2027011 = 3040517) B3040517
theorem B3420589 : Blo 2025435 3420589 := bbase (se 3 (by rfl) ⟨641360, by rfl⟩ : syracuseStep 3420589 = 1282721) (by norm_num)
theorem B4560785 : Blo 2025435 4560785 := bstep (se 2 (by rfl) ⟨1710294, by rfl⟩ : syracuseStep 4560785 = 3420589) B3420589
theorem B3040523 : Blo 2025435 3040523 := bstep (se 1 (by rfl) ⟨2280392, by rfl⟩ : syracuseStep 3040523 = 4560785) B4560785
theorem B2027015 : Blo 2025435 2027015 := bstep (se 1 (by rfl) ⟨1520261, by rfl⟩ : syracuseStep 2027015 = 3040523) B3040523
theorem B2280397 : Blo 2025435 2280397 := bbase (se 3 (by rfl) ⟨427574, by rfl⟩ : syracuseStep 2280397 = 855149) (by norm_num)
theorem B3040529 : Blo 2025435 3040529 := bstep (se 2 (by rfl) ⟨1140198, by rfl⟩ : syracuseStep 3040529 = 2280397) B2280397
theorem B2027019 : Blo 2025435 2027019 := bstep (se 1 (by rfl) ⟨1520264, by rfl⟩ : syracuseStep 2027019 = 3040529) B3040529
theorem B6841205 : Blo 2025435 6841205 := bbase (se 5 (by rfl) ⟨320681, by rfl⟩ : syracuseStep 6841205 = 641363) (by norm_num)
theorem B4560803 : Blo 2025435 4560803 := bstep (se 1 (by rfl) ⟨3420602, by rfl⟩ : syracuseStep 4560803 = 6841205) B6841205
theorem B3040535 : Blo 2025435 3040535 := bstep (se 1 (by rfl) ⟨2280401, by rfl⟩ : syracuseStep 3040535 = 4560803) B4560803
theorem B2027023 : Blo 2025435 2027023 := bstep (se 1 (by rfl) ⟨1520267, by rfl⟩ : syracuseStep 2027023 = 3040535) B3040535
theorem B3040541 : Blo 2025435 3040541 := bbase (se 3 (by rfl) ⟨570101, by rfl⟩ : syracuseStep 3040541 = 1140203) (by norm_num)
theorem B2027027 : Blo 2025435 2027027 := bstep (se 1 (by rfl) ⟨1520270, by rfl⟩ : syracuseStep 2027027 = 3040541) B3040541
theorem B4560821 : Blo 2025435 4560821 := bbase (se 5 (by rfl) ⟨213788, by rfl⟩ : syracuseStep 4560821 = 427577) (by norm_num)
theorem B3040547 : Blo 2025435 3040547 := bstep (se 1 (by rfl) ⟨2280410, by rfl⟩ : syracuseStep 3040547 = 4560821) B4560821
theorem B2027031 : Blo 2025435 2027031 := bstep (se 1 (by rfl) ⟨1520273, by rfl⟩ : syracuseStep 2027031 = 3040547) B3040547
theorem B4870381 : Blo 2025435 4870381 := bbase (se 3 (by rfl) ⟨913196, by rfl⟩ : syracuseStep 4870381 = 1826393) (by norm_num)
theorem B6493841 : Blo 2025435 6493841 := bstep (se 2 (by rfl) ⟨2435190, by rfl⟩ : syracuseStep 6493841 = 4870381) B4870381
theorem B4329227 : Blo 2025435 4329227 := bstep (se 1 (by rfl) ⟨3246920, by rfl⟩ : syracuseStep 4329227 = 6493841) B6493841
theorem B11544605 : Blo 2025435 11544605 := bstep (se 3 (by rfl) ⟨2164613, by rfl⟩ : syracuseStep 11544605 = 4329227) B4329227
theorem B7696403 : Blo 2025435 7696403 := bstep (se 1 (by rfl) ⟨5772302, by rfl⟩ : syracuseStep 7696403 = 11544605) B11544605
theorem B5130935 : Blo 2025435 5130935 := bstep (se 1 (by rfl) ⟨3848201, by rfl⟩ : syracuseStep 5130935 = 7696403) B7696403
theorem B3420623 : Blo 2025435 3420623 := bstep (se 1 (by rfl) ⟨2565467, by rfl⟩ : syracuseStep 3420623 = 5130935) B5130935
theorem B2280415 : Blo 2025435 2280415 := bstep (se 1 (by rfl) ⟨1710311, by rfl⟩ : syracuseStep 2280415 = 3420623) B3420623
theorem B3040553 : Blo 2025435 3040553 := bstep (se 2 (by rfl) ⟨1140207, by rfl⟩ : syracuseStep 3040553 = 2280415) B2280415
theorem B2027035 : Blo 2025435 2027035 := bstep (se 1 (by rfl) ⟨1520276, by rfl⟩ : syracuseStep 2027035 = 3040553) B3040553
theorem B3082045 : Blo 2025435 3082045 := bbase (se 3 (by rfl) ⟨577883, by rfl⟩ : syracuseStep 3082045 = 1155767) (by norm_num)
theorem B4109393 : Blo 2025435 4109393 := bstep (se 2 (by rfl) ⟨1541022, by rfl⟩ : syracuseStep 4109393 = 3082045) B3082045
theorem B2739595 : Blo 2025435 2739595 := bstep (se 1 (by rfl) ⟨2054696, by rfl⟩ : syracuseStep 2739595 = 4109393) B4109393
theorem B3652793 : Blo 2025435 3652793 := bstep (se 2 (by rfl) ⟨1369797, by rfl⟩ : syracuseStep 3652793 = 2739595) B2739595
theorem B2435195 : Blo 2025435 2435195 := bstep (se 1 (by rfl) ⟨1826396, by rfl⟩ : syracuseStep 2435195 = 3652793) B3652793
theorem B6493853 : Blo 2025435 6493853 := bstep (se 3 (by rfl) ⟨1217597, by rfl⟩ : syracuseStep 6493853 = 2435195) B2435195
theorem B4329235 : Blo 2025435 4329235 := bstep (se 1 (by rfl) ⟨3246926, by rfl⟩ : syracuseStep 4329235 = 6493853) B6493853
theorem B5772313 : Blo 2025435 5772313 := bstep (se 2 (by rfl) ⟨2164617, by rfl⟩ : syracuseStep 5772313 = 4329235) B4329235
theorem B7696417 : Blo 2025435 7696417 := bstep (se 2 (by rfl) ⟨2886156, by rfl⟩ : syracuseStep 7696417 = 5772313) B5772313
theorem B10261889 : Blo 2025435 10261889 := bstep (se 2 (by rfl) ⟨3848208, by rfl⟩ : syracuseStep 10261889 = 7696417) B7696417
theorem B6841259 : Blo 2025435 6841259 := bstep (se 1 (by rfl) ⟨5130944, by rfl⟩ : syracuseStep 6841259 = 10261889) B10261889
theorem B4560839 : Blo 2025435 4560839 := bstep (se 1 (by rfl) ⟨3420629, by rfl⟩ : syracuseStep 4560839 = 6841259) B6841259
theorem B3040559 : Blo 2025435 3040559 := bstep (se 1 (by rfl) ⟨2280419, by rfl⟩ : syracuseStep 3040559 = 4560839) B4560839
theorem B2027039 : Blo 2025435 2027039 := bstep (se 1 (by rfl) ⟨1520279, by rfl⟩ : syracuseStep 2027039 = 3040559) B3040559
theorem B3040565 : Blo 2025435 3040565 := bbase (se 5 (by rfl) ⟨142526, by rfl⟩ : syracuseStep 3040565 = 285053) (by norm_num)
theorem B2027043 : Blo 2025435 2027043 := bstep (se 1 (by rfl) ⟨1520282, by rfl⟩ : syracuseStep 2027043 = 3040565) B3040565
theorem B5130965 : Blo 2025435 5130965 := bbase (se 7 (by rfl) ⟨60128, by rfl⟩ : syracuseStep 5130965 = 120257) (by norm_num)
theorem B3420643 : Blo 2025435 3420643 := bstep (se 1 (by rfl) ⟨2565482, by rfl⟩ : syracuseStep 3420643 = 5130965) B5130965
theorem B4560857 : Blo 2025435 4560857 := bstep (se 2 (by rfl) ⟨1710321, by rfl⟩ : syracuseStep 4560857 = 3420643) B3420643
theorem B3040571 : Blo 2025435 3040571 := bstep (se 1 (by rfl) ⟨2280428, by rfl⟩ : syracuseStep 3040571 = 4560857) B4560857
theorem B2027047 : Blo 2025435 2027047 := bstep (se 1 (by rfl) ⟨1520285, by rfl⟩ : syracuseStep 2027047 = 3040571) B3040571
theorem B2280433 : Blo 2025435 2280433 := bbase (se 2 (by rfl) ⟨855162, by rfl⟩ : syracuseStep 2280433 = 1710325) (by norm_num)
theorem B3040577 : Blo 2025435 3040577 := bstep (se 2 (by rfl) ⟨1140216, by rfl⟩ : syracuseStep 3040577 = 2280433) B2280433
theorem B2027051 : Blo 2025435 2027051 := bstep (se 1 (by rfl) ⟨1520288, by rfl⟩ : syracuseStep 2027051 = 3040577) B3040577
theorem B5553989 : Blo 2025435 5553989 := bbase (se 4 (by rfl) ⟨520686, by rfl⟩ : syracuseStep 5553989 = 1041373) (by norm_num)
theorem B59242549 : Blo 2025435 59242549 := bstep (se 5 (by rfl) ⟨2776994, by rfl⟩ : syracuseStep 59242549 = 5553989) B5553989
theorem B78990065 : Blo 2025435 78990065 := bstep (se 2 (by rfl) ⟨29621274, by rfl⟩ : syracuseStep 78990065 = 59242549) B59242549
theorem B52660043 : Blo 2025435 52660043 := bstep (se 1 (by rfl) ⟨39495032, by rfl⟩ : syracuseStep 52660043 = 78990065) B78990065
theorem B35106695 : Blo 2025435 35106695 := bstep (se 1 (by rfl) ⟨26330021, by rfl⟩ : syracuseStep 35106695 = 52660043) B52660043
theorem B23404463 : Blo 2025435 23404463 := bstep (se 1 (by rfl) ⟨17553347, by rfl⟩ : syracuseStep 23404463 = 35106695) B35106695
theorem B15602975 : Blo 2025435 15602975 := bstep (se 1 (by rfl) ⟨11702231, by rfl⟩ : syracuseStep 15602975 = 23404463) B23404463
theorem B10401983 : Blo 2025435 10401983 := bstep (se 1 (by rfl) ⟨7801487, by rfl⟩ : syracuseStep 10401983 = 15602975) B15602975
theorem B6934655 : Blo 2025435 6934655 := bstep (se 1 (by rfl) ⟨5200991, by rfl⟩ : syracuseStep 6934655 = 10401983) B10401983
theorem B4623103 : Blo 2025435 4623103 := bstep (se 1 (by rfl) ⟨3467327, by rfl⟩ : syracuseStep 4623103 = 6934655) B6934655
theorem B6164137 : Blo 2025435 6164137 := bstep (se 2 (by rfl) ⟨2311551, by rfl⟩ : syracuseStep 6164137 = 4623103) B4623103
theorem B8218849 : Blo 2025435 8218849 := bstep (se 2 (by rfl) ⟨3082068, by rfl⟩ : syracuseStep 8218849 = 6164137) B6164137
theorem B10958465 : Blo 2025435 10958465 := bstep (se 2 (by rfl) ⟨4109424, by rfl⟩ : syracuseStep 10958465 = 8218849) B8218849
theorem B7305643 : Blo 2025435 7305643 := bstep (se 1 (by rfl) ⟨5479232, by rfl⟩ : syracuseStep 7305643 = 10958465) B10958465
theorem B9740857 : Blo 2025435 9740857 := bstep (se 2 (by rfl) ⟨3652821, by rfl⟩ : syracuseStep 9740857 = 7305643) B7305643
theorem B12987809 : Blo 2025435 12987809 := bstep (se 2 (by rfl) ⟨4870428, by rfl⟩ : syracuseStep 12987809 = 9740857) B9740857
theorem B8658539 : Blo 2025435 8658539 := bstep (se 1 (by rfl) ⟨6493904, by rfl⟩ : syracuseStep 8658539 = 12987809) B12987809
theorem B5772359 : Blo 2025435 5772359 := bstep (se 1 (by rfl) ⟨4329269, by rfl⟩ : syracuseStep 5772359 = 8658539) B8658539
theorem B3848239 : Blo 2025435 3848239 := bstep (se 1 (by rfl) ⟨2886179, by rfl⟩ : syracuseStep 3848239 = 5772359) B5772359
theorem B5130985 : Blo 2025435 5130985 := bstep (se 2 (by rfl) ⟨1924119, by rfl⟩ : syracuseStep 5130985 = 3848239) B3848239
theorem B6841313 : Blo 2025435 6841313 := bstep (se 2 (by rfl) ⟨2565492, by rfl⟩ : syracuseStep 6841313 = 5130985) B5130985
theorem B4560875 : Blo 2025435 4560875 := bstep (se 1 (by rfl) ⟨3420656, by rfl⟩ : syracuseStep 4560875 = 6841313) B6841313
theorem B3040583 : Blo 2025435 3040583 := bstep (se 1 (by rfl) ⟨2280437, by rfl⟩ : syracuseStep 3040583 = 4560875) B4560875
theorem B2027055 : Blo 2025435 2027055 := bstep (se 1 (by rfl) ⟨1520291, by rfl⟩ : syracuseStep 2027055 = 3040583) B3040583
theorem B3040589 : Blo 2025435 3040589 := bbase (se 3 (by rfl) ⟨570110, by rfl⟩ : syracuseStep 3040589 = 1140221) (by norm_num)
theorem B2027059 : Blo 2025435 2027059 := bstep (se 1 (by rfl) ⟨1520294, by rfl⟩ : syracuseStep 2027059 = 3040589) B3040589
theorem B4560893 : Blo 2025435 4560893 := bbase (se 3 (by rfl) ⟨855167, by rfl⟩ : syracuseStep 4560893 = 1710335) (by norm_num)
theorem B3040595 : Blo 2025435 3040595 := bstep (se 1 (by rfl) ⟨2280446, by rfl⟩ : syracuseStep 3040595 = 4560893) B4560893
theorem B2027063 : Blo 2025435 2027063 := bstep (se 1 (by rfl) ⟨1520297, by rfl⟩ : syracuseStep 2027063 = 3040595) B3040595
theorem B3420677 : Blo 2025435 3420677 := bbase (se 4 (by rfl) ⟨320688, by rfl⟩ : syracuseStep 3420677 = 641377) (by norm_num)
theorem B2280451 : Blo 2025435 2280451 := bstep (se 1 (by rfl) ⟨1710338, by rfl⟩ : syracuseStep 2280451 = 3420677) B3420677
theorem B3040601 : Blo 2025435 3040601 := bstep (se 2 (by rfl) ⟨1140225, by rfl⟩ : syracuseStep 3040601 = 2280451) B2280451
theorem B2027067 : Blo 2025435 2027067 := bstep (se 1 (by rfl) ⟨1520300, by rfl⟩ : syracuseStep 2027067 = 3040601) B3040601
theorem B15393077 : Blo 2025435 15393077 := bbase (se 5 (by rfl) ⟨721550, by rfl⟩ : syracuseStep 15393077 = 1443101) (by norm_num)
theorem B10262051 : Blo 2025435 10262051 := bstep (se 1 (by rfl) ⟨7696538, by rfl⟩ : syracuseStep 10262051 = 15393077) B15393077
theorem B6841367 : Blo 2025435 6841367 := bstep (se 1 (by rfl) ⟨5131025, by rfl⟩ : syracuseStep 6841367 = 10262051) B10262051
theorem B4560911 : Blo 2025435 4560911 := bstep (se 1 (by rfl) ⟨3420683, by rfl⟩ : syracuseStep 4560911 = 6841367) B6841367
theorem B3040607 : Blo 2025435 3040607 := bstep (se 1 (by rfl) ⟨2280455, by rfl⟩ : syracuseStep 3040607 = 4560911) B4560911
theorem B2027071 : Blo 2025435 2027071 := bstep (se 1 (by rfl) ⟨1520303, by rfl⟩ : syracuseStep 2027071 = 3040607) B3040607
theorem B3040613 : Blo 2025435 3040613 := bbase (se 4 (by rfl) ⟨285057, by rfl⟩ : syracuseStep 3040613 = 570115) (by norm_num)
theorem B2027075 : Blo 2025435 2027075 := bstep (se 1 (by rfl) ⟨1520306, by rfl⟩ : syracuseStep 2027075 = 3040613) B3040613
theorem B3848285 : Blo 2025435 3848285 := bbase (se 3 (by rfl) ⟨721553, by rfl⟩ : syracuseStep 3848285 = 1443107) (by norm_num)
theorem B2565523 : Blo 2025435 2565523 := bstep (se 1 (by rfl) ⟨1924142, by rfl⟩ : syracuseStep 2565523 = 3848285) B3848285
theorem B3420697 : Blo 2025435 3420697 := bstep (se 2 (by rfl) ⟨1282761, by rfl⟩ : syracuseStep 3420697 = 2565523) B2565523
theorem B4560929 : Blo 2025435 4560929 := bstep (se 2 (by rfl) ⟨1710348, by rfl⟩ : syracuseStep 4560929 = 3420697) B3420697
theorem B3040619 : Blo 2025435 3040619 := bstep (se 1 (by rfl) ⟨2280464, by rfl⟩ : syracuseStep 3040619 = 4560929) B4560929
theorem B2027079 : Blo 2025435 2027079 := bstep (se 1 (by rfl) ⟨1520309, by rfl⟩ : syracuseStep 2027079 = 3040619) B3040619
theorem B2280469 : Blo 2025435 2280469 := bbase (se 6 (by rfl) ⟨53448, by rfl⟩ : syracuseStep 2280469 = 106897) (by norm_num)
theorem B3040625 : Blo 2025435 3040625 := bstep (se 2 (by rfl) ⟨1140234, by rfl⟩ : syracuseStep 3040625 = 2280469) B2280469
theorem B2027083 : Blo 2025435 2027083 := bstep (se 1 (by rfl) ⟨1520312, by rfl⟩ : syracuseStep 2027083 = 3040625) B3040625
theorem B2565533 : Blo 2025435 2565533 := bbase (se 3 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 2565533 = 962075) (by norm_num)
theorem B6841421 : Blo 2025435 6841421 := bstep (se 3 (by rfl) ⟨1282766, by rfl⟩ : syracuseStep 6841421 = 2565533) B2565533
theorem B4560947 : Blo 2025435 4560947 := bstep (se 1 (by rfl) ⟨3420710, by rfl⟩ : syracuseStep 4560947 = 6841421) B6841421
theorem B3040631 : Blo 2025435 3040631 := bstep (se 1 (by rfl) ⟨2280473, by rfl⟩ : syracuseStep 3040631 = 4560947) B4560947
theorem B2027087 : Blo 2025435 2027087 := bstep (se 1 (by rfl) ⟨1520315, by rfl⟩ : syracuseStep 2027087 = 3040631) B3040631
theorem B3040637 : Blo 2025435 3040637 := bbase (se 3 (by rfl) ⟨570119, by rfl⟩ : syracuseStep 3040637 = 1140239) (by norm_num)
theorem B2027091 : Blo 2025435 2027091 := bstep (se 1 (by rfl) ⟨1520318, by rfl⟩ : syracuseStep 2027091 = 3040637) B3040637
theorem B4560965 : Blo 2025435 4560965 := bbase (se 4 (by rfl) ⟨427590, by rfl⟩ : syracuseStep 4560965 = 855181) (by norm_num)
theorem B3040643 : Blo 2025435 3040643 := bstep (se 1 (by rfl) ⟨2280482, by rfl⟩ : syracuseStep 3040643 = 4560965) B4560965
theorem B2027095 : Blo 2025435 2027095 := bstep (se 1 (by rfl) ⟨1520321, by rfl⟩ : syracuseStep 2027095 = 3040643) B3040643
theorem B5772485 : Blo 2025435 5772485 := bbase (se 4 (by rfl) ⟨541170, by rfl⟩ : syracuseStep 5772485 = 1082341) (by norm_num)
theorem B3848323 : Blo 2025435 3848323 := bstep (se 1 (by rfl) ⟨2886242, by rfl⟩ : syracuseStep 3848323 = 5772485) B5772485
theorem B5131097 : Blo 2025435 5131097 := bstep (se 2 (by rfl) ⟨1924161, by rfl⟩ : syracuseStep 5131097 = 3848323) B3848323
theorem B3420731 : Blo 2025435 3420731 := bstep (se 1 (by rfl) ⟨2565548, by rfl⟩ : syracuseStep 3420731 = 5131097) B5131097
theorem B2280487 : Blo 2025435 2280487 := bstep (se 1 (by rfl) ⟨1710365, by rfl⟩ : syracuseStep 2280487 = 3420731) B3420731
theorem B3040649 : Blo 2025435 3040649 := bstep (se 2 (by rfl) ⟨1140243, by rfl⟩ : syracuseStep 3040649 = 2280487) B2280487
theorem B2027099 : Blo 2025435 2027099 := bstep (se 1 (by rfl) ⟨1520324, by rfl⟩ : syracuseStep 2027099 = 3040649) B3040649
theorem B10262213 : Blo 2025435 10262213 := bbase (se 4 (by rfl) ⟨962082, by rfl⟩ : syracuseStep 10262213 = 1924165) (by norm_num)
theorem B6841475 : Blo 2025435 6841475 := bstep (se 1 (by rfl) ⟨5131106, by rfl⟩ : syracuseStep 6841475 = 10262213) B10262213
theorem B4560983 : Blo 2025435 4560983 := bstep (se 1 (by rfl) ⟨3420737, by rfl⟩ : syracuseStep 4560983 = 6841475) B6841475
theorem B3040655 : Blo 2025435 3040655 := bstep (se 1 (by rfl) ⟨2280491, by rfl⟩ : syracuseStep 3040655 = 4560983) B4560983
theorem B2027103 : Blo 2025435 2027103 := bstep (se 1 (by rfl) ⟨1520327, by rfl⟩ : syracuseStep 2027103 = 3040655) B3040655
theorem B3040661 : Blo 2025435 3040661 := bbase (se 6 (by rfl) ⟨71265, by rfl⟩ : syracuseStep 3040661 = 142531) (by norm_num)
theorem B2027107 : Blo 2025435 2027107 := bstep (se 1 (by rfl) ⟨1520330, by rfl⟩ : syracuseStep 2027107 = 3040661) B3040661
theorem B4329389 : Blo 2025435 4329389 := bbase (se 3 (by rfl) ⟨811760, by rfl⟩ : syracuseStep 4329389 = 1623521) (by norm_num)
theorem B11545037 : Blo 2025435 11545037 := bstep (se 3 (by rfl) ⟨2164694, by rfl⟩ : syracuseStep 11545037 = 4329389) B4329389
theorem B7696691 : Blo 2025435 7696691 := bstep (se 1 (by rfl) ⟨5772518, by rfl⟩ : syracuseStep 7696691 = 11545037) B11545037
theorem B5131127 : Blo 2025435 5131127 := bstep (se 1 (by rfl) ⟨3848345, by rfl⟩ : syracuseStep 5131127 = 7696691) B7696691
theorem B3420751 : Blo 2025435 3420751 := bstep (se 1 (by rfl) ⟨2565563, by rfl⟩ : syracuseStep 3420751 = 5131127) B5131127
theorem B4561001 : Blo 2025435 4561001 := bstep (se 2 (by rfl) ⟨1710375, by rfl⟩ : syracuseStep 4561001 = 3420751) B3420751
theorem B3040667 : Blo 2025435 3040667 := bstep (se 1 (by rfl) ⟨2280500, by rfl⟩ : syracuseStep 3040667 = 4561001) B4561001
theorem B2027111 : Blo 2025435 2027111 := bstep (se 1 (by rfl) ⟨1520333, by rfl⟩ : syracuseStep 2027111 = 3040667) B3040667
theorem B2280505 : Blo 2025435 2280505 := bbase (se 2 (by rfl) ⟨855189, by rfl⟩ : syracuseStep 2280505 = 1710379) (by norm_num)
theorem B3040673 : Blo 2025435 3040673 := bstep (se 2 (by rfl) ⟨1140252, by rfl⟩ : syracuseStep 3040673 = 2280505) B2280505
theorem B2027115 : Blo 2025435 2027115 := bstep (se 1 (by rfl) ⟨1520336, by rfl⟩ : syracuseStep 2027115 = 3040673) B3040673
theorem B2311625 : Blo 2025435 2311625 := bbase (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) (by norm_num)
theorem B6164333 : Blo 2025435 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B4109555 : Blo 2025435 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B10958813 : Blo 2025435 10958813 := bstep (se 3 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 10958813 = 4109555) B4109555
theorem B7305875 : Blo 2025435 7305875 := bstep (se 1 (by rfl) ⟨5479406, by rfl⟩ : syracuseStep 7305875 = 10958813) B10958813
theorem B4870583 : Blo 2025435 4870583 := bstep (se 1 (by rfl) ⟨3652937, by rfl⟩ : syracuseStep 4870583 = 7305875) B7305875
theorem B3247055 : Blo 2025435 3247055 := bstep (se 1 (by rfl) ⟨2435291, by rfl⟩ : syracuseStep 3247055 = 4870583) B4870583
theorem B2164703 : Blo 2025435 2164703 := bstep (se 1 (by rfl) ⟨1623527, by rfl⟩ : syracuseStep 2164703 = 3247055) B3247055
theorem B5772541 : Blo 2025435 5772541 := bstep (se 3 (by rfl) ⟨1082351, by rfl⟩ : syracuseStep 5772541 = 2164703) B2164703
theorem B7696721 : Blo 2025435 7696721 := bstep (se 2 (by rfl) ⟨2886270, by rfl⟩ : syracuseStep 7696721 = 5772541) B5772541
theorem B5131147 : Blo 2025435 5131147 := bstep (se 1 (by rfl) ⟨3848360, by rfl⟩ : syracuseStep 5131147 = 7696721) B7696721
theorem B6841529 : Blo 2025435 6841529 := bstep (se 2 (by rfl) ⟨2565573, by rfl⟩ : syracuseStep 6841529 = 5131147) B5131147
theorem B4561019 : Blo 2025435 4561019 := bstep (se 1 (by rfl) ⟨3420764, by rfl⟩ : syracuseStep 4561019 = 6841529) B6841529
theorem B3040679 : Blo 2025435 3040679 := bstep (se 1 (by rfl) ⟨2280509, by rfl⟩ : syracuseStep 3040679 = 4561019) B4561019
theorem B2027119 : Blo 2025435 2027119 := bstep (se 1 (by rfl) ⟨1520339, by rfl⟩ : syracuseStep 2027119 = 3040679) B3040679
theorem B3040685 : Blo 2025435 3040685 := bbase (se 3 (by rfl) ⟨570128, by rfl⟩ : syracuseStep 3040685 = 1140257) (by norm_num)
theorem B2027123 : Blo 2025435 2027123 := bstep (se 1 (by rfl) ⟨1520342, by rfl⟩ : syracuseStep 2027123 = 3040685) B3040685
theorem B4561037 : Blo 2025435 4561037 := bbase (se 3 (by rfl) ⟨855194, by rfl⟩ : syracuseStep 4561037 = 1710389) (by norm_num)
theorem B3040691 : Blo 2025435 3040691 := bstep (se 1 (by rfl) ⟨2280518, by rfl⟩ : syracuseStep 3040691 = 4561037) B4561037
theorem B2027127 : Blo 2025435 2027127 := bstep (se 1 (by rfl) ⟨1520345, by rfl⟩ : syracuseStep 2027127 = 3040691) B3040691
theorem B2565589 : Blo 2025435 2565589 := bbase (se 7 (by rfl) ⟨30065, by rfl⟩ : syracuseStep 2565589 = 60131) (by norm_num)
theorem B3420785 : Blo 2025435 3420785 := bstep (se 2 (by rfl) ⟨1282794, by rfl⟩ : syracuseStep 3420785 = 2565589) B2565589
theorem B2280523 : Blo 2025435 2280523 := bstep (se 1 (by rfl) ⟨1710392, by rfl⟩ : syracuseStep 2280523 = 3420785) B3420785
theorem B3040697 : Blo 2025435 3040697 := bstep (se 2 (by rfl) ⟨1140261, by rfl⟩ : syracuseStep 3040697 = 2280523) B2280523
theorem B2027131 : Blo 2025435 2027131 := bstep (se 1 (by rfl) ⟨1520348, by rfl⟩ : syracuseStep 2027131 = 3040697) B3040697
theorem B3381805 : Blo 2025435 3381805 := bbase (se 3 (by rfl) ⟨634088, by rfl⟩ : syracuseStep 3381805 = 1268177) (by norm_num)
theorem B4509073 : Blo 2025435 4509073 := bstep (se 2 (by rfl) ⟨1690902, by rfl⟩ : syracuseStep 4509073 = 3381805) B3381805
theorem B24048389 : Blo 2025435 24048389 := bstep (se 4 (by rfl) ⟨2254536, by rfl⟩ : syracuseStep 24048389 = 4509073) B4509073
theorem B16032259 : Blo 2025435 16032259 := bstep (se 1 (by rfl) ⟨12024194, by rfl⟩ : syracuseStep 16032259 = 24048389) B24048389
theorem B85505381 : Blo 2025435 85505381 := bstep (se 4 (by rfl) ⟨8016129, by rfl⟩ : syracuseStep 85505381 = 16032259) B16032259
theorem B57003587 : Blo 2025435 57003587 := bstep (se 1 (by rfl) ⟨42752690, by rfl⟩ : syracuseStep 57003587 = 85505381) B85505381
theorem B38002391 : Blo 2025435 38002391 := bstep (se 1 (by rfl) ⟨28501793, by rfl⟩ : syracuseStep 38002391 = 57003587) B57003587
theorem B25334927 : Blo 2025435 25334927 := bstep (se 1 (by rfl) ⟨19001195, by rfl⟩ : syracuseStep 25334927 = 38002391) B38002391
theorem B16889951 : Blo 2025435 16889951 := bstep (se 1 (by rfl) ⟨12667463, by rfl⟩ : syracuseStep 16889951 = 25334927) B25334927
theorem B11259967 : Blo 2025435 11259967 := bstep (se 1 (by rfl) ⟨8444975, by rfl⟩ : syracuseStep 11259967 = 16889951) B16889951
theorem B15013289 : Blo 2025435 15013289 := bstep (se 2 (by rfl) ⟨5629983, by rfl⟩ : syracuseStep 15013289 = 11259967) B11259967
theorem B40035437 : Blo 2025435 40035437 := bstep (se 3 (by rfl) ⟨7506644, by rfl⟩ : syracuseStep 40035437 = 15013289) B15013289
theorem B26690291 : Blo 2025435 26690291 := bstep (se 1 (by rfl) ⟨20017718, by rfl⟩ : syracuseStep 26690291 = 40035437) B40035437
theorem B17793527 : Blo 2025435 17793527 := bstep (se 1 (by rfl) ⟨13345145, by rfl⟩ : syracuseStep 17793527 = 26690291) B26690291
theorem B47449405 : Blo 2025435 47449405 := bstep (se 3 (by rfl) ⟨8896763, by rfl⟩ : syracuseStep 47449405 = 17793527) B17793527
theorem B63265873 : Blo 2025435 63265873 := bstep (se 2 (by rfl) ⟨23724702, by rfl⟩ : syracuseStep 63265873 = 47449405) B47449405
theorem B84354497 : Blo 2025435 84354497 := bstep (se 2 (by rfl) ⟨31632936, by rfl⟩ : syracuseStep 84354497 = 63265873) B63265873
theorem B56236331 : Blo 2025435 56236331 := bstep (se 1 (by rfl) ⟨42177248, by rfl⟩ : syracuseStep 56236331 = 84354497) B84354497
theorem B37490887 : Blo 2025435 37490887 := bstep (se 1 (by rfl) ⟨28118165, by rfl⟩ : syracuseStep 37490887 = 56236331) B56236331
theorem B49987849 : Blo 2025435 49987849 := bstep (se 2 (by rfl) ⟨18745443, by rfl⟩ : syracuseStep 49987849 = 37490887) B37490887
theorem B66650465 : Blo 2025435 66650465 := bstep (se 2 (by rfl) ⟨24993924, by rfl⟩ : syracuseStep 66650465 = 49987849) B49987849
theorem B177734573 : Blo 2025435 177734573 := bstep (se 3 (by rfl) ⟨33325232, by rfl⟩ : syracuseStep 177734573 = 66650465) B66650465
theorem B118489715 : Blo 2025435 118489715 := bstep (se 1 (by rfl) ⟨88867286, by rfl⟩ : syracuseStep 118489715 = 177734573) B177734573
theorem B78993143 : Blo 2025435 78993143 := bstep (se 1 (by rfl) ⟨59244857, by rfl⟩ : syracuseStep 78993143 = 118489715) B118489715
theorem B52662095 : Blo 2025435 52662095 := bstep (se 1 (by rfl) ⟨39496571, by rfl⟩ : syracuseStep 52662095 = 78993143) B78993143
theorem B35108063 : Blo 2025435 35108063 := bstep (se 1 (by rfl) ⟨26331047, by rfl⟩ : syracuseStep 35108063 = 52662095) B52662095
theorem B23405375 : Blo 2025435 23405375 := bstep (se 1 (by rfl) ⟨17554031, by rfl⟩ : syracuseStep 23405375 = 35108063) B35108063
theorem B62414333 : Blo 2025435 62414333 := bstep (se 3 (by rfl) ⟨11702687, by rfl⟩ : syracuseStep 62414333 = 23405375) B23405375
theorem B41609555 : Blo 2025435 41609555 := bstep (se 1 (by rfl) ⟨31207166, by rfl⟩ : syracuseStep 41609555 = 62414333) B62414333
theorem B27739703 : Blo 2025435 27739703 := bstep (se 1 (by rfl) ⟨20804777, by rfl⟩ : syracuseStep 27739703 = 41609555) B41609555
theorem B73972541 : Blo 2025435 73972541 := bstep (se 3 (by rfl) ⟨13869851, by rfl⟩ : syracuseStep 73972541 = 27739703) B27739703
theorem B197260109 : Blo 2025435 197260109 := bstep (se 3 (by rfl) ⟨36986270, by rfl⟩ : syracuseStep 197260109 = 73972541) B73972541
theorem B131506739 : Blo 2025435 131506739 := bstep (se 1 (by rfl) ⟨98630054, by rfl⟩ : syracuseStep 131506739 = 197260109) B197260109
theorem B87671159 : Blo 2025435 87671159 := bstep (se 1 (by rfl) ⟨65753369, by rfl⟩ : syracuseStep 87671159 = 131506739) B131506739
theorem B58447439 : Blo 2025435 58447439 := bstep (se 1 (by rfl) ⟨43835579, by rfl⟩ : syracuseStep 58447439 = 87671159) B87671159
theorem B38964959 : Blo 2025435 38964959 := bstep (se 1 (by rfl) ⟨29223719, by rfl⟩ : syracuseStep 38964959 = 58447439) B58447439
theorem B25976639 : Blo 2025435 25976639 := bstep (se 1 (by rfl) ⟨19482479, by rfl⟩ : syracuseStep 25976639 = 38964959) B38964959
theorem B17317759 : Blo 2025435 17317759 := bstep (se 1 (by rfl) ⟨12988319, by rfl⟩ : syracuseStep 17317759 = 25976639) B25976639
theorem B23090345 : Blo 2025435 23090345 := bstep (se 2 (by rfl) ⟨8658879, by rfl⟩ : syracuseStep 23090345 = 17317759) B17317759
theorem B15393563 : Blo 2025435 15393563 := bstep (se 1 (by rfl) ⟨11545172, by rfl⟩ : syracuseStep 15393563 = 23090345) B23090345
theorem B10262375 : Blo 2025435 10262375 := bstep (se 1 (by rfl) ⟨7696781, by rfl⟩ : syracuseStep 10262375 = 15393563) B15393563
theorem B6841583 : Blo 2025435 6841583 := bstep (se 1 (by rfl) ⟨5131187, by rfl⟩ : syracuseStep 6841583 = 10262375) B10262375
theorem B4561055 : Blo 2025435 4561055 := bstep (se 1 (by rfl) ⟨3420791, by rfl⟩ : syracuseStep 4561055 = 6841583) B6841583
theorem B3040703 : Blo 2025435 3040703 := bstep (se 1 (by rfl) ⟨2280527, by rfl⟩ : syracuseStep 3040703 = 4561055) B4561055
theorem B2027135 : Blo 2025435 2027135 := bstep (se 1 (by rfl) ⟨1520351, by rfl⟩ : syracuseStep 2027135 = 3040703) B3040703
theorem B3040709 : Blo 2025435 3040709 := bbase (se 4 (by rfl) ⟨285066, by rfl⟩ : syracuseStep 3040709 = 570133) (by norm_num)
theorem B2027139 : Blo 2025435 2027139 := bstep (se 1 (by rfl) ⟨1520354, by rfl⟩ : syracuseStep 2027139 = 3040709) B3040709
theorem B3420805 : Blo 2025435 3420805 := bbase (se 4 (by rfl) ⟨320700, by rfl⟩ : syracuseStep 3420805 = 641401) (by norm_num)
theorem B4561073 : Blo 2025435 4561073 := bstep (se 2 (by rfl) ⟨1710402, by rfl⟩ : syracuseStep 4561073 = 3420805) B3420805
theorem B3040715 : Blo 2025435 3040715 := bstep (se 1 (by rfl) ⟨2280536, by rfl⟩ : syracuseStep 3040715 = 4561073) B4561073
theorem B2027143 : Blo 2025435 2027143 := bstep (se 1 (by rfl) ⟨1520357, by rfl⟩ : syracuseStep 2027143 = 3040715) B3040715
theorem B2280541 : Blo 2025435 2280541 := bbase (se 3 (by rfl) ⟨427601, by rfl⟩ : syracuseStep 2280541 = 855203) (by norm_num)
theorem B3040721 : Blo 2025435 3040721 := bstep (se 2 (by rfl) ⟨1140270, by rfl⟩ : syracuseStep 3040721 = 2280541) B2280541
theorem B2027147 : Blo 2025435 2027147 := bstep (se 1 (by rfl) ⟨1520360, by rfl⟩ : syracuseStep 2027147 = 3040721) B3040721
theorem B6841637 : Blo 2025435 6841637 := bbase (se 4 (by rfl) ⟨641403, by rfl⟩ : syracuseStep 6841637 = 1282807) (by norm_num)
theorem B4561091 : Blo 2025435 4561091 := bstep (se 1 (by rfl) ⟨3420818, by rfl⟩ : syracuseStep 4561091 = 6841637) B6841637
theorem B3040727 : Blo 2025435 3040727 := bstep (se 1 (by rfl) ⟨2280545, by rfl⟩ : syracuseStep 3040727 = 4561091) B4561091
theorem B2027151 : Blo 2025435 2027151 := bstep (se 1 (by rfl) ⟨1520363, by rfl⟩ : syracuseStep 2027151 = 3040727) B3040727
theorem B3040733 : Blo 2025435 3040733 := bbase (se 3 (by rfl) ⟨570137, by rfl⟩ : syracuseStep 3040733 = 1140275) (by norm_num)
theorem B2027155 : Blo 2025435 2027155 := bstep (se 1 (by rfl) ⟨1520366, by rfl⟩ : syracuseStep 2027155 = 3040733) B3040733
theorem B4561109 : Blo 2025435 4561109 := bbase (se 7 (by rfl) ⟨53450, by rfl⟩ : syracuseStep 4561109 = 106901) (by norm_num)
theorem B3040739 : Blo 2025435 3040739 := bstep (se 1 (by rfl) ⟨2280554, by rfl⟩ : syracuseStep 3040739 = 4561109) B4561109
theorem B2027159 : Blo 2025435 2027159 := bstep (se 1 (by rfl) ⟨1520369, by rfl⟩ : syracuseStep 2027159 = 3040739) B3040739
theorem B5479525 : Blo 2025435 5479525 := bbase (se 4 (by rfl) ⟨513705, by rfl⟩ : syracuseStep 5479525 = 1027411) (by norm_num)
theorem B7306033 : Blo 2025435 7306033 := bstep (se 2 (by rfl) ⟨2739762, by rfl⟩ : syracuseStep 7306033 = 5479525) B5479525
theorem B9741377 : Blo 2025435 9741377 := bstep (se 2 (by rfl) ⟨3653016, by rfl⟩ : syracuseStep 9741377 = 7306033) B7306033
theorem B6494251 : Blo 2025435 6494251 := bstep (se 1 (by rfl) ⟨4870688, by rfl⟩ : syracuseStep 6494251 = 9741377) B9741377
theorem B8659001 : Blo 2025435 8659001 := bstep (se 2 (by rfl) ⟨3247125, by rfl⟩ : syracuseStep 8659001 = 6494251) B6494251
theorem B5772667 : Blo 2025435 5772667 := bstep (se 1 (by rfl) ⟨4329500, by rfl⟩ : syracuseStep 5772667 = 8659001) B8659001
theorem B7696889 : Blo 2025435 7696889 := bstep (se 2 (by rfl) ⟨2886333, by rfl⟩ : syracuseStep 7696889 = 5772667) B5772667
theorem B5131259 : Blo 2025435 5131259 := bstep (se 1 (by rfl) ⟨3848444, by rfl⟩ : syracuseStep 5131259 = 7696889) B7696889
theorem B3420839 : Blo 2025435 3420839 := bstep (se 1 (by rfl) ⟨2565629, by rfl⟩ : syracuseStep 3420839 = 5131259) B5131259
theorem B2280559 : Blo 2025435 2280559 := bstep (se 1 (by rfl) ⟨1710419, by rfl⟩ : syracuseStep 2280559 = 3420839) B3420839
theorem B3040745 : Blo 2025435 3040745 := bstep (se 2 (by rfl) ⟨1140279, by rfl⟩ : syracuseStep 3040745 = 2280559) B2280559
theorem B2027163 : Blo 2025435 2027163 := bstep (se 1 (by rfl) ⟨1520372, by rfl⟩ : syracuseStep 2027163 = 3040745) B3040745
theorem B6012197 : Blo 2025435 6012197 := bbase (se 4 (by rfl) ⟨563643, by rfl⟩ : syracuseStep 6012197 = 1127287) (by norm_num)
theorem B4008131 : Blo 2025435 4008131 := bstep (se 1 (by rfl) ⟨3006098, by rfl⟩ : syracuseStep 4008131 = 6012197) B6012197
theorem B2672087 : Blo 2025435 2672087 := bstep (se 1 (by rfl) ⟨2004065, by rfl⟩ : syracuseStep 2672087 = 4008131) B4008131
theorem B7125565 : Blo 2025435 7125565 := bstep (se 3 (by rfl) ⟨1336043, by rfl⟩ : syracuseStep 7125565 = 2672087) B2672087
theorem B9500753 : Blo 2025435 9500753 := bstep (se 2 (by rfl) ⟨3562782, by rfl⟩ : syracuseStep 9500753 = 7125565) B7125565
theorem B25335341 : Blo 2025435 25335341 := bstep (se 3 (by rfl) ⟨4750376, by rfl⟩ : syracuseStep 25335341 = 9500753) B9500753
theorem B16890227 : Blo 2025435 16890227 := bstep (se 1 (by rfl) ⟨12667670, by rfl⟩ : syracuseStep 16890227 = 25335341) B25335341
theorem B11260151 : Blo 2025435 11260151 := bstep (se 1 (by rfl) ⟨8445113, by rfl⟩ : syracuseStep 11260151 = 16890227) B16890227
theorem B7506767 : Blo 2025435 7506767 := bstep (se 1 (by rfl) ⟨5630075, by rfl⟩ : syracuseStep 7506767 = 11260151) B11260151
theorem B5004511 : Blo 2025435 5004511 := bstep (se 1 (by rfl) ⟨3753383, by rfl⟩ : syracuseStep 5004511 = 7506767) B7506767
theorem B26690725 : Blo 2025435 26690725 := bstep (se 4 (by rfl) ⟨2502255, by rfl⟩ : syracuseStep 26690725 = 5004511) B5004511
theorem B142350533 : Blo 2025435 142350533 := bstep (se 4 (by rfl) ⟨13345362, by rfl⟩ : syracuseStep 142350533 = 26690725) B26690725
theorem B94900355 : Blo 2025435 94900355 := bstep (se 1 (by rfl) ⟨71175266, by rfl⟩ : syracuseStep 94900355 = 142350533) B142350533
theorem B63266903 : Blo 2025435 63266903 := bstep (se 1 (by rfl) ⟨47450177, by rfl⟩ : syracuseStep 63266903 = 94900355) B94900355
theorem B42177935 : Blo 2025435 42177935 := bstep (se 1 (by rfl) ⟨31633451, by rfl⟩ : syracuseStep 42177935 = 63266903) B63266903
theorem B28118623 : Blo 2025435 28118623 := bstep (se 1 (by rfl) ⟨21088967, by rfl⟩ : syracuseStep 28118623 = 42177935) B42177935
theorem B37491497 : Blo 2025435 37491497 := bstep (se 2 (by rfl) ⟨14059311, by rfl⟩ : syracuseStep 37491497 = 28118623) B28118623
theorem B24994331 : Blo 2025435 24994331 := bstep (se 1 (by rfl) ⟨18745748, by rfl⟩ : syracuseStep 24994331 = 37491497) B37491497
theorem B16662887 : Blo 2025435 16662887 := bstep (se 1 (by rfl) ⟨12497165, by rfl⟩ : syracuseStep 16662887 = 24994331) B24994331
theorem B11108591 : Blo 2025435 11108591 := bstep (se 1 (by rfl) ⟨8331443, by rfl⟩ : syracuseStep 11108591 = 16662887) B16662887
theorem B7405727 : Blo 2025435 7405727 := bstep (se 1 (by rfl) ⟨5554295, by rfl⟩ : syracuseStep 7405727 = 11108591) B11108591
theorem B19748605 : Blo 2025435 19748605 := bstep (se 3 (by rfl) ⟨3702863, by rfl⟩ : syracuseStep 19748605 = 7405727) B7405727
theorem B26331473 : Blo 2025435 26331473 := bstep (se 2 (by rfl) ⟨9874302, by rfl⟩ : syracuseStep 26331473 = 19748605) B19748605
theorem B17554315 : Blo 2025435 17554315 := bstep (se 1 (by rfl) ⟨13165736, by rfl⟩ : syracuseStep 17554315 = 26331473) B26331473
theorem B23405753 : Blo 2025435 23405753 := bstep (se 2 (by rfl) ⟨8777157, by rfl⟩ : syracuseStep 23405753 = 17554315) B17554315
theorem B15603835 : Blo 2025435 15603835 := bstep (se 1 (by rfl) ⟨11702876, by rfl⟩ : syracuseStep 15603835 = 23405753) B23405753
theorem B20805113 : Blo 2025435 20805113 := bstep (se 2 (by rfl) ⟨7801917, by rfl⟩ : syracuseStep 20805113 = 15603835) B15603835
theorem B13870075 : Blo 2025435 13870075 := bstep (se 1 (by rfl) ⟨10402556, by rfl⟩ : syracuseStep 13870075 = 20805113) B20805113
theorem B18493433 : Blo 2025435 18493433 := bstep (se 2 (by rfl) ⟨6935037, by rfl⟩ : syracuseStep 18493433 = 13870075) B13870075
theorem B12328955 : Blo 2025435 12328955 := bstep (se 1 (by rfl) ⟨9246716, by rfl⟩ : syracuseStep 12328955 = 18493433) B18493433
theorem B8219303 : Blo 2025435 8219303 := bstep (se 1 (by rfl) ⟨6164477, by rfl⟩ : syracuseStep 8219303 = 12328955) B12328955
theorem B5479535 : Blo 2025435 5479535 := bstep (se 1 (by rfl) ⟨4109651, by rfl⟩ : syracuseStep 5479535 = 8219303) B8219303
theorem B3653023 : Blo 2025435 3653023 := bstep (se 1 (by rfl) ⟨2739767, by rfl⟩ : syracuseStep 3653023 = 5479535) B5479535
theorem B4870697 : Blo 2025435 4870697 := bstep (se 2 (by rfl) ⟨1826511, by rfl⟩ : syracuseStep 4870697 = 3653023) B3653023
theorem B12988525 : Blo 2025435 12988525 := bstep (se 3 (by rfl) ⟨2435348, by rfl⟩ : syracuseStep 12988525 = 4870697) B4870697
theorem B17318033 : Blo 2025435 17318033 := bstep (se 2 (by rfl) ⟨6494262, by rfl⟩ : syracuseStep 17318033 = 12988525) B12988525
theorem B11545355 : Blo 2025435 11545355 := bstep (se 1 (by rfl) ⟨8659016, by rfl⟩ : syracuseStep 11545355 = 17318033) B17318033
theorem B7696903 : Blo 2025435 7696903 := bstep (se 1 (by rfl) ⟨5772677, by rfl⟩ : syracuseStep 7696903 = 11545355) B11545355
theorem B10262537 : Blo 2025435 10262537 := bstep (se 2 (by rfl) ⟨3848451, by rfl⟩ : syracuseStep 10262537 = 7696903) B7696903
theorem B6841691 : Blo 2025435 6841691 := bstep (se 1 (by rfl) ⟨5131268, by rfl⟩ : syracuseStep 6841691 = 10262537) B10262537
theorem B4561127 : Blo 2025435 4561127 := bstep (se 1 (by rfl) ⟨3420845, by rfl⟩ : syracuseStep 4561127 = 6841691) B6841691
theorem B3040751 : Blo 2025435 3040751 := bstep (se 1 (by rfl) ⟨2280563, by rfl⟩ : syracuseStep 3040751 = 4561127) B4561127
theorem B2027167 : Blo 2025435 2027167 := bstep (se 1 (by rfl) ⟨1520375, by rfl⟩ : syracuseStep 2027167 = 3040751) B3040751
theorem B3040757 : Blo 2025435 3040757 := bbase (se 5 (by rfl) ⟨142535, by rfl⟩ : syracuseStep 3040757 = 285071) (by norm_num)
theorem B2027171 : Blo 2025435 2027171 := bstep (se 1 (by rfl) ⟨1520378, by rfl⟩ : syracuseStep 2027171 = 3040757) B3040757
theorem B9246757 : Blo 2025435 9246757 := bbase (se 4 (by rfl) ⟨866883, by rfl⟩ : syracuseStep 9246757 = 1733767) (by norm_num)
theorem B12329009 : Blo 2025435 12329009 := bstep (se 2 (by rfl) ⟨4623378, by rfl⟩ : syracuseStep 12329009 = 9246757) B9246757
theorem B8219339 : Blo 2025435 8219339 := bstep (se 1 (by rfl) ⟨6164504, by rfl⟩ : syracuseStep 8219339 = 12329009) B12329009
theorem B5479559 : Blo 2025435 5479559 := bstep (se 1 (by rfl) ⟨4109669, by rfl⟩ : syracuseStep 5479559 = 8219339) B8219339
theorem B3653039 : Blo 2025435 3653039 := bstep (se 1 (by rfl) ⟨2739779, by rfl⟩ : syracuseStep 3653039 = 5479559) B5479559
theorem B2435359 : Blo 2025435 2435359 := bstep (se 1 (by rfl) ⟨1826519, by rfl⟩ : syracuseStep 2435359 = 3653039) B3653039
theorem B3247145 : Blo 2025435 3247145 := bstep (se 2 (by rfl) ⟨1217679, by rfl⟩ : syracuseStep 3247145 = 2435359) B2435359
theorem B2164763 : Blo 2025435 2164763 := bstep (se 1 (by rfl) ⟨1623572, by rfl⟩ : syracuseStep 2164763 = 3247145) B3247145
theorem B5772701 : Blo 2025435 5772701 := bstep (se 3 (by rfl) ⟨1082381, by rfl⟩ : syracuseStep 5772701 = 2164763) B2164763
theorem B3848467 : Blo 2025435 3848467 := bstep (se 1 (by rfl) ⟨2886350, by rfl⟩ : syracuseStep 3848467 = 5772701) B5772701
theorem B5131289 : Blo 2025435 5131289 := bstep (se 2 (by rfl) ⟨1924233, by rfl⟩ : syracuseStep 5131289 = 3848467) B3848467
theorem B3420859 : Blo 2025435 3420859 := bstep (se 1 (by rfl) ⟨2565644, by rfl⟩ : syracuseStep 3420859 = 5131289) B5131289
theorem B4561145 : Blo 2025435 4561145 := bstep (se 2 (by rfl) ⟨1710429, by rfl⟩ : syracuseStep 4561145 = 3420859) B3420859
theorem B3040763 : Blo 2025435 3040763 := bstep (se 1 (by rfl) ⟨2280572, by rfl⟩ : syracuseStep 3040763 = 4561145) B4561145
theorem B2027175 : Blo 2025435 2027175 := bstep (se 1 (by rfl) ⟨1520381, by rfl⟩ : syracuseStep 2027175 = 3040763) B3040763
theorem B2280577 : Blo 2025435 2280577 := bbase (se 2 (by rfl) ⟨855216, by rfl⟩ : syracuseStep 2280577 = 1710433) (by norm_num)
theorem B3040769 : Blo 2025435 3040769 := bstep (se 2 (by rfl) ⟨1140288, by rfl⟩ : syracuseStep 3040769 = 2280577) B2280577
theorem B2027179 : Blo 2025435 2027179 := bstep (se 1 (by rfl) ⟨1520384, by rfl⟩ : syracuseStep 2027179 = 3040769) B3040769
theorem B5131309 : Blo 2025435 5131309 := bbase (se 3 (by rfl) ⟨962120, by rfl⟩ : syracuseStep 5131309 = 1924241) (by norm_num)
theorem B6841745 : Blo 2025435 6841745 := bstep (se 2 (by rfl) ⟨2565654, by rfl⟩ : syracuseStep 6841745 = 5131309) B5131309
theorem B4561163 : Blo 2025435 4561163 := bstep (se 1 (by rfl) ⟨3420872, by rfl⟩ : syracuseStep 4561163 = 6841745) B6841745
theorem B3040775 : Blo 2025435 3040775 := bstep (se 1 (by rfl) ⟨2280581, by rfl⟩ : syracuseStep 3040775 = 4561163) B4561163
theorem B2027183 : Blo 2025435 2027183 := bstep (se 1 (by rfl) ⟨1520387, by rfl⟩ : syracuseStep 2027183 = 3040775) B3040775
theorem B3040781 : Blo 2025435 3040781 := bbase (se 3 (by rfl) ⟨570146, by rfl⟩ : syracuseStep 3040781 = 1140293) (by norm_num)
theorem B2027187 : Blo 2025435 2027187 := bstep (se 1 (by rfl) ⟨1520390, by rfl⟩ : syracuseStep 2027187 = 3040781) B3040781
theorem B4561181 : Blo 2025435 4561181 := bbase (se 3 (by rfl) ⟨855221, by rfl⟩ : syracuseStep 4561181 = 1710443) (by norm_num)
theorem B3040787 : Blo 2025435 3040787 := bstep (se 1 (by rfl) ⟨2280590, by rfl⟩ : syracuseStep 3040787 = 4561181) B4561181
theorem B2027191 : Blo 2025435 2027191 := bstep (se 1 (by rfl) ⟨1520393, by rfl⟩ : syracuseStep 2027191 = 3040787) B3040787
theorem B3420893 : Blo 2025435 3420893 := bbase (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) (by norm_num)
theorem B2280595 : Blo 2025435 2280595 := bstep (se 1 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 2280595 = 3420893) B3420893
theorem B3040793 : Blo 2025435 3040793 := bstep (se 2 (by rfl) ⟨1140297, by rfl⟩ : syracuseStep 3040793 = 2280595) B2280595
theorem B2027195 : Blo 2025435 2027195 := bstep (se 1 (by rfl) ⟨1520396, by rfl⟩ : syracuseStep 2027195 = 3040793) B3040793
theorem B4109717 : Blo 2025435 4109717 := bbase (se 6 (by rfl) ⟨96321, by rfl⟩ : syracuseStep 4109717 = 192643) (by norm_num)
theorem B2739811 : Blo 2025435 2739811 := bstep (se 1 (by rfl) ⟨2054858, by rfl⟩ : syracuseStep 2739811 = 4109717) B4109717
theorem B3653081 : Blo 2025435 3653081 := bstep (se 2 (by rfl) ⟨1369905, by rfl⟩ : syracuseStep 3653081 = 2739811) B2739811
theorem B2435387 : Blo 2025435 2435387 := bstep (se 1 (by rfl) ⟨1826540, by rfl⟩ : syracuseStep 2435387 = 3653081) B3653081
theorem B6494365 : Blo 2025435 6494365 := bstep (se 3 (by rfl) ⟨1217693, by rfl⟩ : syracuseStep 6494365 = 2435387) B2435387
theorem B8659153 : Blo 2025435 8659153 := bstep (se 2 (by rfl) ⟨3247182, by rfl⟩ : syracuseStep 8659153 = 6494365) B6494365
theorem B11545537 : Blo 2025435 11545537 := bstep (se 2 (by rfl) ⟨4329576, by rfl⟩ : syracuseStep 11545537 = 8659153) B8659153
theorem B15394049 : Blo 2025435 15394049 := bstep (se 2 (by rfl) ⟨5772768, by rfl⟩ : syracuseStep 15394049 = 11545537) B11545537
theorem B10262699 : Blo 2025435 10262699 := bstep (se 1 (by rfl) ⟨7697024, by rfl⟩ : syracuseStep 10262699 = 15394049) B15394049
theorem B6841799 : Blo 2025435 6841799 := bstep (se 1 (by rfl) ⟨5131349, by rfl⟩ : syracuseStep 6841799 = 10262699) B10262699
theorem B4561199 : Blo 2025435 4561199 := bstep (se 1 (by rfl) ⟨3420899, by rfl⟩ : syracuseStep 4561199 = 6841799) B6841799
theorem B3040799 : Blo 2025435 3040799 := bstep (se 1 (by rfl) ⟨2280599, by rfl⟩ : syracuseStep 3040799 = 4561199) B4561199
theorem B2027199 : Blo 2025435 2027199 := bstep (se 1 (by rfl) ⟨1520399, by rfl⟩ : syracuseStep 2027199 = 3040799) B3040799
theorem B3040805 : Blo 2025435 3040805 := bbase (se 4 (by rfl) ⟨285075, by rfl⟩ : syracuseStep 3040805 = 570151) (by norm_num)
theorem B2027203 : Blo 2025435 2027203 := bstep (se 1 (by rfl) ⟨1520402, by rfl⟩ : syracuseStep 2027203 = 3040805) B3040805
theorem B2565685 : Blo 2025435 2565685 := bbase (se 5 (by rfl) ⟨120266, by rfl⟩ : syracuseStep 2565685 = 240533) (by norm_num)
theorem B3420913 : Blo 2025435 3420913 := bstep (se 2 (by rfl) ⟨1282842, by rfl⟩ : syracuseStep 3420913 = 2565685) B2565685
theorem B4561217 : Blo 2025435 4561217 := bstep (se 2 (by rfl) ⟨1710456, by rfl⟩ : syracuseStep 4561217 = 3420913) B3420913
theorem B3040811 : Blo 2025435 3040811 := bstep (se 1 (by rfl) ⟨2280608, by rfl⟩ : syracuseStep 3040811 = 4561217) B4561217
theorem B2027207 : Blo 2025435 2027207 := bstep (se 1 (by rfl) ⟨1520405, by rfl⟩ : syracuseStep 2027207 = 3040811) B3040811
theorem B2280613 : Blo 2025435 2280613 := bbase (se 4 (by rfl) ⟨213807, by rfl⟩ : syracuseStep 2280613 = 427615) (by norm_num)
theorem B3040817 : Blo 2025435 3040817 := bstep (se 2 (by rfl) ⟨1140306, by rfl⟩ : syracuseStep 3040817 = 2280613) B2280613
theorem B2027211 : Blo 2025435 2027211 := bstep (se 1 (by rfl) ⟨1520408, by rfl⟩ : syracuseStep 2027211 = 3040817) B3040817
theorem B19483253 : Blo 2025435 19483253 := bbase (se 5 (by rfl) ⟨913277, by rfl⟩ : syracuseStep 19483253 = 1826555) (by norm_num)
theorem B12988835 : Blo 2025435 12988835 := bstep (se 1 (by rfl) ⟨9741626, by rfl⟩ : syracuseStep 12988835 = 19483253) B19483253
theorem B8659223 : Blo 2025435 8659223 := bstep (se 1 (by rfl) ⟨6494417, by rfl⟩ : syracuseStep 8659223 = 12988835) B12988835
theorem B5772815 : Blo 2025435 5772815 := bstep (se 1 (by rfl) ⟨4329611, by rfl⟩ : syracuseStep 5772815 = 8659223) B8659223
theorem B3848543 : Blo 2025435 3848543 := bstep (se 1 (by rfl) ⟨2886407, by rfl⟩ : syracuseStep 3848543 = 5772815) B5772815
theorem B2565695 : Blo 2025435 2565695 := bstep (se 1 (by rfl) ⟨1924271, by rfl⟩ : syracuseStep 2565695 = 3848543) B3848543
theorem B6841853 : Blo 2025435 6841853 := bstep (se 3 (by rfl) ⟨1282847, by rfl⟩ : syracuseStep 6841853 = 2565695) B2565695
theorem B4561235 : Blo 2025435 4561235 := bstep (se 1 (by rfl) ⟨3420926, by rfl⟩ : syracuseStep 4561235 = 6841853) B6841853
theorem B3040823 : Blo 2025435 3040823 := bstep (se 1 (by rfl) ⟨2280617, by rfl⟩ : syracuseStep 3040823 = 4561235) B4561235
theorem B2027215 : Blo 2025435 2027215 := bstep (se 1 (by rfl) ⟨1520411, by rfl⟩ : syracuseStep 2027215 = 3040823) B3040823
theorem B3040829 : Blo 2025435 3040829 := bbase (se 3 (by rfl) ⟨570155, by rfl⟩ : syracuseStep 3040829 = 1140311) (by norm_num)
theorem B2027219 : Blo 2025435 2027219 := bstep (se 1 (by rfl) ⟨1520414, by rfl⟩ : syracuseStep 2027219 = 3040829) B3040829
theorem B4561253 : Blo 2025435 4561253 := bbase (se 4 (by rfl) ⟨427617, by rfl⟩ : syracuseStep 4561253 = 855235) (by norm_num)
theorem B3040835 : Blo 2025435 3040835 := bstep (se 1 (by rfl) ⟨2280626, by rfl⟩ : syracuseStep 3040835 = 4561253) B4561253
theorem B2027223 : Blo 2025435 2027223 := bstep (se 1 (by rfl) ⟨1520417, by rfl⟩ : syracuseStep 2027223 = 3040835) B3040835
theorem B5131421 : Blo 2025435 5131421 := bbase (se 3 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 5131421 = 1924283) (by norm_num)
theorem B3420947 : Blo 2025435 3420947 := bstep (se 1 (by rfl) ⟨2565710, by rfl⟩ : syracuseStep 3420947 = 5131421) B5131421
theorem B2280631 : Blo 2025435 2280631 := bstep (se 1 (by rfl) ⟨1710473, by rfl⟩ : syracuseStep 2280631 = 3420947) B3420947
theorem B3040841 : Blo 2025435 3040841 := bstep (se 2 (by rfl) ⟨1140315, by rfl⟩ : syracuseStep 3040841 = 2280631) B2280631
theorem B2027227 : Blo 2025435 2027227 := bstep (se 1 (by rfl) ⟨1520420, by rfl⟩ : syracuseStep 2027227 = 3040841) B3040841
theorem B3848573 : Blo 2025435 3848573 := bbase (se 3 (by rfl) ⟨721607, by rfl⟩ : syracuseStep 3848573 = 1443215) (by norm_num)
theorem B10262861 : Blo 2025435 10262861 := bstep (se 3 (by rfl) ⟨1924286, by rfl⟩ : syracuseStep 10262861 = 3848573) B3848573
theorem B6841907 : Blo 2025435 6841907 := bstep (se 1 (by rfl) ⟨5131430, by rfl⟩ : syracuseStep 6841907 = 10262861) B10262861
theorem B4561271 : Blo 2025435 4561271 := bstep (se 1 (by rfl) ⟨3420953, by rfl⟩ : syracuseStep 4561271 = 6841907) B6841907
theorem B3040847 : Blo 2025435 3040847 := bstep (se 1 (by rfl) ⟨2280635, by rfl⟩ : syracuseStep 3040847 = 4561271) B4561271
theorem B2027231 : Blo 2025435 2027231 := bstep (se 1 (by rfl) ⟨1520423, by rfl⟩ : syracuseStep 2027231 = 3040847) B3040847
theorem B3040853 : Blo 2025435 3040853 := bbase (se 8 (by rfl) ⟨17817, by rfl⟩ : syracuseStep 3040853 = 35635) (by norm_num)
theorem B2027235 : Blo 2025435 2027235 := bstep (se 1 (by rfl) ⟨1520426, by rfl⟩ : syracuseStep 2027235 = 3040853) B3040853
theorem B3082349 : Blo 2025435 3082349 := bbase (se 3 (by rfl) ⟨577940, by rfl⟩ : syracuseStep 3082349 = 1155881) (by norm_num)
theorem B2054899 : Blo 2025435 2054899 := bstep (se 1 (by rfl) ⟨1541174, by rfl⟩ : syracuseStep 2054899 = 3082349) B3082349
theorem B10959461 : Blo 2025435 10959461 := bstep (se 4 (by rfl) ⟨1027449, by rfl⟩ : syracuseStep 10959461 = 2054899) B2054899
theorem B7306307 : Blo 2025435 7306307 := bstep (se 1 (by rfl) ⟨5479730, by rfl⟩ : syracuseStep 7306307 = 10959461) B10959461
theorem B4870871 : Blo 2025435 4870871 := bstep (se 1 (by rfl) ⟨3653153, by rfl⟩ : syracuseStep 4870871 = 7306307) B7306307
theorem B3247247 : Blo 2025435 3247247 := bstep (se 1 (by rfl) ⟨2435435, by rfl⟩ : syracuseStep 3247247 = 4870871) B4870871
theorem B8659325 : Blo 2025435 8659325 := bstep (se 3 (by rfl) ⟨1623623, by rfl⟩ : syracuseStep 8659325 = 3247247) B3247247
theorem B5772883 : Blo 2025435 5772883 := bstep (se 1 (by rfl) ⟨4329662, by rfl⟩ : syracuseStep 5772883 = 8659325) B8659325
theorem B7697177 : Blo 2025435 7697177 := bstep (se 2 (by rfl) ⟨2886441, by rfl⟩ : syracuseStep 7697177 = 5772883) B5772883
theorem B5131451 : Blo 2025435 5131451 := bstep (se 1 (by rfl) ⟨3848588, by rfl⟩ : syracuseStep 5131451 = 7697177) B7697177
theorem B3420967 : Blo 2025435 3420967 := bstep (se 1 (by rfl) ⟨2565725, by rfl⟩ : syracuseStep 3420967 = 5131451) B5131451
theorem B4561289 : Blo 2025435 4561289 := bstep (se 2 (by rfl) ⟨1710483, by rfl⟩ : syracuseStep 4561289 = 3420967) B3420967
theorem B3040859 : Blo 2025435 3040859 := bstep (se 1 (by rfl) ⟨2280644, by rfl⟩ : syracuseStep 3040859 = 4561289) B4561289
theorem B2027239 : Blo 2025435 2027239 := bstep (se 1 (by rfl) ⟨1520429, by rfl⟩ : syracuseStep 2027239 = 3040859) B3040859
theorem B2280649 : Blo 2025435 2280649 := bbase (se 2 (by rfl) ⟨855243, by rfl⟩ : syracuseStep 2280649 = 1710487) (by norm_num)
theorem B3040865 : Blo 2025435 3040865 := bstep (se 2 (by rfl) ⟨1140324, by rfl⟩ : syracuseStep 3040865 = 2280649) B2280649
theorem B2027243 : Blo 2025435 2027243 := bstep (se 1 (by rfl) ⟨1520432, by rfl⟩ : syracuseStep 2027243 = 3040865) B3040865
theorem B23406677 : Blo 2025435 23406677 := bbase (se 8 (by rfl) ⟨137148, by rfl⟩ : syracuseStep 23406677 = 274297) (by norm_num)
theorem B15604451 : Blo 2025435 15604451 := bstep (se 1 (by rfl) ⟨11703338, by rfl⟩ : syracuseStep 15604451 = 23406677) B23406677
theorem B10402967 : Blo 2025435 10402967 := bstep (se 1 (by rfl) ⟨7802225, by rfl⟩ : syracuseStep 10402967 = 15604451) B15604451
theorem B6935311 : Blo 2025435 6935311 := bstep (se 1 (by rfl) ⟨5201483, by rfl⟩ : syracuseStep 6935311 = 10402967) B10402967
theorem B9247081 : Blo 2025435 9247081 := bstep (se 2 (by rfl) ⟨3467655, by rfl⟩ : syracuseStep 9247081 = 6935311) B6935311
theorem B12329441 : Blo 2025435 12329441 := bstep (se 2 (by rfl) ⟨4623540, by rfl⟩ : syracuseStep 12329441 = 9247081) B9247081
theorem B8219627 : Blo 2025435 8219627 := bstep (se 1 (by rfl) ⟨6164720, by rfl⟩ : syracuseStep 8219627 = 12329441) B12329441
theorem B5479751 : Blo 2025435 5479751 := bstep (se 1 (by rfl) ⟨4109813, by rfl⟩ : syracuseStep 5479751 = 8219627) B8219627
theorem B14612669 : Blo 2025435 14612669 := bstep (se 3 (by rfl) ⟨2739875, by rfl⟩ : syracuseStep 14612669 = 5479751) B5479751
theorem B9741779 : Blo 2025435 9741779 := bstep (se 1 (by rfl) ⟨7306334, by rfl⟩ : syracuseStep 9741779 = 14612669) B14612669
theorem B6494519 : Blo 2025435 6494519 := bstep (se 1 (by rfl) ⟨4870889, by rfl⟩ : syracuseStep 6494519 = 9741779) B9741779
theorem B17318717 : Blo 2025435 17318717 := bstep (se 3 (by rfl) ⟨3247259, by rfl⟩ : syracuseStep 17318717 = 6494519) B6494519
theorem B11545811 : Blo 2025435 11545811 := bstep (se 1 (by rfl) ⟨8659358, by rfl⟩ : syracuseStep 11545811 = 17318717) B17318717
theorem B7697207 : Blo 2025435 7697207 := bstep (se 1 (by rfl) ⟨5772905, by rfl⟩ : syracuseStep 7697207 = 11545811) B11545811
theorem B5131471 : Blo 2025435 5131471 := bstep (se 1 (by rfl) ⟨3848603, by rfl⟩ : syracuseStep 5131471 = 7697207) B7697207
theorem B6841961 : Blo 2025435 6841961 := bstep (se 2 (by rfl) ⟨2565735, by rfl⟩ : syracuseStep 6841961 = 5131471) B5131471
theorem B4561307 : Blo 2025435 4561307 := bstep (se 1 (by rfl) ⟨3420980, by rfl⟩ : syracuseStep 4561307 = 6841961) B6841961
theorem B3040871 : Blo 2025435 3040871 := bstep (se 1 (by rfl) ⟨2280653, by rfl⟩ : syracuseStep 3040871 = 4561307) B4561307
theorem B2027247 : Blo 2025435 2027247 := bstep (se 1 (by rfl) ⟨1520435, by rfl⟩ : syracuseStep 2027247 = 3040871) B3040871
theorem B3040877 : Blo 2025435 3040877 := bbase (se 3 (by rfl) ⟨570164, by rfl⟩ : syracuseStep 3040877 = 1140329) (by norm_num)
theorem B2027251 : Blo 2025435 2027251 := bstep (se 1 (by rfl) ⟨1520438, by rfl⟩ : syracuseStep 2027251 = 3040877) B3040877
theorem B4561325 : Blo 2025435 4561325 := bbase (se 3 (by rfl) ⟨855248, by rfl⟩ : syracuseStep 4561325 = 1710497) (by norm_num)
theorem B3040883 : Blo 2025435 3040883 := bstep (se 1 (by rfl) ⟨2280662, by rfl⟩ : syracuseStep 3040883 = 4561325) B4561325
theorem B2027255 : Blo 2025435 2027255 := bstep (se 1 (by rfl) ⟨1520441, by rfl⟩ : syracuseStep 2027255 = 3040883) B3040883
theorem B2164853 : Blo 2025435 2164853 := bbase (se 5 (by rfl) ⟨101477, by rfl⟩ : syracuseStep 2164853 = 202955) (by norm_num)
theorem B5772941 : Blo 2025435 5772941 := bstep (se 3 (by rfl) ⟨1082426, by rfl⟩ : syracuseStep 5772941 = 2164853) B2164853
theorem B3848627 : Blo 2025435 3848627 := bstep (se 1 (by rfl) ⟨2886470, by rfl⟩ : syracuseStep 3848627 = 5772941) B5772941
theorem B2565751 : Blo 2025435 2565751 := bstep (se 1 (by rfl) ⟨1924313, by rfl⟩ : syracuseStep 2565751 = 3848627) B3848627
theorem B3421001 : Blo 2025435 3421001 := bstep (se 2 (by rfl) ⟨1282875, by rfl⟩ : syracuseStep 3421001 = 2565751) B2565751
theorem B2280667 : Blo 2025435 2280667 := bstep (se 1 (by rfl) ⟨1710500, by rfl⟩ : syracuseStep 2280667 = 3421001) B3421001
theorem B3040889 : Blo 2025435 3040889 := bstep (se 2 (by rfl) ⟨1140333, by rfl⟩ : syracuseStep 3040889 = 2280667) B2280667
theorem B2027259 : Blo 2025435 2027259 := bstep (se 1 (by rfl) ⟨1520444, by rfl⟩ : syracuseStep 2027259 = 3040889) B3040889
theorem B3291589 : Blo 2025435 3291589 := bbase (se 4 (by rfl) ⟨308586, by rfl⟩ : syracuseStep 3291589 = 617173) (by norm_num)
theorem B4388785 : Blo 2025435 4388785 := bstep (se 2 (by rfl) ⟨1645794, by rfl⟩ : syracuseStep 4388785 = 3291589) B3291589
theorem B93627413 : Blo 2025435 93627413 := bstep (se 6 (by rfl) ⟨2194392, by rfl⟩ : syracuseStep 93627413 = 4388785) B4388785
theorem B62418275 : Blo 2025435 62418275 := bstep (se 1 (by rfl) ⟨46813706, by rfl⟩ : syracuseStep 62418275 = 93627413) B93627413
theorem B41612183 : Blo 2025435 41612183 := bstep (se 1 (by rfl) ⟨31209137, by rfl⟩ : syracuseStep 41612183 = 62418275) B62418275
theorem B27741455 : Blo 2025435 27741455 := bstep (se 1 (by rfl) ⟨20806091, by rfl⟩ : syracuseStep 27741455 = 41612183) B41612183
theorem B18494303 : Blo 2025435 18494303 := bstep (se 1 (by rfl) ⟨13870727, by rfl⟩ : syracuseStep 18494303 = 27741455) B27741455
theorem B49318141 : Blo 2025435 49318141 := bstep (se 3 (by rfl) ⟨9247151, by rfl⟩ : syracuseStep 49318141 = 18494303) B18494303
theorem B65757521 : Blo 2025435 65757521 := bstep (se 2 (by rfl) ⟨24659070, by rfl⟩ : syracuseStep 65757521 = 49318141) B49318141
theorem B43838347 : Blo 2025435 43838347 := bstep (se 1 (by rfl) ⟨32878760, by rfl⟩ : syracuseStep 43838347 = 65757521) B65757521
theorem B58451129 : Blo 2025435 58451129 := bstep (se 2 (by rfl) ⟨21919173, by rfl⟩ : syracuseStep 58451129 = 43838347) B43838347
theorem B38967419 : Blo 2025435 38967419 := bstep (se 1 (by rfl) ⟨29225564, by rfl⟩ : syracuseStep 38967419 = 58451129) B58451129
theorem B25978279 : Blo 2025435 25978279 := bstep (se 1 (by rfl) ⟨19483709, by rfl⟩ : syracuseStep 25978279 = 38967419) B38967419
theorem B34637705 : Blo 2025435 34637705 := bstep (se 2 (by rfl) ⟨12989139, by rfl⟩ : syracuseStep 34637705 = 25978279) B25978279
theorem B23091803 : Blo 2025435 23091803 := bstep (se 1 (by rfl) ⟨17318852, by rfl⟩ : syracuseStep 23091803 = 34637705) B34637705
theorem B15394535 : Blo 2025435 15394535 := bstep (se 1 (by rfl) ⟨11545901, by rfl⟩ : syracuseStep 15394535 = 23091803) B23091803
theorem B10263023 : Blo 2025435 10263023 := bstep (se 1 (by rfl) ⟨7697267, by rfl⟩ : syracuseStep 10263023 = 15394535) B15394535
theorem B6842015 : Blo 2025435 6842015 := bstep (se 1 (by rfl) ⟨5131511, by rfl⟩ : syracuseStep 6842015 = 10263023) B10263023
theorem B4561343 : Blo 2025435 4561343 := bstep (se 1 (by rfl) ⟨3421007, by rfl⟩ : syracuseStep 4561343 = 6842015) B6842015
theorem B3040895 : Blo 2025435 3040895 := bstep (se 1 (by rfl) ⟨2280671, by rfl⟩ : syracuseStep 3040895 = 4561343) B4561343
theorem B2027263 : Blo 2025435 2027263 := bstep (se 1 (by rfl) ⟨1520447, by rfl⟩ : syracuseStep 2027263 = 3040895) B3040895
theorem B3040901 : Blo 2025435 3040901 := bbase (se 4 (by rfl) ⟨285084, by rfl⟩ : syracuseStep 3040901 = 570169) (by norm_num)
theorem B2027267 : Blo 2025435 2027267 := bstep (se 1 (by rfl) ⟨1520450, by rfl⟩ : syracuseStep 2027267 = 3040901) B3040901
theorem B3421021 : Blo 2025435 3421021 := bbase (se 3 (by rfl) ⟨641441, by rfl⟩ : syracuseStep 3421021 = 1282883) (by norm_num)
theorem B4561361 : Blo 2025435 4561361 := bstep (se 2 (by rfl) ⟨1710510, by rfl⟩ : syracuseStep 4561361 = 3421021) B3421021
theorem B3040907 : Blo 2025435 3040907 := bstep (se 1 (by rfl) ⟨2280680, by rfl⟩ : syracuseStep 3040907 = 4561361) B4561361
theorem B2027271 : Blo 2025435 2027271 := bstep (se 1 (by rfl) ⟨1520453, by rfl⟩ : syracuseStep 2027271 = 3040907) B3040907
theorem B2280685 : Blo 2025435 2280685 := bbase (se 3 (by rfl) ⟨427628, by rfl⟩ : syracuseStep 2280685 = 855257) (by norm_num)
theorem B3040913 : Blo 2025435 3040913 := bstep (se 2 (by rfl) ⟨1140342, by rfl⟩ : syracuseStep 3040913 = 2280685) B2280685
theorem B2027275 : Blo 2025435 2027275 := bstep (se 1 (by rfl) ⟨1520456, by rfl⟩ : syracuseStep 2027275 = 3040913) B3040913
theorem B6842069 : Blo 2025435 6842069 := bbase (se 7 (by rfl) ⟨80180, by rfl⟩ : syracuseStep 6842069 = 160361) (by norm_num)
theorem B4561379 : Blo 2025435 4561379 := bstep (se 1 (by rfl) ⟨3421034, by rfl⟩ : syracuseStep 4561379 = 6842069) B6842069
theorem B3040919 : Blo 2025435 3040919 := bstep (se 1 (by rfl) ⟨2280689, by rfl⟩ : syracuseStep 3040919 = 4561379) B4561379
theorem B2027279 : Blo 2025435 2027279 := bstep (se 1 (by rfl) ⟨1520459, by rfl⟩ : syracuseStep 2027279 = 3040919) B3040919
theorem B3040925 : Blo 2025435 3040925 := bbase (se 3 (by rfl) ⟨570173, by rfl⟩ : syracuseStep 3040925 = 1140347) (by norm_num)
theorem B2027283 : Blo 2025435 2027283 := bstep (se 1 (by rfl) ⟨1520462, by rfl⟩ : syracuseStep 2027283 = 3040925) B3040925
theorem B4561397 : Blo 2025435 4561397 := bbase (se 5 (by rfl) ⟨213815, by rfl⟩ : syracuseStep 4561397 = 427631) (by norm_num)
theorem B3040931 : Blo 2025435 3040931 := bstep (se 1 (by rfl) ⟨2280698, by rfl⟩ : syracuseStep 3040931 = 4561397) B4561397
theorem B2027287 : Blo 2025435 2027287 := bstep (se 1 (by rfl) ⟨1520465, by rfl⟩ : syracuseStep 2027287 = 3040931) B3040931
theorem B27741845 : Blo 2025435 27741845 := bbase (se 6 (by rfl) ⟨650199, by rfl⟩ : syracuseStep 27741845 = 1300399) (by norm_num)
theorem B18494563 : Blo 2025435 18494563 := bstep (se 1 (by rfl) ⟨13870922, by rfl⟩ : syracuseStep 18494563 = 27741845) B27741845
theorem B24659417 : Blo 2025435 24659417 := bstep (se 2 (by rfl) ⟨9247281, by rfl⟩ : syracuseStep 24659417 = 18494563) B18494563
theorem B16439611 : Blo 2025435 16439611 := bstep (se 1 (by rfl) ⟨12329708, by rfl⟩ : syracuseStep 16439611 = 24659417) B24659417
theorem B21919481 : Blo 2025435 21919481 := bstep (se 2 (by rfl) ⟨8219805, by rfl⟩ : syracuseStep 21919481 = 16439611) B16439611
theorem B14612987 : Blo 2025435 14612987 := bstep (se 1 (by rfl) ⟨10959740, by rfl⟩ : syracuseStep 14612987 = 21919481) B21919481
theorem B38967965 : Blo 2025435 38967965 := bstep (se 3 (by rfl) ⟨7306493, by rfl⟩ : syracuseStep 38967965 = 14612987) B14612987
theorem B25978643 : Blo 2025435 25978643 := bstep (se 1 (by rfl) ⟨19483982, by rfl⟩ : syracuseStep 25978643 = 38967965) B38967965
theorem B17319095 : Blo 2025435 17319095 := bstep (se 1 (by rfl) ⟨12989321, by rfl⟩ : syracuseStep 17319095 = 25978643) B25978643
theorem B11546063 : Blo 2025435 11546063 := bstep (se 1 (by rfl) ⟨8659547, by rfl⟩ : syracuseStep 11546063 = 17319095) B17319095
theorem B7697375 : Blo 2025435 7697375 := bstep (se 1 (by rfl) ⟨5773031, by rfl⟩ : syracuseStep 7697375 = 11546063) B11546063
theorem B5131583 : Blo 2025435 5131583 := bstep (se 1 (by rfl) ⟨3848687, by rfl⟩ : syracuseStep 5131583 = 7697375) B7697375
theorem B3421055 : Blo 2025435 3421055 := bstep (se 1 (by rfl) ⟨2565791, by rfl⟩ : syracuseStep 3421055 = 5131583) B5131583
theorem B2280703 : Blo 2025435 2280703 := bstep (se 1 (by rfl) ⟨1710527, by rfl⟩ : syracuseStep 2280703 = 3421055) B3421055
theorem B3040937 : Blo 2025435 3040937 := bstep (se 2 (by rfl) ⟨1140351, by rfl⟩ : syracuseStep 3040937 = 2280703) B2280703
theorem B2027291 : Blo 2025435 2027291 := bstep (se 1 (by rfl) ⟨1520468, by rfl⟩ : syracuseStep 2027291 = 3040937) B3040937
theorem B6164869 : Blo 2025435 6164869 := bbase (se 4 (by rfl) ⟨577956, by rfl⟩ : syracuseStep 6164869 = 1155913) (by norm_num)
theorem B8219825 : Blo 2025435 8219825 := bstep (se 2 (by rfl) ⟨3082434, by rfl⟩ : syracuseStep 8219825 = 6164869) B6164869
theorem B5479883 : Blo 2025435 5479883 := bstep (se 1 (by rfl) ⟨4109912, by rfl⟩ : syracuseStep 5479883 = 8219825) B8219825
theorem B3653255 : Blo 2025435 3653255 := bstep (se 1 (by rfl) ⟨2739941, by rfl⟩ : syracuseStep 3653255 = 5479883) B5479883
theorem B2435503 : Blo 2025435 2435503 := bstep (se 1 (by rfl) ⟨1826627, by rfl⟩ : syracuseStep 2435503 = 3653255) B3653255
theorem B3247337 : Blo 2025435 3247337 := bstep (se 2 (by rfl) ⟨1217751, by rfl⟩ : syracuseStep 3247337 = 2435503) B2435503
theorem B2164891 : Blo 2025435 2164891 := bstep (se 1 (by rfl) ⟨1623668, by rfl⟩ : syracuseStep 2164891 = 3247337) B3247337
theorem B2886521 : Blo 2025435 2886521 := bstep (se 2 (by rfl) ⟨1082445, by rfl⟩ : syracuseStep 2886521 = 2164891) B2164891
theorem B7697389 : Blo 2025435 7697389 := bstep (se 3 (by rfl) ⟨1443260, by rfl⟩ : syracuseStep 7697389 = 2886521) B2886521
theorem B10263185 : Blo 2025435 10263185 := bstep (se 2 (by rfl) ⟨3848694, by rfl⟩ : syracuseStep 10263185 = 7697389) B7697389
theorem B6842123 : Blo 2025435 6842123 := bstep (se 1 (by rfl) ⟨5131592, by rfl⟩ : syracuseStep 6842123 = 10263185) B10263185
theorem B4561415 : Blo 2025435 4561415 := bstep (se 1 (by rfl) ⟨3421061, by rfl⟩ : syracuseStep 4561415 = 6842123) B6842123
theorem B3040943 : Blo 2025435 3040943 := bstep (se 1 (by rfl) ⟨2280707, by rfl⟩ : syracuseStep 3040943 = 4561415) B4561415
theorem B2027295 : Blo 2025435 2027295 := bstep (se 1 (by rfl) ⟨1520471, by rfl⟩ : syracuseStep 2027295 = 3040943) B3040943
theorem B3040949 : Blo 2025435 3040949 := bbase (se 5 (by rfl) ⟨142544, by rfl⟩ : syracuseStep 3040949 = 285089) (by norm_num)
theorem B2027299 : Blo 2025435 2027299 := bstep (se 1 (by rfl) ⟨1520474, by rfl⟩ : syracuseStep 2027299 = 3040949) B3040949
theorem B5131613 : Blo 2025435 5131613 := bbase (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) (by norm_num)
theorem B3421075 : Blo 2025435 3421075 := bstep (se 1 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 3421075 = 5131613) B5131613
theorem B4561433 : Blo 2025435 4561433 := bstep (se 2 (by rfl) ⟨1710537, by rfl⟩ : syracuseStep 4561433 = 3421075) B3421075
theorem B3040955 : Blo 2025435 3040955 := bstep (se 1 (by rfl) ⟨2280716, by rfl⟩ : syracuseStep 3040955 = 4561433) B4561433
theorem B2027303 : Blo 2025435 2027303 := bstep (se 1 (by rfl) ⟨1520477, by rfl⟩ : syracuseStep 2027303 = 3040955) B3040955
theorem B2280721 : Blo 2025435 2280721 := bbase (se 2 (by rfl) ⟨855270, by rfl⟩ : syracuseStep 2280721 = 1710541) (by norm_num)
theorem B3040961 : Blo 2025435 3040961 := bstep (se 2 (by rfl) ⟨1140360, by rfl⟩ : syracuseStep 3040961 = 2280721) B2280721
theorem B2027307 : Blo 2025435 2027307 := bstep (se 1 (by rfl) ⟨1520480, by rfl⟩ : syracuseStep 2027307 = 3040961) B3040961
theorem B3848725 : Blo 2025435 3848725 := bbase (se 6 (by rfl) ⟨90204, by rfl⟩ : syracuseStep 3848725 = 180409) (by norm_num)
theorem B5131633 : Blo 2025435 5131633 := bstep (se 2 (by rfl) ⟨1924362, by rfl⟩ : syracuseStep 5131633 = 3848725) B3848725
theorem B6842177 : Blo 2025435 6842177 := bstep (se 2 (by rfl) ⟨2565816, by rfl⟩ : syracuseStep 6842177 = 5131633) B5131633
theorem B4561451 : Blo 2025435 4561451 := bstep (se 1 (by rfl) ⟨3421088, by rfl⟩ : syracuseStep 4561451 = 6842177) B6842177
theorem B3040967 : Blo 2025435 3040967 := bstep (se 1 (by rfl) ⟨2280725, by rfl⟩ : syracuseStep 3040967 = 4561451) B4561451
theorem B2027311 : Blo 2025435 2027311 := bstep (se 1 (by rfl) ⟨1520483, by rfl⟩ : syracuseStep 2027311 = 3040967) B3040967
theorem B3040973 : Blo 2025435 3040973 := bbase (se 3 (by rfl) ⟨570182, by rfl⟩ : syracuseStep 3040973 = 1140365) (by norm_num)
theorem B2027315 : Blo 2025435 2027315 := bstep (se 1 (by rfl) ⟨1520486, by rfl⟩ : syracuseStep 2027315 = 3040973) B3040973
theorem B4561469 : Blo 2025435 4561469 := bbase (se 3 (by rfl) ⟨855275, by rfl⟩ : syracuseStep 4561469 = 1710551) (by norm_num)
theorem B3040979 : Blo 2025435 3040979 := bstep (se 1 (by rfl) ⟨2280734, by rfl⟩ : syracuseStep 3040979 = 4561469) B4561469
theorem B2027319 : Blo 2025435 2027319 := bstep (se 1 (by rfl) ⟨1520489, by rfl⟩ : syracuseStep 2027319 = 3040979) B3040979
theorem B3421109 : Blo 2025435 3421109 := bbase (se 5 (by rfl) ⟨160364, by rfl⟩ : syracuseStep 3421109 = 320729) (by norm_num)
theorem B2280739 : Blo 2025435 2280739 := bstep (se 1 (by rfl) ⟨1710554, by rfl⟩ : syracuseStep 2280739 = 3421109) B3421109
theorem B3040985 : Blo 2025435 3040985 := bstep (se 2 (by rfl) ⟨1140369, by rfl⟩ : syracuseStep 3040985 = 2280739) B2280739
theorem B2027323 : Blo 2025435 2027323 := bstep (se 1 (by rfl) ⟨1520492, by rfl⟩ : syracuseStep 2027323 = 3040985) B3040985
theorem B2164925 : Blo 2025435 2164925 := bbase (se 3 (by rfl) ⟨405923, by rfl⟩ : syracuseStep 2164925 = 811847) (by norm_num)
theorem B5773133 : Blo 2025435 5773133 := bstep (se 3 (by rfl) ⟨1082462, by rfl⟩ : syracuseStep 5773133 = 2164925) B2164925
theorem B15395021 : Blo 2025435 15395021 := bstep (se 3 (by rfl) ⟨2886566, by rfl⟩ : syracuseStep 15395021 = 5773133) B5773133
theorem B10263347 : Blo 2025435 10263347 := bstep (se 1 (by rfl) ⟨7697510, by rfl⟩ : syracuseStep 10263347 = 15395021) B15395021
theorem B6842231 : Blo 2025435 6842231 := bstep (se 1 (by rfl) ⟨5131673, by rfl⟩ : syracuseStep 6842231 = 10263347) B10263347
theorem B4561487 : Blo 2025435 4561487 := bstep (se 1 (by rfl) ⟨3421115, by rfl⟩ : syracuseStep 4561487 = 6842231) B6842231
theorem B3040991 : Blo 2025435 3040991 := bstep (se 1 (by rfl) ⟨2280743, by rfl⟩ : syracuseStep 3040991 = 4561487) B4561487
theorem B2027327 : Blo 2025435 2027327 := bstep (se 1 (by rfl) ⟨1520495, by rfl⟩ : syracuseStep 2027327 = 3040991) B3040991
theorem B3040997 : Blo 2025435 3040997 := bbase (se 4 (by rfl) ⟨285093, by rfl⟩ : syracuseStep 3040997 = 570187) (by norm_num)
theorem B2027331 : Blo 2025435 2027331 := bstep (se 1 (by rfl) ⟨1520498, by rfl⟩ : syracuseStep 2027331 = 3040997) B3040997
theorem B5773157 : Blo 2025435 5773157 := bbase (se 4 (by rfl) ⟨541233, by rfl⟩ : syracuseStep 5773157 = 1082467) (by norm_num)
theorem B3848771 : Blo 2025435 3848771 := bstep (se 1 (by rfl) ⟨2886578, by rfl⟩ : syracuseStep 3848771 = 5773157) B5773157
theorem B2565847 : Blo 2025435 2565847 := bstep (se 1 (by rfl) ⟨1924385, by rfl⟩ : syracuseStep 2565847 = 3848771) B3848771
theorem B3421129 : Blo 2025435 3421129 := bstep (se 2 (by rfl) ⟨1282923, by rfl⟩ : syracuseStep 3421129 = 2565847) B2565847
theorem B4561505 : Blo 2025435 4561505 := bstep (se 2 (by rfl) ⟨1710564, by rfl⟩ : syracuseStep 4561505 = 3421129) B3421129
theorem B3041003 : Blo 2025435 3041003 := bstep (se 1 (by rfl) ⟨2280752, by rfl⟩ : syracuseStep 3041003 = 4561505) B4561505
theorem B2027335 : Blo 2025435 2027335 := bstep (se 1 (by rfl) ⟨1520501, by rfl⟩ : syracuseStep 2027335 = 3041003) B3041003
theorem B2280757 : Blo 2025435 2280757 := bbase (se 5 (by rfl) ⟨106910, by rfl⟩ : syracuseStep 2280757 = 213821) (by norm_num)
theorem B3041009 : Blo 2025435 3041009 := bstep (se 2 (by rfl) ⟨1140378, by rfl⟩ : syracuseStep 3041009 = 2280757) B2280757
theorem B2027339 : Blo 2025435 2027339 := bstep (se 1 (by rfl) ⟨1520504, by rfl⟩ : syracuseStep 2027339 = 3041009) B3041009
theorem B2565857 : Blo 2025435 2565857 := bbase (se 2 (by rfl) ⟨962196, by rfl⟩ : syracuseStep 2565857 = 1924393) (by norm_num)
theorem B6842285 : Blo 2025435 6842285 := bstep (se 3 (by rfl) ⟨1282928, by rfl⟩ : syracuseStep 6842285 = 2565857) B2565857
theorem B4561523 : Blo 2025435 4561523 := bstep (se 1 (by rfl) ⟨3421142, by rfl⟩ : syracuseStep 4561523 = 6842285) B6842285
theorem B3041015 : Blo 2025435 3041015 := bstep (se 1 (by rfl) ⟨2280761, by rfl⟩ : syracuseStep 3041015 = 4561523) B4561523
theorem B2027343 : Blo 2025435 2027343 := bstep (se 1 (by rfl) ⟨1520507, by rfl⟩ : syracuseStep 2027343 = 3041015) B3041015
theorem B3041021 : Blo 2025435 3041021 := bbase (se 3 (by rfl) ⟨570191, by rfl⟩ : syracuseStep 3041021 = 1140383) (by norm_num)
theorem B2027347 : Blo 2025435 2027347 := bstep (se 1 (by rfl) ⟨1520510, by rfl⟩ : syracuseStep 2027347 = 3041021) B3041021
theorem B4561541 : Blo 2025435 4561541 := bbase (se 4 (by rfl) ⟨427644, by rfl⟩ : syracuseStep 4561541 = 855289) (by norm_num)
theorem B3041027 : Blo 2025435 3041027 := bstep (se 1 (by rfl) ⟨2280770, by rfl⟩ : syracuseStep 3041027 = 4561541) B4561541
theorem B2027351 : Blo 2025435 2027351 := bstep (se 1 (by rfl) ⟨1520513, by rfl⟩ : syracuseStep 2027351 = 3041027) B3041027
theorem B2055017 : Blo 2025435 2055017 := bbase (se 2 (by rfl) ⟨770631, by rfl⟩ : syracuseStep 2055017 = 1541263) (by norm_num)
theorem B5480045 : Blo 2025435 5480045 := bstep (se 3 (by rfl) ⟨1027508, by rfl⟩ : syracuseStep 5480045 = 2055017) B2055017
theorem B3653363 : Blo 2025435 3653363 := bstep (se 1 (by rfl) ⟨2740022, by rfl⟩ : syracuseStep 3653363 = 5480045) B5480045
theorem B9742301 : Blo 2025435 9742301 := bstep (se 3 (by rfl) ⟨1826681, by rfl⟩ : syracuseStep 9742301 = 3653363) B3653363
theorem B6494867 : Blo 2025435 6494867 := bstep (se 1 (by rfl) ⟨4871150, by rfl⟩ : syracuseStep 6494867 = 9742301) B9742301
theorem B4329911 : Blo 2025435 4329911 := bstep (se 1 (by rfl) ⟨3247433, by rfl⟩ : syracuseStep 4329911 = 6494867) B6494867
theorem B2886607 : Blo 2025435 2886607 := bstep (se 1 (by rfl) ⟨2164955, by rfl⟩ : syracuseStep 2886607 = 4329911) B4329911
theorem B3848809 : Blo 2025435 3848809 := bstep (se 2 (by rfl) ⟨1443303, by rfl⟩ : syracuseStep 3848809 = 2886607) B2886607
theorem B5131745 : Blo 2025435 5131745 := bstep (se 2 (by rfl) ⟨1924404, by rfl⟩ : syracuseStep 5131745 = 3848809) B3848809
theorem B3421163 : Blo 2025435 3421163 := bstep (se 1 (by rfl) ⟨2565872, by rfl⟩ : syracuseStep 3421163 = 5131745) B5131745
theorem B2280775 : Blo 2025435 2280775 := bstep (se 1 (by rfl) ⟨1710581, by rfl⟩ : syracuseStep 2280775 = 3421163) B3421163
theorem B3041033 : Blo 2025435 3041033 := bstep (se 2 (by rfl) ⟨1140387, by rfl⟩ : syracuseStep 3041033 = 2280775) B2280775
theorem B2027355 : Blo 2025435 2027355 := bstep (se 1 (by rfl) ⟨1520516, by rfl⟩ : syracuseStep 2027355 = 3041033) B3041033
theorem B10263509 : Blo 2025435 10263509 := bbase (se 7 (by rfl) ⟨120275, by rfl⟩ : syracuseStep 10263509 = 240551) (by norm_num)
theorem B6842339 : Blo 2025435 6842339 := bstep (se 1 (by rfl) ⟨5131754, by rfl⟩ : syracuseStep 6842339 = 10263509) B10263509
theorem B4561559 : Blo 2025435 4561559 := bstep (se 1 (by rfl) ⟨3421169, by rfl⟩ : syracuseStep 4561559 = 6842339) B6842339
theorem B3041039 : Blo 2025435 3041039 := bstep (se 1 (by rfl) ⟨2280779, by rfl⟩ : syracuseStep 3041039 = 4561559) B4561559
theorem B2027359 : Blo 2025435 2027359 := bstep (se 1 (by rfl) ⟨1520519, by rfl⟩ : syracuseStep 2027359 = 3041039) B3041039
theorem B3041045 : Blo 2025435 3041045 := bbase (se 6 (by rfl) ⟨71274, by rfl⟩ : syracuseStep 3041045 = 142549) (by norm_num)
theorem B2027363 : Blo 2025435 2027363 := bstep (se 1 (by rfl) ⟨1520522, by rfl⟩ : syracuseStep 2027363 = 3041045) B3041045
theorem B5417621 : Blo 2025435 5417621 := bbase (se 6 (by rfl) ⟨126975, by rfl⟩ : syracuseStep 5417621 = 253951) (by norm_num)
theorem B3611747 : Blo 2025435 3611747 := bstep (se 1 (by rfl) ⟨2708810, by rfl⟩ : syracuseStep 3611747 = 5417621) B5417621
theorem B9631325 : Blo 2025435 9631325 := bstep (se 3 (by rfl) ⟨1805873, by rfl⟩ : syracuseStep 9631325 = 3611747) B3611747
theorem B25683533 : Blo 2025435 25683533 := bstep (se 3 (by rfl) ⟨4815662, by rfl⟩ : syracuseStep 25683533 = 9631325) B9631325
theorem B17122355 : Blo 2025435 17122355 := bstep (se 1 (by rfl) ⟨12841766, by rfl⟩ : syracuseStep 17122355 = 25683533) B25683533
theorem B11414903 : Blo 2025435 11414903 := bstep (se 1 (by rfl) ⟨8561177, by rfl⟩ : syracuseStep 11414903 = 17122355) B17122355
theorem B30439741 : Blo 2025435 30439741 := bstep (se 3 (by rfl) ⟨5707451, by rfl⟩ : syracuseStep 30439741 = 11414903) B11414903
theorem B40586321 : Blo 2025435 40586321 := bstep (se 2 (by rfl) ⟨15219870, by rfl⟩ : syracuseStep 40586321 = 30439741) B30439741
theorem B27057547 : Blo 2025435 27057547 := bstep (se 1 (by rfl) ⟨20293160, by rfl⟩ : syracuseStep 27057547 = 40586321) B40586321
theorem B144306917 : Blo 2025435 144306917 := bstep (se 4 (by rfl) ⟨13528773, by rfl⟩ : syracuseStep 144306917 = 27057547) B27057547
theorem B96204611 : Blo 2025435 96204611 := bstep (se 1 (by rfl) ⟨72153458, by rfl⟩ : syracuseStep 96204611 = 144306917) B144306917
theorem B64136407 : Blo 2025435 64136407 := bstep (se 1 (by rfl) ⟨48102305, by rfl⟩ : syracuseStep 64136407 = 96204611) B96204611
theorem B85515209 : Blo 2025435 85515209 := bstep (se 2 (by rfl) ⟨32068203, by rfl⟩ : syracuseStep 85515209 = 64136407) B64136407
theorem B57010139 : Blo 2025435 57010139 := bstep (se 1 (by rfl) ⟨42757604, by rfl⟩ : syracuseStep 57010139 = 85515209) B85515209
theorem B38006759 : Blo 2025435 38006759 := bstep (se 1 (by rfl) ⟨28505069, by rfl⟩ : syracuseStep 38006759 = 57010139) B57010139
theorem B101351357 : Blo 2025435 101351357 := bstep (se 3 (by rfl) ⟨19003379, by rfl⟩ : syracuseStep 101351357 = 38006759) B38006759
theorem B67567571 : Blo 2025435 67567571 := bstep (se 1 (by rfl) ⟨50675678, by rfl⟩ : syracuseStep 67567571 = 101351357) B101351357
theorem B45045047 : Blo 2025435 45045047 := bstep (se 1 (by rfl) ⟨33783785, by rfl⟩ : syracuseStep 45045047 = 67567571) B67567571
theorem B30030031 : Blo 2025435 30030031 := bstep (se 1 (by rfl) ⟨22522523, by rfl⟩ : syracuseStep 30030031 = 45045047) B45045047
theorem B40040041 : Blo 2025435 40040041 := bstep (se 2 (by rfl) ⟨15015015, by rfl⟩ : syracuseStep 40040041 = 30030031) B30030031
theorem B53386721 : Blo 2025435 53386721 := bstep (se 2 (by rfl) ⟨20020020, by rfl⟩ : syracuseStep 53386721 = 40040041) B40040041
theorem B35591147 : Blo 2025435 35591147 := bstep (se 1 (by rfl) ⟨26693360, by rfl⟩ : syracuseStep 35591147 = 53386721) B53386721
theorem B23727431 : Blo 2025435 23727431 := bstep (se 1 (by rfl) ⟨17795573, by rfl⟩ : syracuseStep 23727431 = 35591147) B35591147
theorem B15818287 : Blo 2025435 15818287 := bstep (se 1 (by rfl) ⟨11863715, by rfl⟩ : syracuseStep 15818287 = 23727431) B23727431
theorem B21091049 : Blo 2025435 21091049 := bstep (se 2 (by rfl) ⟨7909143, by rfl⟩ : syracuseStep 21091049 = 15818287) B15818287
theorem B14060699 : Blo 2025435 14060699 := bstep (se 1 (by rfl) ⟨10545524, by rfl⟩ : syracuseStep 14060699 = 21091049) B21091049
theorem B9373799 : Blo 2025435 9373799 := bstep (se 1 (by rfl) ⟨7030349, by rfl⟩ : syracuseStep 9373799 = 14060699) B14060699
theorem B6249199 : Blo 2025435 6249199 := bstep (se 1 (by rfl) ⟨4686899, by rfl⟩ : syracuseStep 6249199 = 9373799) B9373799
theorem B8332265 : Blo 2025435 8332265 := bstep (se 2 (by rfl) ⟨3124599, by rfl⟩ : syracuseStep 8332265 = 6249199) B6249199
theorem B22219373 : Blo 2025435 22219373 := bstep (se 3 (by rfl) ⟨4166132, by rfl⟩ : syracuseStep 22219373 = 8332265) B8332265
theorem B14812915 : Blo 2025435 14812915 := bstep (se 1 (by rfl) ⟨11109686, by rfl⟩ : syracuseStep 14812915 = 22219373) B22219373
theorem B19750553 : Blo 2025435 19750553 := bstep (se 2 (by rfl) ⟨7406457, by rfl⟩ : syracuseStep 19750553 = 14812915) B14812915
theorem B13167035 : Blo 2025435 13167035 := bstep (se 1 (by rfl) ⟨9875276, by rfl⟩ : syracuseStep 13167035 = 19750553) B19750553
theorem B8778023 : Blo 2025435 8778023 := bstep (se 1 (by rfl) ⟨6583517, by rfl⟩ : syracuseStep 8778023 = 13167035) B13167035
theorem B5852015 : Blo 2025435 5852015 := bstep (se 1 (by rfl) ⟨4389011, by rfl⟩ : syracuseStep 5852015 = 8778023) B8778023
theorem B3901343 : Blo 2025435 3901343 := bstep (se 1 (by rfl) ⟨2926007, by rfl⟩ : syracuseStep 3901343 = 5852015) B5852015
theorem B10403581 : Blo 2025435 10403581 := bstep (se 3 (by rfl) ⟨1950671, by rfl⟩ : syracuseStep 10403581 = 3901343) B3901343
theorem B13871441 : Blo 2025435 13871441 := bstep (se 2 (by rfl) ⟨5201790, by rfl⟩ : syracuseStep 13871441 = 10403581) B10403581
theorem B9247627 : Blo 2025435 9247627 := bstep (se 1 (by rfl) ⟨6935720, by rfl⟩ : syracuseStep 9247627 = 13871441) B13871441
theorem B49320677 : Blo 2025435 49320677 := bstep (se 4 (by rfl) ⟨4623813, by rfl⟩ : syracuseStep 49320677 = 9247627) B9247627
theorem B131521805 : Blo 2025435 131521805 := bstep (se 3 (by rfl) ⟨24660338, by rfl⟩ : syracuseStep 131521805 = 49320677) B49320677
theorem B87681203 : Blo 2025435 87681203 := bstep (se 1 (by rfl) ⟨65760902, by rfl⟩ : syracuseStep 87681203 = 131521805) B131521805
theorem B58454135 : Blo 2025435 58454135 := bstep (se 1 (by rfl) ⟨43840601, by rfl⟩ : syracuseStep 58454135 = 87681203) B87681203
theorem B38969423 : Blo 2025435 38969423 := bstep (se 1 (by rfl) ⟨29227067, by rfl⟩ : syracuseStep 38969423 = 58454135) B58454135
theorem B25979615 : Blo 2025435 25979615 := bstep (se 1 (by rfl) ⟨19484711, by rfl⟩ : syracuseStep 25979615 = 38969423) B38969423
theorem B17319743 : Blo 2025435 17319743 := bstep (se 1 (by rfl) ⟨12989807, by rfl⟩ : syracuseStep 17319743 = 25979615) B25979615
theorem B11546495 : Blo 2025435 11546495 := bstep (se 1 (by rfl) ⟨8659871, by rfl⟩ : syracuseStep 11546495 = 17319743) B17319743
theorem B7697663 : Blo 2025435 7697663 := bstep (se 1 (by rfl) ⟨5773247, by rfl⟩ : syracuseStep 7697663 = 11546495) B11546495
theorem B5131775 : Blo 2025435 5131775 := bstep (se 1 (by rfl) ⟨3848831, by rfl⟩ : syracuseStep 5131775 = 7697663) B7697663
theorem B3421183 : Blo 2025435 3421183 := bstep (se 1 (by rfl) ⟨2565887, by rfl⟩ : syracuseStep 3421183 = 5131775) B5131775
theorem B4561577 : Blo 2025435 4561577 := bstep (se 2 (by rfl) ⟨1710591, by rfl⟩ : syracuseStep 4561577 = 3421183) B3421183
theorem B3041051 : Blo 2025435 3041051 := bstep (se 1 (by rfl) ⟨2280788, by rfl⟩ : syracuseStep 3041051 = 4561577) B4561577
theorem B2027367 : Blo 2025435 2027367 := bstep (se 1 (by rfl) ⟨1520525, by rfl⟩ : syracuseStep 2027367 = 3041051) B3041051
theorem B2280793 : Blo 2025435 2280793 := bbase (se 2 (by rfl) ⟨855297, by rfl⟩ : syracuseStep 2280793 = 1710595) (by norm_num)
theorem B3041057 : Blo 2025435 3041057 := bstep (se 2 (by rfl) ⟨1140396, by rfl⟩ : syracuseStep 3041057 = 2280793) B2280793
theorem B2027371 : Blo 2025435 2027371 := bstep (se 1 (by rfl) ⟨1520528, by rfl⟩ : syracuseStep 2027371 = 3041057) B3041057
theorem B8220149 : Blo 2025435 8220149 := bbase (se 5 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 8220149 = 770639) (by norm_num)
theorem B5480099 : Blo 2025435 5480099 := bstep (se 1 (by rfl) ⟨4110074, by rfl⟩ : syracuseStep 5480099 = 8220149) B8220149
theorem B3653399 : Blo 2025435 3653399 := bstep (se 1 (by rfl) ⟨2740049, by rfl⟩ : syracuseStep 3653399 = 5480099) B5480099
theorem B2435599 : Blo 2025435 2435599 := bstep (se 1 (by rfl) ⟨1826699, by rfl⟩ : syracuseStep 2435599 = 3653399) B3653399
theorem B3247465 : Blo 2025435 3247465 := bstep (se 2 (by rfl) ⟨1217799, by rfl⟩ : syracuseStep 3247465 = 2435599) B2435599
theorem B4329953 : Blo 2025435 4329953 := bstep (se 2 (by rfl) ⟨1623732, by rfl⟩ : syracuseStep 4329953 = 3247465) B3247465
theorem B2886635 : Blo 2025435 2886635 := bstep (se 1 (by rfl) ⟨2164976, by rfl⟩ : syracuseStep 2886635 = 4329953) B4329953
theorem B7697693 : Blo 2025435 7697693 := bstep (se 3 (by rfl) ⟨1443317, by rfl⟩ : syracuseStep 7697693 = 2886635) B2886635
theorem B5131795 : Blo 2025435 5131795 := bstep (se 1 (by rfl) ⟨3848846, by rfl⟩ : syracuseStep 5131795 = 7697693) B7697693
theorem B6842393 : Blo 2025435 6842393 := bstep (se 2 (by rfl) ⟨2565897, by rfl⟩ : syracuseStep 6842393 = 5131795) B5131795
theorem B4561595 : Blo 2025435 4561595 := bstep (se 1 (by rfl) ⟨3421196, by rfl⟩ : syracuseStep 4561595 = 6842393) B6842393
theorem B3041063 : Blo 2025435 3041063 := bstep (se 1 (by rfl) ⟨2280797, by rfl⟩ : syracuseStep 3041063 = 4561595) B4561595
theorem B2027375 : Blo 2025435 2027375 := bstep (se 1 (by rfl) ⟨1520531, by rfl⟩ : syracuseStep 2027375 = 3041063) B3041063
theorem B3041069 : Blo 2025435 3041069 := bbase (se 3 (by rfl) ⟨570200, by rfl⟩ : syracuseStep 3041069 = 1140401) (by norm_num)
theorem B2027379 : Blo 2025435 2027379 := bstep (se 1 (by rfl) ⟨1520534, by rfl⟩ : syracuseStep 2027379 = 3041069) B3041069
theorem B4561613 : Blo 2025435 4561613 := bbase (se 3 (by rfl) ⟨855302, by rfl⟩ : syracuseStep 4561613 = 1710605) (by norm_num)
theorem B3041075 : Blo 2025435 3041075 := bstep (se 1 (by rfl) ⟨2280806, by rfl⟩ : syracuseStep 3041075 = 4561613) B4561613
theorem B2027383 : Blo 2025435 2027383 := bstep (se 1 (by rfl) ⟨1520537, by rfl⟩ : syracuseStep 2027383 = 3041075) B3041075
theorem B2565913 : Blo 2025435 2565913 := bbase (se 2 (by rfl) ⟨962217, by rfl⟩ : syracuseStep 2565913 = 1924435) (by norm_num)
theorem B3421217 : Blo 2025435 3421217 := bstep (se 2 (by rfl) ⟨1282956, by rfl⟩ : syracuseStep 3421217 = 2565913) B2565913
theorem B2280811 : Blo 2025435 2280811 := bstep (se 1 (by rfl) ⟨1710608, by rfl⟩ : syracuseStep 2280811 = 3421217) B3421217
theorem B3041081 : Blo 2025435 3041081 := bstep (se 2 (by rfl) ⟨1140405, by rfl⟩ : syracuseStep 3041081 = 2280811) B2280811
theorem B2027387 : Blo 2025435 2027387 := bstep (se 1 (by rfl) ⟨1520540, by rfl⟩ : syracuseStep 2027387 = 3041081) B3041081
theorem B8659973 : Blo 2025435 8659973 := bbase (se 4 (by rfl) ⟨811872, by rfl⟩ : syracuseStep 8659973 = 1623745) (by norm_num)
theorem B23093261 : Blo 2025435 23093261 := bstep (se 3 (by rfl) ⟨4329986, by rfl⟩ : syracuseStep 23093261 = 8659973) B8659973
theorem B15395507 : Blo 2025435 15395507 := bstep (se 1 (by rfl) ⟨11546630, by rfl⟩ : syracuseStep 15395507 = 23093261) B23093261
theorem B10263671 : Blo 2025435 10263671 := bstep (se 1 (by rfl) ⟨7697753, by rfl⟩ : syracuseStep 10263671 = 15395507) B15395507
theorem B6842447 : Blo 2025435 6842447 := bstep (se 1 (by rfl) ⟨5131835, by rfl⟩ : syracuseStep 6842447 = 10263671) B10263671
theorem B4561631 : Blo 2025435 4561631 := bstep (se 1 (by rfl) ⟨3421223, by rfl⟩ : syracuseStep 4561631 = 6842447) B6842447
theorem B3041087 : Blo 2025435 3041087 := bstep (se 1 (by rfl) ⟨2280815, by rfl⟩ : syracuseStep 3041087 = 4561631) B4561631
theorem B2027391 : Blo 2025435 2027391 := bstep (se 1 (by rfl) ⟨1520543, by rfl⟩ : syracuseStep 2027391 = 3041087) B3041087
theorem B3041093 : Blo 2025435 3041093 := bbase (se 4 (by rfl) ⟨285102, by rfl⟩ : syracuseStep 3041093 = 570205) (by norm_num)
theorem B2027395 : Blo 2025435 2027395 := bstep (se 1 (by rfl) ⟨1520546, by rfl⟩ : syracuseStep 2027395 = 3041093) B3041093
theorem B3421237 : Blo 2025435 3421237 := bbase (se 5 (by rfl) ⟨160370, by rfl⟩ : syracuseStep 3421237 = 320741) (by norm_num)
theorem B4561649 : Blo 2025435 4561649 := bstep (se 2 (by rfl) ⟨1710618, by rfl⟩ : syracuseStep 4561649 = 3421237) B3421237
theorem B3041099 : Blo 2025435 3041099 := bstep (se 1 (by rfl) ⟨2280824, by rfl⟩ : syracuseStep 3041099 = 4561649) B4561649
theorem B2027399 : Blo 2025435 2027399 := bstep (se 1 (by rfl) ⟨1520549, by rfl⟩ : syracuseStep 2027399 = 3041099) B3041099
theorem B2280829 : Blo 2025435 2280829 := bbase (se 3 (by rfl) ⟨427655, by rfl⟩ : syracuseStep 2280829 = 855311) (by norm_num)
theorem B3041105 : Blo 2025435 3041105 := bstep (se 2 (by rfl) ⟨1140414, by rfl⟩ : syracuseStep 3041105 = 2280829) B2280829
theorem B2027403 : Blo 2025435 2027403 := bstep (se 1 (by rfl) ⟨1520552, by rfl⟩ : syracuseStep 2027403 = 3041105) B3041105
theorem B6842501 : Blo 2025435 6842501 := bbase (se 4 (by rfl) ⟨641484, by rfl⟩ : syracuseStep 6842501 = 1282969) (by norm_num)
theorem B4561667 : Blo 2025435 4561667 := bstep (se 1 (by rfl) ⟨3421250, by rfl⟩ : syracuseStep 4561667 = 6842501) B6842501
theorem B3041111 : Blo 2025435 3041111 := bstep (se 1 (by rfl) ⟨2280833, by rfl⟩ : syracuseStep 3041111 = 4561667) B4561667
theorem B2027407 : Blo 2025435 2027407 := bstep (se 1 (by rfl) ⟨1520555, by rfl⟩ : syracuseStep 2027407 = 3041111) B3041111
theorem B3041117 : Blo 2025435 3041117 := bbase (se 3 (by rfl) ⟨570209, by rfl⟩ : syracuseStep 3041117 = 1140419) (by norm_num)
theorem B2027411 : Blo 2025435 2027411 := bstep (se 1 (by rfl) ⟨1520558, by rfl⟩ : syracuseStep 2027411 = 3041117) B3041117
theorem B4561685 : Blo 2025435 4561685 := bbase (se 6 (by rfl) ⟨106914, by rfl⟩ : syracuseStep 4561685 = 213829) (by norm_num)
theorem B3041123 : Blo 2025435 3041123 := bstep (se 1 (by rfl) ⟨2280842, by rfl⟩ : syracuseStep 3041123 = 4561685) B4561685
theorem B2027415 : Blo 2025435 2027415 := bstep (se 1 (by rfl) ⟨1520561, by rfl⟩ : syracuseStep 2027415 = 3041123) B3041123
theorem B7697861 : Blo 2025435 7697861 := bbase (se 4 (by rfl) ⟨721674, by rfl⟩ : syracuseStep 7697861 = 1443349) (by norm_num)
theorem B5131907 : Blo 2025435 5131907 := bstep (se 1 (by rfl) ⟨3848930, by rfl⟩ : syracuseStep 5131907 = 7697861) B7697861
theorem B3421271 : Blo 2025435 3421271 := bstep (se 1 (by rfl) ⟨2565953, by rfl⟩ : syracuseStep 3421271 = 5131907) B5131907
theorem B2280847 : Blo 2025435 2280847 := bstep (se 1 (by rfl) ⟨1710635, by rfl⟩ : syracuseStep 2280847 = 3421271) B3421271
theorem B3041129 : Blo 2025435 3041129 := bstep (se 2 (by rfl) ⟨1140423, by rfl⟩ : syracuseStep 3041129 = 2280847) B2280847
theorem B2027419 : Blo 2025435 2027419 := bstep (se 1 (by rfl) ⟨1520564, by rfl⟩ : syracuseStep 2027419 = 3041129) B3041129
theorem B8220341 : Blo 2025435 8220341 := bbase (se 5 (by rfl) ⟨385328, by rfl⟩ : syracuseStep 8220341 = 770657) (by norm_num)
theorem B5480227 : Blo 2025435 5480227 := bstep (se 1 (by rfl) ⟨4110170, by rfl⟩ : syracuseStep 5480227 = 8220341) B8220341
theorem B7306969 : Blo 2025435 7306969 := bstep (se 2 (by rfl) ⟨2740113, by rfl⟩ : syracuseStep 7306969 = 5480227) B5480227
theorem B9742625 : Blo 2025435 9742625 := bstep (se 2 (by rfl) ⟨3653484, by rfl⟩ : syracuseStep 9742625 = 7306969) B7306969
theorem B6495083 : Blo 2025435 6495083 := bstep (se 1 (by rfl) ⟨4871312, by rfl⟩ : syracuseStep 6495083 = 9742625) B9742625
theorem B4330055 : Blo 2025435 4330055 := bstep (se 1 (by rfl) ⟨3247541, by rfl⟩ : syracuseStep 4330055 = 6495083) B6495083
theorem B11546813 : Blo 2025435 11546813 := bstep (se 3 (by rfl) ⟨2165027, by rfl⟩ : syracuseStep 11546813 = 4330055) B4330055
theorem B7697875 : Blo 2025435 7697875 := bstep (se 1 (by rfl) ⟨5773406, by rfl⟩ : syracuseStep 7697875 = 11546813) B11546813
theorem B10263833 : Blo 2025435 10263833 := bstep (se 2 (by rfl) ⟨3848937, by rfl⟩ : syracuseStep 10263833 = 7697875) B7697875
theorem B6842555 : Blo 2025435 6842555 := bstep (se 1 (by rfl) ⟨5131916, by rfl⟩ : syracuseStep 6842555 = 10263833) B10263833
theorem B4561703 : Blo 2025435 4561703 := bstep (se 1 (by rfl) ⟨3421277, by rfl⟩ : syracuseStep 4561703 = 6842555) B6842555
theorem B3041135 : Blo 2025435 3041135 := bstep (se 1 (by rfl) ⟨2280851, by rfl⟩ : syracuseStep 3041135 = 4561703) B4561703
theorem B2027423 : Blo 2025435 2027423 := bstep (se 1 (by rfl) ⟨1520567, by rfl⟩ : syracuseStep 2027423 = 3041135) B3041135
theorem B3041141 : Blo 2025435 3041141 := bbase (se 5 (by rfl) ⟨142553, by rfl⟩ : syracuseStep 3041141 = 285107) (by norm_num)
theorem B2027427 : Blo 2025435 2027427 := bstep (se 1 (by rfl) ⟨1520570, by rfl⟩ : syracuseStep 2027427 = 3041141) B3041141
theorem B4871333 : Blo 2025435 4871333 := bbase (se 4 (by rfl) ⟨456687, by rfl⟩ : syracuseStep 4871333 = 913375) (by norm_num)
theorem B3247555 : Blo 2025435 3247555 := bstep (se 1 (by rfl) ⟨2435666, by rfl⟩ : syracuseStep 3247555 = 4871333) B4871333
theorem B4330073 : Blo 2025435 4330073 := bstep (se 2 (by rfl) ⟨1623777, by rfl⟩ : syracuseStep 4330073 = 3247555) B3247555
theorem B2886715 : Blo 2025435 2886715 := bstep (se 1 (by rfl) ⟨2165036, by rfl⟩ : syracuseStep 2886715 = 4330073) B4330073
theorem B3848953 : Blo 2025435 3848953 := bstep (se 2 (by rfl) ⟨1443357, by rfl⟩ : syracuseStep 3848953 = 2886715) B2886715
theorem B5131937 : Blo 2025435 5131937 := bstep (se 2 (by rfl) ⟨1924476, by rfl⟩ : syracuseStep 5131937 = 3848953) B3848953
theorem B3421291 : Blo 2025435 3421291 := bstep (se 1 (by rfl) ⟨2565968, by rfl⟩ : syracuseStep 3421291 = 5131937) B5131937
theorem B4561721 : Blo 2025435 4561721 := bstep (se 2 (by rfl) ⟨1710645, by rfl⟩ : syracuseStep 4561721 = 3421291) B3421291
theorem B3041147 : Blo 2025435 3041147 := bstep (se 1 (by rfl) ⟨2280860, by rfl⟩ : syracuseStep 3041147 = 4561721) B4561721
theorem B2027431 : Blo 2025435 2027431 := bstep (se 1 (by rfl) ⟨1520573, by rfl⟩ : syracuseStep 2027431 = 3041147) B3041147
theorem B2280865 : Blo 2025435 2280865 := bbase (se 2 (by rfl) ⟨855324, by rfl⟩ : syracuseStep 2280865 = 1710649) (by norm_num)
theorem B3041153 : Blo 2025435 3041153 := bstep (se 2 (by rfl) ⟨1140432, by rfl⟩ : syracuseStep 3041153 = 2280865) B2280865
theorem B2027435 : Blo 2025435 2027435 := bstep (se 1 (by rfl) ⟨1520576, by rfl⟩ : syracuseStep 2027435 = 3041153) B3041153
theorem C0 (j : ℕ) (h1 : 506358 ≤ j) (h2 : j ≤ 506858) : Blo 2025435 (4 * j + 3) := by
  interval_cases j
  · exact B2025435
  · exact B2025439
  · exact B2025443
  · exact B2025447
  · exact B2025451
  · exact B2025455
  · exact B2025459
  · exact B2025463
  · exact B2025467
  · exact B2025471
  · exact B2025475
  · exact B2025479
  · exact B2025483
  · exact B2025487
  · exact B2025491
  · exact B2025495
  · exact B2025499
  · exact B2025503
  · exact B2025507
  · exact B2025511
  · exact B2025515
  · exact B2025519
  · exact B2025523
  · exact B2025527
  · exact B2025531
  · exact B2025535
  · exact B2025539
  · exact B2025543
  · exact B2025547
  · exact B2025551
  · exact B2025555
  · exact B2025559
  · exact B2025563
  · exact B2025567
  · exact B2025571
  · exact B2025575
  · exact B2025579
  · exact B2025583
  · exact B2025587
  · exact B2025591
  · exact B2025595
  · exact B2025599
  · exact B2025603
  · exact B2025607
  · exact B2025611
  · exact B2025615
  · exact B2025619
  · exact B2025623
  · exact B2025627
  · exact B2025631
  · exact B2025635
  · exact B2025639
  · exact B2025643
  · exact B2025647
  · exact B2025651
  · exact B2025655
  · exact B2025659
  · exact B2025663
  · exact B2025667
  · exact B2025671
  · exact B2025675
  · exact B2025679
  · exact B2025683
  · exact B2025687
  · exact B2025691
  · exact B2025695
  · exact B2025699
  · exact B2025703
  · exact B2025707
  · exact B2025711
  · exact B2025715
  · exact B2025719
  · exact B2025723
  · exact B2025727
  · exact B2025731
  · exact B2025735
  · exact B2025739
  · exact B2025743
  · exact B2025747
  · exact B2025751
  · exact B2025755
  · exact B2025759
  · exact B2025763
  · exact B2025767
  · exact B2025771
  · exact B2025775
  · exact B2025779
  · exact B2025783
  · exact B2025787
  · exact B2025791
  · exact B2025795
  · exact B2025799
  · exact B2025803
  · exact B2025807
  · exact B2025811
  · exact B2025815
  · exact B2025819
  · exact B2025823
  · exact B2025827
  · exact B2025831
  · exact B2025835
  · exact B2025839
  · exact B2025843
  · exact B2025847
  · exact B2025851
  · exact B2025855
  · exact B2025859
  · exact B2025863
  · exact B2025867
  · exact B2025871
  · exact B2025875
  · exact B2025879
  · exact B2025883
  · exact B2025887
  · exact B2025891
  · exact B2025895
  · exact B2025899
  · exact B2025903
  · exact B2025907
  · exact B2025911
  · exact B2025915
  · exact B2025919
  · exact B2025923
  · exact B2025927
  · exact B2025931
  · exact B2025935
  · exact B2025939
  · exact B2025943
  · exact B2025947
  · exact B2025951
  · exact B2025955
  · exact B2025959
  · exact B2025963
  · exact B2025967
  · exact B2025971
  · exact B2025975
  · exact B2025979
  · exact B2025983
  · exact B2025987
  · exact B2025991
  · exact B2025995
  · exact B2025999
  · exact B2026003
  · exact B2026007
  · exact B2026011
  · exact B2026015
  · exact B2026019
  · exact B2026023
  · exact B2026027
  · exact B2026031
  · exact B2026035
  · exact B2026039
  · exact B2026043
  · exact B2026047
  · exact B2026051
  · exact B2026055
  · exact B2026059
  · exact B2026063
  · exact B2026067
  · exact B2026071
  · exact B2026075
  · exact B2026079
  · exact B2026083
  · exact B2026087
  · exact B2026091
  · exact B2026095
  · exact B2026099
  · exact B2026103
  · exact B2026107
  · exact B2026111
  · exact B2026115
  · exact B2026119
  · exact B2026123
  · exact B2026127
  · exact B2026131
  · exact B2026135
  · exact B2026139
  · exact B2026143
  · exact B2026147
  · exact B2026151
  · exact B2026155
  · exact B2026159
  · exact B2026163
  · exact B2026167
  · exact B2026171
  · exact B2026175
  · exact B2026179
  · exact B2026183
  · exact B2026187
  · exact B2026191
  · exact B2026195
  · exact B2026199
  · exact B2026203
  · exact B2026207
  · exact B2026211
  · exact B2026215
  · exact B2026219
  · exact B2026223
  · exact B2026227
  · exact B2026231
  · exact B2026235
  · exact B2026239
  · exact B2026243
  · exact B2026247
  · exact B2026251
  · exact B2026255
  · exact B2026259
  · exact B2026263
  · exact B2026267
  · exact B2026271
  · exact B2026275
  · exact B2026279
  · exact B2026283
  · exact B2026287
  · exact B2026291
  · exact B2026295
  · exact B2026299
  · exact B2026303
  · exact B2026307
  · exact B2026311
  · exact B2026315
  · exact B2026319
  · exact B2026323
  · exact B2026327
  · exact B2026331
  · exact B2026335
  · exact B2026339
  · exact B2026343
  · exact B2026347
  · exact B2026351
  · exact B2026355
  · exact B2026359
  · exact B2026363
  · exact B2026367
  · exact B2026371
  · exact B2026375
  · exact B2026379
  · exact B2026383
  · exact B2026387
  · exact B2026391
  · exact B2026395
  · exact B2026399
  · exact B2026403
  · exact B2026407
  · exact B2026411
  · exact B2026415
  · exact B2026419
  · exact B2026423
  · exact B2026427
  · exact B2026431
  · exact B2026435
  · exact B2026439
  · exact B2026443
  · exact B2026447
  · exact B2026451
  · exact B2026455
  · exact B2026459
  · exact B2026463
  · exact B2026467
  · exact B2026471
  · exact B2026475
  · exact B2026479
  · exact B2026483
  · exact B2026487
  · exact B2026491
  · exact B2026495
  · exact B2026499
  · exact B2026503
  · exact B2026507
  · exact B2026511
  · exact B2026515
  · exact B2026519
  · exact B2026523
  · exact B2026527
  · exact B2026531
  · exact B2026535
  · exact B2026539
  · exact B2026543
  · exact B2026547
  · exact B2026551
  · exact B2026555
  · exact B2026559
  · exact B2026563
  · exact B2026567
  · exact B2026571
  · exact B2026575
  · exact B2026579
  · exact B2026583
  · exact B2026587
  · exact B2026591
  · exact B2026595
  · exact B2026599
  · exact B2026603
  · exact B2026607
  · exact B2026611
  · exact B2026615
  · exact B2026619
  · exact B2026623
  · exact B2026627
  · exact B2026631
  · exact B2026635
  · exact B2026639
  · exact B2026643
  · exact B2026647
  · exact B2026651
  · exact B2026655
  · exact B2026659
  · exact B2026663
  · exact B2026667
  · exact B2026671
  · exact B2026675
  · exact B2026679
  · exact B2026683
  · exact B2026687
  · exact B2026691
  · exact B2026695
  · exact B2026699
  · exact B2026703
  · exact B2026707
  · exact B2026711
  · exact B2026715
  · exact B2026719
  · exact B2026723
  · exact B2026727
  · exact B2026731
  · exact B2026735
  · exact B2026739
  · exact B2026743
  · exact B2026747
  · exact B2026751
  · exact B2026755
  · exact B2026759
  · exact B2026763
  · exact B2026767
  · exact B2026771
  · exact B2026775
  · exact B2026779
  · exact B2026783
  · exact B2026787
  · exact B2026791
  · exact B2026795
  · exact B2026799
  · exact B2026803
  · exact B2026807
  · exact B2026811
  · exact B2026815
  · exact B2026819
  · exact B2026823
  · exact B2026827
  · exact B2026831
  · exact B2026835
  · exact B2026839
  · exact B2026843
  · exact B2026847
  · exact B2026851
  · exact B2026855
  · exact B2026859
  · exact B2026863
  · exact B2026867
  · exact B2026871
  · exact B2026875
  · exact B2026879
  · exact B2026883
  · exact B2026887
  · exact B2026891
  · exact B2026895
  · exact B2026899
  · exact B2026903
  · exact B2026907
  · exact B2026911
  · exact B2026915
  · exact B2026919
  · exact B2026923
  · exact B2026927
  · exact B2026931
  · exact B2026935
  · exact B2026939
  · exact B2026943
  · exact B2026947
  · exact B2026951
  · exact B2026955
  · exact B2026959
  · exact B2026963
  · exact B2026967
  · exact B2026971
  · exact B2026975
  · exact B2026979
  · exact B2026983
  · exact B2026987
  · exact B2026991
  · exact B2026995
  · exact B2026999
  · exact B2027003
  · exact B2027007
  · exact B2027011
  · exact B2027015
  · exact B2027019
  · exact B2027023
  · exact B2027027
  · exact B2027031
  · exact B2027035
  · exact B2027039
  · exact B2027043
  · exact B2027047
  · exact B2027051
  · exact B2027055
  · exact B2027059
  · exact B2027063
  · exact B2027067
  · exact B2027071
  · exact B2027075
  · exact B2027079
  · exact B2027083
  · exact B2027087
  · exact B2027091
  · exact B2027095
  · exact B2027099
  · exact B2027103
  · exact B2027107
  · exact B2027111
  · exact B2027115
  · exact B2027119
  · exact B2027123
  · exact B2027127
  · exact B2027131
  · exact B2027135
  · exact B2027139
  · exact B2027143
  · exact B2027147
  · exact B2027151
  · exact B2027155
  · exact B2027159
  · exact B2027163
  · exact B2027167
  · exact B2027171
  · exact B2027175
  · exact B2027179
  · exact B2027183
  · exact B2027187
  · exact B2027191
  · exact B2027195
  · exact B2027199
  · exact B2027203
  · exact B2027207
  · exact B2027211
  · exact B2027215
  · exact B2027219
  · exact B2027223
  · exact B2027227
  · exact B2027231
  · exact B2027235
  · exact B2027239
  · exact B2027243
  · exact B2027247
  · exact B2027251
  · exact B2027255
  · exact B2027259
  · exact B2027263
  · exact B2027267
  · exact B2027271
  · exact B2027275
  · exact B2027279
  · exact B2027283
  · exact B2027287
  · exact B2027291
  · exact B2027295
  · exact B2027299
  · exact B2027303
  · exact B2027307
  · exact B2027311
  · exact B2027315
  · exact B2027319
  · exact B2027323
  · exact B2027327
  · exact B2027331
  · exact B2027335
  · exact B2027339
  · exact B2027343
  · exact B2027347
  · exact B2027351
  · exact B2027355
  · exact B2027359
  · exact B2027363
  · exact B2027367
  · exact B2027371
  · exact B2027375
  · exact B2027379
  · exact B2027383
  · exact B2027387
  · exact B2027391
  · exact B2027395
  · exact B2027399
  · exact B2027403
  · exact B2027407
  · exact B2027411
  · exact B2027415
  · exact B2027419
  · exact B2027423
  · exact B2027427
  · exact B2027431
  · exact B2027435
theorem solution (m : ℕ) (hlo : 2025435 ≤ m) (hhi : m ≤ 2027435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 506358 ≤ j := by omega
    have hj2 : j ≤ 506858 := by omega
    have hb : Blo 2025435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
