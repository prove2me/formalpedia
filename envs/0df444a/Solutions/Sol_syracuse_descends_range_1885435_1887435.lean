-- Prove2me | solution 1 for syracuse_descends_range_1885435_1887435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:35.893978+00:00
-- url     : https://prove2.me/submissions/a4a106f0-3c85-4b93-889b-c6e392ff7454

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

theorem B1911161 : Blo 1885435 1911161 := bbase (se 2 (by rfl) ⟨716685, by rfl⟩ : syracuseStep 1911161 = 1433371) (by norm_num)
theorem B5096429 : Blo 1885435 5096429 := bstep (se 3 (by rfl) ⟨955580, by rfl⟩ : syracuseStep 5096429 = 1911161) B1911161
theorem B3397619 : Blo 1885435 3397619 := bstep (se 1 (by rfl) ⟨2548214, by rfl⟩ : syracuseStep 3397619 = 5096429) B5096429
theorem B2265079 : Blo 1885435 2265079 := bstep (se 1 (by rfl) ⟨1698809, by rfl⟩ : syracuseStep 2265079 = 3397619) B3397619
theorem B3020105 : Blo 1885435 3020105 := bstep (se 2 (by rfl) ⟨1132539, by rfl⟩ : syracuseStep 3020105 = 2265079) B2265079
theorem B8053613 : Blo 1885435 8053613 := bstep (se 3 (by rfl) ⟨1510052, by rfl⟩ : syracuseStep 8053613 = 3020105) B3020105
theorem B5369075 : Blo 1885435 5369075 := bstep (se 1 (by rfl) ⟨4026806, by rfl⟩ : syracuseStep 5369075 = 8053613) B8053613
theorem B3579383 : Blo 1885435 3579383 := bstep (se 1 (by rfl) ⟨2684537, by rfl⟩ : syracuseStep 3579383 = 5369075) B5369075
theorem B2386255 : Blo 1885435 2386255 := bstep (se 1 (by rfl) ⟨1789691, by rfl⟩ : syracuseStep 2386255 = 3579383) B3579383
theorem B3181673 : Blo 1885435 3181673 := bstep (se 2 (by rfl) ⟨1193127, by rfl⟩ : syracuseStep 3181673 = 2386255) B2386255
theorem B2121115 : Blo 1885435 2121115 := bstep (se 1 (by rfl) ⟨1590836, by rfl⟩ : syracuseStep 2121115 = 3181673) B3181673
theorem B2828153 : Blo 1885435 2828153 := bstep (se 2 (by rfl) ⟨1060557, by rfl⟩ : syracuseStep 2828153 = 2121115) B2121115
theorem B1885435 : Blo 1885435 1885435 := bstep (se 1 (by rfl) ⟨1414076, by rfl⟩ : syracuseStep 1885435 = 2828153) B2828153
theorem B4591973 : Blo 1885435 4591973 := bbase (se 4 (by rfl) ⟨430497, by rfl⟩ : syracuseStep 4591973 = 860995) (by norm_num)
theorem B12245261 : Blo 1885435 12245261 := bstep (se 3 (by rfl) ⟨2295986, by rfl⟩ : syracuseStep 12245261 = 4591973) B4591973
theorem B32654029 : Blo 1885435 32654029 := bstep (se 3 (by rfl) ⟨6122630, by rfl⟩ : syracuseStep 32654029 = 12245261) B12245261
theorem B43538705 : Blo 1885435 43538705 := bstep (se 2 (by rfl) ⟨16327014, by rfl⟩ : syracuseStep 43538705 = 32654029) B32654029
theorem B29025803 : Blo 1885435 29025803 := bstep (se 1 (by rfl) ⟨21769352, by rfl⟩ : syracuseStep 29025803 = 43538705) B43538705
theorem B19350535 : Blo 1885435 19350535 := bstep (se 1 (by rfl) ⟨14512901, by rfl⟩ : syracuseStep 19350535 = 29025803) B29025803
theorem B25800713 : Blo 1885435 25800713 := bstep (se 2 (by rfl) ⟨9675267, by rfl⟩ : syracuseStep 25800713 = 19350535) B19350535
theorem B17200475 : Blo 1885435 17200475 := bstep (se 1 (by rfl) ⟨12900356, by rfl⟩ : syracuseStep 17200475 = 25800713) B25800713
theorem B11466983 : Blo 1885435 11466983 := bstep (se 1 (by rfl) ⟨8600237, by rfl⟩ : syracuseStep 11466983 = 17200475) B17200475
theorem B7644655 : Blo 1885435 7644655 := bstep (se 1 (by rfl) ⟨5733491, by rfl⟩ : syracuseStep 7644655 = 11466983) B11466983
theorem B10192873 : Blo 1885435 10192873 := bstep (se 2 (by rfl) ⟨3822327, by rfl⟩ : syracuseStep 10192873 = 7644655) B7644655
theorem B13590497 : Blo 1885435 13590497 := bstep (se 2 (by rfl) ⟨5096436, by rfl⟩ : syracuseStep 13590497 = 10192873) B10192873
theorem B9060331 : Blo 1885435 9060331 := bstep (se 1 (by rfl) ⟨6795248, by rfl⟩ : syracuseStep 9060331 = 13590497) B13590497
theorem B12080441 : Blo 1885435 12080441 := bstep (se 2 (by rfl) ⟨4530165, by rfl⟩ : syracuseStep 12080441 = 9060331) B9060331
theorem B32214509 : Blo 1885435 32214509 := bstep (se 3 (by rfl) ⟨6040220, by rfl⟩ : syracuseStep 32214509 = 12080441) B12080441
theorem B21476339 : Blo 1885435 21476339 := bstep (se 1 (by rfl) ⟨16107254, by rfl⟩ : syracuseStep 21476339 = 32214509) B32214509
theorem B14317559 : Blo 1885435 14317559 := bstep (se 1 (by rfl) ⟨10738169, by rfl⟩ : syracuseStep 14317559 = 21476339) B21476339
theorem B9545039 : Blo 1885435 9545039 := bstep (se 1 (by rfl) ⟨7158779, by rfl⟩ : syracuseStep 9545039 = 14317559) B14317559
theorem B6363359 : Blo 1885435 6363359 := bstep (se 1 (by rfl) ⟨4772519, by rfl⟩ : syracuseStep 6363359 = 9545039) B9545039
theorem B4242239 : Blo 1885435 4242239 := bstep (se 1 (by rfl) ⟨3181679, by rfl⟩ : syracuseStep 4242239 = 6363359) B6363359
theorem B2828159 : Blo 1885435 2828159 := bstep (se 1 (by rfl) ⟨2121119, by rfl⟩ : syracuseStep 2828159 = 4242239) B4242239
theorem B1885439 : Blo 1885435 1885439 := bstep (se 1 (by rfl) ⟨1414079, by rfl⟩ : syracuseStep 1885439 = 2828159) B2828159
theorem B2828165 : Blo 1885435 2828165 := bbase (se 4 (by rfl) ⟨265140, by rfl⟩ : syracuseStep 2828165 = 530281) (by norm_num)
theorem B1885443 : Blo 1885435 1885443 := bstep (se 1 (by rfl) ⟨1414082, by rfl⟩ : syracuseStep 1885443 = 2828165) B2828165
theorem B3181693 : Blo 1885435 3181693 := bbase (se 3 (by rfl) ⟨596567, by rfl⟩ : syracuseStep 3181693 = 1193135) (by norm_num)
theorem B4242257 : Blo 1885435 4242257 := bstep (se 2 (by rfl) ⟨1590846, by rfl⟩ : syracuseStep 4242257 = 3181693) B3181693
theorem B2828171 : Blo 1885435 2828171 := bstep (se 1 (by rfl) ⟨2121128, by rfl⟩ : syracuseStep 2828171 = 4242257) B4242257
theorem B1885447 : Blo 1885435 1885447 := bstep (se 1 (by rfl) ⟨1414085, by rfl⟩ : syracuseStep 1885447 = 2828171) B2828171
theorem B2121133 : Blo 1885435 2121133 := bbase (se 3 (by rfl) ⟨397712, by rfl⟩ : syracuseStep 2121133 = 795425) (by norm_num)
theorem B2828177 : Blo 1885435 2828177 := bstep (se 2 (by rfl) ⟨1060566, by rfl⟩ : syracuseStep 2828177 = 2121133) B2121133
theorem B1885451 : Blo 1885435 1885451 := bstep (se 1 (by rfl) ⟨1414088, by rfl⟩ : syracuseStep 1885451 = 2828177) B2828177
theorem B6363413 : Blo 1885435 6363413 := bbase (se 6 (by rfl) ⟨149142, by rfl⟩ : syracuseStep 6363413 = 298285) (by norm_num)
theorem B4242275 : Blo 1885435 4242275 := bstep (se 1 (by rfl) ⟨3181706, by rfl⟩ : syracuseStep 4242275 = 6363413) B6363413
theorem B2828183 : Blo 1885435 2828183 := bstep (se 1 (by rfl) ⟨2121137, by rfl⟩ : syracuseStep 2828183 = 4242275) B4242275
theorem B1885455 : Blo 1885435 1885455 := bstep (se 1 (by rfl) ⟨1414091, by rfl⟩ : syracuseStep 1885455 = 2828183) B2828183
theorem B2828189 : Blo 1885435 2828189 := bbase (se 3 (by rfl) ⟨530285, by rfl⟩ : syracuseStep 2828189 = 1060571) (by norm_num)
theorem B1885459 : Blo 1885435 1885459 := bstep (se 1 (by rfl) ⟨1414094, by rfl⟩ : syracuseStep 1885459 = 2828189) B2828189
theorem B4242293 : Blo 1885435 4242293 := bbase (se 5 (by rfl) ⟨198857, by rfl⟩ : syracuseStep 4242293 = 397715) (by norm_num)
theorem B2828195 : Blo 1885435 2828195 := bstep (se 1 (by rfl) ⟨2121146, by rfl⟩ : syracuseStep 2828195 = 4242293) B4242293
theorem B1885463 : Blo 1885435 1885463 := bstep (se 1 (by rfl) ⟨1414097, by rfl⟩ : syracuseStep 1885463 = 2828195) B2828195
theorem B2418853 : Blo 1885435 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B51602197 : Blo 1885435 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B68802929 : Blo 1885435 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B45868619 : Blo 1885435 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B30579079 : Blo 1885435 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B40772105 : Blo 1885435 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B27181403 : Blo 1885435 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B18120935 : Blo 1885435 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B12080623 : Blo 1885435 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B16107497 : Blo 1885435 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B10738331 : Blo 1885435 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B7158887 : Blo 1885435 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B4772591 : Blo 1885435 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B3181727 : Blo 1885435 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B2121151 : Blo 1885435 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B2828201 : Blo 1885435 2828201 := bstep (se 2 (by rfl) ⟨1060575, by rfl⟩ : syracuseStep 2828201 = 2121151) B2121151
theorem B1885467 : Blo 1885435 1885467 := bstep (se 1 (by rfl) ⟨1414100, by rfl⟩ : syracuseStep 1885467 = 2828201) B2828201
theorem B7158901 : Blo 1885435 7158901 := bbase (se 5 (by rfl) ⟨335573, by rfl⟩ : syracuseStep 7158901 = 671147) (by norm_num)
theorem B9545201 : Blo 1885435 9545201 := bstep (se 2 (by rfl) ⟨3579450, by rfl⟩ : syracuseStep 9545201 = 7158901) B7158901
theorem B6363467 : Blo 1885435 6363467 := bstep (se 1 (by rfl) ⟨4772600, by rfl⟩ : syracuseStep 6363467 = 9545201) B9545201
theorem B4242311 : Blo 1885435 4242311 := bstep (se 1 (by rfl) ⟨3181733, by rfl⟩ : syracuseStep 4242311 = 6363467) B6363467
theorem B2828207 : Blo 1885435 2828207 := bstep (se 1 (by rfl) ⟨2121155, by rfl⟩ : syracuseStep 2828207 = 4242311) B4242311
theorem B1885471 : Blo 1885435 1885471 := bstep (se 1 (by rfl) ⟨1414103, by rfl⟩ : syracuseStep 1885471 = 2828207) B2828207
theorem B2828213 : Blo 1885435 2828213 := bbase (se 5 (by rfl) ⟨132572, by rfl⟩ : syracuseStep 2828213 = 265145) (by norm_num)
theorem B1885475 : Blo 1885435 1885475 := bstep (se 1 (by rfl) ⟨1414106, by rfl⟩ : syracuseStep 1885475 = 2828213) B2828213
theorem B4772621 : Blo 1885435 4772621 := bbase (se 3 (by rfl) ⟨894866, by rfl⟩ : syracuseStep 4772621 = 1789733) (by norm_num)
theorem B3181747 : Blo 1885435 3181747 := bstep (se 1 (by rfl) ⟨2386310, by rfl⟩ : syracuseStep 3181747 = 4772621) B4772621
theorem B4242329 : Blo 1885435 4242329 := bstep (se 2 (by rfl) ⟨1590873, by rfl⟩ : syracuseStep 4242329 = 3181747) B3181747
theorem B2828219 : Blo 1885435 2828219 := bstep (se 1 (by rfl) ⟨2121164, by rfl⟩ : syracuseStep 2828219 = 4242329) B4242329
theorem B1885479 : Blo 1885435 1885479 := bstep (se 1 (by rfl) ⟨1414109, by rfl⟩ : syracuseStep 1885479 = 2828219) B2828219
theorem B2121169 : Blo 1885435 2121169 := bbase (se 2 (by rfl) ⟨795438, by rfl⟩ : syracuseStep 2121169 = 1590877) (by norm_num)
theorem B2828225 : Blo 1885435 2828225 := bstep (se 2 (by rfl) ⟨1060584, by rfl⟩ : syracuseStep 2828225 = 2121169) B2121169
theorem B1885483 : Blo 1885435 1885483 := bstep (se 1 (by rfl) ⟨1414112, by rfl⟩ : syracuseStep 1885483 = 2828225) B2828225
theorem B4026917 : Blo 1885435 4026917 := bbase (se 4 (by rfl) ⟨377523, by rfl⟩ : syracuseStep 4026917 = 755047) (by norm_num)
theorem B2684611 : Blo 1885435 2684611 := bstep (se 1 (by rfl) ⟨2013458, by rfl⟩ : syracuseStep 2684611 = 4026917) B4026917
theorem B3579481 : Blo 1885435 3579481 := bstep (se 2 (by rfl) ⟨1342305, by rfl⟩ : syracuseStep 3579481 = 2684611) B2684611
theorem B4772641 : Blo 1885435 4772641 := bstep (se 2 (by rfl) ⟨1789740, by rfl⟩ : syracuseStep 4772641 = 3579481) B3579481
theorem B6363521 : Blo 1885435 6363521 := bstep (se 2 (by rfl) ⟨2386320, by rfl⟩ : syracuseStep 6363521 = 4772641) B4772641
theorem B4242347 : Blo 1885435 4242347 := bstep (se 1 (by rfl) ⟨3181760, by rfl⟩ : syracuseStep 4242347 = 6363521) B6363521
theorem B2828231 : Blo 1885435 2828231 := bstep (se 1 (by rfl) ⟨2121173, by rfl⟩ : syracuseStep 2828231 = 4242347) B4242347
theorem B1885487 : Blo 1885435 1885487 := bstep (se 1 (by rfl) ⟨1414115, by rfl⟩ : syracuseStep 1885487 = 2828231) B2828231
theorem B2828237 : Blo 1885435 2828237 := bbase (se 3 (by rfl) ⟨530294, by rfl⟩ : syracuseStep 2828237 = 1060589) (by norm_num)
theorem B1885491 : Blo 1885435 1885491 := bstep (se 1 (by rfl) ⟨1414118, by rfl⟩ : syracuseStep 1885491 = 2828237) B2828237
theorem B4242365 : Blo 1885435 4242365 := bbase (se 3 (by rfl) ⟨795443, by rfl⟩ : syracuseStep 4242365 = 1590887) (by norm_num)
theorem B2828243 : Blo 1885435 2828243 := bstep (se 1 (by rfl) ⟨2121182, by rfl⟩ : syracuseStep 2828243 = 4242365) B4242365
theorem B1885495 : Blo 1885435 1885495 := bstep (se 1 (by rfl) ⟨1414121, by rfl⟩ : syracuseStep 1885495 = 2828243) B2828243
theorem B3181781 : Blo 1885435 3181781 := bbase (se 7 (by rfl) ⟨37286, by rfl⟩ : syracuseStep 3181781 = 74573) (by norm_num)
theorem B2121187 : Blo 1885435 2121187 := bstep (se 1 (by rfl) ⟨1590890, by rfl⟩ : syracuseStep 2121187 = 3181781) B3181781
theorem B2828249 : Blo 1885435 2828249 := bstep (se 2 (by rfl) ⟨1060593, by rfl⟩ : syracuseStep 2828249 = 2121187) B2121187
theorem B1885499 : Blo 1885435 1885499 := bstep (se 1 (by rfl) ⟨1414124, by rfl⟩ : syracuseStep 1885499 = 2828249) B2828249
theorem B3020213 : Blo 1885435 3020213 := bbase (se 5 (by rfl) ⟨141572, by rfl⟩ : syracuseStep 3020213 = 283145) (by norm_num)
theorem B8053901 : Blo 1885435 8053901 := bstep (se 3 (by rfl) ⟨1510106, by rfl⟩ : syracuseStep 8053901 = 3020213) B3020213
theorem B5369267 : Blo 1885435 5369267 := bstep (se 1 (by rfl) ⟨4026950, by rfl⟩ : syracuseStep 5369267 = 8053901) B8053901
theorem B14318045 : Blo 1885435 14318045 := bstep (se 3 (by rfl) ⟨2684633, by rfl⟩ : syracuseStep 14318045 = 5369267) B5369267
theorem B9545363 : Blo 1885435 9545363 := bstep (se 1 (by rfl) ⟨7159022, by rfl⟩ : syracuseStep 9545363 = 14318045) B14318045
theorem B6363575 : Blo 1885435 6363575 := bstep (se 1 (by rfl) ⟨4772681, by rfl⟩ : syracuseStep 6363575 = 9545363) B9545363
theorem B4242383 : Blo 1885435 4242383 := bstep (se 1 (by rfl) ⟨3181787, by rfl⟩ : syracuseStep 4242383 = 6363575) B6363575
theorem B2828255 : Blo 1885435 2828255 := bstep (se 1 (by rfl) ⟨2121191, by rfl⟩ : syracuseStep 2828255 = 4242383) B4242383
theorem B1885503 : Blo 1885435 1885503 := bstep (se 1 (by rfl) ⟨1414127, by rfl⟩ : syracuseStep 1885503 = 2828255) B2828255
theorem B2828261 : Blo 1885435 2828261 := bbase (se 4 (by rfl) ⟨265149, by rfl⟩ : syracuseStep 2828261 = 530299) (by norm_num)
theorem B1885507 : Blo 1885435 1885507 := bstep (se 1 (by rfl) ⟨1414130, by rfl⟩ : syracuseStep 1885507 = 2828261) B2828261
theorem B6040453 : Blo 1885435 6040453 := bbase (se 4 (by rfl) ⟨566292, by rfl⟩ : syracuseStep 6040453 = 1132585) (by norm_num)
theorem B8053937 : Blo 1885435 8053937 := bstep (se 2 (by rfl) ⟨3020226, by rfl⟩ : syracuseStep 8053937 = 6040453) B6040453
theorem B5369291 : Blo 1885435 5369291 := bstep (se 1 (by rfl) ⟨4026968, by rfl⟩ : syracuseStep 5369291 = 8053937) B8053937
theorem B3579527 : Blo 1885435 3579527 := bstep (se 1 (by rfl) ⟨2684645, by rfl⟩ : syracuseStep 3579527 = 5369291) B5369291
theorem B2386351 : Blo 1885435 2386351 := bstep (se 1 (by rfl) ⟨1789763, by rfl⟩ : syracuseStep 2386351 = 3579527) B3579527
theorem B3181801 : Blo 1885435 3181801 := bstep (se 2 (by rfl) ⟨1193175, by rfl⟩ : syracuseStep 3181801 = 2386351) B2386351
theorem B4242401 : Blo 1885435 4242401 := bstep (se 2 (by rfl) ⟨1590900, by rfl⟩ : syracuseStep 4242401 = 3181801) B3181801
theorem B2828267 : Blo 1885435 2828267 := bstep (se 1 (by rfl) ⟨2121200, by rfl⟩ : syracuseStep 2828267 = 4242401) B4242401
theorem B1885511 : Blo 1885435 1885511 := bstep (se 1 (by rfl) ⟨1414133, by rfl⟩ : syracuseStep 1885511 = 2828267) B2828267
theorem B2121205 : Blo 1885435 2121205 := bbase (se 5 (by rfl) ⟨99431, by rfl⟩ : syracuseStep 2121205 = 198863) (by norm_num)
theorem B2828273 : Blo 1885435 2828273 := bstep (se 2 (by rfl) ⟨1060602, by rfl⟩ : syracuseStep 2828273 = 2121205) B2121205
theorem B1885515 : Blo 1885435 1885515 := bstep (se 1 (by rfl) ⟨1414136, by rfl⟩ : syracuseStep 1885515 = 2828273) B2828273
theorem B2386361 : Blo 1885435 2386361 := bbase (se 2 (by rfl) ⟨894885, by rfl⟩ : syracuseStep 2386361 = 1789771) (by norm_num)
theorem B6363629 : Blo 1885435 6363629 := bstep (se 3 (by rfl) ⟨1193180, by rfl⟩ : syracuseStep 6363629 = 2386361) B2386361
theorem B4242419 : Blo 1885435 4242419 := bstep (se 1 (by rfl) ⟨3181814, by rfl⟩ : syracuseStep 4242419 = 6363629) B6363629
theorem B2828279 : Blo 1885435 2828279 := bstep (se 1 (by rfl) ⟨2121209, by rfl⟩ : syracuseStep 2828279 = 4242419) B4242419
theorem B1885519 : Blo 1885435 1885519 := bstep (se 1 (by rfl) ⟨1414139, by rfl⟩ : syracuseStep 1885519 = 2828279) B2828279
theorem B2828285 : Blo 1885435 2828285 := bbase (se 3 (by rfl) ⟨530303, by rfl⟩ : syracuseStep 2828285 = 1060607) (by norm_num)
theorem B1885523 : Blo 1885435 1885523 := bstep (se 1 (by rfl) ⟨1414142, by rfl⟩ : syracuseStep 1885523 = 2828285) B2828285
theorem B4242437 : Blo 1885435 4242437 := bbase (se 4 (by rfl) ⟨397728, by rfl⟩ : syracuseStep 4242437 = 795457) (by norm_num)
theorem B2828291 : Blo 1885435 2828291 := bstep (se 1 (by rfl) ⟨2121218, by rfl⟩ : syracuseStep 2828291 = 4242437) B4242437
theorem B1885527 : Blo 1885435 1885527 := bstep (se 1 (by rfl) ⟨1414145, by rfl⟩ : syracuseStep 1885527 = 2828291) B2828291
theorem B3579565 : Blo 1885435 3579565 := bbase (se 3 (by rfl) ⟨671168, by rfl⟩ : syracuseStep 3579565 = 1342337) (by norm_num)
theorem B4772753 : Blo 1885435 4772753 := bstep (se 2 (by rfl) ⟨1789782, by rfl⟩ : syracuseStep 4772753 = 3579565) B3579565
theorem B3181835 : Blo 1885435 3181835 := bstep (se 1 (by rfl) ⟨2386376, by rfl⟩ : syracuseStep 3181835 = 4772753) B4772753
theorem B2121223 : Blo 1885435 2121223 := bstep (se 1 (by rfl) ⟨1590917, by rfl⟩ : syracuseStep 2121223 = 3181835) B3181835
theorem B2828297 : Blo 1885435 2828297 := bstep (se 2 (by rfl) ⟨1060611, by rfl⟩ : syracuseStep 2828297 = 2121223) B2121223
theorem B1885531 : Blo 1885435 1885531 := bstep (se 1 (by rfl) ⟨1414148, by rfl⟩ : syracuseStep 1885531 = 2828297) B2828297
theorem B9545525 : Blo 1885435 9545525 := bbase (se 5 (by rfl) ⟨447446, by rfl⟩ : syracuseStep 9545525 = 894893) (by norm_num)
theorem B6363683 : Blo 1885435 6363683 := bstep (se 1 (by rfl) ⟨4772762, by rfl⟩ : syracuseStep 6363683 = 9545525) B9545525
theorem B4242455 : Blo 1885435 4242455 := bstep (se 1 (by rfl) ⟨3181841, by rfl⟩ : syracuseStep 4242455 = 6363683) B6363683
theorem B2828303 : Blo 1885435 2828303 := bstep (se 1 (by rfl) ⟨2121227, by rfl⟩ : syracuseStep 2828303 = 4242455) B4242455
theorem B1885535 : Blo 1885435 1885535 := bstep (se 1 (by rfl) ⟨1414151, by rfl⟩ : syracuseStep 1885535 = 2828303) B2828303
theorem B2828309 : Blo 1885435 2828309 := bbase (se 6 (by rfl) ⟨66288, by rfl⟩ : syracuseStep 2828309 = 132577) (by norm_num)
theorem B1885539 : Blo 1885435 1885539 := bstep (se 1 (by rfl) ⟨1414154, by rfl⟩ : syracuseStep 1885539 = 2828309) B2828309
theorem B12081109 : Blo 1885435 12081109 := bbase (se 7 (by rfl) ⟨141575, by rfl⟩ : syracuseStep 12081109 = 283151) (by norm_num)
theorem B16108145 : Blo 1885435 16108145 := bstep (se 2 (by rfl) ⟨6040554, by rfl⟩ : syracuseStep 16108145 = 12081109) B12081109
theorem B10738763 : Blo 1885435 10738763 := bstep (se 1 (by rfl) ⟨8054072, by rfl⟩ : syracuseStep 10738763 = 16108145) B16108145
theorem B7159175 : Blo 1885435 7159175 := bstep (se 1 (by rfl) ⟨5369381, by rfl⟩ : syracuseStep 7159175 = 10738763) B10738763
theorem B4772783 : Blo 1885435 4772783 := bstep (se 1 (by rfl) ⟨3579587, by rfl⟩ : syracuseStep 4772783 = 7159175) B7159175
theorem B3181855 : Blo 1885435 3181855 := bstep (se 1 (by rfl) ⟨2386391, by rfl⟩ : syracuseStep 3181855 = 4772783) B4772783
theorem B4242473 : Blo 1885435 4242473 := bstep (se 2 (by rfl) ⟨1590927, by rfl⟩ : syracuseStep 4242473 = 3181855) B3181855
theorem B2828315 : Blo 1885435 2828315 := bstep (se 1 (by rfl) ⟨2121236, by rfl⟩ : syracuseStep 2828315 = 4242473) B4242473
theorem B1885543 : Blo 1885435 1885543 := bstep (se 1 (by rfl) ⟨1414157, by rfl⟩ : syracuseStep 1885543 = 2828315) B2828315
theorem B2121241 : Blo 1885435 2121241 := bbase (se 2 (by rfl) ⟨795465, by rfl⟩ : syracuseStep 2121241 = 1590931) (by norm_num)
theorem B2828321 : Blo 1885435 2828321 := bstep (se 2 (by rfl) ⟨1060620, by rfl⟩ : syracuseStep 2828321 = 2121241) B2121241
theorem B1885547 : Blo 1885435 1885547 := bstep (se 1 (by rfl) ⟨1414160, by rfl⟩ : syracuseStep 1885547 = 2828321) B2828321
theorem B7159205 : Blo 1885435 7159205 := bbase (se 4 (by rfl) ⟨671175, by rfl⟩ : syracuseStep 7159205 = 1342351) (by norm_num)
theorem B4772803 : Blo 1885435 4772803 := bstep (se 1 (by rfl) ⟨3579602, by rfl⟩ : syracuseStep 4772803 = 7159205) B7159205
theorem B6363737 : Blo 1885435 6363737 := bstep (se 2 (by rfl) ⟨2386401, by rfl⟩ : syracuseStep 6363737 = 4772803) B4772803
theorem B4242491 : Blo 1885435 4242491 := bstep (se 1 (by rfl) ⟨3181868, by rfl⟩ : syracuseStep 4242491 = 6363737) B6363737
theorem B2828327 : Blo 1885435 2828327 := bstep (se 1 (by rfl) ⟨2121245, by rfl⟩ : syracuseStep 2828327 = 4242491) B4242491
theorem B1885551 : Blo 1885435 1885551 := bstep (se 1 (by rfl) ⟨1414163, by rfl⟩ : syracuseStep 1885551 = 2828327) B2828327
theorem B2828333 : Blo 1885435 2828333 := bbase (se 3 (by rfl) ⟨530312, by rfl⟩ : syracuseStep 2828333 = 1060625) (by norm_num)
theorem B1885555 : Blo 1885435 1885555 := bstep (se 1 (by rfl) ⟨1414166, by rfl⟩ : syracuseStep 1885555 = 2828333) B2828333
theorem B4242509 : Blo 1885435 4242509 := bbase (se 3 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 4242509 = 1590941) (by norm_num)
theorem B2828339 : Blo 1885435 2828339 := bstep (se 1 (by rfl) ⟨2121254, by rfl⟩ : syracuseStep 2828339 = 4242509) B4242509
theorem B1885559 : Blo 1885435 1885559 := bstep (se 1 (by rfl) ⟨1414169, by rfl⟩ : syracuseStep 1885559 = 2828339) B2828339
theorem B2386417 : Blo 1885435 2386417 := bbase (se 2 (by rfl) ⟨894906, by rfl⟩ : syracuseStep 2386417 = 1789813) (by norm_num)
theorem B3181889 : Blo 1885435 3181889 := bstep (se 2 (by rfl) ⟨1193208, by rfl⟩ : syracuseStep 3181889 = 2386417) B2386417
theorem B2121259 : Blo 1885435 2121259 := bstep (se 1 (by rfl) ⟨1590944, by rfl⟩ : syracuseStep 2121259 = 3181889) B3181889
theorem B2828345 : Blo 1885435 2828345 := bstep (se 2 (by rfl) ⟨1060629, by rfl⟩ : syracuseStep 2828345 = 2121259) B2121259
theorem B1885563 : Blo 1885435 1885563 := bstep (se 1 (by rfl) ⟨1414172, by rfl⟩ : syracuseStep 1885563 = 2828345) B2828345
theorem B5442709 : Blo 1885435 5442709 := bbase (se 6 (by rfl) ⟨127563, by rfl⟩ : syracuseStep 5442709 = 255127) (by norm_num)
theorem B7256945 : Blo 1885435 7256945 := bstep (se 2 (by rfl) ⟨2721354, by rfl⟩ : syracuseStep 7256945 = 5442709) B5442709
theorem B4837963 : Blo 1885435 4837963 := bstep (se 1 (by rfl) ⟨3628472, by rfl⟩ : syracuseStep 4837963 = 7256945) B7256945
theorem B6450617 : Blo 1885435 6450617 := bstep (se 2 (by rfl) ⟨2418981, by rfl⟩ : syracuseStep 6450617 = 4837963) B4837963
theorem B17201645 : Blo 1885435 17201645 := bstep (se 3 (by rfl) ⟨3225308, by rfl⟩ : syracuseStep 17201645 = 6450617) B6450617
theorem B11467763 : Blo 1885435 11467763 := bstep (se 1 (by rfl) ⟨8600822, by rfl⟩ : syracuseStep 11467763 = 17201645) B17201645
theorem B7645175 : Blo 1885435 7645175 := bstep (se 1 (by rfl) ⟨5733881, by rfl⟩ : syracuseStep 7645175 = 11467763) B11467763
theorem B5096783 : Blo 1885435 5096783 := bstep (se 1 (by rfl) ⟨3822587, by rfl⟩ : syracuseStep 5096783 = 7645175) B7645175
theorem B13591421 : Blo 1885435 13591421 := bstep (se 3 (by rfl) ⟨2548391, by rfl⟩ : syracuseStep 13591421 = 5096783) B5096783
theorem B9060947 : Blo 1885435 9060947 := bstep (se 1 (by rfl) ⟨6795710, by rfl⟩ : syracuseStep 9060947 = 13591421) B13591421
theorem B6040631 : Blo 1885435 6040631 := bstep (se 1 (by rfl) ⟨4530473, by rfl⟩ : syracuseStep 6040631 = 9060947) B9060947
theorem B4027087 : Blo 1885435 4027087 := bstep (se 1 (by rfl) ⟨3020315, by rfl⟩ : syracuseStep 4027087 = 6040631) B6040631
theorem B21477797 : Blo 1885435 21477797 := bstep (se 4 (by rfl) ⟨2013543, by rfl⟩ : syracuseStep 21477797 = 4027087) B4027087
theorem B14318531 : Blo 1885435 14318531 := bstep (se 1 (by rfl) ⟨10738898, by rfl⟩ : syracuseStep 14318531 = 21477797) B21477797
theorem B9545687 : Blo 1885435 9545687 := bstep (se 1 (by rfl) ⟨7159265, by rfl⟩ : syracuseStep 9545687 = 14318531) B14318531
theorem B6363791 : Blo 1885435 6363791 := bstep (se 1 (by rfl) ⟨4772843, by rfl⟩ : syracuseStep 6363791 = 9545687) B9545687
theorem B4242527 : Blo 1885435 4242527 := bstep (se 1 (by rfl) ⟨3181895, by rfl⟩ : syracuseStep 4242527 = 6363791) B6363791
theorem B2828351 : Blo 1885435 2828351 := bstep (se 1 (by rfl) ⟨2121263, by rfl⟩ : syracuseStep 2828351 = 4242527) B4242527
theorem B1885567 : Blo 1885435 1885567 := bstep (se 1 (by rfl) ⟨1414175, by rfl⟩ : syracuseStep 1885567 = 2828351) B2828351
theorem B2828357 : Blo 1885435 2828357 := bbase (se 4 (by rfl) ⟨265158, by rfl⟩ : syracuseStep 2828357 = 530317) (by norm_num)
theorem B1885571 : Blo 1885435 1885571 := bstep (se 1 (by rfl) ⟨1414178, by rfl⟩ : syracuseStep 1885571 = 2828357) B2828357
theorem B3181909 : Blo 1885435 3181909 := bbase (se 11 (by rfl) ⟨2330, by rfl⟩ : syracuseStep 3181909 = 4661) (by norm_num)
theorem B4242545 : Blo 1885435 4242545 := bstep (se 2 (by rfl) ⟨1590954, by rfl⟩ : syracuseStep 4242545 = 3181909) B3181909
theorem B2828363 : Blo 1885435 2828363 := bstep (se 1 (by rfl) ⟨2121272, by rfl⟩ : syracuseStep 2828363 = 4242545) B4242545
theorem B1885575 : Blo 1885435 1885575 := bstep (se 1 (by rfl) ⟨1414181, by rfl⟩ : syracuseStep 1885575 = 2828363) B2828363
theorem B2121277 : Blo 1885435 2121277 := bbase (se 3 (by rfl) ⟨397739, by rfl⟩ : syracuseStep 2121277 = 795479) (by norm_num)
theorem B2828369 : Blo 1885435 2828369 := bstep (se 2 (by rfl) ⟨1060638, by rfl⟩ : syracuseStep 2828369 = 2121277) B2121277
theorem B1885579 : Blo 1885435 1885579 := bstep (se 1 (by rfl) ⟨1414184, by rfl⟩ : syracuseStep 1885579 = 2828369) B2828369
theorem B6363845 : Blo 1885435 6363845 := bbase (se 4 (by rfl) ⟨596610, by rfl⟩ : syracuseStep 6363845 = 1193221) (by norm_num)
theorem B4242563 : Blo 1885435 4242563 := bstep (se 1 (by rfl) ⟨3181922, by rfl⟩ : syracuseStep 4242563 = 6363845) B6363845
theorem B2828375 : Blo 1885435 2828375 := bstep (se 1 (by rfl) ⟨2121281, by rfl⟩ : syracuseStep 2828375 = 4242563) B4242563
theorem B1885583 : Blo 1885435 1885583 := bstep (se 1 (by rfl) ⟨1414187, by rfl⟩ : syracuseStep 1885583 = 2828375) B2828375
theorem B2828381 : Blo 1885435 2828381 := bbase (se 3 (by rfl) ⟨530321, by rfl⟩ : syracuseStep 2828381 = 1060643) (by norm_num)
theorem B1885587 : Blo 1885435 1885587 := bstep (se 1 (by rfl) ⟨1414190, by rfl⟩ : syracuseStep 1885587 = 2828381) B2828381
theorem B4242581 : Blo 1885435 4242581 := bbase (se 6 (by rfl) ⟨99435, by rfl⟩ : syracuseStep 4242581 = 198871) (by norm_num)
theorem B2828387 : Blo 1885435 2828387 := bstep (se 1 (by rfl) ⟨2121290, by rfl⟩ : syracuseStep 2828387 = 4242581) B4242581
theorem B1885591 : Blo 1885435 1885591 := bstep (se 1 (by rfl) ⟨1414193, by rfl⟩ : syracuseStep 1885591 = 2828387) B2828387
theorem B2684765 : Blo 1885435 2684765 := bbase (se 3 (by rfl) ⟨503393, by rfl⟩ : syracuseStep 2684765 = 1006787) (by norm_num)
theorem B7159373 : Blo 1885435 7159373 := bstep (se 3 (by rfl) ⟨1342382, by rfl⟩ : syracuseStep 7159373 = 2684765) B2684765
theorem B4772915 : Blo 1885435 4772915 := bstep (se 1 (by rfl) ⟨3579686, by rfl⟩ : syracuseStep 4772915 = 7159373) B7159373
theorem B3181943 : Blo 1885435 3181943 := bstep (se 1 (by rfl) ⟨2386457, by rfl⟩ : syracuseStep 3181943 = 4772915) B4772915
theorem B2121295 : Blo 1885435 2121295 := bstep (se 1 (by rfl) ⟨1590971, by rfl⟩ : syracuseStep 2121295 = 3181943) B3181943
theorem B2828393 : Blo 1885435 2828393 := bstep (se 2 (by rfl) ⟨1060647, by rfl⟩ : syracuseStep 2828393 = 2121295) B2121295
theorem B1885595 : Blo 1885435 1885595 := bstep (se 1 (by rfl) ⟨1414196, by rfl⟩ : syracuseStep 1885595 = 2828393) B2828393
theorem B20387477 : Blo 1885435 20387477 := bbase (se 6 (by rfl) ⟨477831, by rfl⟩ : syracuseStep 20387477 = 955663) (by norm_num)
theorem B13591651 : Blo 1885435 13591651 := bstep (se 1 (by rfl) ⟨10193738, by rfl⟩ : syracuseStep 13591651 = 20387477) B20387477
theorem B18122201 : Blo 1885435 18122201 := bstep (se 2 (by rfl) ⟨6795825, by rfl⟩ : syracuseStep 18122201 = 13591651) B13591651
theorem B12081467 : Blo 1885435 12081467 := bstep (se 1 (by rfl) ⟨9061100, by rfl⟩ : syracuseStep 12081467 = 18122201) B18122201
theorem B8054311 : Blo 1885435 8054311 := bstep (se 1 (by rfl) ⟨6040733, by rfl⟩ : syracuseStep 8054311 = 12081467) B12081467
theorem B10739081 : Blo 1885435 10739081 := bstep (se 2 (by rfl) ⟨4027155, by rfl⟩ : syracuseStep 10739081 = 8054311) B8054311
theorem B7159387 : Blo 1885435 7159387 := bstep (se 1 (by rfl) ⟨5369540, by rfl⟩ : syracuseStep 7159387 = 10739081) B10739081
theorem B9545849 : Blo 1885435 9545849 := bstep (se 2 (by rfl) ⟨3579693, by rfl⟩ : syracuseStep 9545849 = 7159387) B7159387
theorem B6363899 : Blo 1885435 6363899 := bstep (se 1 (by rfl) ⟨4772924, by rfl⟩ : syracuseStep 6363899 = 9545849) B9545849
theorem B4242599 : Blo 1885435 4242599 := bstep (se 1 (by rfl) ⟨3181949, by rfl⟩ : syracuseStep 4242599 = 6363899) B6363899
theorem B2828399 : Blo 1885435 2828399 := bstep (se 1 (by rfl) ⟨2121299, by rfl⟩ : syracuseStep 2828399 = 4242599) B4242599
theorem B1885599 : Blo 1885435 1885599 := bstep (se 1 (by rfl) ⟨1414199, by rfl⟩ : syracuseStep 1885599 = 2828399) B2828399
theorem B2828405 : Blo 1885435 2828405 := bbase (se 5 (by rfl) ⟨132581, by rfl⟩ : syracuseStep 2828405 = 265163) (by norm_num)
theorem B1885603 : Blo 1885435 1885603 := bstep (se 1 (by rfl) ⟨1414202, by rfl⟩ : syracuseStep 1885603 = 2828405) B2828405
theorem B3579709 : Blo 1885435 3579709 := bbase (se 3 (by rfl) ⟨671195, by rfl⟩ : syracuseStep 3579709 = 1342391) (by norm_num)
theorem B4772945 : Blo 1885435 4772945 := bstep (se 2 (by rfl) ⟨1789854, by rfl⟩ : syracuseStep 4772945 = 3579709) B3579709
theorem B3181963 : Blo 1885435 3181963 := bstep (se 1 (by rfl) ⟨2386472, by rfl⟩ : syracuseStep 3181963 = 4772945) B4772945
theorem B4242617 : Blo 1885435 4242617 := bstep (se 2 (by rfl) ⟨1590981, by rfl⟩ : syracuseStep 4242617 = 3181963) B3181963
theorem B2828411 : Blo 1885435 2828411 := bstep (se 1 (by rfl) ⟨2121308, by rfl⟩ : syracuseStep 2828411 = 4242617) B4242617
theorem B1885607 : Blo 1885435 1885607 := bstep (se 1 (by rfl) ⟨1414205, by rfl⟩ : syracuseStep 1885607 = 2828411) B2828411
theorem B2121313 : Blo 1885435 2121313 := bbase (se 2 (by rfl) ⟨795492, by rfl⟩ : syracuseStep 2121313 = 1590985) (by norm_num)
theorem B2828417 : Blo 1885435 2828417 := bstep (se 2 (by rfl) ⟨1060656, by rfl⟩ : syracuseStep 2828417 = 2121313) B2121313
theorem B1885611 : Blo 1885435 1885611 := bstep (se 1 (by rfl) ⟨1414208, by rfl⟩ : syracuseStep 1885611 = 2828417) B2828417
theorem B4772965 : Blo 1885435 4772965 := bbase (se 4 (by rfl) ⟨447465, by rfl⟩ : syracuseStep 4772965 = 894931) (by norm_num)
theorem B6363953 : Blo 1885435 6363953 := bstep (se 2 (by rfl) ⟨2386482, by rfl⟩ : syracuseStep 6363953 = 4772965) B4772965
theorem B4242635 : Blo 1885435 4242635 := bstep (se 1 (by rfl) ⟨3181976, by rfl⟩ : syracuseStep 4242635 = 6363953) B6363953
theorem B2828423 : Blo 1885435 2828423 := bstep (se 1 (by rfl) ⟨2121317, by rfl⟩ : syracuseStep 2828423 = 4242635) B4242635
theorem B1885615 : Blo 1885435 1885615 := bstep (se 1 (by rfl) ⟨1414211, by rfl⟩ : syracuseStep 1885615 = 2828423) B2828423
theorem B2828429 : Blo 1885435 2828429 := bbase (se 3 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 2828429 = 1060661) (by norm_num)
theorem B1885619 : Blo 1885435 1885619 := bstep (se 1 (by rfl) ⟨1414214, by rfl⟩ : syracuseStep 1885619 = 2828429) B2828429
theorem B4242653 : Blo 1885435 4242653 := bbase (se 3 (by rfl) ⟨795497, by rfl⟩ : syracuseStep 4242653 = 1590995) (by norm_num)
theorem B2828435 : Blo 1885435 2828435 := bstep (se 1 (by rfl) ⟨2121326, by rfl⟩ : syracuseStep 2828435 = 4242653) B4242653
theorem B1885623 : Blo 1885435 1885623 := bstep (se 1 (by rfl) ⟨1414217, by rfl⟩ : syracuseStep 1885623 = 2828435) B2828435
theorem B3181997 : Blo 1885435 3181997 := bbase (se 3 (by rfl) ⟨596624, by rfl⟩ : syracuseStep 3181997 = 1193249) (by norm_num)
theorem B2121331 : Blo 1885435 2121331 := bstep (se 1 (by rfl) ⟨1590998, by rfl⟩ : syracuseStep 2121331 = 3181997) B3181997
theorem B2828441 : Blo 1885435 2828441 := bstep (se 2 (by rfl) ⟨1060665, by rfl⟩ : syracuseStep 2828441 = 2121331) B2121331
theorem B1885627 : Blo 1885435 1885627 := bstep (se 1 (by rfl) ⟨1414220, by rfl⟩ : syracuseStep 1885627 = 2828441) B2828441
theorem B2041085 : Blo 1885435 2041085 := bbase (se 3 (by rfl) ⟨382703, by rfl⟩ : syracuseStep 2041085 = 765407) (by norm_num)
theorem B5442893 : Blo 1885435 5442893 := bstep (se 3 (by rfl) ⟨1020542, by rfl⟩ : syracuseStep 5442893 = 2041085) B2041085
theorem B3628595 : Blo 1885435 3628595 := bstep (se 1 (by rfl) ⟨2721446, by rfl⟩ : syracuseStep 3628595 = 5442893) B5442893
theorem B9676253 : Blo 1885435 9676253 := bstep (se 3 (by rfl) ⟨1814297, by rfl⟩ : syracuseStep 9676253 = 3628595) B3628595
theorem B6450835 : Blo 1885435 6450835 := bstep (se 1 (by rfl) ⟨4838126, by rfl⟩ : syracuseStep 6450835 = 9676253) B9676253
theorem B8601113 : Blo 1885435 8601113 := bstep (se 2 (by rfl) ⟨3225417, by rfl⟩ : syracuseStep 8601113 = 6450835) B6450835
theorem B5734075 : Blo 1885435 5734075 := bstep (se 1 (by rfl) ⟨4300556, by rfl⟩ : syracuseStep 5734075 = 8601113) B8601113
theorem B7645433 : Blo 1885435 7645433 := bstep (se 2 (by rfl) ⟨2867037, by rfl⟩ : syracuseStep 7645433 = 5734075) B5734075
theorem B81551285 : Blo 1885435 81551285 := bstep (se 5 (by rfl) ⟨3822716, by rfl⟩ : syracuseStep 81551285 = 7645433) B7645433
theorem B54367523 : Blo 1885435 54367523 := bstep (se 1 (by rfl) ⟨40775642, by rfl⟩ : syracuseStep 54367523 = 81551285) B81551285
theorem B36245015 : Blo 1885435 36245015 := bstep (se 1 (by rfl) ⟨27183761, by rfl⟩ : syracuseStep 36245015 = 54367523) B54367523
theorem B24163343 : Blo 1885435 24163343 := bstep (se 1 (by rfl) ⟨18122507, by rfl⟩ : syracuseStep 24163343 = 36245015) B36245015
theorem B16108895 : Blo 1885435 16108895 := bstep (se 1 (by rfl) ⟨12081671, by rfl⟩ : syracuseStep 16108895 = 24163343) B24163343
theorem B10739263 : Blo 1885435 10739263 := bstep (se 1 (by rfl) ⟨8054447, by rfl⟩ : syracuseStep 10739263 = 16108895) B16108895
theorem B14319017 : Blo 1885435 14319017 := bstep (se 2 (by rfl) ⟨5369631, by rfl⟩ : syracuseStep 14319017 = 10739263) B10739263
theorem B9546011 : Blo 1885435 9546011 := bstep (se 1 (by rfl) ⟨7159508, by rfl⟩ : syracuseStep 9546011 = 14319017) B14319017
theorem B6364007 : Blo 1885435 6364007 := bstep (se 1 (by rfl) ⟨4773005, by rfl⟩ : syracuseStep 6364007 = 9546011) B9546011
theorem B4242671 : Blo 1885435 4242671 := bstep (se 1 (by rfl) ⟨3182003, by rfl⟩ : syracuseStep 4242671 = 6364007) B6364007
theorem B2828447 : Blo 1885435 2828447 := bstep (se 1 (by rfl) ⟨2121335, by rfl⟩ : syracuseStep 2828447 = 4242671) B4242671
theorem B1885631 : Blo 1885435 1885631 := bstep (se 1 (by rfl) ⟨1414223, by rfl⟩ : syracuseStep 1885631 = 2828447) B2828447
theorem B2828453 : Blo 1885435 2828453 := bbase (se 4 (by rfl) ⟨265167, by rfl⟩ : syracuseStep 2828453 = 530335) (by norm_num)
theorem B1885635 : Blo 1885435 1885635 := bstep (se 1 (by rfl) ⟨1414226, by rfl⟩ : syracuseStep 1885635 = 2828453) B2828453
theorem B2386513 : Blo 1885435 2386513 := bbase (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) (by norm_num)
theorem B3182017 : Blo 1885435 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B4242689 : Blo 1885435 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B2828459 : Blo 1885435 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B1885639 : Blo 1885435 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B2121349 : Blo 1885435 2121349 := bbase (se 4 (by rfl) ⟨198876, by rfl⟩ : syracuseStep 2121349 = 397753) (by norm_num)
theorem B2828465 : Blo 1885435 2828465 := bstep (se 2 (by rfl) ⟨1060674, by rfl⟩ : syracuseStep 2828465 = 2121349) B2121349
theorem B1885643 : Blo 1885435 1885643 := bstep (se 1 (by rfl) ⟨1414232, by rfl⟩ : syracuseStep 1885643 = 2828465) B2828465
theorem B3269453 : Blo 1885435 3269453 := bbase (se 3 (by rfl) ⟨613022, by rfl⟩ : syracuseStep 3269453 = 1226045) (by norm_num)
theorem B34874165 : Blo 1885435 34874165 := bstep (se 5 (by rfl) ⟨1634726, by rfl⟩ : syracuseStep 34874165 = 3269453) B3269453
theorem B23249443 : Blo 1885435 23249443 := bstep (se 1 (by rfl) ⟨17437082, by rfl⟩ : syracuseStep 23249443 = 34874165) B34874165
theorem B30999257 : Blo 1885435 30999257 := bstep (se 2 (by rfl) ⟨11624721, by rfl⟩ : syracuseStep 30999257 = 23249443) B23249443
theorem B20666171 : Blo 1885435 20666171 := bstep (se 1 (by rfl) ⟨15499628, by rfl⟩ : syracuseStep 20666171 = 30999257) B30999257
theorem B13777447 : Blo 1885435 13777447 := bstep (se 1 (by rfl) ⟨10333085, by rfl⟩ : syracuseStep 13777447 = 20666171) B20666171
theorem B18369929 : Blo 1885435 18369929 := bstep (se 2 (by rfl) ⟨6888723, by rfl⟩ : syracuseStep 18369929 = 13777447) B13777447
theorem B48986477 : Blo 1885435 48986477 := bstep (se 3 (by rfl) ⟨9184964, by rfl⟩ : syracuseStep 48986477 = 18369929) B18369929
theorem B32657651 : Blo 1885435 32657651 := bstep (se 1 (by rfl) ⟨24493238, by rfl⟩ : syracuseStep 32657651 = 48986477) B48986477
theorem B21771767 : Blo 1885435 21771767 := bstep (se 1 (by rfl) ⟨16328825, by rfl⟩ : syracuseStep 21771767 = 32657651) B32657651
theorem B14514511 : Blo 1885435 14514511 := bstep (se 1 (by rfl) ⟨10885883, by rfl⟩ : syracuseStep 14514511 = 21771767) B21771767
theorem B19352681 : Blo 1885435 19352681 := bstep (se 2 (by rfl) ⟨7257255, by rfl⟩ : syracuseStep 19352681 = 14514511) B14514511
theorem B12901787 : Blo 1885435 12901787 := bstep (se 1 (by rfl) ⟨9676340, by rfl⟩ : syracuseStep 12901787 = 19352681) B19352681
theorem B8601191 : Blo 1885435 8601191 := bstep (se 1 (by rfl) ⟨6450893, by rfl⟩ : syracuseStep 8601191 = 12901787) B12901787
theorem B5734127 : Blo 1885435 5734127 := bstep (se 1 (by rfl) ⟨4300595, by rfl⟩ : syracuseStep 5734127 = 8601191) B8601191
theorem B3822751 : Blo 1885435 3822751 := bstep (se 1 (by rfl) ⟨2867063, by rfl⟩ : syracuseStep 3822751 = 5734127) B5734127
theorem B5097001 : Blo 1885435 5097001 := bstep (se 2 (by rfl) ⟨1911375, by rfl⟩ : syracuseStep 5097001 = 3822751) B3822751
theorem B6796001 : Blo 1885435 6796001 := bstep (se 2 (by rfl) ⟨2548500, by rfl⟩ : syracuseStep 6796001 = 5097001) B5097001
theorem B4530667 : Blo 1885435 4530667 := bstep (se 1 (by rfl) ⟨3398000, by rfl⟩ : syracuseStep 4530667 = 6796001) B6796001
theorem B6040889 : Blo 1885435 6040889 := bstep (se 2 (by rfl) ⟨2265333, by rfl⟩ : syracuseStep 6040889 = 4530667) B4530667
theorem B4027259 : Blo 1885435 4027259 := bstep (se 1 (by rfl) ⟨3020444, by rfl⟩ : syracuseStep 4027259 = 6040889) B6040889
theorem B2684839 : Blo 1885435 2684839 := bstep (se 1 (by rfl) ⟨2013629, by rfl⟩ : syracuseStep 2684839 = 4027259) B4027259
theorem B3579785 : Blo 1885435 3579785 := bstep (se 2 (by rfl) ⟨1342419, by rfl⟩ : syracuseStep 3579785 = 2684839) B2684839
theorem B2386523 : Blo 1885435 2386523 := bstep (se 1 (by rfl) ⟨1789892, by rfl⟩ : syracuseStep 2386523 = 3579785) B3579785
theorem B6364061 : Blo 1885435 6364061 := bstep (se 3 (by rfl) ⟨1193261, by rfl⟩ : syracuseStep 6364061 = 2386523) B2386523
theorem B4242707 : Blo 1885435 4242707 := bstep (se 1 (by rfl) ⟨3182030, by rfl⟩ : syracuseStep 4242707 = 6364061) B6364061
theorem B2828471 : Blo 1885435 2828471 := bstep (se 1 (by rfl) ⟨2121353, by rfl⟩ : syracuseStep 2828471 = 4242707) B4242707
theorem B1885647 : Blo 1885435 1885647 := bstep (se 1 (by rfl) ⟨1414235, by rfl⟩ : syracuseStep 1885647 = 2828471) B2828471
theorem B2828477 : Blo 1885435 2828477 := bbase (se 3 (by rfl) ⟨530339, by rfl⟩ : syracuseStep 2828477 = 1060679) (by norm_num)
theorem B1885651 : Blo 1885435 1885651 := bstep (se 1 (by rfl) ⟨1414238, by rfl⟩ : syracuseStep 1885651 = 2828477) B2828477
theorem B4242725 : Blo 1885435 4242725 := bbase (se 4 (by rfl) ⟨397755, by rfl⟩ : syracuseStep 4242725 = 795511) (by norm_num)
theorem B2828483 : Blo 1885435 2828483 := bstep (se 1 (by rfl) ⟨2121362, by rfl⟩ : syracuseStep 2828483 = 4242725) B4242725
theorem B1885655 : Blo 1885435 1885655 := bstep (se 1 (by rfl) ⟨1414241, by rfl⟩ : syracuseStep 1885655 = 2828483) B2828483
theorem B4773077 : Blo 1885435 4773077 := bbase (se 7 (by rfl) ⟨55934, by rfl⟩ : syracuseStep 4773077 = 111869) (by norm_num)
theorem B3182051 : Blo 1885435 3182051 := bstep (se 1 (by rfl) ⟨2386538, by rfl⟩ : syracuseStep 3182051 = 4773077) B4773077
theorem B2121367 : Blo 1885435 2121367 := bstep (se 1 (by rfl) ⟨1591025, by rfl⟩ : syracuseStep 2121367 = 3182051) B3182051
theorem B2828489 : Blo 1885435 2828489 := bstep (se 2 (by rfl) ⟨1060683, by rfl⟩ : syracuseStep 2828489 = 2121367) B2121367
theorem B1885659 : Blo 1885435 1885659 := bstep (se 1 (by rfl) ⟨1414244, by rfl⟩ : syracuseStep 1885659 = 2828489) B2828489
theorem B9676421 : Blo 1885435 9676421 := bbase (se 4 (by rfl) ⟨907164, by rfl⟩ : syracuseStep 9676421 = 1814329) (by norm_num)
theorem B6450947 : Blo 1885435 6450947 := bstep (se 1 (by rfl) ⟨4838210, by rfl⟩ : syracuseStep 6450947 = 9676421) B9676421
theorem B4300631 : Blo 1885435 4300631 := bstep (se 1 (by rfl) ⟨3225473, by rfl⟩ : syracuseStep 4300631 = 6450947) B6450947
theorem B2867087 : Blo 1885435 2867087 := bstep (se 1 (by rfl) ⟨2150315, by rfl⟩ : syracuseStep 2867087 = 4300631) B4300631
theorem B7645565 : Blo 1885435 7645565 := bstep (se 3 (by rfl) ⟨1433543, by rfl⟩ : syracuseStep 7645565 = 2867087) B2867087
theorem B5097043 : Blo 1885435 5097043 := bstep (se 1 (by rfl) ⟨3822782, by rfl⟩ : syracuseStep 5097043 = 7645565) B7645565
theorem B6796057 : Blo 1885435 6796057 := bstep (se 2 (by rfl) ⟨2548521, by rfl⟩ : syracuseStep 6796057 = 5097043) B5097043
theorem B9061409 : Blo 1885435 9061409 := bstep (se 2 (by rfl) ⟨3398028, by rfl⟩ : syracuseStep 9061409 = 6796057) B6796057
theorem B6040939 : Blo 1885435 6040939 := bstep (se 1 (by rfl) ⟨4530704, by rfl⟩ : syracuseStep 6040939 = 9061409) B9061409
theorem B8054585 : Blo 1885435 8054585 := bstep (se 2 (by rfl) ⟨3020469, by rfl⟩ : syracuseStep 8054585 = 6040939) B6040939
theorem B5369723 : Blo 1885435 5369723 := bstep (se 1 (by rfl) ⟨4027292, by rfl⟩ : syracuseStep 5369723 = 8054585) B8054585
theorem B3579815 : Blo 1885435 3579815 := bstep (se 1 (by rfl) ⟨2684861, by rfl⟩ : syracuseStep 3579815 = 5369723) B5369723
theorem B9546173 : Blo 1885435 9546173 := bstep (se 3 (by rfl) ⟨1789907, by rfl⟩ : syracuseStep 9546173 = 3579815) B3579815
theorem B6364115 : Blo 1885435 6364115 := bstep (se 1 (by rfl) ⟨4773086, by rfl⟩ : syracuseStep 6364115 = 9546173) B9546173
theorem B4242743 : Blo 1885435 4242743 := bstep (se 1 (by rfl) ⟨3182057, by rfl⟩ : syracuseStep 4242743 = 6364115) B6364115
theorem B2828495 : Blo 1885435 2828495 := bstep (se 1 (by rfl) ⟨2121371, by rfl⟩ : syracuseStep 2828495 = 4242743) B4242743
theorem B1885663 : Blo 1885435 1885663 := bstep (se 1 (by rfl) ⟨1414247, by rfl⟩ : syracuseStep 1885663 = 2828495) B2828495
theorem B2828501 : Blo 1885435 2828501 := bbase (se 7 (by rfl) ⟨33146, by rfl⟩ : syracuseStep 2828501 = 66293) (by norm_num)
theorem B1885667 : Blo 1885435 1885667 := bstep (se 1 (by rfl) ⟨1414250, by rfl⟩ : syracuseStep 1885667 = 2828501) B2828501
theorem B4530725 : Blo 1885435 4530725 := bbase (se 4 (by rfl) ⟨424755, by rfl⟩ : syracuseStep 4530725 = 849511) (by norm_num)
theorem B3020483 : Blo 1885435 3020483 := bstep (se 1 (by rfl) ⟨2265362, by rfl⟩ : syracuseStep 3020483 = 4530725) B4530725
theorem B2013655 : Blo 1885435 2013655 := bstep (se 1 (by rfl) ⟨1510241, by rfl⟩ : syracuseStep 2013655 = 3020483) B3020483
theorem B2684873 : Blo 1885435 2684873 := bstep (se 2 (by rfl) ⟨1006827, by rfl⟩ : syracuseStep 2684873 = 2013655) B2013655
theorem B7159661 : Blo 1885435 7159661 := bstep (se 3 (by rfl) ⟨1342436, by rfl⟩ : syracuseStep 7159661 = 2684873) B2684873
theorem B4773107 : Blo 1885435 4773107 := bstep (se 1 (by rfl) ⟨3579830, by rfl⟩ : syracuseStep 4773107 = 7159661) B7159661
theorem B3182071 : Blo 1885435 3182071 := bstep (se 1 (by rfl) ⟨2386553, by rfl⟩ : syracuseStep 3182071 = 4773107) B4773107
theorem B4242761 : Blo 1885435 4242761 := bstep (se 2 (by rfl) ⟨1591035, by rfl⟩ : syracuseStep 4242761 = 3182071) B3182071
theorem B2828507 : Blo 1885435 2828507 := bstep (se 1 (by rfl) ⟨2121380, by rfl⟩ : syracuseStep 2828507 = 4242761) B4242761
theorem B1885671 : Blo 1885435 1885671 := bstep (se 1 (by rfl) ⟨1414253, by rfl⟩ : syracuseStep 1885671 = 2828507) B2828507
theorem B2121385 : Blo 1885435 2121385 := bbase (se 2 (by rfl) ⟨795519, by rfl⟩ : syracuseStep 2121385 = 1591039) (by norm_num)
theorem B2828513 : Blo 1885435 2828513 := bstep (se 2 (by rfl) ⟨1060692, by rfl⟩ : syracuseStep 2828513 = 2121385) B2121385
theorem B1885675 : Blo 1885435 1885675 := bstep (se 1 (by rfl) ⟨1414256, by rfl⟩ : syracuseStep 1885675 = 2828513) B2828513
theorem B6123413 : Blo 1885435 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B4082275 : Blo 1885435 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B5443033 : Blo 1885435 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B7257377 : Blo 1885435 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B19353005 : Blo 1885435 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B12902003 : Blo 1885435 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B8601335 : Blo 1885435 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B5734223 : Blo 1885435 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B3822815 : Blo 1885435 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B10194173 : Blo 1885435 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B6796115 : Blo 1885435 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B4530743 : Blo 1885435 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B3020495 : Blo 1885435 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B8054653 : Blo 1885435 8054653 := bstep (se 3 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 8054653 = 3020495) B3020495
theorem B10739537 : Blo 1885435 10739537 := bstep (se 2 (by rfl) ⟨4027326, by rfl⟩ : syracuseStep 10739537 = 8054653) B8054653
theorem B7159691 : Blo 1885435 7159691 := bstep (se 1 (by rfl) ⟨5369768, by rfl⟩ : syracuseStep 7159691 = 10739537) B10739537
theorem B4773127 : Blo 1885435 4773127 := bstep (se 1 (by rfl) ⟨3579845, by rfl⟩ : syracuseStep 4773127 = 7159691) B7159691
theorem B6364169 : Blo 1885435 6364169 := bstep (se 2 (by rfl) ⟨2386563, by rfl⟩ : syracuseStep 6364169 = 4773127) B4773127
theorem B4242779 : Blo 1885435 4242779 := bstep (se 1 (by rfl) ⟨3182084, by rfl⟩ : syracuseStep 4242779 = 6364169) B6364169
theorem B2828519 : Blo 1885435 2828519 := bstep (se 1 (by rfl) ⟨2121389, by rfl⟩ : syracuseStep 2828519 = 4242779) B4242779
theorem B1885679 : Blo 1885435 1885679 := bstep (se 1 (by rfl) ⟨1414259, by rfl⟩ : syracuseStep 1885679 = 2828519) B2828519
theorem B2828525 : Blo 1885435 2828525 := bbase (se 3 (by rfl) ⟨530348, by rfl⟩ : syracuseStep 2828525 = 1060697) (by norm_num)
theorem B1885683 : Blo 1885435 1885683 := bstep (se 1 (by rfl) ⟨1414262, by rfl⟩ : syracuseStep 1885683 = 2828525) B2828525
theorem B4242797 : Blo 1885435 4242797 := bbase (se 3 (by rfl) ⟨795524, by rfl⟩ : syracuseStep 4242797 = 1591049) (by norm_num)
theorem B2828531 : Blo 1885435 2828531 := bstep (se 1 (by rfl) ⟨2121398, by rfl⟩ : syracuseStep 2828531 = 4242797) B4242797
theorem B1885687 : Blo 1885435 1885687 := bstep (se 1 (by rfl) ⟨1414265, by rfl⟩ : syracuseStep 1885687 = 2828531) B2828531
theorem B3579869 : Blo 1885435 3579869 := bbase (se 3 (by rfl) ⟨671225, by rfl⟩ : syracuseStep 3579869 = 1342451) (by norm_num)
theorem B2386579 : Blo 1885435 2386579 := bstep (se 1 (by rfl) ⟨1789934, by rfl⟩ : syracuseStep 2386579 = 3579869) B3579869
theorem B3182105 : Blo 1885435 3182105 := bstep (se 2 (by rfl) ⟨1193289, by rfl⟩ : syracuseStep 3182105 = 2386579) B2386579
theorem B2121403 : Blo 1885435 2121403 := bstep (se 1 (by rfl) ⟨1591052, by rfl⟩ : syracuseStep 2121403 = 3182105) B3182105
theorem B2828537 : Blo 1885435 2828537 := bstep (se 2 (by rfl) ⟨1060701, by rfl⟩ : syracuseStep 2828537 = 2121403) B2121403
theorem B1885691 : Blo 1885435 1885691 := bstep (se 1 (by rfl) ⟨1414268, by rfl⟩ : syracuseStep 1885691 = 2828537) B2828537
theorem B1963937 : Blo 1885435 1963937 := bbase (se 2 (by rfl) ⟨736476, by rfl⟩ : syracuseStep 1963937 = 1472953) (by norm_num)
theorem B5237165 : Blo 1885435 5237165 := bstep (se 3 (by rfl) ⟨981968, by rfl⟩ : syracuseStep 5237165 = 1963937) B1963937
theorem B3491443 : Blo 1885435 3491443 := bstep (se 1 (by rfl) ⟨2618582, by rfl⟩ : syracuseStep 3491443 = 5237165) B5237165
theorem B18621029 : Blo 1885435 18621029 := bstep (se 4 (by rfl) ⟨1745721, by rfl⟩ : syracuseStep 18621029 = 3491443) B3491443
theorem B49656077 : Blo 1885435 49656077 := bstep (se 3 (by rfl) ⟨9310514, by rfl⟩ : syracuseStep 49656077 = 18621029) B18621029
theorem B33104051 : Blo 1885435 33104051 := bstep (se 1 (by rfl) ⟨24828038, by rfl⟩ : syracuseStep 33104051 = 49656077) B49656077
theorem B22069367 : Blo 1885435 22069367 := bstep (se 1 (by rfl) ⟨16552025, by rfl⟩ : syracuseStep 22069367 = 33104051) B33104051
theorem B14712911 : Blo 1885435 14712911 := bstep (se 1 (by rfl) ⟨11034683, by rfl⟩ : syracuseStep 14712911 = 22069367) B22069367
theorem B9808607 : Blo 1885435 9808607 := bstep (se 1 (by rfl) ⟨7356455, by rfl⟩ : syracuseStep 9808607 = 14712911) B14712911
theorem B6539071 : Blo 1885435 6539071 := bstep (se 1 (by rfl) ⟨4904303, by rfl⟩ : syracuseStep 6539071 = 9808607) B9808607
theorem B8718761 : Blo 1885435 8718761 := bstep (se 2 (by rfl) ⟨3269535, by rfl⟩ : syracuseStep 8718761 = 6539071) B6539071
theorem B5812507 : Blo 1885435 5812507 := bstep (se 1 (by rfl) ⟨4359380, by rfl⟩ : syracuseStep 5812507 = 8718761) B8718761
theorem B7750009 : Blo 1885435 7750009 := bstep (se 2 (by rfl) ⟨2906253, by rfl⟩ : syracuseStep 7750009 = 5812507) B5812507
theorem B10333345 : Blo 1885435 10333345 := bstep (se 2 (by rfl) ⟨3875004, by rfl⟩ : syracuseStep 10333345 = 7750009) B7750009
theorem B13777793 : Blo 1885435 13777793 := bstep (se 2 (by rfl) ⟨5166672, by rfl⟩ : syracuseStep 13777793 = 10333345) B10333345
theorem B9185195 : Blo 1885435 9185195 := bstep (se 1 (by rfl) ⟨6888896, by rfl⟩ : syracuseStep 9185195 = 13777793) B13777793
theorem B24493853 : Blo 1885435 24493853 := bstep (se 3 (by rfl) ⟨4592597, by rfl⟩ : syracuseStep 24493853 = 9185195) B9185195
theorem B16329235 : Blo 1885435 16329235 := bstep (se 1 (by rfl) ⟨12246926, by rfl⟩ : syracuseStep 16329235 = 24493853) B24493853
theorem B21772313 : Blo 1885435 21772313 := bstep (se 2 (by rfl) ⟨8164617, by rfl⟩ : syracuseStep 21772313 = 16329235) B16329235
theorem B14514875 : Blo 1885435 14514875 := bstep (se 1 (by rfl) ⟨10886156, by rfl⟩ : syracuseStep 14514875 = 21772313) B21772313
theorem B9676583 : Blo 1885435 9676583 := bstep (se 1 (by rfl) ⟨7257437, by rfl⟩ : syracuseStep 9676583 = 14514875) B14514875
theorem B6451055 : Blo 1885435 6451055 := bstep (se 1 (by rfl) ⟨4838291, by rfl⟩ : syracuseStep 6451055 = 9676583) B9676583
theorem B4300703 : Blo 1885435 4300703 := bstep (se 1 (by rfl) ⟨3225527, by rfl⟩ : syracuseStep 4300703 = 6451055) B6451055
theorem B2867135 : Blo 1885435 2867135 := bstep (se 1 (by rfl) ⟨2150351, by rfl⟩ : syracuseStep 2867135 = 4300703) B4300703
theorem B7645693 : Blo 1885435 7645693 := bstep (se 3 (by rfl) ⟨1433567, by rfl⟩ : syracuseStep 7645693 = 2867135) B2867135
theorem B10194257 : Blo 1885435 10194257 := bstep (se 2 (by rfl) ⟨3822846, by rfl⟩ : syracuseStep 10194257 = 7645693) B7645693
theorem B6796171 : Blo 1885435 6796171 := bstep (se 1 (by rfl) ⟨5097128, by rfl⟩ : syracuseStep 6796171 = 10194257) B10194257
theorem B9061561 : Blo 1885435 9061561 := bstep (se 2 (by rfl) ⟨3398085, by rfl⟩ : syracuseStep 9061561 = 6796171) B6796171
theorem B48328325 : Blo 1885435 48328325 := bstep (se 4 (by rfl) ⟨4530780, by rfl⟩ : syracuseStep 48328325 = 9061561) B9061561
theorem B32218883 : Blo 1885435 32218883 := bstep (se 1 (by rfl) ⟨24164162, by rfl⟩ : syracuseStep 32218883 = 48328325) B48328325
theorem B21479255 : Blo 1885435 21479255 := bstep (se 1 (by rfl) ⟨16109441, by rfl⟩ : syracuseStep 21479255 = 32218883) B32218883
theorem B14319503 : Blo 1885435 14319503 := bstep (se 1 (by rfl) ⟨10739627, by rfl⟩ : syracuseStep 14319503 = 21479255) B21479255
theorem B9546335 : Blo 1885435 9546335 := bstep (se 1 (by rfl) ⟨7159751, by rfl⟩ : syracuseStep 9546335 = 14319503) B14319503
theorem B6364223 : Blo 1885435 6364223 := bstep (se 1 (by rfl) ⟨4773167, by rfl⟩ : syracuseStep 6364223 = 9546335) B9546335
theorem B4242815 : Blo 1885435 4242815 := bstep (se 1 (by rfl) ⟨3182111, by rfl⟩ : syracuseStep 4242815 = 6364223) B6364223
theorem B2828543 : Blo 1885435 2828543 := bstep (se 1 (by rfl) ⟨2121407, by rfl⟩ : syracuseStep 2828543 = 4242815) B4242815
theorem B1885695 : Blo 1885435 1885695 := bstep (se 1 (by rfl) ⟨1414271, by rfl⟩ : syracuseStep 1885695 = 2828543) B2828543
theorem B2828549 : Blo 1885435 2828549 := bbase (se 4 (by rfl) ⟨265176, by rfl⟩ : syracuseStep 2828549 = 530353) (by norm_num)
theorem B1885699 : Blo 1885435 1885699 := bstep (se 1 (by rfl) ⟨1414274, by rfl⟩ : syracuseStep 1885699 = 2828549) B2828549
theorem B3182125 : Blo 1885435 3182125 := bbase (se 3 (by rfl) ⟨596648, by rfl⟩ : syracuseStep 3182125 = 1193297) (by norm_num)
theorem B4242833 : Blo 1885435 4242833 := bstep (se 2 (by rfl) ⟨1591062, by rfl⟩ : syracuseStep 4242833 = 3182125) B3182125
theorem B2828555 : Blo 1885435 2828555 := bstep (se 1 (by rfl) ⟨2121416, by rfl⟩ : syracuseStep 2828555 = 4242833) B4242833
theorem B1885703 : Blo 1885435 1885703 := bstep (se 1 (by rfl) ⟨1414277, by rfl⟩ : syracuseStep 1885703 = 2828555) B2828555
theorem B2121421 : Blo 1885435 2121421 := bbase (se 3 (by rfl) ⟨397766, by rfl⟩ : syracuseStep 2121421 = 795533) (by norm_num)
theorem B2828561 : Blo 1885435 2828561 := bstep (se 2 (by rfl) ⟨1060710, by rfl⟩ : syracuseStep 2828561 = 2121421) B2121421
theorem B1885707 : Blo 1885435 1885707 := bstep (se 1 (by rfl) ⟨1414280, by rfl⟩ : syracuseStep 1885707 = 2828561) B2828561
theorem B6364277 : Blo 1885435 6364277 := bbase (se 5 (by rfl) ⟨298325, by rfl⟩ : syracuseStep 6364277 = 596651) (by norm_num)
theorem B4242851 : Blo 1885435 4242851 := bstep (se 1 (by rfl) ⟨3182138, by rfl⟩ : syracuseStep 4242851 = 6364277) B6364277
theorem B2828567 : Blo 1885435 2828567 := bstep (se 1 (by rfl) ⟨2121425, by rfl⟩ : syracuseStep 2828567 = 4242851) B4242851
theorem B1885711 : Blo 1885435 1885711 := bstep (se 1 (by rfl) ⟨1414283, by rfl⟩ : syracuseStep 1885711 = 2828567) B2828567
theorem B2828573 : Blo 1885435 2828573 := bbase (se 3 (by rfl) ⟨530357, by rfl⟩ : syracuseStep 2828573 = 1060715) (by norm_num)
theorem B1885715 : Blo 1885435 1885715 := bstep (se 1 (by rfl) ⟨1414286, by rfl⟩ : syracuseStep 1885715 = 2828573) B2828573
theorem B4242869 : Blo 1885435 4242869 := bbase (se 5 (by rfl) ⟨198884, by rfl⟩ : syracuseStep 4242869 = 397769) (by norm_num)
theorem B2828579 : Blo 1885435 2828579 := bstep (se 1 (by rfl) ⟨2121434, by rfl⟩ : syracuseStep 2828579 = 4242869) B4242869
theorem B1885719 : Blo 1885435 1885719 := bstep (se 1 (by rfl) ⟨1414289, by rfl⟩ : syracuseStep 1885719 = 2828579) B2828579
theorem B4027421 : Blo 1885435 4027421 := bbase (se 3 (by rfl) ⟨755141, by rfl⟩ : syracuseStep 4027421 = 1510283) (by norm_num)
theorem B10739789 : Blo 1885435 10739789 := bstep (se 3 (by rfl) ⟨2013710, by rfl⟩ : syracuseStep 10739789 = 4027421) B4027421
theorem B7159859 : Blo 1885435 7159859 := bstep (se 1 (by rfl) ⟨5369894, by rfl⟩ : syracuseStep 7159859 = 10739789) B10739789
theorem B4773239 : Blo 1885435 4773239 := bstep (se 1 (by rfl) ⟨3579929, by rfl⟩ : syracuseStep 4773239 = 7159859) B7159859
theorem B3182159 : Blo 1885435 3182159 := bstep (se 1 (by rfl) ⟨2386619, by rfl⟩ : syracuseStep 3182159 = 4773239) B4773239
theorem B2121439 : Blo 1885435 2121439 := bstep (se 1 (by rfl) ⟨1591079, by rfl⟩ : syracuseStep 2121439 = 3182159) B3182159
theorem B2828585 : Blo 1885435 2828585 := bstep (se 2 (by rfl) ⟨1060719, by rfl⟩ : syracuseStep 2828585 = 2121439) B2121439
theorem B1885723 : Blo 1885435 1885723 := bstep (se 1 (by rfl) ⟨1414292, by rfl⟩ : syracuseStep 1885723 = 2828585) B2828585
theorem B4027429 : Blo 1885435 4027429 := bbase (se 4 (by rfl) ⟨377571, by rfl⟩ : syracuseStep 4027429 = 755143) (by norm_num)
theorem B5369905 : Blo 1885435 5369905 := bstep (se 2 (by rfl) ⟨2013714, by rfl⟩ : syracuseStep 5369905 = 4027429) B4027429
theorem B7159873 : Blo 1885435 7159873 := bstep (se 2 (by rfl) ⟨2684952, by rfl⟩ : syracuseStep 7159873 = 5369905) B5369905
theorem B9546497 : Blo 1885435 9546497 := bstep (se 2 (by rfl) ⟨3579936, by rfl⟩ : syracuseStep 9546497 = 7159873) B7159873
theorem B6364331 : Blo 1885435 6364331 := bstep (se 1 (by rfl) ⟨4773248, by rfl⟩ : syracuseStep 6364331 = 9546497) B9546497
theorem B4242887 : Blo 1885435 4242887 := bstep (se 1 (by rfl) ⟨3182165, by rfl⟩ : syracuseStep 4242887 = 6364331) B6364331
theorem B2828591 : Blo 1885435 2828591 := bstep (se 1 (by rfl) ⟨2121443, by rfl⟩ : syracuseStep 2828591 = 4242887) B4242887
theorem B1885727 : Blo 1885435 1885727 := bstep (se 1 (by rfl) ⟨1414295, by rfl⟩ : syracuseStep 1885727 = 2828591) B2828591
theorem B2828597 : Blo 1885435 2828597 := bbase (se 5 (by rfl) ⟨132590, by rfl⟩ : syracuseStep 2828597 = 265181) (by norm_num)
theorem B1885731 : Blo 1885435 1885731 := bstep (se 1 (by rfl) ⟨1414298, by rfl⟩ : syracuseStep 1885731 = 2828597) B2828597
theorem B4773269 : Blo 1885435 4773269 := bbase (se 6 (by rfl) ⟨111873, by rfl⟩ : syracuseStep 4773269 = 223747) (by norm_num)
theorem B3182179 : Blo 1885435 3182179 := bstep (se 1 (by rfl) ⟨2386634, by rfl⟩ : syracuseStep 3182179 = 4773269) B4773269
theorem B4242905 : Blo 1885435 4242905 := bstep (se 2 (by rfl) ⟨1591089, by rfl⟩ : syracuseStep 4242905 = 3182179) B3182179
theorem B2828603 : Blo 1885435 2828603 := bstep (se 1 (by rfl) ⟨2121452, by rfl⟩ : syracuseStep 2828603 = 4242905) B4242905
theorem B1885735 : Blo 1885435 1885735 := bstep (se 1 (by rfl) ⟨1414301, by rfl⟩ : syracuseStep 1885735 = 2828603) B2828603
theorem B2121457 : Blo 1885435 2121457 := bbase (se 2 (by rfl) ⟨795546, by rfl⟩ : syracuseStep 2121457 = 1591093) (by norm_num)
theorem B2828609 : Blo 1885435 2828609 := bstep (se 2 (by rfl) ⟨1060728, by rfl⟩ : syracuseStep 2828609 = 2121457) B2121457
theorem B1885739 : Blo 1885435 1885739 := bstep (se 1 (by rfl) ⟨1414304, by rfl⟩ : syracuseStep 1885739 = 2828609) B2828609
theorem B4300813 : Blo 1885435 4300813 := bbase (se 3 (by rfl) ⟨806402, by rfl⟩ : syracuseStep 4300813 = 1612805) (by norm_num)
theorem B5734417 : Blo 1885435 5734417 := bstep (se 2 (by rfl) ⟨2150406, by rfl⟩ : syracuseStep 5734417 = 4300813) B4300813
theorem B7645889 : Blo 1885435 7645889 := bstep (se 2 (by rfl) ⟨2867208, by rfl⟩ : syracuseStep 7645889 = 5734417) B5734417
theorem B5097259 : Blo 1885435 5097259 := bstep (se 1 (by rfl) ⟨3822944, by rfl⟩ : syracuseStep 5097259 = 7645889) B7645889
theorem B27185381 : Blo 1885435 27185381 := bstep (se 4 (by rfl) ⟨2548629, by rfl⟩ : syracuseStep 27185381 = 5097259) B5097259
theorem B18123587 : Blo 1885435 18123587 := bstep (se 1 (by rfl) ⟨13592690, by rfl⟩ : syracuseStep 18123587 = 27185381) B27185381
theorem B12082391 : Blo 1885435 12082391 := bstep (se 1 (by rfl) ⟨9061793, by rfl⟩ : syracuseStep 12082391 = 18123587) B18123587
theorem B8054927 : Blo 1885435 8054927 := bstep (se 1 (by rfl) ⟨6041195, by rfl⟩ : syracuseStep 8054927 = 12082391) B12082391
theorem B5369951 : Blo 1885435 5369951 := bstep (se 1 (by rfl) ⟨4027463, by rfl⟩ : syracuseStep 5369951 = 8054927) B8054927
theorem B3579967 : Blo 1885435 3579967 := bstep (se 1 (by rfl) ⟨2684975, by rfl⟩ : syracuseStep 3579967 = 5369951) B5369951
theorem B4773289 : Blo 1885435 4773289 := bstep (se 2 (by rfl) ⟨1789983, by rfl⟩ : syracuseStep 4773289 = 3579967) B3579967
theorem B6364385 : Blo 1885435 6364385 := bstep (se 2 (by rfl) ⟨2386644, by rfl⟩ : syracuseStep 6364385 = 4773289) B4773289
theorem B4242923 : Blo 1885435 4242923 := bstep (se 1 (by rfl) ⟨3182192, by rfl⟩ : syracuseStep 4242923 = 6364385) B6364385
theorem B2828615 : Blo 1885435 2828615 := bstep (se 1 (by rfl) ⟨2121461, by rfl⟩ : syracuseStep 2828615 = 4242923) B4242923
theorem B1885743 : Blo 1885435 1885743 := bstep (se 1 (by rfl) ⟨1414307, by rfl⟩ : syracuseStep 1885743 = 2828615) B2828615
theorem B2828621 : Blo 1885435 2828621 := bbase (se 3 (by rfl) ⟨530366, by rfl⟩ : syracuseStep 2828621 = 1060733) (by norm_num)
theorem B1885747 : Blo 1885435 1885747 := bstep (se 1 (by rfl) ⟨1414310, by rfl⟩ : syracuseStep 1885747 = 2828621) B2828621
theorem B4242941 : Blo 1885435 4242941 := bbase (se 3 (by rfl) ⟨795551, by rfl⟩ : syracuseStep 4242941 = 1591103) (by norm_num)
theorem B2828627 : Blo 1885435 2828627 := bstep (se 1 (by rfl) ⟨2121470, by rfl⟩ : syracuseStep 2828627 = 4242941) B4242941
theorem B1885751 : Blo 1885435 1885751 := bstep (se 1 (by rfl) ⟨1414313, by rfl⟩ : syracuseStep 1885751 = 2828627) B2828627
theorem B3182213 : Blo 1885435 3182213 := bbase (se 4 (by rfl) ⟨298332, by rfl⟩ : syracuseStep 3182213 = 596665) (by norm_num)
theorem B2121475 : Blo 1885435 2121475 := bstep (se 1 (by rfl) ⟨1591106, by rfl⟩ : syracuseStep 2121475 = 3182213) B3182213
theorem B2828633 : Blo 1885435 2828633 := bstep (se 2 (by rfl) ⟨1060737, by rfl⟩ : syracuseStep 2828633 = 2121475) B2121475
theorem B1885755 : Blo 1885435 1885755 := bstep (se 1 (by rfl) ⟨1414316, by rfl⟩ : syracuseStep 1885755 = 2828633) B2828633
theorem B14319989 : Blo 1885435 14319989 := bbase (se 5 (by rfl) ⟨671249, by rfl⟩ : syracuseStep 14319989 = 1342499) (by norm_num)
theorem B9546659 : Blo 1885435 9546659 := bstep (se 1 (by rfl) ⟨7159994, by rfl⟩ : syracuseStep 9546659 = 14319989) B14319989
theorem B6364439 : Blo 1885435 6364439 := bstep (se 1 (by rfl) ⟨4773329, by rfl⟩ : syracuseStep 6364439 = 9546659) B9546659
theorem B4242959 : Blo 1885435 4242959 := bstep (se 1 (by rfl) ⟨3182219, by rfl⟩ : syracuseStep 4242959 = 6364439) B6364439
theorem B2828639 : Blo 1885435 2828639 := bstep (se 1 (by rfl) ⟨2121479, by rfl⟩ : syracuseStep 2828639 = 4242959) B4242959
theorem B1885759 : Blo 1885435 1885759 := bstep (se 1 (by rfl) ⟨1414319, by rfl⟩ : syracuseStep 1885759 = 2828639) B2828639
theorem B2828645 : Blo 1885435 2828645 := bbase (se 4 (by rfl) ⟨265185, by rfl⟩ : syracuseStep 2828645 = 530371) (by norm_num)
theorem B1885763 : Blo 1885435 1885763 := bstep (se 1 (by rfl) ⟨1414322, by rfl⟩ : syracuseStep 1885763 = 2828645) B2828645
theorem B3580013 : Blo 1885435 3580013 := bbase (se 3 (by rfl) ⟨671252, by rfl⟩ : syracuseStep 3580013 = 1342505) (by norm_num)
theorem B2386675 : Blo 1885435 2386675 := bstep (se 1 (by rfl) ⟨1790006, by rfl⟩ : syracuseStep 2386675 = 3580013) B3580013
theorem B3182233 : Blo 1885435 3182233 := bstep (se 2 (by rfl) ⟨1193337, by rfl⟩ : syracuseStep 3182233 = 2386675) B2386675
theorem B4242977 : Blo 1885435 4242977 := bstep (se 2 (by rfl) ⟨1591116, by rfl⟩ : syracuseStep 4242977 = 3182233) B3182233
theorem B2828651 : Blo 1885435 2828651 := bstep (se 1 (by rfl) ⟨2121488, by rfl⟩ : syracuseStep 2828651 = 4242977) B4242977
theorem B1885767 : Blo 1885435 1885767 := bstep (se 1 (by rfl) ⟨1414325, by rfl⟩ : syracuseStep 1885767 = 2828651) B2828651
theorem B2121493 : Blo 1885435 2121493 := bbase (se 6 (by rfl) ⟨49722, by rfl⟩ : syracuseStep 2121493 = 99445) (by norm_num)
theorem B2828657 : Blo 1885435 2828657 := bstep (se 2 (by rfl) ⟨1060746, by rfl⟩ : syracuseStep 2828657 = 2121493) B2121493
theorem B1885771 : Blo 1885435 1885771 := bstep (se 1 (by rfl) ⟨1414328, by rfl⟩ : syracuseStep 1885771 = 2828657) B2828657
theorem B2386685 : Blo 1885435 2386685 := bbase (se 3 (by rfl) ⟨447503, by rfl⟩ : syracuseStep 2386685 = 895007) (by norm_num)
theorem B6364493 : Blo 1885435 6364493 := bstep (se 3 (by rfl) ⟨1193342, by rfl⟩ : syracuseStep 6364493 = 2386685) B2386685
theorem B4242995 : Blo 1885435 4242995 := bstep (se 1 (by rfl) ⟨3182246, by rfl⟩ : syracuseStep 4242995 = 6364493) B6364493
theorem B2828663 : Blo 1885435 2828663 := bstep (se 1 (by rfl) ⟨2121497, by rfl⟩ : syracuseStep 2828663 = 4242995) B4242995
theorem B1885775 : Blo 1885435 1885775 := bstep (se 1 (by rfl) ⟨1414331, by rfl⟩ : syracuseStep 1885775 = 2828663) B2828663
theorem B2828669 : Blo 1885435 2828669 := bbase (se 3 (by rfl) ⟨530375, by rfl⟩ : syracuseStep 2828669 = 1060751) (by norm_num)
theorem B1885779 : Blo 1885435 1885779 := bstep (se 1 (by rfl) ⟨1414334, by rfl⟩ : syracuseStep 1885779 = 2828669) B2828669
theorem B4243013 : Blo 1885435 4243013 := bbase (se 4 (by rfl) ⟨397782, by rfl⟩ : syracuseStep 4243013 = 795565) (by norm_num)
theorem B2828675 : Blo 1885435 2828675 := bstep (se 1 (by rfl) ⟨2121506, by rfl⟩ : syracuseStep 2828675 = 4243013) B4243013
theorem B1885783 : Blo 1885435 1885783 := bstep (se 1 (by rfl) ⟨1414337, by rfl⟩ : syracuseStep 1885783 = 2828675) B2828675
theorem B3020669 : Blo 1885435 3020669 := bbase (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) (by norm_num)
theorem B2013779 : Blo 1885435 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B5370077 : Blo 1885435 5370077 := bstep (se 3 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 5370077 = 2013779) B2013779
theorem B3580051 : Blo 1885435 3580051 := bstep (se 1 (by rfl) ⟨2685038, by rfl⟩ : syracuseStep 3580051 = 5370077) B5370077
theorem B4773401 : Blo 1885435 4773401 := bstep (se 2 (by rfl) ⟨1790025, by rfl⟩ : syracuseStep 4773401 = 3580051) B3580051
theorem B3182267 : Blo 1885435 3182267 := bstep (se 1 (by rfl) ⟨2386700, by rfl⟩ : syracuseStep 3182267 = 4773401) B4773401
theorem B2121511 : Blo 1885435 2121511 := bstep (se 1 (by rfl) ⟨1591133, by rfl⟩ : syracuseStep 2121511 = 3182267) B3182267
theorem B2828681 : Blo 1885435 2828681 := bstep (se 2 (by rfl) ⟨1060755, by rfl⟩ : syracuseStep 2828681 = 2121511) B2121511
theorem B1885787 : Blo 1885435 1885787 := bstep (se 1 (by rfl) ⟨1414340, by rfl⟩ : syracuseStep 1885787 = 2828681) B2828681
theorem B9546821 : Blo 1885435 9546821 := bbase (se 4 (by rfl) ⟨895014, by rfl⟩ : syracuseStep 9546821 = 1790029) (by norm_num)
theorem B6364547 : Blo 1885435 6364547 := bstep (se 1 (by rfl) ⟨4773410, by rfl⟩ : syracuseStep 6364547 = 9546821) B9546821
theorem B4243031 : Blo 1885435 4243031 := bstep (se 1 (by rfl) ⟨3182273, by rfl⟩ : syracuseStep 4243031 = 6364547) B6364547
theorem B2828687 : Blo 1885435 2828687 := bstep (se 1 (by rfl) ⟨2121515, by rfl⟩ : syracuseStep 2828687 = 4243031) B4243031
theorem B1885791 : Blo 1885435 1885791 := bstep (se 1 (by rfl) ⟨1414343, by rfl⟩ : syracuseStep 1885791 = 2828687) B2828687
theorem B2828693 : Blo 1885435 2828693 := bbase (se 6 (by rfl) ⟨66297, by rfl⟩ : syracuseStep 2828693 = 132595) (by norm_num)
theorem B1885795 : Blo 1885435 1885795 := bstep (se 1 (by rfl) ⟨1414346, by rfl⟩ : syracuseStep 1885795 = 2828693) B2828693
theorem B3061901 : Blo 1885435 3061901 := bbase (se 3 (by rfl) ⟨574106, by rfl⟩ : syracuseStep 3061901 = 1148213) (by norm_num)
theorem B8165069 : Blo 1885435 8165069 := bstep (se 3 (by rfl) ⟨1530950, by rfl⟩ : syracuseStep 8165069 = 3061901) B3061901
theorem B5443379 : Blo 1885435 5443379 := bstep (se 1 (by rfl) ⟨4082534, by rfl⟩ : syracuseStep 5443379 = 8165069) B8165069
theorem B3628919 : Blo 1885435 3628919 := bstep (se 1 (by rfl) ⟨2721689, by rfl⟩ : syracuseStep 3628919 = 5443379) B5443379
theorem B9677117 : Blo 1885435 9677117 := bstep (se 3 (by rfl) ⟨1814459, by rfl⟩ : syracuseStep 9677117 = 3628919) B3628919
theorem B6451411 : Blo 1885435 6451411 := bstep (se 1 (by rfl) ⟨4838558, by rfl⟩ : syracuseStep 6451411 = 9677117) B9677117
theorem B8601881 : Blo 1885435 8601881 := bstep (se 2 (by rfl) ⟨3225705, by rfl⟩ : syracuseStep 8601881 = 6451411) B6451411
theorem B22938349 : Blo 1885435 22938349 := bstep (se 3 (by rfl) ⟨4300940, by rfl⟩ : syracuseStep 22938349 = 8601881) B8601881
theorem B30584465 : Blo 1885435 30584465 := bstep (se 2 (by rfl) ⟨11469174, by rfl⟩ : syracuseStep 30584465 = 22938349) B22938349
theorem B20389643 : Blo 1885435 20389643 := bstep (se 1 (by rfl) ⟨15292232, by rfl⟩ : syracuseStep 20389643 = 30584465) B30584465
theorem B13593095 : Blo 1885435 13593095 := bstep (se 1 (by rfl) ⟨10194821, by rfl⟩ : syracuseStep 13593095 = 20389643) B20389643
theorem B9062063 : Blo 1885435 9062063 := bstep (se 1 (by rfl) ⟨6796547, by rfl⟩ : syracuseStep 9062063 = 13593095) B13593095
theorem B6041375 : Blo 1885435 6041375 := bstep (se 1 (by rfl) ⟨4531031, by rfl⟩ : syracuseStep 6041375 = 9062063) B9062063
theorem B4027583 : Blo 1885435 4027583 := bstep (se 1 (by rfl) ⟨3020687, by rfl⟩ : syracuseStep 4027583 = 6041375) B6041375
theorem B10740221 : Blo 1885435 10740221 := bstep (se 3 (by rfl) ⟨2013791, by rfl⟩ : syracuseStep 10740221 = 4027583) B4027583
theorem B7160147 : Blo 1885435 7160147 := bstep (se 1 (by rfl) ⟨5370110, by rfl⟩ : syracuseStep 7160147 = 10740221) B10740221
theorem B4773431 : Blo 1885435 4773431 := bstep (se 1 (by rfl) ⟨3580073, by rfl⟩ : syracuseStep 4773431 = 7160147) B7160147
theorem B3182287 : Blo 1885435 3182287 := bstep (se 1 (by rfl) ⟨2386715, by rfl⟩ : syracuseStep 3182287 = 4773431) B4773431
theorem B4243049 : Blo 1885435 4243049 := bstep (se 2 (by rfl) ⟨1591143, by rfl⟩ : syracuseStep 4243049 = 3182287) B3182287
theorem B2828699 : Blo 1885435 2828699 := bstep (se 1 (by rfl) ⟨2121524, by rfl⟩ : syracuseStep 2828699 = 4243049) B4243049
theorem B1885799 : Blo 1885435 1885799 := bstep (se 1 (by rfl) ⟨1414349, by rfl⟩ : syracuseStep 1885799 = 2828699) B2828699
theorem B2121529 : Blo 1885435 2121529 := bbase (se 2 (by rfl) ⟨795573, by rfl⟩ : syracuseStep 2121529 = 1591147) (by norm_num)
theorem B2828705 : Blo 1885435 2828705 := bstep (se 2 (by rfl) ⟨1060764, by rfl⟩ : syracuseStep 2828705 = 2121529) B2121529
theorem B1885803 : Blo 1885435 1885803 := bstep (se 1 (by rfl) ⟨1414352, by rfl⟩ : syracuseStep 1885803 = 2828705) B2828705
theorem B5370133 : Blo 1885435 5370133 := bbase (se 6 (by rfl) ⟨125862, by rfl⟩ : syracuseStep 5370133 = 251725) (by norm_num)
theorem B7160177 : Blo 1885435 7160177 := bstep (se 2 (by rfl) ⟨2685066, by rfl⟩ : syracuseStep 7160177 = 5370133) B5370133
theorem B4773451 : Blo 1885435 4773451 := bstep (se 1 (by rfl) ⟨3580088, by rfl⟩ : syracuseStep 4773451 = 7160177) B7160177
theorem B6364601 : Blo 1885435 6364601 := bstep (se 2 (by rfl) ⟨2386725, by rfl⟩ : syracuseStep 6364601 = 4773451) B4773451
theorem B4243067 : Blo 1885435 4243067 := bstep (se 1 (by rfl) ⟨3182300, by rfl⟩ : syracuseStep 4243067 = 6364601) B6364601
theorem B2828711 : Blo 1885435 2828711 := bstep (se 1 (by rfl) ⟨2121533, by rfl⟩ : syracuseStep 2828711 = 4243067) B4243067
theorem B1885807 : Blo 1885435 1885807 := bstep (se 1 (by rfl) ⟨1414355, by rfl⟩ : syracuseStep 1885807 = 2828711) B2828711
theorem B2828717 : Blo 1885435 2828717 := bbase (se 3 (by rfl) ⟨530384, by rfl⟩ : syracuseStep 2828717 = 1060769) (by norm_num)
theorem B1885811 : Blo 1885435 1885811 := bstep (se 1 (by rfl) ⟨1414358, by rfl⟩ : syracuseStep 1885811 = 2828717) B2828717
theorem B4243085 : Blo 1885435 4243085 := bbase (se 3 (by rfl) ⟨795578, by rfl⟩ : syracuseStep 4243085 = 1591157) (by norm_num)
theorem B2828723 : Blo 1885435 2828723 := bstep (se 1 (by rfl) ⟨2121542, by rfl⟩ : syracuseStep 2828723 = 4243085) B4243085
theorem B1885815 : Blo 1885435 1885815 := bstep (se 1 (by rfl) ⟨1414361, by rfl⟩ : syracuseStep 1885815 = 2828723) B2828723
theorem B2386741 : Blo 1885435 2386741 := bbase (se 5 (by rfl) ⟨111878, by rfl⟩ : syracuseStep 2386741 = 223757) (by norm_num)
theorem B3182321 : Blo 1885435 3182321 := bstep (se 2 (by rfl) ⟨1193370, by rfl⟩ : syracuseStep 3182321 = 2386741) B2386741
theorem B2121547 : Blo 1885435 2121547 := bstep (se 1 (by rfl) ⟨1591160, by rfl⟩ : syracuseStep 2121547 = 3182321) B3182321
theorem B2828729 : Blo 1885435 2828729 := bstep (se 2 (by rfl) ⟨1060773, by rfl⟩ : syracuseStep 2828729 = 2121547) B2121547
theorem B1885819 : Blo 1885435 1885819 := bstep (se 1 (by rfl) ⟨1414364, by rfl⟩ : syracuseStep 1885819 = 2828729) B2828729
theorem B9677237 : Blo 1885435 9677237 := bbase (se 5 (by rfl) ⟨453620, by rfl⟩ : syracuseStep 9677237 = 907241) (by norm_num)
theorem B25805965 : Blo 1885435 25805965 := bstep (se 3 (by rfl) ⟨4838618, by rfl⟩ : syracuseStep 25805965 = 9677237) B9677237
theorem B34407953 : Blo 1885435 34407953 := bstep (se 2 (by rfl) ⟨12902982, by rfl⟩ : syracuseStep 34407953 = 25805965) B25805965
theorem B22938635 : Blo 1885435 22938635 := bstep (se 1 (by rfl) ⟨17203976, by rfl⟩ : syracuseStep 22938635 = 34407953) B34407953
theorem B15292423 : Blo 1885435 15292423 := bstep (se 1 (by rfl) ⟨11469317, by rfl⟩ : syracuseStep 15292423 = 22938635) B22938635
theorem B20389897 : Blo 1885435 20389897 := bstep (se 2 (by rfl) ⟨7646211, by rfl⟩ : syracuseStep 20389897 = 15292423) B15292423
theorem B27186529 : Blo 1885435 27186529 := bstep (se 2 (by rfl) ⟨10194948, by rfl⟩ : syracuseStep 27186529 = 20389897) B20389897
theorem B36248705 : Blo 1885435 36248705 := bstep (se 2 (by rfl) ⟨13593264, by rfl⟩ : syracuseStep 36248705 = 27186529) B27186529
theorem B24165803 : Blo 1885435 24165803 := bstep (se 1 (by rfl) ⟨18124352, by rfl⟩ : syracuseStep 24165803 = 36248705) B36248705
theorem B16110535 : Blo 1885435 16110535 := bstep (se 1 (by rfl) ⟨12082901, by rfl⟩ : syracuseStep 16110535 = 24165803) B24165803
theorem B21480713 : Blo 1885435 21480713 := bstep (se 2 (by rfl) ⟨8055267, by rfl⟩ : syracuseStep 21480713 = 16110535) B16110535
theorem B14320475 : Blo 1885435 14320475 := bstep (se 1 (by rfl) ⟨10740356, by rfl⟩ : syracuseStep 14320475 = 21480713) B21480713
theorem B9546983 : Blo 1885435 9546983 := bstep (se 1 (by rfl) ⟨7160237, by rfl⟩ : syracuseStep 9546983 = 14320475) B14320475
theorem B6364655 : Blo 1885435 6364655 := bstep (se 1 (by rfl) ⟨4773491, by rfl⟩ : syracuseStep 6364655 = 9546983) B9546983
theorem B4243103 : Blo 1885435 4243103 := bstep (se 1 (by rfl) ⟨3182327, by rfl⟩ : syracuseStep 4243103 = 6364655) B6364655
theorem B2828735 : Blo 1885435 2828735 := bstep (se 1 (by rfl) ⟨2121551, by rfl⟩ : syracuseStep 2828735 = 4243103) B4243103
theorem B1885823 : Blo 1885435 1885823 := bstep (se 1 (by rfl) ⟨1414367, by rfl⟩ : syracuseStep 1885823 = 2828735) B2828735
theorem B2828741 : Blo 1885435 2828741 := bbase (se 4 (by rfl) ⟨265194, by rfl⟩ : syracuseStep 2828741 = 530389) (by norm_num)
theorem B1885827 : Blo 1885435 1885827 := bstep (se 1 (by rfl) ⟨1414370, by rfl⟩ : syracuseStep 1885827 = 2828741) B2828741
theorem B3182341 : Blo 1885435 3182341 := bbase (se 4 (by rfl) ⟨298344, by rfl⟩ : syracuseStep 3182341 = 596689) (by norm_num)
theorem B4243121 : Blo 1885435 4243121 := bstep (se 2 (by rfl) ⟨1591170, by rfl⟩ : syracuseStep 4243121 = 3182341) B3182341
theorem B2828747 : Blo 1885435 2828747 := bstep (se 1 (by rfl) ⟨2121560, by rfl⟩ : syracuseStep 2828747 = 4243121) B4243121
theorem B1885831 : Blo 1885435 1885831 := bstep (se 1 (by rfl) ⟨1414373, by rfl⟩ : syracuseStep 1885831 = 2828747) B2828747
theorem B2121565 : Blo 1885435 2121565 := bbase (se 3 (by rfl) ⟨397793, by rfl⟩ : syracuseStep 2121565 = 795587) (by norm_num)
theorem B2828753 : Blo 1885435 2828753 := bstep (se 2 (by rfl) ⟨1060782, by rfl⟩ : syracuseStep 2828753 = 2121565) B2121565
theorem B1885835 : Blo 1885435 1885835 := bstep (se 1 (by rfl) ⟨1414376, by rfl⟩ : syracuseStep 1885835 = 2828753) B2828753
theorem B6364709 : Blo 1885435 6364709 := bbase (se 4 (by rfl) ⟨596691, by rfl⟩ : syracuseStep 6364709 = 1193383) (by norm_num)
theorem B4243139 : Blo 1885435 4243139 := bstep (se 1 (by rfl) ⟨3182354, by rfl⟩ : syracuseStep 4243139 = 6364709) B6364709
theorem B2828759 : Blo 1885435 2828759 := bstep (se 1 (by rfl) ⟨2121569, by rfl⟩ : syracuseStep 2828759 = 4243139) B4243139
theorem B1885839 : Blo 1885435 1885839 := bstep (se 1 (by rfl) ⟨1414379, by rfl⟩ : syracuseStep 1885839 = 2828759) B2828759
theorem B2828765 : Blo 1885435 2828765 := bbase (se 3 (by rfl) ⟨530393, by rfl⟩ : syracuseStep 2828765 = 1060787) (by norm_num)
theorem B1885843 : Blo 1885435 1885843 := bstep (se 1 (by rfl) ⟨1414382, by rfl⟩ : syracuseStep 1885843 = 2828765) B2828765
theorem B4243157 : Blo 1885435 4243157 := bbase (se 7 (by rfl) ⟨49724, by rfl⟩ : syracuseStep 4243157 = 99449) (by norm_num)
theorem B2828771 : Blo 1885435 2828771 := bstep (se 1 (by rfl) ⟨2121578, by rfl⟩ : syracuseStep 2828771 = 4243157) B4243157
theorem B1885847 : Blo 1885435 1885847 := bstep (se 1 (by rfl) ⟨1414385, by rfl⟩ : syracuseStep 1885847 = 2828771) B2828771
theorem B4531157 : Blo 1885435 4531157 := bbase (se 7 (by rfl) ⟨53099, by rfl⟩ : syracuseStep 4531157 = 106199) (by norm_num)
theorem B3020771 : Blo 1885435 3020771 := bstep (se 1 (by rfl) ⟨2265578, by rfl⟩ : syracuseStep 3020771 = 4531157) B4531157
theorem B8055389 : Blo 1885435 8055389 := bstep (se 3 (by rfl) ⟨1510385, by rfl⟩ : syracuseStep 8055389 = 3020771) B3020771
theorem B5370259 : Blo 1885435 5370259 := bstep (se 1 (by rfl) ⟨4027694, by rfl⟩ : syracuseStep 5370259 = 8055389) B8055389
theorem B7160345 : Blo 1885435 7160345 := bstep (se 2 (by rfl) ⟨2685129, by rfl⟩ : syracuseStep 7160345 = 5370259) B5370259
theorem B4773563 : Blo 1885435 4773563 := bstep (se 1 (by rfl) ⟨3580172, by rfl⟩ : syracuseStep 4773563 = 7160345) B7160345
theorem B3182375 : Blo 1885435 3182375 := bstep (se 1 (by rfl) ⟨2386781, by rfl⟩ : syracuseStep 3182375 = 4773563) B4773563
theorem B2121583 : Blo 1885435 2121583 := bstep (se 1 (by rfl) ⟨1591187, by rfl⟩ : syracuseStep 2121583 = 3182375) B3182375
theorem B2828777 : Blo 1885435 2828777 := bstep (se 2 (by rfl) ⟨1060791, by rfl⟩ : syracuseStep 2828777 = 2121583) B2121583
theorem B1885851 : Blo 1885435 1885851 := bstep (se 1 (by rfl) ⟨1414388, by rfl⟩ : syracuseStep 1885851 = 2828777) B2828777
theorem B18124661 : Blo 1885435 18124661 := bbase (se 5 (by rfl) ⟨849593, by rfl⟩ : syracuseStep 18124661 = 1699187) (by norm_num)
theorem B12083107 : Blo 1885435 12083107 := bstep (se 1 (by rfl) ⟨9062330, by rfl⟩ : syracuseStep 12083107 = 18124661) B18124661
theorem B16110809 : Blo 1885435 16110809 := bstep (se 2 (by rfl) ⟨6041553, by rfl⟩ : syracuseStep 16110809 = 12083107) B12083107
theorem B10740539 : Blo 1885435 10740539 := bstep (se 1 (by rfl) ⟨8055404, by rfl⟩ : syracuseStep 10740539 = 16110809) B16110809
theorem B7160359 : Blo 1885435 7160359 := bstep (se 1 (by rfl) ⟨5370269, by rfl⟩ : syracuseStep 7160359 = 10740539) B10740539
theorem B9547145 : Blo 1885435 9547145 := bstep (se 2 (by rfl) ⟨3580179, by rfl⟩ : syracuseStep 9547145 = 7160359) B7160359
theorem B6364763 : Blo 1885435 6364763 := bstep (se 1 (by rfl) ⟨4773572, by rfl⟩ : syracuseStep 6364763 = 9547145) B9547145
theorem B4243175 : Blo 1885435 4243175 := bstep (se 1 (by rfl) ⟨3182381, by rfl⟩ : syracuseStep 4243175 = 6364763) B6364763
theorem B2828783 : Blo 1885435 2828783 := bstep (se 1 (by rfl) ⟨2121587, by rfl⟩ : syracuseStep 2828783 = 4243175) B4243175
theorem B1885855 : Blo 1885435 1885855 := bstep (se 1 (by rfl) ⟨1414391, by rfl⟩ : syracuseStep 1885855 = 2828783) B2828783
theorem B2828789 : Blo 1885435 2828789 := bbase (se 5 (by rfl) ⟨132599, by rfl⟩ : syracuseStep 2828789 = 265199) (by norm_num)
theorem B1885859 : Blo 1885435 1885859 := bstep (se 1 (by rfl) ⟨1414394, by rfl⟩ : syracuseStep 1885859 = 2828789) B2828789
theorem B5370293 : Blo 1885435 5370293 := bbase (se 5 (by rfl) ⟨251732, by rfl⟩ : syracuseStep 5370293 = 503465) (by norm_num)
theorem B3580195 : Blo 1885435 3580195 := bstep (se 1 (by rfl) ⟨2685146, by rfl⟩ : syracuseStep 3580195 = 5370293) B5370293
theorem B4773593 : Blo 1885435 4773593 := bstep (se 2 (by rfl) ⟨1790097, by rfl⟩ : syracuseStep 4773593 = 3580195) B3580195
theorem B3182395 : Blo 1885435 3182395 := bstep (se 1 (by rfl) ⟨2386796, by rfl⟩ : syracuseStep 3182395 = 4773593) B4773593
theorem B4243193 : Blo 1885435 4243193 := bstep (se 2 (by rfl) ⟨1591197, by rfl⟩ : syracuseStep 4243193 = 3182395) B3182395
theorem B2828795 : Blo 1885435 2828795 := bstep (se 1 (by rfl) ⟨2121596, by rfl⟩ : syracuseStep 2828795 = 4243193) B4243193
theorem B1885863 : Blo 1885435 1885863 := bstep (se 1 (by rfl) ⟨1414397, by rfl⟩ : syracuseStep 1885863 = 2828795) B2828795
theorem B2121601 : Blo 1885435 2121601 := bbase (se 2 (by rfl) ⟨795600, by rfl⟩ : syracuseStep 2121601 = 1591201) (by norm_num)
theorem B2828801 : Blo 1885435 2828801 := bstep (se 2 (by rfl) ⟨1060800, by rfl⟩ : syracuseStep 2828801 = 2121601) B2121601
theorem B1885867 : Blo 1885435 1885867 := bstep (se 1 (by rfl) ⟨1414400, by rfl⟩ : syracuseStep 1885867 = 2828801) B2828801
theorem B4773613 : Blo 1885435 4773613 := bbase (se 3 (by rfl) ⟨895052, by rfl⟩ : syracuseStep 4773613 = 1790105) (by norm_num)
theorem B6364817 : Blo 1885435 6364817 := bstep (se 2 (by rfl) ⟨2386806, by rfl⟩ : syracuseStep 6364817 = 4773613) B4773613
theorem B4243211 : Blo 1885435 4243211 := bstep (se 1 (by rfl) ⟨3182408, by rfl⟩ : syracuseStep 4243211 = 6364817) B6364817
theorem B2828807 : Blo 1885435 2828807 := bstep (se 1 (by rfl) ⟨2121605, by rfl⟩ : syracuseStep 2828807 = 4243211) B4243211
theorem B1885871 : Blo 1885435 1885871 := bstep (se 1 (by rfl) ⟨1414403, by rfl⟩ : syracuseStep 1885871 = 2828807) B2828807
theorem B2828813 : Blo 1885435 2828813 := bbase (se 3 (by rfl) ⟨530402, by rfl⟩ : syracuseStep 2828813 = 1060805) (by norm_num)
theorem B1885875 : Blo 1885435 1885875 := bstep (se 1 (by rfl) ⟨1414406, by rfl⟩ : syracuseStep 1885875 = 2828813) B2828813
theorem B4243229 : Blo 1885435 4243229 := bbase (se 3 (by rfl) ⟨795605, by rfl⟩ : syracuseStep 4243229 = 1591211) (by norm_num)
theorem B2828819 : Blo 1885435 2828819 := bstep (se 1 (by rfl) ⟨2121614, by rfl⟩ : syracuseStep 2828819 = 4243229) B4243229
theorem B1885879 : Blo 1885435 1885879 := bstep (se 1 (by rfl) ⟨1414409, by rfl⟩ : syracuseStep 1885879 = 2828819) B2828819
theorem B3182429 : Blo 1885435 3182429 := bbase (se 3 (by rfl) ⟨596705, by rfl⟩ : syracuseStep 3182429 = 1193411) (by norm_num)
theorem B2121619 : Blo 1885435 2121619 := bstep (se 1 (by rfl) ⟨1591214, by rfl⟩ : syracuseStep 2121619 = 3182429) B3182429
theorem B2828825 : Blo 1885435 2828825 := bstep (se 2 (by rfl) ⟨1060809, by rfl⟩ : syracuseStep 2828825 = 2121619) B2121619
theorem B1885883 : Blo 1885435 1885883 := bstep (se 1 (by rfl) ⟨1414412, by rfl⟩ : syracuseStep 1885883 = 2828825) B2828825
theorem B8055541 : Blo 1885435 8055541 := bbase (se 5 (by rfl) ⟨377603, by rfl⟩ : syracuseStep 8055541 = 755207) (by norm_num)
theorem B10740721 : Blo 1885435 10740721 := bstep (se 2 (by rfl) ⟨4027770, by rfl⟩ : syracuseStep 10740721 = 8055541) B8055541
theorem B14320961 : Blo 1885435 14320961 := bstep (se 2 (by rfl) ⟨5370360, by rfl⟩ : syracuseStep 14320961 = 10740721) B10740721
theorem B9547307 : Blo 1885435 9547307 := bstep (se 1 (by rfl) ⟨7160480, by rfl⟩ : syracuseStep 9547307 = 14320961) B14320961
theorem B6364871 : Blo 1885435 6364871 := bstep (se 1 (by rfl) ⟨4773653, by rfl⟩ : syracuseStep 6364871 = 9547307) B9547307
theorem B4243247 : Blo 1885435 4243247 := bstep (se 1 (by rfl) ⟨3182435, by rfl⟩ : syracuseStep 4243247 = 6364871) B6364871
theorem B2828831 : Blo 1885435 2828831 := bstep (se 1 (by rfl) ⟨2121623, by rfl⟩ : syracuseStep 2828831 = 4243247) B4243247
theorem B1885887 : Blo 1885435 1885887 := bstep (se 1 (by rfl) ⟨1414415, by rfl⟩ : syracuseStep 1885887 = 2828831) B2828831
theorem B2828837 : Blo 1885435 2828837 := bbase (se 4 (by rfl) ⟨265203, by rfl⟩ : syracuseStep 2828837 = 530407) (by norm_num)
theorem B1885891 : Blo 1885435 1885891 := bstep (se 1 (by rfl) ⟨1414418, by rfl⟩ : syracuseStep 1885891 = 2828837) B2828837
theorem B2386837 : Blo 1885435 2386837 := bbase (se 6 (by rfl) ⟨55941, by rfl⟩ : syracuseStep 2386837 = 111883) (by norm_num)
theorem B3182449 : Blo 1885435 3182449 := bstep (se 2 (by rfl) ⟨1193418, by rfl⟩ : syracuseStep 3182449 = 2386837) B2386837
theorem B4243265 : Blo 1885435 4243265 := bstep (se 2 (by rfl) ⟨1591224, by rfl⟩ : syracuseStep 4243265 = 3182449) B3182449
theorem B2828843 : Blo 1885435 2828843 := bstep (se 1 (by rfl) ⟨2121632, by rfl⟩ : syracuseStep 2828843 = 4243265) B4243265
theorem B1885895 : Blo 1885435 1885895 := bstep (se 1 (by rfl) ⟨1414421, by rfl⟩ : syracuseStep 1885895 = 2828843) B2828843
theorem B2121637 : Blo 1885435 2121637 := bbase (se 4 (by rfl) ⟨198903, by rfl⟩ : syracuseStep 2121637 = 397807) (by norm_num)
theorem B2828849 : Blo 1885435 2828849 := bstep (se 2 (by rfl) ⟨1060818, by rfl⟩ : syracuseStep 2828849 = 2121637) B2121637
theorem B1885899 : Blo 1885435 1885899 := bstep (se 1 (by rfl) ⟨1414424, by rfl⟩ : syracuseStep 1885899 = 2828849) B2828849
theorem B13593845 : Blo 1885435 13593845 := bbase (se 5 (by rfl) ⟨637211, by rfl⟩ : syracuseStep 13593845 = 1274423) (by norm_num)
theorem B9062563 : Blo 1885435 9062563 := bstep (se 1 (by rfl) ⟨6796922, by rfl⟩ : syracuseStep 9062563 = 13593845) B13593845
theorem B12083417 : Blo 1885435 12083417 := bstep (se 2 (by rfl) ⟨4531281, by rfl⟩ : syracuseStep 12083417 = 9062563) B9062563
theorem B8055611 : Blo 1885435 8055611 := bstep (se 1 (by rfl) ⟨6041708, by rfl⟩ : syracuseStep 8055611 = 12083417) B12083417
theorem B5370407 : Blo 1885435 5370407 := bstep (se 1 (by rfl) ⟨4027805, by rfl⟩ : syracuseStep 5370407 = 8055611) B8055611
theorem B3580271 : Blo 1885435 3580271 := bstep (se 1 (by rfl) ⟨2685203, by rfl⟩ : syracuseStep 3580271 = 5370407) B5370407
theorem B2386847 : Blo 1885435 2386847 := bstep (se 1 (by rfl) ⟨1790135, by rfl⟩ : syracuseStep 2386847 = 3580271) B3580271
theorem B6364925 : Blo 1885435 6364925 := bstep (se 3 (by rfl) ⟨1193423, by rfl⟩ : syracuseStep 6364925 = 2386847) B2386847
theorem B4243283 : Blo 1885435 4243283 := bstep (se 1 (by rfl) ⟨3182462, by rfl⟩ : syracuseStep 4243283 = 6364925) B6364925
theorem B2828855 : Blo 1885435 2828855 := bstep (se 1 (by rfl) ⟨2121641, by rfl⟩ : syracuseStep 2828855 = 4243283) B4243283
theorem B1885903 : Blo 1885435 1885903 := bstep (se 1 (by rfl) ⟨1414427, by rfl⟩ : syracuseStep 1885903 = 2828855) B2828855
theorem B2828861 : Blo 1885435 2828861 := bbase (se 3 (by rfl) ⟨530411, by rfl⟩ : syracuseStep 2828861 = 1060823) (by norm_num)
theorem B1885907 : Blo 1885435 1885907 := bstep (se 1 (by rfl) ⟨1414430, by rfl⟩ : syracuseStep 1885907 = 2828861) B2828861
theorem B4243301 : Blo 1885435 4243301 := bbase (se 4 (by rfl) ⟨397809, by rfl⟩ : syracuseStep 4243301 = 795619) (by norm_num)
theorem B2828867 : Blo 1885435 2828867 := bstep (se 1 (by rfl) ⟨2121650, by rfl⟩ : syracuseStep 2828867 = 4243301) B4243301
theorem B1885911 : Blo 1885435 1885911 := bstep (se 1 (by rfl) ⟨1414433, by rfl⟩ : syracuseStep 1885911 = 2828867) B2828867
theorem B4773725 : Blo 1885435 4773725 := bbase (se 3 (by rfl) ⟨895073, by rfl⟩ : syracuseStep 4773725 = 1790147) (by norm_num)
theorem B3182483 : Blo 1885435 3182483 := bstep (se 1 (by rfl) ⟨2386862, by rfl⟩ : syracuseStep 3182483 = 4773725) B4773725
theorem B2121655 : Blo 1885435 2121655 := bstep (se 1 (by rfl) ⟨1591241, by rfl⟩ : syracuseStep 2121655 = 3182483) B3182483
theorem B2828873 : Blo 1885435 2828873 := bstep (se 2 (by rfl) ⟨1060827, by rfl⟩ : syracuseStep 2828873 = 2121655) B2121655
theorem B1885915 : Blo 1885435 1885915 := bstep (se 1 (by rfl) ⟨1414436, by rfl⟩ : syracuseStep 1885915 = 2828873) B2828873
theorem B3580301 : Blo 1885435 3580301 := bbase (se 3 (by rfl) ⟨671306, by rfl⟩ : syracuseStep 3580301 = 1342613) (by norm_num)
theorem B9547469 : Blo 1885435 9547469 := bstep (se 3 (by rfl) ⟨1790150, by rfl⟩ : syracuseStep 9547469 = 3580301) B3580301
theorem B6364979 : Blo 1885435 6364979 := bstep (se 1 (by rfl) ⟨4773734, by rfl⟩ : syracuseStep 6364979 = 9547469) B9547469
theorem B4243319 : Blo 1885435 4243319 := bstep (se 1 (by rfl) ⟨3182489, by rfl⟩ : syracuseStep 4243319 = 6364979) B6364979
theorem B2828879 : Blo 1885435 2828879 := bstep (se 1 (by rfl) ⟨2121659, by rfl⟩ : syracuseStep 2828879 = 4243319) B4243319
theorem B1885919 : Blo 1885435 1885919 := bstep (se 1 (by rfl) ⟨1414439, by rfl⟩ : syracuseStep 1885919 = 2828879) B2828879
theorem B2828885 : Blo 1885435 2828885 := bbase (se 8 (by rfl) ⟨16575, by rfl⟩ : syracuseStep 2828885 = 33151) (by norm_num)
theorem B1885923 : Blo 1885435 1885923 := bstep (se 1 (by rfl) ⟨1414442, by rfl⟩ : syracuseStep 1885923 = 2828885) B2828885
theorem B2150617 : Blo 1885435 2150617 := bbase (se 2 (by rfl) ⟨806481, by rfl⟩ : syracuseStep 2150617 = 1612963) (by norm_num)
theorem B2867489 : Blo 1885435 2867489 := bstep (se 2 (by rfl) ⟨1075308, by rfl⟩ : syracuseStep 2867489 = 2150617) B2150617
theorem B1911659 : Blo 1885435 1911659 := bstep (se 1 (by rfl) ⟨1433744, by rfl⟩ : syracuseStep 1911659 = 2867489) B2867489
theorem B5097757 : Blo 1885435 5097757 := bstep (se 3 (by rfl) ⟨955829, by rfl⟩ : syracuseStep 5097757 = 1911659) B1911659
theorem B6797009 : Blo 1885435 6797009 := bstep (se 2 (by rfl) ⟨2548878, by rfl⟩ : syracuseStep 6797009 = 5097757) B5097757
theorem B4531339 : Blo 1885435 4531339 := bstep (se 1 (by rfl) ⟨3398504, by rfl⟩ : syracuseStep 4531339 = 6797009) B6797009
theorem B6041785 : Blo 1885435 6041785 := bstep (se 2 (by rfl) ⟨2265669, by rfl⟩ : syracuseStep 6041785 = 4531339) B4531339
theorem B8055713 : Blo 1885435 8055713 := bstep (se 2 (by rfl) ⟨3020892, by rfl⟩ : syracuseStep 8055713 = 6041785) B6041785
theorem B5370475 : Blo 1885435 5370475 := bstep (se 1 (by rfl) ⟨4027856, by rfl⟩ : syracuseStep 5370475 = 8055713) B8055713
theorem B7160633 : Blo 1885435 7160633 := bstep (se 2 (by rfl) ⟨2685237, by rfl⟩ : syracuseStep 7160633 = 5370475) B5370475
theorem B4773755 : Blo 1885435 4773755 := bstep (se 1 (by rfl) ⟨3580316, by rfl⟩ : syracuseStep 4773755 = 7160633) B7160633
theorem B3182503 : Blo 1885435 3182503 := bstep (se 1 (by rfl) ⟨2386877, by rfl⟩ : syracuseStep 3182503 = 4773755) B4773755
theorem B4243337 : Blo 1885435 4243337 := bstep (se 2 (by rfl) ⟨1591251, by rfl⟩ : syracuseStep 4243337 = 3182503) B3182503
theorem B2828891 : Blo 1885435 2828891 := bstep (se 1 (by rfl) ⟨2121668, by rfl⟩ : syracuseStep 2828891 = 4243337) B4243337
theorem B1885927 : Blo 1885435 1885927 := bstep (se 1 (by rfl) ⟨1414445, by rfl⟩ : syracuseStep 1885927 = 2828891) B2828891
theorem B2121673 : Blo 1885435 2121673 := bbase (se 2 (by rfl) ⟨795627, by rfl⟩ : syracuseStep 2121673 = 1591255) (by norm_num)
theorem B2828897 : Blo 1885435 2828897 := bstep (se 2 (by rfl) ⟨1060836, by rfl⟩ : syracuseStep 2828897 = 2121673) B2121673
theorem B1885931 : Blo 1885435 1885931 := bstep (se 1 (by rfl) ⟨1414448, by rfl⟩ : syracuseStep 1885931 = 2828897) B2828897
theorem B2867501 : Blo 1885435 2867501 := bbase (se 3 (by rfl) ⟨537656, by rfl⟩ : syracuseStep 2867501 = 1075313) (by norm_num)
theorem B7646669 : Blo 1885435 7646669 := bstep (se 3 (by rfl) ⟨1433750, by rfl⟩ : syracuseStep 7646669 = 2867501) B2867501
theorem B5097779 : Blo 1885435 5097779 := bstep (se 1 (by rfl) ⟨3823334, by rfl⟩ : syracuseStep 5097779 = 7646669) B7646669
theorem B3398519 : Blo 1885435 3398519 := bstep (se 1 (by rfl) ⟨2548889, by rfl⟩ : syracuseStep 3398519 = 5097779) B5097779
theorem B2265679 : Blo 1885435 2265679 := bstep (se 1 (by rfl) ⟨1699259, by rfl⟩ : syracuseStep 2265679 = 3398519) B3398519
theorem B3020905 : Blo 1885435 3020905 := bstep (se 2 (by rfl) ⟨1132839, by rfl⟩ : syracuseStep 3020905 = 2265679) B2265679
theorem B16111493 : Blo 1885435 16111493 := bstep (se 4 (by rfl) ⟨1510452, by rfl⟩ : syracuseStep 16111493 = 3020905) B3020905
theorem B10740995 : Blo 1885435 10740995 := bstep (se 1 (by rfl) ⟨8055746, by rfl⟩ : syracuseStep 10740995 = 16111493) B16111493
theorem B7160663 : Blo 1885435 7160663 := bstep (se 1 (by rfl) ⟨5370497, by rfl⟩ : syracuseStep 7160663 = 10740995) B10740995
theorem B4773775 : Blo 1885435 4773775 := bstep (se 1 (by rfl) ⟨3580331, by rfl⟩ : syracuseStep 4773775 = 7160663) B7160663
theorem B6365033 : Blo 1885435 6365033 := bstep (se 2 (by rfl) ⟨2386887, by rfl⟩ : syracuseStep 6365033 = 4773775) B4773775
theorem B4243355 : Blo 1885435 4243355 := bstep (se 1 (by rfl) ⟨3182516, by rfl⟩ : syracuseStep 4243355 = 6365033) B6365033
theorem B2828903 : Blo 1885435 2828903 := bstep (se 1 (by rfl) ⟨2121677, by rfl⟩ : syracuseStep 2828903 = 4243355) B4243355
theorem B1885935 : Blo 1885435 1885935 := bstep (se 1 (by rfl) ⟨1414451, by rfl⟩ : syracuseStep 1885935 = 2828903) B2828903
theorem B2828909 : Blo 1885435 2828909 := bbase (se 3 (by rfl) ⟨530420, by rfl⟩ : syracuseStep 2828909 = 1060841) (by norm_num)
theorem B1885939 : Blo 1885435 1885939 := bstep (se 1 (by rfl) ⟨1414454, by rfl⟩ : syracuseStep 1885939 = 2828909) B2828909
theorem B4243373 : Blo 1885435 4243373 := bbase (se 3 (by rfl) ⟨795632, by rfl⟩ : syracuseStep 4243373 = 1591265) (by norm_num)
theorem B2828915 : Blo 1885435 2828915 := bstep (se 1 (by rfl) ⟨2121686, by rfl⟩ : syracuseStep 2828915 = 4243373) B4243373
theorem B1885943 : Blo 1885435 1885943 := bstep (se 1 (by rfl) ⟨1414457, by rfl⟩ : syracuseStep 1885943 = 2828915) B2828915
theorem B5370533 : Blo 1885435 5370533 := bbase (se 4 (by rfl) ⟨503487, by rfl⟩ : syracuseStep 5370533 = 1006975) (by norm_num)
theorem B3580355 : Blo 1885435 3580355 := bstep (se 1 (by rfl) ⟨2685266, by rfl⟩ : syracuseStep 3580355 = 5370533) B5370533
theorem B2386903 : Blo 1885435 2386903 := bstep (se 1 (by rfl) ⟨1790177, by rfl⟩ : syracuseStep 2386903 = 3580355) B3580355
theorem B3182537 : Blo 1885435 3182537 := bstep (se 2 (by rfl) ⟨1193451, by rfl⟩ : syracuseStep 3182537 = 2386903) B2386903
theorem B2121691 : Blo 1885435 2121691 := bstep (se 1 (by rfl) ⟨1591268, by rfl⟩ : syracuseStep 2121691 = 3182537) B3182537
theorem B2828921 : Blo 1885435 2828921 := bstep (se 2 (by rfl) ⟨1060845, by rfl⟩ : syracuseStep 2828921 = 2121691) B2121691
theorem B1885947 : Blo 1885435 1885947 := bstep (se 1 (by rfl) ⟨1414460, by rfl⟩ : syracuseStep 1885947 = 2828921) B2828921
theorem B15293461 : Blo 1885435 15293461 := bbase (se 6 (by rfl) ⟨358440, by rfl⟩ : syracuseStep 15293461 = 716881) (by norm_num)
theorem B20391281 : Blo 1885435 20391281 := bstep (se 2 (by rfl) ⟨7646730, by rfl⟩ : syracuseStep 20391281 = 15293461) B15293461
theorem B13594187 : Blo 1885435 13594187 := bstep (se 1 (by rfl) ⟨10195640, by rfl⟩ : syracuseStep 13594187 = 20391281) B20391281
theorem B36251165 : Blo 1885435 36251165 := bstep (se 3 (by rfl) ⟨6797093, by rfl⟩ : syracuseStep 36251165 = 13594187) B13594187
theorem B24167443 : Blo 1885435 24167443 := bstep (se 1 (by rfl) ⟨18125582, by rfl⟩ : syracuseStep 24167443 = 36251165) B36251165
theorem B32223257 : Blo 1885435 32223257 := bstep (se 2 (by rfl) ⟨12083721, by rfl⟩ : syracuseStep 32223257 = 24167443) B24167443
theorem B21482171 : Blo 1885435 21482171 := bstep (se 1 (by rfl) ⟨16111628, by rfl⟩ : syracuseStep 21482171 = 32223257) B32223257
theorem B14321447 : Blo 1885435 14321447 := bstep (se 1 (by rfl) ⟨10741085, by rfl⟩ : syracuseStep 14321447 = 21482171) B21482171
theorem B9547631 : Blo 1885435 9547631 := bstep (se 1 (by rfl) ⟨7160723, by rfl⟩ : syracuseStep 9547631 = 14321447) B14321447
theorem B6365087 : Blo 1885435 6365087 := bstep (se 1 (by rfl) ⟨4773815, by rfl⟩ : syracuseStep 6365087 = 9547631) B9547631
theorem B4243391 : Blo 1885435 4243391 := bstep (se 1 (by rfl) ⟨3182543, by rfl⟩ : syracuseStep 4243391 = 6365087) B6365087
theorem B2828927 : Blo 1885435 2828927 := bstep (se 1 (by rfl) ⟨2121695, by rfl⟩ : syracuseStep 2828927 = 4243391) B4243391
theorem B1885951 : Blo 1885435 1885951 := bstep (se 1 (by rfl) ⟨1414463, by rfl⟩ : syracuseStep 1885951 = 2828927) B2828927
theorem B2828933 : Blo 1885435 2828933 := bbase (se 4 (by rfl) ⟨265212, by rfl⟩ : syracuseStep 2828933 = 530425) (by norm_num)
theorem B1885955 : Blo 1885435 1885955 := bstep (se 1 (by rfl) ⟨1414466, by rfl⟩ : syracuseStep 1885955 = 2828933) B2828933
theorem B3182557 : Blo 1885435 3182557 := bbase (se 3 (by rfl) ⟨596729, by rfl⟩ : syracuseStep 3182557 = 1193459) (by norm_num)
theorem B4243409 : Blo 1885435 4243409 := bstep (se 2 (by rfl) ⟨1591278, by rfl⟩ : syracuseStep 4243409 = 3182557) B3182557
theorem B2828939 : Blo 1885435 2828939 := bstep (se 1 (by rfl) ⟨2121704, by rfl⟩ : syracuseStep 2828939 = 4243409) B4243409
theorem B1885959 : Blo 1885435 1885959 := bstep (se 1 (by rfl) ⟨1414469, by rfl⟩ : syracuseStep 1885959 = 2828939) B2828939
theorem B2121709 : Blo 1885435 2121709 := bbase (se 3 (by rfl) ⟨397820, by rfl⟩ : syracuseStep 2121709 = 795641) (by norm_num)
theorem B2828945 : Blo 1885435 2828945 := bstep (se 2 (by rfl) ⟨1060854, by rfl⟩ : syracuseStep 2828945 = 2121709) B2121709
theorem B1885963 : Blo 1885435 1885963 := bstep (se 1 (by rfl) ⟨1414472, by rfl⟩ : syracuseStep 1885963 = 2828945) B2828945
theorem B6365141 : Blo 1885435 6365141 := bbase (se 7 (by rfl) ⟨74591, by rfl⟩ : syracuseStep 6365141 = 149183) (by norm_num)
theorem B4243427 : Blo 1885435 4243427 := bstep (se 1 (by rfl) ⟨3182570, by rfl⟩ : syracuseStep 4243427 = 6365141) B6365141
theorem B2828951 : Blo 1885435 2828951 := bstep (se 1 (by rfl) ⟨2121713, by rfl⟩ : syracuseStep 2828951 = 4243427) B4243427
theorem B1885967 : Blo 1885435 1885967 := bstep (se 1 (by rfl) ⟨1414475, by rfl⟩ : syracuseStep 1885967 = 2828951) B2828951
theorem B2828957 : Blo 1885435 2828957 := bbase (se 3 (by rfl) ⟨530429, by rfl⟩ : syracuseStep 2828957 = 1060859) (by norm_num)
theorem B1885971 : Blo 1885435 1885971 := bstep (se 1 (by rfl) ⟨1414478, by rfl⟩ : syracuseStep 1885971 = 2828957) B2828957
theorem B4243445 : Blo 1885435 4243445 := bbase (se 5 (by rfl) ⟨198911, by rfl⟩ : syracuseStep 4243445 = 397823) (by norm_num)
theorem B2828963 : Blo 1885435 2828963 := bstep (se 1 (by rfl) ⟨2121722, by rfl⟩ : syracuseStep 2828963 = 4243445) B4243445
theorem B1885975 : Blo 1885435 1885975 := bstep (se 1 (by rfl) ⟨1414481, by rfl⟩ : syracuseStep 1885975 = 2828963) B2828963
theorem B6540053 : Blo 1885435 6540053 := bbase (se 6 (by rfl) ⟨153282, by rfl⟩ : syracuseStep 6540053 = 306565) (by norm_num)
theorem B69760565 : Blo 1885435 69760565 := bstep (se 5 (by rfl) ⟨3270026, by rfl⟩ : syracuseStep 69760565 = 6540053) B6540053
theorem B46507043 : Blo 1885435 46507043 := bstep (se 1 (by rfl) ⟨34880282, by rfl⟩ : syracuseStep 46507043 = 69760565) B69760565
theorem B31004695 : Blo 1885435 31004695 := bstep (se 1 (by rfl) ⟨23253521, by rfl⟩ : syracuseStep 31004695 = 46507043) B46507043
theorem B41339593 : Blo 1885435 41339593 := bstep (se 2 (by rfl) ⟨15502347, by rfl⟩ : syracuseStep 41339593 = 31004695) B31004695
theorem B55119457 : Blo 1885435 55119457 := bstep (se 2 (by rfl) ⟨20669796, by rfl⟩ : syracuseStep 55119457 = 41339593) B41339593
theorem B73492609 : Blo 1885435 73492609 := bstep (se 2 (by rfl) ⟨27559728, by rfl⟩ : syracuseStep 73492609 = 55119457) B55119457
theorem B97990145 : Blo 1885435 97990145 := bstep (se 2 (by rfl) ⟨36746304, by rfl⟩ : syracuseStep 97990145 = 73492609) B73492609
theorem B65326763 : Blo 1885435 65326763 := bstep (se 1 (by rfl) ⟨48995072, by rfl⟩ : syracuseStep 65326763 = 97990145) B97990145
theorem B174204701 : Blo 1885435 174204701 := bstep (se 3 (by rfl) ⟨32663381, by rfl⟩ : syracuseStep 174204701 = 65326763) B65326763
theorem B116136467 : Blo 1885435 116136467 := bstep (se 1 (by rfl) ⟨87102350, by rfl⟩ : syracuseStep 116136467 = 174204701) B174204701
theorem B77424311 : Blo 1885435 77424311 := bstep (se 1 (by rfl) ⟨58068233, by rfl⟩ : syracuseStep 77424311 = 116136467) B116136467
theorem B51616207 : Blo 1885435 51616207 := bstep (se 1 (by rfl) ⟨38712155, by rfl⟩ : syracuseStep 51616207 = 77424311) B77424311
theorem B275286437 : Blo 1885435 275286437 := bstep (se 4 (by rfl) ⟨25808103, by rfl⟩ : syracuseStep 275286437 = 51616207) B51616207
theorem B183524291 : Blo 1885435 183524291 := bstep (se 1 (by rfl) ⟨137643218, by rfl⟩ : syracuseStep 183524291 = 275286437) B275286437
theorem B122349527 : Blo 1885435 122349527 := bstep (se 1 (by rfl) ⟨91762145, by rfl⟩ : syracuseStep 122349527 = 183524291) B183524291
theorem B81566351 : Blo 1885435 81566351 := bstep (se 1 (by rfl) ⟨61174763, by rfl⟩ : syracuseStep 81566351 = 122349527) B122349527
theorem B54377567 : Blo 1885435 54377567 := bstep (se 1 (by rfl) ⟨40783175, by rfl⟩ : syracuseStep 54377567 = 81566351) B81566351
theorem B36251711 : Blo 1885435 36251711 := bstep (se 1 (by rfl) ⟨27188783, by rfl⟩ : syracuseStep 36251711 = 54377567) B54377567
theorem B24167807 : Blo 1885435 24167807 := bstep (se 1 (by rfl) ⟨18125855, by rfl⟩ : syracuseStep 24167807 = 36251711) B36251711
theorem B16111871 : Blo 1885435 16111871 := bstep (se 1 (by rfl) ⟨12083903, by rfl⟩ : syracuseStep 16111871 = 24167807) B24167807
theorem B10741247 : Blo 1885435 10741247 := bstep (se 1 (by rfl) ⟨8055935, by rfl⟩ : syracuseStep 10741247 = 16111871) B16111871
theorem B7160831 : Blo 1885435 7160831 := bstep (se 1 (by rfl) ⟨5370623, by rfl⟩ : syracuseStep 7160831 = 10741247) B10741247
theorem B4773887 : Blo 1885435 4773887 := bstep (se 1 (by rfl) ⟨3580415, by rfl⟩ : syracuseStep 4773887 = 7160831) B7160831
theorem B3182591 : Blo 1885435 3182591 := bstep (se 1 (by rfl) ⟨2386943, by rfl⟩ : syracuseStep 3182591 = 4773887) B4773887
theorem B2121727 : Blo 1885435 2121727 := bstep (se 1 (by rfl) ⟨1591295, by rfl⟩ : syracuseStep 2121727 = 3182591) B3182591
theorem B2828969 : Blo 1885435 2828969 := bstep (se 2 (by rfl) ⟨1060863, by rfl⟩ : syracuseStep 2828969 = 2121727) B2121727
theorem B1885979 : Blo 1885435 1885979 := bstep (se 1 (by rfl) ⟨1414484, by rfl⟩ : syracuseStep 1885979 = 2828969) B2828969
theorem B2685317 : Blo 1885435 2685317 := bbase (se 4 (by rfl) ⟨251748, by rfl⟩ : syracuseStep 2685317 = 503497) (by norm_num)
theorem B7160845 : Blo 1885435 7160845 := bstep (se 3 (by rfl) ⟨1342658, by rfl⟩ : syracuseStep 7160845 = 2685317) B2685317
theorem B9547793 : Blo 1885435 9547793 := bstep (se 2 (by rfl) ⟨3580422, by rfl⟩ : syracuseStep 9547793 = 7160845) B7160845
theorem B6365195 : Blo 1885435 6365195 := bstep (se 1 (by rfl) ⟨4773896, by rfl⟩ : syracuseStep 6365195 = 9547793) B9547793
theorem B4243463 : Blo 1885435 4243463 := bstep (se 1 (by rfl) ⟨3182597, by rfl⟩ : syracuseStep 4243463 = 6365195) B6365195
theorem B2828975 : Blo 1885435 2828975 := bstep (se 1 (by rfl) ⟨2121731, by rfl⟩ : syracuseStep 2828975 = 4243463) B4243463
theorem B1885983 : Blo 1885435 1885983 := bstep (se 1 (by rfl) ⟨1414487, by rfl⟩ : syracuseStep 1885983 = 2828975) B2828975
theorem B2828981 : Blo 1885435 2828981 := bbase (se 5 (by rfl) ⟨132608, by rfl⟩ : syracuseStep 2828981 = 265217) (by norm_num)
theorem B1885987 : Blo 1885435 1885987 := bstep (se 1 (by rfl) ⟨1414490, by rfl⟩ : syracuseStep 1885987 = 2828981) B2828981
theorem B4773917 : Blo 1885435 4773917 := bbase (se 3 (by rfl) ⟨895109, by rfl⟩ : syracuseStep 4773917 = 1790219) (by norm_num)
theorem B3182611 : Blo 1885435 3182611 := bstep (se 1 (by rfl) ⟨2386958, by rfl⟩ : syracuseStep 3182611 = 4773917) B4773917
theorem B4243481 : Blo 1885435 4243481 := bstep (se 2 (by rfl) ⟨1591305, by rfl⟩ : syracuseStep 4243481 = 3182611) B3182611
theorem B2828987 : Blo 1885435 2828987 := bstep (se 1 (by rfl) ⟨2121740, by rfl⟩ : syracuseStep 2828987 = 4243481) B4243481
theorem B1885991 : Blo 1885435 1885991 := bstep (se 1 (by rfl) ⟨1414493, by rfl⟩ : syracuseStep 1885991 = 2828987) B2828987
theorem B2121745 : Blo 1885435 2121745 := bbase (se 2 (by rfl) ⟨795654, by rfl⟩ : syracuseStep 2121745 = 1591309) (by norm_num)
theorem B2828993 : Blo 1885435 2828993 := bstep (se 2 (by rfl) ⟨1060872, by rfl⟩ : syracuseStep 2828993 = 2121745) B2121745
theorem B1885995 : Blo 1885435 1885995 := bstep (se 1 (by rfl) ⟨1414496, by rfl⟩ : syracuseStep 1885995 = 2828993) B2828993
theorem B3580453 : Blo 1885435 3580453 := bbase (se 4 (by rfl) ⟨335667, by rfl⟩ : syracuseStep 3580453 = 671335) (by norm_num)
theorem B4773937 : Blo 1885435 4773937 := bstep (se 2 (by rfl) ⟨1790226, by rfl⟩ : syracuseStep 4773937 = 3580453) B3580453
theorem B6365249 : Blo 1885435 6365249 := bstep (se 2 (by rfl) ⟨2386968, by rfl⟩ : syracuseStep 6365249 = 4773937) B4773937
theorem B4243499 : Blo 1885435 4243499 := bstep (se 1 (by rfl) ⟨3182624, by rfl⟩ : syracuseStep 4243499 = 6365249) B6365249
theorem B2828999 : Blo 1885435 2828999 := bstep (se 1 (by rfl) ⟨2121749, by rfl⟩ : syracuseStep 2828999 = 4243499) B4243499
theorem B1885999 : Blo 1885435 1885999 := bstep (se 1 (by rfl) ⟨1414499, by rfl⟩ : syracuseStep 1885999 = 2828999) B2828999
theorem B2829005 : Blo 1885435 2829005 := bbase (se 3 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 2829005 = 1060877) (by norm_num)
theorem B1886003 : Blo 1885435 1886003 := bstep (se 1 (by rfl) ⟨1414502, by rfl⟩ : syracuseStep 1886003 = 2829005) B2829005
theorem B4243517 : Blo 1885435 4243517 := bbase (se 3 (by rfl) ⟨795659, by rfl⟩ : syracuseStep 4243517 = 1591319) (by norm_num)
theorem B2829011 : Blo 1885435 2829011 := bstep (se 1 (by rfl) ⟨2121758, by rfl⟩ : syracuseStep 2829011 = 4243517) B4243517
theorem B1886007 : Blo 1885435 1886007 := bstep (se 1 (by rfl) ⟨1414505, by rfl⟩ : syracuseStep 1886007 = 2829011) B2829011
theorem B3182645 : Blo 1885435 3182645 := bbase (se 5 (by rfl) ⟨149186, by rfl⟩ : syracuseStep 3182645 = 298373) (by norm_num)
theorem B2121763 : Blo 1885435 2121763 := bstep (se 1 (by rfl) ⟨1591322, by rfl⟩ : syracuseStep 2121763 = 3182645) B3182645
theorem B2829017 : Blo 1885435 2829017 := bstep (se 2 (by rfl) ⟨1060881, by rfl⟩ : syracuseStep 2829017 = 2121763) B2121763
theorem B1886011 : Blo 1885435 1886011 := bstep (se 1 (by rfl) ⟨1414508, by rfl⟩ : syracuseStep 1886011 = 2829017) B2829017
theorem B5370725 : Blo 1885435 5370725 := bbase (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) (by norm_num)
theorem B14321933 : Blo 1885435 14321933 := bstep (se 3 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 14321933 = 5370725) B5370725
theorem B9547955 : Blo 1885435 9547955 := bstep (se 1 (by rfl) ⟨7160966, by rfl⟩ : syracuseStep 9547955 = 14321933) B14321933
theorem B6365303 : Blo 1885435 6365303 := bstep (se 1 (by rfl) ⟨4773977, by rfl⟩ : syracuseStep 6365303 = 9547955) B9547955
theorem B4243535 : Blo 1885435 4243535 := bstep (se 1 (by rfl) ⟨3182651, by rfl⟩ : syracuseStep 4243535 = 6365303) B6365303
theorem B2829023 : Blo 1885435 2829023 := bstep (se 1 (by rfl) ⟨2121767, by rfl⟩ : syracuseStep 2829023 = 4243535) B4243535
theorem B1886015 : Blo 1885435 1886015 := bstep (se 1 (by rfl) ⟨1414511, by rfl⟩ : syracuseStep 1886015 = 2829023) B2829023
theorem B2829029 : Blo 1885435 2829029 := bbase (se 4 (by rfl) ⟨265221, by rfl⟩ : syracuseStep 2829029 = 530443) (by norm_num)
theorem B1886019 : Blo 1885435 1886019 := bstep (se 1 (by rfl) ⟨1414514, by rfl⟩ : syracuseStep 1886019 = 2829029) B2829029
theorem B1911757 : Blo 1885435 1911757 := bbase (se 3 (by rfl) ⟨358454, by rfl⟩ : syracuseStep 1911757 = 716909) (by norm_num)
theorem B2549009 : Blo 1885435 2549009 := bstep (se 2 (by rfl) ⟨955878, by rfl⟩ : syracuseStep 2549009 = 1911757) B1911757
theorem B6797357 : Blo 1885435 6797357 := bstep (se 3 (by rfl) ⟨1274504, by rfl⟩ : syracuseStep 6797357 = 2549009) B2549009
theorem B4531571 : Blo 1885435 4531571 := bstep (se 1 (by rfl) ⟨3398678, by rfl⟩ : syracuseStep 4531571 = 6797357) B6797357
theorem B3021047 : Blo 1885435 3021047 := bstep (se 1 (by rfl) ⟨2265785, by rfl⟩ : syracuseStep 3021047 = 4531571) B4531571
theorem B2014031 : Blo 1885435 2014031 := bstep (se 1 (by rfl) ⟨1510523, by rfl⟩ : syracuseStep 2014031 = 3021047) B3021047
theorem B5370749 : Blo 1885435 5370749 := bstep (se 3 (by rfl) ⟨1007015, by rfl⟩ : syracuseStep 5370749 = 2014031) B2014031
theorem B3580499 : Blo 1885435 3580499 := bstep (se 1 (by rfl) ⟨2685374, by rfl⟩ : syracuseStep 3580499 = 5370749) B5370749
theorem B2386999 : Blo 1885435 2386999 := bstep (se 1 (by rfl) ⟨1790249, by rfl⟩ : syracuseStep 2386999 = 3580499) B3580499
theorem B3182665 : Blo 1885435 3182665 := bstep (se 2 (by rfl) ⟨1193499, by rfl⟩ : syracuseStep 3182665 = 2386999) B2386999
theorem B4243553 : Blo 1885435 4243553 := bstep (se 2 (by rfl) ⟨1591332, by rfl⟩ : syracuseStep 4243553 = 3182665) B3182665
theorem B2829035 : Blo 1885435 2829035 := bstep (se 1 (by rfl) ⟨2121776, by rfl⟩ : syracuseStep 2829035 = 4243553) B4243553
theorem B1886023 : Blo 1885435 1886023 := bstep (se 1 (by rfl) ⟨1414517, by rfl⟩ : syracuseStep 1886023 = 2829035) B2829035
theorem B2121781 : Blo 1885435 2121781 := bbase (se 5 (by rfl) ⟨99458, by rfl⟩ : syracuseStep 2121781 = 198917) (by norm_num)
theorem B2829041 : Blo 1885435 2829041 := bstep (se 2 (by rfl) ⟨1060890, by rfl⟩ : syracuseStep 2829041 = 2121781) B2121781
theorem B1886027 : Blo 1885435 1886027 := bstep (se 1 (by rfl) ⟨1414520, by rfl⟩ : syracuseStep 1886027 = 2829041) B2829041
theorem B2387009 : Blo 1885435 2387009 := bbase (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) (by norm_num)
theorem B6365357 : Blo 1885435 6365357 := bstep (se 3 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 6365357 = 2387009) B2387009
theorem B4243571 : Blo 1885435 4243571 := bstep (se 1 (by rfl) ⟨3182678, by rfl⟩ : syracuseStep 4243571 = 6365357) B6365357
theorem B2829047 : Blo 1885435 2829047 := bstep (se 1 (by rfl) ⟨2121785, by rfl⟩ : syracuseStep 2829047 = 4243571) B4243571
theorem B1886031 : Blo 1885435 1886031 := bstep (se 1 (by rfl) ⟨1414523, by rfl⟩ : syracuseStep 1886031 = 2829047) B2829047
theorem B2829053 : Blo 1885435 2829053 := bbase (se 3 (by rfl) ⟨530447, by rfl⟩ : syracuseStep 2829053 = 1060895) (by norm_num)
theorem B1886035 : Blo 1885435 1886035 := bstep (se 1 (by rfl) ⟨1414526, by rfl⟩ : syracuseStep 1886035 = 2829053) B2829053
theorem B4243589 : Blo 1885435 4243589 := bbase (se 4 (by rfl) ⟨397836, by rfl⟩ : syracuseStep 4243589 = 795673) (by norm_num)
theorem B2829059 : Blo 1885435 2829059 := bstep (se 1 (by rfl) ⟨2121794, by rfl⟩ : syracuseStep 2829059 = 4243589) B4243589
theorem B1886039 : Blo 1885435 1886039 := bstep (se 1 (by rfl) ⟨1414529, by rfl⟩ : syracuseStep 1886039 = 2829059) B2829059
theorem B6797429 : Blo 1885435 6797429 := bbase (se 5 (by rfl) ⟨318629, by rfl⟩ : syracuseStep 6797429 = 637259) (by norm_num)
theorem B4531619 : Blo 1885435 4531619 := bstep (se 1 (by rfl) ⟨3398714, by rfl⟩ : syracuseStep 4531619 = 6797429) B6797429
theorem B3021079 : Blo 1885435 3021079 := bstep (se 1 (by rfl) ⟨2265809, by rfl⟩ : syracuseStep 3021079 = 4531619) B4531619
theorem B4028105 : Blo 1885435 4028105 := bstep (se 2 (by rfl) ⟨1510539, by rfl⟩ : syracuseStep 4028105 = 3021079) B3021079
theorem B2685403 : Blo 1885435 2685403 := bstep (se 1 (by rfl) ⟨2014052, by rfl⟩ : syracuseStep 2685403 = 4028105) B4028105
theorem B3580537 : Blo 1885435 3580537 := bstep (se 2 (by rfl) ⟨1342701, by rfl⟩ : syracuseStep 3580537 = 2685403) B2685403
theorem B4774049 : Blo 1885435 4774049 := bstep (se 2 (by rfl) ⟨1790268, by rfl⟩ : syracuseStep 4774049 = 3580537) B3580537
theorem B3182699 : Blo 1885435 3182699 := bstep (se 1 (by rfl) ⟨2387024, by rfl⟩ : syracuseStep 3182699 = 4774049) B4774049
theorem B2121799 : Blo 1885435 2121799 := bstep (se 1 (by rfl) ⟨1591349, by rfl⟩ : syracuseStep 2121799 = 3182699) B3182699
theorem B2829065 : Blo 1885435 2829065 := bstep (se 2 (by rfl) ⟨1060899, by rfl⟩ : syracuseStep 2829065 = 2121799) B2121799
theorem B1886043 : Blo 1885435 1886043 := bstep (se 1 (by rfl) ⟨1414532, by rfl⟩ : syracuseStep 1886043 = 2829065) B2829065
theorem B9548117 : Blo 1885435 9548117 := bbase (se 10 (by rfl) ⟨13986, by rfl⟩ : syracuseStep 9548117 = 27973) (by norm_num)
theorem B6365411 : Blo 1885435 6365411 := bstep (se 1 (by rfl) ⟨4774058, by rfl⟩ : syracuseStep 6365411 = 9548117) B9548117
theorem B4243607 : Blo 1885435 4243607 := bstep (se 1 (by rfl) ⟨3182705, by rfl⟩ : syracuseStep 4243607 = 6365411) B6365411
theorem B2829071 : Blo 1885435 2829071 := bstep (se 1 (by rfl) ⟨2121803, by rfl⟩ : syracuseStep 2829071 = 4243607) B4243607
theorem B1886047 : Blo 1885435 1886047 := bstep (se 1 (by rfl) ⟨1414535, by rfl⟩ : syracuseStep 1886047 = 2829071) B2829071
theorem B2829077 : Blo 1885435 2829077 := bbase (se 6 (by rfl) ⟨66306, by rfl⟩ : syracuseStep 2829077 = 132613) (by norm_num)
theorem B1886051 : Blo 1885435 1886051 := bstep (se 1 (by rfl) ⟨1414538, by rfl⟩ : syracuseStep 1886051 = 2829077) B2829077
theorem B4301525 : Blo 1885435 4301525 := bbase (se 7 (by rfl) ⟨50408, by rfl⟩ : syracuseStep 4301525 = 100817) (by norm_num)
theorem B2867683 : Blo 1885435 2867683 := bstep (se 1 (by rfl) ⟨2150762, by rfl⟩ : syracuseStep 2867683 = 4301525) B4301525
theorem B3823577 : Blo 1885435 3823577 := bstep (se 2 (by rfl) ⟨1433841, by rfl⟩ : syracuseStep 3823577 = 2867683) B2867683
theorem B2549051 : Blo 1885435 2549051 := bstep (se 1 (by rfl) ⟨1911788, by rfl⟩ : syracuseStep 2549051 = 3823577) B3823577
theorem B27189877 : Blo 1885435 27189877 := bstep (se 5 (by rfl) ⟨1274525, by rfl⟩ : syracuseStep 27189877 = 2549051) B2549051
theorem B36253169 : Blo 1885435 36253169 := bstep (se 2 (by rfl) ⟨13594938, by rfl⟩ : syracuseStep 36253169 = 27189877) B27189877
theorem B24168779 : Blo 1885435 24168779 := bstep (se 1 (by rfl) ⟨18126584, by rfl⟩ : syracuseStep 24168779 = 36253169) B36253169
theorem B16112519 : Blo 1885435 16112519 := bstep (se 1 (by rfl) ⟨12084389, by rfl⟩ : syracuseStep 16112519 = 24168779) B24168779
theorem B10741679 : Blo 1885435 10741679 := bstep (se 1 (by rfl) ⟨8056259, by rfl⟩ : syracuseStep 10741679 = 16112519) B16112519
theorem B7161119 : Blo 1885435 7161119 := bstep (se 1 (by rfl) ⟨5370839, by rfl⟩ : syracuseStep 7161119 = 10741679) B10741679
theorem B4774079 : Blo 1885435 4774079 := bstep (se 1 (by rfl) ⟨3580559, by rfl⟩ : syracuseStep 4774079 = 7161119) B7161119
theorem B3182719 : Blo 1885435 3182719 := bstep (se 1 (by rfl) ⟨2387039, by rfl⟩ : syracuseStep 3182719 = 4774079) B4774079
theorem B4243625 : Blo 1885435 4243625 := bstep (se 2 (by rfl) ⟨1591359, by rfl⟩ : syracuseStep 4243625 = 3182719) B3182719
theorem B2829083 : Blo 1885435 2829083 := bstep (se 1 (by rfl) ⟨2121812, by rfl⟩ : syracuseStep 2829083 = 4243625) B4243625
theorem B1886055 : Blo 1885435 1886055 := bstep (se 1 (by rfl) ⟨1414541, by rfl⟩ : syracuseStep 1886055 = 2829083) B2829083
theorem B2121817 : Blo 1885435 2121817 := bbase (se 2 (by rfl) ⟨795681, by rfl⟩ : syracuseStep 2121817 = 1591363) (by norm_num)
theorem B2829089 : Blo 1885435 2829089 := bstep (se 2 (by rfl) ⟨1060908, by rfl⟩ : syracuseStep 2829089 = 2121817) B2121817
theorem B1886059 : Blo 1885435 1886059 := bstep (se 1 (by rfl) ⟨1414544, by rfl⟩ : syracuseStep 1886059 = 2829089) B2829089
theorem B2265833 : Blo 1885435 2265833 := bbase (se 2 (by rfl) ⟨849687, by rfl⟩ : syracuseStep 2265833 = 1699375) (by norm_num)
theorem B6042221 : Blo 1885435 6042221 := bstep (se 3 (by rfl) ⟨1132916, by rfl⟩ : syracuseStep 6042221 = 2265833) B2265833
theorem B4028147 : Blo 1885435 4028147 := bstep (se 1 (by rfl) ⟨3021110, by rfl⟩ : syracuseStep 4028147 = 6042221) B6042221
theorem B2685431 : Blo 1885435 2685431 := bstep (se 1 (by rfl) ⟨2014073, by rfl⟩ : syracuseStep 2685431 = 4028147) B4028147
theorem B7161149 : Blo 1885435 7161149 := bstep (se 3 (by rfl) ⟨1342715, by rfl⟩ : syracuseStep 7161149 = 2685431) B2685431
theorem B4774099 : Blo 1885435 4774099 := bstep (se 1 (by rfl) ⟨3580574, by rfl⟩ : syracuseStep 4774099 = 7161149) B7161149
theorem B6365465 : Blo 1885435 6365465 := bstep (se 2 (by rfl) ⟨2387049, by rfl⟩ : syracuseStep 6365465 = 4774099) B4774099
theorem B4243643 : Blo 1885435 4243643 := bstep (se 1 (by rfl) ⟨3182732, by rfl⟩ : syracuseStep 4243643 = 6365465) B6365465
theorem B2829095 : Blo 1885435 2829095 := bstep (se 1 (by rfl) ⟨2121821, by rfl⟩ : syracuseStep 2829095 = 4243643) B4243643
theorem B1886063 : Blo 1885435 1886063 := bstep (se 1 (by rfl) ⟨1414547, by rfl⟩ : syracuseStep 1886063 = 2829095) B2829095
theorem B2829101 : Blo 1885435 2829101 := bbase (se 3 (by rfl) ⟨530456, by rfl⟩ : syracuseStep 2829101 = 1060913) (by norm_num)
theorem B1886067 : Blo 1885435 1886067 := bstep (se 1 (by rfl) ⟨1414550, by rfl⟩ : syracuseStep 1886067 = 2829101) B2829101
theorem B4243661 : Blo 1885435 4243661 := bbase (se 3 (by rfl) ⟨795686, by rfl⟩ : syracuseStep 4243661 = 1591373) (by norm_num)
theorem B2829107 : Blo 1885435 2829107 := bstep (se 1 (by rfl) ⟨2121830, by rfl⟩ : syracuseStep 2829107 = 4243661) B4243661
theorem B1886071 : Blo 1885435 1886071 := bstep (se 1 (by rfl) ⟨1414553, by rfl⟩ : syracuseStep 1886071 = 2829107) B2829107
theorem B2387065 : Blo 1885435 2387065 := bbase (se 2 (by rfl) ⟨895149, by rfl⟩ : syracuseStep 2387065 = 1790299) (by norm_num)
theorem B3182753 : Blo 1885435 3182753 := bstep (se 2 (by rfl) ⟨1193532, by rfl⟩ : syracuseStep 3182753 = 2387065) B2387065
theorem B2121835 : Blo 1885435 2121835 := bstep (se 1 (by rfl) ⟨1591376, by rfl⟩ : syracuseStep 2121835 = 3182753) B3182753
theorem B2829113 : Blo 1885435 2829113 := bstep (se 2 (by rfl) ⟨1060917, by rfl⟩ : syracuseStep 2829113 = 2121835) B2121835
theorem B1886075 : Blo 1885435 1886075 := bstep (se 1 (by rfl) ⟨1414556, by rfl⟩ : syracuseStep 1886075 = 2829113) B2829113
theorem B4905301 : Blo 1885435 4905301 := bbase (se 10 (by rfl) ⟨7185, by rfl⟩ : syracuseStep 4905301 = 14371) (by norm_num)
theorem B6540401 : Blo 1885435 6540401 := bstep (se 2 (by rfl) ⟨2452650, by rfl⟩ : syracuseStep 6540401 = 4905301) B4905301
theorem B4360267 : Blo 1885435 4360267 := bstep (se 1 (by rfl) ⟨3270200, by rfl⟩ : syracuseStep 4360267 = 6540401) B6540401
theorem B5813689 : Blo 1885435 5813689 := bstep (se 2 (by rfl) ⟨2180133, by rfl⟩ : syracuseStep 5813689 = 4360267) B4360267
theorem B7751585 : Blo 1885435 7751585 := bstep (se 2 (by rfl) ⟨2906844, by rfl⟩ : syracuseStep 7751585 = 5813689) B5813689
theorem B20670893 : Blo 1885435 20670893 := bstep (se 3 (by rfl) ⟨3875792, by rfl⟩ : syracuseStep 20670893 = 7751585) B7751585
theorem B13780595 : Blo 1885435 13780595 := bstep (se 1 (by rfl) ⟨10335446, by rfl⟩ : syracuseStep 13780595 = 20670893) B20670893
theorem B9187063 : Blo 1885435 9187063 := bstep (se 1 (by rfl) ⟨6890297, by rfl⟩ : syracuseStep 9187063 = 13780595) B13780595
theorem B48997669 : Blo 1885435 48997669 := bstep (se 4 (by rfl) ⟨4593531, by rfl⟩ : syracuseStep 48997669 = 9187063) B9187063
theorem B65330225 : Blo 1885435 65330225 := bstep (se 2 (by rfl) ⟨24498834, by rfl⟩ : syracuseStep 65330225 = 48997669) B48997669
theorem B43553483 : Blo 1885435 43553483 := bstep (se 1 (by rfl) ⟨32665112, by rfl⟩ : syracuseStep 43553483 = 65330225) B65330225
theorem B29035655 : Blo 1885435 29035655 := bstep (se 1 (by rfl) ⟨21776741, by rfl⟩ : syracuseStep 29035655 = 43553483) B43553483
theorem B19357103 : Blo 1885435 19357103 := bstep (se 1 (by rfl) ⟨14517827, by rfl⟩ : syracuseStep 19357103 = 29035655) B29035655
theorem B51618941 : Blo 1885435 51618941 := bstep (se 3 (by rfl) ⟨9678551, by rfl⟩ : syracuseStep 51618941 = 19357103) B19357103
theorem B34412627 : Blo 1885435 34412627 := bstep (se 1 (by rfl) ⟨25809470, by rfl⟩ : syracuseStep 34412627 = 51618941) B51618941
theorem B22941751 : Blo 1885435 22941751 := bstep (se 1 (by rfl) ⟨17206313, by rfl⟩ : syracuseStep 22941751 = 34412627) B34412627
theorem B30589001 : Blo 1885435 30589001 := bstep (se 2 (by rfl) ⟨11470875, by rfl⟩ : syracuseStep 30589001 = 22941751) B22941751
theorem B20392667 : Blo 1885435 20392667 := bstep (se 1 (by rfl) ⟨15294500, by rfl⟩ : syracuseStep 20392667 = 30589001) B30589001
theorem B13595111 : Blo 1885435 13595111 := bstep (se 1 (by rfl) ⟨10196333, by rfl⟩ : syracuseStep 13595111 = 20392667) B20392667
theorem B9063407 : Blo 1885435 9063407 := bstep (se 1 (by rfl) ⟨6797555, by rfl⟩ : syracuseStep 9063407 = 13595111) B13595111
theorem B6042271 : Blo 1885435 6042271 := bstep (se 1 (by rfl) ⟨4531703, by rfl⟩ : syracuseStep 6042271 = 9063407) B9063407
theorem B8056361 : Blo 1885435 8056361 := bstep (se 2 (by rfl) ⟨3021135, by rfl⟩ : syracuseStep 8056361 = 6042271) B6042271
theorem B21483629 : Blo 1885435 21483629 := bstep (se 3 (by rfl) ⟨4028180, by rfl⟩ : syracuseStep 21483629 = 8056361) B8056361
theorem B14322419 : Blo 1885435 14322419 := bstep (se 1 (by rfl) ⟨10741814, by rfl⟩ : syracuseStep 14322419 = 21483629) B21483629
theorem B9548279 : Blo 1885435 9548279 := bstep (se 1 (by rfl) ⟨7161209, by rfl⟩ : syracuseStep 9548279 = 14322419) B14322419
theorem B6365519 : Blo 1885435 6365519 := bstep (se 1 (by rfl) ⟨4774139, by rfl⟩ : syracuseStep 6365519 = 9548279) B9548279
theorem B4243679 : Blo 1885435 4243679 := bstep (se 1 (by rfl) ⟨3182759, by rfl⟩ : syracuseStep 4243679 = 6365519) B6365519
theorem B2829119 : Blo 1885435 2829119 := bstep (se 1 (by rfl) ⟨2121839, by rfl⟩ : syracuseStep 2829119 = 4243679) B4243679
theorem B1886079 : Blo 1885435 1886079 := bstep (se 1 (by rfl) ⟨1414559, by rfl⟩ : syracuseStep 1886079 = 2829119) B2829119
theorem B2829125 : Blo 1885435 2829125 := bbase (se 4 (by rfl) ⟨265230, by rfl⟩ : syracuseStep 2829125 = 530461) (by norm_num)
theorem B1886083 : Blo 1885435 1886083 := bstep (se 1 (by rfl) ⟨1414562, by rfl⟩ : syracuseStep 1886083 = 2829125) B2829125
theorem B3182773 : Blo 1885435 3182773 := bbase (se 5 (by rfl) ⟨149192, by rfl⟩ : syracuseStep 3182773 = 298385) (by norm_num)
theorem B4243697 : Blo 1885435 4243697 := bstep (se 2 (by rfl) ⟨1591386, by rfl⟩ : syracuseStep 4243697 = 3182773) B3182773
theorem B2829131 : Blo 1885435 2829131 := bstep (se 1 (by rfl) ⟨2121848, by rfl⟩ : syracuseStep 2829131 = 4243697) B4243697
theorem B1886087 : Blo 1885435 1886087 := bstep (se 1 (by rfl) ⟨1414565, by rfl⟩ : syracuseStep 1886087 = 2829131) B2829131
theorem B2121853 : Blo 1885435 2121853 := bbase (se 3 (by rfl) ⟨397847, by rfl⟩ : syracuseStep 2121853 = 795695) (by norm_num)
theorem B2829137 : Blo 1885435 2829137 := bstep (se 2 (by rfl) ⟨1060926, by rfl⟩ : syracuseStep 2829137 = 2121853) B2121853
theorem B1886091 : Blo 1885435 1886091 := bstep (se 1 (by rfl) ⟨1414568, by rfl⟩ : syracuseStep 1886091 = 2829137) B2829137
theorem B6365573 : Blo 1885435 6365573 := bbase (se 4 (by rfl) ⟨596772, by rfl⟩ : syracuseStep 6365573 = 1193545) (by norm_num)
theorem B4243715 : Blo 1885435 4243715 := bstep (se 1 (by rfl) ⟨3182786, by rfl⟩ : syracuseStep 4243715 = 6365573) B6365573
theorem B2829143 : Blo 1885435 2829143 := bstep (se 1 (by rfl) ⟨2121857, by rfl⟩ : syracuseStep 2829143 = 4243715) B4243715
theorem B1886095 : Blo 1885435 1886095 := bstep (se 1 (by rfl) ⟨1414571, by rfl⟩ : syracuseStep 1886095 = 2829143) B2829143
theorem B2829149 : Blo 1885435 2829149 := bbase (se 3 (by rfl) ⟨530465, by rfl⟩ : syracuseStep 2829149 = 1060931) (by norm_num)
theorem B1886099 : Blo 1885435 1886099 := bstep (se 1 (by rfl) ⟨1414574, by rfl⟩ : syracuseStep 1886099 = 2829149) B2829149
theorem B4243733 : Blo 1885435 4243733 := bbase (se 6 (by rfl) ⟨99462, by rfl⟩ : syracuseStep 4243733 = 198925) (by norm_num)
theorem B2829155 : Blo 1885435 2829155 := bstep (se 1 (by rfl) ⟨2121866, by rfl⟩ : syracuseStep 2829155 = 4243733) B4243733
theorem B1886103 : Blo 1885435 1886103 := bstep (se 1 (by rfl) ⟨1414577, by rfl⟩ : syracuseStep 1886103 = 2829155) B2829155
theorem B7161317 : Blo 1885435 7161317 := bbase (se 4 (by rfl) ⟨671373, by rfl⟩ : syracuseStep 7161317 = 1342747) (by norm_num)
theorem B4774211 : Blo 1885435 4774211 := bstep (se 1 (by rfl) ⟨3580658, by rfl⟩ : syracuseStep 4774211 = 7161317) B7161317
theorem B3182807 : Blo 1885435 3182807 := bstep (se 1 (by rfl) ⟨2387105, by rfl⟩ : syracuseStep 3182807 = 4774211) B4774211
theorem B2121871 : Blo 1885435 2121871 := bstep (se 1 (by rfl) ⟨1591403, by rfl⟩ : syracuseStep 2121871 = 3182807) B3182807
theorem B2829161 : Blo 1885435 2829161 := bstep (se 2 (by rfl) ⟨1060935, by rfl⟩ : syracuseStep 2829161 = 2121871) B2121871
theorem B1886107 : Blo 1885435 1886107 := bstep (se 1 (by rfl) ⟨1414580, by rfl⟩ : syracuseStep 1886107 = 2829161) B2829161
theorem B4531781 : Blo 1885435 4531781 := bbase (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) (by norm_num)
theorem B3021187 : Blo 1885435 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B4028249 : Blo 1885435 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B10741997 : Blo 1885435 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B7161331 : Blo 1885435 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B9548441 : Blo 1885435 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B6365627 : Blo 1885435 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B4243751 : Blo 1885435 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B2829167 : Blo 1885435 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B1886111 : Blo 1885435 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B2829173 : Blo 1885435 2829173 := bbase (se 5 (by rfl) ⟨132617, by rfl⟩ : syracuseStep 2829173 = 265235) (by norm_num)
theorem B1886115 : Blo 1885435 1886115 := bstep (se 1 (by rfl) ⟨1414586, by rfl⟩ : syracuseStep 1886115 = 2829173) B2829173
theorem B5098277 : Blo 1885435 5098277 := bbase (se 4 (by rfl) ⟨477963, by rfl⟩ : syracuseStep 5098277 = 955927) (by norm_num)
theorem B3398851 : Blo 1885435 3398851 := bstep (se 1 (by rfl) ⟨2549138, by rfl⟩ : syracuseStep 3398851 = 5098277) B5098277
theorem B4531801 : Blo 1885435 4531801 := bstep (se 2 (by rfl) ⟨1699425, by rfl⟩ : syracuseStep 4531801 = 3398851) B3398851
theorem B6042401 : Blo 1885435 6042401 := bstep (se 2 (by rfl) ⟨2265900, by rfl⟩ : syracuseStep 6042401 = 4531801) B4531801
theorem B4028267 : Blo 1885435 4028267 := bstep (se 1 (by rfl) ⟨3021200, by rfl⟩ : syracuseStep 4028267 = 6042401) B6042401
theorem B2685511 : Blo 1885435 2685511 := bstep (se 1 (by rfl) ⟨2014133, by rfl⟩ : syracuseStep 2685511 = 4028267) B4028267
theorem B3580681 : Blo 1885435 3580681 := bstep (se 2 (by rfl) ⟨1342755, by rfl⟩ : syracuseStep 3580681 = 2685511) B2685511
theorem B4774241 : Blo 1885435 4774241 := bstep (se 2 (by rfl) ⟨1790340, by rfl⟩ : syracuseStep 4774241 = 3580681) B3580681
theorem B3182827 : Blo 1885435 3182827 := bstep (se 1 (by rfl) ⟨2387120, by rfl⟩ : syracuseStep 3182827 = 4774241) B4774241
theorem B4243769 : Blo 1885435 4243769 := bstep (se 2 (by rfl) ⟨1591413, by rfl⟩ : syracuseStep 4243769 = 3182827) B3182827
theorem B2829179 : Blo 1885435 2829179 := bstep (se 1 (by rfl) ⟨2121884, by rfl⟩ : syracuseStep 2829179 = 4243769) B4243769
theorem B1886119 : Blo 1885435 1886119 := bstep (se 1 (by rfl) ⟨1414589, by rfl⟩ : syracuseStep 1886119 = 2829179) B2829179
theorem B2121889 : Blo 1885435 2121889 := bbase (se 2 (by rfl) ⟨795708, by rfl⟩ : syracuseStep 2121889 = 1591417) (by norm_num)
theorem B2829185 : Blo 1885435 2829185 := bstep (se 2 (by rfl) ⟨1060944, by rfl⟩ : syracuseStep 2829185 = 2121889) B2121889
theorem B1886123 : Blo 1885435 1886123 := bstep (se 1 (by rfl) ⟨1414592, by rfl⟩ : syracuseStep 1886123 = 2829185) B2829185
theorem B4774261 : Blo 1885435 4774261 := bbase (se 5 (by rfl) ⟨223793, by rfl⟩ : syracuseStep 4774261 = 447587) (by norm_num)
theorem B6365681 : Blo 1885435 6365681 := bstep (se 2 (by rfl) ⟨2387130, by rfl⟩ : syracuseStep 6365681 = 4774261) B4774261
theorem B4243787 : Blo 1885435 4243787 := bstep (se 1 (by rfl) ⟨3182840, by rfl⟩ : syracuseStep 4243787 = 6365681) B6365681
theorem B2829191 : Blo 1885435 2829191 := bstep (se 1 (by rfl) ⟨2121893, by rfl⟩ : syracuseStep 2829191 = 4243787) B4243787
theorem B1886127 : Blo 1885435 1886127 := bstep (se 1 (by rfl) ⟨1414595, by rfl⟩ : syracuseStep 1886127 = 2829191) B2829191
theorem B2829197 : Blo 1885435 2829197 := bbase (se 3 (by rfl) ⟨530474, by rfl⟩ : syracuseStep 2829197 = 1060949) (by norm_num)
theorem B1886131 : Blo 1885435 1886131 := bstep (se 1 (by rfl) ⟨1414598, by rfl⟩ : syracuseStep 1886131 = 2829197) B2829197
theorem B4243805 : Blo 1885435 4243805 := bbase (se 3 (by rfl) ⟨795713, by rfl⟩ : syracuseStep 4243805 = 1591427) (by norm_num)
theorem B2829203 : Blo 1885435 2829203 := bstep (se 1 (by rfl) ⟨2121902, by rfl⟩ : syracuseStep 2829203 = 4243805) B4243805
theorem B1886135 : Blo 1885435 1886135 := bstep (se 1 (by rfl) ⟨1414601, by rfl⟩ : syracuseStep 1886135 = 2829203) B2829203
theorem B3182861 : Blo 1885435 3182861 := bbase (se 3 (by rfl) ⟨596786, by rfl⟩ : syracuseStep 3182861 = 1193573) (by norm_num)
theorem B2121907 : Blo 1885435 2121907 := bstep (se 1 (by rfl) ⟨1591430, by rfl⟩ : syracuseStep 2121907 = 3182861) B3182861
theorem B2829209 : Blo 1885435 2829209 := bstep (se 2 (by rfl) ⟨1060953, by rfl⟩ : syracuseStep 2829209 = 2121907) B2121907
theorem B1886139 : Blo 1885435 1886139 := bstep (se 1 (by rfl) ⟨1414604, by rfl⟩ : syracuseStep 1886139 = 2829209) B2829209
theorem B16113269 : Blo 1885435 16113269 := bbase (se 5 (by rfl) ⟨755309, by rfl⟩ : syracuseStep 16113269 = 1510619) (by norm_num)
theorem B10742179 : Blo 1885435 10742179 := bstep (se 1 (by rfl) ⟨8056634, by rfl⟩ : syracuseStep 10742179 = 16113269) B16113269
theorem B14322905 : Blo 1885435 14322905 := bstep (se 2 (by rfl) ⟨5371089, by rfl⟩ : syracuseStep 14322905 = 10742179) B10742179
theorem B9548603 : Blo 1885435 9548603 := bstep (se 1 (by rfl) ⟨7161452, by rfl⟩ : syracuseStep 9548603 = 14322905) B14322905
theorem B6365735 : Blo 1885435 6365735 := bstep (se 1 (by rfl) ⟨4774301, by rfl⟩ : syracuseStep 6365735 = 9548603) B9548603
theorem B4243823 : Blo 1885435 4243823 := bstep (se 1 (by rfl) ⟨3182867, by rfl⟩ : syracuseStep 4243823 = 6365735) B6365735
theorem B2829215 : Blo 1885435 2829215 := bstep (se 1 (by rfl) ⟨2121911, by rfl⟩ : syracuseStep 2829215 = 4243823) B4243823
theorem B1886143 : Blo 1885435 1886143 := bstep (se 1 (by rfl) ⟨1414607, by rfl⟩ : syracuseStep 1886143 = 2829215) B2829215
theorem B2829221 : Blo 1885435 2829221 := bbase (se 4 (by rfl) ⟨265239, by rfl⟩ : syracuseStep 2829221 = 530479) (by norm_num)
theorem B1886147 : Blo 1885435 1886147 := bstep (se 1 (by rfl) ⟨1414610, by rfl⟩ : syracuseStep 1886147 = 2829221) B2829221
theorem B2387161 : Blo 1885435 2387161 := bbase (se 2 (by rfl) ⟨895185, by rfl⟩ : syracuseStep 2387161 = 1790371) (by norm_num)
theorem B3182881 : Blo 1885435 3182881 := bstep (se 2 (by rfl) ⟨1193580, by rfl⟩ : syracuseStep 3182881 = 2387161) B2387161
theorem B4243841 : Blo 1885435 4243841 := bstep (se 2 (by rfl) ⟨1591440, by rfl⟩ : syracuseStep 4243841 = 3182881) B3182881
theorem B2829227 : Blo 1885435 2829227 := bstep (se 1 (by rfl) ⟨2121920, by rfl⟩ : syracuseStep 2829227 = 4243841) B4243841
theorem B1886151 : Blo 1885435 1886151 := bstep (se 1 (by rfl) ⟨1414613, by rfl⟩ : syracuseStep 1886151 = 2829227) B2829227
theorem B2121925 : Blo 1885435 2121925 := bbase (se 4 (by rfl) ⟨198930, by rfl⟩ : syracuseStep 2121925 = 397861) (by norm_num)
theorem B2829233 : Blo 1885435 2829233 := bstep (se 2 (by rfl) ⟨1060962, by rfl⟩ : syracuseStep 2829233 = 2121925) B2121925
theorem B1886155 : Blo 1885435 1886155 := bstep (se 1 (by rfl) ⟨1414616, by rfl⟩ : syracuseStep 1886155 = 2829233) B2829233
theorem B3580757 : Blo 1885435 3580757 := bbase (se 9 (by rfl) ⟨10490, by rfl⟩ : syracuseStep 3580757 = 20981) (by norm_num)
theorem B2387171 : Blo 1885435 2387171 := bstep (se 1 (by rfl) ⟨1790378, by rfl⟩ : syracuseStep 2387171 = 3580757) B3580757
theorem B6365789 : Blo 1885435 6365789 := bstep (se 3 (by rfl) ⟨1193585, by rfl⟩ : syracuseStep 6365789 = 2387171) B2387171
theorem B4243859 : Blo 1885435 4243859 := bstep (se 1 (by rfl) ⟨3182894, by rfl⟩ : syracuseStep 4243859 = 6365789) B6365789
theorem B2829239 : Blo 1885435 2829239 := bstep (se 1 (by rfl) ⟨2121929, by rfl⟩ : syracuseStep 2829239 = 4243859) B4243859
theorem B1886159 : Blo 1885435 1886159 := bstep (se 1 (by rfl) ⟨1414619, by rfl⟩ : syracuseStep 1886159 = 2829239) B2829239
theorem B2829245 : Blo 1885435 2829245 := bbase (se 3 (by rfl) ⟨530483, by rfl⟩ : syracuseStep 2829245 = 1060967) (by norm_num)
theorem B1886163 : Blo 1885435 1886163 := bstep (se 1 (by rfl) ⟨1414622, by rfl⟩ : syracuseStep 1886163 = 2829245) B2829245
theorem B4243877 : Blo 1885435 4243877 := bbase (se 4 (by rfl) ⟨397863, by rfl⟩ : syracuseStep 4243877 = 795727) (by norm_num)
theorem B2829251 : Blo 1885435 2829251 := bstep (se 1 (by rfl) ⟨2121938, by rfl⟩ : syracuseStep 2829251 = 4243877) B4243877
theorem B1886167 : Blo 1885435 1886167 := bstep (se 1 (by rfl) ⟨1414625, by rfl⟩ : syracuseStep 1886167 = 2829251) B2829251
theorem B4774373 : Blo 1885435 4774373 := bbase (se 4 (by rfl) ⟨447597, by rfl⟩ : syracuseStep 4774373 = 895195) (by norm_num)
theorem B3182915 : Blo 1885435 3182915 := bstep (se 1 (by rfl) ⟨2387186, by rfl⟩ : syracuseStep 3182915 = 4774373) B4774373
theorem B2121943 : Blo 1885435 2121943 := bstep (se 1 (by rfl) ⟨1591457, by rfl⟩ : syracuseStep 2121943 = 3182915) B3182915
theorem B2829257 : Blo 1885435 2829257 := bstep (se 2 (by rfl) ⟨1060971, by rfl⟩ : syracuseStep 2829257 = 2121943) B2121943
theorem B1886171 : Blo 1885435 1886171 := bstep (se 1 (by rfl) ⟨1414628, by rfl⟩ : syracuseStep 1886171 = 2829257) B2829257
theorem B2014193 : Blo 1885435 2014193 := bbase (se 2 (by rfl) ⟨755322, by rfl⟩ : syracuseStep 2014193 = 1510645) (by norm_num)
theorem B5371181 : Blo 1885435 5371181 := bstep (se 3 (by rfl) ⟨1007096, by rfl⟩ : syracuseStep 5371181 = 2014193) B2014193
theorem B3580787 : Blo 1885435 3580787 := bstep (se 1 (by rfl) ⟨2685590, by rfl⟩ : syracuseStep 3580787 = 5371181) B5371181
theorem B9548765 : Blo 1885435 9548765 := bstep (se 3 (by rfl) ⟨1790393, by rfl⟩ : syracuseStep 9548765 = 3580787) B3580787
theorem B6365843 : Blo 1885435 6365843 := bstep (se 1 (by rfl) ⟨4774382, by rfl⟩ : syracuseStep 6365843 = 9548765) B9548765
theorem B4243895 : Blo 1885435 4243895 := bstep (se 1 (by rfl) ⟨3182921, by rfl⟩ : syracuseStep 4243895 = 6365843) B6365843
theorem B2829263 : Blo 1885435 2829263 := bstep (se 1 (by rfl) ⟨2121947, by rfl⟩ : syracuseStep 2829263 = 4243895) B4243895
theorem B1886175 : Blo 1885435 1886175 := bstep (se 1 (by rfl) ⟨1414631, by rfl⟩ : syracuseStep 1886175 = 2829263) B2829263
theorem B2829269 : Blo 1885435 2829269 := bbase (se 7 (by rfl) ⟨33155, by rfl⟩ : syracuseStep 2829269 = 66311) (by norm_num)
theorem B1886179 : Blo 1885435 1886179 := bstep (se 1 (by rfl) ⟨1414634, by rfl⟩ : syracuseStep 1886179 = 2829269) B2829269
theorem B7161605 : Blo 1885435 7161605 := bbase (se 4 (by rfl) ⟨671400, by rfl⟩ : syracuseStep 7161605 = 1342801) (by norm_num)
theorem B4774403 : Blo 1885435 4774403 := bstep (se 1 (by rfl) ⟨3580802, by rfl⟩ : syracuseStep 4774403 = 7161605) B7161605
theorem B3182935 : Blo 1885435 3182935 := bstep (se 1 (by rfl) ⟨2387201, by rfl⟩ : syracuseStep 3182935 = 4774403) B4774403
theorem B4243913 : Blo 1885435 4243913 := bstep (se 2 (by rfl) ⟨1591467, by rfl⟩ : syracuseStep 4243913 = 3182935) B3182935
theorem B2829275 : Blo 1885435 2829275 := bstep (se 1 (by rfl) ⟨2121956, by rfl⟩ : syracuseStep 2829275 = 4243913) B4243913
theorem B1886183 : Blo 1885435 1886183 := bstep (se 1 (by rfl) ⟨1414637, by rfl⟩ : syracuseStep 1886183 = 2829275) B2829275
theorem B2121961 : Blo 1885435 2121961 := bbase (se 2 (by rfl) ⟨795735, by rfl⟩ : syracuseStep 2121961 = 1591471) (by norm_num)
theorem B2829281 : Blo 1885435 2829281 := bstep (se 2 (by rfl) ⟨1060980, by rfl⟩ : syracuseStep 2829281 = 2121961) B2121961
theorem B1886187 : Blo 1885435 1886187 := bstep (se 1 (by rfl) ⟨1414640, by rfl⟩ : syracuseStep 1886187 = 2829281) B2829281
theorem B10742453 : Blo 1885435 10742453 := bbase (se 5 (by rfl) ⟨503552, by rfl⟩ : syracuseStep 10742453 = 1007105) (by norm_num)
theorem B7161635 : Blo 1885435 7161635 := bstep (se 1 (by rfl) ⟨5371226, by rfl⟩ : syracuseStep 7161635 = 10742453) B10742453
theorem B4774423 : Blo 1885435 4774423 := bstep (se 1 (by rfl) ⟨3580817, by rfl⟩ : syracuseStep 4774423 = 7161635) B7161635
theorem B6365897 : Blo 1885435 6365897 := bstep (se 2 (by rfl) ⟨2387211, by rfl⟩ : syracuseStep 6365897 = 4774423) B4774423
theorem B4243931 : Blo 1885435 4243931 := bstep (se 1 (by rfl) ⟨3182948, by rfl⟩ : syracuseStep 4243931 = 6365897) B6365897
theorem B2829287 : Blo 1885435 2829287 := bstep (se 1 (by rfl) ⟨2121965, by rfl⟩ : syracuseStep 2829287 = 4243931) B4243931
theorem B1886191 : Blo 1885435 1886191 := bstep (se 1 (by rfl) ⟨1414643, by rfl⟩ : syracuseStep 1886191 = 2829287) B2829287
theorem B2829293 : Blo 1885435 2829293 := bbase (se 3 (by rfl) ⟨530492, by rfl⟩ : syracuseStep 2829293 = 1060985) (by norm_num)
theorem B1886195 : Blo 1885435 1886195 := bstep (se 1 (by rfl) ⟨1414646, by rfl⟩ : syracuseStep 1886195 = 2829293) B2829293
theorem B4243949 : Blo 1885435 4243949 := bbase (se 3 (by rfl) ⟨795740, by rfl⟩ : syracuseStep 4243949 = 1591481) (by norm_num)
theorem B2829299 : Blo 1885435 2829299 := bstep (se 1 (by rfl) ⟨2121974, by rfl⟩ : syracuseStep 2829299 = 4243949) B4243949
theorem B1886199 : Blo 1885435 1886199 := bstep (se 1 (by rfl) ⟨1414649, by rfl⟩ : syracuseStep 1886199 = 2829299) B2829299
theorem B2041705 : Blo 1885435 2041705 := bbase (se 2 (by rfl) ⟨765639, by rfl⟩ : syracuseStep 2041705 = 1531279) (by norm_num)
theorem B10889093 : Blo 1885435 10889093 := bstep (se 4 (by rfl) ⟨1020852, by rfl⟩ : syracuseStep 10889093 = 2041705) B2041705
theorem B7259395 : Blo 1885435 7259395 := bstep (se 1 (by rfl) ⟨5444546, by rfl⟩ : syracuseStep 7259395 = 10889093) B10889093
theorem B9679193 : Blo 1885435 9679193 := bstep (se 2 (by rfl) ⟨3629697, by rfl⟩ : syracuseStep 9679193 = 7259395) B7259395
theorem B6452795 : Blo 1885435 6452795 := bstep (se 1 (by rfl) ⟨4839596, by rfl⟩ : syracuseStep 6452795 = 9679193) B9679193
theorem B17207453 : Blo 1885435 17207453 := bstep (se 3 (by rfl) ⟨3226397, by rfl⟩ : syracuseStep 17207453 = 6452795) B6452795
theorem B11471635 : Blo 1885435 11471635 := bstep (se 1 (by rfl) ⟨8603726, by rfl⟩ : syracuseStep 11471635 = 17207453) B17207453
theorem B15295513 : Blo 1885435 15295513 := bstep (se 2 (by rfl) ⟨5735817, by rfl⟩ : syracuseStep 15295513 = 11471635) B11471635
theorem B20394017 : Blo 1885435 20394017 := bstep (se 2 (by rfl) ⟨7647756, by rfl⟩ : syracuseStep 20394017 = 15295513) B15295513
theorem B13596011 : Blo 1885435 13596011 := bstep (se 1 (by rfl) ⟨10197008, by rfl⟩ : syracuseStep 13596011 = 20394017) B20394017
theorem B9064007 : Blo 1885435 9064007 := bstep (se 1 (by rfl) ⟨6798005, by rfl⟩ : syracuseStep 9064007 = 13596011) B13596011
theorem B6042671 : Blo 1885435 6042671 := bstep (se 1 (by rfl) ⟨4532003, by rfl⟩ : syracuseStep 6042671 = 9064007) B9064007
theorem B4028447 : Blo 1885435 4028447 := bstep (se 1 (by rfl) ⟨3021335, by rfl⟩ : syracuseStep 4028447 = 6042671) B6042671
theorem B2685631 : Blo 1885435 2685631 := bstep (se 1 (by rfl) ⟨2014223, by rfl⟩ : syracuseStep 2685631 = 4028447) B4028447
theorem B3580841 : Blo 1885435 3580841 := bstep (se 2 (by rfl) ⟨1342815, by rfl⟩ : syracuseStep 3580841 = 2685631) B2685631
theorem B2387227 : Blo 1885435 2387227 := bstep (se 1 (by rfl) ⟨1790420, by rfl⟩ : syracuseStep 2387227 = 3580841) B3580841
theorem B3182969 : Blo 1885435 3182969 := bstep (se 2 (by rfl) ⟨1193613, by rfl⟩ : syracuseStep 3182969 = 2387227) B2387227
theorem B2121979 : Blo 1885435 2121979 := bstep (se 1 (by rfl) ⟨1591484, by rfl⟩ : syracuseStep 2121979 = 3182969) B3182969
theorem B2829305 : Blo 1885435 2829305 := bstep (se 2 (by rfl) ⟨1060989, by rfl⟩ : syracuseStep 2829305 = 2121979) B2121979
theorem B1886203 : Blo 1885435 1886203 := bstep (se 1 (by rfl) ⟨1414652, by rfl⟩ : syracuseStep 1886203 = 2829305) B2829305
theorem B8721125 : Blo 1885435 8721125 := bbase (se 4 (by rfl) ⟨817605, by rfl⟩ : syracuseStep 8721125 = 1635211) (by norm_num)
theorem B5814083 : Blo 1885435 5814083 := bstep (se 1 (by rfl) ⟨4360562, by rfl⟩ : syracuseStep 5814083 = 8721125) B8721125
theorem B3876055 : Blo 1885435 3876055 := bstep (se 1 (by rfl) ⟨2907041, by rfl⟩ : syracuseStep 3876055 = 5814083) B5814083
theorem B82689173 : Blo 1885435 82689173 := bstep (se 6 (by rfl) ⟨1938027, by rfl⟩ : syracuseStep 82689173 = 3876055) B3876055
theorem B55126115 : Blo 1885435 55126115 := bstep (se 1 (by rfl) ⟨41344586, by rfl⟩ : syracuseStep 55126115 = 82689173) B82689173
theorem B36750743 : Blo 1885435 36750743 := bstep (se 1 (by rfl) ⟨27563057, by rfl⟩ : syracuseStep 36750743 = 55126115) B55126115
theorem B24500495 : Blo 1885435 24500495 := bstep (se 1 (by rfl) ⟨18375371, by rfl⟩ : syracuseStep 24500495 = 36750743) B36750743
theorem B16333663 : Blo 1885435 16333663 := bstep (se 1 (by rfl) ⟨12250247, by rfl⟩ : syracuseStep 16333663 = 24500495) B24500495
theorem B21778217 : Blo 1885435 21778217 := bstep (se 2 (by rfl) ⟨8166831, by rfl⟩ : syracuseStep 21778217 = 16333663) B16333663
theorem B14518811 : Blo 1885435 14518811 := bstep (se 1 (by rfl) ⟨10889108, by rfl⟩ : syracuseStep 14518811 = 21778217) B21778217
theorem B9679207 : Blo 1885435 9679207 := bstep (se 1 (by rfl) ⟨7259405, by rfl⟩ : syracuseStep 9679207 = 14518811) B14518811
theorem B12905609 : Blo 1885435 12905609 := bstep (se 2 (by rfl) ⟨4839603, by rfl⟩ : syracuseStep 12905609 = 9679207) B9679207
theorem B34414957 : Blo 1885435 34414957 := bstep (se 3 (by rfl) ⟨6452804, by rfl⟩ : syracuseStep 34414957 = 12905609) B12905609
theorem B45886609 : Blo 1885435 45886609 := bstep (se 2 (by rfl) ⟨17207478, by rfl⟩ : syracuseStep 45886609 = 34414957) B34414957
theorem B61182145 : Blo 1885435 61182145 := bstep (se 2 (by rfl) ⟨22943304, by rfl⟩ : syracuseStep 61182145 = 45886609) B45886609
theorem B81576193 : Blo 1885435 81576193 := bstep (se 2 (by rfl) ⟨30591072, by rfl⟩ : syracuseStep 81576193 = 61182145) B61182145
theorem B108768257 : Blo 1885435 108768257 := bstep (se 2 (by rfl) ⟨40788096, by rfl⟩ : syracuseStep 108768257 = 81576193) B81576193
theorem B72512171 : Blo 1885435 72512171 := bstep (se 1 (by rfl) ⟨54384128, by rfl⟩ : syracuseStep 72512171 = 108768257) B108768257
theorem B48341447 : Blo 1885435 48341447 := bstep (se 1 (by rfl) ⟨36256085, by rfl⟩ : syracuseStep 48341447 = 72512171) B72512171
theorem B32227631 : Blo 1885435 32227631 := bstep (se 1 (by rfl) ⟨24170723, by rfl⟩ : syracuseStep 32227631 = 48341447) B48341447
theorem B21485087 : Blo 1885435 21485087 := bstep (se 1 (by rfl) ⟨16113815, by rfl⟩ : syracuseStep 21485087 = 32227631) B32227631
theorem B14323391 : Blo 1885435 14323391 := bstep (se 1 (by rfl) ⟨10742543, by rfl⟩ : syracuseStep 14323391 = 21485087) B21485087
theorem B9548927 : Blo 1885435 9548927 := bstep (se 1 (by rfl) ⟨7161695, by rfl⟩ : syracuseStep 9548927 = 14323391) B14323391
theorem B6365951 : Blo 1885435 6365951 := bstep (se 1 (by rfl) ⟨4774463, by rfl⟩ : syracuseStep 6365951 = 9548927) B9548927
theorem B4243967 : Blo 1885435 4243967 := bstep (se 1 (by rfl) ⟨3182975, by rfl⟩ : syracuseStep 4243967 = 6365951) B6365951
theorem B2829311 : Blo 1885435 2829311 := bstep (se 1 (by rfl) ⟨2121983, by rfl⟩ : syracuseStep 2829311 = 4243967) B4243967
theorem B1886207 : Blo 1885435 1886207 := bstep (se 1 (by rfl) ⟨1414655, by rfl⟩ : syracuseStep 1886207 = 2829311) B2829311
theorem B2829317 : Blo 1885435 2829317 := bbase (se 4 (by rfl) ⟨265248, by rfl⟩ : syracuseStep 2829317 = 530497) (by norm_num)
theorem B1886211 : Blo 1885435 1886211 := bstep (se 1 (by rfl) ⟨1414658, by rfl⟩ : syracuseStep 1886211 = 2829317) B2829317
theorem B3182989 : Blo 1885435 3182989 := bbase (se 3 (by rfl) ⟨596810, by rfl⟩ : syracuseStep 3182989 = 1193621) (by norm_num)
theorem B4243985 : Blo 1885435 4243985 := bstep (se 2 (by rfl) ⟨1591494, by rfl⟩ : syracuseStep 4243985 = 3182989) B3182989
theorem B2829323 : Blo 1885435 2829323 := bstep (se 1 (by rfl) ⟨2121992, by rfl⟩ : syracuseStep 2829323 = 4243985) B4243985
theorem B1886215 : Blo 1885435 1886215 := bstep (se 1 (by rfl) ⟨1414661, by rfl⟩ : syracuseStep 1886215 = 2829323) B2829323
theorem B2121997 : Blo 1885435 2121997 := bbase (se 3 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 2121997 = 795749) (by norm_num)
theorem B2829329 : Blo 1885435 2829329 := bstep (se 2 (by rfl) ⟨1060998, by rfl⟩ : syracuseStep 2829329 = 2121997) B2121997
theorem B1886219 : Blo 1885435 1886219 := bstep (se 1 (by rfl) ⟨1414664, by rfl⟩ : syracuseStep 1886219 = 2829329) B2829329
theorem B6366005 : Blo 1885435 6366005 := bbase (se 5 (by rfl) ⟨298406, by rfl⟩ : syracuseStep 6366005 = 596813) (by norm_num)
theorem B4244003 : Blo 1885435 4244003 := bstep (se 1 (by rfl) ⟨3183002, by rfl⟩ : syracuseStep 4244003 = 6366005) B6366005
theorem B2829335 : Blo 1885435 2829335 := bstep (se 1 (by rfl) ⟨2122001, by rfl⟩ : syracuseStep 2829335 = 4244003) B4244003
theorem B1886223 : Blo 1885435 1886223 := bstep (se 1 (by rfl) ⟨1414667, by rfl⟩ : syracuseStep 1886223 = 2829335) B2829335
theorem B2829341 : Blo 1885435 2829341 := bbase (se 3 (by rfl) ⟨530501, by rfl⟩ : syracuseStep 2829341 = 1061003) (by norm_num)
theorem B1886227 : Blo 1885435 1886227 := bstep (se 1 (by rfl) ⟨1414670, by rfl⟩ : syracuseStep 1886227 = 2829341) B2829341
theorem B4244021 : Blo 1885435 4244021 := bbase (se 5 (by rfl) ⟨198938, by rfl⟩ : syracuseStep 4244021 = 397877) (by norm_num)
theorem B2829347 : Blo 1885435 2829347 := bstep (se 1 (by rfl) ⟨2122010, by rfl⟩ : syracuseStep 2829347 = 4244021) B4244021
theorem B1886231 : Blo 1885435 1886231 := bstep (se 1 (by rfl) ⟨1414673, by rfl⟩ : syracuseStep 1886231 = 2829347) B2829347
theorem B8057029 : Blo 1885435 8057029 := bbase (se 4 (by rfl) ⟨755346, by rfl⟩ : syracuseStep 8057029 = 1510693) (by norm_num)
theorem B10742705 : Blo 1885435 10742705 := bstep (se 2 (by rfl) ⟨4028514, by rfl⟩ : syracuseStep 10742705 = 8057029) B8057029
theorem B7161803 : Blo 1885435 7161803 := bstep (se 1 (by rfl) ⟨5371352, by rfl⟩ : syracuseStep 7161803 = 10742705) B10742705
theorem B4774535 : Blo 1885435 4774535 := bstep (se 1 (by rfl) ⟨3580901, by rfl⟩ : syracuseStep 4774535 = 7161803) B7161803
theorem B3183023 : Blo 1885435 3183023 := bstep (se 1 (by rfl) ⟨2387267, by rfl⟩ : syracuseStep 3183023 = 4774535) B4774535
theorem B2122015 : Blo 1885435 2122015 := bstep (se 1 (by rfl) ⟨1591511, by rfl⟩ : syracuseStep 2122015 = 3183023) B3183023
theorem B2829353 : Blo 1885435 2829353 := bstep (se 2 (by rfl) ⟨1061007, by rfl⟩ : syracuseStep 2829353 = 2122015) B2122015
theorem B1886235 : Blo 1885435 1886235 := bstep (se 1 (by rfl) ⟨1414676, by rfl⟩ : syracuseStep 1886235 = 2829353) B2829353
theorem B8057045 : Blo 1885435 8057045 := bbase (se 7 (by rfl) ⟨94418, by rfl⟩ : syracuseStep 8057045 = 188837) (by norm_num)
theorem B5371363 : Blo 1885435 5371363 := bstep (se 1 (by rfl) ⟨4028522, by rfl⟩ : syracuseStep 5371363 = 8057045) B8057045
theorem B7161817 : Blo 1885435 7161817 := bstep (se 2 (by rfl) ⟨2685681, by rfl⟩ : syracuseStep 7161817 = 5371363) B5371363
theorem B9549089 : Blo 1885435 9549089 := bstep (se 2 (by rfl) ⟨3580908, by rfl⟩ : syracuseStep 9549089 = 7161817) B7161817
theorem B6366059 : Blo 1885435 6366059 := bstep (se 1 (by rfl) ⟨4774544, by rfl⟩ : syracuseStep 6366059 = 9549089) B9549089
theorem B4244039 : Blo 1885435 4244039 := bstep (se 1 (by rfl) ⟨3183029, by rfl⟩ : syracuseStep 4244039 = 6366059) B6366059
theorem B2829359 : Blo 1885435 2829359 := bstep (se 1 (by rfl) ⟨2122019, by rfl⟩ : syracuseStep 2829359 = 4244039) B4244039
theorem B1886239 : Blo 1885435 1886239 := bstep (se 1 (by rfl) ⟨1414679, by rfl⟩ : syracuseStep 1886239 = 2829359) B2829359
theorem B2829365 : Blo 1885435 2829365 := bbase (se 5 (by rfl) ⟨132626, by rfl⟩ : syracuseStep 2829365 = 265253) (by norm_num)
theorem B1886243 : Blo 1885435 1886243 := bstep (se 1 (by rfl) ⟨1414682, by rfl⟩ : syracuseStep 1886243 = 2829365) B2829365
theorem B4774565 : Blo 1885435 4774565 := bbase (se 4 (by rfl) ⟨447615, by rfl⟩ : syracuseStep 4774565 = 895231) (by norm_num)
theorem B3183043 : Blo 1885435 3183043 := bstep (se 1 (by rfl) ⟨2387282, by rfl⟩ : syracuseStep 3183043 = 4774565) B4774565
theorem B4244057 : Blo 1885435 4244057 := bstep (se 2 (by rfl) ⟨1591521, by rfl⟩ : syracuseStep 4244057 = 3183043) B3183043
theorem B2829371 : Blo 1885435 2829371 := bstep (se 1 (by rfl) ⟨2122028, by rfl⟩ : syracuseStep 2829371 = 4244057) B4244057
theorem B1886247 : Blo 1885435 1886247 := bstep (se 1 (by rfl) ⟨1414685, by rfl⟩ : syracuseStep 1886247 = 2829371) B2829371
theorem B2122033 : Blo 1885435 2122033 := bbase (se 2 (by rfl) ⟨795762, by rfl⟩ : syracuseStep 2122033 = 1591525) (by norm_num)
theorem B2829377 : Blo 1885435 2829377 := bstep (se 2 (by rfl) ⟨1061016, by rfl⟩ : syracuseStep 2829377 = 2122033) B2122033
theorem B1886251 : Blo 1885435 1886251 := bstep (se 1 (by rfl) ⟨1414688, by rfl⟩ : syracuseStep 1886251 = 2829377) B2829377
theorem B4028557 : Blo 1885435 4028557 := bbase (se 3 (by rfl) ⟨755354, by rfl⟩ : syracuseStep 4028557 = 1510709) (by norm_num)
theorem B5371409 : Blo 1885435 5371409 := bstep (se 2 (by rfl) ⟨2014278, by rfl⟩ : syracuseStep 5371409 = 4028557) B4028557
theorem B3580939 : Blo 1885435 3580939 := bstep (se 1 (by rfl) ⟨2685704, by rfl⟩ : syracuseStep 3580939 = 5371409) B5371409
theorem B4774585 : Blo 1885435 4774585 := bstep (se 2 (by rfl) ⟨1790469, by rfl⟩ : syracuseStep 4774585 = 3580939) B3580939
theorem B6366113 : Blo 1885435 6366113 := bstep (se 2 (by rfl) ⟨2387292, by rfl⟩ : syracuseStep 6366113 = 4774585) B4774585
theorem B4244075 : Blo 1885435 4244075 := bstep (se 1 (by rfl) ⟨3183056, by rfl⟩ : syracuseStep 4244075 = 6366113) B6366113
theorem B2829383 : Blo 1885435 2829383 := bstep (se 1 (by rfl) ⟨2122037, by rfl⟩ : syracuseStep 2829383 = 4244075) B4244075
theorem B1886255 : Blo 1885435 1886255 := bstep (se 1 (by rfl) ⟨1414691, by rfl⟩ : syracuseStep 1886255 = 2829383) B2829383
theorem B2829389 : Blo 1885435 2829389 := bbase (se 3 (by rfl) ⟨530510, by rfl⟩ : syracuseStep 2829389 = 1061021) (by norm_num)
theorem B1886259 : Blo 1885435 1886259 := bstep (se 1 (by rfl) ⟨1414694, by rfl⟩ : syracuseStep 1886259 = 2829389) B2829389
theorem B4244093 : Blo 1885435 4244093 := bbase (se 3 (by rfl) ⟨795767, by rfl⟩ : syracuseStep 4244093 = 1591535) (by norm_num)
theorem B2829395 : Blo 1885435 2829395 := bstep (se 1 (by rfl) ⟨2122046, by rfl⟩ : syracuseStep 2829395 = 4244093) B4244093
theorem B1886263 : Blo 1885435 1886263 := bstep (se 1 (by rfl) ⟨1414697, by rfl⟩ : syracuseStep 1886263 = 2829395) B2829395
theorem B3183077 : Blo 1885435 3183077 := bbase (se 4 (by rfl) ⟨298413, by rfl⟩ : syracuseStep 3183077 = 596827) (by norm_num)
theorem B2122051 : Blo 1885435 2122051 := bstep (se 1 (by rfl) ⟨1591538, by rfl⟩ : syracuseStep 2122051 = 3183077) B3183077
theorem B2829401 : Blo 1885435 2829401 := bstep (se 2 (by rfl) ⟨1061025, by rfl⟩ : syracuseStep 2829401 = 2122051) B2122051
theorem B1886267 : Blo 1885435 1886267 := bstep (se 1 (by rfl) ⟨1414700, by rfl⟩ : syracuseStep 1886267 = 2829401) B2829401
theorem B2419885 : Blo 1885435 2419885 := bbase (se 3 (by rfl) ⟨453728, by rfl⟩ : syracuseStep 2419885 = 907457) (by norm_num)
theorem B12906053 : Blo 1885435 12906053 := bstep (se 4 (by rfl) ⟨1209942, by rfl⟩ : syracuseStep 12906053 = 2419885) B2419885
theorem B8604035 : Blo 1885435 8604035 := bstep (se 1 (by rfl) ⟨6453026, by rfl⟩ : syracuseStep 8604035 = 12906053) B12906053
theorem B5736023 : Blo 1885435 5736023 := bstep (se 1 (by rfl) ⟨4302017, by rfl⟩ : syracuseStep 5736023 = 8604035) B8604035
theorem B3824015 : Blo 1885435 3824015 := bstep (se 1 (by rfl) ⟨2868011, by rfl⟩ : syracuseStep 3824015 = 5736023) B5736023
theorem B10197373 : Blo 1885435 10197373 := bstep (se 3 (by rfl) ⟨1912007, by rfl⟩ : syracuseStep 10197373 = 3824015) B3824015
theorem B13596497 : Blo 1885435 13596497 := bstep (se 2 (by rfl) ⟨5098686, by rfl⟩ : syracuseStep 13596497 = 10197373) B10197373
theorem B9064331 : Blo 1885435 9064331 := bstep (se 1 (by rfl) ⟨6798248, by rfl⟩ : syracuseStep 9064331 = 13596497) B13596497
theorem B6042887 : Blo 1885435 6042887 := bstep (se 1 (by rfl) ⟨4532165, by rfl⟩ : syracuseStep 6042887 = 9064331) B9064331
theorem B4028591 : Blo 1885435 4028591 := bstep (se 1 (by rfl) ⟨3021443, by rfl⟩ : syracuseStep 4028591 = 6042887) B6042887
theorem B2685727 : Blo 1885435 2685727 := bstep (se 1 (by rfl) ⟨2014295, by rfl⟩ : syracuseStep 2685727 = 4028591) B4028591
theorem B14323877 : Blo 1885435 14323877 := bstep (se 4 (by rfl) ⟨1342863, by rfl⟩ : syracuseStep 14323877 = 2685727) B2685727
theorem B9549251 : Blo 1885435 9549251 := bstep (se 1 (by rfl) ⟨7161938, by rfl⟩ : syracuseStep 9549251 = 14323877) B14323877
theorem B6366167 : Blo 1885435 6366167 := bstep (se 1 (by rfl) ⟨4774625, by rfl⟩ : syracuseStep 6366167 = 9549251) B9549251
theorem B4244111 : Blo 1885435 4244111 := bstep (se 1 (by rfl) ⟨3183083, by rfl⟩ : syracuseStep 4244111 = 6366167) B6366167
theorem B2829407 : Blo 1885435 2829407 := bstep (se 1 (by rfl) ⟨2122055, by rfl⟩ : syracuseStep 2829407 = 4244111) B4244111
theorem B1886271 : Blo 1885435 1886271 := bstep (se 1 (by rfl) ⟨1414703, by rfl⟩ : syracuseStep 1886271 = 2829407) B2829407
theorem B2829413 : Blo 1885435 2829413 := bbase (se 4 (by rfl) ⟨265257, by rfl⟩ : syracuseStep 2829413 = 530515) (by norm_num)
theorem B1886275 : Blo 1885435 1886275 := bstep (se 1 (by rfl) ⟨1414706, by rfl⟩ : syracuseStep 1886275 = 2829413) B2829413
theorem B2266093 : Blo 1885435 2266093 := bbase (se 3 (by rfl) ⟨424892, by rfl⟩ : syracuseStep 2266093 = 849785) (by norm_num)
theorem B3021457 : Blo 1885435 3021457 := bstep (se 2 (by rfl) ⟨1133046, by rfl⟩ : syracuseStep 3021457 = 2266093) B2266093
theorem B4028609 : Blo 1885435 4028609 := bstep (se 2 (by rfl) ⟨1510728, by rfl⟩ : syracuseStep 4028609 = 3021457) B3021457
theorem B2685739 : Blo 1885435 2685739 := bstep (se 1 (by rfl) ⟨2014304, by rfl⟩ : syracuseStep 2685739 = 4028609) B4028609
theorem B3580985 : Blo 1885435 3580985 := bstep (se 2 (by rfl) ⟨1342869, by rfl⟩ : syracuseStep 3580985 = 2685739) B2685739
theorem B2387323 : Blo 1885435 2387323 := bstep (se 1 (by rfl) ⟨1790492, by rfl⟩ : syracuseStep 2387323 = 3580985) B3580985
theorem B3183097 : Blo 1885435 3183097 := bstep (se 2 (by rfl) ⟨1193661, by rfl⟩ : syracuseStep 3183097 = 2387323) B2387323
theorem B4244129 : Blo 1885435 4244129 := bstep (se 2 (by rfl) ⟨1591548, by rfl⟩ : syracuseStep 4244129 = 3183097) B3183097
theorem B2829419 : Blo 1885435 2829419 := bstep (se 1 (by rfl) ⟨2122064, by rfl⟩ : syracuseStep 2829419 = 4244129) B4244129
theorem B1886279 : Blo 1885435 1886279 := bstep (se 1 (by rfl) ⟨1414709, by rfl⟩ : syracuseStep 1886279 = 2829419) B2829419
theorem B2122069 : Blo 1885435 2122069 := bbase (se 10 (by rfl) ⟨3108, by rfl⟩ : syracuseStep 2122069 = 6217) (by norm_num)
theorem B2829425 : Blo 1885435 2829425 := bstep (se 2 (by rfl) ⟨1061034, by rfl⟩ : syracuseStep 2829425 = 2122069) B2122069
theorem B1886283 : Blo 1885435 1886283 := bstep (se 1 (by rfl) ⟨1414712, by rfl⟩ : syracuseStep 1886283 = 2829425) B2829425
theorem B2387333 : Blo 1885435 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B6366221 : Blo 1885435 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B4244147 : Blo 1885435 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B2829431 : Blo 1885435 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B1886287 : Blo 1885435 1886287 := bstep (se 1 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 1886287 = 2829431) B2829431
theorem B2829437 : Blo 1885435 2829437 := bbase (se 3 (by rfl) ⟨530519, by rfl⟩ : syracuseStep 2829437 = 1061039) (by norm_num)
theorem B1886291 : Blo 1885435 1886291 := bstep (se 1 (by rfl) ⟨1414718, by rfl⟩ : syracuseStep 1886291 = 2829437) B2829437
theorem B4244165 : Blo 1885435 4244165 := bbase (se 4 (by rfl) ⟨397890, by rfl⟩ : syracuseStep 4244165 = 795781) (by norm_num)
theorem B2829443 : Blo 1885435 2829443 := bstep (se 1 (by rfl) ⟨2122082, by rfl⟩ : syracuseStep 2829443 = 4244165) B4244165
theorem B1886295 : Blo 1885435 1886295 := bstep (se 1 (by rfl) ⟨1414721, by rfl⟩ : syracuseStep 1886295 = 2829443) B2829443
theorem B2151041 : Blo 1885435 2151041 := bbase (se 2 (by rfl) ⟨806640, by rfl⟩ : syracuseStep 2151041 = 1613281) (by norm_num)
theorem B5736109 : Blo 1885435 5736109 := bstep (se 3 (by rfl) ⟨1075520, by rfl⟩ : syracuseStep 5736109 = 2151041) B2151041
theorem B7648145 : Blo 1885435 7648145 := bstep (se 2 (by rfl) ⟨2868054, by rfl⟩ : syracuseStep 7648145 = 5736109) B5736109
theorem B5098763 : Blo 1885435 5098763 := bstep (se 1 (by rfl) ⟨3824072, by rfl⟩ : syracuseStep 5098763 = 7648145) B7648145
theorem B3399175 : Blo 1885435 3399175 := bstep (se 1 (by rfl) ⟨2549381, by rfl⟩ : syracuseStep 3399175 = 5098763) B5098763
theorem B18128933 : Blo 1885435 18128933 := bstep (se 4 (by rfl) ⟨1699587, by rfl⟩ : syracuseStep 18128933 = 3399175) B3399175
theorem B12085955 : Blo 1885435 12085955 := bstep (se 1 (by rfl) ⟨9064466, by rfl⟩ : syracuseStep 12085955 = 18128933) B18128933
theorem B8057303 : Blo 1885435 8057303 := bstep (se 1 (by rfl) ⟨6042977, by rfl⟩ : syracuseStep 8057303 = 12085955) B12085955
theorem B5371535 : Blo 1885435 5371535 := bstep (se 1 (by rfl) ⟨4028651, by rfl⟩ : syracuseStep 5371535 = 8057303) B8057303
theorem B3581023 : Blo 1885435 3581023 := bstep (se 1 (by rfl) ⟨2685767, by rfl⟩ : syracuseStep 3581023 = 5371535) B5371535
theorem B4774697 : Blo 1885435 4774697 := bstep (se 2 (by rfl) ⟨1790511, by rfl⟩ : syracuseStep 4774697 = 3581023) B3581023
theorem B3183131 : Blo 1885435 3183131 := bstep (se 1 (by rfl) ⟨2387348, by rfl⟩ : syracuseStep 3183131 = 4774697) B4774697
theorem B2122087 : Blo 1885435 2122087 := bstep (se 1 (by rfl) ⟨1591565, by rfl⟩ : syracuseStep 2122087 = 3183131) B3183131
theorem B2829449 : Blo 1885435 2829449 := bstep (se 2 (by rfl) ⟨1061043, by rfl⟩ : syracuseStep 2829449 = 2122087) B2122087
theorem B1886299 : Blo 1885435 1886299 := bstep (se 1 (by rfl) ⟨1414724, by rfl⟩ : syracuseStep 1886299 = 2829449) B2829449
theorem B9549413 : Blo 1885435 9549413 := bbase (se 4 (by rfl) ⟨895257, by rfl⟩ : syracuseStep 9549413 = 1790515) (by norm_num)
theorem B6366275 : Blo 1885435 6366275 := bstep (se 1 (by rfl) ⟨4774706, by rfl⟩ : syracuseStep 6366275 = 9549413) B9549413
theorem B4244183 : Blo 1885435 4244183 := bstep (se 1 (by rfl) ⟨3183137, by rfl⟩ : syracuseStep 4244183 = 6366275) B6366275
theorem B2829455 : Blo 1885435 2829455 := bstep (se 1 (by rfl) ⟨2122091, by rfl⟩ : syracuseStep 2829455 = 4244183) B4244183
theorem B1886303 : Blo 1885435 1886303 := bstep (se 1 (by rfl) ⟨1414727, by rfl⟩ : syracuseStep 1886303 = 2829455) B2829455
theorem B2829461 : Blo 1885435 2829461 := bbase (se 6 (by rfl) ⟨66315, by rfl⟩ : syracuseStep 2829461 = 132631) (by norm_num)
theorem B1886307 : Blo 1885435 1886307 := bstep (se 1 (by rfl) ⟨1414730, by rfl⟩ : syracuseStep 1886307 = 2829461) B2829461
theorem B10197589 : Blo 1885435 10197589 := bbase (se 8 (by rfl) ⟨59751, by rfl⟩ : syracuseStep 10197589 = 119503) (by norm_num)
theorem B13596785 : Blo 1885435 13596785 := bstep (se 2 (by rfl) ⟨5098794, by rfl⟩ : syracuseStep 13596785 = 10197589) B10197589
theorem B9064523 : Blo 1885435 9064523 := bstep (se 1 (by rfl) ⟨6798392, by rfl⟩ : syracuseStep 9064523 = 13596785) B13596785
theorem B6043015 : Blo 1885435 6043015 := bstep (se 1 (by rfl) ⟨4532261, by rfl⟩ : syracuseStep 6043015 = 9064523) B9064523
theorem B8057353 : Blo 1885435 8057353 := bstep (se 2 (by rfl) ⟨3021507, by rfl⟩ : syracuseStep 8057353 = 6043015) B6043015
theorem B10743137 : Blo 1885435 10743137 := bstep (se 2 (by rfl) ⟨4028676, by rfl⟩ : syracuseStep 10743137 = 8057353) B8057353
theorem B7162091 : Blo 1885435 7162091 := bstep (se 1 (by rfl) ⟨5371568, by rfl⟩ : syracuseStep 7162091 = 10743137) B10743137
theorem B4774727 : Blo 1885435 4774727 := bstep (se 1 (by rfl) ⟨3581045, by rfl⟩ : syracuseStep 4774727 = 7162091) B7162091
theorem B3183151 : Blo 1885435 3183151 := bstep (se 1 (by rfl) ⟨2387363, by rfl⟩ : syracuseStep 3183151 = 4774727) B4774727
theorem B4244201 : Blo 1885435 4244201 := bstep (se 2 (by rfl) ⟨1591575, by rfl⟩ : syracuseStep 4244201 = 3183151) B3183151
theorem B2829467 : Blo 1885435 2829467 := bstep (se 1 (by rfl) ⟨2122100, by rfl⟩ : syracuseStep 2829467 = 4244201) B4244201
theorem B1886311 : Blo 1885435 1886311 := bstep (se 1 (by rfl) ⟨1414733, by rfl⟩ : syracuseStep 1886311 = 2829467) B2829467
theorem B2122105 : Blo 1885435 2122105 := bbase (se 2 (by rfl) ⟨795789, by rfl⟩ : syracuseStep 2122105 = 1591579) (by norm_num)
theorem B2829473 : Blo 1885435 2829473 := bstep (se 2 (by rfl) ⟨1061052, by rfl⟩ : syracuseStep 2829473 = 2122105) B2122105
theorem B1886315 : Blo 1885435 1886315 := bstep (se 1 (by rfl) ⟨1414736, by rfl⟩ : syracuseStep 1886315 = 2829473) B2829473
theorem B6798421 : Blo 1885435 6798421 := bbase (se 8 (by rfl) ⟨39834, by rfl⟩ : syracuseStep 6798421 = 79669) (by norm_num)
theorem B9064561 : Blo 1885435 9064561 := bstep (se 2 (by rfl) ⟨3399210, by rfl⟩ : syracuseStep 9064561 = 6798421) B6798421
theorem B12086081 : Blo 1885435 12086081 := bstep (se 2 (by rfl) ⟨4532280, by rfl⟩ : syracuseStep 12086081 = 9064561) B9064561
theorem B8057387 : Blo 1885435 8057387 := bstep (se 1 (by rfl) ⟨6043040, by rfl⟩ : syracuseStep 8057387 = 12086081) B12086081
theorem B5371591 : Blo 1885435 5371591 := bstep (se 1 (by rfl) ⟨4028693, by rfl⟩ : syracuseStep 5371591 = 8057387) B8057387
theorem B7162121 : Blo 1885435 7162121 := bstep (se 2 (by rfl) ⟨2685795, by rfl⟩ : syracuseStep 7162121 = 5371591) B5371591
theorem B4774747 : Blo 1885435 4774747 := bstep (se 1 (by rfl) ⟨3581060, by rfl⟩ : syracuseStep 4774747 = 7162121) B7162121
theorem B6366329 : Blo 1885435 6366329 := bstep (se 2 (by rfl) ⟨2387373, by rfl⟩ : syracuseStep 6366329 = 4774747) B4774747
theorem B4244219 : Blo 1885435 4244219 := bstep (se 1 (by rfl) ⟨3183164, by rfl⟩ : syracuseStep 4244219 = 6366329) B6366329
theorem B2829479 : Blo 1885435 2829479 := bstep (se 1 (by rfl) ⟨2122109, by rfl⟩ : syracuseStep 2829479 = 4244219) B4244219
theorem B1886319 : Blo 1885435 1886319 := bstep (se 1 (by rfl) ⟨1414739, by rfl⟩ : syracuseStep 1886319 = 2829479) B2829479
theorem B2829485 : Blo 1885435 2829485 := bbase (se 3 (by rfl) ⟨530528, by rfl⟩ : syracuseStep 2829485 = 1061057) (by norm_num)
theorem B1886323 : Blo 1885435 1886323 := bstep (se 1 (by rfl) ⟨1414742, by rfl⟩ : syracuseStep 1886323 = 2829485) B2829485
theorem B4244237 : Blo 1885435 4244237 := bbase (se 3 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 4244237 = 1591589) (by norm_num)
theorem B2829491 : Blo 1885435 2829491 := bstep (se 1 (by rfl) ⟨2122118, by rfl⟩ : syracuseStep 2829491 = 4244237) B4244237
theorem B1886327 : Blo 1885435 1886327 := bstep (se 1 (by rfl) ⟨1414745, by rfl⟩ : syracuseStep 1886327 = 2829491) B2829491
theorem B2387389 : Blo 1885435 2387389 := bbase (se 3 (by rfl) ⟨447635, by rfl⟩ : syracuseStep 2387389 = 895271) (by norm_num)
theorem B3183185 : Blo 1885435 3183185 := bstep (se 2 (by rfl) ⟨1193694, by rfl⟩ : syracuseStep 3183185 = 2387389) B2387389
theorem B2122123 : Blo 1885435 2122123 := bstep (se 1 (by rfl) ⟨1591592, by rfl⟩ : syracuseStep 2122123 = 3183185) B3183185
theorem B2829497 : Blo 1885435 2829497 := bstep (se 2 (by rfl) ⟨1061061, by rfl⟩ : syracuseStep 2829497 = 2122123) B2122123
theorem B1886331 : Blo 1885435 1886331 := bstep (se 1 (by rfl) ⟨1414748, by rfl⟩ : syracuseStep 1886331 = 2829497) B2829497
theorem B4360861 : Blo 1885435 4360861 := bbase (se 3 (by rfl) ⟨817661, by rfl⟩ : syracuseStep 4360861 = 1635323) (by norm_num)
theorem B23257925 : Blo 1885435 23257925 := bstep (se 4 (by rfl) ⟨2180430, by rfl⟩ : syracuseStep 23257925 = 4360861) B4360861
theorem B15505283 : Blo 1885435 15505283 := bstep (se 1 (by rfl) ⟨11628962, by rfl⟩ : syracuseStep 15505283 = 23257925) B23257925
theorem B41347421 : Blo 1885435 41347421 := bstep (se 3 (by rfl) ⟨7752641, by rfl⟩ : syracuseStep 41347421 = 15505283) B15505283
theorem B27564947 : Blo 1885435 27564947 := bstep (se 1 (by rfl) ⟨20673710, by rfl⟩ : syracuseStep 27564947 = 41347421) B41347421
theorem B18376631 : Blo 1885435 18376631 := bstep (se 1 (by rfl) ⟨13782473, by rfl⟩ : syracuseStep 18376631 = 27564947) B27564947
theorem B12251087 : Blo 1885435 12251087 := bstep (se 1 (by rfl) ⟨9188315, by rfl⟩ : syracuseStep 12251087 = 18376631) B18376631
theorem B8167391 : Blo 1885435 8167391 := bstep (se 1 (by rfl) ⟨6125543, by rfl⟩ : syracuseStep 8167391 = 12251087) B12251087
theorem B5444927 : Blo 1885435 5444927 := bstep (se 1 (by rfl) ⟨4083695, by rfl⟩ : syracuseStep 5444927 = 8167391) B8167391
theorem B3629951 : Blo 1885435 3629951 := bstep (se 1 (by rfl) ⟨2722463, by rfl⟩ : syracuseStep 3629951 = 5444927) B5444927
theorem B2419967 : Blo 1885435 2419967 := bstep (se 1 (by rfl) ⟨1814975, by rfl⟩ : syracuseStep 2419967 = 3629951) B3629951
theorem B6453245 : Blo 1885435 6453245 := bstep (se 3 (by rfl) ⟨1209983, by rfl⟩ : syracuseStep 6453245 = 2419967) B2419967
theorem B4302163 : Blo 1885435 4302163 := bstep (se 1 (by rfl) ⟨3226622, by rfl⟩ : syracuseStep 4302163 = 6453245) B6453245
theorem B5736217 : Blo 1885435 5736217 := bstep (se 2 (by rfl) ⟨2151081, by rfl⟩ : syracuseStep 5736217 = 4302163) B4302163
theorem B7648289 : Blo 1885435 7648289 := bstep (se 2 (by rfl) ⟨2868108, by rfl⟩ : syracuseStep 7648289 = 5736217) B5736217
theorem B5098859 : Blo 1885435 5098859 := bstep (se 1 (by rfl) ⟨3824144, by rfl⟩ : syracuseStep 5098859 = 7648289) B7648289
theorem B3399239 : Blo 1885435 3399239 := bstep (se 1 (by rfl) ⟨2549429, by rfl⟩ : syracuseStep 3399239 = 5098859) B5098859
theorem B9064637 : Blo 1885435 9064637 := bstep (se 3 (by rfl) ⟨1699619, by rfl⟩ : syracuseStep 9064637 = 3399239) B3399239
theorem B6043091 : Blo 1885435 6043091 := bstep (se 1 (by rfl) ⟨4532318, by rfl⟩ : syracuseStep 6043091 = 9064637) B9064637
theorem B16114909 : Blo 1885435 16114909 := bstep (se 3 (by rfl) ⟨3021545, by rfl⟩ : syracuseStep 16114909 = 6043091) B6043091
theorem B21486545 : Blo 1885435 21486545 := bstep (se 2 (by rfl) ⟨8057454, by rfl⟩ : syracuseStep 21486545 = 16114909) B16114909
theorem B14324363 : Blo 1885435 14324363 := bstep (se 1 (by rfl) ⟨10743272, by rfl⟩ : syracuseStep 14324363 = 21486545) B21486545
theorem B9549575 : Blo 1885435 9549575 := bstep (se 1 (by rfl) ⟨7162181, by rfl⟩ : syracuseStep 9549575 = 14324363) B14324363
theorem B6366383 : Blo 1885435 6366383 := bstep (se 1 (by rfl) ⟨4774787, by rfl⟩ : syracuseStep 6366383 = 9549575) B9549575
theorem B4244255 : Blo 1885435 4244255 := bstep (se 1 (by rfl) ⟨3183191, by rfl⟩ : syracuseStep 4244255 = 6366383) B6366383
theorem B2829503 : Blo 1885435 2829503 := bstep (se 1 (by rfl) ⟨2122127, by rfl⟩ : syracuseStep 2829503 = 4244255) B4244255
theorem B1886335 : Blo 1885435 1886335 := bstep (se 1 (by rfl) ⟨1414751, by rfl⟩ : syracuseStep 1886335 = 2829503) B2829503
theorem B2829509 : Blo 1885435 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B1886339 : Blo 1885435 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B3183205 : Blo 1885435 3183205 := bbase (se 4 (by rfl) ⟨298425, by rfl⟩ : syracuseStep 3183205 = 596851) (by norm_num)
theorem B4244273 : Blo 1885435 4244273 := bstep (se 2 (by rfl) ⟨1591602, by rfl⟩ : syracuseStep 4244273 = 3183205) B3183205
theorem B2829515 : Blo 1885435 2829515 := bstep (se 1 (by rfl) ⟨2122136, by rfl⟩ : syracuseStep 2829515 = 4244273) B4244273
theorem B1886343 : Blo 1885435 1886343 := bstep (se 1 (by rfl) ⟨1414757, by rfl⟩ : syracuseStep 1886343 = 2829515) B2829515
theorem B2122141 : Blo 1885435 2122141 := bbase (se 3 (by rfl) ⟨397901, by rfl⟩ : syracuseStep 2122141 = 795803) (by norm_num)
theorem B2829521 : Blo 1885435 2829521 := bstep (se 2 (by rfl) ⟨1061070, by rfl⟩ : syracuseStep 2829521 = 2122141) B2122141
theorem B1886347 : Blo 1885435 1886347 := bstep (se 1 (by rfl) ⟨1414760, by rfl⟩ : syracuseStep 1886347 = 2829521) B2829521
theorem B6366437 : Blo 1885435 6366437 := bbase (se 4 (by rfl) ⟨596853, by rfl⟩ : syracuseStep 6366437 = 1193707) (by norm_num)
theorem B4244291 : Blo 1885435 4244291 := bstep (se 1 (by rfl) ⟨3183218, by rfl⟩ : syracuseStep 4244291 = 6366437) B6366437
theorem B2829527 : Blo 1885435 2829527 := bstep (se 1 (by rfl) ⟨2122145, by rfl⟩ : syracuseStep 2829527 = 4244291) B4244291
theorem B1886351 : Blo 1885435 1886351 := bstep (se 1 (by rfl) ⟨1414763, by rfl⟩ : syracuseStep 1886351 = 2829527) B2829527
theorem B2829533 : Blo 1885435 2829533 := bbase (se 3 (by rfl) ⟨530537, by rfl⟩ : syracuseStep 2829533 = 1061075) (by norm_num)
theorem B1886355 : Blo 1885435 1886355 := bstep (se 1 (by rfl) ⟨1414766, by rfl⟩ : syracuseStep 1886355 = 2829533) B2829533
theorem B4244309 : Blo 1885435 4244309 := bbase (se 9 (by rfl) ⟨12434, by rfl⟩ : syracuseStep 4244309 = 24869) (by norm_num)
theorem B2829539 : Blo 1885435 2829539 := bstep (se 1 (by rfl) ⟨2122154, by rfl⟩ : syracuseStep 2829539 = 4244309) B4244309
theorem B1886359 : Blo 1885435 1886359 := bstep (se 1 (by rfl) ⟨1414769, by rfl⟩ : syracuseStep 1886359 = 2829539) B2829539
theorem B5371717 : Blo 1885435 5371717 := bbase (se 4 (by rfl) ⟨503598, by rfl⟩ : syracuseStep 5371717 = 1007197) (by norm_num)
theorem B7162289 : Blo 1885435 7162289 := bstep (se 2 (by rfl) ⟨2685858, by rfl⟩ : syracuseStep 7162289 = 5371717) B5371717
theorem B4774859 : Blo 1885435 4774859 := bstep (se 1 (by rfl) ⟨3581144, by rfl⟩ : syracuseStep 4774859 = 7162289) B7162289
theorem B3183239 : Blo 1885435 3183239 := bstep (se 1 (by rfl) ⟨2387429, by rfl⟩ : syracuseStep 3183239 = 4774859) B4774859
theorem B2122159 : Blo 1885435 2122159 := bstep (se 1 (by rfl) ⟨1591619, by rfl⟩ : syracuseStep 2122159 = 3183239) B3183239
theorem B2829545 : Blo 1885435 2829545 := bstep (se 2 (by rfl) ⟨1061079, by rfl⟩ : syracuseStep 2829545 = 2122159) B2122159
theorem B1886363 : Blo 1885435 1886363 := bstep (se 1 (by rfl) ⟨1414772, by rfl⟩ : syracuseStep 1886363 = 2829545) B2829545
theorem B27565397 : Blo 1885435 27565397 := bbase (se 11 (by rfl) ⟨20189, by rfl⟩ : syracuseStep 27565397 = 40379) (by norm_num)
theorem B18376931 : Blo 1885435 18376931 := bstep (se 1 (by rfl) ⟨13782698, by rfl⟩ : syracuseStep 18376931 = 27565397) B27565397
theorem B12251287 : Blo 1885435 12251287 := bstep (se 1 (by rfl) ⟨9188465, by rfl⟩ : syracuseStep 12251287 = 18376931) B18376931
theorem B16335049 : Blo 1885435 16335049 := bstep (se 2 (by rfl) ⟨6125643, by rfl⟩ : syracuseStep 16335049 = 12251287) B12251287
theorem B21780065 : Blo 1885435 21780065 := bstep (se 2 (by rfl) ⟨8167524, by rfl⟩ : syracuseStep 21780065 = 16335049) B16335049
theorem B14520043 : Blo 1885435 14520043 := bstep (se 1 (by rfl) ⟨10890032, by rfl⟩ : syracuseStep 14520043 = 21780065) B21780065
theorem B19360057 : Blo 1885435 19360057 := bstep (se 2 (by rfl) ⟨7260021, by rfl⟩ : syracuseStep 19360057 = 14520043) B14520043
theorem B25813409 : Blo 1885435 25813409 := bstep (se 2 (by rfl) ⟨9680028, by rfl⟩ : syracuseStep 25813409 = 19360057) B19360057
theorem B68835757 : Blo 1885435 68835757 := bstep (se 3 (by rfl) ⟨12906704, by rfl⟩ : syracuseStep 68835757 = 25813409) B25813409
theorem B91781009 : Blo 1885435 91781009 := bstep (se 2 (by rfl) ⟨34417878, by rfl⟩ : syracuseStep 91781009 = 68835757) B68835757
theorem B61187339 : Blo 1885435 61187339 := bstep (se 1 (by rfl) ⟨45890504, by rfl⟩ : syracuseStep 61187339 = 91781009) B91781009
theorem B40791559 : Blo 1885435 40791559 := bstep (se 1 (by rfl) ⟨30593669, by rfl⟩ : syracuseStep 40791559 = 61187339) B61187339
theorem B54388745 : Blo 1885435 54388745 := bstep (se 2 (by rfl) ⟨20395779, by rfl⟩ : syracuseStep 54388745 = 40791559) B40791559
theorem B36259163 : Blo 1885435 36259163 := bstep (se 1 (by rfl) ⟨27194372, by rfl⟩ : syracuseStep 36259163 = 54388745) B54388745
theorem B24172775 : Blo 1885435 24172775 := bstep (se 1 (by rfl) ⟨18129581, by rfl⟩ : syracuseStep 24172775 = 36259163) B36259163
theorem B16115183 : Blo 1885435 16115183 := bstep (se 1 (by rfl) ⟨12086387, by rfl⟩ : syracuseStep 16115183 = 24172775) B24172775
theorem B10743455 : Blo 1885435 10743455 := bstep (se 1 (by rfl) ⟨8057591, by rfl⟩ : syracuseStep 10743455 = 16115183) B16115183
theorem B7162303 : Blo 1885435 7162303 := bstep (se 1 (by rfl) ⟨5371727, by rfl⟩ : syracuseStep 7162303 = 10743455) B10743455
theorem B9549737 : Blo 1885435 9549737 := bstep (se 2 (by rfl) ⟨3581151, by rfl⟩ : syracuseStep 9549737 = 7162303) B7162303
theorem B6366491 : Blo 1885435 6366491 := bstep (se 1 (by rfl) ⟨4774868, by rfl⟩ : syracuseStep 6366491 = 9549737) B9549737
theorem B4244327 : Blo 1885435 4244327 := bstep (se 1 (by rfl) ⟨3183245, by rfl⟩ : syracuseStep 4244327 = 6366491) B6366491
theorem B2829551 : Blo 1885435 2829551 := bstep (se 1 (by rfl) ⟨2122163, by rfl⟩ : syracuseStep 2829551 = 4244327) B4244327
theorem B1886367 : Blo 1885435 1886367 := bstep (se 1 (by rfl) ⟨1414775, by rfl⟩ : syracuseStep 1886367 = 2829551) B2829551
theorem B2829557 : Blo 1885435 2829557 := bbase (se 5 (by rfl) ⟨132635, by rfl⟩ : syracuseStep 2829557 = 265271) (by norm_num)
theorem B1886371 : Blo 1885435 1886371 := bstep (se 1 (by rfl) ⟨1414778, by rfl⟩ : syracuseStep 1886371 = 2829557) B2829557
theorem B103254101 : Blo 1885435 103254101 := bbase (se 8 (by rfl) ⟨605004, by rfl⟩ : syracuseStep 103254101 = 1210009) (by norm_num)
theorem B68836067 : Blo 1885435 68836067 := bstep (se 1 (by rfl) ⟨51627050, by rfl⟩ : syracuseStep 68836067 = 103254101) B103254101
theorem B45890711 : Blo 1885435 45890711 := bstep (se 1 (by rfl) ⟨34418033, by rfl⟩ : syracuseStep 45890711 = 68836067) B68836067
theorem B30593807 : Blo 1885435 30593807 := bstep (se 1 (by rfl) ⟨22945355, by rfl⟩ : syracuseStep 30593807 = 45890711) B45890711
theorem B20395871 : Blo 1885435 20395871 := bstep (se 1 (by rfl) ⟨15296903, by rfl⟩ : syracuseStep 20395871 = 30593807) B30593807
theorem B13597247 : Blo 1885435 13597247 := bstep (se 1 (by rfl) ⟨10197935, by rfl⟩ : syracuseStep 13597247 = 20395871) B20395871
theorem B9064831 : Blo 1885435 9064831 := bstep (se 1 (by rfl) ⟨6798623, by rfl⟩ : syracuseStep 9064831 = 13597247) B13597247
theorem B12086441 : Blo 1885435 12086441 := bstep (se 2 (by rfl) ⟨4532415, by rfl⟩ : syracuseStep 12086441 = 9064831) B9064831
theorem B8057627 : Blo 1885435 8057627 := bstep (se 1 (by rfl) ⟨6043220, by rfl⟩ : syracuseStep 8057627 = 12086441) B12086441
theorem B5371751 : Blo 1885435 5371751 := bstep (se 1 (by rfl) ⟨4028813, by rfl⟩ : syracuseStep 5371751 = 8057627) B8057627
theorem B3581167 : Blo 1885435 3581167 := bstep (se 1 (by rfl) ⟨2685875, by rfl⟩ : syracuseStep 3581167 = 5371751) B5371751
theorem B4774889 : Blo 1885435 4774889 := bstep (se 2 (by rfl) ⟨1790583, by rfl⟩ : syracuseStep 4774889 = 3581167) B3581167
theorem B3183259 : Blo 1885435 3183259 := bstep (se 1 (by rfl) ⟨2387444, by rfl⟩ : syracuseStep 3183259 = 4774889) B4774889
theorem B4244345 : Blo 1885435 4244345 := bstep (se 2 (by rfl) ⟨1591629, by rfl⟩ : syracuseStep 4244345 = 3183259) B3183259
theorem B2829563 : Blo 1885435 2829563 := bstep (se 1 (by rfl) ⟨2122172, by rfl⟩ : syracuseStep 2829563 = 4244345) B4244345
theorem B1886375 : Blo 1885435 1886375 := bstep (se 1 (by rfl) ⟨1414781, by rfl⟩ : syracuseStep 1886375 = 2829563) B2829563
theorem B2122177 : Blo 1885435 2122177 := bbase (se 2 (by rfl) ⟨795816, by rfl⟩ : syracuseStep 2122177 = 1591633) (by norm_num)
theorem B2829569 : Blo 1885435 2829569 := bstep (se 2 (by rfl) ⟨1061088, by rfl⟩ : syracuseStep 2829569 = 2122177) B2122177
theorem B1886379 : Blo 1885435 1886379 := bstep (se 1 (by rfl) ⟨1414784, by rfl⟩ : syracuseStep 1886379 = 2829569) B2829569
theorem B4774909 : Blo 1885435 4774909 := bbase (se 3 (by rfl) ⟨895295, by rfl⟩ : syracuseStep 4774909 = 1790591) (by norm_num)
theorem B6366545 : Blo 1885435 6366545 := bstep (se 2 (by rfl) ⟨2387454, by rfl⟩ : syracuseStep 6366545 = 4774909) B4774909
theorem B4244363 : Blo 1885435 4244363 := bstep (se 1 (by rfl) ⟨3183272, by rfl⟩ : syracuseStep 4244363 = 6366545) B6366545
theorem B2829575 : Blo 1885435 2829575 := bstep (se 1 (by rfl) ⟨2122181, by rfl⟩ : syracuseStep 2829575 = 4244363) B4244363
theorem B1886383 : Blo 1885435 1886383 := bstep (se 1 (by rfl) ⟨1414787, by rfl⟩ : syracuseStep 1886383 = 2829575) B2829575
theorem B2829581 : Blo 1885435 2829581 := bbase (se 3 (by rfl) ⟨530546, by rfl⟩ : syracuseStep 2829581 = 1061093) (by norm_num)
theorem B1886387 : Blo 1885435 1886387 := bstep (se 1 (by rfl) ⟨1414790, by rfl⟩ : syracuseStep 1886387 = 2829581) B2829581
theorem B4244381 : Blo 1885435 4244381 := bbase (se 3 (by rfl) ⟨795821, by rfl⟩ : syracuseStep 4244381 = 1591643) (by norm_num)
theorem B2829587 : Blo 1885435 2829587 := bstep (se 1 (by rfl) ⟨2122190, by rfl⟩ : syracuseStep 2829587 = 4244381) B4244381
theorem B1886391 : Blo 1885435 1886391 := bstep (se 1 (by rfl) ⟨1414793, by rfl⟩ : syracuseStep 1886391 = 2829587) B2829587
theorem B3183293 : Blo 1885435 3183293 := bbase (se 3 (by rfl) ⟨596867, by rfl⟩ : syracuseStep 3183293 = 1193735) (by norm_num)
theorem B2122195 : Blo 1885435 2122195 := bstep (se 1 (by rfl) ⟨1591646, by rfl⟩ : syracuseStep 2122195 = 3183293) B3183293
theorem B2829593 : Blo 1885435 2829593 := bstep (se 2 (by rfl) ⟨1061097, by rfl⟩ : syracuseStep 2829593 = 2122195) B2122195
theorem B1886395 : Blo 1885435 1886395 := bstep (se 1 (by rfl) ⟨1414796, by rfl⟩ : syracuseStep 1886395 = 2829593) B2829593
theorem B10743637 : Blo 1885435 10743637 := bbase (se 9 (by rfl) ⟨31475, by rfl⟩ : syracuseStep 10743637 = 62951) (by norm_num)
theorem B14324849 : Blo 1885435 14324849 := bstep (se 2 (by rfl) ⟨5371818, by rfl⟩ : syracuseStep 14324849 = 10743637) B10743637
theorem B9549899 : Blo 1885435 9549899 := bstep (se 1 (by rfl) ⟨7162424, by rfl⟩ : syracuseStep 9549899 = 14324849) B14324849
theorem B6366599 : Blo 1885435 6366599 := bstep (se 1 (by rfl) ⟨4774949, by rfl⟩ : syracuseStep 6366599 = 9549899) B9549899
theorem B4244399 : Blo 1885435 4244399 := bstep (se 1 (by rfl) ⟨3183299, by rfl⟩ : syracuseStep 4244399 = 6366599) B6366599
theorem B2829599 : Blo 1885435 2829599 := bstep (se 1 (by rfl) ⟨2122199, by rfl⟩ : syracuseStep 2829599 = 4244399) B4244399
theorem B1886399 : Blo 1885435 1886399 := bstep (se 1 (by rfl) ⟨1414799, by rfl⟩ : syracuseStep 1886399 = 2829599) B2829599
theorem B2829605 : Blo 1885435 2829605 := bbase (se 4 (by rfl) ⟨265275, by rfl⟩ : syracuseStep 2829605 = 530551) (by norm_num)
theorem B1886403 : Blo 1885435 1886403 := bstep (se 1 (by rfl) ⟨1414802, by rfl⟩ : syracuseStep 1886403 = 2829605) B2829605
theorem B2387485 : Blo 1885435 2387485 := bbase (se 3 (by rfl) ⟨447653, by rfl⟩ : syracuseStep 2387485 = 895307) (by norm_num)
theorem B3183313 : Blo 1885435 3183313 := bstep (se 2 (by rfl) ⟨1193742, by rfl⟩ : syracuseStep 3183313 = 2387485) B2387485
theorem B4244417 : Blo 1885435 4244417 := bstep (se 2 (by rfl) ⟨1591656, by rfl⟩ : syracuseStep 4244417 = 3183313) B3183313
theorem B2829611 : Blo 1885435 2829611 := bstep (se 1 (by rfl) ⟨2122208, by rfl⟩ : syracuseStep 2829611 = 4244417) B4244417
theorem B1886407 : Blo 1885435 1886407 := bstep (se 1 (by rfl) ⟨1414805, by rfl⟩ : syracuseStep 1886407 = 2829611) B2829611
theorem B2122213 : Blo 1885435 2122213 := bbase (se 4 (by rfl) ⟨198957, by rfl⟩ : syracuseStep 2122213 = 397915) (by norm_num)
theorem B2829617 : Blo 1885435 2829617 := bstep (se 2 (by rfl) ⟨1061106, by rfl⟩ : syracuseStep 2829617 = 2122213) B2122213
theorem B1886411 : Blo 1885435 1886411 := bstep (se 1 (by rfl) ⟨1414808, by rfl⟩ : syracuseStep 1886411 = 2829617) B2829617
theorem B6043349 : Blo 1885435 6043349 := bbase (se 7 (by rfl) ⟨70820, by rfl⟩ : syracuseStep 6043349 = 141641) (by norm_num)
theorem B4028899 : Blo 1885435 4028899 := bstep (se 1 (by rfl) ⟨3021674, by rfl⟩ : syracuseStep 4028899 = 6043349) B6043349
theorem B5371865 : Blo 1885435 5371865 := bstep (se 2 (by rfl) ⟨2014449, by rfl⟩ : syracuseStep 5371865 = 4028899) B4028899
theorem B3581243 : Blo 1885435 3581243 := bstep (se 1 (by rfl) ⟨2685932, by rfl⟩ : syracuseStep 3581243 = 5371865) B5371865
theorem B2387495 : Blo 1885435 2387495 := bstep (se 1 (by rfl) ⟨1790621, by rfl⟩ : syracuseStep 2387495 = 3581243) B3581243
theorem B6366653 : Blo 1885435 6366653 := bstep (se 3 (by rfl) ⟨1193747, by rfl⟩ : syracuseStep 6366653 = 2387495) B2387495
theorem B4244435 : Blo 1885435 4244435 := bstep (se 1 (by rfl) ⟨3183326, by rfl⟩ : syracuseStep 4244435 = 6366653) B6366653
theorem B2829623 : Blo 1885435 2829623 := bstep (se 1 (by rfl) ⟨2122217, by rfl⟩ : syracuseStep 2829623 = 4244435) B4244435
theorem B1886415 : Blo 1885435 1886415 := bstep (se 1 (by rfl) ⟨1414811, by rfl⟩ : syracuseStep 1886415 = 2829623) B2829623
theorem B2829629 : Blo 1885435 2829629 := bbase (se 3 (by rfl) ⟨530555, by rfl⟩ : syracuseStep 2829629 = 1061111) (by norm_num)
theorem B1886419 : Blo 1885435 1886419 := bstep (se 1 (by rfl) ⟨1414814, by rfl⟩ : syracuseStep 1886419 = 2829629) B2829629
theorem B4244453 : Blo 1885435 4244453 := bbase (se 4 (by rfl) ⟨397917, by rfl⟩ : syracuseStep 4244453 = 795835) (by norm_num)
theorem B2829635 : Blo 1885435 2829635 := bstep (se 1 (by rfl) ⟨2122226, by rfl⟩ : syracuseStep 2829635 = 4244453) B4244453
theorem B1886423 : Blo 1885435 1886423 := bstep (se 1 (by rfl) ⟨1414817, by rfl⟩ : syracuseStep 1886423 = 2829635) B2829635
theorem B4775021 : Blo 1885435 4775021 := bbase (se 3 (by rfl) ⟨895316, by rfl⟩ : syracuseStep 4775021 = 1790633) (by norm_num)
theorem B3183347 : Blo 1885435 3183347 := bstep (se 1 (by rfl) ⟨2387510, by rfl⟩ : syracuseStep 3183347 = 4775021) B4775021
theorem B2122231 : Blo 1885435 2122231 := bstep (se 1 (by rfl) ⟨1591673, by rfl⟩ : syracuseStep 2122231 = 3183347) B3183347
theorem B2829641 : Blo 1885435 2829641 := bstep (se 2 (by rfl) ⟨1061115, by rfl⟩ : syracuseStep 2829641 = 2122231) B2122231
theorem B1886427 : Blo 1885435 1886427 := bstep (se 1 (by rfl) ⟨1414820, by rfl⟩ : syracuseStep 1886427 = 2829641) B2829641
theorem B4028933 : Blo 1885435 4028933 := bbase (se 4 (by rfl) ⟨377712, by rfl⟩ : syracuseStep 4028933 = 755425) (by norm_num)
theorem B2685955 : Blo 1885435 2685955 := bstep (se 1 (by rfl) ⟨2014466, by rfl⟩ : syracuseStep 2685955 = 4028933) B4028933
theorem B3581273 : Blo 1885435 3581273 := bstep (se 2 (by rfl) ⟨1342977, by rfl⟩ : syracuseStep 3581273 = 2685955) B2685955
theorem B9550061 : Blo 1885435 9550061 := bstep (se 3 (by rfl) ⟨1790636, by rfl⟩ : syracuseStep 9550061 = 3581273) B3581273
theorem B6366707 : Blo 1885435 6366707 := bstep (se 1 (by rfl) ⟨4775030, by rfl⟩ : syracuseStep 6366707 = 9550061) B9550061
theorem B4244471 : Blo 1885435 4244471 := bstep (se 1 (by rfl) ⟨3183353, by rfl⟩ : syracuseStep 4244471 = 6366707) B6366707
theorem B2829647 : Blo 1885435 2829647 := bstep (se 1 (by rfl) ⟨2122235, by rfl⟩ : syracuseStep 2829647 = 4244471) B4244471
theorem B1886431 : Blo 1885435 1886431 := bstep (se 1 (by rfl) ⟨1414823, by rfl⟩ : syracuseStep 1886431 = 2829647) B2829647
theorem B2829653 : Blo 1885435 2829653 := bbase (se 11 (by rfl) ⟨2072, by rfl⟩ : syracuseStep 2829653 = 4145) (by norm_num)
theorem B1886435 : Blo 1885435 1886435 := bstep (se 1 (by rfl) ⟨1414826, by rfl⟩ : syracuseStep 1886435 = 2829653) B2829653
theorem B2266285 : Blo 1885435 2266285 := bbase (se 3 (by rfl) ⟨424928, by rfl⟩ : syracuseStep 2266285 = 849857) (by norm_num)
theorem B3021713 : Blo 1885435 3021713 := bstep (se 2 (by rfl) ⟨1133142, by rfl⟩ : syracuseStep 3021713 = 2266285) B2266285
theorem B2014475 : Blo 1885435 2014475 := bstep (se 1 (by rfl) ⟨1510856, by rfl⟩ : syracuseStep 2014475 = 3021713) B3021713
theorem B5371933 : Blo 1885435 5371933 := bstep (se 3 (by rfl) ⟨1007237, by rfl⟩ : syracuseStep 5371933 = 2014475) B2014475
theorem B7162577 : Blo 1885435 7162577 := bstep (se 2 (by rfl) ⟨2685966, by rfl⟩ : syracuseStep 7162577 = 5371933) B5371933
theorem B4775051 : Blo 1885435 4775051 := bstep (se 1 (by rfl) ⟨3581288, by rfl⟩ : syracuseStep 4775051 = 7162577) B7162577
theorem B3183367 : Blo 1885435 3183367 := bstep (se 1 (by rfl) ⟨2387525, by rfl⟩ : syracuseStep 3183367 = 4775051) B4775051
theorem B4244489 : Blo 1885435 4244489 := bstep (se 2 (by rfl) ⟨1591683, by rfl⟩ : syracuseStep 4244489 = 3183367) B3183367
theorem B2829659 : Blo 1885435 2829659 := bstep (se 1 (by rfl) ⟨2122244, by rfl⟩ : syracuseStep 2829659 = 4244489) B4244489
theorem B1886439 : Blo 1885435 1886439 := bstep (se 1 (by rfl) ⟨1414829, by rfl⟩ : syracuseStep 1886439 = 2829659) B2829659
theorem B2122249 : Blo 1885435 2122249 := bbase (se 2 (by rfl) ⟨795843, by rfl⟩ : syracuseStep 2122249 = 1591687) (by norm_num)
theorem B2829665 : Blo 1885435 2829665 := bstep (se 2 (by rfl) ⟨1061124, by rfl⟩ : syracuseStep 2829665 = 2122249) B2122249
theorem B1886443 : Blo 1885435 1886443 := bstep (se 1 (by rfl) ⟨1414832, by rfl⟩ : syracuseStep 1886443 = 2829665) B2829665
theorem B12907253 : Blo 1885435 12907253 := bbase (se 5 (by rfl) ⟨605027, by rfl⟩ : syracuseStep 12907253 = 1210055) (by norm_num)
theorem B8604835 : Blo 1885435 8604835 := bstep (se 1 (by rfl) ⟨6453626, by rfl⟩ : syracuseStep 8604835 = 12907253) B12907253
theorem B45892453 : Blo 1885435 45892453 := bstep (se 4 (by rfl) ⟨4302417, by rfl⟩ : syracuseStep 45892453 = 8604835) B8604835
theorem B61189937 : Blo 1885435 61189937 := bstep (se 2 (by rfl) ⟨22946226, by rfl⟩ : syracuseStep 61189937 = 45892453) B45892453
theorem B40793291 : Blo 1885435 40793291 := bstep (se 1 (by rfl) ⟨30594968, by rfl⟩ : syracuseStep 40793291 = 61189937) B61189937
theorem B27195527 : Blo 1885435 27195527 := bstep (se 1 (by rfl) ⟨20396645, by rfl⟩ : syracuseStep 27195527 = 40793291) B40793291
theorem B18130351 : Blo 1885435 18130351 := bstep (se 1 (by rfl) ⟨13597763, by rfl⟩ : syracuseStep 18130351 = 27195527) B27195527
theorem B24173801 : Blo 1885435 24173801 := bstep (se 2 (by rfl) ⟨9065175, by rfl⟩ : syracuseStep 24173801 = 18130351) B18130351
theorem B16115867 : Blo 1885435 16115867 := bstep (se 1 (by rfl) ⟨12086900, by rfl⟩ : syracuseStep 16115867 = 24173801) B24173801
theorem B10743911 : Blo 1885435 10743911 := bstep (se 1 (by rfl) ⟨8057933, by rfl⟩ : syracuseStep 10743911 = 16115867) B16115867
theorem B7162607 : Blo 1885435 7162607 := bstep (se 1 (by rfl) ⟨5371955, by rfl⟩ : syracuseStep 7162607 = 10743911) B10743911
theorem B4775071 : Blo 1885435 4775071 := bstep (se 1 (by rfl) ⟨3581303, by rfl⟩ : syracuseStep 4775071 = 7162607) B7162607
theorem B6366761 : Blo 1885435 6366761 := bstep (se 2 (by rfl) ⟨2387535, by rfl⟩ : syracuseStep 6366761 = 4775071) B4775071
theorem B4244507 : Blo 1885435 4244507 := bstep (se 1 (by rfl) ⟨3183380, by rfl⟩ : syracuseStep 4244507 = 6366761) B6366761
theorem B2829671 : Blo 1885435 2829671 := bstep (se 1 (by rfl) ⟨2122253, by rfl⟩ : syracuseStep 2829671 = 4244507) B4244507
theorem B1886447 : Blo 1885435 1886447 := bstep (se 1 (by rfl) ⟨1414835, by rfl⟩ : syracuseStep 1886447 = 2829671) B2829671
theorem B2829677 : Blo 1885435 2829677 := bbase (se 3 (by rfl) ⟨530564, by rfl⟩ : syracuseStep 2829677 = 1061129) (by norm_num)
theorem B1886451 : Blo 1885435 1886451 := bstep (se 1 (by rfl) ⟨1414838, by rfl⟩ : syracuseStep 1886451 = 2829677) B2829677
theorem B4244525 : Blo 1885435 4244525 := bbase (se 3 (by rfl) ⟨795848, by rfl⟩ : syracuseStep 4244525 = 1591697) (by norm_num)
theorem B2829683 : Blo 1885435 2829683 := bstep (se 1 (by rfl) ⟨2122262, by rfl⟩ : syracuseStep 2829683 = 4244525) B4244525
theorem B1886455 : Blo 1885435 1886455 := bstep (se 1 (by rfl) ⟨1414841, by rfl⟩ : syracuseStep 1886455 = 2829683) B2829683
theorem B2266309 : Blo 1885435 2266309 := bbase (se 4 (by rfl) ⟨212466, by rfl⟩ : syracuseStep 2266309 = 424933) (by norm_num)
theorem B12086981 : Blo 1885435 12086981 := bstep (se 4 (by rfl) ⟨1133154, by rfl⟩ : syracuseStep 12086981 = 2266309) B2266309
theorem B8057987 : Blo 1885435 8057987 := bstep (se 1 (by rfl) ⟨6043490, by rfl⟩ : syracuseStep 8057987 = 12086981) B12086981
theorem B5371991 : Blo 1885435 5371991 := bstep (se 1 (by rfl) ⟨4028993, by rfl⟩ : syracuseStep 5371991 = 8057987) B8057987
theorem B3581327 : Blo 1885435 3581327 := bstep (se 1 (by rfl) ⟨2685995, by rfl⟩ : syracuseStep 3581327 = 5371991) B5371991
theorem B2387551 : Blo 1885435 2387551 := bstep (se 1 (by rfl) ⟨1790663, by rfl⟩ : syracuseStep 2387551 = 3581327) B3581327
theorem B3183401 : Blo 1885435 3183401 := bstep (se 2 (by rfl) ⟨1193775, by rfl⟩ : syracuseStep 3183401 = 2387551) B2387551
theorem B2122267 : Blo 1885435 2122267 := bstep (se 1 (by rfl) ⟨1591700, by rfl⟩ : syracuseStep 2122267 = 3183401) B3183401
theorem B2829689 : Blo 1885435 2829689 := bstep (se 2 (by rfl) ⟨1061133, by rfl⟩ : syracuseStep 2829689 = 2122267) B2122267
theorem B1886459 : Blo 1885435 1886459 := bstep (se 1 (by rfl) ⟨1414844, by rfl⟩ : syracuseStep 1886459 = 2829689) B2829689
theorem B2266313 : Blo 1885435 2266313 := bbase (se 2 (by rfl) ⟨849867, by rfl⟩ : syracuseStep 2266313 = 1699735) (by norm_num)
theorem B6043501 : Blo 1885435 6043501 := bstep (se 3 (by rfl) ⟨1133156, by rfl⟩ : syracuseStep 6043501 = 2266313) B2266313
theorem B32232005 : Blo 1885435 32232005 := bstep (se 4 (by rfl) ⟨3021750, by rfl⟩ : syracuseStep 32232005 = 6043501) B6043501
theorem B21488003 : Blo 1885435 21488003 := bstep (se 1 (by rfl) ⟨16116002, by rfl⟩ : syracuseStep 21488003 = 32232005) B32232005
theorem B14325335 : Blo 1885435 14325335 := bstep (se 1 (by rfl) ⟨10744001, by rfl⟩ : syracuseStep 14325335 = 21488003) B21488003
theorem B9550223 : Blo 1885435 9550223 := bstep (se 1 (by rfl) ⟨7162667, by rfl⟩ : syracuseStep 9550223 = 14325335) B14325335
theorem B6366815 : Blo 1885435 6366815 := bstep (se 1 (by rfl) ⟨4775111, by rfl⟩ : syracuseStep 6366815 = 9550223) B9550223
theorem B4244543 : Blo 1885435 4244543 := bstep (se 1 (by rfl) ⟨3183407, by rfl⟩ : syracuseStep 4244543 = 6366815) B6366815
theorem B2829695 : Blo 1885435 2829695 := bstep (se 1 (by rfl) ⟨2122271, by rfl⟩ : syracuseStep 2829695 = 4244543) B4244543
theorem B1886463 : Blo 1885435 1886463 := bstep (se 1 (by rfl) ⟨1414847, by rfl⟩ : syracuseStep 1886463 = 2829695) B2829695
theorem B2829701 : Blo 1885435 2829701 := bbase (se 4 (by rfl) ⟨265284, by rfl⟩ : syracuseStep 2829701 = 530569) (by norm_num)
theorem B1886467 : Blo 1885435 1886467 := bstep (se 1 (by rfl) ⟨1414850, by rfl⟩ : syracuseStep 1886467 = 2829701) B2829701
theorem B3183421 : Blo 1885435 3183421 := bbase (se 3 (by rfl) ⟨596891, by rfl⟩ : syracuseStep 3183421 = 1193783) (by norm_num)
theorem B4244561 : Blo 1885435 4244561 := bstep (se 2 (by rfl) ⟨1591710, by rfl⟩ : syracuseStep 4244561 = 3183421) B3183421
theorem B2829707 : Blo 1885435 2829707 := bstep (se 1 (by rfl) ⟨2122280, by rfl⟩ : syracuseStep 2829707 = 4244561) B4244561
theorem B1886471 : Blo 1885435 1886471 := bstep (se 1 (by rfl) ⟨1414853, by rfl⟩ : syracuseStep 1886471 = 2829707) B2829707
theorem B2122285 : Blo 1885435 2122285 := bbase (se 3 (by rfl) ⟨397928, by rfl⟩ : syracuseStep 2122285 = 795857) (by norm_num)
theorem B2829713 : Blo 1885435 2829713 := bstep (se 2 (by rfl) ⟨1061142, by rfl⟩ : syracuseStep 2829713 = 2122285) B2122285
theorem B1886475 : Blo 1885435 1886475 := bstep (se 1 (by rfl) ⟨1414856, by rfl⟩ : syracuseStep 1886475 = 2829713) B2829713
theorem B6366869 : Blo 1885435 6366869 := bbase (se 6 (by rfl) ⟨149223, by rfl⟩ : syracuseStep 6366869 = 298447) (by norm_num)
theorem B4244579 : Blo 1885435 4244579 := bstep (se 1 (by rfl) ⟨3183434, by rfl⟩ : syracuseStep 4244579 = 6366869) B6366869
theorem B2829719 : Blo 1885435 2829719 := bstep (se 1 (by rfl) ⟨2122289, by rfl⟩ : syracuseStep 2829719 = 4244579) B4244579
theorem B1886479 : Blo 1885435 1886479 := bstep (se 1 (by rfl) ⟨1414859, by rfl⟩ : syracuseStep 1886479 = 2829719) B2829719
theorem B2829725 : Blo 1885435 2829725 := bbase (se 3 (by rfl) ⟨530573, by rfl⟩ : syracuseStep 2829725 = 1061147) (by norm_num)
theorem B1886483 : Blo 1885435 1886483 := bstep (se 1 (by rfl) ⟨1414862, by rfl⟩ : syracuseStep 1886483 = 2829725) B2829725
theorem B4244597 : Blo 1885435 4244597 := bbase (se 5 (by rfl) ⟨198965, by rfl⟩ : syracuseStep 4244597 = 397931) (by norm_num)
theorem B2829731 : Blo 1885435 2829731 := bstep (se 1 (by rfl) ⟨2122298, by rfl⟩ : syracuseStep 2829731 = 4244597) B4244597
theorem B1886487 : Blo 1885435 1886487 := bstep (se 1 (by rfl) ⟨1414865, by rfl⟩ : syracuseStep 1886487 = 2829731) B2829731
theorem B16116245 : Blo 1885435 16116245 := bbase (se 6 (by rfl) ⟨377724, by rfl⟩ : syracuseStep 16116245 = 755449) (by norm_num)
theorem B10744163 : Blo 1885435 10744163 := bstep (se 1 (by rfl) ⟨8058122, by rfl⟩ : syracuseStep 10744163 = 16116245) B16116245
theorem B7162775 : Blo 1885435 7162775 := bstep (se 1 (by rfl) ⟨5372081, by rfl⟩ : syracuseStep 7162775 = 10744163) B10744163
theorem B4775183 : Blo 1885435 4775183 := bstep (se 1 (by rfl) ⟨3581387, by rfl⟩ : syracuseStep 4775183 = 7162775) B7162775
theorem B3183455 : Blo 1885435 3183455 := bstep (se 1 (by rfl) ⟨2387591, by rfl⟩ : syracuseStep 3183455 = 4775183) B4775183
theorem B2122303 : Blo 1885435 2122303 := bstep (se 1 (by rfl) ⟨1591727, by rfl⟩ : syracuseStep 2122303 = 3183455) B3183455
theorem B2829737 : Blo 1885435 2829737 := bstep (se 2 (by rfl) ⟨1061151, by rfl⟩ : syracuseStep 2829737 = 2122303) B2122303
theorem B1886491 : Blo 1885435 1886491 := bstep (se 1 (by rfl) ⟨1414868, by rfl⟩ : syracuseStep 1886491 = 2829737) B2829737
theorem B7162789 : Blo 1885435 7162789 := bbase (se 4 (by rfl) ⟨671511, by rfl⟩ : syracuseStep 7162789 = 1343023) (by norm_num)
theorem B9550385 : Blo 1885435 9550385 := bstep (se 2 (by rfl) ⟨3581394, by rfl⟩ : syracuseStep 9550385 = 7162789) B7162789
theorem B6366923 : Blo 1885435 6366923 := bstep (se 1 (by rfl) ⟨4775192, by rfl⟩ : syracuseStep 6366923 = 9550385) B9550385
theorem B4244615 : Blo 1885435 4244615 := bstep (se 1 (by rfl) ⟨3183461, by rfl⟩ : syracuseStep 4244615 = 6366923) B6366923
theorem B2829743 : Blo 1885435 2829743 := bstep (se 1 (by rfl) ⟨2122307, by rfl⟩ : syracuseStep 2829743 = 4244615) B4244615
theorem B1886495 : Blo 1885435 1886495 := bstep (se 1 (by rfl) ⟨1414871, by rfl⟩ : syracuseStep 1886495 = 2829743) B2829743
theorem B2829749 : Blo 1885435 2829749 := bbase (se 5 (by rfl) ⟨132644, by rfl⟩ : syracuseStep 2829749 = 265289) (by norm_num)
theorem B1886499 : Blo 1885435 1886499 := bstep (se 1 (by rfl) ⟨1414874, by rfl⟩ : syracuseStep 1886499 = 2829749) B2829749
theorem B4775213 : Blo 1885435 4775213 := bbase (se 3 (by rfl) ⟨895352, by rfl⟩ : syracuseStep 4775213 = 1790705) (by norm_num)
theorem B3183475 : Blo 1885435 3183475 := bstep (se 1 (by rfl) ⟨2387606, by rfl⟩ : syracuseStep 3183475 = 4775213) B4775213
theorem B4244633 : Blo 1885435 4244633 := bstep (se 2 (by rfl) ⟨1591737, by rfl⟩ : syracuseStep 4244633 = 3183475) B3183475
theorem B2829755 : Blo 1885435 2829755 := bstep (se 1 (by rfl) ⟨2122316, by rfl⟩ : syracuseStep 2829755 = 4244633) B4244633
theorem B1886503 : Blo 1885435 1886503 := bstep (se 1 (by rfl) ⟨1414877, by rfl⟩ : syracuseStep 1886503 = 2829755) B2829755
theorem B2122321 : Blo 1885435 2122321 := bbase (se 2 (by rfl) ⟨795870, by rfl⟩ : syracuseStep 2122321 = 1591741) (by norm_num)
theorem B2829761 : Blo 1885435 2829761 := bstep (se 2 (by rfl) ⟨1061160, by rfl⟩ : syracuseStep 2829761 = 2122321) B2122321
theorem B1886507 : Blo 1885435 1886507 := bstep (se 1 (by rfl) ⟨1414880, by rfl⟩ : syracuseStep 1886507 = 2829761) B2829761
theorem B2686069 : Blo 1885435 2686069 := bbase (se 5 (by rfl) ⟨125909, by rfl⟩ : syracuseStep 2686069 = 251819) (by norm_num)
theorem B3581425 : Blo 1885435 3581425 := bstep (se 2 (by rfl) ⟨1343034, by rfl⟩ : syracuseStep 3581425 = 2686069) B2686069
theorem B4775233 : Blo 1885435 4775233 := bstep (se 2 (by rfl) ⟨1790712, by rfl⟩ : syracuseStep 4775233 = 3581425) B3581425
theorem B6366977 : Blo 1885435 6366977 := bstep (se 2 (by rfl) ⟨2387616, by rfl⟩ : syracuseStep 6366977 = 4775233) B4775233
theorem B4244651 : Blo 1885435 4244651 := bstep (se 1 (by rfl) ⟨3183488, by rfl⟩ : syracuseStep 4244651 = 6366977) B6366977
theorem B2829767 : Blo 1885435 2829767 := bstep (se 1 (by rfl) ⟨2122325, by rfl⟩ : syracuseStep 2829767 = 4244651) B4244651
theorem B1886511 : Blo 1885435 1886511 := bstep (se 1 (by rfl) ⟨1414883, by rfl⟩ : syracuseStep 1886511 = 2829767) B2829767
theorem B2829773 : Blo 1885435 2829773 := bbase (se 3 (by rfl) ⟨530582, by rfl⟩ : syracuseStep 2829773 = 1061165) (by norm_num)
theorem B1886515 : Blo 1885435 1886515 := bstep (se 1 (by rfl) ⟨1414886, by rfl⟩ : syracuseStep 1886515 = 2829773) B2829773
theorem B4244669 : Blo 1885435 4244669 := bbase (se 3 (by rfl) ⟨795875, by rfl⟩ : syracuseStep 4244669 = 1591751) (by norm_num)
theorem B2829779 : Blo 1885435 2829779 := bstep (se 1 (by rfl) ⟨2122334, by rfl⟩ : syracuseStep 2829779 = 4244669) B4244669
theorem B1886519 : Blo 1885435 1886519 := bstep (se 1 (by rfl) ⟨1414889, by rfl⟩ : syracuseStep 1886519 = 2829779) B2829779
theorem B3183509 : Blo 1885435 3183509 := bbase (se 6 (by rfl) ⟨74613, by rfl⟩ : syracuseStep 3183509 = 149227) (by norm_num)
theorem B2122339 : Blo 1885435 2122339 := bstep (se 1 (by rfl) ⟨1591754, by rfl⟩ : syracuseStep 2122339 = 3183509) B3183509
theorem B2829785 : Blo 1885435 2829785 := bstep (se 2 (by rfl) ⟨1061169, by rfl⟩ : syracuseStep 2829785 = 2122339) B2122339
theorem B1886523 : Blo 1885435 1886523 := bstep (se 1 (by rfl) ⟨1414892, by rfl⟩ : syracuseStep 1886523 = 2829785) B2829785
theorem B12087413 : Blo 1885435 12087413 := bbase (se 5 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 12087413 = 1133195) (by norm_num)
theorem B8058275 : Blo 1885435 8058275 := bstep (se 1 (by rfl) ⟨6043706, by rfl⟩ : syracuseStep 8058275 = 12087413) B12087413
theorem B5372183 : Blo 1885435 5372183 := bstep (se 1 (by rfl) ⟨4029137, by rfl⟩ : syracuseStep 5372183 = 8058275) B8058275
theorem B14325821 : Blo 1885435 14325821 := bstep (se 3 (by rfl) ⟨2686091, by rfl⟩ : syracuseStep 14325821 = 5372183) B5372183
theorem B9550547 : Blo 1885435 9550547 := bstep (se 1 (by rfl) ⟨7162910, by rfl⟩ : syracuseStep 9550547 = 14325821) B14325821
theorem B6367031 : Blo 1885435 6367031 := bstep (se 1 (by rfl) ⟨4775273, by rfl⟩ : syracuseStep 6367031 = 9550547) B9550547
theorem B4244687 : Blo 1885435 4244687 := bstep (se 1 (by rfl) ⟨3183515, by rfl⟩ : syracuseStep 4244687 = 6367031) B6367031
theorem B2829791 : Blo 1885435 2829791 := bstep (se 1 (by rfl) ⟨2122343, by rfl⟩ : syracuseStep 2829791 = 4244687) B4244687
theorem B1886527 : Blo 1885435 1886527 := bstep (se 1 (by rfl) ⟨1414895, by rfl⟩ : syracuseStep 1886527 = 2829791) B2829791
theorem B2829797 : Blo 1885435 2829797 := bbase (se 4 (by rfl) ⟨265293, by rfl⟩ : syracuseStep 2829797 = 530587) (by norm_num)
theorem B1886531 : Blo 1885435 1886531 := bstep (se 1 (by rfl) ⟨1414898, by rfl⟩ : syracuseStep 1886531 = 2829797) B2829797
theorem B2868413 : Blo 1885435 2868413 := bbase (se 3 (by rfl) ⟨537827, by rfl⟩ : syracuseStep 2868413 = 1075655) (by norm_num)
theorem B7649101 : Blo 1885435 7649101 := bstep (se 3 (by rfl) ⟨1434206, by rfl⟩ : syracuseStep 7649101 = 2868413) B2868413
theorem B10198801 : Blo 1885435 10198801 := bstep (se 2 (by rfl) ⟨3824550, by rfl⟩ : syracuseStep 10198801 = 7649101) B7649101
theorem B13598401 : Blo 1885435 13598401 := bstep (se 2 (by rfl) ⟨5099400, by rfl⟩ : syracuseStep 13598401 = 10198801) B10198801
theorem B18131201 : Blo 1885435 18131201 := bstep (se 2 (by rfl) ⟨6799200, by rfl⟩ : syracuseStep 18131201 = 13598401) B13598401
theorem B12087467 : Blo 1885435 12087467 := bstep (se 1 (by rfl) ⟨9065600, by rfl⟩ : syracuseStep 12087467 = 18131201) B18131201
theorem B8058311 : Blo 1885435 8058311 := bstep (se 1 (by rfl) ⟨6043733, by rfl⟩ : syracuseStep 8058311 = 12087467) B12087467
theorem B5372207 : Blo 1885435 5372207 := bstep (se 1 (by rfl) ⟨4029155, by rfl⟩ : syracuseStep 5372207 = 8058311) B8058311
theorem B3581471 : Blo 1885435 3581471 := bstep (se 1 (by rfl) ⟨2686103, by rfl⟩ : syracuseStep 3581471 = 5372207) B5372207
theorem B2387647 : Blo 1885435 2387647 := bstep (se 1 (by rfl) ⟨1790735, by rfl⟩ : syracuseStep 2387647 = 3581471) B3581471
theorem B3183529 : Blo 1885435 3183529 := bstep (se 2 (by rfl) ⟨1193823, by rfl⟩ : syracuseStep 3183529 = 2387647) B2387647
theorem B4244705 : Blo 1885435 4244705 := bstep (se 2 (by rfl) ⟨1591764, by rfl⟩ : syracuseStep 4244705 = 3183529) B3183529
theorem B2829803 : Blo 1885435 2829803 := bstep (se 1 (by rfl) ⟨2122352, by rfl⟩ : syracuseStep 2829803 = 4244705) B4244705
theorem B1886535 : Blo 1885435 1886535 := bstep (se 1 (by rfl) ⟨1414901, by rfl⟩ : syracuseStep 1886535 = 2829803) B2829803
theorem B2122357 : Blo 1885435 2122357 := bbase (se 5 (by rfl) ⟨99485, by rfl⟩ : syracuseStep 2122357 = 198971) (by norm_num)
theorem B2829809 : Blo 1885435 2829809 := bstep (se 2 (by rfl) ⟨1061178, by rfl⟩ : syracuseStep 2829809 = 2122357) B2122357
theorem B1886539 : Blo 1885435 1886539 := bstep (se 1 (by rfl) ⟨1414904, by rfl⟩ : syracuseStep 1886539 = 2829809) B2829809
theorem B2387657 : Blo 1885435 2387657 := bbase (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) (by norm_num)
theorem B6367085 : Blo 1885435 6367085 := bstep (se 3 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 6367085 = 2387657) B2387657
theorem B4244723 : Blo 1885435 4244723 := bstep (se 1 (by rfl) ⟨3183542, by rfl⟩ : syracuseStep 4244723 = 6367085) B6367085
theorem B2829815 : Blo 1885435 2829815 := bstep (se 1 (by rfl) ⟨2122361, by rfl⟩ : syracuseStep 2829815 = 4244723) B4244723
theorem B1886543 : Blo 1885435 1886543 := bstep (se 1 (by rfl) ⟨1414907, by rfl⟩ : syracuseStep 1886543 = 2829815) B2829815
theorem B2829821 : Blo 1885435 2829821 := bbase (se 3 (by rfl) ⟨530591, by rfl⟩ : syracuseStep 2829821 = 1061183) (by norm_num)
theorem B1886547 : Blo 1885435 1886547 := bstep (se 1 (by rfl) ⟨1414910, by rfl⟩ : syracuseStep 1886547 = 2829821) B2829821
theorem B4244741 : Blo 1885435 4244741 := bbase (se 4 (by rfl) ⟨397944, by rfl⟩ : syracuseStep 4244741 = 795889) (by norm_num)
theorem B2829827 : Blo 1885435 2829827 := bstep (se 1 (by rfl) ⟨2122370, by rfl⟩ : syracuseStep 2829827 = 4244741) B4244741
theorem B1886551 : Blo 1885435 1886551 := bstep (se 1 (by rfl) ⟨1414913, by rfl⟩ : syracuseStep 1886551 = 2829827) B2829827
theorem B3581509 : Blo 1885435 3581509 := bbase (se 4 (by rfl) ⟨335766, by rfl⟩ : syracuseStep 3581509 = 671533) (by norm_num)
theorem B4775345 : Blo 1885435 4775345 := bstep (se 2 (by rfl) ⟨1790754, by rfl⟩ : syracuseStep 4775345 = 3581509) B3581509
theorem B3183563 : Blo 1885435 3183563 := bstep (se 1 (by rfl) ⟨2387672, by rfl⟩ : syracuseStep 3183563 = 4775345) B4775345
theorem B2122375 : Blo 1885435 2122375 := bstep (se 1 (by rfl) ⟨1591781, by rfl⟩ : syracuseStep 2122375 = 3183563) B3183563
theorem B2829833 : Blo 1885435 2829833 := bstep (se 2 (by rfl) ⟨1061187, by rfl⟩ : syracuseStep 2829833 = 2122375) B2122375
theorem B1886555 : Blo 1885435 1886555 := bstep (se 1 (by rfl) ⟨1414916, by rfl⟩ : syracuseStep 1886555 = 2829833) B2829833
theorem B9550709 : Blo 1885435 9550709 := bbase (se 5 (by rfl) ⟨447689, by rfl⟩ : syracuseStep 9550709 = 895379) (by norm_num)
theorem B6367139 : Blo 1885435 6367139 := bstep (se 1 (by rfl) ⟨4775354, by rfl⟩ : syracuseStep 6367139 = 9550709) B9550709
theorem B4244759 : Blo 1885435 4244759 := bstep (se 1 (by rfl) ⟨3183569, by rfl⟩ : syracuseStep 4244759 = 6367139) B6367139
theorem B2829839 : Blo 1885435 2829839 := bstep (se 1 (by rfl) ⟨2122379, by rfl⟩ : syracuseStep 2829839 = 4244759) B4244759
theorem B1886559 : Blo 1885435 1886559 := bstep (se 1 (by rfl) ⟨1414919, by rfl⟩ : syracuseStep 1886559 = 2829839) B2829839
theorem B2829845 : Blo 1885435 2829845 := bbase (se 6 (by rfl) ⟨66324, by rfl⟩ : syracuseStep 2829845 = 132649) (by norm_num)
theorem B1886563 : Blo 1885435 1886563 := bstep (se 1 (by rfl) ⟨1414922, by rfl⟩ : syracuseStep 1886563 = 2829845) B2829845
theorem B14521589 : Blo 1885435 14521589 := bbase (se 5 (by rfl) ⟨680699, by rfl⟩ : syracuseStep 14521589 = 1361399) (by norm_num)
theorem B9681059 : Blo 1885435 9681059 := bstep (se 1 (by rfl) ⟨7260794, by rfl⟩ : syracuseStep 9681059 = 14521589) B14521589
theorem B6454039 : Blo 1885435 6454039 := bstep (se 1 (by rfl) ⟨4840529, by rfl⟩ : syracuseStep 6454039 = 9681059) B9681059
theorem B8605385 : Blo 1885435 8605385 := bstep (se 2 (by rfl) ⟨3227019, by rfl⟩ : syracuseStep 8605385 = 6454039) B6454039
theorem B5736923 : Blo 1885435 5736923 := bstep (se 1 (by rfl) ⟨4302692, by rfl⟩ : syracuseStep 5736923 = 8605385) B8605385
theorem B3824615 : Blo 1885435 3824615 := bstep (se 1 (by rfl) ⟨2868461, by rfl⟩ : syracuseStep 3824615 = 5736923) B5736923
theorem B10198973 : Blo 1885435 10198973 := bstep (se 3 (by rfl) ⟨1912307, by rfl⟩ : syracuseStep 10198973 = 3824615) B3824615
theorem B6799315 : Blo 1885435 6799315 := bstep (se 1 (by rfl) ⟨5099486, by rfl⟩ : syracuseStep 6799315 = 10198973) B10198973
theorem B9065753 : Blo 1885435 9065753 := bstep (se 2 (by rfl) ⟨3399657, by rfl⟩ : syracuseStep 9065753 = 6799315) B6799315
theorem B6043835 : Blo 1885435 6043835 := bstep (se 1 (by rfl) ⟨4532876, by rfl⟩ : syracuseStep 6043835 = 9065753) B9065753
theorem B16116893 : Blo 1885435 16116893 := bstep (se 3 (by rfl) ⟨3021917, by rfl⟩ : syracuseStep 16116893 = 6043835) B6043835
theorem B10744595 : Blo 1885435 10744595 := bstep (se 1 (by rfl) ⟨8058446, by rfl⟩ : syracuseStep 10744595 = 16116893) B16116893
theorem B7163063 : Blo 1885435 7163063 := bstep (se 1 (by rfl) ⟨5372297, by rfl⟩ : syracuseStep 7163063 = 10744595) B10744595
theorem B4775375 : Blo 1885435 4775375 := bstep (se 1 (by rfl) ⟨3581531, by rfl⟩ : syracuseStep 4775375 = 7163063) B7163063
theorem B3183583 : Blo 1885435 3183583 := bstep (se 1 (by rfl) ⟨2387687, by rfl⟩ : syracuseStep 3183583 = 4775375) B4775375
theorem B4244777 : Blo 1885435 4244777 := bstep (se 2 (by rfl) ⟨1591791, by rfl⟩ : syracuseStep 4244777 = 3183583) B3183583
theorem B2829851 : Blo 1885435 2829851 := bstep (se 1 (by rfl) ⟨2122388, by rfl⟩ : syracuseStep 2829851 = 4244777) B4244777
theorem B1886567 : Blo 1885435 1886567 := bstep (se 1 (by rfl) ⟨1414925, by rfl⟩ : syracuseStep 1886567 = 2829851) B2829851
theorem B2122393 : Blo 1885435 2122393 := bbase (se 2 (by rfl) ⟨795897, by rfl⟩ : syracuseStep 2122393 = 1591795) (by norm_num)
theorem B2829857 : Blo 1885435 2829857 := bstep (se 2 (by rfl) ⟨1061196, by rfl⟩ : syracuseStep 2829857 = 2122393) B2122393
theorem B1886571 : Blo 1885435 1886571 := bstep (se 1 (by rfl) ⟨1414928, by rfl⟩ : syracuseStep 1886571 = 2829857) B2829857
theorem B7163093 : Blo 1885435 7163093 := bbase (se 7 (by rfl) ⟨83942, by rfl⟩ : syracuseStep 7163093 = 167885) (by norm_num)
theorem B4775395 : Blo 1885435 4775395 := bstep (se 1 (by rfl) ⟨3581546, by rfl⟩ : syracuseStep 4775395 = 7163093) B7163093
theorem B6367193 : Blo 1885435 6367193 := bstep (se 2 (by rfl) ⟨2387697, by rfl⟩ : syracuseStep 6367193 = 4775395) B4775395
theorem B4244795 : Blo 1885435 4244795 := bstep (se 1 (by rfl) ⟨3183596, by rfl⟩ : syracuseStep 4244795 = 6367193) B6367193
theorem B2829863 : Blo 1885435 2829863 := bstep (se 1 (by rfl) ⟨2122397, by rfl⟩ : syracuseStep 2829863 = 4244795) B4244795
theorem B1886575 : Blo 1885435 1886575 := bstep (se 1 (by rfl) ⟨1414931, by rfl⟩ : syracuseStep 1886575 = 2829863) B2829863
theorem B2829869 : Blo 1885435 2829869 := bbase (se 3 (by rfl) ⟨530600, by rfl⟩ : syracuseStep 2829869 = 1061201) (by norm_num)
theorem B1886579 : Blo 1885435 1886579 := bstep (se 1 (by rfl) ⟨1414934, by rfl⟩ : syracuseStep 1886579 = 2829869) B2829869
theorem B4244813 : Blo 1885435 4244813 := bbase (se 3 (by rfl) ⟨795902, by rfl⟩ : syracuseStep 4244813 = 1591805) (by norm_num)
theorem B2829875 : Blo 1885435 2829875 := bstep (se 1 (by rfl) ⟨2122406, by rfl⟩ : syracuseStep 2829875 = 4244813) B4244813
theorem B1886583 : Blo 1885435 1886583 := bstep (se 1 (by rfl) ⟨1414937, by rfl⟩ : syracuseStep 1886583 = 2829875) B2829875
theorem B2387713 : Blo 1885435 2387713 := bbase (se 2 (by rfl) ⟨895392, by rfl⟩ : syracuseStep 2387713 = 1790785) (by norm_num)
theorem B3183617 : Blo 1885435 3183617 := bstep (se 2 (by rfl) ⟨1193856, by rfl⟩ : syracuseStep 3183617 = 2387713) B2387713
theorem B2122411 : Blo 1885435 2122411 := bstep (se 1 (by rfl) ⟨1591808, by rfl⟩ : syracuseStep 2122411 = 3183617) B3183617
theorem B2829881 : Blo 1885435 2829881 := bstep (se 2 (by rfl) ⟨1061205, by rfl⟩ : syracuseStep 2829881 = 2122411) B2122411
theorem B1886587 : Blo 1885435 1886587 := bstep (se 1 (by rfl) ⟨1414940, by rfl⟩ : syracuseStep 1886587 = 2829881) B2829881
theorem B2014637 : Blo 1885435 2014637 := bbase (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) (by norm_num)
theorem B21489461 : Blo 1885435 21489461 := bstep (se 5 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 21489461 = 2014637) B2014637
theorem B14326307 : Blo 1885435 14326307 := bstep (se 1 (by rfl) ⟨10744730, by rfl⟩ : syracuseStep 14326307 = 21489461) B21489461
theorem B9550871 : Blo 1885435 9550871 := bstep (se 1 (by rfl) ⟨7163153, by rfl⟩ : syracuseStep 9550871 = 14326307) B14326307
theorem B6367247 : Blo 1885435 6367247 := bstep (se 1 (by rfl) ⟨4775435, by rfl⟩ : syracuseStep 6367247 = 9550871) B9550871
theorem B4244831 : Blo 1885435 4244831 := bstep (se 1 (by rfl) ⟨3183623, by rfl⟩ : syracuseStep 4244831 = 6367247) B6367247
theorem B2829887 : Blo 1885435 2829887 := bstep (se 1 (by rfl) ⟨2122415, by rfl⟩ : syracuseStep 2829887 = 4244831) B4244831
theorem B1886591 : Blo 1885435 1886591 := bstep (se 1 (by rfl) ⟨1414943, by rfl⟩ : syracuseStep 1886591 = 2829887) B2829887
theorem B2829893 : Blo 1885435 2829893 := bbase (se 4 (by rfl) ⟨265302, by rfl⟩ : syracuseStep 2829893 = 530605) (by norm_num)
theorem B1886595 : Blo 1885435 1886595 := bstep (se 1 (by rfl) ⟨1414946, by rfl⟩ : syracuseStep 1886595 = 2829893) B2829893
theorem B3183637 : Blo 1885435 3183637 := bbase (se 6 (by rfl) ⟨74616, by rfl⟩ : syracuseStep 3183637 = 149233) (by norm_num)
theorem B4244849 : Blo 1885435 4244849 := bstep (se 2 (by rfl) ⟨1591818, by rfl⟩ : syracuseStep 4244849 = 3183637) B3183637
theorem B2829899 : Blo 1885435 2829899 := bstep (se 1 (by rfl) ⟨2122424, by rfl⟩ : syracuseStep 2829899 = 4244849) B4244849
theorem B1886599 : Blo 1885435 1886599 := bstep (se 1 (by rfl) ⟨1414949, by rfl⟩ : syracuseStep 1886599 = 2829899) B2829899
theorem B2122429 : Blo 1885435 2122429 := bbase (se 3 (by rfl) ⟨397955, by rfl⟩ : syracuseStep 2122429 = 795911) (by norm_num)
theorem B2829905 : Blo 1885435 2829905 := bstep (se 2 (by rfl) ⟨1061214, by rfl⟩ : syracuseStep 2829905 = 2122429) B2122429
theorem B1886603 : Blo 1885435 1886603 := bstep (se 1 (by rfl) ⟨1414952, by rfl⟩ : syracuseStep 1886603 = 2829905) B2829905
theorem B6367301 : Blo 1885435 6367301 := bbase (se 4 (by rfl) ⟨596934, by rfl⟩ : syracuseStep 6367301 = 1193869) (by norm_num)
theorem B4244867 : Blo 1885435 4244867 := bstep (se 1 (by rfl) ⟨3183650, by rfl⟩ : syracuseStep 4244867 = 6367301) B6367301
theorem B2829911 : Blo 1885435 2829911 := bstep (se 1 (by rfl) ⟨2122433, by rfl⟩ : syracuseStep 2829911 = 4244867) B4244867
theorem B1886607 : Blo 1885435 1886607 := bstep (se 1 (by rfl) ⟨1414955, by rfl⟩ : syracuseStep 1886607 = 2829911) B2829911
theorem B2829917 : Blo 1885435 2829917 := bbase (se 3 (by rfl) ⟨530609, by rfl⟩ : syracuseStep 2829917 = 1061219) (by norm_num)
theorem B1886611 : Blo 1885435 1886611 := bstep (se 1 (by rfl) ⟨1414958, by rfl⟩ : syracuseStep 1886611 = 2829917) B2829917
theorem B4244885 : Blo 1885435 4244885 := bbase (se 6 (by rfl) ⟨99489, by rfl⟩ : syracuseStep 4244885 = 198979) (by norm_num)
theorem B2829923 : Blo 1885435 2829923 := bstep (se 1 (by rfl) ⟨2122442, by rfl⟩ : syracuseStep 2829923 = 4244885) B4244885
theorem B1886615 : Blo 1885435 1886615 := bstep (se 1 (by rfl) ⟨1414961, by rfl⟩ : syracuseStep 1886615 = 2829923) B2829923
theorem B9066005 : Blo 1885435 9066005 := bbase (se 6 (by rfl) ⟨212484, by rfl⟩ : syracuseStep 9066005 = 424969) (by norm_num)
theorem B6044003 : Blo 1885435 6044003 := bstep (se 1 (by rfl) ⟨4533002, by rfl⟩ : syracuseStep 6044003 = 9066005) B9066005
theorem B4029335 : Blo 1885435 4029335 := bstep (se 1 (by rfl) ⟨3022001, by rfl⟩ : syracuseStep 4029335 = 6044003) B6044003
theorem B2686223 : Blo 1885435 2686223 := bstep (se 1 (by rfl) ⟨2014667, by rfl⟩ : syracuseStep 2686223 = 4029335) B4029335
theorem B7163261 : Blo 1885435 7163261 := bstep (se 3 (by rfl) ⟨1343111, by rfl⟩ : syracuseStep 7163261 = 2686223) B2686223
theorem B4775507 : Blo 1885435 4775507 := bstep (se 1 (by rfl) ⟨3581630, by rfl⟩ : syracuseStep 4775507 = 7163261) B7163261
theorem B3183671 : Blo 1885435 3183671 := bstep (se 1 (by rfl) ⟨2387753, by rfl⟩ : syracuseStep 3183671 = 4775507) B4775507
theorem B2122447 : Blo 1885435 2122447 := bstep (se 1 (by rfl) ⟨1591835, by rfl⟩ : syracuseStep 2122447 = 3183671) B3183671
theorem B2829929 : Blo 1885435 2829929 := bstep (se 2 (by rfl) ⟨1061223, by rfl⟩ : syracuseStep 2829929 = 2122447) B2122447
theorem B1886619 : Blo 1885435 1886619 := bstep (se 1 (by rfl) ⟨1414964, by rfl⟩ : syracuseStep 1886619 = 2829929) B2829929
theorem B4302821 : Blo 1885435 4302821 := bbase (se 4 (by rfl) ⟨403389, by rfl⟩ : syracuseStep 4302821 = 806779) (by norm_num)
theorem B2868547 : Blo 1885435 2868547 := bstep (se 1 (by rfl) ⟨2151410, by rfl⟩ : syracuseStep 2868547 = 4302821) B4302821
theorem B3824729 : Blo 1885435 3824729 := bstep (se 2 (by rfl) ⟨1434273, by rfl⟩ : syracuseStep 3824729 = 2868547) B2868547
theorem B2549819 : Blo 1885435 2549819 := bstep (se 1 (by rfl) ⟨1912364, by rfl⟩ : syracuseStep 2549819 = 3824729) B3824729
theorem B6799517 : Blo 1885435 6799517 := bstep (se 3 (by rfl) ⟨1274909, by rfl⟩ : syracuseStep 6799517 = 2549819) B2549819
theorem B4533011 : Blo 1885435 4533011 := bstep (se 1 (by rfl) ⟨3399758, by rfl⟩ : syracuseStep 4533011 = 6799517) B6799517
theorem B3022007 : Blo 1885435 3022007 := bstep (se 1 (by rfl) ⟨2266505, by rfl⟩ : syracuseStep 3022007 = 4533011) B4533011
theorem B8058685 : Blo 1885435 8058685 := bstep (se 3 (by rfl) ⟨1511003, by rfl⟩ : syracuseStep 8058685 = 3022007) B3022007
theorem B10744913 : Blo 1885435 10744913 := bstep (se 2 (by rfl) ⟨4029342, by rfl⟩ : syracuseStep 10744913 = 8058685) B8058685
theorem B7163275 : Blo 1885435 7163275 := bstep (se 1 (by rfl) ⟨5372456, by rfl⟩ : syracuseStep 7163275 = 10744913) B10744913
theorem B9551033 : Blo 1885435 9551033 := bstep (se 2 (by rfl) ⟨3581637, by rfl⟩ : syracuseStep 9551033 = 7163275) B7163275
theorem B6367355 : Blo 1885435 6367355 := bstep (se 1 (by rfl) ⟨4775516, by rfl⟩ : syracuseStep 6367355 = 9551033) B9551033
theorem B4244903 : Blo 1885435 4244903 := bstep (se 1 (by rfl) ⟨3183677, by rfl⟩ : syracuseStep 4244903 = 6367355) B6367355
theorem B2829935 : Blo 1885435 2829935 := bstep (se 1 (by rfl) ⟨2122451, by rfl⟩ : syracuseStep 2829935 = 4244903) B4244903
theorem B1886623 : Blo 1885435 1886623 := bstep (se 1 (by rfl) ⟨1414967, by rfl⟩ : syracuseStep 1886623 = 2829935) B2829935
theorem B2829941 : Blo 1885435 2829941 := bbase (se 5 (by rfl) ⟨132653, by rfl⟩ : syracuseStep 2829941 = 265307) (by norm_num)
theorem B1886627 : Blo 1885435 1886627 := bstep (se 1 (by rfl) ⟨1414970, by rfl⟩ : syracuseStep 1886627 = 2829941) B2829941
theorem B3581653 : Blo 1885435 3581653 := bbase (se 7 (by rfl) ⟨41972, by rfl⟩ : syracuseStep 3581653 = 83945) (by norm_num)
theorem B4775537 : Blo 1885435 4775537 := bstep (se 2 (by rfl) ⟨1790826, by rfl⟩ : syracuseStep 4775537 = 3581653) B3581653
theorem B3183691 : Blo 1885435 3183691 := bstep (se 1 (by rfl) ⟨2387768, by rfl⟩ : syracuseStep 3183691 = 4775537) B4775537
theorem B4244921 : Blo 1885435 4244921 := bstep (se 2 (by rfl) ⟨1591845, by rfl⟩ : syracuseStep 4244921 = 3183691) B3183691
theorem B2829947 : Blo 1885435 2829947 := bstep (se 1 (by rfl) ⟨2122460, by rfl⟩ : syracuseStep 2829947 = 4244921) B4244921
theorem B1886631 : Blo 1885435 1886631 := bstep (se 1 (by rfl) ⟨1414973, by rfl⟩ : syracuseStep 1886631 = 2829947) B2829947
theorem B2122465 : Blo 1885435 2122465 := bbase (se 2 (by rfl) ⟨795924, by rfl⟩ : syracuseStep 2122465 = 1591849) (by norm_num)
theorem B2829953 : Blo 1885435 2829953 := bstep (se 2 (by rfl) ⟨1061232, by rfl⟩ : syracuseStep 2829953 = 2122465) B2122465
theorem B1886635 : Blo 1885435 1886635 := bstep (se 1 (by rfl) ⟨1414976, by rfl⟩ : syracuseStep 1886635 = 2829953) B2829953
theorem B4775557 : Blo 1885435 4775557 := bbase (se 4 (by rfl) ⟨447708, by rfl⟩ : syracuseStep 4775557 = 895417) (by norm_num)
theorem B6367409 : Blo 1885435 6367409 := bstep (se 2 (by rfl) ⟨2387778, by rfl⟩ : syracuseStep 6367409 = 4775557) B4775557
theorem B4244939 : Blo 1885435 4244939 := bstep (se 1 (by rfl) ⟨3183704, by rfl⟩ : syracuseStep 4244939 = 6367409) B6367409
theorem B2829959 : Blo 1885435 2829959 := bstep (se 1 (by rfl) ⟨2122469, by rfl⟩ : syracuseStep 2829959 = 4244939) B4244939
theorem B1886639 : Blo 1885435 1886639 := bstep (se 1 (by rfl) ⟨1414979, by rfl⟩ : syracuseStep 1886639 = 2829959) B2829959
theorem B2829965 : Blo 1885435 2829965 := bbase (se 3 (by rfl) ⟨530618, by rfl⟩ : syracuseStep 2829965 = 1061237) (by norm_num)
theorem B1886643 : Blo 1885435 1886643 := bstep (se 1 (by rfl) ⟨1414982, by rfl⟩ : syracuseStep 1886643 = 2829965) B2829965
theorem B4244957 : Blo 1885435 4244957 := bbase (se 3 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 4244957 = 1591859) (by norm_num)
theorem B2829971 : Blo 1885435 2829971 := bstep (se 1 (by rfl) ⟨2122478, by rfl⟩ : syracuseStep 2829971 = 4244957) B4244957
theorem B1886647 : Blo 1885435 1886647 := bstep (se 1 (by rfl) ⟨1414985, by rfl⟩ : syracuseStep 1886647 = 2829971) B2829971
theorem B3183725 : Blo 1885435 3183725 := bbase (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) (by norm_num)
theorem B2122483 : Blo 1885435 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B2829977 : Blo 1885435 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B1886651 : Blo 1885435 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B22948757 : Blo 1885435 22948757 := bbase (se 6 (by rfl) ⟨537861, by rfl⟩ : syracuseStep 22948757 = 1075723) (by norm_num)
theorem B15299171 : Blo 1885435 15299171 := bstep (se 1 (by rfl) ⟨11474378, by rfl⟩ : syracuseStep 15299171 = 22948757) B22948757
theorem B10199447 : Blo 1885435 10199447 := bstep (se 1 (by rfl) ⟨7649585, by rfl⟩ : syracuseStep 10199447 = 15299171) B15299171
theorem B6799631 : Blo 1885435 6799631 := bstep (se 1 (by rfl) ⟨5099723, by rfl⟩ : syracuseStep 6799631 = 10199447) B10199447
theorem B18132349 : Blo 1885435 18132349 := bstep (se 3 (by rfl) ⟨3399815, by rfl⟩ : syracuseStep 18132349 = 6799631) B6799631
theorem B24176465 : Blo 1885435 24176465 := bstep (se 2 (by rfl) ⟨9066174, by rfl⟩ : syracuseStep 24176465 = 18132349) B18132349
theorem B16117643 : Blo 1885435 16117643 := bstep (se 1 (by rfl) ⟨12088232, by rfl⟩ : syracuseStep 16117643 = 24176465) B24176465
theorem B10745095 : Blo 1885435 10745095 := bstep (se 1 (by rfl) ⟨8058821, by rfl⟩ : syracuseStep 10745095 = 16117643) B16117643
theorem B14326793 : Blo 1885435 14326793 := bstep (se 2 (by rfl) ⟨5372547, by rfl⟩ : syracuseStep 14326793 = 10745095) B10745095
theorem B9551195 : Blo 1885435 9551195 := bstep (se 1 (by rfl) ⟨7163396, by rfl⟩ : syracuseStep 9551195 = 14326793) B14326793
theorem B6367463 : Blo 1885435 6367463 := bstep (se 1 (by rfl) ⟨4775597, by rfl⟩ : syracuseStep 6367463 = 9551195) B9551195
theorem B4244975 : Blo 1885435 4244975 := bstep (se 1 (by rfl) ⟨3183731, by rfl⟩ : syracuseStep 4244975 = 6367463) B6367463
theorem B2829983 : Blo 1885435 2829983 := bstep (se 1 (by rfl) ⟨2122487, by rfl⟩ : syracuseStep 2829983 = 4244975) B4244975
theorem B1886655 : Blo 1885435 1886655 := bstep (se 1 (by rfl) ⟨1414991, by rfl⟩ : syracuseStep 1886655 = 2829983) B2829983
theorem B2829989 : Blo 1885435 2829989 := bbase (se 4 (by rfl) ⟨265311, by rfl⟩ : syracuseStep 2829989 = 530623) (by norm_num)
theorem B1886659 : Blo 1885435 1886659 := bstep (se 1 (by rfl) ⟨1414994, by rfl⟩ : syracuseStep 1886659 = 2829989) B2829989
theorem B2387809 : Blo 1885435 2387809 := bbase (se 2 (by rfl) ⟨895428, by rfl⟩ : syracuseStep 2387809 = 1790857) (by norm_num)
theorem B3183745 : Blo 1885435 3183745 := bstep (se 2 (by rfl) ⟨1193904, by rfl⟩ : syracuseStep 3183745 = 2387809) B2387809
theorem B4244993 : Blo 1885435 4244993 := bstep (se 2 (by rfl) ⟨1591872, by rfl⟩ : syracuseStep 4244993 = 3183745) B3183745
theorem B2829995 : Blo 1885435 2829995 := bstep (se 1 (by rfl) ⟨2122496, by rfl⟩ : syracuseStep 2829995 = 4244993) B4244993
theorem B1886663 : Blo 1885435 1886663 := bstep (se 1 (by rfl) ⟨1414997, by rfl⟩ : syracuseStep 1886663 = 2829995) B2829995
theorem B2122501 : Blo 1885435 2122501 := bbase (se 4 (by rfl) ⟨198984, by rfl⟩ : syracuseStep 2122501 = 397969) (by norm_num)
theorem B2830001 : Blo 1885435 2830001 := bstep (se 2 (by rfl) ⟨1061250, by rfl⟩ : syracuseStep 2830001 = 2122501) B2122501
theorem B1886667 : Blo 1885435 1886667 := bstep (se 1 (by rfl) ⟨1415000, by rfl⟩ : syracuseStep 1886667 = 2830001) B2830001
theorem B3022085 : Blo 1885435 3022085 := bbase (se 4 (by rfl) ⟨283320, by rfl⟩ : syracuseStep 3022085 = 566641) (by norm_num)
theorem B2014723 : Blo 1885435 2014723 := bstep (se 1 (by rfl) ⟨1511042, by rfl⟩ : syracuseStep 2014723 = 3022085) B3022085
theorem B2686297 : Blo 1885435 2686297 := bstep (se 2 (by rfl) ⟨1007361, by rfl⟩ : syracuseStep 2686297 = 2014723) B2014723
theorem B3581729 : Blo 1885435 3581729 := bstep (se 2 (by rfl) ⟨1343148, by rfl⟩ : syracuseStep 3581729 = 2686297) B2686297
theorem B2387819 : Blo 1885435 2387819 := bstep (se 1 (by rfl) ⟨1790864, by rfl⟩ : syracuseStep 2387819 = 3581729) B3581729
theorem B6367517 : Blo 1885435 6367517 := bstep (se 3 (by rfl) ⟨1193909, by rfl⟩ : syracuseStep 6367517 = 2387819) B2387819
theorem B4245011 : Blo 1885435 4245011 := bstep (se 1 (by rfl) ⟨3183758, by rfl⟩ : syracuseStep 4245011 = 6367517) B6367517
theorem B2830007 : Blo 1885435 2830007 := bstep (se 1 (by rfl) ⟨2122505, by rfl⟩ : syracuseStep 2830007 = 4245011) B4245011
theorem B1886671 : Blo 1885435 1886671 := bstep (se 1 (by rfl) ⟨1415003, by rfl⟩ : syracuseStep 1886671 = 2830007) B2830007
theorem B2830013 : Blo 1885435 2830013 := bbase (se 3 (by rfl) ⟨530627, by rfl⟩ : syracuseStep 2830013 = 1061255) (by norm_num)
theorem B1886675 : Blo 1885435 1886675 := bstep (se 1 (by rfl) ⟨1415006, by rfl⟩ : syracuseStep 1886675 = 2830013) B2830013
theorem B4245029 : Blo 1885435 4245029 := bbase (se 4 (by rfl) ⟨397971, by rfl⟩ : syracuseStep 4245029 = 795943) (by norm_num)
theorem B2830019 : Blo 1885435 2830019 := bstep (se 1 (by rfl) ⟨2122514, by rfl⟩ : syracuseStep 2830019 = 4245029) B4245029
theorem B1886679 : Blo 1885435 1886679 := bstep (se 1 (by rfl) ⟨1415009, by rfl⟩ : syracuseStep 1886679 = 2830019) B2830019
theorem B4775669 : Blo 1885435 4775669 := bbase (se 5 (by rfl) ⟨223859, by rfl⟩ : syracuseStep 4775669 = 447719) (by norm_num)
theorem B3183779 : Blo 1885435 3183779 := bstep (se 1 (by rfl) ⟨2387834, by rfl⟩ : syracuseStep 3183779 = 4775669) B4775669
theorem B2122519 : Blo 1885435 2122519 := bstep (se 1 (by rfl) ⟨1591889, by rfl⟩ : syracuseStep 2122519 = 3183779) B3183779
theorem B2830025 : Blo 1885435 2830025 := bstep (se 2 (by rfl) ⟨1061259, by rfl⟩ : syracuseStep 2830025 = 2122519) B2122519
theorem B1886683 : Blo 1885435 1886683 := bstep (se 1 (by rfl) ⟨1415012, by rfl⟩ : syracuseStep 1886683 = 2830025) B2830025
theorem B1912429 : Blo 1885435 1912429 := bbase (se 3 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 1912429 = 717161) (by norm_num)
theorem B10199621 : Blo 1885435 10199621 := bstep (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) B1912429
theorem B27198989 : Blo 1885435 27198989 := bstep (se 3 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 27198989 = 10199621) B10199621
theorem B18132659 : Blo 1885435 18132659 := bstep (se 1 (by rfl) ⟨13599494, by rfl⟩ : syracuseStep 18132659 = 27198989) B27198989
theorem B12088439 : Blo 1885435 12088439 := bstep (se 1 (by rfl) ⟨9066329, by rfl⟩ : syracuseStep 12088439 = 18132659) B18132659
theorem B8058959 : Blo 1885435 8058959 := bstep (se 1 (by rfl) ⟨6044219, by rfl⟩ : syracuseStep 8058959 = 12088439) B12088439
theorem B5372639 : Blo 1885435 5372639 := bstep (se 1 (by rfl) ⟨4029479, by rfl⟩ : syracuseStep 5372639 = 8058959) B8058959
theorem B3581759 : Blo 1885435 3581759 := bstep (se 1 (by rfl) ⟨2686319, by rfl⟩ : syracuseStep 3581759 = 5372639) B5372639
theorem B9551357 : Blo 1885435 9551357 := bstep (se 3 (by rfl) ⟨1790879, by rfl⟩ : syracuseStep 9551357 = 3581759) B3581759
theorem B6367571 : Blo 1885435 6367571 := bstep (se 1 (by rfl) ⟨4775678, by rfl⟩ : syracuseStep 6367571 = 9551357) B9551357
theorem B4245047 : Blo 1885435 4245047 := bstep (se 1 (by rfl) ⟨3183785, by rfl⟩ : syracuseStep 4245047 = 6367571) B6367571
theorem B2830031 : Blo 1885435 2830031 := bstep (se 1 (by rfl) ⟨2122523, by rfl⟩ : syracuseStep 2830031 = 4245047) B4245047
theorem B1886687 : Blo 1885435 1886687 := bstep (se 1 (by rfl) ⟨1415015, by rfl⟩ : syracuseStep 1886687 = 2830031) B2830031
theorem B2830037 : Blo 1885435 2830037 := bbase (se 7 (by rfl) ⟨33164, by rfl⟩ : syracuseStep 2830037 = 66329) (by norm_num)
theorem B1886691 : Blo 1885435 1886691 := bstep (se 1 (by rfl) ⟨1415018, by rfl⟩ : syracuseStep 1886691 = 2830037) B2830037
theorem B2549917 : Blo 1885435 2549917 := bbase (se 3 (by rfl) ⟨478109, by rfl⟩ : syracuseStep 2549917 = 956219) (by norm_num)
theorem B3399889 : Blo 1885435 3399889 := bstep (se 2 (by rfl) ⟨1274958, by rfl⟩ : syracuseStep 3399889 = 2549917) B2549917
theorem B4533185 : Blo 1885435 4533185 := bstep (se 2 (by rfl) ⟨1699944, by rfl⟩ : syracuseStep 4533185 = 3399889) B3399889
theorem B3022123 : Blo 1885435 3022123 := bstep (se 1 (by rfl) ⟨2266592, by rfl⟩ : syracuseStep 3022123 = 4533185) B4533185
theorem B4029497 : Blo 1885435 4029497 := bstep (se 2 (by rfl) ⟨1511061, by rfl⟩ : syracuseStep 4029497 = 3022123) B3022123
theorem B2686331 : Blo 1885435 2686331 := bstep (se 1 (by rfl) ⟨2014748, by rfl⟩ : syracuseStep 2686331 = 4029497) B4029497
theorem B7163549 : Blo 1885435 7163549 := bstep (se 3 (by rfl) ⟨1343165, by rfl⟩ : syracuseStep 7163549 = 2686331) B2686331
theorem B4775699 : Blo 1885435 4775699 := bstep (se 1 (by rfl) ⟨3581774, by rfl⟩ : syracuseStep 4775699 = 7163549) B7163549
theorem B3183799 : Blo 1885435 3183799 := bstep (se 1 (by rfl) ⟨2387849, by rfl⟩ : syracuseStep 3183799 = 4775699) B4775699
theorem B4245065 : Blo 1885435 4245065 := bstep (se 2 (by rfl) ⟨1591899, by rfl⟩ : syracuseStep 4245065 = 3183799) B3183799
theorem B2830043 : Blo 1885435 2830043 := bstep (se 1 (by rfl) ⟨2122532, by rfl⟩ : syracuseStep 2830043 = 4245065) B4245065
theorem B1886695 : Blo 1885435 1886695 := bstep (se 1 (by rfl) ⟨1415021, by rfl⟩ : syracuseStep 1886695 = 2830043) B2830043
theorem B2122537 : Blo 1885435 2122537 := bbase (se 2 (by rfl) ⟨795951, by rfl⟩ : syracuseStep 2122537 = 1591903) (by norm_num)
theorem B2830049 : Blo 1885435 2830049 := bstep (se 2 (by rfl) ⟨1061268, by rfl⟩ : syracuseStep 2830049 = 2122537) B2122537
theorem B1886699 : Blo 1885435 1886699 := bstep (se 1 (by rfl) ⟨1415024, by rfl⟩ : syracuseStep 1886699 = 2830049) B2830049
theorem B2180857 : Blo 1885435 2180857 := bbase (se 2 (by rfl) ⟨817821, by rfl⟩ : syracuseStep 2180857 = 1635643) (by norm_num)
theorem B2907809 : Blo 1885435 2907809 := bstep (se 2 (by rfl) ⟨1090428, by rfl⟩ : syracuseStep 2907809 = 2180857) B2180857
theorem B1938539 : Blo 1885435 1938539 := bstep (se 1 (by rfl) ⟨1453904, by rfl⟩ : syracuseStep 1938539 = 2907809) B2907809
theorem B5169437 : Blo 1885435 5169437 := bstep (se 3 (by rfl) ⟨969269, by rfl⟩ : syracuseStep 5169437 = 1938539) B1938539
theorem B3446291 : Blo 1885435 3446291 := bstep (se 1 (by rfl) ⟨2584718, by rfl⟩ : syracuseStep 3446291 = 5169437) B5169437
theorem B2297527 : Blo 1885435 2297527 := bstep (se 1 (by rfl) ⟨1723145, by rfl⟩ : syracuseStep 2297527 = 3446291) B3446291
theorem B12253477 : Blo 1885435 12253477 := bstep (se 4 (by rfl) ⟨1148763, by rfl⟩ : syracuseStep 12253477 = 2297527) B2297527
theorem B16337969 : Blo 1885435 16337969 := bstep (se 2 (by rfl) ⟨6126738, by rfl⟩ : syracuseStep 16337969 = 12253477) B12253477
theorem B10891979 : Blo 1885435 10891979 := bstep (se 1 (by rfl) ⟨8168984, by rfl⟩ : syracuseStep 10891979 = 16337969) B16337969
theorem B7261319 : Blo 1885435 7261319 := bstep (se 1 (by rfl) ⟨5445989, by rfl⟩ : syracuseStep 7261319 = 10891979) B10891979
theorem B4840879 : Blo 1885435 4840879 := bstep (se 1 (by rfl) ⟨3630659, by rfl⟩ : syracuseStep 4840879 = 7261319) B7261319
theorem B6454505 : Blo 1885435 6454505 := bstep (se 2 (by rfl) ⟨2420439, by rfl⟩ : syracuseStep 6454505 = 4840879) B4840879
theorem B4303003 : Blo 1885435 4303003 := bstep (se 1 (by rfl) ⟨3227252, by rfl⟩ : syracuseStep 4303003 = 6454505) B6454505
theorem B5737337 : Blo 1885435 5737337 := bstep (se 2 (by rfl) ⟨2151501, by rfl⟩ : syracuseStep 5737337 = 4303003) B4303003
theorem B3824891 : Blo 1885435 3824891 := bstep (se 1 (by rfl) ⟨2868668, by rfl⟩ : syracuseStep 3824891 = 5737337) B5737337
theorem B2549927 : Blo 1885435 2549927 := bstep (se 1 (by rfl) ⟨1912445, by rfl⟩ : syracuseStep 2549927 = 3824891) B3824891
theorem B6799805 : Blo 1885435 6799805 := bstep (se 3 (by rfl) ⟨1274963, by rfl⟩ : syracuseStep 6799805 = 2549927) B2549927
theorem B4533203 : Blo 1885435 4533203 := bstep (se 1 (by rfl) ⟨3399902, by rfl⟩ : syracuseStep 4533203 = 6799805) B6799805
theorem B12088541 : Blo 1885435 12088541 := bstep (se 3 (by rfl) ⟨2266601, by rfl⟩ : syracuseStep 12088541 = 4533203) B4533203
theorem B8059027 : Blo 1885435 8059027 := bstep (se 1 (by rfl) ⟨6044270, by rfl⟩ : syracuseStep 8059027 = 12088541) B12088541
theorem B10745369 : Blo 1885435 10745369 := bstep (se 2 (by rfl) ⟨4029513, by rfl⟩ : syracuseStep 10745369 = 8059027) B8059027
theorem B7163579 : Blo 1885435 7163579 := bstep (se 1 (by rfl) ⟨5372684, by rfl⟩ : syracuseStep 7163579 = 10745369) B10745369
theorem B4775719 : Blo 1885435 4775719 := bstep (se 1 (by rfl) ⟨3581789, by rfl⟩ : syracuseStep 4775719 = 7163579) B7163579
theorem B6367625 : Blo 1885435 6367625 := bstep (se 2 (by rfl) ⟨2387859, by rfl⟩ : syracuseStep 6367625 = 4775719) B4775719
theorem B4245083 : Blo 1885435 4245083 := bstep (se 1 (by rfl) ⟨3183812, by rfl⟩ : syracuseStep 4245083 = 6367625) B6367625
theorem B2830055 : Blo 1885435 2830055 := bstep (se 1 (by rfl) ⟨2122541, by rfl⟩ : syracuseStep 2830055 = 4245083) B4245083
theorem B1886703 : Blo 1885435 1886703 := bstep (se 1 (by rfl) ⟨1415027, by rfl⟩ : syracuseStep 1886703 = 2830055) B2830055
theorem B2830061 : Blo 1885435 2830061 := bbase (se 3 (by rfl) ⟨530636, by rfl⟩ : syracuseStep 2830061 = 1061273) (by norm_num)
theorem B1886707 : Blo 1885435 1886707 := bstep (se 1 (by rfl) ⟨1415030, by rfl⟩ : syracuseStep 1886707 = 2830061) B2830061
theorem B4245101 : Blo 1885435 4245101 := bbase (se 3 (by rfl) ⟨795956, by rfl⟩ : syracuseStep 4245101 = 1591913) (by norm_num)
theorem B2830067 : Blo 1885435 2830067 := bstep (se 1 (by rfl) ⟨2122550, by rfl⟩ : syracuseStep 2830067 = 4245101) B4245101
theorem B1886711 : Blo 1885435 1886711 := bstep (se 1 (by rfl) ⟨1415033, by rfl⟩ : syracuseStep 1886711 = 2830067) B2830067
theorem B3581813 : Blo 1885435 3581813 := bbase (se 5 (by rfl) ⟨167897, by rfl⟩ : syracuseStep 3581813 = 335795) (by norm_num)
theorem B2387875 : Blo 1885435 2387875 := bstep (se 1 (by rfl) ⟨1790906, by rfl⟩ : syracuseStep 2387875 = 3581813) B3581813
theorem B3183833 : Blo 1885435 3183833 := bstep (se 2 (by rfl) ⟨1193937, by rfl⟩ : syracuseStep 3183833 = 2387875) B2387875
theorem B2122555 : Blo 1885435 2122555 := bstep (se 1 (by rfl) ⟨1591916, by rfl⟩ : syracuseStep 2122555 = 3183833) B3183833
theorem B2830073 : Blo 1885435 2830073 := bstep (se 2 (by rfl) ⟨1061277, by rfl⟩ : syracuseStep 2830073 = 2122555) B2122555
theorem B1886715 : Blo 1885435 1886715 := bstep (se 1 (by rfl) ⟨1415036, by rfl⟩ : syracuseStep 1886715 = 2830073) B2830073
theorem B3315941 : Blo 1885435 3315941 := bbase (se 4 (by rfl) ⟨310869, by rfl⟩ : syracuseStep 3315941 = 621739) (by norm_num)
theorem B2210627 : Blo 1885435 2210627 := bstep (se 1 (by rfl) ⟨1657970, by rfl⟩ : syracuseStep 2210627 = 3315941) B3315941
theorem B5895005 : Blo 1885435 5895005 := bstep (se 3 (by rfl) ⟨1105313, by rfl⟩ : syracuseStep 5895005 = 2210627) B2210627
theorem B15720013 : Blo 1885435 15720013 := bstep (se 3 (by rfl) ⟨2947502, by rfl⟩ : syracuseStep 15720013 = 5895005) B5895005
theorem B20960017 : Blo 1885435 20960017 := bstep (se 2 (by rfl) ⟨7860006, by rfl⟩ : syracuseStep 20960017 = 15720013) B15720013
theorem B447147029 : Blo 1885435 447147029 := bstep (se 6 (by rfl) ⟨10480008, by rfl⟩ : syracuseStep 447147029 = 20960017) B20960017
theorem B298098019 : Blo 1885435 298098019 := bstep (se 1 (by rfl) ⟨223573514, by rfl⟩ : syracuseStep 298098019 = 447147029) B447147029
theorem B397464025 : Blo 1885435 397464025 := bstep (se 2 (by rfl) ⟨149049009, by rfl⟩ : syracuseStep 397464025 = 298098019) B298098019
theorem B529952033 : Blo 1885435 529952033 := bstep (se 2 (by rfl) ⟨198732012, by rfl⟩ : syracuseStep 529952033 = 397464025) B397464025
theorem B353301355 : Blo 1885435 353301355 := bstep (se 1 (by rfl) ⟨264976016, by rfl⟩ : syracuseStep 353301355 = 529952033) B529952033
theorem B471068473 : Blo 1885435 471068473 := bstep (se 2 (by rfl) ⟨176650677, by rfl⟩ : syracuseStep 471068473 = 353301355) B353301355
theorem B628091297 : Blo 1885435 628091297 := bstep (se 2 (by rfl) ⟨235534236, by rfl⟩ : syracuseStep 628091297 = 471068473) B471068473
theorem B418727531 : Blo 1885435 418727531 := bstep (se 1 (by rfl) ⟨314045648, by rfl⟩ : syracuseStep 418727531 = 628091297) B628091297
theorem B279151687 : Blo 1885435 279151687 := bstep (se 1 (by rfl) ⟨209363765, by rfl⟩ : syracuseStep 279151687 = 418727531) B418727531
theorem B372202249 : Blo 1885435 372202249 := bstep (se 2 (by rfl) ⟨139575843, by rfl⟩ : syracuseStep 372202249 = 279151687) B279151687
theorem B496269665 : Blo 1885435 496269665 := bstep (se 2 (by rfl) ⟨186101124, by rfl⟩ : syracuseStep 496269665 = 372202249) B372202249
theorem B330846443 : Blo 1885435 330846443 := bstep (se 1 (by rfl) ⟨248134832, by rfl⟩ : syracuseStep 330846443 = 496269665) B496269665
theorem B220564295 : Blo 1885435 220564295 := bstep (se 1 (by rfl) ⟨165423221, by rfl⟩ : syracuseStep 220564295 = 330846443) B330846443
theorem B147042863 : Blo 1885435 147042863 := bstep (se 1 (by rfl) ⟨110282147, by rfl⟩ : syracuseStep 147042863 = 220564295) B220564295
theorem B98028575 : Blo 1885435 98028575 := bstep (se 1 (by rfl) ⟨73521431, by rfl⟩ : syracuseStep 98028575 = 147042863) B147042863
theorem B65352383 : Blo 1885435 65352383 := bstep (se 1 (by rfl) ⟨49014287, by rfl⟩ : syracuseStep 65352383 = 98028575) B98028575
theorem B43568255 : Blo 1885435 43568255 := bstep (se 1 (by rfl) ⟨32676191, by rfl⟩ : syracuseStep 43568255 = 65352383) B65352383
theorem B29045503 : Blo 1885435 29045503 := bstep (se 1 (by rfl) ⟨21784127, by rfl⟩ : syracuseStep 29045503 = 43568255) B43568255
theorem B38727337 : Blo 1885435 38727337 := bstep (se 2 (by rfl) ⟨14522751, by rfl⟩ : syracuseStep 38727337 = 29045503) B29045503
theorem B51636449 : Blo 1885435 51636449 := bstep (se 2 (by rfl) ⟨19363668, by rfl⟩ : syracuseStep 51636449 = 38727337) B38727337
theorem B34424299 : Blo 1885435 34424299 := bstep (se 1 (by rfl) ⟨25818224, by rfl⟩ : syracuseStep 34424299 = 51636449) B51636449
theorem B45899065 : Blo 1885435 45899065 := bstep (se 2 (by rfl) ⟨17212149, by rfl⟩ : syracuseStep 45899065 = 34424299) B34424299
theorem B61198753 : Blo 1885435 61198753 := bstep (se 2 (by rfl) ⟨22949532, by rfl⟩ : syracuseStep 61198753 = 45899065) B45899065
theorem B81598337 : Blo 1885435 81598337 := bstep (se 2 (by rfl) ⟨30599376, by rfl⟩ : syracuseStep 81598337 = 61198753) B61198753
theorem B54398891 : Blo 1885435 54398891 := bstep (se 1 (by rfl) ⟨40799168, by rfl⟩ : syracuseStep 54398891 = 81598337) B81598337
theorem B36265927 : Blo 1885435 36265927 := bstep (se 1 (by rfl) ⟨27199445, by rfl⟩ : syracuseStep 36265927 = 54398891) B54398891
theorem B48354569 : Blo 1885435 48354569 := bstep (se 2 (by rfl) ⟨18132963, by rfl⟩ : syracuseStep 48354569 = 36265927) B36265927
theorem B32236379 : Blo 1885435 32236379 := bstep (se 1 (by rfl) ⟨24177284, by rfl⟩ : syracuseStep 32236379 = 48354569) B48354569
theorem B21490919 : Blo 1885435 21490919 := bstep (se 1 (by rfl) ⟨16118189, by rfl⟩ : syracuseStep 21490919 = 32236379) B32236379
theorem B14327279 : Blo 1885435 14327279 := bstep (se 1 (by rfl) ⟨10745459, by rfl⟩ : syracuseStep 14327279 = 21490919) B21490919
theorem B9551519 : Blo 1885435 9551519 := bstep (se 1 (by rfl) ⟨7163639, by rfl⟩ : syracuseStep 9551519 = 14327279) B14327279
theorem B6367679 : Blo 1885435 6367679 := bstep (se 1 (by rfl) ⟨4775759, by rfl⟩ : syracuseStep 6367679 = 9551519) B9551519
theorem B4245119 : Blo 1885435 4245119 := bstep (se 1 (by rfl) ⟨3183839, by rfl⟩ : syracuseStep 4245119 = 6367679) B6367679
theorem B2830079 : Blo 1885435 2830079 := bstep (se 1 (by rfl) ⟨2122559, by rfl⟩ : syracuseStep 2830079 = 4245119) B4245119
theorem B1886719 : Blo 1885435 1886719 := bstep (se 1 (by rfl) ⟨1415039, by rfl⟩ : syracuseStep 1886719 = 2830079) B2830079
theorem B2830085 : Blo 1885435 2830085 := bbase (se 4 (by rfl) ⟨265320, by rfl⟩ : syracuseStep 2830085 = 530641) (by norm_num)
theorem B1886723 : Blo 1885435 1886723 := bstep (se 1 (by rfl) ⟨1415042, by rfl⟩ : syracuseStep 1886723 = 2830085) B2830085
theorem B3183853 : Blo 1885435 3183853 := bbase (se 3 (by rfl) ⟨596972, by rfl⟩ : syracuseStep 3183853 = 1193945) (by norm_num)
theorem B4245137 : Blo 1885435 4245137 := bstep (se 2 (by rfl) ⟨1591926, by rfl⟩ : syracuseStep 4245137 = 3183853) B3183853
theorem B2830091 : Blo 1885435 2830091 := bstep (se 1 (by rfl) ⟨2122568, by rfl⟩ : syracuseStep 2830091 = 4245137) B4245137
theorem B1886727 : Blo 1885435 1886727 := bstep (se 1 (by rfl) ⟨1415045, by rfl⟩ : syracuseStep 1886727 = 2830091) B2830091
theorem B2122573 : Blo 1885435 2122573 := bbase (se 3 (by rfl) ⟨397982, by rfl⟩ : syracuseStep 2122573 = 795965) (by norm_num)
theorem B2830097 : Blo 1885435 2830097 := bstep (se 2 (by rfl) ⟨1061286, by rfl⟩ : syracuseStep 2830097 = 2122573) B2122573
theorem B1886731 : Blo 1885435 1886731 := bstep (se 1 (by rfl) ⟨1415048, by rfl⟩ : syracuseStep 1886731 = 2830097) B2830097
theorem B6367733 : Blo 1885435 6367733 := bbase (se 5 (by rfl) ⟨298487, by rfl⟩ : syracuseStep 6367733 = 596975) (by norm_num)
theorem B4245155 : Blo 1885435 4245155 := bstep (se 1 (by rfl) ⟨3183866, by rfl⟩ : syracuseStep 4245155 = 6367733) B6367733
theorem B2830103 : Blo 1885435 2830103 := bstep (se 1 (by rfl) ⟨2122577, by rfl⟩ : syracuseStep 2830103 = 4245155) B4245155
theorem B1886735 : Blo 1885435 1886735 := bstep (se 1 (by rfl) ⟨1415051, by rfl⟩ : syracuseStep 1886735 = 2830103) B2830103
theorem B2830109 : Blo 1885435 2830109 := bbase (se 3 (by rfl) ⟨530645, by rfl⟩ : syracuseStep 2830109 = 1061291) (by norm_num)
theorem B1886739 : Blo 1885435 1886739 := bstep (se 1 (by rfl) ⟨1415054, by rfl⟩ : syracuseStep 1886739 = 2830109) B2830109
theorem B4245173 : Blo 1885435 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B2830115 : Blo 1885435 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B1886743 : Blo 1885435 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B10745621 : Blo 1885435 10745621 := bbase (se 6 (by rfl) ⟨251850, by rfl⟩ : syracuseStep 10745621 = 503701) (by norm_num)
theorem B7163747 : Blo 1885435 7163747 := bstep (se 1 (by rfl) ⟨5372810, by rfl⟩ : syracuseStep 7163747 = 10745621) B10745621
theorem B4775831 : Blo 1885435 4775831 := bstep (se 1 (by rfl) ⟨3581873, by rfl⟩ : syracuseStep 4775831 = 7163747) B7163747
theorem B3183887 : Blo 1885435 3183887 := bstep (se 1 (by rfl) ⟨2387915, by rfl⟩ : syracuseStep 3183887 = 4775831) B4775831
theorem B2122591 : Blo 1885435 2122591 := bstep (se 1 (by rfl) ⟨1591943, by rfl⟩ : syracuseStep 2122591 = 3183887) B3183887
theorem B2830121 : Blo 1885435 2830121 := bstep (se 2 (by rfl) ⟨1061295, by rfl⟩ : syracuseStep 2830121 = 2122591) B2122591
theorem B1886747 : Blo 1885435 1886747 := bstep (se 1 (by rfl) ⟨1415060, by rfl⟩ : syracuseStep 1886747 = 2830121) B2830121
theorem B5372821 : Blo 1885435 5372821 := bbase (se 6 (by rfl) ⟨125925, by rfl⟩ : syracuseStep 5372821 = 251851) (by norm_num)
theorem B7163761 : Blo 1885435 7163761 := bstep (se 2 (by rfl) ⟨2686410, by rfl⟩ : syracuseStep 7163761 = 5372821) B5372821
theorem B9551681 : Blo 1885435 9551681 := bstep (se 2 (by rfl) ⟨3581880, by rfl⟩ : syracuseStep 9551681 = 7163761) B7163761
theorem B6367787 : Blo 1885435 6367787 := bstep (se 1 (by rfl) ⟨4775840, by rfl⟩ : syracuseStep 6367787 = 9551681) B9551681
theorem B4245191 : Blo 1885435 4245191 := bstep (se 1 (by rfl) ⟨3183893, by rfl⟩ : syracuseStep 4245191 = 6367787) B6367787
theorem B2830127 : Blo 1885435 2830127 := bstep (se 1 (by rfl) ⟨2122595, by rfl⟩ : syracuseStep 2830127 = 4245191) B4245191
theorem B1886751 : Blo 1885435 1886751 := bstep (se 1 (by rfl) ⟨1415063, by rfl⟩ : syracuseStep 1886751 = 2830127) B2830127
theorem B2830133 : Blo 1885435 2830133 := bbase (se 5 (by rfl) ⟨132662, by rfl⟩ : syracuseStep 2830133 = 265325) (by norm_num)
theorem B1886755 : Blo 1885435 1886755 := bstep (se 1 (by rfl) ⟨1415066, by rfl⟩ : syracuseStep 1886755 = 2830133) B2830133
theorem B4775861 : Blo 1885435 4775861 := bbase (se 5 (by rfl) ⟨223868, by rfl⟩ : syracuseStep 4775861 = 447737) (by norm_num)
theorem B3183907 : Blo 1885435 3183907 := bstep (se 1 (by rfl) ⟨2387930, by rfl⟩ : syracuseStep 3183907 = 4775861) B4775861
theorem B4245209 : Blo 1885435 4245209 := bstep (se 2 (by rfl) ⟨1591953, by rfl⟩ : syracuseStep 4245209 = 3183907) B3183907
theorem B2830139 : Blo 1885435 2830139 := bstep (se 1 (by rfl) ⟨2122604, by rfl⟩ : syracuseStep 2830139 = 4245209) B4245209
theorem B1886759 : Blo 1885435 1886759 := bstep (se 1 (by rfl) ⟨1415069, by rfl⟩ : syracuseStep 1886759 = 2830139) B2830139
theorem B2122609 : Blo 1885435 2122609 := bbase (se 2 (by rfl) ⟨795978, by rfl⟩ : syracuseStep 2122609 = 1591957) (by norm_num)
theorem B2830145 : Blo 1885435 2830145 := bstep (se 2 (by rfl) ⟨1061304, by rfl⟩ : syracuseStep 2830145 = 2122609) B2122609
theorem B1886763 : Blo 1885435 1886763 := bstep (se 1 (by rfl) ⟨1415072, by rfl⟩ : syracuseStep 1886763 = 2830145) B2830145
theorem B8059301 : Blo 1885435 8059301 := bbase (se 4 (by rfl) ⟨755559, by rfl⟩ : syracuseStep 8059301 = 1511119) (by norm_num)
theorem B5372867 : Blo 1885435 5372867 := bstep (se 1 (by rfl) ⟨4029650, by rfl⟩ : syracuseStep 5372867 = 8059301) B8059301
theorem B3581911 : Blo 1885435 3581911 := bstep (se 1 (by rfl) ⟨2686433, by rfl⟩ : syracuseStep 3581911 = 5372867) B5372867
theorem B4775881 : Blo 1885435 4775881 := bstep (se 2 (by rfl) ⟨1790955, by rfl⟩ : syracuseStep 4775881 = 3581911) B3581911
theorem B6367841 : Blo 1885435 6367841 := bstep (se 2 (by rfl) ⟨2387940, by rfl⟩ : syracuseStep 6367841 = 4775881) B4775881
theorem B4245227 : Blo 1885435 4245227 := bstep (se 1 (by rfl) ⟨3183920, by rfl⟩ : syracuseStep 4245227 = 6367841) B6367841
theorem B2830151 : Blo 1885435 2830151 := bstep (se 1 (by rfl) ⟨2122613, by rfl⟩ : syracuseStep 2830151 = 4245227) B4245227
theorem B1886767 : Blo 1885435 1886767 := bstep (se 1 (by rfl) ⟨1415075, by rfl⟩ : syracuseStep 1886767 = 2830151) B2830151
theorem B2830157 : Blo 1885435 2830157 := bbase (se 3 (by rfl) ⟨530654, by rfl⟩ : syracuseStep 2830157 = 1061309) (by norm_num)
theorem B1886771 : Blo 1885435 1886771 := bstep (se 1 (by rfl) ⟨1415078, by rfl⟩ : syracuseStep 1886771 = 2830157) B2830157
theorem B4245245 : Blo 1885435 4245245 := bbase (se 3 (by rfl) ⟨795983, by rfl⟩ : syracuseStep 4245245 = 1591967) (by norm_num)
theorem B2830163 : Blo 1885435 2830163 := bstep (se 1 (by rfl) ⟨2122622, by rfl⟩ : syracuseStep 2830163 = 4245245) B4245245
theorem B1886775 : Blo 1885435 1886775 := bstep (se 1 (by rfl) ⟨1415081, by rfl⟩ : syracuseStep 1886775 = 2830163) B2830163
theorem B3183941 : Blo 1885435 3183941 := bbase (se 4 (by rfl) ⟨298494, by rfl⟩ : syracuseStep 3183941 = 596989) (by norm_num)
theorem B2122627 : Blo 1885435 2122627 := bstep (se 1 (by rfl) ⟨1591970, by rfl⟩ : syracuseStep 2122627 = 3183941) B3183941
theorem B2830169 : Blo 1885435 2830169 := bstep (se 2 (by rfl) ⟨1061313, by rfl⟩ : syracuseStep 2830169 = 2122627) B2122627
theorem B1886779 : Blo 1885435 1886779 := bstep (se 1 (by rfl) ⟨1415084, by rfl⟩ : syracuseStep 1886779 = 2830169) B2830169
theorem B14327765 : Blo 1885435 14327765 := bbase (se 7 (by rfl) ⟨167903, by rfl⟩ : syracuseStep 14327765 = 335807) (by norm_num)
theorem B9551843 : Blo 1885435 9551843 := bstep (se 1 (by rfl) ⟨7163882, by rfl⟩ : syracuseStep 9551843 = 14327765) B14327765
theorem B6367895 : Blo 1885435 6367895 := bstep (se 1 (by rfl) ⟨4775921, by rfl⟩ : syracuseStep 6367895 = 9551843) B9551843
theorem B4245263 : Blo 1885435 4245263 := bstep (se 1 (by rfl) ⟨3183947, by rfl⟩ : syracuseStep 4245263 = 6367895) B6367895
theorem B2830175 : Blo 1885435 2830175 := bstep (se 1 (by rfl) ⟨2122631, by rfl⟩ : syracuseStep 2830175 = 4245263) B4245263
theorem B1886783 : Blo 1885435 1886783 := bstep (se 1 (by rfl) ⟨1415087, by rfl⟩ : syracuseStep 1886783 = 2830175) B2830175
theorem B2830181 : Blo 1885435 2830181 := bbase (se 4 (by rfl) ⟨265329, by rfl⟩ : syracuseStep 2830181 = 530659) (by norm_num)
theorem B1886787 : Blo 1885435 1886787 := bstep (se 1 (by rfl) ⟨1415090, by rfl⟩ : syracuseStep 1886787 = 2830181) B2830181
theorem B3581957 : Blo 1885435 3581957 := bbase (se 4 (by rfl) ⟨335808, by rfl⟩ : syracuseStep 3581957 = 671617) (by norm_num)
theorem B2387971 : Blo 1885435 2387971 := bstep (se 1 (by rfl) ⟨1790978, by rfl⟩ : syracuseStep 2387971 = 3581957) B3581957
theorem B3183961 : Blo 1885435 3183961 := bstep (se 2 (by rfl) ⟨1193985, by rfl⟩ : syracuseStep 3183961 = 2387971) B2387971
theorem B4245281 : Blo 1885435 4245281 := bstep (se 2 (by rfl) ⟨1591980, by rfl⟩ : syracuseStep 4245281 = 3183961) B3183961
theorem B2830187 : Blo 1885435 2830187 := bstep (se 1 (by rfl) ⟨2122640, by rfl⟩ : syracuseStep 2830187 = 4245281) B4245281
theorem B1886791 : Blo 1885435 1886791 := bstep (se 1 (by rfl) ⟨1415093, by rfl⟩ : syracuseStep 1886791 = 2830187) B2830187
theorem B2122645 : Blo 1885435 2122645 := bbase (se 6 (by rfl) ⟨49749, by rfl⟩ : syracuseStep 2122645 = 99499) (by norm_num)
theorem B2830193 : Blo 1885435 2830193 := bstep (se 2 (by rfl) ⟨1061322, by rfl⟩ : syracuseStep 2830193 = 2122645) B2122645
theorem B1886795 : Blo 1885435 1886795 := bstep (se 1 (by rfl) ⟨1415096, by rfl⟩ : syracuseStep 1886795 = 2830193) B2830193
theorem B2387981 : Blo 1885435 2387981 := bbase (se 3 (by rfl) ⟨447746, by rfl⟩ : syracuseStep 2387981 = 895493) (by norm_num)
theorem B6367949 : Blo 1885435 6367949 := bstep (se 3 (by rfl) ⟨1193990, by rfl⟩ : syracuseStep 6367949 = 2387981) B2387981
theorem B4245299 : Blo 1885435 4245299 := bstep (se 1 (by rfl) ⟨3183974, by rfl⟩ : syracuseStep 4245299 = 6367949) B6367949
theorem B2830199 : Blo 1885435 2830199 := bstep (se 1 (by rfl) ⟨2122649, by rfl⟩ : syracuseStep 2830199 = 4245299) B4245299
theorem B1886799 : Blo 1885435 1886799 := bstep (se 1 (by rfl) ⟨1415099, by rfl⟩ : syracuseStep 1886799 = 2830199) B2830199
theorem B2830205 : Blo 1885435 2830205 := bbase (se 3 (by rfl) ⟨530663, by rfl⟩ : syracuseStep 2830205 = 1061327) (by norm_num)
theorem B1886803 : Blo 1885435 1886803 := bstep (se 1 (by rfl) ⟨1415102, by rfl⟩ : syracuseStep 1886803 = 2830205) B2830205
theorem B4245317 : Blo 1885435 4245317 := bbase (se 4 (by rfl) ⟨397998, by rfl⟩ : syracuseStep 4245317 = 795997) (by norm_num)
theorem B2830211 : Blo 1885435 2830211 := bstep (se 1 (by rfl) ⟨2122658, by rfl⟩ : syracuseStep 2830211 = 4245317) B4245317
theorem B1886807 : Blo 1885435 1886807 := bstep (se 1 (by rfl) ⟨1415105, by rfl⟩ : syracuseStep 1886807 = 2830211) B2830211
theorem B3022309 : Blo 1885435 3022309 := bbase (se 4 (by rfl) ⟨283341, by rfl⟩ : syracuseStep 3022309 = 566683) (by norm_num)
theorem B4029745 : Blo 1885435 4029745 := bstep (se 2 (by rfl) ⟨1511154, by rfl⟩ : syracuseStep 4029745 = 3022309) B3022309
theorem B5372993 : Blo 1885435 5372993 := bstep (se 2 (by rfl) ⟨2014872, by rfl⟩ : syracuseStep 5372993 = 4029745) B4029745
theorem B3581995 : Blo 1885435 3581995 := bstep (se 1 (by rfl) ⟨2686496, by rfl⟩ : syracuseStep 3581995 = 5372993) B5372993
theorem B4775993 : Blo 1885435 4775993 := bstep (se 2 (by rfl) ⟨1790997, by rfl⟩ : syracuseStep 4775993 = 3581995) B3581995
theorem B3183995 : Blo 1885435 3183995 := bstep (se 1 (by rfl) ⟨2387996, by rfl⟩ : syracuseStep 3183995 = 4775993) B4775993
theorem B2122663 : Blo 1885435 2122663 := bstep (se 1 (by rfl) ⟨1591997, by rfl⟩ : syracuseStep 2122663 = 3183995) B3183995
theorem B2830217 : Blo 1885435 2830217 := bstep (se 2 (by rfl) ⟨1061331, by rfl⟩ : syracuseStep 2830217 = 2122663) B2122663
theorem B1886811 : Blo 1885435 1886811 := bstep (se 1 (by rfl) ⟨1415108, by rfl⟩ : syracuseStep 1886811 = 2830217) B2830217
theorem B9552005 : Blo 1885435 9552005 := bbase (se 4 (by rfl) ⟨895500, by rfl⟩ : syracuseStep 9552005 = 1791001) (by norm_num)
theorem B6368003 : Blo 1885435 6368003 := bstep (se 1 (by rfl) ⟨4776002, by rfl⟩ : syracuseStep 6368003 = 9552005) B9552005
theorem B4245335 : Blo 1885435 4245335 := bstep (se 1 (by rfl) ⟨3184001, by rfl⟩ : syracuseStep 4245335 = 6368003) B6368003
theorem B2830223 : Blo 1885435 2830223 := bstep (se 1 (by rfl) ⟨2122667, by rfl⟩ : syracuseStep 2830223 = 4245335) B4245335
theorem B1886815 : Blo 1885435 1886815 := bstep (se 1 (by rfl) ⟨1415111, by rfl⟩ : syracuseStep 1886815 = 2830223) B2830223
theorem B2830229 : Blo 1885435 2830229 := bbase (se 6 (by rfl) ⟨66333, by rfl⟩ : syracuseStep 2830229 = 132667) (by norm_num)
theorem B1886819 : Blo 1885435 1886819 := bstep (se 1 (by rfl) ⟨1415114, by rfl⟩ : syracuseStep 1886819 = 2830229) B2830229
theorem B2014885 : Blo 1885435 2014885 := bbase (se 4 (by rfl) ⟨188895, by rfl⟩ : syracuseStep 2014885 = 377791) (by norm_num)
theorem B10746053 : Blo 1885435 10746053 := bstep (se 4 (by rfl) ⟨1007442, by rfl⟩ : syracuseStep 10746053 = 2014885) B2014885
theorem B7164035 : Blo 1885435 7164035 := bstep (se 1 (by rfl) ⟨5373026, by rfl⟩ : syracuseStep 7164035 = 10746053) B10746053
theorem B4776023 : Blo 1885435 4776023 := bstep (se 1 (by rfl) ⟨3582017, by rfl⟩ : syracuseStep 4776023 = 7164035) B7164035
theorem B3184015 : Blo 1885435 3184015 := bstep (se 1 (by rfl) ⟨2388011, by rfl⟩ : syracuseStep 3184015 = 4776023) B4776023
theorem B4245353 : Blo 1885435 4245353 := bstep (se 2 (by rfl) ⟨1592007, by rfl⟩ : syracuseStep 4245353 = 3184015) B3184015
theorem B2830235 : Blo 1885435 2830235 := bstep (se 1 (by rfl) ⟨2122676, by rfl⟩ : syracuseStep 2830235 = 4245353) B4245353
theorem B1886823 : Blo 1885435 1886823 := bstep (se 1 (by rfl) ⟨1415117, by rfl⟩ : syracuseStep 1886823 = 2830235) B2830235
theorem B2122681 : Blo 1885435 2122681 := bbase (se 2 (by rfl) ⟨796005, by rfl⟩ : syracuseStep 2122681 = 1592011) (by norm_num)
theorem B2830241 : Blo 1885435 2830241 := bstep (se 2 (by rfl) ⟨1061340, by rfl⟩ : syracuseStep 2830241 = 2122681) B2122681
theorem B1886827 : Blo 1885435 1886827 := bstep (se 1 (by rfl) ⟨1415120, by rfl⟩ : syracuseStep 1886827 = 2830241) B2830241
theorem B9814517 : Blo 1885435 9814517 := bbase (se 5 (by rfl) ⟨460055, by rfl⟩ : syracuseStep 9814517 = 920111) (by norm_num)
theorem B6543011 : Blo 1885435 6543011 := bstep (se 1 (by rfl) ⟨4907258, by rfl⟩ : syracuseStep 6543011 = 9814517) B9814517
theorem B17448029 : Blo 1885435 17448029 := bstep (se 3 (by rfl) ⟨3271505, by rfl⟩ : syracuseStep 17448029 = 6543011) B6543011
theorem B11632019 : Blo 1885435 11632019 := bstep (se 1 (by rfl) ⟨8724014, by rfl⟩ : syracuseStep 11632019 = 17448029) B17448029
theorem B31018717 : Blo 1885435 31018717 := bstep (se 3 (by rfl) ⟨5816009, by rfl⟩ : syracuseStep 31018717 = 11632019) B11632019
theorem B41358289 : Blo 1885435 41358289 := bstep (se 2 (by rfl) ⟨15509358, by rfl⟩ : syracuseStep 41358289 = 31018717) B31018717
theorem B55144385 : Blo 1885435 55144385 := bstep (se 2 (by rfl) ⟨20679144, by rfl⟩ : syracuseStep 55144385 = 41358289) B41358289
theorem B36762923 : Blo 1885435 36762923 := bstep (se 1 (by rfl) ⟨27572192, by rfl⟩ : syracuseStep 36762923 = 55144385) B55144385
theorem B24508615 : Blo 1885435 24508615 := bstep (se 1 (by rfl) ⟨18381461, by rfl⟩ : syracuseStep 24508615 = 36762923) B36762923
theorem B32678153 : Blo 1885435 32678153 := bstep (se 2 (by rfl) ⟨12254307, by rfl⟩ : syracuseStep 32678153 = 24508615) B24508615
theorem B21785435 : Blo 1885435 21785435 := bstep (se 1 (by rfl) ⟨16339076, by rfl⟩ : syracuseStep 21785435 = 32678153) B32678153
theorem B14523623 : Blo 1885435 14523623 := bstep (se 1 (by rfl) ⟨10892717, by rfl⟩ : syracuseStep 14523623 = 21785435) B21785435
theorem B9682415 : Blo 1885435 9682415 := bstep (se 1 (by rfl) ⟨7261811, by rfl⟩ : syracuseStep 9682415 = 14523623) B14523623
theorem B6454943 : Blo 1885435 6454943 := bstep (se 1 (by rfl) ⟨4841207, by rfl⟩ : syracuseStep 6454943 = 9682415) B9682415
theorem B4303295 : Blo 1885435 4303295 := bstep (se 1 (by rfl) ⟨3227471, by rfl⟩ : syracuseStep 4303295 = 6454943) B6454943
theorem B2868863 : Blo 1885435 2868863 := bstep (se 1 (by rfl) ⟨2151647, by rfl⟩ : syracuseStep 2868863 = 4303295) B4303295
theorem B7650301 : Blo 1885435 7650301 := bstep (se 3 (by rfl) ⟨1434431, by rfl⟩ : syracuseStep 7650301 = 2868863) B2868863
theorem B10200401 : Blo 1885435 10200401 := bstep (se 2 (by rfl) ⟨3825150, by rfl⟩ : syracuseStep 10200401 = 7650301) B7650301
theorem B6800267 : Blo 1885435 6800267 := bstep (se 1 (by rfl) ⟨5100200, by rfl⟩ : syracuseStep 6800267 = 10200401) B10200401
theorem B4533511 : Blo 1885435 4533511 := bstep (se 1 (by rfl) ⟨3400133, by rfl⟩ : syracuseStep 4533511 = 6800267) B6800267
theorem B6044681 : Blo 1885435 6044681 := bstep (se 2 (by rfl) ⟨2266755, by rfl⟩ : syracuseStep 6044681 = 4533511) B4533511
theorem B4029787 : Blo 1885435 4029787 := bstep (se 1 (by rfl) ⟨3022340, by rfl⟩ : syracuseStep 4029787 = 6044681) B6044681
theorem B5373049 : Blo 1885435 5373049 := bstep (se 2 (by rfl) ⟨2014893, by rfl⟩ : syracuseStep 5373049 = 4029787) B4029787
theorem B7164065 : Blo 1885435 7164065 := bstep (se 2 (by rfl) ⟨2686524, by rfl⟩ : syracuseStep 7164065 = 5373049) B5373049
theorem B4776043 : Blo 1885435 4776043 := bstep (se 1 (by rfl) ⟨3582032, by rfl⟩ : syracuseStep 4776043 = 7164065) B7164065
theorem B6368057 : Blo 1885435 6368057 := bstep (se 2 (by rfl) ⟨2388021, by rfl⟩ : syracuseStep 6368057 = 4776043) B4776043
theorem B4245371 : Blo 1885435 4245371 := bstep (se 1 (by rfl) ⟨3184028, by rfl⟩ : syracuseStep 4245371 = 6368057) B6368057
theorem B2830247 : Blo 1885435 2830247 := bstep (se 1 (by rfl) ⟨2122685, by rfl⟩ : syracuseStep 2830247 = 4245371) B4245371
theorem B1886831 : Blo 1885435 1886831 := bstep (se 1 (by rfl) ⟨1415123, by rfl⟩ : syracuseStep 1886831 = 2830247) B2830247
theorem B2830253 : Blo 1885435 2830253 := bbase (se 3 (by rfl) ⟨530672, by rfl⟩ : syracuseStep 2830253 = 1061345) (by norm_num)
theorem B1886835 : Blo 1885435 1886835 := bstep (se 1 (by rfl) ⟨1415126, by rfl⟩ : syracuseStep 1886835 = 2830253) B2830253
theorem B4245389 : Blo 1885435 4245389 := bbase (se 3 (by rfl) ⟨796010, by rfl⟩ : syracuseStep 4245389 = 1592021) (by norm_num)
theorem B2830259 : Blo 1885435 2830259 := bstep (se 1 (by rfl) ⟨2122694, by rfl⟩ : syracuseStep 2830259 = 4245389) B4245389
theorem B1886839 : Blo 1885435 1886839 := bstep (se 1 (by rfl) ⟨1415129, by rfl⟩ : syracuseStep 1886839 = 2830259) B2830259
theorem B2388037 : Blo 1885435 2388037 := bbase (se 4 (by rfl) ⟨223878, by rfl⟩ : syracuseStep 2388037 = 447757) (by norm_num)
theorem B3184049 : Blo 1885435 3184049 := bstep (se 2 (by rfl) ⟨1194018, by rfl⟩ : syracuseStep 3184049 = 2388037) B2388037
theorem B2122699 : Blo 1885435 2122699 := bstep (se 1 (by rfl) ⟨1592024, by rfl⟩ : syracuseStep 2122699 = 3184049) B3184049
theorem B2830265 : Blo 1885435 2830265 := bstep (se 2 (by rfl) ⟨1061349, by rfl⟩ : syracuseStep 2830265 = 2122699) B2122699
theorem B1886843 : Blo 1885435 1886843 := bstep (se 1 (by rfl) ⟨1415132, by rfl⟩ : syracuseStep 1886843 = 2830265) B2830265
theorem B6454997 : Blo 1885435 6454997 := bbase (se 7 (by rfl) ⟨75644, by rfl⟩ : syracuseStep 6454997 = 151289) (by norm_num)
theorem B4303331 : Blo 1885435 4303331 := bstep (se 1 (by rfl) ⟨3227498, by rfl⟩ : syracuseStep 4303331 = 6454997) B6454997
theorem B2868887 : Blo 1885435 2868887 := bstep (se 1 (by rfl) ⟨2151665, by rfl⟩ : syracuseStep 2868887 = 4303331) B4303331
theorem B1912591 : Blo 1885435 1912591 := bstep (se 1 (by rfl) ⟨1434443, by rfl⟩ : syracuseStep 1912591 = 2868887) B2868887
theorem B10200485 : Blo 1885435 10200485 := bstep (se 4 (by rfl) ⟨956295, by rfl⟩ : syracuseStep 10200485 = 1912591) B1912591
theorem B6800323 : Blo 1885435 6800323 := bstep (se 1 (by rfl) ⟨5100242, by rfl⟩ : syracuseStep 6800323 = 10200485) B10200485
theorem B9067097 : Blo 1885435 9067097 := bstep (se 2 (by rfl) ⟨3400161, by rfl⟩ : syracuseStep 9067097 = 6800323) B6800323
theorem B24178925 : Blo 1885435 24178925 := bstep (se 3 (by rfl) ⟨4533548, by rfl⟩ : syracuseStep 24178925 = 9067097) B9067097
theorem B16119283 : Blo 1885435 16119283 := bstep (se 1 (by rfl) ⟨12089462, by rfl⟩ : syracuseStep 16119283 = 24178925) B24178925
theorem B21492377 : Blo 1885435 21492377 := bstep (se 2 (by rfl) ⟨8059641, by rfl⟩ : syracuseStep 21492377 = 16119283) B16119283
theorem B14328251 : Blo 1885435 14328251 := bstep (se 1 (by rfl) ⟨10746188, by rfl⟩ : syracuseStep 14328251 = 21492377) B21492377
theorem B9552167 : Blo 1885435 9552167 := bstep (se 1 (by rfl) ⟨7164125, by rfl⟩ : syracuseStep 9552167 = 14328251) B14328251
theorem B6368111 : Blo 1885435 6368111 := bstep (se 1 (by rfl) ⟨4776083, by rfl⟩ : syracuseStep 6368111 = 9552167) B9552167
theorem B4245407 : Blo 1885435 4245407 := bstep (se 1 (by rfl) ⟨3184055, by rfl⟩ : syracuseStep 4245407 = 6368111) B6368111
theorem B2830271 : Blo 1885435 2830271 := bstep (se 1 (by rfl) ⟨2122703, by rfl⟩ : syracuseStep 2830271 = 4245407) B4245407
theorem B1886847 : Blo 1885435 1886847 := bstep (se 1 (by rfl) ⟨1415135, by rfl⟩ : syracuseStep 1886847 = 2830271) B2830271
theorem B2830277 : Blo 1885435 2830277 := bbase (se 4 (by rfl) ⟨265338, by rfl⟩ : syracuseStep 2830277 = 530677) (by norm_num)
theorem B1886851 : Blo 1885435 1886851 := bstep (se 1 (by rfl) ⟨1415138, by rfl⟩ : syracuseStep 1886851 = 2830277) B2830277
theorem B3184069 : Blo 1885435 3184069 := bbase (se 4 (by rfl) ⟨298506, by rfl⟩ : syracuseStep 3184069 = 597013) (by norm_num)
theorem B4245425 : Blo 1885435 4245425 := bstep (se 2 (by rfl) ⟨1592034, by rfl⟩ : syracuseStep 4245425 = 3184069) B3184069
theorem B2830283 : Blo 1885435 2830283 := bstep (se 1 (by rfl) ⟨2122712, by rfl⟩ : syracuseStep 2830283 = 4245425) B4245425
theorem B1886855 : Blo 1885435 1886855 := bstep (se 1 (by rfl) ⟨1415141, by rfl⟩ : syracuseStep 1886855 = 2830283) B2830283
theorem B2122717 : Blo 1885435 2122717 := bbase (se 3 (by rfl) ⟨398009, by rfl⟩ : syracuseStep 2122717 = 796019) (by norm_num)
theorem B2830289 : Blo 1885435 2830289 := bstep (se 2 (by rfl) ⟨1061358, by rfl⟩ : syracuseStep 2830289 = 2122717) B2122717
theorem B1886859 : Blo 1885435 1886859 := bstep (se 1 (by rfl) ⟨1415144, by rfl⟩ : syracuseStep 1886859 = 2830289) B2830289
theorem B6368165 : Blo 1885435 6368165 := bbase (se 4 (by rfl) ⟨597015, by rfl⟩ : syracuseStep 6368165 = 1194031) (by norm_num)
theorem B4245443 : Blo 1885435 4245443 := bstep (se 1 (by rfl) ⟨3184082, by rfl⟩ : syracuseStep 4245443 = 6368165) B6368165
theorem B2830295 : Blo 1885435 2830295 := bstep (se 1 (by rfl) ⟨2122721, by rfl⟩ : syracuseStep 2830295 = 4245443) B4245443
theorem B1886863 : Blo 1885435 1886863 := bstep (se 1 (by rfl) ⟨1415147, by rfl⟩ : syracuseStep 1886863 = 2830295) B2830295
theorem B2830301 : Blo 1885435 2830301 := bbase (se 3 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 2830301 = 1061363) (by norm_num)
theorem B1886867 : Blo 1885435 1886867 := bstep (se 1 (by rfl) ⟨1415150, by rfl⟩ : syracuseStep 1886867 = 2830301) B2830301
theorem B4245461 : Blo 1885435 4245461 := bbase (se 7 (by rfl) ⟨49751, by rfl⟩ : syracuseStep 4245461 = 99503) (by norm_num)
theorem B2830307 : Blo 1885435 2830307 := bstep (se 1 (by rfl) ⟨2122730, by rfl⟩ : syracuseStep 2830307 = 4245461) B4245461
theorem B1886871 : Blo 1885435 1886871 := bstep (se 1 (by rfl) ⟨1415153, by rfl⟩ : syracuseStep 1886871 = 2830307) B2830307
theorem B3400213 : Blo 1885435 3400213 := bbase (se 6 (by rfl) ⟨79692, by rfl⟩ : syracuseStep 3400213 = 159385) (by norm_num)
theorem B4533617 : Blo 1885435 4533617 := bstep (se 2 (by rfl) ⟨1700106, by rfl⟩ : syracuseStep 4533617 = 3400213) B3400213
theorem B12089645 : Blo 1885435 12089645 := bstep (se 3 (by rfl) ⟨2266808, by rfl⟩ : syracuseStep 12089645 = 4533617) B4533617
theorem B8059763 : Blo 1885435 8059763 := bstep (se 1 (by rfl) ⟨6044822, by rfl⟩ : syracuseStep 8059763 = 12089645) B12089645
theorem B5373175 : Blo 1885435 5373175 := bstep (se 1 (by rfl) ⟨4029881, by rfl⟩ : syracuseStep 5373175 = 8059763) B8059763
theorem B7164233 : Blo 1885435 7164233 := bstep (se 2 (by rfl) ⟨2686587, by rfl⟩ : syracuseStep 7164233 = 5373175) B5373175
theorem B4776155 : Blo 1885435 4776155 := bstep (se 1 (by rfl) ⟨3582116, by rfl⟩ : syracuseStep 4776155 = 7164233) B7164233
theorem B3184103 : Blo 1885435 3184103 := bstep (se 1 (by rfl) ⟨2388077, by rfl⟩ : syracuseStep 3184103 = 4776155) B4776155
theorem B2122735 : Blo 1885435 2122735 := bstep (se 1 (by rfl) ⟨1592051, by rfl⟩ : syracuseStep 2122735 = 3184103) B3184103
theorem B2830313 : Blo 1885435 2830313 := bstep (se 2 (by rfl) ⟨1061367, by rfl⟩ : syracuseStep 2830313 = 2122735) B2122735
theorem B1886875 : Blo 1885435 1886875 := bstep (se 1 (by rfl) ⟨1415156, by rfl⟩ : syracuseStep 1886875 = 2830313) B2830313
theorem B2266813 : Blo 1885435 2266813 := bbase (se 3 (by rfl) ⟨425027, by rfl⟩ : syracuseStep 2266813 = 850055) (by norm_num)
theorem B3022417 : Blo 1885435 3022417 := bstep (se 2 (by rfl) ⟨1133406, by rfl⟩ : syracuseStep 3022417 = 2266813) B2266813
theorem B16119557 : Blo 1885435 16119557 := bstep (se 4 (by rfl) ⟨1511208, by rfl⟩ : syracuseStep 16119557 = 3022417) B3022417
theorem B10746371 : Blo 1885435 10746371 := bstep (se 1 (by rfl) ⟨8059778, by rfl⟩ : syracuseStep 10746371 = 16119557) B16119557
theorem B7164247 : Blo 1885435 7164247 := bstep (se 1 (by rfl) ⟨5373185, by rfl⟩ : syracuseStep 7164247 = 10746371) B10746371
theorem B9552329 : Blo 1885435 9552329 := bstep (se 2 (by rfl) ⟨3582123, by rfl⟩ : syracuseStep 9552329 = 7164247) B7164247
theorem B6368219 : Blo 1885435 6368219 := bstep (se 1 (by rfl) ⟨4776164, by rfl⟩ : syracuseStep 6368219 = 9552329) B9552329
theorem B4245479 : Blo 1885435 4245479 := bstep (se 1 (by rfl) ⟨3184109, by rfl⟩ : syracuseStep 4245479 = 6368219) B6368219
theorem B2830319 : Blo 1885435 2830319 := bstep (se 1 (by rfl) ⟨2122739, by rfl⟩ : syracuseStep 2830319 = 4245479) B4245479
theorem B1886879 : Blo 1885435 1886879 := bstep (se 1 (by rfl) ⟨1415159, by rfl⟩ : syracuseStep 1886879 = 2830319) B2830319
theorem B2830325 : Blo 1885435 2830325 := bbase (se 5 (by rfl) ⟨132671, by rfl⟩ : syracuseStep 2830325 = 265343) (by norm_num)
theorem B1886883 : Blo 1885435 1886883 := bstep (se 1 (by rfl) ⟨1415162, by rfl⟩ : syracuseStep 1886883 = 2830325) B2830325
theorem B2868949 : Blo 1885435 2868949 := bbase (se 7 (by rfl) ⟨33620, by rfl⟩ : syracuseStep 2868949 = 67241) (by norm_num)
theorem B3825265 : Blo 1885435 3825265 := bstep (se 2 (by rfl) ⟨1434474, by rfl⟩ : syracuseStep 3825265 = 2868949) B2868949
theorem B5100353 : Blo 1885435 5100353 := bstep (se 2 (by rfl) ⟨1912632, by rfl⟩ : syracuseStep 5100353 = 3825265) B3825265
theorem B3400235 : Blo 1885435 3400235 := bstep (se 1 (by rfl) ⟨2550176, by rfl⟩ : syracuseStep 3400235 = 5100353) B5100353
theorem B2266823 : Blo 1885435 2266823 := bstep (se 1 (by rfl) ⟨1700117, by rfl⟩ : syracuseStep 2266823 = 3400235) B3400235
theorem B6044861 : Blo 1885435 6044861 := bstep (se 3 (by rfl) ⟨1133411, by rfl⟩ : syracuseStep 6044861 = 2266823) B2266823
theorem B4029907 : Blo 1885435 4029907 := bstep (se 1 (by rfl) ⟨3022430, by rfl⟩ : syracuseStep 4029907 = 6044861) B6044861
theorem B5373209 : Blo 1885435 5373209 := bstep (se 2 (by rfl) ⟨2014953, by rfl⟩ : syracuseStep 5373209 = 4029907) B4029907
theorem B3582139 : Blo 1885435 3582139 := bstep (se 1 (by rfl) ⟨2686604, by rfl⟩ : syracuseStep 3582139 = 5373209) B5373209
theorem B4776185 : Blo 1885435 4776185 := bstep (se 2 (by rfl) ⟨1791069, by rfl⟩ : syracuseStep 4776185 = 3582139) B3582139
theorem B3184123 : Blo 1885435 3184123 := bstep (se 1 (by rfl) ⟨2388092, by rfl⟩ : syracuseStep 3184123 = 4776185) B4776185
theorem B4245497 : Blo 1885435 4245497 := bstep (se 2 (by rfl) ⟨1592061, by rfl⟩ : syracuseStep 4245497 = 3184123) B3184123
theorem B2830331 : Blo 1885435 2830331 := bstep (se 1 (by rfl) ⟨2122748, by rfl⟩ : syracuseStep 2830331 = 4245497) B4245497
theorem B1886887 : Blo 1885435 1886887 := bstep (se 1 (by rfl) ⟨1415165, by rfl⟩ : syracuseStep 1886887 = 2830331) B2830331
theorem B2122753 : Blo 1885435 2122753 := bbase (se 2 (by rfl) ⟨796032, by rfl⟩ : syracuseStep 2122753 = 1592065) (by norm_num)
theorem B2830337 : Blo 1885435 2830337 := bstep (se 2 (by rfl) ⟨1061376, by rfl⟩ : syracuseStep 2830337 = 2122753) B2122753
theorem B1886891 : Blo 1885435 1886891 := bstep (se 1 (by rfl) ⟨1415168, by rfl⟩ : syracuseStep 1886891 = 2830337) B2830337
theorem B4776205 : Blo 1885435 4776205 := bbase (se 3 (by rfl) ⟨895538, by rfl⟩ : syracuseStep 4776205 = 1791077) (by norm_num)
theorem B6368273 : Blo 1885435 6368273 := bstep (se 2 (by rfl) ⟨2388102, by rfl⟩ : syracuseStep 6368273 = 4776205) B4776205
theorem B4245515 : Blo 1885435 4245515 := bstep (se 1 (by rfl) ⟨3184136, by rfl⟩ : syracuseStep 4245515 = 6368273) B6368273
theorem B2830343 : Blo 1885435 2830343 := bstep (se 1 (by rfl) ⟨2122757, by rfl⟩ : syracuseStep 2830343 = 4245515) B4245515
theorem B1886895 : Blo 1885435 1886895 := bstep (se 1 (by rfl) ⟨1415171, by rfl⟩ : syracuseStep 1886895 = 2830343) B2830343
theorem B2830349 : Blo 1885435 2830349 := bbase (se 3 (by rfl) ⟨530690, by rfl⟩ : syracuseStep 2830349 = 1061381) (by norm_num)
theorem B1886899 : Blo 1885435 1886899 := bstep (se 1 (by rfl) ⟨1415174, by rfl⟩ : syracuseStep 1886899 = 2830349) B2830349
theorem B4245533 : Blo 1885435 4245533 := bbase (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) (by norm_num)
theorem B2830355 : Blo 1885435 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B1886903 : Blo 1885435 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B3184157 : Blo 1885435 3184157 := bbase (se 3 (by rfl) ⟨597029, by rfl⟩ : syracuseStep 3184157 = 1194059) (by norm_num)
theorem B2122771 : Blo 1885435 2122771 := bstep (se 1 (by rfl) ⟨1592078, by rfl⟩ : syracuseStep 2122771 = 3184157) B3184157
theorem B2830361 : Blo 1885435 2830361 := bstep (se 2 (by rfl) ⟨1061385, by rfl⟩ : syracuseStep 2830361 = 2122771) B2122771
theorem B1886907 : Blo 1885435 1886907 := bstep (se 1 (by rfl) ⟨1415180, by rfl⟩ : syracuseStep 1886907 = 2830361) B2830361
theorem B3400277 : Blo 1885435 3400277 := bbase (se 8 (by rfl) ⟨19923, by rfl⟩ : syracuseStep 3400277 = 39847) (by norm_num)
theorem B9067405 : Blo 1885435 9067405 := bstep (se 3 (by rfl) ⟨1700138, by rfl⟩ : syracuseStep 9067405 = 3400277) B3400277
theorem B12089873 : Blo 1885435 12089873 := bstep (se 2 (by rfl) ⟨4533702, by rfl⟩ : syracuseStep 12089873 = 9067405) B9067405
theorem B8059915 : Blo 1885435 8059915 := bstep (se 1 (by rfl) ⟨6044936, by rfl⟩ : syracuseStep 8059915 = 12089873) B12089873
theorem B10746553 : Blo 1885435 10746553 := bstep (se 2 (by rfl) ⟨4029957, by rfl⟩ : syracuseStep 10746553 = 8059915) B8059915
theorem B14328737 : Blo 1885435 14328737 := bstep (se 2 (by rfl) ⟨5373276, by rfl⟩ : syracuseStep 14328737 = 10746553) B10746553
theorem B9552491 : Blo 1885435 9552491 := bstep (se 1 (by rfl) ⟨7164368, by rfl⟩ : syracuseStep 9552491 = 14328737) B14328737
theorem B6368327 : Blo 1885435 6368327 := bstep (se 1 (by rfl) ⟨4776245, by rfl⟩ : syracuseStep 6368327 = 9552491) B9552491
theorem B4245551 : Blo 1885435 4245551 := bstep (se 1 (by rfl) ⟨3184163, by rfl⟩ : syracuseStep 4245551 = 6368327) B6368327
theorem B2830367 : Blo 1885435 2830367 := bstep (se 1 (by rfl) ⟨2122775, by rfl⟩ : syracuseStep 2830367 = 4245551) B4245551
theorem B1886911 : Blo 1885435 1886911 := bstep (se 1 (by rfl) ⟨1415183, by rfl⟩ : syracuseStep 1886911 = 2830367) B2830367
theorem B2830373 : Blo 1885435 2830373 := bbase (se 4 (by rfl) ⟨265347, by rfl⟩ : syracuseStep 2830373 = 530695) (by norm_num)
theorem B1886915 : Blo 1885435 1886915 := bstep (se 1 (by rfl) ⟨1415186, by rfl⟩ : syracuseStep 1886915 = 2830373) B2830373
theorem B2388133 : Blo 1885435 2388133 := bbase (se 4 (by rfl) ⟨223887, by rfl⟩ : syracuseStep 2388133 = 447775) (by norm_num)
theorem B3184177 : Blo 1885435 3184177 := bstep (se 2 (by rfl) ⟨1194066, by rfl⟩ : syracuseStep 3184177 = 2388133) B2388133
theorem B4245569 : Blo 1885435 4245569 := bstep (se 2 (by rfl) ⟨1592088, by rfl⟩ : syracuseStep 4245569 = 3184177) B3184177
theorem B2830379 : Blo 1885435 2830379 := bstep (se 1 (by rfl) ⟨2122784, by rfl⟩ : syracuseStep 2830379 = 4245569) B4245569
theorem B1886919 : Blo 1885435 1886919 := bstep (se 1 (by rfl) ⟨1415189, by rfl⟩ : syracuseStep 1886919 = 2830379) B2830379
theorem B2122789 : Blo 1885435 2122789 := bbase (se 4 (by rfl) ⟨199011, by rfl⟩ : syracuseStep 2122789 = 398023) (by norm_num)
theorem B2830385 : Blo 1885435 2830385 := bstep (se 2 (by rfl) ⟨1061394, by rfl⟩ : syracuseStep 2830385 = 2122789) B2122789
theorem B1886923 : Blo 1885435 1886923 := bstep (se 1 (by rfl) ⟨1415192, by rfl⟩ : syracuseStep 1886923 = 2830385) B2830385
theorem B1912673 : Blo 1885435 1912673 := bbase (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) (by norm_num)
theorem B5100461 : Blo 1885435 5100461 := bstep (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) B1912673
theorem B3400307 : Blo 1885435 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B2266871 : Blo 1885435 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B6044989 : Blo 1885435 6044989 := bstep (se 3 (by rfl) ⟨1133435, by rfl⟩ : syracuseStep 6044989 = 2266871) B2266871
theorem B8059985 : Blo 1885435 8059985 := bstep (se 2 (by rfl) ⟨3022494, by rfl⟩ : syracuseStep 8059985 = 6044989) B6044989
theorem B5373323 : Blo 1885435 5373323 := bstep (se 1 (by rfl) ⟨4029992, by rfl⟩ : syracuseStep 5373323 = 8059985) B8059985
theorem B3582215 : Blo 1885435 3582215 := bstep (se 1 (by rfl) ⟨2686661, by rfl⟩ : syracuseStep 3582215 = 5373323) B5373323
theorem B2388143 : Blo 1885435 2388143 := bstep (se 1 (by rfl) ⟨1791107, by rfl⟩ : syracuseStep 2388143 = 3582215) B3582215
theorem B6368381 : Blo 1885435 6368381 := bstep (se 3 (by rfl) ⟨1194071, by rfl⟩ : syracuseStep 6368381 = 2388143) B2388143
theorem B4245587 : Blo 1885435 4245587 := bstep (se 1 (by rfl) ⟨3184190, by rfl⟩ : syracuseStep 4245587 = 6368381) B6368381
theorem B2830391 : Blo 1885435 2830391 := bstep (se 1 (by rfl) ⟨2122793, by rfl⟩ : syracuseStep 2830391 = 4245587) B4245587
theorem B1886927 : Blo 1885435 1886927 := bstep (se 1 (by rfl) ⟨1415195, by rfl⟩ : syracuseStep 1886927 = 2830391) B2830391
theorem B2830397 : Blo 1885435 2830397 := bbase (se 3 (by rfl) ⟨530699, by rfl⟩ : syracuseStep 2830397 = 1061399) (by norm_num)
theorem B1886931 : Blo 1885435 1886931 := bstep (se 1 (by rfl) ⟨1415198, by rfl⟩ : syracuseStep 1886931 = 2830397) B2830397
theorem B4245605 : Blo 1885435 4245605 := bbase (se 4 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 4245605 = 796051) (by norm_num)
theorem B2830403 : Blo 1885435 2830403 := bstep (se 1 (by rfl) ⟨2122802, by rfl⟩ : syracuseStep 2830403 = 4245605) B4245605
theorem B1886935 : Blo 1885435 1886935 := bstep (se 1 (by rfl) ⟨1415201, by rfl⟩ : syracuseStep 1886935 = 2830403) B2830403
theorem B4776317 : Blo 1885435 4776317 := bbase (se 3 (by rfl) ⟨895559, by rfl⟩ : syracuseStep 4776317 = 1791119) (by norm_num)
theorem B3184211 : Blo 1885435 3184211 := bstep (se 1 (by rfl) ⟨2388158, by rfl⟩ : syracuseStep 3184211 = 4776317) B4776317
theorem B2122807 : Blo 1885435 2122807 := bstep (se 1 (by rfl) ⟨1592105, by rfl⟩ : syracuseStep 2122807 = 3184211) B3184211
theorem B2830409 : Blo 1885435 2830409 := bstep (se 2 (by rfl) ⟨1061403, by rfl⟩ : syracuseStep 2830409 = 2122807) B2122807
theorem B1886939 : Blo 1885435 1886939 := bstep (se 1 (by rfl) ⟨1415204, by rfl⟩ : syracuseStep 1886939 = 2830409) B2830409
theorem B3582245 : Blo 1885435 3582245 := bbase (se 4 (by rfl) ⟨335835, by rfl⟩ : syracuseStep 3582245 = 671671) (by norm_num)
theorem B9552653 : Blo 1885435 9552653 := bstep (se 3 (by rfl) ⟨1791122, by rfl⟩ : syracuseStep 9552653 = 3582245) B3582245
theorem B6368435 : Blo 1885435 6368435 := bstep (se 1 (by rfl) ⟨4776326, by rfl⟩ : syracuseStep 6368435 = 9552653) B9552653
theorem B4245623 : Blo 1885435 4245623 := bstep (se 1 (by rfl) ⟨3184217, by rfl⟩ : syracuseStep 4245623 = 6368435) B6368435
theorem B2830415 : Blo 1885435 2830415 := bstep (se 1 (by rfl) ⟨2122811, by rfl⟩ : syracuseStep 2830415 = 4245623) B4245623
theorem B1886943 : Blo 1885435 1886943 := bstep (se 1 (by rfl) ⟨1415207, by rfl⟩ : syracuseStep 1886943 = 2830415) B2830415
theorem B2830421 : Blo 1885435 2830421 := bbase (se 8 (by rfl) ⟨16584, by rfl⟩ : syracuseStep 2830421 = 33169) (by norm_num)
theorem B1886947 : Blo 1885435 1886947 := bstep (se 1 (by rfl) ⟨1415210, by rfl⟩ : syracuseStep 1886947 = 2830421) B2830421
theorem B11476181 : Blo 1885435 11476181 := bbase (se 7 (by rfl) ⟨134486, by rfl⟩ : syracuseStep 11476181 = 268973) (by norm_num)
theorem B7650787 : Blo 1885435 7650787 := bstep (se 1 (by rfl) ⟨5738090, by rfl⟩ : syracuseStep 7650787 = 11476181) B11476181
theorem B10201049 : Blo 1885435 10201049 := bstep (se 2 (by rfl) ⟨3825393, by rfl⟩ : syracuseStep 10201049 = 7650787) B7650787
theorem B6800699 : Blo 1885435 6800699 := bstep (se 1 (by rfl) ⟨5100524, by rfl⟩ : syracuseStep 6800699 = 10201049) B10201049
theorem B18135197 : Blo 1885435 18135197 := bstep (se 3 (by rfl) ⟨3400349, by rfl⟩ : syracuseStep 18135197 = 6800699) B6800699
theorem B12090131 : Blo 1885435 12090131 := bstep (se 1 (by rfl) ⟨9067598, by rfl⟩ : syracuseStep 12090131 = 18135197) B18135197
theorem B8060087 : Blo 1885435 8060087 := bstep (se 1 (by rfl) ⟨6045065, by rfl⟩ : syracuseStep 8060087 = 12090131) B12090131
theorem B5373391 : Blo 1885435 5373391 := bstep (se 1 (by rfl) ⟨4030043, by rfl⟩ : syracuseStep 5373391 = 8060087) B8060087
theorem B7164521 : Blo 1885435 7164521 := bstep (se 2 (by rfl) ⟨2686695, by rfl⟩ : syracuseStep 7164521 = 5373391) B5373391
theorem B4776347 : Blo 1885435 4776347 := bstep (se 1 (by rfl) ⟨3582260, by rfl⟩ : syracuseStep 4776347 = 7164521) B7164521
theorem B3184231 : Blo 1885435 3184231 := bstep (se 1 (by rfl) ⟨2388173, by rfl⟩ : syracuseStep 3184231 = 4776347) B4776347
theorem B4245641 : Blo 1885435 4245641 := bstep (se 2 (by rfl) ⟨1592115, by rfl⟩ : syracuseStep 4245641 = 3184231) B3184231
theorem B2830427 : Blo 1885435 2830427 := bstep (se 1 (by rfl) ⟨2122820, by rfl⟩ : syracuseStep 2830427 = 4245641) B4245641
theorem B1886951 : Blo 1885435 1886951 := bstep (se 1 (by rfl) ⟨1415213, by rfl⟩ : syracuseStep 1886951 = 2830427) B2830427
theorem B2122825 : Blo 1885435 2122825 := bbase (se 2 (by rfl) ⟨796059, by rfl⟩ : syracuseStep 2122825 = 1592119) (by norm_num)
theorem B2830433 : Blo 1885435 2830433 := bstep (se 2 (by rfl) ⟨1061412, by rfl⟩ : syracuseStep 2830433 = 2122825) B2122825
theorem B1886955 : Blo 1885435 1886955 := bstep (se 1 (by rfl) ⟨1415216, by rfl⟩ : syracuseStep 1886955 = 2830433) B2830433
theorem B2266909 : Blo 1885435 2266909 := bbase (se 3 (by rfl) ⟨425045, by rfl⟩ : syracuseStep 2266909 = 850091) (by norm_num)
theorem B12090181 : Blo 1885435 12090181 := bstep (se 4 (by rfl) ⟨1133454, by rfl⟩ : syracuseStep 12090181 = 2266909) B2266909
theorem B16120241 : Blo 1885435 16120241 := bstep (se 2 (by rfl) ⟨6045090, by rfl⟩ : syracuseStep 16120241 = 12090181) B12090181
theorem B10746827 : Blo 1885435 10746827 := bstep (se 1 (by rfl) ⟨8060120, by rfl⟩ : syracuseStep 10746827 = 16120241) B16120241
theorem B7164551 : Blo 1885435 7164551 := bstep (se 1 (by rfl) ⟨5373413, by rfl⟩ : syracuseStep 7164551 = 10746827) B10746827
theorem B4776367 : Blo 1885435 4776367 := bstep (se 1 (by rfl) ⟨3582275, by rfl⟩ : syracuseStep 4776367 = 7164551) B7164551
theorem B6368489 : Blo 1885435 6368489 := bstep (se 2 (by rfl) ⟨2388183, by rfl⟩ : syracuseStep 6368489 = 4776367) B4776367
theorem B4245659 : Blo 1885435 4245659 := bstep (se 1 (by rfl) ⟨3184244, by rfl⟩ : syracuseStep 4245659 = 6368489) B6368489
theorem B2830439 : Blo 1885435 2830439 := bstep (se 1 (by rfl) ⟨2122829, by rfl⟩ : syracuseStep 2830439 = 4245659) B4245659
theorem B1886959 : Blo 1885435 1886959 := bstep (se 1 (by rfl) ⟨1415219, by rfl⟩ : syracuseStep 1886959 = 2830439) B2830439
theorem B2830445 : Blo 1885435 2830445 := bbase (se 3 (by rfl) ⟨530708, by rfl⟩ : syracuseStep 2830445 = 1061417) (by norm_num)
theorem B1886963 : Blo 1885435 1886963 := bstep (se 1 (by rfl) ⟨1415222, by rfl⟩ : syracuseStep 1886963 = 2830445) B2830445
theorem B4245677 : Blo 1885435 4245677 := bbase (se 3 (by rfl) ⟨796064, by rfl⟩ : syracuseStep 4245677 = 1592129) (by norm_num)
theorem B2830451 : Blo 1885435 2830451 := bstep (se 1 (by rfl) ⟨2122838, by rfl⟩ : syracuseStep 2830451 = 4245677) B4245677
theorem B1886967 : Blo 1885435 1886967 := bstep (se 1 (by rfl) ⟨1415225, by rfl⟩ : syracuseStep 1886967 = 2830451) B2830451
theorem B6800773 : Blo 1885435 6800773 := bbase (se 4 (by rfl) ⟨637572, by rfl⟩ : syracuseStep 6800773 = 1275145) (by norm_num)
theorem B9067697 : Blo 1885435 9067697 := bstep (se 2 (by rfl) ⟨3400386, by rfl⟩ : syracuseStep 9067697 = 6800773) B6800773
theorem B6045131 : Blo 1885435 6045131 := bstep (se 1 (by rfl) ⟨4533848, by rfl⟩ : syracuseStep 6045131 = 9067697) B9067697
theorem B4030087 : Blo 1885435 4030087 := bstep (se 1 (by rfl) ⟨3022565, by rfl⟩ : syracuseStep 4030087 = 6045131) B6045131
theorem B5373449 : Blo 1885435 5373449 := bstep (se 2 (by rfl) ⟨2015043, by rfl⟩ : syracuseStep 5373449 = 4030087) B4030087
theorem B3582299 : Blo 1885435 3582299 := bstep (se 1 (by rfl) ⟨2686724, by rfl⟩ : syracuseStep 3582299 = 5373449) B5373449
theorem B2388199 : Blo 1885435 2388199 := bstep (se 1 (by rfl) ⟨1791149, by rfl⟩ : syracuseStep 2388199 = 3582299) B3582299
theorem B3184265 : Blo 1885435 3184265 := bstep (se 2 (by rfl) ⟨1194099, by rfl⟩ : syracuseStep 3184265 = 2388199) B2388199
theorem B2122843 : Blo 1885435 2122843 := bstep (se 1 (by rfl) ⟨1592132, by rfl⟩ : syracuseStep 2122843 = 3184265) B3184265
theorem B2830457 : Blo 1885435 2830457 := bstep (se 2 (by rfl) ⟨1061421, by rfl⟩ : syracuseStep 2830457 = 2122843) B2122843
theorem B1886971 : Blo 1885435 1886971 := bstep (se 1 (by rfl) ⟨1415228, by rfl⟩ : syracuseStep 1886971 = 2830457) B2830457
theorem B24180565 : Blo 1885435 24180565 := bbase (se 9 (by rfl) ⟨70841, by rfl⟩ : syracuseStep 24180565 = 141683) (by norm_num)
theorem B32240753 : Blo 1885435 32240753 := bstep (se 2 (by rfl) ⟨12090282, by rfl⟩ : syracuseStep 32240753 = 24180565) B24180565
theorem B21493835 : Blo 1885435 21493835 := bstep (se 1 (by rfl) ⟨16120376, by rfl⟩ : syracuseStep 21493835 = 32240753) B32240753
theorem B14329223 : Blo 1885435 14329223 := bstep (se 1 (by rfl) ⟨10746917, by rfl⟩ : syracuseStep 14329223 = 21493835) B21493835
theorem B9552815 : Blo 1885435 9552815 := bstep (se 1 (by rfl) ⟨7164611, by rfl⟩ : syracuseStep 9552815 = 14329223) B14329223
theorem B6368543 : Blo 1885435 6368543 := bstep (se 1 (by rfl) ⟨4776407, by rfl⟩ : syracuseStep 6368543 = 9552815) B9552815
theorem B4245695 : Blo 1885435 4245695 := bstep (se 1 (by rfl) ⟨3184271, by rfl⟩ : syracuseStep 4245695 = 6368543) B6368543
theorem B2830463 : Blo 1885435 2830463 := bstep (se 1 (by rfl) ⟨2122847, by rfl⟩ : syracuseStep 2830463 = 4245695) B4245695
theorem B1886975 : Blo 1885435 1886975 := bstep (se 1 (by rfl) ⟨1415231, by rfl⟩ : syracuseStep 1886975 = 2830463) B2830463
theorem B2830469 : Blo 1885435 2830469 := bbase (se 4 (by rfl) ⟨265356, by rfl⟩ : syracuseStep 2830469 = 530713) (by norm_num)
theorem B1886979 : Blo 1885435 1886979 := bstep (se 1 (by rfl) ⟨1415234, by rfl⟩ : syracuseStep 1886979 = 2830469) B2830469
theorem B3184285 : Blo 1885435 3184285 := bbase (se 3 (by rfl) ⟨597053, by rfl⟩ : syracuseStep 3184285 = 1194107) (by norm_num)
theorem B4245713 : Blo 1885435 4245713 := bstep (se 2 (by rfl) ⟨1592142, by rfl⟩ : syracuseStep 4245713 = 3184285) B3184285
theorem B2830475 : Blo 1885435 2830475 := bstep (se 1 (by rfl) ⟨2122856, by rfl⟩ : syracuseStep 2830475 = 4245713) B4245713
theorem B1886983 : Blo 1885435 1886983 := bstep (se 1 (by rfl) ⟨1415237, by rfl⟩ : syracuseStep 1886983 = 2830475) B2830475
theorem B2122861 : Blo 1885435 2122861 := bbase (se 3 (by rfl) ⟨398036, by rfl⟩ : syracuseStep 2122861 = 796073) (by norm_num)
theorem B2830481 : Blo 1885435 2830481 := bstep (se 2 (by rfl) ⟨1061430, by rfl⟩ : syracuseStep 2830481 = 2122861) B2122861
theorem B1886987 : Blo 1885435 1886987 := bstep (se 1 (by rfl) ⟨1415240, by rfl⟩ : syracuseStep 1886987 = 2830481) B2830481
theorem B6368597 : Blo 1885435 6368597 := bbase (se 11 (by rfl) ⟨4664, by rfl⟩ : syracuseStep 6368597 = 9329) (by norm_num)
theorem B4245731 : Blo 1885435 4245731 := bstep (se 1 (by rfl) ⟨3184298, by rfl⟩ : syracuseStep 4245731 = 6368597) B6368597
theorem B2830487 : Blo 1885435 2830487 := bstep (se 1 (by rfl) ⟨2122865, by rfl⟩ : syracuseStep 2830487 = 4245731) B4245731
theorem B1886991 : Blo 1885435 1886991 := bstep (se 1 (by rfl) ⟨1415243, by rfl⟩ : syracuseStep 1886991 = 2830487) B2830487
theorem B2830493 : Blo 1885435 2830493 := bbase (se 3 (by rfl) ⟨530717, by rfl⟩ : syracuseStep 2830493 = 1061435) (by norm_num)
theorem B1886995 : Blo 1885435 1886995 := bstep (se 1 (by rfl) ⟨1415246, by rfl⟩ : syracuseStep 1886995 = 2830493) B2830493
theorem B4245749 : Blo 1885435 4245749 := bbase (se 5 (by rfl) ⟨199019, by rfl⟩ : syracuseStep 4245749 = 398039) (by norm_num)
theorem B2830499 : Blo 1885435 2830499 := bstep (se 1 (by rfl) ⟨2122874, by rfl⟩ : syracuseStep 2830499 = 4245749) B4245749
theorem B1886999 : Blo 1885435 1886999 := bstep (se 1 (by rfl) ⟨1415249, by rfl⟩ : syracuseStep 1886999 = 2830499) B2830499
theorem B3234517 : Blo 1885435 3234517 := bbase (se 7 (by rfl) ⟨37904, by rfl⟩ : syracuseStep 3234517 = 75809) (by norm_num)
theorem B17250757 : Blo 1885435 17250757 := bstep (se 4 (by rfl) ⟨1617258, by rfl⟩ : syracuseStep 17250757 = 3234517) B3234517
theorem B368016149 : Blo 1885435 368016149 := bstep (se 6 (by rfl) ⟨8625378, by rfl⟩ : syracuseStep 368016149 = 17250757) B17250757
theorem B245344099 : Blo 1885435 245344099 := bstep (se 1 (by rfl) ⟨184008074, by rfl⟩ : syracuseStep 245344099 = 368016149) B368016149
theorem B327125465 : Blo 1885435 327125465 := bstep (se 2 (by rfl) ⟨122672049, by rfl⟩ : syracuseStep 327125465 = 245344099) B245344099
theorem B218083643 : Blo 1885435 218083643 := bstep (se 1 (by rfl) ⟨163562732, by rfl⟩ : syracuseStep 218083643 = 327125465) B327125465
theorem B145389095 : Blo 1885435 145389095 := bstep (se 1 (by rfl) ⟨109041821, by rfl⟩ : syracuseStep 145389095 = 218083643) B218083643
theorem B96926063 : Blo 1885435 96926063 := bstep (se 1 (by rfl) ⟨72694547, by rfl⟩ : syracuseStep 96926063 = 145389095) B145389095
theorem B258469501 : Blo 1885435 258469501 := bstep (se 3 (by rfl) ⟨48463031, by rfl⟩ : syracuseStep 258469501 = 96926063) B96926063
theorem B344626001 : Blo 1885435 344626001 := bstep (se 2 (by rfl) ⟨129234750, by rfl⟩ : syracuseStep 344626001 = 258469501) B258469501
theorem B229750667 : Blo 1885435 229750667 := bstep (se 1 (by rfl) ⟨172313000, by rfl⟩ : syracuseStep 229750667 = 344626001) B344626001
theorem B153167111 : Blo 1885435 153167111 := bstep (se 1 (by rfl) ⟨114875333, by rfl⟩ : syracuseStep 153167111 = 229750667) B229750667
theorem B102111407 : Blo 1885435 102111407 := bstep (se 1 (by rfl) ⟨76583555, by rfl⟩ : syracuseStep 102111407 = 153167111) B153167111
theorem B68074271 : Blo 1885435 68074271 := bstep (se 1 (by rfl) ⟨51055703, by rfl⟩ : syracuseStep 68074271 = 102111407) B102111407
theorem B45382847 : Blo 1885435 45382847 := bstep (se 1 (by rfl) ⟨34037135, by rfl⟩ : syracuseStep 45382847 = 68074271) B68074271
theorem B121020925 : Blo 1885435 121020925 := bstep (se 3 (by rfl) ⟨22691423, by rfl⟩ : syracuseStep 121020925 = 45382847) B45382847
theorem B161361233 : Blo 1885435 161361233 := bstep (se 2 (by rfl) ⟨60510462, by rfl⟩ : syracuseStep 161361233 = 121020925) B121020925
theorem B107574155 : Blo 1885435 107574155 := bstep (se 1 (by rfl) ⟨80680616, by rfl⟩ : syracuseStep 107574155 = 161361233) B161361233
theorem B71716103 : Blo 1885435 71716103 := bstep (se 1 (by rfl) ⟨53787077, by rfl⟩ : syracuseStep 71716103 = 107574155) B107574155
theorem B47810735 : Blo 1885435 47810735 := bstep (se 1 (by rfl) ⟨35858051, by rfl⟩ : syracuseStep 47810735 = 71716103) B71716103
theorem B31873823 : Blo 1885435 31873823 := bstep (se 1 (by rfl) ⟨23905367, by rfl⟩ : syracuseStep 31873823 = 47810735) B47810735
theorem B21249215 : Blo 1885435 21249215 := bstep (se 1 (by rfl) ⟨15936911, by rfl⟩ : syracuseStep 21249215 = 31873823) B31873823
theorem B14166143 : Blo 1885435 14166143 := bstep (se 1 (by rfl) ⟨10624607, by rfl⟩ : syracuseStep 14166143 = 21249215) B21249215
theorem B9444095 : Blo 1885435 9444095 := bstep (se 1 (by rfl) ⟨7083071, by rfl⟩ : syracuseStep 9444095 = 14166143) B14166143
theorem B6296063 : Blo 1885435 6296063 := bstep (se 1 (by rfl) ⟨4722047, by rfl⟩ : syracuseStep 6296063 = 9444095) B9444095
theorem B16789501 : Blo 1885435 16789501 := bstep (se 3 (by rfl) ⟨3148031, by rfl⟩ : syracuseStep 16789501 = 6296063) B6296063
theorem B89544005 : Blo 1885435 89544005 := bstep (se 4 (by rfl) ⟨8394750, by rfl⟩ : syracuseStep 89544005 = 16789501) B16789501
theorem B59696003 : Blo 1885435 59696003 := bstep (se 1 (by rfl) ⟨44772002, by rfl⟩ : syracuseStep 59696003 = 89544005) B89544005
theorem B39797335 : Blo 1885435 39797335 := bstep (se 1 (by rfl) ⟨29848001, by rfl⟩ : syracuseStep 39797335 = 59696003) B59696003
theorem B53063113 : Blo 1885435 53063113 := bstep (se 2 (by rfl) ⟨19898667, by rfl⟩ : syracuseStep 53063113 = 39797335) B39797335
theorem B70750817 : Blo 1885435 70750817 := bstep (se 2 (by rfl) ⟨26531556, by rfl⟩ : syracuseStep 70750817 = 53063113) B53063113
theorem B47167211 : Blo 1885435 47167211 := bstep (se 1 (by rfl) ⟨35375408, by rfl⟩ : syracuseStep 47167211 = 70750817) B70750817
theorem B31444807 : Blo 1885435 31444807 := bstep (se 1 (by rfl) ⟨23583605, by rfl⟩ : syracuseStep 31444807 = 47167211) B47167211
theorem B41926409 : Blo 1885435 41926409 := bstep (se 2 (by rfl) ⟨15722403, by rfl⟩ : syracuseStep 41926409 = 31444807) B31444807
theorem B27950939 : Blo 1885435 27950939 := bstep (se 1 (by rfl) ⟨20963204, by rfl⟩ : syracuseStep 27950939 = 41926409) B41926409
theorem B18633959 : Blo 1885435 18633959 := bstep (se 1 (by rfl) ⟨13975469, by rfl⟩ : syracuseStep 18633959 = 27950939) B27950939
theorem B12422639 : Blo 1885435 12422639 := bstep (se 1 (by rfl) ⟨9316979, by rfl⟩ : syracuseStep 12422639 = 18633959) B18633959
theorem B8281759 : Blo 1885435 8281759 := bstep (se 1 (by rfl) ⟨6211319, by rfl⟩ : syracuseStep 8281759 = 12422639) B12422639
theorem B11042345 : Blo 1885435 11042345 := bstep (se 2 (by rfl) ⟨4140879, by rfl⟩ : syracuseStep 11042345 = 8281759) B8281759
theorem B7361563 : Blo 1885435 7361563 := bstep (se 1 (by rfl) ⟨5521172, by rfl⟩ : syracuseStep 7361563 = 11042345) B11042345
theorem B9815417 : Blo 1885435 9815417 := bstep (se 2 (by rfl) ⟨3680781, by rfl⟩ : syracuseStep 9815417 = 7361563) B7361563
theorem B6543611 : Blo 1885435 6543611 := bstep (se 1 (by rfl) ⟨4907708, by rfl⟩ : syracuseStep 6543611 = 9815417) B9815417
theorem B4362407 : Blo 1885435 4362407 := bstep (se 1 (by rfl) ⟨3271805, by rfl⟩ : syracuseStep 4362407 = 6543611) B6543611
theorem B2908271 : Blo 1885435 2908271 := bstep (se 1 (by rfl) ⟨2181203, by rfl⟩ : syracuseStep 2908271 = 4362407) B4362407
theorem B1938847 : Blo 1885435 1938847 := bstep (se 1 (by rfl) ⟨1454135, by rfl⟩ : syracuseStep 1938847 = 2908271) B2908271
theorem B2585129 : Blo 1885435 2585129 := bstep (se 2 (by rfl) ⟨969423, by rfl⟩ : syracuseStep 2585129 = 1938847) B1938847
theorem B6893677 : Blo 1885435 6893677 := bstep (se 3 (by rfl) ⟨1292564, by rfl⟩ : syracuseStep 6893677 = 2585129) B2585129
theorem B9191569 : Blo 1885435 9191569 := bstep (se 2 (by rfl) ⟨3446838, by rfl⟩ : syracuseStep 9191569 = 6893677) B6893677
theorem B12255425 : Blo 1885435 12255425 := bstep (se 2 (by rfl) ⟨4595784, by rfl⟩ : syracuseStep 12255425 = 9191569) B9191569
theorem B8170283 : Blo 1885435 8170283 := bstep (se 1 (by rfl) ⟨6127712, by rfl⟩ : syracuseStep 8170283 = 12255425) B12255425
theorem B5446855 : Blo 1885435 5446855 := bstep (se 1 (by rfl) ⟨4085141, by rfl⟩ : syracuseStep 5446855 = 8170283) B8170283
theorem B7262473 : Blo 1885435 7262473 := bstep (se 2 (by rfl) ⟨2723427, by rfl⟩ : syracuseStep 7262473 = 5446855) B5446855
theorem B9683297 : Blo 1885435 9683297 := bstep (se 2 (by rfl) ⟨3631236, by rfl⟩ : syracuseStep 9683297 = 7262473) B7262473
theorem B6455531 : Blo 1885435 6455531 := bstep (se 1 (by rfl) ⟨4841648, by rfl⟩ : syracuseStep 6455531 = 9683297) B9683297
theorem B4303687 : Blo 1885435 4303687 := bstep (se 1 (by rfl) ⟨3227765, by rfl⟩ : syracuseStep 4303687 = 6455531) B6455531
theorem B5738249 : Blo 1885435 5738249 := bstep (se 2 (by rfl) ⟨2151843, by rfl⟩ : syracuseStep 5738249 = 4303687) B4303687
theorem B3825499 : Blo 1885435 3825499 := bstep (se 1 (by rfl) ⟨2869124, by rfl⟩ : syracuseStep 3825499 = 5738249) B5738249
theorem B5100665 : Blo 1885435 5100665 := bstep (se 2 (by rfl) ⟨1912749, by rfl⟩ : syracuseStep 5100665 = 3825499) B3825499
theorem B13601773 : Blo 1885435 13601773 := bstep (se 3 (by rfl) ⟨2550332, by rfl⟩ : syracuseStep 13601773 = 5100665) B5100665
theorem B18135697 : Blo 1885435 18135697 := bstep (se 2 (by rfl) ⟨6800886, by rfl⟩ : syracuseStep 18135697 = 13601773) B13601773
theorem B24180929 : Blo 1885435 24180929 := bstep (se 2 (by rfl) ⟨9067848, by rfl⟩ : syracuseStep 24180929 = 18135697) B18135697
theorem B16120619 : Blo 1885435 16120619 := bstep (se 1 (by rfl) ⟨12090464, by rfl⟩ : syracuseStep 16120619 = 24180929) B24180929
theorem B10747079 : Blo 1885435 10747079 := bstep (se 1 (by rfl) ⟨8060309, by rfl⟩ : syracuseStep 10747079 = 16120619) B16120619
theorem B7164719 : Blo 1885435 7164719 := bstep (se 1 (by rfl) ⟨5373539, by rfl⟩ : syracuseStep 7164719 = 10747079) B10747079
theorem B4776479 : Blo 1885435 4776479 := bstep (se 1 (by rfl) ⟨3582359, by rfl⟩ : syracuseStep 4776479 = 7164719) B7164719
theorem B3184319 : Blo 1885435 3184319 := bstep (se 1 (by rfl) ⟨2388239, by rfl⟩ : syracuseStep 3184319 = 4776479) B4776479
theorem B2122879 : Blo 1885435 2122879 := bstep (se 1 (by rfl) ⟨1592159, by rfl⟩ : syracuseStep 2122879 = 3184319) B3184319
theorem B2830505 : Blo 1885435 2830505 := bstep (se 2 (by rfl) ⟨1061439, by rfl⟩ : syracuseStep 2830505 = 2122879) B2122879
theorem B1887003 : Blo 1885435 1887003 := bstep (se 1 (by rfl) ⟨1415252, by rfl⟩ : syracuseStep 1887003 = 2830505) B2830505
theorem B5100677 : Blo 1885435 5100677 := bbase (se 4 (by rfl) ⟨478188, by rfl⟩ : syracuseStep 5100677 = 956377) (by norm_num)
theorem B3400451 : Blo 1885435 3400451 := bstep (se 1 (by rfl) ⟨2550338, by rfl⟩ : syracuseStep 3400451 = 5100677) B5100677
theorem B2266967 : Blo 1885435 2266967 := bstep (se 1 (by rfl) ⟨1700225, by rfl⟩ : syracuseStep 2266967 = 3400451) B3400451
theorem B6045245 : Blo 1885435 6045245 := bstep (se 3 (by rfl) ⟨1133483, by rfl⟩ : syracuseStep 6045245 = 2266967) B2266967
theorem B4030163 : Blo 1885435 4030163 := bstep (se 1 (by rfl) ⟨3022622, by rfl⟩ : syracuseStep 4030163 = 6045245) B6045245
theorem B2686775 : Blo 1885435 2686775 := bstep (se 1 (by rfl) ⟨2015081, by rfl⟩ : syracuseStep 2686775 = 4030163) B4030163
theorem B7164733 : Blo 1885435 7164733 := bstep (se 3 (by rfl) ⟨1343387, by rfl⟩ : syracuseStep 7164733 = 2686775) B2686775
theorem B9552977 : Blo 1885435 9552977 := bstep (se 2 (by rfl) ⟨3582366, by rfl⟩ : syracuseStep 9552977 = 7164733) B7164733
theorem B6368651 : Blo 1885435 6368651 := bstep (se 1 (by rfl) ⟨4776488, by rfl⟩ : syracuseStep 6368651 = 9552977) B9552977
theorem B4245767 : Blo 1885435 4245767 := bstep (se 1 (by rfl) ⟨3184325, by rfl⟩ : syracuseStep 4245767 = 6368651) B6368651
theorem B2830511 : Blo 1885435 2830511 := bstep (se 1 (by rfl) ⟨2122883, by rfl⟩ : syracuseStep 2830511 = 4245767) B4245767
theorem B1887007 : Blo 1885435 1887007 := bstep (se 1 (by rfl) ⟨1415255, by rfl⟩ : syracuseStep 1887007 = 2830511) B2830511
theorem B2830517 : Blo 1885435 2830517 := bbase (se 5 (by rfl) ⟨132680, by rfl⟩ : syracuseStep 2830517 = 265361) (by norm_num)
theorem B1887011 : Blo 1885435 1887011 := bstep (se 1 (by rfl) ⟨1415258, by rfl⟩ : syracuseStep 1887011 = 2830517) B2830517
theorem B4776509 : Blo 1885435 4776509 := bbase (se 3 (by rfl) ⟨895595, by rfl⟩ : syracuseStep 4776509 = 1791191) (by norm_num)
theorem B3184339 : Blo 1885435 3184339 := bstep (se 1 (by rfl) ⟨2388254, by rfl⟩ : syracuseStep 3184339 = 4776509) B4776509
theorem B4245785 : Blo 1885435 4245785 := bstep (se 2 (by rfl) ⟨1592169, by rfl⟩ : syracuseStep 4245785 = 3184339) B3184339
theorem B2830523 : Blo 1885435 2830523 := bstep (se 1 (by rfl) ⟨2122892, by rfl⟩ : syracuseStep 2830523 = 4245785) B4245785
theorem B1887015 : Blo 1885435 1887015 := bstep (se 1 (by rfl) ⟨1415261, by rfl⟩ : syracuseStep 1887015 = 2830523) B2830523
theorem B2122897 : Blo 1885435 2122897 := bbase (se 2 (by rfl) ⟨796086, by rfl⟩ : syracuseStep 2122897 = 1592173) (by norm_num)
theorem B2830529 : Blo 1885435 2830529 := bstep (se 2 (by rfl) ⟨1061448, by rfl⟩ : syracuseStep 2830529 = 2122897) B2122897
theorem B1887019 : Blo 1885435 1887019 := bstep (se 1 (by rfl) ⟨1415264, by rfl⟩ : syracuseStep 1887019 = 2830529) B2830529
theorem B3582397 : Blo 1885435 3582397 := bbase (se 3 (by rfl) ⟨671699, by rfl⟩ : syracuseStep 3582397 = 1343399) (by norm_num)
theorem B4776529 : Blo 1885435 4776529 := bstep (se 2 (by rfl) ⟨1791198, by rfl⟩ : syracuseStep 4776529 = 3582397) B3582397
theorem B6368705 : Blo 1885435 6368705 := bstep (se 2 (by rfl) ⟨2388264, by rfl⟩ : syracuseStep 6368705 = 4776529) B4776529
theorem B4245803 : Blo 1885435 4245803 := bstep (se 1 (by rfl) ⟨3184352, by rfl⟩ : syracuseStep 4245803 = 6368705) B6368705
theorem B2830535 : Blo 1885435 2830535 := bstep (se 1 (by rfl) ⟨2122901, by rfl⟩ : syracuseStep 2830535 = 4245803) B4245803
theorem B1887023 : Blo 1885435 1887023 := bstep (se 1 (by rfl) ⟨1415267, by rfl⟩ : syracuseStep 1887023 = 2830535) B2830535
theorem B2830541 : Blo 1885435 2830541 := bbase (se 3 (by rfl) ⟨530726, by rfl⟩ : syracuseStep 2830541 = 1061453) (by norm_num)
theorem B1887027 : Blo 1885435 1887027 := bstep (se 1 (by rfl) ⟨1415270, by rfl⟩ : syracuseStep 1887027 = 2830541) B2830541
theorem B4245821 : Blo 1885435 4245821 := bbase (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) (by norm_num)
theorem B2830547 : Blo 1885435 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B1887031 : Blo 1885435 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B3184373 : Blo 1885435 3184373 := bbase (se 5 (by rfl) ⟨149267, by rfl⟩ : syracuseStep 3184373 = 298535) (by norm_num)
theorem B2122915 : Blo 1885435 2122915 := bstep (se 1 (by rfl) ⟨1592186, by rfl⟩ : syracuseStep 2122915 = 3184373) B3184373
theorem B2830553 : Blo 1885435 2830553 := bstep (se 2 (by rfl) ⟨1061457, by rfl⟩ : syracuseStep 2830553 = 2122915) B2122915
theorem B1887035 : Blo 1885435 1887035 := bstep (se 1 (by rfl) ⟨1415276, by rfl⟩ : syracuseStep 1887035 = 2830553) B2830553
theorem B9068021 : Blo 1885435 9068021 := bbase (se 5 (by rfl) ⟨425063, by rfl⟩ : syracuseStep 9068021 = 850127) (by norm_num)
theorem B6045347 : Blo 1885435 6045347 := bstep (se 1 (by rfl) ⟨4534010, by rfl⟩ : syracuseStep 6045347 = 9068021) B9068021
theorem B4030231 : Blo 1885435 4030231 := bstep (se 1 (by rfl) ⟨3022673, by rfl⟩ : syracuseStep 4030231 = 6045347) B6045347
theorem B5373641 : Blo 1885435 5373641 := bstep (se 2 (by rfl) ⟨2015115, by rfl⟩ : syracuseStep 5373641 = 4030231) B4030231
theorem B14329709 : Blo 1885435 14329709 := bstep (se 3 (by rfl) ⟨2686820, by rfl⟩ : syracuseStep 14329709 = 5373641) B5373641
theorem B9553139 : Blo 1885435 9553139 := bstep (se 1 (by rfl) ⟨7164854, by rfl⟩ : syracuseStep 9553139 = 14329709) B14329709
theorem B6368759 : Blo 1885435 6368759 := bstep (se 1 (by rfl) ⟨4776569, by rfl⟩ : syracuseStep 6368759 = 9553139) B9553139
theorem B4245839 : Blo 1885435 4245839 := bstep (se 1 (by rfl) ⟨3184379, by rfl⟩ : syracuseStep 4245839 = 6368759) B6368759
theorem B2830559 : Blo 1885435 2830559 := bstep (se 1 (by rfl) ⟨2122919, by rfl⟩ : syracuseStep 2830559 = 4245839) B4245839
theorem B1887039 : Blo 1885435 1887039 := bstep (se 1 (by rfl) ⟨1415279, by rfl⟩ : syracuseStep 1887039 = 2830559) B2830559
theorem B2830565 : Blo 1885435 2830565 := bbase (se 4 (by rfl) ⟨265365, by rfl⟩ : syracuseStep 2830565 = 530731) (by norm_num)
theorem B1887043 : Blo 1885435 1887043 := bstep (se 1 (by rfl) ⟨1415282, by rfl⟩ : syracuseStep 1887043 = 2830565) B2830565
theorem B15302357 : Blo 1885435 15302357 := bbase (se 7 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 15302357 = 358649) (by norm_num)
theorem B10201571 : Blo 1885435 10201571 := bstep (se 1 (by rfl) ⟨7651178, by rfl⟩ : syracuseStep 10201571 = 15302357) B15302357
theorem B6801047 : Blo 1885435 6801047 := bstep (se 1 (by rfl) ⟨5100785, by rfl⟩ : syracuseStep 6801047 = 10201571) B10201571
theorem B4534031 : Blo 1885435 4534031 := bstep (se 1 (by rfl) ⟨3400523, by rfl⟩ : syracuseStep 4534031 = 6801047) B6801047
theorem B3022687 : Blo 1885435 3022687 := bstep (se 1 (by rfl) ⟨2267015, by rfl⟩ : syracuseStep 3022687 = 4534031) B4534031
theorem B4030249 : Blo 1885435 4030249 := bstep (se 2 (by rfl) ⟨1511343, by rfl⟩ : syracuseStep 4030249 = 3022687) B3022687
theorem B5373665 : Blo 1885435 5373665 := bstep (se 2 (by rfl) ⟨2015124, by rfl⟩ : syracuseStep 5373665 = 4030249) B4030249
theorem B3582443 : Blo 1885435 3582443 := bstep (se 1 (by rfl) ⟨2686832, by rfl⟩ : syracuseStep 3582443 = 5373665) B5373665
theorem B2388295 : Blo 1885435 2388295 := bstep (se 1 (by rfl) ⟨1791221, by rfl⟩ : syracuseStep 2388295 = 3582443) B3582443
theorem B3184393 : Blo 1885435 3184393 := bstep (se 2 (by rfl) ⟨1194147, by rfl⟩ : syracuseStep 3184393 = 2388295) B2388295
theorem B4245857 : Blo 1885435 4245857 := bstep (se 2 (by rfl) ⟨1592196, by rfl⟩ : syracuseStep 4245857 = 3184393) B3184393
theorem B2830571 : Blo 1885435 2830571 := bstep (se 1 (by rfl) ⟨2122928, by rfl⟩ : syracuseStep 2830571 = 4245857) B4245857
theorem B1887047 : Blo 1885435 1887047 := bstep (se 1 (by rfl) ⟨1415285, by rfl⟩ : syracuseStep 1887047 = 2830571) B2830571
theorem B2122933 : Blo 1885435 2122933 := bbase (se 5 (by rfl) ⟨99512, by rfl⟩ : syracuseStep 2122933 = 199025) (by norm_num)
theorem B2830577 : Blo 1885435 2830577 := bstep (se 2 (by rfl) ⟨1061466, by rfl⟩ : syracuseStep 2830577 = 2122933) B2122933
theorem B1887051 : Blo 1885435 1887051 := bstep (se 1 (by rfl) ⟨1415288, by rfl⟩ : syracuseStep 1887051 = 2830577) B2830577
theorem B2388305 : Blo 1885435 2388305 := bbase (se 2 (by rfl) ⟨895614, by rfl⟩ : syracuseStep 2388305 = 1791229) (by norm_num)
theorem B6368813 : Blo 1885435 6368813 := bstep (se 3 (by rfl) ⟨1194152, by rfl⟩ : syracuseStep 6368813 = 2388305) B2388305
theorem B4245875 : Blo 1885435 4245875 := bstep (se 1 (by rfl) ⟨3184406, by rfl⟩ : syracuseStep 4245875 = 6368813) B6368813
theorem B2830583 : Blo 1885435 2830583 := bstep (se 1 (by rfl) ⟨2122937, by rfl⟩ : syracuseStep 2830583 = 4245875) B4245875
theorem B1887055 : Blo 1885435 1887055 := bstep (se 1 (by rfl) ⟨1415291, by rfl⟩ : syracuseStep 1887055 = 2830583) B2830583
theorem B2830589 : Blo 1885435 2830589 := bbase (se 3 (by rfl) ⟨530735, by rfl⟩ : syracuseStep 2830589 = 1061471) (by norm_num)
theorem B1887059 : Blo 1885435 1887059 := bstep (se 1 (by rfl) ⟨1415294, by rfl⟩ : syracuseStep 1887059 = 2830589) B2830589
theorem B4245893 : Blo 1885435 4245893 := bbase (se 4 (by rfl) ⟨398052, by rfl⟩ : syracuseStep 4245893 = 796105) (by norm_num)
theorem B2830595 : Blo 1885435 2830595 := bstep (se 1 (by rfl) ⟨2122946, by rfl⟩ : syracuseStep 2830595 = 4245893) B4245893
theorem B1887063 : Blo 1885435 1887063 := bstep (se 1 (by rfl) ⟨1415297, by rfl⟩ : syracuseStep 1887063 = 2830595) B2830595
theorem B2686861 : Blo 1885435 2686861 := bbase (se 3 (by rfl) ⟨503786, by rfl⟩ : syracuseStep 2686861 = 1007573) (by norm_num)
theorem B3582481 : Blo 1885435 3582481 := bstep (se 2 (by rfl) ⟨1343430, by rfl⟩ : syracuseStep 3582481 = 2686861) B2686861
theorem B4776641 : Blo 1885435 4776641 := bstep (se 2 (by rfl) ⟨1791240, by rfl⟩ : syracuseStep 4776641 = 3582481) B3582481
theorem B3184427 : Blo 1885435 3184427 := bstep (se 1 (by rfl) ⟨2388320, by rfl⟩ : syracuseStep 3184427 = 4776641) B4776641
theorem B2122951 : Blo 1885435 2122951 := bstep (se 1 (by rfl) ⟨1592213, by rfl⟩ : syracuseStep 2122951 = 3184427) B3184427
theorem B2830601 : Blo 1885435 2830601 := bstep (se 2 (by rfl) ⟨1061475, by rfl⟩ : syracuseStep 2830601 = 2122951) B2122951
theorem B1887067 : Blo 1885435 1887067 := bstep (se 1 (by rfl) ⟨1415300, by rfl⟩ : syracuseStep 1887067 = 2830601) B2830601
theorem B9553301 : Blo 1885435 9553301 := bbase (se 6 (by rfl) ⟨223905, by rfl⟩ : syracuseStep 9553301 = 447811) (by norm_num)
theorem B6368867 : Blo 1885435 6368867 := bstep (se 1 (by rfl) ⟨4776650, by rfl⟩ : syracuseStep 6368867 = 9553301) B9553301
theorem B4245911 : Blo 1885435 4245911 := bstep (se 1 (by rfl) ⟨3184433, by rfl⟩ : syracuseStep 4245911 = 6368867) B6368867
theorem B2830607 : Blo 1885435 2830607 := bstep (se 1 (by rfl) ⟨2122955, by rfl⟩ : syracuseStep 2830607 = 4245911) B4245911
theorem B1887071 : Blo 1885435 1887071 := bstep (se 1 (by rfl) ⟨1415303, by rfl⟩ : syracuseStep 1887071 = 2830607) B2830607
theorem B2830613 : Blo 1885435 2830613 := bbase (se 6 (by rfl) ⟨66342, by rfl⟩ : syracuseStep 2830613 = 132685) (by norm_num)
theorem B1887075 : Blo 1885435 1887075 := bstep (se 1 (by rfl) ⟨1415306, by rfl⟩ : syracuseStep 1887075 = 2830613) B2830613
theorem B9068213 : Blo 1885435 9068213 := bbase (se 5 (by rfl) ⟨425072, by rfl⟩ : syracuseStep 9068213 = 850145) (by norm_num)
theorem B24181901 : Blo 1885435 24181901 := bstep (se 3 (by rfl) ⟨4534106, by rfl⟩ : syracuseStep 24181901 = 9068213) B9068213
theorem B16121267 : Blo 1885435 16121267 := bstep (se 1 (by rfl) ⟨12090950, by rfl⟩ : syracuseStep 16121267 = 24181901) B24181901
theorem B10747511 : Blo 1885435 10747511 := bstep (se 1 (by rfl) ⟨8060633, by rfl⟩ : syracuseStep 10747511 = 16121267) B16121267
theorem B7165007 : Blo 1885435 7165007 := bstep (se 1 (by rfl) ⟨5373755, by rfl⟩ : syracuseStep 7165007 = 10747511) B10747511
theorem B4776671 : Blo 1885435 4776671 := bstep (se 1 (by rfl) ⟨3582503, by rfl⟩ : syracuseStep 4776671 = 7165007) B7165007
theorem B3184447 : Blo 1885435 3184447 := bstep (se 1 (by rfl) ⟨2388335, by rfl⟩ : syracuseStep 3184447 = 4776671) B4776671
theorem B4245929 : Blo 1885435 4245929 := bstep (se 2 (by rfl) ⟨1592223, by rfl⟩ : syracuseStep 4245929 = 3184447) B3184447
theorem B2830619 : Blo 1885435 2830619 := bstep (se 1 (by rfl) ⟨2122964, by rfl⟩ : syracuseStep 2830619 = 4245929) B4245929
theorem B1887079 : Blo 1885435 1887079 := bstep (se 1 (by rfl) ⟨1415309, by rfl⟩ : syracuseStep 1887079 = 2830619) B2830619
theorem B2122969 : Blo 1885435 2122969 := bbase (se 2 (by rfl) ⟨796113, by rfl⟩ : syracuseStep 2122969 = 1592227) (by norm_num)
theorem B2830625 : Blo 1885435 2830625 := bstep (se 2 (by rfl) ⟨1061484, by rfl⟩ : syracuseStep 2830625 = 2122969) B2122969
theorem B1887083 : Blo 1885435 1887083 := bstep (se 1 (by rfl) ⟨1415312, by rfl⟩ : syracuseStep 1887083 = 2830625) B2830625
theorem B2723549 : Blo 1885435 2723549 := bbase (se 3 (by rfl) ⟨510665, by rfl⟩ : syracuseStep 2723549 = 1021331) (by norm_num)
theorem B7262797 : Blo 1885435 7262797 := bstep (se 3 (by rfl) ⟨1361774, by rfl⟩ : syracuseStep 7262797 = 2723549) B2723549
theorem B9683729 : Blo 1885435 9683729 := bstep (se 2 (by rfl) ⟨3631398, by rfl⟩ : syracuseStep 9683729 = 7262797) B7262797
theorem B6455819 : Blo 1885435 6455819 := bstep (se 1 (by rfl) ⟨4841864, by rfl⟩ : syracuseStep 6455819 = 9683729) B9683729
theorem B17215517 : Blo 1885435 17215517 := bstep (se 3 (by rfl) ⟨3227909, by rfl⟩ : syracuseStep 17215517 = 6455819) B6455819
theorem B11477011 : Blo 1885435 11477011 := bstep (se 1 (by rfl) ⟨8607758, by rfl⟩ : syracuseStep 11477011 = 17215517) B17215517
theorem B15302681 : Blo 1885435 15302681 := bstep (se 2 (by rfl) ⟨5738505, by rfl⟩ : syracuseStep 15302681 = 11477011) B11477011
theorem B10201787 : Blo 1885435 10201787 := bstep (se 1 (by rfl) ⟨7651340, by rfl⟩ : syracuseStep 10201787 = 15302681) B15302681
theorem B6801191 : Blo 1885435 6801191 := bstep (se 1 (by rfl) ⟨5100893, by rfl⟩ : syracuseStep 6801191 = 10201787) B10201787
theorem B4534127 : Blo 1885435 4534127 := bstep (se 1 (by rfl) ⟨3400595, by rfl⟩ : syracuseStep 4534127 = 6801191) B6801191
theorem B3022751 : Blo 1885435 3022751 := bstep (se 1 (by rfl) ⟨2267063, by rfl⟩ : syracuseStep 3022751 = 4534127) B4534127
theorem B2015167 : Blo 1885435 2015167 := bstep (se 1 (by rfl) ⟨1511375, by rfl⟩ : syracuseStep 2015167 = 3022751) B3022751
theorem B2686889 : Blo 1885435 2686889 := bstep (se 2 (by rfl) ⟨1007583, by rfl⟩ : syracuseStep 2686889 = 2015167) B2015167
theorem B7165037 : Blo 1885435 7165037 := bstep (se 3 (by rfl) ⟨1343444, by rfl⟩ : syracuseStep 7165037 = 2686889) B2686889
theorem B4776691 : Blo 1885435 4776691 := bstep (se 1 (by rfl) ⟨3582518, by rfl⟩ : syracuseStep 4776691 = 7165037) B7165037
theorem B6368921 : Blo 1885435 6368921 := bstep (se 2 (by rfl) ⟨2388345, by rfl⟩ : syracuseStep 6368921 = 4776691) B4776691
theorem B4245947 : Blo 1885435 4245947 := bstep (se 1 (by rfl) ⟨3184460, by rfl⟩ : syracuseStep 4245947 = 6368921) B6368921
theorem B2830631 : Blo 1885435 2830631 := bstep (se 1 (by rfl) ⟨2122973, by rfl⟩ : syracuseStep 2830631 = 4245947) B4245947
theorem B1887087 : Blo 1885435 1887087 := bstep (se 1 (by rfl) ⟨1415315, by rfl⟩ : syracuseStep 1887087 = 2830631) B2830631
theorem B2830637 : Blo 1885435 2830637 := bbase (se 3 (by rfl) ⟨530744, by rfl⟩ : syracuseStep 2830637 = 1061489) (by norm_num)
theorem B1887091 : Blo 1885435 1887091 := bstep (se 1 (by rfl) ⟨1415318, by rfl⟩ : syracuseStep 1887091 = 2830637) B2830637
theorem B4245965 : Blo 1885435 4245965 := bbase (se 3 (by rfl) ⟨796118, by rfl⟩ : syracuseStep 4245965 = 1592237) (by norm_num)
theorem B2830643 : Blo 1885435 2830643 := bstep (se 1 (by rfl) ⟨2122982, by rfl⟩ : syracuseStep 2830643 = 4245965) B4245965
theorem B1887095 : Blo 1885435 1887095 := bstep (se 1 (by rfl) ⟨1415321, by rfl⟩ : syracuseStep 1887095 = 2830643) B2830643
theorem B2388361 : Blo 1885435 2388361 := bbase (se 2 (by rfl) ⟨895635, by rfl⟩ : syracuseStep 2388361 = 1791271) (by norm_num)
theorem B3184481 : Blo 1885435 3184481 := bstep (se 2 (by rfl) ⟨1194180, by rfl⟩ : syracuseStep 3184481 = 2388361) B2388361
theorem B2122987 : Blo 1885435 2122987 := bstep (se 1 (by rfl) ⟨1592240, by rfl⟩ : syracuseStep 2122987 = 3184481) B3184481
theorem B2830649 : Blo 1885435 2830649 := bstep (se 2 (by rfl) ⟨1061493, by rfl⟩ : syracuseStep 2830649 = 2122987) B2122987
theorem B1887099 : Blo 1885435 1887099 := bstep (se 1 (by rfl) ⟨1415324, by rfl⟩ : syracuseStep 1887099 = 2830649) B2830649
theorem B2298013 : Blo 1885435 2298013 := bbase (se 3 (by rfl) ⟨430877, by rfl⟩ : syracuseStep 2298013 = 861755) (by norm_num)
theorem B12256069 : Blo 1885435 12256069 := bstep (se 4 (by rfl) ⟨1149006, by rfl⟩ : syracuseStep 12256069 = 2298013) B2298013
theorem B16341425 : Blo 1885435 16341425 := bstep (se 2 (by rfl) ⟨6128034, by rfl⟩ : syracuseStep 16341425 = 12256069) B12256069
theorem B10894283 : Blo 1885435 10894283 := bstep (se 1 (by rfl) ⟨8170712, by rfl⟩ : syracuseStep 10894283 = 16341425) B16341425
theorem B7262855 : Blo 1885435 7262855 := bstep (se 1 (by rfl) ⟨5447141, by rfl⟩ : syracuseStep 7262855 = 10894283) B10894283
theorem B4841903 : Blo 1885435 4841903 := bstep (se 1 (by rfl) ⟨3631427, by rfl⟩ : syracuseStep 4841903 = 7262855) B7262855
theorem B12911741 : Blo 1885435 12911741 := bstep (se 3 (by rfl) ⟨2420951, by rfl⟩ : syracuseStep 12911741 = 4841903) B4841903
theorem B8607827 : Blo 1885435 8607827 := bstep (se 1 (by rfl) ⟨6455870, by rfl⟩ : syracuseStep 8607827 = 12911741) B12911741
theorem B22954205 : Blo 1885435 22954205 := bstep (se 3 (by rfl) ⟨4303913, by rfl⟩ : syracuseStep 22954205 = 8607827) B8607827
theorem B61211213 : Blo 1885435 61211213 := bstep (se 3 (by rfl) ⟨11477102, by rfl⟩ : syracuseStep 61211213 = 22954205) B22954205
theorem B40807475 : Blo 1885435 40807475 := bstep (se 1 (by rfl) ⟨30605606, by rfl⟩ : syracuseStep 40807475 = 61211213) B61211213
theorem B27204983 : Blo 1885435 27204983 := bstep (se 1 (by rfl) ⟨20403737, by rfl⟩ : syracuseStep 27204983 = 40807475) B40807475
theorem B18136655 : Blo 1885435 18136655 := bstep (se 1 (by rfl) ⟨13602491, by rfl⟩ : syracuseStep 18136655 = 27204983) B27204983
theorem B12091103 : Blo 1885435 12091103 := bstep (se 1 (by rfl) ⟨9068327, by rfl⟩ : syracuseStep 12091103 = 18136655) B18136655
theorem B8060735 : Blo 1885435 8060735 := bstep (se 1 (by rfl) ⟨6045551, by rfl⟩ : syracuseStep 8060735 = 12091103) B12091103
theorem B21495293 : Blo 1885435 21495293 := bstep (se 3 (by rfl) ⟨4030367, by rfl⟩ : syracuseStep 21495293 = 8060735) B8060735
theorem B14330195 : Blo 1885435 14330195 := bstep (se 1 (by rfl) ⟨10747646, by rfl⟩ : syracuseStep 14330195 = 21495293) B21495293
theorem B9553463 : Blo 1885435 9553463 := bstep (se 1 (by rfl) ⟨7165097, by rfl⟩ : syracuseStep 9553463 = 14330195) B14330195
theorem B6368975 : Blo 1885435 6368975 := bstep (se 1 (by rfl) ⟨4776731, by rfl⟩ : syracuseStep 6368975 = 9553463) B9553463
theorem B4245983 : Blo 1885435 4245983 := bstep (se 1 (by rfl) ⟨3184487, by rfl⟩ : syracuseStep 4245983 = 6368975) B6368975
theorem B2830655 : Blo 1885435 2830655 := bstep (se 1 (by rfl) ⟨2122991, by rfl⟩ : syracuseStep 2830655 = 4245983) B4245983
theorem B1887103 : Blo 1885435 1887103 := bstep (se 1 (by rfl) ⟨1415327, by rfl⟩ : syracuseStep 1887103 = 2830655) B2830655
theorem B2830661 : Blo 1885435 2830661 := bbase (se 4 (by rfl) ⟨265374, by rfl⟩ : syracuseStep 2830661 = 530749) (by norm_num)
theorem B1887107 : Blo 1885435 1887107 := bstep (se 1 (by rfl) ⟨1415330, by rfl⟩ : syracuseStep 1887107 = 2830661) B2830661
theorem B3184501 : Blo 1885435 3184501 := bbase (se 5 (by rfl) ⟨149273, by rfl⟩ : syracuseStep 3184501 = 298547) (by norm_num)
theorem B4246001 : Blo 1885435 4246001 := bstep (se 2 (by rfl) ⟨1592250, by rfl⟩ : syracuseStep 4246001 = 3184501) B3184501
theorem B2830667 : Blo 1885435 2830667 := bstep (se 1 (by rfl) ⟨2123000, by rfl⟩ : syracuseStep 2830667 = 4246001) B4246001
theorem B1887111 : Blo 1885435 1887111 := bstep (se 1 (by rfl) ⟨1415333, by rfl⟩ : syracuseStep 1887111 = 2830667) B2830667
theorem B2123005 : Blo 1885435 2123005 := bbase (se 3 (by rfl) ⟨398063, by rfl⟩ : syracuseStep 2123005 = 796127) (by norm_num)
theorem B2830673 : Blo 1885435 2830673 := bstep (se 2 (by rfl) ⟨1061502, by rfl⟩ : syracuseStep 2830673 = 2123005) B2123005
theorem B1887115 : Blo 1885435 1887115 := bstep (se 1 (by rfl) ⟨1415336, by rfl⟩ : syracuseStep 1887115 = 2830673) B2830673
theorem B6369029 : Blo 1885435 6369029 := bbase (se 4 (by rfl) ⟨597096, by rfl⟩ : syracuseStep 6369029 = 1194193) (by norm_num)
theorem B4246019 : Blo 1885435 4246019 := bstep (se 1 (by rfl) ⟨3184514, by rfl⟩ : syracuseStep 4246019 = 6369029) B6369029
theorem B2830679 : Blo 1885435 2830679 := bstep (se 1 (by rfl) ⟨2123009, by rfl⟩ : syracuseStep 2830679 = 4246019) B4246019
theorem B1887119 : Blo 1885435 1887119 := bstep (se 1 (by rfl) ⟨1415339, by rfl⟩ : syracuseStep 1887119 = 2830679) B2830679
theorem B2830685 : Blo 1885435 2830685 := bbase (se 3 (by rfl) ⟨530753, by rfl⟩ : syracuseStep 2830685 = 1061507) (by norm_num)
theorem B1887123 : Blo 1885435 1887123 := bstep (se 1 (by rfl) ⟨1415342, by rfl⟩ : syracuseStep 1887123 = 2830685) B2830685
theorem B4246037 : Blo 1885435 4246037 := bbase (se 6 (by rfl) ⟨99516, by rfl⟩ : syracuseStep 4246037 = 199033) (by norm_num)
theorem B2830691 : Blo 1885435 2830691 := bstep (se 1 (by rfl) ⟨2123018, by rfl⟩ : syracuseStep 2830691 = 4246037) B4246037
theorem B1887127 : Blo 1885435 1887127 := bstep (se 1 (by rfl) ⟨1415345, by rfl⟩ : syracuseStep 1887127 = 2830691) B2830691
theorem B7165205 : Blo 1885435 7165205 := bbase (se 6 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 7165205 = 335869) (by norm_num)
theorem B4776803 : Blo 1885435 4776803 := bstep (se 1 (by rfl) ⟨3582602, by rfl⟩ : syracuseStep 4776803 = 7165205) B7165205
theorem B3184535 : Blo 1885435 3184535 := bstep (se 1 (by rfl) ⟨2388401, by rfl⟩ : syracuseStep 3184535 = 4776803) B4776803
theorem B2123023 : Blo 1885435 2123023 := bstep (se 1 (by rfl) ⟨1592267, by rfl⟩ : syracuseStep 2123023 = 3184535) B3184535
theorem B2830697 : Blo 1885435 2830697 := bstep (se 2 (by rfl) ⟨1061511, by rfl⟩ : syracuseStep 2830697 = 2123023) B2123023
theorem B1887131 : Blo 1885435 1887131 := bstep (se 1 (by rfl) ⟨1415348, by rfl⟩ : syracuseStep 1887131 = 2830697) B2830697
theorem B10747829 : Blo 1885435 10747829 := bbase (se 5 (by rfl) ⟨503804, by rfl⟩ : syracuseStep 10747829 = 1007609) (by norm_num)
theorem B7165219 : Blo 1885435 7165219 := bstep (se 1 (by rfl) ⟨5373914, by rfl⟩ : syracuseStep 7165219 = 10747829) B10747829
theorem B9553625 : Blo 1885435 9553625 := bstep (se 2 (by rfl) ⟨3582609, by rfl⟩ : syracuseStep 9553625 = 7165219) B7165219
theorem B6369083 : Blo 1885435 6369083 := bstep (se 1 (by rfl) ⟨4776812, by rfl⟩ : syracuseStep 6369083 = 9553625) B9553625
theorem B4246055 : Blo 1885435 4246055 := bstep (se 1 (by rfl) ⟨3184541, by rfl⟩ : syracuseStep 4246055 = 6369083) B6369083
theorem B2830703 : Blo 1885435 2830703 := bstep (se 1 (by rfl) ⟨2123027, by rfl⟩ : syracuseStep 2830703 = 4246055) B4246055
theorem B1887135 : Blo 1885435 1887135 := bstep (se 1 (by rfl) ⟨1415351, by rfl⟩ : syracuseStep 1887135 = 2830703) B2830703
theorem B2830709 : Blo 1885435 2830709 := bbase (se 5 (by rfl) ⟨132689, by rfl⟩ : syracuseStep 2830709 = 265379) (by norm_num)
theorem B1887139 : Blo 1885435 1887139 := bstep (se 1 (by rfl) ⟨1415354, by rfl⟩ : syracuseStep 1887139 = 2830709) B2830709
theorem B5170645 : Blo 1885435 5170645 := bbase (se 7 (by rfl) ⟨60593, by rfl⟩ : syracuseStep 5170645 = 121187) (by norm_num)
theorem B27576773 : Blo 1885435 27576773 := bstep (se 4 (by rfl) ⟨2585322, by rfl⟩ : syracuseStep 27576773 = 5170645) B5170645
theorem B18384515 : Blo 1885435 18384515 := bstep (se 1 (by rfl) ⟨13788386, by rfl⟩ : syracuseStep 18384515 = 27576773) B27576773
theorem B12256343 : Blo 1885435 12256343 := bstep (se 1 (by rfl) ⟨9192257, by rfl⟩ : syracuseStep 12256343 = 18384515) B18384515
theorem B8170895 : Blo 1885435 8170895 := bstep (se 1 (by rfl) ⟨6128171, by rfl⟩ : syracuseStep 8170895 = 12256343) B12256343
theorem B5447263 : Blo 1885435 5447263 := bstep (se 1 (by rfl) ⟨4085447, by rfl⟩ : syracuseStep 5447263 = 8170895) B8170895
theorem B7263017 : Blo 1885435 7263017 := bstep (se 2 (by rfl) ⟨2723631, by rfl⟩ : syracuseStep 7263017 = 5447263) B5447263
theorem B4842011 : Blo 1885435 4842011 := bstep (se 1 (by rfl) ⟨3631508, by rfl⟩ : syracuseStep 4842011 = 7263017) B7263017
theorem B3228007 : Blo 1885435 3228007 := bstep (se 1 (by rfl) ⟨2421005, by rfl⟩ : syracuseStep 3228007 = 4842011) B4842011
theorem B4304009 : Blo 1885435 4304009 := bstep (se 2 (by rfl) ⟨1614003, by rfl⟩ : syracuseStep 4304009 = 3228007) B3228007
theorem B2869339 : Blo 1885435 2869339 := bstep (se 1 (by rfl) ⟨2152004, by rfl⟩ : syracuseStep 2869339 = 4304009) B4304009
theorem B3825785 : Blo 1885435 3825785 := bstep (se 2 (by rfl) ⟨1434669, by rfl⟩ : syracuseStep 3825785 = 2869339) B2869339
theorem B2550523 : Blo 1885435 2550523 := bstep (se 1 (by rfl) ⟨1912892, by rfl⟩ : syracuseStep 2550523 = 3825785) B3825785
theorem B3400697 : Blo 1885435 3400697 := bstep (se 2 (by rfl) ⟨1275261, by rfl⟩ : syracuseStep 3400697 = 2550523) B2550523
theorem B2267131 : Blo 1885435 2267131 := bstep (se 1 (by rfl) ⟨1700348, by rfl⟩ : syracuseStep 2267131 = 3400697) B3400697
theorem B3022841 : Blo 1885435 3022841 := bstep (se 2 (by rfl) ⟨1133565, by rfl⟩ : syracuseStep 3022841 = 2267131) B2267131
theorem B2015227 : Blo 1885435 2015227 := bstep (se 1 (by rfl) ⟨1511420, by rfl⟩ : syracuseStep 2015227 = 3022841) B3022841
theorem B2686969 : Blo 1885435 2686969 := bstep (se 2 (by rfl) ⟨1007613, by rfl⟩ : syracuseStep 2686969 = 2015227) B2015227
theorem B3582625 : Blo 1885435 3582625 := bstep (se 2 (by rfl) ⟨1343484, by rfl⟩ : syracuseStep 3582625 = 2686969) B2686969
theorem B4776833 : Blo 1885435 4776833 := bstep (se 2 (by rfl) ⟨1791312, by rfl⟩ : syracuseStep 4776833 = 3582625) B3582625
theorem B3184555 : Blo 1885435 3184555 := bstep (se 1 (by rfl) ⟨2388416, by rfl⟩ : syracuseStep 3184555 = 4776833) B4776833
theorem B4246073 : Blo 1885435 4246073 := bstep (se 2 (by rfl) ⟨1592277, by rfl⟩ : syracuseStep 4246073 = 3184555) B3184555
theorem B2830715 : Blo 1885435 2830715 := bstep (se 1 (by rfl) ⟨2123036, by rfl⟩ : syracuseStep 2830715 = 4246073) B4246073
theorem B1887143 : Blo 1885435 1887143 := bstep (se 1 (by rfl) ⟨1415357, by rfl⟩ : syracuseStep 1887143 = 2830715) B2830715
theorem B2123041 : Blo 1885435 2123041 := bbase (se 2 (by rfl) ⟨796140, by rfl⟩ : syracuseStep 2123041 = 1592281) (by norm_num)
theorem B2830721 : Blo 1885435 2830721 := bstep (se 2 (by rfl) ⟨1061520, by rfl⟩ : syracuseStep 2830721 = 2123041) B2123041
theorem B1887147 : Blo 1885435 1887147 := bstep (se 1 (by rfl) ⟨1415360, by rfl⟩ : syracuseStep 1887147 = 2830721) B2830721
theorem B4776853 : Blo 1885435 4776853 := bbase (se 6 (by rfl) ⟨111957, by rfl⟩ : syracuseStep 4776853 = 223915) (by norm_num)
theorem B6369137 : Blo 1885435 6369137 := bstep (se 2 (by rfl) ⟨2388426, by rfl⟩ : syracuseStep 6369137 = 4776853) B4776853
theorem B4246091 : Blo 1885435 4246091 := bstep (se 1 (by rfl) ⟨3184568, by rfl⟩ : syracuseStep 4246091 = 6369137) B6369137
theorem B2830727 : Blo 1885435 2830727 := bstep (se 1 (by rfl) ⟨2123045, by rfl⟩ : syracuseStep 2830727 = 4246091) B4246091
theorem B1887151 : Blo 1885435 1887151 := bstep (se 1 (by rfl) ⟨1415363, by rfl⟩ : syracuseStep 1887151 = 2830727) B2830727
theorem B2830733 : Blo 1885435 2830733 := bbase (se 3 (by rfl) ⟨530762, by rfl⟩ : syracuseStep 2830733 = 1061525) (by norm_num)
theorem B1887155 : Blo 1885435 1887155 := bstep (se 1 (by rfl) ⟨1415366, by rfl⟩ : syracuseStep 1887155 = 2830733) B2830733
theorem B4246109 : Blo 1885435 4246109 := bbase (se 3 (by rfl) ⟨796145, by rfl⟩ : syracuseStep 4246109 = 1592291) (by norm_num)
theorem B2830739 : Blo 1885435 2830739 := bstep (se 1 (by rfl) ⟨2123054, by rfl⟩ : syracuseStep 2830739 = 4246109) B4246109
theorem B1887159 : Blo 1885435 1887159 := bstep (se 1 (by rfl) ⟨1415369, by rfl⟩ : syracuseStep 1887159 = 2830739) B2830739
theorem B3184589 : Blo 1885435 3184589 := bbase (se 3 (by rfl) ⟨597110, by rfl⟩ : syracuseStep 3184589 = 1194221) (by norm_num)
theorem B2123059 : Blo 1885435 2123059 := bstep (se 1 (by rfl) ⟨1592294, by rfl⟩ : syracuseStep 2123059 = 3184589) B3184589
theorem B2830745 : Blo 1885435 2830745 := bstep (se 2 (by rfl) ⟨1061529, by rfl⟩ : syracuseStep 2830745 = 2123059) B2123059
theorem B1887163 : Blo 1885435 1887163 := bstep (se 1 (by rfl) ⟨1415372, by rfl⟩ : syracuseStep 1887163 = 2830745) B2830745
theorem B3148301 : Blo 1885435 3148301 := bbase (se 3 (by rfl) ⟨590306, by rfl⟩ : syracuseStep 3148301 = 1180613) (by norm_num)
theorem B2098867 : Blo 1885435 2098867 := bstep (se 1 (by rfl) ⟨1574150, by rfl⟩ : syracuseStep 2098867 = 3148301) B3148301
theorem B44775829 : Blo 1885435 44775829 := bstep (se 6 (by rfl) ⟨1049433, by rfl⟩ : syracuseStep 44775829 = 2098867) B2098867
theorem B238804421 : Blo 1885435 238804421 := bstep (se 4 (by rfl) ⟨22387914, by rfl⟩ : syracuseStep 238804421 = 44775829) B44775829
theorem B636811789 : Blo 1885435 636811789 := bstep (se 3 (by rfl) ⟨119402210, by rfl⟩ : syracuseStep 636811789 = 238804421) B238804421
theorem B849082385 : Blo 1885435 849082385 := bstep (se 2 (by rfl) ⟨318405894, by rfl⟩ : syracuseStep 849082385 = 636811789) B636811789
theorem B2264219693 : Blo 1885435 2264219693 := bstep (se 3 (by rfl) ⟨424541192, by rfl⟩ : syracuseStep 2264219693 = 849082385) B849082385
theorem B1509479795 : Blo 1885435 1509479795 := bstep (se 1 (by rfl) ⟨1132109846, by rfl⟩ : syracuseStep 1509479795 = 2264219693) B2264219693
theorem B1006319863 : Blo 1885435 1006319863 := bstep (se 1 (by rfl) ⟨754739897, by rfl⟩ : syracuseStep 1006319863 = 1509479795) B1509479795
theorem B1341759817 : Blo 1885435 1341759817 := bstep (se 2 (by rfl) ⟨503159931, by rfl⟩ : syracuseStep 1341759817 = 1006319863) B1006319863
theorem B1789013089 : Blo 1885435 1789013089 := bstep (se 2 (by rfl) ⟨670879908, by rfl⟩ : syracuseStep 1789013089 = 1341759817) B1341759817
theorem B2385350785 : Blo 1885435 2385350785 := bstep (se 2 (by rfl) ⟨894506544, by rfl⟩ : syracuseStep 2385350785 = 1789013089) B1789013089
theorem B3180467713 : Blo 1885435 3180467713 := bstep (se 2 (by rfl) ⟨1192675392, by rfl⟩ : syracuseStep 3180467713 = 2385350785) B2385350785
theorem B4240623617 : Blo 1885435 4240623617 := bstep (se 2 (by rfl) ⟨1590233856, by rfl⟩ : syracuseStep 4240623617 = 3180467713) B3180467713
theorem B2827082411 : Blo 1885435 2827082411 := bstep (se 1 (by rfl) ⟨2120311808, by rfl⟩ : syracuseStep 2827082411 = 4240623617) B4240623617
theorem B1884721607 : Blo 1885435 1884721607 := bstep (se 1 (by rfl) ⟨1413541205, by rfl⟩ : syracuseStep 1884721607 = 2827082411) B2827082411
theorem B1256481071 : Blo 1885435 1256481071 := bstep (se 1 (by rfl) ⟨942360803, by rfl⟩ : syracuseStep 1256481071 = 1884721607) B1884721607
theorem B837654047 : Blo 1885435 837654047 := bstep (se 1 (by rfl) ⟨628240535, by rfl⟩ : syracuseStep 837654047 = 1256481071) B1256481071
theorem B558436031 : Blo 1885435 558436031 := bstep (se 1 (by rfl) ⟨418827023, by rfl⟩ : syracuseStep 558436031 = 837654047) B837654047
theorem B372290687 : Blo 1885435 372290687 := bstep (se 1 (by rfl) ⟨279218015, by rfl⟩ : syracuseStep 372290687 = 558436031) B558436031
theorem B248193791 : Blo 1885435 248193791 := bstep (se 1 (by rfl) ⟨186145343, by rfl⟩ : syracuseStep 248193791 = 372290687) B372290687
theorem B165462527 : Blo 1885435 165462527 := bstep (se 1 (by rfl) ⟨124096895, by rfl⟩ : syracuseStep 165462527 = 248193791) B248193791
theorem B110308351 : Blo 1885435 110308351 := bstep (se 1 (by rfl) ⟨82731263, by rfl⟩ : syracuseStep 110308351 = 165462527) B165462527
theorem B147077801 : Blo 1885435 147077801 := bstep (se 2 (by rfl) ⟨55154175, by rfl⟩ : syracuseStep 147077801 = 110308351) B110308351
theorem B98051867 : Blo 1885435 98051867 := bstep (se 1 (by rfl) ⟨73538900, by rfl⟩ : syracuseStep 98051867 = 147077801) B147077801
theorem B65367911 : Blo 1885435 65367911 := bstep (se 1 (by rfl) ⟨49025933, by rfl⟩ : syracuseStep 65367911 = 98051867) B98051867
theorem B43578607 : Blo 1885435 43578607 := bstep (se 1 (by rfl) ⟨32683955, by rfl⟩ : syracuseStep 43578607 = 65367911) B65367911
theorem B58104809 : Blo 1885435 58104809 := bstep (se 2 (by rfl) ⟨21789303, by rfl⟩ : syracuseStep 58104809 = 43578607) B43578607
theorem B38736539 : Blo 1885435 38736539 := bstep (se 1 (by rfl) ⟨29052404, by rfl⟩ : syracuseStep 38736539 = 58104809) B58104809
theorem B25824359 : Blo 1885435 25824359 := bstep (se 1 (by rfl) ⟨19368269, by rfl⟩ : syracuseStep 25824359 = 38736539) B38736539
theorem B17216239 : Blo 1885435 17216239 := bstep (se 1 (by rfl) ⟨12912179, by rfl⟩ : syracuseStep 17216239 = 25824359) B25824359
theorem B22954985 : Blo 1885435 22954985 := bstep (se 2 (by rfl) ⟨8608119, by rfl⟩ : syracuseStep 22954985 = 17216239) B17216239
theorem B15303323 : Blo 1885435 15303323 := bstep (se 1 (by rfl) ⟨11477492, by rfl⟩ : syracuseStep 15303323 = 22954985) B22954985
theorem B10202215 : Blo 1885435 10202215 := bstep (se 1 (by rfl) ⟨7651661, by rfl⟩ : syracuseStep 10202215 = 15303323) B15303323
theorem B13602953 : Blo 1885435 13602953 := bstep (se 2 (by rfl) ⟨5101107, by rfl⟩ : syracuseStep 13602953 = 10202215) B10202215
theorem B9068635 : Blo 1885435 9068635 := bstep (se 1 (by rfl) ⟨6801476, by rfl⟩ : syracuseStep 9068635 = 13602953) B13602953
theorem B12091513 : Blo 1885435 12091513 := bstep (se 2 (by rfl) ⟨4534317, by rfl⟩ : syracuseStep 12091513 = 9068635) B9068635
theorem B16122017 : Blo 1885435 16122017 := bstep (se 2 (by rfl) ⟨6045756, by rfl⟩ : syracuseStep 16122017 = 12091513) B12091513
theorem B10748011 : Blo 1885435 10748011 := bstep (se 1 (by rfl) ⟨8061008, by rfl⟩ : syracuseStep 10748011 = 16122017) B16122017
theorem B14330681 : Blo 1885435 14330681 := bstep (se 2 (by rfl) ⟨5374005, by rfl⟩ : syracuseStep 14330681 = 10748011) B10748011
theorem B9553787 : Blo 1885435 9553787 := bstep (se 1 (by rfl) ⟨7165340, by rfl⟩ : syracuseStep 9553787 = 14330681) B14330681
theorem B6369191 : Blo 1885435 6369191 := bstep (se 1 (by rfl) ⟨4776893, by rfl⟩ : syracuseStep 6369191 = 9553787) B9553787
theorem B4246127 : Blo 1885435 4246127 := bstep (se 1 (by rfl) ⟨3184595, by rfl⟩ : syracuseStep 4246127 = 6369191) B6369191
theorem B2830751 : Blo 1885435 2830751 := bstep (se 1 (by rfl) ⟨2123063, by rfl⟩ : syracuseStep 2830751 = 4246127) B4246127
theorem B1887167 : Blo 1885435 1887167 := bstep (se 1 (by rfl) ⟨1415375, by rfl⟩ : syracuseStep 1887167 = 2830751) B2830751
theorem B2830757 : Blo 1885435 2830757 := bbase (se 4 (by rfl) ⟨265383, by rfl⟩ : syracuseStep 2830757 = 530767) (by norm_num)
theorem B1887171 : Blo 1885435 1887171 := bstep (se 1 (by rfl) ⟨1415378, by rfl⟩ : syracuseStep 1887171 = 2830757) B2830757
theorem B2388457 : Blo 1885435 2388457 := bbase (se 2 (by rfl) ⟨895671, by rfl⟩ : syracuseStep 2388457 = 1791343) (by norm_num)
theorem B3184609 : Blo 1885435 3184609 := bstep (se 2 (by rfl) ⟨1194228, by rfl⟩ : syracuseStep 3184609 = 2388457) B2388457
theorem B4246145 : Blo 1885435 4246145 := bstep (se 2 (by rfl) ⟨1592304, by rfl⟩ : syracuseStep 4246145 = 3184609) B3184609
theorem B2830763 : Blo 1885435 2830763 := bstep (se 1 (by rfl) ⟨2123072, by rfl⟩ : syracuseStep 2830763 = 4246145) B4246145
theorem B1887175 : Blo 1885435 1887175 := bstep (se 1 (by rfl) ⟨1415381, by rfl⟩ : syracuseStep 1887175 = 2830763) B2830763
theorem B2123077 : Blo 1885435 2123077 := bbase (se 4 (by rfl) ⟨199038, by rfl⟩ : syracuseStep 2123077 = 398077) (by norm_num)
theorem B2830769 : Blo 1885435 2830769 := bstep (se 2 (by rfl) ⟨1061538, by rfl⟩ : syracuseStep 2830769 = 2123077) B2123077
theorem B1887179 : Blo 1885435 1887179 := bstep (se 1 (by rfl) ⟨1415384, by rfl⟩ : syracuseStep 1887179 = 2830769) B2830769
theorem B3582701 : Blo 1885435 3582701 := bbase (se 3 (by rfl) ⟨671756, by rfl⟩ : syracuseStep 3582701 = 1343513) (by norm_num)
theorem B2388467 : Blo 1885435 2388467 := bstep (se 1 (by rfl) ⟨1791350, by rfl⟩ : syracuseStep 2388467 = 3582701) B3582701
theorem B6369245 : Blo 1885435 6369245 := bstep (se 3 (by rfl) ⟨1194233, by rfl⟩ : syracuseStep 6369245 = 2388467) B2388467
theorem B4246163 : Blo 1885435 4246163 := bstep (se 1 (by rfl) ⟨3184622, by rfl⟩ : syracuseStep 4246163 = 6369245) B6369245
theorem B2830775 : Blo 1885435 2830775 := bstep (se 1 (by rfl) ⟨2123081, by rfl⟩ : syracuseStep 2830775 = 4246163) B4246163
theorem B1887183 : Blo 1885435 1887183 := bstep (se 1 (by rfl) ⟨1415387, by rfl⟩ : syracuseStep 1887183 = 2830775) B2830775
theorem B2830781 : Blo 1885435 2830781 := bbase (se 3 (by rfl) ⟨530771, by rfl⟩ : syracuseStep 2830781 = 1061543) (by norm_num)
theorem B1887187 : Blo 1885435 1887187 := bstep (se 1 (by rfl) ⟨1415390, by rfl⟩ : syracuseStep 1887187 = 2830781) B2830781
theorem B4246181 : Blo 1885435 4246181 := bbase (se 4 (by rfl) ⟨398079, by rfl⟩ : syracuseStep 4246181 = 796159) (by norm_num)
theorem B2830787 : Blo 1885435 2830787 := bstep (se 1 (by rfl) ⟨2123090, by rfl⟩ : syracuseStep 2830787 = 4246181) B4246181
theorem B1887191 : Blo 1885435 1887191 := bstep (se 1 (by rfl) ⟨1415393, by rfl⟩ : syracuseStep 1887191 = 2830787) B2830787
theorem B4776965 : Blo 1885435 4776965 := bbase (se 4 (by rfl) ⟨447840, by rfl⟩ : syracuseStep 4776965 = 895681) (by norm_num)
theorem B3184643 : Blo 1885435 3184643 := bstep (se 1 (by rfl) ⟨2388482, by rfl⟩ : syracuseStep 3184643 = 4776965) B4776965
theorem B2123095 : Blo 1885435 2123095 := bstep (se 1 (by rfl) ⟨1592321, by rfl⟩ : syracuseStep 2123095 = 3184643) B3184643
theorem B2830793 : Blo 1885435 2830793 := bstep (se 2 (by rfl) ⟨1061547, by rfl⟩ : syracuseStep 2830793 = 2123095) B2123095
theorem B1887195 : Blo 1885435 1887195 := bstep (se 1 (by rfl) ⟨1415396, by rfl⟩ : syracuseStep 1887195 = 2830793) B2830793
theorem B4030573 : Blo 1885435 4030573 := bbase (se 3 (by rfl) ⟨755732, by rfl⟩ : syracuseStep 4030573 = 1511465) (by norm_num)
theorem B5374097 : Blo 1885435 5374097 := bstep (se 2 (by rfl) ⟨2015286, by rfl⟩ : syracuseStep 5374097 = 4030573) B4030573
theorem B3582731 : Blo 1885435 3582731 := bstep (se 1 (by rfl) ⟨2687048, by rfl⟩ : syracuseStep 3582731 = 5374097) B5374097
theorem B9553949 : Blo 1885435 9553949 := bstep (se 3 (by rfl) ⟨1791365, by rfl⟩ : syracuseStep 9553949 = 3582731) B3582731
theorem B6369299 : Blo 1885435 6369299 := bstep (se 1 (by rfl) ⟨4776974, by rfl⟩ : syracuseStep 6369299 = 9553949) B9553949
theorem B4246199 : Blo 1885435 4246199 := bstep (se 1 (by rfl) ⟨3184649, by rfl⟩ : syracuseStep 4246199 = 6369299) B6369299
theorem B2830799 : Blo 1885435 2830799 := bstep (se 1 (by rfl) ⟨2123099, by rfl⟩ : syracuseStep 2830799 = 4246199) B4246199
theorem B1887199 : Blo 1885435 1887199 := bstep (se 1 (by rfl) ⟨1415399, by rfl⟩ : syracuseStep 1887199 = 2830799) B2830799
theorem B2830805 : Blo 1885435 2830805 := bbase (se 7 (by rfl) ⟨33173, by rfl⟩ : syracuseStep 2830805 = 66347) (by norm_num)
theorem B1887203 : Blo 1885435 1887203 := bstep (se 1 (by rfl) ⟨1415402, by rfl⟩ : syracuseStep 1887203 = 2830805) B2830805
theorem B7165493 : Blo 1885435 7165493 := bbase (se 5 (by rfl) ⟨335882, by rfl⟩ : syracuseStep 7165493 = 671765) (by norm_num)
theorem B4776995 : Blo 1885435 4776995 := bstep (se 1 (by rfl) ⟨3582746, by rfl⟩ : syracuseStep 4776995 = 7165493) B7165493
theorem B3184663 : Blo 1885435 3184663 := bstep (se 1 (by rfl) ⟨2388497, by rfl⟩ : syracuseStep 3184663 = 4776995) B4776995
theorem B4246217 : Blo 1885435 4246217 := bstep (se 2 (by rfl) ⟨1592331, by rfl⟩ : syracuseStep 4246217 = 3184663) B3184663
theorem B2830811 : Blo 1885435 2830811 := bstep (se 1 (by rfl) ⟨2123108, by rfl⟩ : syracuseStep 2830811 = 4246217) B4246217
theorem B1887207 : Blo 1885435 1887207 := bstep (se 1 (by rfl) ⟨1415405, by rfl⟩ : syracuseStep 1887207 = 2830811) B2830811
theorem B2123113 : Blo 1885435 2123113 := bbase (se 2 (by rfl) ⟨796167, by rfl⟩ : syracuseStep 2123113 = 1592335) (by norm_num)
theorem B2830817 : Blo 1885435 2830817 := bstep (se 2 (by rfl) ⟨1061556, by rfl⟩ : syracuseStep 2830817 = 2123113) B2123113
theorem B1887211 : Blo 1885435 1887211 := bstep (se 1 (by rfl) ⟨1415408, by rfl⟩ : syracuseStep 1887211 = 2830817) B2830817
theorem B3631645 : Blo 1885435 3631645 := bbase (se 3 (by rfl) ⟨680933, by rfl⟩ : syracuseStep 3631645 = 1361867) (by norm_num)
theorem B4842193 : Blo 1885435 4842193 := bstep (se 2 (by rfl) ⟨1815822, by rfl⟩ : syracuseStep 4842193 = 3631645) B3631645
theorem B6456257 : Blo 1885435 6456257 := bstep (se 2 (by rfl) ⟨2421096, by rfl⟩ : syracuseStep 6456257 = 4842193) B4842193
theorem B4304171 : Blo 1885435 4304171 := bstep (se 1 (by rfl) ⟨3228128, by rfl⟩ : syracuseStep 4304171 = 6456257) B6456257
theorem B2869447 : Blo 1885435 2869447 := bstep (se 1 (by rfl) ⟨2152085, by rfl⟩ : syracuseStep 2869447 = 4304171) B4304171
theorem B3825929 : Blo 1885435 3825929 := bstep (se 2 (by rfl) ⟨1434723, by rfl⟩ : syracuseStep 3825929 = 2869447) B2869447
theorem B2550619 : Blo 1885435 2550619 := bstep (se 1 (by rfl) ⟨1912964, by rfl⟩ : syracuseStep 2550619 = 3825929) B3825929
theorem B13603301 : Blo 1885435 13603301 := bstep (se 4 (by rfl) ⟨1275309, by rfl⟩ : syracuseStep 13603301 = 2550619) B2550619
theorem B9068867 : Blo 1885435 9068867 := bstep (se 1 (by rfl) ⟨6801650, by rfl⟩ : syracuseStep 9068867 = 13603301) B13603301
theorem B6045911 : Blo 1885435 6045911 := bstep (se 1 (by rfl) ⟨4534433, by rfl⟩ : syracuseStep 6045911 = 9068867) B9068867
theorem B4030607 : Blo 1885435 4030607 := bstep (se 1 (by rfl) ⟨3022955, by rfl⟩ : syracuseStep 4030607 = 6045911) B6045911
theorem B10748285 : Blo 1885435 10748285 := bstep (se 3 (by rfl) ⟨2015303, by rfl⟩ : syracuseStep 10748285 = 4030607) B4030607
theorem B7165523 : Blo 1885435 7165523 := bstep (se 1 (by rfl) ⟨5374142, by rfl⟩ : syracuseStep 7165523 = 10748285) B10748285
theorem B4777015 : Blo 1885435 4777015 := bstep (se 1 (by rfl) ⟨3582761, by rfl⟩ : syracuseStep 4777015 = 7165523) B7165523
theorem B6369353 : Blo 1885435 6369353 := bstep (se 2 (by rfl) ⟨2388507, by rfl⟩ : syracuseStep 6369353 = 4777015) B4777015
theorem B4246235 : Blo 1885435 4246235 := bstep (se 1 (by rfl) ⟨3184676, by rfl⟩ : syracuseStep 4246235 = 6369353) B6369353
theorem B2830823 : Blo 1885435 2830823 := bstep (se 1 (by rfl) ⟨2123117, by rfl⟩ : syracuseStep 2830823 = 4246235) B4246235
theorem B1887215 : Blo 1885435 1887215 := bstep (se 1 (by rfl) ⟨1415411, by rfl⟩ : syracuseStep 1887215 = 2830823) B2830823
theorem B2830829 : Blo 1885435 2830829 := bbase (se 3 (by rfl) ⟨530780, by rfl⟩ : syracuseStep 2830829 = 1061561) (by norm_num)
theorem B1887219 : Blo 1885435 1887219 := bstep (se 1 (by rfl) ⟨1415414, by rfl⟩ : syracuseStep 1887219 = 2830829) B2830829
theorem B4246253 : Blo 1885435 4246253 := bbase (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) (by norm_num)
theorem B2830835 : Blo 1885435 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B1887223 : Blo 1885435 1887223 := bstep (se 1 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 1887223 = 2830835) B2830835
theorem B2015317 : Blo 1885435 2015317 := bbase (se 8 (by rfl) ⟨11808, by rfl⟩ : syracuseStep 2015317 = 23617) (by norm_num)
theorem B2687089 : Blo 1885435 2687089 := bstep (se 2 (by rfl) ⟨1007658, by rfl⟩ : syracuseStep 2687089 = 2015317) B2015317
theorem B3582785 : Blo 1885435 3582785 := bstep (se 2 (by rfl) ⟨1343544, by rfl⟩ : syracuseStep 3582785 = 2687089) B2687089
theorem B2388523 : Blo 1885435 2388523 := bstep (se 1 (by rfl) ⟨1791392, by rfl⟩ : syracuseStep 2388523 = 3582785) B3582785
theorem B3184697 : Blo 1885435 3184697 := bstep (se 2 (by rfl) ⟨1194261, by rfl⟩ : syracuseStep 3184697 = 2388523) B2388523
theorem B2123131 : Blo 1885435 2123131 := bstep (se 1 (by rfl) ⟨1592348, by rfl⟩ : syracuseStep 2123131 = 3184697) B3184697
theorem B2830841 : Blo 1885435 2830841 := bstep (se 2 (by rfl) ⟨1061565, by rfl⟩ : syracuseStep 2830841 = 2123131) B2123131
theorem B1887227 : Blo 1885435 1887227 := bstep (se 1 (by rfl) ⟨1415420, by rfl⟩ : syracuseStep 1887227 = 2830841) B2830841
theorem B54413653 : Blo 1885435 54413653 := bbase (se 10 (by rfl) ⟨79707, by rfl⟩ : syracuseStep 54413653 = 159415) (by norm_num)
theorem B72551537 : Blo 1885435 72551537 := bstep (se 2 (by rfl) ⟨27206826, by rfl⟩ : syracuseStep 72551537 = 54413653) B54413653
theorem B48367691 : Blo 1885435 48367691 := bstep (se 1 (by rfl) ⟨36275768, by rfl⟩ : syracuseStep 48367691 = 72551537) B72551537
theorem B32245127 : Blo 1885435 32245127 := bstep (se 1 (by rfl) ⟨24183845, by rfl⟩ : syracuseStep 32245127 = 48367691) B48367691
theorem B21496751 : Blo 1885435 21496751 := bstep (se 1 (by rfl) ⟨16122563, by rfl⟩ : syracuseStep 21496751 = 32245127) B32245127
theorem B14331167 : Blo 1885435 14331167 := bstep (se 1 (by rfl) ⟨10748375, by rfl⟩ : syracuseStep 14331167 = 21496751) B21496751
theorem B9554111 : Blo 1885435 9554111 := bstep (se 1 (by rfl) ⟨7165583, by rfl⟩ : syracuseStep 9554111 = 14331167) B14331167
theorem B6369407 : Blo 1885435 6369407 := bstep (se 1 (by rfl) ⟨4777055, by rfl⟩ : syracuseStep 6369407 = 9554111) B9554111
theorem B4246271 : Blo 1885435 4246271 := bstep (se 1 (by rfl) ⟨3184703, by rfl⟩ : syracuseStep 4246271 = 6369407) B6369407
theorem B2830847 : Blo 1885435 2830847 := bstep (se 1 (by rfl) ⟨2123135, by rfl⟩ : syracuseStep 2830847 = 4246271) B4246271
theorem B1887231 : Blo 1885435 1887231 := bstep (se 1 (by rfl) ⟨1415423, by rfl⟩ : syracuseStep 1887231 = 2830847) B2830847
theorem B2830853 : Blo 1885435 2830853 := bbase (se 4 (by rfl) ⟨265392, by rfl⟩ : syracuseStep 2830853 = 530785) (by norm_num)
theorem B1887235 : Blo 1885435 1887235 := bstep (se 1 (by rfl) ⟨1415426, by rfl⟩ : syracuseStep 1887235 = 2830853) B2830853
theorem B3184717 : Blo 1885435 3184717 := bbase (se 3 (by rfl) ⟨597134, by rfl⟩ : syracuseStep 3184717 = 1194269) (by norm_num)
theorem B4246289 : Blo 1885435 4246289 := bstep (se 2 (by rfl) ⟨1592358, by rfl⟩ : syracuseStep 4246289 = 3184717) B3184717
theorem B2830859 : Blo 1885435 2830859 := bstep (se 1 (by rfl) ⟨2123144, by rfl⟩ : syracuseStep 2830859 = 4246289) B4246289
theorem B1887239 : Blo 1885435 1887239 := bstep (se 1 (by rfl) ⟨1415429, by rfl⟩ : syracuseStep 1887239 = 2830859) B2830859
theorem B2123149 : Blo 1885435 2123149 := bbase (se 3 (by rfl) ⟨398090, by rfl⟩ : syracuseStep 2123149 = 796181) (by norm_num)
theorem B2830865 : Blo 1885435 2830865 := bstep (se 2 (by rfl) ⟨1061574, by rfl⟩ : syracuseStep 2830865 = 2123149) B2123149
theorem B1887243 : Blo 1885435 1887243 := bstep (se 1 (by rfl) ⟨1415432, by rfl⟩ : syracuseStep 1887243 = 2830865) B2830865
theorem B6369461 : Blo 1885435 6369461 := bbase (se 5 (by rfl) ⟨298568, by rfl⟩ : syracuseStep 6369461 = 597137) (by norm_num)
theorem B4246307 : Blo 1885435 4246307 := bstep (se 1 (by rfl) ⟨3184730, by rfl⟩ : syracuseStep 4246307 = 6369461) B6369461
theorem B2830871 : Blo 1885435 2830871 := bstep (se 1 (by rfl) ⟨2123153, by rfl⟩ : syracuseStep 2830871 = 4246307) B4246307
theorem B1887247 : Blo 1885435 1887247 := bstep (se 1 (by rfl) ⟨1415435, by rfl⟩ : syracuseStep 1887247 = 2830871) B2830871
theorem B2830877 : Blo 1885435 2830877 := bbase (se 3 (by rfl) ⟨530789, by rfl⟩ : syracuseStep 2830877 = 1061579) (by norm_num)
theorem B1887251 : Blo 1885435 1887251 := bstep (se 1 (by rfl) ⟨1415438, by rfl⟩ : syracuseStep 1887251 = 2830877) B2830877
theorem B4246325 : Blo 1885435 4246325 := bbase (se 5 (by rfl) ⟨199046, by rfl⟩ : syracuseStep 4246325 = 398093) (by norm_num)
theorem B2830883 : Blo 1885435 2830883 := bstep (se 1 (by rfl) ⟨2123162, by rfl⟩ : syracuseStep 2830883 = 4246325) B4246325
theorem B1887255 : Blo 1885435 1887255 := bstep (se 1 (by rfl) ⟨1415441, by rfl⟩ : syracuseStep 1887255 = 2830883) B2830883
theorem B1913009 : Blo 1885435 1913009 := bbase (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) (by norm_num)
theorem B20405429 : Blo 1885435 20405429 := bstep (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) B1913009
theorem B13603619 : Blo 1885435 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B9069079 : Blo 1885435 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B12092105 : Blo 1885435 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B8061403 : Blo 1885435 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B10748537 : Blo 1885435 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B7165691 : Blo 1885435 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B4777127 : Blo 1885435 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B3184751 : Blo 1885435 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B2123167 : Blo 1885435 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B2830889 : Blo 1885435 2830889 := bstep (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) B2123167
theorem B1887259 : Blo 1885435 1887259 := bstep (se 1 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 1887259 = 2830889) B2830889
theorem B5896709 : Blo 1885435 5896709 := bbase (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) (by norm_num)
theorem B3931139 : Blo 1885435 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B2620759 : Blo 1885435 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B3494345 : Blo 1885435 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B9318253 : Blo 1885435 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B12424337 : Blo 1885435 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B8282891 : Blo 1885435 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B22087709 : Blo 1885435 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B235602229 : Blo 1885435 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B314136305 : Blo 1885435 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B209424203 : Blo 1885435 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B139616135 : Blo 1885435 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B93077423 : Blo 1885435 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B62051615 : Blo 1885435 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B41367743 : Blo 1885435 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B27578495 : Blo 1885435 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B18385663 : Blo 1885435 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B24514217 : Blo 1885435 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B16342811 : Blo 1885435 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B10895207 : Blo 1885435 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B29053885 : Blo 1885435 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B38738513 : Blo 1885435 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B25825675 : Blo 1885435 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B34434233 : Blo 1885435 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B22956155 : Blo 1885435 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B15304103 : Blo 1885435 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B10202735 : Blo 1885435 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B6801823 : Blo 1885435 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B9069097 : Blo 1885435 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B12092129 : Blo 1885435 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B8061419 : Blo 1885435 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B5374279 : Blo 1885435 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B7165705 : Blo 1885435 7165705 := bstep (se 2 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 7165705 = 5374279) B5374279
theorem B9554273 : Blo 1885435 9554273 := bstep (se 2 (by rfl) ⟨3582852, by rfl⟩ : syracuseStep 9554273 = 7165705) B7165705
theorem B6369515 : Blo 1885435 6369515 := bstep (se 1 (by rfl) ⟨4777136, by rfl⟩ : syracuseStep 6369515 = 9554273) B9554273
theorem B4246343 : Blo 1885435 4246343 := bstep (se 1 (by rfl) ⟨3184757, by rfl⟩ : syracuseStep 4246343 = 6369515) B6369515
theorem B2830895 : Blo 1885435 2830895 := bstep (se 1 (by rfl) ⟨2123171, by rfl⟩ : syracuseStep 2830895 = 4246343) B4246343
theorem B1887263 : Blo 1885435 1887263 := bstep (se 1 (by rfl) ⟨1415447, by rfl⟩ : syracuseStep 1887263 = 2830895) B2830895
theorem B2830901 : Blo 1885435 2830901 := bbase (se 5 (by rfl) ⟨132698, by rfl⟩ : syracuseStep 2830901 = 265397) (by norm_num)
theorem B1887267 : Blo 1885435 1887267 := bstep (se 1 (by rfl) ⟨1415450, by rfl⟩ : syracuseStep 1887267 = 2830901) B2830901
theorem B4777157 : Blo 1885435 4777157 := bbase (se 4 (by rfl) ⟨447858, by rfl⟩ : syracuseStep 4777157 = 895717) (by norm_num)
theorem B3184771 : Blo 1885435 3184771 := bstep (se 1 (by rfl) ⟨2388578, by rfl⟩ : syracuseStep 3184771 = 4777157) B4777157
theorem B4246361 : Blo 1885435 4246361 := bstep (se 2 (by rfl) ⟨1592385, by rfl⟩ : syracuseStep 4246361 = 3184771) B3184771
theorem B2830907 : Blo 1885435 2830907 := bstep (se 1 (by rfl) ⟨2123180, by rfl⟩ : syracuseStep 2830907 = 4246361) B4246361
theorem B1887271 : Blo 1885435 1887271 := bstep (se 1 (by rfl) ⟨1415453, by rfl⟩ : syracuseStep 1887271 = 2830907) B2830907
theorem B2123185 : Blo 1885435 2123185 := bbase (se 2 (by rfl) ⟨796194, by rfl⟩ : syracuseStep 2123185 = 1592389) (by norm_num)
theorem B2830913 : Blo 1885435 2830913 := bstep (se 2 (by rfl) ⟨1061592, by rfl⟩ : syracuseStep 2830913 = 2123185) B2123185
theorem B1887275 : Blo 1885435 1887275 := bstep (se 1 (by rfl) ⟨1415456, by rfl⟩ : syracuseStep 1887275 = 2830913) B2830913
theorem B5374325 : Blo 1885435 5374325 := bbase (se 5 (by rfl) ⟨251921, by rfl⟩ : syracuseStep 5374325 = 503843) (by norm_num)
theorem B3582883 : Blo 1885435 3582883 := bstep (se 1 (by rfl) ⟨2687162, by rfl⟩ : syracuseStep 3582883 = 5374325) B5374325
theorem B4777177 : Blo 1885435 4777177 := bstep (se 2 (by rfl) ⟨1791441, by rfl⟩ : syracuseStep 4777177 = 3582883) B3582883
theorem B6369569 : Blo 1885435 6369569 := bstep (se 2 (by rfl) ⟨2388588, by rfl⟩ : syracuseStep 6369569 = 4777177) B4777177
theorem B4246379 : Blo 1885435 4246379 := bstep (se 1 (by rfl) ⟨3184784, by rfl⟩ : syracuseStep 4246379 = 6369569) B6369569
theorem B2830919 : Blo 1885435 2830919 := bstep (se 1 (by rfl) ⟨2123189, by rfl⟩ : syracuseStep 2830919 = 4246379) B4246379
theorem B1887279 : Blo 1885435 1887279 := bstep (se 1 (by rfl) ⟨1415459, by rfl⟩ : syracuseStep 1887279 = 2830919) B2830919
theorem B2830925 : Blo 1885435 2830925 := bbase (se 3 (by rfl) ⟨530798, by rfl⟩ : syracuseStep 2830925 = 1061597) (by norm_num)
theorem B1887283 : Blo 1885435 1887283 := bstep (se 1 (by rfl) ⟨1415462, by rfl⟩ : syracuseStep 1887283 = 2830925) B2830925
theorem B4246397 : Blo 1885435 4246397 := bbase (se 3 (by rfl) ⟨796199, by rfl⟩ : syracuseStep 4246397 = 1592399) (by norm_num)
theorem B2830931 : Blo 1885435 2830931 := bstep (se 1 (by rfl) ⟨2123198, by rfl⟩ : syracuseStep 2830931 = 4246397) B4246397
theorem B1887287 : Blo 1885435 1887287 := bstep (se 1 (by rfl) ⟨1415465, by rfl⟩ : syracuseStep 1887287 = 2830931) B2830931
theorem B3184805 : Blo 1885435 3184805 := bbase (se 4 (by rfl) ⟨298575, by rfl⟩ : syracuseStep 3184805 = 597151) (by norm_num)
theorem B2123203 : Blo 1885435 2123203 := bstep (se 1 (by rfl) ⟨1592402, by rfl⟩ : syracuseStep 2123203 = 3184805) B3184805
theorem B2830937 : Blo 1885435 2830937 := bstep (se 2 (by rfl) ⟨1061601, by rfl⟩ : syracuseStep 2830937 = 2123203) B2123203
theorem B1887291 : Blo 1885435 1887291 := bstep (se 1 (by rfl) ⟨1415468, by rfl⟩ : syracuseStep 1887291 = 2830937) B2830937
theorem B2015389 : Blo 1885435 2015389 := bbase (se 3 (by rfl) ⟨377885, by rfl⟩ : syracuseStep 2015389 = 755771) (by norm_num)
theorem B2687185 : Blo 1885435 2687185 := bstep (se 2 (by rfl) ⟨1007694, by rfl⟩ : syracuseStep 2687185 = 2015389) B2015389
theorem B14331653 : Blo 1885435 14331653 := bstep (se 4 (by rfl) ⟨1343592, by rfl⟩ : syracuseStep 14331653 = 2687185) B2687185
theorem B9554435 : Blo 1885435 9554435 := bstep (se 1 (by rfl) ⟨7165826, by rfl⟩ : syracuseStep 9554435 = 14331653) B14331653
theorem B6369623 : Blo 1885435 6369623 := bstep (se 1 (by rfl) ⟨4777217, by rfl⟩ : syracuseStep 6369623 = 9554435) B9554435
theorem B4246415 : Blo 1885435 4246415 := bstep (se 1 (by rfl) ⟨3184811, by rfl⟩ : syracuseStep 4246415 = 6369623) B6369623
theorem B2830943 : Blo 1885435 2830943 := bstep (se 1 (by rfl) ⟨2123207, by rfl⟩ : syracuseStep 2830943 = 4246415) B4246415
theorem B1887295 : Blo 1885435 1887295 := bstep (se 1 (by rfl) ⟨1415471, by rfl⟩ : syracuseStep 1887295 = 2830943) B2830943
theorem B2830949 : Blo 1885435 2830949 := bbase (se 4 (by rfl) ⟨265401, by rfl⟩ : syracuseStep 2830949 = 530803) (by norm_num)
theorem B1887299 : Blo 1885435 1887299 := bstep (se 1 (by rfl) ⟨1415474, by rfl⟩ : syracuseStep 1887299 = 2830949) B2830949
theorem B2687197 : Blo 1885435 2687197 := bbase (se 3 (by rfl) ⟨503849, by rfl⟩ : syracuseStep 2687197 = 1007699) (by norm_num)
theorem B3582929 : Blo 1885435 3582929 := bstep (se 2 (by rfl) ⟨1343598, by rfl⟩ : syracuseStep 3582929 = 2687197) B2687197
theorem B2388619 : Blo 1885435 2388619 := bstep (se 1 (by rfl) ⟨1791464, by rfl⟩ : syracuseStep 2388619 = 3582929) B3582929
theorem B3184825 : Blo 1885435 3184825 := bstep (se 2 (by rfl) ⟨1194309, by rfl⟩ : syracuseStep 3184825 = 2388619) B2388619
theorem B4246433 : Blo 1885435 4246433 := bstep (se 2 (by rfl) ⟨1592412, by rfl⟩ : syracuseStep 4246433 = 3184825) B3184825
theorem B2830955 : Blo 1885435 2830955 := bstep (se 1 (by rfl) ⟨2123216, by rfl⟩ : syracuseStep 2830955 = 4246433) B4246433
theorem B1887303 : Blo 1885435 1887303 := bstep (se 1 (by rfl) ⟨1415477, by rfl⟩ : syracuseStep 1887303 = 2830955) B2830955
theorem B2123221 : Blo 1885435 2123221 := bbase (se 7 (by rfl) ⟨24881, by rfl⟩ : syracuseStep 2123221 = 49763) (by norm_num)
theorem B2830961 : Blo 1885435 2830961 := bstep (se 2 (by rfl) ⟨1061610, by rfl⟩ : syracuseStep 2830961 = 2123221) B2123221
theorem B1887307 : Blo 1885435 1887307 := bstep (se 1 (by rfl) ⟨1415480, by rfl⟩ : syracuseStep 1887307 = 2830961) B2830961
theorem B2388629 : Blo 1885435 2388629 := bbase (se 6 (by rfl) ⟨55983, by rfl⟩ : syracuseStep 2388629 = 111967) (by norm_num)
theorem B6369677 : Blo 1885435 6369677 := bstep (se 3 (by rfl) ⟨1194314, by rfl⟩ : syracuseStep 6369677 = 2388629) B2388629
theorem B4246451 : Blo 1885435 4246451 := bstep (se 1 (by rfl) ⟨3184838, by rfl⟩ : syracuseStep 4246451 = 6369677) B6369677
theorem B2830967 : Blo 1885435 2830967 := bstep (se 1 (by rfl) ⟨2123225, by rfl⟩ : syracuseStep 2830967 = 4246451) B4246451
theorem B1887311 : Blo 1885435 1887311 := bstep (se 1 (by rfl) ⟨1415483, by rfl⟩ : syracuseStep 1887311 = 2830967) B2830967
theorem B2830973 : Blo 1885435 2830973 := bbase (se 3 (by rfl) ⟨530807, by rfl⟩ : syracuseStep 2830973 = 1061615) (by norm_num)
theorem B1887315 : Blo 1885435 1887315 := bstep (se 1 (by rfl) ⟨1415486, by rfl⟩ : syracuseStep 1887315 = 2830973) B2830973
theorem B4246469 : Blo 1885435 4246469 := bbase (se 4 (by rfl) ⟨398106, by rfl⟩ : syracuseStep 4246469 = 796213) (by norm_num)
theorem B2830979 : Blo 1885435 2830979 := bstep (se 1 (by rfl) ⟨2123234, by rfl⟩ : syracuseStep 2830979 = 4246469) B4246469
theorem B1887319 : Blo 1885435 1887319 := bstep (se 1 (by rfl) ⟨1415489, by rfl⟩ : syracuseStep 1887319 = 2830979) B2830979
theorem B3401021 : Blo 1885435 3401021 := bbase (se 3 (by rfl) ⟨637691, by rfl⟩ : syracuseStep 3401021 = 1275383) (by norm_num)
theorem B2267347 : Blo 1885435 2267347 := bstep (se 1 (by rfl) ⟨1700510, by rfl⟩ : syracuseStep 2267347 = 3401021) B3401021
theorem B3023129 : Blo 1885435 3023129 := bstep (se 2 (by rfl) ⟨1133673, by rfl⟩ : syracuseStep 3023129 = 2267347) B2267347
theorem B8061677 : Blo 1885435 8061677 := bstep (se 3 (by rfl) ⟨1511564, by rfl⟩ : syracuseStep 8061677 = 3023129) B3023129
theorem B5374451 : Blo 1885435 5374451 := bstep (se 1 (by rfl) ⟨4030838, by rfl⟩ : syracuseStep 5374451 = 8061677) B8061677
theorem B3582967 : Blo 1885435 3582967 := bstep (se 1 (by rfl) ⟨2687225, by rfl⟩ : syracuseStep 3582967 = 5374451) B5374451
theorem B4777289 : Blo 1885435 4777289 := bstep (se 2 (by rfl) ⟨1791483, by rfl⟩ : syracuseStep 4777289 = 3582967) B3582967
theorem B3184859 : Blo 1885435 3184859 := bstep (se 1 (by rfl) ⟨2388644, by rfl⟩ : syracuseStep 3184859 = 4777289) B4777289
theorem B2123239 : Blo 1885435 2123239 := bstep (se 1 (by rfl) ⟨1592429, by rfl⟩ : syracuseStep 2123239 = 3184859) B3184859
theorem B2830985 : Blo 1885435 2830985 := bstep (se 2 (by rfl) ⟨1061619, by rfl⟩ : syracuseStep 2830985 = 2123239) B2123239
theorem B1887323 : Blo 1885435 1887323 := bstep (se 1 (by rfl) ⟨1415492, by rfl⟩ : syracuseStep 1887323 = 2830985) B2830985
theorem B9554597 : Blo 1885435 9554597 := bbase (se 4 (by rfl) ⟨895743, by rfl⟩ : syracuseStep 9554597 = 1791487) (by norm_num)
theorem B6369731 : Blo 1885435 6369731 := bstep (se 1 (by rfl) ⟨4777298, by rfl⟩ : syracuseStep 6369731 = 9554597) B9554597
theorem B4246487 : Blo 1885435 4246487 := bstep (se 1 (by rfl) ⟨3184865, by rfl⟩ : syracuseStep 4246487 = 6369731) B6369731
theorem B2830991 : Blo 1885435 2830991 := bstep (se 1 (by rfl) ⟨2123243, by rfl⟩ : syracuseStep 2830991 = 4246487) B4246487
theorem B1887327 : Blo 1885435 1887327 := bstep (se 1 (by rfl) ⟨1415495, by rfl⟩ : syracuseStep 1887327 = 2830991) B2830991
theorem B2830997 : Blo 1885435 2830997 := bbase (se 6 (by rfl) ⟨66351, by rfl⟩ : syracuseStep 2830997 = 132703) (by norm_num)
theorem B1887331 : Blo 1885435 1887331 := bstep (se 1 (by rfl) ⟨1415498, by rfl⟩ : syracuseStep 1887331 = 2830997) B2830997
theorem B7263749 : Blo 1885435 7263749 := bbase (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) (by norm_num)
theorem B4842499 : Blo 1885435 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B6456665 : Blo 1885435 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B17217773 : Blo 1885435 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B11478515 : Blo 1885435 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B30609373 : Blo 1885435 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B40812497 : Blo 1885435 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B27208331 : Blo 1885435 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B18138887 : Blo 1885435 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B12092591 : Blo 1885435 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B8061727 : Blo 1885435 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B10748969 : Blo 1885435 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B7165979 : Blo 1885435 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B4777319 : Blo 1885435 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B3184879 : Blo 1885435 3184879 := bstep (se 1 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 3184879 = 4777319) B4777319
theorem B4246505 : Blo 1885435 4246505 := bstep (se 2 (by rfl) ⟨1592439, by rfl⟩ : syracuseStep 4246505 = 3184879) B3184879
theorem B2831003 : Blo 1885435 2831003 := bstep (se 1 (by rfl) ⟨2123252, by rfl⟩ : syracuseStep 2831003 = 4246505) B4246505
theorem B1887335 : Blo 1885435 1887335 := bstep (se 1 (by rfl) ⟨1415501, by rfl⟩ : syracuseStep 1887335 = 2831003) B2831003
theorem B2123257 : Blo 1885435 2123257 := bbase (se 2 (by rfl) ⟨796221, by rfl⟩ : syracuseStep 2123257 = 1592443) (by norm_num)
theorem B2831009 : Blo 1885435 2831009 := bstep (se 2 (by rfl) ⟨1061628, by rfl⟩ : syracuseStep 2831009 = 2123257) B2123257
theorem B1887339 : Blo 1885435 1887339 := bstep (se 1 (by rfl) ⟨1415504, by rfl⟩ : syracuseStep 1887339 = 2831009) B2831009
theorem B4534741 : Blo 1885435 4534741 := bbase (se 7 (by rfl) ⟨53141, by rfl⟩ : syracuseStep 4534741 = 106283) (by norm_num)
theorem B6046321 : Blo 1885435 6046321 := bstep (se 2 (by rfl) ⟨2267370, by rfl⟩ : syracuseStep 6046321 = 4534741) B4534741
theorem B8061761 : Blo 1885435 8061761 := bstep (se 2 (by rfl) ⟨3023160, by rfl⟩ : syracuseStep 8061761 = 6046321) B6046321
theorem B5374507 : Blo 1885435 5374507 := bstep (se 1 (by rfl) ⟨4030880, by rfl⟩ : syracuseStep 5374507 = 8061761) B8061761
theorem B7166009 : Blo 1885435 7166009 := bstep (se 2 (by rfl) ⟨2687253, by rfl⟩ : syracuseStep 7166009 = 5374507) B5374507
theorem B4777339 : Blo 1885435 4777339 := bstep (se 1 (by rfl) ⟨3583004, by rfl⟩ : syracuseStep 4777339 = 7166009) B7166009
theorem B6369785 : Blo 1885435 6369785 := bstep (se 2 (by rfl) ⟨2388669, by rfl⟩ : syracuseStep 6369785 = 4777339) B4777339
theorem B4246523 : Blo 1885435 4246523 := bstep (se 1 (by rfl) ⟨3184892, by rfl⟩ : syracuseStep 4246523 = 6369785) B6369785
theorem B2831015 : Blo 1885435 2831015 := bstep (se 1 (by rfl) ⟨2123261, by rfl⟩ : syracuseStep 2831015 = 4246523) B4246523
theorem B1887343 : Blo 1885435 1887343 := bstep (se 1 (by rfl) ⟨1415507, by rfl⟩ : syracuseStep 1887343 = 2831015) B2831015
theorem B2831021 : Blo 1885435 2831021 := bbase (se 3 (by rfl) ⟨530816, by rfl⟩ : syracuseStep 2831021 = 1061633) (by norm_num)
theorem B1887347 : Blo 1885435 1887347 := bstep (se 1 (by rfl) ⟨1415510, by rfl⟩ : syracuseStep 1887347 = 2831021) B2831021
theorem B4246541 : Blo 1885435 4246541 := bbase (se 3 (by rfl) ⟨796226, by rfl⟩ : syracuseStep 4246541 = 1592453) (by norm_num)
theorem B2831027 : Blo 1885435 2831027 := bstep (se 1 (by rfl) ⟨2123270, by rfl⟩ : syracuseStep 2831027 = 4246541) B4246541
theorem B1887351 : Blo 1885435 1887351 := bstep (se 1 (by rfl) ⟨1415513, by rfl⟩ : syracuseStep 1887351 = 2831027) B2831027
theorem B2388685 : Blo 1885435 2388685 := bbase (se 3 (by rfl) ⟨447878, by rfl⟩ : syracuseStep 2388685 = 895757) (by norm_num)
theorem B3184913 : Blo 1885435 3184913 := bstep (se 2 (by rfl) ⟨1194342, by rfl⟩ : syracuseStep 3184913 = 2388685) B2388685
theorem B2123275 : Blo 1885435 2123275 := bstep (se 1 (by rfl) ⟨1592456, by rfl⟩ : syracuseStep 2123275 = 3184913) B3184913
theorem B2831033 : Blo 1885435 2831033 := bstep (se 2 (by rfl) ⟨1061637, by rfl⟩ : syracuseStep 2831033 = 2123275) B2123275
theorem B1887355 : Blo 1885435 1887355 := bstep (se 1 (by rfl) ⟨1415516, by rfl⟩ : syracuseStep 1887355 = 2831033) B2831033
theorem B4908629 : Blo 1885435 4908629 := bbase (se 8 (by rfl) ⟨28761, by rfl⟩ : syracuseStep 4908629 = 57523) (by norm_num)
theorem B3272419 : Blo 1885435 3272419 := bstep (se 1 (by rfl) ⟨2454314, by rfl⟩ : syracuseStep 3272419 = 4908629) B4908629
theorem B17452901 : Blo 1885435 17452901 := bstep (se 4 (by rfl) ⟨1636209, by rfl⟩ : syracuseStep 17452901 = 3272419) B3272419
theorem B46541069 : Blo 1885435 46541069 := bstep (se 3 (by rfl) ⟨8726450, by rfl⟩ : syracuseStep 46541069 = 17452901) B17452901
theorem B31027379 : Blo 1885435 31027379 := bstep (se 1 (by rfl) ⟨23270534, by rfl⟩ : syracuseStep 31027379 = 46541069) B46541069
theorem B82739677 : Blo 1885435 82739677 := bstep (se 3 (by rfl) ⟨15513689, by rfl⟩ : syracuseStep 82739677 = 31027379) B31027379
theorem B110319569 : Blo 1885435 110319569 := bstep (se 2 (by rfl) ⟨41369838, by rfl⟩ : syracuseStep 110319569 = 82739677) B82739677
theorem B73546379 : Blo 1885435 73546379 := bstep (se 1 (by rfl) ⟨55159784, by rfl⟩ : syracuseStep 73546379 = 110319569) B110319569
theorem B49030919 : Blo 1885435 49030919 := bstep (se 1 (by rfl) ⟨36773189, by rfl⟩ : syracuseStep 49030919 = 73546379) B73546379
theorem B32687279 : Blo 1885435 32687279 := bstep (se 1 (by rfl) ⟨24515459, by rfl⟩ : syracuseStep 32687279 = 49030919) B49030919
theorem B21791519 : Blo 1885435 21791519 := bstep (se 1 (by rfl) ⟨16343639, by rfl⟩ : syracuseStep 21791519 = 32687279) B32687279
theorem B14527679 : Blo 1885435 14527679 := bstep (se 1 (by rfl) ⟨10895759, by rfl⟩ : syracuseStep 14527679 = 21791519) B21791519
theorem B38740477 : Blo 1885435 38740477 := bstep (se 3 (by rfl) ⟨7263839, by rfl⟩ : syracuseStep 38740477 = 14527679) B14527679
theorem B51653969 : Blo 1885435 51653969 := bstep (se 2 (by rfl) ⟨19370238, by rfl⟩ : syracuseStep 51653969 = 38740477) B38740477
theorem B34435979 : Blo 1885435 34435979 := bstep (se 1 (by rfl) ⟨25826984, by rfl⟩ : syracuseStep 34435979 = 51653969) B51653969
theorem B22957319 : Blo 1885435 22957319 := bstep (se 1 (by rfl) ⟨17217989, by rfl⟩ : syracuseStep 22957319 = 34435979) B34435979
theorem B15304879 : Blo 1885435 15304879 := bstep (se 1 (by rfl) ⟨11478659, by rfl⟩ : syracuseStep 15304879 = 22957319) B22957319
theorem B20406505 : Blo 1885435 20406505 := bstep (se 2 (by rfl) ⟨7652439, by rfl⟩ : syracuseStep 20406505 = 15304879) B15304879
theorem B27208673 : Blo 1885435 27208673 := bstep (se 2 (by rfl) ⟨10203252, by rfl⟩ : syracuseStep 27208673 = 20406505) B20406505
theorem B18139115 : Blo 1885435 18139115 := bstep (se 1 (by rfl) ⟨13604336, by rfl⟩ : syracuseStep 18139115 = 27208673) B27208673
theorem B12092743 : Blo 1885435 12092743 := bstep (se 1 (by rfl) ⟨9069557, by rfl⟩ : syracuseStep 12092743 = 18139115) B18139115
theorem B16123657 : Blo 1885435 16123657 := bstep (se 2 (by rfl) ⟨6046371, by rfl⟩ : syracuseStep 16123657 = 12092743) B12092743
theorem B21498209 : Blo 1885435 21498209 := bstep (se 2 (by rfl) ⟨8061828, by rfl⟩ : syracuseStep 21498209 = 16123657) B16123657
theorem B14332139 : Blo 1885435 14332139 := bstep (se 1 (by rfl) ⟨10749104, by rfl⟩ : syracuseStep 14332139 = 21498209) B21498209
theorem B9554759 : Blo 1885435 9554759 := bstep (se 1 (by rfl) ⟨7166069, by rfl⟩ : syracuseStep 9554759 = 14332139) B14332139
theorem B6369839 : Blo 1885435 6369839 := bstep (se 1 (by rfl) ⟨4777379, by rfl⟩ : syracuseStep 6369839 = 9554759) B9554759
theorem B4246559 : Blo 1885435 4246559 := bstep (se 1 (by rfl) ⟨3184919, by rfl⟩ : syracuseStep 4246559 = 6369839) B6369839
theorem B2831039 : Blo 1885435 2831039 := bstep (se 1 (by rfl) ⟨2123279, by rfl⟩ : syracuseStep 2831039 = 4246559) B4246559
theorem B1887359 : Blo 1885435 1887359 := bstep (se 1 (by rfl) ⟨1415519, by rfl⟩ : syracuseStep 1887359 = 2831039) B2831039
theorem B2831045 : Blo 1885435 2831045 := bbase (se 4 (by rfl) ⟨265410, by rfl⟩ : syracuseStep 2831045 = 530821) (by norm_num)
theorem B1887363 : Blo 1885435 1887363 := bstep (se 1 (by rfl) ⟨1415522, by rfl⟩ : syracuseStep 1887363 = 2831045) B2831045
theorem B3184933 : Blo 1885435 3184933 := bbase (se 4 (by rfl) ⟨298587, by rfl⟩ : syracuseStep 3184933 = 597175) (by norm_num)
theorem B4246577 : Blo 1885435 4246577 := bstep (se 2 (by rfl) ⟨1592466, by rfl⟩ : syracuseStep 4246577 = 3184933) B3184933
theorem B2831051 : Blo 1885435 2831051 := bstep (se 1 (by rfl) ⟨2123288, by rfl⟩ : syracuseStep 2831051 = 4246577) B4246577
theorem B1887367 : Blo 1885435 1887367 := bstep (se 1 (by rfl) ⟨1415525, by rfl⟩ : syracuseStep 1887367 = 2831051) B2831051
theorem B2123293 : Blo 1885435 2123293 := bbase (se 3 (by rfl) ⟨398117, by rfl⟩ : syracuseStep 2123293 = 796235) (by norm_num)
theorem B2831057 : Blo 1885435 2831057 := bstep (se 2 (by rfl) ⟨1061646, by rfl⟩ : syracuseStep 2831057 = 2123293) B2123293
theorem B1887371 : Blo 1885435 1887371 := bstep (se 1 (by rfl) ⟨1415528, by rfl⟩ : syracuseStep 1887371 = 2831057) B2831057
theorem B6369893 : Blo 1885435 6369893 := bbase (se 4 (by rfl) ⟨597177, by rfl⟩ : syracuseStep 6369893 = 1194355) (by norm_num)
theorem B4246595 : Blo 1885435 4246595 := bstep (se 1 (by rfl) ⟨3184946, by rfl⟩ : syracuseStep 4246595 = 6369893) B6369893
theorem B2831063 : Blo 1885435 2831063 := bstep (se 1 (by rfl) ⟨2123297, by rfl⟩ : syracuseStep 2831063 = 4246595) B4246595
theorem B1887375 : Blo 1885435 1887375 := bstep (se 1 (by rfl) ⟨1415531, by rfl⟩ : syracuseStep 1887375 = 2831063) B2831063
theorem B2831069 : Blo 1885435 2831069 := bbase (se 3 (by rfl) ⟨530825, by rfl⟩ : syracuseStep 2831069 = 1061651) (by norm_num)
theorem B1887379 : Blo 1885435 1887379 := bstep (se 1 (by rfl) ⟨1415534, by rfl⟩ : syracuseStep 1887379 = 2831069) B2831069
theorem B4246613 : Blo 1885435 4246613 := bbase (se 8 (by rfl) ⟨24882, by rfl⟩ : syracuseStep 4246613 = 49765) (by norm_num)
theorem B2831075 : Blo 1885435 2831075 := bstep (se 1 (by rfl) ⟨2123306, by rfl⟩ : syracuseStep 2831075 = 4246613) B4246613
theorem B1887383 : Blo 1885435 1887383 := bstep (se 1 (by rfl) ⟨1415537, by rfl⟩ : syracuseStep 1887383 = 2831075) B2831075
theorem B2908861 : Blo 1885435 2908861 := bbase (se 3 (by rfl) ⟨545411, by rfl⟩ : syracuseStep 2908861 = 1090823) (by norm_num)
theorem B15513925 : Blo 1885435 15513925 := bstep (se 4 (by rfl) ⟨1454430, by rfl⟩ : syracuseStep 15513925 = 2908861) B2908861
theorem B20685233 : Blo 1885435 20685233 := bstep (se 2 (by rfl) ⟨7756962, by rfl⟩ : syracuseStep 20685233 = 15513925) B15513925
theorem B55160621 : Blo 1885435 55160621 := bstep (se 3 (by rfl) ⟨10342616, by rfl⟩ : syracuseStep 55160621 = 20685233) B20685233
theorem B36773747 : Blo 1885435 36773747 := bstep (se 1 (by rfl) ⟨27580310, by rfl⟩ : syracuseStep 36773747 = 55160621) B55160621
theorem B24515831 : Blo 1885435 24515831 := bstep (se 1 (by rfl) ⟨18386873, by rfl⟩ : syracuseStep 24515831 = 36773747) B36773747
theorem B16343887 : Blo 1885435 16343887 := bstep (se 1 (by rfl) ⟨12257915, by rfl⟩ : syracuseStep 16343887 = 24515831) B24515831
theorem B21791849 : Blo 1885435 21791849 := bstep (se 2 (by rfl) ⟨8171943, by rfl⟩ : syracuseStep 21791849 = 16343887) B16343887
theorem B58111597 : Blo 1885435 58111597 := bstep (se 3 (by rfl) ⟨10895924, by rfl⟩ : syracuseStep 58111597 = 21791849) B21791849
theorem B77482129 : Blo 1885435 77482129 := bstep (se 2 (by rfl) ⟨29055798, by rfl⟩ : syracuseStep 77482129 = 58111597) B58111597
theorem B103309505 : Blo 1885435 103309505 := bstep (se 2 (by rfl) ⟨38741064, by rfl⟩ : syracuseStep 103309505 = 77482129) B77482129
theorem B68873003 : Blo 1885435 68873003 := bstep (se 1 (by rfl) ⟨51654752, by rfl⟩ : syracuseStep 68873003 = 103309505) B103309505
theorem B45915335 : Blo 1885435 45915335 := bstep (se 1 (by rfl) ⟨34436501, by rfl⟩ : syracuseStep 45915335 = 68873003) B68873003
theorem B30610223 : Blo 1885435 30610223 := bstep (se 1 (by rfl) ⟨22957667, by rfl⟩ : syracuseStep 30610223 = 45915335) B45915335
theorem B20406815 : Blo 1885435 20406815 := bstep (se 1 (by rfl) ⟨15305111, by rfl⟩ : syracuseStep 20406815 = 30610223) B30610223
theorem B13604543 : Blo 1885435 13604543 := bstep (se 1 (by rfl) ⟨10203407, by rfl⟩ : syracuseStep 13604543 = 20406815) B20406815
theorem B9069695 : Blo 1885435 9069695 := bstep (se 1 (by rfl) ⟨6802271, by rfl⟩ : syracuseStep 9069695 = 13604543) B13604543
theorem B6046463 : Blo 1885435 6046463 := bstep (se 1 (by rfl) ⟨4534847, by rfl⟩ : syracuseStep 6046463 = 9069695) B9069695
theorem B4030975 : Blo 1885435 4030975 := bstep (se 1 (by rfl) ⟨3023231, by rfl⟩ : syracuseStep 4030975 = 6046463) B6046463
theorem B5374633 : Blo 1885435 5374633 := bstep (se 2 (by rfl) ⟨2015487, by rfl⟩ : syracuseStep 5374633 = 4030975) B4030975
theorem B7166177 : Blo 1885435 7166177 := bstep (se 2 (by rfl) ⟨2687316, by rfl⟩ : syracuseStep 7166177 = 5374633) B5374633
theorem B4777451 : Blo 1885435 4777451 := bstep (se 1 (by rfl) ⟨3583088, by rfl⟩ : syracuseStep 4777451 = 7166177) B7166177
theorem B3184967 : Blo 1885435 3184967 := bstep (se 1 (by rfl) ⟨2388725, by rfl⟩ : syracuseStep 3184967 = 4777451) B4777451
theorem B2123311 : Blo 1885435 2123311 := bstep (se 1 (by rfl) ⟨1592483, by rfl⟩ : syracuseStep 2123311 = 3184967) B3184967
theorem B2831081 : Blo 1885435 2831081 := bstep (se 2 (by rfl) ⟨1061655, by rfl⟩ : syracuseStep 2831081 = 2123311) B2123311
theorem B1887387 : Blo 1885435 1887387 := bstep (se 1 (by rfl) ⟨1415540, by rfl⟩ : syracuseStep 1887387 = 2831081) B2831081
theorem B4363301 : Blo 1885435 4363301 := bbase (se 4 (by rfl) ⟨409059, by rfl⟩ : syracuseStep 4363301 = 818119) (by norm_num)
theorem B2908867 : Blo 1885435 2908867 := bstep (se 1 (by rfl) ⟨2181650, by rfl⟩ : syracuseStep 2908867 = 4363301) B4363301
theorem B3878489 : Blo 1885435 3878489 := bstep (se 2 (by rfl) ⟨1454433, by rfl⟩ : syracuseStep 3878489 = 2908867) B2908867
theorem B2585659 : Blo 1885435 2585659 := bstep (se 1 (by rfl) ⟨1939244, by rfl⟩ : syracuseStep 2585659 = 3878489) B3878489
theorem B3447545 : Blo 1885435 3447545 := bstep (se 2 (by rfl) ⟨1292829, by rfl⟩ : syracuseStep 3447545 = 2585659) B2585659
theorem B36773813 : Blo 1885435 36773813 := bstep (se 5 (by rfl) ⟨1723772, by rfl⟩ : syracuseStep 36773813 = 3447545) B3447545
theorem B24515875 : Blo 1885435 24515875 := bstep (se 1 (by rfl) ⟨18386906, by rfl⟩ : syracuseStep 24515875 = 36773813) B36773813
theorem B32687833 : Blo 1885435 32687833 := bstep (se 2 (by rfl) ⟨12257937, by rfl⟩ : syracuseStep 32687833 = 24515875) B24515875
theorem B43583777 : Blo 1885435 43583777 := bstep (se 2 (by rfl) ⟨16343916, by rfl⟩ : syracuseStep 43583777 = 32687833) B32687833
theorem B29055851 : Blo 1885435 29055851 := bstep (se 1 (by rfl) ⟨21791888, by rfl⟩ : syracuseStep 29055851 = 43583777) B43583777
theorem B19370567 : Blo 1885435 19370567 := bstep (se 1 (by rfl) ⟨14527925, by rfl⟩ : syracuseStep 19370567 = 29055851) B29055851
theorem B12913711 : Blo 1885435 12913711 := bstep (se 1 (by rfl) ⟨9685283, by rfl⟩ : syracuseStep 12913711 = 19370567) B19370567
theorem B68873125 : Blo 1885435 68873125 := bstep (se 4 (by rfl) ⟨6456855, by rfl⟩ : syracuseStep 68873125 = 12913711) B12913711
theorem B91830833 : Blo 1885435 91830833 := bstep (se 2 (by rfl) ⟨34436562, by rfl⟩ : syracuseStep 91830833 = 68873125) B68873125
theorem B61220555 : Blo 1885435 61220555 := bstep (se 1 (by rfl) ⟨45915416, by rfl⟩ : syracuseStep 61220555 = 91830833) B91830833
theorem B40813703 : Blo 1885435 40813703 := bstep (se 1 (by rfl) ⟨30610277, by rfl⟩ : syracuseStep 40813703 = 61220555) B61220555
theorem B27209135 : Blo 1885435 27209135 := bstep (se 1 (by rfl) ⟨20406851, by rfl⟩ : syracuseStep 27209135 = 40813703) B40813703
theorem B18139423 : Blo 1885435 18139423 := bstep (se 1 (by rfl) ⟨13604567, by rfl⟩ : syracuseStep 18139423 = 27209135) B27209135
theorem B24185897 : Blo 1885435 24185897 := bstep (se 2 (by rfl) ⟨9069711, by rfl⟩ : syracuseStep 24185897 = 18139423) B18139423
theorem B16123931 : Blo 1885435 16123931 := bstep (se 1 (by rfl) ⟨12092948, by rfl⟩ : syracuseStep 16123931 = 24185897) B24185897
theorem B10749287 : Blo 1885435 10749287 := bstep (se 1 (by rfl) ⟨8061965, by rfl⟩ : syracuseStep 10749287 = 16123931) B16123931
theorem B7166191 : Blo 1885435 7166191 := bstep (se 1 (by rfl) ⟨5374643, by rfl⟩ : syracuseStep 7166191 = 10749287) B10749287
theorem B9554921 : Blo 1885435 9554921 := bstep (se 2 (by rfl) ⟨3583095, by rfl⟩ : syracuseStep 9554921 = 7166191) B7166191
theorem B6369947 : Blo 1885435 6369947 := bstep (se 1 (by rfl) ⟨4777460, by rfl⟩ : syracuseStep 6369947 = 9554921) B9554921
theorem B4246631 : Blo 1885435 4246631 := bstep (se 1 (by rfl) ⟨3184973, by rfl⟩ : syracuseStep 4246631 = 6369947) B6369947
theorem B2831087 : Blo 1885435 2831087 := bstep (se 1 (by rfl) ⟨2123315, by rfl⟩ : syracuseStep 2831087 = 4246631) B4246631
theorem B1887391 : Blo 1885435 1887391 := bstep (se 1 (by rfl) ⟨1415543, by rfl⟩ : syracuseStep 1887391 = 2831087) B2831087
theorem B2831093 : Blo 1885435 2831093 := bbase (se 5 (by rfl) ⟨132707, by rfl⟩ : syracuseStep 2831093 = 265415) (by norm_num)
theorem B1887395 : Blo 1885435 1887395 := bstep (se 1 (by rfl) ⟨1415546, by rfl⟩ : syracuseStep 1887395 = 2831093) B2831093
theorem B6046501 : Blo 1885435 6046501 := bbase (se 4 (by rfl) ⟨566859, by rfl⟩ : syracuseStep 6046501 = 1133719) (by norm_num)
theorem B8062001 : Blo 1885435 8062001 := bstep (se 2 (by rfl) ⟨3023250, by rfl⟩ : syracuseStep 8062001 = 6046501) B6046501
theorem B5374667 : Blo 1885435 5374667 := bstep (se 1 (by rfl) ⟨4031000, by rfl⟩ : syracuseStep 5374667 = 8062001) B8062001
theorem B3583111 : Blo 1885435 3583111 := bstep (se 1 (by rfl) ⟨2687333, by rfl⟩ : syracuseStep 3583111 = 5374667) B5374667
theorem B4777481 : Blo 1885435 4777481 := bstep (se 2 (by rfl) ⟨1791555, by rfl⟩ : syracuseStep 4777481 = 3583111) B3583111
theorem B3184987 : Blo 1885435 3184987 := bstep (se 1 (by rfl) ⟨2388740, by rfl⟩ : syracuseStep 3184987 = 4777481) B4777481
theorem B4246649 : Blo 1885435 4246649 := bstep (se 2 (by rfl) ⟨1592493, by rfl⟩ : syracuseStep 4246649 = 3184987) B3184987
theorem B2831099 : Blo 1885435 2831099 := bstep (se 1 (by rfl) ⟨2123324, by rfl⟩ : syracuseStep 2831099 = 4246649) B4246649
theorem B1887399 : Blo 1885435 1887399 := bstep (se 1 (by rfl) ⟨1415549, by rfl⟩ : syracuseStep 1887399 = 2831099) B2831099
theorem B2123329 : Blo 1885435 2123329 := bbase (se 2 (by rfl) ⟨796248, by rfl⟩ : syracuseStep 2123329 = 1592497) (by norm_num)
theorem B2831105 : Blo 1885435 2831105 := bstep (se 2 (by rfl) ⟨1061664, by rfl⟩ : syracuseStep 2831105 = 2123329) B2123329
theorem B1887403 : Blo 1885435 1887403 := bstep (se 1 (by rfl) ⟨1415552, by rfl⟩ : syracuseStep 1887403 = 2831105) B2831105
theorem B4777501 : Blo 1885435 4777501 := bbase (se 3 (by rfl) ⟨895781, by rfl⟩ : syracuseStep 4777501 = 1791563) (by norm_num)
theorem B6370001 : Blo 1885435 6370001 := bstep (se 2 (by rfl) ⟨2388750, by rfl⟩ : syracuseStep 6370001 = 4777501) B4777501
theorem B4246667 : Blo 1885435 4246667 := bstep (se 1 (by rfl) ⟨3185000, by rfl⟩ : syracuseStep 4246667 = 6370001) B6370001
theorem B2831111 : Blo 1885435 2831111 := bstep (se 1 (by rfl) ⟨2123333, by rfl⟩ : syracuseStep 2831111 = 4246667) B4246667
theorem B1887407 : Blo 1885435 1887407 := bstep (se 1 (by rfl) ⟨1415555, by rfl⟩ : syracuseStep 1887407 = 2831111) B2831111
theorem B2831117 : Blo 1885435 2831117 := bbase (se 3 (by rfl) ⟨530834, by rfl⟩ : syracuseStep 2831117 = 1061669) (by norm_num)
theorem B1887411 : Blo 1885435 1887411 := bstep (se 1 (by rfl) ⟨1415558, by rfl⟩ : syracuseStep 1887411 = 2831117) B2831117
theorem B4246685 : Blo 1885435 4246685 := bbase (se 3 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 4246685 = 1592507) (by norm_num)
theorem B2831123 : Blo 1885435 2831123 := bstep (se 1 (by rfl) ⟨2123342, by rfl⟩ : syracuseStep 2831123 = 4246685) B4246685
theorem B1887415 : Blo 1885435 1887415 := bstep (se 1 (by rfl) ⟨1415561, by rfl⟩ : syracuseStep 1887415 = 2831123) B2831123
theorem B3185021 : Blo 1885435 3185021 := bbase (se 3 (by rfl) ⟨597191, by rfl⟩ : syracuseStep 3185021 = 1194383) (by norm_num)
theorem B2123347 : Blo 1885435 2123347 := bstep (se 1 (by rfl) ⟨1592510, by rfl⟩ : syracuseStep 2123347 = 3185021) B3185021
theorem B2831129 : Blo 1885435 2831129 := bstep (se 2 (by rfl) ⟨1061673, by rfl⟩ : syracuseStep 2831129 = 2123347) B2123347
theorem B1887419 : Blo 1885435 1887419 := bstep (se 1 (by rfl) ⟨1415564, by rfl⟩ : syracuseStep 1887419 = 2831129) B2831129
theorem B4534933 : Blo 1885435 4534933 := bbase (se 6 (by rfl) ⟨106287, by rfl⟩ : syracuseStep 4534933 = 212575) (by norm_num)
theorem B6046577 : Blo 1885435 6046577 := bstep (se 2 (by rfl) ⟨2267466, by rfl⟩ : syracuseStep 6046577 = 4534933) B4534933
theorem B4031051 : Blo 1885435 4031051 := bstep (se 1 (by rfl) ⟨3023288, by rfl⟩ : syracuseStep 4031051 = 6046577) B6046577
theorem B10749469 : Blo 1885435 10749469 := bstep (se 3 (by rfl) ⟨2015525, by rfl⟩ : syracuseStep 10749469 = 4031051) B4031051
theorem B14332625 : Blo 1885435 14332625 := bstep (se 2 (by rfl) ⟨5374734, by rfl⟩ : syracuseStep 14332625 = 10749469) B10749469
theorem B9555083 : Blo 1885435 9555083 := bstep (se 1 (by rfl) ⟨7166312, by rfl⟩ : syracuseStep 9555083 = 14332625) B14332625
theorem B6370055 : Blo 1885435 6370055 := bstep (se 1 (by rfl) ⟨4777541, by rfl⟩ : syracuseStep 6370055 = 9555083) B9555083
theorem B4246703 : Blo 1885435 4246703 := bstep (se 1 (by rfl) ⟨3185027, by rfl⟩ : syracuseStep 4246703 = 6370055) B6370055
theorem B2831135 : Blo 1885435 2831135 := bstep (se 1 (by rfl) ⟨2123351, by rfl⟩ : syracuseStep 2831135 = 4246703) B4246703
theorem B1887423 : Blo 1885435 1887423 := bstep (se 1 (by rfl) ⟨1415567, by rfl⟩ : syracuseStep 1887423 = 2831135) B2831135
theorem B2831141 : Blo 1885435 2831141 := bbase (se 4 (by rfl) ⟨265419, by rfl⟩ : syracuseStep 2831141 = 530839) (by norm_num)
theorem B1887427 : Blo 1885435 1887427 := bstep (se 1 (by rfl) ⟨1415570, by rfl⟩ : syracuseStep 1887427 = 2831141) B2831141
theorem B2388781 : Blo 1885435 2388781 := bbase (se 3 (by rfl) ⟨447896, by rfl⟩ : syracuseStep 2388781 = 895793) (by norm_num)
theorem B3185041 : Blo 1885435 3185041 := bstep (se 2 (by rfl) ⟨1194390, by rfl⟩ : syracuseStep 3185041 = 2388781) B2388781
theorem B4246721 : Blo 1885435 4246721 := bstep (se 2 (by rfl) ⟨1592520, by rfl⟩ : syracuseStep 4246721 = 3185041) B3185041
theorem B2831147 : Blo 1885435 2831147 := bstep (se 1 (by rfl) ⟨2123360, by rfl⟩ : syracuseStep 2831147 = 4246721) B4246721
theorem B1887431 : Blo 1885435 1887431 := bstep (se 1 (by rfl) ⟨1415573, by rfl⟩ : syracuseStep 1887431 = 2831147) B2831147
theorem B2123365 : Blo 1885435 2123365 := bbase (se 4 (by rfl) ⟨199065, by rfl⟩ : syracuseStep 2123365 = 398131) (by norm_num)
theorem B2831153 : Blo 1885435 2831153 := bstep (se 2 (by rfl) ⟨1061682, by rfl⟩ : syracuseStep 2831153 = 2123365) B2123365
theorem B1887435 : Blo 1885435 1887435 := bstep (se 1 (by rfl) ⟨1415576, by rfl⟩ : syracuseStep 1887435 = 2831153) B2831153
theorem C0 (j : ℕ) (h1 : 471358 ≤ j) (h2 : j ≤ 471858) : Blo 1885435 (4 * j + 3) := by
  interval_cases j
  · exact B1885435
  · exact B1885439
  · exact B1885443
  · exact B1885447
  · exact B1885451
  · exact B1885455
  · exact B1885459
  · exact B1885463
  · exact B1885467
  · exact B1885471
  · exact B1885475
  · exact B1885479
  · exact B1885483
  · exact B1885487
  · exact B1885491
  · exact B1885495
  · exact B1885499
  · exact B1885503
  · exact B1885507
  · exact B1885511
  · exact B1885515
  · exact B1885519
  · exact B1885523
  · exact B1885527
  · exact B1885531
  · exact B1885535
  · exact B1885539
  · exact B1885543
  · exact B1885547
  · exact B1885551
  · exact B1885555
  · exact B1885559
  · exact B1885563
  · exact B1885567
  · exact B1885571
  · exact B1885575
  · exact B1885579
  · exact B1885583
  · exact B1885587
  · exact B1885591
  · exact B1885595
  · exact B1885599
  · exact B1885603
  · exact B1885607
  · exact B1885611
  · exact B1885615
  · exact B1885619
  · exact B1885623
  · exact B1885627
  · exact B1885631
  · exact B1885635
  · exact B1885639
  · exact B1885643
  · exact B1885647
  · exact B1885651
  · exact B1885655
  · exact B1885659
  · exact B1885663
  · exact B1885667
  · exact B1885671
  · exact B1885675
  · exact B1885679
  · exact B1885683
  · exact B1885687
  · exact B1885691
  · exact B1885695
  · exact B1885699
  · exact B1885703
  · exact B1885707
  · exact B1885711
  · exact B1885715
  · exact B1885719
  · exact B1885723
  · exact B1885727
  · exact B1885731
  · exact B1885735
  · exact B1885739
  · exact B1885743
  · exact B1885747
  · exact B1885751
  · exact B1885755
  · exact B1885759
  · exact B1885763
  · exact B1885767
  · exact B1885771
  · exact B1885775
  · exact B1885779
  · exact B1885783
  · exact B1885787
  · exact B1885791
  · exact B1885795
  · exact B1885799
  · exact B1885803
  · exact B1885807
  · exact B1885811
  · exact B1885815
  · exact B1885819
  · exact B1885823
  · exact B1885827
  · exact B1885831
  · exact B1885835
  · exact B1885839
  · exact B1885843
  · exact B1885847
  · exact B1885851
  · exact B1885855
  · exact B1885859
  · exact B1885863
  · exact B1885867
  · exact B1885871
  · exact B1885875
  · exact B1885879
  · exact B1885883
  · exact B1885887
  · exact B1885891
  · exact B1885895
  · exact B1885899
  · exact B1885903
  · exact B1885907
  · exact B1885911
  · exact B1885915
  · exact B1885919
  · exact B1885923
  · exact B1885927
  · exact B1885931
  · exact B1885935
  · exact B1885939
  · exact B1885943
  · exact B1885947
  · exact B1885951
  · exact B1885955
  · exact B1885959
  · exact B1885963
  · exact B1885967
  · exact B1885971
  · exact B1885975
  · exact B1885979
  · exact B1885983
  · exact B1885987
  · exact B1885991
  · exact B1885995
  · exact B1885999
  · exact B1886003
  · exact B1886007
  · exact B1886011
  · exact B1886015
  · exact B1886019
  · exact B1886023
  · exact B1886027
  · exact B1886031
  · exact B1886035
  · exact B1886039
  · exact B1886043
  · exact B1886047
  · exact B1886051
  · exact B1886055
  · exact B1886059
  · exact B1886063
  · exact B1886067
  · exact B1886071
  · exact B1886075
  · exact B1886079
  · exact B1886083
  · exact B1886087
  · exact B1886091
  · exact B1886095
  · exact B1886099
  · exact B1886103
  · exact B1886107
  · exact B1886111
  · exact B1886115
  · exact B1886119
  · exact B1886123
  · exact B1886127
  · exact B1886131
  · exact B1886135
  · exact B1886139
  · exact B1886143
  · exact B1886147
  · exact B1886151
  · exact B1886155
  · exact B1886159
  · exact B1886163
  · exact B1886167
  · exact B1886171
  · exact B1886175
  · exact B1886179
  · exact B1886183
  · exact B1886187
  · exact B1886191
  · exact B1886195
  · exact B1886199
  · exact B1886203
  · exact B1886207
  · exact B1886211
  · exact B1886215
  · exact B1886219
  · exact B1886223
  · exact B1886227
  · exact B1886231
  · exact B1886235
  · exact B1886239
  · exact B1886243
  · exact B1886247
  · exact B1886251
  · exact B1886255
  · exact B1886259
  · exact B1886263
  · exact B1886267
  · exact B1886271
  · exact B1886275
  · exact B1886279
  · exact B1886283
  · exact B1886287
  · exact B1886291
  · exact B1886295
  · exact B1886299
  · exact B1886303
  · exact B1886307
  · exact B1886311
  · exact B1886315
  · exact B1886319
  · exact B1886323
  · exact B1886327
  · exact B1886331
  · exact B1886335
  · exact B1886339
  · exact B1886343
  · exact B1886347
  · exact B1886351
  · exact B1886355
  · exact B1886359
  · exact B1886363
  · exact B1886367
  · exact B1886371
  · exact B1886375
  · exact B1886379
  · exact B1886383
  · exact B1886387
  · exact B1886391
  · exact B1886395
  · exact B1886399
  · exact B1886403
  · exact B1886407
  · exact B1886411
  · exact B1886415
  · exact B1886419
  · exact B1886423
  · exact B1886427
  · exact B1886431
  · exact B1886435
  · exact B1886439
  · exact B1886443
  · exact B1886447
  · exact B1886451
  · exact B1886455
  · exact B1886459
  · exact B1886463
  · exact B1886467
  · exact B1886471
  · exact B1886475
  · exact B1886479
  · exact B1886483
  · exact B1886487
  · exact B1886491
  · exact B1886495
  · exact B1886499
  · exact B1886503
  · exact B1886507
  · exact B1886511
  · exact B1886515
  · exact B1886519
  · exact B1886523
  · exact B1886527
  · exact B1886531
  · exact B1886535
  · exact B1886539
  · exact B1886543
  · exact B1886547
  · exact B1886551
  · exact B1886555
  · exact B1886559
  · exact B1886563
  · exact B1886567
  · exact B1886571
  · exact B1886575
  · exact B1886579
  · exact B1886583
  · exact B1886587
  · exact B1886591
  · exact B1886595
  · exact B1886599
  · exact B1886603
  · exact B1886607
  · exact B1886611
  · exact B1886615
  · exact B1886619
  · exact B1886623
  · exact B1886627
  · exact B1886631
  · exact B1886635
  · exact B1886639
  · exact B1886643
  · exact B1886647
  · exact B1886651
  · exact B1886655
  · exact B1886659
  · exact B1886663
  · exact B1886667
  · exact B1886671
  · exact B1886675
  · exact B1886679
  · exact B1886683
  · exact B1886687
  · exact B1886691
  · exact B1886695
  · exact B1886699
  · exact B1886703
  · exact B1886707
  · exact B1886711
  · exact B1886715
  · exact B1886719
  · exact B1886723
  · exact B1886727
  · exact B1886731
  · exact B1886735
  · exact B1886739
  · exact B1886743
  · exact B1886747
  · exact B1886751
  · exact B1886755
  · exact B1886759
  · exact B1886763
  · exact B1886767
  · exact B1886771
  · exact B1886775
  · exact B1886779
  · exact B1886783
  · exact B1886787
  · exact B1886791
  · exact B1886795
  · exact B1886799
  · exact B1886803
  · exact B1886807
  · exact B1886811
  · exact B1886815
  · exact B1886819
  · exact B1886823
  · exact B1886827
  · exact B1886831
  · exact B1886835
  · exact B1886839
  · exact B1886843
  · exact B1886847
  · exact B1886851
  · exact B1886855
  · exact B1886859
  · exact B1886863
  · exact B1886867
  · exact B1886871
  · exact B1886875
  · exact B1886879
  · exact B1886883
  · exact B1886887
  · exact B1886891
  · exact B1886895
  · exact B1886899
  · exact B1886903
  · exact B1886907
  · exact B1886911
  · exact B1886915
  · exact B1886919
  · exact B1886923
  · exact B1886927
  · exact B1886931
  · exact B1886935
  · exact B1886939
  · exact B1886943
  · exact B1886947
  · exact B1886951
  · exact B1886955
  · exact B1886959
  · exact B1886963
  · exact B1886967
  · exact B1886971
  · exact B1886975
  · exact B1886979
  · exact B1886983
  · exact B1886987
  · exact B1886991
  · exact B1886995
  · exact B1886999
  · exact B1887003
  · exact B1887007
  · exact B1887011
  · exact B1887015
  · exact B1887019
  · exact B1887023
  · exact B1887027
  · exact B1887031
  · exact B1887035
  · exact B1887039
  · exact B1887043
  · exact B1887047
  · exact B1887051
  · exact B1887055
  · exact B1887059
  · exact B1887063
  · exact B1887067
  · exact B1887071
  · exact B1887075
  · exact B1887079
  · exact B1887083
  · exact B1887087
  · exact B1887091
  · exact B1887095
  · exact B1887099
  · exact B1887103
  · exact B1887107
  · exact B1887111
  · exact B1887115
  · exact B1887119
  · exact B1887123
  · exact B1887127
  · exact B1887131
  · exact B1887135
  · exact B1887139
  · exact B1887143
  · exact B1887147
  · exact B1887151
  · exact B1887155
  · exact B1887159
  · exact B1887163
  · exact B1887167
  · exact B1887171
  · exact B1887175
  · exact B1887179
  · exact B1887183
  · exact B1887187
  · exact B1887191
  · exact B1887195
  · exact B1887199
  · exact B1887203
  · exact B1887207
  · exact B1887211
  · exact B1887215
  · exact B1887219
  · exact B1887223
  · exact B1887227
  · exact B1887231
  · exact B1887235
  · exact B1887239
  · exact B1887243
  · exact B1887247
  · exact B1887251
  · exact B1887255
  · exact B1887259
  · exact B1887263
  · exact B1887267
  · exact B1887271
  · exact B1887275
  · exact B1887279
  · exact B1887283
  · exact B1887287
  · exact B1887291
  · exact B1887295
  · exact B1887299
  · exact B1887303
  · exact B1887307
  · exact B1887311
  · exact B1887315
  · exact B1887319
  · exact B1887323
  · exact B1887327
  · exact B1887331
  · exact B1887335
  · exact B1887339
  · exact B1887343
  · exact B1887347
  · exact B1887351
  · exact B1887355
  · exact B1887359
  · exact B1887363
  · exact B1887367
  · exact B1887371
  · exact B1887375
  · exact B1887379
  · exact B1887383
  · exact B1887387
  · exact B1887391
  · exact B1887395
  · exact B1887399
  · exact B1887403
  · exact B1887407
  · exact B1887411
  · exact B1887415
  · exact B1887419
  · exact B1887423
  · exact B1887427
  · exact B1887431
  · exact B1887435
theorem solution (m : ℕ) (hlo : 1885435 ≤ m) (hhi : m ≤ 1887435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 471358 ≤ j := by omega
    have hj2 : j ≤ 471858 := by omega
    have hb : Blo 1885435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
