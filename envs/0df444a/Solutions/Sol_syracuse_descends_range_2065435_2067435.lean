-- Prove2me | solution 1 for syracuse_descends_range_2065435_2067435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:15:58.168535+00:00
-- url     : https://prove2.me/submissions/8b72287d-f2b9-482d-8f91-589e98929dbb

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

theorem B190780757 : Blo 2065435 190780757 := bbase (se 14 (by rfl) ⟨17466, by rfl⟩ : syracuseStep 190780757 = 34933) (by norm_num)
theorem B127187171 : Blo 2065435 127187171 := bstep (se 1 (by rfl) ⟨95390378, by rfl⟩ : syracuseStep 127187171 = 190780757) B190780757
theorem B84791447 : Blo 2065435 84791447 := bstep (se 1 (by rfl) ⟨63593585, by rfl⟩ : syracuseStep 84791447 = 127187171) B127187171
theorem B56527631 : Blo 2065435 56527631 := bstep (se 1 (by rfl) ⟨42395723, by rfl⟩ : syracuseStep 56527631 = 84791447) B84791447
theorem B37685087 : Blo 2065435 37685087 := bstep (se 1 (by rfl) ⟨28263815, by rfl⟩ : syracuseStep 37685087 = 56527631) B56527631
theorem B25123391 : Blo 2065435 25123391 := bstep (se 1 (by rfl) ⟨18842543, by rfl⟩ : syracuseStep 25123391 = 37685087) B37685087
theorem B16748927 : Blo 2065435 16748927 := bstep (se 1 (by rfl) ⟨12561695, by rfl⟩ : syracuseStep 16748927 = 25123391) B25123391
theorem B11165951 : Blo 2065435 11165951 := bstep (se 1 (by rfl) ⟨8374463, by rfl⟩ : syracuseStep 11165951 = 16748927) B16748927
theorem B29775869 : Blo 2065435 29775869 := bstep (se 3 (by rfl) ⟨5582975, by rfl⟩ : syracuseStep 29775869 = 11165951) B11165951
theorem B19850579 : Blo 2065435 19850579 := bstep (se 1 (by rfl) ⟨14887934, by rfl⟩ : syracuseStep 19850579 = 29775869) B29775869
theorem B13233719 : Blo 2065435 13233719 := bstep (se 1 (by rfl) ⟨9925289, by rfl⟩ : syracuseStep 13233719 = 19850579) B19850579
theorem B8822479 : Blo 2065435 8822479 := bstep (se 1 (by rfl) ⟨6616859, by rfl⟩ : syracuseStep 8822479 = 13233719) B13233719
theorem B11763305 : Blo 2065435 11763305 := bstep (se 2 (by rfl) ⟨4411239, by rfl⟩ : syracuseStep 11763305 = 8822479) B8822479
theorem B7842203 : Blo 2065435 7842203 := bstep (se 1 (by rfl) ⟨5881652, by rfl⟩ : syracuseStep 7842203 = 11763305) B11763305
theorem B5228135 : Blo 2065435 5228135 := bstep (se 1 (by rfl) ⟨3921101, by rfl⟩ : syracuseStep 5228135 = 7842203) B7842203
theorem B3485423 : Blo 2065435 3485423 := bstep (se 1 (by rfl) ⟨2614067, by rfl⟩ : syracuseStep 3485423 = 5228135) B5228135
theorem B2323615 : Blo 2065435 2323615 := bstep (se 1 (by rfl) ⟨1742711, by rfl⟩ : syracuseStep 2323615 = 3485423) B3485423
theorem B3098153 : Blo 2065435 3098153 := bstep (se 2 (by rfl) ⟨1161807, by rfl⟩ : syracuseStep 3098153 = 2323615) B2323615
theorem B2065435 : Blo 2065435 2065435 := bstep (se 1 (by rfl) ⟨1549076, by rfl⟩ : syracuseStep 2065435 = 3098153) B3098153
theorem B2515181 : Blo 2065435 2515181 := bbase (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) (by norm_num)
theorem B26828597 : Blo 2065435 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B17885731 : Blo 2065435 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B23847641 : Blo 2065435 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B15898427 : Blo 2065435 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B10598951 : Blo 2065435 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B7065967 : Blo 2065435 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B9421289 : Blo 2065435 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B6280859 : Blo 2065435 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B16748957 : Blo 2065435 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B44663885 : Blo 2065435 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B29775923 : Blo 2065435 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B19850615 : Blo 2065435 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B13233743 : Blo 2065435 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B8822495 : Blo 2065435 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B5881663 : Blo 2065435 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B7842217 : Blo 2065435 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B10456289 : Blo 2065435 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B6970859 : Blo 2065435 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B4647239 : Blo 2065435 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B3098159 : Blo 2065435 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B2065439 : Blo 2065435 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B3098165 : Blo 2065435 3098165 := bbase (se 5 (by rfl) ⟨145226, by rfl⟩ : syracuseStep 3098165 = 290453) (by norm_num)
theorem B2065443 : Blo 2065435 2065443 := bstep (se 1 (by rfl) ⟨1549082, by rfl⟩ : syracuseStep 2065443 = 3098165) B3098165
theorem B5228165 : Blo 2065435 5228165 := bbase (se 4 (by rfl) ⟨490140, by rfl⟩ : syracuseStep 5228165 = 980281) (by norm_num)
theorem B3485443 : Blo 2065435 3485443 := bstep (se 1 (by rfl) ⟨2614082, by rfl⟩ : syracuseStep 3485443 = 5228165) B5228165
theorem B4647257 : Blo 2065435 4647257 := bstep (se 2 (by rfl) ⟨1742721, by rfl⟩ : syracuseStep 4647257 = 3485443) B3485443
theorem B3098171 : Blo 2065435 3098171 := bstep (se 1 (by rfl) ⟨2323628, by rfl⟩ : syracuseStep 3098171 = 4647257) B4647257
theorem B2065447 : Blo 2065435 2065447 := bstep (se 1 (by rfl) ⟨1549085, by rfl⟩ : syracuseStep 2065447 = 3098171) B3098171
theorem B2323633 : Blo 2065435 2323633 := bbase (se 2 (by rfl) ⟨871362, by rfl⟩ : syracuseStep 2323633 = 1742725) (by norm_num)
theorem B3098177 : Blo 2065435 3098177 := bstep (se 2 (by rfl) ⟨1161816, by rfl⟩ : syracuseStep 3098177 = 2323633) B2323633
theorem B2065451 : Blo 2065435 2065451 := bstep (se 1 (by rfl) ⟨1549088, by rfl⟩ : syracuseStep 2065451 = 3098177) B3098177
theorem B2205641 : Blo 2065435 2205641 := bbase (se 2 (by rfl) ⟨827115, by rfl⟩ : syracuseStep 2205641 = 1654231) (by norm_num)
theorem B5881709 : Blo 2065435 5881709 := bstep (se 3 (by rfl) ⟨1102820, by rfl⟩ : syracuseStep 5881709 = 2205641) B2205641
theorem B3921139 : Blo 2065435 3921139 := bstep (se 1 (by rfl) ⟨2940854, by rfl⟩ : syracuseStep 3921139 = 5881709) B5881709
theorem B5228185 : Blo 2065435 5228185 := bstep (se 2 (by rfl) ⟨1960569, by rfl⟩ : syracuseStep 5228185 = 3921139) B3921139
theorem B6970913 : Blo 2065435 6970913 := bstep (se 2 (by rfl) ⟨2614092, by rfl⟩ : syracuseStep 6970913 = 5228185) B5228185
theorem B4647275 : Blo 2065435 4647275 := bstep (se 1 (by rfl) ⟨3485456, by rfl⟩ : syracuseStep 4647275 = 6970913) B6970913
theorem B3098183 : Blo 2065435 3098183 := bstep (se 1 (by rfl) ⟨2323637, by rfl⟩ : syracuseStep 3098183 = 4647275) B4647275
theorem B2065455 : Blo 2065435 2065455 := bstep (se 1 (by rfl) ⟨1549091, by rfl⟩ : syracuseStep 2065455 = 3098183) B3098183
theorem B3098189 : Blo 2065435 3098189 := bbase (se 3 (by rfl) ⟨580910, by rfl⟩ : syracuseStep 3098189 = 1161821) (by norm_num)
theorem B2065459 : Blo 2065435 2065459 := bstep (se 1 (by rfl) ⟨1549094, by rfl⟩ : syracuseStep 2065459 = 3098189) B3098189
theorem B4647293 : Blo 2065435 4647293 := bbase (se 3 (by rfl) ⟨871367, by rfl⟩ : syracuseStep 4647293 = 1742735) (by norm_num)
theorem B3098195 : Blo 2065435 3098195 := bstep (se 1 (by rfl) ⟨2323646, by rfl⟩ : syracuseStep 3098195 = 4647293) B4647293
theorem B2065463 : Blo 2065435 2065463 := bstep (se 1 (by rfl) ⟨1549097, by rfl⟩ : syracuseStep 2065463 = 3098195) B3098195
theorem B3485477 : Blo 2065435 3485477 := bbase (se 4 (by rfl) ⟨326763, by rfl⟩ : syracuseStep 3485477 = 653527) (by norm_num)
theorem B2323651 : Blo 2065435 2323651 := bstep (se 1 (by rfl) ⟨1742738, by rfl⟩ : syracuseStep 2323651 = 3485477) B3485477
theorem B3098201 : Blo 2065435 3098201 := bstep (se 2 (by rfl) ⟨1161825, by rfl⟩ : syracuseStep 3098201 = 2323651) B2323651
theorem B2065467 : Blo 2065435 2065467 := bstep (se 1 (by rfl) ⟨1549100, by rfl⟩ : syracuseStep 2065467 = 3098201) B3098201
theorem B2940877 : Blo 2065435 2940877 := bbase (se 3 (by rfl) ⟨551414, by rfl⟩ : syracuseStep 2940877 = 1102829) (by norm_num)
theorem B15684677 : Blo 2065435 15684677 := bstep (se 4 (by rfl) ⟨1470438, by rfl⟩ : syracuseStep 15684677 = 2940877) B2940877
theorem B10456451 : Blo 2065435 10456451 := bstep (se 1 (by rfl) ⟨7842338, by rfl⟩ : syracuseStep 10456451 = 15684677) B15684677
theorem B6970967 : Blo 2065435 6970967 := bstep (se 1 (by rfl) ⟨5228225, by rfl⟩ : syracuseStep 6970967 = 10456451) B10456451
theorem B4647311 : Blo 2065435 4647311 := bstep (se 1 (by rfl) ⟨3485483, by rfl⟩ : syracuseStep 4647311 = 6970967) B6970967
theorem B3098207 : Blo 2065435 3098207 := bstep (se 1 (by rfl) ⟨2323655, by rfl⟩ : syracuseStep 3098207 = 4647311) B4647311
theorem B2065471 : Blo 2065435 2065471 := bstep (se 1 (by rfl) ⟨1549103, by rfl⟩ : syracuseStep 2065471 = 3098207) B3098207
theorem B3098213 : Blo 2065435 3098213 := bbase (se 4 (by rfl) ⟨290457, by rfl⟩ : syracuseStep 3098213 = 580915) (by norm_num)
theorem B2065475 : Blo 2065435 2065475 := bstep (se 1 (by rfl) ⟨1549106, by rfl⟩ : syracuseStep 2065475 = 3098213) B3098213
theorem B3308501 : Blo 2065435 3308501 := bbase (se 7 (by rfl) ⟨38771, by rfl⟩ : syracuseStep 3308501 = 77543) (by norm_num)
theorem B2205667 : Blo 2065435 2205667 := bstep (se 1 (by rfl) ⟨1654250, by rfl⟩ : syracuseStep 2205667 = 3308501) B3308501
theorem B2940889 : Blo 2065435 2940889 := bstep (se 2 (by rfl) ⟨1102833, by rfl⟩ : syracuseStep 2940889 = 2205667) B2205667
theorem B3921185 : Blo 2065435 3921185 := bstep (se 2 (by rfl) ⟨1470444, by rfl⟩ : syracuseStep 3921185 = 2940889) B2940889
theorem B2614123 : Blo 2065435 2614123 := bstep (se 1 (by rfl) ⟨1960592, by rfl⟩ : syracuseStep 2614123 = 3921185) B3921185
theorem B3485497 : Blo 2065435 3485497 := bstep (se 2 (by rfl) ⟨1307061, by rfl⟩ : syracuseStep 3485497 = 2614123) B2614123
theorem B4647329 : Blo 2065435 4647329 := bstep (se 2 (by rfl) ⟨1742748, by rfl⟩ : syracuseStep 4647329 = 3485497) B3485497
theorem B3098219 : Blo 2065435 3098219 := bstep (se 1 (by rfl) ⟨2323664, by rfl⟩ : syracuseStep 3098219 = 4647329) B4647329
theorem B2065479 : Blo 2065435 2065479 := bstep (se 1 (by rfl) ⟨1549109, by rfl⟩ : syracuseStep 2065479 = 3098219) B3098219
theorem B2323669 : Blo 2065435 2323669 := bbase (se 7 (by rfl) ⟨27230, by rfl⟩ : syracuseStep 2323669 = 54461) (by norm_num)
theorem B3098225 : Blo 2065435 3098225 := bstep (se 2 (by rfl) ⟨1161834, by rfl⟩ : syracuseStep 3098225 = 2323669) B2323669
theorem B2065483 : Blo 2065435 2065483 := bstep (se 1 (by rfl) ⟨1549112, by rfl⟩ : syracuseStep 2065483 = 3098225) B3098225
theorem B2614133 : Blo 2065435 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B6971021 : Blo 2065435 6971021 := bstep (se 3 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 6971021 = 2614133) B2614133
theorem B4647347 : Blo 2065435 4647347 := bstep (se 1 (by rfl) ⟨3485510, by rfl⟩ : syracuseStep 4647347 = 6971021) B6971021
theorem B3098231 : Blo 2065435 3098231 := bstep (se 1 (by rfl) ⟨2323673, by rfl⟩ : syracuseStep 3098231 = 4647347) B4647347
theorem B2065487 : Blo 2065435 2065487 := bstep (se 1 (by rfl) ⟨1549115, by rfl⟩ : syracuseStep 2065487 = 3098231) B3098231
theorem B3098237 : Blo 2065435 3098237 := bbase (se 3 (by rfl) ⟨580919, by rfl⟩ : syracuseStep 3098237 = 1161839) (by norm_num)
theorem B2065491 : Blo 2065435 2065491 := bstep (se 1 (by rfl) ⟨1549118, by rfl⟩ : syracuseStep 2065491 = 3098237) B3098237
theorem B4647365 : Blo 2065435 4647365 := bbase (se 4 (by rfl) ⟨435690, by rfl⟩ : syracuseStep 4647365 = 871381) (by norm_num)
theorem B3098243 : Blo 2065435 3098243 := bstep (se 1 (by rfl) ⟨2323682, by rfl⟩ : syracuseStep 3098243 = 4647365) B4647365
theorem B2065495 : Blo 2065435 2065495 := bstep (se 1 (by rfl) ⟨1549121, by rfl⟩ : syracuseStep 2065495 = 3098243) B3098243
theorem B20122037 : Blo 2065435 20122037 := bbase (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) (by norm_num)
theorem B13414691 : Blo 2065435 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B35772509 : Blo 2065435 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B23848339 : Blo 2065435 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B31797785 : Blo 2065435 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B21198523 : Blo 2065435 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B28264697 : Blo 2065435 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B18843131 : Blo 2065435 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B12562087 : Blo 2065435 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B16749449 : Blo 2065435 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B11166299 : Blo 2065435 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B7444199 : Blo 2065435 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B4962799 : Blo 2065435 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B6617065 : Blo 2065435 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B8822753 : Blo 2065435 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B5881835 : Blo 2065435 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B3921223 : Blo 2065435 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B5228297 : Blo 2065435 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B3485531 : Blo 2065435 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B2323687 : Blo 2065435 2323687 := bstep (se 1 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 2323687 = 3485531) B3485531
theorem B3098249 : Blo 2065435 3098249 := bstep (se 2 (by rfl) ⟨1161843, by rfl⟩ : syracuseStep 3098249 = 2323687) B2323687
theorem B2065499 : Blo 2065435 2065499 := bstep (se 1 (by rfl) ⟨1549124, by rfl⟩ : syracuseStep 2065499 = 3098249) B3098249
theorem B10456613 : Blo 2065435 10456613 := bbase (se 4 (by rfl) ⟨980307, by rfl⟩ : syracuseStep 10456613 = 1960615) (by norm_num)
theorem B6971075 : Blo 2065435 6971075 := bstep (se 1 (by rfl) ⟨5228306, by rfl⟩ : syracuseStep 6971075 = 10456613) B10456613
theorem B4647383 : Blo 2065435 4647383 := bstep (se 1 (by rfl) ⟨3485537, by rfl⟩ : syracuseStep 4647383 = 6971075) B6971075
theorem B3098255 : Blo 2065435 3098255 := bstep (se 1 (by rfl) ⟨2323691, by rfl⟩ : syracuseStep 3098255 = 4647383) B4647383
theorem B2065503 : Blo 2065435 2065503 := bstep (se 1 (by rfl) ⟨1549127, by rfl⟩ : syracuseStep 2065503 = 3098255) B3098255
theorem B3098261 : Blo 2065435 3098261 := bbase (se 6 (by rfl) ⟨72615, by rfl⟩ : syracuseStep 3098261 = 145231) (by norm_num)
theorem B2065507 : Blo 2065435 2065507 := bstep (se 1 (by rfl) ⟨1549130, by rfl⟩ : syracuseStep 2065507 = 3098261) B3098261
theorem B2093693 : Blo 2065435 2093693 := bbase (se 3 (by rfl) ⟨392567, by rfl⟩ : syracuseStep 2093693 = 785135) (by norm_num)
theorem B5583181 : Blo 2065435 5583181 := bstep (se 3 (by rfl) ⟨1046846, by rfl⟩ : syracuseStep 5583181 = 2093693) B2093693
theorem B7444241 : Blo 2065435 7444241 := bstep (se 2 (by rfl) ⟨2791590, by rfl⟩ : syracuseStep 7444241 = 5583181) B5583181
theorem B4962827 : Blo 2065435 4962827 := bstep (se 1 (by rfl) ⟨3722120, by rfl⟩ : syracuseStep 4962827 = 7444241) B7444241
theorem B13234205 : Blo 2065435 13234205 := bstep (se 3 (by rfl) ⟨2481413, by rfl⟩ : syracuseStep 13234205 = 4962827) B4962827
theorem B8822803 : Blo 2065435 8822803 := bstep (se 1 (by rfl) ⟨6617102, by rfl⟩ : syracuseStep 8822803 = 13234205) B13234205
theorem B11763737 : Blo 2065435 11763737 := bstep (se 2 (by rfl) ⟨4411401, by rfl⟩ : syracuseStep 11763737 = 8822803) B8822803
theorem B7842491 : Blo 2065435 7842491 := bstep (se 1 (by rfl) ⟨5881868, by rfl⟩ : syracuseStep 7842491 = 11763737) B11763737
theorem B5228327 : Blo 2065435 5228327 := bstep (se 1 (by rfl) ⟨3921245, by rfl⟩ : syracuseStep 5228327 = 7842491) B7842491
theorem B3485551 : Blo 2065435 3485551 := bstep (se 1 (by rfl) ⟨2614163, by rfl⟩ : syracuseStep 3485551 = 5228327) B5228327
theorem B4647401 : Blo 2065435 4647401 := bstep (se 2 (by rfl) ⟨1742775, by rfl⟩ : syracuseStep 4647401 = 3485551) B3485551
theorem B3098267 : Blo 2065435 3098267 := bstep (se 1 (by rfl) ⟨2323700, by rfl⟩ : syracuseStep 3098267 = 4647401) B4647401
theorem B2065511 : Blo 2065435 2065511 := bstep (se 1 (by rfl) ⟨1549133, by rfl⟩ : syracuseStep 2065511 = 3098267) B3098267
theorem B2323705 : Blo 2065435 2323705 := bbase (se 2 (by rfl) ⟨871389, by rfl⟩ : syracuseStep 2323705 = 1742779) (by norm_num)
theorem B3098273 : Blo 2065435 3098273 := bstep (se 2 (by rfl) ⟨1161852, by rfl⟩ : syracuseStep 3098273 = 2323705) B2323705
theorem B2065515 : Blo 2065435 2065515 := bstep (se 1 (by rfl) ⟨1549136, by rfl⟩ : syracuseStep 2065515 = 3098273) B3098273
theorem B8822837 : Blo 2065435 8822837 := bbase (se 5 (by rfl) ⟨413570, by rfl⟩ : syracuseStep 8822837 = 827141) (by norm_num)
theorem B5881891 : Blo 2065435 5881891 := bstep (se 1 (by rfl) ⟨4411418, by rfl⟩ : syracuseStep 5881891 = 8822837) B8822837
theorem B7842521 : Blo 2065435 7842521 := bstep (se 2 (by rfl) ⟨2940945, by rfl⟩ : syracuseStep 7842521 = 5881891) B5881891
theorem B5228347 : Blo 2065435 5228347 := bstep (se 1 (by rfl) ⟨3921260, by rfl⟩ : syracuseStep 5228347 = 7842521) B7842521
theorem B6971129 : Blo 2065435 6971129 := bstep (se 2 (by rfl) ⟨2614173, by rfl⟩ : syracuseStep 6971129 = 5228347) B5228347
theorem B4647419 : Blo 2065435 4647419 := bstep (se 1 (by rfl) ⟨3485564, by rfl⟩ : syracuseStep 4647419 = 6971129) B6971129
theorem B3098279 : Blo 2065435 3098279 := bstep (se 1 (by rfl) ⟨2323709, by rfl⟩ : syracuseStep 3098279 = 4647419) B4647419
theorem B2065519 : Blo 2065435 2065519 := bstep (se 1 (by rfl) ⟨1549139, by rfl⟩ : syracuseStep 2065519 = 3098279) B3098279
theorem B3098285 : Blo 2065435 3098285 := bbase (se 3 (by rfl) ⟨580928, by rfl⟩ : syracuseStep 3098285 = 1161857) (by norm_num)
theorem B2065523 : Blo 2065435 2065523 := bstep (se 1 (by rfl) ⟨1549142, by rfl⟩ : syracuseStep 2065523 = 3098285) B3098285
theorem B4647437 : Blo 2065435 4647437 := bbase (se 3 (by rfl) ⟨871394, by rfl⟩ : syracuseStep 4647437 = 1742789) (by norm_num)
theorem B3098291 : Blo 2065435 3098291 := bstep (se 1 (by rfl) ⟨2323718, by rfl⟩ : syracuseStep 3098291 = 4647437) B4647437
theorem B2065527 : Blo 2065435 2065527 := bstep (se 1 (by rfl) ⟨1549145, by rfl⟩ : syracuseStep 2065527 = 3098291) B3098291
theorem B2614189 : Blo 2065435 2614189 := bbase (se 3 (by rfl) ⟨490160, by rfl⟩ : syracuseStep 2614189 = 980321) (by norm_num)
theorem B3485585 : Blo 2065435 3485585 := bstep (se 2 (by rfl) ⟨1307094, by rfl⟩ : syracuseStep 3485585 = 2614189) B2614189
theorem B2323723 : Blo 2065435 2323723 := bstep (se 1 (by rfl) ⟨1742792, by rfl⟩ : syracuseStep 2323723 = 3485585) B3485585
theorem B3098297 : Blo 2065435 3098297 := bstep (se 2 (by rfl) ⟨1161861, by rfl⟩ : syracuseStep 3098297 = 2323723) B2323723
theorem B2065531 : Blo 2065435 2065531 := bstep (se 1 (by rfl) ⟨1549148, by rfl⟩ : syracuseStep 2065531 = 3098297) B3098297
theorem B13234357 : Blo 2065435 13234357 := bbase (se 5 (by rfl) ⟨620360, by rfl⟩ : syracuseStep 13234357 = 1240721) (by norm_num)
theorem B17645809 : Blo 2065435 17645809 := bstep (se 2 (by rfl) ⟨6617178, by rfl⟩ : syracuseStep 17645809 = 13234357) B13234357
theorem B23527745 : Blo 2065435 23527745 := bstep (se 2 (by rfl) ⟨8822904, by rfl⟩ : syracuseStep 23527745 = 17645809) B17645809
theorem B15685163 : Blo 2065435 15685163 := bstep (se 1 (by rfl) ⟨11763872, by rfl⟩ : syracuseStep 15685163 = 23527745) B23527745
theorem B10456775 : Blo 2065435 10456775 := bstep (se 1 (by rfl) ⟨7842581, by rfl⟩ : syracuseStep 10456775 = 15685163) B15685163
theorem B6971183 : Blo 2065435 6971183 := bstep (se 1 (by rfl) ⟨5228387, by rfl⟩ : syracuseStep 6971183 = 10456775) B10456775
theorem B4647455 : Blo 2065435 4647455 := bstep (se 1 (by rfl) ⟨3485591, by rfl⟩ : syracuseStep 4647455 = 6971183) B6971183
theorem B3098303 : Blo 2065435 3098303 := bstep (se 1 (by rfl) ⟨2323727, by rfl⟩ : syracuseStep 3098303 = 4647455) B4647455
theorem B2065535 : Blo 2065435 2065535 := bstep (se 1 (by rfl) ⟨1549151, by rfl⟩ : syracuseStep 2065535 = 3098303) B3098303
theorem B3098309 : Blo 2065435 3098309 := bbase (se 4 (by rfl) ⟨290466, by rfl⟩ : syracuseStep 3098309 = 580933) (by norm_num)
theorem B2065539 : Blo 2065435 2065539 := bstep (se 1 (by rfl) ⟨1549154, by rfl⟩ : syracuseStep 2065539 = 3098309) B3098309
theorem B3485605 : Blo 2065435 3485605 := bbase (se 4 (by rfl) ⟨326775, by rfl⟩ : syracuseStep 3485605 = 653551) (by norm_num)
theorem B4647473 : Blo 2065435 4647473 := bstep (se 2 (by rfl) ⟨1742802, by rfl⟩ : syracuseStep 4647473 = 3485605) B3485605
theorem B3098315 : Blo 2065435 3098315 := bstep (se 1 (by rfl) ⟨2323736, by rfl⟩ : syracuseStep 3098315 = 4647473) B4647473
theorem B2065543 : Blo 2065435 2065543 := bstep (se 1 (by rfl) ⟨1549157, by rfl⟩ : syracuseStep 2065543 = 3098315) B3098315
theorem B2323741 : Blo 2065435 2323741 := bbase (se 3 (by rfl) ⟨435701, by rfl⟩ : syracuseStep 2323741 = 871403) (by norm_num)
theorem B3098321 : Blo 2065435 3098321 := bstep (se 2 (by rfl) ⟨1161870, by rfl⟩ : syracuseStep 3098321 = 2323741) B2323741
theorem B2065547 : Blo 2065435 2065547 := bstep (se 1 (by rfl) ⟨1549160, by rfl⟩ : syracuseStep 2065547 = 3098321) B3098321
theorem B6971237 : Blo 2065435 6971237 := bbase (se 4 (by rfl) ⟨653553, by rfl⟩ : syracuseStep 6971237 = 1307107) (by norm_num)
theorem B4647491 : Blo 2065435 4647491 := bstep (se 1 (by rfl) ⟨3485618, by rfl⟩ : syracuseStep 4647491 = 6971237) B6971237
theorem B3098327 : Blo 2065435 3098327 := bstep (se 1 (by rfl) ⟨2323745, by rfl⟩ : syracuseStep 3098327 = 4647491) B4647491
theorem B2065551 : Blo 2065435 2065551 := bstep (se 1 (by rfl) ⟨1549163, by rfl⟩ : syracuseStep 2065551 = 3098327) B3098327
theorem B3098333 : Blo 2065435 3098333 := bbase (se 3 (by rfl) ⟨580937, by rfl⟩ : syracuseStep 3098333 = 1161875) (by norm_num)
theorem B2065555 : Blo 2065435 2065555 := bstep (se 1 (by rfl) ⟨1549166, by rfl⟩ : syracuseStep 2065555 = 3098333) B3098333
theorem B4647509 : Blo 2065435 4647509 := bbase (se 8 (by rfl) ⟨27231, by rfl⟩ : syracuseStep 4647509 = 54463) (by norm_num)
theorem B3098339 : Blo 2065435 3098339 := bstep (se 1 (by rfl) ⟨2323754, by rfl⟩ : syracuseStep 3098339 = 4647509) B4647509
theorem B2065559 : Blo 2065435 2065559 := bstep (se 1 (by rfl) ⟨1549169, by rfl⟩ : syracuseStep 2065559 = 3098339) B3098339
theorem B14132789 : Blo 2065435 14132789 := bbase (se 5 (by rfl) ⟨662474, by rfl⟩ : syracuseStep 14132789 = 1324949) (by norm_num)
theorem B9421859 : Blo 2065435 9421859 := bstep (se 1 (by rfl) ⟨7066394, by rfl⟩ : syracuseStep 9421859 = 14132789) B14132789
theorem B6281239 : Blo 2065435 6281239 := bstep (se 1 (by rfl) ⟨4710929, by rfl⟩ : syracuseStep 6281239 = 9421859) B9421859
theorem B8374985 : Blo 2065435 8374985 := bstep (se 2 (by rfl) ⟨3140619, by rfl⟩ : syracuseStep 8374985 = 6281239) B6281239
theorem B5583323 : Blo 2065435 5583323 := bstep (se 1 (by rfl) ⟨4187492, by rfl⟩ : syracuseStep 5583323 = 8374985) B8374985
theorem B3722215 : Blo 2065435 3722215 := bstep (se 1 (by rfl) ⟨2791661, by rfl⟩ : syracuseStep 3722215 = 5583323) B5583323
theorem B4962953 : Blo 2065435 4962953 := bstep (se 2 (by rfl) ⟨1861107, by rfl⟩ : syracuseStep 4962953 = 3722215) B3722215
theorem B3308635 : Blo 2065435 3308635 := bstep (se 1 (by rfl) ⟨2481476, by rfl⟩ : syracuseStep 3308635 = 4962953) B4962953
theorem B4411513 : Blo 2065435 4411513 := bstep (se 2 (by rfl) ⟨1654317, by rfl⟩ : syracuseStep 4411513 = 3308635) B3308635
theorem B5882017 : Blo 2065435 5882017 := bstep (se 2 (by rfl) ⟨2205756, by rfl⟩ : syracuseStep 5882017 = 4411513) B4411513
theorem B7842689 : Blo 2065435 7842689 := bstep (se 2 (by rfl) ⟨2941008, by rfl⟩ : syracuseStep 7842689 = 5882017) B5882017
theorem B5228459 : Blo 2065435 5228459 := bstep (se 1 (by rfl) ⟨3921344, by rfl⟩ : syracuseStep 5228459 = 7842689) B7842689
theorem B3485639 : Blo 2065435 3485639 := bstep (se 1 (by rfl) ⟨2614229, by rfl⟩ : syracuseStep 3485639 = 5228459) B5228459
theorem B2323759 : Blo 2065435 2323759 := bstep (se 1 (by rfl) ⟨1742819, by rfl⟩ : syracuseStep 2323759 = 3485639) B3485639
theorem B3098345 : Blo 2065435 3098345 := bstep (se 2 (by rfl) ⟨1161879, by rfl⟩ : syracuseStep 3098345 = 2323759) B2323759
theorem B2065563 : Blo 2065435 2065563 := bstep (se 1 (by rfl) ⟨1549172, by rfl⟩ : syracuseStep 2065563 = 3098345) B3098345
theorem B3722221 : Blo 2065435 3722221 := bbase (se 3 (by rfl) ⟨697916, by rfl⟩ : syracuseStep 3722221 = 1395833) (by norm_num)
theorem B4962961 : Blo 2065435 4962961 := bstep (se 2 (by rfl) ⟨1861110, by rfl⟩ : syracuseStep 4962961 = 3722221) B3722221
theorem B26469125 : Blo 2065435 26469125 := bstep (se 4 (by rfl) ⟨2481480, by rfl⟩ : syracuseStep 26469125 = 4962961) B4962961
theorem B17646083 : Blo 2065435 17646083 := bstep (se 1 (by rfl) ⟨13234562, by rfl⟩ : syracuseStep 17646083 = 26469125) B26469125
theorem B11764055 : Blo 2065435 11764055 := bstep (se 1 (by rfl) ⟨8823041, by rfl⟩ : syracuseStep 11764055 = 17646083) B17646083
theorem B7842703 : Blo 2065435 7842703 := bstep (se 1 (by rfl) ⟨5882027, by rfl⟩ : syracuseStep 7842703 = 11764055) B11764055
theorem B10456937 : Blo 2065435 10456937 := bstep (se 2 (by rfl) ⟨3921351, by rfl⟩ : syracuseStep 10456937 = 7842703) B7842703
theorem B6971291 : Blo 2065435 6971291 := bstep (se 1 (by rfl) ⟨5228468, by rfl⟩ : syracuseStep 6971291 = 10456937) B10456937
theorem B4647527 : Blo 2065435 4647527 := bstep (se 1 (by rfl) ⟨3485645, by rfl⟩ : syracuseStep 4647527 = 6971291) B6971291
theorem B3098351 : Blo 2065435 3098351 := bstep (se 1 (by rfl) ⟨2323763, by rfl⟩ : syracuseStep 3098351 = 4647527) B4647527
theorem B2065567 : Blo 2065435 2065567 := bstep (se 1 (by rfl) ⟨1549175, by rfl⟩ : syracuseStep 2065567 = 3098351) B3098351
theorem B3098357 : Blo 2065435 3098357 := bbase (se 5 (by rfl) ⟨145235, by rfl⟩ : syracuseStep 3098357 = 290471) (by norm_num)
theorem B2065571 : Blo 2065435 2065571 := bstep (se 1 (by rfl) ⟨1549178, by rfl⟩ : syracuseStep 2065571 = 3098357) B3098357
theorem B8823077 : Blo 2065435 8823077 := bbase (se 4 (by rfl) ⟨827163, by rfl⟩ : syracuseStep 8823077 = 1654327) (by norm_num)
theorem B5882051 : Blo 2065435 5882051 := bstep (se 1 (by rfl) ⟨4411538, by rfl⟩ : syracuseStep 5882051 = 8823077) B8823077
theorem B3921367 : Blo 2065435 3921367 := bstep (se 1 (by rfl) ⟨2941025, by rfl⟩ : syracuseStep 3921367 = 5882051) B5882051
theorem B5228489 : Blo 2065435 5228489 := bstep (se 2 (by rfl) ⟨1960683, by rfl⟩ : syracuseStep 5228489 = 3921367) B3921367
theorem B3485659 : Blo 2065435 3485659 := bstep (se 1 (by rfl) ⟨2614244, by rfl⟩ : syracuseStep 3485659 = 5228489) B5228489
theorem B4647545 : Blo 2065435 4647545 := bstep (se 2 (by rfl) ⟨1742829, by rfl⟩ : syracuseStep 4647545 = 3485659) B3485659
theorem B3098363 : Blo 2065435 3098363 := bstep (se 1 (by rfl) ⟨2323772, by rfl⟩ : syracuseStep 3098363 = 4647545) B4647545
theorem B2065575 : Blo 2065435 2065575 := bstep (se 1 (by rfl) ⟨1549181, by rfl⟩ : syracuseStep 2065575 = 3098363) B3098363
theorem B2323777 : Blo 2065435 2323777 := bbase (se 2 (by rfl) ⟨871416, by rfl⟩ : syracuseStep 2323777 = 1742833) (by norm_num)
theorem B3098369 : Blo 2065435 3098369 := bstep (se 2 (by rfl) ⟨1161888, by rfl⟩ : syracuseStep 3098369 = 2323777) B2323777
theorem B2065579 : Blo 2065435 2065579 := bstep (se 1 (by rfl) ⟨1549184, by rfl⟩ : syracuseStep 2065579 = 3098369) B3098369
theorem B5228509 : Blo 2065435 5228509 := bbase (se 3 (by rfl) ⟨980345, by rfl⟩ : syracuseStep 5228509 = 1960691) (by norm_num)
theorem B6971345 : Blo 2065435 6971345 := bstep (se 2 (by rfl) ⟨2614254, by rfl⟩ : syracuseStep 6971345 = 5228509) B5228509
theorem B4647563 : Blo 2065435 4647563 := bstep (se 1 (by rfl) ⟨3485672, by rfl⟩ : syracuseStep 4647563 = 6971345) B6971345
theorem B3098375 : Blo 2065435 3098375 := bstep (se 1 (by rfl) ⟨2323781, by rfl⟩ : syracuseStep 3098375 = 4647563) B4647563
theorem B2065583 : Blo 2065435 2065583 := bstep (se 1 (by rfl) ⟨1549187, by rfl⟩ : syracuseStep 2065583 = 3098375) B3098375
theorem B3098381 : Blo 2065435 3098381 := bbase (se 3 (by rfl) ⟨580946, by rfl⟩ : syracuseStep 3098381 = 1161893) (by norm_num)
theorem B2065587 : Blo 2065435 2065587 := bstep (se 1 (by rfl) ⟨1549190, by rfl⟩ : syracuseStep 2065587 = 3098381) B3098381
theorem B4647581 : Blo 2065435 4647581 := bbase (se 3 (by rfl) ⟨871421, by rfl⟩ : syracuseStep 4647581 = 1742843) (by norm_num)
theorem B3098387 : Blo 2065435 3098387 := bstep (se 1 (by rfl) ⟨2323790, by rfl⟩ : syracuseStep 3098387 = 4647581) B4647581
theorem B2065591 : Blo 2065435 2065591 := bstep (se 1 (by rfl) ⟨1549193, by rfl⟩ : syracuseStep 2065591 = 3098387) B3098387
theorem B3485693 : Blo 2065435 3485693 := bbase (se 3 (by rfl) ⟨653567, by rfl⟩ : syracuseStep 3485693 = 1307135) (by norm_num)
theorem B2323795 : Blo 2065435 2323795 := bstep (se 1 (by rfl) ⟨1742846, by rfl⟩ : syracuseStep 2323795 = 3485693) B3485693
theorem B3098393 : Blo 2065435 3098393 := bstep (se 2 (by rfl) ⟨1161897, by rfl⟩ : syracuseStep 3098393 = 2323795) B2323795
theorem B2065595 : Blo 2065435 2065595 := bstep (se 1 (by rfl) ⟨1549196, by rfl⟩ : syracuseStep 2065595 = 3098393) B3098393
theorem B4411589 : Blo 2065435 4411589 := bbase (se 4 (by rfl) ⟨413586, by rfl⟩ : syracuseStep 4411589 = 827173) (by norm_num)
theorem B11764237 : Blo 2065435 11764237 := bstep (se 3 (by rfl) ⟨2205794, by rfl⟩ : syracuseStep 11764237 = 4411589) B4411589
theorem B15685649 : Blo 2065435 15685649 := bstep (se 2 (by rfl) ⟨5882118, by rfl⟩ : syracuseStep 15685649 = 11764237) B11764237
theorem B10457099 : Blo 2065435 10457099 := bstep (se 1 (by rfl) ⟨7842824, by rfl⟩ : syracuseStep 10457099 = 15685649) B15685649
theorem B6971399 : Blo 2065435 6971399 := bstep (se 1 (by rfl) ⟨5228549, by rfl⟩ : syracuseStep 6971399 = 10457099) B10457099
theorem B4647599 : Blo 2065435 4647599 := bstep (se 1 (by rfl) ⟨3485699, by rfl⟩ : syracuseStep 4647599 = 6971399) B6971399
theorem B3098399 : Blo 2065435 3098399 := bstep (se 1 (by rfl) ⟨2323799, by rfl⟩ : syracuseStep 3098399 = 4647599) B4647599
theorem B2065599 : Blo 2065435 2065599 := bstep (se 1 (by rfl) ⟨1549199, by rfl⟩ : syracuseStep 2065599 = 3098399) B3098399
theorem B3098405 : Blo 2065435 3098405 := bbase (se 4 (by rfl) ⟨290475, by rfl⟩ : syracuseStep 3098405 = 580951) (by norm_num)
theorem B2065603 : Blo 2065435 2065603 := bstep (se 1 (by rfl) ⟨1549202, by rfl⟩ : syracuseStep 2065603 = 3098405) B3098405
theorem B2614285 : Blo 2065435 2614285 := bbase (se 3 (by rfl) ⟨490178, by rfl⟩ : syracuseStep 2614285 = 980357) (by norm_num)
theorem B3485713 : Blo 2065435 3485713 := bstep (se 2 (by rfl) ⟨1307142, by rfl⟩ : syracuseStep 3485713 = 2614285) B2614285
theorem B4647617 : Blo 2065435 4647617 := bstep (se 2 (by rfl) ⟨1742856, by rfl⟩ : syracuseStep 4647617 = 3485713) B3485713
theorem B3098411 : Blo 2065435 3098411 := bstep (se 1 (by rfl) ⟨2323808, by rfl⟩ : syracuseStep 3098411 = 4647617) B4647617
theorem B2065607 : Blo 2065435 2065607 := bstep (se 1 (by rfl) ⟨1549205, by rfl⟩ : syracuseStep 2065607 = 3098411) B3098411
theorem B2323813 : Blo 2065435 2323813 := bbase (se 4 (by rfl) ⟨217857, by rfl⟩ : syracuseStep 2323813 = 435715) (by norm_num)
theorem B3098417 : Blo 2065435 3098417 := bstep (se 2 (by rfl) ⟨1161906, by rfl⟩ : syracuseStep 3098417 = 2323813) B2323813
theorem B2065611 : Blo 2065435 2065611 := bstep (se 1 (by rfl) ⟨1549208, by rfl⟩ : syracuseStep 2065611 = 3098417) B3098417
theorem B5882165 : Blo 2065435 5882165 := bbase (se 5 (by rfl) ⟨275726, by rfl⟩ : syracuseStep 5882165 = 551453) (by norm_num)
theorem B3921443 : Blo 2065435 3921443 := bstep (se 1 (by rfl) ⟨2941082, by rfl⟩ : syracuseStep 3921443 = 5882165) B5882165
theorem B2614295 : Blo 2065435 2614295 := bstep (se 1 (by rfl) ⟨1960721, by rfl⟩ : syracuseStep 2614295 = 3921443) B3921443
theorem B6971453 : Blo 2065435 6971453 := bstep (se 3 (by rfl) ⟨1307147, by rfl⟩ : syracuseStep 6971453 = 2614295) B2614295
theorem B4647635 : Blo 2065435 4647635 := bstep (se 1 (by rfl) ⟨3485726, by rfl⟩ : syracuseStep 4647635 = 6971453) B6971453
theorem B3098423 : Blo 2065435 3098423 := bstep (se 1 (by rfl) ⟨2323817, by rfl⟩ : syracuseStep 3098423 = 4647635) B4647635
theorem B2065615 : Blo 2065435 2065615 := bstep (se 1 (by rfl) ⟨1549211, by rfl⟩ : syracuseStep 2065615 = 3098423) B3098423
theorem B3098429 : Blo 2065435 3098429 := bbase (se 3 (by rfl) ⟨580955, by rfl⟩ : syracuseStep 3098429 = 1161911) (by norm_num)
theorem B2065619 : Blo 2065435 2065619 := bstep (se 1 (by rfl) ⟨1549214, by rfl⟩ : syracuseStep 2065619 = 3098429) B3098429
theorem B4647653 : Blo 2065435 4647653 := bbase (se 4 (by rfl) ⟨435717, by rfl⟩ : syracuseStep 4647653 = 871435) (by norm_num)
theorem B3098435 : Blo 2065435 3098435 := bstep (se 1 (by rfl) ⟨2323826, by rfl⟩ : syracuseStep 3098435 = 4647653) B4647653
theorem B2065623 : Blo 2065435 2065623 := bstep (se 1 (by rfl) ⟨1549217, by rfl⟩ : syracuseStep 2065623 = 3098435) B3098435
theorem B5228621 : Blo 2065435 5228621 := bbase (se 3 (by rfl) ⟨980366, by rfl⟩ : syracuseStep 5228621 = 1960733) (by norm_num)
theorem B3485747 : Blo 2065435 3485747 := bstep (se 1 (by rfl) ⟨2614310, by rfl⟩ : syracuseStep 3485747 = 5228621) B5228621
theorem B2323831 : Blo 2065435 2323831 := bstep (se 1 (by rfl) ⟨1742873, by rfl⟩ : syracuseStep 2323831 = 3485747) B3485747
theorem B3098441 : Blo 2065435 3098441 := bstep (se 2 (by rfl) ⟨1161915, by rfl⟩ : syracuseStep 3098441 = 2323831) B2323831
theorem B2065627 : Blo 2065435 2065627 := bstep (se 1 (by rfl) ⟨1549220, by rfl⟩ : syracuseStep 2065627 = 3098441) B3098441
theorem B2205829 : Blo 2065435 2205829 := bbase (se 4 (by rfl) ⟨206796, by rfl⟩ : syracuseStep 2205829 = 413593) (by norm_num)
theorem B2941105 : Blo 2065435 2941105 := bstep (se 2 (by rfl) ⟨1102914, by rfl⟩ : syracuseStep 2941105 = 2205829) B2205829
theorem B3921473 : Blo 2065435 3921473 := bstep (se 2 (by rfl) ⟨1470552, by rfl⟩ : syracuseStep 3921473 = 2941105) B2941105
theorem B10457261 : Blo 2065435 10457261 := bstep (se 3 (by rfl) ⟨1960736, by rfl⟩ : syracuseStep 10457261 = 3921473) B3921473
theorem B6971507 : Blo 2065435 6971507 := bstep (se 1 (by rfl) ⟨5228630, by rfl⟩ : syracuseStep 6971507 = 10457261) B10457261
theorem B4647671 : Blo 2065435 4647671 := bstep (se 1 (by rfl) ⟨3485753, by rfl⟩ : syracuseStep 4647671 = 6971507) B6971507
theorem B3098447 : Blo 2065435 3098447 := bstep (se 1 (by rfl) ⟨2323835, by rfl⟩ : syracuseStep 3098447 = 4647671) B4647671
theorem B2065631 : Blo 2065435 2065631 := bstep (se 1 (by rfl) ⟨1549223, by rfl⟩ : syracuseStep 2065631 = 3098447) B3098447
theorem B3098453 : Blo 2065435 3098453 := bbase (se 9 (by rfl) ⟨9077, by rfl⟩ : syracuseStep 3098453 = 18155) (by norm_num)
theorem B2065635 : Blo 2065435 2065635 := bstep (se 1 (by rfl) ⟨1549226, by rfl⟩ : syracuseStep 2065635 = 3098453) B3098453
theorem B8943733 : Blo 2065435 8943733 := bbase (se 5 (by rfl) ⟨419237, by rfl⟩ : syracuseStep 8943733 = 838475) (by norm_num)
theorem B11924977 : Blo 2065435 11924977 := bstep (se 2 (by rfl) ⟨4471866, by rfl⟩ : syracuseStep 11924977 = 8943733) B8943733
theorem B15899969 : Blo 2065435 15899969 := bstep (se 2 (by rfl) ⟨5962488, by rfl⟩ : syracuseStep 15899969 = 11924977) B11924977
theorem B10599979 : Blo 2065435 10599979 := bstep (se 1 (by rfl) ⟨7949984, by rfl⟩ : syracuseStep 10599979 = 15899969) B15899969
theorem B14133305 : Blo 2065435 14133305 := bstep (se 2 (by rfl) ⟨5299989, by rfl⟩ : syracuseStep 14133305 = 10599979) B10599979
theorem B37688813 : Blo 2065435 37688813 := bstep (se 3 (by rfl) ⟨7066652, by rfl⟩ : syracuseStep 37688813 = 14133305) B14133305
theorem B25125875 : Blo 2065435 25125875 := bstep (se 1 (by rfl) ⟨18844406, by rfl⟩ : syracuseStep 25125875 = 37688813) B37688813
theorem B16750583 : Blo 2065435 16750583 := bstep (se 1 (by rfl) ⟨12562937, by rfl⟩ : syracuseStep 16750583 = 25125875) B25125875
theorem B11167055 : Blo 2065435 11167055 := bstep (se 1 (by rfl) ⟨8375291, by rfl⟩ : syracuseStep 11167055 = 16750583) B16750583
theorem B7444703 : Blo 2065435 7444703 := bstep (se 1 (by rfl) ⟨5583527, by rfl⟩ : syracuseStep 7444703 = 11167055) B11167055
theorem B4963135 : Blo 2065435 4963135 := bstep (se 1 (by rfl) ⟨3722351, by rfl⟩ : syracuseStep 4963135 = 7444703) B7444703
theorem B6617513 : Blo 2065435 6617513 := bstep (se 2 (by rfl) ⟨2481567, by rfl⟩ : syracuseStep 6617513 = 4963135) B4963135
theorem B4411675 : Blo 2065435 4411675 := bstep (se 1 (by rfl) ⟨3308756, by rfl⟩ : syracuseStep 4411675 = 6617513) B6617513
theorem B5882233 : Blo 2065435 5882233 := bstep (se 2 (by rfl) ⟨2205837, by rfl⟩ : syracuseStep 5882233 = 4411675) B4411675
theorem B7842977 : Blo 2065435 7842977 := bstep (se 2 (by rfl) ⟨2941116, by rfl⟩ : syracuseStep 7842977 = 5882233) B5882233
theorem B5228651 : Blo 2065435 5228651 := bstep (se 1 (by rfl) ⟨3921488, by rfl⟩ : syracuseStep 5228651 = 7842977) B7842977
theorem B3485767 : Blo 2065435 3485767 := bstep (se 1 (by rfl) ⟨2614325, by rfl⟩ : syracuseStep 3485767 = 5228651) B5228651
theorem B4647689 : Blo 2065435 4647689 := bstep (se 2 (by rfl) ⟨1742883, by rfl⟩ : syracuseStep 4647689 = 3485767) B3485767
theorem B3098459 : Blo 2065435 3098459 := bstep (se 1 (by rfl) ⟨2323844, by rfl⟩ : syracuseStep 3098459 = 4647689) B4647689
theorem B2065639 : Blo 2065435 2065639 := bstep (se 1 (by rfl) ⟨1549229, by rfl⟩ : syracuseStep 2065639 = 3098459) B3098459
theorem B2323849 : Blo 2065435 2323849 := bbase (se 2 (by rfl) ⟨871443, by rfl⟩ : syracuseStep 2323849 = 1742887) (by norm_num)
theorem B3098465 : Blo 2065435 3098465 := bstep (se 2 (by rfl) ⟨1161924, by rfl⟩ : syracuseStep 3098465 = 2323849) B2323849
theorem B2065643 : Blo 2065435 2065643 := bstep (se 1 (by rfl) ⟨1549232, by rfl⟩ : syracuseStep 2065643 = 3098465) B3098465
theorem B20123477 : Blo 2065435 20123477 := bbase (se 9 (by rfl) ⟨58955, by rfl⟩ : syracuseStep 20123477 = 117911) (by norm_num)
theorem B13415651 : Blo 2065435 13415651 := bstep (se 1 (by rfl) ⟨10061738, by rfl⟩ : syracuseStep 13415651 = 20123477) B20123477
theorem B8943767 : Blo 2065435 8943767 := bstep (se 1 (by rfl) ⟨6707825, by rfl⟩ : syracuseStep 8943767 = 13415651) B13415651
theorem B5962511 : Blo 2065435 5962511 := bstep (se 1 (by rfl) ⟨4471883, by rfl⟩ : syracuseStep 5962511 = 8943767) B8943767
theorem B3975007 : Blo 2065435 3975007 := bstep (se 1 (by rfl) ⟨2981255, by rfl⟩ : syracuseStep 3975007 = 5962511) B5962511
theorem B5300009 : Blo 2065435 5300009 := bstep (se 2 (by rfl) ⟨1987503, by rfl⟩ : syracuseStep 5300009 = 3975007) B3975007
theorem B3533339 : Blo 2065435 3533339 := bstep (se 1 (by rfl) ⟨2650004, by rfl⟩ : syracuseStep 3533339 = 5300009) B5300009
theorem B9422237 : Blo 2065435 9422237 := bstep (se 3 (by rfl) ⟨1766669, by rfl⟩ : syracuseStep 9422237 = 3533339) B3533339
theorem B25125965 : Blo 2065435 25125965 := bstep (se 3 (by rfl) ⟨4711118, by rfl⟩ : syracuseStep 25125965 = 9422237) B9422237
theorem B16750643 : Blo 2065435 16750643 := bstep (se 1 (by rfl) ⟨12562982, by rfl⟩ : syracuseStep 16750643 = 25125965) B25125965
theorem B44668381 : Blo 2065435 44668381 := bstep (se 3 (by rfl) ⟨8375321, by rfl⟩ : syracuseStep 44668381 = 16750643) B16750643
theorem B59557841 : Blo 2065435 59557841 := bstep (se 2 (by rfl) ⟨22334190, by rfl⟩ : syracuseStep 59557841 = 44668381) B44668381
theorem B39705227 : Blo 2065435 39705227 := bstep (se 1 (by rfl) ⟨29778920, by rfl⟩ : syracuseStep 39705227 = 59557841) B59557841
theorem B26470151 : Blo 2065435 26470151 := bstep (se 1 (by rfl) ⟨19852613, by rfl⟩ : syracuseStep 26470151 = 39705227) B39705227
theorem B17646767 : Blo 2065435 17646767 := bstep (se 1 (by rfl) ⟨13235075, by rfl⟩ : syracuseStep 17646767 = 26470151) B26470151
theorem B11764511 : Blo 2065435 11764511 := bstep (se 1 (by rfl) ⟨8823383, by rfl⟩ : syracuseStep 11764511 = 17646767) B17646767
theorem B7843007 : Blo 2065435 7843007 := bstep (se 1 (by rfl) ⟨5882255, by rfl⟩ : syracuseStep 7843007 = 11764511) B11764511
theorem B5228671 : Blo 2065435 5228671 := bstep (se 1 (by rfl) ⟨3921503, by rfl⟩ : syracuseStep 5228671 = 7843007) B7843007
theorem B6971561 : Blo 2065435 6971561 := bstep (se 2 (by rfl) ⟨2614335, by rfl⟩ : syracuseStep 6971561 = 5228671) B5228671
theorem B4647707 : Blo 2065435 4647707 := bstep (se 1 (by rfl) ⟨3485780, by rfl⟩ : syracuseStep 4647707 = 6971561) B6971561
theorem B3098471 : Blo 2065435 3098471 := bstep (se 1 (by rfl) ⟨2323853, by rfl⟩ : syracuseStep 3098471 = 4647707) B4647707
theorem B2065647 : Blo 2065435 2065647 := bstep (se 1 (by rfl) ⟨1549235, by rfl⟩ : syracuseStep 2065647 = 3098471) B3098471
theorem B3098477 : Blo 2065435 3098477 := bbase (se 3 (by rfl) ⟨580964, by rfl⟩ : syracuseStep 3098477 = 1161929) (by norm_num)
theorem B2065651 : Blo 2065435 2065651 := bstep (se 1 (by rfl) ⟨1549238, by rfl⟩ : syracuseStep 2065651 = 3098477) B3098477
theorem B4647725 : Blo 2065435 4647725 := bbase (se 3 (by rfl) ⟨871448, by rfl⟩ : syracuseStep 4647725 = 1742897) (by norm_num)
theorem B3098483 : Blo 2065435 3098483 := bstep (se 1 (by rfl) ⟨2323862, by rfl⟩ : syracuseStep 3098483 = 4647725) B4647725
theorem B2065655 : Blo 2065435 2065655 := bstep (se 1 (by rfl) ⟨1549241, by rfl⟩ : syracuseStep 2065655 = 3098483) B3098483
theorem B3308789 : Blo 2065435 3308789 := bbase (se 5 (by rfl) ⟨155099, by rfl⟩ : syracuseStep 3308789 = 310199) (by norm_num)
theorem B8823437 : Blo 2065435 8823437 := bstep (se 3 (by rfl) ⟨1654394, by rfl⟩ : syracuseStep 8823437 = 3308789) B3308789
theorem B5882291 : Blo 2065435 5882291 := bstep (se 1 (by rfl) ⟨4411718, by rfl⟩ : syracuseStep 5882291 = 8823437) B8823437
theorem B3921527 : Blo 2065435 3921527 := bstep (se 1 (by rfl) ⟨2941145, by rfl⟩ : syracuseStep 3921527 = 5882291) B5882291
theorem B2614351 : Blo 2065435 2614351 := bstep (se 1 (by rfl) ⟨1960763, by rfl⟩ : syracuseStep 2614351 = 3921527) B3921527
theorem B3485801 : Blo 2065435 3485801 := bstep (se 2 (by rfl) ⟨1307175, by rfl⟩ : syracuseStep 3485801 = 2614351) B2614351
theorem B2323867 : Blo 2065435 2323867 := bstep (se 1 (by rfl) ⟨1742900, by rfl⟩ : syracuseStep 2323867 = 3485801) B3485801
theorem B3098489 : Blo 2065435 3098489 := bstep (se 2 (by rfl) ⟨1161933, by rfl⟩ : syracuseStep 3098489 = 2323867) B2323867
theorem B2065659 : Blo 2065435 2065659 := bstep (se 1 (by rfl) ⟨1549244, by rfl⟩ : syracuseStep 2065659 = 3098489) B3098489
theorem B3975037 : Blo 2065435 3975037 := bbase (se 3 (by rfl) ⟨745319, by rfl⟩ : syracuseStep 3975037 = 1490639) (by norm_num)
theorem B84800789 : Blo 2065435 84800789 := bstep (se 6 (by rfl) ⟨1987518, by rfl⟩ : syracuseStep 84800789 = 3975037) B3975037
theorem B56533859 : Blo 2065435 56533859 := bstep (se 1 (by rfl) ⟨42400394, by rfl⟩ : syracuseStep 56533859 = 84800789) B84800789
theorem B37689239 : Blo 2065435 37689239 := bstep (se 1 (by rfl) ⟨28266929, by rfl⟩ : syracuseStep 37689239 = 56533859) B56533859
theorem B25126159 : Blo 2065435 25126159 := bstep (se 1 (by rfl) ⟨18844619, by rfl⟩ : syracuseStep 25126159 = 37689239) B37689239
theorem B33501545 : Blo 2065435 33501545 := bstep (se 2 (by rfl) ⟨12563079, by rfl⟩ : syracuseStep 33501545 = 25126159) B25126159
theorem B22334363 : Blo 2065435 22334363 := bstep (se 1 (by rfl) ⟨16750772, by rfl⟩ : syracuseStep 22334363 = 33501545) B33501545
theorem B14889575 : Blo 2065435 14889575 := bstep (se 1 (by rfl) ⟨11167181, by rfl⟩ : syracuseStep 14889575 = 22334363) B22334363
theorem B9926383 : Blo 2065435 9926383 := bstep (se 1 (by rfl) ⟨7444787, by rfl⟩ : syracuseStep 9926383 = 14889575) B14889575
theorem B13235177 : Blo 2065435 13235177 := bstep (se 2 (by rfl) ⟨4963191, by rfl⟩ : syracuseStep 13235177 = 9926383) B9926383
theorem B35293805 : Blo 2065435 35293805 := bstep (se 3 (by rfl) ⟨6617588, by rfl⟩ : syracuseStep 35293805 = 13235177) B13235177
theorem B23529203 : Blo 2065435 23529203 := bstep (se 1 (by rfl) ⟨17646902, by rfl⟩ : syracuseStep 23529203 = 35293805) B35293805
theorem B15686135 : Blo 2065435 15686135 := bstep (se 1 (by rfl) ⟨11764601, by rfl⟩ : syracuseStep 15686135 = 23529203) B23529203
theorem B10457423 : Blo 2065435 10457423 := bstep (se 1 (by rfl) ⟨7843067, by rfl⟩ : syracuseStep 10457423 = 15686135) B15686135
theorem B6971615 : Blo 2065435 6971615 := bstep (se 1 (by rfl) ⟨5228711, by rfl⟩ : syracuseStep 6971615 = 10457423) B10457423
theorem B4647743 : Blo 2065435 4647743 := bstep (se 1 (by rfl) ⟨3485807, by rfl⟩ : syracuseStep 4647743 = 6971615) B6971615
theorem B3098495 : Blo 2065435 3098495 := bstep (se 1 (by rfl) ⟨2323871, by rfl⟩ : syracuseStep 3098495 = 4647743) B4647743
theorem B2065663 : Blo 2065435 2065663 := bstep (se 1 (by rfl) ⟨1549247, by rfl⟩ : syracuseStep 2065663 = 3098495) B3098495
theorem B3098501 : Blo 2065435 3098501 := bbase (se 4 (by rfl) ⟨290484, by rfl⟩ : syracuseStep 3098501 = 580969) (by norm_num)
theorem B2065667 : Blo 2065435 2065667 := bstep (se 1 (by rfl) ⟨1549250, by rfl⟩ : syracuseStep 2065667 = 3098501) B3098501
theorem B3485821 : Blo 2065435 3485821 := bbase (se 3 (by rfl) ⟨653591, by rfl⟩ : syracuseStep 3485821 = 1307183) (by norm_num)
theorem B4647761 : Blo 2065435 4647761 := bstep (se 2 (by rfl) ⟨1742910, by rfl⟩ : syracuseStep 4647761 = 3485821) B3485821
theorem B3098507 : Blo 2065435 3098507 := bstep (se 1 (by rfl) ⟨2323880, by rfl⟩ : syracuseStep 3098507 = 4647761) B4647761
theorem B2065671 : Blo 2065435 2065671 := bstep (se 1 (by rfl) ⟨1549253, by rfl⟩ : syracuseStep 2065671 = 3098507) B3098507
theorem B2323885 : Blo 2065435 2323885 := bbase (se 3 (by rfl) ⟨435728, by rfl⟩ : syracuseStep 2323885 = 871457) (by norm_num)
theorem B3098513 : Blo 2065435 3098513 := bstep (se 2 (by rfl) ⟨1161942, by rfl⟩ : syracuseStep 3098513 = 2323885) B2323885
theorem B2065675 : Blo 2065435 2065675 := bstep (se 1 (by rfl) ⟨1549256, by rfl⟩ : syracuseStep 2065675 = 3098513) B3098513
theorem B6971669 : Blo 2065435 6971669 := bbase (se 6 (by rfl) ⟨163398, by rfl⟩ : syracuseStep 6971669 = 326797) (by norm_num)
theorem B4647779 : Blo 2065435 4647779 := bstep (se 1 (by rfl) ⟨3485834, by rfl⟩ : syracuseStep 4647779 = 6971669) B6971669
theorem B3098519 : Blo 2065435 3098519 := bstep (se 1 (by rfl) ⟨2323889, by rfl⟩ : syracuseStep 3098519 = 4647779) B4647779
theorem B2065679 : Blo 2065435 2065679 := bstep (se 1 (by rfl) ⟨1549259, by rfl⟩ : syracuseStep 2065679 = 3098519) B3098519
theorem B3098525 : Blo 2065435 3098525 := bbase (se 3 (by rfl) ⟨580973, by rfl⟩ : syracuseStep 3098525 = 1161947) (by norm_num)
theorem B2065683 : Blo 2065435 2065683 := bstep (se 1 (by rfl) ⟨1549262, by rfl⟩ : syracuseStep 2065683 = 3098525) B3098525
theorem B4647797 : Blo 2065435 4647797 := bbase (se 5 (by rfl) ⟨217865, by rfl⟩ : syracuseStep 4647797 = 435731) (by norm_num)
theorem B3098531 : Blo 2065435 3098531 := bstep (se 1 (by rfl) ⟨2323898, by rfl⟩ : syracuseStep 3098531 = 4647797) B4647797
theorem B2065687 : Blo 2065435 2065687 := bstep (se 1 (by rfl) ⟨1549265, by rfl⟩ : syracuseStep 2065687 = 3098531) B3098531
theorem B4029325 : Blo 2065435 4029325 := bbase (se 3 (by rfl) ⟨755498, by rfl⟩ : syracuseStep 4029325 = 1510997) (by norm_num)
theorem B21489733 : Blo 2065435 21489733 := bstep (se 4 (by rfl) ⟨2014662, by rfl⟩ : syracuseStep 21489733 = 4029325) B4029325
theorem B28652977 : Blo 2065435 28652977 := bstep (se 2 (by rfl) ⟨10744866, by rfl⟩ : syracuseStep 28652977 = 21489733) B21489733
theorem B38203969 : Blo 2065435 38203969 := bstep (se 2 (by rfl) ⟨14326488, by rfl⟩ : syracuseStep 38203969 = 28652977) B28652977
theorem B50938625 : Blo 2065435 50938625 := bstep (se 2 (by rfl) ⟨19101984, by rfl⟩ : syracuseStep 50938625 = 38203969) B38203969
theorem B33959083 : Blo 2065435 33959083 := bstep (se 1 (by rfl) ⟨25469312, by rfl⟩ : syracuseStep 33959083 = 50938625) B50938625
theorem B45278777 : Blo 2065435 45278777 := bstep (se 2 (by rfl) ⟨16979541, by rfl⟩ : syracuseStep 45278777 = 33959083) B33959083
theorem B120743405 : Blo 2065435 120743405 := bstep (se 3 (by rfl) ⟨22639388, by rfl⟩ : syracuseStep 120743405 = 45278777) B45278777
theorem B80495603 : Blo 2065435 80495603 := bstep (se 1 (by rfl) ⟨60371702, by rfl⟩ : syracuseStep 80495603 = 120743405) B120743405
theorem B53663735 : Blo 2065435 53663735 := bstep (se 1 (by rfl) ⟨40247801, by rfl⟩ : syracuseStep 53663735 = 80495603) B80495603
theorem B143103293 : Blo 2065435 143103293 := bstep (se 3 (by rfl) ⟨26831867, by rfl⟩ : syracuseStep 143103293 = 53663735) B53663735
theorem B95402195 : Blo 2065435 95402195 := bstep (se 1 (by rfl) ⟨71551646, by rfl⟩ : syracuseStep 95402195 = 143103293) B143103293
theorem B63601463 : Blo 2065435 63601463 := bstep (se 1 (by rfl) ⟨47701097, by rfl⟩ : syracuseStep 63601463 = 95402195) B95402195
theorem B169603901 : Blo 2065435 169603901 := bstep (se 3 (by rfl) ⟨31800731, by rfl⟩ : syracuseStep 169603901 = 63601463) B63601463
theorem B113069267 : Blo 2065435 113069267 := bstep (se 1 (by rfl) ⟨84801950, by rfl⟩ : syracuseStep 113069267 = 169603901) B169603901
theorem B75379511 : Blo 2065435 75379511 := bstep (se 1 (by rfl) ⟨56534633, by rfl⟩ : syracuseStep 75379511 = 113069267) B113069267
theorem B50253007 : Blo 2065435 50253007 := bstep (se 1 (by rfl) ⟨37689755, by rfl⟩ : syracuseStep 50253007 = 75379511) B75379511
theorem B67004009 : Blo 2065435 67004009 := bstep (se 2 (by rfl) ⟨25126503, by rfl⟩ : syracuseStep 67004009 = 50253007) B50253007
theorem B44669339 : Blo 2065435 44669339 := bstep (se 1 (by rfl) ⟨33502004, by rfl⟩ : syracuseStep 44669339 = 67004009) B67004009
theorem B29779559 : Blo 2065435 29779559 := bstep (se 1 (by rfl) ⟨22334669, by rfl⟩ : syracuseStep 29779559 = 44669339) B44669339
theorem B19853039 : Blo 2065435 19853039 := bstep (se 1 (by rfl) ⟨14889779, by rfl⟩ : syracuseStep 19853039 = 29779559) B29779559
theorem B13235359 : Blo 2065435 13235359 := bstep (se 1 (by rfl) ⟨9926519, by rfl⟩ : syracuseStep 13235359 = 19853039) B19853039
theorem B17647145 : Blo 2065435 17647145 := bstep (se 2 (by rfl) ⟨6617679, by rfl⟩ : syracuseStep 17647145 = 13235359) B13235359
theorem B11764763 : Blo 2065435 11764763 := bstep (se 1 (by rfl) ⟨8823572, by rfl⟩ : syracuseStep 11764763 = 17647145) B17647145
theorem B7843175 : Blo 2065435 7843175 := bstep (se 1 (by rfl) ⟨5882381, by rfl⟩ : syracuseStep 7843175 = 11764763) B11764763
theorem B5228783 : Blo 2065435 5228783 := bstep (se 1 (by rfl) ⟨3921587, by rfl⟩ : syracuseStep 5228783 = 7843175) B7843175
theorem B3485855 : Blo 2065435 3485855 := bstep (se 1 (by rfl) ⟨2614391, by rfl⟩ : syracuseStep 3485855 = 5228783) B5228783
theorem B2323903 : Blo 2065435 2323903 := bstep (se 1 (by rfl) ⟨1742927, by rfl⟩ : syracuseStep 2323903 = 3485855) B3485855
theorem B3098537 : Blo 2065435 3098537 := bstep (se 2 (by rfl) ⟨1161951, by rfl⟩ : syracuseStep 3098537 = 2323903) B2323903
theorem B2065691 : Blo 2065435 2065691 := bstep (se 1 (by rfl) ⟨1549268, by rfl⟩ : syracuseStep 2065691 = 3098537) B3098537
theorem B7843189 : Blo 2065435 7843189 := bbase (se 5 (by rfl) ⟨367649, by rfl⟩ : syracuseStep 7843189 = 735299) (by norm_num)
theorem B10457585 : Blo 2065435 10457585 := bstep (se 2 (by rfl) ⟨3921594, by rfl⟩ : syracuseStep 10457585 = 7843189) B7843189
theorem B6971723 : Blo 2065435 6971723 := bstep (se 1 (by rfl) ⟨5228792, by rfl⟩ : syracuseStep 6971723 = 10457585) B10457585
theorem B4647815 : Blo 2065435 4647815 := bstep (se 1 (by rfl) ⟨3485861, by rfl⟩ : syracuseStep 4647815 = 6971723) B6971723
theorem B3098543 : Blo 2065435 3098543 := bstep (se 1 (by rfl) ⟨2323907, by rfl⟩ : syracuseStep 3098543 = 4647815) B4647815
theorem B2065695 : Blo 2065435 2065695 := bstep (se 1 (by rfl) ⟨1549271, by rfl⟩ : syracuseStep 2065695 = 3098543) B3098543
theorem B3098549 : Blo 2065435 3098549 := bbase (se 5 (by rfl) ⟨145244, by rfl⟩ : syracuseStep 3098549 = 290489) (by norm_num)
theorem B2065699 : Blo 2065435 2065699 := bstep (se 1 (by rfl) ⟨1549274, by rfl⟩ : syracuseStep 2065699 = 3098549) B3098549
theorem B5228813 : Blo 2065435 5228813 := bbase (se 3 (by rfl) ⟨980402, by rfl⟩ : syracuseStep 5228813 = 1960805) (by norm_num)
theorem B3485875 : Blo 2065435 3485875 := bstep (se 1 (by rfl) ⟨2614406, by rfl⟩ : syracuseStep 3485875 = 5228813) B5228813
theorem B4647833 : Blo 2065435 4647833 := bstep (se 2 (by rfl) ⟨1742937, by rfl⟩ : syracuseStep 4647833 = 3485875) B3485875
theorem B3098555 : Blo 2065435 3098555 := bstep (se 1 (by rfl) ⟨2323916, by rfl⟩ : syracuseStep 3098555 = 4647833) B4647833
theorem B2065703 : Blo 2065435 2065703 := bstep (se 1 (by rfl) ⟨1549277, by rfl⟩ : syracuseStep 2065703 = 3098555) B3098555
theorem B2323921 : Blo 2065435 2323921 := bbase (se 2 (by rfl) ⟨871470, by rfl⟩ : syracuseStep 2323921 = 1742941) (by norm_num)
theorem B3098561 : Blo 2065435 3098561 := bstep (se 2 (by rfl) ⟨1161960, by rfl⟩ : syracuseStep 3098561 = 2323921) B2323921
theorem B2065707 : Blo 2065435 2065707 := bstep (se 1 (by rfl) ⟨1549280, by rfl⟩ : syracuseStep 2065707 = 3098561) B3098561
theorem B4411829 : Blo 2065435 4411829 := bbase (se 5 (by rfl) ⟨206804, by rfl⟩ : syracuseStep 4411829 = 413609) (by norm_num)
theorem B2941219 : Blo 2065435 2941219 := bstep (se 1 (by rfl) ⟨2205914, by rfl⟩ : syracuseStep 2941219 = 4411829) B4411829
theorem B3921625 : Blo 2065435 3921625 := bstep (se 2 (by rfl) ⟨1470609, by rfl⟩ : syracuseStep 3921625 = 2941219) B2941219
theorem B5228833 : Blo 2065435 5228833 := bstep (se 2 (by rfl) ⟨1960812, by rfl⟩ : syracuseStep 5228833 = 3921625) B3921625
theorem B6971777 : Blo 2065435 6971777 := bstep (se 2 (by rfl) ⟨2614416, by rfl⟩ : syracuseStep 6971777 = 5228833) B5228833
theorem B4647851 : Blo 2065435 4647851 := bstep (se 1 (by rfl) ⟨3485888, by rfl⟩ : syracuseStep 4647851 = 6971777) B6971777
theorem B3098567 : Blo 2065435 3098567 := bstep (se 1 (by rfl) ⟨2323925, by rfl⟩ : syracuseStep 3098567 = 4647851) B4647851
theorem B2065711 : Blo 2065435 2065711 := bstep (se 1 (by rfl) ⟨1549283, by rfl⟩ : syracuseStep 2065711 = 3098567) B3098567
theorem B3098573 : Blo 2065435 3098573 := bbase (se 3 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 3098573 = 1161965) (by norm_num)
theorem B2065715 : Blo 2065435 2065715 := bstep (se 1 (by rfl) ⟨1549286, by rfl⟩ : syracuseStep 2065715 = 3098573) B3098573
theorem B4647869 : Blo 2065435 4647869 := bbase (se 3 (by rfl) ⟨871475, by rfl⟩ : syracuseStep 4647869 = 1742951) (by norm_num)
theorem B3098579 : Blo 2065435 3098579 := bstep (se 1 (by rfl) ⟨2323934, by rfl⟩ : syracuseStep 3098579 = 4647869) B4647869
theorem B2065719 : Blo 2065435 2065719 := bstep (se 1 (by rfl) ⟨1549289, by rfl⟩ : syracuseStep 2065719 = 3098579) B3098579
theorem B3485909 : Blo 2065435 3485909 := bbase (se 7 (by rfl) ⟨40850, by rfl⟩ : syracuseStep 3485909 = 81701) (by norm_num)
theorem B2323939 : Blo 2065435 2323939 := bstep (se 1 (by rfl) ⟨1742954, by rfl⟩ : syracuseStep 2323939 = 3485909) B3485909
theorem B3098585 : Blo 2065435 3098585 := bstep (se 2 (by rfl) ⟨1161969, by rfl⟩ : syracuseStep 3098585 = 2323939) B2323939
theorem B2065723 : Blo 2065435 2065723 := bstep (se 1 (by rfl) ⟨1549292, by rfl⟩ : syracuseStep 2065723 = 3098585) B3098585
theorem B2481673 : Blo 2065435 2481673 := bbase (se 2 (by rfl) ⟨930627, by rfl⟩ : syracuseStep 2481673 = 1861255) (by norm_num)
theorem B3308897 : Blo 2065435 3308897 := bstep (se 2 (by rfl) ⟨1240836, by rfl⟩ : syracuseStep 3308897 = 2481673) B2481673
theorem B8823725 : Blo 2065435 8823725 := bstep (se 3 (by rfl) ⟨1654448, by rfl⟩ : syracuseStep 8823725 = 3308897) B3308897
theorem B5882483 : Blo 2065435 5882483 := bstep (se 1 (by rfl) ⟨4411862, by rfl⟩ : syracuseStep 5882483 = 8823725) B8823725
theorem B15686621 : Blo 2065435 15686621 := bstep (se 3 (by rfl) ⟨2941241, by rfl⟩ : syracuseStep 15686621 = 5882483) B5882483
theorem B10457747 : Blo 2065435 10457747 := bstep (se 1 (by rfl) ⟨7843310, by rfl⟩ : syracuseStep 10457747 = 15686621) B15686621
theorem B6971831 : Blo 2065435 6971831 := bstep (se 1 (by rfl) ⟨5228873, by rfl⟩ : syracuseStep 6971831 = 10457747) B10457747
theorem B4647887 : Blo 2065435 4647887 := bstep (se 1 (by rfl) ⟨3485915, by rfl⟩ : syracuseStep 4647887 = 6971831) B6971831
theorem B3098591 : Blo 2065435 3098591 := bstep (se 1 (by rfl) ⟨2323943, by rfl⟩ : syracuseStep 3098591 = 4647887) B4647887
theorem B2065727 : Blo 2065435 2065727 := bstep (se 1 (by rfl) ⟨1549295, by rfl⟩ : syracuseStep 2065727 = 3098591) B3098591
theorem B3098597 : Blo 2065435 3098597 := bbase (se 4 (by rfl) ⟨290493, by rfl⟩ : syracuseStep 3098597 = 580987) (by norm_num)
theorem B2065731 : Blo 2065435 2065731 := bstep (se 1 (by rfl) ⟨1549298, by rfl⟩ : syracuseStep 2065731 = 3098597) B3098597
theorem B3722525 : Blo 2065435 3722525 := bbase (se 3 (by rfl) ⟨697973, by rfl⟩ : syracuseStep 3722525 = 1395947) (by norm_num)
theorem B2481683 : Blo 2065435 2481683 := bstep (se 1 (by rfl) ⟨1861262, by rfl⟩ : syracuseStep 2481683 = 3722525) B3722525
theorem B6617821 : Blo 2065435 6617821 := bstep (se 3 (by rfl) ⟨1240841, by rfl⟩ : syracuseStep 6617821 = 2481683) B2481683
theorem B8823761 : Blo 2065435 8823761 := bstep (se 2 (by rfl) ⟨3308910, by rfl⟩ : syracuseStep 8823761 = 6617821) B6617821
theorem B5882507 : Blo 2065435 5882507 := bstep (se 1 (by rfl) ⟨4411880, by rfl⟩ : syracuseStep 5882507 = 8823761) B8823761
theorem B3921671 : Blo 2065435 3921671 := bstep (se 1 (by rfl) ⟨2941253, by rfl⟩ : syracuseStep 3921671 = 5882507) B5882507
theorem B2614447 : Blo 2065435 2614447 := bstep (se 1 (by rfl) ⟨1960835, by rfl⟩ : syracuseStep 2614447 = 3921671) B3921671
theorem B3485929 : Blo 2065435 3485929 := bstep (se 2 (by rfl) ⟨1307223, by rfl⟩ : syracuseStep 3485929 = 2614447) B2614447
theorem B4647905 : Blo 2065435 4647905 := bstep (se 2 (by rfl) ⟨1742964, by rfl⟩ : syracuseStep 4647905 = 3485929) B3485929
theorem B3098603 : Blo 2065435 3098603 := bstep (se 1 (by rfl) ⟨2323952, by rfl⟩ : syracuseStep 3098603 = 4647905) B4647905
theorem B2065735 : Blo 2065435 2065735 := bstep (se 1 (by rfl) ⟨1549301, by rfl⟩ : syracuseStep 2065735 = 3098603) B3098603
theorem B2323957 : Blo 2065435 2323957 := bbase (se 5 (by rfl) ⟨108935, by rfl⟩ : syracuseStep 2323957 = 217871) (by norm_num)
theorem B3098609 : Blo 2065435 3098609 := bstep (se 2 (by rfl) ⟨1161978, by rfl⟩ : syracuseStep 3098609 = 2323957) B2323957
theorem B2065739 : Blo 2065435 2065739 := bstep (se 1 (by rfl) ⟨1549304, by rfl⟩ : syracuseStep 2065739 = 3098609) B3098609
theorem B2614457 : Blo 2065435 2614457 := bbase (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) (by norm_num)
theorem B6971885 : Blo 2065435 6971885 := bstep (se 3 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 6971885 = 2614457) B2614457
theorem B4647923 : Blo 2065435 4647923 := bstep (se 1 (by rfl) ⟨3485942, by rfl⟩ : syracuseStep 4647923 = 6971885) B6971885
theorem B3098615 : Blo 2065435 3098615 := bstep (se 1 (by rfl) ⟨2323961, by rfl⟩ : syracuseStep 3098615 = 4647923) B4647923
theorem B2065743 : Blo 2065435 2065743 := bstep (se 1 (by rfl) ⟨1549307, by rfl⟩ : syracuseStep 2065743 = 3098615) B3098615
theorem B3098621 : Blo 2065435 3098621 := bbase (se 3 (by rfl) ⟨580991, by rfl⟩ : syracuseStep 3098621 = 1161983) (by norm_num)
theorem B2065747 : Blo 2065435 2065747 := bstep (se 1 (by rfl) ⟨1549310, by rfl⟩ : syracuseStep 2065747 = 3098621) B3098621
theorem B4647941 : Blo 2065435 4647941 := bbase (se 4 (by rfl) ⟨435744, by rfl⟩ : syracuseStep 4647941 = 871489) (by norm_num)
theorem B3098627 : Blo 2065435 3098627 := bstep (se 1 (by rfl) ⟨2323970, by rfl⟩ : syracuseStep 3098627 = 4647941) B4647941
theorem B2065751 : Blo 2065435 2065751 := bstep (se 1 (by rfl) ⟨1549313, by rfl⟩ : syracuseStep 2065751 = 3098627) B3098627
theorem B3921709 : Blo 2065435 3921709 := bbase (se 3 (by rfl) ⟨735320, by rfl⟩ : syracuseStep 3921709 = 1470641) (by norm_num)
theorem B5228945 : Blo 2065435 5228945 := bstep (se 2 (by rfl) ⟨1960854, by rfl⟩ : syracuseStep 5228945 = 3921709) B3921709
theorem B3485963 : Blo 2065435 3485963 := bstep (se 1 (by rfl) ⟨2614472, by rfl⟩ : syracuseStep 3485963 = 5228945) B5228945
theorem B2323975 : Blo 2065435 2323975 := bstep (se 1 (by rfl) ⟨1742981, by rfl⟩ : syracuseStep 2323975 = 3485963) B3485963
theorem B3098633 : Blo 2065435 3098633 := bstep (se 2 (by rfl) ⟨1161987, by rfl⟩ : syracuseStep 3098633 = 2323975) B2323975
theorem B2065755 : Blo 2065435 2065755 := bstep (se 1 (by rfl) ⟨1549316, by rfl⟩ : syracuseStep 2065755 = 3098633) B3098633
theorem B10457909 : Blo 2065435 10457909 := bbase (se 5 (by rfl) ⟨490214, by rfl⟩ : syracuseStep 10457909 = 980429) (by norm_num)
theorem B6971939 : Blo 2065435 6971939 := bstep (se 1 (by rfl) ⟨5228954, by rfl⟩ : syracuseStep 6971939 = 10457909) B10457909
theorem B4647959 : Blo 2065435 4647959 := bstep (se 1 (by rfl) ⟨3485969, by rfl⟩ : syracuseStep 4647959 = 6971939) B6971939
theorem B3098639 : Blo 2065435 3098639 := bstep (se 1 (by rfl) ⟨2323979, by rfl⟩ : syracuseStep 3098639 = 4647959) B4647959
theorem B2065759 : Blo 2065435 2065759 := bstep (se 1 (by rfl) ⟨1549319, by rfl⟩ : syracuseStep 2065759 = 3098639) B3098639
theorem B3098645 : Blo 2065435 3098645 := bbase (se 6 (by rfl) ⟨72624, by rfl⟩ : syracuseStep 3098645 = 145249) (by norm_num)
theorem B2065763 : Blo 2065435 2065763 := bstep (se 1 (by rfl) ⟨1549322, by rfl⟩ : syracuseStep 2065763 = 3098645) B3098645
theorem B2481721 : Blo 2065435 2481721 := bbase (se 2 (by rfl) ⟨930645, by rfl⟩ : syracuseStep 2481721 = 1861291) (by norm_num)
theorem B13235845 : Blo 2065435 13235845 := bstep (se 4 (by rfl) ⟨1240860, by rfl⟩ : syracuseStep 13235845 = 2481721) B2481721
theorem B17647793 : Blo 2065435 17647793 := bstep (se 2 (by rfl) ⟨6617922, by rfl⟩ : syracuseStep 17647793 = 13235845) B13235845
theorem B11765195 : Blo 2065435 11765195 := bstep (se 1 (by rfl) ⟨8823896, by rfl⟩ : syracuseStep 11765195 = 17647793) B17647793
theorem B7843463 : Blo 2065435 7843463 := bstep (se 1 (by rfl) ⟨5882597, by rfl⟩ : syracuseStep 7843463 = 11765195) B11765195
theorem B5228975 : Blo 2065435 5228975 := bstep (se 1 (by rfl) ⟨3921731, by rfl⟩ : syracuseStep 5228975 = 7843463) B7843463
theorem B3485983 : Blo 2065435 3485983 := bstep (se 1 (by rfl) ⟨2614487, by rfl⟩ : syracuseStep 3485983 = 5228975) B5228975
theorem B4647977 : Blo 2065435 4647977 := bstep (se 2 (by rfl) ⟨1742991, by rfl⟩ : syracuseStep 4647977 = 3485983) B3485983
theorem B3098651 : Blo 2065435 3098651 := bstep (se 1 (by rfl) ⟨2323988, by rfl⟩ : syracuseStep 3098651 = 4647977) B4647977
theorem B2065767 : Blo 2065435 2065767 := bstep (se 1 (by rfl) ⟨1549325, by rfl⟩ : syracuseStep 2065767 = 3098651) B3098651
theorem B2323993 : Blo 2065435 2323993 := bbase (se 2 (by rfl) ⟨871497, by rfl⟩ : syracuseStep 2323993 = 1742995) (by norm_num)
theorem B3098657 : Blo 2065435 3098657 := bstep (se 2 (by rfl) ⟨1161996, by rfl⟩ : syracuseStep 3098657 = 2323993) B2323993
theorem B2065771 : Blo 2065435 2065771 := bstep (se 1 (by rfl) ⟨1549328, by rfl⟩ : syracuseStep 2065771 = 3098657) B3098657
theorem B7843493 : Blo 2065435 7843493 := bbase (se 4 (by rfl) ⟨735327, by rfl⟩ : syracuseStep 7843493 = 1470655) (by norm_num)
theorem B5228995 : Blo 2065435 5228995 := bstep (se 1 (by rfl) ⟨3921746, by rfl⟩ : syracuseStep 5228995 = 7843493) B7843493
theorem B6971993 : Blo 2065435 6971993 := bstep (se 2 (by rfl) ⟨2614497, by rfl⟩ : syracuseStep 6971993 = 5228995) B5228995
theorem B4647995 : Blo 2065435 4647995 := bstep (se 1 (by rfl) ⟨3485996, by rfl⟩ : syracuseStep 4647995 = 6971993) B6971993
theorem B3098663 : Blo 2065435 3098663 := bstep (se 1 (by rfl) ⟨2323997, by rfl⟩ : syracuseStep 3098663 = 4647995) B4647995
theorem B2065775 : Blo 2065435 2065775 := bstep (se 1 (by rfl) ⟨1549331, by rfl⟩ : syracuseStep 2065775 = 3098663) B3098663
theorem B3098669 : Blo 2065435 3098669 := bbase (se 3 (by rfl) ⟨581000, by rfl⟩ : syracuseStep 3098669 = 1162001) (by norm_num)
theorem B2065779 : Blo 2065435 2065779 := bstep (se 1 (by rfl) ⟨1549334, by rfl⟩ : syracuseStep 2065779 = 3098669) B3098669
theorem B4648013 : Blo 2065435 4648013 := bbase (se 3 (by rfl) ⟨871502, by rfl⟩ : syracuseStep 4648013 = 1743005) (by norm_num)
theorem B3098675 : Blo 2065435 3098675 := bstep (se 1 (by rfl) ⟨2324006, by rfl⟩ : syracuseStep 3098675 = 4648013) B4648013
theorem B2065783 : Blo 2065435 2065783 := bstep (se 1 (by rfl) ⟨1549337, by rfl⟩ : syracuseStep 2065783 = 3098675) B3098675
theorem B2614513 : Blo 2065435 2614513 := bbase (se 2 (by rfl) ⟨980442, by rfl⟩ : syracuseStep 2614513 = 1960885) (by norm_num)
theorem B3486017 : Blo 2065435 3486017 := bstep (se 2 (by rfl) ⟨1307256, by rfl⟩ : syracuseStep 3486017 = 2614513) B2614513
theorem B2324011 : Blo 2065435 2324011 := bstep (se 1 (by rfl) ⟨1743008, by rfl⟩ : syracuseStep 2324011 = 3486017) B3486017
theorem B3098681 : Blo 2065435 3098681 := bstep (se 2 (by rfl) ⟨1162005, by rfl⟩ : syracuseStep 3098681 = 2324011) B2324011
theorem B2065787 : Blo 2065435 2065787 := bstep (se 1 (by rfl) ⟨1549340, by rfl⟩ : syracuseStep 2065787 = 3098681) B3098681
theorem B3140965 : Blo 2065435 3140965 := bbase (se 4 (by rfl) ⟨294465, by rfl⟩ : syracuseStep 3140965 = 588931) (by norm_num)
theorem B4187953 : Blo 2065435 4187953 := bstep (se 2 (by rfl) ⟨1570482, by rfl⟩ : syracuseStep 4187953 = 3140965) B3140965
theorem B22335749 : Blo 2065435 22335749 := bstep (se 4 (by rfl) ⟨2093976, by rfl⟩ : syracuseStep 22335749 = 4187953) B4187953
theorem B14890499 : Blo 2065435 14890499 := bstep (se 1 (by rfl) ⟨11167874, by rfl⟩ : syracuseStep 14890499 = 22335749) B22335749
theorem B9926999 : Blo 2065435 9926999 := bstep (se 1 (by rfl) ⟨7445249, by rfl⟩ : syracuseStep 9926999 = 14890499) B14890499
theorem B6617999 : Blo 2065435 6617999 := bstep (se 1 (by rfl) ⟨4963499, by rfl⟩ : syracuseStep 6617999 = 9926999) B9926999
theorem B4411999 : Blo 2065435 4411999 := bstep (se 1 (by rfl) ⟨3308999, by rfl⟩ : syracuseStep 4411999 = 6617999) B6617999
theorem B23530661 : Blo 2065435 23530661 := bstep (se 4 (by rfl) ⟨2205999, by rfl⟩ : syracuseStep 23530661 = 4411999) B4411999
theorem B15687107 : Blo 2065435 15687107 := bstep (se 1 (by rfl) ⟨11765330, by rfl⟩ : syracuseStep 15687107 = 23530661) B23530661
theorem B10458071 : Blo 2065435 10458071 := bstep (se 1 (by rfl) ⟨7843553, by rfl⟩ : syracuseStep 10458071 = 15687107) B15687107
theorem B6972047 : Blo 2065435 6972047 := bstep (se 1 (by rfl) ⟨5229035, by rfl⟩ : syracuseStep 6972047 = 10458071) B10458071
theorem B4648031 : Blo 2065435 4648031 := bstep (se 1 (by rfl) ⟨3486023, by rfl⟩ : syracuseStep 4648031 = 6972047) B6972047
theorem B3098687 : Blo 2065435 3098687 := bstep (se 1 (by rfl) ⟨2324015, by rfl⟩ : syracuseStep 3098687 = 4648031) B4648031
theorem B2065791 : Blo 2065435 2065791 := bstep (se 1 (by rfl) ⟨1549343, by rfl⟩ : syracuseStep 2065791 = 3098687) B3098687
theorem B3098693 : Blo 2065435 3098693 := bbase (se 4 (by rfl) ⟨290502, by rfl⟩ : syracuseStep 3098693 = 581005) (by norm_num)
theorem B2065795 : Blo 2065435 2065795 := bstep (se 1 (by rfl) ⟨1549346, by rfl⟩ : syracuseStep 2065795 = 3098693) B3098693
theorem B3486037 : Blo 2065435 3486037 := bbase (se 10 (by rfl) ⟨5106, by rfl⟩ : syracuseStep 3486037 = 10213) (by norm_num)
theorem B4648049 : Blo 2065435 4648049 := bstep (se 2 (by rfl) ⟨1743018, by rfl⟩ : syracuseStep 4648049 = 3486037) B3486037
theorem B3098699 : Blo 2065435 3098699 := bstep (se 1 (by rfl) ⟨2324024, by rfl⟩ : syracuseStep 3098699 = 4648049) B4648049
theorem B2065799 : Blo 2065435 2065799 := bstep (se 1 (by rfl) ⟨1549349, by rfl⟩ : syracuseStep 2065799 = 3098699) B3098699
theorem B2324029 : Blo 2065435 2324029 := bbase (se 3 (by rfl) ⟨435755, by rfl⟩ : syracuseStep 2324029 = 871511) (by norm_num)
theorem B3098705 : Blo 2065435 3098705 := bstep (se 2 (by rfl) ⟨1162014, by rfl⟩ : syracuseStep 3098705 = 2324029) B2324029
theorem B2065803 : Blo 2065435 2065803 := bstep (se 1 (by rfl) ⟨1549352, by rfl⟩ : syracuseStep 2065803 = 3098705) B3098705
theorem B6972101 : Blo 2065435 6972101 := bbase (se 4 (by rfl) ⟨653634, by rfl⟩ : syracuseStep 6972101 = 1307269) (by norm_num)
theorem B4648067 : Blo 2065435 4648067 := bstep (se 1 (by rfl) ⟨3486050, by rfl⟩ : syracuseStep 4648067 = 6972101) B6972101
theorem B3098711 : Blo 2065435 3098711 := bstep (se 1 (by rfl) ⟨2324033, by rfl⟩ : syracuseStep 3098711 = 4648067) B4648067
theorem B2065807 : Blo 2065435 2065807 := bstep (se 1 (by rfl) ⟨1549355, by rfl⟩ : syracuseStep 2065807 = 3098711) B3098711
theorem B3098717 : Blo 2065435 3098717 := bbase (se 3 (by rfl) ⟨581009, by rfl⟩ : syracuseStep 3098717 = 1162019) (by norm_num)
theorem B2065811 : Blo 2065435 2065811 := bstep (se 1 (by rfl) ⟨1549358, by rfl⟩ : syracuseStep 2065811 = 3098717) B3098717
theorem B4648085 : Blo 2065435 4648085 := bbase (se 6 (by rfl) ⟨108939, by rfl⟩ : syracuseStep 4648085 = 217879) (by norm_num)
theorem B3098723 : Blo 2065435 3098723 := bstep (se 1 (by rfl) ⟨2324042, by rfl⟩ : syracuseStep 3098723 = 4648085) B4648085
theorem B2065815 : Blo 2065435 2065815 := bstep (se 1 (by rfl) ⟨1549361, by rfl⟩ : syracuseStep 2065815 = 3098723) B3098723
theorem B2941373 : Blo 2065435 2941373 := bbase (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) (by norm_num)
theorem B7843661 : Blo 2065435 7843661 := bstep (se 3 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 7843661 = 2941373) B2941373
theorem B5229107 : Blo 2065435 5229107 := bstep (se 1 (by rfl) ⟨3921830, by rfl⟩ : syracuseStep 5229107 = 7843661) B7843661
theorem B3486071 : Blo 2065435 3486071 := bstep (se 1 (by rfl) ⟨2614553, by rfl⟩ : syracuseStep 3486071 = 5229107) B5229107
theorem B2324047 : Blo 2065435 2324047 := bstep (se 1 (by rfl) ⟨1743035, by rfl⟩ : syracuseStep 2324047 = 3486071) B3486071
theorem B3098729 : Blo 2065435 3098729 := bstep (se 2 (by rfl) ⟨1162023, by rfl⟩ : syracuseStep 3098729 = 2324047) B2324047
theorem B2065819 : Blo 2065435 2065819 := bstep (se 1 (by rfl) ⟨1549364, by rfl⟩ : syracuseStep 2065819 = 3098729) B3098729
theorem B2981509 : Blo 2065435 2981509 := bbase (se 4 (by rfl) ⟨279516, by rfl⟩ : syracuseStep 2981509 = 559033) (by norm_num)
theorem B15901381 : Blo 2065435 15901381 := bstep (se 4 (by rfl) ⟨1490754, by rfl⟩ : syracuseStep 15901381 = 2981509) B2981509
theorem B21201841 : Blo 2065435 21201841 := bstep (se 2 (by rfl) ⟨7950690, by rfl⟩ : syracuseStep 21201841 = 15901381) B15901381
theorem B28269121 : Blo 2065435 28269121 := bstep (se 2 (by rfl) ⟨10600920, by rfl⟩ : syracuseStep 28269121 = 21201841) B21201841
theorem B37692161 : Blo 2065435 37692161 := bstep (se 2 (by rfl) ⟨14134560, by rfl⟩ : syracuseStep 37692161 = 28269121) B28269121
theorem B25128107 : Blo 2065435 25128107 := bstep (se 1 (by rfl) ⟨18846080, by rfl⟩ : syracuseStep 25128107 = 37692161) B37692161
theorem B16752071 : Blo 2065435 16752071 := bstep (se 1 (by rfl) ⟨12564053, by rfl⟩ : syracuseStep 16752071 = 25128107) B25128107
theorem B11168047 : Blo 2065435 11168047 := bstep (se 1 (by rfl) ⟨8376035, by rfl⟩ : syracuseStep 11168047 = 16752071) B16752071
theorem B14890729 : Blo 2065435 14890729 := bstep (se 2 (by rfl) ⟨5584023, by rfl⟩ : syracuseStep 14890729 = 11168047) B11168047
theorem B19854305 : Blo 2065435 19854305 := bstep (se 2 (by rfl) ⟨7445364, by rfl⟩ : syracuseStep 19854305 = 14890729) B14890729
theorem B13236203 : Blo 2065435 13236203 := bstep (se 1 (by rfl) ⟨9927152, by rfl⟩ : syracuseStep 13236203 = 19854305) B19854305
theorem B8824135 : Blo 2065435 8824135 := bstep (se 1 (by rfl) ⟨6618101, by rfl⟩ : syracuseStep 8824135 = 13236203) B13236203
theorem B11765513 : Blo 2065435 11765513 := bstep (se 2 (by rfl) ⟨4412067, by rfl⟩ : syracuseStep 11765513 = 8824135) B8824135
theorem B7843675 : Blo 2065435 7843675 := bstep (se 1 (by rfl) ⟨5882756, by rfl⟩ : syracuseStep 7843675 = 11765513) B11765513
theorem B10458233 : Blo 2065435 10458233 := bstep (se 2 (by rfl) ⟨3921837, by rfl⟩ : syracuseStep 10458233 = 7843675) B7843675
theorem B6972155 : Blo 2065435 6972155 := bstep (se 1 (by rfl) ⟨5229116, by rfl⟩ : syracuseStep 6972155 = 10458233) B10458233
theorem B4648103 : Blo 2065435 4648103 := bstep (se 1 (by rfl) ⟨3486077, by rfl⟩ : syracuseStep 4648103 = 6972155) B6972155
theorem B3098735 : Blo 2065435 3098735 := bstep (se 1 (by rfl) ⟨2324051, by rfl⟩ : syracuseStep 3098735 = 4648103) B4648103
theorem B2065823 : Blo 2065435 2065823 := bstep (se 1 (by rfl) ⟨1549367, by rfl⟩ : syracuseStep 2065823 = 3098735) B3098735
theorem B3098741 : Blo 2065435 3098741 := bbase (se 5 (by rfl) ⟨145253, by rfl⟩ : syracuseStep 3098741 = 290507) (by norm_num)
theorem B2065827 : Blo 2065435 2065827 := bstep (se 1 (by rfl) ⟨1549370, by rfl⟩ : syracuseStep 2065827 = 3098741) B3098741
theorem B3921853 : Blo 2065435 3921853 := bbase (se 3 (by rfl) ⟨735347, by rfl⟩ : syracuseStep 3921853 = 1470695) (by norm_num)
theorem B5229137 : Blo 2065435 5229137 := bstep (se 2 (by rfl) ⟨1960926, by rfl⟩ : syracuseStep 5229137 = 3921853) B3921853
theorem B3486091 : Blo 2065435 3486091 := bstep (se 1 (by rfl) ⟨2614568, by rfl⟩ : syracuseStep 3486091 = 5229137) B5229137
theorem B4648121 : Blo 2065435 4648121 := bstep (se 2 (by rfl) ⟨1743045, by rfl⟩ : syracuseStep 4648121 = 3486091) B3486091
theorem B3098747 : Blo 2065435 3098747 := bstep (se 1 (by rfl) ⟨2324060, by rfl⟩ : syracuseStep 3098747 = 4648121) B4648121
theorem B2065831 : Blo 2065435 2065831 := bstep (se 1 (by rfl) ⟨1549373, by rfl⟩ : syracuseStep 2065831 = 3098747) B3098747
theorem B2324065 : Blo 2065435 2324065 := bbase (se 2 (by rfl) ⟨871524, by rfl⟩ : syracuseStep 2324065 = 1743049) (by norm_num)
theorem B3098753 : Blo 2065435 3098753 := bstep (se 2 (by rfl) ⟨1162032, by rfl⟩ : syracuseStep 3098753 = 2324065) B2324065
theorem B2065835 : Blo 2065435 2065835 := bstep (se 1 (by rfl) ⟨1549376, by rfl⟩ : syracuseStep 2065835 = 3098753) B3098753
theorem B5229157 : Blo 2065435 5229157 := bbase (se 4 (by rfl) ⟨490233, by rfl⟩ : syracuseStep 5229157 = 980467) (by norm_num)
theorem B6972209 : Blo 2065435 6972209 := bstep (se 2 (by rfl) ⟨2614578, by rfl⟩ : syracuseStep 6972209 = 5229157) B5229157
theorem B4648139 : Blo 2065435 4648139 := bstep (se 1 (by rfl) ⟨3486104, by rfl⟩ : syracuseStep 4648139 = 6972209) B6972209
theorem B3098759 : Blo 2065435 3098759 := bstep (se 1 (by rfl) ⟨2324069, by rfl⟩ : syracuseStep 3098759 = 4648139) B4648139
theorem B2065839 : Blo 2065435 2065839 := bstep (se 1 (by rfl) ⟨1549379, by rfl⟩ : syracuseStep 2065839 = 3098759) B3098759
theorem B3098765 : Blo 2065435 3098765 := bbase (se 3 (by rfl) ⟨581018, by rfl⟩ : syracuseStep 3098765 = 1162037) (by norm_num)
theorem B2065843 : Blo 2065435 2065843 := bstep (se 1 (by rfl) ⟨1549382, by rfl⟩ : syracuseStep 2065843 = 3098765) B3098765
theorem B4648157 : Blo 2065435 4648157 := bbase (se 3 (by rfl) ⟨871529, by rfl⟩ : syracuseStep 4648157 = 1743059) (by norm_num)
theorem B3098771 : Blo 2065435 3098771 := bstep (se 1 (by rfl) ⟨2324078, by rfl⟩ : syracuseStep 3098771 = 4648157) B4648157
theorem B2065847 : Blo 2065435 2065847 := bstep (se 1 (by rfl) ⟨1549385, by rfl⟩ : syracuseStep 2065847 = 3098771) B3098771
theorem B3486125 : Blo 2065435 3486125 := bbase (se 3 (by rfl) ⟨653648, by rfl⟩ : syracuseStep 3486125 = 1307297) (by norm_num)
theorem B2324083 : Blo 2065435 2324083 := bstep (se 1 (by rfl) ⟨1743062, by rfl⟩ : syracuseStep 2324083 = 3486125) B3486125
theorem B3098777 : Blo 2065435 3098777 := bstep (se 2 (by rfl) ⟨1162041, by rfl⟩ : syracuseStep 3098777 = 2324083) B2324083
theorem B2065851 : Blo 2065435 2065851 := bstep (se 1 (by rfl) ⟨1549388, by rfl⟩ : syracuseStep 2065851 = 3098777) B3098777
theorem B5372861 : Blo 2065435 5372861 := bbase (se 3 (by rfl) ⟨1007411, by rfl⟩ : syracuseStep 5372861 = 2014823) (by norm_num)
theorem B57310517 : Blo 2065435 57310517 := bstep (se 5 (by rfl) ⟨2686430, by rfl⟩ : syracuseStep 57310517 = 5372861) B5372861
theorem B38207011 : Blo 2065435 38207011 := bstep (se 1 (by rfl) ⟨28655258, by rfl⟩ : syracuseStep 38207011 = 57310517) B57310517
theorem B50942681 : Blo 2065435 50942681 := bstep (se 2 (by rfl) ⟨19103505, by rfl⟩ : syracuseStep 50942681 = 38207011) B38207011
theorem B33961787 : Blo 2065435 33961787 := bstep (se 1 (by rfl) ⟨25471340, by rfl⟩ : syracuseStep 33961787 = 50942681) B50942681
theorem B22641191 : Blo 2065435 22641191 := bstep (se 1 (by rfl) ⟨16980893, by rfl⟩ : syracuseStep 22641191 = 33961787) B33961787
theorem B15094127 : Blo 2065435 15094127 := bstep (se 1 (by rfl) ⟨11320595, by rfl⟩ : syracuseStep 15094127 = 22641191) B22641191
theorem B10062751 : Blo 2065435 10062751 := bstep (se 1 (by rfl) ⟨7547063, by rfl⟩ : syracuseStep 10062751 = 15094127) B15094127
theorem B13417001 : Blo 2065435 13417001 := bstep (se 2 (by rfl) ⟨5031375, by rfl⟩ : syracuseStep 13417001 = 10062751) B10062751
theorem B8944667 : Blo 2065435 8944667 := bstep (se 1 (by rfl) ⟨6708500, by rfl⟩ : syracuseStep 8944667 = 13417001) B13417001
theorem B5963111 : Blo 2065435 5963111 := bstep (se 1 (by rfl) ⟨4472333, by rfl⟩ : syracuseStep 5963111 = 8944667) B8944667
theorem B3975407 : Blo 2065435 3975407 := bstep (se 1 (by rfl) ⟨2981555, by rfl⟩ : syracuseStep 3975407 = 5963111) B5963111
theorem B2650271 : Blo 2065435 2650271 := bstep (se 1 (by rfl) ⟨1987703, by rfl⟩ : syracuseStep 2650271 = 3975407) B3975407
theorem B7067389 : Blo 2065435 7067389 := bstep (se 3 (by rfl) ⟨1325135, by rfl⟩ : syracuseStep 7067389 = 2650271) B2650271
theorem B9423185 : Blo 2065435 9423185 := bstep (se 2 (by rfl) ⟨3533694, by rfl⟩ : syracuseStep 9423185 = 7067389) B7067389
theorem B100513973 : Blo 2065435 100513973 := bstep (se 5 (by rfl) ⟨4711592, by rfl⟩ : syracuseStep 100513973 = 9423185) B9423185
theorem B67009315 : Blo 2065435 67009315 := bstep (se 1 (by rfl) ⟨50256986, by rfl⟩ : syracuseStep 67009315 = 100513973) B100513973
theorem B89345753 : Blo 2065435 89345753 := bstep (se 2 (by rfl) ⟨33504657, by rfl⟩ : syracuseStep 89345753 = 67009315) B67009315
theorem B59563835 : Blo 2065435 59563835 := bstep (se 1 (by rfl) ⟨44672876, by rfl⟩ : syracuseStep 59563835 = 89345753) B89345753
theorem B39709223 : Blo 2065435 39709223 := bstep (se 1 (by rfl) ⟨29781917, by rfl⟩ : syracuseStep 39709223 = 59563835) B59563835
theorem B26472815 : Blo 2065435 26472815 := bstep (se 1 (by rfl) ⟨19854611, by rfl⟩ : syracuseStep 26472815 = 39709223) B39709223
theorem B17648543 : Blo 2065435 17648543 := bstep (se 1 (by rfl) ⟨13236407, by rfl⟩ : syracuseStep 17648543 = 26472815) B26472815
theorem B11765695 : Blo 2065435 11765695 := bstep (se 1 (by rfl) ⟨8824271, by rfl⟩ : syracuseStep 11765695 = 17648543) B17648543
theorem B15687593 : Blo 2065435 15687593 := bstep (se 2 (by rfl) ⟨5882847, by rfl⟩ : syracuseStep 15687593 = 11765695) B11765695
theorem B10458395 : Blo 2065435 10458395 := bstep (se 1 (by rfl) ⟨7843796, by rfl⟩ : syracuseStep 10458395 = 15687593) B15687593
theorem B6972263 : Blo 2065435 6972263 := bstep (se 1 (by rfl) ⟨5229197, by rfl⟩ : syracuseStep 6972263 = 10458395) B10458395
theorem B4648175 : Blo 2065435 4648175 := bstep (se 1 (by rfl) ⟨3486131, by rfl⟩ : syracuseStep 4648175 = 6972263) B6972263
theorem B3098783 : Blo 2065435 3098783 := bstep (se 1 (by rfl) ⟨2324087, by rfl⟩ : syracuseStep 3098783 = 4648175) B4648175
theorem B2065855 : Blo 2065435 2065855 := bstep (se 1 (by rfl) ⟨1549391, by rfl⟩ : syracuseStep 2065855 = 3098783) B3098783
theorem B3098789 : Blo 2065435 3098789 := bbase (se 4 (by rfl) ⟨290511, by rfl⟩ : syracuseStep 3098789 = 581023) (by norm_num)
theorem B2065859 : Blo 2065435 2065859 := bstep (se 1 (by rfl) ⟨1549394, by rfl⟩ : syracuseStep 2065859 = 3098789) B3098789
theorem B2614609 : Blo 2065435 2614609 := bbase (se 2 (by rfl) ⟨980478, by rfl⟩ : syracuseStep 2614609 = 1960957) (by norm_num)
theorem B3486145 : Blo 2065435 3486145 := bstep (se 2 (by rfl) ⟨1307304, by rfl⟩ : syracuseStep 3486145 = 2614609) B2614609
theorem B4648193 : Blo 2065435 4648193 := bstep (se 2 (by rfl) ⟨1743072, by rfl⟩ : syracuseStep 4648193 = 3486145) B3486145
theorem B3098795 : Blo 2065435 3098795 := bstep (se 1 (by rfl) ⟨2324096, by rfl⟩ : syracuseStep 3098795 = 4648193) B4648193
theorem B2065863 : Blo 2065435 2065863 := bstep (se 1 (by rfl) ⟨1549397, by rfl⟩ : syracuseStep 2065863 = 3098795) B3098795
theorem B2324101 : Blo 2065435 2324101 := bbase (se 4 (by rfl) ⟨217884, by rfl⟩ : syracuseStep 2324101 = 435769) (by norm_num)
theorem B3098801 : Blo 2065435 3098801 := bstep (se 2 (by rfl) ⟨1162050, by rfl⟩ : syracuseStep 3098801 = 2324101) B2324101
theorem B2065867 : Blo 2065435 2065867 := bstep (se 1 (by rfl) ⟨1549400, by rfl⟩ : syracuseStep 2065867 = 3098801) B3098801
theorem B4963693 : Blo 2065435 4963693 := bbase (se 3 (by rfl) ⟨930692, by rfl⟩ : syracuseStep 4963693 = 1861385) (by norm_num)
theorem B6618257 : Blo 2065435 6618257 := bstep (se 2 (by rfl) ⟨2481846, by rfl⟩ : syracuseStep 6618257 = 4963693) B4963693
theorem B4412171 : Blo 2065435 4412171 := bstep (se 1 (by rfl) ⟨3309128, by rfl⟩ : syracuseStep 4412171 = 6618257) B6618257
theorem B2941447 : Blo 2065435 2941447 := bstep (se 1 (by rfl) ⟨2206085, by rfl⟩ : syracuseStep 2941447 = 4412171) B4412171
theorem B3921929 : Blo 2065435 3921929 := bstep (se 2 (by rfl) ⟨1470723, by rfl⟩ : syracuseStep 3921929 = 2941447) B2941447
theorem B2614619 : Blo 2065435 2614619 := bstep (se 1 (by rfl) ⟨1960964, by rfl⟩ : syracuseStep 2614619 = 3921929) B3921929
theorem B6972317 : Blo 2065435 6972317 := bstep (se 3 (by rfl) ⟨1307309, by rfl⟩ : syracuseStep 6972317 = 2614619) B2614619
theorem B4648211 : Blo 2065435 4648211 := bstep (se 1 (by rfl) ⟨3486158, by rfl⟩ : syracuseStep 4648211 = 6972317) B6972317
theorem B3098807 : Blo 2065435 3098807 := bstep (se 1 (by rfl) ⟨2324105, by rfl⟩ : syracuseStep 3098807 = 4648211) B4648211
theorem B2065871 : Blo 2065435 2065871 := bstep (se 1 (by rfl) ⟨1549403, by rfl⟩ : syracuseStep 2065871 = 3098807) B3098807
theorem B3098813 : Blo 2065435 3098813 := bbase (se 3 (by rfl) ⟨581027, by rfl⟩ : syracuseStep 3098813 = 1162055) (by norm_num)
theorem B2065875 : Blo 2065435 2065875 := bstep (se 1 (by rfl) ⟨1549406, by rfl⟩ : syracuseStep 2065875 = 3098813) B3098813
theorem B4648229 : Blo 2065435 4648229 := bbase (se 4 (by rfl) ⟨435771, by rfl⟩ : syracuseStep 4648229 = 871543) (by norm_num)
theorem B3098819 : Blo 2065435 3098819 := bstep (se 1 (by rfl) ⟨2324114, by rfl⟩ : syracuseStep 3098819 = 4648229) B4648229
theorem B2065879 : Blo 2065435 2065879 := bstep (se 1 (by rfl) ⟨1549409, by rfl⟩ : syracuseStep 2065879 = 3098819) B3098819
theorem B5229269 : Blo 2065435 5229269 := bbase (se 7 (by rfl) ⟨61280, by rfl⟩ : syracuseStep 5229269 = 122561) (by norm_num)
theorem B3486179 : Blo 2065435 3486179 := bstep (se 1 (by rfl) ⟨2614634, by rfl⟩ : syracuseStep 3486179 = 5229269) B5229269
theorem B2324119 : Blo 2065435 2324119 := bstep (se 1 (by rfl) ⟨1743089, by rfl⟩ : syracuseStep 2324119 = 3486179) B3486179
theorem B3098825 : Blo 2065435 3098825 := bstep (se 2 (by rfl) ⟨1162059, by rfl⟩ : syracuseStep 3098825 = 2324119) B2324119
theorem B2065883 : Blo 2065435 2065883 := bstep (se 1 (by rfl) ⟨1549412, by rfl⟩ : syracuseStep 2065883 = 3098825) B3098825
theorem B9927461 : Blo 2065435 9927461 := bbase (se 4 (by rfl) ⟨930699, by rfl⟩ : syracuseStep 9927461 = 1861399) (by norm_num)
theorem B6618307 : Blo 2065435 6618307 := bstep (se 1 (by rfl) ⟨4963730, by rfl⟩ : syracuseStep 6618307 = 9927461) B9927461
theorem B8824409 : Blo 2065435 8824409 := bstep (se 2 (by rfl) ⟨3309153, by rfl⟩ : syracuseStep 8824409 = 6618307) B6618307
theorem B5882939 : Blo 2065435 5882939 := bstep (se 1 (by rfl) ⟨4412204, by rfl⟩ : syracuseStep 5882939 = 8824409) B8824409
theorem B3921959 : Blo 2065435 3921959 := bstep (se 1 (by rfl) ⟨2941469, by rfl⟩ : syracuseStep 3921959 = 5882939) B5882939
theorem B10458557 : Blo 2065435 10458557 := bstep (se 3 (by rfl) ⟨1960979, by rfl⟩ : syracuseStep 10458557 = 3921959) B3921959
theorem B6972371 : Blo 2065435 6972371 := bstep (se 1 (by rfl) ⟨5229278, by rfl⟩ : syracuseStep 6972371 = 10458557) B10458557
theorem B4648247 : Blo 2065435 4648247 := bstep (se 1 (by rfl) ⟨3486185, by rfl⟩ : syracuseStep 4648247 = 6972371) B6972371
theorem B3098831 : Blo 2065435 3098831 := bstep (se 1 (by rfl) ⟨2324123, by rfl⟩ : syracuseStep 3098831 = 4648247) B4648247
theorem B2065887 : Blo 2065435 2065887 := bstep (se 1 (by rfl) ⟨1549415, by rfl⟩ : syracuseStep 2065887 = 3098831) B3098831
theorem B3098837 : Blo 2065435 3098837 := bbase (se 7 (by rfl) ⟨36314, by rfl⟩ : syracuseStep 3098837 = 72629) (by norm_num)
theorem B2065891 : Blo 2065435 2065891 := bstep (se 1 (by rfl) ⟨1549418, by rfl⟩ : syracuseStep 2065891 = 3098837) B3098837
theorem B3533765 : Blo 2065435 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B9423373 : Blo 2065435 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B12564497 : Blo 2065435 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B8376331 : Blo 2065435 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B11168441 : Blo 2065435 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B7445627 : Blo 2065435 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B4963751 : Blo 2065435 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B3309167 : Blo 2065435 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B2206111 : Blo 2065435 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B2941481 : Blo 2065435 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B7843949 : Blo 2065435 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B5229299 : Blo 2065435 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B3486199 : Blo 2065435 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B4648265 : Blo 2065435 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B3098843 : Blo 2065435 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B2065895 : Blo 2065435 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B2324137 : Blo 2065435 2324137 := bbase (se 2 (by rfl) ⟨871551, by rfl⟩ : syracuseStep 2324137 = 1743103) (by norm_num)
theorem B3098849 : Blo 2065435 3098849 := bstep (se 2 (by rfl) ⟨1162068, by rfl⟩ : syracuseStep 3098849 = 2324137) B2324137
theorem B2065899 : Blo 2065435 2065899 := bstep (se 1 (by rfl) ⟨1549424, by rfl⟩ : syracuseStep 2065899 = 3098849) B3098849
theorem B4188181 : Blo 2065435 4188181 := bbase (se 6 (by rfl) ⟨98160, by rfl⟩ : syracuseStep 4188181 = 196321) (by norm_num)
theorem B5584241 : Blo 2065435 5584241 := bstep (se 2 (by rfl) ⟨2094090, by rfl⟩ : syracuseStep 5584241 = 4188181) B4188181
theorem B3722827 : Blo 2065435 3722827 := bstep (se 1 (by rfl) ⟨2792120, by rfl⟩ : syracuseStep 3722827 = 5584241) B5584241
theorem B4963769 : Blo 2065435 4963769 := bstep (se 2 (by rfl) ⟨1861413, by rfl⟩ : syracuseStep 4963769 = 3722827) B3722827
theorem B3309179 : Blo 2065435 3309179 := bstep (se 1 (by rfl) ⟨2481884, by rfl⟩ : syracuseStep 3309179 = 4963769) B4963769
theorem B8824477 : Blo 2065435 8824477 := bstep (se 3 (by rfl) ⟨1654589, by rfl⟩ : syracuseStep 8824477 = 3309179) B3309179
theorem B11765969 : Blo 2065435 11765969 := bstep (se 2 (by rfl) ⟨4412238, by rfl⟩ : syracuseStep 11765969 = 8824477) B8824477
theorem B7843979 : Blo 2065435 7843979 := bstep (se 1 (by rfl) ⟨5882984, by rfl⟩ : syracuseStep 7843979 = 11765969) B11765969
theorem B5229319 : Blo 2065435 5229319 := bstep (se 1 (by rfl) ⟨3921989, by rfl⟩ : syracuseStep 5229319 = 7843979) B7843979
theorem B6972425 : Blo 2065435 6972425 := bstep (se 2 (by rfl) ⟨2614659, by rfl⟩ : syracuseStep 6972425 = 5229319) B5229319
theorem B4648283 : Blo 2065435 4648283 := bstep (se 1 (by rfl) ⟨3486212, by rfl⟩ : syracuseStep 4648283 = 6972425) B6972425
theorem B3098855 : Blo 2065435 3098855 := bstep (se 1 (by rfl) ⟨2324141, by rfl⟩ : syracuseStep 3098855 = 4648283) B4648283
theorem B2065903 : Blo 2065435 2065903 := bstep (se 1 (by rfl) ⟨1549427, by rfl⟩ : syracuseStep 2065903 = 3098855) B3098855
theorem B3098861 : Blo 2065435 3098861 := bbase (se 3 (by rfl) ⟨581036, by rfl⟩ : syracuseStep 3098861 = 1162073) (by norm_num)
theorem B2065907 : Blo 2065435 2065907 := bstep (se 1 (by rfl) ⟨1549430, by rfl⟩ : syracuseStep 2065907 = 3098861) B3098861
theorem B4648301 : Blo 2065435 4648301 := bbase (se 3 (by rfl) ⟨871556, by rfl⟩ : syracuseStep 4648301 = 1743113) (by norm_num)
theorem B3098867 : Blo 2065435 3098867 := bstep (se 1 (by rfl) ⟨2324150, by rfl⟩ : syracuseStep 3098867 = 4648301) B4648301
theorem B2065911 : Blo 2065435 2065911 := bstep (se 1 (by rfl) ⟨1549433, by rfl⟩ : syracuseStep 2065911 = 3098867) B3098867
theorem B3922013 : Blo 2065435 3922013 := bbase (se 3 (by rfl) ⟨735377, by rfl⟩ : syracuseStep 3922013 = 1470755) (by norm_num)
theorem B2614675 : Blo 2065435 2614675 := bstep (se 1 (by rfl) ⟨1961006, by rfl⟩ : syracuseStep 2614675 = 3922013) B3922013
theorem B3486233 : Blo 2065435 3486233 := bstep (se 2 (by rfl) ⟨1307337, by rfl⟩ : syracuseStep 3486233 = 2614675) B2614675
theorem B2324155 : Blo 2065435 2324155 := bstep (se 1 (by rfl) ⟨1743116, by rfl⟩ : syracuseStep 2324155 = 3486233) B3486233
theorem B3098873 : Blo 2065435 3098873 := bstep (se 2 (by rfl) ⟨1162077, by rfl⟩ : syracuseStep 3098873 = 2324155) B2324155
theorem B2065915 : Blo 2065435 2065915 := bstep (se 1 (by rfl) ⟨1549436, by rfl⟩ : syracuseStep 2065915 = 3098873) B3098873
theorem B7951061 : Blo 2065435 7951061 := bbase (se 7 (by rfl) ⟨93176, by rfl⟩ : syracuseStep 7951061 = 186353) (by norm_num)
theorem B21202829 : Blo 2065435 21202829 := bstep (se 3 (by rfl) ⟨3975530, by rfl⟩ : syracuseStep 21202829 = 7951061) B7951061
theorem B14135219 : Blo 2065435 14135219 := bstep (se 1 (by rfl) ⟨10601414, by rfl⟩ : syracuseStep 14135219 = 21202829) B21202829
theorem B9423479 : Blo 2065435 9423479 := bstep (se 1 (by rfl) ⟨7067609, by rfl⟩ : syracuseStep 9423479 = 14135219) B14135219
theorem B6282319 : Blo 2065435 6282319 := bstep (se 1 (by rfl) ⟨4711739, by rfl⟩ : syracuseStep 6282319 = 9423479) B9423479
theorem B8376425 : Blo 2065435 8376425 := bstep (se 2 (by rfl) ⟨3141159, by rfl⟩ : syracuseStep 8376425 = 6282319) B6282319
theorem B5584283 : Blo 2065435 5584283 := bstep (se 1 (by rfl) ⟨4188212, by rfl⟩ : syracuseStep 5584283 = 8376425) B8376425
theorem B3722855 : Blo 2065435 3722855 := bstep (se 1 (by rfl) ⟨2792141, by rfl⟩ : syracuseStep 3722855 = 5584283) B5584283
theorem B9927613 : Blo 2065435 9927613 := bstep (se 3 (by rfl) ⟨1861427, by rfl⟩ : syracuseStep 9927613 = 3722855) B3722855
theorem B52947269 : Blo 2065435 52947269 := bstep (se 4 (by rfl) ⟨4963806, by rfl⟩ : syracuseStep 52947269 = 9927613) B9927613
theorem B35298179 : Blo 2065435 35298179 := bstep (se 1 (by rfl) ⟨26473634, by rfl⟩ : syracuseStep 35298179 = 52947269) B52947269
theorem B23532119 : Blo 2065435 23532119 := bstep (se 1 (by rfl) ⟨17649089, by rfl⟩ : syracuseStep 23532119 = 35298179) B35298179
theorem B15688079 : Blo 2065435 15688079 := bstep (se 1 (by rfl) ⟨11766059, by rfl⟩ : syracuseStep 15688079 = 23532119) B23532119
theorem B10458719 : Blo 2065435 10458719 := bstep (se 1 (by rfl) ⟨7844039, by rfl⟩ : syracuseStep 10458719 = 15688079) B15688079
theorem B6972479 : Blo 2065435 6972479 := bstep (se 1 (by rfl) ⟨5229359, by rfl⟩ : syracuseStep 6972479 = 10458719) B10458719
theorem B4648319 : Blo 2065435 4648319 := bstep (se 1 (by rfl) ⟨3486239, by rfl⟩ : syracuseStep 4648319 = 6972479) B6972479
theorem B3098879 : Blo 2065435 3098879 := bstep (se 1 (by rfl) ⟨2324159, by rfl⟩ : syracuseStep 3098879 = 4648319) B4648319
theorem B2065919 : Blo 2065435 2065919 := bstep (se 1 (by rfl) ⟨1549439, by rfl⟩ : syracuseStep 2065919 = 3098879) B3098879
theorem B3098885 : Blo 2065435 3098885 := bbase (se 4 (by rfl) ⟨290520, by rfl⟩ : syracuseStep 3098885 = 581041) (by norm_num)
theorem B2065923 : Blo 2065435 2065923 := bstep (se 1 (by rfl) ⟨1549442, by rfl⟩ : syracuseStep 2065923 = 3098885) B3098885
theorem B3486253 : Blo 2065435 3486253 := bbase (se 3 (by rfl) ⟨653672, by rfl⟩ : syracuseStep 3486253 = 1307345) (by norm_num)
theorem B4648337 : Blo 2065435 4648337 := bstep (se 2 (by rfl) ⟨1743126, by rfl⟩ : syracuseStep 4648337 = 3486253) B3486253
theorem B3098891 : Blo 2065435 3098891 := bstep (se 1 (by rfl) ⟨2324168, by rfl⟩ : syracuseStep 3098891 = 4648337) B4648337
theorem B2065927 : Blo 2065435 2065927 := bstep (se 1 (by rfl) ⟨1549445, by rfl⟩ : syracuseStep 2065927 = 3098891) B3098891
theorem B2324173 : Blo 2065435 2324173 := bbase (se 3 (by rfl) ⟨435782, by rfl⟩ : syracuseStep 2324173 = 871565) (by norm_num)
theorem B3098897 : Blo 2065435 3098897 := bstep (se 2 (by rfl) ⟨1162086, by rfl⟩ : syracuseStep 3098897 = 2324173) B2324173
theorem B2065931 : Blo 2065435 2065931 := bstep (se 1 (by rfl) ⟨1549448, by rfl⟩ : syracuseStep 2065931 = 3098897) B3098897
theorem B6972533 : Blo 2065435 6972533 := bbase (se 5 (by rfl) ⟨326837, by rfl⟩ : syracuseStep 6972533 = 653675) (by norm_num)
theorem B4648355 : Blo 2065435 4648355 := bstep (se 1 (by rfl) ⟨3486266, by rfl⟩ : syracuseStep 4648355 = 6972533) B6972533
theorem B3098903 : Blo 2065435 3098903 := bstep (se 1 (by rfl) ⟨2324177, by rfl⟩ : syracuseStep 3098903 = 4648355) B4648355
theorem B2065935 : Blo 2065435 2065935 := bstep (se 1 (by rfl) ⟨1549451, by rfl⟩ : syracuseStep 2065935 = 3098903) B3098903
theorem B3098909 : Blo 2065435 3098909 := bbase (se 3 (by rfl) ⟨581045, by rfl⟩ : syracuseStep 3098909 = 1162091) (by norm_num)
theorem B2065939 : Blo 2065435 2065939 := bstep (se 1 (by rfl) ⟨1549454, by rfl⟩ : syracuseStep 2065939 = 3098909) B3098909
theorem B4648373 : Blo 2065435 4648373 := bbase (se 5 (by rfl) ⟨217892, by rfl⟩ : syracuseStep 4648373 = 435785) (by norm_num)
theorem B3098915 : Blo 2065435 3098915 := bstep (se 1 (by rfl) ⟨2324186, by rfl⟩ : syracuseStep 3098915 = 4648373) B4648373
theorem B2065943 : Blo 2065435 2065943 := bstep (se 1 (by rfl) ⟨1549457, by rfl⟩ : syracuseStep 2065943 = 3098915) B3098915
theorem B4412333 : Blo 2065435 4412333 := bbase (se 3 (by rfl) ⟨827312, by rfl⟩ : syracuseStep 4412333 = 1654625) (by norm_num)
theorem B11766221 : Blo 2065435 11766221 := bstep (se 3 (by rfl) ⟨2206166, by rfl⟩ : syracuseStep 11766221 = 4412333) B4412333
theorem B7844147 : Blo 2065435 7844147 := bstep (se 1 (by rfl) ⟨5883110, by rfl⟩ : syracuseStep 7844147 = 11766221) B11766221
theorem B5229431 : Blo 2065435 5229431 := bstep (se 1 (by rfl) ⟨3922073, by rfl⟩ : syracuseStep 5229431 = 7844147) B7844147
theorem B3486287 : Blo 2065435 3486287 := bstep (se 1 (by rfl) ⟨2614715, by rfl⟩ : syracuseStep 3486287 = 5229431) B5229431
theorem B2324191 : Blo 2065435 2324191 := bstep (se 1 (by rfl) ⟨1743143, by rfl⟩ : syracuseStep 2324191 = 3486287) B3486287
theorem B3098921 : Blo 2065435 3098921 := bstep (se 2 (by rfl) ⟨1162095, by rfl⟩ : syracuseStep 3098921 = 2324191) B2324191
theorem B2065947 : Blo 2065435 2065947 := bstep (se 1 (by rfl) ⟨1549460, by rfl⟩ : syracuseStep 2065947 = 3098921) B3098921
theorem B4412341 : Blo 2065435 4412341 := bbase (se 5 (by rfl) ⟨206828, by rfl⟩ : syracuseStep 4412341 = 413657) (by norm_num)
theorem B5883121 : Blo 2065435 5883121 := bstep (se 2 (by rfl) ⟨2206170, by rfl⟩ : syracuseStep 5883121 = 4412341) B4412341
theorem B7844161 : Blo 2065435 7844161 := bstep (se 2 (by rfl) ⟨2941560, by rfl⟩ : syracuseStep 7844161 = 5883121) B5883121
theorem B10458881 : Blo 2065435 10458881 := bstep (se 2 (by rfl) ⟨3922080, by rfl⟩ : syracuseStep 10458881 = 7844161) B7844161
theorem B6972587 : Blo 2065435 6972587 := bstep (se 1 (by rfl) ⟨5229440, by rfl⟩ : syracuseStep 6972587 = 10458881) B10458881
theorem B4648391 : Blo 2065435 4648391 := bstep (se 1 (by rfl) ⟨3486293, by rfl⟩ : syracuseStep 4648391 = 6972587) B6972587
theorem B3098927 : Blo 2065435 3098927 := bstep (se 1 (by rfl) ⟨2324195, by rfl⟩ : syracuseStep 3098927 = 4648391) B4648391
theorem B2065951 : Blo 2065435 2065951 := bstep (se 1 (by rfl) ⟨1549463, by rfl⟩ : syracuseStep 2065951 = 3098927) B3098927
theorem B3098933 : Blo 2065435 3098933 := bbase (se 5 (by rfl) ⟨145262, by rfl⟩ : syracuseStep 3098933 = 290525) (by norm_num)
theorem B2065955 : Blo 2065435 2065955 := bstep (se 1 (by rfl) ⟨1549466, by rfl⟩ : syracuseStep 2065955 = 3098933) B3098933
theorem B5229461 : Blo 2065435 5229461 := bbase (se 6 (by rfl) ⟨122565, by rfl⟩ : syracuseStep 5229461 = 245131) (by norm_num)
theorem B3486307 : Blo 2065435 3486307 := bstep (se 1 (by rfl) ⟨2614730, by rfl⟩ : syracuseStep 3486307 = 5229461) B5229461
theorem B4648409 : Blo 2065435 4648409 := bstep (se 2 (by rfl) ⟨1743153, by rfl⟩ : syracuseStep 4648409 = 3486307) B3486307
theorem B3098939 : Blo 2065435 3098939 := bstep (se 1 (by rfl) ⟨2324204, by rfl⟩ : syracuseStep 3098939 = 4648409) B4648409
theorem B2065959 : Blo 2065435 2065959 := bstep (se 1 (by rfl) ⟨1549469, by rfl⟩ : syracuseStep 2065959 = 3098939) B3098939
theorem B2324209 : Blo 2065435 2324209 := bbase (se 2 (by rfl) ⟨871578, by rfl⟩ : syracuseStep 2324209 = 1743157) (by norm_num)
theorem B3098945 : Blo 2065435 3098945 := bstep (se 2 (by rfl) ⟨1162104, by rfl⟩ : syracuseStep 3098945 = 2324209) B2324209
theorem B2065963 : Blo 2065435 2065963 := bstep (se 1 (by rfl) ⟨1549472, by rfl⟩ : syracuseStep 2065963 = 3098945) B3098945
theorem B2355925 : Blo 2065435 2355925 := bbase (se 7 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 2355925 = 55217) (by norm_num)
theorem B3141233 : Blo 2065435 3141233 := bstep (se 2 (by rfl) ⟨1177962, by rfl⟩ : syracuseStep 3141233 = 2355925) B2355925
theorem B2094155 : Blo 2065435 2094155 := bstep (se 1 (by rfl) ⟨1570616, by rfl⟩ : syracuseStep 2094155 = 3141233) B3141233
theorem B22337653 : Blo 2065435 22337653 := bstep (se 5 (by rfl) ⟨1047077, by rfl⟩ : syracuseStep 22337653 = 2094155) B2094155
theorem B29783537 : Blo 2065435 29783537 := bstep (se 2 (by rfl) ⟨11168826, by rfl⟩ : syracuseStep 29783537 = 22337653) B22337653
theorem B19855691 : Blo 2065435 19855691 := bstep (se 1 (by rfl) ⟨14891768, by rfl⟩ : syracuseStep 19855691 = 29783537) B29783537
theorem B13237127 : Blo 2065435 13237127 := bstep (se 1 (by rfl) ⟨9927845, by rfl⟩ : syracuseStep 13237127 = 19855691) B19855691
theorem B8824751 : Blo 2065435 8824751 := bstep (se 1 (by rfl) ⟨6618563, by rfl⟩ : syracuseStep 8824751 = 13237127) B13237127
theorem B5883167 : Blo 2065435 5883167 := bstep (se 1 (by rfl) ⟨4412375, by rfl⟩ : syracuseStep 5883167 = 8824751) B8824751
theorem B3922111 : Blo 2065435 3922111 := bstep (se 1 (by rfl) ⟨2941583, by rfl⟩ : syracuseStep 3922111 = 5883167) B5883167
theorem B5229481 : Blo 2065435 5229481 := bstep (se 2 (by rfl) ⟨1961055, by rfl⟩ : syracuseStep 5229481 = 3922111) B3922111
theorem B6972641 : Blo 2065435 6972641 := bstep (se 2 (by rfl) ⟨2614740, by rfl⟩ : syracuseStep 6972641 = 5229481) B5229481
theorem B4648427 : Blo 2065435 4648427 := bstep (se 1 (by rfl) ⟨3486320, by rfl⟩ : syracuseStep 4648427 = 6972641) B6972641
theorem B3098951 : Blo 2065435 3098951 := bstep (se 1 (by rfl) ⟨2324213, by rfl⟩ : syracuseStep 3098951 = 4648427) B4648427
theorem B2065967 : Blo 2065435 2065967 := bstep (se 1 (by rfl) ⟨1549475, by rfl⟩ : syracuseStep 2065967 = 3098951) B3098951
theorem B3098957 : Blo 2065435 3098957 := bbase (se 3 (by rfl) ⟨581054, by rfl⟩ : syracuseStep 3098957 = 1162109) (by norm_num)
theorem B2065971 : Blo 2065435 2065971 := bstep (se 1 (by rfl) ⟨1549478, by rfl⟩ : syracuseStep 2065971 = 3098957) B3098957
theorem B4648445 : Blo 2065435 4648445 := bbase (se 3 (by rfl) ⟨871583, by rfl⟩ : syracuseStep 4648445 = 1743167) (by norm_num)
theorem B3098963 : Blo 2065435 3098963 := bstep (se 1 (by rfl) ⟨2324222, by rfl⟩ : syracuseStep 3098963 = 4648445) B4648445
theorem B2065975 : Blo 2065435 2065975 := bstep (se 1 (by rfl) ⟨1549481, by rfl⟩ : syracuseStep 2065975 = 3098963) B3098963
theorem B3486341 : Blo 2065435 3486341 := bbase (se 4 (by rfl) ⟨326844, by rfl⟩ : syracuseStep 3486341 = 653689) (by norm_num)
theorem B2324227 : Blo 2065435 2324227 := bstep (se 1 (by rfl) ⟨1743170, by rfl⟩ : syracuseStep 2324227 = 3486341) B3486341
theorem B3098969 : Blo 2065435 3098969 := bstep (se 2 (by rfl) ⟨1162113, by rfl⟩ : syracuseStep 3098969 = 2324227) B2324227
theorem B2065979 : Blo 2065435 2065979 := bstep (se 1 (by rfl) ⟨1549484, by rfl⟩ : syracuseStep 2065979 = 3098969) B3098969
theorem B15688565 : Blo 2065435 15688565 := bbase (se 5 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 15688565 = 1470803) (by norm_num)
theorem B10459043 : Blo 2065435 10459043 := bstep (se 1 (by rfl) ⟨7844282, by rfl⟩ : syracuseStep 10459043 = 15688565) B15688565
theorem B6972695 : Blo 2065435 6972695 := bstep (se 1 (by rfl) ⟨5229521, by rfl⟩ : syracuseStep 6972695 = 10459043) B10459043
theorem B4648463 : Blo 2065435 4648463 := bstep (se 1 (by rfl) ⟨3486347, by rfl⟩ : syracuseStep 4648463 = 6972695) B6972695
theorem B3098975 : Blo 2065435 3098975 := bstep (se 1 (by rfl) ⟨2324231, by rfl⟩ : syracuseStep 3098975 = 4648463) B4648463
theorem B2065983 : Blo 2065435 2065983 := bstep (se 1 (by rfl) ⟨1549487, by rfl⟩ : syracuseStep 2065983 = 3098975) B3098975
theorem B3098981 : Blo 2065435 3098981 := bbase (se 4 (by rfl) ⟨290529, by rfl⟩ : syracuseStep 3098981 = 581059) (by norm_num)
theorem B2065987 : Blo 2065435 2065987 := bstep (se 1 (by rfl) ⟨1549490, by rfl⟩ : syracuseStep 2065987 = 3098981) B3098981
theorem B3922157 : Blo 2065435 3922157 := bbase (se 3 (by rfl) ⟨735404, by rfl⟩ : syracuseStep 3922157 = 1470809) (by norm_num)
theorem B2614771 : Blo 2065435 2614771 := bstep (se 1 (by rfl) ⟨1961078, by rfl⟩ : syracuseStep 2614771 = 3922157) B3922157
theorem B3486361 : Blo 2065435 3486361 := bstep (se 2 (by rfl) ⟨1307385, by rfl⟩ : syracuseStep 3486361 = 2614771) B2614771
theorem B4648481 : Blo 2065435 4648481 := bstep (se 2 (by rfl) ⟨1743180, by rfl⟩ : syracuseStep 4648481 = 3486361) B3486361
theorem B3098987 : Blo 2065435 3098987 := bstep (se 1 (by rfl) ⟨2324240, by rfl⟩ : syracuseStep 3098987 = 4648481) B4648481
theorem B2065991 : Blo 2065435 2065991 := bstep (se 1 (by rfl) ⟨1549493, by rfl⟩ : syracuseStep 2065991 = 3098987) B3098987
theorem B2324245 : Blo 2065435 2324245 := bbase (se 6 (by rfl) ⟨54474, by rfl⟩ : syracuseStep 2324245 = 108949) (by norm_num)
theorem B3098993 : Blo 2065435 3098993 := bstep (se 2 (by rfl) ⟨1162122, by rfl⟩ : syracuseStep 3098993 = 2324245) B2324245
theorem B2065995 : Blo 2065435 2065995 := bstep (se 1 (by rfl) ⟨1549496, by rfl⟩ : syracuseStep 2065995 = 3098993) B3098993
theorem B2614781 : Blo 2065435 2614781 := bbase (se 3 (by rfl) ⟨490271, by rfl⟩ : syracuseStep 2614781 = 980543) (by norm_num)
theorem B6972749 : Blo 2065435 6972749 := bstep (se 3 (by rfl) ⟨1307390, by rfl⟩ : syracuseStep 6972749 = 2614781) B2614781
theorem B4648499 : Blo 2065435 4648499 := bstep (se 1 (by rfl) ⟨3486374, by rfl⟩ : syracuseStep 4648499 = 6972749) B6972749
theorem B3098999 : Blo 2065435 3098999 := bstep (se 1 (by rfl) ⟨2324249, by rfl⟩ : syracuseStep 3098999 = 4648499) B4648499
theorem B2065999 : Blo 2065435 2065999 := bstep (se 1 (by rfl) ⟨1549499, by rfl⟩ : syracuseStep 2065999 = 3098999) B3098999
theorem B3099005 : Blo 2065435 3099005 := bbase (se 3 (by rfl) ⟨581063, by rfl⟩ : syracuseStep 3099005 = 1162127) (by norm_num)
theorem B2066003 : Blo 2065435 2066003 := bstep (se 1 (by rfl) ⟨1549502, by rfl⟩ : syracuseStep 2066003 = 3099005) B3099005
theorem B4648517 : Blo 2065435 4648517 := bbase (se 4 (by rfl) ⟨435798, by rfl⟩ : syracuseStep 4648517 = 871597) (by norm_num)
theorem B3099011 : Blo 2065435 3099011 := bstep (se 1 (by rfl) ⟨2324258, by rfl⟩ : syracuseStep 3099011 = 4648517) B4648517
theorem B2066007 : Blo 2065435 2066007 := bstep (se 1 (by rfl) ⟨1549505, by rfl⟩ : syracuseStep 2066007 = 3099011) B3099011
theorem B12565205 : Blo 2065435 12565205 := bbase (se 7 (by rfl) ⟨147248, by rfl⟩ : syracuseStep 12565205 = 294497) (by norm_num)
theorem B8376803 : Blo 2065435 8376803 := bstep (se 1 (by rfl) ⟨6282602, by rfl⟩ : syracuseStep 8376803 = 12565205) B12565205
theorem B5584535 : Blo 2065435 5584535 := bstep (se 1 (by rfl) ⟨4188401, by rfl⟩ : syracuseStep 5584535 = 8376803) B8376803
theorem B3723023 : Blo 2065435 3723023 := bstep (se 1 (by rfl) ⟨2792267, by rfl⟩ : syracuseStep 3723023 = 5584535) B5584535
theorem B2482015 : Blo 2065435 2482015 := bstep (se 1 (by rfl) ⟨1861511, by rfl⟩ : syracuseStep 2482015 = 3723023) B3723023
theorem B3309353 : Blo 2065435 3309353 := bstep (se 2 (by rfl) ⟨1241007, by rfl⟩ : syracuseStep 3309353 = 2482015) B2482015
theorem B2206235 : Blo 2065435 2206235 := bstep (se 1 (by rfl) ⟨1654676, by rfl⟩ : syracuseStep 2206235 = 3309353) B3309353
theorem B5883293 : Blo 2065435 5883293 := bstep (se 3 (by rfl) ⟨1103117, by rfl⟩ : syracuseStep 5883293 = 2206235) B2206235
theorem B3922195 : Blo 2065435 3922195 := bstep (se 1 (by rfl) ⟨2941646, by rfl⟩ : syracuseStep 3922195 = 5883293) B5883293
theorem B5229593 : Blo 2065435 5229593 := bstep (se 2 (by rfl) ⟨1961097, by rfl⟩ : syracuseStep 5229593 = 3922195) B3922195
theorem B3486395 : Blo 2065435 3486395 := bstep (se 1 (by rfl) ⟨2614796, by rfl⟩ : syracuseStep 3486395 = 5229593) B5229593
theorem B2324263 : Blo 2065435 2324263 := bstep (se 1 (by rfl) ⟨1743197, by rfl⟩ : syracuseStep 2324263 = 3486395) B3486395
theorem B3099017 : Blo 2065435 3099017 := bstep (se 2 (by rfl) ⟨1162131, by rfl⟩ : syracuseStep 3099017 = 2324263) B2324263
theorem B2066011 : Blo 2065435 2066011 := bstep (se 1 (by rfl) ⟨1549508, by rfl⟩ : syracuseStep 2066011 = 3099017) B3099017
theorem B10459205 : Blo 2065435 10459205 := bbase (se 4 (by rfl) ⟨980550, by rfl⟩ : syracuseStep 10459205 = 1961101) (by norm_num)
theorem B6972803 : Blo 2065435 6972803 := bstep (se 1 (by rfl) ⟨5229602, by rfl⟩ : syracuseStep 6972803 = 10459205) B10459205
theorem B4648535 : Blo 2065435 4648535 := bstep (se 1 (by rfl) ⟨3486401, by rfl⟩ : syracuseStep 4648535 = 6972803) B6972803
theorem B3099023 : Blo 2065435 3099023 := bstep (se 1 (by rfl) ⟨2324267, by rfl⟩ : syracuseStep 3099023 = 4648535) B4648535
theorem B2066015 : Blo 2065435 2066015 := bstep (se 1 (by rfl) ⟨1549511, by rfl⟩ : syracuseStep 2066015 = 3099023) B3099023
theorem B3099029 : Blo 2065435 3099029 := bbase (se 6 (by rfl) ⟨72633, by rfl⟩ : syracuseStep 3099029 = 145267) (by norm_num)
theorem B2066019 : Blo 2065435 2066019 := bstep (se 1 (by rfl) ⟨1549514, by rfl⟩ : syracuseStep 2066019 = 3099029) B3099029
theorem B5584565 : Blo 2065435 5584565 := bbase (se 5 (by rfl) ⟨261776, by rfl⟩ : syracuseStep 5584565 = 523553) (by norm_num)
theorem B14892173 : Blo 2065435 14892173 := bstep (se 3 (by rfl) ⟨2792282, by rfl⟩ : syracuseStep 14892173 = 5584565) B5584565
theorem B9928115 : Blo 2065435 9928115 := bstep (se 1 (by rfl) ⟨7446086, by rfl⟩ : syracuseStep 9928115 = 14892173) B14892173
theorem B6618743 : Blo 2065435 6618743 := bstep (se 1 (by rfl) ⟨4964057, by rfl⟩ : syracuseStep 6618743 = 9928115) B9928115
theorem B4412495 : Blo 2065435 4412495 := bstep (se 1 (by rfl) ⟨3309371, by rfl⟩ : syracuseStep 4412495 = 6618743) B6618743
theorem B11766653 : Blo 2065435 11766653 := bstep (se 3 (by rfl) ⟨2206247, by rfl⟩ : syracuseStep 11766653 = 4412495) B4412495
theorem B7844435 : Blo 2065435 7844435 := bstep (se 1 (by rfl) ⟨5883326, by rfl⟩ : syracuseStep 7844435 = 11766653) B11766653
theorem B5229623 : Blo 2065435 5229623 := bstep (se 1 (by rfl) ⟨3922217, by rfl⟩ : syracuseStep 5229623 = 7844435) B7844435
theorem B3486415 : Blo 2065435 3486415 := bstep (se 1 (by rfl) ⟨2614811, by rfl⟩ : syracuseStep 3486415 = 5229623) B5229623
theorem B4648553 : Blo 2065435 4648553 := bstep (se 2 (by rfl) ⟨1743207, by rfl⟩ : syracuseStep 4648553 = 3486415) B3486415
theorem B3099035 : Blo 2065435 3099035 := bstep (se 1 (by rfl) ⟨2324276, by rfl⟩ : syracuseStep 3099035 = 4648553) B4648553
theorem B2066023 : Blo 2065435 2066023 := bstep (se 1 (by rfl) ⟨1549517, by rfl⟩ : syracuseStep 2066023 = 3099035) B3099035
theorem B2324281 : Blo 2065435 2324281 := bbase (se 2 (by rfl) ⟨871605, by rfl⟩ : syracuseStep 2324281 = 1743211) (by norm_num)
theorem B3099041 : Blo 2065435 3099041 := bstep (se 2 (by rfl) ⟨1162140, by rfl⟩ : syracuseStep 3099041 = 2324281) B2324281
theorem B2066027 : Blo 2065435 2066027 := bstep (se 1 (by rfl) ⟨1549520, by rfl⟩ : syracuseStep 2066027 = 3099041) B3099041
theorem B5883349 : Blo 2065435 5883349 := bbase (se 7 (by rfl) ⟨68945, by rfl⟩ : syracuseStep 5883349 = 137891) (by norm_num)
theorem B7844465 : Blo 2065435 7844465 := bstep (se 2 (by rfl) ⟨2941674, by rfl⟩ : syracuseStep 7844465 = 5883349) B5883349
theorem B5229643 : Blo 2065435 5229643 := bstep (se 1 (by rfl) ⟨3922232, by rfl⟩ : syracuseStep 5229643 = 7844465) B7844465
theorem B6972857 : Blo 2065435 6972857 := bstep (se 2 (by rfl) ⟨2614821, by rfl⟩ : syracuseStep 6972857 = 5229643) B5229643
theorem B4648571 : Blo 2065435 4648571 := bstep (se 1 (by rfl) ⟨3486428, by rfl⟩ : syracuseStep 4648571 = 6972857) B6972857
theorem B3099047 : Blo 2065435 3099047 := bstep (se 1 (by rfl) ⟨2324285, by rfl⟩ : syracuseStep 3099047 = 4648571) B4648571
theorem B2066031 : Blo 2065435 2066031 := bstep (se 1 (by rfl) ⟨1549523, by rfl⟩ : syracuseStep 2066031 = 3099047) B3099047
theorem B3099053 : Blo 2065435 3099053 := bbase (se 3 (by rfl) ⟨581072, by rfl⟩ : syracuseStep 3099053 = 1162145) (by norm_num)
theorem B2066035 : Blo 2065435 2066035 := bstep (se 1 (by rfl) ⟨1549526, by rfl⟩ : syracuseStep 2066035 = 3099053) B3099053
theorem B4648589 : Blo 2065435 4648589 := bbase (se 3 (by rfl) ⟨871610, by rfl⟩ : syracuseStep 4648589 = 1743221) (by norm_num)
theorem B3099059 : Blo 2065435 3099059 := bstep (se 1 (by rfl) ⟨2324294, by rfl⟩ : syracuseStep 3099059 = 4648589) B4648589
theorem B2066039 : Blo 2065435 2066039 := bstep (se 1 (by rfl) ⟨1549529, by rfl⟩ : syracuseStep 2066039 = 3099059) B3099059
theorem B2614837 : Blo 2065435 2614837 := bbase (se 5 (by rfl) ⟨122570, by rfl⟩ : syracuseStep 2614837 = 245141) (by norm_num)
theorem B3486449 : Blo 2065435 3486449 := bstep (se 2 (by rfl) ⟨1307418, by rfl⟩ : syracuseStep 3486449 = 2614837) B2614837
theorem B2324299 : Blo 2065435 2324299 := bstep (se 1 (by rfl) ⟨1743224, by rfl⟩ : syracuseStep 2324299 = 3486449) B3486449
theorem B3099065 : Blo 2065435 3099065 := bstep (se 2 (by rfl) ⟨1162149, by rfl⟩ : syracuseStep 3099065 = 2324299) B2324299
theorem B2066043 : Blo 2065435 2066043 := bstep (se 1 (by rfl) ⟨1549532, by rfl⟩ : syracuseStep 2066043 = 3099065) B3099065
theorem B2515921 : Blo 2065435 2515921 := bbase (se 2 (by rfl) ⟨943470, by rfl⟩ : syracuseStep 2515921 = 1886941) (by norm_num)
theorem B13418245 : Blo 2065435 13418245 := bstep (se 4 (by rfl) ⟨1257960, by rfl⟩ : syracuseStep 13418245 = 2515921) B2515921
theorem B17890993 : Blo 2065435 17890993 := bstep (se 2 (by rfl) ⟨6709122, by rfl⟩ : syracuseStep 17890993 = 13418245) B13418245
theorem B23854657 : Blo 2065435 23854657 := bstep (se 2 (by rfl) ⟨8945496, by rfl⟩ : syracuseStep 23854657 = 17890993) B17890993
theorem B31806209 : Blo 2065435 31806209 := bstep (se 2 (by rfl) ⟨11927328, by rfl⟩ : syracuseStep 31806209 = 23854657) B23854657
theorem B21204139 : Blo 2065435 21204139 := bstep (se 1 (by rfl) ⟨15903104, by rfl⟩ : syracuseStep 21204139 = 31806209) B31806209
theorem B28272185 : Blo 2065435 28272185 := bstep (se 2 (by rfl) ⟨10602069, by rfl⟩ : syracuseStep 28272185 = 21204139) B21204139
theorem B18848123 : Blo 2065435 18848123 := bstep (se 1 (by rfl) ⟨14136092, by rfl⟩ : syracuseStep 18848123 = 28272185) B28272185
theorem B12565415 : Blo 2065435 12565415 := bstep (se 1 (by rfl) ⟨9424061, by rfl⟩ : syracuseStep 12565415 = 18848123) B18848123
theorem B8376943 : Blo 2065435 8376943 := bstep (se 1 (by rfl) ⟨6282707, by rfl⟩ : syracuseStep 8376943 = 12565415) B12565415
theorem B11169257 : Blo 2065435 11169257 := bstep (se 2 (by rfl) ⟨4188471, by rfl⟩ : syracuseStep 11169257 = 8376943) B8376943
theorem B29784685 : Blo 2065435 29784685 := bstep (se 3 (by rfl) ⟨5584628, by rfl⟩ : syracuseStep 29784685 = 11169257) B11169257
theorem B39712913 : Blo 2065435 39712913 := bstep (se 2 (by rfl) ⟨14892342, by rfl⟩ : syracuseStep 39712913 = 29784685) B29784685
theorem B26475275 : Blo 2065435 26475275 := bstep (se 1 (by rfl) ⟨19856456, by rfl⟩ : syracuseStep 26475275 = 39712913) B39712913
theorem B17650183 : Blo 2065435 17650183 := bstep (se 1 (by rfl) ⟨13237637, by rfl⟩ : syracuseStep 17650183 = 26475275) B26475275
theorem B23533577 : Blo 2065435 23533577 := bstep (se 2 (by rfl) ⟨8825091, by rfl⟩ : syracuseStep 23533577 = 17650183) B17650183
theorem B15689051 : Blo 2065435 15689051 := bstep (se 1 (by rfl) ⟨11766788, by rfl⟩ : syracuseStep 15689051 = 23533577) B23533577
theorem B10459367 : Blo 2065435 10459367 := bstep (se 1 (by rfl) ⟨7844525, by rfl⟩ : syracuseStep 10459367 = 15689051) B15689051
theorem B6972911 : Blo 2065435 6972911 := bstep (se 1 (by rfl) ⟨5229683, by rfl⟩ : syracuseStep 6972911 = 10459367) B10459367
theorem B4648607 : Blo 2065435 4648607 := bstep (se 1 (by rfl) ⟨3486455, by rfl⟩ : syracuseStep 4648607 = 6972911) B6972911
theorem B3099071 : Blo 2065435 3099071 := bstep (se 1 (by rfl) ⟨2324303, by rfl⟩ : syracuseStep 3099071 = 4648607) B4648607
theorem B2066047 : Blo 2065435 2066047 := bstep (se 1 (by rfl) ⟨1549535, by rfl⟩ : syracuseStep 2066047 = 3099071) B3099071
theorem B3099077 : Blo 2065435 3099077 := bbase (se 4 (by rfl) ⟨290538, by rfl⟩ : syracuseStep 3099077 = 581077) (by norm_num)
theorem B2066051 : Blo 2065435 2066051 := bstep (se 1 (by rfl) ⟨1549538, by rfl⟩ : syracuseStep 2066051 = 3099077) B3099077
theorem B3486469 : Blo 2065435 3486469 := bbase (se 4 (by rfl) ⟨326856, by rfl⟩ : syracuseStep 3486469 = 653713) (by norm_num)
theorem B4648625 : Blo 2065435 4648625 := bstep (se 2 (by rfl) ⟨1743234, by rfl⟩ : syracuseStep 4648625 = 3486469) B3486469
theorem B3099083 : Blo 2065435 3099083 := bstep (se 1 (by rfl) ⟨2324312, by rfl⟩ : syracuseStep 3099083 = 4648625) B4648625
theorem B2066055 : Blo 2065435 2066055 := bstep (se 1 (by rfl) ⟨1549541, by rfl⟩ : syracuseStep 2066055 = 3099083) B3099083
theorem B2324317 : Blo 2065435 2324317 := bbase (se 3 (by rfl) ⟨435809, by rfl⟩ : syracuseStep 2324317 = 871619) (by norm_num)
theorem B3099089 : Blo 2065435 3099089 := bstep (se 2 (by rfl) ⟨1162158, by rfl⟩ : syracuseStep 3099089 = 2324317) B2324317
theorem B2066059 : Blo 2065435 2066059 := bstep (se 1 (by rfl) ⟨1549544, by rfl⟩ : syracuseStep 2066059 = 3099089) B3099089
theorem B6972965 : Blo 2065435 6972965 := bbase (se 4 (by rfl) ⟨653715, by rfl⟩ : syracuseStep 6972965 = 1307431) (by norm_num)
theorem B4648643 : Blo 2065435 4648643 := bstep (se 1 (by rfl) ⟨3486482, by rfl⟩ : syracuseStep 4648643 = 6972965) B6972965
theorem B3099095 : Blo 2065435 3099095 := bstep (se 1 (by rfl) ⟨2324321, by rfl⟩ : syracuseStep 3099095 = 4648643) B4648643
theorem B2066063 : Blo 2065435 2066063 := bstep (se 1 (by rfl) ⟨1549547, by rfl⟩ : syracuseStep 2066063 = 3099095) B3099095
theorem B3099101 : Blo 2065435 3099101 := bbase (se 3 (by rfl) ⟨581081, by rfl⟩ : syracuseStep 3099101 = 1162163) (by norm_num)
theorem B2066067 : Blo 2065435 2066067 := bstep (se 1 (by rfl) ⟨1549550, by rfl⟩ : syracuseStep 2066067 = 3099101) B3099101
theorem B4648661 : Blo 2065435 4648661 := bbase (se 7 (by rfl) ⟨54476, by rfl⟩ : syracuseStep 4648661 = 108953) (by norm_num)
theorem B3099107 : Blo 2065435 3099107 := bstep (se 1 (by rfl) ⟨2324330, by rfl⟩ : syracuseStep 3099107 = 4648661) B4648661
theorem B2066071 : Blo 2065435 2066071 := bstep (se 1 (by rfl) ⟨1549553, by rfl⟩ : syracuseStep 2066071 = 3099107) B3099107
theorem B2094265 : Blo 2065435 2094265 := bbase (se 2 (by rfl) ⟨785349, by rfl⟩ : syracuseStep 2094265 = 1570699) (by norm_num)
theorem B11169413 : Blo 2065435 11169413 := bstep (se 4 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 11169413 = 2094265) B2094265
theorem B7446275 : Blo 2065435 7446275 := bstep (se 1 (by rfl) ⟨5584706, by rfl⟩ : syracuseStep 7446275 = 11169413) B11169413
theorem B4964183 : Blo 2065435 4964183 := bstep (se 1 (by rfl) ⟨3723137, by rfl⟩ : syracuseStep 4964183 = 7446275) B7446275
theorem B3309455 : Blo 2065435 3309455 := bstep (se 1 (by rfl) ⟨2482091, by rfl⟩ : syracuseStep 3309455 = 4964183) B4964183
theorem B8825213 : Blo 2065435 8825213 := bstep (se 3 (by rfl) ⟨1654727, by rfl⟩ : syracuseStep 8825213 = 3309455) B3309455
theorem B5883475 : Blo 2065435 5883475 := bstep (se 1 (by rfl) ⟨4412606, by rfl⟩ : syracuseStep 5883475 = 8825213) B8825213
theorem B7844633 : Blo 2065435 7844633 := bstep (se 2 (by rfl) ⟨2941737, by rfl⟩ : syracuseStep 7844633 = 5883475) B5883475
theorem B5229755 : Blo 2065435 5229755 := bstep (se 1 (by rfl) ⟨3922316, by rfl⟩ : syracuseStep 5229755 = 7844633) B7844633
theorem B3486503 : Blo 2065435 3486503 := bstep (se 1 (by rfl) ⟨2614877, by rfl⟩ : syracuseStep 3486503 = 5229755) B5229755
theorem B2324335 : Blo 2065435 2324335 := bstep (se 1 (by rfl) ⟨1743251, by rfl⟩ : syracuseStep 2324335 = 3486503) B3486503
theorem B3099113 : Blo 2065435 3099113 := bstep (se 2 (by rfl) ⟨1162167, by rfl⟩ : syracuseStep 3099113 = 2324335) B2324335
theorem B2066075 : Blo 2065435 2066075 := bstep (se 1 (by rfl) ⟨1549556, by rfl⟩ : syracuseStep 2066075 = 3099113) B3099113
theorem B25131221 : Blo 2065435 25131221 := bbase (se 7 (by rfl) ⟨294506, by rfl⟩ : syracuseStep 25131221 = 589013) (by norm_num)
theorem B16754147 : Blo 2065435 16754147 := bstep (se 1 (by rfl) ⟨12565610, by rfl⟩ : syracuseStep 16754147 = 25131221) B25131221
theorem B11169431 : Blo 2065435 11169431 := bstep (se 1 (by rfl) ⟨8377073, by rfl⟩ : syracuseStep 11169431 = 16754147) B16754147
theorem B7446287 : Blo 2065435 7446287 := bstep (se 1 (by rfl) ⟨5584715, by rfl⟩ : syracuseStep 7446287 = 11169431) B11169431
theorem B19856765 : Blo 2065435 19856765 := bstep (se 3 (by rfl) ⟨3723143, by rfl⟩ : syracuseStep 19856765 = 7446287) B7446287
theorem B13237843 : Blo 2065435 13237843 := bstep (se 1 (by rfl) ⟨9928382, by rfl⟩ : syracuseStep 13237843 = 19856765) B19856765
theorem B17650457 : Blo 2065435 17650457 := bstep (se 2 (by rfl) ⟨6618921, by rfl⟩ : syracuseStep 17650457 = 13237843) B13237843
theorem B11766971 : Blo 2065435 11766971 := bstep (se 1 (by rfl) ⟨8825228, by rfl⟩ : syracuseStep 11766971 = 17650457) B17650457
theorem B7844647 : Blo 2065435 7844647 := bstep (se 1 (by rfl) ⟨5883485, by rfl⟩ : syracuseStep 7844647 = 11766971) B11766971
theorem B10459529 : Blo 2065435 10459529 := bstep (se 2 (by rfl) ⟨3922323, by rfl⟩ : syracuseStep 10459529 = 7844647) B7844647
theorem B6973019 : Blo 2065435 6973019 := bstep (se 1 (by rfl) ⟨5229764, by rfl⟩ : syracuseStep 6973019 = 10459529) B10459529
theorem B4648679 : Blo 2065435 4648679 := bstep (se 1 (by rfl) ⟨3486509, by rfl⟩ : syracuseStep 4648679 = 6973019) B6973019
theorem B3099119 : Blo 2065435 3099119 := bstep (se 1 (by rfl) ⟨2324339, by rfl⟩ : syracuseStep 3099119 = 4648679) B4648679
theorem B2066079 : Blo 2065435 2066079 := bstep (se 1 (by rfl) ⟨1549559, by rfl⟩ : syracuseStep 2066079 = 3099119) B3099119
theorem B3099125 : Blo 2065435 3099125 := bbase (se 5 (by rfl) ⟨145271, by rfl⟩ : syracuseStep 3099125 = 290543) (by norm_num)
theorem B2066083 : Blo 2065435 2066083 := bstep (se 1 (by rfl) ⟨1549562, by rfl⟩ : syracuseStep 2066083 = 3099125) B3099125
theorem B5883509 : Blo 2065435 5883509 := bbase (se 5 (by rfl) ⟨275789, by rfl⟩ : syracuseStep 5883509 = 551579) (by norm_num)
theorem B3922339 : Blo 2065435 3922339 := bstep (se 1 (by rfl) ⟨2941754, by rfl⟩ : syracuseStep 3922339 = 5883509) B5883509
theorem B5229785 : Blo 2065435 5229785 := bstep (se 2 (by rfl) ⟨1961169, by rfl⟩ : syracuseStep 5229785 = 3922339) B3922339
theorem B3486523 : Blo 2065435 3486523 := bstep (se 1 (by rfl) ⟨2614892, by rfl⟩ : syracuseStep 3486523 = 5229785) B5229785
theorem B4648697 : Blo 2065435 4648697 := bstep (se 2 (by rfl) ⟨1743261, by rfl⟩ : syracuseStep 4648697 = 3486523) B3486523
theorem B3099131 : Blo 2065435 3099131 := bstep (se 1 (by rfl) ⟨2324348, by rfl⟩ : syracuseStep 3099131 = 4648697) B4648697
theorem B2066087 : Blo 2065435 2066087 := bstep (se 1 (by rfl) ⟨1549565, by rfl⟩ : syracuseStep 2066087 = 3099131) B3099131
theorem B2324353 : Blo 2065435 2324353 := bbase (se 2 (by rfl) ⟨871632, by rfl⟩ : syracuseStep 2324353 = 1743265) (by norm_num)
theorem B3099137 : Blo 2065435 3099137 := bstep (se 2 (by rfl) ⟨1162176, by rfl⟩ : syracuseStep 3099137 = 2324353) B2324353
theorem B2066091 : Blo 2065435 2066091 := bstep (se 1 (by rfl) ⟨1549568, by rfl⟩ : syracuseStep 2066091 = 3099137) B3099137
theorem B5229805 : Blo 2065435 5229805 := bbase (se 3 (by rfl) ⟨980588, by rfl⟩ : syracuseStep 5229805 = 1961177) (by norm_num)
theorem B6973073 : Blo 2065435 6973073 := bstep (se 2 (by rfl) ⟨2614902, by rfl⟩ : syracuseStep 6973073 = 5229805) B5229805
theorem B4648715 : Blo 2065435 4648715 := bstep (se 1 (by rfl) ⟨3486536, by rfl⟩ : syracuseStep 4648715 = 6973073) B6973073
theorem B3099143 : Blo 2065435 3099143 := bstep (se 1 (by rfl) ⟨2324357, by rfl⟩ : syracuseStep 3099143 = 4648715) B4648715
theorem B2066095 : Blo 2065435 2066095 := bstep (se 1 (by rfl) ⟨1549571, by rfl⟩ : syracuseStep 2066095 = 3099143) B3099143
theorem B3099149 : Blo 2065435 3099149 := bbase (se 3 (by rfl) ⟨581090, by rfl⟩ : syracuseStep 3099149 = 1162181) (by norm_num)
theorem B2066099 : Blo 2065435 2066099 := bstep (se 1 (by rfl) ⟨1549574, by rfl⟩ : syracuseStep 2066099 = 3099149) B3099149
theorem B4648733 : Blo 2065435 4648733 := bbase (se 3 (by rfl) ⟨871637, by rfl⟩ : syracuseStep 4648733 = 1743275) (by norm_num)
theorem B3099155 : Blo 2065435 3099155 := bstep (se 1 (by rfl) ⟨2324366, by rfl⟩ : syracuseStep 3099155 = 4648733) B4648733
theorem B2066103 : Blo 2065435 2066103 := bstep (se 1 (by rfl) ⟨1549577, by rfl⟩ : syracuseStep 2066103 = 3099155) B3099155
theorem B3486557 : Blo 2065435 3486557 := bbase (se 3 (by rfl) ⟨653729, by rfl⟩ : syracuseStep 3486557 = 1307459) (by norm_num)
theorem B2324371 : Blo 2065435 2324371 := bstep (se 1 (by rfl) ⟨1743278, by rfl⟩ : syracuseStep 2324371 = 3486557) B3486557
theorem B3099161 : Blo 2065435 3099161 := bstep (se 2 (by rfl) ⟨1162185, by rfl⟩ : syracuseStep 3099161 = 2324371) B2324371
theorem B2066107 : Blo 2065435 2066107 := bstep (se 1 (by rfl) ⟨1549580, by rfl⟩ : syracuseStep 2066107 = 3099161) B3099161
theorem B8825365 : Blo 2065435 8825365 := bbase (se 6 (by rfl) ⟨206844, by rfl⟩ : syracuseStep 8825365 = 413689) (by norm_num)
theorem B11767153 : Blo 2065435 11767153 := bstep (se 2 (by rfl) ⟨4412682, by rfl⟩ : syracuseStep 11767153 = 8825365) B8825365
theorem B15689537 : Blo 2065435 15689537 := bstep (se 2 (by rfl) ⟨5883576, by rfl⟩ : syracuseStep 15689537 = 11767153) B11767153
theorem B10459691 : Blo 2065435 10459691 := bstep (se 1 (by rfl) ⟨7844768, by rfl⟩ : syracuseStep 10459691 = 15689537) B15689537
theorem B6973127 : Blo 2065435 6973127 := bstep (se 1 (by rfl) ⟨5229845, by rfl⟩ : syracuseStep 6973127 = 10459691) B10459691
theorem B4648751 : Blo 2065435 4648751 := bstep (se 1 (by rfl) ⟨3486563, by rfl⟩ : syracuseStep 4648751 = 6973127) B6973127
theorem B3099167 : Blo 2065435 3099167 := bstep (se 1 (by rfl) ⟨2324375, by rfl⟩ : syracuseStep 3099167 = 4648751) B4648751
theorem B2066111 : Blo 2065435 2066111 := bstep (se 1 (by rfl) ⟨1549583, by rfl⟩ : syracuseStep 2066111 = 3099167) B3099167
theorem B3099173 : Blo 2065435 3099173 := bbase (se 4 (by rfl) ⟨290547, by rfl⟩ : syracuseStep 3099173 = 581095) (by norm_num)
theorem B2066115 : Blo 2065435 2066115 := bstep (se 1 (by rfl) ⟨1549586, by rfl⟩ : syracuseStep 2066115 = 3099173) B3099173
theorem B2614933 : Blo 2065435 2614933 := bbase (se 6 (by rfl) ⟨61287, by rfl⟩ : syracuseStep 2614933 = 122575) (by norm_num)
theorem B3486577 : Blo 2065435 3486577 := bstep (se 2 (by rfl) ⟨1307466, by rfl⟩ : syracuseStep 3486577 = 2614933) B2614933
theorem B4648769 : Blo 2065435 4648769 := bstep (se 2 (by rfl) ⟨1743288, by rfl⟩ : syracuseStep 4648769 = 3486577) B3486577
theorem B3099179 : Blo 2065435 3099179 := bstep (se 1 (by rfl) ⟨2324384, by rfl⟩ : syracuseStep 3099179 = 4648769) B4648769
theorem B2066119 : Blo 2065435 2066119 := bstep (se 1 (by rfl) ⟨1549589, by rfl⟩ : syracuseStep 2066119 = 3099179) B3099179
theorem B2324389 : Blo 2065435 2324389 := bbase (se 4 (by rfl) ⟨217911, by rfl⟩ : syracuseStep 2324389 = 435823) (by norm_num)
theorem B3099185 : Blo 2065435 3099185 := bstep (se 2 (by rfl) ⟨1162194, by rfl⟩ : syracuseStep 3099185 = 2324389) B2324389
theorem B2066123 : Blo 2065435 2066123 := bstep (se 1 (by rfl) ⟨1549592, by rfl⟩ : syracuseStep 2066123 = 3099185) B3099185
theorem B2869141 : Blo 2065435 2869141 := bbase (se 6 (by rfl) ⟨67245, by rfl⟩ : syracuseStep 2869141 = 134491) (by norm_num)
theorem B3825521 : Blo 2065435 3825521 := bstep (se 2 (by rfl) ⟨1434570, by rfl⟩ : syracuseStep 3825521 = 2869141) B2869141
theorem B2550347 : Blo 2065435 2550347 := bstep (se 1 (by rfl) ⟨1912760, by rfl⟩ : syracuseStep 2550347 = 3825521) B3825521
theorem B27203701 : Blo 2065435 27203701 := bstep (se 5 (by rfl) ⟨1275173, by rfl⟩ : syracuseStep 27203701 = 2550347) B2550347
theorem B36271601 : Blo 2065435 36271601 := bstep (se 2 (by rfl) ⟨13601850, by rfl⟩ : syracuseStep 36271601 = 27203701) B27203701
theorem B24181067 : Blo 2065435 24181067 := bstep (se 1 (by rfl) ⟨18135800, by rfl⟩ : syracuseStep 24181067 = 36271601) B36271601
theorem B16120711 : Blo 2065435 16120711 := bstep (se 1 (by rfl) ⟨12090533, by rfl⟩ : syracuseStep 16120711 = 24181067) B24181067
theorem B21494281 : Blo 2065435 21494281 := bstep (se 2 (by rfl) ⟨8060355, by rfl⟩ : syracuseStep 21494281 = 16120711) B16120711
theorem B28659041 : Blo 2065435 28659041 := bstep (se 2 (by rfl) ⟨10747140, by rfl⟩ : syracuseStep 28659041 = 21494281) B21494281
theorem B19106027 : Blo 2065435 19106027 := bstep (se 1 (by rfl) ⟨14329520, by rfl⟩ : syracuseStep 19106027 = 28659041) B28659041
theorem B12737351 : Blo 2065435 12737351 := bstep (se 1 (by rfl) ⟨9553013, by rfl⟩ : syracuseStep 12737351 = 19106027) B19106027
theorem B8491567 : Blo 2065435 8491567 := bstep (se 1 (by rfl) ⟨6368675, by rfl⟩ : syracuseStep 8491567 = 12737351) B12737351
theorem B11322089 : Blo 2065435 11322089 := bstep (se 2 (by rfl) ⟨4245783, by rfl⟩ : syracuseStep 11322089 = 8491567) B8491567
theorem B7548059 : Blo 2065435 7548059 := bstep (se 1 (by rfl) ⟨5661044, by rfl⟩ : syracuseStep 7548059 = 11322089) B11322089
theorem B5032039 : Blo 2065435 5032039 := bstep (se 1 (by rfl) ⟨3774029, by rfl⟩ : syracuseStep 5032039 = 7548059) B7548059
theorem B6709385 : Blo 2065435 6709385 := bstep (se 2 (by rfl) ⟨2516019, by rfl⟩ : syracuseStep 6709385 = 5032039) B5032039
theorem B4472923 : Blo 2065435 4472923 := bstep (se 1 (by rfl) ⟨3354692, by rfl⟩ : syracuseStep 4472923 = 6709385) B6709385
theorem B5963897 : Blo 2065435 5963897 := bstep (se 2 (by rfl) ⟨2236461, by rfl⟩ : syracuseStep 5963897 = 4472923) B4472923
theorem B3975931 : Blo 2065435 3975931 := bstep (se 1 (by rfl) ⟨2981948, by rfl⟩ : syracuseStep 3975931 = 5963897) B5963897
theorem B21204965 : Blo 2065435 21204965 := bstep (se 4 (by rfl) ⟨1987965, by rfl⟩ : syracuseStep 21204965 = 3975931) B3975931
theorem B14136643 : Blo 2065435 14136643 := bstep (se 1 (by rfl) ⟨10602482, by rfl⟩ : syracuseStep 14136643 = 21204965) B21204965
theorem B18848857 : Blo 2065435 18848857 := bstep (se 2 (by rfl) ⟨7068321, by rfl⟩ : syracuseStep 18848857 = 14136643) B14136643
theorem B25131809 : Blo 2065435 25131809 := bstep (se 2 (by rfl) ⟨9424428, by rfl⟩ : syracuseStep 25131809 = 18848857) B18848857
theorem B16754539 : Blo 2065435 16754539 := bstep (se 1 (by rfl) ⟨12565904, by rfl⟩ : syracuseStep 16754539 = 25131809) B25131809
theorem B22339385 : Blo 2065435 22339385 := bstep (se 2 (by rfl) ⟨8377269, by rfl⟩ : syracuseStep 22339385 = 16754539) B16754539
theorem B14892923 : Blo 2065435 14892923 := bstep (se 1 (by rfl) ⟨11169692, by rfl⟩ : syracuseStep 14892923 = 22339385) B22339385
theorem B9928615 : Blo 2065435 9928615 := bstep (se 1 (by rfl) ⟨7446461, by rfl⟩ : syracuseStep 9928615 = 14892923) B14892923
theorem B13238153 : Blo 2065435 13238153 := bstep (se 2 (by rfl) ⟨4964307, by rfl⟩ : syracuseStep 13238153 = 9928615) B9928615
theorem B8825435 : Blo 2065435 8825435 := bstep (se 1 (by rfl) ⟨6619076, by rfl⟩ : syracuseStep 8825435 = 13238153) B13238153
theorem B5883623 : Blo 2065435 5883623 := bstep (se 1 (by rfl) ⟨4412717, by rfl⟩ : syracuseStep 5883623 = 8825435) B8825435
theorem B3922415 : Blo 2065435 3922415 := bstep (se 1 (by rfl) ⟨2941811, by rfl⟩ : syracuseStep 3922415 = 5883623) B5883623
theorem B2614943 : Blo 2065435 2614943 := bstep (se 1 (by rfl) ⟨1961207, by rfl⟩ : syracuseStep 2614943 = 3922415) B3922415
theorem B6973181 : Blo 2065435 6973181 := bstep (se 3 (by rfl) ⟨1307471, by rfl⟩ : syracuseStep 6973181 = 2614943) B2614943
theorem B4648787 : Blo 2065435 4648787 := bstep (se 1 (by rfl) ⟨3486590, by rfl⟩ : syracuseStep 4648787 = 6973181) B6973181
theorem B3099191 : Blo 2065435 3099191 := bstep (se 1 (by rfl) ⟨2324393, by rfl⟩ : syracuseStep 3099191 = 4648787) B4648787
theorem B2066127 : Blo 2065435 2066127 := bstep (se 1 (by rfl) ⟨1549595, by rfl⟩ : syracuseStep 2066127 = 3099191) B3099191
theorem B3099197 : Blo 2065435 3099197 := bbase (se 3 (by rfl) ⟨581099, by rfl⟩ : syracuseStep 3099197 = 1162199) (by norm_num)
theorem B2066131 : Blo 2065435 2066131 := bstep (se 1 (by rfl) ⟨1549598, by rfl⟩ : syracuseStep 2066131 = 3099197) B3099197
theorem B4648805 : Blo 2065435 4648805 := bbase (se 4 (by rfl) ⟨435825, by rfl⟩ : syracuseStep 4648805 = 871651) (by norm_num)
theorem B3099203 : Blo 2065435 3099203 := bstep (se 1 (by rfl) ⟨2324402, by rfl⟩ : syracuseStep 3099203 = 4648805) B4648805
theorem B2066135 : Blo 2065435 2066135 := bstep (se 1 (by rfl) ⟨1549601, by rfl⟩ : syracuseStep 2066135 = 3099203) B3099203
theorem B5229917 : Blo 2065435 5229917 := bbase (se 3 (by rfl) ⟨980609, by rfl⟩ : syracuseStep 5229917 = 1961219) (by norm_num)
theorem B3486611 : Blo 2065435 3486611 := bstep (se 1 (by rfl) ⟨2614958, by rfl⟩ : syracuseStep 3486611 = 5229917) B5229917
theorem B2324407 : Blo 2065435 2324407 := bstep (se 1 (by rfl) ⟨1743305, by rfl⟩ : syracuseStep 2324407 = 3486611) B3486611
theorem B3099209 : Blo 2065435 3099209 := bstep (se 2 (by rfl) ⟨1162203, by rfl⟩ : syracuseStep 3099209 = 2324407) B2324407
theorem B2066139 : Blo 2065435 2066139 := bstep (se 1 (by rfl) ⟨1549604, by rfl⟩ : syracuseStep 2066139 = 3099209) B3099209
theorem B3922445 : Blo 2065435 3922445 := bbase (se 3 (by rfl) ⟨735458, by rfl⟩ : syracuseStep 3922445 = 1470917) (by norm_num)
theorem B10459853 : Blo 2065435 10459853 := bstep (se 3 (by rfl) ⟨1961222, by rfl⟩ : syracuseStep 10459853 = 3922445) B3922445
theorem B6973235 : Blo 2065435 6973235 := bstep (se 1 (by rfl) ⟨5229926, by rfl⟩ : syracuseStep 6973235 = 10459853) B10459853
theorem B4648823 : Blo 2065435 4648823 := bstep (se 1 (by rfl) ⟨3486617, by rfl⟩ : syracuseStep 4648823 = 6973235) B6973235
theorem B3099215 : Blo 2065435 3099215 := bstep (se 1 (by rfl) ⟨2324411, by rfl⟩ : syracuseStep 3099215 = 4648823) B4648823
theorem B2066143 : Blo 2065435 2066143 := bstep (se 1 (by rfl) ⟨1549607, by rfl⟩ : syracuseStep 2066143 = 3099215) B3099215
theorem B3099221 : Blo 2065435 3099221 := bbase (se 8 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 3099221 = 36319) (by norm_num)
theorem B2066147 : Blo 2065435 2066147 := bstep (se 1 (by rfl) ⟨1549610, by rfl⟩ : syracuseStep 2066147 = 3099221) B3099221
theorem B4964365 : Blo 2065435 4964365 := bbase (se 3 (by rfl) ⟨930818, by rfl⟩ : syracuseStep 4964365 = 1861637) (by norm_num)
theorem B6619153 : Blo 2065435 6619153 := bstep (se 2 (by rfl) ⟨2482182, by rfl⟩ : syracuseStep 6619153 = 4964365) B4964365
theorem B8825537 : Blo 2065435 8825537 := bstep (se 2 (by rfl) ⟨3309576, by rfl⟩ : syracuseStep 8825537 = 6619153) B6619153
theorem B5883691 : Blo 2065435 5883691 := bstep (se 1 (by rfl) ⟨4412768, by rfl⟩ : syracuseStep 5883691 = 8825537) B8825537
theorem B7844921 : Blo 2065435 7844921 := bstep (se 2 (by rfl) ⟨2941845, by rfl⟩ : syracuseStep 7844921 = 5883691) B5883691
theorem B5229947 : Blo 2065435 5229947 := bstep (se 1 (by rfl) ⟨3922460, by rfl⟩ : syracuseStep 5229947 = 7844921) B7844921
theorem B3486631 : Blo 2065435 3486631 := bstep (se 1 (by rfl) ⟨2614973, by rfl⟩ : syracuseStep 3486631 = 5229947) B5229947
theorem B4648841 : Blo 2065435 4648841 := bstep (se 2 (by rfl) ⟨1743315, by rfl⟩ : syracuseStep 4648841 = 3486631) B3486631
theorem B3099227 : Blo 2065435 3099227 := bstep (se 1 (by rfl) ⟨2324420, by rfl⟩ : syracuseStep 3099227 = 4648841) B4648841
theorem B2066151 : Blo 2065435 2066151 := bstep (se 1 (by rfl) ⟨1549613, by rfl⟩ : syracuseStep 2066151 = 3099227) B3099227
theorem B2324425 : Blo 2065435 2324425 := bbase (se 2 (by rfl) ⟨871659, by rfl⟩ : syracuseStep 2324425 = 1743319) (by norm_num)
theorem B3099233 : Blo 2065435 3099233 := bstep (se 2 (by rfl) ⟨1162212, by rfl⟩ : syracuseStep 3099233 = 2324425) B2324425
theorem B2066155 : Blo 2065435 2066155 := bstep (se 1 (by rfl) ⟨1549616, by rfl⟩ : syracuseStep 2066155 = 3099233) B3099233
theorem B3309589 : Blo 2065435 3309589 := bbase (se 6 (by rfl) ⟨77568, by rfl⟩ : syracuseStep 3309589 = 155137) (by norm_num)
theorem B17651141 : Blo 2065435 17651141 := bstep (se 4 (by rfl) ⟨1654794, by rfl⟩ : syracuseStep 17651141 = 3309589) B3309589
theorem B11767427 : Blo 2065435 11767427 := bstep (se 1 (by rfl) ⟨8825570, by rfl⟩ : syracuseStep 11767427 = 17651141) B17651141
theorem B7844951 : Blo 2065435 7844951 := bstep (se 1 (by rfl) ⟨5883713, by rfl⟩ : syracuseStep 7844951 = 11767427) B11767427
theorem B5229967 : Blo 2065435 5229967 := bstep (se 1 (by rfl) ⟨3922475, by rfl⟩ : syracuseStep 5229967 = 7844951) B7844951
theorem B6973289 : Blo 2065435 6973289 := bstep (se 2 (by rfl) ⟨2614983, by rfl⟩ : syracuseStep 6973289 = 5229967) B5229967
theorem B4648859 : Blo 2065435 4648859 := bstep (se 1 (by rfl) ⟨3486644, by rfl⟩ : syracuseStep 4648859 = 6973289) B6973289
theorem B3099239 : Blo 2065435 3099239 := bstep (se 1 (by rfl) ⟨2324429, by rfl⟩ : syracuseStep 3099239 = 4648859) B4648859
theorem B2066159 : Blo 2065435 2066159 := bstep (se 1 (by rfl) ⟨1549619, by rfl⟩ : syracuseStep 2066159 = 3099239) B3099239
theorem B3099245 : Blo 2065435 3099245 := bbase (se 3 (by rfl) ⟨581108, by rfl⟩ : syracuseStep 3099245 = 1162217) (by norm_num)
theorem B2066163 : Blo 2065435 2066163 := bstep (se 1 (by rfl) ⟨1549622, by rfl⟩ : syracuseStep 2066163 = 3099245) B3099245
theorem B4648877 : Blo 2065435 4648877 := bbase (se 3 (by rfl) ⟨871664, by rfl⟩ : syracuseStep 4648877 = 1743329) (by norm_num)
theorem B3099251 : Blo 2065435 3099251 := bstep (se 1 (by rfl) ⟨2324438, by rfl⟩ : syracuseStep 3099251 = 4648877) B4648877
theorem B2066167 : Blo 2065435 2066167 := bstep (se 1 (by rfl) ⟨1549625, by rfl⟩ : syracuseStep 2066167 = 3099251) B3099251
theorem B5883749 : Blo 2065435 5883749 := bbase (se 4 (by rfl) ⟨551601, by rfl⟩ : syracuseStep 5883749 = 1103203) (by norm_num)
theorem B3922499 : Blo 2065435 3922499 := bstep (se 1 (by rfl) ⟨2941874, by rfl⟩ : syracuseStep 3922499 = 5883749) B5883749
theorem B2614999 : Blo 2065435 2614999 := bstep (se 1 (by rfl) ⟨1961249, by rfl⟩ : syracuseStep 2614999 = 3922499) B3922499
theorem B3486665 : Blo 2065435 3486665 := bstep (se 2 (by rfl) ⟨1307499, by rfl⟩ : syracuseStep 3486665 = 2614999) B2614999
theorem B2324443 : Blo 2065435 2324443 := bstep (se 1 (by rfl) ⟨1743332, by rfl⟩ : syracuseStep 2324443 = 3486665) B3486665
theorem B3099257 : Blo 2065435 3099257 := bstep (se 2 (by rfl) ⟨1162221, by rfl⟩ : syracuseStep 3099257 = 2324443) B2324443
theorem B2066171 : Blo 2065435 2066171 := bstep (se 1 (by rfl) ⟨1549628, by rfl⟩ : syracuseStep 2066171 = 3099257) B3099257
theorem B7068485 : Blo 2065435 7068485 := bbase (se 4 (by rfl) ⟨662670, by rfl⟩ : syracuseStep 7068485 = 1325341) (by norm_num)
theorem B4712323 : Blo 2065435 4712323 := bstep (se 1 (by rfl) ⟨3534242, by rfl⟩ : syracuseStep 4712323 = 7068485) B7068485
theorem B6283097 : Blo 2065435 6283097 := bstep (se 2 (by rfl) ⟨2356161, by rfl⟩ : syracuseStep 6283097 = 4712323) B4712323
theorem B4188731 : Blo 2065435 4188731 := bstep (se 1 (by rfl) ⟨3141548, by rfl⟩ : syracuseStep 4188731 = 6283097) B6283097
theorem B11169949 : Blo 2065435 11169949 := bstep (se 3 (by rfl) ⟨2094365, by rfl⟩ : syracuseStep 11169949 = 4188731) B4188731
theorem B14893265 : Blo 2065435 14893265 := bstep (se 2 (by rfl) ⟨5584974, by rfl⟩ : syracuseStep 14893265 = 11169949) B11169949
theorem B39715373 : Blo 2065435 39715373 := bstep (se 3 (by rfl) ⟨7446632, by rfl⟩ : syracuseStep 39715373 = 14893265) B14893265
theorem B26476915 : Blo 2065435 26476915 := bstep (se 1 (by rfl) ⟨19857686, by rfl⟩ : syracuseStep 26476915 = 39715373) B39715373
theorem B35302553 : Blo 2065435 35302553 := bstep (se 2 (by rfl) ⟨13238457, by rfl⟩ : syracuseStep 35302553 = 26476915) B26476915
theorem B23535035 : Blo 2065435 23535035 := bstep (se 1 (by rfl) ⟨17651276, by rfl⟩ : syracuseStep 23535035 = 35302553) B35302553
theorem B15690023 : Blo 2065435 15690023 := bstep (se 1 (by rfl) ⟨11767517, by rfl⟩ : syracuseStep 15690023 = 23535035) B23535035
theorem B10460015 : Blo 2065435 10460015 := bstep (se 1 (by rfl) ⟨7845011, by rfl⟩ : syracuseStep 10460015 = 15690023) B15690023
theorem B6973343 : Blo 2065435 6973343 := bstep (se 1 (by rfl) ⟨5230007, by rfl⟩ : syracuseStep 6973343 = 10460015) B10460015
theorem B4648895 : Blo 2065435 4648895 := bstep (se 1 (by rfl) ⟨3486671, by rfl⟩ : syracuseStep 4648895 = 6973343) B6973343
theorem B3099263 : Blo 2065435 3099263 := bstep (se 1 (by rfl) ⟨2324447, by rfl⟩ : syracuseStep 3099263 = 4648895) B4648895
theorem B2066175 : Blo 2065435 2066175 := bstep (se 1 (by rfl) ⟨1549631, by rfl⟩ : syracuseStep 2066175 = 3099263) B3099263
theorem B3099269 : Blo 2065435 3099269 := bbase (se 4 (by rfl) ⟨290556, by rfl⟩ : syracuseStep 3099269 = 581113) (by norm_num)
theorem B2066179 : Blo 2065435 2066179 := bstep (se 1 (by rfl) ⟨1549634, by rfl⟩ : syracuseStep 2066179 = 3099269) B3099269
theorem B3486685 : Blo 2065435 3486685 := bbase (se 3 (by rfl) ⟨653753, by rfl⟩ : syracuseStep 3486685 = 1307507) (by norm_num)
theorem B4648913 : Blo 2065435 4648913 := bstep (se 2 (by rfl) ⟨1743342, by rfl⟩ : syracuseStep 4648913 = 3486685) B3486685
theorem B3099275 : Blo 2065435 3099275 := bstep (se 1 (by rfl) ⟨2324456, by rfl⟩ : syracuseStep 3099275 = 4648913) B4648913
theorem B2066183 : Blo 2065435 2066183 := bstep (se 1 (by rfl) ⟨1549637, by rfl⟩ : syracuseStep 2066183 = 3099275) B3099275
theorem B2324461 : Blo 2065435 2324461 := bbase (se 3 (by rfl) ⟨435836, by rfl⟩ : syracuseStep 2324461 = 871673) (by norm_num)
theorem B3099281 : Blo 2065435 3099281 := bstep (se 2 (by rfl) ⟨1162230, by rfl⟩ : syracuseStep 3099281 = 2324461) B2324461
theorem B2066187 : Blo 2065435 2066187 := bstep (se 1 (by rfl) ⟨1549640, by rfl⟩ : syracuseStep 2066187 = 3099281) B3099281
theorem B6973397 : Blo 2065435 6973397 := bbase (se 7 (by rfl) ⟨81719, by rfl⟩ : syracuseStep 6973397 = 163439) (by norm_num)
theorem B4648931 : Blo 2065435 4648931 := bstep (se 1 (by rfl) ⟨3486698, by rfl⟩ : syracuseStep 4648931 = 6973397) B6973397
theorem B3099287 : Blo 2065435 3099287 := bstep (se 1 (by rfl) ⟨2324465, by rfl⟩ : syracuseStep 3099287 = 4648931) B4648931
theorem B2066191 : Blo 2065435 2066191 := bstep (se 1 (by rfl) ⟨1549643, by rfl⟩ : syracuseStep 2066191 = 3099287) B3099287
theorem B3099293 : Blo 2065435 3099293 := bbase (se 3 (by rfl) ⟨581117, by rfl⟩ : syracuseStep 3099293 = 1162235) (by norm_num)
theorem B2066195 : Blo 2065435 2066195 := bstep (se 1 (by rfl) ⟨1549646, by rfl⟩ : syracuseStep 2066195 = 3099293) B3099293
theorem B4648949 : Blo 2065435 4648949 := bbase (se 5 (by rfl) ⟨217919, by rfl⟩ : syracuseStep 4648949 = 435839) (by norm_num)
theorem B3099299 : Blo 2065435 3099299 := bstep (se 1 (by rfl) ⟨2324474, by rfl⟩ : syracuseStep 3099299 = 4648949) B4648949
theorem B2066199 : Blo 2065435 2066199 := bstep (se 1 (by rfl) ⟨1549649, by rfl⟩ : syracuseStep 2066199 = 3099299) B3099299
theorem B7068581 : Blo 2065435 7068581 := bbase (se 4 (by rfl) ⟨662679, by rfl⟩ : syracuseStep 7068581 = 1325359) (by norm_num)
theorem B4712387 : Blo 2065435 4712387 := bstep (se 1 (by rfl) ⟨3534290, by rfl⟩ : syracuseStep 4712387 = 7068581) B7068581
theorem B50265461 : Blo 2065435 50265461 := bstep (se 5 (by rfl) ⟨2356193, by rfl⟩ : syracuseStep 50265461 = 4712387) B4712387
theorem B134041229 : Blo 2065435 134041229 := bstep (se 3 (by rfl) ⟨25132730, by rfl⟩ : syracuseStep 134041229 = 50265461) B50265461
theorem B89360819 : Blo 2065435 89360819 := bstep (se 1 (by rfl) ⟨67020614, by rfl⟩ : syracuseStep 89360819 = 134041229) B134041229
theorem B59573879 : Blo 2065435 59573879 := bstep (se 1 (by rfl) ⟨44680409, by rfl⟩ : syracuseStep 59573879 = 89360819) B89360819
theorem B39715919 : Blo 2065435 39715919 := bstep (se 1 (by rfl) ⟨29786939, by rfl⟩ : syracuseStep 39715919 = 59573879) B59573879
theorem B26477279 : Blo 2065435 26477279 := bstep (se 1 (by rfl) ⟨19857959, by rfl⟩ : syracuseStep 26477279 = 39715919) B39715919
theorem B17651519 : Blo 2065435 17651519 := bstep (se 1 (by rfl) ⟨13238639, by rfl⟩ : syracuseStep 17651519 = 26477279) B26477279
theorem B11767679 : Blo 2065435 11767679 := bstep (se 1 (by rfl) ⟨8825759, by rfl⟩ : syracuseStep 11767679 = 17651519) B17651519
theorem B7845119 : Blo 2065435 7845119 := bstep (se 1 (by rfl) ⟨5883839, by rfl⟩ : syracuseStep 7845119 = 11767679) B11767679
theorem B5230079 : Blo 2065435 5230079 := bstep (se 1 (by rfl) ⟨3922559, by rfl⟩ : syracuseStep 5230079 = 7845119) B7845119
theorem B3486719 : Blo 2065435 3486719 := bstep (se 1 (by rfl) ⟨2615039, by rfl⟩ : syracuseStep 3486719 = 5230079) B5230079
theorem B2324479 : Blo 2065435 2324479 := bstep (se 1 (by rfl) ⟨1743359, by rfl⟩ : syracuseStep 2324479 = 3486719) B3486719
theorem B3099305 : Blo 2065435 3099305 := bstep (se 2 (by rfl) ⟨1162239, by rfl⟩ : syracuseStep 3099305 = 2324479) B2324479
theorem B2066203 : Blo 2065435 2066203 := bstep (se 1 (by rfl) ⟨1549652, by rfl⟩ : syracuseStep 2066203 = 3099305) B3099305
theorem B2941925 : Blo 2065435 2941925 := bbase (se 4 (by rfl) ⟨275805, by rfl⟩ : syracuseStep 2941925 = 551611) (by norm_num)
theorem B7845133 : Blo 2065435 7845133 := bstep (se 3 (by rfl) ⟨1470962, by rfl⟩ : syracuseStep 7845133 = 2941925) B2941925
theorem B10460177 : Blo 2065435 10460177 := bstep (se 2 (by rfl) ⟨3922566, by rfl⟩ : syracuseStep 10460177 = 7845133) B7845133
theorem B6973451 : Blo 2065435 6973451 := bstep (se 1 (by rfl) ⟨5230088, by rfl⟩ : syracuseStep 6973451 = 10460177) B10460177
theorem B4648967 : Blo 2065435 4648967 := bstep (se 1 (by rfl) ⟨3486725, by rfl⟩ : syracuseStep 4648967 = 6973451) B6973451
theorem B3099311 : Blo 2065435 3099311 := bstep (se 1 (by rfl) ⟨2324483, by rfl⟩ : syracuseStep 3099311 = 4648967) B4648967
theorem B2066207 : Blo 2065435 2066207 := bstep (se 1 (by rfl) ⟨1549655, by rfl⟩ : syracuseStep 2066207 = 3099311) B3099311
theorem B3099317 : Blo 2065435 3099317 := bbase (se 5 (by rfl) ⟨145280, by rfl⟩ : syracuseStep 3099317 = 290561) (by norm_num)
theorem B2066211 : Blo 2065435 2066211 := bstep (se 1 (by rfl) ⟨1549658, by rfl⟩ : syracuseStep 2066211 = 3099317) B3099317
theorem B5230109 : Blo 2065435 5230109 := bbase (se 3 (by rfl) ⟨980645, by rfl⟩ : syracuseStep 5230109 = 1961291) (by norm_num)
theorem B3486739 : Blo 2065435 3486739 := bstep (se 1 (by rfl) ⟨2615054, by rfl⟩ : syracuseStep 3486739 = 5230109) B5230109
theorem B4648985 : Blo 2065435 4648985 := bstep (se 2 (by rfl) ⟨1743369, by rfl⟩ : syracuseStep 4648985 = 3486739) B3486739
theorem B3099323 : Blo 2065435 3099323 := bstep (se 1 (by rfl) ⟨2324492, by rfl⟩ : syracuseStep 3099323 = 4648985) B4648985
theorem B2066215 : Blo 2065435 2066215 := bstep (se 1 (by rfl) ⟨1549661, by rfl⟩ : syracuseStep 2066215 = 3099323) B3099323
theorem B2324497 : Blo 2065435 2324497 := bbase (se 2 (by rfl) ⟨871686, by rfl⟩ : syracuseStep 2324497 = 1743373) (by norm_num)
theorem B3099329 : Blo 2065435 3099329 := bstep (se 2 (by rfl) ⟨1162248, by rfl⟩ : syracuseStep 3099329 = 2324497) B2324497
theorem B2066219 : Blo 2065435 2066219 := bstep (se 1 (by rfl) ⟨1549664, by rfl⟩ : syracuseStep 2066219 = 3099329) B3099329
theorem B3922597 : Blo 2065435 3922597 := bbase (se 4 (by rfl) ⟨367743, by rfl⟩ : syracuseStep 3922597 = 735487) (by norm_num)
theorem B5230129 : Blo 2065435 5230129 := bstep (se 2 (by rfl) ⟨1961298, by rfl⟩ : syracuseStep 5230129 = 3922597) B3922597
theorem B6973505 : Blo 2065435 6973505 := bstep (se 2 (by rfl) ⟨2615064, by rfl⟩ : syracuseStep 6973505 = 5230129) B5230129
theorem B4649003 : Blo 2065435 4649003 := bstep (se 1 (by rfl) ⟨3486752, by rfl⟩ : syracuseStep 4649003 = 6973505) B6973505
theorem B3099335 : Blo 2065435 3099335 := bstep (se 1 (by rfl) ⟨2324501, by rfl⟩ : syracuseStep 3099335 = 4649003) B4649003
theorem B2066223 : Blo 2065435 2066223 := bstep (se 1 (by rfl) ⟨1549667, by rfl⟩ : syracuseStep 2066223 = 3099335) B3099335
theorem B3099341 : Blo 2065435 3099341 := bbase (se 3 (by rfl) ⟨581126, by rfl⟩ : syracuseStep 3099341 = 1162253) (by norm_num)
theorem B2066227 : Blo 2065435 2066227 := bstep (se 1 (by rfl) ⟨1549670, by rfl⟩ : syracuseStep 2066227 = 3099341) B3099341
theorem B4649021 : Blo 2065435 4649021 := bbase (se 3 (by rfl) ⟨871691, by rfl⟩ : syracuseStep 4649021 = 1743383) (by norm_num)
theorem B3099347 : Blo 2065435 3099347 := bstep (se 1 (by rfl) ⟨2324510, by rfl⟩ : syracuseStep 3099347 = 4649021) B4649021
theorem B2066231 : Blo 2065435 2066231 := bstep (se 1 (by rfl) ⟨1549673, by rfl⟩ : syracuseStep 2066231 = 3099347) B3099347
theorem B3486773 : Blo 2065435 3486773 := bbase (se 5 (by rfl) ⟨163442, by rfl⟩ : syracuseStep 3486773 = 326885) (by norm_num)
theorem B2324515 : Blo 2065435 2324515 := bstep (se 1 (by rfl) ⟨1743386, by rfl⟩ : syracuseStep 2324515 = 3486773) B3486773
theorem B3099353 : Blo 2065435 3099353 := bstep (se 2 (by rfl) ⟨1162257, by rfl⟩ : syracuseStep 3099353 = 2324515) B2324515
theorem B2066235 : Blo 2065435 2066235 := bstep (se 1 (by rfl) ⟨1549676, by rfl⟩ : syracuseStep 2066235 = 3099353) B3099353
theorem B5883941 : Blo 2065435 5883941 := bbase (se 4 (by rfl) ⟨551619, by rfl⟩ : syracuseStep 5883941 = 1103239) (by norm_num)
theorem B15690509 : Blo 2065435 15690509 := bstep (se 3 (by rfl) ⟨2941970, by rfl⟩ : syracuseStep 15690509 = 5883941) B5883941
theorem B10460339 : Blo 2065435 10460339 := bstep (se 1 (by rfl) ⟨7845254, by rfl⟩ : syracuseStep 10460339 = 15690509) B15690509
theorem B6973559 : Blo 2065435 6973559 := bstep (se 1 (by rfl) ⟨5230169, by rfl⟩ : syracuseStep 6973559 = 10460339) B10460339
theorem B4649039 : Blo 2065435 4649039 := bstep (se 1 (by rfl) ⟨3486779, by rfl⟩ : syracuseStep 4649039 = 6973559) B6973559
theorem B3099359 : Blo 2065435 3099359 := bstep (se 1 (by rfl) ⟨2324519, by rfl⟩ : syracuseStep 3099359 = 4649039) B4649039
theorem B2066239 : Blo 2065435 2066239 := bstep (se 1 (by rfl) ⟨1549679, by rfl⟩ : syracuseStep 2066239 = 3099359) B3099359
theorem B3099365 : Blo 2065435 3099365 := bbase (se 4 (by rfl) ⟨290565, by rfl⟩ : syracuseStep 3099365 = 581131) (by norm_num)
theorem B2066243 : Blo 2065435 2066243 := bstep (se 1 (by rfl) ⟨1549682, by rfl⟩ : syracuseStep 2066243 = 3099365) B3099365
theorem B4964597 : Blo 2065435 4964597 := bbase (se 5 (by rfl) ⟨232715, by rfl⟩ : syracuseStep 4964597 = 465431) (by norm_num)
theorem B3309731 : Blo 2065435 3309731 := bstep (se 1 (by rfl) ⟨2482298, by rfl⟩ : syracuseStep 3309731 = 4964597) B4964597
theorem B2206487 : Blo 2065435 2206487 := bstep (se 1 (by rfl) ⟨1654865, by rfl⟩ : syracuseStep 2206487 = 3309731) B3309731
theorem B5883965 : Blo 2065435 5883965 := bstep (se 3 (by rfl) ⟨1103243, by rfl⟩ : syracuseStep 5883965 = 2206487) B2206487
theorem B3922643 : Blo 2065435 3922643 := bstep (se 1 (by rfl) ⟨2941982, by rfl⟩ : syracuseStep 3922643 = 5883965) B5883965
theorem B2615095 : Blo 2065435 2615095 := bstep (se 1 (by rfl) ⟨1961321, by rfl⟩ : syracuseStep 2615095 = 3922643) B3922643
theorem B3486793 : Blo 2065435 3486793 := bstep (se 2 (by rfl) ⟨1307547, by rfl⟩ : syracuseStep 3486793 = 2615095) B2615095
theorem B4649057 : Blo 2065435 4649057 := bstep (se 2 (by rfl) ⟨1743396, by rfl⟩ : syracuseStep 4649057 = 3486793) B3486793
theorem B3099371 : Blo 2065435 3099371 := bstep (se 1 (by rfl) ⟨2324528, by rfl⟩ : syracuseStep 3099371 = 4649057) B4649057
theorem B2066247 : Blo 2065435 2066247 := bstep (se 1 (by rfl) ⟨1549685, by rfl⟩ : syracuseStep 2066247 = 3099371) B3099371
theorem B2324533 : Blo 2065435 2324533 := bbase (se 5 (by rfl) ⟨108962, by rfl⟩ : syracuseStep 2324533 = 217925) (by norm_num)
theorem B3099377 : Blo 2065435 3099377 := bstep (se 2 (by rfl) ⟨1162266, by rfl⟩ : syracuseStep 3099377 = 2324533) B2324533
theorem B2066251 : Blo 2065435 2066251 := bstep (se 1 (by rfl) ⟨1549688, by rfl⟩ : syracuseStep 2066251 = 3099377) B3099377
theorem B2615105 : Blo 2065435 2615105 := bbase (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) (by norm_num)
theorem B6973613 : Blo 2065435 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B4649075 : Blo 2065435 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B3099383 : Blo 2065435 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B2066255 : Blo 2065435 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B3099389 : Blo 2065435 3099389 := bbase (se 3 (by rfl) ⟨581135, by rfl⟩ : syracuseStep 3099389 = 1162271) (by norm_num)
theorem B2066259 : Blo 2065435 2066259 := bstep (se 1 (by rfl) ⟨1549694, by rfl⟩ : syracuseStep 2066259 = 3099389) B3099389
theorem B4649093 : Blo 2065435 4649093 := bbase (se 4 (by rfl) ⟨435852, by rfl⟩ : syracuseStep 4649093 = 871705) (by norm_num)
theorem B3099395 : Blo 2065435 3099395 := bstep (se 1 (by rfl) ⟨2324546, by rfl⟩ : syracuseStep 3099395 = 4649093) B4649093
theorem B2066263 : Blo 2065435 2066263 := bstep (se 1 (by rfl) ⟨1549697, by rfl⟩ : syracuseStep 2066263 = 3099395) B3099395
theorem B4964645 : Blo 2065435 4964645 := bbase (se 4 (by rfl) ⟨465435, by rfl⟩ : syracuseStep 4964645 = 930871) (by norm_num)
theorem B3309763 : Blo 2065435 3309763 := bstep (se 1 (by rfl) ⟨2482322, by rfl⟩ : syracuseStep 3309763 = 4964645) B4964645
theorem B4413017 : Blo 2065435 4413017 := bstep (se 2 (by rfl) ⟨1654881, by rfl⟩ : syracuseStep 4413017 = 3309763) B3309763
theorem B2942011 : Blo 2065435 2942011 := bstep (se 1 (by rfl) ⟨2206508, by rfl⟩ : syracuseStep 2942011 = 4413017) B4413017
theorem B3922681 : Blo 2065435 3922681 := bstep (se 2 (by rfl) ⟨1471005, by rfl⟩ : syracuseStep 3922681 = 2942011) B2942011
theorem B5230241 : Blo 2065435 5230241 := bstep (se 2 (by rfl) ⟨1961340, by rfl⟩ : syracuseStep 5230241 = 3922681) B3922681
theorem B3486827 : Blo 2065435 3486827 := bstep (se 1 (by rfl) ⟨2615120, by rfl⟩ : syracuseStep 3486827 = 5230241) B5230241
theorem B2324551 : Blo 2065435 2324551 := bstep (se 1 (by rfl) ⟨1743413, by rfl⟩ : syracuseStep 2324551 = 3486827) B3486827
theorem B3099401 : Blo 2065435 3099401 := bstep (se 2 (by rfl) ⟨1162275, by rfl⟩ : syracuseStep 3099401 = 2324551) B2324551
theorem B2066267 : Blo 2065435 2066267 := bstep (se 1 (by rfl) ⟨1549700, by rfl⟩ : syracuseStep 2066267 = 3099401) B3099401
theorem B10460501 : Blo 2065435 10460501 := bbase (se 11 (by rfl) ⟨7661, by rfl⟩ : syracuseStep 10460501 = 15323) (by norm_num)
theorem B6973667 : Blo 2065435 6973667 := bstep (se 1 (by rfl) ⟨5230250, by rfl⟩ : syracuseStep 6973667 = 10460501) B10460501
theorem B4649111 : Blo 2065435 4649111 := bstep (se 1 (by rfl) ⟨3486833, by rfl⟩ : syracuseStep 4649111 = 6973667) B6973667
theorem B3099407 : Blo 2065435 3099407 := bstep (se 1 (by rfl) ⟨2324555, by rfl⟩ : syracuseStep 3099407 = 4649111) B4649111
theorem B2066271 : Blo 2065435 2066271 := bstep (se 1 (by rfl) ⟨1549703, by rfl⟩ : syracuseStep 2066271 = 3099407) B3099407
theorem B3099413 : Blo 2065435 3099413 := bbase (se 6 (by rfl) ⟨72642, by rfl⟩ : syracuseStep 3099413 = 145285) (by norm_num)
theorem B2066275 : Blo 2065435 2066275 := bstep (se 1 (by rfl) ⟨1549706, by rfl⟩ : syracuseStep 2066275 = 3099413) B3099413
theorem B28661141 : Blo 2065435 28661141 := bbase (se 6 (by rfl) ⟨671745, by rfl⟩ : syracuseStep 28661141 = 1343491) (by norm_num)
theorem B19107427 : Blo 2065435 19107427 := bstep (se 1 (by rfl) ⟨14330570, by rfl⟩ : syracuseStep 19107427 = 28661141) B28661141
theorem B25476569 : Blo 2065435 25476569 := bstep (se 2 (by rfl) ⟨9553713, by rfl⟩ : syracuseStep 25476569 = 19107427) B19107427
theorem B16984379 : Blo 2065435 16984379 := bstep (se 1 (by rfl) ⟨12738284, by rfl⟩ : syracuseStep 16984379 = 25476569) B25476569
theorem B11322919 : Blo 2065435 11322919 := bstep (se 1 (by rfl) ⟨8492189, by rfl⟩ : syracuseStep 11322919 = 16984379) B16984379
theorem B15097225 : Blo 2065435 15097225 := bstep (se 2 (by rfl) ⟨5661459, by rfl⟩ : syracuseStep 15097225 = 11322919) B11322919
theorem B20129633 : Blo 2065435 20129633 := bstep (se 2 (by rfl) ⟨7548612, by rfl⟩ : syracuseStep 20129633 = 15097225) B15097225
theorem B13419755 : Blo 2065435 13419755 := bstep (se 1 (by rfl) ⟨10064816, by rfl⟩ : syracuseStep 13419755 = 20129633) B20129633
theorem B8946503 : Blo 2065435 8946503 := bstep (se 1 (by rfl) ⟨6709877, by rfl⟩ : syracuseStep 8946503 = 13419755) B13419755
theorem B5964335 : Blo 2065435 5964335 := bstep (se 1 (by rfl) ⟨4473251, by rfl⟩ : syracuseStep 5964335 = 8946503) B8946503
theorem B3976223 : Blo 2065435 3976223 := bstep (se 1 (by rfl) ⟨2982167, by rfl⟩ : syracuseStep 3976223 = 5964335) B5964335
theorem B10603261 : Blo 2065435 10603261 := bstep (se 3 (by rfl) ⟨1988111, by rfl⟩ : syracuseStep 10603261 = 3976223) B3976223
theorem B14137681 : Blo 2065435 14137681 := bstep (se 2 (by rfl) ⟨5301630, by rfl⟩ : syracuseStep 14137681 = 10603261) B10603261
theorem B18850241 : Blo 2065435 18850241 := bstep (se 2 (by rfl) ⟨7068840, by rfl⟩ : syracuseStep 18850241 = 14137681) B14137681
theorem B12566827 : Blo 2065435 12566827 := bstep (se 1 (by rfl) ⟨9425120, by rfl⟩ : syracuseStep 12566827 = 18850241) B18850241
theorem B16755769 : Blo 2065435 16755769 := bstep (se 2 (by rfl) ⟨6283413, by rfl⟩ : syracuseStep 16755769 = 12566827) B12566827
theorem B22341025 : Blo 2065435 22341025 := bstep (se 2 (by rfl) ⟨8377884, by rfl⟩ : syracuseStep 22341025 = 16755769) B16755769
theorem B29788033 : Blo 2065435 29788033 := bstep (se 2 (by rfl) ⟨11170512, by rfl⟩ : syracuseStep 29788033 = 22341025) B22341025
theorem B39717377 : Blo 2065435 39717377 := bstep (se 2 (by rfl) ⟨14894016, by rfl⟩ : syracuseStep 39717377 = 29788033) B29788033
theorem B26478251 : Blo 2065435 26478251 := bstep (se 1 (by rfl) ⟨19858688, by rfl⟩ : syracuseStep 26478251 = 39717377) B39717377
theorem B17652167 : Blo 2065435 17652167 := bstep (se 1 (by rfl) ⟨13239125, by rfl⟩ : syracuseStep 17652167 = 26478251) B26478251
theorem B11768111 : Blo 2065435 11768111 := bstep (se 1 (by rfl) ⟨8826083, by rfl⟩ : syracuseStep 11768111 = 17652167) B17652167
theorem B7845407 : Blo 2065435 7845407 := bstep (se 1 (by rfl) ⟨5884055, by rfl⟩ : syracuseStep 7845407 = 11768111) B11768111
theorem B5230271 : Blo 2065435 5230271 := bstep (se 1 (by rfl) ⟨3922703, by rfl⟩ : syracuseStep 5230271 = 7845407) B7845407
theorem B3486847 : Blo 2065435 3486847 := bstep (se 1 (by rfl) ⟨2615135, by rfl⟩ : syracuseStep 3486847 = 5230271) B5230271
theorem B4649129 : Blo 2065435 4649129 := bstep (se 2 (by rfl) ⟨1743423, by rfl⟩ : syracuseStep 4649129 = 3486847) B3486847
theorem B3099419 : Blo 2065435 3099419 := bstep (se 1 (by rfl) ⟨2324564, by rfl⟩ : syracuseStep 3099419 = 4649129) B4649129
theorem B2066279 : Blo 2065435 2066279 := bstep (se 1 (by rfl) ⟨1549709, by rfl⟩ : syracuseStep 2066279 = 3099419) B3099419
theorem B2324569 : Blo 2065435 2324569 := bbase (se 2 (by rfl) ⟨871713, by rfl⟩ : syracuseStep 2324569 = 1743427) (by norm_num)
theorem B3099425 : Blo 2065435 3099425 := bstep (se 2 (by rfl) ⟨1162284, by rfl⟩ : syracuseStep 3099425 = 2324569) B2324569
theorem B2066283 : Blo 2065435 2066283 := bstep (se 1 (by rfl) ⟨1549712, by rfl⟩ : syracuseStep 2066283 = 3099425) B3099425
theorem B6619589 : Blo 2065435 6619589 := bbase (se 4 (by rfl) ⟨620586, by rfl⟩ : syracuseStep 6619589 = 1241173) (by norm_num)
theorem B4413059 : Blo 2065435 4413059 := bstep (se 1 (by rfl) ⟨3309794, by rfl⟩ : syracuseStep 4413059 = 6619589) B6619589
theorem B2942039 : Blo 2065435 2942039 := bstep (se 1 (by rfl) ⟨2206529, by rfl⟩ : syracuseStep 2942039 = 4413059) B4413059
theorem B7845437 : Blo 2065435 7845437 := bstep (se 3 (by rfl) ⟨1471019, by rfl⟩ : syracuseStep 7845437 = 2942039) B2942039
theorem B5230291 : Blo 2065435 5230291 := bstep (se 1 (by rfl) ⟨3922718, by rfl⟩ : syracuseStep 5230291 = 7845437) B7845437
theorem B6973721 : Blo 2065435 6973721 := bstep (se 2 (by rfl) ⟨2615145, by rfl⟩ : syracuseStep 6973721 = 5230291) B5230291
theorem B4649147 : Blo 2065435 4649147 := bstep (se 1 (by rfl) ⟨3486860, by rfl⟩ : syracuseStep 4649147 = 6973721) B6973721
theorem B3099431 : Blo 2065435 3099431 := bstep (se 1 (by rfl) ⟨2324573, by rfl⟩ : syracuseStep 3099431 = 4649147) B4649147
theorem B2066287 : Blo 2065435 2066287 := bstep (se 1 (by rfl) ⟨1549715, by rfl⟩ : syracuseStep 2066287 = 3099431) B3099431
theorem B3099437 : Blo 2065435 3099437 := bbase (se 3 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 3099437 = 1162289) (by norm_num)
theorem B2066291 : Blo 2065435 2066291 := bstep (se 1 (by rfl) ⟨1549718, by rfl⟩ : syracuseStep 2066291 = 3099437) B3099437
theorem B4649165 : Blo 2065435 4649165 := bbase (se 3 (by rfl) ⟨871718, by rfl⟩ : syracuseStep 4649165 = 1743437) (by norm_num)
theorem B3099443 : Blo 2065435 3099443 := bstep (se 1 (by rfl) ⟨2324582, by rfl⟩ : syracuseStep 3099443 = 4649165) B4649165
theorem B2066295 : Blo 2065435 2066295 := bstep (se 1 (by rfl) ⟨1549721, by rfl⟩ : syracuseStep 2066295 = 3099443) B3099443
theorem B2615161 : Blo 2065435 2615161 := bbase (se 2 (by rfl) ⟨980685, by rfl⟩ : syracuseStep 2615161 = 1961371) (by norm_num)
theorem B3486881 : Blo 2065435 3486881 := bstep (se 2 (by rfl) ⟨1307580, by rfl⟩ : syracuseStep 3486881 = 2615161) B2615161
theorem B2324587 : Blo 2065435 2324587 := bstep (se 1 (by rfl) ⟨1743440, by rfl⟩ : syracuseStep 2324587 = 3486881) B3486881
theorem B3099449 : Blo 2065435 3099449 := bstep (se 2 (by rfl) ⟨1162293, by rfl⟩ : syracuseStep 3099449 = 2324587) B2324587
theorem B2066299 : Blo 2065435 2066299 := bstep (se 1 (by rfl) ⟨1549724, by rfl⟩ : syracuseStep 2066299 = 3099449) B3099449
theorem B22646101 : Blo 2065435 22646101 := bbase (se 11 (by rfl) ⟨16586, by rfl⟩ : syracuseStep 22646101 = 33173) (by norm_num)
theorem B30194801 : Blo 2065435 30194801 := bstep (se 2 (by rfl) ⟨11323050, by rfl⟩ : syracuseStep 30194801 = 22646101) B22646101
theorem B20129867 : Blo 2065435 20129867 := bstep (se 1 (by rfl) ⟨15097400, by rfl⟩ : syracuseStep 20129867 = 30194801) B30194801
theorem B13419911 : Blo 2065435 13419911 := bstep (se 1 (by rfl) ⟨10064933, by rfl⟩ : syracuseStep 13419911 = 20129867) B20129867
theorem B8946607 : Blo 2065435 8946607 := bstep (se 1 (by rfl) ⟨6709955, by rfl⟩ : syracuseStep 8946607 = 13419911) B13419911
theorem B11928809 : Blo 2065435 11928809 := bstep (se 2 (by rfl) ⟨4473303, by rfl⟩ : syracuseStep 11928809 = 8946607) B8946607
theorem B31810157 : Blo 2065435 31810157 := bstep (se 3 (by rfl) ⟨5964404, by rfl⟩ : syracuseStep 31810157 = 11928809) B11928809
theorem B21206771 : Blo 2065435 21206771 := bstep (se 1 (by rfl) ⟨15905078, by rfl⟩ : syracuseStep 21206771 = 31810157) B31810157
theorem B14137847 : Blo 2065435 14137847 := bstep (se 1 (by rfl) ⟨10603385, by rfl⟩ : syracuseStep 14137847 = 21206771) B21206771
theorem B9425231 : Blo 2065435 9425231 := bstep (se 1 (by rfl) ⟨7068923, by rfl⟩ : syracuseStep 9425231 = 14137847) B14137847
theorem B6283487 : Blo 2065435 6283487 := bstep (se 1 (by rfl) ⟨4712615, by rfl⟩ : syracuseStep 6283487 = 9425231) B9425231
theorem B4188991 : Blo 2065435 4188991 := bstep (se 1 (by rfl) ⟨3141743, by rfl⟩ : syracuseStep 4188991 = 6283487) B6283487
theorem B5585321 : Blo 2065435 5585321 := bstep (se 2 (by rfl) ⟨2094495, by rfl⟩ : syracuseStep 5585321 = 4188991) B4188991
theorem B14894189 : Blo 2065435 14894189 := bstep (se 3 (by rfl) ⟨2792660, by rfl⟩ : syracuseStep 14894189 = 5585321) B5585321
theorem B9929459 : Blo 2065435 9929459 := bstep (se 1 (by rfl) ⟨7447094, by rfl⟩ : syracuseStep 9929459 = 14894189) B14894189
theorem B6619639 : Blo 2065435 6619639 := bstep (se 1 (by rfl) ⟨4964729, by rfl⟩ : syracuseStep 6619639 = 9929459) B9929459
theorem B8826185 : Blo 2065435 8826185 := bstep (se 2 (by rfl) ⟨3309819, by rfl⟩ : syracuseStep 8826185 = 6619639) B6619639
theorem B23536493 : Blo 2065435 23536493 := bstep (se 3 (by rfl) ⟨4413092, by rfl⟩ : syracuseStep 23536493 = 8826185) B8826185
theorem B15690995 : Blo 2065435 15690995 := bstep (se 1 (by rfl) ⟨11768246, by rfl⟩ : syracuseStep 15690995 = 23536493) B23536493
theorem B10460663 : Blo 2065435 10460663 := bstep (se 1 (by rfl) ⟨7845497, by rfl⟩ : syracuseStep 10460663 = 15690995) B15690995
theorem B6973775 : Blo 2065435 6973775 := bstep (se 1 (by rfl) ⟨5230331, by rfl⟩ : syracuseStep 6973775 = 10460663) B10460663
theorem B4649183 : Blo 2065435 4649183 := bstep (se 1 (by rfl) ⟨3486887, by rfl⟩ : syracuseStep 4649183 = 6973775) B6973775
theorem B3099455 : Blo 2065435 3099455 := bstep (se 1 (by rfl) ⟨2324591, by rfl⟩ : syracuseStep 3099455 = 4649183) B4649183
theorem B2066303 : Blo 2065435 2066303 := bstep (se 1 (by rfl) ⟨1549727, by rfl⟩ : syracuseStep 2066303 = 3099455) B3099455
theorem B3099461 : Blo 2065435 3099461 := bbase (se 4 (by rfl) ⟨290574, by rfl⟩ : syracuseStep 3099461 = 581149) (by norm_num)
theorem B2066307 : Blo 2065435 2066307 := bstep (se 1 (by rfl) ⟨1549730, by rfl⟩ : syracuseStep 2066307 = 3099461) B3099461
theorem B3486901 : Blo 2065435 3486901 := bbase (se 5 (by rfl) ⟨163448, by rfl⟩ : syracuseStep 3486901 = 326897) (by norm_num)
theorem B4649201 : Blo 2065435 4649201 := bstep (se 2 (by rfl) ⟨1743450, by rfl⟩ : syracuseStep 4649201 = 3486901) B3486901
theorem B3099467 : Blo 2065435 3099467 := bstep (se 1 (by rfl) ⟨2324600, by rfl⟩ : syracuseStep 3099467 = 4649201) B4649201
theorem B2066311 : Blo 2065435 2066311 := bstep (se 1 (by rfl) ⟨1549733, by rfl⟩ : syracuseStep 2066311 = 3099467) B3099467
theorem B2324605 : Blo 2065435 2324605 := bbase (se 3 (by rfl) ⟨435863, by rfl⟩ : syracuseStep 2324605 = 871727) (by norm_num)
theorem B3099473 : Blo 2065435 3099473 := bstep (se 2 (by rfl) ⟨1162302, by rfl⟩ : syracuseStep 3099473 = 2324605) B2324605
theorem B2066315 : Blo 2065435 2066315 := bstep (se 1 (by rfl) ⟨1549736, by rfl⟩ : syracuseStep 2066315 = 3099473) B3099473
theorem B6973829 : Blo 2065435 6973829 := bbase (se 4 (by rfl) ⟨653796, by rfl⟩ : syracuseStep 6973829 = 1307593) (by norm_num)
theorem B4649219 : Blo 2065435 4649219 := bstep (se 1 (by rfl) ⟨3486914, by rfl⟩ : syracuseStep 4649219 = 6973829) B6973829
theorem B3099479 : Blo 2065435 3099479 := bstep (se 1 (by rfl) ⟨2324609, by rfl⟩ : syracuseStep 3099479 = 4649219) B4649219
theorem B2066319 : Blo 2065435 2066319 := bstep (se 1 (by rfl) ⟨1549739, by rfl⟩ : syracuseStep 2066319 = 3099479) B3099479
theorem B3099485 : Blo 2065435 3099485 := bbase (se 3 (by rfl) ⟨581153, by rfl⟩ : syracuseStep 3099485 = 1162307) (by norm_num)
theorem B2066323 : Blo 2065435 2066323 := bstep (se 1 (by rfl) ⟨1549742, by rfl⟩ : syracuseStep 2066323 = 3099485) B3099485
theorem B4649237 : Blo 2065435 4649237 := bbase (se 6 (by rfl) ⟨108966, by rfl⟩ : syracuseStep 4649237 = 217933) (by norm_num)
theorem B3099491 : Blo 2065435 3099491 := bstep (se 1 (by rfl) ⟨2324618, by rfl⟩ : syracuseStep 3099491 = 4649237) B4649237
theorem B2066327 : Blo 2065435 2066327 := bstep (se 1 (by rfl) ⟨1549745, by rfl⟩ : syracuseStep 2066327 = 3099491) B3099491
theorem B7845605 : Blo 2065435 7845605 := bbase (se 4 (by rfl) ⟨735525, by rfl⟩ : syracuseStep 7845605 = 1471051) (by norm_num)
theorem B5230403 : Blo 2065435 5230403 := bstep (se 1 (by rfl) ⟨3922802, by rfl⟩ : syracuseStep 5230403 = 7845605) B7845605
theorem B3486935 : Blo 2065435 3486935 := bstep (se 1 (by rfl) ⟨2615201, by rfl⟩ : syracuseStep 3486935 = 5230403) B5230403
theorem B2324623 : Blo 2065435 2324623 := bstep (se 1 (by rfl) ⟨1743467, by rfl⟩ : syracuseStep 2324623 = 3486935) B3486935
theorem B3099497 : Blo 2065435 3099497 := bstep (se 2 (by rfl) ⟨1162311, by rfl⟩ : syracuseStep 3099497 = 2324623) B2324623
theorem B2066331 : Blo 2065435 2066331 := bstep (se 1 (by rfl) ⟨1549748, by rfl⟩ : syracuseStep 2066331 = 3099497) B3099497
theorem B3534517 : Blo 2065435 3534517 := bbase (se 5 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 3534517 = 331361) (by norm_num)
theorem B4712689 : Blo 2065435 4712689 := bstep (se 2 (by rfl) ⟨1767258, by rfl⟩ : syracuseStep 4712689 = 3534517) B3534517
theorem B6283585 : Blo 2065435 6283585 := bstep (se 2 (by rfl) ⟨2356344, by rfl⟩ : syracuseStep 6283585 = 4712689) B4712689
theorem B8378113 : Blo 2065435 8378113 := bstep (se 2 (by rfl) ⟨3141792, by rfl⟩ : syracuseStep 8378113 = 6283585) B6283585
theorem B11170817 : Blo 2065435 11170817 := bstep (se 2 (by rfl) ⟨4189056, by rfl⟩ : syracuseStep 11170817 = 8378113) B8378113
theorem B7447211 : Blo 2065435 7447211 := bstep (se 1 (by rfl) ⟨5585408, by rfl⟩ : syracuseStep 7447211 = 11170817) B11170817
theorem B4964807 : Blo 2065435 4964807 := bstep (se 1 (by rfl) ⟨3723605, by rfl⟩ : syracuseStep 4964807 = 7447211) B7447211
theorem B3309871 : Blo 2065435 3309871 := bstep (se 1 (by rfl) ⟨2482403, by rfl⟩ : syracuseStep 3309871 = 4964807) B4964807
theorem B4413161 : Blo 2065435 4413161 := bstep (se 2 (by rfl) ⟨1654935, by rfl⟩ : syracuseStep 4413161 = 3309871) B3309871
theorem B11768429 : Blo 2065435 11768429 := bstep (se 3 (by rfl) ⟨2206580, by rfl⟩ : syracuseStep 11768429 = 4413161) B4413161
theorem B7845619 : Blo 2065435 7845619 := bstep (se 1 (by rfl) ⟨5884214, by rfl⟩ : syracuseStep 7845619 = 11768429) B11768429
theorem B10460825 : Blo 2065435 10460825 := bstep (se 2 (by rfl) ⟨3922809, by rfl⟩ : syracuseStep 10460825 = 7845619) B7845619
theorem B6973883 : Blo 2065435 6973883 := bstep (se 1 (by rfl) ⟨5230412, by rfl⟩ : syracuseStep 6973883 = 10460825) B10460825
theorem B4649255 : Blo 2065435 4649255 := bstep (se 1 (by rfl) ⟨3486941, by rfl⟩ : syracuseStep 4649255 = 6973883) B6973883
theorem B3099503 : Blo 2065435 3099503 := bstep (se 1 (by rfl) ⟨2324627, by rfl⟩ : syracuseStep 3099503 = 4649255) B4649255
theorem B2066335 : Blo 2065435 2066335 := bstep (se 1 (by rfl) ⟨1549751, by rfl⟩ : syracuseStep 2066335 = 3099503) B3099503
theorem B3099509 : Blo 2065435 3099509 := bbase (se 5 (by rfl) ⟨145289, by rfl⟩ : syracuseStep 3099509 = 290579) (by norm_num)
theorem B2066339 : Blo 2065435 2066339 := bstep (se 1 (by rfl) ⟨1549754, by rfl⟩ : syracuseStep 2066339 = 3099509) B3099509
theorem B12567221 : Blo 2065435 12567221 := bbase (se 5 (by rfl) ⟨589088, by rfl⟩ : syracuseStep 12567221 = 1178177) (by norm_num)
theorem B8378147 : Blo 2065435 8378147 := bstep (se 1 (by rfl) ⟨6283610, by rfl⟩ : syracuseStep 8378147 = 12567221) B12567221
theorem B5585431 : Blo 2065435 5585431 := bstep (se 1 (by rfl) ⟨4189073, by rfl⟩ : syracuseStep 5585431 = 8378147) B8378147
theorem B7447241 : Blo 2065435 7447241 := bstep (se 2 (by rfl) ⟨2792715, by rfl⟩ : syracuseStep 7447241 = 5585431) B5585431
theorem B4964827 : Blo 2065435 4964827 := bstep (se 1 (by rfl) ⟨3723620, by rfl⟩ : syracuseStep 4964827 = 7447241) B7447241
theorem B6619769 : Blo 2065435 6619769 := bstep (se 2 (by rfl) ⟨2482413, by rfl⟩ : syracuseStep 6619769 = 4964827) B4964827
theorem B4413179 : Blo 2065435 4413179 := bstep (se 1 (by rfl) ⟨3309884, by rfl⟩ : syracuseStep 4413179 = 6619769) B6619769
theorem B2942119 : Blo 2065435 2942119 := bstep (se 1 (by rfl) ⟨2206589, by rfl⟩ : syracuseStep 2942119 = 4413179) B4413179
theorem B3922825 : Blo 2065435 3922825 := bstep (se 2 (by rfl) ⟨1471059, by rfl⟩ : syracuseStep 3922825 = 2942119) B2942119
theorem B5230433 : Blo 2065435 5230433 := bstep (se 2 (by rfl) ⟨1961412, by rfl⟩ : syracuseStep 5230433 = 3922825) B3922825
theorem B3486955 : Blo 2065435 3486955 := bstep (se 1 (by rfl) ⟨2615216, by rfl⟩ : syracuseStep 3486955 = 5230433) B5230433
theorem B4649273 : Blo 2065435 4649273 := bstep (se 2 (by rfl) ⟨1743477, by rfl⟩ : syracuseStep 4649273 = 3486955) B3486955
theorem B3099515 : Blo 2065435 3099515 := bstep (se 1 (by rfl) ⟨2324636, by rfl⟩ : syracuseStep 3099515 = 4649273) B4649273
theorem B2066343 : Blo 2065435 2066343 := bstep (se 1 (by rfl) ⟨1549757, by rfl⟩ : syracuseStep 2066343 = 3099515) B3099515
theorem B2324641 : Blo 2065435 2324641 := bbase (se 2 (by rfl) ⟨871740, by rfl⟩ : syracuseStep 2324641 = 1743481) (by norm_num)
theorem B3099521 : Blo 2065435 3099521 := bstep (se 2 (by rfl) ⟨1162320, by rfl⟩ : syracuseStep 3099521 = 2324641) B2324641
theorem B2066347 : Blo 2065435 2066347 := bstep (se 1 (by rfl) ⟨1549760, by rfl⟩ : syracuseStep 2066347 = 3099521) B3099521
theorem B5230453 : Blo 2065435 5230453 := bbase (se 5 (by rfl) ⟨245177, by rfl⟩ : syracuseStep 5230453 = 490355) (by norm_num)
theorem B6973937 : Blo 2065435 6973937 := bstep (se 2 (by rfl) ⟨2615226, by rfl⟩ : syracuseStep 6973937 = 5230453) B5230453
theorem B4649291 : Blo 2065435 4649291 := bstep (se 1 (by rfl) ⟨3486968, by rfl⟩ : syracuseStep 4649291 = 6973937) B6973937
theorem B3099527 : Blo 2065435 3099527 := bstep (se 1 (by rfl) ⟨2324645, by rfl⟩ : syracuseStep 3099527 = 4649291) B4649291
theorem B2066351 : Blo 2065435 2066351 := bstep (se 1 (by rfl) ⟨1549763, by rfl⟩ : syracuseStep 2066351 = 3099527) B3099527
theorem B3099533 : Blo 2065435 3099533 := bbase (se 3 (by rfl) ⟨581162, by rfl⟩ : syracuseStep 3099533 = 1162325) (by norm_num)
theorem B2066355 : Blo 2065435 2066355 := bstep (se 1 (by rfl) ⟨1549766, by rfl⟩ : syracuseStep 2066355 = 3099533) B3099533
theorem B4649309 : Blo 2065435 4649309 := bbase (se 3 (by rfl) ⟨871745, by rfl⟩ : syracuseStep 4649309 = 1743491) (by norm_num)
theorem B3099539 : Blo 2065435 3099539 := bstep (se 1 (by rfl) ⟨2324654, by rfl⟩ : syracuseStep 3099539 = 4649309) B4649309
theorem B2066359 : Blo 2065435 2066359 := bstep (se 1 (by rfl) ⟨1549769, by rfl⟩ : syracuseStep 2066359 = 3099539) B3099539
theorem B3486989 : Blo 2065435 3486989 := bbase (se 3 (by rfl) ⟨653810, by rfl⟩ : syracuseStep 3486989 = 1307621) (by norm_num)
theorem B2324659 : Blo 2065435 2324659 := bstep (se 1 (by rfl) ⟨1743494, by rfl⟩ : syracuseStep 2324659 = 3486989) B3486989
theorem B3099545 : Blo 2065435 3099545 := bstep (se 2 (by rfl) ⟨1162329, by rfl⟩ : syracuseStep 3099545 = 2324659) B2324659
theorem B2066363 : Blo 2065435 2066363 := bstep (se 1 (by rfl) ⟨1549772, by rfl⟩ : syracuseStep 2066363 = 3099545) B3099545
theorem B17652917 : Blo 2065435 17652917 := bbase (se 5 (by rfl) ⟨827480, by rfl⟩ : syracuseStep 17652917 = 1654961) (by norm_num)
theorem B11768611 : Blo 2065435 11768611 := bstep (se 1 (by rfl) ⟨8826458, by rfl⟩ : syracuseStep 11768611 = 17652917) B17652917
theorem B15691481 : Blo 2065435 15691481 := bstep (se 2 (by rfl) ⟨5884305, by rfl⟩ : syracuseStep 15691481 = 11768611) B11768611
theorem B10460987 : Blo 2065435 10460987 := bstep (se 1 (by rfl) ⟨7845740, by rfl⟩ : syracuseStep 10460987 = 15691481) B15691481
theorem B6973991 : Blo 2065435 6973991 := bstep (se 1 (by rfl) ⟨5230493, by rfl⟩ : syracuseStep 6973991 = 10460987) B10460987
theorem B4649327 : Blo 2065435 4649327 := bstep (se 1 (by rfl) ⟨3486995, by rfl⟩ : syracuseStep 4649327 = 6973991) B6973991
theorem B3099551 : Blo 2065435 3099551 := bstep (se 1 (by rfl) ⟨2324663, by rfl⟩ : syracuseStep 3099551 = 4649327) B4649327
theorem B2066367 : Blo 2065435 2066367 := bstep (se 1 (by rfl) ⟨1549775, by rfl⟩ : syracuseStep 2066367 = 3099551) B3099551
theorem B3099557 : Blo 2065435 3099557 := bbase (se 4 (by rfl) ⟨290583, by rfl⟩ : syracuseStep 3099557 = 581167) (by norm_num)
theorem B2066371 : Blo 2065435 2066371 := bstep (se 1 (by rfl) ⟨1549778, by rfl⟩ : syracuseStep 2066371 = 3099557) B3099557
theorem B2615257 : Blo 2065435 2615257 := bbase (se 2 (by rfl) ⟨980721, by rfl⟩ : syracuseStep 2615257 = 1961443) (by norm_num)
theorem B3487009 : Blo 2065435 3487009 := bstep (se 2 (by rfl) ⟨1307628, by rfl⟩ : syracuseStep 3487009 = 2615257) B2615257
theorem B4649345 : Blo 2065435 4649345 := bstep (se 2 (by rfl) ⟨1743504, by rfl⟩ : syracuseStep 4649345 = 3487009) B3487009
theorem B3099563 : Blo 2065435 3099563 := bstep (se 1 (by rfl) ⟨2324672, by rfl⟩ : syracuseStep 3099563 = 4649345) B4649345
theorem B2066375 : Blo 2065435 2066375 := bstep (se 1 (by rfl) ⟨1549781, by rfl⟩ : syracuseStep 2066375 = 3099563) B3099563
theorem B2324677 : Blo 2065435 2324677 := bbase (se 4 (by rfl) ⟨217938, by rfl⟩ : syracuseStep 2324677 = 435877) (by norm_num)
theorem B3099569 : Blo 2065435 3099569 := bstep (se 2 (by rfl) ⟨1162338, by rfl⟩ : syracuseStep 3099569 = 2324677) B2324677
theorem B2066379 : Blo 2065435 2066379 := bstep (se 1 (by rfl) ⟨1549784, by rfl⟩ : syracuseStep 2066379 = 3099569) B3099569
theorem B3922901 : Blo 2065435 3922901 := bbase (se 7 (by rfl) ⟨45971, by rfl⟩ : syracuseStep 3922901 = 91943) (by norm_num)
theorem B2615267 : Blo 2065435 2615267 := bstep (se 1 (by rfl) ⟨1961450, by rfl⟩ : syracuseStep 2615267 = 3922901) B3922901
theorem B6974045 : Blo 2065435 6974045 := bstep (se 3 (by rfl) ⟨1307633, by rfl⟩ : syracuseStep 6974045 = 2615267) B2615267
theorem B4649363 : Blo 2065435 4649363 := bstep (se 1 (by rfl) ⟨3487022, by rfl⟩ : syracuseStep 4649363 = 6974045) B6974045
theorem B3099575 : Blo 2065435 3099575 := bstep (se 1 (by rfl) ⟨2324681, by rfl⟩ : syracuseStep 3099575 = 4649363) B4649363
theorem B2066383 : Blo 2065435 2066383 := bstep (se 1 (by rfl) ⟨1549787, by rfl⟩ : syracuseStep 2066383 = 3099575) B3099575
theorem B3099581 : Blo 2065435 3099581 := bbase (se 3 (by rfl) ⟨581171, by rfl⟩ : syracuseStep 3099581 = 1162343) (by norm_num)
theorem B2066387 : Blo 2065435 2066387 := bstep (se 1 (by rfl) ⟨1549790, by rfl⟩ : syracuseStep 2066387 = 3099581) B3099581
theorem B4649381 : Blo 2065435 4649381 := bbase (se 4 (by rfl) ⟨435879, by rfl⟩ : syracuseStep 4649381 = 871759) (by norm_num)
theorem B3099587 : Blo 2065435 3099587 := bstep (se 1 (by rfl) ⟨2324690, by rfl⟩ : syracuseStep 3099587 = 4649381) B4649381
theorem B2066391 : Blo 2065435 2066391 := bstep (se 1 (by rfl) ⟨1549793, by rfl⟩ : syracuseStep 2066391 = 3099587) B3099587
theorem B5230565 : Blo 2065435 5230565 := bbase (se 4 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 5230565 = 980731) (by norm_num)
theorem B3487043 : Blo 2065435 3487043 := bstep (se 1 (by rfl) ⟨2615282, by rfl⟩ : syracuseStep 3487043 = 5230565) B5230565
theorem B2324695 : Blo 2065435 2324695 := bstep (se 1 (by rfl) ⟨1743521, by rfl⟩ : syracuseStep 2324695 = 3487043) B3487043
theorem B3099593 : Blo 2065435 3099593 := bstep (se 2 (by rfl) ⟨1162347, by rfl⟩ : syracuseStep 3099593 = 2324695) B2324695
theorem B2066395 : Blo 2065435 2066395 := bstep (se 1 (by rfl) ⟨1549796, by rfl⟩ : syracuseStep 2066395 = 3099593) B3099593
theorem B2206649 : Blo 2065435 2206649 := bbase (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) (by norm_num)
theorem B5884397 : Blo 2065435 5884397 := bstep (se 3 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 5884397 = 2206649) B2206649
theorem B3922931 : Blo 2065435 3922931 := bstep (se 1 (by rfl) ⟨2942198, by rfl⟩ : syracuseStep 3922931 = 5884397) B5884397
theorem B10461149 : Blo 2065435 10461149 := bstep (se 3 (by rfl) ⟨1961465, by rfl⟩ : syracuseStep 10461149 = 3922931) B3922931
theorem B6974099 : Blo 2065435 6974099 := bstep (se 1 (by rfl) ⟨5230574, by rfl⟩ : syracuseStep 6974099 = 10461149) B10461149
theorem B4649399 : Blo 2065435 4649399 := bstep (se 1 (by rfl) ⟨3487049, by rfl⟩ : syracuseStep 4649399 = 6974099) B6974099
theorem B3099599 : Blo 2065435 3099599 := bstep (se 1 (by rfl) ⟨2324699, by rfl⟩ : syracuseStep 3099599 = 4649399) B4649399
theorem B2066399 : Blo 2065435 2066399 := bstep (se 1 (by rfl) ⟨1549799, by rfl⟩ : syracuseStep 2066399 = 3099599) B3099599
theorem B3099605 : Blo 2065435 3099605 := bbase (se 7 (by rfl) ⟨36323, by rfl⟩ : syracuseStep 3099605 = 72647) (by norm_num)
theorem B2066403 : Blo 2065435 2066403 := bstep (se 1 (by rfl) ⟨1549802, by rfl⟩ : syracuseStep 2066403 = 3099605) B3099605
theorem B7845893 : Blo 2065435 7845893 := bbase (se 4 (by rfl) ⟨735552, by rfl⟩ : syracuseStep 7845893 = 1471105) (by norm_num)
theorem B5230595 : Blo 2065435 5230595 := bstep (se 1 (by rfl) ⟨3922946, by rfl⟩ : syracuseStep 5230595 = 7845893) B7845893
theorem B3487063 : Blo 2065435 3487063 := bstep (se 1 (by rfl) ⟨2615297, by rfl⟩ : syracuseStep 3487063 = 5230595) B5230595
theorem B4649417 : Blo 2065435 4649417 := bstep (se 2 (by rfl) ⟨1743531, by rfl⟩ : syracuseStep 4649417 = 3487063) B3487063
theorem B3099611 : Blo 2065435 3099611 := bstep (se 1 (by rfl) ⟨2324708, by rfl⟩ : syracuseStep 3099611 = 4649417) B4649417
theorem B2066407 : Blo 2065435 2066407 := bstep (se 1 (by rfl) ⟨1549805, by rfl⟩ : syracuseStep 2066407 = 3099611) B3099611
theorem B2324713 : Blo 2065435 2324713 := bbase (se 2 (by rfl) ⟨871767, by rfl⟩ : syracuseStep 2324713 = 1743535) (by norm_num)
theorem B3099617 : Blo 2065435 3099617 := bstep (se 2 (by rfl) ⟨1162356, by rfl⟩ : syracuseStep 3099617 = 2324713) B2324713
theorem B2066411 : Blo 2065435 2066411 := bstep (se 1 (by rfl) ⟨1549808, by rfl⟩ : syracuseStep 2066411 = 3099617) B3099617
theorem B11768885 : Blo 2065435 11768885 := bbase (se 5 (by rfl) ⟨551666, by rfl⟩ : syracuseStep 11768885 = 1103333) (by norm_num)
theorem B7845923 : Blo 2065435 7845923 := bstep (se 1 (by rfl) ⟨5884442, by rfl⟩ : syracuseStep 7845923 = 11768885) B11768885
theorem B5230615 : Blo 2065435 5230615 := bstep (se 1 (by rfl) ⟨3922961, by rfl⟩ : syracuseStep 5230615 = 7845923) B7845923
theorem B6974153 : Blo 2065435 6974153 := bstep (se 2 (by rfl) ⟨2615307, by rfl⟩ : syracuseStep 6974153 = 5230615) B5230615
theorem B4649435 : Blo 2065435 4649435 := bstep (se 1 (by rfl) ⟨3487076, by rfl⟩ : syracuseStep 4649435 = 6974153) B6974153
theorem B3099623 : Blo 2065435 3099623 := bstep (se 1 (by rfl) ⟨2324717, by rfl⟩ : syracuseStep 3099623 = 4649435) B4649435
theorem B2066415 : Blo 2065435 2066415 := bstep (se 1 (by rfl) ⟨1549811, by rfl⟩ : syracuseStep 2066415 = 3099623) B3099623
theorem B3099629 : Blo 2065435 3099629 := bbase (se 3 (by rfl) ⟨581180, by rfl⟩ : syracuseStep 3099629 = 1162361) (by norm_num)
theorem B2066419 : Blo 2065435 2066419 := bstep (se 1 (by rfl) ⟨1549814, by rfl⟩ : syracuseStep 2066419 = 3099629) B3099629
theorem B4649453 : Blo 2065435 4649453 := bbase (se 3 (by rfl) ⟨871772, by rfl⟩ : syracuseStep 4649453 = 1743545) (by norm_num)
theorem B3099635 : Blo 2065435 3099635 := bstep (se 1 (by rfl) ⟨2324726, by rfl⟩ : syracuseStep 3099635 = 4649453) B4649453
theorem B2066423 : Blo 2065435 2066423 := bstep (se 1 (by rfl) ⟨1549817, by rfl⟩ : syracuseStep 2066423 = 3099635) B3099635
theorem B11171317 : Blo 2065435 11171317 := bbase (se 5 (by rfl) ⟨523655, by rfl⟩ : syracuseStep 11171317 = 1047311) (by norm_num)
theorem B14895089 : Blo 2065435 14895089 := bstep (se 2 (by rfl) ⟨5585658, by rfl⟩ : syracuseStep 14895089 = 11171317) B11171317
theorem B9930059 : Blo 2065435 9930059 := bstep (se 1 (by rfl) ⟨7447544, by rfl⟩ : syracuseStep 9930059 = 14895089) B14895089
theorem B6620039 : Blo 2065435 6620039 := bstep (se 1 (by rfl) ⟨4965029, by rfl⟩ : syracuseStep 6620039 = 9930059) B9930059
theorem B4413359 : Blo 2065435 4413359 := bstep (se 1 (by rfl) ⟨3310019, by rfl⟩ : syracuseStep 4413359 = 6620039) B6620039
theorem B2942239 : Blo 2065435 2942239 := bstep (se 1 (by rfl) ⟨2206679, by rfl⟩ : syracuseStep 2942239 = 4413359) B4413359
theorem B3922985 : Blo 2065435 3922985 := bstep (se 2 (by rfl) ⟨1471119, by rfl⟩ : syracuseStep 3922985 = 2942239) B2942239
theorem B2615323 : Blo 2065435 2615323 := bstep (se 1 (by rfl) ⟨1961492, by rfl⟩ : syracuseStep 2615323 = 3922985) B3922985
theorem B3487097 : Blo 2065435 3487097 := bstep (se 2 (by rfl) ⟨1307661, by rfl⟩ : syracuseStep 3487097 = 2615323) B2615323
theorem B2324731 : Blo 2065435 2324731 := bstep (se 1 (by rfl) ⟨1743548, by rfl⟩ : syracuseStep 2324731 = 3487097) B3487097
theorem B3099641 : Blo 2065435 3099641 := bstep (se 2 (by rfl) ⟨1162365, by rfl⟩ : syracuseStep 3099641 = 2324731) B2324731
theorem B2066427 : Blo 2065435 2066427 := bstep (se 1 (by rfl) ⟨1549820, by rfl⟩ : syracuseStep 2066427 = 3099641) B3099641
theorem B3184805 : Blo 2065435 3184805 := bbase (se 4 (by rfl) ⟨298575, by rfl⟩ : syracuseStep 3184805 = 597151) (by norm_num)
theorem B8492813 : Blo 2065435 8492813 := bstep (se 3 (by rfl) ⟨1592402, by rfl⟩ : syracuseStep 8492813 = 3184805) B3184805
theorem B5661875 : Blo 2065435 5661875 := bstep (se 1 (by rfl) ⟨4246406, by rfl⟩ : syracuseStep 5661875 = 8492813) B8492813
theorem B3774583 : Blo 2065435 3774583 := bstep (se 1 (by rfl) ⟨2830937, by rfl⟩ : syracuseStep 3774583 = 5661875) B5661875
theorem B5032777 : Blo 2065435 5032777 := bstep (se 2 (by rfl) ⟨1887291, by rfl⟩ : syracuseStep 5032777 = 3774583) B3774583
theorem B6710369 : Blo 2065435 6710369 := bstep (se 2 (by rfl) ⟨2516388, by rfl⟩ : syracuseStep 6710369 = 5032777) B5032777
theorem B17894317 : Blo 2065435 17894317 := bstep (se 3 (by rfl) ⟨3355184, by rfl⟩ : syracuseStep 17894317 = 6710369) B6710369
theorem B23859089 : Blo 2065435 23859089 := bstep (se 2 (by rfl) ⟨8947158, by rfl⟩ : syracuseStep 23859089 = 17894317) B17894317
theorem B15906059 : Blo 2065435 15906059 := bstep (se 1 (by rfl) ⟨11929544, by rfl⟩ : syracuseStep 15906059 = 23859089) B23859089
theorem B10604039 : Blo 2065435 10604039 := bstep (se 1 (by rfl) ⟨7953029, by rfl⟩ : syracuseStep 10604039 = 15906059) B15906059
theorem B28277437 : Blo 2065435 28277437 := bstep (se 3 (by rfl) ⟨5302019, by rfl⟩ : syracuseStep 28277437 = 10604039) B10604039
theorem B37703249 : Blo 2065435 37703249 := bstep (se 2 (by rfl) ⟨14138718, by rfl⟩ : syracuseStep 37703249 = 28277437) B28277437
theorem B25135499 : Blo 2065435 25135499 := bstep (se 1 (by rfl) ⟨18851624, by rfl⟩ : syracuseStep 25135499 = 37703249) B37703249
theorem B16756999 : Blo 2065435 16756999 := bstep (se 1 (by rfl) ⟨12567749, by rfl⟩ : syracuseStep 16756999 = 25135499) B25135499
theorem B89370661 : Blo 2065435 89370661 := bstep (se 4 (by rfl) ⟨8378499, by rfl⟩ : syracuseStep 89370661 = 16756999) B16756999
theorem B119160881 : Blo 2065435 119160881 := bstep (se 2 (by rfl) ⟨44685330, by rfl⟩ : syracuseStep 119160881 = 89370661) B89370661
theorem B79440587 : Blo 2065435 79440587 := bstep (se 1 (by rfl) ⟨59580440, by rfl⟩ : syracuseStep 79440587 = 119160881) B119160881
theorem B52960391 : Blo 2065435 52960391 := bstep (se 1 (by rfl) ⟨39720293, by rfl⟩ : syracuseStep 52960391 = 79440587) B79440587
theorem B35306927 : Blo 2065435 35306927 := bstep (se 1 (by rfl) ⟨26480195, by rfl⟩ : syracuseStep 35306927 = 52960391) B52960391
theorem B23537951 : Blo 2065435 23537951 := bstep (se 1 (by rfl) ⟨17653463, by rfl⟩ : syracuseStep 23537951 = 35306927) B35306927
theorem B15691967 : Blo 2065435 15691967 := bstep (se 1 (by rfl) ⟨11768975, by rfl⟩ : syracuseStep 15691967 = 23537951) B23537951
theorem B10461311 : Blo 2065435 10461311 := bstep (se 1 (by rfl) ⟨7845983, by rfl⟩ : syracuseStep 10461311 = 15691967) B15691967
theorem B6974207 : Blo 2065435 6974207 := bstep (se 1 (by rfl) ⟨5230655, by rfl⟩ : syracuseStep 6974207 = 10461311) B10461311
theorem B4649471 : Blo 2065435 4649471 := bstep (se 1 (by rfl) ⟨3487103, by rfl⟩ : syracuseStep 4649471 = 6974207) B6974207
theorem B3099647 : Blo 2065435 3099647 := bstep (se 1 (by rfl) ⟨2324735, by rfl⟩ : syracuseStep 3099647 = 4649471) B4649471
theorem B2066431 : Blo 2065435 2066431 := bstep (se 1 (by rfl) ⟨1549823, by rfl⟩ : syracuseStep 2066431 = 3099647) B3099647
theorem B3099653 : Blo 2065435 3099653 := bbase (se 4 (by rfl) ⟨290592, by rfl⟩ : syracuseStep 3099653 = 581185) (by norm_num)
theorem B2066435 : Blo 2065435 2066435 := bstep (se 1 (by rfl) ⟨1549826, by rfl⟩ : syracuseStep 2066435 = 3099653) B3099653
theorem B3487117 : Blo 2065435 3487117 := bbase (se 3 (by rfl) ⟨653834, by rfl⟩ : syracuseStep 3487117 = 1307669) (by norm_num)
theorem B4649489 : Blo 2065435 4649489 := bstep (se 2 (by rfl) ⟨1743558, by rfl⟩ : syracuseStep 4649489 = 3487117) B3487117
theorem B3099659 : Blo 2065435 3099659 := bstep (se 1 (by rfl) ⟨2324744, by rfl⟩ : syracuseStep 3099659 = 4649489) B4649489
theorem B2066439 : Blo 2065435 2066439 := bstep (se 1 (by rfl) ⟨1549829, by rfl⟩ : syracuseStep 2066439 = 3099659) B3099659
theorem B2324749 : Blo 2065435 2324749 := bbase (se 3 (by rfl) ⟨435890, by rfl⟩ : syracuseStep 2324749 = 871781) (by norm_num)
theorem B3099665 : Blo 2065435 3099665 := bstep (se 2 (by rfl) ⟨1162374, by rfl⟩ : syracuseStep 3099665 = 2324749) B2324749
theorem B2066443 : Blo 2065435 2066443 := bstep (se 1 (by rfl) ⟨1549832, by rfl⟩ : syracuseStep 2066443 = 3099665) B3099665
theorem B6974261 : Blo 2065435 6974261 := bbase (se 5 (by rfl) ⟨326918, by rfl⟩ : syracuseStep 6974261 = 653837) (by norm_num)
theorem B4649507 : Blo 2065435 4649507 := bstep (se 1 (by rfl) ⟨3487130, by rfl⟩ : syracuseStep 4649507 = 6974261) B6974261
theorem B3099671 : Blo 2065435 3099671 := bstep (se 1 (by rfl) ⟨2324753, by rfl⟩ : syracuseStep 3099671 = 4649507) B4649507
theorem B2066447 : Blo 2065435 2066447 := bstep (se 1 (by rfl) ⟨1549835, by rfl⟩ : syracuseStep 2066447 = 3099671) B3099671
theorem B3099677 : Blo 2065435 3099677 := bbase (se 3 (by rfl) ⟨581189, by rfl⟩ : syracuseStep 3099677 = 1162379) (by norm_num)
theorem B2066451 : Blo 2065435 2066451 := bstep (se 1 (by rfl) ⟨1549838, by rfl⟩ : syracuseStep 2066451 = 3099677) B3099677
theorem B4649525 : Blo 2065435 4649525 := bbase (se 5 (by rfl) ⟨217946, by rfl⟩ : syracuseStep 4649525 = 435893) (by norm_num)
theorem B3099683 : Blo 2065435 3099683 := bstep (se 1 (by rfl) ⟨2324762, by rfl⟩ : syracuseStep 3099683 = 4649525) B4649525
theorem B2066455 : Blo 2065435 2066455 := bstep (se 1 (by rfl) ⟨1549841, by rfl⟩ : syracuseStep 2066455 = 3099683) B3099683
theorem B8826853 : Blo 2065435 8826853 := bbase (se 4 (by rfl) ⟨827517, by rfl⟩ : syracuseStep 8826853 = 1655035) (by norm_num)
theorem B11769137 : Blo 2065435 11769137 := bstep (se 2 (by rfl) ⟨4413426, by rfl⟩ : syracuseStep 11769137 = 8826853) B8826853
theorem B7846091 : Blo 2065435 7846091 := bstep (se 1 (by rfl) ⟨5884568, by rfl⟩ : syracuseStep 7846091 = 11769137) B11769137
theorem B5230727 : Blo 2065435 5230727 := bstep (se 1 (by rfl) ⟨3923045, by rfl⟩ : syracuseStep 5230727 = 7846091) B7846091
theorem B3487151 : Blo 2065435 3487151 := bstep (se 1 (by rfl) ⟨2615363, by rfl⟩ : syracuseStep 3487151 = 5230727) B5230727
theorem B2324767 : Blo 2065435 2324767 := bstep (se 1 (by rfl) ⟨1743575, by rfl⟩ : syracuseStep 2324767 = 3487151) B3487151
theorem B3099689 : Blo 2065435 3099689 := bstep (se 2 (by rfl) ⟨1162383, by rfl⟩ : syracuseStep 3099689 = 2324767) B2324767
theorem B2066459 : Blo 2065435 2066459 := bstep (se 1 (by rfl) ⟨1549844, by rfl⟩ : syracuseStep 2066459 = 3099689) B3099689
theorem B8826869 : Blo 2065435 8826869 := bbase (se 5 (by rfl) ⟨413759, by rfl⟩ : syracuseStep 8826869 = 827519) (by norm_num)
theorem B5884579 : Blo 2065435 5884579 := bstep (se 1 (by rfl) ⟨4413434, by rfl⟩ : syracuseStep 5884579 = 8826869) B8826869
theorem B7846105 : Blo 2065435 7846105 := bstep (se 2 (by rfl) ⟨2942289, by rfl⟩ : syracuseStep 7846105 = 5884579) B5884579
theorem B10461473 : Blo 2065435 10461473 := bstep (se 2 (by rfl) ⟨3923052, by rfl⟩ : syracuseStep 10461473 = 7846105) B7846105
theorem B6974315 : Blo 2065435 6974315 := bstep (se 1 (by rfl) ⟨5230736, by rfl⟩ : syracuseStep 6974315 = 10461473) B10461473
theorem B4649543 : Blo 2065435 4649543 := bstep (se 1 (by rfl) ⟨3487157, by rfl⟩ : syracuseStep 4649543 = 6974315) B6974315
theorem B3099695 : Blo 2065435 3099695 := bstep (se 1 (by rfl) ⟨2324771, by rfl⟩ : syracuseStep 3099695 = 4649543) B4649543
theorem B2066463 : Blo 2065435 2066463 := bstep (se 1 (by rfl) ⟨1549847, by rfl⟩ : syracuseStep 2066463 = 3099695) B3099695
theorem B3099701 : Blo 2065435 3099701 := bbase (se 5 (by rfl) ⟨145298, by rfl⟩ : syracuseStep 3099701 = 290597) (by norm_num)
theorem B2066467 : Blo 2065435 2066467 := bstep (se 1 (by rfl) ⟨1549850, by rfl⟩ : syracuseStep 2066467 = 3099701) B3099701
theorem B5230757 : Blo 2065435 5230757 := bbase (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) (by norm_num)
theorem B3487171 : Blo 2065435 3487171 := bstep (se 1 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 3487171 = 5230757) B5230757
theorem B4649561 : Blo 2065435 4649561 := bstep (se 2 (by rfl) ⟨1743585, by rfl⟩ : syracuseStep 4649561 = 3487171) B3487171
theorem B3099707 : Blo 2065435 3099707 := bstep (se 1 (by rfl) ⟨2324780, by rfl⟩ : syracuseStep 3099707 = 4649561) B4649561
theorem B2066471 : Blo 2065435 2066471 := bstep (se 1 (by rfl) ⟨1549853, by rfl⟩ : syracuseStep 2066471 = 3099707) B3099707
theorem B2324785 : Blo 2065435 2324785 := bbase (se 2 (by rfl) ⟨871794, by rfl⟩ : syracuseStep 2324785 = 1743589) (by norm_num)
theorem B3099713 : Blo 2065435 3099713 := bstep (se 2 (by rfl) ⟨1162392, by rfl⟩ : syracuseStep 3099713 = 2324785) B2324785
theorem B2066475 : Blo 2065435 2066475 := bstep (se 1 (by rfl) ⟨1549856, by rfl⟩ : syracuseStep 2066475 = 3099713) B3099713
theorem B4413469 : Blo 2065435 4413469 := bbase (se 3 (by rfl) ⟨827525, by rfl⟩ : syracuseStep 4413469 = 1655051) (by norm_num)
theorem B5884625 : Blo 2065435 5884625 := bstep (se 2 (by rfl) ⟨2206734, by rfl⟩ : syracuseStep 5884625 = 4413469) B4413469
theorem B3923083 : Blo 2065435 3923083 := bstep (se 1 (by rfl) ⟨2942312, by rfl⟩ : syracuseStep 3923083 = 5884625) B5884625
theorem B5230777 : Blo 2065435 5230777 := bstep (se 2 (by rfl) ⟨1961541, by rfl⟩ : syracuseStep 5230777 = 3923083) B3923083
theorem B6974369 : Blo 2065435 6974369 := bstep (se 2 (by rfl) ⟨2615388, by rfl⟩ : syracuseStep 6974369 = 5230777) B5230777
theorem B4649579 : Blo 2065435 4649579 := bstep (se 1 (by rfl) ⟨3487184, by rfl⟩ : syracuseStep 4649579 = 6974369) B6974369
theorem B3099719 : Blo 2065435 3099719 := bstep (se 1 (by rfl) ⟨2324789, by rfl⟩ : syracuseStep 3099719 = 4649579) B4649579
theorem B2066479 : Blo 2065435 2066479 := bstep (se 1 (by rfl) ⟨1549859, by rfl⟩ : syracuseStep 2066479 = 3099719) B3099719
theorem B3099725 : Blo 2065435 3099725 := bbase (se 3 (by rfl) ⟨581198, by rfl⟩ : syracuseStep 3099725 = 1162397) (by norm_num)
theorem B2066483 : Blo 2065435 2066483 := bstep (se 1 (by rfl) ⟨1549862, by rfl⟩ : syracuseStep 2066483 = 3099725) B3099725
theorem B4649597 : Blo 2065435 4649597 := bbase (se 3 (by rfl) ⟨871799, by rfl⟩ : syracuseStep 4649597 = 1743599) (by norm_num)
theorem B3099731 : Blo 2065435 3099731 := bstep (se 1 (by rfl) ⟨2324798, by rfl⟩ : syracuseStep 3099731 = 4649597) B4649597
theorem B2066487 : Blo 2065435 2066487 := bstep (se 1 (by rfl) ⟨1549865, by rfl⟩ : syracuseStep 2066487 = 3099731) B3099731
theorem B3487205 : Blo 2065435 3487205 := bbase (se 4 (by rfl) ⟨326925, by rfl⟩ : syracuseStep 3487205 = 653851) (by norm_num)
theorem B2324803 : Blo 2065435 2324803 := bstep (se 1 (by rfl) ⟨1743602, by rfl⟩ : syracuseStep 2324803 = 3487205) B3487205
theorem B3099737 : Blo 2065435 3099737 := bstep (se 2 (by rfl) ⟨1162401, by rfl⟩ : syracuseStep 3099737 = 2324803) B2324803
theorem B2066491 : Blo 2065435 2066491 := bstep (se 1 (by rfl) ⟨1549868, by rfl⟩ : syracuseStep 2066491 = 3099737) B3099737
theorem B10203205 : Blo 2065435 10203205 := bbase (se 4 (by rfl) ⟨956550, by rfl⟩ : syracuseStep 10203205 = 1913101) (by norm_num)
theorem B13604273 : Blo 2065435 13604273 := bstep (se 2 (by rfl) ⟨5101602, by rfl⟩ : syracuseStep 13604273 = 10203205) B10203205
theorem B9069515 : Blo 2065435 9069515 := bstep (se 1 (by rfl) ⟨6802136, by rfl⟩ : syracuseStep 9069515 = 13604273) B13604273
theorem B6046343 : Blo 2065435 6046343 := bstep (se 1 (by rfl) ⟨4534757, by rfl⟩ : syracuseStep 6046343 = 9069515) B9069515
theorem B4030895 : Blo 2065435 4030895 := bstep (se 1 (by rfl) ⟨3023171, by rfl⟩ : syracuseStep 4030895 = 6046343) B6046343
theorem B2687263 : Blo 2065435 2687263 := bstep (se 1 (by rfl) ⟨2015447, by rfl⟩ : syracuseStep 2687263 = 4030895) B4030895
theorem B14332069 : Blo 2065435 14332069 := bstep (se 4 (by rfl) ⟨1343631, by rfl⟩ : syracuseStep 14332069 = 2687263) B2687263
theorem B76437701 : Blo 2065435 76437701 := bstep (se 4 (by rfl) ⟨7166034, by rfl⟩ : syracuseStep 76437701 = 14332069) B14332069
theorem B50958467 : Blo 2065435 50958467 := bstep (se 1 (by rfl) ⟨38218850, by rfl⟩ : syracuseStep 50958467 = 76437701) B76437701
theorem B33972311 : Blo 2065435 33972311 := bstep (se 1 (by rfl) ⟨25479233, by rfl⟩ : syracuseStep 33972311 = 50958467) B50958467
theorem B22648207 : Blo 2065435 22648207 := bstep (se 1 (by rfl) ⟨16986155, by rfl⟩ : syracuseStep 22648207 = 33972311) B33972311
theorem B30197609 : Blo 2065435 30197609 := bstep (se 2 (by rfl) ⟨11324103, by rfl⟩ : syracuseStep 30197609 = 22648207) B22648207
theorem B20131739 : Blo 2065435 20131739 := bstep (se 1 (by rfl) ⟨15098804, by rfl⟩ : syracuseStep 20131739 = 30197609) B30197609
theorem B13421159 : Blo 2065435 13421159 := bstep (se 1 (by rfl) ⟨10065869, by rfl⟩ : syracuseStep 13421159 = 20131739) B20131739
theorem B8947439 : Blo 2065435 8947439 := bstep (se 1 (by rfl) ⟨6710579, by rfl⟩ : syracuseStep 8947439 = 13421159) B13421159
theorem B5964959 : Blo 2065435 5964959 := bstep (se 1 (by rfl) ⟨4473719, by rfl⟩ : syracuseStep 5964959 = 8947439) B8947439
theorem B15906557 : Blo 2065435 15906557 := bstep (se 3 (by rfl) ⟨2982479, by rfl⟩ : syracuseStep 15906557 = 5964959) B5964959
theorem B10604371 : Blo 2065435 10604371 := bstep (se 1 (by rfl) ⟨7953278, by rfl⟩ : syracuseStep 10604371 = 15906557) B15906557
theorem B14139161 : Blo 2065435 14139161 := bstep (se 2 (by rfl) ⟨5302185, by rfl⟩ : syracuseStep 14139161 = 10604371) B10604371
theorem B9426107 : Blo 2065435 9426107 := bstep (se 1 (by rfl) ⟨7069580, by rfl⟩ : syracuseStep 9426107 = 14139161) B14139161
theorem B6284071 : Blo 2065435 6284071 := bstep (se 1 (by rfl) ⟨4713053, by rfl⟩ : syracuseStep 6284071 = 9426107) B9426107
theorem B33515045 : Blo 2065435 33515045 := bstep (se 4 (by rfl) ⟨3142035, by rfl⟩ : syracuseStep 33515045 = 6284071) B6284071
theorem B22343363 : Blo 2065435 22343363 := bstep (se 1 (by rfl) ⟨16757522, by rfl⟩ : syracuseStep 22343363 = 33515045) B33515045
theorem B14895575 : Blo 2065435 14895575 := bstep (se 1 (by rfl) ⟨11171681, by rfl⟩ : syracuseStep 14895575 = 22343363) B22343363
theorem B9930383 : Blo 2065435 9930383 := bstep (se 1 (by rfl) ⟨7447787, by rfl⟩ : syracuseStep 9930383 = 14895575) B14895575
theorem B6620255 : Blo 2065435 6620255 := bstep (se 1 (by rfl) ⟨4965191, by rfl⟩ : syracuseStep 6620255 = 9930383) B9930383
theorem B4413503 : Blo 2065435 4413503 := bstep (se 1 (by rfl) ⟨3310127, by rfl⟩ : syracuseStep 4413503 = 6620255) B6620255
theorem B2942335 : Blo 2065435 2942335 := bstep (se 1 (by rfl) ⟨2206751, by rfl⟩ : syracuseStep 2942335 = 4413503) B4413503
theorem B15692453 : Blo 2065435 15692453 := bstep (se 4 (by rfl) ⟨1471167, by rfl⟩ : syracuseStep 15692453 = 2942335) B2942335
theorem B10461635 : Blo 2065435 10461635 := bstep (se 1 (by rfl) ⟨7846226, by rfl⟩ : syracuseStep 10461635 = 15692453) B15692453
theorem B6974423 : Blo 2065435 6974423 := bstep (se 1 (by rfl) ⟨5230817, by rfl⟩ : syracuseStep 6974423 = 10461635) B10461635
theorem B4649615 : Blo 2065435 4649615 := bstep (se 1 (by rfl) ⟨3487211, by rfl⟩ : syracuseStep 4649615 = 6974423) B6974423
theorem B3099743 : Blo 2065435 3099743 := bstep (se 1 (by rfl) ⟨2324807, by rfl⟩ : syracuseStep 3099743 = 4649615) B4649615
theorem B2066495 : Blo 2065435 2066495 := bstep (se 1 (by rfl) ⟨1549871, by rfl⟩ : syracuseStep 2066495 = 3099743) B3099743
theorem B3099749 : Blo 2065435 3099749 := bbase (se 4 (by rfl) ⟨290601, by rfl⟩ : syracuseStep 3099749 = 581203) (by norm_num)
theorem B2066499 : Blo 2065435 2066499 := bstep (se 1 (by rfl) ⟨1549874, by rfl⟩ : syracuseStep 2066499 = 3099749) B3099749
theorem B3310141 : Blo 2065435 3310141 := bbase (se 3 (by rfl) ⟨620651, by rfl⟩ : syracuseStep 3310141 = 1241303) (by norm_num)
theorem B4413521 : Blo 2065435 4413521 := bstep (se 2 (by rfl) ⟨1655070, by rfl⟩ : syracuseStep 4413521 = 3310141) B3310141
theorem B2942347 : Blo 2065435 2942347 := bstep (se 1 (by rfl) ⟨2206760, by rfl⟩ : syracuseStep 2942347 = 4413521) B4413521
theorem B3923129 : Blo 2065435 3923129 := bstep (se 2 (by rfl) ⟨1471173, by rfl⟩ : syracuseStep 3923129 = 2942347) B2942347
theorem B2615419 : Blo 2065435 2615419 := bstep (se 1 (by rfl) ⟨1961564, by rfl⟩ : syracuseStep 2615419 = 3923129) B3923129
theorem B3487225 : Blo 2065435 3487225 := bstep (se 2 (by rfl) ⟨1307709, by rfl⟩ : syracuseStep 3487225 = 2615419) B2615419
theorem B4649633 : Blo 2065435 4649633 := bstep (se 2 (by rfl) ⟨1743612, by rfl⟩ : syracuseStep 4649633 = 3487225) B3487225
theorem B3099755 : Blo 2065435 3099755 := bstep (se 1 (by rfl) ⟨2324816, by rfl⟩ : syracuseStep 3099755 = 4649633) B4649633
theorem B2066503 : Blo 2065435 2066503 := bstep (se 1 (by rfl) ⟨1549877, by rfl⟩ : syracuseStep 2066503 = 3099755) B3099755
theorem B2324821 : Blo 2065435 2324821 := bbase (se 10 (by rfl) ⟨3405, by rfl⟩ : syracuseStep 2324821 = 6811) (by norm_num)
theorem B3099761 : Blo 2065435 3099761 := bstep (se 2 (by rfl) ⟨1162410, by rfl⟩ : syracuseStep 3099761 = 2324821) B2324821
theorem B2066507 : Blo 2065435 2066507 := bstep (se 1 (by rfl) ⟨1549880, by rfl⟩ : syracuseStep 2066507 = 3099761) B3099761
theorem B2615429 : Blo 2065435 2615429 := bbase (se 4 (by rfl) ⟨245196, by rfl⟩ : syracuseStep 2615429 = 490393) (by norm_num)
theorem B6974477 : Blo 2065435 6974477 := bstep (se 3 (by rfl) ⟨1307714, by rfl⟩ : syracuseStep 6974477 = 2615429) B2615429
theorem B4649651 : Blo 2065435 4649651 := bstep (se 1 (by rfl) ⟨3487238, by rfl⟩ : syracuseStep 4649651 = 6974477) B6974477
theorem B3099767 : Blo 2065435 3099767 := bstep (se 1 (by rfl) ⟨2324825, by rfl⟩ : syracuseStep 3099767 = 4649651) B4649651
theorem B2066511 : Blo 2065435 2066511 := bstep (se 1 (by rfl) ⟨1549883, by rfl⟩ : syracuseStep 2066511 = 3099767) B3099767
theorem B3099773 : Blo 2065435 3099773 := bbase (se 3 (by rfl) ⟨581207, by rfl⟩ : syracuseStep 3099773 = 1162415) (by norm_num)
theorem B2066515 : Blo 2065435 2066515 := bstep (se 1 (by rfl) ⟨1549886, by rfl⟩ : syracuseStep 2066515 = 3099773) B3099773
theorem B4649669 : Blo 2065435 4649669 := bbase (se 4 (by rfl) ⟨435906, by rfl⟩ : syracuseStep 4649669 = 871813) (by norm_num)
theorem B3099779 : Blo 2065435 3099779 := bstep (se 1 (by rfl) ⟨2324834, by rfl⟩ : syracuseStep 3099779 = 4649669) B4649669
theorem B2066519 : Blo 2065435 2066519 := bstep (se 1 (by rfl) ⟨1549889, by rfl⟩ : syracuseStep 2066519 = 3099779) B3099779
theorem B3184949 : Blo 2065435 3184949 := bbase (se 5 (by rfl) ⟨149294, by rfl⟩ : syracuseStep 3184949 = 298589) (by norm_num)
theorem B2123299 : Blo 2065435 2123299 := bstep (se 1 (by rfl) ⟨1592474, by rfl⟩ : syracuseStep 2123299 = 3184949) B3184949
theorem B11324261 : Blo 2065435 11324261 := bstep (se 4 (by rfl) ⟨1061649, by rfl⟩ : syracuseStep 11324261 = 2123299) B2123299
theorem B7549507 : Blo 2065435 7549507 := bstep (se 1 (by rfl) ⟨5662130, by rfl⟩ : syracuseStep 7549507 = 11324261) B11324261
theorem B40264037 : Blo 2065435 40264037 := bstep (se 4 (by rfl) ⟨3774753, by rfl⟩ : syracuseStep 40264037 = 7549507) B7549507
theorem B26842691 : Blo 2065435 26842691 := bstep (se 1 (by rfl) ⟨20132018, by rfl⟩ : syracuseStep 26842691 = 40264037) B40264037
theorem B17895127 : Blo 2065435 17895127 := bstep (se 1 (by rfl) ⟨13421345, by rfl⟩ : syracuseStep 17895127 = 26842691) B26842691
theorem B23860169 : Blo 2065435 23860169 := bstep (se 2 (by rfl) ⟨8947563, by rfl⟩ : syracuseStep 23860169 = 17895127) B17895127
theorem B15906779 : Blo 2065435 15906779 := bstep (se 1 (by rfl) ⟨11930084, by rfl⟩ : syracuseStep 15906779 = 23860169) B23860169
theorem B10604519 : Blo 2065435 10604519 := bstep (se 1 (by rfl) ⟨7953389, by rfl⟩ : syracuseStep 10604519 = 15906779) B15906779
theorem B7069679 : Blo 2065435 7069679 := bstep (se 1 (by rfl) ⟨5302259, by rfl⟩ : syracuseStep 7069679 = 10604519) B10604519
theorem B4713119 : Blo 2065435 4713119 := bstep (se 1 (by rfl) ⟨3534839, by rfl⟩ : syracuseStep 4713119 = 7069679) B7069679
theorem B3142079 : Blo 2065435 3142079 := bstep (se 1 (by rfl) ⟨2356559, by rfl⟩ : syracuseStep 3142079 = 4713119) B4713119
theorem B2094719 : Blo 2065435 2094719 := bstep (se 1 (by rfl) ⟨1571039, by rfl⟩ : syracuseStep 2094719 = 3142079) B3142079
theorem B5585917 : Blo 2065435 5585917 := bstep (se 3 (by rfl) ⟨1047359, by rfl⟩ : syracuseStep 5585917 = 2094719) B2094719
theorem B7447889 : Blo 2065435 7447889 := bstep (se 2 (by rfl) ⟨2792958, by rfl⟩ : syracuseStep 7447889 = 5585917) B5585917
theorem B19861037 : Blo 2065435 19861037 := bstep (se 3 (by rfl) ⟨3723944, by rfl⟩ : syracuseStep 19861037 = 7447889) B7447889
theorem B13240691 : Blo 2065435 13240691 := bstep (se 1 (by rfl) ⟨9930518, by rfl⟩ : syracuseStep 13240691 = 19861037) B19861037
theorem B8827127 : Blo 2065435 8827127 := bstep (se 1 (by rfl) ⟨6620345, by rfl⟩ : syracuseStep 8827127 = 13240691) B13240691
theorem B5884751 : Blo 2065435 5884751 := bstep (se 1 (by rfl) ⟨4413563, by rfl⟩ : syracuseStep 5884751 = 8827127) B8827127
theorem B3923167 : Blo 2065435 3923167 := bstep (se 1 (by rfl) ⟨2942375, by rfl⟩ : syracuseStep 3923167 = 5884751) B5884751
theorem B5230889 : Blo 2065435 5230889 := bstep (se 2 (by rfl) ⟨1961583, by rfl⟩ : syracuseStep 5230889 = 3923167) B3923167
theorem B3487259 : Blo 2065435 3487259 := bstep (se 1 (by rfl) ⟨2615444, by rfl⟩ : syracuseStep 3487259 = 5230889) B5230889
theorem B2324839 : Blo 2065435 2324839 := bstep (se 1 (by rfl) ⟨1743629, by rfl⟩ : syracuseStep 2324839 = 3487259) B3487259
theorem B3099785 : Blo 2065435 3099785 := bstep (se 2 (by rfl) ⟨1162419, by rfl⟩ : syracuseStep 3099785 = 2324839) B2324839
theorem B2066523 : Blo 2065435 2066523 := bstep (se 1 (by rfl) ⟨1549892, by rfl⟩ : syracuseStep 2066523 = 3099785) B3099785
theorem B10461797 : Blo 2065435 10461797 := bbase (se 4 (by rfl) ⟨980793, by rfl⟩ : syracuseStep 10461797 = 1961587) (by norm_num)
theorem B6974531 : Blo 2065435 6974531 := bstep (se 1 (by rfl) ⟨5230898, by rfl⟩ : syracuseStep 6974531 = 10461797) B10461797
theorem B4649687 : Blo 2065435 4649687 := bstep (se 1 (by rfl) ⟨3487265, by rfl⟩ : syracuseStep 4649687 = 6974531) B6974531
theorem B3099791 : Blo 2065435 3099791 := bstep (se 1 (by rfl) ⟨2324843, by rfl⟩ : syracuseStep 3099791 = 4649687) B4649687
theorem B2066527 : Blo 2065435 2066527 := bstep (se 1 (by rfl) ⟨1549895, by rfl⟩ : syracuseStep 2066527 = 3099791) B3099791
theorem B3099797 : Blo 2065435 3099797 := bbase (se 6 (by rfl) ⟨72651, by rfl⟩ : syracuseStep 3099797 = 145303) (by norm_num)
theorem B2066531 : Blo 2065435 2066531 := bstep (se 1 (by rfl) ⟨1549898, by rfl⟩ : syracuseStep 2066531 = 3099797) B3099797
theorem B7069717 : Blo 2065435 7069717 := bbase (se 6 (by rfl) ⟨165696, by rfl⟩ : syracuseStep 7069717 = 331393) (by norm_num)
theorem B9426289 : Blo 2065435 9426289 := bstep (se 2 (by rfl) ⟨3534858, by rfl⟩ : syracuseStep 9426289 = 7069717) B7069717
theorem B12568385 : Blo 2065435 12568385 := bstep (se 2 (by rfl) ⟨4713144, by rfl⟩ : syracuseStep 12568385 = 9426289) B9426289
theorem B33515693 : Blo 2065435 33515693 := bstep (se 3 (by rfl) ⟨6284192, by rfl⟩ : syracuseStep 33515693 = 12568385) B12568385
theorem B22343795 : Blo 2065435 22343795 := bstep (se 1 (by rfl) ⟨16757846, by rfl⟩ : syracuseStep 22343795 = 33515693) B33515693
theorem B14895863 : Blo 2065435 14895863 := bstep (se 1 (by rfl) ⟨11171897, by rfl⟩ : syracuseStep 14895863 = 22343795) B22343795
theorem B9930575 : Blo 2065435 9930575 := bstep (se 1 (by rfl) ⟨7447931, by rfl⟩ : syracuseStep 9930575 = 14895863) B14895863
theorem B6620383 : Blo 2065435 6620383 := bstep (se 1 (by rfl) ⟨4965287, by rfl⟩ : syracuseStep 6620383 = 9930575) B9930575
theorem B8827177 : Blo 2065435 8827177 := bstep (se 2 (by rfl) ⟨3310191, by rfl⟩ : syracuseStep 8827177 = 6620383) B6620383
theorem B11769569 : Blo 2065435 11769569 := bstep (se 2 (by rfl) ⟨4413588, by rfl⟩ : syracuseStep 11769569 = 8827177) B8827177
theorem B7846379 : Blo 2065435 7846379 := bstep (se 1 (by rfl) ⟨5884784, by rfl⟩ : syracuseStep 7846379 = 11769569) B11769569
theorem B5230919 : Blo 2065435 5230919 := bstep (se 1 (by rfl) ⟨3923189, by rfl⟩ : syracuseStep 5230919 = 7846379) B7846379
theorem B3487279 : Blo 2065435 3487279 := bstep (se 1 (by rfl) ⟨2615459, by rfl⟩ : syracuseStep 3487279 = 5230919) B5230919
theorem B4649705 : Blo 2065435 4649705 := bstep (se 2 (by rfl) ⟨1743639, by rfl⟩ : syracuseStep 4649705 = 3487279) B3487279
theorem B3099803 : Blo 2065435 3099803 := bstep (se 1 (by rfl) ⟨2324852, by rfl⟩ : syracuseStep 3099803 = 4649705) B4649705
theorem B2066535 : Blo 2065435 2066535 := bstep (se 1 (by rfl) ⟨1549901, by rfl⟩ : syracuseStep 2066535 = 3099803) B3099803
theorem B2324857 : Blo 2065435 2324857 := bbase (se 2 (by rfl) ⟨871821, by rfl⟩ : syracuseStep 2324857 = 1743643) (by norm_num)
theorem B3099809 : Blo 2065435 3099809 := bstep (se 2 (by rfl) ⟨1162428, by rfl⟩ : syracuseStep 3099809 = 2324857) B2324857
theorem B2066539 : Blo 2065435 2066539 := bstep (se 1 (by rfl) ⟨1549904, by rfl⟩ : syracuseStep 2066539 = 3099809) B3099809
theorem B9930613 : Blo 2065435 9930613 := bbase (se 5 (by rfl) ⟨465497, by rfl⟩ : syracuseStep 9930613 = 930995) (by norm_num)
theorem B13240817 : Blo 2065435 13240817 := bstep (se 2 (by rfl) ⟨4965306, by rfl⟩ : syracuseStep 13240817 = 9930613) B9930613
theorem B8827211 : Blo 2065435 8827211 := bstep (se 1 (by rfl) ⟨6620408, by rfl⟩ : syracuseStep 8827211 = 13240817) B13240817
theorem B5884807 : Blo 2065435 5884807 := bstep (se 1 (by rfl) ⟨4413605, by rfl⟩ : syracuseStep 5884807 = 8827211) B8827211
theorem B7846409 : Blo 2065435 7846409 := bstep (se 2 (by rfl) ⟨2942403, by rfl⟩ : syracuseStep 7846409 = 5884807) B5884807
theorem B5230939 : Blo 2065435 5230939 := bstep (se 1 (by rfl) ⟨3923204, by rfl⟩ : syracuseStep 5230939 = 7846409) B7846409
theorem B6974585 : Blo 2065435 6974585 := bstep (se 2 (by rfl) ⟨2615469, by rfl⟩ : syracuseStep 6974585 = 5230939) B5230939
theorem B4649723 : Blo 2065435 4649723 := bstep (se 1 (by rfl) ⟨3487292, by rfl⟩ : syracuseStep 4649723 = 6974585) B6974585
theorem B3099815 : Blo 2065435 3099815 := bstep (se 1 (by rfl) ⟨2324861, by rfl⟩ : syracuseStep 3099815 = 4649723) B4649723
theorem B2066543 : Blo 2065435 2066543 := bstep (se 1 (by rfl) ⟨1549907, by rfl⟩ : syracuseStep 2066543 = 3099815) B3099815
theorem B3099821 : Blo 2065435 3099821 := bbase (se 3 (by rfl) ⟨581216, by rfl⟩ : syracuseStep 3099821 = 1162433) (by norm_num)
theorem B2066547 : Blo 2065435 2066547 := bstep (se 1 (by rfl) ⟨1549910, by rfl⟩ : syracuseStep 2066547 = 3099821) B3099821
theorem B4649741 : Blo 2065435 4649741 := bbase (se 3 (by rfl) ⟨871826, by rfl⟩ : syracuseStep 4649741 = 1743653) (by norm_num)
theorem B3099827 : Blo 2065435 3099827 := bstep (se 1 (by rfl) ⟨2324870, by rfl⟩ : syracuseStep 3099827 = 4649741) B4649741
theorem B2066551 : Blo 2065435 2066551 := bstep (se 1 (by rfl) ⟨1549913, by rfl⟩ : syracuseStep 2066551 = 3099827) B3099827
theorem B2615485 : Blo 2065435 2615485 := bbase (se 3 (by rfl) ⟨490403, by rfl⟩ : syracuseStep 2615485 = 980807) (by norm_num)
theorem B3487313 : Blo 2065435 3487313 := bstep (se 2 (by rfl) ⟨1307742, by rfl⟩ : syracuseStep 3487313 = 2615485) B2615485
theorem B2324875 : Blo 2065435 2324875 := bstep (se 1 (by rfl) ⟨1743656, by rfl⟩ : syracuseStep 2324875 = 3487313) B3487313
theorem B3099833 : Blo 2065435 3099833 := bstep (se 2 (by rfl) ⟨1162437, by rfl⟩ : syracuseStep 3099833 = 2324875) B2324875
theorem B2066555 : Blo 2065435 2066555 := bstep (se 1 (by rfl) ⟨1549916, by rfl⟩ : syracuseStep 2066555 = 3099833) B3099833
theorem B3142133 : Blo 2065435 3142133 := bbase (se 5 (by rfl) ⟨147287, by rfl⟩ : syracuseStep 3142133 = 294575) (by norm_num)
theorem B2094755 : Blo 2065435 2094755 := bstep (se 1 (by rfl) ⟨1571066, by rfl⟩ : syracuseStep 2094755 = 3142133) B3142133
theorem B5586013 : Blo 2065435 5586013 := bstep (se 3 (by rfl) ⟨1047377, by rfl⟩ : syracuseStep 5586013 = 2094755) B2094755
theorem B7448017 : Blo 2065435 7448017 := bstep (se 2 (by rfl) ⟨2793006, by rfl⟩ : syracuseStep 7448017 = 5586013) B5586013
theorem B9930689 : Blo 2065435 9930689 := bstep (se 2 (by rfl) ⟨3724008, by rfl⟩ : syracuseStep 9930689 = 7448017) B7448017
theorem B6620459 : Blo 2065435 6620459 := bstep (se 1 (by rfl) ⟨4965344, by rfl⟩ : syracuseStep 6620459 = 9930689) B9930689
theorem B17654557 : Blo 2065435 17654557 := bstep (se 3 (by rfl) ⟨3310229, by rfl⟩ : syracuseStep 17654557 = 6620459) B6620459
theorem B23539409 : Blo 2065435 23539409 := bstep (se 2 (by rfl) ⟨8827278, by rfl⟩ : syracuseStep 23539409 = 17654557) B17654557
theorem B15692939 : Blo 2065435 15692939 := bstep (se 1 (by rfl) ⟨11769704, by rfl⟩ : syracuseStep 15692939 = 23539409) B23539409
theorem B10461959 : Blo 2065435 10461959 := bstep (se 1 (by rfl) ⟨7846469, by rfl⟩ : syracuseStep 10461959 = 15692939) B15692939
theorem B6974639 : Blo 2065435 6974639 := bstep (se 1 (by rfl) ⟨5230979, by rfl⟩ : syracuseStep 6974639 = 10461959) B10461959
theorem B4649759 : Blo 2065435 4649759 := bstep (se 1 (by rfl) ⟨3487319, by rfl⟩ : syracuseStep 4649759 = 6974639) B6974639
theorem B3099839 : Blo 2065435 3099839 := bstep (se 1 (by rfl) ⟨2324879, by rfl⟩ : syracuseStep 3099839 = 4649759) B4649759
theorem B2066559 : Blo 2065435 2066559 := bstep (se 1 (by rfl) ⟨1549919, by rfl⟩ : syracuseStep 2066559 = 3099839) B3099839
theorem B3099845 : Blo 2065435 3099845 := bbase (se 4 (by rfl) ⟨290610, by rfl⟩ : syracuseStep 3099845 = 581221) (by norm_num)
theorem B2066563 : Blo 2065435 2066563 := bstep (se 1 (by rfl) ⟨1549922, by rfl⟩ : syracuseStep 2066563 = 3099845) B3099845
theorem B3487333 : Blo 2065435 3487333 := bbase (se 4 (by rfl) ⟨326937, by rfl⟩ : syracuseStep 3487333 = 653875) (by norm_num)
theorem B4649777 : Blo 2065435 4649777 := bstep (se 2 (by rfl) ⟨1743666, by rfl⟩ : syracuseStep 4649777 = 3487333) B3487333
theorem B3099851 : Blo 2065435 3099851 := bstep (se 1 (by rfl) ⟨2324888, by rfl⟩ : syracuseStep 3099851 = 4649777) B4649777
theorem B2066567 : Blo 2065435 2066567 := bstep (se 1 (by rfl) ⟨1549925, by rfl⟩ : syracuseStep 2066567 = 3099851) B3099851
theorem B2324893 : Blo 2065435 2324893 := bbase (se 3 (by rfl) ⟨435917, by rfl⟩ : syracuseStep 2324893 = 871835) (by norm_num)
theorem B3099857 : Blo 2065435 3099857 := bstep (se 2 (by rfl) ⟨1162446, by rfl⟩ : syracuseStep 3099857 = 2324893) B2324893
theorem B2066571 : Blo 2065435 2066571 := bstep (se 1 (by rfl) ⟨1549928, by rfl⟩ : syracuseStep 2066571 = 3099857) B3099857
theorem B6974693 : Blo 2065435 6974693 := bbase (se 4 (by rfl) ⟨653877, by rfl⟩ : syracuseStep 6974693 = 1307755) (by norm_num)
theorem B4649795 : Blo 2065435 4649795 := bstep (se 1 (by rfl) ⟨3487346, by rfl⟩ : syracuseStep 4649795 = 6974693) B6974693
theorem B3099863 : Blo 2065435 3099863 := bstep (se 1 (by rfl) ⟨2324897, by rfl⟩ : syracuseStep 3099863 = 4649795) B4649795
theorem B2066575 : Blo 2065435 2066575 := bstep (se 1 (by rfl) ⟨1549931, by rfl⟩ : syracuseStep 2066575 = 3099863) B3099863
theorem B3099869 : Blo 2065435 3099869 := bbase (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) (by norm_num)
theorem B2066579 : Blo 2065435 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B4649813 : Blo 2065435 4649813 := bbase (se 9 (by rfl) ⟨13622, by rfl⟩ : syracuseStep 4649813 = 27245) (by norm_num)
theorem B3099875 : Blo 2065435 3099875 := bstep (se 1 (by rfl) ⟨2324906, by rfl⟩ : syracuseStep 3099875 = 4649813) B4649813
theorem B2066583 : Blo 2065435 2066583 := bstep (se 1 (by rfl) ⟨1549937, by rfl⟩ : syracuseStep 2066583 = 3099875) B3099875
theorem B5884933 : Blo 2065435 5884933 := bbase (se 4 (by rfl) ⟨551712, by rfl⟩ : syracuseStep 5884933 = 1103425) (by norm_num)
theorem B7846577 : Blo 2065435 7846577 := bstep (se 2 (by rfl) ⟨2942466, by rfl⟩ : syracuseStep 7846577 = 5884933) B5884933
theorem B5231051 : Blo 2065435 5231051 := bstep (se 1 (by rfl) ⟨3923288, by rfl⟩ : syracuseStep 5231051 = 7846577) B7846577
theorem B3487367 : Blo 2065435 3487367 := bstep (se 1 (by rfl) ⟨2615525, by rfl⟩ : syracuseStep 3487367 = 5231051) B5231051
theorem B2324911 : Blo 2065435 2324911 := bstep (se 1 (by rfl) ⟨1743683, by rfl⟩ : syracuseStep 2324911 = 3487367) B3487367
theorem B3099881 : Blo 2065435 3099881 := bstep (se 2 (by rfl) ⟨1162455, by rfl⟩ : syracuseStep 3099881 = 2324911) B2324911
theorem B2066587 : Blo 2065435 2066587 := bstep (se 1 (by rfl) ⟨1549940, by rfl⟩ : syracuseStep 2066587 = 3099881) B3099881
theorem B3355445 : Blo 2065435 3355445 := bbase (se 5 (by rfl) ⟨157286, by rfl⟩ : syracuseStep 3355445 = 314573) (by norm_num)
theorem B8947853 : Blo 2065435 8947853 := bstep (se 3 (by rfl) ⟨1677722, by rfl⟩ : syracuseStep 8947853 = 3355445) B3355445
theorem B5965235 : Blo 2065435 5965235 := bstep (se 1 (by rfl) ⟨4473926, by rfl⟩ : syracuseStep 5965235 = 8947853) B8947853
theorem B3976823 : Blo 2065435 3976823 := bstep (se 1 (by rfl) ⟨2982617, by rfl⟩ : syracuseStep 3976823 = 5965235) B5965235
theorem B10604861 : Blo 2065435 10604861 := bstep (se 3 (by rfl) ⟨1988411, by rfl⟩ : syracuseStep 10604861 = 3976823) B3976823
theorem B7069907 : Blo 2065435 7069907 := bstep (se 1 (by rfl) ⟨5302430, by rfl⟩ : syracuseStep 7069907 = 10604861) B10604861
theorem B18853085 : Blo 2065435 18853085 := bstep (se 3 (by rfl) ⟨3534953, by rfl⟩ : syracuseStep 18853085 = 7069907) B7069907
theorem B50274893 : Blo 2065435 50274893 := bstep (se 3 (by rfl) ⟨9426542, by rfl⟩ : syracuseStep 50274893 = 18853085) B18853085
theorem B33516595 : Blo 2065435 33516595 := bstep (se 1 (by rfl) ⟨25137446, by rfl⟩ : syracuseStep 33516595 = 50274893) B50274893
theorem B44688793 : Blo 2065435 44688793 := bstep (se 2 (by rfl) ⟨16758297, by rfl⟩ : syracuseStep 44688793 = 33516595) B33516595
theorem B59585057 : Blo 2065435 59585057 := bstep (se 2 (by rfl) ⟨22344396, by rfl⟩ : syracuseStep 59585057 = 44688793) B44688793
theorem B39723371 : Blo 2065435 39723371 := bstep (se 1 (by rfl) ⟨29792528, by rfl⟩ : syracuseStep 39723371 = 59585057) B59585057
theorem B26482247 : Blo 2065435 26482247 := bstep (se 1 (by rfl) ⟨19861685, by rfl⟩ : syracuseStep 26482247 = 39723371) B39723371
theorem B17654831 : Blo 2065435 17654831 := bstep (se 1 (by rfl) ⟨13241123, by rfl⟩ : syracuseStep 17654831 = 26482247) B26482247
theorem B11769887 : Blo 2065435 11769887 := bstep (se 1 (by rfl) ⟨8827415, by rfl⟩ : syracuseStep 11769887 = 17654831) B17654831
theorem B7846591 : Blo 2065435 7846591 := bstep (se 1 (by rfl) ⟨5884943, by rfl⟩ : syracuseStep 7846591 = 11769887) B11769887
theorem B10462121 : Blo 2065435 10462121 := bstep (se 2 (by rfl) ⟨3923295, by rfl⟩ : syracuseStep 10462121 = 7846591) B7846591
theorem B6974747 : Blo 2065435 6974747 := bstep (se 1 (by rfl) ⟨5231060, by rfl⟩ : syracuseStep 6974747 = 10462121) B10462121
theorem B4649831 : Blo 2065435 4649831 := bstep (se 1 (by rfl) ⟨3487373, by rfl⟩ : syracuseStep 4649831 = 6974747) B6974747
theorem B3099887 : Blo 2065435 3099887 := bstep (se 1 (by rfl) ⟨2324915, by rfl⟩ : syracuseStep 3099887 = 4649831) B4649831
theorem B2066591 : Blo 2065435 2066591 := bstep (se 1 (by rfl) ⟨1549943, by rfl⟩ : syracuseStep 2066591 = 3099887) B3099887
theorem B3099893 : Blo 2065435 3099893 := bbase (se 5 (by rfl) ⟨145307, by rfl⟩ : syracuseStep 3099893 = 290615) (by norm_num)
theorem B2066595 : Blo 2065435 2066595 := bstep (se 1 (by rfl) ⟨1549946, by rfl⟩ : syracuseStep 2066595 = 3099893) B3099893
theorem B2793061 : Blo 2065435 2793061 := bbase (se 4 (by rfl) ⟨261849, by rfl⟩ : syracuseStep 2793061 = 523699) (by norm_num)
theorem B14896325 : Blo 2065435 14896325 := bstep (se 4 (by rfl) ⟨1396530, by rfl⟩ : syracuseStep 14896325 = 2793061) B2793061
theorem B9930883 : Blo 2065435 9930883 := bstep (se 1 (by rfl) ⟨7448162, by rfl⟩ : syracuseStep 9930883 = 14896325) B14896325
theorem B13241177 : Blo 2065435 13241177 := bstep (se 2 (by rfl) ⟨4965441, by rfl⟩ : syracuseStep 13241177 = 9930883) B9930883
theorem B8827451 : Blo 2065435 8827451 := bstep (se 1 (by rfl) ⟨6620588, by rfl⟩ : syracuseStep 8827451 = 13241177) B13241177
theorem B5884967 : Blo 2065435 5884967 := bstep (se 1 (by rfl) ⟨4413725, by rfl⟩ : syracuseStep 5884967 = 8827451) B8827451
theorem B3923311 : Blo 2065435 3923311 := bstep (se 1 (by rfl) ⟨2942483, by rfl⟩ : syracuseStep 3923311 = 5884967) B5884967
theorem B5231081 : Blo 2065435 5231081 := bstep (se 2 (by rfl) ⟨1961655, by rfl⟩ : syracuseStep 5231081 = 3923311) B3923311
theorem B3487387 : Blo 2065435 3487387 := bstep (se 1 (by rfl) ⟨2615540, by rfl⟩ : syracuseStep 3487387 = 5231081) B5231081
theorem B4649849 : Blo 2065435 4649849 := bstep (se 2 (by rfl) ⟨1743693, by rfl⟩ : syracuseStep 4649849 = 3487387) B3487387
theorem B3099899 : Blo 2065435 3099899 := bstep (se 1 (by rfl) ⟨2324924, by rfl⟩ : syracuseStep 3099899 = 4649849) B4649849
theorem B2066599 : Blo 2065435 2066599 := bstep (se 1 (by rfl) ⟨1549949, by rfl⟩ : syracuseStep 2066599 = 3099899) B3099899
theorem B2324929 : Blo 2065435 2324929 := bbase (se 2 (by rfl) ⟨871848, by rfl⟩ : syracuseStep 2324929 = 1743697) (by norm_num)
theorem B3099905 : Blo 2065435 3099905 := bstep (se 2 (by rfl) ⟨1162464, by rfl⟩ : syracuseStep 3099905 = 2324929) B2324929
theorem B2066603 : Blo 2065435 2066603 := bstep (se 1 (by rfl) ⟨1549952, by rfl⟩ : syracuseStep 2066603 = 3099905) B3099905
theorem B5231101 : Blo 2065435 5231101 := bbase (se 3 (by rfl) ⟨980831, by rfl⟩ : syracuseStep 5231101 = 1961663) (by norm_num)
theorem B6974801 : Blo 2065435 6974801 := bstep (se 2 (by rfl) ⟨2615550, by rfl⟩ : syracuseStep 6974801 = 5231101) B5231101
theorem B4649867 : Blo 2065435 4649867 := bstep (se 1 (by rfl) ⟨3487400, by rfl⟩ : syracuseStep 4649867 = 6974801) B6974801
theorem B3099911 : Blo 2065435 3099911 := bstep (se 1 (by rfl) ⟨2324933, by rfl⟩ : syracuseStep 3099911 = 4649867) B4649867
theorem B2066607 : Blo 2065435 2066607 := bstep (se 1 (by rfl) ⟨1549955, by rfl⟩ : syracuseStep 2066607 = 3099911) B3099911
theorem B3099917 : Blo 2065435 3099917 := bbase (se 3 (by rfl) ⟨581234, by rfl⟩ : syracuseStep 3099917 = 1162469) (by norm_num)
theorem B2066611 : Blo 2065435 2066611 := bstep (se 1 (by rfl) ⟨1549958, by rfl⟩ : syracuseStep 2066611 = 3099917) B3099917
theorem B4649885 : Blo 2065435 4649885 := bbase (se 3 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 4649885 = 1743707) (by norm_num)
theorem B3099923 : Blo 2065435 3099923 := bstep (se 1 (by rfl) ⟨2324942, by rfl⟩ : syracuseStep 3099923 = 4649885) B4649885
theorem B2066615 : Blo 2065435 2066615 := bstep (se 1 (by rfl) ⟨1549961, by rfl⟩ : syracuseStep 2066615 = 3099923) B3099923
theorem B3487421 : Blo 2065435 3487421 := bbase (se 3 (by rfl) ⟨653891, by rfl⟩ : syracuseStep 3487421 = 1307783) (by norm_num)
theorem B2324947 : Blo 2065435 2324947 := bstep (se 1 (by rfl) ⟨1743710, by rfl⟩ : syracuseStep 2324947 = 3487421) B3487421
theorem B3099929 : Blo 2065435 3099929 := bstep (se 2 (by rfl) ⟨1162473, by rfl⟩ : syracuseStep 3099929 = 2324947) B2324947
theorem B2066619 : Blo 2065435 2066619 := bstep (se 1 (by rfl) ⟨1549964, by rfl⟩ : syracuseStep 2066619 = 3099929) B3099929
theorem B11770069 : Blo 2065435 11770069 := bbase (se 7 (by rfl) ⟨137930, by rfl⟩ : syracuseStep 11770069 = 275861) (by norm_num)
theorem B15693425 : Blo 2065435 15693425 := bstep (se 2 (by rfl) ⟨5885034, by rfl⟩ : syracuseStep 15693425 = 11770069) B11770069
theorem B10462283 : Blo 2065435 10462283 := bstep (se 1 (by rfl) ⟨7846712, by rfl⟩ : syracuseStep 10462283 = 15693425) B15693425
theorem B6974855 : Blo 2065435 6974855 := bstep (se 1 (by rfl) ⟨5231141, by rfl⟩ : syracuseStep 6974855 = 10462283) B10462283
theorem B4649903 : Blo 2065435 4649903 := bstep (se 1 (by rfl) ⟨3487427, by rfl⟩ : syracuseStep 4649903 = 6974855) B6974855
theorem B3099935 : Blo 2065435 3099935 := bstep (se 1 (by rfl) ⟨2324951, by rfl⟩ : syracuseStep 3099935 = 4649903) B4649903
theorem B2066623 : Blo 2065435 2066623 := bstep (se 1 (by rfl) ⟨1549967, by rfl⟩ : syracuseStep 2066623 = 3099935) B3099935
theorem B3099941 : Blo 2065435 3099941 := bbase (se 4 (by rfl) ⟨290619, by rfl⟩ : syracuseStep 3099941 = 581239) (by norm_num)
theorem B2066627 : Blo 2065435 2066627 := bstep (se 1 (by rfl) ⟨1549970, by rfl⟩ : syracuseStep 2066627 = 3099941) B3099941
theorem B2615581 : Blo 2065435 2615581 := bbase (se 3 (by rfl) ⟨490421, by rfl⟩ : syracuseStep 2615581 = 980843) (by norm_num)
theorem B3487441 : Blo 2065435 3487441 := bstep (se 2 (by rfl) ⟨1307790, by rfl⟩ : syracuseStep 3487441 = 2615581) B2615581
theorem B4649921 : Blo 2065435 4649921 := bstep (se 2 (by rfl) ⟨1743720, by rfl⟩ : syracuseStep 4649921 = 3487441) B3487441
theorem B3099947 : Blo 2065435 3099947 := bstep (se 1 (by rfl) ⟨2324960, by rfl⟩ : syracuseStep 3099947 = 4649921) B4649921
theorem B2066631 : Blo 2065435 2066631 := bstep (se 1 (by rfl) ⟨1549973, by rfl⟩ : syracuseStep 2066631 = 3099947) B3099947
theorem B2324965 : Blo 2065435 2324965 := bbase (se 4 (by rfl) ⟨217965, by rfl⟩ : syracuseStep 2324965 = 435931) (by norm_num)
theorem B3099953 : Blo 2065435 3099953 := bstep (se 2 (by rfl) ⟨1162482, by rfl⟩ : syracuseStep 3099953 = 2324965) B2324965
theorem B2066635 : Blo 2065435 2066635 := bstep (se 1 (by rfl) ⟨1549976, by rfl⟩ : syracuseStep 2066635 = 3099953) B3099953
theorem B2482769 : Blo 2065435 2482769 := bbase (se 2 (by rfl) ⟨931038, by rfl⟩ : syracuseStep 2482769 = 1862077) (by norm_num)
theorem B6620717 : Blo 2065435 6620717 := bstep (se 3 (by rfl) ⟨1241384, by rfl⟩ : syracuseStep 6620717 = 2482769) B2482769
theorem B4413811 : Blo 2065435 4413811 := bstep (se 1 (by rfl) ⟨3310358, by rfl⟩ : syracuseStep 4413811 = 6620717) B6620717
theorem B5885081 : Blo 2065435 5885081 := bstep (se 2 (by rfl) ⟨2206905, by rfl⟩ : syracuseStep 5885081 = 4413811) B4413811
theorem B3923387 : Blo 2065435 3923387 := bstep (se 1 (by rfl) ⟨2942540, by rfl⟩ : syracuseStep 3923387 = 5885081) B5885081
theorem B2615591 : Blo 2065435 2615591 := bstep (se 1 (by rfl) ⟨1961693, by rfl⟩ : syracuseStep 2615591 = 3923387) B3923387
theorem B6974909 : Blo 2065435 6974909 := bstep (se 3 (by rfl) ⟨1307795, by rfl⟩ : syracuseStep 6974909 = 2615591) B2615591
theorem B4649939 : Blo 2065435 4649939 := bstep (se 1 (by rfl) ⟨3487454, by rfl⟩ : syracuseStep 4649939 = 6974909) B6974909
theorem B3099959 : Blo 2065435 3099959 := bstep (se 1 (by rfl) ⟨2324969, by rfl⟩ : syracuseStep 3099959 = 4649939) B4649939
theorem B2066639 : Blo 2065435 2066639 := bstep (se 1 (by rfl) ⟨1549979, by rfl⟩ : syracuseStep 2066639 = 3099959) B3099959
theorem B3099965 : Blo 2065435 3099965 := bbase (se 3 (by rfl) ⟨581243, by rfl⟩ : syracuseStep 3099965 = 1162487) (by norm_num)
theorem B2066643 : Blo 2065435 2066643 := bstep (se 1 (by rfl) ⟨1549982, by rfl⟩ : syracuseStep 2066643 = 3099965) B3099965
theorem B4649957 : Blo 2065435 4649957 := bbase (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) (by norm_num)
theorem B3099971 : Blo 2065435 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B2066647 : Blo 2065435 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B5231213 : Blo 2065435 5231213 := bbase (se 3 (by rfl) ⟨980852, by rfl⟩ : syracuseStep 5231213 = 1961705) (by norm_num)
theorem B3487475 : Blo 2065435 3487475 := bstep (se 1 (by rfl) ⟨2615606, by rfl⟩ : syracuseStep 3487475 = 5231213) B5231213
theorem B2324983 : Blo 2065435 2324983 := bstep (se 1 (by rfl) ⟨1743737, by rfl⟩ : syracuseStep 2324983 = 3487475) B3487475
theorem B3099977 : Blo 2065435 3099977 := bstep (se 2 (by rfl) ⟨1162491, by rfl⟩ : syracuseStep 3099977 = 2324983) B2324983
theorem B2066651 : Blo 2065435 2066651 := bstep (se 1 (by rfl) ⟨1549988, by rfl⟩ : syracuseStep 2066651 = 3099977) B3099977
theorem B4413845 : Blo 2065435 4413845 := bbase (se 6 (by rfl) ⟨103449, by rfl⟩ : syracuseStep 4413845 = 206899) (by norm_num)
theorem B2942563 : Blo 2065435 2942563 := bstep (se 1 (by rfl) ⟨2206922, by rfl⟩ : syracuseStep 2942563 = 4413845) B4413845
theorem B3923417 : Blo 2065435 3923417 := bstep (se 2 (by rfl) ⟨1471281, by rfl⟩ : syracuseStep 3923417 = 2942563) B2942563
theorem B10462445 : Blo 2065435 10462445 := bstep (se 3 (by rfl) ⟨1961708, by rfl⟩ : syracuseStep 10462445 = 3923417) B3923417
theorem B6974963 : Blo 2065435 6974963 := bstep (se 1 (by rfl) ⟨5231222, by rfl⟩ : syracuseStep 6974963 = 10462445) B10462445
theorem B4649975 : Blo 2065435 4649975 := bstep (se 1 (by rfl) ⟨3487481, by rfl⟩ : syracuseStep 4649975 = 6974963) B6974963
theorem B3099983 : Blo 2065435 3099983 := bstep (se 1 (by rfl) ⟨2324987, by rfl⟩ : syracuseStep 3099983 = 4649975) B4649975
theorem B2066655 : Blo 2065435 2066655 := bstep (se 1 (by rfl) ⟨1549991, by rfl⟩ : syracuseStep 2066655 = 3099983) B3099983
theorem B3099989 : Blo 2065435 3099989 := bbase (se 11 (by rfl) ⟨2270, by rfl⟩ : syracuseStep 3099989 = 4541) (by norm_num)
theorem B2066659 : Blo 2065435 2066659 := bstep (se 1 (by rfl) ⟨1549994, by rfl⟩ : syracuseStep 2066659 = 3099989) B3099989
theorem B3310397 : Blo 2065435 3310397 := bbase (se 3 (by rfl) ⟨620699, by rfl⟩ : syracuseStep 3310397 = 1241399) (by norm_num)
theorem B2206931 : Blo 2065435 2206931 := bstep (se 1 (by rfl) ⟨1655198, by rfl⟩ : syracuseStep 2206931 = 3310397) B3310397
theorem B5885149 : Blo 2065435 5885149 := bstep (se 3 (by rfl) ⟨1103465, by rfl⟩ : syracuseStep 5885149 = 2206931) B2206931
theorem B7846865 : Blo 2065435 7846865 := bstep (se 2 (by rfl) ⟨2942574, by rfl⟩ : syracuseStep 7846865 = 5885149) B5885149
theorem B5231243 : Blo 2065435 5231243 := bstep (se 1 (by rfl) ⟨3923432, by rfl⟩ : syracuseStep 5231243 = 7846865) B7846865
theorem B3487495 : Blo 2065435 3487495 := bstep (se 1 (by rfl) ⟨2615621, by rfl⟩ : syracuseStep 3487495 = 5231243) B5231243
theorem B4649993 : Blo 2065435 4649993 := bstep (se 2 (by rfl) ⟨1743747, by rfl⟩ : syracuseStep 4649993 = 3487495) B3487495
theorem B3099995 : Blo 2065435 3099995 := bstep (se 1 (by rfl) ⟨2324996, by rfl⟩ : syracuseStep 3099995 = 4649993) B4649993
theorem B2066663 : Blo 2065435 2066663 := bstep (se 1 (by rfl) ⟨1549997, by rfl⟩ : syracuseStep 2066663 = 3099995) B3099995
theorem B2325001 : Blo 2065435 2325001 := bbase (se 2 (by rfl) ⟨871875, by rfl⟩ : syracuseStep 2325001 = 1743751) (by norm_num)
theorem B3100001 : Blo 2065435 3100001 := bstep (se 2 (by rfl) ⟨1162500, by rfl⟩ : syracuseStep 3100001 = 2325001) B2325001
theorem B2066667 : Blo 2065435 2066667 := bstep (se 1 (by rfl) ⟨1550000, by rfl⟩ : syracuseStep 2066667 = 3100001) B3100001
theorem B5302637 : Blo 2065435 5302637 := bbase (se 3 (by rfl) ⟨994244, by rfl⟩ : syracuseStep 5302637 = 1988489) (by norm_num)
theorem B3535091 : Blo 2065435 3535091 := bstep (se 1 (by rfl) ⟨2651318, by rfl⟩ : syracuseStep 3535091 = 5302637) B5302637
theorem B2356727 : Blo 2065435 2356727 := bstep (se 1 (by rfl) ⟨1767545, by rfl⟩ : syracuseStep 2356727 = 3535091) B3535091
theorem B25138421 : Blo 2065435 25138421 := bstep (se 5 (by rfl) ⟨1178363, by rfl⟩ : syracuseStep 25138421 = 2356727) B2356727
theorem B16758947 : Blo 2065435 16758947 := bstep (se 1 (by rfl) ⟨12569210, by rfl⟩ : syracuseStep 16758947 = 25138421) B25138421
theorem B44690525 : Blo 2065435 44690525 := bstep (se 3 (by rfl) ⟨8379473, by rfl⟩ : syracuseStep 44690525 = 16758947) B16758947
theorem B29793683 : Blo 2065435 29793683 := bstep (se 1 (by rfl) ⟨22345262, by rfl⟩ : syracuseStep 29793683 = 44690525) B44690525
theorem B19862455 : Blo 2065435 19862455 := bstep (se 1 (by rfl) ⟨14896841, by rfl⟩ : syracuseStep 19862455 = 29793683) B29793683
theorem B26483273 : Blo 2065435 26483273 := bstep (se 2 (by rfl) ⟨9931227, by rfl⟩ : syracuseStep 26483273 = 19862455) B19862455
theorem B17655515 : Blo 2065435 17655515 := bstep (se 1 (by rfl) ⟨13241636, by rfl⟩ : syracuseStep 17655515 = 26483273) B26483273
theorem B11770343 : Blo 2065435 11770343 := bstep (se 1 (by rfl) ⟨8827757, by rfl⟩ : syracuseStep 11770343 = 17655515) B17655515
theorem B7846895 : Blo 2065435 7846895 := bstep (se 1 (by rfl) ⟨5885171, by rfl⟩ : syracuseStep 7846895 = 11770343) B11770343
theorem B5231263 : Blo 2065435 5231263 := bstep (se 1 (by rfl) ⟨3923447, by rfl⟩ : syracuseStep 5231263 = 7846895) B7846895
theorem B6975017 : Blo 2065435 6975017 := bstep (se 2 (by rfl) ⟨2615631, by rfl⟩ : syracuseStep 6975017 = 5231263) B5231263
theorem B4650011 : Blo 2065435 4650011 := bstep (se 1 (by rfl) ⟨3487508, by rfl⟩ : syracuseStep 4650011 = 6975017) B6975017
theorem B3100007 : Blo 2065435 3100007 := bstep (se 1 (by rfl) ⟨2325005, by rfl⟩ : syracuseStep 3100007 = 4650011) B4650011
theorem B2066671 : Blo 2065435 2066671 := bstep (se 1 (by rfl) ⟨1550003, by rfl⟩ : syracuseStep 2066671 = 3100007) B3100007
theorem B3100013 : Blo 2065435 3100013 := bbase (se 3 (by rfl) ⟨581252, by rfl⟩ : syracuseStep 3100013 = 1162505) (by norm_num)
theorem B2066675 : Blo 2065435 2066675 := bstep (se 1 (by rfl) ⟨1550006, by rfl⟩ : syracuseStep 2066675 = 3100013) B3100013
theorem B4650029 : Blo 2065435 4650029 := bbase (se 3 (by rfl) ⟨871880, by rfl⟩ : syracuseStep 4650029 = 1743761) (by norm_num)
theorem B3100019 : Blo 2065435 3100019 := bstep (se 1 (by rfl) ⟨2325014, by rfl⟩ : syracuseStep 3100019 = 4650029) B4650029
theorem B2066679 : Blo 2065435 2066679 := bstep (se 1 (by rfl) ⟨1550009, by rfl⟩ : syracuseStep 2066679 = 3100019) B3100019
theorem B13241717 : Blo 2065435 13241717 := bbase (se 5 (by rfl) ⟨620705, by rfl⟩ : syracuseStep 13241717 = 1241411) (by norm_num)
theorem B8827811 : Blo 2065435 8827811 := bstep (se 1 (by rfl) ⟨6620858, by rfl⟩ : syracuseStep 8827811 = 13241717) B13241717
theorem B5885207 : Blo 2065435 5885207 := bstep (se 1 (by rfl) ⟨4413905, by rfl⟩ : syracuseStep 5885207 = 8827811) B8827811
theorem B3923471 : Blo 2065435 3923471 := bstep (se 1 (by rfl) ⟨2942603, by rfl⟩ : syracuseStep 3923471 = 5885207) B5885207
theorem B2615647 : Blo 2065435 2615647 := bstep (se 1 (by rfl) ⟨1961735, by rfl⟩ : syracuseStep 2615647 = 3923471) B3923471
theorem B3487529 : Blo 2065435 3487529 := bstep (se 2 (by rfl) ⟨1307823, by rfl⟩ : syracuseStep 3487529 = 2615647) B2615647
theorem B2325019 : Blo 2065435 2325019 := bstep (se 1 (by rfl) ⟨1743764, by rfl⟩ : syracuseStep 2325019 = 3487529) B3487529
theorem B3100025 : Blo 2065435 3100025 := bstep (se 2 (by rfl) ⟨1162509, by rfl⟩ : syracuseStep 3100025 = 2325019) B2325019
theorem B2066683 : Blo 2065435 2066683 := bstep (se 1 (by rfl) ⟨1550012, by rfl⟩ : syracuseStep 2066683 = 3100025) B3100025
theorem B6620869 : Blo 2065435 6620869 := bbase (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) (by norm_num)
theorem B35311301 : Blo 2065435 35311301 := bstep (se 4 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 35311301 = 6620869) B6620869
theorem B23540867 : Blo 2065435 23540867 := bstep (se 1 (by rfl) ⟨17655650, by rfl⟩ : syracuseStep 23540867 = 35311301) B35311301
theorem B15693911 : Blo 2065435 15693911 := bstep (se 1 (by rfl) ⟨11770433, by rfl⟩ : syracuseStep 15693911 = 23540867) B23540867
theorem B10462607 : Blo 2065435 10462607 := bstep (se 1 (by rfl) ⟨7846955, by rfl⟩ : syracuseStep 10462607 = 15693911) B15693911
theorem B6975071 : Blo 2065435 6975071 := bstep (se 1 (by rfl) ⟨5231303, by rfl⟩ : syracuseStep 6975071 = 10462607) B10462607
theorem B4650047 : Blo 2065435 4650047 := bstep (se 1 (by rfl) ⟨3487535, by rfl⟩ : syracuseStep 4650047 = 6975071) B6975071
theorem B3100031 : Blo 2065435 3100031 := bstep (se 1 (by rfl) ⟨2325023, by rfl⟩ : syracuseStep 3100031 = 4650047) B4650047
theorem B2066687 : Blo 2065435 2066687 := bstep (se 1 (by rfl) ⟨1550015, by rfl⟩ : syracuseStep 2066687 = 3100031) B3100031
theorem B3100037 : Blo 2065435 3100037 := bbase (se 4 (by rfl) ⟨290628, by rfl⟩ : syracuseStep 3100037 = 581257) (by norm_num)
theorem B2066691 : Blo 2065435 2066691 := bstep (se 1 (by rfl) ⟨1550018, by rfl⟩ : syracuseStep 2066691 = 3100037) B3100037
theorem B3487549 : Blo 2065435 3487549 := bbase (se 3 (by rfl) ⟨653915, by rfl⟩ : syracuseStep 3487549 = 1307831) (by norm_num)
theorem B4650065 : Blo 2065435 4650065 := bstep (se 2 (by rfl) ⟨1743774, by rfl⟩ : syracuseStep 4650065 = 3487549) B3487549
theorem B3100043 : Blo 2065435 3100043 := bstep (se 1 (by rfl) ⟨2325032, by rfl⟩ : syracuseStep 3100043 = 4650065) B4650065
theorem B2066695 : Blo 2065435 2066695 := bstep (se 1 (by rfl) ⟨1550021, by rfl⟩ : syracuseStep 2066695 = 3100043) B3100043
theorem B2325037 : Blo 2065435 2325037 := bbase (se 3 (by rfl) ⟨435944, by rfl⟩ : syracuseStep 2325037 = 871889) (by norm_num)
theorem B3100049 : Blo 2065435 3100049 := bstep (se 2 (by rfl) ⟨1162518, by rfl⟩ : syracuseStep 3100049 = 2325037) B2325037
theorem B2066699 : Blo 2065435 2066699 := bstep (se 1 (by rfl) ⟨1550024, by rfl⟩ : syracuseStep 2066699 = 3100049) B3100049
theorem B6975125 : Blo 2065435 6975125 := bbase (se 6 (by rfl) ⟨163479, by rfl⟩ : syracuseStep 6975125 = 326959) (by norm_num)
theorem B4650083 : Blo 2065435 4650083 := bstep (se 1 (by rfl) ⟨3487562, by rfl⟩ : syracuseStep 4650083 = 6975125) B6975125
theorem B3100055 : Blo 2065435 3100055 := bstep (se 1 (by rfl) ⟨2325041, by rfl⟩ : syracuseStep 3100055 = 4650083) B4650083
theorem B2066703 : Blo 2065435 2066703 := bstep (se 1 (by rfl) ⟨1550027, by rfl⟩ : syracuseStep 2066703 = 3100055) B3100055
theorem B3100061 : Blo 2065435 3100061 := bbase (se 3 (by rfl) ⟨581261, by rfl⟩ : syracuseStep 3100061 = 1162523) (by norm_num)
theorem B2066707 : Blo 2065435 2066707 := bstep (se 1 (by rfl) ⟨1550030, by rfl⟩ : syracuseStep 2066707 = 3100061) B3100061
theorem B4650101 : Blo 2065435 4650101 := bbase (se 5 (by rfl) ⟨217973, by rfl⟩ : syracuseStep 4650101 = 435947) (by norm_num)
theorem B3100067 : Blo 2065435 3100067 := bstep (se 1 (by rfl) ⟨2325050, by rfl⟩ : syracuseStep 3100067 = 4650101) B4650101
theorem B2066711 : Blo 2065435 2066711 := bstep (se 1 (by rfl) ⟨1550033, by rfl⟩ : syracuseStep 2066711 = 3100067) B3100067
theorem B17655893 : Blo 2065435 17655893 := bbase (se 8 (by rfl) ⟨103452, by rfl⟩ : syracuseStep 17655893 = 206905) (by norm_num)
theorem B11770595 : Blo 2065435 11770595 := bstep (se 1 (by rfl) ⟨8827946, by rfl⟩ : syracuseStep 11770595 = 17655893) B17655893
theorem B7847063 : Blo 2065435 7847063 := bstep (se 1 (by rfl) ⟨5885297, by rfl⟩ : syracuseStep 7847063 = 11770595) B11770595
theorem B5231375 : Blo 2065435 5231375 := bstep (se 1 (by rfl) ⟨3923531, by rfl⟩ : syracuseStep 5231375 = 7847063) B7847063
theorem B3487583 : Blo 2065435 3487583 := bstep (se 1 (by rfl) ⟨2615687, by rfl⟩ : syracuseStep 3487583 = 5231375) B5231375
theorem B2325055 : Blo 2065435 2325055 := bstep (se 1 (by rfl) ⟨1743791, by rfl⟩ : syracuseStep 2325055 = 3487583) B3487583
theorem B3100073 : Blo 2065435 3100073 := bstep (se 2 (by rfl) ⟨1162527, by rfl⟩ : syracuseStep 3100073 = 2325055) B2325055
theorem B2066715 : Blo 2065435 2066715 := bstep (se 1 (by rfl) ⟨1550036, by rfl⟩ : syracuseStep 2066715 = 3100073) B3100073
theorem B7847077 : Blo 2065435 7847077 := bbase (se 4 (by rfl) ⟨735663, by rfl⟩ : syracuseStep 7847077 = 1471327) (by norm_num)
theorem B10462769 : Blo 2065435 10462769 := bstep (se 2 (by rfl) ⟨3923538, by rfl⟩ : syracuseStep 10462769 = 7847077) B7847077
theorem B6975179 : Blo 2065435 6975179 := bstep (se 1 (by rfl) ⟨5231384, by rfl⟩ : syracuseStep 6975179 = 10462769) B10462769
theorem B4650119 : Blo 2065435 4650119 := bstep (se 1 (by rfl) ⟨3487589, by rfl⟩ : syracuseStep 4650119 = 6975179) B6975179
theorem B3100079 : Blo 2065435 3100079 := bstep (se 1 (by rfl) ⟨2325059, by rfl⟩ : syracuseStep 3100079 = 4650119) B4650119
theorem B2066719 : Blo 2065435 2066719 := bstep (se 1 (by rfl) ⟨1550039, by rfl⟩ : syracuseStep 2066719 = 3100079) B3100079
theorem B3100085 : Blo 2065435 3100085 := bbase (se 5 (by rfl) ⟨145316, by rfl⟩ : syracuseStep 3100085 = 290633) (by norm_num)
theorem B2066723 : Blo 2065435 2066723 := bstep (se 1 (by rfl) ⟨1550042, by rfl⟩ : syracuseStep 2066723 = 3100085) B3100085
theorem B5231405 : Blo 2065435 5231405 := bbase (se 3 (by rfl) ⟨980888, by rfl⟩ : syracuseStep 5231405 = 1961777) (by norm_num)
theorem B3487603 : Blo 2065435 3487603 := bstep (se 1 (by rfl) ⟨2615702, by rfl⟩ : syracuseStep 3487603 = 5231405) B5231405
theorem B4650137 : Blo 2065435 4650137 := bstep (se 2 (by rfl) ⟨1743801, by rfl⟩ : syracuseStep 4650137 = 3487603) B3487603
theorem B3100091 : Blo 2065435 3100091 := bstep (se 1 (by rfl) ⟨2325068, by rfl⟩ : syracuseStep 3100091 = 4650137) B4650137
theorem B2066727 : Blo 2065435 2066727 := bstep (se 1 (by rfl) ⟨1550045, by rfl⟩ : syracuseStep 2066727 = 3100091) B3100091
theorem B2325073 : Blo 2065435 2325073 := bbase (se 2 (by rfl) ⟨871902, by rfl⟩ : syracuseStep 2325073 = 1743805) (by norm_num)
theorem B3100097 : Blo 2065435 3100097 := bstep (se 2 (by rfl) ⟨1162536, by rfl⟩ : syracuseStep 3100097 = 2325073) B2325073
theorem B2066731 : Blo 2065435 2066731 := bstep (se 1 (by rfl) ⟨1550048, by rfl⟩ : syracuseStep 2066731 = 3100097) B3100097
theorem B2942677 : Blo 2065435 2942677 := bbase (se 7 (by rfl) ⟨34484, by rfl⟩ : syracuseStep 2942677 = 68969) (by norm_num)
theorem B3923569 : Blo 2065435 3923569 := bstep (se 2 (by rfl) ⟨1471338, by rfl⟩ : syracuseStep 3923569 = 2942677) B2942677
theorem B5231425 : Blo 2065435 5231425 := bstep (se 2 (by rfl) ⟨1961784, by rfl⟩ : syracuseStep 5231425 = 3923569) B3923569
theorem B6975233 : Blo 2065435 6975233 := bstep (se 2 (by rfl) ⟨2615712, by rfl⟩ : syracuseStep 6975233 = 5231425) B5231425
theorem B4650155 : Blo 2065435 4650155 := bstep (se 1 (by rfl) ⟨3487616, by rfl⟩ : syracuseStep 4650155 = 6975233) B6975233
theorem B3100103 : Blo 2065435 3100103 := bstep (se 1 (by rfl) ⟨2325077, by rfl⟩ : syracuseStep 3100103 = 4650155) B4650155
theorem B2066735 : Blo 2065435 2066735 := bstep (se 1 (by rfl) ⟨1550051, by rfl⟩ : syracuseStep 2066735 = 3100103) B3100103
theorem B3100109 : Blo 2065435 3100109 := bbase (se 3 (by rfl) ⟨581270, by rfl⟩ : syracuseStep 3100109 = 1162541) (by norm_num)
theorem B2066739 : Blo 2065435 2066739 := bstep (se 1 (by rfl) ⟨1550054, by rfl⟩ : syracuseStep 2066739 = 3100109) B3100109
theorem B4650173 : Blo 2065435 4650173 := bbase (se 3 (by rfl) ⟨871907, by rfl⟩ : syracuseStep 4650173 = 1743815) (by norm_num)
theorem B3100115 : Blo 2065435 3100115 := bstep (se 1 (by rfl) ⟨2325086, by rfl⟩ : syracuseStep 3100115 = 4650173) B4650173
theorem B2066743 : Blo 2065435 2066743 := bstep (se 1 (by rfl) ⟨1550057, by rfl⟩ : syracuseStep 2066743 = 3100115) B3100115
theorem B3487637 : Blo 2065435 3487637 := bbase (se 6 (by rfl) ⟨81741, by rfl⟩ : syracuseStep 3487637 = 163483) (by norm_num)
theorem B2325091 : Blo 2065435 2325091 := bstep (se 1 (by rfl) ⟨1743818, by rfl⟩ : syracuseStep 2325091 = 3487637) B3487637
theorem B3100121 : Blo 2065435 3100121 := bstep (se 2 (by rfl) ⟨1162545, by rfl⟩ : syracuseStep 3100121 = 2325091) B2325091
theorem B2066747 : Blo 2065435 2066747 := bstep (se 1 (by rfl) ⟨1550060, by rfl⟩ : syracuseStep 2066747 = 3100121) B3100121
theorem B5586533 : Blo 2065435 5586533 := bbase (se 4 (by rfl) ⟨523737, by rfl⟩ : syracuseStep 5586533 = 1047475) (by norm_num)
theorem B3724355 : Blo 2065435 3724355 := bstep (se 1 (by rfl) ⟨2793266, by rfl⟩ : syracuseStep 3724355 = 5586533) B5586533
theorem B2482903 : Blo 2065435 2482903 := bstep (se 1 (by rfl) ⟨1862177, by rfl⟩ : syracuseStep 2482903 = 3724355) B3724355
theorem B13242149 : Blo 2065435 13242149 := bstep (se 4 (by rfl) ⟨1241451, by rfl⟩ : syracuseStep 13242149 = 2482903) B2482903
theorem B8828099 : Blo 2065435 8828099 := bstep (se 1 (by rfl) ⟨6621074, by rfl⟩ : syracuseStep 8828099 = 13242149) B13242149
theorem B5885399 : Blo 2065435 5885399 := bstep (se 1 (by rfl) ⟨4414049, by rfl⟩ : syracuseStep 5885399 = 8828099) B8828099
theorem B15694397 : Blo 2065435 15694397 := bstep (se 3 (by rfl) ⟨2942699, by rfl⟩ : syracuseStep 15694397 = 5885399) B5885399
theorem B10462931 : Blo 2065435 10462931 := bstep (se 1 (by rfl) ⟨7847198, by rfl⟩ : syracuseStep 10462931 = 15694397) B15694397
theorem B6975287 : Blo 2065435 6975287 := bstep (se 1 (by rfl) ⟨5231465, by rfl⟩ : syracuseStep 6975287 = 10462931) B10462931
theorem B4650191 : Blo 2065435 4650191 := bstep (se 1 (by rfl) ⟨3487643, by rfl⟩ : syracuseStep 4650191 = 6975287) B6975287
theorem B3100127 : Blo 2065435 3100127 := bstep (se 1 (by rfl) ⟨2325095, by rfl⟩ : syracuseStep 3100127 = 4650191) B4650191
theorem B2066751 : Blo 2065435 2066751 := bstep (se 1 (by rfl) ⟨1550063, by rfl⟩ : syracuseStep 2066751 = 3100127) B3100127
theorem B3100133 : Blo 2065435 3100133 := bbase (se 4 (by rfl) ⟨290637, by rfl⟩ : syracuseStep 3100133 = 581275) (by norm_num)
theorem B2066755 : Blo 2065435 2066755 := bstep (se 1 (by rfl) ⟨1550066, by rfl⟩ : syracuseStep 2066755 = 3100133) B3100133
theorem B35794325 : Blo 2065435 35794325 := bbase (se 6 (by rfl) ⟨838929, by rfl⟩ : syracuseStep 35794325 = 1677859) (by norm_num)
theorem B95451533 : Blo 2065435 95451533 := bstep (se 3 (by rfl) ⟨17897162, by rfl⟩ : syracuseStep 95451533 = 35794325) B35794325
theorem B63634355 : Blo 2065435 63634355 := bstep (se 1 (by rfl) ⟨47725766, by rfl⟩ : syracuseStep 63634355 = 95451533) B95451533
theorem B42422903 : Blo 2065435 42422903 := bstep (se 1 (by rfl) ⟨31817177, by rfl⟩ : syracuseStep 42422903 = 63634355) B63634355
theorem B28281935 : Blo 2065435 28281935 := bstep (se 1 (by rfl) ⟨21211451, by rfl⟩ : syracuseStep 28281935 = 42422903) B42422903
theorem B18854623 : Blo 2065435 18854623 := bstep (se 1 (by rfl) ⟨14140967, by rfl⟩ : syracuseStep 18854623 = 28281935) B28281935
theorem B25139497 : Blo 2065435 25139497 := bstep (se 2 (by rfl) ⟨9427311, by rfl⟩ : syracuseStep 25139497 = 18854623) B18854623
theorem B33519329 : Blo 2065435 33519329 := bstep (se 2 (by rfl) ⟨12569748, by rfl⟩ : syracuseStep 33519329 = 25139497) B25139497
theorem B22346219 : Blo 2065435 22346219 := bstep (se 1 (by rfl) ⟨16759664, by rfl⟩ : syracuseStep 22346219 = 33519329) B33519329
theorem B14897479 : Blo 2065435 14897479 := bstep (se 1 (by rfl) ⟨11173109, by rfl⟩ : syracuseStep 14897479 = 22346219) B22346219
theorem B19863305 : Blo 2065435 19863305 := bstep (se 2 (by rfl) ⟨7448739, by rfl⟩ : syracuseStep 19863305 = 14897479) B14897479
theorem B13242203 : Blo 2065435 13242203 := bstep (se 1 (by rfl) ⟨9931652, by rfl⟩ : syracuseStep 13242203 = 19863305) B19863305
theorem B8828135 : Blo 2065435 8828135 := bstep (se 1 (by rfl) ⟨6621101, by rfl⟩ : syracuseStep 8828135 = 13242203) B13242203
theorem B5885423 : Blo 2065435 5885423 := bstep (se 1 (by rfl) ⟨4414067, by rfl⟩ : syracuseStep 5885423 = 8828135) B8828135
theorem B3923615 : Blo 2065435 3923615 := bstep (se 1 (by rfl) ⟨2942711, by rfl⟩ : syracuseStep 3923615 = 5885423) B5885423
theorem B2615743 : Blo 2065435 2615743 := bstep (se 1 (by rfl) ⟨1961807, by rfl⟩ : syracuseStep 2615743 = 3923615) B3923615
theorem B3487657 : Blo 2065435 3487657 := bstep (se 2 (by rfl) ⟨1307871, by rfl⟩ : syracuseStep 3487657 = 2615743) B2615743
theorem B4650209 : Blo 2065435 4650209 := bstep (se 2 (by rfl) ⟨1743828, by rfl⟩ : syracuseStep 4650209 = 3487657) B3487657
theorem B3100139 : Blo 2065435 3100139 := bstep (se 1 (by rfl) ⟨2325104, by rfl⟩ : syracuseStep 3100139 = 4650209) B4650209
theorem B2066759 : Blo 2065435 2066759 := bstep (se 1 (by rfl) ⟨1550069, by rfl⟩ : syracuseStep 2066759 = 3100139) B3100139
theorem B2325109 : Blo 2065435 2325109 := bbase (se 5 (by rfl) ⟨108989, by rfl⟩ : syracuseStep 2325109 = 217979) (by norm_num)
theorem B3100145 : Blo 2065435 3100145 := bstep (se 2 (by rfl) ⟨1162554, by rfl⟩ : syracuseStep 3100145 = 2325109) B2325109
theorem B2066763 : Blo 2065435 2066763 := bstep (se 1 (by rfl) ⟨1550072, by rfl⟩ : syracuseStep 2066763 = 3100145) B3100145
theorem B2615753 : Blo 2065435 2615753 := bbase (se 2 (by rfl) ⟨980907, by rfl⟩ : syracuseStep 2615753 = 1961815) (by norm_num)
theorem B6975341 : Blo 2065435 6975341 := bstep (se 3 (by rfl) ⟨1307876, by rfl⟩ : syracuseStep 6975341 = 2615753) B2615753
theorem B4650227 : Blo 2065435 4650227 := bstep (se 1 (by rfl) ⟨3487670, by rfl⟩ : syracuseStep 4650227 = 6975341) B6975341
theorem B3100151 : Blo 2065435 3100151 := bstep (se 1 (by rfl) ⟨2325113, by rfl⟩ : syracuseStep 3100151 = 4650227) B4650227
theorem B2066767 : Blo 2065435 2066767 := bstep (se 1 (by rfl) ⟨1550075, by rfl⟩ : syracuseStep 2066767 = 3100151) B3100151
theorem B3100157 : Blo 2065435 3100157 := bbase (se 3 (by rfl) ⟨581279, by rfl⟩ : syracuseStep 3100157 = 1162559) (by norm_num)
theorem B2066771 : Blo 2065435 2066771 := bstep (se 1 (by rfl) ⟨1550078, by rfl⟩ : syracuseStep 2066771 = 3100157) B3100157
theorem B4650245 : Blo 2065435 4650245 := bbase (se 4 (by rfl) ⟨435960, by rfl⟩ : syracuseStep 4650245 = 871921) (by norm_num)
theorem B3100163 : Blo 2065435 3100163 := bstep (se 1 (by rfl) ⟨2325122, by rfl⟩ : syracuseStep 3100163 = 4650245) B4650245
theorem B2066775 : Blo 2065435 2066775 := bstep (se 1 (by rfl) ⟨1550081, by rfl⟩ : syracuseStep 2066775 = 3100163) B3100163
theorem B3923653 : Blo 2065435 3923653 := bbase (se 4 (by rfl) ⟨367842, by rfl⟩ : syracuseStep 3923653 = 735685) (by norm_num)
theorem B5231537 : Blo 2065435 5231537 := bstep (se 2 (by rfl) ⟨1961826, by rfl⟩ : syracuseStep 5231537 = 3923653) B3923653
theorem B3487691 : Blo 2065435 3487691 := bstep (se 1 (by rfl) ⟨2615768, by rfl⟩ : syracuseStep 3487691 = 5231537) B5231537
theorem B2325127 : Blo 2065435 2325127 := bstep (se 1 (by rfl) ⟨1743845, by rfl⟩ : syracuseStep 2325127 = 3487691) B3487691
theorem B3100169 : Blo 2065435 3100169 := bstep (se 2 (by rfl) ⟨1162563, by rfl⟩ : syracuseStep 3100169 = 2325127) B2325127
theorem B2066779 : Blo 2065435 2066779 := bstep (se 1 (by rfl) ⟨1550084, by rfl⟩ : syracuseStep 2066779 = 3100169) B3100169
theorem B10463093 : Blo 2065435 10463093 := bbase (se 5 (by rfl) ⟨490457, by rfl⟩ : syracuseStep 10463093 = 980915) (by norm_num)
theorem B6975395 : Blo 2065435 6975395 := bstep (se 1 (by rfl) ⟨5231546, by rfl⟩ : syracuseStep 6975395 = 10463093) B10463093
theorem B4650263 : Blo 2065435 4650263 := bstep (se 1 (by rfl) ⟨3487697, by rfl⟩ : syracuseStep 4650263 = 6975395) B6975395
theorem B3100175 : Blo 2065435 3100175 := bstep (se 1 (by rfl) ⟨2325131, by rfl⟩ : syracuseStep 3100175 = 4650263) B4650263
theorem B2066783 : Blo 2065435 2066783 := bstep (se 1 (by rfl) ⟨1550087, by rfl⟩ : syracuseStep 2066783 = 3100175) B3100175
theorem B3100181 : Blo 2065435 3100181 := bbase (se 6 (by rfl) ⟨72660, by rfl⟩ : syracuseStep 3100181 = 145321) (by norm_num)
theorem B2066787 : Blo 2065435 2066787 := bstep (se 1 (by rfl) ⟨1550090, by rfl⟩ : syracuseStep 2066787 = 3100181) B3100181
theorem B4189981 : Blo 2065435 4189981 := bbase (se 3 (by rfl) ⟨785621, by rfl⟩ : syracuseStep 4189981 = 1571243) (by norm_num)
theorem B5586641 : Blo 2065435 5586641 := bstep (se 2 (by rfl) ⟨2094990, by rfl⟩ : syracuseStep 5586641 = 4189981) B4189981
theorem B3724427 : Blo 2065435 3724427 := bstep (se 1 (by rfl) ⟨2793320, by rfl⟩ : syracuseStep 3724427 = 5586641) B5586641
theorem B9931805 : Blo 2065435 9931805 := bstep (se 3 (by rfl) ⟨1862213, by rfl⟩ : syracuseStep 9931805 = 3724427) B3724427
theorem B6621203 : Blo 2065435 6621203 := bstep (se 1 (by rfl) ⟨4965902, by rfl⟩ : syracuseStep 6621203 = 9931805) B9931805
theorem B17656541 : Blo 2065435 17656541 := bstep (se 3 (by rfl) ⟨3310601, by rfl⟩ : syracuseStep 17656541 = 6621203) B6621203
theorem B11771027 : Blo 2065435 11771027 := bstep (se 1 (by rfl) ⟨8828270, by rfl⟩ : syracuseStep 11771027 = 17656541) B17656541
theorem B7847351 : Blo 2065435 7847351 := bstep (se 1 (by rfl) ⟨5885513, by rfl⟩ : syracuseStep 7847351 = 11771027) B11771027
theorem B5231567 : Blo 2065435 5231567 := bstep (se 1 (by rfl) ⟨3923675, by rfl⟩ : syracuseStep 5231567 = 7847351) B7847351
theorem B3487711 : Blo 2065435 3487711 := bstep (se 1 (by rfl) ⟨2615783, by rfl⟩ : syracuseStep 3487711 = 5231567) B5231567
theorem B4650281 : Blo 2065435 4650281 := bstep (se 2 (by rfl) ⟨1743855, by rfl⟩ : syracuseStep 4650281 = 3487711) B3487711
theorem B3100187 : Blo 2065435 3100187 := bstep (se 1 (by rfl) ⟨2325140, by rfl⟩ : syracuseStep 3100187 = 4650281) B4650281
theorem B2066791 : Blo 2065435 2066791 := bstep (se 1 (by rfl) ⟨1550093, by rfl⟩ : syracuseStep 2066791 = 3100187) B3100187
theorem B2325145 : Blo 2065435 2325145 := bbase (se 2 (by rfl) ⟨871929, by rfl⟩ : syracuseStep 2325145 = 1743859) (by norm_num)
theorem B3100193 : Blo 2065435 3100193 := bstep (se 2 (by rfl) ⟨1162572, by rfl⟩ : syracuseStep 3100193 = 2325145) B2325145
theorem B2066795 : Blo 2065435 2066795 := bstep (se 1 (by rfl) ⟨1550096, by rfl⟩ : syracuseStep 2066795 = 3100193) B3100193
theorem B7847381 : Blo 2065435 7847381 := bbase (se 7 (by rfl) ⟨91961, by rfl⟩ : syracuseStep 7847381 = 183923) (by norm_num)
theorem B5231587 : Blo 2065435 5231587 := bstep (se 1 (by rfl) ⟨3923690, by rfl⟩ : syracuseStep 5231587 = 7847381) B7847381
theorem B6975449 : Blo 2065435 6975449 := bstep (se 2 (by rfl) ⟨2615793, by rfl⟩ : syracuseStep 6975449 = 5231587) B5231587
theorem B4650299 : Blo 2065435 4650299 := bstep (se 1 (by rfl) ⟨3487724, by rfl⟩ : syracuseStep 4650299 = 6975449) B6975449
theorem B3100199 : Blo 2065435 3100199 := bstep (se 1 (by rfl) ⟨2325149, by rfl⟩ : syracuseStep 3100199 = 4650299) B4650299
theorem B2066799 : Blo 2065435 2066799 := bstep (se 1 (by rfl) ⟨1550099, by rfl⟩ : syracuseStep 2066799 = 3100199) B3100199
theorem B3100205 : Blo 2065435 3100205 := bbase (se 3 (by rfl) ⟨581288, by rfl⟩ : syracuseStep 3100205 = 1162577) (by norm_num)
theorem B2066803 : Blo 2065435 2066803 := bstep (se 1 (by rfl) ⟨1550102, by rfl⟩ : syracuseStep 2066803 = 3100205) B3100205
theorem B4650317 : Blo 2065435 4650317 := bbase (se 3 (by rfl) ⟨871934, by rfl⟩ : syracuseStep 4650317 = 1743869) (by norm_num)
theorem B3100211 : Blo 2065435 3100211 := bstep (se 1 (by rfl) ⟨2325158, by rfl⟩ : syracuseStep 3100211 = 4650317) B4650317
theorem B2066807 : Blo 2065435 2066807 := bstep (se 1 (by rfl) ⟨1550105, by rfl⟩ : syracuseStep 2066807 = 3100211) B3100211
theorem B2615809 : Blo 2065435 2615809 := bbase (se 2 (by rfl) ⟨980928, by rfl⟩ : syracuseStep 2615809 = 1961857) (by norm_num)
theorem B3487745 : Blo 2065435 3487745 := bstep (se 2 (by rfl) ⟨1307904, by rfl⟩ : syracuseStep 3487745 = 2615809) B2615809
theorem B2325163 : Blo 2065435 2325163 := bstep (se 1 (by rfl) ⟨1743872, by rfl⟩ : syracuseStep 2325163 = 3487745) B3487745
theorem B3100217 : Blo 2065435 3100217 := bstep (se 2 (by rfl) ⟨1162581, by rfl⟩ : syracuseStep 3100217 = 2325163) B2325163
theorem B2066811 : Blo 2065435 2066811 := bstep (se 1 (by rfl) ⟨1550108, by rfl⟩ : syracuseStep 2066811 = 3100217) B3100217
theorem B2207093 : Blo 2065435 2207093 := bbase (se 5 (by rfl) ⟨103457, by rfl⟩ : syracuseStep 2207093 = 206915) (by norm_num)
theorem B23542325 : Blo 2065435 23542325 := bstep (se 5 (by rfl) ⟨1103546, by rfl⟩ : syracuseStep 23542325 = 2207093) B2207093
theorem B15694883 : Blo 2065435 15694883 := bstep (se 1 (by rfl) ⟨11771162, by rfl⟩ : syracuseStep 15694883 = 23542325) B23542325
theorem B10463255 : Blo 2065435 10463255 := bstep (se 1 (by rfl) ⟨7847441, by rfl⟩ : syracuseStep 10463255 = 15694883) B15694883
theorem B6975503 : Blo 2065435 6975503 := bstep (se 1 (by rfl) ⟨5231627, by rfl⟩ : syracuseStep 6975503 = 10463255) B10463255
theorem B4650335 : Blo 2065435 4650335 := bstep (se 1 (by rfl) ⟨3487751, by rfl⟩ : syracuseStep 4650335 = 6975503) B6975503
theorem B3100223 : Blo 2065435 3100223 := bstep (se 1 (by rfl) ⟨2325167, by rfl⟩ : syracuseStep 3100223 = 4650335) B4650335
theorem B2066815 : Blo 2065435 2066815 := bstep (se 1 (by rfl) ⟨1550111, by rfl⟩ : syracuseStep 2066815 = 3100223) B3100223
theorem B3100229 : Blo 2065435 3100229 := bbase (se 4 (by rfl) ⟨290646, by rfl⟩ : syracuseStep 3100229 = 581293) (by norm_num)
theorem B2066819 : Blo 2065435 2066819 := bstep (se 1 (by rfl) ⟨1550114, by rfl⟩ : syracuseStep 2066819 = 3100229) B3100229
theorem B3487765 : Blo 2065435 3487765 := bbase (se 6 (by rfl) ⟨81744, by rfl⟩ : syracuseStep 3487765 = 163489) (by norm_num)
theorem B4650353 : Blo 2065435 4650353 := bstep (se 2 (by rfl) ⟨1743882, by rfl⟩ : syracuseStep 4650353 = 3487765) B3487765
theorem B3100235 : Blo 2065435 3100235 := bstep (se 1 (by rfl) ⟨2325176, by rfl⟩ : syracuseStep 3100235 = 4650353) B4650353
theorem B2066823 : Blo 2065435 2066823 := bstep (se 1 (by rfl) ⟨1550117, by rfl⟩ : syracuseStep 2066823 = 3100235) B3100235
theorem B2325181 : Blo 2065435 2325181 := bbase (se 3 (by rfl) ⟨435971, by rfl⟩ : syracuseStep 2325181 = 871943) (by norm_num)
theorem B3100241 : Blo 2065435 3100241 := bstep (se 2 (by rfl) ⟨1162590, by rfl⟩ : syracuseStep 3100241 = 2325181) B2325181
theorem B2066827 : Blo 2065435 2066827 := bstep (se 1 (by rfl) ⟨1550120, by rfl⟩ : syracuseStep 2066827 = 3100241) B3100241
theorem B6975557 : Blo 2065435 6975557 := bbase (se 4 (by rfl) ⟨653958, by rfl⟩ : syracuseStep 6975557 = 1307917) (by norm_num)
theorem B4650371 : Blo 2065435 4650371 := bstep (se 1 (by rfl) ⟨3487778, by rfl⟩ : syracuseStep 4650371 = 6975557) B6975557
theorem B3100247 : Blo 2065435 3100247 := bstep (se 1 (by rfl) ⟨2325185, by rfl⟩ : syracuseStep 3100247 = 4650371) B4650371
theorem B2066831 : Blo 2065435 2066831 := bstep (se 1 (by rfl) ⟨1550123, by rfl⟩ : syracuseStep 2066831 = 3100247) B3100247
theorem B3100253 : Blo 2065435 3100253 := bbase (se 3 (by rfl) ⟨581297, by rfl⟩ : syracuseStep 3100253 = 1162595) (by norm_num)
theorem B2066835 : Blo 2065435 2066835 := bstep (se 1 (by rfl) ⟨1550126, by rfl⟩ : syracuseStep 2066835 = 3100253) B3100253
theorem B4650389 : Blo 2065435 4650389 := bbase (se 6 (by rfl) ⟨108993, by rfl⟩ : syracuseStep 4650389 = 217987) (by norm_num)
theorem B3100259 : Blo 2065435 3100259 := bstep (se 1 (by rfl) ⟨2325194, by rfl⟩ : syracuseStep 3100259 = 4650389) B4650389
theorem B2066839 : Blo 2065435 2066839 := bstep (se 1 (by rfl) ⟨1550129, by rfl⟩ : syracuseStep 2066839 = 3100259) B3100259
theorem B7070773 : Blo 2065435 7070773 := bbase (se 5 (by rfl) ⟨331442, by rfl⟩ : syracuseStep 7070773 = 662885) (by norm_num)
theorem B9427697 : Blo 2065435 9427697 := bstep (se 2 (by rfl) ⟨3535386, by rfl⟩ : syracuseStep 9427697 = 7070773) B7070773
theorem B6285131 : Blo 2065435 6285131 := bstep (se 1 (by rfl) ⟨4713848, by rfl⟩ : syracuseStep 6285131 = 9427697) B9427697
theorem B4190087 : Blo 2065435 4190087 := bstep (se 1 (by rfl) ⟨3142565, by rfl⟩ : syracuseStep 4190087 = 6285131) B6285131
theorem B11173565 : Blo 2065435 11173565 := bstep (se 3 (by rfl) ⟨2095043, by rfl⟩ : syracuseStep 11173565 = 4190087) B4190087
theorem B7449043 : Blo 2065435 7449043 := bstep (se 1 (by rfl) ⟨5586782, by rfl⟩ : syracuseStep 7449043 = 11173565) B11173565
theorem B9932057 : Blo 2065435 9932057 := bstep (se 2 (by rfl) ⟨3724521, by rfl⟩ : syracuseStep 9932057 = 7449043) B7449043
theorem B6621371 : Blo 2065435 6621371 := bstep (se 1 (by rfl) ⟨4966028, by rfl⟩ : syracuseStep 6621371 = 9932057) B9932057
theorem B4414247 : Blo 2065435 4414247 := bstep (se 1 (by rfl) ⟨3310685, by rfl⟩ : syracuseStep 4414247 = 6621371) B6621371
theorem B2942831 : Blo 2065435 2942831 := bstep (se 1 (by rfl) ⟨2207123, by rfl⟩ : syracuseStep 2942831 = 4414247) B4414247
theorem B7847549 : Blo 2065435 7847549 := bstep (se 3 (by rfl) ⟨1471415, by rfl⟩ : syracuseStep 7847549 = 2942831) B2942831
theorem B5231699 : Blo 2065435 5231699 := bstep (se 1 (by rfl) ⟨3923774, by rfl⟩ : syracuseStep 5231699 = 7847549) B7847549
theorem B3487799 : Blo 2065435 3487799 := bstep (se 1 (by rfl) ⟨2615849, by rfl⟩ : syracuseStep 3487799 = 5231699) B5231699
theorem B2325199 : Blo 2065435 2325199 := bstep (se 1 (by rfl) ⟨1743899, by rfl⟩ : syracuseStep 2325199 = 3487799) B3487799
theorem B3100265 : Blo 2065435 3100265 := bstep (se 2 (by rfl) ⟨1162599, by rfl⟩ : syracuseStep 3100265 = 2325199) B2325199
theorem B2066843 : Blo 2065435 2066843 := bstep (se 1 (by rfl) ⟨1550132, by rfl⟩ : syracuseStep 2066843 = 3100265) B3100265
theorem B4966037 : Blo 2065435 4966037 := bbase (se 6 (by rfl) ⟨116391, by rfl⟩ : syracuseStep 4966037 = 232783) (by norm_num)
theorem B3310691 : Blo 2065435 3310691 := bstep (se 1 (by rfl) ⟨2483018, by rfl⟩ : syracuseStep 3310691 = 4966037) B4966037
theorem B8828509 : Blo 2065435 8828509 := bstep (se 3 (by rfl) ⟨1655345, by rfl⟩ : syracuseStep 8828509 = 3310691) B3310691
theorem B11771345 : Blo 2065435 11771345 := bstep (se 2 (by rfl) ⟨4414254, by rfl⟩ : syracuseStep 11771345 = 8828509) B8828509
theorem B7847563 : Blo 2065435 7847563 := bstep (se 1 (by rfl) ⟨5885672, by rfl⟩ : syracuseStep 7847563 = 11771345) B11771345
theorem B10463417 : Blo 2065435 10463417 := bstep (se 2 (by rfl) ⟨3923781, by rfl⟩ : syracuseStep 10463417 = 7847563) B7847563
theorem B6975611 : Blo 2065435 6975611 := bstep (se 1 (by rfl) ⟨5231708, by rfl⟩ : syracuseStep 6975611 = 10463417) B10463417
theorem B4650407 : Blo 2065435 4650407 := bstep (se 1 (by rfl) ⟨3487805, by rfl⟩ : syracuseStep 4650407 = 6975611) B6975611
theorem B3100271 : Blo 2065435 3100271 := bstep (se 1 (by rfl) ⟨2325203, by rfl⟩ : syracuseStep 3100271 = 4650407) B4650407
theorem B2066847 : Blo 2065435 2066847 := bstep (se 1 (by rfl) ⟨1550135, by rfl⟩ : syracuseStep 2066847 = 3100271) B3100271
theorem B3100277 : Blo 2065435 3100277 := bbase (se 5 (by rfl) ⟨145325, by rfl⟩ : syracuseStep 3100277 = 290651) (by norm_num)
theorem B2066851 : Blo 2065435 2066851 := bstep (se 1 (by rfl) ⟨1550138, by rfl⟩ : syracuseStep 2066851 = 3100277) B3100277
theorem B3923797 : Blo 2065435 3923797 := bbase (se 9 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 3923797 = 22991) (by norm_num)
theorem B5231729 : Blo 2065435 5231729 := bstep (se 2 (by rfl) ⟨1961898, by rfl⟩ : syracuseStep 5231729 = 3923797) B3923797
theorem B3487819 : Blo 2065435 3487819 := bstep (se 1 (by rfl) ⟨2615864, by rfl⟩ : syracuseStep 3487819 = 5231729) B5231729
theorem B4650425 : Blo 2065435 4650425 := bstep (se 2 (by rfl) ⟨1743909, by rfl⟩ : syracuseStep 4650425 = 3487819) B3487819
theorem B3100283 : Blo 2065435 3100283 := bstep (se 1 (by rfl) ⟨2325212, by rfl⟩ : syracuseStep 3100283 = 4650425) B4650425
theorem B2066855 : Blo 2065435 2066855 := bstep (se 1 (by rfl) ⟨1550141, by rfl⟩ : syracuseStep 2066855 = 3100283) B3100283
theorem B2325217 : Blo 2065435 2325217 := bbase (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) (by norm_num)
theorem B3100289 : Blo 2065435 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B2066859 : Blo 2065435 2066859 := bstep (se 1 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 2066859 = 3100289) B3100289
theorem B5231749 : Blo 2065435 5231749 := bbase (se 4 (by rfl) ⟨490476, by rfl⟩ : syracuseStep 5231749 = 980953) (by norm_num)
theorem B6975665 : Blo 2065435 6975665 := bstep (se 2 (by rfl) ⟨2615874, by rfl⟩ : syracuseStep 6975665 = 5231749) B5231749
theorem B4650443 : Blo 2065435 4650443 := bstep (se 1 (by rfl) ⟨3487832, by rfl⟩ : syracuseStep 4650443 = 6975665) B6975665
theorem B3100295 : Blo 2065435 3100295 := bstep (se 1 (by rfl) ⟨2325221, by rfl⟩ : syracuseStep 3100295 = 4650443) B4650443
theorem B2066863 : Blo 2065435 2066863 := bstep (se 1 (by rfl) ⟨1550147, by rfl⟩ : syracuseStep 2066863 = 3100295) B3100295
theorem B3100301 : Blo 2065435 3100301 := bbase (se 3 (by rfl) ⟨581306, by rfl⟩ : syracuseStep 3100301 = 1162613) (by norm_num)
theorem B2066867 : Blo 2065435 2066867 := bstep (se 1 (by rfl) ⟨1550150, by rfl⟩ : syracuseStep 2066867 = 3100301) B3100301
theorem B4650461 : Blo 2065435 4650461 := bbase (se 3 (by rfl) ⟨871961, by rfl⟩ : syracuseStep 4650461 = 1743923) (by norm_num)
theorem B3100307 : Blo 2065435 3100307 := bstep (se 1 (by rfl) ⟨2325230, by rfl⟩ : syracuseStep 3100307 = 4650461) B4650461
theorem B2066871 : Blo 2065435 2066871 := bstep (se 1 (by rfl) ⟨1550153, by rfl⟩ : syracuseStep 2066871 = 3100307) B3100307
theorem B3487853 : Blo 2065435 3487853 := bbase (se 3 (by rfl) ⟨653972, by rfl⟩ : syracuseStep 3487853 = 1307945) (by norm_num)
theorem B2325235 : Blo 2065435 2325235 := bstep (se 1 (by rfl) ⟨1743926, by rfl⟩ : syracuseStep 2325235 = 3487853) B3487853
theorem B3100313 : Blo 2065435 3100313 := bstep (se 2 (by rfl) ⟨1162617, by rfl⟩ : syracuseStep 3100313 = 2325235) B2325235
theorem B2066875 : Blo 2065435 2066875 := bstep (se 1 (by rfl) ⟨1550156, by rfl⟩ : syracuseStep 2066875 = 3100313) B3100313
theorem B7954757 : Blo 2065435 7954757 := bbase (se 4 (by rfl) ⟨745758, by rfl⟩ : syracuseStep 7954757 = 1491517) (by norm_num)
theorem B5303171 : Blo 2065435 5303171 := bstep (se 1 (by rfl) ⟨3977378, by rfl⟩ : syracuseStep 5303171 = 7954757) B7954757
theorem B14141789 : Blo 2065435 14141789 := bstep (se 3 (by rfl) ⟨2651585, by rfl⟩ : syracuseStep 14141789 = 5303171) B5303171
theorem B9427859 : Blo 2065435 9427859 := bstep (se 1 (by rfl) ⟨7070894, by rfl⟩ : syracuseStep 9427859 = 14141789) B14141789
theorem B6285239 : Blo 2065435 6285239 := bstep (se 1 (by rfl) ⟨4713929, by rfl⟩ : syracuseStep 6285239 = 9427859) B9427859
theorem B4190159 : Blo 2065435 4190159 := bstep (se 1 (by rfl) ⟨3142619, by rfl⟩ : syracuseStep 4190159 = 6285239) B6285239
theorem B2793439 : Blo 2065435 2793439 := bstep (se 1 (by rfl) ⟨2095079, by rfl⟩ : syracuseStep 2793439 = 4190159) B4190159
theorem B3724585 : Blo 2065435 3724585 := bstep (se 2 (by rfl) ⟨1396719, by rfl⟩ : syracuseStep 3724585 = 2793439) B2793439
theorem B19864453 : Blo 2065435 19864453 := bstep (se 4 (by rfl) ⟨1862292, by rfl⟩ : syracuseStep 19864453 = 3724585) B3724585
theorem B26485937 : Blo 2065435 26485937 := bstep (se 2 (by rfl) ⟨9932226, by rfl⟩ : syracuseStep 26485937 = 19864453) B19864453
theorem B17657291 : Blo 2065435 17657291 := bstep (se 1 (by rfl) ⟨13242968, by rfl⟩ : syracuseStep 17657291 = 26485937) B26485937
theorem B11771527 : Blo 2065435 11771527 := bstep (se 1 (by rfl) ⟨8828645, by rfl⟩ : syracuseStep 11771527 = 17657291) B17657291
theorem B15695369 : Blo 2065435 15695369 := bstep (se 2 (by rfl) ⟨5885763, by rfl⟩ : syracuseStep 15695369 = 11771527) B11771527
theorem B10463579 : Blo 2065435 10463579 := bstep (se 1 (by rfl) ⟨7847684, by rfl⟩ : syracuseStep 10463579 = 15695369) B15695369
theorem B6975719 : Blo 2065435 6975719 := bstep (se 1 (by rfl) ⟨5231789, by rfl⟩ : syracuseStep 6975719 = 10463579) B10463579
theorem B4650479 : Blo 2065435 4650479 := bstep (se 1 (by rfl) ⟨3487859, by rfl⟩ : syracuseStep 4650479 = 6975719) B6975719
theorem B3100319 : Blo 2065435 3100319 := bstep (se 1 (by rfl) ⟨2325239, by rfl⟩ : syracuseStep 3100319 = 4650479) B4650479
theorem B2066879 : Blo 2065435 2066879 := bstep (se 1 (by rfl) ⟨1550159, by rfl⟩ : syracuseStep 2066879 = 3100319) B3100319
theorem B3100325 : Blo 2065435 3100325 := bbase (se 4 (by rfl) ⟨290655, by rfl⟩ : syracuseStep 3100325 = 581311) (by norm_num)
theorem B2066883 : Blo 2065435 2066883 := bstep (se 1 (by rfl) ⟨1550162, by rfl⟩ : syracuseStep 2066883 = 3100325) B3100325
theorem B2615905 : Blo 2065435 2615905 := bbase (se 2 (by rfl) ⟨980964, by rfl⟩ : syracuseStep 2615905 = 1961929) (by norm_num)
theorem B3487873 : Blo 2065435 3487873 := bstep (se 2 (by rfl) ⟨1307952, by rfl⟩ : syracuseStep 3487873 = 2615905) B2615905
theorem B4650497 : Blo 2065435 4650497 := bstep (se 2 (by rfl) ⟨1743936, by rfl⟩ : syracuseStep 4650497 = 3487873) B3487873
theorem B3100331 : Blo 2065435 3100331 := bstep (se 1 (by rfl) ⟨2325248, by rfl⟩ : syracuseStep 3100331 = 4650497) B4650497
theorem B2066887 : Blo 2065435 2066887 := bstep (se 1 (by rfl) ⟨1550165, by rfl⟩ : syracuseStep 2066887 = 3100331) B3100331
theorem B2325253 : Blo 2065435 2325253 := bbase (se 4 (by rfl) ⟨217992, by rfl⟩ : syracuseStep 2325253 = 435985) (by norm_num)
theorem B3100337 : Blo 2065435 3100337 := bstep (se 2 (by rfl) ⟨1162626, by rfl⟩ : syracuseStep 3100337 = 2325253) B2325253
theorem B2066891 : Blo 2065435 2066891 := bstep (se 1 (by rfl) ⟨1550168, by rfl⟩ : syracuseStep 2066891 = 3100337) B3100337
theorem B2483077 : Blo 2065435 2483077 := bbase (se 4 (by rfl) ⟨232788, by rfl⟩ : syracuseStep 2483077 = 465577) (by norm_num)
theorem B3310769 : Blo 2065435 3310769 := bstep (se 2 (by rfl) ⟨1241538, by rfl⟩ : syracuseStep 3310769 = 2483077) B2483077
theorem B2207179 : Blo 2065435 2207179 := bstep (se 1 (by rfl) ⟨1655384, by rfl⟩ : syracuseStep 2207179 = 3310769) B3310769
theorem B2942905 : Blo 2065435 2942905 := bstep (se 2 (by rfl) ⟨1103589, by rfl⟩ : syracuseStep 2942905 = 2207179) B2207179
theorem B3923873 : Blo 2065435 3923873 := bstep (se 2 (by rfl) ⟨1471452, by rfl⟩ : syracuseStep 3923873 = 2942905) B2942905
theorem B2615915 : Blo 2065435 2615915 := bstep (se 1 (by rfl) ⟨1961936, by rfl⟩ : syracuseStep 2615915 = 3923873) B3923873
theorem B6975773 : Blo 2065435 6975773 := bstep (se 3 (by rfl) ⟨1307957, by rfl⟩ : syracuseStep 6975773 = 2615915) B2615915
theorem B4650515 : Blo 2065435 4650515 := bstep (se 1 (by rfl) ⟨3487886, by rfl⟩ : syracuseStep 4650515 = 6975773) B6975773
theorem B3100343 : Blo 2065435 3100343 := bstep (se 1 (by rfl) ⟨2325257, by rfl⟩ : syracuseStep 3100343 = 4650515) B4650515
theorem B2066895 : Blo 2065435 2066895 := bstep (se 1 (by rfl) ⟨1550171, by rfl⟩ : syracuseStep 2066895 = 3100343) B3100343
theorem B3100349 : Blo 2065435 3100349 := bbase (se 3 (by rfl) ⟨581315, by rfl⟩ : syracuseStep 3100349 = 1162631) (by norm_num)
theorem B2066899 : Blo 2065435 2066899 := bstep (se 1 (by rfl) ⟨1550174, by rfl⟩ : syracuseStep 2066899 = 3100349) B3100349
theorem B4650533 : Blo 2065435 4650533 := bbase (se 4 (by rfl) ⟨435987, by rfl⟩ : syracuseStep 4650533 = 871975) (by norm_num)
theorem B3100355 : Blo 2065435 3100355 := bstep (se 1 (by rfl) ⟨2325266, by rfl⟩ : syracuseStep 3100355 = 4650533) B4650533
theorem B2066903 : Blo 2065435 2066903 := bstep (se 1 (by rfl) ⟨1550177, by rfl⟩ : syracuseStep 2066903 = 3100355) B3100355
theorem B5231861 : Blo 2065435 5231861 := bbase (se 5 (by rfl) ⟨245243, by rfl⟩ : syracuseStep 5231861 = 490487) (by norm_num)
theorem B3487907 : Blo 2065435 3487907 := bstep (se 1 (by rfl) ⟨2615930, by rfl⟩ : syracuseStep 3487907 = 5231861) B5231861
theorem B2325271 : Blo 2065435 2325271 := bstep (se 1 (by rfl) ⟨1743953, by rfl⟩ : syracuseStep 2325271 = 3487907) B3487907
theorem B3100361 : Blo 2065435 3100361 := bstep (se 2 (by rfl) ⟨1162635, by rfl⟩ : syracuseStep 3100361 = 2325271) B2325271
theorem B2066907 : Blo 2065435 2066907 := bstep (se 1 (by rfl) ⟨1550180, by rfl⟩ : syracuseStep 2066907 = 3100361) B3100361
theorem B40271573 : Blo 2065435 40271573 := bbase (se 7 (by rfl) ⟨471932, by rfl⟩ : syracuseStep 40271573 = 943865) (by norm_num)
theorem B26847715 : Blo 2065435 26847715 := bstep (se 1 (by rfl) ⟨20135786, by rfl⟩ : syracuseStep 26847715 = 40271573) B40271573
theorem B35796953 : Blo 2065435 35796953 := bstep (se 2 (by rfl) ⟨13423857, by rfl⟩ : syracuseStep 35796953 = 26847715) B26847715
theorem B23864635 : Blo 2065435 23864635 := bstep (se 1 (by rfl) ⟨17898476, by rfl⟩ : syracuseStep 23864635 = 35796953) B35796953
theorem B31819513 : Blo 2065435 31819513 := bstep (se 2 (by rfl) ⟨11932317, by rfl⟩ : syracuseStep 31819513 = 23864635) B23864635
theorem B42426017 : Blo 2065435 42426017 := bstep (se 2 (by rfl) ⟨15909756, by rfl⟩ : syracuseStep 42426017 = 31819513) B31819513
theorem B28284011 : Blo 2065435 28284011 := bstep (se 1 (by rfl) ⟨21213008, by rfl⟩ : syracuseStep 28284011 = 42426017) B42426017
theorem B18856007 : Blo 2065435 18856007 := bstep (se 1 (by rfl) ⟨14142005, by rfl⟩ : syracuseStep 18856007 = 28284011) B28284011
theorem B12570671 : Blo 2065435 12570671 := bstep (se 1 (by rfl) ⟨9428003, by rfl⟩ : syracuseStep 12570671 = 18856007) B18856007
theorem B33521789 : Blo 2065435 33521789 := bstep (se 3 (by rfl) ⟨6285335, by rfl⟩ : syracuseStep 33521789 = 12570671) B12570671
theorem B22347859 : Blo 2065435 22347859 := bstep (se 1 (by rfl) ⟨16760894, by rfl⟩ : syracuseStep 22347859 = 33521789) B33521789
theorem B29797145 : Blo 2065435 29797145 := bstep (se 2 (by rfl) ⟨11173929, by rfl⟩ : syracuseStep 29797145 = 22347859) B22347859
theorem B19864763 : Blo 2065435 19864763 := bstep (se 1 (by rfl) ⟨14898572, by rfl⟩ : syracuseStep 19864763 = 29797145) B29797145
theorem B13243175 : Blo 2065435 13243175 := bstep (se 1 (by rfl) ⟨9932381, by rfl⟩ : syracuseStep 13243175 = 19864763) B19864763
theorem B8828783 : Blo 2065435 8828783 := bstep (se 1 (by rfl) ⟨6621587, by rfl⟩ : syracuseStep 8828783 = 13243175) B13243175
theorem B5885855 : Blo 2065435 5885855 := bstep (se 1 (by rfl) ⟨4414391, by rfl⟩ : syracuseStep 5885855 = 8828783) B8828783
theorem B3923903 : Blo 2065435 3923903 := bstep (se 1 (by rfl) ⟨2942927, by rfl⟩ : syracuseStep 3923903 = 5885855) B5885855
theorem B10463741 : Blo 2065435 10463741 := bstep (se 3 (by rfl) ⟨1961951, by rfl⟩ : syracuseStep 10463741 = 3923903) B3923903
theorem B6975827 : Blo 2065435 6975827 := bstep (se 1 (by rfl) ⟨5231870, by rfl⟩ : syracuseStep 6975827 = 10463741) B10463741
theorem B4650551 : Blo 2065435 4650551 := bstep (se 1 (by rfl) ⟨3487913, by rfl⟩ : syracuseStep 4650551 = 6975827) B6975827
theorem B3100367 : Blo 2065435 3100367 := bstep (se 1 (by rfl) ⟨2325275, by rfl⟩ : syracuseStep 3100367 = 4650551) B4650551
theorem B2066911 : Blo 2065435 2066911 := bstep (se 1 (by rfl) ⟨1550183, by rfl⟩ : syracuseStep 2066911 = 3100367) B3100367
theorem B3100373 : Blo 2065435 3100373 := bbase (se 7 (by rfl) ⟨36332, by rfl⟩ : syracuseStep 3100373 = 72665) (by norm_num)
theorem B2066915 : Blo 2065435 2066915 := bstep (se 1 (by rfl) ⟨1550186, by rfl⟩ : syracuseStep 2066915 = 3100373) B3100373
theorem B7449317 : Blo 2065435 7449317 := bbase (se 4 (by rfl) ⟨698373, by rfl⟩ : syracuseStep 7449317 = 1396747) (by norm_num)
theorem B4966211 : Blo 2065435 4966211 := bstep (se 1 (by rfl) ⟨3724658, by rfl⟩ : syracuseStep 4966211 = 7449317) B7449317
theorem B3310807 : Blo 2065435 3310807 := bstep (se 1 (by rfl) ⟨2483105, by rfl⟩ : syracuseStep 3310807 = 4966211) B4966211
theorem B4414409 : Blo 2065435 4414409 := bstep (se 2 (by rfl) ⟨1655403, by rfl⟩ : syracuseStep 4414409 = 3310807) B3310807
theorem B2942939 : Blo 2065435 2942939 := bstep (se 1 (by rfl) ⟨2207204, by rfl⟩ : syracuseStep 2942939 = 4414409) B4414409
theorem B7847837 : Blo 2065435 7847837 := bstep (se 3 (by rfl) ⟨1471469, by rfl⟩ : syracuseStep 7847837 = 2942939) B2942939
theorem B5231891 : Blo 2065435 5231891 := bstep (se 1 (by rfl) ⟨3923918, by rfl⟩ : syracuseStep 5231891 = 7847837) B7847837
theorem B3487927 : Blo 2065435 3487927 := bstep (se 1 (by rfl) ⟨2615945, by rfl⟩ : syracuseStep 3487927 = 5231891) B5231891
theorem B4650569 : Blo 2065435 4650569 := bstep (se 2 (by rfl) ⟨1743963, by rfl⟩ : syracuseStep 4650569 = 3487927) B3487927
theorem B3100379 : Blo 2065435 3100379 := bstep (se 1 (by rfl) ⟨2325284, by rfl⟩ : syracuseStep 3100379 = 4650569) B4650569
theorem B2066919 : Blo 2065435 2066919 := bstep (se 1 (by rfl) ⟨1550189, by rfl⟩ : syracuseStep 2066919 = 3100379) B3100379
theorem B2325289 : Blo 2065435 2325289 := bbase (se 2 (by rfl) ⟨871983, by rfl⟩ : syracuseStep 2325289 = 1743967) (by norm_num)
theorem B3100385 : Blo 2065435 3100385 := bstep (se 2 (by rfl) ⟨1162644, by rfl⟩ : syracuseStep 3100385 = 2325289) B2325289
theorem B2066923 : Blo 2065435 2066923 := bstep (se 1 (by rfl) ⟨1550192, by rfl⟩ : syracuseStep 2066923 = 3100385) B3100385
theorem B4966229 : Blo 2065435 4966229 := bbase (se 9 (by rfl) ⟨14549, by rfl⟩ : syracuseStep 4966229 = 29099) (by norm_num)
theorem B13243277 : Blo 2065435 13243277 := bstep (se 3 (by rfl) ⟨2483114, by rfl⟩ : syracuseStep 13243277 = 4966229) B4966229
theorem B8828851 : Blo 2065435 8828851 := bstep (se 1 (by rfl) ⟨6621638, by rfl⟩ : syracuseStep 8828851 = 13243277) B13243277
theorem B11771801 : Blo 2065435 11771801 := bstep (se 2 (by rfl) ⟨4414425, by rfl⟩ : syracuseStep 11771801 = 8828851) B8828851
theorem B7847867 : Blo 2065435 7847867 := bstep (se 1 (by rfl) ⟨5885900, by rfl⟩ : syracuseStep 7847867 = 11771801) B11771801
theorem B5231911 : Blo 2065435 5231911 := bstep (se 1 (by rfl) ⟨3923933, by rfl⟩ : syracuseStep 5231911 = 7847867) B7847867
theorem B6975881 : Blo 2065435 6975881 := bstep (se 2 (by rfl) ⟨2615955, by rfl⟩ : syracuseStep 6975881 = 5231911) B5231911
theorem B4650587 : Blo 2065435 4650587 := bstep (se 1 (by rfl) ⟨3487940, by rfl⟩ : syracuseStep 4650587 = 6975881) B6975881
theorem B3100391 : Blo 2065435 3100391 := bstep (se 1 (by rfl) ⟨2325293, by rfl⟩ : syracuseStep 3100391 = 4650587) B4650587
theorem B2066927 : Blo 2065435 2066927 := bstep (se 1 (by rfl) ⟨1550195, by rfl⟩ : syracuseStep 2066927 = 3100391) B3100391
theorem B3100397 : Blo 2065435 3100397 := bbase (se 3 (by rfl) ⟨581324, by rfl⟩ : syracuseStep 3100397 = 1162649) (by norm_num)
theorem B2066931 : Blo 2065435 2066931 := bstep (se 1 (by rfl) ⟨1550198, by rfl⟩ : syracuseStep 2066931 = 3100397) B3100397
theorem B4650605 : Blo 2065435 4650605 := bbase (se 3 (by rfl) ⟨871988, by rfl⟩ : syracuseStep 4650605 = 1743977) (by norm_num)
theorem B3100403 : Blo 2065435 3100403 := bstep (se 1 (by rfl) ⟨2325302, by rfl⟩ : syracuseStep 3100403 = 4650605) B4650605
theorem B2066935 : Blo 2065435 2066935 := bstep (se 1 (by rfl) ⟨1550201, by rfl⟩ : syracuseStep 2066935 = 3100403) B3100403
theorem B3923957 : Blo 2065435 3923957 := bbase (se 5 (by rfl) ⟨183935, by rfl⟩ : syracuseStep 3923957 = 367871) (by norm_num)
theorem B2615971 : Blo 2065435 2615971 := bstep (se 1 (by rfl) ⟨1961978, by rfl⟩ : syracuseStep 2615971 = 3923957) B3923957
theorem B3487961 : Blo 2065435 3487961 := bstep (se 2 (by rfl) ⟨1307985, by rfl⟩ : syracuseStep 3487961 = 2615971) B2615971
theorem B2325307 : Blo 2065435 2325307 := bstep (se 1 (by rfl) ⟨1743980, by rfl⟩ : syracuseStep 2325307 = 3487961) B3487961
theorem B3100409 : Blo 2065435 3100409 := bstep (se 2 (by rfl) ⟨1162653, by rfl⟩ : syracuseStep 3100409 = 2325307) B2325307
theorem B2066939 : Blo 2065435 2066939 := bstep (se 1 (by rfl) ⟨1550204, by rfl⟩ : syracuseStep 2066939 = 3100409) B3100409
theorem B2687845 : Blo 2065435 2687845 := bbase (se 4 (by rfl) ⟨251985, by rfl⟩ : syracuseStep 2687845 = 503971) (by norm_num)
theorem B3583793 : Blo 2065435 3583793 := bstep (se 2 (by rfl) ⟨1343922, by rfl⟩ : syracuseStep 3583793 = 2687845) B2687845
theorem B2389195 : Blo 2065435 2389195 := bstep (se 1 (by rfl) ⟨1791896, by rfl⟩ : syracuseStep 2389195 = 3583793) B3583793
theorem B3185593 : Blo 2065435 3185593 := bstep (se 2 (by rfl) ⟨1194597, by rfl⟩ : syracuseStep 3185593 = 2389195) B2389195
theorem B67959317 : Blo 2065435 67959317 := bstep (se 6 (by rfl) ⟨1592796, by rfl⟩ : syracuseStep 67959317 = 3185593) B3185593
theorem B45306211 : Blo 2065435 45306211 := bstep (se 1 (by rfl) ⟨33979658, by rfl⟩ : syracuseStep 45306211 = 67959317) B67959317
theorem B60408281 : Blo 2065435 60408281 := bstep (se 2 (by rfl) ⟨22653105, by rfl⟩ : syracuseStep 60408281 = 45306211) B45306211
theorem B161088749 : Blo 2065435 161088749 := bstep (se 3 (by rfl) ⟨30204140, by rfl⟩ : syracuseStep 161088749 = 60408281) B60408281
theorem B107392499 : Blo 2065435 107392499 := bstep (se 1 (by rfl) ⟨80544374, by rfl⟩ : syracuseStep 107392499 = 161088749) B161088749
theorem B71594999 : Blo 2065435 71594999 := bstep (se 1 (by rfl) ⟨53696249, by rfl⟩ : syracuseStep 71594999 = 107392499) B107392499
theorem B47729999 : Blo 2065435 47729999 := bstep (se 1 (by rfl) ⟨35797499, by rfl⟩ : syracuseStep 47729999 = 71594999) B71594999
theorem B127279997 : Blo 2065435 127279997 := bstep (se 3 (by rfl) ⟨23864999, by rfl⟩ : syracuseStep 127279997 = 47729999) B47729999
theorem B84853331 : Blo 2065435 84853331 := bstep (se 1 (by rfl) ⟨63639998, by rfl⟩ : syracuseStep 84853331 = 127279997) B127279997
theorem B56568887 : Blo 2065435 56568887 := bstep (se 1 (by rfl) ⟨42426665, by rfl⟩ : syracuseStep 56568887 = 84853331) B84853331
theorem B37712591 : Blo 2065435 37712591 := bstep (se 1 (by rfl) ⟨28284443, by rfl⟩ : syracuseStep 37712591 = 56568887) B56568887
theorem B25141727 : Blo 2065435 25141727 := bstep (se 1 (by rfl) ⟨18856295, by rfl⟩ : syracuseStep 25141727 = 37712591) B37712591
theorem B16761151 : Blo 2065435 16761151 := bstep (se 1 (by rfl) ⟨12570863, by rfl⟩ : syracuseStep 16761151 = 25141727) B25141727
theorem B89392805 : Blo 2065435 89392805 := bstep (se 4 (by rfl) ⟨8380575, by rfl⟩ : syracuseStep 89392805 = 16761151) B16761151
theorem B59595203 : Blo 2065435 59595203 := bstep (se 1 (by rfl) ⟨44696402, by rfl⟩ : syracuseStep 59595203 = 89392805) B89392805
theorem B39730135 : Blo 2065435 39730135 := bstep (se 1 (by rfl) ⟨29797601, by rfl⟩ : syracuseStep 39730135 = 59595203) B59595203
theorem B52973513 : Blo 2065435 52973513 := bstep (se 2 (by rfl) ⟨19865067, by rfl⟩ : syracuseStep 52973513 = 39730135) B39730135
theorem B35315675 : Blo 2065435 35315675 := bstep (se 1 (by rfl) ⟨26486756, by rfl⟩ : syracuseStep 35315675 = 52973513) B52973513
theorem B23543783 : Blo 2065435 23543783 := bstep (se 1 (by rfl) ⟨17657837, by rfl⟩ : syracuseStep 23543783 = 35315675) B35315675
theorem B15695855 : Blo 2065435 15695855 := bstep (se 1 (by rfl) ⟨11771891, by rfl⟩ : syracuseStep 15695855 = 23543783) B23543783
theorem B10463903 : Blo 2065435 10463903 := bstep (se 1 (by rfl) ⟨7847927, by rfl⟩ : syracuseStep 10463903 = 15695855) B15695855
theorem B6975935 : Blo 2065435 6975935 := bstep (se 1 (by rfl) ⟨5231951, by rfl⟩ : syracuseStep 6975935 = 10463903) B10463903
theorem B4650623 : Blo 2065435 4650623 := bstep (se 1 (by rfl) ⟨3487967, by rfl⟩ : syracuseStep 4650623 = 6975935) B6975935
theorem B3100415 : Blo 2065435 3100415 := bstep (se 1 (by rfl) ⟨2325311, by rfl⟩ : syracuseStep 3100415 = 4650623) B4650623
theorem B2066943 : Blo 2065435 2066943 := bstep (se 1 (by rfl) ⟨1550207, by rfl⟩ : syracuseStep 2066943 = 3100415) B3100415
theorem B3100421 : Blo 2065435 3100421 := bbase (se 4 (by rfl) ⟨290664, by rfl⟩ : syracuseStep 3100421 = 581329) (by norm_num)
theorem B2066947 : Blo 2065435 2066947 := bstep (se 1 (by rfl) ⟨1550210, by rfl⟩ : syracuseStep 2066947 = 3100421) B3100421
theorem B3487981 : Blo 2065435 3487981 := bbase (se 3 (by rfl) ⟨653996, by rfl⟩ : syracuseStep 3487981 = 1307993) (by norm_num)
theorem B4650641 : Blo 2065435 4650641 := bstep (se 2 (by rfl) ⟨1743990, by rfl⟩ : syracuseStep 4650641 = 3487981) B3487981
theorem B3100427 : Blo 2065435 3100427 := bstep (se 1 (by rfl) ⟨2325320, by rfl⟩ : syracuseStep 3100427 = 4650641) B4650641
theorem B2066951 : Blo 2065435 2066951 := bstep (se 1 (by rfl) ⟨1550213, by rfl⟩ : syracuseStep 2066951 = 3100427) B3100427
theorem B2325325 : Blo 2065435 2325325 := bbase (se 3 (by rfl) ⟨435998, by rfl⟩ : syracuseStep 2325325 = 871997) (by norm_num)
theorem B3100433 : Blo 2065435 3100433 := bstep (se 2 (by rfl) ⟨1162662, by rfl⟩ : syracuseStep 3100433 = 2325325) B2325325
theorem B2066955 : Blo 2065435 2066955 := bstep (se 1 (by rfl) ⟨1550216, by rfl⟩ : syracuseStep 2066955 = 3100433) B3100433
theorem B6975989 : Blo 2065435 6975989 := bbase (se 5 (by rfl) ⟨326999, by rfl⟩ : syracuseStep 6975989 = 653999) (by norm_num)
theorem B4650659 : Blo 2065435 4650659 := bstep (se 1 (by rfl) ⟨3487994, by rfl⟩ : syracuseStep 4650659 = 6975989) B6975989
theorem B3100439 : Blo 2065435 3100439 := bstep (se 1 (by rfl) ⟨2325329, by rfl⟩ : syracuseStep 3100439 = 4650659) B4650659
theorem B2066959 : Blo 2065435 2066959 := bstep (se 1 (by rfl) ⟨1550219, by rfl⟩ : syracuseStep 2066959 = 3100439) B3100439
theorem B3100445 : Blo 2065435 3100445 := bbase (se 3 (by rfl) ⟨581333, by rfl⟩ : syracuseStep 3100445 = 1162667) (by norm_num)
theorem B2066963 : Blo 2065435 2066963 := bstep (se 1 (by rfl) ⟨1550222, by rfl⟩ : syracuseStep 2066963 = 3100445) B3100445
theorem B4650677 : Blo 2065435 4650677 := bbase (se 5 (by rfl) ⟨218000, by rfl⟩ : syracuseStep 4650677 = 436001) (by norm_num)
theorem B3100451 : Blo 2065435 3100451 := bstep (se 1 (by rfl) ⟨2325338, by rfl⟩ : syracuseStep 3100451 = 4650677) B4650677
theorem B2066967 : Blo 2065435 2066967 := bstep (se 1 (by rfl) ⟨1550225, by rfl⟩ : syracuseStep 2066967 = 3100451) B3100451
theorem B11772053 : Blo 2065435 11772053 := bbase (se 6 (by rfl) ⟨275907, by rfl⟩ : syracuseStep 11772053 = 551815) (by norm_num)
theorem B7848035 : Blo 2065435 7848035 := bstep (se 1 (by rfl) ⟨5886026, by rfl⟩ : syracuseStep 7848035 = 11772053) B11772053
theorem B5232023 : Blo 2065435 5232023 := bstep (se 1 (by rfl) ⟨3924017, by rfl⟩ : syracuseStep 5232023 = 7848035) B7848035
theorem B3488015 : Blo 2065435 3488015 := bstep (se 1 (by rfl) ⟨2616011, by rfl⟩ : syracuseStep 3488015 = 5232023) B5232023
theorem B2325343 : Blo 2065435 2325343 := bstep (se 1 (by rfl) ⟨1744007, by rfl⟩ : syracuseStep 2325343 = 3488015) B3488015
theorem B3100457 : Blo 2065435 3100457 := bstep (se 2 (by rfl) ⟨1162671, by rfl⟩ : syracuseStep 3100457 = 2325343) B2325343
theorem B2066971 : Blo 2065435 2066971 := bstep (se 1 (by rfl) ⟨1550228, by rfl⟩ : syracuseStep 2066971 = 3100457) B3100457
theorem B5886037 : Blo 2065435 5886037 := bbase (se 8 (by rfl) ⟨34488, by rfl⟩ : syracuseStep 5886037 = 68977) (by norm_num)
theorem B7848049 : Blo 2065435 7848049 := bstep (se 2 (by rfl) ⟨2943018, by rfl⟩ : syracuseStep 7848049 = 5886037) B5886037
theorem B10464065 : Blo 2065435 10464065 := bstep (se 2 (by rfl) ⟨3924024, by rfl⟩ : syracuseStep 10464065 = 7848049) B7848049
theorem B6976043 : Blo 2065435 6976043 := bstep (se 1 (by rfl) ⟨5232032, by rfl⟩ : syracuseStep 6976043 = 10464065) B10464065
theorem B4650695 : Blo 2065435 4650695 := bstep (se 1 (by rfl) ⟨3488021, by rfl⟩ : syracuseStep 4650695 = 6976043) B6976043
theorem B3100463 : Blo 2065435 3100463 := bstep (se 1 (by rfl) ⟨2325347, by rfl⟩ : syracuseStep 3100463 = 4650695) B4650695
theorem B2066975 : Blo 2065435 2066975 := bstep (se 1 (by rfl) ⟨1550231, by rfl⟩ : syracuseStep 2066975 = 3100463) B3100463
theorem B3100469 : Blo 2065435 3100469 := bbase (se 5 (by rfl) ⟨145334, by rfl⟩ : syracuseStep 3100469 = 290669) (by norm_num)
theorem B2066979 : Blo 2065435 2066979 := bstep (se 1 (by rfl) ⟨1550234, by rfl⟩ : syracuseStep 2066979 = 3100469) B3100469
theorem B5232053 : Blo 2065435 5232053 := bbase (se 5 (by rfl) ⟨245252, by rfl⟩ : syracuseStep 5232053 = 490505) (by norm_num)
theorem B3488035 : Blo 2065435 3488035 := bstep (se 1 (by rfl) ⟨2616026, by rfl⟩ : syracuseStep 3488035 = 5232053) B5232053
theorem B4650713 : Blo 2065435 4650713 := bstep (se 2 (by rfl) ⟨1744017, by rfl⟩ : syracuseStep 4650713 = 3488035) B3488035
theorem B3100475 : Blo 2065435 3100475 := bstep (se 1 (by rfl) ⟨2325356, by rfl⟩ : syracuseStep 3100475 = 4650713) B4650713
theorem B2066983 : Blo 2065435 2066983 := bstep (se 1 (by rfl) ⟨1550237, by rfl⟩ : syracuseStep 2066983 = 3100475) B3100475
theorem B2325361 : Blo 2065435 2325361 := bbase (se 2 (by rfl) ⟨872010, by rfl⟩ : syracuseStep 2325361 = 1744021) (by norm_num)
theorem B3100481 : Blo 2065435 3100481 := bstep (se 2 (by rfl) ⟨1162680, by rfl⟩ : syracuseStep 3100481 = 2325361) B2325361
theorem B2066987 : Blo 2065435 2066987 := bstep (se 1 (by rfl) ⟨1550240, by rfl⟩ : syracuseStep 2066987 = 3100481) B3100481
theorem B8829125 : Blo 2065435 8829125 := bbase (se 4 (by rfl) ⟨827730, by rfl⟩ : syracuseStep 8829125 = 1655461) (by norm_num)
theorem B5886083 : Blo 2065435 5886083 := bstep (se 1 (by rfl) ⟨4414562, by rfl⟩ : syracuseStep 5886083 = 8829125) B8829125
theorem B3924055 : Blo 2065435 3924055 := bstep (se 1 (by rfl) ⟨2943041, by rfl⟩ : syracuseStep 3924055 = 5886083) B5886083
theorem B5232073 : Blo 2065435 5232073 := bstep (se 2 (by rfl) ⟨1962027, by rfl⟩ : syracuseStep 5232073 = 3924055) B3924055
theorem B6976097 : Blo 2065435 6976097 := bstep (se 2 (by rfl) ⟨2616036, by rfl⟩ : syracuseStep 6976097 = 5232073) B5232073
theorem B4650731 : Blo 2065435 4650731 := bstep (se 1 (by rfl) ⟨3488048, by rfl⟩ : syracuseStep 4650731 = 6976097) B6976097
theorem B3100487 : Blo 2065435 3100487 := bstep (se 1 (by rfl) ⟨2325365, by rfl⟩ : syracuseStep 3100487 = 4650731) B4650731
theorem B2066991 : Blo 2065435 2066991 := bstep (se 1 (by rfl) ⟨1550243, by rfl⟩ : syracuseStep 2066991 = 3100487) B3100487
theorem B3100493 : Blo 2065435 3100493 := bbase (se 3 (by rfl) ⟨581342, by rfl⟩ : syracuseStep 3100493 = 1162685) (by norm_num)
theorem B2066995 : Blo 2065435 2066995 := bstep (se 1 (by rfl) ⟨1550246, by rfl⟩ : syracuseStep 2066995 = 3100493) B3100493
theorem B4650749 : Blo 2065435 4650749 := bbase (se 3 (by rfl) ⟨872015, by rfl⟩ : syracuseStep 4650749 = 1744031) (by norm_num)
theorem B3100499 : Blo 2065435 3100499 := bstep (se 1 (by rfl) ⟨2325374, by rfl⟩ : syracuseStep 3100499 = 4650749) B4650749
theorem B2066999 : Blo 2065435 2066999 := bstep (se 1 (by rfl) ⟨1550249, by rfl⟩ : syracuseStep 2066999 = 3100499) B3100499
theorem B3488069 : Blo 2065435 3488069 := bbase (se 4 (by rfl) ⟨327006, by rfl⟩ : syracuseStep 3488069 = 654013) (by norm_num)
theorem B2325379 : Blo 2065435 2325379 := bstep (se 1 (by rfl) ⟨1744034, by rfl⟩ : syracuseStep 2325379 = 3488069) B3488069
theorem B3100505 : Blo 2065435 3100505 := bstep (se 2 (by rfl) ⟨1162689, by rfl⟩ : syracuseStep 3100505 = 2325379) B2325379
theorem B2067003 : Blo 2065435 2067003 := bstep (se 1 (by rfl) ⟨1550252, by rfl⟩ : syracuseStep 2067003 = 3100505) B3100505
theorem B15696341 : Blo 2065435 15696341 := bbase (se 7 (by rfl) ⟨183941, by rfl⟩ : syracuseStep 15696341 = 367883) (by norm_num)
theorem B10464227 : Blo 2065435 10464227 := bstep (se 1 (by rfl) ⟨7848170, by rfl⟩ : syracuseStep 10464227 = 15696341) B15696341
theorem B6976151 : Blo 2065435 6976151 := bstep (se 1 (by rfl) ⟨5232113, by rfl⟩ : syracuseStep 6976151 = 10464227) B10464227
theorem B4650767 : Blo 2065435 4650767 := bstep (se 1 (by rfl) ⟨3488075, by rfl⟩ : syracuseStep 4650767 = 6976151) B6976151
theorem B3100511 : Blo 2065435 3100511 := bstep (se 1 (by rfl) ⟨2325383, by rfl⟩ : syracuseStep 3100511 = 4650767) B4650767
theorem B2067007 : Blo 2065435 2067007 := bstep (se 1 (by rfl) ⟨1550255, by rfl⟩ : syracuseStep 2067007 = 3100511) B3100511
theorem B3100517 : Blo 2065435 3100517 := bbase (se 4 (by rfl) ⟨290673, by rfl⟩ : syracuseStep 3100517 = 581347) (by norm_num)
theorem B2067011 : Blo 2065435 2067011 := bstep (se 1 (by rfl) ⟨1550258, by rfl⟩ : syracuseStep 2067011 = 3100517) B3100517
theorem B3924101 : Blo 2065435 3924101 := bbase (se 4 (by rfl) ⟨367884, by rfl⟩ : syracuseStep 3924101 = 735769) (by norm_num)
theorem B2616067 : Blo 2065435 2616067 := bstep (se 1 (by rfl) ⟨1962050, by rfl⟩ : syracuseStep 2616067 = 3924101) B3924101
theorem B3488089 : Blo 2065435 3488089 := bstep (se 2 (by rfl) ⟨1308033, by rfl⟩ : syracuseStep 3488089 = 2616067) B2616067
theorem B4650785 : Blo 2065435 4650785 := bstep (se 2 (by rfl) ⟨1744044, by rfl⟩ : syracuseStep 4650785 = 3488089) B3488089
theorem B3100523 : Blo 2065435 3100523 := bstep (se 1 (by rfl) ⟨2325392, by rfl⟩ : syracuseStep 3100523 = 4650785) B4650785
theorem B2067015 : Blo 2065435 2067015 := bstep (se 1 (by rfl) ⟨1550261, by rfl⟩ : syracuseStep 2067015 = 3100523) B3100523
theorem B2325397 : Blo 2065435 2325397 := bbase (se 6 (by rfl) ⟨54501, by rfl⟩ : syracuseStep 2325397 = 109003) (by norm_num)
theorem B3100529 : Blo 2065435 3100529 := bstep (se 2 (by rfl) ⟨1162698, by rfl⟩ : syracuseStep 3100529 = 2325397) B2325397
theorem B2067019 : Blo 2065435 2067019 := bstep (se 1 (by rfl) ⟨1550264, by rfl⟩ : syracuseStep 2067019 = 3100529) B3100529
theorem B2616077 : Blo 2065435 2616077 := bbase (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) (by norm_num)
theorem B6976205 : Blo 2065435 6976205 := bstep (se 3 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 6976205 = 2616077) B2616077
theorem B4650803 : Blo 2065435 4650803 := bstep (se 1 (by rfl) ⟨3488102, by rfl⟩ : syracuseStep 4650803 = 6976205) B6976205
theorem B3100535 : Blo 2065435 3100535 := bstep (se 1 (by rfl) ⟨2325401, by rfl⟩ : syracuseStep 3100535 = 4650803) B4650803
theorem B2067023 : Blo 2065435 2067023 := bstep (se 1 (by rfl) ⟨1550267, by rfl⟩ : syracuseStep 2067023 = 3100535) B3100535
theorem B3100541 : Blo 2065435 3100541 := bbase (se 3 (by rfl) ⟨581351, by rfl⟩ : syracuseStep 3100541 = 1162703) (by norm_num)
theorem B2067027 : Blo 2065435 2067027 := bstep (se 1 (by rfl) ⟨1550270, by rfl⟩ : syracuseStep 2067027 = 3100541) B3100541
theorem B4650821 : Blo 2065435 4650821 := bbase (se 4 (by rfl) ⟨436014, by rfl⟩ : syracuseStep 4650821 = 872029) (by norm_num)
theorem B3100547 : Blo 2065435 3100547 := bstep (se 1 (by rfl) ⟨2325410, by rfl⟩ : syracuseStep 3100547 = 4650821) B4650821
theorem B2067031 : Blo 2065435 2067031 := bstep (se 1 (by rfl) ⟨1550273, by rfl⟩ : syracuseStep 2067031 = 3100547) B3100547
theorem B2483245 : Blo 2065435 2483245 := bbase (se 3 (by rfl) ⟨465608, by rfl⟩ : syracuseStep 2483245 = 931217) (by norm_num)
theorem B3310993 : Blo 2065435 3310993 := bstep (se 2 (by rfl) ⟨1241622, by rfl⟩ : syracuseStep 3310993 = 2483245) B2483245
theorem B4414657 : Blo 2065435 4414657 := bstep (se 2 (by rfl) ⟨1655496, by rfl⟩ : syracuseStep 4414657 = 3310993) B3310993
theorem B5886209 : Blo 2065435 5886209 := bstep (se 2 (by rfl) ⟨2207328, by rfl⟩ : syracuseStep 5886209 = 4414657) B4414657
theorem B3924139 : Blo 2065435 3924139 := bstep (se 1 (by rfl) ⟨2943104, by rfl⟩ : syracuseStep 3924139 = 5886209) B5886209
theorem B5232185 : Blo 2065435 5232185 := bstep (se 2 (by rfl) ⟨1962069, by rfl⟩ : syracuseStep 5232185 = 3924139) B3924139
theorem B3488123 : Blo 2065435 3488123 := bstep (se 1 (by rfl) ⟨2616092, by rfl⟩ : syracuseStep 3488123 = 5232185) B5232185
theorem B2325415 : Blo 2065435 2325415 := bstep (se 1 (by rfl) ⟨1744061, by rfl⟩ : syracuseStep 2325415 = 3488123) B3488123
theorem B3100553 : Blo 2065435 3100553 := bstep (se 2 (by rfl) ⟨1162707, by rfl⟩ : syracuseStep 3100553 = 2325415) B2325415
theorem B2067035 : Blo 2065435 2067035 := bstep (se 1 (by rfl) ⟨1550276, by rfl⟩ : syracuseStep 2067035 = 3100553) B3100553
theorem B10464389 : Blo 2065435 10464389 := bbase (se 4 (by rfl) ⟨981036, by rfl⟩ : syracuseStep 10464389 = 1962073) (by norm_num)
theorem B6976259 : Blo 2065435 6976259 := bstep (se 1 (by rfl) ⟨5232194, by rfl⟩ : syracuseStep 6976259 = 10464389) B10464389
theorem B4650839 : Blo 2065435 4650839 := bstep (se 1 (by rfl) ⟨3488129, by rfl⟩ : syracuseStep 4650839 = 6976259) B6976259
theorem B3100559 : Blo 2065435 3100559 := bstep (se 1 (by rfl) ⟨2325419, by rfl⟩ : syracuseStep 3100559 = 4650839) B4650839
theorem B2067039 : Blo 2065435 2067039 := bstep (se 1 (by rfl) ⟨1550279, by rfl⟩ : syracuseStep 2067039 = 3100559) B3100559
theorem B3100565 : Blo 2065435 3100565 := bbase (se 6 (by rfl) ⟨72669, by rfl⟩ : syracuseStep 3100565 = 145339) (by norm_num)
theorem B2067043 : Blo 2065435 2067043 := bstep (se 1 (by rfl) ⟨1550282, by rfl⟩ : syracuseStep 2067043 = 3100565) B3100565
theorem B2207341 : Blo 2065435 2207341 := bbase (se 3 (by rfl) ⟨413876, by rfl⟩ : syracuseStep 2207341 = 827753) (by norm_num)
theorem B11772485 : Blo 2065435 11772485 := bstep (se 4 (by rfl) ⟨1103670, by rfl⟩ : syracuseStep 11772485 = 2207341) B2207341
theorem B7848323 : Blo 2065435 7848323 := bstep (se 1 (by rfl) ⟨5886242, by rfl⟩ : syracuseStep 7848323 = 11772485) B11772485
theorem B5232215 : Blo 2065435 5232215 := bstep (se 1 (by rfl) ⟨3924161, by rfl⟩ : syracuseStep 5232215 = 7848323) B7848323
theorem B3488143 : Blo 2065435 3488143 := bstep (se 1 (by rfl) ⟨2616107, by rfl⟩ : syracuseStep 3488143 = 5232215) B5232215
theorem B4650857 : Blo 2065435 4650857 := bstep (se 2 (by rfl) ⟨1744071, by rfl⟩ : syracuseStep 4650857 = 3488143) B3488143
theorem B3100571 : Blo 2065435 3100571 := bstep (se 1 (by rfl) ⟨2325428, by rfl⟩ : syracuseStep 3100571 = 4650857) B4650857
theorem B2067047 : Blo 2065435 2067047 := bstep (se 1 (by rfl) ⟨1550285, by rfl⟩ : syracuseStep 2067047 = 3100571) B3100571
theorem B2325433 : Blo 2065435 2325433 := bbase (se 2 (by rfl) ⟨872037, by rfl⟩ : syracuseStep 2325433 = 1744075) (by norm_num)
theorem B3100577 : Blo 2065435 3100577 := bstep (se 2 (by rfl) ⟨1162716, by rfl⟩ : syracuseStep 3100577 = 2325433) B2325433
theorem B2067051 : Blo 2065435 2067051 := bstep (se 1 (by rfl) ⟨1550288, by rfl⟩ : syracuseStep 2067051 = 3100577) B3100577
theorem B8495381 : Blo 2065435 8495381 := bbase (se 6 (by rfl) ⟨199110, by rfl⟩ : syracuseStep 8495381 = 398221) (by norm_num)
theorem B22654349 : Blo 2065435 22654349 := bstep (se 3 (by rfl) ⟨4247690, by rfl⟩ : syracuseStep 22654349 = 8495381) B8495381
theorem B15102899 : Blo 2065435 15102899 := bstep (se 1 (by rfl) ⟨11327174, by rfl⟩ : syracuseStep 15102899 = 22654349) B22654349
theorem B10068599 : Blo 2065435 10068599 := bstep (se 1 (by rfl) ⟨7551449, by rfl⟩ : syracuseStep 10068599 = 15102899) B15102899
theorem B6712399 : Blo 2065435 6712399 := bstep (se 1 (by rfl) ⟨5034299, by rfl⟩ : syracuseStep 6712399 = 10068599) B10068599
theorem B8949865 : Blo 2065435 8949865 := bstep (se 2 (by rfl) ⟨3356199, by rfl⟩ : syracuseStep 8949865 = 6712399) B6712399
theorem B11933153 : Blo 2065435 11933153 := bstep (se 2 (by rfl) ⟨4474932, by rfl⟩ : syracuseStep 11933153 = 8949865) B8949865
theorem B7955435 : Blo 2065435 7955435 := bstep (se 1 (by rfl) ⟨5966576, by rfl⟩ : syracuseStep 7955435 = 11933153) B11933153
theorem B21214493 : Blo 2065435 21214493 := bstep (se 3 (by rfl) ⟨3977717, by rfl⟩ : syracuseStep 21214493 = 7955435) B7955435
theorem B14142995 : Blo 2065435 14142995 := bstep (se 1 (by rfl) ⟨10607246, by rfl⟩ : syracuseStep 14142995 = 21214493) B21214493
theorem B9428663 : Blo 2065435 9428663 := bstep (se 1 (by rfl) ⟨7071497, by rfl⟩ : syracuseStep 9428663 = 14142995) B14142995
theorem B6285775 : Blo 2065435 6285775 := bstep (se 1 (by rfl) ⟨4714331, by rfl⟩ : syracuseStep 6285775 = 9428663) B9428663
theorem B8381033 : Blo 2065435 8381033 := bstep (se 2 (by rfl) ⟨3142887, by rfl⟩ : syracuseStep 8381033 = 6285775) B6285775
theorem B5587355 : Blo 2065435 5587355 := bstep (se 1 (by rfl) ⟨4190516, by rfl⟩ : syracuseStep 5587355 = 8381033) B8381033
theorem B3724903 : Blo 2065435 3724903 := bstep (se 1 (by rfl) ⟨2793677, by rfl⟩ : syracuseStep 3724903 = 5587355) B5587355
theorem B4966537 : Blo 2065435 4966537 := bstep (se 2 (by rfl) ⟨1862451, by rfl⟩ : syracuseStep 4966537 = 3724903) B3724903
theorem B6622049 : Blo 2065435 6622049 := bstep (se 2 (by rfl) ⟨2483268, by rfl⟩ : syracuseStep 6622049 = 4966537) B4966537
theorem B4414699 : Blo 2065435 4414699 := bstep (se 1 (by rfl) ⟨3311024, by rfl⟩ : syracuseStep 4414699 = 6622049) B6622049
theorem B5886265 : Blo 2065435 5886265 := bstep (se 2 (by rfl) ⟨2207349, by rfl⟩ : syracuseStep 5886265 = 4414699) B4414699
theorem B7848353 : Blo 2065435 7848353 := bstep (se 2 (by rfl) ⟨2943132, by rfl⟩ : syracuseStep 7848353 = 5886265) B5886265
theorem B5232235 : Blo 2065435 5232235 := bstep (se 1 (by rfl) ⟨3924176, by rfl⟩ : syracuseStep 5232235 = 7848353) B7848353
theorem B6976313 : Blo 2065435 6976313 := bstep (se 2 (by rfl) ⟨2616117, by rfl⟩ : syracuseStep 6976313 = 5232235) B5232235
theorem B4650875 : Blo 2065435 4650875 := bstep (se 1 (by rfl) ⟨3488156, by rfl⟩ : syracuseStep 4650875 = 6976313) B6976313
theorem B3100583 : Blo 2065435 3100583 := bstep (se 1 (by rfl) ⟨2325437, by rfl⟩ : syracuseStep 3100583 = 4650875) B4650875
theorem B2067055 : Blo 2065435 2067055 := bstep (se 1 (by rfl) ⟨1550291, by rfl⟩ : syracuseStep 2067055 = 3100583) B3100583
theorem B3100589 : Blo 2065435 3100589 := bbase (se 3 (by rfl) ⟨581360, by rfl⟩ : syracuseStep 3100589 = 1162721) (by norm_num)
theorem B2067059 : Blo 2065435 2067059 := bstep (se 1 (by rfl) ⟨1550294, by rfl⟩ : syracuseStep 2067059 = 3100589) B3100589
theorem B4650893 : Blo 2065435 4650893 := bbase (se 3 (by rfl) ⟨872042, by rfl⟩ : syracuseStep 4650893 = 1744085) (by norm_num)
theorem B3100595 : Blo 2065435 3100595 := bstep (se 1 (by rfl) ⟨2325446, by rfl⟩ : syracuseStep 3100595 = 4650893) B4650893
theorem B2067063 : Blo 2065435 2067063 := bstep (se 1 (by rfl) ⟨1550297, by rfl⟩ : syracuseStep 2067063 = 3100595) B3100595
theorem B2616133 : Blo 2065435 2616133 := bbase (se 4 (by rfl) ⟨245262, by rfl⟩ : syracuseStep 2616133 = 490525) (by norm_num)
theorem B3488177 : Blo 2065435 3488177 := bstep (se 2 (by rfl) ⟨1308066, by rfl⟩ : syracuseStep 3488177 = 2616133) B2616133
theorem B2325451 : Blo 2065435 2325451 := bstep (se 1 (by rfl) ⟨1744088, by rfl⟩ : syracuseStep 2325451 = 3488177) B3488177
theorem B3100601 : Blo 2065435 3100601 := bstep (se 2 (by rfl) ⟨1162725, by rfl⟩ : syracuseStep 3100601 = 2325451) B2325451
theorem B2067067 : Blo 2065435 2067067 := bstep (se 1 (by rfl) ⟨1550300, by rfl⟩ : syracuseStep 2067067 = 3100601) B3100601
theorem B5587397 : Blo 2065435 5587397 := bbase (se 4 (by rfl) ⟨523818, by rfl⟩ : syracuseStep 5587397 = 1047637) (by norm_num)
theorem B3724931 : Blo 2065435 3724931 := bstep (se 1 (by rfl) ⟨2793698, by rfl⟩ : syracuseStep 3724931 = 5587397) B5587397
theorem B9933149 : Blo 2065435 9933149 := bstep (se 3 (by rfl) ⟨1862465, by rfl⟩ : syracuseStep 9933149 = 3724931) B3724931
theorem B26488397 : Blo 2065435 26488397 := bstep (se 3 (by rfl) ⟨4966574, by rfl⟩ : syracuseStep 26488397 = 9933149) B9933149
theorem B17658931 : Blo 2065435 17658931 := bstep (se 1 (by rfl) ⟨13244198, by rfl⟩ : syracuseStep 17658931 = 26488397) B26488397
theorem B23545241 : Blo 2065435 23545241 := bstep (se 2 (by rfl) ⟨8829465, by rfl⟩ : syracuseStep 23545241 = 17658931) B17658931
theorem B15696827 : Blo 2065435 15696827 := bstep (se 1 (by rfl) ⟨11772620, by rfl⟩ : syracuseStep 15696827 = 23545241) B23545241
theorem B10464551 : Blo 2065435 10464551 := bstep (se 1 (by rfl) ⟨7848413, by rfl⟩ : syracuseStep 10464551 = 15696827) B15696827
theorem B6976367 : Blo 2065435 6976367 := bstep (se 1 (by rfl) ⟨5232275, by rfl⟩ : syracuseStep 6976367 = 10464551) B10464551
theorem B4650911 : Blo 2065435 4650911 := bstep (se 1 (by rfl) ⟨3488183, by rfl⟩ : syracuseStep 4650911 = 6976367) B6976367
theorem B3100607 : Blo 2065435 3100607 := bstep (se 1 (by rfl) ⟨2325455, by rfl⟩ : syracuseStep 3100607 = 4650911) B4650911
theorem B2067071 : Blo 2065435 2067071 := bstep (se 1 (by rfl) ⟨1550303, by rfl⟩ : syracuseStep 2067071 = 3100607) B3100607
theorem B3100613 : Blo 2065435 3100613 := bbase (se 4 (by rfl) ⟨290682, by rfl⟩ : syracuseStep 3100613 = 581365) (by norm_num)
theorem B2067075 : Blo 2065435 2067075 := bstep (se 1 (by rfl) ⟨1550306, by rfl⟩ : syracuseStep 2067075 = 3100613) B3100613
theorem B3488197 : Blo 2065435 3488197 := bbase (se 4 (by rfl) ⟨327018, by rfl⟩ : syracuseStep 3488197 = 654037) (by norm_num)
theorem B4650929 : Blo 2065435 4650929 := bstep (se 2 (by rfl) ⟨1744098, by rfl⟩ : syracuseStep 4650929 = 3488197) B3488197
theorem B3100619 : Blo 2065435 3100619 := bstep (se 1 (by rfl) ⟨2325464, by rfl⟩ : syracuseStep 3100619 = 4650929) B4650929
theorem B2067079 : Blo 2065435 2067079 := bstep (se 1 (by rfl) ⟨1550309, by rfl⟩ : syracuseStep 2067079 = 3100619) B3100619
theorem B2325469 : Blo 2065435 2325469 := bbase (se 3 (by rfl) ⟨436025, by rfl⟩ : syracuseStep 2325469 = 872051) (by norm_num)
theorem B3100625 : Blo 2065435 3100625 := bstep (se 2 (by rfl) ⟨1162734, by rfl⟩ : syracuseStep 3100625 = 2325469) B2325469
theorem B2067083 : Blo 2065435 2067083 := bstep (se 1 (by rfl) ⟨1550312, by rfl⟩ : syracuseStep 2067083 = 3100625) B3100625
theorem B6976421 : Blo 2065435 6976421 := bbase (se 4 (by rfl) ⟨654039, by rfl⟩ : syracuseStep 6976421 = 1308079) (by norm_num)
theorem B4650947 : Blo 2065435 4650947 := bstep (se 1 (by rfl) ⟨3488210, by rfl⟩ : syracuseStep 4650947 = 6976421) B6976421
theorem B3100631 : Blo 2065435 3100631 := bstep (se 1 (by rfl) ⟨2325473, by rfl⟩ : syracuseStep 3100631 = 4650947) B4650947
theorem B2067087 : Blo 2065435 2067087 := bstep (se 1 (by rfl) ⟨1550315, by rfl⟩ : syracuseStep 2067087 = 3100631) B3100631
theorem B3100637 : Blo 2065435 3100637 := bbase (se 3 (by rfl) ⟨581369, by rfl⟩ : syracuseStep 3100637 = 1162739) (by norm_num)
theorem B2067091 : Blo 2065435 2067091 := bstep (se 1 (by rfl) ⟨1550318, by rfl⟩ : syracuseStep 2067091 = 3100637) B3100637
theorem B4650965 : Blo 2065435 4650965 := bbase (se 7 (by rfl) ⟨54503, by rfl⟩ : syracuseStep 4650965 = 109007) (by norm_num)
theorem B3100643 : Blo 2065435 3100643 := bstep (se 1 (by rfl) ⟨2325482, by rfl⟩ : syracuseStep 3100643 = 4650965) B4650965
theorem B2067095 : Blo 2065435 2067095 := bstep (se 1 (by rfl) ⟨1550321, by rfl⟩ : syracuseStep 2067095 = 3100643) B3100643
theorem B2651869 : Blo 2065435 2651869 := bbase (se 3 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 2651869 = 994451) (by norm_num)
theorem B3535825 : Blo 2065435 3535825 := bstep (se 2 (by rfl) ⟨1325934, by rfl⟩ : syracuseStep 3535825 = 2651869) B2651869
theorem B4714433 : Blo 2065435 4714433 := bstep (se 2 (by rfl) ⟨1767912, by rfl⟩ : syracuseStep 4714433 = 3535825) B3535825
theorem B3142955 : Blo 2065435 3142955 := bstep (se 1 (by rfl) ⟨2357216, by rfl⟩ : syracuseStep 3142955 = 4714433) B4714433
theorem B2095303 : Blo 2065435 2095303 := bstep (se 1 (by rfl) ⟨1571477, by rfl⟩ : syracuseStep 2095303 = 3142955) B3142955
theorem B2793737 : Blo 2065435 2793737 := bstep (se 2 (by rfl) ⟨1047651, by rfl⟩ : syracuseStep 2793737 = 2095303) B2095303
theorem B7449965 : Blo 2065435 7449965 := bstep (se 3 (by rfl) ⟨1396868, by rfl⟩ : syracuseStep 7449965 = 2793737) B2793737
theorem B4966643 : Blo 2065435 4966643 := bstep (se 1 (by rfl) ⟨3724982, by rfl⟩ : syracuseStep 4966643 = 7449965) B7449965
theorem B13244381 : Blo 2065435 13244381 := bstep (se 3 (by rfl) ⟨2483321, by rfl⟩ : syracuseStep 13244381 = 4966643) B4966643
theorem B8829587 : Blo 2065435 8829587 := bstep (se 1 (by rfl) ⟨6622190, by rfl⟩ : syracuseStep 8829587 = 13244381) B13244381
theorem B5886391 : Blo 2065435 5886391 := bstep (se 1 (by rfl) ⟨4414793, by rfl⟩ : syracuseStep 5886391 = 8829587) B8829587
theorem B7848521 : Blo 2065435 7848521 := bstep (se 2 (by rfl) ⟨2943195, by rfl⟩ : syracuseStep 7848521 = 5886391) B5886391
theorem B5232347 : Blo 2065435 5232347 := bstep (se 1 (by rfl) ⟨3924260, by rfl⟩ : syracuseStep 5232347 = 7848521) B7848521
theorem B3488231 : Blo 2065435 3488231 := bstep (se 1 (by rfl) ⟨2616173, by rfl⟩ : syracuseStep 3488231 = 5232347) B5232347
theorem B2325487 : Blo 2065435 2325487 := bstep (se 1 (by rfl) ⟨1744115, by rfl⟩ : syracuseStep 2325487 = 3488231) B3488231
theorem B3100649 : Blo 2065435 3100649 := bstep (se 2 (by rfl) ⟨1162743, by rfl⟩ : syracuseStep 3100649 = 2325487) B2325487
theorem B2067099 : Blo 2065435 2067099 := bstep (se 1 (by rfl) ⟨1550324, by rfl⟩ : syracuseStep 2067099 = 3100649) B3100649
theorem B3311101 : Blo 2065435 3311101 := bbase (se 3 (by rfl) ⟨620831, by rfl⟩ : syracuseStep 3311101 = 1241663) (by norm_num)
theorem B17659205 : Blo 2065435 17659205 := bstep (se 4 (by rfl) ⟨1655550, by rfl⟩ : syracuseStep 17659205 = 3311101) B3311101
theorem B11772803 : Blo 2065435 11772803 := bstep (se 1 (by rfl) ⟨8829602, by rfl⟩ : syracuseStep 11772803 = 17659205) B17659205
theorem B7848535 : Blo 2065435 7848535 := bstep (se 1 (by rfl) ⟨5886401, by rfl⟩ : syracuseStep 7848535 = 11772803) B11772803
theorem B10464713 : Blo 2065435 10464713 := bstep (se 2 (by rfl) ⟨3924267, by rfl⟩ : syracuseStep 10464713 = 7848535) B7848535
theorem B6976475 : Blo 2065435 6976475 := bstep (se 1 (by rfl) ⟨5232356, by rfl⟩ : syracuseStep 6976475 = 10464713) B10464713
theorem B4650983 : Blo 2065435 4650983 := bstep (se 1 (by rfl) ⟨3488237, by rfl⟩ : syracuseStep 4650983 = 6976475) B6976475
theorem B3100655 : Blo 2065435 3100655 := bstep (se 1 (by rfl) ⟨2325491, by rfl⟩ : syracuseStep 3100655 = 4650983) B4650983
theorem B2067103 : Blo 2065435 2067103 := bstep (se 1 (by rfl) ⟨1550327, by rfl⟩ : syracuseStep 2067103 = 3100655) B3100655
theorem B3100661 : Blo 2065435 3100661 := bbase (se 5 (by rfl) ⟨145343, by rfl⟩ : syracuseStep 3100661 = 290687) (by norm_num)
theorem B2067107 : Blo 2065435 2067107 := bstep (se 1 (by rfl) ⟨1550330, by rfl⟩ : syracuseStep 2067107 = 3100661) B3100661
theorem B6622229 : Blo 2065435 6622229 := bbase (se 6 (by rfl) ⟨155208, by rfl⟩ : syracuseStep 6622229 = 310417) (by norm_num)
theorem B4414819 : Blo 2065435 4414819 := bstep (se 1 (by rfl) ⟨3311114, by rfl⟩ : syracuseStep 4414819 = 6622229) B6622229
theorem B5886425 : Blo 2065435 5886425 := bstep (se 2 (by rfl) ⟨2207409, by rfl⟩ : syracuseStep 5886425 = 4414819) B4414819
theorem B3924283 : Blo 2065435 3924283 := bstep (se 1 (by rfl) ⟨2943212, by rfl⟩ : syracuseStep 3924283 = 5886425) B5886425
theorem B5232377 : Blo 2065435 5232377 := bstep (se 2 (by rfl) ⟨1962141, by rfl⟩ : syracuseStep 5232377 = 3924283) B3924283
theorem B3488251 : Blo 2065435 3488251 := bstep (se 1 (by rfl) ⟨2616188, by rfl⟩ : syracuseStep 3488251 = 5232377) B5232377
theorem B4651001 : Blo 2065435 4651001 := bstep (se 2 (by rfl) ⟨1744125, by rfl⟩ : syracuseStep 4651001 = 3488251) B3488251
theorem B3100667 : Blo 2065435 3100667 := bstep (se 1 (by rfl) ⟨2325500, by rfl⟩ : syracuseStep 3100667 = 4651001) B4651001
theorem B2067111 : Blo 2065435 2067111 := bstep (se 1 (by rfl) ⟨1550333, by rfl⟩ : syracuseStep 2067111 = 3100667) B3100667
theorem B2325505 : Blo 2065435 2325505 := bbase (se 2 (by rfl) ⟨872064, by rfl⟩ : syracuseStep 2325505 = 1744129) (by norm_num)
theorem B3100673 : Blo 2065435 3100673 := bstep (se 2 (by rfl) ⟨1162752, by rfl⟩ : syracuseStep 3100673 = 2325505) B2325505
theorem B2067115 : Blo 2065435 2067115 := bstep (se 1 (by rfl) ⟨1550336, by rfl⟩ : syracuseStep 2067115 = 3100673) B3100673
theorem B5232397 : Blo 2065435 5232397 := bbase (se 3 (by rfl) ⟨981074, by rfl⟩ : syracuseStep 5232397 = 1962149) (by norm_num)
theorem B6976529 : Blo 2065435 6976529 := bstep (se 2 (by rfl) ⟨2616198, by rfl⟩ : syracuseStep 6976529 = 5232397) B5232397
theorem B4651019 : Blo 2065435 4651019 := bstep (se 1 (by rfl) ⟨3488264, by rfl⟩ : syracuseStep 4651019 = 6976529) B6976529
theorem B3100679 : Blo 2065435 3100679 := bstep (se 1 (by rfl) ⟨2325509, by rfl⟩ : syracuseStep 3100679 = 4651019) B4651019
theorem B2067119 : Blo 2065435 2067119 := bstep (se 1 (by rfl) ⟨1550339, by rfl⟩ : syracuseStep 2067119 = 3100679) B3100679
theorem B3100685 : Blo 2065435 3100685 := bbase (se 3 (by rfl) ⟨581378, by rfl⟩ : syracuseStep 3100685 = 1162757) (by norm_num)
theorem B2067123 : Blo 2065435 2067123 := bstep (se 1 (by rfl) ⟨1550342, by rfl⟩ : syracuseStep 2067123 = 3100685) B3100685
theorem B4651037 : Blo 2065435 4651037 := bbase (se 3 (by rfl) ⟨872069, by rfl⟩ : syracuseStep 4651037 = 1744139) (by norm_num)
theorem B3100691 : Blo 2065435 3100691 := bstep (se 1 (by rfl) ⟨2325518, by rfl⟩ : syracuseStep 3100691 = 4651037) B4651037
theorem B2067127 : Blo 2065435 2067127 := bstep (se 1 (by rfl) ⟨1550345, by rfl⟩ : syracuseStep 2067127 = 3100691) B3100691
theorem B3488285 : Blo 2065435 3488285 := bbase (se 3 (by rfl) ⟨654053, by rfl⟩ : syracuseStep 3488285 = 1308107) (by norm_num)
theorem B2325523 : Blo 2065435 2325523 := bstep (se 1 (by rfl) ⟨1744142, by rfl⟩ : syracuseStep 2325523 = 3488285) B3488285
theorem B3100697 : Blo 2065435 3100697 := bstep (se 2 (by rfl) ⟨1162761, by rfl⟩ : syracuseStep 3100697 = 2325523) B2325523
theorem B2067131 : Blo 2065435 2067131 := bstep (se 1 (by rfl) ⟨1550348, by rfl⟩ : syracuseStep 2067131 = 3100697) B3100697
theorem B2357257 : Blo 2065435 2357257 := bbase (se 2 (by rfl) ⟨883971, by rfl⟩ : syracuseStep 2357257 = 1767943) (by norm_num)
theorem B3143009 : Blo 2065435 3143009 := bstep (se 2 (by rfl) ⟨1178628, by rfl⟩ : syracuseStep 3143009 = 2357257) B2357257
theorem B2095339 : Blo 2065435 2095339 := bstep (se 1 (by rfl) ⟨1571504, by rfl⟩ : syracuseStep 2095339 = 3143009) B3143009
theorem B2793785 : Blo 2065435 2793785 := bstep (se 2 (by rfl) ⟨1047669, by rfl⟩ : syracuseStep 2793785 = 2095339) B2095339
theorem B7450093 : Blo 2065435 7450093 := bstep (se 3 (by rfl) ⟨1396892, by rfl⟩ : syracuseStep 7450093 = 2793785) B2793785
theorem B9933457 : Blo 2065435 9933457 := bstep (se 2 (by rfl) ⟨3725046, by rfl⟩ : syracuseStep 9933457 = 7450093) B7450093
theorem B13244609 : Blo 2065435 13244609 := bstep (se 2 (by rfl) ⟨4966728, by rfl⟩ : syracuseStep 13244609 = 9933457) B9933457
theorem B8829739 : Blo 2065435 8829739 := bstep (se 1 (by rfl) ⟨6622304, by rfl⟩ : syracuseStep 8829739 = 13244609) B13244609
theorem B11772985 : Blo 2065435 11772985 := bstep (se 2 (by rfl) ⟨4414869, by rfl⟩ : syracuseStep 11772985 = 8829739) B8829739
theorem B15697313 : Blo 2065435 15697313 := bstep (se 2 (by rfl) ⟨5886492, by rfl⟩ : syracuseStep 15697313 = 11772985) B11772985
theorem B10464875 : Blo 2065435 10464875 := bstep (se 1 (by rfl) ⟨7848656, by rfl⟩ : syracuseStep 10464875 = 15697313) B15697313
theorem B6976583 : Blo 2065435 6976583 := bstep (se 1 (by rfl) ⟨5232437, by rfl⟩ : syracuseStep 6976583 = 10464875) B10464875
theorem B4651055 : Blo 2065435 4651055 := bstep (se 1 (by rfl) ⟨3488291, by rfl⟩ : syracuseStep 4651055 = 6976583) B6976583
theorem B3100703 : Blo 2065435 3100703 := bstep (se 1 (by rfl) ⟨2325527, by rfl⟩ : syracuseStep 3100703 = 4651055) B4651055
theorem B2067135 : Blo 2065435 2067135 := bstep (se 1 (by rfl) ⟨1550351, by rfl⟩ : syracuseStep 2067135 = 3100703) B3100703
theorem B3100709 : Blo 2065435 3100709 := bbase (se 4 (by rfl) ⟨290691, by rfl⟩ : syracuseStep 3100709 = 581383) (by norm_num)
theorem B2067139 : Blo 2065435 2067139 := bstep (se 1 (by rfl) ⟨1550354, by rfl⟩ : syracuseStep 2067139 = 3100709) B3100709
theorem B2616229 : Blo 2065435 2616229 := bbase (se 4 (by rfl) ⟨245271, by rfl⟩ : syracuseStep 2616229 = 490543) (by norm_num)
theorem B3488305 : Blo 2065435 3488305 := bstep (se 2 (by rfl) ⟨1308114, by rfl⟩ : syracuseStep 3488305 = 2616229) B2616229
theorem B4651073 : Blo 2065435 4651073 := bstep (se 2 (by rfl) ⟨1744152, by rfl⟩ : syracuseStep 4651073 = 3488305) B3488305
theorem B3100715 : Blo 2065435 3100715 := bstep (se 1 (by rfl) ⟨2325536, by rfl⟩ : syracuseStep 3100715 = 4651073) B4651073
theorem B2067143 : Blo 2065435 2067143 := bstep (se 1 (by rfl) ⟨1550357, by rfl⟩ : syracuseStep 2067143 = 3100715) B3100715
theorem B2325541 : Blo 2065435 2325541 := bbase (se 4 (by rfl) ⟨218019, by rfl⟩ : syracuseStep 2325541 = 436039) (by norm_num)
theorem B3100721 : Blo 2065435 3100721 := bstep (se 2 (by rfl) ⟨1162770, by rfl⟩ : syracuseStep 3100721 = 2325541) B2325541
theorem B2067147 : Blo 2065435 2067147 := bstep (se 1 (by rfl) ⟨1550360, by rfl⟩ : syracuseStep 2067147 = 3100721) B3100721
theorem B6622357 : Blo 2065435 6622357 := bbase (se 6 (by rfl) ⟨155211, by rfl⟩ : syracuseStep 6622357 = 310423) (by norm_num)
theorem B8829809 : Blo 2065435 8829809 := bstep (se 2 (by rfl) ⟨3311178, by rfl⟩ : syracuseStep 8829809 = 6622357) B6622357
theorem B5886539 : Blo 2065435 5886539 := bstep (se 1 (by rfl) ⟨4414904, by rfl⟩ : syracuseStep 5886539 = 8829809) B8829809
theorem B3924359 : Blo 2065435 3924359 := bstep (se 1 (by rfl) ⟨2943269, by rfl⟩ : syracuseStep 3924359 = 5886539) B5886539
theorem B2616239 : Blo 2065435 2616239 := bstep (se 1 (by rfl) ⟨1962179, by rfl⟩ : syracuseStep 2616239 = 3924359) B3924359
theorem B6976637 : Blo 2065435 6976637 := bstep (se 3 (by rfl) ⟨1308119, by rfl⟩ : syracuseStep 6976637 = 2616239) B2616239
theorem B4651091 : Blo 2065435 4651091 := bstep (se 1 (by rfl) ⟨3488318, by rfl⟩ : syracuseStep 4651091 = 6976637) B6976637
theorem B3100727 : Blo 2065435 3100727 := bstep (se 1 (by rfl) ⟨2325545, by rfl⟩ : syracuseStep 3100727 = 4651091) B4651091
theorem B2067151 : Blo 2065435 2067151 := bstep (se 1 (by rfl) ⟨1550363, by rfl⟩ : syracuseStep 2067151 = 3100727) B3100727
theorem B3100733 : Blo 2065435 3100733 := bbase (se 3 (by rfl) ⟨581387, by rfl⟩ : syracuseStep 3100733 = 1162775) (by norm_num)
theorem B2067155 : Blo 2065435 2067155 := bstep (se 1 (by rfl) ⟨1550366, by rfl⟩ : syracuseStep 2067155 = 3100733) B3100733
theorem B4651109 : Blo 2065435 4651109 := bbase (se 4 (by rfl) ⟨436041, by rfl⟩ : syracuseStep 4651109 = 872083) (by norm_num)
theorem B3100739 : Blo 2065435 3100739 := bstep (se 1 (by rfl) ⟨2325554, by rfl⟩ : syracuseStep 3100739 = 4651109) B4651109
theorem B2067159 : Blo 2065435 2067159 := bstep (se 1 (by rfl) ⟨1550369, by rfl⟩ : syracuseStep 2067159 = 3100739) B3100739
theorem B5232509 : Blo 2065435 5232509 := bbase (se 3 (by rfl) ⟨981095, by rfl⟩ : syracuseStep 5232509 = 1962191) (by norm_num)
theorem B3488339 : Blo 2065435 3488339 := bstep (se 1 (by rfl) ⟨2616254, by rfl⟩ : syracuseStep 3488339 = 5232509) B5232509
theorem B2325559 : Blo 2065435 2325559 := bstep (se 1 (by rfl) ⟨1744169, by rfl⟩ : syracuseStep 2325559 = 3488339) B3488339
theorem B3100745 : Blo 2065435 3100745 := bstep (se 2 (by rfl) ⟨1162779, by rfl⟩ : syracuseStep 3100745 = 2325559) B2325559
theorem B2067163 : Blo 2065435 2067163 := bstep (se 1 (by rfl) ⟨1550372, by rfl⟩ : syracuseStep 2067163 = 3100745) B3100745
theorem B3924389 : Blo 2065435 3924389 := bbase (se 4 (by rfl) ⟨367911, by rfl⟩ : syracuseStep 3924389 = 735823) (by norm_num)
theorem B10465037 : Blo 2065435 10465037 := bstep (se 3 (by rfl) ⟨1962194, by rfl⟩ : syracuseStep 10465037 = 3924389) B3924389
theorem B6976691 : Blo 2065435 6976691 := bstep (se 1 (by rfl) ⟨5232518, by rfl⟩ : syracuseStep 6976691 = 10465037) B10465037
theorem B4651127 : Blo 2065435 4651127 := bstep (se 1 (by rfl) ⟨3488345, by rfl⟩ : syracuseStep 4651127 = 6976691) B6976691
theorem B3100751 : Blo 2065435 3100751 := bstep (se 1 (by rfl) ⟨2325563, by rfl⟩ : syracuseStep 3100751 = 4651127) B4651127
theorem B2067167 : Blo 2065435 2067167 := bstep (se 1 (by rfl) ⟨1550375, by rfl⟩ : syracuseStep 2067167 = 3100751) B3100751
theorem B3100757 : Blo 2065435 3100757 := bbase (se 8 (by rfl) ⟨18168, by rfl⟩ : syracuseStep 3100757 = 36337) (by norm_num)
theorem B2067171 : Blo 2065435 2067171 := bstep (se 1 (by rfl) ⟨1550378, by rfl⟩ : syracuseStep 2067171 = 3100757) B3100757
theorem B10607861 : Blo 2065435 10607861 := bbase (se 5 (by rfl) ⟨497243, by rfl⟩ : syracuseStep 10607861 = 994487) (by norm_num)
theorem B28287629 : Blo 2065435 28287629 := bstep (se 3 (by rfl) ⟨5303930, by rfl⟩ : syracuseStep 28287629 = 10607861) B10607861
theorem B18858419 : Blo 2065435 18858419 := bstep (se 1 (by rfl) ⟨14143814, by rfl⟩ : syracuseStep 18858419 = 28287629) B28287629
theorem B12572279 : Blo 2065435 12572279 := bstep (se 1 (by rfl) ⟨9429209, by rfl⟩ : syracuseStep 12572279 = 18858419) B18858419
theorem B8381519 : Blo 2065435 8381519 := bstep (se 1 (by rfl) ⟨6286139, by rfl⟩ : syracuseStep 8381519 = 12572279) B12572279
theorem B5587679 : Blo 2065435 5587679 := bstep (se 1 (by rfl) ⟨4190759, by rfl⟩ : syracuseStep 5587679 = 8381519) B8381519
theorem B3725119 : Blo 2065435 3725119 := bstep (se 1 (by rfl) ⟨2793839, by rfl⟩ : syracuseStep 3725119 = 5587679) B5587679
theorem B19867301 : Blo 2065435 19867301 := bstep (se 4 (by rfl) ⟨1862559, by rfl⟩ : syracuseStep 19867301 = 3725119) B3725119
theorem B13244867 : Blo 2065435 13244867 := bstep (se 1 (by rfl) ⟨9933650, by rfl⟩ : syracuseStep 13244867 = 19867301) B19867301
theorem B8829911 : Blo 2065435 8829911 := bstep (se 1 (by rfl) ⟨6622433, by rfl⟩ : syracuseStep 8829911 = 13244867) B13244867
theorem B5886607 : Blo 2065435 5886607 := bstep (se 1 (by rfl) ⟨4414955, by rfl⟩ : syracuseStep 5886607 = 8829911) B8829911
theorem B7848809 : Blo 2065435 7848809 := bstep (se 2 (by rfl) ⟨2943303, by rfl⟩ : syracuseStep 7848809 = 5886607) B5886607
theorem B5232539 : Blo 2065435 5232539 := bstep (se 1 (by rfl) ⟨3924404, by rfl⟩ : syracuseStep 5232539 = 7848809) B7848809
theorem B3488359 : Blo 2065435 3488359 := bstep (se 1 (by rfl) ⟨2616269, by rfl⟩ : syracuseStep 3488359 = 5232539) B5232539
theorem B4651145 : Blo 2065435 4651145 := bstep (se 2 (by rfl) ⟨1744179, by rfl⟩ : syracuseStep 4651145 = 3488359) B3488359
theorem B3100763 : Blo 2065435 3100763 := bstep (se 1 (by rfl) ⟨2325572, by rfl⟩ : syracuseStep 3100763 = 4651145) B4651145
theorem B2067175 : Blo 2065435 2067175 := bstep (se 1 (by rfl) ⟨1550381, by rfl⟩ : syracuseStep 2067175 = 3100763) B3100763
theorem B2325577 : Blo 2065435 2325577 := bbase (se 2 (by rfl) ⟨872091, by rfl⟩ : syracuseStep 2325577 = 1744183) (by norm_num)
theorem B3100769 : Blo 2065435 3100769 := bstep (se 2 (by rfl) ⟨1162788, by rfl⟩ : syracuseStep 3100769 = 2325577) B2325577
theorem B2067179 : Blo 2065435 2067179 := bstep (se 1 (by rfl) ⟨1550384, by rfl⟩ : syracuseStep 2067179 = 3100769) B3100769
theorem B13244917 : Blo 2065435 13244917 := bbase (se 5 (by rfl) ⟨620855, by rfl⟩ : syracuseStep 13244917 = 1241711) (by norm_num)
theorem B17659889 : Blo 2065435 17659889 := bstep (se 2 (by rfl) ⟨6622458, by rfl⟩ : syracuseStep 17659889 = 13244917) B13244917
theorem B11773259 : Blo 2065435 11773259 := bstep (se 1 (by rfl) ⟨8829944, by rfl⟩ : syracuseStep 11773259 = 17659889) B17659889
theorem B7848839 : Blo 2065435 7848839 := bstep (se 1 (by rfl) ⟨5886629, by rfl⟩ : syracuseStep 7848839 = 11773259) B11773259
theorem B5232559 : Blo 2065435 5232559 := bstep (se 1 (by rfl) ⟨3924419, by rfl⟩ : syracuseStep 5232559 = 7848839) B7848839
theorem B6976745 : Blo 2065435 6976745 := bstep (se 2 (by rfl) ⟨2616279, by rfl⟩ : syracuseStep 6976745 = 5232559) B5232559
theorem B4651163 : Blo 2065435 4651163 := bstep (se 1 (by rfl) ⟨3488372, by rfl⟩ : syracuseStep 4651163 = 6976745) B6976745
theorem B3100775 : Blo 2065435 3100775 := bstep (se 1 (by rfl) ⟨2325581, by rfl⟩ : syracuseStep 3100775 = 4651163) B4651163
theorem B2067183 : Blo 2065435 2067183 := bstep (se 1 (by rfl) ⟨1550387, by rfl⟩ : syracuseStep 2067183 = 3100775) B3100775
theorem B3100781 : Blo 2065435 3100781 := bbase (se 3 (by rfl) ⟨581396, by rfl⟩ : syracuseStep 3100781 = 1162793) (by norm_num)
theorem B2067187 : Blo 2065435 2067187 := bstep (se 1 (by rfl) ⟨1550390, by rfl⟩ : syracuseStep 2067187 = 3100781) B3100781
theorem B4651181 : Blo 2065435 4651181 := bbase (se 3 (by rfl) ⟨872096, by rfl⟩ : syracuseStep 4651181 = 1744193) (by norm_num)
theorem B3100787 : Blo 2065435 3100787 := bstep (se 1 (by rfl) ⟨2325590, by rfl⟩ : syracuseStep 3100787 = 4651181) B4651181
theorem B2067191 : Blo 2065435 2067191 := bstep (se 1 (by rfl) ⟨1550393, by rfl⟩ : syracuseStep 2067191 = 3100787) B3100787
theorem B9933749 : Blo 2065435 9933749 := bbase (se 5 (by rfl) ⟨465644, by rfl⟩ : syracuseStep 9933749 = 931289) (by norm_num)
theorem B6622499 : Blo 2065435 6622499 := bstep (se 1 (by rfl) ⟨4966874, by rfl⟩ : syracuseStep 6622499 = 9933749) B9933749
theorem B4414999 : Blo 2065435 4414999 := bstep (se 1 (by rfl) ⟨3311249, by rfl⟩ : syracuseStep 4414999 = 6622499) B6622499
theorem B5886665 : Blo 2065435 5886665 := bstep (se 2 (by rfl) ⟨2207499, by rfl⟩ : syracuseStep 5886665 = 4414999) B4414999
theorem B3924443 : Blo 2065435 3924443 := bstep (se 1 (by rfl) ⟨2943332, by rfl⟩ : syracuseStep 3924443 = 5886665) B5886665
theorem B2616295 : Blo 2065435 2616295 := bstep (se 1 (by rfl) ⟨1962221, by rfl⟩ : syracuseStep 2616295 = 3924443) B3924443
theorem B3488393 : Blo 2065435 3488393 := bstep (se 2 (by rfl) ⟨1308147, by rfl⟩ : syracuseStep 3488393 = 2616295) B2616295
theorem B2325595 : Blo 2065435 2325595 := bstep (se 1 (by rfl) ⟨1744196, by rfl⟩ : syracuseStep 2325595 = 3488393) B3488393
theorem B3100793 : Blo 2065435 3100793 := bstep (se 2 (by rfl) ⟨1162797, by rfl⟩ : syracuseStep 3100793 = 2325595) B2325595
theorem B2067195 : Blo 2065435 2067195 := bstep (se 1 (by rfl) ⟨1550396, by rfl⟩ : syracuseStep 2067195 = 3100793) B3100793
theorem B2483441 : Blo 2065435 2483441 := bbase (se 2 (by rfl) ⟨931290, by rfl⟩ : syracuseStep 2483441 = 1862581) (by norm_num)
theorem B26490037 : Blo 2065435 26490037 := bstep (se 5 (by rfl) ⟨1241720, by rfl⟩ : syracuseStep 26490037 = 2483441) B2483441
theorem B35320049 : Blo 2065435 35320049 := bstep (se 2 (by rfl) ⟨13245018, by rfl⟩ : syracuseStep 35320049 = 26490037) B26490037
theorem B23546699 : Blo 2065435 23546699 := bstep (se 1 (by rfl) ⟨17660024, by rfl⟩ : syracuseStep 23546699 = 35320049) B35320049
theorem B15697799 : Blo 2065435 15697799 := bstep (se 1 (by rfl) ⟨11773349, by rfl⟩ : syracuseStep 15697799 = 23546699) B23546699
theorem B10465199 : Blo 2065435 10465199 := bstep (se 1 (by rfl) ⟨7848899, by rfl⟩ : syracuseStep 10465199 = 15697799) B15697799
theorem B6976799 : Blo 2065435 6976799 := bstep (se 1 (by rfl) ⟨5232599, by rfl⟩ : syracuseStep 6976799 = 10465199) B10465199
theorem B4651199 : Blo 2065435 4651199 := bstep (se 1 (by rfl) ⟨3488399, by rfl⟩ : syracuseStep 4651199 = 6976799) B6976799
theorem B3100799 : Blo 2065435 3100799 := bstep (se 1 (by rfl) ⟨2325599, by rfl⟩ : syracuseStep 3100799 = 4651199) B4651199
theorem B2067199 : Blo 2065435 2067199 := bstep (se 1 (by rfl) ⟨1550399, by rfl⟩ : syracuseStep 2067199 = 3100799) B3100799
theorem B3100805 : Blo 2065435 3100805 := bbase (se 4 (by rfl) ⟨290700, by rfl⟩ : syracuseStep 3100805 = 581401) (by norm_num)
theorem B2067203 : Blo 2065435 2067203 := bstep (se 1 (by rfl) ⟨1550402, by rfl⟩ : syracuseStep 2067203 = 3100805) B3100805
theorem B3488413 : Blo 2065435 3488413 := bbase (se 3 (by rfl) ⟨654077, by rfl⟩ : syracuseStep 3488413 = 1308155) (by norm_num)
theorem B4651217 : Blo 2065435 4651217 := bstep (se 2 (by rfl) ⟨1744206, by rfl⟩ : syracuseStep 4651217 = 3488413) B3488413
theorem B3100811 : Blo 2065435 3100811 := bstep (se 1 (by rfl) ⟨2325608, by rfl⟩ : syracuseStep 3100811 = 4651217) B4651217
theorem B2067207 : Blo 2065435 2067207 := bstep (se 1 (by rfl) ⟨1550405, by rfl⟩ : syracuseStep 2067207 = 3100811) B3100811
theorem B2325613 : Blo 2065435 2325613 := bbase (se 3 (by rfl) ⟨436052, by rfl⟩ : syracuseStep 2325613 = 872105) (by norm_num)
theorem B3100817 : Blo 2065435 3100817 := bstep (se 2 (by rfl) ⟨1162806, by rfl⟩ : syracuseStep 3100817 = 2325613) B2325613
theorem B2067211 : Blo 2065435 2067211 := bstep (se 1 (by rfl) ⟨1550408, by rfl⟩ : syracuseStep 2067211 = 3100817) B3100817
theorem B6976853 : Blo 2065435 6976853 := bbase (se 13 (by rfl) ⟨1277, by rfl⟩ : syracuseStep 6976853 = 2555) (by norm_num)
theorem B4651235 : Blo 2065435 4651235 := bstep (se 1 (by rfl) ⟨3488426, by rfl⟩ : syracuseStep 4651235 = 6976853) B6976853
theorem B3100823 : Blo 2065435 3100823 := bstep (se 1 (by rfl) ⟨2325617, by rfl⟩ : syracuseStep 3100823 = 4651235) B4651235
theorem B2067215 : Blo 2065435 2067215 := bstep (se 1 (by rfl) ⟨1550411, by rfl⟩ : syracuseStep 2067215 = 3100823) B3100823
theorem B3100829 : Blo 2065435 3100829 := bbase (se 3 (by rfl) ⟨581405, by rfl⟩ : syracuseStep 3100829 = 1162811) (by norm_num)
theorem B2067219 : Blo 2065435 2067219 := bstep (se 1 (by rfl) ⟨1550414, by rfl⟩ : syracuseStep 2067219 = 3100829) B3100829
theorem B4651253 : Blo 2065435 4651253 := bbase (se 5 (by rfl) ⟨218027, by rfl⟩ : syracuseStep 4651253 = 436055) (by norm_num)
theorem B3100835 : Blo 2065435 3100835 := bstep (se 1 (by rfl) ⟨2325626, by rfl⟩ : syracuseStep 3100835 = 4651253) B4651253
theorem B2067223 : Blo 2065435 2067223 := bstep (se 1 (by rfl) ⟨1550417, by rfl⟩ : syracuseStep 2067223 = 3100835) B3100835
theorem B7072085 : Blo 2065435 7072085 := bbase (se 10 (by rfl) ⟨10359, by rfl⟩ : syracuseStep 7072085 = 20719) (by norm_num)
theorem B4714723 : Blo 2065435 4714723 := bstep (se 1 (by rfl) ⟨3536042, by rfl⟩ : syracuseStep 4714723 = 7072085) B7072085
theorem B6286297 : Blo 2065435 6286297 := bstep (se 2 (by rfl) ⟨2357361, by rfl⟩ : syracuseStep 6286297 = 4714723) B4714723
theorem B8381729 : Blo 2065435 8381729 := bstep (se 2 (by rfl) ⟨3143148, by rfl⟩ : syracuseStep 8381729 = 6286297) B6286297
theorem B22351277 : Blo 2065435 22351277 := bstep (se 3 (by rfl) ⟨4190864, by rfl⟩ : syracuseStep 22351277 = 8381729) B8381729
theorem B14900851 : Blo 2065435 14900851 := bstep (se 1 (by rfl) ⟨11175638, by rfl⟩ : syracuseStep 14900851 = 22351277) B22351277
theorem B19867801 : Blo 2065435 19867801 := bstep (se 2 (by rfl) ⟨7450425, by rfl⟩ : syracuseStep 19867801 = 14900851) B14900851
theorem B26490401 : Blo 2065435 26490401 := bstep (se 2 (by rfl) ⟨9933900, by rfl⟩ : syracuseStep 26490401 = 19867801) B19867801
theorem B17660267 : Blo 2065435 17660267 := bstep (se 1 (by rfl) ⟨13245200, by rfl⟩ : syracuseStep 17660267 = 26490401) B26490401
theorem B11773511 : Blo 2065435 11773511 := bstep (se 1 (by rfl) ⟨8830133, by rfl⟩ : syracuseStep 11773511 = 17660267) B17660267
theorem B7849007 : Blo 2065435 7849007 := bstep (se 1 (by rfl) ⟨5886755, by rfl⟩ : syracuseStep 7849007 = 11773511) B11773511
theorem B5232671 : Blo 2065435 5232671 := bstep (se 1 (by rfl) ⟨3924503, by rfl⟩ : syracuseStep 5232671 = 7849007) B7849007
theorem B3488447 : Blo 2065435 3488447 := bstep (se 1 (by rfl) ⟨2616335, by rfl⟩ : syracuseStep 3488447 = 5232671) B5232671
theorem B2325631 : Blo 2065435 2325631 := bstep (se 1 (by rfl) ⟨1744223, by rfl⟩ : syracuseStep 2325631 = 3488447) B3488447
theorem B3100841 : Blo 2065435 3100841 := bstep (se 2 (by rfl) ⟨1162815, by rfl⟩ : syracuseStep 3100841 = 2325631) B2325631
theorem B2067227 : Blo 2065435 2067227 := bstep (se 1 (by rfl) ⟨1550420, by rfl⟩ : syracuseStep 2067227 = 3100841) B3100841
theorem B6622613 : Blo 2065435 6622613 := bbase (se 6 (by rfl) ⟨155217, by rfl⟩ : syracuseStep 6622613 = 310435) (by norm_num)
theorem B4415075 : Blo 2065435 4415075 := bstep (se 1 (by rfl) ⟨3311306, by rfl⟩ : syracuseStep 4415075 = 6622613) B6622613
theorem B2943383 : Blo 2065435 2943383 := bstep (se 1 (by rfl) ⟨2207537, by rfl⟩ : syracuseStep 2943383 = 4415075) B4415075
theorem B7849021 : Blo 2065435 7849021 := bstep (se 3 (by rfl) ⟨1471691, by rfl⟩ : syracuseStep 7849021 = 2943383) B2943383
theorem B10465361 : Blo 2065435 10465361 := bstep (se 2 (by rfl) ⟨3924510, by rfl⟩ : syracuseStep 10465361 = 7849021) B7849021
theorem B6976907 : Blo 2065435 6976907 := bstep (se 1 (by rfl) ⟨5232680, by rfl⟩ : syracuseStep 6976907 = 10465361) B10465361
theorem B4651271 : Blo 2065435 4651271 := bstep (se 1 (by rfl) ⟨3488453, by rfl⟩ : syracuseStep 4651271 = 6976907) B6976907
theorem B3100847 : Blo 2065435 3100847 := bstep (se 1 (by rfl) ⟨2325635, by rfl⟩ : syracuseStep 3100847 = 4651271) B4651271
theorem B2067231 : Blo 2065435 2067231 := bstep (se 1 (by rfl) ⟨1550423, by rfl⟩ : syracuseStep 2067231 = 3100847) B3100847
theorem B3100853 : Blo 2065435 3100853 := bbase (se 5 (by rfl) ⟨145352, by rfl⟩ : syracuseStep 3100853 = 290705) (by norm_num)
theorem B2067235 : Blo 2065435 2067235 := bstep (se 1 (by rfl) ⟨1550426, by rfl⟩ : syracuseStep 2067235 = 3100853) B3100853
theorem B5232701 : Blo 2065435 5232701 := bbase (se 3 (by rfl) ⟨981131, by rfl⟩ : syracuseStep 5232701 = 1962263) (by norm_num)
theorem B3488467 : Blo 2065435 3488467 := bstep (se 1 (by rfl) ⟨2616350, by rfl⟩ : syracuseStep 3488467 = 5232701) B5232701
theorem B4651289 : Blo 2065435 4651289 := bstep (se 2 (by rfl) ⟨1744233, by rfl⟩ : syracuseStep 4651289 = 3488467) B3488467
theorem B3100859 : Blo 2065435 3100859 := bstep (se 1 (by rfl) ⟨2325644, by rfl⟩ : syracuseStep 3100859 = 4651289) B4651289
theorem B2067239 : Blo 2065435 2067239 := bstep (se 1 (by rfl) ⟨1550429, by rfl⟩ : syracuseStep 2067239 = 3100859) B3100859
theorem B2325649 : Blo 2065435 2325649 := bbase (se 2 (by rfl) ⟨872118, by rfl⟩ : syracuseStep 2325649 = 1744237) (by norm_num)
theorem B3100865 : Blo 2065435 3100865 := bstep (se 2 (by rfl) ⟨1162824, by rfl⟩ : syracuseStep 3100865 = 2325649) B2325649
theorem B2067243 : Blo 2065435 2067243 := bstep (se 1 (by rfl) ⟨1550432, by rfl⟩ : syracuseStep 2067243 = 3100865) B3100865
theorem B3924541 : Blo 2065435 3924541 := bbase (se 3 (by rfl) ⟨735851, by rfl⟩ : syracuseStep 3924541 = 1471703) (by norm_num)
theorem B5232721 : Blo 2065435 5232721 := bstep (se 2 (by rfl) ⟨1962270, by rfl⟩ : syracuseStep 5232721 = 3924541) B3924541
theorem B6976961 : Blo 2065435 6976961 := bstep (se 2 (by rfl) ⟨2616360, by rfl⟩ : syracuseStep 6976961 = 5232721) B5232721
theorem B4651307 : Blo 2065435 4651307 := bstep (se 1 (by rfl) ⟨3488480, by rfl⟩ : syracuseStep 4651307 = 6976961) B6976961
theorem B3100871 : Blo 2065435 3100871 := bstep (se 1 (by rfl) ⟨2325653, by rfl⟩ : syracuseStep 3100871 = 4651307) B4651307
theorem B2067247 : Blo 2065435 2067247 := bstep (se 1 (by rfl) ⟨1550435, by rfl⟩ : syracuseStep 2067247 = 3100871) B3100871
theorem B3100877 : Blo 2065435 3100877 := bbase (se 3 (by rfl) ⟨581414, by rfl⟩ : syracuseStep 3100877 = 1162829) (by norm_num)
theorem B2067251 : Blo 2065435 2067251 := bstep (se 1 (by rfl) ⟨1550438, by rfl⟩ : syracuseStep 2067251 = 3100877) B3100877
theorem B4651325 : Blo 2065435 4651325 := bbase (se 3 (by rfl) ⟨872123, by rfl⟩ : syracuseStep 4651325 = 1744247) (by norm_num)
theorem B3100883 : Blo 2065435 3100883 := bstep (se 1 (by rfl) ⟨2325662, by rfl⟩ : syracuseStep 3100883 = 4651325) B4651325
theorem B2067255 : Blo 2065435 2067255 := bstep (se 1 (by rfl) ⟨1550441, by rfl⟩ : syracuseStep 2067255 = 3100883) B3100883
theorem B3488501 : Blo 2065435 3488501 := bbase (se 5 (by rfl) ⟨163523, by rfl⟩ : syracuseStep 3488501 = 327047) (by norm_num)
theorem B2325667 : Blo 2065435 2325667 := bstep (se 1 (by rfl) ⟨1744250, by rfl⟩ : syracuseStep 2325667 = 3488501) B3488501
theorem B3100889 : Blo 2065435 3100889 := bstep (se 2 (by rfl) ⟨1162833, by rfl⟩ : syracuseStep 3100889 = 2325667) B2325667
theorem B2067259 : Blo 2065435 2067259 := bstep (se 1 (by rfl) ⟨1550444, by rfl⟩ : syracuseStep 2067259 = 3100889) B3100889
theorem B4714805 : Blo 2065435 4714805 := bbase (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) (by norm_num)
theorem B12572813 : Blo 2065435 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B8381875 : Blo 2065435 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B11175833 : Blo 2065435 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B7450555 : Blo 2065435 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B9934073 : Blo 2065435 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B6622715 : Blo 2065435 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B4415143 : Blo 2065435 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B5886857 : Blo 2065435 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B15698285 : Blo 2065435 15698285 := bstep (se 3 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 15698285 = 5886857) B5886857
theorem B10465523 : Blo 2065435 10465523 := bstep (se 1 (by rfl) ⟨7849142, by rfl⟩ : syracuseStep 10465523 = 15698285) B15698285
theorem B6977015 : Blo 2065435 6977015 := bstep (se 1 (by rfl) ⟨5232761, by rfl⟩ : syracuseStep 6977015 = 10465523) B10465523
theorem B4651343 : Blo 2065435 4651343 := bstep (se 1 (by rfl) ⟨3488507, by rfl⟩ : syracuseStep 4651343 = 6977015) B6977015
theorem B3100895 : Blo 2065435 3100895 := bstep (se 1 (by rfl) ⟨2325671, by rfl⟩ : syracuseStep 3100895 = 4651343) B4651343
theorem B2067263 : Blo 2065435 2067263 := bstep (se 1 (by rfl) ⟨1550447, by rfl⟩ : syracuseStep 2067263 = 3100895) B3100895
theorem B3100901 : Blo 2065435 3100901 := bbase (se 4 (by rfl) ⟨290709, by rfl⟩ : syracuseStep 3100901 = 581419) (by norm_num)
theorem B2067267 : Blo 2065435 2067267 := bstep (se 1 (by rfl) ⟨1550450, by rfl⟩ : syracuseStep 2067267 = 3100901) B3100901
theorem B3725293 : Blo 2065435 3725293 := bbase (se 3 (by rfl) ⟨698492, by rfl⟩ : syracuseStep 3725293 = 1396985) (by norm_num)
theorem B4967057 : Blo 2065435 4967057 := bstep (se 2 (by rfl) ⟨1862646, by rfl⟩ : syracuseStep 4967057 = 3725293) B3725293
theorem B3311371 : Blo 2065435 3311371 := bstep (se 1 (by rfl) ⟨2483528, by rfl⟩ : syracuseStep 3311371 = 4967057) B4967057
theorem B4415161 : Blo 2065435 4415161 := bstep (se 2 (by rfl) ⟨1655685, by rfl⟩ : syracuseStep 4415161 = 3311371) B3311371
theorem B5886881 : Blo 2065435 5886881 := bstep (se 2 (by rfl) ⟨2207580, by rfl⟩ : syracuseStep 5886881 = 4415161) B4415161
theorem B3924587 : Blo 2065435 3924587 := bstep (se 1 (by rfl) ⟨2943440, by rfl⟩ : syracuseStep 3924587 = 5886881) B5886881
theorem B2616391 : Blo 2065435 2616391 := bstep (se 1 (by rfl) ⟨1962293, by rfl⟩ : syracuseStep 2616391 = 3924587) B3924587
theorem B3488521 : Blo 2065435 3488521 := bstep (se 2 (by rfl) ⟨1308195, by rfl⟩ : syracuseStep 3488521 = 2616391) B2616391
theorem B4651361 : Blo 2065435 4651361 := bstep (se 2 (by rfl) ⟨1744260, by rfl⟩ : syracuseStep 4651361 = 3488521) B3488521
theorem B3100907 : Blo 2065435 3100907 := bstep (se 1 (by rfl) ⟨2325680, by rfl⟩ : syracuseStep 3100907 = 4651361) B4651361
theorem B2067271 : Blo 2065435 2067271 := bstep (se 1 (by rfl) ⟨1550453, by rfl⟩ : syracuseStep 2067271 = 3100907) B3100907
theorem B2325685 : Blo 2065435 2325685 := bbase (se 5 (by rfl) ⟨109016, by rfl⟩ : syracuseStep 2325685 = 218033) (by norm_num)
theorem B3100913 : Blo 2065435 3100913 := bstep (se 2 (by rfl) ⟨1162842, by rfl⟩ : syracuseStep 3100913 = 2325685) B2325685
theorem B2067275 : Blo 2065435 2067275 := bstep (se 1 (by rfl) ⟨1550456, by rfl⟩ : syracuseStep 2067275 = 3100913) B3100913
theorem B2616401 : Blo 2065435 2616401 := bbase (se 2 (by rfl) ⟨981150, by rfl⟩ : syracuseStep 2616401 = 1962301) (by norm_num)
theorem B6977069 : Blo 2065435 6977069 := bstep (se 3 (by rfl) ⟨1308200, by rfl⟩ : syracuseStep 6977069 = 2616401) B2616401
theorem B4651379 : Blo 2065435 4651379 := bstep (se 1 (by rfl) ⟨3488534, by rfl⟩ : syracuseStep 4651379 = 6977069) B6977069
theorem B3100919 : Blo 2065435 3100919 := bstep (se 1 (by rfl) ⟨2325689, by rfl⟩ : syracuseStep 3100919 = 4651379) B4651379
theorem B2067279 : Blo 2065435 2067279 := bstep (se 1 (by rfl) ⟨1550459, by rfl⟩ : syracuseStep 2067279 = 3100919) B3100919
theorem B3100925 : Blo 2065435 3100925 := bbase (se 3 (by rfl) ⟨581423, by rfl⟩ : syracuseStep 3100925 = 1162847) (by norm_num)
theorem B2067283 : Blo 2065435 2067283 := bstep (se 1 (by rfl) ⟨1550462, by rfl⟩ : syracuseStep 2067283 = 3100925) B3100925
theorem B4651397 : Blo 2065435 4651397 := bbase (se 4 (by rfl) ⟨436068, by rfl⟩ : syracuseStep 4651397 = 872137) (by norm_num)
theorem B3100931 : Blo 2065435 3100931 := bstep (se 1 (by rfl) ⟨2325698, by rfl⟩ : syracuseStep 3100931 = 4651397) B4651397
theorem B2067287 : Blo 2065435 2067287 := bstep (se 1 (by rfl) ⟨1550465, by rfl⟩ : syracuseStep 2067287 = 3100931) B3100931
theorem B2943469 : Blo 2065435 2943469 := bbase (se 3 (by rfl) ⟨551900, by rfl⟩ : syracuseStep 2943469 = 1103801) (by norm_num)
theorem B3924625 : Blo 2065435 3924625 := bstep (se 2 (by rfl) ⟨1471734, by rfl⟩ : syracuseStep 3924625 = 2943469) B2943469
theorem B5232833 : Blo 2065435 5232833 := bstep (se 2 (by rfl) ⟨1962312, by rfl⟩ : syracuseStep 5232833 = 3924625) B3924625
theorem B3488555 : Blo 2065435 3488555 := bstep (se 1 (by rfl) ⟨2616416, by rfl⟩ : syracuseStep 3488555 = 5232833) B5232833
theorem B2325703 : Blo 2065435 2325703 := bstep (se 1 (by rfl) ⟨1744277, by rfl⟩ : syracuseStep 2325703 = 3488555) B3488555
theorem B3100937 : Blo 2065435 3100937 := bstep (se 2 (by rfl) ⟨1162851, by rfl⟩ : syracuseStep 3100937 = 2325703) B2325703
theorem B2067291 : Blo 2065435 2067291 := bstep (se 1 (by rfl) ⟨1550468, by rfl⟩ : syracuseStep 2067291 = 3100937) B3100937
theorem B10465685 : Blo 2065435 10465685 := bbase (se 6 (by rfl) ⟨245289, by rfl⟩ : syracuseStep 10465685 = 490579) (by norm_num)
theorem B6977123 : Blo 2065435 6977123 := bstep (se 1 (by rfl) ⟨5232842, by rfl⟩ : syracuseStep 6977123 = 10465685) B10465685
theorem B4651415 : Blo 2065435 4651415 := bstep (se 1 (by rfl) ⟨3488561, by rfl⟩ : syracuseStep 4651415 = 6977123) B6977123
theorem B3100943 : Blo 2065435 3100943 := bstep (se 1 (by rfl) ⟨2325707, by rfl⟩ : syracuseStep 3100943 = 4651415) B4651415
theorem B2067295 : Blo 2065435 2067295 := bstep (se 1 (by rfl) ⟨1550471, by rfl⟩ : syracuseStep 2067295 = 3100943) B3100943
theorem B3100949 : Blo 2065435 3100949 := bbase (se 6 (by rfl) ⟨72678, by rfl⟩ : syracuseStep 3100949 = 145357) (by norm_num)
theorem B2067299 : Blo 2065435 2067299 := bstep (se 1 (by rfl) ⟨1550474, by rfl⟩ : syracuseStep 2067299 = 3100949) B3100949
theorem B8382037 : Blo 2065435 8382037 := bbase (se 8 (by rfl) ⟨49113, by rfl⟩ : syracuseStep 8382037 = 98227) (by norm_num)
theorem B11176049 : Blo 2065435 11176049 := bstep (se 2 (by rfl) ⟨4191018, by rfl⟩ : syracuseStep 11176049 = 8382037) B8382037
theorem B7450699 : Blo 2065435 7450699 := bstep (se 1 (by rfl) ⟨5588024, by rfl⟩ : syracuseStep 7450699 = 11176049) B11176049
theorem B9934265 : Blo 2065435 9934265 := bstep (se 2 (by rfl) ⟨3725349, by rfl⟩ : syracuseStep 9934265 = 7450699) B7450699
theorem B26491373 : Blo 2065435 26491373 := bstep (se 3 (by rfl) ⟨4967132, by rfl⟩ : syracuseStep 26491373 = 9934265) B9934265
theorem B17660915 : Blo 2065435 17660915 := bstep (se 1 (by rfl) ⟨13245686, by rfl⟩ : syracuseStep 17660915 = 26491373) B26491373
theorem B11773943 : Blo 2065435 11773943 := bstep (se 1 (by rfl) ⟨8830457, by rfl⟩ : syracuseStep 11773943 = 17660915) B17660915
theorem B7849295 : Blo 2065435 7849295 := bstep (se 1 (by rfl) ⟨5886971, by rfl⟩ : syracuseStep 7849295 = 11773943) B11773943
theorem B5232863 : Blo 2065435 5232863 := bstep (se 1 (by rfl) ⟨3924647, by rfl⟩ : syracuseStep 5232863 = 7849295) B7849295
theorem B3488575 : Blo 2065435 3488575 := bstep (se 1 (by rfl) ⟨2616431, by rfl⟩ : syracuseStep 3488575 = 5232863) B5232863
theorem B4651433 : Blo 2065435 4651433 := bstep (se 2 (by rfl) ⟨1744287, by rfl⟩ : syracuseStep 4651433 = 3488575) B3488575
theorem B3100955 : Blo 2065435 3100955 := bstep (se 1 (by rfl) ⟨2325716, by rfl⟩ : syracuseStep 3100955 = 4651433) B4651433
theorem B2067303 : Blo 2065435 2067303 := bstep (se 1 (by rfl) ⟨1550477, by rfl⟩ : syracuseStep 2067303 = 3100955) B3100955
theorem B2325721 : Blo 2065435 2325721 := bbase (se 2 (by rfl) ⟨872145, by rfl⟩ : syracuseStep 2325721 = 1744291) (by norm_num)
theorem B3100961 : Blo 2065435 3100961 := bstep (se 2 (by rfl) ⟨1162860, by rfl⟩ : syracuseStep 3100961 = 2325721) B2325721
theorem B2067307 : Blo 2065435 2067307 := bstep (se 1 (by rfl) ⟨1550480, by rfl⟩ : syracuseStep 2067307 = 3100961) B3100961
theorem B3725365 : Blo 2065435 3725365 := bbase (se 5 (by rfl) ⟨174626, by rfl⟩ : syracuseStep 3725365 = 349253) (by norm_num)
theorem B4967153 : Blo 2065435 4967153 := bstep (se 2 (by rfl) ⟨1862682, by rfl⟩ : syracuseStep 4967153 = 3725365) B3725365
theorem B3311435 : Blo 2065435 3311435 := bstep (se 1 (by rfl) ⟨2483576, by rfl⟩ : syracuseStep 3311435 = 4967153) B4967153
theorem B2207623 : Blo 2065435 2207623 := bstep (se 1 (by rfl) ⟨1655717, by rfl⟩ : syracuseStep 2207623 = 3311435) B3311435
theorem B2943497 : Blo 2065435 2943497 := bstep (se 2 (by rfl) ⟨1103811, by rfl⟩ : syracuseStep 2943497 = 2207623) B2207623
theorem B7849325 : Blo 2065435 7849325 := bstep (se 3 (by rfl) ⟨1471748, by rfl⟩ : syracuseStep 7849325 = 2943497) B2943497
theorem B5232883 : Blo 2065435 5232883 := bstep (se 1 (by rfl) ⟨3924662, by rfl⟩ : syracuseStep 5232883 = 7849325) B7849325
theorem B6977177 : Blo 2065435 6977177 := bstep (se 2 (by rfl) ⟨2616441, by rfl⟩ : syracuseStep 6977177 = 5232883) B5232883
theorem B4651451 : Blo 2065435 4651451 := bstep (se 1 (by rfl) ⟨3488588, by rfl⟩ : syracuseStep 4651451 = 6977177) B6977177
theorem B3100967 : Blo 2065435 3100967 := bstep (se 1 (by rfl) ⟨2325725, by rfl⟩ : syracuseStep 3100967 = 4651451) B4651451
theorem B2067311 : Blo 2065435 2067311 := bstep (se 1 (by rfl) ⟨1550483, by rfl⟩ : syracuseStep 2067311 = 3100967) B3100967
theorem B3100973 : Blo 2065435 3100973 := bbase (se 3 (by rfl) ⟨581432, by rfl⟩ : syracuseStep 3100973 = 1162865) (by norm_num)
theorem B2067315 : Blo 2065435 2067315 := bstep (se 1 (by rfl) ⟨1550486, by rfl⟩ : syracuseStep 2067315 = 3100973) B3100973
theorem B4651469 : Blo 2065435 4651469 := bbase (se 3 (by rfl) ⟨872150, by rfl⟩ : syracuseStep 4651469 = 1744301) (by norm_num)
theorem B3100979 : Blo 2065435 3100979 := bstep (se 1 (by rfl) ⟨2325734, by rfl⟩ : syracuseStep 3100979 = 4651469) B4651469
theorem B2067319 : Blo 2065435 2067319 := bstep (se 1 (by rfl) ⟨1550489, by rfl⟩ : syracuseStep 2067319 = 3100979) B3100979
theorem B2616457 : Blo 2065435 2616457 := bbase (se 2 (by rfl) ⟨981171, by rfl⟩ : syracuseStep 2616457 = 1962343) (by norm_num)
theorem B3488609 : Blo 2065435 3488609 := bstep (se 2 (by rfl) ⟨1308228, by rfl⟩ : syracuseStep 3488609 = 2616457) B2616457
theorem B2325739 : Blo 2065435 2325739 := bstep (se 1 (by rfl) ⟨1744304, by rfl⟩ : syracuseStep 2325739 = 3488609) B3488609
theorem B3100985 : Blo 2065435 3100985 := bstep (se 2 (by rfl) ⟨1162869, by rfl⟩ : syracuseStep 3100985 = 2325739) B2325739
theorem B2067323 : Blo 2065435 2067323 := bstep (se 1 (by rfl) ⟨1550492, by rfl⟩ : syracuseStep 2067323 = 3100985) B3100985
theorem B8382133 : Blo 2065435 8382133 := bbase (se 5 (by rfl) ⟨392912, by rfl⟩ : syracuseStep 8382133 = 785825) (by norm_num)
theorem B44704709 : Blo 2065435 44704709 := bstep (se 4 (by rfl) ⟨4191066, by rfl⟩ : syracuseStep 44704709 = 8382133) B8382133
theorem B29803139 : Blo 2065435 29803139 := bstep (se 1 (by rfl) ⟨22352354, by rfl⟩ : syracuseStep 29803139 = 44704709) B44704709
theorem B19868759 : Blo 2065435 19868759 := bstep (se 1 (by rfl) ⟨14901569, by rfl⟩ : syracuseStep 19868759 = 29803139) B29803139
theorem B13245839 : Blo 2065435 13245839 := bstep (se 1 (by rfl) ⟨9934379, by rfl⟩ : syracuseStep 13245839 = 19868759) B19868759
theorem B8830559 : Blo 2065435 8830559 := bstep (se 1 (by rfl) ⟨6622919, by rfl⟩ : syracuseStep 8830559 = 13245839) B13245839
theorem B23548157 : Blo 2065435 23548157 := bstep (se 3 (by rfl) ⟨4415279, by rfl⟩ : syracuseStep 23548157 = 8830559) B8830559
theorem B15698771 : Blo 2065435 15698771 := bstep (se 1 (by rfl) ⟨11774078, by rfl⟩ : syracuseStep 15698771 = 23548157) B23548157
theorem B10465847 : Blo 2065435 10465847 := bstep (se 1 (by rfl) ⟨7849385, by rfl⟩ : syracuseStep 10465847 = 15698771) B15698771
theorem B6977231 : Blo 2065435 6977231 := bstep (se 1 (by rfl) ⟨5232923, by rfl⟩ : syracuseStep 6977231 = 10465847) B10465847
theorem B4651487 : Blo 2065435 4651487 := bstep (se 1 (by rfl) ⟨3488615, by rfl⟩ : syracuseStep 4651487 = 6977231) B6977231
theorem B3100991 : Blo 2065435 3100991 := bstep (se 1 (by rfl) ⟨2325743, by rfl⟩ : syracuseStep 3100991 = 4651487) B4651487
theorem B2067327 : Blo 2065435 2067327 := bstep (se 1 (by rfl) ⟨1550495, by rfl⟩ : syracuseStep 2067327 = 3100991) B3100991
theorem B3100997 : Blo 2065435 3100997 := bbase (se 4 (by rfl) ⟨290718, by rfl⟩ : syracuseStep 3100997 = 581437) (by norm_num)
theorem B2067331 : Blo 2065435 2067331 := bstep (se 1 (by rfl) ⟨1550498, by rfl⟩ : syracuseStep 2067331 = 3100997) B3100997
theorem B3488629 : Blo 2065435 3488629 := bbase (se 5 (by rfl) ⟨163529, by rfl⟩ : syracuseStep 3488629 = 327059) (by norm_num)
theorem B4651505 : Blo 2065435 4651505 := bstep (se 2 (by rfl) ⟨1744314, by rfl⟩ : syracuseStep 4651505 = 3488629) B3488629
theorem B3101003 : Blo 2065435 3101003 := bstep (se 1 (by rfl) ⟨2325752, by rfl⟩ : syracuseStep 3101003 = 4651505) B4651505
theorem B2067335 : Blo 2065435 2067335 := bstep (se 1 (by rfl) ⟨1550501, by rfl⟩ : syracuseStep 2067335 = 3101003) B3101003
theorem B2325757 : Blo 2065435 2325757 := bbase (se 3 (by rfl) ⟨436079, by rfl⟩ : syracuseStep 2325757 = 872159) (by norm_num)
theorem B3101009 : Blo 2065435 3101009 := bstep (se 2 (by rfl) ⟨1162878, by rfl⟩ : syracuseStep 3101009 = 2325757) B2325757
theorem B2067339 : Blo 2065435 2067339 := bstep (se 1 (by rfl) ⟨1550504, by rfl⟩ : syracuseStep 2067339 = 3101009) B3101009
theorem B6977285 : Blo 2065435 6977285 := bbase (se 4 (by rfl) ⟨654120, by rfl⟩ : syracuseStep 6977285 = 1308241) (by norm_num)
theorem B4651523 : Blo 2065435 4651523 := bstep (se 1 (by rfl) ⟨3488642, by rfl⟩ : syracuseStep 4651523 = 6977285) B6977285
theorem B3101015 : Blo 2065435 3101015 := bstep (se 1 (by rfl) ⟨2325761, by rfl⟩ : syracuseStep 3101015 = 4651523) B4651523
theorem B2067343 : Blo 2065435 2067343 := bstep (se 1 (by rfl) ⟨1550507, by rfl⟩ : syracuseStep 2067343 = 3101015) B3101015
theorem B3101021 : Blo 2065435 3101021 := bbase (se 3 (by rfl) ⟨581441, by rfl⟩ : syracuseStep 3101021 = 1162883) (by norm_num)
theorem B2067347 : Blo 2065435 2067347 := bstep (se 1 (by rfl) ⟨1550510, by rfl⟩ : syracuseStep 2067347 = 3101021) B3101021
theorem B4651541 : Blo 2065435 4651541 := bbase (se 6 (by rfl) ⟨109020, by rfl⟩ : syracuseStep 4651541 = 218041) (by norm_num)
theorem B3101027 : Blo 2065435 3101027 := bstep (se 1 (by rfl) ⟨2325770, by rfl⟩ : syracuseStep 3101027 = 4651541) B4651541
theorem B2067351 : Blo 2065435 2067351 := bstep (se 1 (by rfl) ⟨1550513, by rfl⟩ : syracuseStep 2067351 = 3101027) B3101027
theorem B7849493 : Blo 2065435 7849493 := bbase (se 6 (by rfl) ⟨183972, by rfl⟩ : syracuseStep 7849493 = 367945) (by norm_num)
theorem B5232995 : Blo 2065435 5232995 := bstep (se 1 (by rfl) ⟨3924746, by rfl⟩ : syracuseStep 5232995 = 7849493) B7849493
theorem B3488663 : Blo 2065435 3488663 := bstep (se 1 (by rfl) ⟨2616497, by rfl⟩ : syracuseStep 3488663 = 5232995) B5232995
theorem B2325775 : Blo 2065435 2325775 := bstep (se 1 (by rfl) ⟨1744331, by rfl⟩ : syracuseStep 2325775 = 3488663) B3488663
theorem B3101033 : Blo 2065435 3101033 := bstep (se 2 (by rfl) ⟨1162887, by rfl⟩ : syracuseStep 3101033 = 2325775) B2325775
theorem B2067355 : Blo 2065435 2067355 := bstep (se 1 (by rfl) ⟨1550516, by rfl⟩ : syracuseStep 2067355 = 3101033) B3101033
theorem B11774261 : Blo 2065435 11774261 := bbase (se 5 (by rfl) ⟨551918, by rfl⟩ : syracuseStep 11774261 = 1103837) (by norm_num)
theorem B7849507 : Blo 2065435 7849507 := bstep (se 1 (by rfl) ⟨5887130, by rfl⟩ : syracuseStep 7849507 = 11774261) B11774261
theorem B10466009 : Blo 2065435 10466009 := bstep (se 2 (by rfl) ⟨3924753, by rfl⟩ : syracuseStep 10466009 = 7849507) B7849507
theorem B6977339 : Blo 2065435 6977339 := bstep (se 1 (by rfl) ⟨5233004, by rfl⟩ : syracuseStep 6977339 = 10466009) B10466009
theorem B4651559 : Blo 2065435 4651559 := bstep (se 1 (by rfl) ⟨3488669, by rfl⟩ : syracuseStep 4651559 = 6977339) B6977339
theorem B3101039 : Blo 2065435 3101039 := bstep (se 1 (by rfl) ⟨2325779, by rfl⟩ : syracuseStep 3101039 = 4651559) B4651559
theorem B2067359 : Blo 2065435 2067359 := bstep (se 1 (by rfl) ⟨1550519, by rfl⟩ : syracuseStep 2067359 = 3101039) B3101039
theorem B3101045 : Blo 2065435 3101045 := bbase (se 5 (by rfl) ⟨145361, by rfl⟩ : syracuseStep 3101045 = 290723) (by norm_num)
theorem B2067363 : Blo 2065435 2067363 := bstep (se 1 (by rfl) ⟨1550522, by rfl⟩ : syracuseStep 2067363 = 3101045) B3101045
theorem B3311525 : Blo 2065435 3311525 := bbase (se 4 (by rfl) ⟨310455, by rfl⟩ : syracuseStep 3311525 = 620911) (by norm_num)
theorem B2207683 : Blo 2065435 2207683 := bstep (se 1 (by rfl) ⟨1655762, by rfl⟩ : syracuseStep 2207683 = 3311525) B3311525
theorem B2943577 : Blo 2065435 2943577 := bstep (se 2 (by rfl) ⟨1103841, by rfl⟩ : syracuseStep 2943577 = 2207683) B2207683
theorem B3924769 : Blo 2065435 3924769 := bstep (se 2 (by rfl) ⟨1471788, by rfl⟩ : syracuseStep 3924769 = 2943577) B2943577
theorem B5233025 : Blo 2065435 5233025 := bstep (se 2 (by rfl) ⟨1962384, by rfl⟩ : syracuseStep 5233025 = 3924769) B3924769
theorem B3488683 : Blo 2065435 3488683 := bstep (se 1 (by rfl) ⟨2616512, by rfl⟩ : syracuseStep 3488683 = 5233025) B5233025
theorem B4651577 : Blo 2065435 4651577 := bstep (se 2 (by rfl) ⟨1744341, by rfl⟩ : syracuseStep 4651577 = 3488683) B3488683
theorem B3101051 : Blo 2065435 3101051 := bstep (se 1 (by rfl) ⟨2325788, by rfl⟩ : syracuseStep 3101051 = 4651577) B4651577
theorem B2067367 : Blo 2065435 2067367 := bstep (se 1 (by rfl) ⟨1550525, by rfl⟩ : syracuseStep 2067367 = 3101051) B3101051
theorem B2325793 : Blo 2065435 2325793 := bbase (se 2 (by rfl) ⟨872172, by rfl⟩ : syracuseStep 2325793 = 1744345) (by norm_num)
theorem B3101057 : Blo 2065435 3101057 := bstep (se 2 (by rfl) ⟨1162896, by rfl⟩ : syracuseStep 3101057 = 2325793) B2325793
theorem B2067371 : Blo 2065435 2067371 := bstep (se 1 (by rfl) ⟨1550528, by rfl⟩ : syracuseStep 2067371 = 3101057) B3101057
theorem B5233045 : Blo 2065435 5233045 := bbase (se 6 (by rfl) ⟨122649, by rfl⟩ : syracuseStep 5233045 = 245299) (by norm_num)
theorem B6977393 : Blo 2065435 6977393 := bstep (se 2 (by rfl) ⟨2616522, by rfl⟩ : syracuseStep 6977393 = 5233045) B5233045
theorem B4651595 : Blo 2065435 4651595 := bstep (se 1 (by rfl) ⟨3488696, by rfl⟩ : syracuseStep 4651595 = 6977393) B6977393
theorem B3101063 : Blo 2065435 3101063 := bstep (se 1 (by rfl) ⟨2325797, by rfl⟩ : syracuseStep 3101063 = 4651595) B4651595
theorem B2067375 : Blo 2065435 2067375 := bstep (se 1 (by rfl) ⟨1550531, by rfl⟩ : syracuseStep 2067375 = 3101063) B3101063
theorem B3101069 : Blo 2065435 3101069 := bbase (se 3 (by rfl) ⟨581450, by rfl⟩ : syracuseStep 3101069 = 1162901) (by norm_num)
theorem B2067379 : Blo 2065435 2067379 := bstep (se 1 (by rfl) ⟨1550534, by rfl⟩ : syracuseStep 2067379 = 3101069) B3101069
theorem B4651613 : Blo 2065435 4651613 := bbase (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) (by norm_num)
theorem B3101075 : Blo 2065435 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B2067383 : Blo 2065435 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B3488717 : Blo 2065435 3488717 := bbase (se 3 (by rfl) ⟨654134, by rfl⟩ : syracuseStep 3488717 = 1308269) (by norm_num)
theorem B2325811 : Blo 2065435 2325811 := bstep (se 1 (by rfl) ⟨1744358, by rfl⟩ : syracuseStep 2325811 = 3488717) B3488717
theorem B3101081 : Blo 2065435 3101081 := bstep (se 2 (by rfl) ⟨1162905, by rfl⟩ : syracuseStep 3101081 = 2325811) B2325811
theorem B2067387 : Blo 2065435 2067387 := bstep (se 1 (by rfl) ⟨1550540, by rfl⟩ : syracuseStep 2067387 = 3101081) B3101081
theorem B50294357 : Blo 2065435 50294357 := bbase (se 8 (by rfl) ⟨294693, by rfl⟩ : syracuseStep 50294357 = 589387) (by norm_num)
theorem B33529571 : Blo 2065435 33529571 := bstep (se 1 (by rfl) ⟨25147178, by rfl⟩ : syracuseStep 33529571 = 50294357) B50294357
theorem B22353047 : Blo 2065435 22353047 := bstep (se 1 (by rfl) ⟨16764785, by rfl⟩ : syracuseStep 22353047 = 33529571) B33529571
theorem B14902031 : Blo 2065435 14902031 := bstep (se 1 (by rfl) ⟨11176523, by rfl⟩ : syracuseStep 14902031 = 22353047) B22353047
theorem B9934687 : Blo 2065435 9934687 := bstep (se 1 (by rfl) ⟨7451015, by rfl⟩ : syracuseStep 9934687 = 14902031) B14902031
theorem B13246249 : Blo 2065435 13246249 := bstep (se 2 (by rfl) ⟨4967343, by rfl⟩ : syracuseStep 13246249 = 9934687) B9934687
theorem B17661665 : Blo 2065435 17661665 := bstep (se 2 (by rfl) ⟨6623124, by rfl⟩ : syracuseStep 17661665 = 13246249) B13246249
theorem B11774443 : Blo 2065435 11774443 := bstep (se 1 (by rfl) ⟨8830832, by rfl⟩ : syracuseStep 11774443 = 17661665) B17661665
theorem B15699257 : Blo 2065435 15699257 := bstep (se 2 (by rfl) ⟨5887221, by rfl⟩ : syracuseStep 15699257 = 11774443) B11774443
theorem B10466171 : Blo 2065435 10466171 := bstep (se 1 (by rfl) ⟨7849628, by rfl⟩ : syracuseStep 10466171 = 15699257) B15699257
theorem B6977447 : Blo 2065435 6977447 := bstep (se 1 (by rfl) ⟨5233085, by rfl⟩ : syracuseStep 6977447 = 10466171) B10466171
theorem B4651631 : Blo 2065435 4651631 := bstep (se 1 (by rfl) ⟨3488723, by rfl⟩ : syracuseStep 4651631 = 6977447) B6977447
theorem B3101087 : Blo 2065435 3101087 := bstep (se 1 (by rfl) ⟨2325815, by rfl⟩ : syracuseStep 3101087 = 4651631) B4651631
theorem B2067391 : Blo 2065435 2067391 := bstep (se 1 (by rfl) ⟨1550543, by rfl⟩ : syracuseStep 2067391 = 3101087) B3101087
theorem B3101093 : Blo 2065435 3101093 := bbase (se 4 (by rfl) ⟨290727, by rfl⟩ : syracuseStep 3101093 = 581455) (by norm_num)
theorem B2067395 : Blo 2065435 2067395 := bstep (se 1 (by rfl) ⟨1550546, by rfl⟩ : syracuseStep 2067395 = 3101093) B3101093
theorem B2616553 : Blo 2065435 2616553 := bbase (se 2 (by rfl) ⟨981207, by rfl⟩ : syracuseStep 2616553 = 1962415) (by norm_num)
theorem B3488737 : Blo 2065435 3488737 := bstep (se 2 (by rfl) ⟨1308276, by rfl⟩ : syracuseStep 3488737 = 2616553) B2616553
theorem B4651649 : Blo 2065435 4651649 := bstep (se 2 (by rfl) ⟨1744368, by rfl⟩ : syracuseStep 4651649 = 3488737) B3488737
theorem B3101099 : Blo 2065435 3101099 := bstep (se 1 (by rfl) ⟨2325824, by rfl⟩ : syracuseStep 3101099 = 4651649) B4651649
theorem B2067399 : Blo 2065435 2067399 := bstep (se 1 (by rfl) ⟨1550549, by rfl⟩ : syracuseStep 2067399 = 3101099) B3101099
theorem B2325829 : Blo 2065435 2325829 := bbase (se 4 (by rfl) ⟨218046, by rfl⟩ : syracuseStep 2325829 = 436093) (by norm_num)
theorem B3101105 : Blo 2065435 3101105 := bstep (se 2 (by rfl) ⟨1162914, by rfl⟩ : syracuseStep 3101105 = 2325829) B2325829
theorem B2067403 : Blo 2065435 2067403 := bstep (se 1 (by rfl) ⟨1550552, by rfl⟩ : syracuseStep 2067403 = 3101105) B3101105
theorem B3924845 : Blo 2065435 3924845 := bbase (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) (by norm_num)
theorem B2616563 : Blo 2065435 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B6977501 : Blo 2065435 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B4651667 : Blo 2065435 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B3101111 : Blo 2065435 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B2067407 : Blo 2065435 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B3101117 : Blo 2065435 3101117 := bbase (se 3 (by rfl) ⟨581459, by rfl⟩ : syracuseStep 3101117 = 1162919) (by norm_num)
theorem B2067411 : Blo 2065435 2067411 := bstep (se 1 (by rfl) ⟨1550558, by rfl⟩ : syracuseStep 2067411 = 3101117) B3101117
theorem B4651685 : Blo 2065435 4651685 := bbase (se 4 (by rfl) ⟨436095, by rfl⟩ : syracuseStep 4651685 = 872191) (by norm_num)
theorem B3101123 : Blo 2065435 3101123 := bstep (se 1 (by rfl) ⟨2325842, by rfl⟩ : syracuseStep 3101123 = 4651685) B4651685
theorem B2067415 : Blo 2065435 2067415 := bstep (se 1 (by rfl) ⟨1550561, by rfl⟩ : syracuseStep 2067415 = 3101123) B3101123
theorem B5233157 : Blo 2065435 5233157 := bbase (se 4 (by rfl) ⟨490608, by rfl⟩ : syracuseStep 5233157 = 981217) (by norm_num)
theorem B3488771 : Blo 2065435 3488771 := bstep (se 1 (by rfl) ⟨2616578, by rfl⟩ : syracuseStep 3488771 = 5233157) B5233157
theorem B2325847 : Blo 2065435 2325847 := bstep (se 1 (by rfl) ⟨1744385, by rfl⟩ : syracuseStep 2325847 = 3488771) B3488771
theorem B3101129 : Blo 2065435 3101129 := bstep (se 2 (by rfl) ⟨1162923, by rfl⟩ : syracuseStep 3101129 = 2325847) B2325847
theorem B2067419 : Blo 2065435 2067419 := bstep (se 1 (by rfl) ⟨1550564, by rfl⟩ : syracuseStep 2067419 = 3101129) B3101129
theorem B4415485 : Blo 2065435 4415485 := bbase (se 3 (by rfl) ⟨827903, by rfl⟩ : syracuseStep 4415485 = 1655807) (by norm_num)
theorem B5887313 : Blo 2065435 5887313 := bstep (se 2 (by rfl) ⟨2207742, by rfl⟩ : syracuseStep 5887313 = 4415485) B4415485
theorem B3924875 : Blo 2065435 3924875 := bstep (se 1 (by rfl) ⟨2943656, by rfl⟩ : syracuseStep 3924875 = 5887313) B5887313
theorem B10466333 : Blo 2065435 10466333 := bstep (se 3 (by rfl) ⟨1962437, by rfl⟩ : syracuseStep 10466333 = 3924875) B3924875
theorem B6977555 : Blo 2065435 6977555 := bstep (se 1 (by rfl) ⟨5233166, by rfl⟩ : syracuseStep 6977555 = 10466333) B10466333
theorem B4651703 : Blo 2065435 4651703 := bstep (se 1 (by rfl) ⟨3488777, by rfl⟩ : syracuseStep 4651703 = 6977555) B6977555
theorem B3101135 : Blo 2065435 3101135 := bstep (se 1 (by rfl) ⟨2325851, by rfl⟩ : syracuseStep 3101135 = 4651703) B4651703
theorem B2067423 : Blo 2065435 2067423 := bstep (se 1 (by rfl) ⟨1550567, by rfl⟩ : syracuseStep 2067423 = 3101135) B3101135
theorem B3101141 : Blo 2065435 3101141 := bbase (se 7 (by rfl) ⟨36341, by rfl⟩ : syracuseStep 3101141 = 72683) (by norm_num)
theorem B2067427 : Blo 2065435 2067427 := bstep (se 1 (by rfl) ⟨1550570, by rfl⟩ : syracuseStep 2067427 = 3101141) B3101141
theorem B7849781 : Blo 2065435 7849781 := bbase (se 5 (by rfl) ⟨367958, by rfl⟩ : syracuseStep 7849781 = 735917) (by norm_num)
theorem B5233187 : Blo 2065435 5233187 := bstep (se 1 (by rfl) ⟨3924890, by rfl⟩ : syracuseStep 5233187 = 7849781) B7849781
theorem B3488791 : Blo 2065435 3488791 := bstep (se 1 (by rfl) ⟨2616593, by rfl⟩ : syracuseStep 3488791 = 5233187) B5233187
theorem B4651721 : Blo 2065435 4651721 := bstep (se 2 (by rfl) ⟨1744395, by rfl⟩ : syracuseStep 4651721 = 3488791) B3488791
theorem B3101147 : Blo 2065435 3101147 := bstep (se 1 (by rfl) ⟨2325860, by rfl⟩ : syracuseStep 3101147 = 4651721) B4651721
theorem B2067431 : Blo 2065435 2067431 := bstep (se 1 (by rfl) ⟨1550573, by rfl⟩ : syracuseStep 2067431 = 3101147) B3101147
theorem B2325865 : Blo 2065435 2325865 := bbase (se 2 (by rfl) ⟨872199, by rfl⟩ : syracuseStep 2325865 = 1744399) (by norm_num)
theorem B3101153 : Blo 2065435 3101153 := bstep (se 2 (by rfl) ⟨1162932, by rfl⟩ : syracuseStep 3101153 = 2325865) B2325865
theorem B2067435 : Blo 2065435 2067435 := bstep (se 1 (by rfl) ⟨1550576, by rfl⟩ : syracuseStep 2067435 = 3101153) B3101153
theorem C0 (j : ℕ) (h1 : 516358 ≤ j) (h2 : j ≤ 516858) : Blo 2065435 (4 * j + 3) := by
  interval_cases j
  · exact B2065435
  · exact B2065439
  · exact B2065443
  · exact B2065447
  · exact B2065451
  · exact B2065455
  · exact B2065459
  · exact B2065463
  · exact B2065467
  · exact B2065471
  · exact B2065475
  · exact B2065479
  · exact B2065483
  · exact B2065487
  · exact B2065491
  · exact B2065495
  · exact B2065499
  · exact B2065503
  · exact B2065507
  · exact B2065511
  · exact B2065515
  · exact B2065519
  · exact B2065523
  · exact B2065527
  · exact B2065531
  · exact B2065535
  · exact B2065539
  · exact B2065543
  · exact B2065547
  · exact B2065551
  · exact B2065555
  · exact B2065559
  · exact B2065563
  · exact B2065567
  · exact B2065571
  · exact B2065575
  · exact B2065579
  · exact B2065583
  · exact B2065587
  · exact B2065591
  · exact B2065595
  · exact B2065599
  · exact B2065603
  · exact B2065607
  · exact B2065611
  · exact B2065615
  · exact B2065619
  · exact B2065623
  · exact B2065627
  · exact B2065631
  · exact B2065635
  · exact B2065639
  · exact B2065643
  · exact B2065647
  · exact B2065651
  · exact B2065655
  · exact B2065659
  · exact B2065663
  · exact B2065667
  · exact B2065671
  · exact B2065675
  · exact B2065679
  · exact B2065683
  · exact B2065687
  · exact B2065691
  · exact B2065695
  · exact B2065699
  · exact B2065703
  · exact B2065707
  · exact B2065711
  · exact B2065715
  · exact B2065719
  · exact B2065723
  · exact B2065727
  · exact B2065731
  · exact B2065735
  · exact B2065739
  · exact B2065743
  · exact B2065747
  · exact B2065751
  · exact B2065755
  · exact B2065759
  · exact B2065763
  · exact B2065767
  · exact B2065771
  · exact B2065775
  · exact B2065779
  · exact B2065783
  · exact B2065787
  · exact B2065791
  · exact B2065795
  · exact B2065799
  · exact B2065803
  · exact B2065807
  · exact B2065811
  · exact B2065815
  · exact B2065819
  · exact B2065823
  · exact B2065827
  · exact B2065831
  · exact B2065835
  · exact B2065839
  · exact B2065843
  · exact B2065847
  · exact B2065851
  · exact B2065855
  · exact B2065859
  · exact B2065863
  · exact B2065867
  · exact B2065871
  · exact B2065875
  · exact B2065879
  · exact B2065883
  · exact B2065887
  · exact B2065891
  · exact B2065895
  · exact B2065899
  · exact B2065903
  · exact B2065907
  · exact B2065911
  · exact B2065915
  · exact B2065919
  · exact B2065923
  · exact B2065927
  · exact B2065931
  · exact B2065935
  · exact B2065939
  · exact B2065943
  · exact B2065947
  · exact B2065951
  · exact B2065955
  · exact B2065959
  · exact B2065963
  · exact B2065967
  · exact B2065971
  · exact B2065975
  · exact B2065979
  · exact B2065983
  · exact B2065987
  · exact B2065991
  · exact B2065995
  · exact B2065999
  · exact B2066003
  · exact B2066007
  · exact B2066011
  · exact B2066015
  · exact B2066019
  · exact B2066023
  · exact B2066027
  · exact B2066031
  · exact B2066035
  · exact B2066039
  · exact B2066043
  · exact B2066047
  · exact B2066051
  · exact B2066055
  · exact B2066059
  · exact B2066063
  · exact B2066067
  · exact B2066071
  · exact B2066075
  · exact B2066079
  · exact B2066083
  · exact B2066087
  · exact B2066091
  · exact B2066095
  · exact B2066099
  · exact B2066103
  · exact B2066107
  · exact B2066111
  · exact B2066115
  · exact B2066119
  · exact B2066123
  · exact B2066127
  · exact B2066131
  · exact B2066135
  · exact B2066139
  · exact B2066143
  · exact B2066147
  · exact B2066151
  · exact B2066155
  · exact B2066159
  · exact B2066163
  · exact B2066167
  · exact B2066171
  · exact B2066175
  · exact B2066179
  · exact B2066183
  · exact B2066187
  · exact B2066191
  · exact B2066195
  · exact B2066199
  · exact B2066203
  · exact B2066207
  · exact B2066211
  · exact B2066215
  · exact B2066219
  · exact B2066223
  · exact B2066227
  · exact B2066231
  · exact B2066235
  · exact B2066239
  · exact B2066243
  · exact B2066247
  · exact B2066251
  · exact B2066255
  · exact B2066259
  · exact B2066263
  · exact B2066267
  · exact B2066271
  · exact B2066275
  · exact B2066279
  · exact B2066283
  · exact B2066287
  · exact B2066291
  · exact B2066295
  · exact B2066299
  · exact B2066303
  · exact B2066307
  · exact B2066311
  · exact B2066315
  · exact B2066319
  · exact B2066323
  · exact B2066327
  · exact B2066331
  · exact B2066335
  · exact B2066339
  · exact B2066343
  · exact B2066347
  · exact B2066351
  · exact B2066355
  · exact B2066359
  · exact B2066363
  · exact B2066367
  · exact B2066371
  · exact B2066375
  · exact B2066379
  · exact B2066383
  · exact B2066387
  · exact B2066391
  · exact B2066395
  · exact B2066399
  · exact B2066403
  · exact B2066407
  · exact B2066411
  · exact B2066415
  · exact B2066419
  · exact B2066423
  · exact B2066427
  · exact B2066431
  · exact B2066435
  · exact B2066439
  · exact B2066443
  · exact B2066447
  · exact B2066451
  · exact B2066455
  · exact B2066459
  · exact B2066463
  · exact B2066467
  · exact B2066471
  · exact B2066475
  · exact B2066479
  · exact B2066483
  · exact B2066487
  · exact B2066491
  · exact B2066495
  · exact B2066499
  · exact B2066503
  · exact B2066507
  · exact B2066511
  · exact B2066515
  · exact B2066519
  · exact B2066523
  · exact B2066527
  · exact B2066531
  · exact B2066535
  · exact B2066539
  · exact B2066543
  · exact B2066547
  · exact B2066551
  · exact B2066555
  · exact B2066559
  · exact B2066563
  · exact B2066567
  · exact B2066571
  · exact B2066575
  · exact B2066579
  · exact B2066583
  · exact B2066587
  · exact B2066591
  · exact B2066595
  · exact B2066599
  · exact B2066603
  · exact B2066607
  · exact B2066611
  · exact B2066615
  · exact B2066619
  · exact B2066623
  · exact B2066627
  · exact B2066631
  · exact B2066635
  · exact B2066639
  · exact B2066643
  · exact B2066647
  · exact B2066651
  · exact B2066655
  · exact B2066659
  · exact B2066663
  · exact B2066667
  · exact B2066671
  · exact B2066675
  · exact B2066679
  · exact B2066683
  · exact B2066687
  · exact B2066691
  · exact B2066695
  · exact B2066699
  · exact B2066703
  · exact B2066707
  · exact B2066711
  · exact B2066715
  · exact B2066719
  · exact B2066723
  · exact B2066727
  · exact B2066731
  · exact B2066735
  · exact B2066739
  · exact B2066743
  · exact B2066747
  · exact B2066751
  · exact B2066755
  · exact B2066759
  · exact B2066763
  · exact B2066767
  · exact B2066771
  · exact B2066775
  · exact B2066779
  · exact B2066783
  · exact B2066787
  · exact B2066791
  · exact B2066795
  · exact B2066799
  · exact B2066803
  · exact B2066807
  · exact B2066811
  · exact B2066815
  · exact B2066819
  · exact B2066823
  · exact B2066827
  · exact B2066831
  · exact B2066835
  · exact B2066839
  · exact B2066843
  · exact B2066847
  · exact B2066851
  · exact B2066855
  · exact B2066859
  · exact B2066863
  · exact B2066867
  · exact B2066871
  · exact B2066875
  · exact B2066879
  · exact B2066883
  · exact B2066887
  · exact B2066891
  · exact B2066895
  · exact B2066899
  · exact B2066903
  · exact B2066907
  · exact B2066911
  · exact B2066915
  · exact B2066919
  · exact B2066923
  · exact B2066927
  · exact B2066931
  · exact B2066935
  · exact B2066939
  · exact B2066943
  · exact B2066947
  · exact B2066951
  · exact B2066955
  · exact B2066959
  · exact B2066963
  · exact B2066967
  · exact B2066971
  · exact B2066975
  · exact B2066979
  · exact B2066983
  · exact B2066987
  · exact B2066991
  · exact B2066995
  · exact B2066999
  · exact B2067003
  · exact B2067007
  · exact B2067011
  · exact B2067015
  · exact B2067019
  · exact B2067023
  · exact B2067027
  · exact B2067031
  · exact B2067035
  · exact B2067039
  · exact B2067043
  · exact B2067047
  · exact B2067051
  · exact B2067055
  · exact B2067059
  · exact B2067063
  · exact B2067067
  · exact B2067071
  · exact B2067075
  · exact B2067079
  · exact B2067083
  · exact B2067087
  · exact B2067091
  · exact B2067095
  · exact B2067099
  · exact B2067103
  · exact B2067107
  · exact B2067111
  · exact B2067115
  · exact B2067119
  · exact B2067123
  · exact B2067127
  · exact B2067131
  · exact B2067135
  · exact B2067139
  · exact B2067143
  · exact B2067147
  · exact B2067151
  · exact B2067155
  · exact B2067159
  · exact B2067163
  · exact B2067167
  · exact B2067171
  · exact B2067175
  · exact B2067179
  · exact B2067183
  · exact B2067187
  · exact B2067191
  · exact B2067195
  · exact B2067199
  · exact B2067203
  · exact B2067207
  · exact B2067211
  · exact B2067215
  · exact B2067219
  · exact B2067223
  · exact B2067227
  · exact B2067231
  · exact B2067235
  · exact B2067239
  · exact B2067243
  · exact B2067247
  · exact B2067251
  · exact B2067255
  · exact B2067259
  · exact B2067263
  · exact B2067267
  · exact B2067271
  · exact B2067275
  · exact B2067279
  · exact B2067283
  · exact B2067287
  · exact B2067291
  · exact B2067295
  · exact B2067299
  · exact B2067303
  · exact B2067307
  · exact B2067311
  · exact B2067315
  · exact B2067319
  · exact B2067323
  · exact B2067327
  · exact B2067331
  · exact B2067335
  · exact B2067339
  · exact B2067343
  · exact B2067347
  · exact B2067351
  · exact B2067355
  · exact B2067359
  · exact B2067363
  · exact B2067367
  · exact B2067371
  · exact B2067375
  · exact B2067379
  · exact B2067383
  · exact B2067387
  · exact B2067391
  · exact B2067395
  · exact B2067399
  · exact B2067403
  · exact B2067407
  · exact B2067411
  · exact B2067415
  · exact B2067419
  · exact B2067423
  · exact B2067427
  · exact B2067431
  · exact B2067435
theorem solution (m : ℕ) (hlo : 2065435 ≤ m) (hhi : m ≤ 2067435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 516358 ≤ j := by omega
    have hj2 : j ≤ 516858 := by omega
    have hb : Blo 2065435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
